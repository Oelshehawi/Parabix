#include "ztf-phrase-scan.h"
#include "common.h"
#include <llvm/IR/Function.h>                      // for Function, Function...
#include <llvm/IR/Module.h>                        // for Module
#include <llvm/Support/CommandLine.h>              // for ParseCommandLineOp...
#include <llvm/Support/Debug.h>                    // for dbgs
#include <kernel/core/kernel_builder.h>
#include <kernel/core/streamset.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/Support/raw_ostream.h>
#include <boost/intrusive/detail/math.hpp>
#include <sstream>

#if 0
#define DEBUG_PRINT(title,value) b->CallPrintInt(title, value)
#else
#define DEBUG_PRINT(title,value)
#endif

#if 0
#define CHECK_COMPRESSION_DECOMPRESSION_STORE
#endif
#if 0
#define PRINT_DICT_ONLY
#endif
#if 0
#define PRINT_PHRASE_DEBUG_INFO
#endif
#if 0
#define PRINT_HT_STATS
#endif
#if 0
#define PRINT_HT_STATS_MARK_REPEATED_HASHVAL
#endif
#if 0
#define PRINT_DECOMPRESSION_DICT_INFO
#endif
using namespace kernel;
using namespace llvm;

using BuilderRef = Kernel::BuilderRef;

// First pass:
// Create the frequency table for current segment while comparing with global frequency table.
// replace/update phrases from global table if the frequency of phrase in current segment is more than the frequency in global table.
// Second pass:
// Lookup phrases in global table; mark 1-bit at the last byte of the phrase for phrases that have entry in the global table.

// Each segment consists of full lines only
// lfData -> positions of line break in each segment of 1048576 bytes

MarkRepeatedHashvalue::MarkRepeatedHashvalue(BuilderRef b,
                                               EncodingInfo encodingScheme,
                                               unsigned numSyms,
                                               unsigned groupNo,
                                               unsigned offset,
                                               StreamSet * lfData,
                                               StreamSet * symEndMarks,
                                               StreamSet * cmpMarksSoFar,
                                               StreamSet * const hashValues,
                                               StreamSet * const byteData,
                                               StreamSet * hashMarks,
                                               StreamSet * hashValuesUpdated, 
                                               unsigned strideBlocks)
: MultiBlockKernel(b, "MarkRepeatedHashvalue" + std::to_string(numSyms) + std::to_string(groupNo) + lengthGroupSuffix(encodingScheme, groupNo),
                   {Binding{"lfPos", lfData, FixedRate(ProcessingRate::Rational{1, 1048576})}, // reads 1 item per stride of 1MB
                    Binding{"symEndMarks", symEndMarks, FixedRate(), Deferred()}, // exact processed is PartialSum("lfPos"), but might not be exact multiple of blockwidth or at aligned location
                    Binding{"cmpMarksSoFar", cmpMarksSoFar, FixedRate(), Deferred() },
                    Binding{"hashValues", hashValues, FixedRate(), Deferred() },
                    Binding{"byteData", byteData, FixedRate(), Deferred() }},
                   {}, {}, {},
                   {InternalScalar{b->getBitBlockType(), "pendingMaskInverted"},
                    InternalScalar{b->getBitBlockType(), "pendingPhraseMask"},
                    InternalScalar{b->getBitBlockType(), "pendingDictPhraseMask"},
                    InternalScalar{b->getSizeTy(), "segIndex"},
                    InternalScalar{b->getSizeTy(), "absBlocksProcessed"},
                    InternalScalar{b->getSizeTy(), "lastLfPos"},
                    InternalScalar{ArrayType::get(ArrayType::get(ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), phraseHashSubTableSize(encodingScheme, groupNo)), encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1), "hashTable"},
                    InternalScalar{ArrayType::get(b->getInt8Ty(), phraseHashSubTableSize(encodingScheme, groupNo) * (encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1)), "freqTable"},
                    InternalScalar{ArrayType::get(ArrayType::get(ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), phraseHashSubTableSize(encodingScheme, groupNo)), encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1), "segmentHashTable"},
                    InternalScalar{ArrayType::get(b->getInt8Ty(), phraseHashSubTableSize(encodingScheme, groupNo) * (encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1)), "segmentFreqTable"}}),
mEncodingScheme(encodingScheme), mStrideSize(1048576), mGroupNo(groupNo), mNumSym(numSyms), mSubStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS)), mOffset(offset) {
    mOutputStreamSets.emplace_back("hashMarks", hashMarks, BoundedRate(0, 1));
    mOutputStreamSets.emplace_back("hashValuesUpdated", hashValuesUpdated, BoundedRate(0, 1));
    setStride(1048576);
}

void MarkRepeatedHashvalue::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    ScanWordParameters sw(b, mStride);
    LengthGroupParameters lg(b, mEncodingScheme, mGroupNo, mNumSym);
    Constant * sz_STRIDE = b->getSize(mStride);
    Constant * sz_SUB_STRIDE = b->getSize(mSubStride);
    Constant * sz_BLOCKS_PER_STRIDE = b->getSize(mStride/b->getBitBlockWidth());
    Constant * sz_BLOCKS_PER_SUB_STRIDE = b->getSize(mSubStride/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_TWO = b->getSize(2);
    Constant * sz_BITS = b->getSize(SIZE_T_BITS);
    Constant * sz_BITS_PER_BYTE = b->getSize(BITS_PER_BYTE);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    Constant * sz_PHRASE_LEN_OFFSET = b->getSize(mOffset);
    Value * sz_HALF_TBL_IDX = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo) / 2);
    Value * sz_HALF_TBL_IDX_0 = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo) / 3);
    Value * checkGroupNum = b->CreateICmpUGT(b->getSize(mGroupNo), sz_ZERO);
    sz_HALF_TBL_IDX = b->CreateSelect(checkGroupNum, sz_HALF_TBL_IDX, sz_HALF_TBL_IDX_0);
    // NEED FIX: may be reverted?
    checkGroupNum = b->CreateICmpEQ(b->getSize(mGroupNo), b->getSize(3));
    sz_HALF_TBL_IDX = b->CreateSelect(checkGroupNum, sz_ZERO, sz_HALF_TBL_IDX);

    Value * const sz_HASH_TABLE = b->getSize((mEncodingScheme.byLength[mGroupNo].hi * phraseHashSubTableSize(mEncodingScheme, mGroupNo)) * (mEncodingScheme.byLength[mGroupNo].hi - mEncodingScheme.byLength[mGroupNo].lo + 1));
    Value * const sz_FREQ_TABLE = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo) * (mEncodingScheme.byLength[mGroupNo].hi - mEncodingScheme.byLength[mGroupNo].lo + 1));
    assert ((mStride % mSubStride) == 0);
    Value * totalSubStrides =  b->getSize(mStride / mSubStride); // 102400/2048 with BitBlock=256

    Type * sizeTy = b->getSizeTy();
    Type * bitBlockPtrTy = b->getBitBlockType()->getPointerTo();
    Type * phraseType = ArrayType::get(b->getInt8Ty(), mEncodingScheme.byLength[mGroupNo].hi);

    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const stridePrologue = b->CreateBasicBlock("stridePrologue");
    BasicBlock * const subStrideMaskPrep = b->CreateBasicBlock("subStrideMaskPrep");
    BasicBlock * const strideMasksReady = b->CreateBasicBlock("strideMasksReady");
    BasicBlock * const keyProcessingLoop = b->CreateBasicBlock("keyProcessingLoop");
    BasicBlock * const processKey = b->CreateBasicBlock("processKey");
    BasicBlock * const tryStore = b->CreateBasicBlock("tryStore");
    BasicBlock * const storeKey = b->CreateBasicBlock("storeKey");
    BasicBlock * const nextKey = b->CreateBasicBlock("nextKey");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const updatePending = b->CreateBasicBlock("updatePending");
    BasicBlock * const hashMarksDone = b->CreateBasicBlock("hashMarksDone");
    BasicBlock * const symProcessingLoop = b->CreateBasicBlock("symProcessingLoop");
    BasicBlock * const processSym = b->CreateBasicBlock("processSym");
    BasicBlock * const checkSymCompression = b->CreateBasicBlock("checkSymCompression");
    BasicBlock * const markSymCompression = b->CreateBasicBlock("markSymCompression");
    BasicBlock * const nextSym = b->CreateBasicBlock("nextSym");
    BasicBlock * const subStridePhrasesDone = b->CreateBasicBlock("subStridePhrasesDone");

    BasicBlock * const updateGlobalCount = b->CreateBasicBlock("updateGlobalCount");
    BasicBlock * const storeSymInGlobal = b->CreateBasicBlock("storeSymInGlobal");
    BasicBlock * const symsDone = b->CreateBasicBlock("symsDone");
    BasicBlock * const compareSyms = b->CreateBasicBlock("compareSyms");
    BasicBlock * const updateSegmentInternals = b->CreateBasicBlock("updateSegmentInternals");
    BasicBlock * const replaceGlobalTblEntry = b->CreateBasicBlock("replaceGlobalTblEntry");
    BasicBlock * const checkGlobalUpdate = b->CreateBasicBlock("checkGlobalUpdate");
    BasicBlock * const hashTableDone = b->CreateBasicBlock("hashTableDone");
    BasicBlock * const symProcessingPrep= b->CreateBasicBlock("symProcessingPrep");
    BasicBlock * const symMaskReady = b->CreateBasicBlock("symMaskReady");
    BasicBlock * const compareOverlappingSymWithinAndAcrossGroups = b->CreateBasicBlock("compareOverlappingSymWithinAndAcrossGroups");
    BasicBlock * const compareOverlappingSymInLastGroup = b->CreateBasicBlock("compareOverlappingSymInLastGroup");
    // BasicBlock * const printPhrase = b->CreateBasicBlock("printPhrase");
    // BasicBlock * const proceed = b->CreateBasicBlock("proceed");
#ifdef PRINT_HT_STATS_MARK_REPEATED_HASHVAL
    BasicBlock * const printHTusage = b->CreateBasicBlock("printHTusage");
    BasicBlock * const iterateSubTbl = b->CreateBasicBlock("iterateSubTbl");
    BasicBlock * const goToNextSubTbl = b->CreateBasicBlock("goToNextSubTbl");
    BasicBlock * const goToNextStride = b->CreateBasicBlock("goToNextStride");
    BasicBlock * const printIdx = b->CreateBasicBlock("printIdx");
    BasicBlock * const checkNextIdx = b->CreateBasicBlock("checkNextIdx");
#endif
    Value * const initialPos = b->getProcessedItemCount("symEndMarks"); // ensure this is blockwidth multiple. Refer to scalar absBlocksProcessed to skip a sub-block
    Value * const avail = b->getAvailableItemCount("symEndMarks");
    Value * const initialProduced = b->getProducedItemCount("hashMarks");

    Value * const bytesAccessible = b->getAccessibleItemCount("byteData");
    Value * const processedBlocks = b->getScalarField("absBlocksProcessed");
    Value * const actualProcessed = b->CreateMul(processedBlocks, sz_BLOCKWIDTH);
    Value * hashTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("segmentHashTable"), b->getInt8PtrTy());
    Value * freqTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("segmentFreqTable"), b->getInt8PtrTy());
    Value * globalHashTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("hashTable"), b->getInt8PtrTy());
    Value * globalFreqTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("freqTable"), b->getInt8PtrTy());

    Value * pendingMask = b->CreateNot(b->getScalarField("pendingMaskInverted")); // may not be needed as we do not need to LookBehind any processed words
    Value * producedPtr = b->CreateBitCast(b->getRawOutputPointer("hashMarks", actualProcessed), bitBlockPtrTy);
    b->CreateStore(pendingMask, producedPtr);

    Value * hashMarksPtr = b->CreateBitCast(b->getRawOutputPointer("hashMarks", actualProcessed), bitBlockPtrTy);
    b->CreateBr(stridePrologue);

    b->SetInsertPoint(stridePrologue);
    // Set up the loop variables as PHI nodes at the beginning of each stride.
    PHINode * const strideNo = b->CreatePHI(sizeTy, 2);
    strideNo->addIncoming(sz_ZERO, entryBlock);
    Value * nextStrideNo = b->CreateAdd(strideNo, sz_ONE);
    Value * const curIdx = b->getScalarField("segIndex");
    Value * lfPosPtr = b->CreateBitCast(b->getRawInputPointer("lfPos", curIdx), b->getSizeTy()->getPointerTo());
    Value * lfPos = b->CreateAlignedLoad(lfPosPtr, 1);
    Value * toCopy = b->CreateMul(b->CreateSub(lfPos, b->getScalarField("lastLfPos")), sz_TWO); // data to be written in this stride
    Value * memCpyPos = b->CreateAdd(b->getScalarField("lastLfPos"), sz_ONE);
    b->CreateMemCpy(b->getRawOutputPointer("hashValuesUpdated", memCpyPos), b->getRawInputPointer("hashValues", memCpyPos), toCopy, 1); 

    Value * totalProcessed = b->CreateMul(b->getScalarField("absBlocksProcessed"), sz_BLOCKWIDTH);
    Value * stridePos =  totalProcessed;
    Value * strideBlockOffset = b->getScalarField("absBlocksProcessed");
    Value * processBeforeThisPos = lfPos;
    Value * processAfterThisPos = b->getScalarField("lastLfPos");
    b->setScalarField("lastLfPos", lfPos);
    // overlapping partial blocks are processed twice within the same segment -> ok.
    // When the segment changes, do not process the partial block's already processed symbols.
    b->CreateBr(subStrideMaskPrep);

    b->SetInsertPoint(subStrideMaskPrep);
    PHINode * const subStrideNo = b->CreatePHI(sizeTy, 2);
    subStrideNo->addIncoming(sz_ZERO, stridePrologue);
    Value * nextSubStrideNo = b->CreateAdd(subStrideNo, sz_ONE);
    Value * subStridePos = b->CreateAdd(stridePos, b->CreateMul(subStrideNo, sz_SUB_STRIDE));
    Value * subStrideBlockOffset = b->CreateAdd(strideBlockOffset, b->CreateMul(subStrideNo, sz_BLOCKS_PER_SUB_STRIDE));
    std::vector<Value *> keyMasks = initializeCompressionMasks2(b, sw, sz_BLOCKS_PER_SUB_STRIDE, 1, subStrideBlockOffset, hashMarksPtr, strideMasksReady);
    Value * keyMask = keyMasks[0];

    b->SetInsertPoint(strideMasksReady);
    subStrideBlockOffset = b->CreateSub(subStrideBlockOffset, processedBlocks); // relative block offset
    Value * keyWordBasePtr = b->getInputStreamBlockPtr("symEndMarks", sz_ZERO, subStrideBlockOffset);
    keyWordBasePtr = b->CreateBitCast(keyWordBasePtr, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(keyMask, sz_ZERO), hashTableDone, keyProcessingLoop);

    b->SetInsertPoint(keyProcessingLoop);
    PHINode * const keyMaskPhi = b->CreatePHI(sizeTy, 2);
    keyMaskPhi->addIncoming(keyMask, strideMasksReady);
    PHINode * const keyWordPhi = b->CreatePHI(sizeTy, 2);
    keyWordPhi->addIncoming(sz_ZERO, strideMasksReady);
    Value * keyWordIdx = b->CreateCountForwardZeroes(keyMaskPhi, "keyWordIdx");
    Value * nextKeyWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(keyWordBasePtr, keyWordIdx)), sizeTy);
    Value * theKeyWord = b->CreateSelect(b->CreateICmpEQ(keyWordPhi, sz_ZERO), nextKeyWord, keyWordPhi);
    Value * keyWordPos = b->CreateAdd(subStridePos, b->CreateMul(keyWordIdx, sw.WIDTH));
    Value * keyMarkPosInWord = b->CreateCountForwardZeroes(theKeyWord);
    Value * keyMarkPos = b->CreateAdd(keyWordPos, keyMarkPosInWord, "keyEndPos");
    Value * keyProcessCond = b->CreateAnd(b->CreateICmpULE(keyMarkPos, processBeforeThisPos), b->CreateICmpUGT(keyMarkPos, processAfterThisPos));
    b->CreateCondBr(keyProcessCond, processKey, nextKey);

    b->SetInsertPoint(processKey);
    /* Determine the key length. */
    Value * hashValue = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", keyMarkPos)), sizeTy);
    Value * keyLength = b->CreateAdd(b->CreateLShr(hashValue, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET, "keyLength");
    Value * keyStartPos = b->CreateSub(keyMarkPos, b->CreateSub(keyLength, sz_ONE), "keyStartPos");
    // keyOffset for accessing the final half of an entry.
    Value * keyOffset = b->CreateSub(keyLength, lg.HALF_LENGTH);
    // Build up a single encoded value for table lookup from the hashcode sequence.
    Value * codewordVal = b->CreateAnd(hashValue, lg.LAST_SUFFIX_MASK);
    Value * hashcodePos = keyMarkPos;
    // codewordVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(codewordVal, sz_ONE), b->CreateShl(codewordVal, sz_ONE)),
    //                               codewordVal);
    for (unsigned j = 1; j < lg.groupInfo.encoding_bytes - 1; j++) {
        hashcodePos = b->CreateSub(hashcodePos, sz_ONE);
        Value * suffixByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", hashcodePos)), sizeTy);
        codewordVal = b->CreateShl(codewordVal, lg.HASH_SHIFT_BITS);
        codewordVal = b->CreateOr(codewordVal, b->CreateAnd(suffixByte, lg.SUFFIX_MASK));
    }
    // add PREFIX_LENGTH_MASK bits for larger index space
    hashcodePos = b->CreateSub(hashcodePos, sz_ONE);
    Value * pfxByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", hashcodePos)), sizeTy);
    // shift by pfx len bits
    pfxByte = b->CreateTrunc(b->CreateAnd(pfxByte, lg.PREFIX_LENGTH_MASK), b->getInt8Ty());
    // codewordVal = b->CreateOr(codewordVal, b->CreateAnd(pfxByte, lg.SUFFIX_MASK));
    // codewordVal = b->CreateOr(b->CreateAnd(codewordVal, lg.EXTRA_BITS_MASK), b->CreateShl(codewordVal, lg.EXTRA_BITS));
    Value * subTablePtr = b->CreateGEP(hashTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    Value * tableIdxHash = b->CreateAnd(codewordVal, lg.TABLE_MASK, "tableIdx");
    Value * origTableIdx = tableIdxHash;
    // tableIdxHash = b->CreateSelect(b->CreateICmpUGT(tableIdxHash, sz_HALF_TBL_IDX), tableIdxHash, b->CreateAdd(tableIdxHash, sz_HALF_TBL_IDX));
    Value * keyIdxPtr = b->CreateGEP(subTablePtr, b->CreateMul(tableIdxHash, keyLength));
    Value * tblEntryPtr = b->CreateInBoundsGEP(keyIdxPtr, sz_ZERO);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength);
    Value * freqSubTablePtr = b->CreateGEP(freqTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.FREQ_SUBTABLE_SIZE));
    Value * freqTblEntryPtr = b->CreateInBoundsGEP(freqSubTablePtr, tableIdxHash);

    Value * globalSubTablePtr = b->CreateGEP(globalHashTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    Value * globalKeyIdxPtr = b->CreateGEP(globalSubTablePtr, b->CreateMul(tableIdxHash, keyLength));
    Value * globalTblEntryPtr = b->CreateInBoundsGEP(globalKeyIdxPtr, sz_ZERO);
    Value * globalFreqSubTablePtr = b->CreateGEP(globalFreqTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.FREQ_SUBTABLE_SIZE));
    Value * globalFreqTblEntryPtr = b->CreateInBoundsGEP(globalFreqSubTablePtr, tableIdxHash);

    // Use two 8-byte loads to get hash and symbol values.
    Value * freqTblPtr = b->CreateBitCast(freqTblEntryPtr, b->getInt8PtrTy());
    Value * tblPtr1 = b->CreateBitCast(tblEntryPtr, lg.halfSymPtrTy);
    Value * tblPtr2 = b->CreateBitCast(b->CreateGEP(tblEntryPtr, keyOffset), lg.halfSymPtrTy);
    Value * symPtr1 = b->CreateBitCast(b->getRawInputPointer("byteData", keyStartPos), lg.halfSymPtrTy);
#if 0 // write data in csv
// "codewordValNum","tableIdxHashNum","length","phrase"
    b->CreateDprintfCall(b->getInt32(STDERR_FILENO), "\n");
    Value * codewordValNum = codewordVal;
    Type * const t = codewordVal->getType();
    if (t->isPointerTy()) {
        codewordValNum = b->CreatePtrToInt(codewordVal, b->getInt64Ty());
    } else if (t->isIntegerTy()) {
        if (t->getIntegerBitWidth() < 64) {
            codewordValNum = b->CreateZExt(codewordVal,  b->getInt64Ty());
        }
    }
    // to read all 4 columns without error lines
    // b->CreateDprintfCall(b->getInt32(STDERR_FILENO), "%" PRIu64 , codewordValNum);
    // b->CreateDprintfCall(b->getInt32(STDERR_FILENO), "\",\"");

    Value * tableIdxHashNum = tableIdxHash;
    Type * const t1 = tableIdxHash->getType();
    if (t1->isPointerTy()) {
        tableIdxHashNum = b->CreatePtrToInt(tableIdxHash, b->getInt64Ty());
    } else if (t1->isIntegerTy()) {
        if (t1->getIntegerBitWidth() < 64) {
            tableIdxHashNum = b->CreateZExt(tableIdxHash,  b->getInt64Ty());
        }
    }
    // to read all 4 columns without error lines
    // b->CreateDprintfCall(b->getInt32(STDERR_FILENO), "%" PRIu64 , tableIdxHashNum);
    // b->CreateDprintfCall(b->getInt32(STDERR_FILENO), "\",\"");
    // b->CreateDprintfCall(b->getInt32(STDERR_FILENO), "%" PRIu64 , keyLength);
    // b->CreateDprintfCall(b->getInt32(STDERR_FILENO), "\",\"");

    b->CreateDprintfCall(b->getInt32(STDERR_FILENO), "\"");
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength);
    b->CreateDprintfCall(b->getInt32(STDERR_FILENO), "\"");
#endif
    Value * symPtr2 = b->CreateBitCast(b->getRawInputPointer("byteData", b->CreateAdd(keyStartPos, keyOffset)), lg.halfSymPtrTy);
    // Check to see if the hash table entry is nonzero (already assigned).
    Value * sym1 = b->CreateAlignedLoad(symPtr1, 1);
    Value * sym2 = b->CreateAlignedLoad(symPtr2, 1);
    Value * entry1 = b->CreateMonitoredScalarFieldLoad("segmentHashTable", tblPtr1);
    Value * entry2 = b->CreateMonitoredScalarFieldLoad("segmentHashTable", tblPtr2);
    Value * countEntry = b->CreateMonitoredScalarFieldLoad("segmentFreqTable", freqTblPtr);

    Value * globalFreqTblPtr = b->CreateBitCast(globalFreqTblEntryPtr, b->getInt8PtrTy());
    Value * globalTblPtr1 = b->CreateBitCast(globalTblEntryPtr, lg.halfSymPtrTy);
    Value * globalTblPtr2 = b->CreateBitCast(b->CreateGEP(globalTblEntryPtr, keyOffset), lg.halfSymPtrTy);
    Value * globalEntry1 = b->CreateMonitoredScalarFieldLoad("hashTable", globalTblPtr1);
    Value * globalEntry2 = b->CreateMonitoredScalarFieldLoad("hashTable", globalTblPtr2);
    Value * globalCountEntry = b->CreateMonitoredScalarFieldLoad("freqTable", globalFreqTblPtr);

    Value * symIsEqEntry = b->CreateAnd(b->CreateICmpEQ(entry1, sym1), b->CreateICmpEQ(entry2, sym2));
    b->CreateCondBr(symIsEqEntry, updateSegmentInternals, tryStore);

    b->SetInsertPoint(tryStore);
    Value * isEmptyEntry = b->CreateICmpEQ(b->CreateOr(entry1, entry2), Constant::getNullValue(lg.halfLengthTy));
    b->CreateCondBr(isEmptyEntry, storeKey, nextKey); //tryHandleCollision

    b->SetInsertPoint(storeKey);
#if 0
    Value * lgthBase = b->CreateSub(keyLength, lg.LO);
    Value * pfxOffset = b->CreateAdd(lg.PREFIX_BASE, lgthBase);
    Value * multiplier = b->CreateMul(lg.RANGE, pfxByte);
    Value * ZTF_prefix_dbg = b->CreateAdd(pfxOffset, multiplier);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength);
    writtenVal = b->CreateOr(b->CreateShl(writtenVal, lg.MAX_HASH_BITS), ZTF_prefix_dbg, "writtenVal");
    Value * const copyLen = b->CreateAdd(lg.ENC_BYTES, sz_ZERO);
    Value * outputCodeword = b->CreateAlloca(b->getInt64Ty(), copyLen);
    b->CreateAlignedStore(writtenVal, outputCodeword, 1);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), outputCodeword, copyLen);
    b->CallPrintInt("writtenVal", writtenVal);
    b->CallPrintInt("phraseLengthFinal", keyLength);
    b->CallPrintInt("mNumSym", b->getSize(mNumSym));
    b->CallPrintInt("phraseWordPos", keyWordPos);
    b->CallPrintInt("phraseMarkPosInWord", keyMarkPosInWord);
    b->CallPrintInt("phraseMarkPosFinal", keyMarkPos);
#endif
    // We have a new symbol that allows future occurrences of the symbol to
    // be compressed using the hash code.
    b->CreateMonitoredScalarFieldStore("segmentHashTable", sym1, tblPtr1);
    b->CreateMonitoredScalarFieldStore("segmentHashTable", sym2, tblPtr2);
    b->CreateMonitoredScalarFieldStore("segmentFreqTable", b->getInt8(0x1), freqTblPtr);
    b->CreateBr(nextKey);

    b->SetInsertPoint(updateSegmentInternals);
    Value * updateCount = b->CreateSelect(b->CreateICmpEQ(countEntry, b->getInt8(0xFF)), countEntry, b->CreateAdd(countEntry, b->getInt8(0x1)));
    b->CreateMonitoredScalarFieldStore("segmentFreqTable", updateCount, freqTblPtr);
    // if globalHashtable entry is empty, store the phrase in global hashtable.
    Value * globalSymEmpty = b->CreateICmpEQ(b->CreateOr(globalEntry1, globalEntry2), Constant::getNullValue(lg.halfLengthTy));

    // if global table slot is empty, store the segment table entry.
    b->CreateCondBr(globalSymEmpty, storeSymInGlobal, compareSyms);
    b->SetInsertPoint(storeSymInGlobal);
    b->CreateMonitoredScalarFieldStore("hashTable", sym1, globalTblPtr1);
    b->CreateMonitoredScalarFieldStore("hashTable", sym2, globalTblPtr2);
    b->CreateMonitoredScalarFieldStore("freqTable", updateCount, globalFreqTblPtr);
    b->CreateBr(nextKey);

    b->SetInsertPoint(compareSyms);
    Value * tableEntriesAreEqual = b->CreateAnd(b->CreateICmpEQ(entry1, globalEntry1), b->CreateICmpEQ(entry2, globalEntry2));
    b->CreateCondBr(tableEntriesAreEqual, updateGlobalCount, checkGlobalUpdate);
    b->SetInsertPoint(updateGlobalCount);
    b->CreateMonitoredScalarFieldStore("freqTable", updateCount, globalFreqTblPtr);
    b->CreateBr(nextKey);

    // if symbols in segment table and global table do not match, compare the frequencies,
    // and retain the higher frequency symbol.
    b->SetInsertPoint(checkGlobalUpdate);
    Value * compareFreq = b->CreateICmpUGT(updateCount, globalCountEntry, "compareFreq");
    b->CreateCondBr(compareFreq, replaceGlobalTblEntry, nextKey);

    b->SetInsertPoint(replaceGlobalTblEntry);
#if 0
    Value * globalTblPtr = b->CreateBitCast(globalTblEntryPtr, b->getInt8PtrTy());
    Value * tblPtr = b->CreateBitCast(tblEntryPtr, b->getInt8PtrTy());
    b->CallPrintInt("tableIdxHash", tableIdxHash);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), globalTblPtr, keyLength);
    b->CallPrintInt("globalCountEntry", globalCountEntry);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), tblPtr, keyLength);
    b->CallPrintInt("countEntry", countEntry);
#endif
    b->CreateMonitoredScalarFieldStore("hashTable", sym1, globalTblPtr1);
    b->CreateMonitoredScalarFieldStore("hashTable", sym2, globalTblPtr2);
    b->CreateMonitoredScalarFieldStore("freqTable", updateCount, globalFreqTblPtr);
    b->CreateBr(nextKey);

    b->SetInsertPoint(nextKey);
    Value * dropKey = b->CreateResetLowestBit(theKeyWord);
    Value * thisWordDone = b->CreateICmpEQ(dropKey, sz_ZERO);
    // There may be more keys in the key mask.
    Value * nextKeyMask = b->CreateSelect(thisWordDone, b->CreateResetLowestBit(keyMaskPhi), keyMaskPhi);
    BasicBlock * currentBB = b->GetInsertBlock();
    keyMaskPhi->addIncoming(nextKeyMask, currentBB);
    keyWordPhi->addIncoming(dropKey, currentBB);
    b->CreateCondBr(b->CreateICmpNE(nextKeyMask, sz_ZERO), keyProcessingLoop, hashTableDone);

    b->SetInsertPoint(hashTableDone);
    subStrideNo->addIncoming(nextSubStrideNo, hashTableDone);
    b->CreateCondBr(b->CreateICmpNE(nextSubStrideNo, totalSubStrides), subStrideMaskPrep, symProcessingPrep);

    b->SetInsertPoint(symProcessingPrep);
    PHINode * const step2subStrideNo = b->CreatePHI(sizeTy, 2, "step2subStrideNo");
    step2subStrideNo->addIncoming(sz_ZERO, hashTableDone);
    Value * step2nextSubStrideNo = b->CreateAdd(step2subStrideNo, sz_ONE);
    Value * step2subStridePos = b->CreateAdd(stridePos, b->CreateMul(step2subStrideNo, sz_SUB_STRIDE));
    Value * step2subStrideBlockOffset = b->CreateAdd(strideBlockOffset, b->CreateMul(step2subStrideNo, sz_BLOCKS_PER_SUB_STRIDE));
    std::vector<Value *> symMasks = initializeCompressionMasks2(b, sw, sz_BLOCKS_PER_SUB_STRIDE, 1, step2subStrideBlockOffset, hashMarksPtr, symMaskReady);
    Value * symMask = symMasks[0];

    b->SetInsertPoint(symMaskReady);
    step2subStrideBlockOffset = b->CreateSub(step2subStrideBlockOffset, processedBlocks);
    Value * symWordBasePtr = b->getInputStreamBlockPtr("symEndMarks", sz_ZERO, step2subStrideBlockOffset);
    symWordBasePtr = b->CreateBitCast(symWordBasePtr, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(symMask, sz_ZERO), subStridePhrasesDone, symProcessingLoop);

    b->SetInsertPoint(symProcessingLoop);
    PHINode * const symMaskPhi = b->CreatePHI(sizeTy, 2);
    symMaskPhi->addIncoming(symMask, symMaskReady);
    PHINode * const symWordPhi = b->CreatePHI(sizeTy, 2);
    symWordPhi->addIncoming(sz_ZERO, symMaskReady);
    Value * symWordIdx = b->CreateCountForwardZeroes(symMaskPhi, "symWordIdx");
    Value * nextsymWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(symWordBasePtr, symWordIdx)), sizeTy);
    Value * theSymWord = b->CreateSelect(b->CreateICmpEQ(symWordPhi, sz_ZERO), nextsymWord, symWordPhi);
    Value * symWordPos = b->CreateAdd(step2subStridePos, b->CreateMul(symWordIdx, sw.WIDTH));
    Value * symMarkPosInWord = b->CreateCountForwardZeroes(theSymWord);
    Value * symMarkPos = b->CreateAdd(symWordPos, symMarkPosInWord, "symEndPos");
    Value * symProcessCond = b->CreateAnd(b->CreateICmpULE(symMarkPos, processBeforeThisPos), b->CreateICmpUGT(symMarkPos, processAfterThisPos));
    b->CreateCondBr(symProcessCond, processSym, nextSym);

    b->SetInsertPoint(processSym);
    /* Determine the sym length. */
    Value * symHashValue = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", symMarkPos)), sizeTy);
    Value * symLength = b->CreateAdd(b->CreateLShr(symHashValue, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET, "symLength");
    Value * symStartPos = b->CreateSub(symMarkPos, b->CreateSub(symLength, sz_ONE), "symStartPos");
    // symOffset for accessing the final half of an entry.
    Value * symOffset = b->CreateSub(symLength, lg.HALF_LENGTH);

    // Build up a single encoded value for table lookup from the hashcode sequence.
    Value * symCodewordVal = b->CreateAnd(symHashValue, lg.LAST_SUFFIX_MASK);
    Value * symHashcodePos = symMarkPos;
    // symCodewordVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(symCodewordVal, sz_ONE), b->CreateShl(symCodewordVal, sz_ONE)),
    //                               symCodewordVal);
    for (unsigned j = 1; j < lg.groupInfo.encoding_bytes - 1; j++) {
        symHashcodePos = b->CreateSub(symHashcodePos, sz_ONE);
        Value * symSuffixByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", symHashcodePos)), sizeTy);
        symCodewordVal = b->CreateShl(symCodewordVal, lg.HASH_SHIFT_BITS);
        symCodewordVal = b->CreateOr(symCodewordVal, b->CreateAnd(symSuffixByte, lg.SUFFIX_MASK));
    }
    // add PREFIX_LENGTH_MASK bits for larger index space
    symHashcodePos = b->CreateSub(symHashcodePos, sz_ONE);
    Value * symPfxByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", symHashcodePos)), sizeTy);
    symPfxByte = b->CreateTrunc(b->CreateAnd(symPfxByte, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    // symCodewordVal = b->CreateOr(b->CreateAnd(symCodewordVal, lg.EXTRA_BITS_MASK), b->CreateShl(symCodewordVal, lg.EXTRA_BITS));

    Value * symSubTablePtr = b->CreateGEP(globalHashTableBasePtr, b->CreateMul(b->CreateSub(symLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    Value * symTableIdxHash = b->CreateAnd(symCodewordVal, lg.TABLE_MASK, "tableIdx");
    Value * symIdxPtr = b->CreateGEP(symSubTablePtr, b->CreateMul(symTableIdxHash, symLength));
    Value * symTblEntryPtr = b->CreateInBoundsGEP(symIdxPtr, sz_ZERO);
    // Use two 8-byte loads to get hash and symbol values.
    Value * symTblPtr1 = b->CreateBitCast(symTblEntryPtr, lg.halfSymPtrTy);
    Value * symTblPtr2 = b->CreateBitCast(b->CreateGEP(symTblEntryPtr, symOffset), lg.halfSymPtrTy);
    Value * symPtr11 = b->CreateBitCast(b->getRawInputPointer("byteData", symStartPos), lg.halfSymPtrTy);
    Value * symPtr22 = b->CreateBitCast(b->getRawInputPointer("byteData", b->CreateAdd(symStartPos, symOffset)), lg.halfSymPtrTy);
    // Check to see if the hash table entry is nonzero (already assigned).
    Value * sym11 = b->CreateAlignedLoad(symPtr11, 1);
    Value * sym22 = b->CreateAlignedLoad(symPtr22, 1);
    Value * entry11 = b->CreateMonitoredScalarFieldLoad("hashTable", symTblPtr1);
    Value * entry22 = b->CreateMonitoredScalarFieldLoad("hashTable", symTblPtr2);

    Value * symIsEqEntry1 = b->CreateAnd(b->CreateICmpEQ(entry11, sym11), b->CreateICmpEQ(entry22, sym22));
    b->CreateCondBr(symIsEqEntry1, checkSymCompression, nextSym);
#if 0
        // update pfx byte to 0
        // Value * condCheck = b->CreateICmpEQ(symHashValue, b->getSize(0xda3));
        // b->CreateCondBr(condCheck, printPhrase, proceed);
        // b->SetInsertPoint(printPhrase);
        // b->CreateWriteCall(b->getInt32(STDOUT_FILENO), symPtr1, keyLength);
        // b->CallPrintInt("tableIdxHash", tableIdxHash);
        // b->CallPrintInt("keyLength", keyLength);
        // b->CallPrintInt("symTableIdxHash", symTableIdxHash);
        // b->CallPrintInt("symHashValue", symHashValue);
        // b->CallPrintInt("(b->CreateAnd(symHashValue, b->getSize(0xFF7F)", b->CreateAnd(symHashValue, b->getSize(0xFF7F)));
        // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr11, symLength);
        // b->CreateBr(proceed);
        // b->SetInsertPoint(proceed);
#endif
#if 0
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr11, symLength);
    // b->CallPrintInt("symHashValue", symHashValue);
    // b->CallPrintInt("symLength", symLength);
    // b->CallPrintInt("symTableIdxHashSH", symTableIdxHashSH);
    // b->CallPrintInt("b->CreateZExtOrTrunc(b->CreateOr(symHashValue, b->getSize(0x80)), b->getInt16Ty())", b->CreateZExtOrTrunc(b->CreateOr(symHashValue, b->getSize(0x80)), b->getInt16Ty()));
    // b->CallPrintInt("b->CreateOr(symHashValue, b->getSize(0x80)", b->CreateOr(symHashValue, b->getSize(0x80)));
#endif

    b->SetInsertPoint(checkSymCompression);
    // Mark the last bit of phrase
    Value * overlapConditionCheck = b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE);
    Value * startBase = b->CreateSub(symStartPos, b->CreateURem(symStartPos, b->getSize(8)));
    Value * offset = b->CreateSub(symStartPos, startBase);
    Value * symLenMask = b->CreateSub(b->CreateShl(sz_ONE, symLength), sz_ONE);
    symLenMask = b->CreateShl(symLenMask, offset);
    Value * const outputMarkBasePtr = b->CreateBitCast(b->getRawOutputPointer("hashMarks", startBase), sizeTy->getPointerTo());
    Value * initialOutputMark = b->CreateAlignedLoad(outputMarkBasePtr, 1);

    b->CreateCondBr(b->CreateAnd(overlapConditionCheck, b->CreateICmpULT(b->getSize(mGroupNo), b->getSize(3))),
                    compareOverlappingSymWithinAndAcrossGroups, compareOverlappingSymInLastGroup);

    b->SetInsertPoint(compareOverlappingSymWithinAndAcrossGroups); //CHECKS: no cmpMark should exist between phrase start and end marks

    Value * const cmpMarkBasePtr = b->CreateBitCast(b->getRawInputPointer("cmpMarksSoFar", startBase), sizeTy->getPointerTo());
    Value * initialCmpMark = b->CreateAlignedLoad(cmpMarkBasePtr, 1);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr11, symLength);
    // b->CallPrintInt("symHashValue", symHashValue);
    // b->CallPrintInt("initialCmpMark-orig", initialCmpMark);
    // b->CallPrintInt("initialOutputMark-orig", initialOutputMark);
    // b->CallPrintInt("symMarkPos", symMarkPos);
    // b->CallPrintInt("b->CreateURem(symMarkPos, sz_BITS)", b->CreateURem(symMarkPos, sz_BITS));
    // b->CallPrintInt("markBase", markBase);
    // b->CallPrintInt("offset", offset);
    // b->CallPrintInt("symLength", symLength);
    // b->CallPrintInt("symLenMask", symLenMask);

    Value * cmpMarkUpdated = b->CreateAnd(initialCmpMark, symLenMask);
    Value * outputMarkUpdated = b->CreateAnd(initialOutputMark, symLenMask);
    // b->CallPrintInt("cmpMarkUpdated", cmpMarkUpdated);
    // b->CallPrintInt("outputMarkUpdated", outputMarkUpdated);

    // b->CallPrintInt("ifSymNotEliminated", b->CreateOr(cmpMarkUpdated, outputMarkUpdated));
    Value * ifSymNotEliminated = b->CreateOr(initialCmpMark, initialOutputMark);
    b->CreateCondBr(b->CreateICmpEQ(ifSymNotEliminated, sz_ZERO), markSymCompression, nextSym);

    b->SetInsertPoint(compareOverlappingSymInLastGroup);
    Value * outputMarkUpdatedLastGroup = b->CreateAnd(initialOutputMark, symLenMask);
    b->CreateCondBr(b->CreateICmpEQ(outputMarkUpdatedLastGroup, sz_ZERO), markSymCompression, nextSym);

    b->SetInsertPoint(markSymCompression);
    // Mark the last bit of phrase
    Value * phraseMarkBase = b->CreateSub(symMarkPos, b->CreateURem(symMarkPos, sz_BITS));
    Value * markOffset = b->CreateSub(symMarkPos, phraseMarkBase);
    Value * const phraseMarkBasePtr = b->CreateBitCast(b->getRawOutputPointer("hashMarks", phraseMarkBase), sizeTy->getPointerTo());
    Value * initialMark = b->CreateAlignedLoad(phraseMarkBasePtr, 1);
    Value * updatedMask = b->CreateOr(initialMark, b->CreateShl(sz_ONE, markOffset));
    b->CreateAlignedStore(updatedMask, phraseMarkBasePtr, 1);
    b->CreateBr(nextSym);

    b->SetInsertPoint(nextSym);
    Value * dropSym = b->CreateResetLowestBit(theSymWord);
    Value * thisSymWordDone = b->CreateICmpEQ(dropSym, sz_ZERO);
    // There may be more syms in the sym mask.
    Value * nextSymMask = b->CreateSelect(thisSymWordDone, b->CreateResetLowestBit(symMaskPhi), symMaskPhi);
    BasicBlock * currentBB1 = b->GetInsertBlock();
    symMaskPhi->addIncoming(nextSymMask, currentBB1);
    symWordPhi->addIncoming(dropSym, currentBB1);
    b->CreateCondBr(b->CreateICmpNE(nextSymMask, sz_ZERO), symProcessingLoop, subStridePhrasesDone);

    b->SetInsertPoint(subStridePhrasesDone);
    step2subStrideNo->addIncoming(step2nextSubStrideNo, subStridePhrasesDone);
    b->CreateCondBr(b->CreateICmpNE(step2nextSubStrideNo, totalSubStrides), symProcessingPrep, symsDone);

    b->SetInsertPoint(symsDone);
    b->setScalarField("segIndex", b->CreateAdd(sz_ONE, b->getScalarField("segIndex")));
    b->setScalarField("absBlocksProcessed", b->CreateUDiv(lfPos, sz_BLOCKWIDTH));
    Value * segProcessed = b->CreateSub(lfPos, totalProcessed);
    strideNo->addIncoming(nextStrideNo, symsDone);
    Value * hashTableSz = b->getSize((mEncodingScheme.byLength[mGroupNo].hi * phraseHashSubTableSize(mEncodingScheme, mGroupNo)) * (mEncodingScheme.byLength[mGroupNo].hi - mEncodingScheme.byLength[mGroupNo].lo + 1));
    Value * freqTableSz = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo) * (mEncodingScheme.byLength[mGroupNo].hi - mEncodingScheme.byLength[mGroupNo].lo + 1));
    b->CreateMemZero(hashTableBasePtr, hashTableSz);
    b->CreateMemZero(freqTableBasePtr, freqTableSz);
    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), stridePrologue, stridesDone);
    b->SetInsertPoint(stridesDone);

    // Although we have written the last block mask, we do not include it as
    // produced, because we may need to update it in the event that there is
    // a compressible symbol starting in this segment and finishing in the next.
    Value * producedBlocks = b->CreateUDiv(lfPos, sz_BLOCKWIDTH);
    Value * produced = b->CreateSelect(b->isFinal(), avail, b->CreateMul(producedBlocks, sz_BLOCKWIDTH));
    b->setProducedItemCount("hashMarks", produced);
    b->setProducedItemCount("hashValuesUpdated", produced);
    Value * processed = b->CreateSelect(b->isFinal(), avail, b->CreateMul(producedBlocks, sz_BLOCKWIDTH));
    b->setProcessedItemCount("symEndMarks", processed);
    b->setProcessedItemCount("cmpMarksSoFar", processed);
    b->setProcessedItemCount("hashValues", processed);
    b->setProcessedItemCount("byteData", processed);
#ifdef PRINT_HT_STATS_MARK_REPEATED_HASHVAL
    Value * const numSubTables = b->CreateMul(lg.PHRASE_SUBTABLE_SIZE,
                                              b->CreateAdd(b->CreateSub(lg.HI, lg.LO), sz_ONE));
    b->CallPrintInt("groupNo", b->getSize(mGroupNo));
    // b->CreateCondBr(b->CreateAnd(b->isFinal(), b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE)), printHTusage, goToNextStride);
    b->CreateCondBr(b->isFinal(), printHTusage, goToNextStride);
    b->SetInsertPoint(printHTusage);
    PHINode * subTblIdx = b->CreatePHI(sizeTy, 2);
    subTblIdx->addIncoming(sz_ZERO, stridesDone);
    Value * nextSubTblIdx = b->CreateAdd(subTblIdx, lg.PHRASE_SUBTABLE_SIZE);
    Value * keyLen = b->CreateAdd(lg.LO, b->CreateUDiv(subTblIdx, lg.PHRASE_SUBTABLE_SIZE));
    Value * phraseHashSubTableSize = lg.PHRASE_SUBTABLE_SIZE;
    Value * subTblEntryPtr = b->CreateGEP(globalHashTableBasePtr, subTblIdx);

    b->CallPrintInt("subTblIdx", subTblIdx);
    b->CallPrintInt("nextSubTblIdx", nextSubTblIdx);
    b->CallPrintInt("phraseHashSubTableSize", phraseHashSubTableSize);
    b->CallPrintInt("keyLen", keyLen);
    b->CreateBr(iterateSubTbl);

    b->SetInsertPoint(iterateSubTbl);
    PHINode * idx = b->CreatePHI(sizeTy, 2);
    idx->addIncoming(sz_ZERO, printHTusage);
    Value * nextIdx = b->CreateAdd(idx, keyLen);
    Value * idxTblEntryPtr = b->CreateInBoundsGEP(subTblEntryPtr, idx);
    Value * idxTblPtr1 = b->CreateBitCast(idxTblEntryPtr, b->getInt8PtrTy());
    Value * idxEntry1 = b->CreateMonitoredScalarFieldLoad("hashTable", idxTblPtr1);
    Value * idxEntryEmpty = b->CreateICmpEQ(idxEntry1, Constant::getNullValue(b->getInt8Ty()));
    b->CreateCondBr(idxEntryEmpty, printIdx, checkNextIdx);

    b->SetInsertPoint(printIdx);
    b->CallPrintInt("idx", idx);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), idxTblPtr1, keyLen);
    b->CreateBr(checkNextIdx);

    b->SetInsertPoint(checkNextIdx);
    idx->addIncoming(nextIdx, checkNextIdx);
    // b->CallPrintInt("nextIdx", nextIdx);
    b->CreateCondBr(b->CreateICmpULT(nextIdx, phraseHashSubTableSize), iterateSubTbl, goToNextSubTbl);

    b->SetInsertPoint(goToNextSubTbl);
    subTblIdx->addIncoming(nextSubTblIdx, goToNextSubTbl);
    b->CreateCondBr(b->CreateICmpNE(nextSubTblIdx, numSubTables), printHTusage, goToNextStride);

    b->SetInsertPoint(goToNextStride);
#endif
    b->CreateCondBr(b->isFinal(), hashMarksDone, updatePending);
    b->SetInsertPoint(updatePending);
    Value * pendingPtr = b->CreateBitCast(b->getRawOutputPointer("hashMarks", produced), bitBlockPtrTy);
    Value * lastMask = b->CreateBlockAlignedLoad(pendingPtr);
    b->setScalarField("pendingMaskInverted", b->CreateNot(lastMask));
    b->CreateBr(hashMarksDone);
    b->SetInsertPoint(hashMarksDone);
    // b->CallPrintInt("mGroupNo", b->getSize(mGroupNo));
    // b->CallPrintInt("sz_HALF_TBL_IDX", sz_HALF_TBL_IDX);
    // b->CallPrintInt("hashTableSz", hashTableSz);
    // b->CallPrintInt("freqTableSz", freqTableSz);
}

// ensure each segment processes only full lines. Next segment starts after the last segment's last line.
SymbolGroupCompression::SymbolGroupCompression(BuilderRef b,
                                               unsigned plen,
                                               EncodingInfo encodingScheme,
                                               unsigned numSyms,
                                               unsigned groupNo,
                                               unsigned offset,
                                               StreamSet * lfData,
                                               StreamSet * symbolMarks,
                                               StreamSet * hashValues,
                                               StreamSet * const byteData,
                                               StreamSet * compressionMask,
                                               StreamSet * encodedBytes,
                                               StreamSet * codewordMask,
                                               unsigned strideBlocks)
: MultiBlockKernel(b, "SymbolGroupCompression" + std::to_string(numSyms) + std::to_string(groupNo) + lengthGroupSuffix(encodingScheme, groupNo) + std::to_string(plen),
                   {Binding{"lfPos", lfData, FixedRate(ProcessingRate::Rational{1, 1048576})},
                    Binding{"symbolMarks", symbolMarks, BoundedRate(0, 1)},
                    Binding{"hashValues", hashValues, BoundedRate(0, 1)},
                    Binding{"byteData", byteData, BoundedRate(0, 1)}},
                   {}, {}, {},
                   {InternalScalar{b->getBitBlockType(), "pendingMaskInverted"},
                    InternalScalar{b->getBitBlockType(), "pendingPhraseMask"},
                    InternalScalar{b->getSizeTy(), "segIndex"},
                    InternalScalar{b->getSizeTy(), "absBlocksProcessed"},
                    InternalScalar{b->getSizeTy(), "lastLfPos"},
                    InternalScalar{ArrayType::get(ArrayType::get(ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), phraseHashSubTableSize(encodingScheme, groupNo)), 
+                                  (encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1)), "hashTable"}}),
mEncodingScheme(encodingScheme), mGroupNo(groupNo), mNumSym(numSyms), mSubStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS)), mOffset(offset) {
    if (DelayedAttributeIsSet()) {
        mOutputStreamSets.emplace_back("compressionMask", compressionMask, FixedRate(), Delayed(1048576) );
        mOutputStreamSets.emplace_back("encodedBytes", encodedBytes, FixedRate(), Delayed(1048576) );
        mOutputStreamSets.emplace_back("codewordMask", codewordMask, FixedRate(), Delayed(1048576) );
    } else {
        mOutputStreamSets.emplace_back("compressionMask", compressionMask, BoundedRate(0,1));
        mOutputStreamSets.emplace_back("encodedBytes", encodedBytes, BoundedRate(0,1));
        addInternalScalar(ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), "pendingOutput");
    }
    setStride(1048576);
}

void SymbolGroupCompression::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    ScanWordParameters sw(b, mStride);
    LengthGroupParameters lg(b, mEncodingScheme, mGroupNo, mNumSym);
    Constant * sz_DELAYED = b->getSize(mEncodingScheme.maxSymbolLength());
    Constant * sz_STRIDE = b->getSize(mStride);
    Constant * sz_SUB_STRIDE = b->getSize(mSubStride);
    Constant * sz_BLOCKS_PER_STRIDE = b->getSize(mStride/b->getBitBlockWidth());
    Constant * sz_BLOCKS_PER_SUB_STRIDE = b->getSize(mSubStride/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_BITS = b->getSize(SIZE_T_BITS);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    // Constant * sz_PLEN = b->getSize(mPlen);
    Constant * sz_PHRASE_LEN_OFFSET = b->getSize(mOffset);
    Value * sz_HALF_TBL_IDX = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo) / 2);
    Value * sz_HALF_TBL_IDX_0 = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo) / 3);
    Value * checkGroupNum = b->CreateICmpUGT(b->getSize(mGroupNo), sz_ZERO);
    sz_HALF_TBL_IDX = b->CreateSelect(checkGroupNum, sz_HALF_TBL_IDX, sz_HALF_TBL_IDX_0);
    checkGroupNum = b->CreateICmpEQ(b->getSize(mGroupNo), b->getSize(3));
    sz_HALF_TBL_IDX = b->CreateSelect(checkGroupNum, sz_ZERO, sz_HALF_TBL_IDX);

    assert ((mStride % mSubStride) == 0);
    Value * totalSubStrides =  b->getSize(mStride / mSubStride);

    Type * sizeTy = b->getSizeTy();
    Type * bitBlockPtrTy = b->getBitBlockType()->getPointerTo();
    Type * phraseType = ArrayType::get(b->getInt8Ty(), mEncodingScheme.byLength[mGroupNo].hi);

    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const stridePrologue = b->CreateBasicBlock("stridePrologue");
    BasicBlock * const subStrideMaskPrep = b->CreateBasicBlock("subStrideMaskPrep");
    BasicBlock * const strideMasksReady = b->CreateBasicBlock("strideMasksReady");
    BasicBlock * const keyProcessingLoop = b->CreateBasicBlock("keyProcessingLoop");
    BasicBlock * const storeKey = b->CreateBasicBlock("storeKey");
    BasicBlock * const markCompression = b->CreateBasicBlock("markCompression");
    BasicBlock * const nextKey = b->CreateBasicBlock("nextKey");
    BasicBlock * const keysDone = b->CreateBasicBlock("keysDone");
    BasicBlock * const subStridePhrasesDone = b->CreateBasicBlock("subStridePhrasesDone");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const updatePending = b->CreateBasicBlock("updatePending");
    BasicBlock * const compressionMaskDone = b->CreateBasicBlock("compressionMaskDone");
    BasicBlock * const processKey = b->CreateBasicBlock("processKey");
    // FOR DEBUGGING ONLY
    BasicBlock * const printPhrase = b->CreateBasicBlock("printPhrase");
    BasicBlock * const proceed = b->CreateBasicBlock("proceed");

#ifdef PRINT_HT_STATS
    BasicBlock * const printHTusage = b->CreateBasicBlock("printHTusage");
    BasicBlock * const iterateSubTbl = b->CreateBasicBlock("iterateSubTbl");
    BasicBlock * const goToNextSubTbl = b->CreateBasicBlock("goToNextSubTbl");
    BasicBlock * const goToNextStride = b->CreateBasicBlock("goToNextStride");
    BasicBlock * const printIdx = b->CreateBasicBlock("printIdx");
    BasicBlock * const checkNextIdx = b->CreateBasicBlock("checkNextIdx");
#endif

#ifdef PRINT_PHRASE_DEBUG_INFO
    // BasicBlock * const writeDebugOutput = b->CreateBasicBlock("writeDebugOutput");
    // BasicBlock * const writeDebugOutput1 = b->CreateBasicBlock("writeDebugOutput1");
    // BasicBlock * const dontWriteDebugOutput = b->CreateBasicBlock("dontWriteDebugOutput");
#endif
    Value * const initialPos = b->getProcessedItemCount("symbolMarks");
    Value * const avail = b->getAvailableItemCount("symbolMarks");
    Value * const initialProduced = b->getProducedItemCount("compressionMask");
    Value * const phrasesProduced = b->getProducedItemCount("codewordMask");

    Value * const processedBlocks = b->getScalarField("absBlocksProcessed");
    Value * const actualProcessed = b->CreateMul(processedBlocks, sz_BLOCKWIDTH);
    Value * pendingPhraseMask = b->getScalarField("pendingPhraseMask");
    Value * phrasesProducedPtr = b->CreateBitCast(b->getRawOutputPointer("codewordMask", actualProcessed), bitBlockPtrTy);
    b->CreateStore(pendingPhraseMask, phrasesProducedPtr);
    Value * pendingMask = b->CreateNot(b->getScalarField("pendingMaskInverted"));
    Value * producedPtr = b->CreateBitCast(b->getRawOutputPointer("compressionMask", actualProcessed), bitBlockPtrTy);
    b->CreateStore(pendingMask, producedPtr);
    Value * phraseMaskPtr = b->CreateBitCast(b->getRawOutputPointer("codewordMask", actualProcessed), bitBlockPtrTy);
    Value * compressMaskPtr = b->CreateBitCast(b->getRawOutputPointer("compressionMask", actualProcessed), bitBlockPtrTy);
    Value * hashTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("hashTable"), b->getInt8PtrTy());
    if (!DelayedAttributeIsSet()) {
        // Copy pending output data.
        Value * const initialProduced1 = b->getProducedItemCount("encodedBytes");
        b->CreateMemCpy(b->getRawOutputPointer("encodedBytes", initialProduced1), b->getScalarFieldPtr("pendingOutput"), sz_DELAYED, 1);
    }
    // Copy all new input to the output buffer; this will be then
    // overwritten when and as necessary for decompression of ZTF codes.
    b->CreateBr(stridePrologue);

    b->SetInsertPoint(stridePrologue);
    // Set up the loop variables as PHI nodes at the beginning of each stride.
    PHINode * const strideNo = b->CreatePHI(sizeTy, 2);
    strideNo->addIncoming(sz_ZERO, entryBlock);
    Value * nextStrideNo = b->CreateAdd(strideNo, sz_ONE);

    Value * const curIdx = b->getScalarField("segIndex");
    Value * lfPosPtr = b->CreateBitCast(b->getRawInputPointer("lfPos", curIdx), b->getSizeTy()->getPointerTo());
    Value * lfPos = b->CreateAlignedLoad(lfPosPtr, 1);

    Value * toCopy = b->CreateSub(lfPos, b->getScalarField("lastLfPos"));
    Value * memCpyPos = b->CreateAdd(b->getScalarField("lastLfPos"), sz_ONE);
    b->CreateMemCpy(b->getRawOutputPointer("encodedBytes", memCpyPos), b->getRawInputPointer("byteData", memCpyPos), toCopy, 1); 

    Value * totalProcessed = b->CreateMul(b->getScalarField("absBlocksProcessed"), sz_BLOCKWIDTH);
    Value * stridePos =  totalProcessed;
    Value * strideBlockOffset = b->getScalarField("absBlocksProcessed");
    Value * processBeforeThisPos = lfPos;
    Value * processAfterThisPos = b->getScalarField("lastLfPos");
    b->CreateBr(subStrideMaskPrep);

    b->SetInsertPoint(subStrideMaskPrep);
    PHINode * const subStrideNo = b->CreatePHI(sizeTy, 2);
    subStrideNo->addIncoming(sz_ZERO, stridePrologue);
    Value * nextSubStrideNo = b->CreateAdd(subStrideNo, sz_ONE);
    Value * subStridePos = b->CreateAdd(stridePos, b->CreateMul(subStrideNo, sz_SUB_STRIDE));
    Value * subStrideBlockOffset = b->CreateAdd(strideBlockOffset,
                                             b->CreateMul(subStrideNo, sz_BLOCKS_PER_SUB_STRIDE));

    ///TODO: optimize if there are no hashmarks in the keyMasks stream
    std::vector<Value *> keyMasks = initializeCompressionMasks(b, sw, sz_BLOCKS_PER_SUB_STRIDE, 1, subStrideBlockOffset, compressMaskPtr, phraseMaskPtr, strideMasksReady);
    Value * keyMask = keyMasks[0];

    b->SetInsertPoint(strideMasksReady);
    // Iterate through key symbols and update the hash table as appropriate.
    // As symbols are encountered, the hash value is retrieved from the
    // hashValues stream.   There are then three possibilities:
    //   1.  The hashTable has no entry for this hash value.
    //       In this case, the current symbol is copied into the table.
    //   2.  The hashTable has an entry for this hash value, and
    //       that entry is equal to the current symbol.    Mark the
    //       symbol for compression.
    //   3.  The hashTable has an entry for this hash value, but
    //       that entry is not equal to the current symbol.    Skip the
    //       symbol.
    //
    subStrideBlockOffset = b->CreateSub(subStrideBlockOffset, processedBlocks); // relative block offset
    Value * keyWordBasePtr = b->getInputStreamBlockPtr("symbolMarks", sz_ZERO, subStrideBlockOffset);
    keyWordBasePtr = b->CreateBitCast(keyWordBasePtr, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(keyMask, sz_ZERO), subStridePhrasesDone, keyProcessingLoop);

    b->SetInsertPoint(keyProcessingLoop);
    PHINode * const keyMaskPhi = b->CreatePHI(sizeTy, 2);
    keyMaskPhi->addIncoming(keyMask, strideMasksReady);
    PHINode * const keyWordPhi = b->CreatePHI(sizeTy, 2);
    keyWordPhi->addIncoming(sz_ZERO, strideMasksReady);
    Value * keyWordIdx = b->CreateCountForwardZeroes(keyMaskPhi, "keyWordIdx");
    Value * nextKeyWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(keyWordBasePtr, keyWordIdx)), sizeTy);
    Value * theKeyWord = b->CreateSelect(b->CreateICmpEQ(keyWordPhi, sz_ZERO), nextKeyWord, keyWordPhi);
    Value * keyWordPos = b->CreateAdd(subStridePos, b->CreateMul(keyWordIdx, sw.WIDTH));
    Value * keyMarkPosInWord = b->CreateCountForwardZeroes(theKeyWord);
    Value * keyMarkPos = b->CreateAdd(keyWordPos, keyMarkPosInWord, "keyEndPos");
    Value * keyProcessCond = b->CreateAnd(b->CreateICmpULE(keyMarkPos, processBeforeThisPos), b->CreateICmpUGT(keyMarkPos, processAfterThisPos));
    b->CreateCondBr(keyProcessCond, processKey, nextKey);

    b->SetInsertPoint(processKey);
    /* Determine the key length. */
    Value * hashValue = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", keyMarkPos)), sizeTy);
    Value * hashExtBit = b->CreateAnd(hashValue, b->getSize(0x80));
    Value * keyLength = b->CreateAdd(b->CreateLShr(hashValue, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET, "keyLength");
    Value * keyStartPos = b->CreateSub(keyMarkPos, b->CreateSub(keyLength, sz_ONE), "keyStartPos");
    // keyOffset for accessing the final half of an entry.
    Value * keyOffset = b->CreateSub(keyLength, lg.HALF_LENGTH);
    // Get the hash of this key.
    // Value * keyHash = b->CreateAnd(hashValue, lg.HASH_MASK_NEW, "keyHash");
    /*
    For 2-byte codeword, extract 32-bits of hashvalue
    hi 8 bits of both 16-bits are length part -> discarded
    Hence HASH_MASK_NEW -> mask of FFFFFFFF, FFFFFFFFFFFF, FFFFFFFFFFFFFFFF for LG {0,1,2}, 3, 4 respectively.
    */
    // Build up a single encoded value for table lookup from the hashcode sequence.
    Value * codewordVal = b->CreateAnd(hashValue, lg.LAST_SUFFIX_MASK);
    // codewordVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(codewordVal, sz_ONE), b->CreateShl(codewordVal, sz_ONE)),
    //                               codewordVal);
    Value * hashcodePos = keyMarkPos;
#ifdef PRINT_DICT_ONLY
    Value * writtenVal = b->CreateAdd(lg.LAST_SUFFIX_BASE, b->CreateAnd(hashValue, lg.LAST_SUFFIX_MASK));;
#endif
    // codewordVal = b->CreateShl(codewordVal, lg.LAST_SUFFIX_SHIFT_BITS);
    for (unsigned j = 1; j < lg.groupInfo.encoding_bytes - 1/* + mNumSym*/; j++) { // same # encoding_bytes for k-sym phrases
        hashcodePos = b->CreateSub(hashcodePos, sz_ONE);
        Value * suffixByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", hashcodePos)), sizeTy);
        codewordVal = b->CreateShl(codewordVal, lg.HASH_SHIFT_BITS);
        codewordVal = b->CreateOr(codewordVal, b->CreateAnd(suffixByte, lg.SUFFIX_MASK));
#ifdef PRINT_DICT_ONLY
        writtenVal = b->CreateOr(b->CreateShl(writtenVal, lg.MAX_HASH_BITS), b->CreateAnd(suffixByte, lg.SUFFIX_MASK));
#endif
    }
    // add PREFIX_LENGTH_MASK bits for larger index space
    hashcodePos = b->CreateSub(hashcodePos, sz_ONE);
    Value * pfxByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", hashcodePos)), sizeTy);

    pfxByte = b->CreateTrunc(b->CreateAnd(pfxByte, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    Value * extBit = b->CreateLShr(hashExtBit, b->getSize(7));
#ifdef PRINT_DICT_ONLY
    pfxByte = b->CreateSelect(b->CreateICmpEQ(b->CreateAnd(extBit, sz_ONE), sz_ONE),
                                  b->CreateOr(pfxByte, sz_ONE),
                                  b->CreateAnd(pfxByte, b->getSize(0x6)));
    pfxByte = b->CreateTrunc(pfxByte, b->getInt64Ty());
    Value * lgthBase1 = b->CreateSub(keyLength, lg.LO);
    Value * pfxOffset1 = b->CreateAdd(lg.PREFIX_BASE, lgthBase1);
    Value * multiplier1 = b->CreateMul(lg.RANGE, pfxByte);
    Value * ZTF_prefix1 = b->CreateAdd(pfxOffset1, multiplier1);
#endif
    Value * subTablePtr = b->CreateGEP(hashTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    // codewordVal = b->CreateOr(b->CreateAnd(codewordVal, lg.EXTRA_BITS_MASK), b->CreateShl(codewordVal, lg.EXTRA_BITS));
    /// TODO: experiment the number of bits in sz_TABLEMASK
    Value * tableIdxHash = b->CreateAnd(codewordVal, lg.TABLE_MASK, "tableIdx");
    Value * tableIdxHashOld = tableIdxHash;
    // tableIdxHash = b->CreateSelect(b->CreateAnd(b->CreateICmpULT(tableIdxHash, sz_HALF_TBL_IDX), b->CreateICmpEQ(extBit, sz_ONE)),
    //                                b->CreateAdd(sz_HALF_TBL_IDX, tableIdxHash), tableIdxHash);
    // b->CallPrintInt("keyLength", keyLength);
    // b->CallPrintInt("hashValue", hashValue);
    Value * keyIdxPtr = b->CreateGEP(subTablePtr, b->CreateMul(tableIdxHash, keyLength));
    Value * tblEntryPtr = b->CreateInBoundsGEP(keyIdxPtr, sz_ZERO);
    // Use two 8-byte loads to get hash and symbol values.
    Value * tblPtr1 = b->CreateBitCast(tblEntryPtr, lg.halfSymPtrTy);
    Value * tblPtr2 = b->CreateBitCast(b->CreateGEP(tblEntryPtr, keyOffset), lg.halfSymPtrTy);
    Value * symPtr1 = b->CreateBitCast(b->getRawInputPointer("byteData", keyStartPos), lg.halfSymPtrTy);
    Value * symPtr2 = b->CreateBitCast(b->getRawInputPointer("byteData", b->CreateAdd(keyStartPos, keyOffset)), lg.halfSymPtrTy);
    // Check to see if the hash table entry is nonzero (already assigned).
    Value * sym1 = b->CreateAlignedLoad(symPtr1, 1);
    Value * sym2 = b->CreateAlignedLoad(symPtr2, 1);
    Value * entry1 = b->CreateMonitoredScalarFieldLoad("hashTable", tblPtr1);
    Value * entry2 = b->CreateMonitoredScalarFieldLoad("hashTable", tblPtr2);
/*
    All the marked symMarks indicate hashMarks for only repeated phrases.
    Among those marks,
    1. If any symbol is being seen for the first time and has no hash table entry, store that hashcode in the hashtable
    and mark its compression mask.
    2. If the hashcode exists in the hashtable but the current phrase and hash table entry do not match, go to next symbol.
*/
    Value * symIsEqEntry = b->CreateAnd(b->CreateICmpEQ(entry1, sym1), b->CreateICmpEQ(entry2, sym2));
    b->CreateCondBr(symIsEqEntry, markCompression, storeKey);

    // replace any colliding phrase; it'll be the new frequent phrase
    b->SetInsertPoint(storeKey);
#ifdef PRINT_DICT_ONLY
    // b->CallPrintInt("strideNo", strideNo);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength);
    writtenVal = b->CreateOr(b->CreateShl(writtenVal, lg.MAX_HASH_BITS), ZTF_prefix1, "writtenVal");
    Value * const copyLen = b->CreateAdd(lg.ENC_BYTES, sz_ZERO);
    Value * outputCodeword = b->CreateAlloca(b->getInt64Ty(), copyLen);
    b->CreateAlignedStore(writtenVal, outputCodeword, 1);
    // b->CreateWriteCall(b->getInt32(STDOUT_FILENO), outputCodeword, copyLen);
    b->CallPrintInt("hashValue", hashValue);
    b->CallPrintInt("writtenVal", writtenVal);
    b->CallPrintInt("pfxOffset1", pfxOffset1);
    b->CallPrintInt("multiplier1", multiplier1);
    b->CallPrintInt("ZTF_prefix1", ZTF_prefix1);
    b->CallPrintInt("hashExtBit", hashExtBit);
    b->CallPrintInt("extBit", extBit);
    b->CallPrintInt("b->CreateICmpEQ(b->CreateAnd(extBit, sz_ONE), sz_ONE)", b->CreateICmpEQ(b->CreateAnd(extBit, sz_ONE), sz_ONE));
    b->CallPrintInt("b->CreateOr(pfxByte, sz_ONE)", b->CreateOr(pfxByte, sz_ONE));
    b->CallPrintInt("b->CreateTrunc(b->CreateAnd(pfxByte, lg.PREFIX_LENGTH_MASK), b->getInt64Ty())", b->CreateTrunc(b->CreateAnd(pfxByte, lg.PREFIX_LENGTH_MASK), b->getInt64Ty()));
    b->CallPrintInt("b->CreateTrunc(pfxByte, b->getInt64Ty())", b->CreateTrunc(pfxByte, b->getInt64Ty()));
    b->CallPrintInt("tableIdxHash", tableIdxHash);
    b->CallPrintInt("keyLength", keyLength);
    b->CallPrintInt("mNumSym", b->getSize(mNumSym));
    // b->CallPrintInt("phraseWordPos", keyWordPos);
    // b->CallPrintInt("phraseMarkPosInWord", keyMarkPosInWord);
    // b->CallPrintInt("phraseMarkPosFinal", keyMarkPos);
#endif

    // Mark the last byte of phrase -> subtract 1 from keyMarkPos for safe markPos calculation
    Value * phraseEndPos = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE), sz_ZERO, sz_ONE);
    Value * phraseMarkBase = b->CreateSub(b->CreateSub(keyMarkPos, phraseEndPos), b->CreateURem(b->CreateSub(keyMarkPos, phraseEndPos), sz_BITS));
    Value * markOffset = b->CreateSub(b->CreateSub(keyMarkPos, phraseEndPos), phraseMarkBase);
    Value * const codewordMaskBasePtr = b->CreateBitCast(b->getRawOutputPointer("codewordMask", phraseMarkBase), sizeTy->getPointerTo());
    Value * initialMark = b->CreateAlignedLoad(codewordMaskBasePtr, 1);
    Value * updatedMask = b->CreateOr(initialMark, b->CreateShl(sz_ONE, markOffset));
    b->CreateAlignedStore(updatedMask, codewordMaskBasePtr, 1);

    // We have a new symbol that allows future occurrences of the symbol to
    // be compressed using the hash code.
    b->CreateMonitoredScalarFieldStore("hashTable", sym1, tblPtr1);
    b->CreateMonitoredScalarFieldStore("hashTable", sym2, tblPtr2);
#if 0
    b->CreateCondBr(b->CreateICmpEQ(keyLength, sz_PLEN), writeDebugOutput1, dontWriteDebugOutput);
    b->SetInsertPoint(writeDebugOutput1);
    b->CallPrintInt("keyMarkPos", keyMarkPos);
    b->CallPrintInt("markOffset", markOffset);
    b->CallPrintInt("(markOffset-1)", b->CreateSub(markOffset, sz_ONE));
    b->CallPrintInt("keyMarkPosInWord", keyMarkPosInWord);
    b->CreateBr(dontWriteDebugOutput);
    b->SetInsertPoint(dontWriteDebugOutput);
#endif

#ifdef PRINT_PHRASE_DEBUG_INFO
    // b->CreateCondBr(b->CreateICmpEQ(keyLength, sz_PLEN), writeDebugOutput, markCompression);
    // b->SetInsertPoint(writeDebugOutput);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength);
    b->CallPrintInt("keyLength", keyLength);
    b->CallPrintInt("keyMarkPos", keyMarkPos);
    b->CallPrintInt("b->CreateSub(keyMarkPos, phraseEndPos)", b->CreateSub(keyMarkPos, phraseEndPos));
#endif
    // markCompression even for the first occurrence
    b->CreateBr(markCompression);

    b->SetInsertPoint(markCompression);
    Value * condCheck = b->CreateICmpEQ(hashValue, b->getSize(0x6fa));
    b->CreateCondBr(condCheck, printPhrase, proceed);
    b->SetInsertPoint(printPhrase);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength);
    // b->CallPrintInt("hashValue", hashValue);
    // b->CallPrintInt("extBit", extBit);
    // b->CallPrintInt("hashExtBit", hashExtBit);
    // b->CallPrintInt("b->CreateICmpEQ(b->CreateAnd(extBit, sz_ONE), sz_ONE", b->CreateICmpEQ(b->CreateAnd(extBit, sz_ONE), sz_ONE));
    // b->CallPrintInt("b->CreateLShr(hashExtBit, b->getSize(7))", hashExtBit);
    // b->CallPrintInt("tableIdxHashOld", tableIdxHashOld);
    // b->CallPrintInt("tableIdxHash", tableIdxHash);
    // b->CallPrintInt("pfxLgthMask-before", b->CreateAnd(old, lg.PREFIX_LENGTH_MASK));
    // b->CallPrintInt("b->CreateOr(pfxByte, sz_ONE)", b->CreateOr(pfxByte, sz_ONE));
    // b->CallPrintInt("b->CreateAnd(pfxByte, b->getSize(0xE))", b->CreateAnd(pfxByte, b->getSize(0xE)));
    // b->CallPrintInt("pfxByte", pfxByte);
    // b->CallPrintInt("ZTF_prefix1", ZTF_prefix1);
    // b->CallPrintInt("keyLength", keyLength);
    b->CreateBr(proceed);
    b->SetInsertPoint(proceed);
    Value * maskLength = b->CreateZExt(b->CreateSub(keyLength, lg.ENC_BYTES, "maskLength"), sizeTy);
    // Compute a mask of bits, with zeroes marking positions to eliminate.
    // The entire symbols will be replaced, but we need to keep the required
    // number of positions for the encoded ZTF sequence.
    Value * mask = b->CreateSub(b->CreateShl(sz_ONE, maskLength), sz_ONE);
    // Determine a base position from which both the keyStart and the keyEnd
    // are accessible within SIZE_T_BITS - 8, and which will not overflow
    // the buffer.
    assert(SIZE_T_BITS - 8 > 2 * lg.groupHalfLength);
    Value * startBase = b->CreateSub(keyStartPos, b->CreateURem(keyStartPos, b->getSize(8)));
    Value * markBase = b->CreateSub(keyMarkPos, b->CreateURem(keyMarkPos, sz_BITS));
    Value * keyBase = b->CreateSelect(b->CreateICmpULT(startBase, markBase), startBase, markBase);
    Value * bitOffset = b->CreateSub(keyStartPos, keyBase);

    mask = b->CreateShl(mask, bitOffset);
    Value * const keyBasePtr = b->CreateBitCast(b->getRawOutputPointer("compressionMask", keyBase), sizeTy->getPointerTo());
    Value * initialMask = b->CreateAlignedLoad(keyBasePtr, 1);
    Value * updated = b->CreateAnd(initialMask, b->CreateNot(mask));
    b->CreateAlignedStore(updated, keyBasePtr, 1);
    Value * curPos = keyMarkPos;
    Value * curHash = hashValue;
    // Write the suffixes.
    Value * last_suffix = b->CreateTrunc(b->CreateAdd(lg.LAST_SUFFIX_BASE, b->CreateAnd(curHash, lg.LAST_SUFFIX_MASK, "ZTF_suffix_last")), b->getInt8Ty());
    b->CreateStore(last_suffix, b->getRawOutputPointer("encodedBytes", curPos));
    curPos = b->CreateSub(curPos, sz_ONE);
#if 0
    Value * writtenVal = b->CreateZExt(b->CreateAdd(lg.LAST_SUFFIX_BASE, b->CreateAnd(curHash, lg.LAST_SUFFIX_MASK, "ZTF_suffix_last")), sizeTy);
#endif

    for (unsigned i = 0; i < lg.groupInfo.encoding_bytes - 2; i++) {
        Value * ZTF_suffix = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", curPos)), sizeTy);
#if 0
        writtenVal = b->CreateOr(b->CreateShl(writtenVal, lg.MAX_HASH_BITS), b->CreateAnd(ZTF_suffix, lg.SUFFIX_MASK));
#endif
        b->CreateStore(b->CreateTrunc(b->CreateAnd(ZTF_suffix, lg.SUFFIX_MASK), b->getInt8Ty()), b->getRawOutputPointer("encodedBytes", curPos));
        curPos = b->CreateSub(curPos, sz_ONE);
    }
    // Now prepare the prefix - PREFIX_BASE + ... + remaining hash bits.
    /*
            3    |  0xC0-0xC7
            4    |  0xC8-0xCF
            5    |  0xD0, 0xD4, 0xD8, 0xDC
            6    |  0xD1, 0xD5, 0xD9, 0xDD
            7    |  0xD2, 0xD6, 0xDA, 0xDE
            8    |  0xD3, 0xD7, 0xDB, 0xDF
            9-16 |  0xE0 - 0xEF (3-bytes)
            17-32|  0xF0 - 0xFF (4-bytes)

                (length - lo) = row of the prefix table
            LG    RANGE         xHashBits      hashMask     numRows
            0      0               3              111          8
            1      0               3              111          8
            2      0-3             2               11          4
            3      0-7             1                1          8
            4      0-15            0                0         16
            (PFX_BASE + RANGE) + (numRows * (keyHash AND hashMask))
    */
    Value * pfxLgthMask = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", curPos)), sizeTy);
    Value * old = pfxLgthMask;
    hashExtBit = b->CreateLShr(hashExtBit, b->getSize(7));
    pfxLgthMask = b->CreateTrunc(b->CreateAnd(pfxLgthMask, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    // pfxLgthMask = b->CreateSelect(b->CreateICmpEQ(b->CreateAnd(hashExtBit, sz_ONE), sz_ZERO),
    //                               b->CreateOr(pfxLgthMask, sz_ONE),
    //                               b->CreateAnd(pfxLgthMask, b->getSize(0x6)));
    // pfxLgthMask = b->CreateTrunc(pfxLgthMask, b->getInt64Ty());
    //b->CreateTrunc(b->CreateAnd(pfxLgthMask, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    Value * lgthBase = b->CreateSub(keyLength, lg.LO);
    Value * pfxOffset = b->CreateAdd(lg.PREFIX_BASE, lgthBase);
    Value * multiplier = b->CreateMul(lg.RANGE, pfxLgthMask);
    Value * ZTF_prefix = b->CreateAdd(pfxOffset, multiplier, "ZTF_prefix");
#ifdef PRINT_DICT_ONLY
    // b->CallPrintInt("ZTF_prefix", ZTF_prefix);
#endif
    b->CreateStore(b->CreateTrunc(ZTF_prefix, b->getInt8Ty()), b->getRawOutputPointer("encodedBytes", curPos));
    b->CreateBr(nextKey);

    b->SetInsertPoint(nextKey);
    Value * dropKey = b->CreateResetLowestBit(theKeyWord);
    Value * thisWordDone = b->CreateICmpEQ(dropKey, sz_ZERO);
    // There may be more keys in the key mask.
    Value * nextKeyMask = b->CreateSelect(thisWordDone, b->CreateResetLowestBit(keyMaskPhi), keyMaskPhi);
    BasicBlock * currentBB = b->GetInsertBlock();
    keyMaskPhi->addIncoming(nextKeyMask, currentBB);
    keyWordPhi->addIncoming(dropKey, currentBB);
    b->CreateCondBr(b->CreateICmpNE(nextKeyMask, sz_ZERO), keyProcessingLoop, subStridePhrasesDone);

    b->SetInsertPoint(subStridePhrasesDone);
    subStrideNo->addIncoming(nextSubStrideNo, subStridePhrasesDone);
    b->CreateCondBr(b->CreateICmpNE(nextSubStrideNo, totalSubStrides), subStrideMaskPrep, keysDone);

    b->SetInsertPoint(keysDone);
    b->setScalarField("segIndex", b->CreateAdd(sz_ONE, b->getScalarField("segIndex")));
    b->setScalarField("absBlocksProcessed", b->CreateUDiv(lfPos, sz_BLOCKWIDTH));
    strideNo->addIncoming(nextStrideNo, keysDone);
    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), stridePrologue, stridesDone);

    b->SetInsertPoint(stridesDone);
    Value * producedBlocks = b->CreateUDiv(lfPos, sz_BLOCKWIDTH);
    // Although we have written the last block mask, we do not include it as
    // produced, because we may need to update it in the event that there is
    // a compressible symbol starting in this segment and finishing in the next.
    Value * produced = b->CreateSelect(b->isFinal(), avail, b->CreateMul(producedBlocks, sz_BLOCKWIDTH));
    b->setProducedItemCount("encodedBytes", produced);
    b->setProducedItemCount("compressionMask", produced);
    b->setProducedItemCount("codewordMask", produced);
    // b->CallPrintInt("produced", produced);
    Value * processed = b->CreateSelect(b->isFinal(), avail, b->CreateMul(producedBlocks, sz_BLOCKWIDTH));
    b->setProcessedItemCount("byteData", processed);
    b->setProcessedItemCount("symbolMarks", processed);
    b->setProcessedItemCount("hashValues", processed);

#ifdef PRINT_HT_STATS
    Value * const numSubTables = b->CreateMul(lg.PHRASE_SUBTABLE_SIZE,
                                              b->CreateAdd(b->CreateSub(lg.HI, lg.LO), sz_ONE));
    b->CallPrintInt("groupNo", b->getSize(mGroupNo));
    // b->CreateCondBr(b->CreateAnd(b->isFinal(), b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE)), printHTusage, goToNextStride);
    b->CreateCondBr(b->isFinal(), printHTusage, goToNextStride);
    b->SetInsertPoint(printHTusage);
    PHINode * subTblIdx = b->CreatePHI(sizeTy, 2);
    subTblIdx->addIncoming(sz_ZERO, stridesDone);
    Value * nextSubTblIdx = b->CreateAdd(subTblIdx, lg.PHRASE_SUBTABLE_SIZE);
    Value * keyLen = b->CreateAdd(lg.LO, b->CreateUDiv(subTblIdx, lg.PHRASE_SUBTABLE_SIZE));
    Value * phraseHashSubTableSize = lg.PHRASE_SUBTABLE_SIZE;
    Value * subTblEntryPtr = b->CreateGEP(hashTableBasePtr, subTblIdx);

    b->CallPrintInt("subTblIdx", subTblIdx);
    b->CallPrintInt("nextSubTblIdx", nextSubTblIdx);
    b->CallPrintInt("phraseHashSubTableSize", phraseHashSubTableSize);
    b->CallPrintInt("keyLen", keyLen);
    b->CreateBr(iterateSubTbl);

    b->SetInsertPoint(iterateSubTbl);
    PHINode * idx = b->CreatePHI(sizeTy, 2);
    idx->addIncoming(sz_ZERO, printHTusage);
    Value * nextIdx = b->CreateAdd(idx, keyLen);
    Value * idxTblEntryPtr = b->CreateInBoundsGEP(subTblEntryPtr, idx);
    Value * idxTblPtr1 = b->CreateBitCast(idxTblEntryPtr, b->getInt8PtrTy());
    Value * idxEntry1 = b->CreateMonitoredScalarFieldLoad("hashTable", idxTblPtr1);
    Value * idxEntryEmpty = b->CreateICmpEQ(idxEntry1, Constant::getNullValue(b->getInt8Ty()));
    b->CreateCondBr(idxEntryEmpty, checkNextIdx, printIdx);

    b->SetInsertPoint(printIdx);
    b->CallPrintInt("idx", idx);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), idxTblPtr1, keyLen);
    b->CreateBr(checkNextIdx);

    b->SetInsertPoint(checkNextIdx);
    idx->addIncoming(nextIdx, checkNextIdx);
    // b->CallPrintInt("nextIdx", nextIdx);
    b->CreateCondBr(b->CreateICmpULT(nextIdx, phraseHashSubTableSize), iterateSubTbl, goToNextSubTbl);

    b->SetInsertPoint(goToNextSubTbl);
    subTblIdx->addIncoming(nextSubTblIdx, goToNextSubTbl);
    b->CreateCondBr(b->CreateICmpNE(nextSubTblIdx, numSubTables), printHTusage, goToNextStride);

    b->SetInsertPoint(goToNextStride);
#endif

    b->CreateCondBr(b->isFinal(), compressionMaskDone, updatePending);
    b->SetInsertPoint(updatePending);
    Value * pendingPtr = b->CreateBitCast(b->getRawOutputPointer("compressionMask", produced), bitBlockPtrTy);
    Value * lastMask = b->CreateBlockAlignedLoad(pendingPtr);
    b->setScalarField("pendingMaskInverted", b->CreateNot(lastMask));
    Value * pendingCWmaskPtr = b->CreateBitCast(b->getRawOutputPointer("codewordMask", produced), bitBlockPtrTy);
    Value * lastCWMask = b->CreateBlockAlignedLoad(pendingCWmaskPtr);
    b->setScalarField("pendingPhraseMask", lastCWMask);
    b->CreateBr(compressionMaskDone);
    b->SetInsertPoint(compressionMaskDone);
}

/*
* each stride provides 1048576 items
* identify the last linebreak in every 1048576 items.
---> blockoffset is calculated based on already processed blocks in current segment (overall processed blocks stored in processedBlocks scalar)
---> processedSubBlockSizePhi to indicate processed items in the last block of last 1MB items processed where lb was found.
---> add processedSubBlockSizePhi to the lf position calculated in current stride (nextByteDataProcessed)
* set the processed items (multiple of block size) of lineBreaks
*/

/*
Try 2:
* process 1 page of data per stride.
* get mask of line segBreaks
* check the position of each line break (LB_s) in stride
* store LB_s in lastSeenLbScalar
* if (LB_s - lastSegLbPos) > 1048576,
* write lastSeenLbScalar in the output LFpartialSum
* set lastSegLbPos to lastSeenLbScalar
* update scalar index = index+1
*/
OffsetCalcKernel::OffsetCalcKernel(BuilderRef b,
                                StreamSet * LF,
                                StreamSet * LFpartialSum,
                                unsigned strideBlocks)
: MultiBlockKernel(b, "OffsetCalcKernel" +  std::to_string(strideBlocks),
                   {Binding{"lineBreaks", LF, FixedRate()}},
                   {}, {}, {},{}) {
    mOutputStreamSets.emplace_back("LFpartialSum", LFpartialSum, BoundedRate(0, 1), Add1());
    addInternalScalar(b->getSizeTy(), "index");
    addInternalScalar(b->getSizeTy(), "lastStrideLbPos");
    addInternalScalar(b->getSizeTy(), "lastSegLbPos");
    setStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS));
}
void OffsetCalcKernel::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    ScanWordParameters sw(b, mStride);
    Constant * sz_STRIDE = b->getSize(mStride);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    Constant * sz_BLOCKS_PER_STRIDE = b->getSize(mStride/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_SEGSIZE = b->getSize(1048576);
    Type * sizeTy = b->getSizeTy();

    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const stridePrologue = b->CreateBasicBlock("stridePrologue");
    BasicBlock * const strideMasksReady = b->CreateBasicBlock("strideMasksReady");
    BasicBlock * const lbProcessingLoop = b->CreateBasicBlock("lbProcessingLoop");
    BasicBlock * const writeOutput = b->CreateBasicBlock("writeOutput");
    BasicBlock * const nextLb = b->CreateBasicBlock("nextLb");
    BasicBlock * const LbDone = b->CreateBasicBlock("LbDone");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const writePending = b->CreateBasicBlock("writePending");
    BasicBlock * const lbCalcDone = b->CreateBasicBlock("lbCalcDone");

    Value * const initialPos = b->getProcessedItemCount("lineBreaks");
    Value * const avail = b->getAvailableItemCount("lineBreaks");
    b->CreateBr(stridePrologue);

    b->SetInsertPoint(stridePrologue);
    PHINode * const strideNo = b->CreatePHI(sizeTy, 2, "strideNo");
    strideNo->addIncoming(sz_ZERO, entryBlock);
    Value * nextStrideNo = b->CreateAdd(strideNo, sz_ONE);
    Value * stridePos = b->CreateAdd(initialPos, b->CreateMul(strideNo, sz_STRIDE));
    Value * strideBlockOffset = b->CreateMul(strideNo, sz_BLOCKS_PER_STRIDE);
    std::vector<Value *> lbMasks(1);
    initializeLinebreakMasks(b, sw, sz_BLOCKS_PER_STRIDE, 1, strideBlockOffset, lbMasks, strideMasksReady);
    Value * lbMask = lbMasks[0];
    b->SetInsertPoint(strideMasksReady);

    Value * lbWordBasePtr = b->getInputStreamBlockPtr("lineBreaks", sz_ZERO, strideBlockOffset);
    lbWordBasePtr = b->CreateBitCast(lbWordBasePtr, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(lbMask, sz_ZERO), LbDone, lbProcessingLoop);

    b->SetInsertPoint(lbProcessingLoop);
    PHINode * const keyMaskPhi = b->CreatePHI(sizeTy, 2);
    keyMaskPhi->addIncoming(lbMask, strideMasksReady);
    PHINode * const keyWordPhi = b->CreatePHI(sizeTy, 2);
    keyWordPhi->addIncoming(sz_ZERO, strideMasksReady);

    Value * keyWordIdx = b->CreateCountForwardZeroes(keyMaskPhi, "keyWordIdx");
    Value * nextKeyWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(lbWordBasePtr, keyWordIdx)), sizeTy);
    Value * theKeyWord = b->CreateSelect(b->CreateICmpEQ(keyWordPhi, sz_ZERO), nextKeyWord, keyWordPhi);
    Value * keyWordPos = b->CreateAdd(stridePos, b->CreateMul(keyWordIdx, sw.WIDTH));
    Value * keyMarkPosInWord = b->CreateCountForwardZeroes(theKeyWord);
    Value * lbPos = b->CreateAdd(keyWordPos, keyMarkPosInWord, "lbPos");

    Value * segLbPos = b->CreateSub(lbPos, b->getScalarField("lastSegLbPos"));
    b->CreateCondBr(b->CreateICmpUGT(segLbPos, sz_SEGSIZE), writeOutput, nextLb);

    b->SetInsertPoint(writeOutput);
    Value * const segLbPosFinal = b->getScalarField("lastStrideLbPos");
    b->CreateStore(b->CreateTrunc(b->CreateSelect(b->isFinal(), avail, segLbPosFinal), b->getInt64Ty()), b->getRawOutputPointer("LFpartialSum", b->getScalarField("index")));
    b->setScalarField("index", b->CreateAdd(sz_ONE, b->getScalarField("index")));
    b->setScalarField("lastSegLbPos", segLbPosFinal);

    b->CreateBr(nextLb);

    b->SetInsertPoint(nextLb);
    b->setScalarField("lastStrideLbPos", lbPos);
    Value * dropKey = b->CreateResetLowestBit(theKeyWord);
    Value * thisWordDone = b->CreateICmpEQ(dropKey, sz_ZERO);
    Value * nextKeyMask = b->CreateSelect(thisWordDone, b->CreateResetLowestBit(keyMaskPhi), keyMaskPhi);
    BasicBlock * currentBB = b->GetInsertBlock();
    keyMaskPhi->addIncoming(nextKeyMask, currentBB);
    keyWordPhi->addIncoming(dropKey, currentBB);
    b->CreateCondBr(b->CreateICmpNE(nextKeyMask, sz_ZERO), lbProcessingLoop, LbDone);

    b->SetInsertPoint(LbDone);
    strideNo->addIncoming(nextStrideNo, LbDone);
    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), stridePrologue, stridesDone);

    b->SetInsertPoint(stridesDone);
    b->CreateCondBr(b->isFinal(), writePending, lbCalcDone);

    b->SetInsertPoint(writePending);
    b->CreateStore(b->CreateTrunc(avail, b->getInt64Ty()), b->getRawOutputPointer("LFpartialSum", b->getScalarField("index")));
    // part of next segment's first block is already marked as processed. The prsdSubBlockSize will be added to the next segment's last LB offset
    b->setScalarField("index", b->CreateAdd(sz_ONE, b->getScalarField("index")));
    b->CreateBr(lbCalcDone);

    b->SetInsertPoint(lbCalcDone);
    b->setProducedItemCount("LFpartialSum", b->getScalarField("index"));
}

FilterCompressedData::FilterCompressedData(BuilderRef b,
                                EncodingInfo encodingScheme,
                                unsigned numSyms,
                                StreamSet * byteData,
                                StreamSet * combinedMask,
                                StreamSet * symEndMarker,
                                StreamSet * cmpBytes,
                                StreamSet * partialSum,
                                unsigned strideBlocks)
: MultiBlockKernel(b, "FilterCompressedData" +  std::to_string(strideBlocks) + "_" + std::to_string(numSyms),
                   {Binding{"phraseMask", combinedMask},
                    Binding{"symEndMarker", symEndMarker},
                    Binding{"byteData", byteData, FixedRate(), LookBehind(33)}},
                   {}, {}, {},{}),
mSubStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS)) {
    mOutputStreamSets.emplace_back("cmpBytes", cmpBytes, BoundedRate(0, 1)/*PopcountOf("phraseMask")*/);
    mOutputStreamSets.emplace_back("partialSum", partialSum, FixedRate(ProcessingRate::Rational{1, 1048576}), Delayed(1));
    setStride(1048576);
}
// use symbolEndMarks and check if accessible byte_pos > last accessible symbol_end markPos to ensure complete phrase is written 
// in a single segment
void FilterCompressedData::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    ScanWordParameters sw(b, mStride);
    Constant * sz_STRIDE = b->getSize(mStride);
    Constant * sz_SUB_STRIDE = b->getSize(mSubStride);
    Constant * sz_BLOCKS_PER_STRIDE = b->getSize(mStride/b->getBitBlockWidth());
    Constant * sz_BLOCKS_PER_SUB_STRIDE = b->getSize(mSubStride/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_EIGHT = b->getSize(8);
    assert ((mStride % mSubStride) == 0);
    Value * totalSubStrides =  b->getSize(mStride / mSubStride); // 102400/2048 with BitBlock=256
    // b->CallPrintInt("totalSubStrides", totalSubStrides);

    Type * sizeTy = b->getSizeTy();

    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const stridePrologue = b->CreateBasicBlock("stridePrologue");
    BasicBlock * const subStrideMaskPrep = b->CreateBasicBlock("subStrideMaskPrep");
    BasicBlock * const strideMasksReady = b->CreateBasicBlock("strideMasksReady");
    BasicBlock * const filteringLoop = b->CreateBasicBlock("filteringLoop");
    BasicBlock * const subStridePhrasesDone = b->CreateBasicBlock("subStridePhrasesDone");
    BasicBlock * const checkFinalLoopCond = b->CreateBasicBlock("checkFinalLoopCond");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const updatePending = b->CreateBasicBlock("updatePending");
    BasicBlock * const filteringMaskDone = b->CreateBasicBlock("filteringMaskDone");

    Value * const initialPos = b->getProcessedItemCount("phraseMask");
    Value * const initialProducedBytes = b->getProducedItemCount("cmpBytes");
    // b->CallPrintInt("initialProducedBytes", initialProducedBytes);
    // b->CallPrintInt("avail", avail);
    // b->CallPrintInt("accessible", b->getAccessibleItemCount("phraseMask"));
    b->CreateBr(stridePrologue);

    b->SetInsertPoint(stridePrologue);
    PHINode * const strideNo = b->CreatePHI(sizeTy, 2);
    strideNo->addIncoming(sz_ZERO, entryBlock);
    PHINode * const segWritePosPhi = b->CreatePHI(sizeTy, 2);
    segWritePosPhi->addIncoming(initialProducedBytes, entryBlock);
    PHINode * const segFullPhrasePos = b->CreatePHI(sizeTy, 2);
    segFullPhrasePos->addIncoming(initialProducedBytes, entryBlock);
    Value * nextStrideNo = b->CreateAdd(strideNo, sz_ONE);
    Value * stridePos = b->CreateAdd(initialPos, b->CreateMul(strideNo, sz_STRIDE));
    Value * strideBlockOffset = b->CreateMul(strideNo, sz_BLOCKS_PER_STRIDE);
    b->CreateBr(subStrideMaskPrep);

    b->SetInsertPoint(subStrideMaskPrep);
    PHINode * const subStrideNo = b->CreatePHI(sizeTy, 2);
    subStrideNo->addIncoming(sz_ZERO, stridePrologue);
    PHINode * const writePosPhi = b->CreatePHI(sizeTy, 2);
    writePosPhi->addIncoming(segWritePosPhi, stridePrologue);
    PHINode * const fullPhraseProducedInStridePhi = b->CreatePHI(sizeTy, 2);
    fullPhraseProducedInStridePhi->addIncoming(segFullPhrasePos, stridePrologue);

    Value * nextSubStrideNo = b->CreateAdd(subStrideNo, sz_ONE);
    Value * subStridePos = b->CreateAdd(stridePos, b->CreateMul(subStrideNo, sz_SUB_STRIDE));
    Value * readSubStrideBlockOffset = b->CreateAdd(strideBlockOffset,
                                                b->CreateMul(subStrideNo, sz_BLOCKS_PER_SUB_STRIDE));
    std::vector<Value *> phraseMasks = initializeCompressionMasks1(b, sw, sz_BLOCKS_PER_SUB_STRIDE, 1, readSubStrideBlockOffset, strideMasksReady);
    Value * phraseMask = phraseMasks[0];

    b->SetInsertPoint(strideMasksReady);
    Value * phraseWordBasePtr = b->getInputStreamBlockPtr("phraseMask", sz_ZERO, readSubStrideBlockOffset);
    phraseWordBasePtr = b->CreateBitCast(phraseWordBasePtr, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(phraseMask, sz_ZERO), subStridePhrasesDone, filteringLoop);

    b->SetInsertPoint(filteringLoop);
    PHINode * const phraseMaskPhi = b->CreatePHI(sizeTy, 2);
    phraseMaskPhi->addIncoming(phraseMask, strideMasksReady);
    PHINode * const phraseWordPhi = b->CreatePHI(sizeTy, 2);
    phraseWordPhi->addIncoming(sz_ZERO, strideMasksReady);
    PHINode * const subStrideWritePos = b->CreatePHI(sizeTy, 2);
    subStrideWritePos->addIncoming(writePosPhi, strideMasksReady);
    PHINode * const subStrideFullPhrasePhi = b->CreatePHI(sizeTy, 2);
    subStrideFullPhrasePhi->addIncoming(fullPhraseProducedInStridePhi, strideMasksReady);

    Value * phraseWordIdx = b->CreateCountForwardZeroes(phraseMaskPhi, "symIdx");
    Value * nextphraseWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(phraseWordBasePtr, phraseWordIdx)), sizeTy);
    Value * thephraseWord = b->CreateSelect(b->CreateICmpEQ(phraseWordPhi, sz_ZERO), nextphraseWord, phraseWordPhi);
    Value * phraseWordPos = b->CreateAdd(subStridePos, b->CreateMul(phraseWordIdx, sw.WIDTH));
    Value * phraseMarkPosInWord = b->CreateCountForwardZeroes(thephraseWord);
    Value * phraseMarkPos = b->CreateAdd(phraseWordPos, phraseMarkPosInWord);

    //byte-boundary for phraseWordPos
    Value * maskBit = sz_ONE;
    Value * startBase = b->CreateSub(phraseMarkPos, b->CreateURem(phraseMarkPos, sz_EIGHT));
    Value * startBitOffset = b->CreateSub(phraseMarkPos, startBase);
    maskBit = b->CreateShl(maskBit, startBitOffset);
    Value * const maskBasePtr = b->CreateBitCast(b->getRawInputPointer("symEndMarker", startBase), sizeTy->getPointerTo());
    Value * initialEndMark = b->CreateAlignedLoad(maskBasePtr, 1);
    Value * checkBitSet = b->CreateAnd(initialEndMark, maskBit);
    Value * updatedIdx = b->CreateSelect(b->CreateICmpUGT(checkBitSet, sz_ZERO), subStrideWritePos, subStrideFullPhrasePhi);

    b->CreateMemCpy(b->getRawOutputPointer("cmpBytes", subStrideWritePos), b->getRawInputPointer("byteData", phraseMarkPos), sz_ONE, 1);
    Value * dropPhrase = b->CreateResetLowestBit(thephraseWord);
    Value * thisWordDone = b->CreateICmpEQ(dropPhrase, sz_ZERO);
    // There may be more phrases in the phrase mask.
    Value * nextphraseMask = b->CreateSelect(thisWordDone, b->CreateResetLowestBit(phraseMaskPhi), phraseMaskPhi);
    Value * const nextWritePos = b->CreateAdd(subStrideWritePos, sz_ONE);
    BasicBlock * currentBB = b->GetInsertBlock();
    phraseMaskPhi->addIncoming(nextphraseMask, currentBB);
    phraseWordPhi->addIncoming(dropPhrase, currentBB);
    subStrideWritePos->addIncoming(nextWritePos, currentBB);
    subStrideFullPhrasePhi->addIncoming(updatedIdx, currentBB);
    b->CreateCondBr(b->CreateICmpNE(nextphraseMask, sz_ZERO), filteringLoop, subStridePhrasesDone);

    b->SetInsertPoint(subStridePhrasesDone);
    PHINode * const nextSubStrideWritePos = b->CreatePHI(sizeTy, 2);
    nextSubStrideWritePos->addIncoming(nextWritePos, filteringLoop);
    nextSubStrideWritePos->addIncoming(writePosPhi, strideMasksReady);

    PHINode * const nextFullPhraseEndPos = b->CreatePHI(sizeTy, 2);
    // b->CallPrintInt("updatedIdx", updatedIdx);
    nextFullPhraseEndPos->addIncoming(updatedIdx, filteringLoop);
    nextFullPhraseEndPos->addIncoming(fullPhraseProducedInStridePhi, strideMasksReady);

    BasicBlock * stridePhrasesDoneBB = b->GetInsertBlock();
    subStrideNo->addIncoming(nextSubStrideNo, stridePhrasesDoneBB);
    writePosPhi->addIncoming(nextSubStrideWritePos, stridePhrasesDoneBB);
    fullPhraseProducedInStridePhi->addIncoming(nextFullPhraseEndPos, stridePhrasesDoneBB);
    b->CreateCondBr(b->CreateICmpNE(nextSubStrideNo, totalSubStrides), subStrideMaskPrep, checkFinalLoopCond);

    b->SetInsertPoint(checkFinalLoopCond);
    strideNo->addIncoming(nextStrideNo, checkFinalLoopCond);
    Value * segWritePosUpdate = nextSubStrideWritePos; //b->CreateAdd(nextSubStrideWritePos, sz_ONE);
    segWritePosPhi->addIncoming(segWritePosUpdate, checkFinalLoopCond);
    Value * segFullPhraseEndPos = nextFullPhraseEndPos;
    segFullPhrasePos->addIncoming(segFullPhraseEndPos, checkFinalLoopCond);
    // Value * symPtr1 = b->CreateBitCast(b->getRawInputPointer("byteData", b->CreateSub(phraseMarkPos, b->getSize(3))), b->getInt8PtrTy());
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, b->CreateAdd(b->getSize(3), sz_ONE));
    // b->CallPrintInt("segWritePosUpdate", segWritePosUpdate);
    // b->CallPrintInt("phraseMarkPos", phraseMarkPos);

    Value * segProcessed = b->CreateAdd(initialPos, b->CreateMul(sz_STRIDE, strideNo));
    segProcessed = b->CreateUDiv(segProcessed, sz_STRIDE);
    // b->CallPrintInt("segProcessed", segProcessed);
    b->CreateStore(b->CreateTrunc(b->CreateSelect(b->isFinal(), segWritePosUpdate, b->CreateAdd(nextFullPhraseEndPos, sz_ONE) /* +1 for the next writable position*/ ), b->getInt64Ty()), b->getRawOutputPointer("partialSum", segProcessed));
    // Value * symPtr2 = b->CreateBitCast(b->getRawOutputPointer("cmpBytes", b->CreateSub(nextFullPhraseEndPos, b->getSize(3))), b->getInt8PtrTy());
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr2, b->CreateAdd(b->getSize(3), sz_ONE));
    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), stridePrologue, stridesDone);
    b->SetInsertPoint(stridesDone);
    // Value * processedBytes = b->CreateSelect(b->isFinal(), avail, b->CreateSub(phraseWordPos, b->CreateSub(segWritePosUpdate, nextFullPhraseEndPos)));
    // b->setProcessedItemCount("byteData", processedBytes);
    b->setProducedItemCount("cmpBytes", segWritePosUpdate);
    b->CreateCondBr(b->isFinal(), filteringMaskDone, updatePending);
    b->SetInsertPoint(updatePending);
    // No partial codewords are written across multiple segments. The full codeword shall be written in current segment.

    b->CreateBr(filteringMaskDone);
    b->SetInsertPoint(filteringMaskDone);
}

// Assumes phrases with frequency >= 2 are compressed
WriteDictionary::WriteDictionary(BuilderRef b,
                                unsigned plen,
                                EncodingInfo encodingScheme,
                                unsigned numSyms,
                                unsigned offset,
                                StreamSet * lfData,
                                StreamSet * byteData,
                                StreamSet * codedBytes,
                                StreamSet * phraseMask,
                                StreamSet * allLenHashValues,
                                StreamSet * dictionaryBytes,
                                StreamSet * dictPartialSum,
                                unsigned strideBlocks)
: MultiBlockKernel(b, "WriteDictionary" +  std::to_string(strideBlocks) + "_" + std::to_string(numSyms) + std::to_string(plen),
                   {Binding{"lfPos", lfData, FixedRate(ProcessingRate::Rational{1, 1048576})},
                    Binding{"phraseMask", phraseMask, FixedRate(), Deferred()},
                    Binding{"byteData", byteData, FixedRate(), Deferred()},
                    Binding{"codedBytes", codedBytes, FixedRate(), Deferred()},
                    Binding{"lengthData", allLenHashValues, FixedRate(), Deferred()}},
                   {}, {}, {}, {
                    InternalScalar{b->getSizeTy(), "segIndex"},
                    InternalScalar{b->getSizeTy(), "absBlocksProcessed"},
                    InternalScalar{b->getSizeTy(), "lastLfPos"},
                   }),
mEncodingScheme(encodingScheme), mNumSym(numSyms), mSubStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS)) {
    if (DelayedAttributeIsSet()) {
        mOutputStreamSets.emplace_back("dictionaryBytes", dictionaryBytes, BoundedRate(0, 1));
        mOutputStreamSets.emplace_back("dictPartialSum", dictPartialSum, BoundedRate(0, ceiling(ProcessingRate::Rational{1, 1048576})));
        addInternalScalar(ArrayType::get(b->getInt8Ty(), encodingScheme.maxSymbolLength()), "pendingPhrase");
        addInternalScalar(ArrayType::get(b->getInt8Ty(), encodingScheme.maxEncodingBytes()), "pendingCodeword");
        addInternalScalar(b->getInt8Ty(), "pendingPhraseLen");
        addInternalScalar(b->getInt8Ty(), "pendingCodewordLen");
    } else {
        mOutputStreamSets.emplace_back("dictionaryBytes", dictionaryBytes, BoundedRate(0,1));
    }
    setStride(1048576);
}

void WriteDictionary::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    // b->CallPrintInt("numOfStrides-dict", numOfStrides);
    ScanWordParameters sw(b, mStride);
    Constant * sz_STRIDE = b->getSize(mStride);
    Constant * sz_SUB_STRIDE = b->getSize(mSubStride);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    Constant * sz_BLOCKS_PER_STRIDE = b->getSize(mStride/b->getBitBlockWidth());
    Constant * sz_BLOCKS_PER_SUB_STRIDE = b->getSize(mSubStride/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_TWO = b->getSize(2);
    Constant * sz_SYM_MASK = b->getSize(0x1F);
    Constant * sz_HASH_TABLE_START = b->getSize(65278);
    Constant * sz_HASH_TABLE_END = b->getSize(65535);
    assert ((mStride % mSubStride) == 0);
    Value * totalSubStrides =  b->getSize(mStride / mSubStride); // 102400/2048 with BitBlock=256
    // b->CallPrintInt("totalSubStrides", totalSubStrides);

    Type * sizeTy = b->getSizeTy();
#ifdef PRINT_PHRASE_DEBUG_INFO
    Type * halfLengthTy = b->getIntNTy(8U * 8);
    Type * halfSymPtrTy = halfLengthTy->getPointerTo();
#endif

    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const stridePrologue = b->CreateBasicBlock("stridePrologue");
    BasicBlock * const subStrideMaskPrep = b->CreateBasicBlock("subStrideMaskPrep");
    BasicBlock * const writeHTStart = b->CreateBasicBlock("writeHTStart");
    BasicBlock * const writeFEFE = b->CreateBasicBlock("writeFEFE");
    BasicBlock * const FEFEDone = b->CreateBasicBlock("FEFEDone");
    BasicBlock * const firstPhrase = b->CreateBasicBlock("firstPhrase");
    BasicBlock * const firstPhraseDone = b->CreateBasicBlock("firstPhraseDone");
    BasicBlock * const firstCodeword = b->CreateBasicBlock("firstCodeword");
    BasicBlock * const firstCodewordDone = b->CreateBasicBlock("firstCodewordDone");
    BasicBlock * const tryWriteMask = b->CreateBasicBlock("tryWriteMask");
    BasicBlock * const writeMask = b->CreateBasicBlock("writeMask");
    BasicBlock * const strideMasksReady = b->CreateBasicBlock("strideMasksReady");
    BasicBlock * const dictProcessingLoop = b->CreateBasicBlock("dictProcessingLoop");
    BasicBlock * const writePhrase = b->CreateBasicBlock("writePhrase");
    BasicBlock * const writeSegPhrase = b->CreateBasicBlock("writeSegPhrase");
    BasicBlock * const phraseWritten = b->CreateBasicBlock("phraseWritten");
    BasicBlock * const writeCodeword = b->CreateBasicBlock("writeCodeword");
    BasicBlock * const codewordWritten = b->CreateBasicBlock("codewordWritten");
    BasicBlock * const tryUpdateMask = b->CreateBasicBlock("tryUpdateMask");
    BasicBlock * const updateMask = b->CreateBasicBlock("updateMask");
    BasicBlock * const nextPhrase = b->CreateBasicBlock("nextPhrase");
    BasicBlock * const checkWriteHTEnd = b->CreateBasicBlock("checkWriteHTEnd");
    BasicBlock * const writeHTEnd = b->CreateBasicBlock("writeHTEnd");
    BasicBlock * const subStridePhrasesDone = b->CreateBasicBlock("subStridePhrasesDone");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const updatePending = b->CreateBasicBlock("updatePending");
    BasicBlock * const compressionMaskDone = b->CreateBasicBlock("compressionMaskDone");
    BasicBlock * const checkFinalLoopCond = b->CreateBasicBlock("checkFinalLoopCond");
    BasicBlock * const writePendingPhrase = b->CreateBasicBlock("writePendingPhrase");
    BasicBlock * const pendingPhraseWritten = b->CreateBasicBlock("pendingPhraseWritten");
    BasicBlock * const writePendingCodeword = b->CreateBasicBlock("writePendingCodeword");
    BasicBlock * const pendingCodewordWritten = b->CreateBasicBlock("pendingCodewordWritten");
    BasicBlock * const storeInPending = b->CreateBasicBlock("storeInPending");
    BasicBlock * const processPhrase = b->CreateBasicBlock("processPhrase");

#ifdef PRINT_PHRASE_DEBUG_INFO
    // BasicBlock * const writeDebugOutput = b->CreateBasicBlock("writeDebugOutput");
    // BasicBlock * const writeDebugOutput1 = b->CreateBasicBlock("writeDebugOutput1");
#endif
    Value * const initialPos = b->getProcessedItemCount("phraseMask");
    Value * const avail = b->getAvailableItemCount("phraseMask");
    Value * const initialProducedBytes = b->getProducedItemCount("dictionaryBytes");
    Value * const processedBlocks = b->getScalarField("absBlocksProcessed");
    Value * const actualProcessed = b->CreateMul(processedBlocks, sz_BLOCKWIDTH);
    b->CreateBr(stridePrologue);

    b->SetInsertPoint(stridePrologue);
    // Set up the loop variables as PHI nodes at the beginning of each stride.
    PHINode * const strideNo = b->CreatePHI(sizeTy, 2);
    strideNo->addIncoming(sz_ZERO, entryBlock);
    PHINode * const segWritePosPhi = b->CreatePHI(sizeTy, 2);
    segWritePosPhi->addIncoming(initialProducedBytes, entryBlock);
    // b->CallPrintInt("segWritePosPhi", segWritePosPhi);
    Value * nextStrideNo = b->CreateAdd(strideNo, sz_ONE);
    Value * const curIdx = b->getScalarField("segIndex");
    Value * lfPosPtr = b->CreateBitCast(b->getRawInputPointer("lfPos", curIdx), b->getSizeTy()->getPointerTo());
    Value * lfPos = b->CreateAlignedLoad(lfPosPtr, 1);
    Value * totalProcessed = b->CreateMul(b->getScalarField("absBlocksProcessed"), sz_BLOCKWIDTH);
    Value * stridePos =  totalProcessed;
    Value * strideBlockOffset = b->getScalarField("absBlocksProcessed");
    Value * processBeforeThisPos = lfPos;
    Value * processAfterThisPos = b->getScalarField("lastLfPos");
    // b->CallPrintInt("strideNo-writeDict", strideNo);
    b->CreateBr(subStrideMaskPrep);

    b->SetInsertPoint(subStrideMaskPrep);
    PHINode * const subStrideNo = b->CreatePHI(sizeTy, 2);
    subStrideNo->addIncoming(sz_ZERO, stridePrologue);
    // starts from 1MB boundary for every 1MB stride - starts where the prev segment dictionary ended
    PHINode * const writePosPhi = b->CreatePHI(sizeTy, 2);
    writePosPhi->addIncoming(segWritePosPhi, stridePrologue); // segWritePosPhi
    // b->CallPrintInt("writePosPhi", writePosPhi);
    // b->CallPrintInt("subStrideNo", subStrideNo);
    Value * nextSubStrideNo = b->CreateAdd(subStrideNo, sz_ONE);
    Value * subStridePos = b->CreateAdd(stridePos, b->CreateMul(subStrideNo, sz_SUB_STRIDE));
    // b->CallPrintInt("subStridePos", subStridePos);
    Value * readSubStrideBlockOffset = b->CreateAdd(strideBlockOffset,
                                                b->CreateMul(subStrideNo, sz_BLOCKS_PER_SUB_STRIDE));
    // b->CallPrintInt("readSubStrideBlockOffset", readSubStrideBlockOffset);
    std::vector<Value *> phraseMasks = initializeCompressionMasks1(b, sw, sz_BLOCKS_PER_SUB_STRIDE, 1, readSubStrideBlockOffset, strideMasksReady);
    Value * phraseMask = phraseMasks[0];

    b->SetInsertPoint(strideMasksReady);
    readSubStrideBlockOffset = b->CreateSub(readSubStrideBlockOffset, processedBlocks);
    Value * phraseWordBasePtr = b->getInputStreamBlockPtr("phraseMask", sz_ZERO, readSubStrideBlockOffset);
    phraseWordBasePtr = b->CreateBitCast(phraseWordBasePtr, sw.pointerTy);
    // b->CallPrintInt("phraseWordBasePtr", phraseWordBasePtr);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(phraseMask, sz_ZERO), subStridePhrasesDone, dictProcessingLoop);

    b->SetInsertPoint(dictProcessingLoop);
    PHINode * const phraseMaskPhi = b->CreatePHI(sizeTy, 2);
    phraseMaskPhi->addIncoming(phraseMask, strideMasksReady);
    PHINode * const phraseWordPhi = b->CreatePHI(sizeTy, 2);
    phraseWordPhi->addIncoming(sz_ZERO, strideMasksReady);
    PHINode * const subStrideWritePos = b->CreatePHI(sizeTy, 2);
    subStrideWritePos->addIncoming(writePosPhi, strideMasksReady);
    // b->CallPrintInt("subStrideWritePos", subStrideWritePos);
    Value * phraseWordIdx = b->CreateCountForwardZeroes(phraseMaskPhi, "phraseWordIdx");
    Value * nextphraseWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(phraseWordBasePtr, phraseWordIdx)), sizeTy);
    Value * thephraseWord = b->CreateSelect(b->CreateICmpEQ(phraseWordPhi, sz_ZERO), nextphraseWord, phraseWordPhi);
    Value * phraseWordPos = b->CreateAdd(subStridePos, b->CreateMul(phraseWordIdx, sw.WIDTH));
    Value * phraseMarkPosInWord = b->CreateCountForwardZeroes(thephraseWord);
    Value * phraseMarkPosInit = b->CreateAdd(phraseWordPos, phraseMarkPosInWord);
    // For 1-sym phrases the phraseMark position may have moved across words as phraseMark is at last-but-one position of the phrase
    Value * isPhraseEndPosOnWordBoundary = b->CreateICmpEQ(phraseMarkPosInWord, b->getSize(0x3F));

    /* Determine the phrase length. */
    Value * phraseMarkPosTry1 = phraseMarkPosInit; // XX3F
    Value * phraseLengthTry1 = b->CreateZExtOrTrunc(b->CreateLoad(b->getRawInputPointer("lengthData", phraseMarkPosTry1)), sizeTy);
    Value * numSymInPhraseTry1 = b->CreateAnd(b->CreateLShr(phraseLengthTry1, b->getSize(5)), b->getSize(7));
    // In case of 1-sym phrase, if markPos is on last bit (64) of the word mask, check the first bit of next word mask
    Value * phraseMarkPosTry2 = b->CreateSelect(isPhraseEndPosOnWordBoundary, b->CreateSub(phraseWordPos, sz_ONE), phraseMarkPosInit); // XX00
    Value * phraseLengthTry2 = b->CreateZExtOrTrunc(b->CreateLoad(b->getRawInputPointer("lengthData", phraseMarkPosTry2)), sizeTy);
    Value * numSymInPhraseTry2 = b->CreateAnd(b->CreateLShr(phraseLengthTry2, b->getSize(5)), b->getSize(7));

    // If markPos is on bit 64, and numSymInPhraseTry1 > numSymInPhraseTry2, the final markPos need not be shifted.
    Value * numSymInPhrase = numSymInPhraseTry1;
    numSymInPhrase = b->CreateSelect(b->CreateAnd(isPhraseEndPosOnWordBoundary, b->CreateICmpUGT(numSymInPhraseTry1, numSymInPhraseTry2)), 
                                     numSymInPhrase, numSymInPhraseTry2);
    numSymInPhrase = b->CreateSelect(b->CreateICmpUGT(numSymInPhraseTry2, numSymInPhraseTry1), numSymInPhraseTry1, numSymInPhrase);
    /*
    numSymInPhraseTry1      numSymInPhraseTry2      Eval
            1                       1               numSymInPhraseTry1
            1                       2               numSymInPhraseTry1
            2                       1               numSymInPhraseTry1
            2                       2               numSymInPhraseTry1
    */
    Value * symMarkPosShiftNeeded = b->CreateICmpULT(numSymInPhrase, b->getSize(mNumSym));
    Value * phraseEndPosShift = b->CreateSelect(symMarkPosShiftNeeded, sz_ONE, sz_ZERO); // shift by k-pos for k-sym phrases
    // Update the position of phrase in word (phraseMarkPosInWord) rather than adding 1 to the calculated phraseEnd position
    Value * phraseMarkPosInWordFinal = b->CreateSelect(symMarkPosShiftNeeded, b->CreateAdd(phraseMarkPosInWord, phraseEndPosShift), phraseMarkPosInWord);
    // Update phraseMarkPosInWord for 1-sym phrases if the index is the last bit in the word (to access phrase at correct location)
    phraseMarkPosInWordFinal = b->CreateSelect(b->CreateAnd(isPhraseEndPosOnWordBoundary,/*valid for 64-bit words*/symMarkPosShiftNeeded),
                                               sw.WIDTH/*sz_ZERO read phrase from next word mask*/, phraseMarkPosInWordFinal);
    Value * phraseMarkPosFinal = b->CreateAdd(phraseWordPos, phraseMarkPosInWordFinal);
    // Update phraseLength as well - if phrase has k symbols, retreive length from phraseMarkPosFinal - (symCount-k) position
    Value * phraseLengthFinal = b->CreateZExtOrTrunc(b->CreateLoad(b->getRawInputPointer("lengthData", b->CreateSub(phraseMarkPosFinal, phraseEndPosShift))), sizeTy, "phraseLengthFinal");
    // Value * phraseLenOffset = b->CreateSelect(symMarkPosShiftNeeded, sz_ZERO, sz_ONE); // unused
    phraseLengthFinal = b->CreateAnd(phraseLengthFinal, sz_SYM_MASK);
    phraseLengthFinal = b->CreateAdd(phraseLengthFinal, sz_ONE);//phraseLenOffset);
    Value * phraseStartPos = b->CreateSub(phraseMarkPosFinal, b->CreateSub(phraseLengthFinal, sz_ONE), "phraseStartPos");

    Value * cwLenInit = b->getSize(2);
    cwLenInit = b->CreateSelect(b->CreateICmpUGT(phraseLengthFinal, b->getSize(8)), b->CreateAdd(cwLenInit, sz_ONE), cwLenInit);
    Value * codeWordLen = b->CreateSelect(b->CreateICmpUGT(phraseLengthFinal, b->getSize(16)), b->CreateAdd(cwLenInit, sz_ONE), cwLenInit, "codeWordLen");
    // Write phrase followed by codeword
    Value * codeWordStartPos =  b->CreateSub(phraseMarkPosFinal, b->CreateSub(codeWordLen, sz_ONE));
    // Add pending phrase and codeword length
    phraseLengthFinal = b->CreateAdd(b->CreateZExt(b->getScalarField("pendingPhraseLen"), sizeTy), phraseLengthFinal);
    codeWordLen = b->CreateAdd(b->CreateZExt(b->getScalarField("pendingCodewordLen"), sizeTy), codeWordLen);
    Value * const checkStartBoundary = b->CreateICmpEQ(subStrideWritePos, segWritePosPhi, "checkStartBoundary"); // beginning of each segment's dicitonary

    Value * phraseProcessCond = b->CreateAnd(b->CreateICmpULE(phraseMarkPosFinal, processBeforeThisPos), b->CreateICmpUGT(phraseMarkPosFinal, processAfterThisPos));
    b->CreateCondBr(phraseProcessCond, processPhrase, nextPhrase);

    b->SetInsertPoint(processPhrase);

    b->CreateCondBr(b->CreateICmpEQ(phraseMarkPosFinal, b->CreateAdd(stridePos, sz_STRIDE)), storeInPending, writeHTStart);
    b->SetInsertPoint(storeInPending);
    b->CreateMemCpy(b->getScalarFieldPtr("pendingPhrase"), b->getRawInputPointer("byteData", phraseStartPos), phraseLengthFinal, 1);
    b->setScalarField("pendingPhraseLen", b->CreateZExtOrTrunc(phraseLengthFinal, b->getInt8Ty()));
    b->CreateMemCpy(b->getScalarFieldPtr("pendingCodeword"), b->getRawInputPointer("codedBytes", codeWordStartPos), codeWordLen, 1);
    b->setScalarField("pendingCodewordLen", b->CreateZExtOrTrunc(codeWordLen, b->getInt8Ty()));
    b->CreateBr(nextPhrase);
    // Write initial hashtable boundary "fefe"; start boundary written only if the segment contains dictionary entry
    b->SetInsertPoint(writeHTStart);
    PHINode * const curWritePos = b->CreatePHI(sizeTy, 2);
    PHINode * const loopIdx = b->CreatePHI(sizeTy, 2);
    curWritePos->addIncoming(subStrideWritePos, processPhrase);
    loopIdx->addIncoming(sz_ZERO, processPhrase);

    Value * writeLen = sz_TWO;
    writeLen = b->CreateSelect(b->CreateICmpEQ(loopIdx, sz_ONE), b->CreateZExt(b->getScalarField("pendingPhraseLen"), sizeTy), writeLen);
    writeLen = b->CreateSelect(b->CreateICmpEQ(loopIdx, sz_TWO), b->CreateZExt(b->getScalarField("pendingCodewordLen"), sizeTy), writeLen);
    writeLen = b->CreateSelect(b->CreateICmpEQ(loopIdx, b->getSize(3)), b->CreateSub(phraseLengthFinal, b->CreateZExt(b->getScalarField("pendingPhraseLen"), sizeTy)), writeLen);
    writeLen = b->CreateSelect(b->CreateICmpEQ(loopIdx, b->getSize(4)), b->CreateSub(codeWordLen, b->CreateZExt(b->getScalarField("pendingCodewordLen"), sizeTy)), writeLen);
    writeLen = b->CreateSelect(checkStartBoundary, writeLen, sz_ZERO);
    Value * nextLoopIdx = b->CreateAdd(loopIdx, sz_ONE);
    Value * updateWritePos = b->CreateAdd(curWritePos, writeLen);
    Value * maxLoopIdx = b->getSize(5);
    // b->CallPrintInt("loopIdx", loopIdx);
    // b->CallPrintInt("writeLen", writeLen);
    b->CreateCondBr(b->CreateAnd(checkStartBoundary, b->CreateICmpEQ(loopIdx, sz_ZERO)), writeFEFE, FEFEDone);

    b->SetInsertPoint(writeFEFE);
    Value * const startBoundary = sz_TWO;
    Value * sBoundaryCodeword = b->CreateAlloca(b->getInt64Ty(), startBoundary);
    b->CreateAlignedStore(sz_HASH_TABLE_START, sBoundaryCodeword, 1);
    // b->CallPrintInt("curWritePos-writeFEFE", curWritePos);
    b->CreateMemCpy(b->getRawOutputPointer("dictionaryBytes", curWritePos), sBoundaryCodeword, startBoundary, 1);
    // b->CallPrintInt("curWritePos-start", curWritePos);
    b->CreateBr(FEFEDone);
    // Write start boundary
    b->SetInsertPoint(FEFEDone);
    b->CreateCondBr(b->CreateAnd(checkStartBoundary, b->CreateICmpEQ(loopIdx, sz_ONE)), writePendingPhrase, pendingPhraseWritten);
    b->SetInsertPoint(writePendingPhrase);
    b->CreateMemCpy(b->getRawOutputPointer("dictionaryBytes", curWritePos), b->getScalarFieldPtr("pendingPhrase"), b->getScalarField("pendingPhraseLen"), 1);
    b->CreateMemZero(b->getScalarFieldPtr("pendingPhrase"), b->getSize(mEncodingScheme.maxSymbolLength()));
    b->CreateBr(pendingPhraseWritten);

    b->SetInsertPoint(pendingPhraseWritten);
    b->CreateCondBr(b->CreateAnd(checkStartBoundary, b->CreateICmpEQ(loopIdx, sz_TWO)), writePendingCodeword, pendingCodewordWritten);
    b->SetInsertPoint(writePendingCodeword);
    b->CreateMemCpy(b->getRawOutputPointer("dictionaryBytes", curWritePos), b->getScalarFieldPtr("pendingCodeword"), b->getScalarField("pendingCodewordLen"), 1);
    b->CreateMemZero(b->getScalarFieldPtr("pendingCodeword"), b->getSize(mEncodingScheme.maxEncodingBytes()));
    b->CreateBr(pendingCodewordWritten);

    b->SetInsertPoint(pendingCodewordWritten);
    b->CreateCondBr(b->CreateAnd(checkStartBoundary, b->CreateICmpEQ(loopIdx, b->getSize(3))), firstPhrase, firstPhraseDone);
    b->SetInsertPoint(firstPhrase);
    b->CreateMemCpy(b->getRawOutputPointer("dictionaryBytes", curWritePos), 
                    b->getRawInputPointer("byteData", phraseStartPos),
                    b->CreateSub(phraseLengthFinal, b->CreateZExt(b->getScalarField("pendingPhraseLen"), sizeTy)), 1);
    b->setScalarField("pendingPhraseLen", b->getInt8(0));
#ifdef PRINT_PHRASE_DEBUG_INFO
    // b->CreateCondBr(b->CreateICmpEQ(phraseLengthFinal, sz_PLEN), writeDebugOutput, firstPhraseDone);
    // b->SetInsertPoint(writeDebugOutput);

    b->CallPrintInt("phraseMarkPosFinal-start", phraseMarkPosFinal);
    b->CallPrintInt("phraseLengthFinal-start-start", phraseLengthFinal);
    Value * symPtr1 = b->CreateBitCast(b->getRawInputPointer("byteData", phraseStartPos), halfSymPtrTy);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, phraseLengthFinal);

    // b->CallPrintInt("phraseLengthTry1-orig-start", phraseLengthTry1);
    b->CallPrintInt("phraseMarkPosTry1-start", phraseMarkPosTry1);
    b->CallPrintInt("phraseLengthTry1-start", b->CreateAnd(phraseLengthTry1, sz_SYM_MASK));
    // b->CallPrintInt("numSymInPhraseTry1-start", b->CreateAnd(numSymInPhraseTry1, sz_SYM_MASK));
    Value * phraseStartPosTry1 = b->CreateSub(phraseMarkPosTry1, b->CreateSub(phraseLengthTry1, sz_ONE));
    Value * symTry1 = b->CreateBitCast(b->getRawInputPointer("byteData", phraseStartPosTry1), halfSymPtrTy);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symTry1, b->CreateAnd(phraseLengthTry1, sz_SYM_MASK));
    b->CallPrintInt("phraseMarkPosTry2-start", phraseMarkPosTry2);
    b->CallPrintInt("phraseLengthTry2-start", b->CreateAnd(phraseLengthTry2, sz_SYM_MASK));
    // b->CallPrintInt("numSymInPhraseTry2-start", numSymInPhraseTry2);
    Value * phraseStartPosTry2 = b->CreateSub(phraseMarkPosTry2, b->CreateSub(phraseLengthTry2, sz_ONE));
    Value * symTry2 = b->CreateBitCast(b->getRawInputPointer("byteData", phraseStartPosTry2), halfSymPtrTy);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symTry2, b->CreateAnd(phraseLengthTry2, sz_SYM_MASK));
#endif

    b->CreateBr(firstPhraseDone);
    // Write phrase
    b->SetInsertPoint(firstPhraseDone);
    b->CreateCondBr(b->CreateAnd(checkStartBoundary, b->CreateICmpEQ(loopIdx, b->getSize(4))), firstCodeword, firstCodewordDone);
    b->SetInsertPoint(firstCodeword);
    b->CreateMemCpy(b->getRawOutputPointer("dictionaryBytes", curWritePos), 
                    b->getRawInputPointer("codedBytes", codeWordStartPos), 
                    b->CreateSub(codeWordLen, b->CreateZExt(b->getScalarField("pendingCodewordLen"), sizeTy)), 1);
    b->setScalarField("pendingCodewordLen", b->getInt8(0));
    b->CreateBr(firstCodewordDone);
    // Write codeword
    b->SetInsertPoint(firstCodewordDone);
    BasicBlock * thisBB = b->GetInsertBlock();
    loopIdx->addIncoming(nextLoopIdx, thisBB);
    curWritePos->addIncoming(updateWritePos, thisBB);
    // b->CallPrintInt("updateWritePos", updateWritePos);
    b->CreateCondBr(b->CreateAnd(checkStartBoundary, b->CreateICmpNE(nextLoopIdx, maxLoopIdx)), writeHTStart, tryWriteMask);

    b->SetInsertPoint(tryWriteMask);
    // Update dictionaryMask
    b->CreateCondBr(checkStartBoundary, writeMask, writeSegPhrase);
    b->SetInsertPoint(writeMask);
    // Value * const maskLength = b->CreateZExt(b->CreateAdd(sz_TWO, b->CreateAdd(phraseLengthFinal, codeWordLen)), sizeTy);
    // Value * mask = b->CreateSub(b->CreateShl(sz_ONE, maskLength), sz_ONE);
    // Value * startMaskBase = b->CreateSub(subStrideWritePos, b->CreateURem(subStrideWritePos, sz_EIGHT));
    // Value * startMaskbitOffset = b->CreateSub(subStrideWritePos, startMaskBase);
    // mask = b->CreateShl(mask, startMaskbitOffset);
    // Value * const maskBasePtr = b->CreateBitCast(b->getRawOutputPointer("dictionaryMask", startMaskBase), sizeTy->getPointerTo());
    // Value * initialBoundaryMask = b->CreateAlignedLoad(maskBasePtr, 1);
    // Value * updatedBoundaryMask = b->CreateOr(initialBoundaryMask, mask);
    // b->CreateAlignedStore(updatedBoundaryMask, maskBasePtr, 1);
    b->CreateBr(writeSegPhrase);

    b->SetInsertPoint(writeSegPhrase);
    // If not first phrase of the segment
    // Write phrase followed by codeword
    PHINode * const segWritePos = b->CreatePHI(sizeTy, 3);
    PHINode * const segLoopIdx = b->CreatePHI(sizeTy, 3);
    segWritePos->addIncoming(subStrideWritePos, writeMask);
    segLoopIdx->addIncoming(sz_ZERO, writeMask);
    segWritePos->addIncoming(subStrideWritePos, tryWriteMask);
    segLoopIdx->addIncoming(sz_ZERO, tryWriteMask);

    Value * segWriteLen = b->CreateSelect(b->CreateICmpEQ(segLoopIdx, sz_ZERO), phraseLengthFinal, codeWordLen);
    segWriteLen = b->CreateSelect(b->CreateNot(checkStartBoundary), segWriteLen, sz_ZERO);
    Value * nextSegLoopIdx = b->CreateAdd(segLoopIdx, sz_ONE);
    Value * updateSegWritePos = b->CreateAdd(segWritePos, segWriteLen);

    b->CreateCondBr(b->CreateAnd(b->CreateNot(checkStartBoundary), b->CreateICmpEQ(segLoopIdx, sz_ZERO)), writePhrase, phraseWritten);
    // Write phrase
    b->SetInsertPoint(writePhrase);
    // b->CallPrintInt("curWritePos-writePhrase", segWritePos);
    b->CreateMemCpy(b->getRawOutputPointer("dictionaryBytes", segWritePos), b->getRawInputPointer("byteData", phraseStartPos), phraseLengthFinal, 1);

#ifdef PRINT_PHRASE_DEBUG_INFO
    // b->CreateCondBr(b->CreateICmpEQ(phraseLengthFinal, sz_PLEN), writeDebugOutput1, phraseWritten);
    // b->SetInsertPoint(writeDebugOutput1);
    // written in the dict
    b->CallPrintInt("phraseMarkPosFinal-seg", phraseMarkPosFinal);
    b->CallPrintInt("phraseLengthFinal-seg", phraseLengthFinal);
    Value * symPtr3 = b->CreateBitCast(b->getRawInputPointer("byteData", phraseStartPos), halfSymPtrTy);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr3, phraseLengthFinal);
    // try1
    // b->CallPrintInt("phraseLengthTry1-orig-seg", phraseLengthTry1);
    // b->CallPrintInt("phraseMarkPosInWord", phraseMarkPosInWord);
    // b->CallPrintInt("phraseEndPosShift", phraseEndPosShift);
    b->CallPrintInt("phraseMarkPosTry1-seg", phraseMarkPosTry1);
    b->CallPrintInt("phraseLengthTry1-seg", b->CreateAnd(phraseLengthTry1, sz_SYM_MASK));
    // b->CallPrintInt("numSymInPhraseTry1-seg", b->CreateAnd(numSymInPhraseTry1, sz_SYM_MASK));
    Value * phraseStartPosTry1_seg = b->CreateSub(phraseMarkPosTry1, b->CreateSub(phraseLengthTry1, sz_ONE));
    Value * symTry1_seg = b->CreateBitCast(b->getRawInputPointer("byteData", phraseStartPosTry1_seg), halfSymPtrTy);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symTry1_seg, b->CreateAnd(phraseLengthTry1, sz_SYM_MASK));
    // try2
    b->CallPrintInt("phraseMarkPosTry2-seg", phraseMarkPosTry2);
    b->CallPrintInt("phraseLengthTry2-seg", b->CreateAnd(phraseLengthTry2, sz_SYM_MASK));
    // b->CallPrintInt("numSymInPhraseTry2-seg", numSymInPhraseTry2);
    Value * phraseStartPosTry2_seg = b->CreateSub(phraseMarkPosTry2, b->CreateSub(phraseLengthTry2, sz_ONE));
    Value * symTry2_seg = b->CreateBitCast(b->getRawInputPointer("byteData", phraseStartPosTry2_seg), halfSymPtrTy);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symTry2_seg, b->CreateAnd(phraseLengthTry2, sz_SYM_MASK));
#endif
    b->CreateBr(phraseWritten);

    b->SetInsertPoint(phraseWritten);
    b->CreateCondBr(b->CreateAnd(b->CreateNot(checkStartBoundary), b->CreateICmpEQ(segLoopIdx, sz_ONE)), writeCodeword, codewordWritten);
    // Write codeword
    b->SetInsertPoint(writeCodeword);
    // b->CallPrintInt("curWritePos-writeCodeword", segWritePos);
    // Value * symPtr4 = b->CreateBitCast(b->getRawInputPointer("codedBytes", codeWordStartPos), halfSymPtrTy);
    // b->CreateWriteCall(b->getInt32(STDOUT_FILENO), symPtr4, codeWordLen);
    b->CreateMemCpy(b->getRawOutputPointer("dictionaryBytes", segWritePos), b->getRawInputPointer("codedBytes", codeWordStartPos), codeWordLen, 1);
    b->CreateBr(codewordWritten);

    b->SetInsertPoint(codewordWritten);
    BasicBlock * thisSegBB = b->GetInsertBlock();
    segLoopIdx->addIncoming(nextSegLoopIdx, thisSegBB);
    segWritePos->addIncoming(updateSegWritePos, thisSegBB);
    b->CreateCondBr(b->CreateICmpNE(nextSegLoopIdx, b->getSize(2)), writeSegPhrase, tryUpdateMask);

    b->SetInsertPoint(tryUpdateMask);
    b->CreateCondBr(checkStartBoundary, nextPhrase, updateMask);
    b->SetInsertPoint(updateMask);
    // Value * phraseMaskLength = b->CreateZExt(b->CreateAdd(phraseLengthFinal, codeWordLen), sizeTy);
    // Value * lastMask = b->CreateSub(b->CreateShl(sz_ONE, phraseMaskLength), sz_ONE);
    // Value * dictBase = b->CreateSub(subStrideWritePos, b->CreateURem(subStrideWritePos, sz_EIGHT));
    // Value * bitOffset1 = b->CreateSub(subStrideWritePos, dictBase);
    // lastMask = b->CreateShl(lastMask, bitOffset1);
    // Value * const dictPhraseBasePtr = b->CreateBitCast(b->getRawOutputPointer("dictionaryMask", dictBase), sizeTy->getPointerTo());
    // Value * initialdictPhraseMask = b->CreateAlignedLoad(dictPhraseBasePtr, 1);
    // Value * updatedDictPhraseMask = b->CreateOr(initialdictPhraseMask, lastMask);
    // b->CreateAlignedStore(updatedDictPhraseMask, dictPhraseBasePtr, 1);
    b->CreateBr(nextPhrase);

    b->SetInsertPoint(nextPhrase);
    Value * dropPhrase = b->CreateResetLowestBit(thephraseWord);
    Value * thisWordDone = b->CreateICmpEQ(dropPhrase, sz_ZERO);
    // There may be more phrases in the phrase mask.
    Value * nextphraseMask = b->CreateSelect(thisWordDone, b->CreateResetLowestBit(phraseMaskPhi), phraseMaskPhi);
    Value * const startBoundaryLen = b->CreateSelect(checkStartBoundary, sz_TWO, sz_ZERO);
    Value * const nextWritePos = b->CreateAdd(subStrideWritePos, b->CreateAdd(startBoundaryLen,
                                 b->CreateAdd(codeWordLen, phraseLengthFinal)), "nextWritePos");
    BasicBlock * currentBB = b->GetInsertBlock();
    phraseMaskPhi->addIncoming(nextphraseMask, currentBB);
    phraseWordPhi->addIncoming(dropPhrase, currentBB);
    subStrideWritePos->addIncoming(nextWritePos, currentBB);
    b->CreateCondBr(b->CreateICmpEQ(nextphraseMask, sz_ZERO), subStridePhrasesDone, dictProcessingLoop);

    b->SetInsertPoint(subStridePhrasesDone);
    PHINode * const nextSubStrideWritePos = b->CreatePHI(sizeTy, 2);
    nextSubStrideWritePos->addIncoming(nextWritePos, nextPhrase);
    nextSubStrideWritePos->addIncoming(writePosPhi, strideMasksReady);

    BasicBlock * stridePhrasesDoneBB = b->GetInsertBlock();
    subStrideNo->addIncoming(nextSubStrideNo, stridePhrasesDoneBB);
    writePosPhi->addIncoming(nextSubStrideWritePos, stridePhrasesDoneBB);
    b->CreateCondBr(b->CreateICmpNE(nextSubStrideNo, totalSubStrides), subStrideMaskPrep, checkWriteHTEnd);

    b->SetInsertPoint(checkWriteHTEnd);
    // Note to self: Assumes that the stride contains no dict, does not write start and end boundary
    b->CreateCondBr(b->CreateICmpEQ(nextSubStrideWritePos, /*b->CreateAdd(segWritePosPhi, sz_TWO)*/ segWritePosPhi), checkFinalLoopCond, writeHTEnd);
    b->SetInsertPoint(writeHTEnd);
    // Write hashtable end boundary FFFF
    // b->CallPrintInt("curWritePos-writeFFFF", nextSubStrideWritePos);
    Value * const copyLen = sz_TWO;
    Value * boundaryCodeword = b->CreateAlloca(b->getInt64Ty(), copyLen);
    b->CreateAlignedStore(sz_HASH_TABLE_END, boundaryCodeword, 1);
    b->CreateMemCpy(b->getRawOutputPointer("dictionaryBytes", nextSubStrideWritePos), boundaryCodeword, copyLen, 1);
    // Value * lastBoundaryBase = b->CreateSub(nextSubStrideWritePos, b->CreateURem(nextSubStrideWritePos, sz_EIGHT));
    // Value * lastBoundaryBitOffset = b->CreateSub(nextSubStrideWritePos, lastBoundaryBase);
    // Value * boundaryBits = b->getSize(0x3);
    // boundaryBits = b->CreateShl(boundaryBits, lastBoundaryBitOffset);
    // Value * const dictPtr = b->CreateBitCast(b->getRawOutputPointer("dictionaryMask", lastBoundaryBase), sizeTy->getPointerTo());
    // Value * initMask = b->CreateAlignedLoad(dictPtr, 1);
    // Value * update = b->CreateOr(initMask, boundaryBits);
    // b->CreateAlignedStore(update, dictPtr, 1);
    b->CreateBr(checkFinalLoopCond);

    b->SetInsertPoint(checkFinalLoopCond);
    strideNo->addIncoming(nextStrideNo, checkFinalLoopCond);
    b->setScalarField("segIndex", b->CreateAdd(sz_ONE, b->getScalarField("segIndex")));
    b->setScalarField("absBlocksProcessed", b->CreateUDiv(lfPos, sz_BLOCKWIDTH));
    Value * segWritePosUpdate = b->CreateSelect(b->CreateICmpEQ(nextSubStrideWritePos, segWritePosPhi), nextSubStrideWritePos, b->CreateAdd(nextSubStrideWritePos, sz_TWO), "segWritePosUpdate");

    // Value * producedBase = b->CreateSub(segWritePosUpdate, b->CreateURem(segWritePosUpdate, sz_BLOCK_SIZE));
    // Value * producedBitOffset = b->CreateSub(segWritePosUpdate, producedBase);
    // Value * nextAlignedOffset = b->CreateSub(sz_BLOCK_SIZE, producedBitOffset);
    // Value * producedByteOffset = b->CreateSelect(b->CreateICmpEQ(producedBitOffset, sz_ZERO), producedBitOffset, nextAlignedOffset);
    // Value * const producedCurSegment = b->CreateAdd(segWritePosUpdate, producedByteOffset);

    segWritePosPhi->addIncoming(segWritePosUpdate, checkFinalLoopCond);
    // b->CallPrintInt("nextSubStrideWritePos", nextSubStrideWritePos);
    // b->CallPrintInt("segWritePosUpdate", segWritePosUpdate);
    // b->CallPrintInt("producedByteOffset", producedByteOffset);

    // Write the produced dictionary count to integer-stream
    Value * segProcessed = b->CreateAdd(initialPos, b->CreateMul(sz_STRIDE, strideNo)); // stridePos
    segProcessed = b->CreateUDiv(segProcessed, sz_STRIDE);
    // b->CallPrintInt("segProcessed", segProcessed);
    b->CreateStore(b->CreateTrunc(segWritePosUpdate, b->getInt64Ty()), b->getRawOutputPointer("dictPartialSum", segProcessed));
    // b->CallPrintInt("segWritePosUpdate", segWritePosUpdate);

    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), stridePrologue, stridesDone);
    b->SetInsertPoint(stridesDone);
    // Value * segProcessedLast = b->CreateAdd(initialPos, b->CreateMul(sz_STRIDE, numOfStrides));
    // segProcessedLast = b->CreateUDiv(segProcessedLast, sz_STRIDE);
    // b->CallPrintInt("segProcessedLast", segProcessedLast);
    // b->CreateStore(b->CreateTrunc(segWritePosUpdate, b->getInt64Ty()), b->getRawOutputPointer("dictPartialSum", segProcessedLast));
    // b->CallPrintInt("segWritePosUpdate-last", segWritePosUpdate);

    b->setProducedItemCount("dictionaryBytes", segWritePosUpdate);
    b->setProducedItemCount("dictPartialSum", b->CreateSub(b->getScalarField("segIndex"), sz_ONE));
    Value * producedBlocks = b->CreateUDiv(lfPos, sz_BLOCKWIDTH);
    Value * processed = b->CreateSelect(b->isFinal(), avail, b->CreateMul(producedBlocks, sz_BLOCKWIDTH));
    b->setProcessedItemCount("phraseMask", processed);
    b->setProcessedItemCount("byteData", processed);
    b->setProcessedItemCount("codedBytes", processed);
    b->setProcessedItemCount("lengthData", processed);
    b->CreateCondBr(b->isFinal(), compressionMaskDone, updatePending);
    b->SetInsertPoint(updatePending);
    // No partial phrases in the segment are written in the dicitonary. The phrase shall be moved to the next segment.

    b->CreateBr(compressionMaskDone);
    b->SetInsertPoint(compressionMaskDone);
}

InterleaveCompressionSegment::InterleaveCompressionSegment(BuilderRef b,
                                    StreamSet * dictData,
                                    StreamSet * codedBytes,
                                    StreamSet * dictPartialSum,
                                    StreamSet * cmpPartialSum,
                                    unsigned strideBlocks)
: MultiBlockKernel(b, "InterleaveCompressionSegment" + std::to_string(strideBlocks) + "_" + std::to_string(dictPartialSum->getNumElements()) + "_" + std::to_string(cmpPartialSum->getNumElements()),
                   {Binding{"dictPartialSum", dictPartialSum, FixedRate(1)},
                    Binding{"cmpPartialSum", cmpPartialSum, /*FixedRate(1048576)*/ FixedRate(1)},
                    Binding{"dictData", dictData, PartialSum("dictPartialSum")},
                    Binding{"codedBytes", codedBytes, PartialSum("cmpPartialSum") /*PopcountOf("compressedMask")*/}},
                   {}, {}, {}, {}) {
    setStride(1);
    addAttribute(SideEffecting());
    addAttribute(ExecuteStridesIndividually());
}

void InterleaveCompressionSegment::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {

    Value * const dictAvail = b->getAccessibleItemCount("dictData");
    Value * const cmpAvail = b->getAccessibleItemCount("codedBytes");
    Value * const dictProcessed = b->getProcessedItemCount("dictData");
    Value * const cmpProcessed = b->getProcessedItemCount("codedBytes");

    Constant * const stdOutFd = b->getInt32(STDOUT_FILENO);
    b->CreateWriteCall(stdOutFd, b->getRawInputPointer("dictData", dictProcessed), dictAvail);
    b->CreateWriteCall(stdOutFd, b->getRawInputPointer("codedBytes", cmpProcessed), cmpAvail);

}

SymbolGroupDecompression::SymbolGroupDecompression(BuilderRef b,
                                                   EncodingInfo encodingScheme,
                                                   unsigned numSym,
                                                   unsigned groupNo,
                                                   StreamSet * const codeWordMarks,
                                                   StreamSet * const hashMarks, StreamSet * const byteData,
                                                   StreamSet * const result, unsigned strideBlocks)
: MultiBlockKernel(b, "SymbolGroupDecompression" + lengthGroupSuffix(encodingScheme, groupNo),
                   {Binding{"keyMarks0", codeWordMarks},
                       Binding{"hashMarks0", hashMarks},
                       Binding{"byteData", byteData, FixedRate(), Deferred()}
                   },
                   {}, {}, {},
                   {InternalScalar{ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), "pendingOutput"},
                    // Hash table 8 length-based tables with 256 16-byte entries each.
                    InternalScalar{ArrayType::get(ArrayType::get(ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), phraseHashSubTableSize(encodingScheme, groupNo)),
                                   (encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1)), "hashTable"}}),
    mEncodingScheme(encodingScheme), mGroupNo(groupNo), mNumSym(numSym) {
    if (DelayedAttributeIsSet()) {
        mOutputStreamSets.emplace_back("result", result, FixedRate(), Delayed(encodingScheme.maxSymbolLength()));
    } else {
        mOutputStreamSets.emplace_back("result", result, BoundedRate(0,1));
    }
    setStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS));
}

void SymbolGroupDecompression::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {

    ScanWordParameters sw(b, mStride);
    LengthGroupParameters lg(b, mEncodingScheme, mGroupNo);
    Constant * sz_STRIDE = b->getSize(mStride);
    Constant * sz_BLOCKS_PER_STRIDE = b->getSize(mStride/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Type * sizeTy = b->getSizeTy();

    Value * sz_HALF_TBL_IDX = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo) / 2);
    Value * sz_HALF_TBL_IDX_0 = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo) / 3);
    Value * checkGroupNum = b->CreateICmpUGT(b->getSize(mGroupNo), sz_ZERO);
    sz_HALF_TBL_IDX = b->CreateSelect(checkGroupNum, sz_HALF_TBL_IDX, sz_HALF_TBL_IDX_0);
    checkGroupNum = b->CreateICmpEQ(b->getSize(mGroupNo), b->getSize(3));
    sz_HALF_TBL_IDX = b->CreateSelect(checkGroupNum, sz_ZERO, sz_HALF_TBL_IDX);

    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const stridePrologue = b->CreateBasicBlock("stridePrologue");
    BasicBlock * const strideMasksReady = b->CreateBasicBlock("strideMasksReady");
    BasicBlock * const keyProcessingLoop = b->CreateBasicBlock("keyProcessingLoop");
    BasicBlock * const nextKey = b->CreateBasicBlock("nextKey");
    BasicBlock * const keysDone = b->CreateBasicBlock("keysDone");
    BasicBlock * const hashProcessingLoop = b->CreateBasicBlock("hashProcessingLoop");
    BasicBlock * const lookupSym = b->CreateBasicBlock("lookupSym");
    BasicBlock * const nextHash = b->CreateBasicBlock("nextHash");
    BasicBlock * const hashesDone = b->CreateBasicBlock("hashesDone");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const updateHashTable = b->CreateBasicBlock("updateHashTable");
    BasicBlock * const replaceCodewords = b->CreateBasicBlock("replaceCodewords");
    BasicBlock * const strideDone = b->CreateBasicBlock("strideDone");

    Value * const initialPos = b->getProcessedItemCount("keyMarks0");
    Value * const avail = b->getAvailableItemCount("keyMarks0");

    Value * const initialProduced = b->getProducedItemCount("result");
    b->CreateMemCpy(b->getRawOutputPointer("result", initialProduced), b->getScalarFieldPtr("pendingOutput"), lg.HI, 1);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), b->getScalarFieldPtr("pendingOutput"), b->CreateAdd(lg.HI, sz_ZERO));

    // Copy all new input to the output buffer; this will be then
    // overwritten when and as necessary for decompression of ZTF codes.
    ///TODO: only copy the decompressed data, not the hashtable from the compressed data
    Value * toCopy = b->CreateMul(numOfStrides, sz_STRIDE);
    b->CreateMemCpy(b->getRawOutputPointer("result", initialPos), b->getRawInputPointer("byteData", initialPos), toCopy, 1);

    Type * phraseType = ArrayType::get(b->getInt8Ty(), mEncodingScheme.byLength[mGroupNo].hi);
    Value * hashTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("hashTable"), b->getInt8PtrTy());
    b->CreateBr(stridePrologue);

    b->SetInsertPoint(stridePrologue);
    // Set up the loop variables as PHI nodes at the beginning of each stride.
    PHINode * const strideNo = b->CreatePHI(sizeTy, 2);
    strideNo->addIncoming(sz_ZERO, entryBlock);
    Value * nextStrideNo = b->CreateAdd(strideNo, sz_ONE);
    Value * stridePos = b->CreateAdd(initialPos, b->CreateMul(strideNo, sz_STRIDE));
    Value * strideBlockOffset = b->CreateMul(strideNo, sz_BLOCKS_PER_STRIDE);

    std::vector<Value *> keyMasks(1);
    std::vector<Value *> hashMasks(1);
    initializeDecompressionMasks(b, sw, sz_BLOCKS_PER_STRIDE, 1, strideBlockOffset, keyMasks, hashMasks, strideMasksReady);
    Value * keyMask = keyMasks[0]; // codeword marks in dictionary
    Value * hashMask = hashMasks[0]; // codeword marks in compressed data

    b->SetInsertPoint(strideMasksReady);
    Value * decmpFirst = b->CreateICmpUGE(keyMask, hashMask); // hashMarks should be decompressed first

    b->CreateCondBr(decmpFirst, replaceCodewords, updateHashTable);

    b->SetInsertPoint(updateHashTable);
    Value * keyWordBasePtr = b->getInputStreamBlockPtr("keyMarks0", sz_ZERO, strideBlockOffset);
    keyWordBasePtr = b->CreateBitCast(keyWordBasePtr, sw.pointerTy);
    DEBUG_PRINT("keyMask", keyMask);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(keyMask, sz_ZERO), keysDone, keyProcessingLoop);

    b->SetInsertPoint(keyProcessingLoop);
    PHINode * const keyMaskPhi = b->CreatePHI(sizeTy, 2);
    keyMaskPhi->addIncoming(keyMask, updateHashTable);
    PHINode * const keyWordPhi = b->CreatePHI(sizeTy, 2);
    keyWordPhi->addIncoming(sz_ZERO, updateHashTable);
    Value * keyWordIdx = b->CreateCountForwardZeroes(keyMaskPhi, "keyWordIdx");
    Value * nextKeyWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(keyWordBasePtr, keyWordIdx)), sizeTy);
    Value * theKeyWord = b->CreateSelect(b->CreateICmpEQ(keyWordPhi, sz_ZERO), nextKeyWord, keyWordPhi);
    Value * keyWordPos = b->CreateAdd(stridePos, b->CreateMul(keyWordIdx, sw.WIDTH));
    Value * keyMarkPosInWord = b->CreateCountForwardZeroes(theKeyWord);
    Value * keyMarkPos = b->CreateAdd(keyWordPos, keyMarkPosInWord, "keyEndPos");
    DEBUG_PRINT("keyMarkPos", keyMarkPos);
    /* Determine the key length. */
    // determine keyLength from the codeword prefix
    Value * pfxPos = b->CreateSub(keyMarkPos, lg.MAX_INDEX);
    Value * const thePfx = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("byteData", pfxPos)), sizeTy);
    Value * theGroupLen = b->CreateSub(thePfx, lg.PREFIX_BASE);
    Value * keyLength = b->CreateAdd(b->CreateAnd(theGroupLen, lg.PHRASE_EXTENSION_MASK), lg.LO, "keyLength");
    Value * keyStartPos = b->CreateSub(pfxPos, keyLength, "keyStartPos");
    DEBUG_PRINT("keyLength", keyLength);

    // fetch the phrase and corresponding codeword
    // calculate the hashtable index and store the phrase
    // step over to the next phrase of same length

    // keyOffset for accessing the final half of an entry.
    Value * keyOffset = b->CreateSub(keyLength, lg.HALF_LENGTH);
    DEBUG_PRINT("keyOffset", keyOffset);
    // Build up a single encoded value for table lookup from the hashcode sequence.
    Value * hashcodePos = keyMarkPos;
    Value * codewordVal = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("byteData", hashcodePos)), sizeTy);
    // b->CallPrintInt("codewordVal-sfx", codewordVal);
#ifdef PRINT_DECOMPRESSION_DICT_INFO
    Value * codewordVal_debug = codewordVal;
#endif
    codewordVal = b->CreateSelect(b->CreateICmpUGE(codewordVal, b->getSize(0x80)), b->CreateSub(codewordVal, b->getSize(0x80)), codewordVal);
    // codewordVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(codewordVal, sz_ONE), b->CreateShl(codewordVal, sz_ONE)),
    //                               codewordVal);
    for (unsigned j = 1; j < lg.groupInfo.encoding_bytes - 1; j++) {
        hashcodePos = b->CreateSub(hashcodePos, sz_ONE);
        Value * sfxByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("byteData", hashcodePos)), sizeTy);
        codewordVal = b->CreateShl(codewordVal, lg.HASH_SHIFT_BITS);
        codewordVal = b->CreateOr(codewordVal, sfxByte);
        // b->CallPrintInt("sfxByte", sfxByte);
#ifdef PRINT_DECOMPRESSION_DICT_INFO
        codewordVal_debug = b->CreateOr(b->CreateShl(codewordVal_debug, lg.MAX_HASH_BITS), sfxByte);
#endif
    }
    // Value * pfxByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("byteData", hashcodePos)), sizeTy);
    Value * keylen_range = b->CreateSub(keyLength, lg.LO);
    Value * thePfxOffset = b->CreateAdd(lg.PREFIX_BASE, keylen_range);
    Value * theMultiplier = b->CreateSub(thePfx, thePfxOffset);
    Value * thePfxHashBits = b->CreateUDiv(theMultiplier, lg.RANGE);
    thePfxHashBits = b->CreateTrunc(thePfxHashBits, b->getInt64Ty());
    /// CHECK: Assertion for CreateUDiv(multiplier, lg.RANGE)
#ifdef PRINT_DECOMPRESSION_DICT_INFO
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), b->getRawInputPointer("byteData", keyStartPos), keyLength);
    Value * hashLen = b->CreateAdd(lg.ENC_BYTES, sz_ZERO);
    Value * hashStart = b->CreateSub(keyMarkPos, hashLen);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), b->getRawInputPointer("byteData", hashStart), hashLen);
    codewordVal_debug = b->CreateOr(b->CreateShl(codewordVal_debug, lg.MAX_HASH_BITS), thePfx);
#endif

#if 0
    b->CallPrintInt("decmp-tableIdxHash", b->CreateAnd(codewordVal, lg.TABLE_MASK));
#endif

    Value * subTablePtr = b->CreateGEP(hashTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    // codewordVal = b->CreateOr(b->CreateAnd(codewordVal, lg.EXTRA_BITS_MASK), b->CreateShl(codewordVal, lg.EXTRA_BITS));
    Value * tableIdxHash = b->CreateAnd(codewordVal, lg.TABLE_MASK, "tableIdx");
    // tableIdxHash = b->CreateSelect(b->CreateAnd(b->CreateICmpULT(tableIdxHash, sz_HALF_TBL_IDX), b->CreateICmpEQ(b->CreateAnd(thePfxHashBits, sz_ONE), sz_ONE)),
    //                                b->CreateAdd(sz_HALF_TBL_IDX, tableIdxHash), tableIdxHash);
    Value * keyIdxPtr = b->CreateGEP(subTablePtr, b->CreateMul(tableIdxHash, keyLength));
    Value * tblEntryPtr = b->CreateInBoundsGEP(keyIdxPtr, sz_ZERO);
    // Use two halfSymLen loads to get hash and symbol values.
    Value * tblPtr1 = b->CreateBitCast(tblEntryPtr, lg.halfSymPtrTy);
    Value * tblPtr2 = b->CreateBitCast(b->CreateGEP(tblEntryPtr, keyOffset), lg.halfSymPtrTy);
    Value * symPtr1 = b->CreateBitCast(b->getRawInputPointer("byteData", keyStartPos), lg.halfSymPtrTy);
    Value * symPtr2 = b->CreateBitCast(b->getRawInputPointer("byteData", b->CreateAdd(keyStartPos, keyOffset)), lg.halfSymPtrTy);

    // Check to see if the hash table entry is nonzero (already assigned).
    Value * sym1 = b->CreateLoad(symPtr1);
    Value * sym2 = b->CreateLoad(symPtr2);
    Value * entry1 = b->CreateMonitoredScalarFieldLoad("hashTable", tblPtr1);
    Value * entry2 = b->CreateMonitoredScalarFieldLoad("hashTable", tblPtr2);
#ifdef PRINT_DECOMPRESSION_DICT_INFO
    Value * pfxLgthMask = thePfx;
    pfxLgthMask = b->CreateTrunc(b->CreateAnd(pfxLgthMask, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    Value * lgthBase = b->CreateSub(keyLength, lg.LO);
    Value * pfxOffset1 = b->CreateAdd(lg.PREFIX_BASE, lgthBase);
    Value * multiplier1 = b->CreateMul(lg.RANGE, pfxLgthMask);
    Value * ZTF_prefix = b->CreateAdd(pfxOffset1, multiplier1, "ZTF_prefix");
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength);
    b->CallPrintInt("hashCode", b->CreateOr(codewordVal_debug, thePfx));
    // b->CallPrintInt("keyLength", keyLength);
#endif
#ifdef CHECK_COMPRESSION_DECOMPRESSION_STORE
    b->CallPrintInt("hashCode", keyHash);
    b->CallPrintInt("keyStartPos", keyStartPos);
    b->CallPrintInt("keyLength", keyLength);
#endif
    // store/replace phrase in hashtable
    b->CreateMonitoredScalarFieldStore("hashTable", sym1, tblPtr1);
    b->CreateMonitoredScalarFieldStore("hashTable", sym2, tblPtr2);
    b->CreateBr(nextKey);

    b->SetInsertPoint(nextKey);
#if 0
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), tblPtr1, b->CreateSub(keyLength, keyOffset));
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), tblPtr2, keyOffset);
#endif
    Value * dropKey = b->CreateResetLowestBit(theKeyWord);
    Value * thisWordDone = b->CreateICmpEQ(dropKey, sz_ZERO);
    // There may be more keys in the key mask.
    Value * nextKeyMask = b->CreateSelect(thisWordDone, b->CreateResetLowestBit(keyMaskPhi), keyMaskPhi);
    BasicBlock * currentBB = b->GetInsertBlock();
    keyMaskPhi->addIncoming(nextKeyMask, currentBB);
    keyWordPhi->addIncoming(dropKey, currentBB);
    b->CreateCondBr(b->CreateICmpNE(nextKeyMask, sz_ZERO), keyProcessingLoop, keysDone);

    b->SetInsertPoint(keysDone);
    b->CreateCondBr(decmpFirst, strideDone, replaceCodewords);

    b->SetInsertPoint(replaceCodewords);
    // replace codewords by decompressed phrases
    Value * hashWordBasePtr = b->getInputStreamBlockPtr("hashMarks0", sz_ZERO, strideBlockOffset);
    hashWordBasePtr = b->CreateBitCast(hashWordBasePtr, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(hashMask, sz_ZERO), hashesDone, hashProcessingLoop);

    b->SetInsertPoint(hashProcessingLoop);
    PHINode * const hashMaskPhi = b->CreatePHI(sizeTy, 2);
    hashMaskPhi->addIncoming(hashMask, replaceCodewords);
    PHINode * const hashWordPhi = b->CreatePHI(sizeTy, 2);
    hashWordPhi->addIncoming(sz_ZERO, replaceCodewords);
    Value * hashWordIdx = b->CreateCountForwardZeroes(hashMaskPhi, "hashWordIdx");
    Value * nextHashWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(hashWordBasePtr, hashWordIdx)), sizeTy);
    Value * theHashWord = b->CreateSelect(b->CreateICmpEQ(hashWordPhi, sz_ZERO), nextHashWord, hashWordPhi);
    Value * hashWordPos = b->CreateAdd(stridePos, b->CreateMul(hashWordIdx, sw.WIDTH));
    Value * hashPosInWord = b->CreateCountForwardZeroes(theHashWord);
    Value * hashMarkPos = b->CreateAdd(hashWordPos, hashPosInWord, "hashMarkPos");
    DEBUG_PRINT("hashMarkPos", hashMarkPos);
    Value * hashPfxPos = b->CreateSub(hashMarkPos, lg.MAX_INDEX);
    Value * const hashPfx = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("byteData", hashPfxPos)), sizeTy);
    DEBUG_PRINT("hashPfx", hashPfx);
    // Build up a single encoded value from the ZTF code sequence.
    Value * pfxGroupLen = b->CreateSub(hashPfx, lg.PREFIX_BASE, "encodedVal");
    /*
    pfxGroupLen                = 0-7, 0-7, 0-FF, 0-FF, 0-FF
    bits to calculate len      = 0,   0,   2,    3,    4
    */
    Value * curPos = hashMarkPos;
    Value * encodedVal = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("byteData", curPos)), sizeTy);
    // encodedVal = b->CreateShl(encodedVal, lg.LAST_SUFFIX_SHIFT_BITS);
#if 0
    Value * encodedVal_debug = encodedVal;
#endif
    //b->CallPrintInt("lastSuffixByte", encodedVal);
    encodedVal = b->CreateSelect(b->CreateICmpUGE(encodedVal, b->getSize(0x80)), b->CreateSub(encodedVal, b->getSize(0x80)), encodedVal);
    // encodedVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(encodedVal, sz_ONE), b->CreateShl(encodedVal, sz_ONE)),
    //                               encodedVal);
    for (unsigned i = 1; i < lg.groupInfo.encoding_bytes-1; i++) {
        curPos = b->CreateSub(curPos, sz_ONE);
        Value * suffixByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("byteData", curPos)), sizeTy);
        //b->CallPrintInt("suffixByte"+std::to_string(i), suffixByte);
        encodedVal = b->CreateShl(encodedVal, lg.HASH_SHIFT_BITS);
        encodedVal = b->CreateOr(encodedVal, suffixByte, "encodedVal");
#if 0
        encodedVal_debug = b->CreateOr(b->CreateShl(encodedVal_debug, lg.MAX_HASH_BITS), suffixByte);
#endif
    }
    /// WIP: add the logic to extract LAST_SUFFIX_MASK bits for k-symbol phrases
    Value * symLength = b->CreateAdd(b->CreateAnd(pfxGroupLen, lg.PHRASE_EXTENSION_MASK), lg.LO, "symLength");
    /*
    extract PREFIX_LENGTH_MASK bits from prefix -> required for dict index lookup
    * get the length_range from key length
    * key_len - lg.lo = length_range
    * PREFIX_BASE + length_range = pfxOffset
    * PFX - pfxOffset = multiplier
    * multiplier/lg.RANGE = PREFIX_LENGTH_MASK bits
    */
    Value * len_range = b->CreateSub(symLength, lg.LO);
    Value * pfxOffset = b->CreateAdd(lg.PREFIX_BASE, len_range);
    Value * multiplier = b->CreateSub(hashPfx, pfxOffset);
    Value * pfxHashBits = b->CreateUDiv(multiplier, lg.RANGE);
    pfxHashBits =  b->CreateTrunc(pfxHashBits, b->getInt64Ty());
    /// CHECK: Assertion for CreateUDiv(multiplier, lg.RANGE)
    Value * prefixByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("byteData", curPos)), sizeTy);
#if 0
    encodedVal_debug = b->CreateOr(b->CreateShl(encodedVal_debug, lg.MAX_HASH_BITS), hashPfx);
#endif
    Value * validLength = b->CreateAnd(b->CreateICmpUGE(symLength, lg.LO), b->CreateICmpULE(symLength, lg.HI));
    DEBUG_PRINT("symLength", symLength);
    b->CreateCondBr(validLength, lookupSym, nextHash);
    b->SetInsertPoint(lookupSym);
#if 0
    b->CallPrintInt("DhashVal-lookup", b->CreateAnd(encodedVal, lg.TABLE_MASK));
#endif
    Value * symStartPos = b->CreateSub(hashMarkPos, b->CreateSub(symLength, sz_ONE), "symStartPos");
    Value * symOffset = b->CreateSub(symLength, lg.HALF_LENGTH);

    subTablePtr = b->CreateGEP(hashTableBasePtr, b->CreateMul(b->CreateSub(symLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    // encodedVal = b->CreateOr(b->CreateAnd(encodedVal, lg.EXTRA_BITS_MASK), b->CreateShl(encodedVal, lg.EXTRA_BITS));
    tableIdxHash = b->CreateAnd(encodedVal, lg.TABLE_MASK);
    // tableIdxHash = b->CreateSelect(b->CreateAnd(b->CreateICmpULT(tableIdxHash, sz_HALF_TBL_IDX), b->CreateICmpEQ(b->CreateAnd(pfxHashBits, sz_ONE), sz_ONE)),
    //                 b->CreateAdd(sz_HALF_TBL_IDX, tableIdxHash), tableIdxHash);
    keyIdxPtr = b->CreateGEP(subTablePtr, b->CreateMul(tableIdxHash, symLength));
    tblEntryPtr = b->CreateInBoundsGEP(keyIdxPtr, sz_ZERO);

    // Use two halfSymLen loads to get hash and symbol values.
    tblPtr1 = b->CreateBitCast(tblEntryPtr, lg.halfSymPtrTy);
    tblPtr2 = b->CreateBitCast(b->CreateGEP(tblEntryPtr, symOffset), lg.halfSymPtrTy);
    entry1 = b->CreateAlignedLoad(tblPtr1, 1);
    entry2 = b->CreateAlignedLoad(tblPtr2, 1);
#if 0
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), tblPtr1, b->CreateSub(symLength, symOffset));
    b->CallPrintInt("codewordRead", encodedVal_debug);
#endif
    symPtr1 = b->CreateBitCast(b->getRawOutputPointer("result", symStartPos), lg.halfSymPtrTy);
    symPtr2 = b->CreateBitCast(b->getRawOutputPointer("result", b->CreateAdd(symStartPos, symOffset)), lg.halfSymPtrTy);
    b->CreateAlignedStore(entry1, symPtr1, 1);
    b->CreateAlignedStore(entry2, symPtr2, 1);
    b->CreateBr(nextHash);
    b->SetInsertPoint(nextHash);
    Value * dropHash = b->CreateResetLowestBit(theHashWord);
    Value * hashMaskDone = b->CreateICmpEQ(dropHash, sz_ZERO);
    // There may be more hashes in the hash mask.
    Value * nextHashMask = b->CreateSelect(hashMaskDone, b->CreateResetLowestBit(hashMaskPhi), hashMaskPhi);
    BasicBlock * hashBB = b->GetInsertBlock();
    hashMaskPhi->addIncoming(nextHashMask, hashBB);
    hashWordPhi->addIncoming(dropHash, hashBB);
    b->CreateCondBr(b->CreateICmpNE(nextHashMask, sz_ZERO), hashProcessingLoop, hashesDone);

    b->SetInsertPoint(hashesDone);
    b->CreateCondBr(decmpFirst, updateHashTable, strideDone);
    b->SetInsertPoint(strideDone);

    strideNo->addIncoming(nextStrideNo, strideDone);
    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), stridePrologue, stridesDone);

    b->SetInsertPoint(stridesDone);
    // If the segment ends in the middle of a 2-byte codeword, we need to
    // make sure that we still have access to the codeword in the next block.
    Value * processed = b->CreateSelect(b->isFinal(), avail, b->CreateSub(avail, lg.HI)); // b->CreateSub(avail, lg.HI);
    b->setProcessedItemCount("byteData", processed);
    // b->CallPrintInt("processed", processed);
    // b->CallPrintInt("avail", avail);

    Value * guaranteedProduced = b->CreateSub(avail, lg.HI);
    b->CreateMemCpy(b->getScalarFieldPtr("pendingOutput"), b->getRawOutputPointer("result", guaranteedProduced), lg.HI, 1);
    b->setProducedItemCount("result", b->CreateSelect(b->isFinal(), avail, guaranteedProduced));
}

/*
* Input:
candidateMatchesInDict -> 1-bit marker on the last byte of codewords corresponding to the candidate match phrases in dictionary.
nonCandidateMatchesInDict -> 1-bit marker on the last byte of codewords corresponding to all the non-candidate-match phrases in dictionary.
                          -> Required when a candidate match phrase's (phrase P1) codeword (codeword C1)
                             is used as codeword for a different phrase (phrase P2) in the subsequent segments.
codeWordInCipherText -> 1-bit marker on the last byte of all codewords in the cipher-text.
* Output:
allCandidateMatches -> 1-bit marker on the last byte of codewords in the cipher-text that match with the codewords in candidateMatchesInDict stream.
*/
FinalizeCandidateMatches::FinalizeCandidateMatches(BuilderRef b,
                           EncodingInfo encodingScheme,
                           StreamSet * const cmpData,
                           StreamSet * candidateMatchesInDict,
                           StreamSet * nonCandidateMatchesInDict,
                           StreamSet * codeWordInCipherText,
                           StreamSet * allCandidateMatches,
                           unsigned strideBlocks)
: MultiBlockKernel(b, "FinalizeCandidateMatches" + lengthGroupSuffix(encodingScheme, 0),
                   {Binding{"keyMarks00", candidateMatchesInDict},
                    Binding{"keyMarks10", nonCandidateMatchesInDict},
                    Binding{"hashMarks0", codeWordInCipherText},
                    Binding{"cmpData", cmpData, FixedRate(), Deferred() }},
                   {}, {}, {},
                   {InternalScalar{b->getBitBlockType(), "pendingMaskInverted"},
                   // 16 subtables, each sub-table has 32768 indices, each index can store 4-bytes data
                   InternalScalar{ArrayType::get(ArrayType::get(ArrayType::get(b->getInt8Ty(), encodingScheme.byLength.size()), phraseHashSubTableSize(encodingScheme, 2)),
                                   (encodingScheme.byLength[3].hi - encodingScheme.byLength[3].lo + 1)), "codewordTable"}}),
mEncodingScheme(encodingScheme) {
    mOutputStreamSets.emplace_back("allCandidateMatches", allCandidateMatches, FixedRate(), Delayed(encodingScheme.maxSymbolLength()) );
    setStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS));
}

void FinalizeCandidateMatches::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    ScanWordParameters sw(b, mStride);
    Constant * sz_STRIDE = b->getSize(mStride);
    Constant * sz_BLOCKS_PER_STRIDE = b->getSize(mStride/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_TWO = b->getSize(2);
    Constant * sz_THREE = b->getSize(3);
    Constant * sz_BITS = b->getSize(SIZE_T_BITS);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    Constant * sz_CODEWORD_PFX_START = b->getSize(0xC0);
    Constant * sz_CODEWORD_PFX_END = b->getSize(0xFF);
    Constant * sz_C0 = b->getSize(0xC0);
    Constant * sz_C7 = b->getSize(0xC7);
    Constant * sz_C8 = b->getSize(0xC8);
    Constant * sz_DF = b->getSize(0xDF);
    Constant * sz_E0 = b->getSize(0xE0);
    Constant * sz_EF = b->getSize(0xEF);
    Constant * sz_F0 = b->getSize(0xF0);
    Constant * sz_FF = b->getSize(0xFF);
    Constant * sz_32 = b->getSize(32);
    Constant * sz_HASH_SHIFT_BITS = b->getSize(7);
    Constant * sz_SUFFIX_MASK = b->getSize(0x7F);
    Constant * PHRASE_SUBTABLE_SIZE = b->getSize(phraseHashSubTableSize(mEncodingScheme, 2));
    Type * sizeTy = b->getSizeTy();
    Type * bitBlockPtrTy = b->getBitBlockType()->getPointerTo();

    Constant * sz_HALF_TBL_IDX_G0 = b->getSize(phraseHashSubTableSize(mEncodingScheme, 0) / 3);
    Constant * sz_HALF_TBL_IDX_G1 = b->getSize(phraseHashSubTableSize(mEncodingScheme, 1) / 2);
    Constant * sz_HALF_TBL_IDX_G2 = b->getSize(phraseHashSubTableSize(mEncodingScheme, 2) / 2);
    Constant * sz_HALF_TBL_IDX_G3 = sz_ZERO;

    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const stridePrologue = b->CreateBasicBlock("stridePrologue");
    BasicBlock * const outputMasksReady = b->CreateBasicBlock("outputMasksReady");
    BasicBlock * const strideMasksReady = b->CreateBasicBlock("strideMasksReady");
    BasicBlock * const keyProcessingLoop = b->CreateBasicBlock("keyProcessingLoop");
    BasicBlock * const nextKey = b->CreateBasicBlock("nextKey");
    BasicBlock * const hashProcessingLoop = b->CreateBasicBlock("hashProcessingLoop");
    BasicBlock * const markHashEntry = b->CreateBasicBlock("markHashEntry");
    BasicBlock * const markCodeword = b->CreateBasicBlock("markCodeword");
    BasicBlock * const nextHash = b->CreateBasicBlock("nextHash");
    BasicBlock * const hashesDone = b->CreateBasicBlock("hashesDone");
    BasicBlock * const updatePending = b->CreateBasicBlock("updatePending");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const hashMarksDone = b->CreateBasicBlock("hashMarksDone");
    BasicBlock * const compareCodewords = b->CreateBasicBlock("compareCodewords");
    BasicBlock * const updateHashTable = b->CreateBasicBlock("updateHashTable");
    BasicBlock * const CMkeysDone = b->CreateBasicBlock("CMkeysDone");
    BasicBlock * const NCMkeysDone = b->CreateBasicBlock("NCMkeysDone");
    BasicBlock * const NCMkeyProcessingLoop = b->CreateBasicBlock("NCMkeyProcessingLoop");
    BasicBlock * const nextKeyNCM = b->CreateBasicBlock("nextKeyNCM");
    BasicBlock * const markHashEntryNCM = b->CreateBasicBlock("markHashEntryNCM");
    BasicBlock * const lookupSym = b->CreateBasicBlock("lookupSym");

    Value * const initialPos = b->getProcessedItemCount("keyMarks00");
    Value * const avail = b->getAvailableItemCount("keyMarks00");
    Value * const initialProduced = b->getProducedItemCount("allCandidateMatches");
    Value * hashTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("codewordTable"), b->getInt8PtrTy());
    Value * pendingMask = b->CreateNot(b->getScalarField("pendingMaskInverted"));
    Value * producedPtr = b->CreateBitCast(b->getRawOutputPointer("allCandidateMatches", initialProduced), bitBlockPtrTy);
    b->CreateStore(pendingMask, producedPtr);

    Value * hashMarksPtr = b->CreateBitCast(b->getRawOutputPointer("allCandidateMatches", initialPos), bitBlockPtrTy);
    b->CreateBr(stridePrologue);

    b->SetInsertPoint(stridePrologue);
    PHINode * const strideNo = b->CreatePHI(sizeTy, 2);
    strideNo->addIncoming(sz_ZERO, entryBlock);
    Value * nextStrideNo = b->CreateAdd(strideNo, sz_ONE);
    Value * stridePos = b->CreateAdd(initialPos, b->CreateMul(strideNo, sz_STRIDE));
    Value * strideBlockOffset = b->CreateMul(strideNo, sz_BLOCKS_PER_STRIDE);

    initializeOutputMasks(b, sw, sz_BLOCKS_PER_STRIDE, strideBlockOffset, hashMarksPtr, outputMasksReady);
    b->SetInsertPoint(outputMasksReady);

    std::vector<Value *> keyMasks0(1);
    std::vector<Value *> keyMasks1(1);
    std::vector<Value *> hashMasks(1);
    initializeCodeWordMasks(b, sw, sz_BLOCKS_PER_STRIDE, 1, strideBlockOffset, keyMasks0, keyMasks1, hashMasks, strideMasksReady);
    Value * keyMaskCM = keyMasks0[0];
    Value * keyMaskNCM = keyMasks1[0];
    Value * hashMask = hashMasks[0];

    b->SetInsertPoint(strideMasksReady);
    Value * cmpCWFirst = b->CreateICmpUGE(b->CreateOr(keyMaskCM, keyMaskNCM), hashMask); // hashMarks should be decompressed first
    b->CreateCondBr(cmpCWFirst, compareCodewords, updateHashTable);
    b->SetInsertPoint(updateHashTable);

    Value * keyWordBasePtr = b->getInputStreamBlockPtr("keyMarks00", sz_ZERO, strideBlockOffset);
    keyWordBasePtr = b->CreateBitCast(keyWordBasePtr, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(keyMaskCM, sz_ZERO), CMkeysDone, keyProcessingLoop);

    b->SetInsertPoint(keyProcessingLoop);
    PHINode * const keyMaskCMPhi = b->CreatePHI(sizeTy, 2);
    keyMaskCMPhi->addIncoming(keyMaskCM, updateHashTable);
    PHINode * const keyWordPhi = b->CreatePHI(sizeTy, 2);
    keyWordPhi->addIncoming(sz_ZERO, updateHashTable);
    Value * keyWordIdx = b->CreateCountForwardZeroes(keyMaskCMPhi);
    Value * nextKeyWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(keyWordBasePtr, keyWordIdx)), sizeTy);
    Value * theKeyWord = b->CreateSelect(b->CreateICmpEQ(keyWordPhi, sz_ZERO), nextKeyWord, keyWordPhi);
    Value * keyWordPos = b->CreateAdd(stridePos, b->CreateMul(keyWordIdx, sw.WIDTH));
    Value * keyMarkPosInWord = b->CreateCountForwardZeroes(theKeyWord);
    Value * keyMarkPos = b->CreateAdd(keyWordPos, keyMarkPosInWord);

    Value * pfx1 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", b->CreateSub(keyMarkPos, sz_ONE))), sizeTy);
    Value * pfx2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", b->CreateSub(keyMarkPos, sz_TWO))), sizeTy);
    Value * pfx3 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", b->CreateSub(keyMarkPos, sz_THREE))), sizeTy);

    Value * pfx = pfx1;
    pfx = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(pfx2, sz_CODEWORD_PFX_START), b->CreateICmpULE(pfx2, sz_CODEWORD_PFX_END)), pfx2, pfx, "pfx");
    pfx = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(pfx3, sz_CODEWORD_PFX_START), b->CreateICmpULE(pfx3, sz_CODEWORD_PFX_END)), pfx3, pfx, "pfx");

    Value * groupNo = sz_ZERO;
    groupNo = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(pfx, sz_C8), b->CreateICmpULE(pfx, sz_DF)), sz_ONE, groupNo, "groupNo1");
    groupNo = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(pfx, sz_E0), b->CreateICmpULE(pfx, sz_EF)), sz_TWO, groupNo, "groupNo2");
    groupNo = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(pfx, sz_F0), b->CreateICmpULE(pfx, sz_FF)), sz_THREE, groupNo, "groupNo3");

    Value * pfx_base = sz_C0;
    pfx_base = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_ONE), sz_C8, pfx_base, "pfx_base");
    pfx_base = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_TWO), sz_E0, pfx_base, "pfx_base");
    pfx_base = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_THREE), sz_F0, pfx_base, "pfx_base");

    Value * lo = b->getSize(4);
    lo = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_ONE), b->getSize(5), lo, "lo");
    lo = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_TWO), b->getSize(9), lo, "lo");
    lo = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_THREE), b->getSize(17), lo, "lo");

    Value * hi = b->getSize(4);
    hi = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_ONE), b->getSize(8), hi, "hi");
    hi = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_TWO), b->getSize(16), hi, "hi");
    hi = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_THREE), b->getSize(32), hi, "hi");

    Value * extension_bits = b->CreateAdd(groupNo, sz_ONE);
    extension_bits = b->CreateSelect(b->CreateICmpULE(b->CreateSub(hi, lo), extension_bits), b->CreateSub(hi, lo), extension_bits, "extension_bits");
    Value * PHRASE_EXTENSION_MASK = b->CreateSub(b->CreateShl(sz_ONE, extension_bits), sz_ONE);

    Value * table_mask_bits = b->getSize(10);
    table_mask_bits = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_ONE), b->getSize(9), table_mask_bits, "table_mask_bits");
    table_mask_bits = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_TWO), b->getSize(15), table_mask_bits);
    table_mask_bits = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_THREE), b->getSize(14), table_mask_bits);
    Value * TABLE_MASK = b->CreateSub(b->CreateShl(sz_ONE, table_mask_bits), sz_ONE);

    Value * sz_HALF_TBL_IDX = sz_HALF_TBL_IDX_G0;
    sz_HALF_TBL_IDX = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_ONE), sz_HALF_TBL_IDX_G1, sz_HALF_TBL_IDX, "sz_HALF_TBL_IDX");
    sz_HALF_TBL_IDX = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_TWO), sz_HALF_TBL_IDX_G2, sz_HALF_TBL_IDX);
    sz_HALF_TBL_IDX = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_THREE), sz_HALF_TBL_IDX_G3, sz_HALF_TBL_IDX);

    Value * const thePfx = b->CreateZExt(pfx, sizeTy);
    Value * theGroupLen = b->CreateSub(thePfx, pfx_base);
    Value * keyLength = b->CreateAdd(b->CreateAnd(theGroupLen, PHRASE_EXTENSION_MASK), lo, "keyLength");

    Value * hashcodePos = keyMarkPos;
    Value * codewordVal = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", hashcodePos)), sizeTy);
    // codewordVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(codewordVal, sz_ONE), b->CreateShl(codewordVal, sz_ONE)),
    //                               codewordVal);

    // j = 1
    hashcodePos = b->CreateSub(hashcodePos, sz_ONE);
    Value * hashSfxByte1 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", hashcodePos)), sizeTy);
    codewordVal = b->CreateSelect(b->CreateICmpUGE(groupNo, sz_TWO), b->CreateOr(b->CreateShl(codewordVal, sz_HASH_SHIFT_BITS),
                                                                                 b->CreateAnd(hashSfxByte1, sz_SUFFIX_MASK)),
                                                                    codewordVal);
    // j = 2
    hashcodePos = b->CreateSub(hashcodePos, sz_ONE);
    Value * hashSfxByte2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", hashcodePos)), sizeTy);
    codewordVal = b->CreateSelect(b->CreateICmpEQ(groupNo, sz_THREE), b->CreateOr(b->CreateShl(codewordVal, sz_HASH_SHIFT_BITS),
                                                                                  b->CreateAnd(hashSfxByte2, sz_SUFFIX_MASK)),
                                                                      codewordVal);

    Value * keylen_range = b->CreateSub(keyLength, lo);
    Value * thePfxOffset = b->CreateAdd(pfx_base, keylen_range);
    Value * theMultiplier = b->CreateSub(thePfx, thePfxOffset);
    Value * lg_RANGE = b->CreateAdd(b->CreateSub(hi, lo), sz_ONE);
    Value * thePfxHashBits = b->CreateUDiv(theMultiplier, lg_RANGE);
    thePfxHashBits = b->CreateTrunc(thePfxHashBits, b->getInt64Ty());

    Value * tableIdxHash = b->CreateAnd(codewordVal, TABLE_MASK);
    // tableIdxHash = b->CreateSelect(b->CreateAnd(b->CreateICmpULT(tableIdxHash, sz_HALF_TBL_IDX), b->CreateICmpEQ(b->CreateAnd(thePfxHashBits, sz_ONE), sz_ONE)),
    //                 b->CreateAdd(sz_HALF_TBL_IDX, tableIdxHash), tableIdxHash);
    Value * subTablePtr = b->CreateGEP(hashTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lo), PHRASE_SUBTABLE_SIZE));
    // b->CallPrintInt("tableIdxHash", tableIdxHash);
    Value * keyIdxPtr = b->CreateGEP(subTablePtr, b->CreateMul(tableIdxHash, keyLength));
    // b->CallPrintInt("keyLength", keyLength);
    Value * tblEntryPtr = b->CreateGEP(keyIdxPtr, groupNo);
    // b->CallPrintInt("groupNo", groupNo);
    // b->CallPrintInt("tblEntryPtr", tblEntryPtr);
    Value * tblPtr = b->CreateBitCast(tblEntryPtr, b->getInt8PtrTy());
    Value * tblEntry = b->CreateMonitoredScalarFieldLoad("codewordTable", tblPtr);

    Value * entryVal = b->CreateTrunc(tblEntry, b->getInt8Ty());
    Value * entryExists = b->CreateICmpEQ(entryVal, b->getInt8(0x1));
    b->CreateCondBr(entryExists, nextKey, markHashEntry);

    b->SetInsertPoint(markHashEntry);
    b->CreateMonitoredScalarFieldStore("codewordTable", b->getInt8(0x1), tblPtr);
    // b->CallPrintInt("codewordVal-0x1", codewordVal);
    b->CreateBr(nextKey);

    b->SetInsertPoint(nextKey);
    Value * dropKey = b->CreateResetLowestBit(theKeyWord);
    Value * thisWordDone = b->CreateICmpEQ(dropKey, sz_ZERO);
    // There may be more keys in the key mask.
    Value * nextKeyMaskCM = b->CreateSelect(thisWordDone, b->CreateResetLowestBit(keyMaskCMPhi), keyMaskCMPhi);
    BasicBlock * currentBB = b->GetInsertBlock();
    keyMaskCMPhi->addIncoming(nextKeyMaskCM, currentBB);
    keyWordPhi->addIncoming(dropKey, currentBB);
    b->CreateCondBr(b->CreateICmpNE(nextKeyMaskCM, sz_ZERO), keyProcessingLoop, CMkeysDone);

    b->SetInsertPoint(CMkeysDone);
    Value * keyWord1BasePtr = b->getInputStreamBlockPtr("keyMarks10", sz_ZERO, strideBlockOffset);
    keyWord1BasePtr = b->CreateBitCast(keyWord1BasePtr, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(keyMaskNCM, sz_ZERO), NCMkeysDone, NCMkeyProcessingLoop);

    b->SetInsertPoint(NCMkeyProcessingLoop);
    PHINode * const keyMaskNCMPhi = b->CreatePHI(sizeTy, 2);
    keyMaskNCMPhi->addIncoming(keyMaskNCM, CMkeysDone);
    PHINode * const keyWordNCMPhi = b->CreatePHI(sizeTy, 2);
    keyWordNCMPhi->addIncoming(sz_ZERO, CMkeysDone);
    Value * keyWordNCMIdx = b->CreateCountForwardZeroes(keyMaskNCMPhi);
    Value * nextKeyWordNCM = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(keyWord1BasePtr, keyWordNCMIdx)), sizeTy);
    Value * theKeyWordNCM = b->CreateSelect(b->CreateICmpEQ(keyWordNCMPhi, sz_ZERO), nextKeyWordNCM, keyWordNCMPhi);
    Value * keyWordPosNCM = b->CreateAdd(stridePos, b->CreateMul(keyWordNCMIdx, sw.WIDTH));
    Value * keyMarkPosInWordNCM = b->CreateCountForwardZeroes(theKeyWordNCM);
    Value * keyMarkPosNCM = b->CreateAdd(keyWordPosNCM, keyMarkPosInWordNCM);

    Value * pfx1NCM = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", b->CreateSub(keyMarkPosNCM, sz_ONE))), sizeTy);
    Value * pfx2NCM = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", b->CreateSub(keyMarkPosNCM, sz_TWO))), sizeTy);
    Value * pfx3NCM = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", b->CreateSub(keyMarkPosNCM, sz_THREE))), sizeTy);

    Value * pfxNCM = pfx1NCM;
    pfxNCM = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(pfx2NCM, sz_CODEWORD_PFX_START), b->CreateICmpULE(pfx2NCM, sz_CODEWORD_PFX_END)), pfx2NCM, pfxNCM);
    pfxNCM = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(pfx3NCM, sz_CODEWORD_PFX_START), b->CreateICmpULE(pfx3NCM, sz_CODEWORD_PFX_END)), pfx3NCM, pfxNCM);

    Value * groupNoNCM = sz_ZERO;
    groupNoNCM = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(pfxNCM, sz_C8), b->CreateICmpULE(pfxNCM, sz_DF)), sz_ONE, groupNoNCM);
    groupNoNCM = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(pfxNCM, sz_E0), b->CreateICmpULE(pfxNCM, sz_EF)), sz_TWO, groupNoNCM);
    groupNoNCM = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(pfxNCM, sz_F0), b->CreateICmpULE(pfxNCM, sz_FF)), sz_THREE, groupNoNCM);

    Value * pfx_baseNCM = sz_C0;
    pfx_baseNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_ONE), sz_C8, pfx_baseNCM);
    pfx_baseNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_TWO), sz_E0, pfx_baseNCM);
    pfx_baseNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_THREE), sz_F0, pfx_baseNCM);

    Value * loNCM = b->getSize(4);
    loNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_ONE), b->getSize(5), loNCM);
    loNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_TWO), b->getSize(9), loNCM);
    loNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_THREE), b->getSize(17), loNCM);

    Value * hiNCM = b->getSize(4);
    hiNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_ONE), b->getSize(8), hiNCM);
    hiNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_TWO), b->getSize(16), hiNCM);
    hiNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_THREE), b->getSize(32), hiNCM);

    Value * extension_bitsNCM = b->CreateAdd(groupNoNCM, sz_ONE);
    extension_bitsNCM = b->CreateSelect(b->CreateICmpULE(b->CreateSub(hiNCM, loNCM), extension_bitsNCM), b->CreateSub(hiNCM, loNCM), extension_bitsNCM);
    Value * PHRASE_EXTENSION_MASK_NCM = b->CreateSub(b->CreateShl(sz_ONE, extension_bitsNCM), sz_ONE);

    Value * table_mask_bitsNCM = b->getSize(10);
    table_mask_bitsNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_ONE), b->getSize(9), table_mask_bitsNCM);
    table_mask_bitsNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_TWO), b->getSize(15), table_mask_bitsNCM);
    table_mask_bitsNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_THREE), b->getSize(14), table_mask_bitsNCM);
    Value * TABLE_MASK_NCM = b->CreateSub(b->CreateShl(sz_ONE, table_mask_bitsNCM), sz_ONE);

    sz_HALF_TBL_IDX = sz_HALF_TBL_IDX_G0;
    sz_HALF_TBL_IDX = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_ONE), sz_HALF_TBL_IDX_G1, sz_HALF_TBL_IDX);
    sz_HALF_TBL_IDX = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_TWO), sz_HALF_TBL_IDX_G2, sz_HALF_TBL_IDX);
    sz_HALF_TBL_IDX = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_THREE), sz_HALF_TBL_IDX_G3, sz_HALF_TBL_IDX);

    Value * const thePfxNCM = b->CreateZExt(pfxNCM, sizeTy);
    Value * theGroupLenNCM = b->CreateSub(thePfxNCM, pfx_baseNCM);
    Value * keyLengthNCM = b->CreateAdd(b->CreateAnd(theGroupLenNCM, PHRASE_EXTENSION_MASK_NCM), loNCM, "keyLength");

    Value * hashcodePosNCM = keyMarkPosNCM;
    Value * codewordValNCM = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", hashcodePosNCM)), sizeTy);
    // codewordVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(codewordVal, sz_ONE), b->CreateShl(codewordVal, sz_ONE)),
    //                               codewordVal);

    // j = 1
    hashcodePosNCM = b->CreateSub(hashcodePosNCM, sz_ONE);
    Value * sfxByte1NCM = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", hashcodePosNCM)), sizeTy);
    codewordValNCM = b->CreateSelect(b->CreateICmpUGE(groupNoNCM, sz_TWO), b->CreateOr(b->CreateShl(codewordValNCM, sz_HASH_SHIFT_BITS),
                                                                           b->CreateAnd(sfxByte1NCM, sz_SUFFIX_MASK)),
                                                                           codewordValNCM);
    // j = 2
    hashcodePosNCM = b->CreateSub(hashcodePosNCM, sz_ONE);
    Value * sfxByte2NCM = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", hashcodePosNCM)), sizeTy);
    codewordValNCM = b->CreateSelect(b->CreateICmpEQ(groupNoNCM, sz_THREE), b->CreateOr(b->CreateShl(codewordValNCM, sz_HASH_SHIFT_BITS),
                                                                            b->CreateAnd(sfxByte2NCM, sz_SUFFIX_MASK)),
                                                                            codewordValNCM);

    Value * keylen_rangeNCM = b->CreateSub(keyLengthNCM, loNCM);
    Value * thePfxOffsetNCM = b->CreateAdd(pfx_baseNCM, keylen_rangeNCM);
    Value * theMultiplierNCM = b->CreateSub(thePfxNCM, thePfxOffsetNCM);
    Value * lg_RANGE_NCM = b->CreateAdd(b->CreateSub(hiNCM, loNCM), sz_ONE);
    Value * thePfxHashBitsNCM = b->CreateUDiv(theMultiplierNCM, lg_RANGE_NCM);
    thePfxHashBitsNCM = b->CreateTrunc(thePfxHashBitsNCM, b->getInt64Ty());

    Value * tableIdxHashNCM = b->CreateAnd(codewordValNCM, TABLE_MASK_NCM);
    // tableIdxHashNCM = b->CreateSelect(b->CreateAnd(b->CreateICmpULT(tableIdxHashNCM, sz_HALF_TBL_IDX), b->CreateICmpEQ(b->CreateAnd(thePfxHashBitsNCM, sz_ONE), sz_ONE)),
    //                   b->CreateAdd(sz_HALF_TBL_IDX, tableIdxHashNCM), tableIdxHashNCM);
    Value * subTablePtrNCM = b->CreateGEP(hashTableBasePtr, b->CreateMul(b->CreateSub(keyLengthNCM, loNCM), PHRASE_SUBTABLE_SIZE));
    // b->CallPrintInt("tableIdxHashNCM", tableIdxHashNCM);
    Value * keyIdxPtrNCM = b->CreateGEP(subTablePtrNCM, b->CreateMul(tableIdxHashNCM, keyLengthNCM));
    // b->CallPrintInt("keyLengthNCM", keyLengthNCM);
    Value * tblEntryPtrNCM = b->CreateGEP(keyIdxPtrNCM, groupNoNCM);
    Value * tblPtrNCM = b->CreateBitCast(tblEntryPtrNCM, b->getInt8PtrTy());
    // b->CallPrintInt("groupNoNCM", groupNoNCM);
    // b->CallPrintInt("tblEntryPtrNCM", tblEntryPtrNCM);
    Value * tblEntryNCM = b->CreateMonitoredScalarFieldLoad("codewordTable", tblPtrNCM);

    Value * entryValNCM = b->CreateTrunc(tblEntryNCM, b->getInt8Ty());
    Value * entryExistsNCM = b->CreateICmpEQ(entryValNCM, b->getInt8(0x2));
    b->CreateCondBr(entryExistsNCM, nextKeyNCM, markHashEntryNCM);

    b->SetInsertPoint(markHashEntryNCM);
    b->CreateMonitoredScalarFieldStore("codewordTable", b->getInt8(0x2), tblPtrNCM);
    // b->CallPrintInt("codewordValNCM-0x2", codewordValNCM);
    b->CreateBr(nextKeyNCM);

    b->SetInsertPoint(nextKeyNCM);
    Value * dropKeyNCM = b->CreateResetLowestBit(theKeyWordNCM);
    Value * thisWordDoneNCM = b->CreateICmpEQ(dropKeyNCM, sz_ZERO);
    Value * nextKeyMaskNCM = b->CreateSelect(thisWordDoneNCM, b->CreateResetLowestBit(keyMaskNCMPhi), keyMaskNCMPhi);
    BasicBlock * currentBB_NCM = b->GetInsertBlock();
    keyMaskNCMPhi->addIncoming(nextKeyMaskNCM, currentBB_NCM);
    keyWordNCMPhi->addIncoming(dropKeyNCM, currentBB_NCM);
    b->CreateCondBr(b->CreateICmpNE(nextKeyMaskNCM, sz_ZERO), NCMkeyProcessingLoop, NCMkeysDone);

    b->SetInsertPoint(NCMkeysDone);
    b->CreateCondBr(cmpCWFirst, stridesDone, compareCodewords);
    b->SetInsertPoint(compareCodewords);

    // mark 1-bit for codewords in codewordTable
    Value * hashWordBasePtr = b->getInputStreamBlockPtr("hashMarks0", sz_ZERO, strideBlockOffset);
    hashWordBasePtr = b->CreateBitCast(hashWordBasePtr, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(hashMask, sz_ZERO), hashesDone, hashProcessingLoop);

    b->SetInsertPoint(hashProcessingLoop);
    PHINode * const hashMaskPhi = b->CreatePHI(sizeTy, 2);
    hashMaskPhi->addIncoming(hashMask, compareCodewords);
    PHINode * const hashWordPhi = b->CreatePHI(sizeTy, 2);
    hashWordPhi->addIncoming(sz_ZERO, compareCodewords);
    Value * hashWordIdx = b->CreateCountForwardZeroes(hashMaskPhi);
    Value * nextHashWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(hashWordBasePtr, hashWordIdx)), sizeTy);
    Value * theHashWord = b->CreateSelect(b->CreateICmpEQ(hashWordPhi, sz_ZERO), nextHashWord, hashWordPhi);
    Value * hashWordPos = b->CreateAdd(stridePos, b->CreateMul(hashWordIdx, sw.WIDTH));
    Value * hashPosInWord = b->CreateCountForwardZeroes(theHashWord);
    Value * hashMarkPos = b->CreateAdd(hashWordPos, hashPosInWord);
    // b->CallPrintInt("hashMarkPos", hashMarkPos);
    Value * hashPfx1 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", b->CreateSub(hashMarkPos, sz_ONE))), sizeTy);
    Value * hashPfx2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", b->CreateSub(hashMarkPos, sz_TWO))), sizeTy);
    Value * hashPfx3 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", b->CreateSub(hashMarkPos, sz_THREE))), sizeTy);

    Value * hashPfx = hashPfx1;
    hashPfx = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(hashPfx2, sz_CODEWORD_PFX_START), b->CreateICmpULE(hashPfx2, sz_CODEWORD_PFX_END)), hashPfx2, hashPfx);
    hashPfx = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(hashPfx3, sz_CODEWORD_PFX_START), b->CreateICmpULE(hashPfx3, sz_CODEWORD_PFX_END)), hashPfx3, hashPfx);

    Value * hashGroupNo = sz_ZERO;
    hashGroupNo = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(hashPfx, sz_C8), b->CreateICmpULE(hashPfx, sz_DF)), sz_ONE, hashGroupNo);
    hashGroupNo = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(hashPfx, sz_E0), b->CreateICmpULE(hashPfx, sz_EF)), sz_TWO, hashGroupNo);
    hashGroupNo = b->CreateSelect(b->CreateAnd(b->CreateICmpUGE(hashPfx, sz_F0), b->CreateICmpULE(hashPfx, sz_FF)), sz_THREE, hashGroupNo);

    Value * hash_lo = b->getSize(4);
    hash_lo = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_ONE), b->getSize(5), hash_lo);
    hash_lo = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_TWO), b->getSize(9), hash_lo);
    hash_lo = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_THREE), b->getSize(17), hash_lo);

    Value * hash_hi = b->getSize(4);
    hash_hi = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_ONE), b->getSize(8), hash_hi);
    hash_hi = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_TWO), b->getSize(16), hash_hi);
    hash_hi = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_THREE), b->getSize(32), hash_hi);

    Value * hash_pfx_base = sz_C0;
    hash_pfx_base = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_ONE), sz_C8, hash_pfx_base);
    hash_pfx_base = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_TWO), sz_E0, hash_pfx_base);
    hash_pfx_base = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_THREE), sz_F0, hash_pfx_base);

    Value * hash_table_mask_bits = b->getSize(10);
    hash_table_mask_bits = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_ONE), b->getSize(9), hash_table_mask_bits);
    hash_table_mask_bits = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_TWO), b->getSize(15), hash_table_mask_bits);
    hash_table_mask_bits = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_THREE), b->getSize(14), hash_table_mask_bits);
    Value * HASH_TABLE_MASK = b->CreateSub(b->CreateShl(sz_ONE, hash_table_mask_bits), sz_ONE);

    sz_HALF_TBL_IDX = sz_HALF_TBL_IDX_G0;
    sz_HALF_TBL_IDX = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_ONE), sz_HALF_TBL_IDX_G1, sz_HALF_TBL_IDX);
    sz_HALF_TBL_IDX = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_TWO), sz_HALF_TBL_IDX_G2, sz_HALF_TBL_IDX);
    sz_HALF_TBL_IDX = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_THREE), sz_HALF_TBL_IDX_G3, sz_HALF_TBL_IDX);

    Value * pfxGroupLen = b->CreateSub(hashPfx, hash_pfx_base);
    Value * curHashPos = hashMarkPos;
    Value * encodedVal = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", curHashPos)), sizeTy);
    // encodedVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(encodedVal, sz_ONE), b->CreateShl(encodedVal, sz_ONE)),
    //                               encodedVal);

    // j = 1
    curHashPos = b->CreateSub(curHashPos, sz_ONE);
    hashSfxByte1 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", curHashPos)), sizeTy);
    encodedVal = b->CreateSelect(b->CreateICmpUGE(hashGroupNo, sz_TWO), b->CreateOr(b->CreateShl(encodedVal, sz_HASH_SHIFT_BITS),
                                                                                 b->CreateAnd(hashSfxByte1, sz_SUFFIX_MASK)),
                                                                     encodedVal);
    // j = 2
    curHashPos = b->CreateSub(curHashPos, sz_ONE);
    hashSfxByte2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("cmpData", curHashPos)), sizeTy);
    encodedVal = b->CreateSelect(b->CreateICmpEQ(hashGroupNo, sz_THREE), b->CreateOr(b->CreateShl(encodedVal, sz_HASH_SHIFT_BITS),
                                                                                 b->CreateAnd(hashSfxByte2, sz_SUFFIX_MASK)),
                                                                    encodedVal);

    Value * hash_extension_bits = b->CreateAdd(hashGroupNo, sz_ONE);
    hash_extension_bits = b->CreateSelect(b->CreateICmpULE(b->CreateSub(hash_hi, hash_lo), hash_extension_bits), b->CreateSub(hash_hi, hash_lo), hash_extension_bits);
    Value * HASH_EXTENSION_MASK = b->CreateSub(b->CreateShl(sz_ONE, hash_extension_bits), sz_ONE);

    Value * symLength = b->CreateAdd(b->CreateAnd(pfxGroupLen, HASH_EXTENSION_MASK), hash_lo, "symLength");
    Value * len_range = b->CreateSub(symLength, hash_lo);
    Value * pfxOffset = b->CreateAdd(hash_pfx_base, len_range);
    Value * multiplier = b->CreateSub(hashPfx, pfxOffset);
    Value * lg_RANGE_HASH = b->CreateAdd(b->CreateSub(hash_hi, hash_lo), sz_ONE);
    Value * pfxHashBits = b->CreateUDiv(multiplier, lg_RANGE_HASH);

    Value * validLength = b->CreateAnd(b->CreateICmpUGE(symLength, hash_lo), b->CreateICmpULE(symLength, hash_hi));
    b->CreateCondBr(validLength, lookupSym, nextHash);

    b->SetInsertPoint(lookupSym);
    subTablePtr = b->CreateGEP(hashTableBasePtr, b->CreateMul(b->CreateSub(symLength, hash_lo), PHRASE_SUBTABLE_SIZE));
    tableIdxHash = b->CreateAnd(encodedVal, HASH_TABLE_MASK);
    // tableIdxHash = b->CreateSelect(b->CreateAnd(b->CreateICmpULT(tableIdxHash, sz_HALF_TBL_IDX), b->CreateICmpEQ(b->CreateAnd(pfxHashBits, sz_ONE), sz_ONE)),
    //                 b->CreateAdd(sz_HALF_TBL_IDX, tableIdxHash), tableIdxHash);
    keyIdxPtr = b->CreateGEP(subTablePtr, b->CreateMul(tableIdxHash, symLength));
    tblEntryPtr = b->CreateInBoundsGEP(keyIdxPtr, hashGroupNo);
    tblPtr = b->CreateBitCast(tblEntryPtr, b->getInt8PtrTy());
    // b->CallPrintInt("tableIdxHash-hash", tableIdxHash);
    // b->CallPrintInt("symLength", symLength);
    // b->CallPrintInt("hashGroupNo", hashGroupNo);
    // b->CallPrintInt("tblEntryPtr-hash", tblEntryPtr);
    tblEntry = b->CreateMonitoredScalarFieldLoad("codewordTable", tblPtr);

    entryVal = b->CreateTrunc(tblEntry, b->getInt8Ty());
    // b->CallPrintInt("encodedVal", encodedVal);
    b->CreateCondBr(b->CreateICmpEQ(entryVal, b->getInt8(0x1)), markCodeword, nextHash);

    b->SetInsertPoint(markCodeword);
    Value * hashEndBase = b->CreateSub(hashMarkPos, b->CreateURem(hashMarkPos, sz_BITS));
    Value * markOffset = b->CreateSub(hashMarkPos, hashEndBase);
    Value * const outputBasePtr = b->CreateBitCast(b->getRawOutputPointer("allCandidateMatches", hashEndBase), sizeTy->getPointerTo());
    Value * initialMark = b->CreateAlignedLoad(outputBasePtr, 1);
    Value * updatedMask = b->CreateOr(initialMark, b->CreateShl(sz_ONE, markOffset));
    b->CreateAlignedStore(updatedMask, outputBasePtr, 1);
    b->CreateBr(nextHash);

    b->SetInsertPoint(nextHash);
    Value * dropHash = b->CreateResetLowestBit(theHashWord);
    Value * hashMaskDone = b->CreateICmpEQ(dropHash, sz_ZERO);
    // There may be more hashes in the hash mask.
    Value * nextHashMask = b->CreateSelect(hashMaskDone, b->CreateResetLowestBit(hashMaskPhi), hashMaskPhi);
    BasicBlock * hashBB = b->GetInsertBlock();
    hashMaskPhi->addIncoming(nextHashMask, hashBB);
    hashWordPhi->addIncoming(dropHash, hashBB);
    b->CreateCondBr(b->CreateICmpNE(nextHashMask, sz_ZERO), hashProcessingLoop, hashesDone);

    b->SetInsertPoint(hashesDone);
    strideNo->addIncoming(nextStrideNo, hashesDone);
    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), stridePrologue, stridesDone);

    b->SetInsertPoint(stridesDone);
    Value * produced = b->CreateSelect(b->isFinal(), avail, b->CreateSub(avail, sz_BLOCKWIDTH));
    b->setProducedItemCount("allCandidateMatches", produced);

    Value * processed = b->CreateSelect(b->isFinal(), avail, b->CreateSub(avail, sz_32));
    b->setProcessedItemCount("cmpData", processed);

    b->CreateCondBr(b->isFinal(), hashMarksDone, updatePending);
    b->SetInsertPoint(updatePending);
    Value * pendingPtr = b->CreateBitCast(b->getRawOutputPointer("allCandidateMatches", produced), bitBlockPtrTy);
    Value * lastMask = b->CreateBlockAlignedLoad(pendingPtr);
    b->setScalarField("pendingMaskInverted", b->CreateNot(lastMask));

    b->CreateBr(hashMarksDone);
    b->SetInsertPoint(hashMarksDone);
}

//NOTE TO SELF: segmentPartialSum -> 1 integer value per segment => BoundedRate(0, 1) ====> not a rational number
SegOffsetCalcKernel::SegOffsetCalcKernel(BuilderRef b,
                                StreamSet * byteData,
                                StreamSet * segBoundary,
                                StreamSet * segmentPartialSum,
                                bool offsetFlag,
                                unsigned strideBlocks)
: MultiBlockKernel(b, "SegOffsetCalcKernel" +  std::to_string(strideBlocks) + std::to_string(offsetFlag),
                   {Binding{"byteData", byteData, FixedRate()},
                    Binding{"segBreaks", segBoundary, FixedRate()}},
                   {}, {}, {},{}), mOffsetFlag(offsetFlag) {
    mOutputStreamSets.emplace_back("segmentPartialSum", segmentPartialSum, PopcountOf("segBreaks"));
    addInternalScalar(b->getSizeTy(), "index");
    addInternalScalar(b->getSizeTy(), "processedSubBlockSize");
    addInternalScalar(b->getSizeTy(), "producedIdx");
    setStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS));
}
void SegOffsetCalcKernel::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    ScanWordParameters sw(b, mStride);
    Constant * sz_STRIDE = b->getSize(mStride);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    Constant * sz_BLOCKS_PER_STRIDE = b->getSize(mStride/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Type * sizeTy = b->getSizeTy();

    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const stridePrologue = b->CreateBasicBlock("stridePrologue");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const endPosReady = b->CreateBasicBlock("endPosReady");
    BasicBlock * const writePartialSum = b->CreateBasicBlock("writePartialSum");
    BasicBlock * const checkNext = b->CreateBasicBlock("checkNext");
    BasicBlock * const writeNextSegStart = b->CreateBasicBlock("writeNextSegStart");
    BasicBlock * const segDone = b->CreateBasicBlock("segDone");

    Value * const initialProcessedLines = b->getProcessedItemCount("segBreaks");
    Value * const avail = b->getAvailableItemCount("byteData");
    b->CreateBr(stridePrologue);

    b->SetInsertPoint(stridePrologue);
    PHINode * const strideNo = b->CreatePHI(sizeTy, 2);
    strideNo->addIncoming(sz_ZERO, entryBlock);
    Value * nextStrideNo = b->CreateAdd(strideNo, sz_ONE);

    Value * strideBlockOffset = b->CreateMul(strideNo, sz_BLOCKS_PER_STRIDE);
    Value * segEndInStride = getSegBoundaryPos(b, sw, sz_BLOCKWIDTH, sz_BLOCKS_PER_STRIDE, strideBlockOffset, endPosReady);

    b->SetInsertPoint(endPosReady);
    // b->CallPrintInt("segEndInStride", segEndInStride);
    b->CreateCondBr(b->CreateICmpUGT(segEndInStride, sz_ZERO), writePartialSum, checkNext); ///CHECK: causing wrong number of segEnd for wiki-all?

    b->SetInsertPoint(writePartialSum);
    Value * const nextSegEnd = b->CreateAdd(b->CreateAdd(initialProcessedLines, b->CreateMul(strideNo, sz_STRIDE)), segEndInStride);
    // b->CallPrintInt("nextSegEnd", nextSegEnd);
    b->CreateStore(b->CreateTrunc(nextSegEnd, b->getInt64Ty()), b->getRawOutputPointer("segmentPartialSum", b->getScalarField("producedIdx")));
    // Value * ptr1 = b->CreateBitCast(b->getRawOutputPointer("segmentPartialSum", b->getScalarField("producedIdx")), b->getInt64Ty()->getPointerTo());
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), ptr1, b->getSize(1));
    // b->CallPrintInt("producedIdx", b->getScalarField("producedIdx"));
    b->setScalarField("producedIdx", b->CreateAdd(b->getScalarField("producedIdx"), sz_ONE));
    b->CreateBr(checkNext);

    b->SetInsertPoint(checkNext);
    strideNo->addIncoming(nextStrideNo, checkNext);
    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), stridePrologue, stridesDone);

    b->SetInsertPoint(stridesDone);
    b->CreateCondBr(b->isFinal(), writeNextSegStart, segDone);

    b->SetInsertPoint(writeNextSegStart);
    // b->CallPrintInt("avail", avail);
    b->CreateStore(b->CreateTrunc(/*b->CreateAdd(avail, b->getSize(2))*/avail, b->getInt64Ty()), b->getRawOutputPointer("segmentPartialSum", b->getScalarField("producedIdx"))); /// NOTE TO SELF: avail + 1 to maintain same operations to determine segEnd in next kernels
    b->setScalarField("producedIdx", b->CreateAdd(b->getScalarField("producedIdx"), sz_ONE));
    b->CreateBr(segDone);

    b->SetInsertPoint(segDone);
    // b->setProducedItemCount("segmentPartialSum", b->getScalarField("producedIdx"));
}

// each compressed segment is definitely < 1048576 bytes. So per stride, byteData read is maximum to 1048576; to be precise, 
// filtereData produced each stride is minimum to the dictionary size of the segment and maximum to the size of the compressed segment (1048576)
SegmentFilter::SegmentFilter(BuilderRef b,
                                StreamSet * const MatchesBySegment,
                                StreamSet * const offsetStartData,
                                StreamSet * const offsetEndData,
                                StreamSet * const byteData,
                                StreamSet * const filtereData)
: MultiBlockKernel(b, "SegmentFilter_" +  std::to_string(offsetStartData->getNumElements()) + "_" + std::to_string(byteData->getNumElements()),
                   {Binding{"MatchesBySegment", MatchesBySegment, FixedRate(1)},
                    Binding{"offsetStartData", offsetStartData, FixedRate(1)},
                    // offsetStartData 1 more item than the number of segments.
                    // last value is the end of compressed bytes.
                    Binding{"offsetEndData", offsetEndData, FixedRate(1)},
                    Binding{"byteData", byteData, GreedyRate(1), Deferred()}},
                   {}, {}, {}, {}) {
    mOutputStreamSets.emplace_back("filtereData", filtereData, BoundedRate(0, 1048576));
    addInternalScalar(b->getSizeTy(), "bitIdx");
    addInternalScalar(b->getSizeTy(), "startOffset");
    /*
    index 0:
    offsetStartData -> start of seg 2
    offsetEndData   -> end of dict of seg 1
    segSize         -> offsetStartData - startOffset
    dictSize        -> offsetEndData - startOffset
    set startOffset to offsetStartData
    */
    setStride(1);
}
void SegmentFilter::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    // check the bit at segIdx in MatchesBySegment
    // if 1, memcpy byteData to filtereData
    //      memcpy size = offsetStartData[segIdx+1] - offsetStartData[segIdx]
    // else, memcpy only dictionary part to filtereData
    Type * const sizeTy = b->getSizeTy();
    Type * const blockTy = b->getBitBlockType();
    Value * const sz_ZERO = b->getSize(0);
    Value * const sz_ONE = b->getSize(1);
    BasicBlock * const entry = b->GetInsertBlock();
    BasicBlock * const startSegment = b->CreateBasicBlock("startSegment");
    BasicBlock * const processSegment = b->CreateBasicBlock("processSegment");
    BasicBlock * const segmentsDone = b->CreateBasicBlock("segmentsDone");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const filterSeg = b->CreateBasicBlock("filterSeg");
    BasicBlock * const filterDict = b->CreateBasicBlock("filterDict");

    Value * const segProcessed = b->getProcessedItemCount("MatchesBySegment");
    Value * const segAvail = b->getAvailableItemCount("MatchesBySegment");
    Value * const produced = b->getProducedItemCount("filtereData");
    Value * const availBytes = b->getAvailableItemCount("byteData");
    Value * const processedBytes = b->getProcessedItemCount("byteData");
    Value * const availStarts = b->getAvailableItemCount("offsetStartData");
    Value * const processedStarts = b->getProcessedItemCount("offsetStartData");
    Value * const availEnds = b->getAvailableItemCount("offsetEndData");
    Value * const processedEnds = b->getProcessedItemCount("offsetEndData");
    // b->CallPrintInt("numOfStrides", numOfStrides);
    // b->CallPrintInt("segAvail", segAvail);
    // b->CallPrintInt("segProcessed", segProcessed);
    // b->CallPrintInt("availBytes", availBytes);
    // b->CallPrintInt("processedBytes", processedBytes);
    // b->CallPrintInt("availStarts", availStarts);
    // b->CallPrintInt("processedStarts", processedStarts);
    // b->CallPrintInt("availEnds", availEnds);
    // b->CallPrintInt("processedEnds", processedEnds);
    b->CreateBr(startSegment);

    b->SetInsertPoint(startSegment);
    PHINode * strideNo = b->CreatePHI(sizeTy, 2);
    strideNo->addIncoming(sz_ZERO, entry);
    PHINode * segProduced = b->CreatePHI(sizeTy, 2, "segProduced");
    segProduced->addIncoming(produced, entry);
    Value * nextStrideNo = b->CreateAdd(strideNo, sz_ONE);

    Value * const segIdx = b->CreateAdd(strideNo, segProcessed, "segIdx");
    b->CreateCondBr(b->CreateICmpEQ(segIdx, segAvail), segmentsDone, processSegment);

    b->SetInsertPoint(processSegment);
    // b->CallPrintInt("segIdx", segIdx);
    Value * segBase = b->CreateSub(segIdx, b->CreateURem(segIdx, b->getSize(8))); // does segBase start from 0?
    Value * matchesBasePtr = b->CreateBitCast(b->getRawInputPointer("MatchesBySegment", segBase), sizeTy->getPointerTo());
    Value * matches = b->CreateAlignedLoad(matchesBasePtr, 1);
    Value * copySeg = b->CreateAnd(matches, b->CreateShl(sz_ONE, b->getScalarField("bitIdx")));
    // b->CallPrintInt("segIdx", segIdx);
    // b->CallPrintInt("segBase", segBase);
    // b->CallPrintInt("bitIdx", b->getScalarField("bitIdx"));
    // b->CallPrintInt("b->CreateShl(sz_ONE, b->getScalarField(bitIdx))", b->CreateShl(sz_ONE, b->getScalarField("bitIdx")));
    // b->CallPrintInt("matches", matches);
    // b->CallPrintInt("copySeg", copySeg);
    // b->CallPrintInt("segProduced", segProduced);
    Value * segEndPtr = b->CreateBitCast(b->getRawInputPointer("offsetStartData", segIdx), b->getSizeTy()->getPointerTo());
    Value * segEndPos = b->CreateAlignedLoad(segEndPtr, 1);
    segEndPos = b->CreateSelect(b->CreateICmpEQ(segEndPos, availBytes), segEndPos, b->CreateAdd(segEndPos, sz_ONE));
    // b->CallPrintInt("segEndPos", segEndPos);

    Value * segStartPos = b->getScalarField("startOffset");
    // b->CallPrintInt("segStartPos", segStartPos);
    b->CreateCondBr(b->CreateICmpUGT(copySeg, sz_ZERO), filterSeg, filterDict);

    b->SetInsertPoint(filterSeg);
    Value * segSize = b->CreateSub(segEndPos, segStartPos);
    // b->CallPrintInt("segSize", segSize);
    b->CreateMemCpy(b->getRawOutputPointer("filtereData", segProduced), b->getRawInputPointer("byteData", segStartPos), segSize, 1);
    Value * const nextWritePos = b->CreateAdd(segProduced, segSize);
    // b->CallPrintInt("nextWritePos", nextWritePos);
    b->CreateBr(segmentsDone);

    b->SetInsertPoint(filterDict);
    Value * dictStartPos = segStartPos;
    Value * dictEndPtr = b->CreateBitCast(b->getRawInputPointer("offsetEndData", segIdx), b->getSizeTy()->getPointerTo());
    Value * dictEndPos = b->CreateAlignedLoad(dictEndPtr, 1); // position of last "ff" in dict end boundary
    dictEndPos = b->CreateSelect(b->CreateICmpEQ(dictEndPos, availBytes), dictEndPos, b->CreateAdd(dictEndPos, sz_ONE));  // position after last "ff" in dictionary
    Value * dictSize = b->CreateSub(dictEndPos, dictStartPos);
    // b->CallPrintInt("dictEndPos", dictEndPos);
    // b->CallPrintInt("dictSize", dictSize);
    b->CreateMemCpy(b->getRawOutputPointer("filtereData", segProduced), b->getRawInputPointer("byteData", dictStartPos), dictSize, 1);

    Value * const nextWritePosAfterDict = b->CreateAdd(segProduced, dictSize);
    // b->CallPrintInt("nextWritePosAfterDict", nextWritePosAfterDict);
    b->CreateBr(segmentsDone);

    b->SetInsertPoint(segmentsDone);
    PHINode * const strideProduced = b->CreatePHI(sizeTy, 2, "strideProduced");
    strideProduced->addIncoming(nextWritePos, filterSeg);
    strideProduced->addIncoming(nextWritePosAfterDict, filterDict);
    strideProduced->addIncoming(segProduced, startSegment);

    segProduced->addIncoming(strideProduced, segmentsDone);
    strideNo->addIncoming(nextStrideNo, segmentsDone);

    PHINode * const processed = b->CreatePHI(sizeTy, 2, "processed");
    processed->addIncoming(segEndPos, filterSeg);
    processed->addIncoming(segEndPos, filterDict);
    processed->addIncoming(availBytes, startSegment);

    // b->CallPrintInt("strideProduced", strideProduced);
    // b->CallPrintInt("b->isFinal()", b->isFinal());

    b->setScalarField("bitIdx", b->CreateSelect(b->CreateICmpEQ(b->getScalarField("bitIdx"), b->getSize(7)), sz_ZERO, b->CreateAdd(b->getScalarField("bitIdx"), sz_ONE)));
    b->setScalarField("startOffset", processed);
    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), startSegment, stridesDone);

    b->SetInsertPoint(stridesDone);
    // b->CallPrintInt("processed-fin", processed);
    // b->CallPrintInt("availBytes-fin", availBytes);
    b->setProcessedItemCount("byteData", b->CreateSelect(b->CreateICmpUGT(processed, availBytes), availBytes, processed)); //b->CreateSub(segEndPos, sz_ONE)));
    // b->CallPrintInt("strideProduced-final", strideProduced);
    b->setProducedItemCount("filtereData", strideProduced);
}
