#include <kernel/ztf/ztf-phrase-scan.h>
#include <kernel/ztf/common.h>
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
#if 0
#define USE_CUCKOO_HASHING
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

// frequency calculation: VERY SLOW!!
// use a simple vector to store all the unique phrases.
// search the vector sequentially for occurrence of every new phrase.
// if found, increment the counter corresponding to the phrase; maintain the counters in another vector. Phrases and counter will have same index.
// else, add the phrase to the end of the vector and initialize the counter to 1.

MarkRepeatedHashvalue::MarkRepeatedHashvalue(BuilderRef b,
                                               EncodingInfo encodingScheme,
                                               unsigned numSyms,
                                               unsigned groupNo,
                                               unsigned offset,
                                               StreamSet * lfData,
                                               StreamSet * symEndMarks,
                                               StreamSet * cmpMarksSoFar,
                                               StreamSet * const hashValues,
                                               StreamSet * const initFreq,
                                               StreamSet * const byteData,
                                               StreamSet * hashMarks,
                                               StreamSet * secHashMarks,
                                               StreamSet * freqUpdated, 
                                               unsigned strideBlocks)
: MultiBlockKernel(b, "MarkRepeatedHashvalue" + std::to_string(numSyms) + std::to_string(groupNo) + lengthGroupSuffix(encodingScheme, groupNo),
                   {Binding{"lfPos", lfData, GreedyRate(), Deferred()}, // reads 1 item per stride of 1MB
                    Binding{"symEndMarks", symEndMarks, FixedRate(), Deferred()}, // exact processed is PartialSum("lfPos"), but might not be exact multiple of blockwidth or at aligned location
                    Binding{"cmpMarksSoFar", cmpMarksSoFar, FixedRate(), Deferred() },
                    Binding{"hashValues", hashValues, FixedRate(), Deferred() },
                    Binding{"initFreq", initFreq, FixedRate(), Deferred() },
                    Binding{"byteData", byteData, FixedRate(), Deferred() }},
                   {}, {}, {},
                   {InternalScalar{b->getBitBlockType(), "pendingMaskInverted"},
                    InternalScalar{b->getBitBlockType(), "pendingPhraseMask"},
                    InternalScalar{b->getBitBlockType(), "pendingDictPhraseMask"},
                    InternalScalar{b->getSizeTy(), "segIndex"},
                    InternalScalar{b->getSizeTy(), "absBlocksProcessed"},
                    InternalScalar{b->getSizeTy(), "lastLfPos"},
                    InternalScalar{b->getSizeTy(), "lastSegIndex"},
                    InternalScalar{ArrayType::get(ArrayType::get(ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), phraseHashSubTableSize(encodingScheme, groupNo, numSyms)), encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1), "hashTable"},
                    InternalScalar{ArrayType::get(b->getSizeTy(), phraseHashSubTableSize(encodingScheme, groupNo, numSyms) * (encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1)), "freqTable"},
                    InternalScalar{ArrayType::get(b->getSizeTy(), phraseHashSubTableSize(encodingScheme, groupNo, numSyms) * (encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1)), "secondHashEntryTable"},
                    InternalScalar{ArrayType::get(ArrayType::get(ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), phraseVectorSize(encodingScheme, groupNo)), encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1), "phraseVector"},
                    InternalScalar{ArrayType::get(b->getSizeTy(), phraseVectorSize(encodingScheme, groupNo) * (encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1)), "phraseFreqCount"}}),
mEncodingScheme(encodingScheme), mStrideSize(1048576), mGroupNo(groupNo), mNumSym(numSyms), mSubStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS)), mOffset(offset) {
    mOutputStreamSets.emplace_back("hashMarks", hashMarks, FixedRate(), Delayed(1048576));
    mOutputStreamSets.emplace_back("secHashMarks", secHashMarks, FixedRate(), Delayed(1048576));
    mOutputStreamSets.emplace_back("freqUpdated", freqUpdated, FixedRate(), Delayed(1048576));
    setStride(1048576);
}

void MarkRepeatedHashvalue::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    ScanWordParameters sw(b, mStrideSize);
    LengthGroupParameters lg(b, mEncodingScheme, mGroupNo, mNumSym);
    Constant * sz_SUB_STRIDE = b->getSize(mSubStride);
    Constant * sz_BLOCKS_PER_SUB_STRIDE = b->getSize(mSubStride/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_TWO = b->getSize(2);
    Constant * sz_BITS = b->getSize(SIZE_T_BITS);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    Constant * sz_PHRASE_LEN_OFFSET = b->getSize(mOffset);
    Constant * sz_FFFF = b->getInt16(0xFFFF);
    Value * mGroupNoVal = b->getSize(mGroupNo);
    Value * const sz_PHRASELEN_VECTOR_SIZE = b->getSize(mEncodingScheme.byLength[mGroupNo].hi * phraseVectorSize(mEncodingScheme, mGroupNo));
    Value * const sz_PHRASELEN_FREQ_VECTOR_SIZE = b->getSize(phraseVectorSize(mEncodingScheme, mGroupNo));
    Value * sz_HASH_TBL = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo, mNumSym));

    assert ((mStrideSize % mSubStride) == 0);
    Value * totalSubStrides =  b->getSize(mStrideSize / mSubStride); // 102400/2048 with BitBlock=256

    Type * sizeTy = b->getSizeTy();
    Type * bitBlockPtrTy = b->getBitBlockType()->getPointerTo();

    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const stridePrologue = b->CreateBasicBlock("stridePrologue");
    BasicBlock * const subStrideMaskPrep = b->CreateBasicBlock("subStrideMaskPrep");
    BasicBlock * const strideMasksReady = b->CreateBasicBlock("strideMasksReady");
    BasicBlock * const keyProcessingLoop = b->CreateBasicBlock("keyProcessingLoop");
    BasicBlock * const processKey = b->CreateBasicBlock("processKey");
    BasicBlock * const tryAddingToTable = b->CreateBasicBlock("tryAddingToTable");
#ifdef USE_CUCKOO_HASHING
    Type * const boolTy = b->getInt1Ty();
    BasicBlock * const storeInFirstHash = b->CreateBasicBlock("storeInFirstHash");
    BasicBlock * const checkSecondHash = b->CreateBasicBlock("checkSecondHash");
    BasicBlock * const storeInSecondHash = b->CreateBasicBlock("storeInSecondHash");
    BasicBlock * const checkLoopCond = b->CreateBasicBlock("checkLoopCond");
    BasicBlock * const secHashPhrases = b->CreateBasicBlock("secHashPhrases");
    BasicBlock * const secHashSymMarked = b->CreateBasicBlock("secHashSymMarked");
    BasicBlock * const calcSymSuffixMask = b->CreateBasicBlock("calcSymSuffixMask");
    BasicBlock * const calcSymPfxMask = b->CreateBasicBlock("calcSymPfxMask");
#endif
    BasicBlock * const nextKey = b->CreateBasicBlock("nextKey");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const updatePending = b->CreateBasicBlock("updatePending");
    BasicBlock * const hashMarksDone = b->CreateBasicBlock("hashMarksDone");
    BasicBlock * const symProcessingLoop = b->CreateBasicBlock("symProcessingLoop");
    BasicBlock * const processSym = b->CreateBasicBlock("processSym");
    BasicBlock * const checkSymCompression = b->CreateBasicBlock("checkSymCompression");
    BasicBlock * const continueOverlapCheck = b->CreateBasicBlock("continueOverlapCheck");
    BasicBlock * const removeHashTableEntry = b->CreateBasicBlock("removeHashTableEntry");
    BasicBlock * const updateFreq = b->CreateBasicBlock("updateFreq");
    BasicBlock * const markSymCompression = b->CreateBasicBlock("markSymCompression");
    BasicBlock * const nextSym = b->CreateBasicBlock("nextSym");
    BasicBlock * const subStridePhrasesDone = b->CreateBasicBlock("subStridePhrasesDone");

    BasicBlock * const symsDone = b->CreateBasicBlock("symsDone");
    // BasicBlock * const replaceSegmentEntry = b->CreateBasicBlock("replaceSegmentEntry");
    // BasicBlock * const replaceGlobalTblEntry = b->CreateBasicBlock("replaceGlobalTblEntry");
    // BasicBlock * const checkGlobalUpdate = b->CreateBasicBlock("checkGlobalUpdate");
    BasicBlock * const hashTableDone = b->CreateBasicBlock("hashTableDone");
    BasicBlock * const symProcessingPrep= b->CreateBasicBlock("symProcessingPrep");
    BasicBlock * const symMaskReady = b->CreateBasicBlock("symMaskReady");
    BasicBlock * const compareOverlappingSymWithinAndAcrossGroups = b->CreateBasicBlock("compareOverlappingSymWithinAndAcrossGroups");
    BasicBlock * const compareOverlappingSymInLastGroup = b->CreateBasicBlock("compareOverlappingSymInLastGroup");
#if 0
    BasicBlock * const printPhrase = b->CreateBasicBlock("printPhrase");
    BasicBlock * const proceed = b->CreateBasicBlock("proceed");
#endif

    BasicBlock * const freqCalcPrep = b->CreateBasicBlock("freqCalcPrep");
    BasicBlock * const phraseMaskReady = b->CreateBasicBlock("phraseMaskReady");
    BasicBlock * const phraseProcessingLoop = b->CreateBasicBlock("phraseProcessingLoop");
    BasicBlock * const subStridePhrasesDone_0 = b->CreateBasicBlock("subStridePhrasesDone_0");
    BasicBlock * const processPhrase = b->CreateBasicBlock("processPhrase");
    BasicBlock * const getOrAddPhrase = b->CreateBasicBlock("getOrAddPhrase");
    BasicBlock * const nextPhrase = b->CreateBasicBlock("nextPhrase");
    BasicBlock * const insertPhrase = b->CreateBasicBlock("insertPhrase");
    BasicBlock * const comparePhrases = b->CreateBasicBlock("comparePhrases");
    BasicBlock * const checkNextIdx = b->CreateBasicBlock("checkNextIdx");
    BasicBlock * const updatePhraseFreq = b->CreateBasicBlock("updatePhraseFreq");

    BasicBlock * const freqCalcPrep_part2 = b->CreateBasicBlock("freqCalcPrep_part2");
    BasicBlock * const phraseMaskReady_part2 = b->CreateBasicBlock("phraseMaskReady_part2");
    BasicBlock * const phraseProcessingLoop_part2 = b->CreateBasicBlock("phraseProcessingLoop_part2");
    BasicBlock * const processPhrase_part2 = b->CreateBasicBlock("processPhrase_part2");
    BasicBlock * const nextPhrase_part2 = b->CreateBasicBlock("nextPhrase_part2");
    BasicBlock * const lookupPhrase = b->CreateBasicBlock("lookupPhrase");
    BasicBlock * const checkNextIdx_part2 = b->CreateBasicBlock("checkNextIdx_part2");
    BasicBlock * const writeFreqInBuffer = b->CreateBasicBlock("writeFreqInBuffer");
    BasicBlock * const subStridePhrasesDone_1 = b->CreateBasicBlock("subStridePhrasesDone_1");

    BasicBlock * const checkSameGrpOverlap = b->CreateBasicBlock("checkSameGrpOverlap");
    BasicBlock * const unMarkSameGrpPhrase = b->CreateBasicBlock("unMarkSameGrpPhrase");
    BasicBlock * const checkUnmark = b->CreateBasicBlock("checkUnmark");

    BasicBlock * const calcSuffixMask = b->CreateBasicBlock("calcSuffixMask");
    BasicBlock * const calcPfxMask = b->CreateBasicBlock("calcPfxMask");

    BasicBlock * const checkIdxCond  = b->CreateBasicBlock("checkIdxCond ");
    BasicBlock * const storeInNextEmptyHash  = b->CreateBasicBlock("storeInNextEmptyHash ");
    BasicBlock * const findNextAvailIdx  = b->CreateBasicBlock("findNextAvailIdx ");
    BasicBlock * const tryHandleCollision = b->CreateBasicBlock("tryHandleCollision");
    BasicBlock * const indexReady = b->CreateBasicBlock("indexReady");

    BasicBlock * const updatePhraseHashIdx = b->CreateBasicBlock("updatePhraseHashIdx");
    BasicBlock * const tryStore = b->CreateBasicBlock("tryStore");
    BasicBlock * const writeNextIdx = b->CreateBasicBlock("writeNextIdx");
    BasicBlock * const tryStoreInNextIdx = b->CreateBasicBlock("tryStoreInNextIdx");

#ifdef PRINT_HT_STATS_MARK_REPEATED_HASHVAL
    BasicBlock * const printHTusage = b->CreateBasicBlock("printHTusage");
    BasicBlock * const iterateSubTbl = b->CreateBasicBlock("iterateSubTbl");
    BasicBlock * const goToNextSubTbl = b->CreateBasicBlock("goToNextSubTbl");
    BasicBlock * const goToNextStride = b->CreateBasicBlock("goToNextStride");
    BasicBlock * const printIdx = b->CreateBasicBlock("printIdx");
    BasicBlock * const checkNextIdx = b->CreateBasicBlock("checkNextIdx");
#endif
    Value * const avail = b->getAvailableItemCount("symEndMarks");

    Value * const processedBlocks = b->getScalarField("absBlocksProcessed");
    Value * const actualProcessed = b->CreateMul(processedBlocks, sz_BLOCKWIDTH);
    // Value * hashTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("segmentHashTable"), b->getInt8PtrTy());
    // Value * freqTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("segmentFreqTable"), sizeTy->getPointerTo());
    Value * globalHashTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("hashTable"), b->getInt8PtrTy());
    Value * globalFreqTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("freqTable"), sizeTy->getPointerTo());
#ifdef USE_CUCKOO_HASHING
    Value * secHashTblBasePtr = b->CreateBitCast(b->getScalarFieldPtr("secondHashEntryTable"), sizeTy->getPointerTo());
#endif
    Value * phraseVectorBasePtr = b->CreateBitCast(b->getScalarFieldPtr("phraseVector"), b->getInt8PtrTy());
    Value * phraseFreqVecBasePtr = b->CreateBitCast(b->getScalarFieldPtr("phraseFreqCount"), b->getInt16Ty()->getPointerTo());

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
    Value * toCopy = b->CreateMul(b->CreateSub(lfPos, b->getScalarField("lastLfPos")), sz_TWO);
    Value * memCpyPos = b->getScalarField("lastLfPos");
    b->CreateMemCpy(b->getRawOutputPointer("freqUpdated", memCpyPos), b->getRawInputPointer("initFreq", memCpyPos), toCopy, 1); 

    Value * totalProcessed = b->CreateMul(b->getScalarField("absBlocksProcessed"), sz_BLOCKWIDTH);
    Value * stridePos =  totalProcessed;
    Value * strideBlockOffset = b->getScalarField("absBlocksProcessed");
    Value * processBeforeThisPos = lfPos;
    Value * processAfterThisPos = b->getScalarField("lastLfPos");
    b->setScalarField("lastLfPos", lfPos);

    Value * const sz_phraseVector = b->getSize(phraseVectorSize(mEncodingScheme, mGroupNo));
    // overlapping partial blocks are processed twice within the same segment -> ok.
    // When the segment changes, do not process the partial block's already processed symbols.
// ====================================================================
    b->CreateBr(freqCalcPrep);

    b->SetInsertPoint(freqCalcPrep);
    PHINode * const step0subStrideNo = b->CreatePHI(sizeTy, 2, "step0subStrideNo");
    step0subStrideNo->addIncoming(sz_ZERO, stridePrologue);
    Value * step0nextSubStrideNo = b->CreateAdd(step0subStrideNo, sz_ONE);
    Value * step0subStridePos = b->CreateAdd(stridePos, b->CreateMul(step0subStrideNo, sz_SUB_STRIDE));
    Value * step0subStrideBlockOffset = b->CreateAdd(strideBlockOffset, b->CreateMul(step0subStrideNo, sz_BLOCKS_PER_SUB_STRIDE));
    std::vector<Value *> phraseMasks0 = initializeCompressionMasks2_init(b, sw, sz_BLOCKS_PER_SUB_STRIDE, 1, step0subStrideBlockOffset, phraseMaskReady);
    Value * phraseMask0 = phraseMasks0[0];

    b->SetInsertPoint(phraseMaskReady);
    step0subStrideBlockOffset = b->CreateSub(step0subStrideBlockOffset, processedBlocks);
    Value * phraseWordBasePtr = b->getInputStreamBlockPtr("symEndMarks", sz_ZERO, step0subStrideBlockOffset);
    phraseWordBasePtr = b->CreateBitCast(phraseWordBasePtr, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(phraseMask0, sz_ZERO), subStridePhrasesDone_0, phraseProcessingLoop);

    b->SetInsertPoint(phraseProcessingLoop);
    PHINode * const phraseMaskPhi = b->CreatePHI(sizeTy, 2);
    phraseMaskPhi->addIncoming(phraseMask0, phraseMaskReady);
    PHINode * const phraseWordPhi = b->CreatePHI(sizeTy, 2);
    phraseWordPhi->addIncoming(sz_ZERO, phraseMaskReady);
    Value * phraseWordIdx = b->CreateCountForwardZeroes(phraseMaskPhi, "phraseWordIdx");
    Value * nextPhraseWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(phraseWordBasePtr, phraseWordIdx)), sizeTy);
    Value * thePhraseWord = b->CreateSelect(b->CreateICmpEQ(phraseWordPhi, sz_ZERO), nextPhraseWord, phraseWordPhi);
    Value * phraseWordPos = b->CreateAdd(step0subStridePos, b->CreateMul(phraseWordIdx, sw.WIDTH));
    Value * phraseMarkPosInWord = b->CreateCountForwardZeroes(thePhraseWord);
    Value * phraseMarkPos = b->CreateAdd(phraseWordPos, phraseMarkPosInWord, "symEndPos");
    Value * phraseProcessCond = b->CreateAnd(b->CreateICmpULE(phraseMarkPos, processBeforeThisPos), b->CreateICmpUGT(phraseMarkPos, processAfterThisPos));
    b->CreateCondBr(phraseProcessCond, processPhrase, nextPhrase);

    b->SetInsertPoint(processPhrase);
    /* Determine the sym length. */
    Value * phraseHashValue = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", phraseMarkPos)), sizeTy);
    Value * phraseLength = b->CreateAdd(b->CreateLShr(phraseHashValue, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET, "phraseLength");
    Value * phraseStartPos = b->CreateSub(phraseMarkPos, b->CreateSub(phraseLength, sz_ONE), "phraseStartPos");
    // phraseOffset for accessing the final half of an entry.
    Value * phraseOffset = b->CreateSub(phraseLength, lg.HALF_LENGTH);

    Value * fullSymPtr1 = b->CreateBitCast(b->getRawInputPointer("byteData", phraseStartPos), lg.halfSymPtrTy);
    Value * fullSymPtr2 = b->CreateBitCast(b->getRawInputPointer("byteData", b->CreateAdd(phraseStartPos, phraseOffset)), lg.halfSymPtrTy);
    Value * fullSym1 = b->CreateAlignedLoad(fullSymPtr1, 1);
    Value * fullSym2 = b->CreateAlignedLoad(fullSymPtr2, 1);

    Value * const maxIdx = b->CreateMul(sz_phraseVector, phraseLength);

    b->CreateBr(getOrAddPhrase);
    b->SetInsertPoint(getOrAddPhrase);
    PHINode * idx = b->CreatePHI(sizeTy, 2);
    idx->addIncoming(sz_ZERO, processPhrase);
    Value * nextIdx = b->CreateAdd(idx, phraseLength);
    Value * phraseLenEntryPtr = b->CreateInBoundsGEP(phraseVectorBasePtr, b->CreateMul(b->CreateSub(phraseLength, lg.LO), sz_PHRASELEN_VECTOR_SIZE));
    Value * phraseIdxPtr = b->CreateGEP(phraseLenEntryPtr, idx);
    Value * phraseEntryPtr = b->CreateInBoundsGEP(phraseIdxPtr, sz_ZERO);
    Value * phraseEntryPtr1 = b->CreateBitCast(phraseEntryPtr, lg.halfSymPtrTy);
    Value * phraseEntryPtr2 = b->CreateBitCast(b->CreateGEP(phraseEntryPtr, phraseOffset), lg.halfSymPtrTy);
    Value * phraseEntry1 = b->CreateMonitoredScalarFieldLoad("phraseVector", phraseEntryPtr1);
    Value * phraseEntry2 = b->CreateMonitoredScalarFieldLoad("phraseVector", phraseEntryPtr2);
    Value * phraseFreqIdxPtr = b->CreateGEP(phraseFreqVecBasePtr, b->CreateMul(b->CreateSub(phraseLength, lg.LO), sz_PHRASELEN_FREQ_VECTOR_SIZE));
    Value * phraseFreqPtr = b->CreateInBoundsGEP(phraseFreqIdxPtr, idx);
    Value * phraseFreqEntryPtr = b->CreateBitCast(phraseFreqPtr, b->getInt16Ty()->getPointerTo());
    Value * freqEntry = b->CreateMonitoredScalarFieldLoad("phraseFreqCount", phraseFreqEntryPtr);

    Value * entryEmpty = b->CreateICmpEQ(b->CreateOr(phraseEntry1, phraseEntry2), Constant::getNullValue(lg.halfLengthTy));
    b->CreateCondBr(entryEmpty, insertPhrase, comparePhrases);

    b->SetInsertPoint(insertPhrase);
    b->CreateMonitoredScalarFieldStore("phraseVector", fullSym1, phraseEntryPtr1);
    b->CreateMonitoredScalarFieldStore("phraseVector", fullSym2, phraseEntryPtr2);
    b->CreateMonitoredScalarFieldStore("phraseFreqCount", b->getInt16(1), phraseFreqEntryPtr);
    // initialize the counter
    b->CreateBr(nextPhrase);
    b->SetInsertPoint(comparePhrases);
    Value * phrasesEqual = b->CreateAnd(b->CreateICmpEQ(phraseEntry1, fullSym1), b->CreateICmpEQ(phraseEntry2, fullSym2));
    b->CreateCondBr(phrasesEqual, updatePhraseFreq, checkNextIdx);

    b->SetInsertPoint(checkNextIdx);
    idx->addIncoming(nextIdx, checkNextIdx);
    b->CreateCondBr(b->CreateICmpEQ(nextIdx, maxIdx), nextPhrase, getOrAddPhrase);

    b->SetInsertPoint(updatePhraseFreq);
    b->CreateMonitoredScalarFieldStore("phraseFreqCount", b->CreateAdd(b->getInt16(1), freqEntry), phraseFreqEntryPtr);
    // update the count at index "idx"
    b->CreateBr(nextPhrase);

    b->SetInsertPoint(nextPhrase);
    Value * dropPhrase = b->CreateResetLowestBit(thePhraseWord);
    Value * thisPhraseWordDone = b->CreateICmpEQ(dropPhrase, sz_ZERO);
    // There may be more syms in the sym mask.
    Value * nextPhraseMask = b->CreateSelect(thisPhraseWordDone, b->CreateResetLowestBit(phraseMaskPhi), phraseMaskPhi);
    BasicBlock * currentBB0 = b->GetInsertBlock();
    phraseMaskPhi->addIncoming(nextPhraseMask, currentBB0);
    phraseWordPhi->addIncoming(dropPhrase, currentBB0);
    b->CreateCondBr(b->CreateICmpNE(nextPhraseMask, sz_ZERO), phraseProcessingLoop, subStridePhrasesDone_0);

    b->SetInsertPoint(subStridePhrasesDone_0);
    step0subStrideNo->addIncoming(step0nextSubStrideNo, subStridePhrasesDone_0);
    b->CreateCondBr(b->CreateICmpNE(step0nextSubStrideNo, totalSubStrides), freqCalcPrep, freqCalcPrep_part2);
// ========================================================================================================================================================================
//                                            create final freq buffer
// ========================================================================================================================================================================

    b->SetInsertPoint(freqCalcPrep_part2);
    PHINode * const step01subStrideNo = b->CreatePHI(sizeTy, 2, "step01subStrideNo");
    step01subStrideNo->addIncoming(sz_ZERO, subStridePhrasesDone_0);
    Value * step01nextSubStrideNo = b->CreateAdd(step01subStrideNo, sz_ONE);
    Value * step01subStridePos = b->CreateAdd(stridePos, b->CreateMul(step01subStrideNo, sz_SUB_STRIDE));
    Value * step01subStrideBlockOffset = b->CreateAdd(strideBlockOffset, b->CreateMul(step01subStrideNo, sz_BLOCKS_PER_SUB_STRIDE));
    std::vector<Value *> phraseMasks01 = initializeCompressionMasks2(b, sw, sz_BLOCKS_PER_SUB_STRIDE, 1, step01subStrideBlockOffset, hashMarksPtr, phraseMaskReady_part2);
    Value * phraseMask01 = phraseMasks01[0];

    b->SetInsertPoint(phraseMaskReady_part2);
    step01subStrideBlockOffset = b->CreateSub(step01subStrideBlockOffset, processedBlocks);
    Value * phraseWordBasePtr0 = b->getInputStreamBlockPtr("symEndMarks", sz_ZERO, step01subStrideBlockOffset);
    phraseWordBasePtr0 = b->CreateBitCast(phraseWordBasePtr0, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(phraseMask01, sz_ZERO), subStridePhrasesDone_1, phraseProcessingLoop_part2);

    b->SetInsertPoint(phraseProcessingLoop_part2);
    PHINode * const phraseMaskPhi0 = b->CreatePHI(sizeTy, 2);
    phraseMaskPhi0->addIncoming(phraseMask01, phraseMaskReady_part2);
    PHINode * const phraseWordPhi0 = b->CreatePHI(sizeTy, 2);
    phraseWordPhi0->addIncoming(sz_ZERO, phraseMaskReady_part2);
    Value * phraseWordIdx0 = b->CreateCountForwardZeroes(phraseMaskPhi0, "phraseWordIdx0");
    Value * nextPhraseWord0 = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(phraseWordBasePtr0, phraseWordIdx0)), sizeTy);
    Value * thePhraseWord0 = b->CreateSelect(b->CreateICmpEQ(phraseWordPhi0, sz_ZERO), nextPhraseWord0, phraseWordPhi0);
    Value * phraseWordPos0 = b->CreateAdd(step01subStridePos, b->CreateMul(phraseWordIdx0, sw.WIDTH));
    Value * phraseMarkPosInWord0 = b->CreateCountForwardZeroes(thePhraseWord0);
    Value * phraseMarkPos0 = b->CreateAdd(phraseWordPos0, phraseMarkPosInWord0, "symEndPos");
    Value * phraseProcessCond0 = b->CreateAnd(b->CreateICmpULE(phraseMarkPos0, processBeforeThisPos), b->CreateICmpUGT(phraseMarkPos0, processAfterThisPos));
    b->CreateCondBr(phraseProcessCond0, processPhrase_part2, nextPhrase_part2);

    b->SetInsertPoint(processPhrase_part2);
    /* Determine the sym length. */
    Value * phraseHashValue0 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", phraseMarkPos0)), sizeTy);
    Value * phraseLength0 = b->CreateAdd(b->CreateLShr(phraseHashValue0, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET, "phraseLength0");
    Value * phraseStartPos0 = b->CreateSub(phraseMarkPos0, b->CreateSub(phraseLength0, sz_ONE), "phraseStartPos0");
    // phraseOffset for accessing the final half of an entry.
    Value * phraseOffset0 = b->CreateSub(phraseLength0, lg.HALF_LENGTH);

    Value * fullSymPtr10 = b->CreateBitCast(b->getRawInputPointer("byteData", phraseStartPos0), lg.halfSymPtrTy);
    Value * fullSymPtr20 = b->CreateBitCast(b->getRawInputPointer("byteData", b->CreateAdd(phraseStartPos0, phraseOffset0)), lg.halfSymPtrTy);
    Value * fullSym10 = b->CreateAlignedLoad(fullSymPtr10, 1);
    Value * fullSym20 = b->CreateAlignedLoad(fullSymPtr20, 1);

    Value * const maxIdx0 = b->CreateMul(sz_phraseVector, phraseLength0);

    b->CreateBr(lookupPhrase);
    b->SetInsertPoint(lookupPhrase);
    PHINode * idx0 = b->CreatePHI(sizeTy, 2);
    idx0->addIncoming(sz_ZERO, processPhrase_part2);
    Value * nextIdx0 = b->CreateAdd(idx0, phraseLength0);
    Value * phraseLenEntryPtr0 = b->CreateInBoundsGEP(phraseVectorBasePtr, b->CreateMul(b->CreateSub(phraseLength0, lg.LO), sz_PHRASELEN_VECTOR_SIZE));
    Value * phraseIdxPtr0 = b->CreateGEP(phraseLenEntryPtr0, idx0);
    Value * phraseEntryPtr0 = b->CreateInBoundsGEP(phraseIdxPtr0, sz_ZERO);
    Value * phraseEntryPtr01 = b->CreateBitCast(phraseEntryPtr0, lg.halfSymPtrTy);
    Value * phraseEntryPtr02 = b->CreateBitCast(b->CreateGEP(phraseEntryPtr0, phraseOffset0), lg.halfSymPtrTy);
    Value * phraseEntry10 = b->CreateMonitoredScalarFieldLoad("phraseVector", phraseEntryPtr01);
    Value * phraseEntry20 = b->CreateMonitoredScalarFieldLoad("phraseVector", phraseEntryPtr02);
    Value * phraseFreqIdxPtr0 = b->CreateGEP(phraseFreqVecBasePtr, b->CreateMul(b->CreateSub(phraseLength0, lg.LO), sz_PHRASELEN_FREQ_VECTOR_SIZE));
    Value * phraseFreqPtr0 = b->CreateInBoundsGEP(phraseFreqIdxPtr0, idx0);
    Value * phraseFreqEntryPtr0 = b->CreateBitCast(phraseFreqPtr0, b->getInt16Ty()->getPointerTo());
    Value * finalFreq = b->CreateMonitoredScalarFieldLoad("phraseFreqCount", phraseFreqEntryPtr0);

    Value * phrasesEqual0 = b->CreateAnd(b->CreateICmpEQ(phraseEntry10, fullSym10), b->CreateICmpEQ(phraseEntry20, fullSym20));
    b->CreateCondBr(phrasesEqual0, writeFreqInBuffer, checkNextIdx_part2);

    b->SetInsertPoint(writeFreqInBuffer);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), b->CreateBitCast(phraseEntryPtr0, b->getInt8PtrTy()), phraseLength0);
    // b->CallPrintInt("finalFreq", finalFreq);
    b->CreateStore(b->CreateTrunc(b->CreateAnd(finalFreq, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", phraseMarkPos0));
    b->CreateBr(nextPhrase_part2);

    b->SetInsertPoint(checkNextIdx_part2);
    idx0->addIncoming(nextIdx0, checkNextIdx_part2);
    b->CreateCondBr(b->CreateICmpEQ(nextIdx0, maxIdx0), nextPhrase_part2, lookupPhrase);

    b->SetInsertPoint(nextPhrase_part2);
    Value * dropPhrase0 = b->CreateResetLowestBit(thePhraseWord0);
    Value * thisPhraseWordDone0 = b->CreateICmpEQ(dropPhrase0, sz_ZERO);
    // There may be more syms in the sym mask.
    Value * nextPhraseMask0 = b->CreateSelect(thisPhraseWordDone0, b->CreateResetLowestBit(phraseMaskPhi0), phraseMaskPhi0);
    BasicBlock * currentBB01 = b->GetInsertBlock();
    phraseMaskPhi0->addIncoming(nextPhraseMask0, currentBB01);
    phraseWordPhi0->addIncoming(dropPhrase0, currentBB01);
    b->CreateCondBr(b->CreateICmpNE(nextPhraseMask0, sz_ZERO), phraseProcessingLoop_part2, subStridePhrasesDone_1);

    b->SetInsertPoint(subStridePhrasesDone_1);
    step01subStrideNo->addIncoming(step01nextSubStrideNo, subStridePhrasesDone_1);
    b->CreateCondBr(b->CreateICmpNE(step01nextSubStrideNo, totalSubStrides), freqCalcPrep_part2, subStrideMaskPrep);

// ========================================================================================================================================================================
//                                 final freq buffer created
// ========================================================================================================================================================================
    b->SetInsertPoint(subStrideMaskPrep);
    PHINode * const subStrideNo = b->CreatePHI(sizeTy, 2);
    subStrideNo->addIncoming(sz_ZERO, subStridePhrasesDone_1);
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
#ifdef USE_CUCKOO_HASHING
    Value * keyMarkPos_H2 = b->CreateSub(keyMarkPos, sz_ONE, "keyEndPos_H2");
#endif
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

#ifdef USE_CUCKOO_HASHING
    Value * codewordVal_H2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", keyMarkPos_H2)), sizeTy);
    codewordVal_H2 = b->CreateAnd(codewordVal_H2, lg.LAST_SUFFIX_MASK);
    Value * hashcodePos_H2 = keyMarkPos_H2;
#endif
    // codewordVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(codewordVal, sz_ONE), b->CreateShl(codewordVal, sz_ONE)),
    //                               codewordVal);
    b->CreateCondBr(b->CreateICmpUGT(mGroupNoVal, sz_ZERO), calcSuffixMask, calcPfxMask);

    b->SetInsertPoint(calcSuffixMask);
    hashcodePos = b->CreateSub(hashcodePos, sz_ONE);
    Value * secondLastSuffix = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", hashcodePos)), sizeTy);
    Value * cwVal = b->CreateShl(codewordVal, lg.SEC_LAST_SFX);
    cwVal = b->CreateOr(cwVal, b->CreateAnd(secondLastSuffix, lg.SEC_LAST_SUFFIX_MASK));

#ifdef USE_CUCKOO_HASHING
    hashcodePos_H2 = b->CreateSub(hashcodePos_H2, sz_ONE);
    Value * secondLastSuffix_H2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", hashcodePos_H2)), sizeTy);
    Value * cwVal_H2 = b->CreateShl(codewordVal_H2, lg.SEC_LAST_SFX);
    cwVal_H2 = b->CreateOr(cwVal_H2, b->CreateAnd(secondLastSuffix_H2, lg.SEC_LAST_SUFFIX_MASK));
#endif
    b->CreateBr(calcPfxMask);

    b->SetInsertPoint(calcPfxMask);
    PHINode * hcPos = b->CreatePHI(sizeTy, 2);
    hcPos->addIncoming(hashcodePos, calcSuffixMask);
    hcPos->addIncoming(keyMarkPos, processKey);
    PHINode * codewordValPhi = b->CreatePHI(sizeTy, 2, "codewordValPhi");
    codewordValPhi->addIncoming(cwVal, calcSuffixMask);
    codewordValPhi->addIncoming(codewordVal, processKey);
#ifdef USE_CUCKOO_HASHING
    PHINode * hcPos_H2 = b->CreatePHI(sizeTy, 2);
    hcPos_H2->addIncoming(hashcodePos_H2, calcSuffixMask);
    hcPos_H2->addIncoming(keyMarkPos_H2, processKey);
    PHINode * codewordValPhi_H2 = b->CreatePHI(sizeTy, 2, "codewordValPhi");
    codewordValPhi_H2->addIncoming(cwVal_H2, calcSuffixMask);
    codewordValPhi_H2->addIncoming(codewordVal_H2, processKey);
    Value * codewordValFin_H2 = codewordValPhi_H2;
    Value * readPos_H2 = b->CreateSub(hcPos_H2, sz_ONE);
    Value * pfxByte_H2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", readPos_H2)), sizeTy);
    pfxByte_H2 = b->CreateTrunc(b->CreateAnd(pfxByte_H2, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    codewordValFin_H2 = b->CreateOr(b->CreateShl(codewordValFin_H2, lg.EXTRA_BITS), b->CreateAnd(pfxByte_H2, lg.EXTRA_BITS_MASK));
    Value * tableIdxHash_H2 = b->CreateAnd(codewordValFin_H2, lg.TABLE_MASK, "tableIdxHash_H2");

    Value * hash2IdxPtr = b->CreateGEP(globalSubTablePtr, b->CreateMul(tableIdxHash_H2, keyLength));
    Value * hash2EntryPtr = b->CreateInBoundsGEP(hash2IdxPtr, sz_ZERO);
    Value * hash2Ptr1 = b->CreateBitCast(hash2EntryPtr, lg.halfSymPtrTy);
    Value * hash2Ptr2 = b->CreateBitCast(b->CreateGEP(hash2EntryPtr, keyOffset), lg.halfSymPtrTy);
    Value * entry1hash2 = b->CreateMonitoredScalarFieldLoad("hashTable", hash2Ptr1);
    Value * entry2hash2 = b->CreateMonitoredScalarFieldLoad("hashTable", hash2Ptr2);
    Value * globalFreqTblEntryPtr2 = b->CreateInBoundsGEP(globalFreqSubTablePtr, tableIdxHash_H2);
    Value * globalFreqTblPtr2 = b->CreateBitCast(globalFreqTblEntryPtr2, sizeTy->getPointerTo());
    Value * globalInitCount2 = b->CreateMonitoredScalarFieldLoad("freqTable", globalFreqTblPtr2);

    Value * secHashTablePtr = b->CreateGEP(secHashTblBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.FREQ_SUBTABLE_SIZE));

#endif
    Value * codewordValFin = codewordValPhi;
    // add PREFIX_LENGTH_MASK bits for larger index space
    Value * readPos = b->CreateSub(hcPos, sz_ONE);
    Value * pfxByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", readPos)), sizeTy);
    // shift by pfx len bits
    pfxByte = b->CreateTrunc(b->CreateAnd(pfxByte, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    codewordValFin = b->CreateOr(b->CreateShl(codewordValFin, lg.EXTRA_BITS), b->CreateAnd(pfxByte, lg.EXTRA_BITS_MASK)); 

    // verify startIdx is in bounds of hashtable indices
    Value * tableIdxHash = b->CreateAnd(codewordValFin, lg.TABLE_MASK, "tableIdxHash");
    Value * startIdx = b->CreateAdd(tableIdxHash, sz_ONE);
    startIdx = b->CreateSelect(b->CreateICmpUGE(startIdx, sz_HASH_TBL), tableIdxHash, startIdx);

    Value * globalSubTablePtr = b->CreateGEP(globalHashTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    Value * globalFreqSubTablePtr = b->CreateGEP(globalFreqTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.FREQ_SUBTABLE_SIZE));

    Value * symPtr1 = b->CreateBitCast(b->getRawInputPointer("byteData", keyStartPos), lg.halfSymPtrTy);
#if 0 // write data in csv
    // "codewordValNum","tableIdxHashNum","length","phrase"
    b->CreateDprintfCall(b->getInt32(STDERR_FILENO), "\n");
    Value * codewordValNum = codewordValFin;
    Type * const t = codewordValFin->getType();
    if (t->isPointerTy()) {
        codewordValNum = b->CreatePtrToInt(codewordValFin, b->getInt64Ty());
    } else if (t->isIntegerTy()) {
        if (t->getIntegerBitWidth() < 64) {
            codewordValNum = b->CreateZExt(codewordValFin,  b->getInt64Ty());
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

    Value * hash1IdxPtr = b->CreateGEP(globalSubTablePtr, b->CreateMul(tableIdxHash, keyLength));
    Value * hash1EntryPtr = b->CreateInBoundsGEP(hash1IdxPtr, sz_ZERO);
    Value * hash1Ptr1 = b->CreateBitCast(hash1EntryPtr, lg.halfSymPtrTy);
    Value * hash1Ptr2 = b->CreateBitCast(b->CreateGEP(hash1EntryPtr, keyOffset), lg.halfSymPtrTy);
    Value * entry1hash1 = b->CreateMonitoredScalarFieldLoad("hashTable", hash1Ptr1);
    Value * entry2hash1 = b->CreateMonitoredScalarFieldLoad("hashTable", hash1Ptr2);
    Value * globalFreqTblEntryPtr1 = b->CreateInBoundsGEP(globalFreqSubTablePtr, tableIdxHash);
    Value * globalFreqTblPtr1 = b->CreateBitCast(globalFreqTblEntryPtr1, sizeTy->getPointerTo());
    Value * globalInitCount1 = b->CreateMonitoredScalarFieldLoad("freqTable", globalFreqTblPtr1);

    Value * phraseFreq = b->CreateZExt(b->CreateLoad(b->getRawOutputPointer("freqUpdated", keyMarkPos)), sizeTy);
    Value * hasGreaterFreq = b->CreateICmpUGT(phraseFreq, globalInitCount1);
    Value * minFreqReqForCmp = b->CreateSelect(b->CreateICmpEQ(mGroupNoVal, sz_ZERO), b->getSize(4), sz_TWO);
    Value * isPhraseCompressible = b->CreateAnd(b->CreateICmpUGT(phraseFreq, minFreqReqForCmp), hasGreaterFreq);
    Value * isEntryEmpty = b->CreateICmpEQ(b->CreateOr(entry1hash1, entry2hash1), Constant::getNullValue(lg.halfLengthTy)); 

    Value * phraseInTableOrigIdx = b->CreateAnd(b->CreateICmpEQ(entry1hash1, sym1), b->CreateICmpEQ(entry2hash1, sym2));
    b->CreateCondBr(phraseInTableOrigIdx, updatePhraseHashIdx, tryStore);
    b->SetInsertPoint(updatePhraseHashIdx);
    b->CreateStore(b->CreateTrunc(b->CreateAnd(tableIdxHash, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPos, sz_ONE)));
    b->CreateBr(nextKey);

    b->SetInsertPoint(tryStore);
    b->CreateCondBr(b->CreateAnd(isEntryEmpty, isPhraseCompressible), tryAddingToTable, tryHandleCollision);
    b->SetInsertPoint(tryAddingToTable);
#ifdef USE_CUCKOO_HASHING
    Value * origPhrase1 = sym1;
    Value * origPhrase2 = sym2;

    PHINode * phraseMoved = b->CreatePHI(sizeTy, 2, "phraseMoved");
    phraseMoved->addIncoming(sz_ZERO, tryStore);
    PHINode * successPhi = b->CreatePHI(boolTy, 2, "successPhi");
    successPhi->addIncoming(b->getInt1(0), tryStore);

    PHINode * tableIdxHash1Phi = b->CreatePHI(sizeTy, 2, "tableIdxHash1Phi");
    tableIdxHash1Phi->addIncoming(tableIdxHash, tryStore);
    PHINode * tableIdxHash2Phi = b->CreatePHI(sizeTy, 2, "tableIdxHash2Phi");
    tableIdxHash2Phi->addIncoming(tableIdxHash_H2, tryStore);

    PHINode * addPhrase1 = b->CreatePHI(sym1->getType(), 2, "addPhrase1");
    addPhrase1->addIncoming(sym1, tryStore);
    PHINode * addPhrase2 = b->CreatePHI(sym2->getType(), 2, "addPhrase2");
    addPhrase2->addIncoming(sym2, tryStore);
    PHINode * addFreq = b->CreatePHI(sizeTy, 2);
    addFreq->addIncoming(phraseFreq, tryStore);
    Value * globalKeyIdxPtr_2 = b->CreateGEP(globalSubTablePtr, b->CreateMul(tableIdxHash_H2, keyLength));
    Value * globalTblEntryPtr_2 = b->CreateInBoundsGEP(globalKeyIdxPtr_2, sz_ZERO);

    // b->CallPrintInt("phraseMoved", phraseMoved);
    // Value * globalFreqTblEntryPtr = b->CreateInBoundsGEP(globalFreqSubTablePtr, tableIdxHash, "globalFreqTblEntryPtr");
    // Value * globalFreqTblPtr = b->CreateBitCast(globalFreqTblEntryPtr, sizeTy->getPointerTo());
    Value * globalKeyIdxPtr = b->CreateGEP(globalSubTablePtr, b->CreateMul(tableIdxHash, keyLength));
    Value * globalTblEntryPtr = b->CreateInBoundsGEP(globalKeyIdxPtr, sz_ZERO);
    Value * globalTblPtr1 = b->CreateBitCast(globalTblEntryPtr, lg.halfSymPtrTy);
    Value * globalTblPtr2 = b->CreateBitCast(b->CreateGEP(globalTblEntryPtr, keyOffset), lg.halfSymPtrTy);
    Value * entryFH1 = b->CreateMonitoredScalarFieldLoad("hashTable", globalTblPtr1);
    Value * entryFH2 = b->CreateMonitoredScalarFieldLoad("hashTable", globalTblPtr2);
    Value * entryFreqFH = b->CreateMonitoredScalarFieldLoad("freqTable", globalFreqTblPtr);

    Value * secHashTblEntryPtr = b->CreateInBoundsGEP(secHashTablePtr, /*tableIdxHash1Phi*/ tableIdxHash, "secHashTblEntryPtr");
    Value * secHashTblPtr = b->CreateBitCast(secHashTblEntryPtr, sizeTy->getPointerTo());
    Value * symSecHash = b->CreateMonitoredScalarFieldLoad("secondHashEntryTable", secHashTblPtr);
    // Value * isEmptyEntryFH = b->CreateICmpEQ(b->CreateOr(entryFH1, entryFH2), Constant::getNullValue(lg.halfLengthTy));
    // Value * lSegIdx = b->getScalarField("lastSegIndex");
    // Value * cSegIdx = b->getScalarField("segIndex");
    // Value * newSegEntry = b->CreateOr(b->CreateICmpEQ(cSegIdx, sz_ZERO), /* first segment */
    //                                   b->CreateICmpNE(lSegIdx, cSegIdx)); // isn't this ALWAYS TRUE?????
    b->CreateMonitoredScalarFieldStore("secondHashEntryTable", tableIdxHash_H2, secHashTblPtr);
    Value * symIsEqEntry = b->CreateAnd(b->CreateICmpEQ(addPhrase1, origPhrase1), b->CreateICmpEQ(addPhrase2, origPhrase2));
    Value * updateCount = b->CreateSelect(symIsEqEntry, b->CreateAdd(phraseMoved, sz_ONE), phraseMoved);
#endif
    Value * globalKeyIdxPtr = b->CreateGEP(globalSubTablePtr, b->CreateMul(tableIdxHash, keyLength));
    Value * globalTblEntryPtr = b->CreateInBoundsGEP(globalKeyIdxPtr, sz_ZERO);
    Value * globalTblPtr1 = b->CreateBitCast(globalTblEntryPtr, lg.halfSymPtrTy);
    Value * globalTblPtr2 = b->CreateBitCast(b->CreateGEP(globalTblEntryPtr, keyOffset), lg.halfSymPtrTy);
    b->CreateMonitoredScalarFieldStore("hashTable", /*addPhrase1*/sym1, globalTblPtr1);
    b->CreateMonitoredScalarFieldStore("hashTable", /*addPhrase2*/sym2, globalTblPtr2);
    b->CreateMonitoredScalarFieldStore("freqTable", /*addFreq*/phraseFreq, globalFreqTblPtr1);
    b->CreateStore(b->CreateTrunc(b->CreateAnd(tableIdxHash, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPos, sz_ONE)));
    b->CreateBr(nextKey); //checkLoopCond);

    b->SetInsertPoint(tryHandleCollision);
    Value * const endIdx = b->CreateSelect(b->CreateICmpUGE(b->CreateAdd(startIdx, b->getSize(0x50)), sz_HASH_TBL), b->CreateSub(sz_HASH_TBL, sz_ONE), b->CreateAdd(startIdx, b->getSize(0x50)));
    Value * findNextAvailIdxCond = b->CreateICmpUGE(phraseFreq, minFreqReqForCmp); // phrase can already exist in the nextAvailIdx
    findNextAvailIdxCond = b->CreateAnd(findNextAvailIdxCond, b->CreateICmpULT(startIdx, endIdx));
    b->CreateCondBr(findNextAvailIdxCond, findNextAvailIdx, nextKey); // same segment collision

    b->SetInsertPoint(findNextAvailIdx);
    b->CreateBr(indexReady);
    b->SetInsertPoint(indexReady);
    PHINode * curIndex = b->CreatePHI(sizeTy, 2, "curIndex");
    curIndex->addIncoming(startIdx, findNextAvailIdx);
    Value * nextIndex = b->CreateAdd(curIndex, sz_ONE);

    Value * nextSymIdxPtr = b->CreateGEP(globalSubTablePtr, b->CreateMul(curIndex, keyLength));
    Value * nextSymEntryPtr = b->CreateInBoundsGEP(nextSymIdxPtr, sz_ZERO);
    Value * nextSymPtr1 = b->CreateBitCast(nextSymEntryPtr, lg.halfSymPtrTy);
    Value * nextSymPtr2 = b->CreateBitCast(b->CreateGEP(nextSymEntryPtr, keyOffset), lg.halfSymPtrTy);
    Value * nextSym1 = b->CreateMonitoredScalarFieldLoad("hashTable", nextSymPtr1);
    Value * nextSym2 = b->CreateMonitoredScalarFieldLoad("hashTable", nextSymPtr2);
    Value * nextSymFreqTblEntryPtr = b->CreateInBoundsGEP(globalFreqSubTablePtr, curIndex);
    Value * nextSymFreqTblPtr = b->CreateBitCast(nextSymFreqTblEntryPtr, sizeTy->getPointerTo());
    // Value * nextSymFreq2 = b->CreateMonitoredScalarFieldLoad("freqTable", nextSymFreqTblPtr);
    // b->CallPrintInt("curIndex", curIndex);
    Value * phraseMatch = b->CreateAnd(b->CreateICmpEQ(nextSym1, sym1), b->CreateICmpEQ(nextSym2, sym2));
    b->CreateCondBr(phraseMatch, writeNextIdx, tryStoreInNextIdx);
    b->SetInsertPoint(writeNextIdx);
    b->CreateStore(b->CreateTrunc(b->CreateAnd(curIndex, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPos, sz_ONE)));
    b->CreateBr(nextKey);

    b->SetInsertPoint(tryStoreInNextIdx);
    Value * isEmptyNextSymEntry = b->CreateICmpEQ(b->CreateOr(nextSym1, nextSym2), Constant::getNullValue(lg.halfLengthTy));
    b->CreateCondBr(b->CreateOr(isEmptyNextSymEntry, /*b->CreateICmpUGT(phraseFreq, nextSymFreq2)*/b->CreateICmpUGE(phraseFreq, minFreqReqForCmp)), storeInNextEmptyHash, checkIdxCond);
    b->SetInsertPoint(storeInNextEmptyHash);
    b->CreateMonitoredScalarFieldStore("hashTable", sym1, nextSymPtr1);
    b->CreateMonitoredScalarFieldStore("hashTable", sym2, nextSymPtr2);
    b->CreateMonitoredScalarFieldStore("freqTable", phraseFreq, nextSymFreqTblPtr);
    b->CreateStore(b->CreateTrunc(b->CreateAnd(curIndex, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPos, sz_ONE))); // ANND curIndex with TABLE_MASK ??
    b->CreateBr(nextKey);

    b->SetInsertPoint(checkIdxCond);
    curIndex->addIncoming(nextIndex, checkIdxCond);
    b->CreateCondBr(b->CreateICmpNE(nextIndex, endIdx), indexReady, nextKey);

#ifdef USE_CUCKOO_HASHING
    // move the phrase from its first hash index (H1) and place the colliding phrase in H1
    b->SetInsertPoint(checkSecondHash);

    Value * evictPhrase1AtFH = entryFH1;
    Value * evictPhrase2AtFH = entryFH2;
    Value * evictPhraseFreqAtFH = entryFreqFH;
    Value * evictPhraseAltHash = symSecHash;
    Value * evictPhraseHash = tableIdxHash1Phi;

    b->CreateMonitoredScalarFieldStore("hashTable", addPhrase1, globalTblPtr1);
    b->CreateMonitoredScalarFieldStore("hashTable", addPhrase2, globalTblPtr2);
    b->CreateMonitoredScalarFieldStore("secondHashEntryTable", tableIdxHash1Phi, secHashTblPtr);
    b->CreateMonitoredScalarFieldStore("freqTable", addFreq, globalFreqTblPtr);

    Value * symIsEqEntrySH = b->CreateAnd(b->CreateICmpEQ(addPhrase1, origPhrase1), b->CreateICmpEQ(addPhrase2, origPhrase2));
    Value * updateCountSH = b->CreateSelect(symIsEqEntrySH, b->CreateAdd(phraseMoved, sz_ONE), phraseMoved);
    Value * success1 = b->CreateSelect(symIsEqEntrySH, b->getInt1(1), b->getInt1(0));

    // try storing evicted entry in its second hash index
    Value * evictSymIdxPtr = b->CreateGEP(globalSubTablePtr, b->CreateMul(evictPhraseAltHash, keyLength));
    Value * evictSymEntryPtr = b->CreateInBoundsGEP(evictSymIdxPtr, sz_ZERO);
    Value * evictSymPtr1 = b->CreateBitCast(evictSymEntryPtr, lg.halfSymPtrTy);
    Value * evictSymPtr2 = b->CreateBitCast(b->CreateGEP(evictSymEntryPtr, keyOffset), lg.halfSymPtrTy);
    Value * evictSymSH1 = b->CreateMonitoredScalarFieldLoad("hashTable", evictSymPtr1);
    Value * evictSymSH2 = b->CreateMonitoredScalarFieldLoad("hashTable", evictSymPtr2);
    Value * evictSymSHTblEntryPtr = b->CreateInBoundsGEP(secHashTablePtr, evictPhraseAltHash);
    Value * evictSymSHTblPtr = b->CreateBitCast(evictSymSHTblEntryPtr, sizeTy->getPointerTo());
    Value * evictSymFreqTblEntryPtr = b->CreateInBoundsGEP(globalFreqSubTablePtr, evictPhraseAltHash);
    Value * evictSymFreqTblPtr = b->CreateBitCast(evictSymFreqTblEntryPtr, sizeTy->getPointerTo());
    Value * evictSymFreqSH2 = b->CreateMonitoredScalarFieldLoad("freqTable", evictSymFreqTblPtr);

    Value * isEmptyEvictSymShEntry = b->CreateICmpEQ(b->CreateOr(evictSymSH1, evictSymSH2), Constant::getNullValue(lg.halfLengthTy)); // also check for freq? happens in the next iteration.
    b->CreateCondBr(b->CreateOr(newSegEntry, isEmptyEvictSymShEntry), storeInSecondHash, checkLoopCond);

    b->SetInsertPoint(storeInSecondHash);
    // evict the phrase from its H1 and store in H2
    // if cannot be stored, loop again.
    b->CreateMonitoredScalarFieldStore("hashTable", evictPhrase1AtFH, evictSymPtr1);
    b->CreateMonitoredScalarFieldStore("hashTable", evictPhrase2AtFH, evictSymPtr2);
    b->CreateMonitoredScalarFieldStore("secondHashEntryTable", evictPhraseHash, evictSymSHTblPtr);
    b->CreateMonitoredScalarFieldStore("freqTable", evictPhraseFreqAtFH, evictSymFreqTblPtr);

    Value * evictPhraseIsEqEntrySH = b->CreateAnd(b->CreateICmpEQ(evictPhrase1AtFH, origPhrase1), b->CreateICmpEQ(evictPhrase2AtFH, origPhrase2));
    Value * evictPhraseUpdateCountSH = b->CreateSelect(evictPhraseIsEqEntrySH, b->CreateAdd(phraseMoved, sz_ONE), phraseMoved);
    Value * success2 = b->getInt1(1);
    b->CreateBr(checkLoopCond);

    b->SetInsertPoint(checkLoopCond);
    PHINode * successPhiUpdate = b->CreatePHI(boolTy, 3);
    successPhiUpdate->addIncoming(b->getInt1(1), storeInFirstHash);
    successPhiUpdate->addIncoming(success1, checkSecondHash);
    successPhiUpdate->addIncoming(success2, storeInSecondHash);

    PHINode * movedCountUpdate = b->CreatePHI(sizeTy, 3);
    movedCountUpdate->addIncoming(updateCount, storeInFirstHash);
    movedCountUpdate->addIncoming(updateCountSH, checkSecondHash);
    movedCountUpdate->addIncoming(evictPhraseUpdateCountSH, storeInSecondHash);

    PHINode * hash1Update = b->CreatePHI(sizeTy, 3);
    hash1Update->addIncoming(tableIdxHash1Phi, storeInFirstHash); // doesn't matter?
    hash1Update->addIncoming(evictPhraseAltHash, checkSecondHash);
    hash1Update->addIncoming(evictPhraseAltHash, storeInSecondHash);

    PHINode * hash2Update = b->CreatePHI(sizeTy, 3);
    hash2Update->addIncoming(tableIdxHash2Phi, storeInFirstHash); // doesn't matter?
    hash2Update->addIncoming(evictPhraseHash, checkSecondHash);
    hash2Update->addIncoming(evictPhraseHash, storeInSecondHash);

    PHINode * addPhrase1Update = b->CreatePHI(sym1->getType(), 3, "addPhrase1Update");
    addPhrase1Update->addIncoming(addPhrase1, storeInFirstHash); // doesn't matter?
    addPhrase1Update->addIncoming(evictPhrase1AtFH, checkSecondHash);
    addPhrase1Update->addIncoming(evictPhrase1AtFH, storeInSecondHash);

    PHINode * addPhrase2Update = b->CreatePHI(sym2->getType(), 3, "addPhrase2Update");
    addPhrase2Update->addIncoming(addPhrase2, storeInFirstHash); // doesn't matter?
    addPhrase2Update->addIncoming(evictPhrase2AtFH, checkSecondHash);
    addPhrase2Update->addIncoming(evictPhrase1AtFH, storeInSecondHash);

    PHINode * freqUpdate = b->CreatePHI(sizeTy, 3, "freqUpdate");
    freqUpdate->addIncoming(addFreq, storeInFirstHash); // doesn't matter?
    freqUpdate->addIncoming(evictPhraseFreqAtFH, checkSecondHash);
    freqUpdate->addIncoming(evictPhraseFreqAtFH, storeInSecondHash);

    phraseMoved->addIncoming(movedCountUpdate, checkLoopCond);
    successPhi->addIncoming(successPhiUpdate, checkLoopCond);
    tableIdxHash1Phi->addIncoming(hash1Update, checkLoopCond);
    tableIdxHash2Phi->addIncoming(hash2Update, checkLoopCond);
    addPhrase1->addIncoming(addPhrase1Update, checkLoopCond);
    addPhrase2->addIncoming(addPhrase2Update, checkLoopCond);
    addFreq->addIncoming(freqUpdate, checkLoopCond);
    b->CreateCondBr(b->CreateAnd(b->CreateICmpNE(movedCountUpdate, b->getSize(3)), 
                                 b->CreateICmpEQ(successPhiUpdate, b->getInt1(0))), tryAddingToTable, nextKey);
#endif
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
#ifdef USE_CUCKOO_HASHING
    Value * symMarkPos_H2 = b->CreateSub(symMarkPos, sz_ONE);
    Value * symCodewordVal_H2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", symMarkPos_H2)), sizeTy);
    Value * symHashcodePos_H2 = symMarkPos_H2;

    // Build up a single encoded value for table lookup from the hashcode sequence.
    Value * symCodewordVal = b->CreateAnd(symHashValue, lg.LAST_SUFFIX_MASK);
    Value * symHashcodePos = symMarkPos;
    // symCodewordVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(symCodewordVal, sz_ONE), b->CreateShl(symCodewordVal, sz_ONE)),
    //                               symCodewordVal);

    b->CreateCondBr(b->CreateICmpUGT(mGroupNoVal, sz_ZERO), calcSymSuffixMask, calcSymPfxMask);

    b->SetInsertPoint(calcSymSuffixMask);
    symHashcodePos = b->CreateSub(symHashcodePos, sz_ONE);
    symHashcodePos_H2 = b->CreateSub(symHashcodePos_H2, sz_ONE);
    Value * symSecondLastSuffix = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", symHashcodePos)), sizeTy);
    Value * symSecondLastSuffix_H2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", symHashcodePos_H2)), sizeTy);
    Value * symCwVal = b->CreateShl(symCodewordVal, lg.SEC_LAST_SFX, "symCodewordVal");
    symCwVal = b->CreateOr(symCwVal, b->CreateAnd(symSecondLastSuffix, lg.SEC_LAST_SUFFIX_MASK));

    Value * symCwVal_H2 = b->CreateShl(symCodewordVal_H2, lg.SEC_LAST_SFX, "symCodewordVal_H2");
    symCwVal_H2 = b->CreateOr(symCwVal_H2, b->CreateAnd(symSecondLastSuffix_H2, lg.SEC_LAST_SUFFIX_MASK));

    b->CreateBr(calcSymPfxMask);

    b->SetInsertPoint(calcSymPfxMask);
    PHINode * hcPos_1 = b->CreatePHI(sizeTy, 2);
    hcPos_1->addIncoming(symHashcodePos, calcSymSuffixMask);
    hcPos_1->addIncoming(symMarkPos, processSym);
    PHINode * symCodewordValPhi = b->CreatePHI(sizeTy, 2, "symCodewordValPhi");
    symCodewordValPhi->addIncoming(symCwVal, calcSymSuffixMask);
    symCodewordValPhi->addIncoming(symCodewordVal, processSym);
    PHINode * hcPos_2 = b->CreatePHI(sizeTy, 2);
    hcPos_2->addIncoming(symHashcodePos_H2, calcSymSuffixMask);
    hcPos_2->addIncoming(symMarkPos_H2, processSym);
    PHINode * symCodewordValPhi_H2 = b->CreatePHI(sizeTy, 2, "symCodewordValPhi");
    symCodewordValPhi_H2->addIncoming(symCwVal_H2, calcSymSuffixMask);
    symCodewordValPhi_H2->addIncoming(symCodewordVal_H2, processSym);
    Value * symCodewordValFin_H2 = symCodewordValPhi_H2;
    Value * readPos_2 = b->CreateSub(hcPos_2, sz_ONE);
    Value * symPfxByte_H2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", readPos_2)), sizeTy);
    symPfxByte_H2 = b->CreateTrunc(b->CreateAnd(symPfxByte_H2, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    symCodewordValFin_H2 = b->CreateOr(b->CreateAnd(symPfxByte_H2, lg.EXTRA_BITS_MASK), b->CreateShl(symCodewordValFin_H2, lg.EXTRA_BITS));
    Value * symTableIdxHash_H2 = b->CreateAnd(symCodewordValFin_H2, lg.TABLE_MASK, "tableIdx");
    Value * symIdxPtr_H2 = b->CreateGEP(symSubTablePtr, b->CreateMul(symTableIdxHash_H2, symLength));
    Value * symTblEntryPtr_H2 = b->CreateInBoundsGEP(symIdxPtr_H2, sz_ZERO);
    Value * symTblPtr1_H2 = b->CreateBitCast(symTblEntryPtr_H2, lg.halfSymPtrTy);
    Value * symTblPtr2_H2 = b->CreateBitCast(b->CreateGEP(symTblEntryPtr_H2, symOffset), lg.halfSymPtrTy);
    Value * entry11_H2 = b->CreateMonitoredScalarFieldLoad("hashTable", symTblPtr1_H2);
    Value * entry22_H2 = b->CreateMonitoredScalarFieldLoad("hashTable", symTblPtr2_H2);
    Value * symIsEqEntry1_H2 = b->CreateAnd(b->CreateICmpEQ(entry11_H2, sym11), b->CreateICmpEQ(entry22_H2, sym22));
    Value * symCodewordValFin = symCodewordValPhi;
    // add PREFIX_LENGTH_MASK bits for larger index space
    Value * readPos_1 = b->CreateSub(hcPos_1, sz_ONE);
    Value * symPfxByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", readPos_1)), sizeTy);
    symPfxByte = b->CreateTrunc(b->CreateAnd(symPfxByte, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    symCodewordValFin = b->CreateOr(b->CreateAnd(symPfxByte, lg.EXTRA_BITS_MASK), b->CreateShl(symCodewordValFin, lg.EXTRA_BITS));
#endif
    Value * symTblIndex = b->CreateZExt(b->CreateLoad(b->getRawOutputPointer("freqUpdated", b->CreateSub(symMarkPos, sz_ONE))), sizeTy);
    Value * symSubTablePtr = b->CreateGEP(globalHashTableBasePtr, b->CreateMul(b->CreateSub(symLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    Value * symTableIdxHash = b->CreateAnd(/*symCodewordValFin*/symTblIndex, lg.TABLE_MASK, "tableIdx");
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

    Value * symFreqSubTablePtr = b->CreateGEP(globalFreqTableBasePtr, b->CreateMul(b->CreateSub(symLength, lg.LO), lg.FREQ_SUBTABLE_SIZE));
    Value * symFreqTblEntryPtr = b->CreateInBoundsGEP(symFreqSubTablePtr, symTableIdxHash, "symFreqTblEntryPtr");
    Value * symFreqTblPtr = b->CreateBitCast(symFreqTblEntryPtr, sizeTy->getPointerTo());
    Value * symFreq = b->CreateMonitoredScalarFieldLoad("freqTable", symFreqTblPtr);

    Value * symIsEqEntry1 = b->CreateAnd(b->CreateICmpEQ(entry11, sym11), b->CreateICmpEQ(entry22, sym22));
#ifdef USE_CUCKOO_HASHING
    symIsEqEntry1 = b->CreateOr(symIsEqEntry1, symIsEqEntry1_H2);
#endif
    b->CreateCondBr(symIsEqEntry1, checkSymCompression, nextSym);
#if 0
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr11, symLength);
    // b->CallPrintInt("symHashValue", symHashValue);
    // b->CallPrintInt("symLength", symLength);
    // b->CallPrintInt("symTableIdxHashSH", symTableIdxHashSH);
    // b->CallPrintInt("b->CreateZExtOrTrunc(b->CreateOr(symHashValue, b->getSize(0x80)), b->getInt16Ty())", b->CreateZExtOrTrunc(b->CreateOr(symHashValue, b->getSize(0x80)), b->getInt16Ty()));
    // b->CallPrintInt("b->CreateOr(symHashValue, b->getSize(0x80)", b->CreateOr(symHashValue, b->getSize(0x80)));
#endif
    b->SetInsertPoint(checkSymCompression);

#if 0
    // update pfx byte to 0
    Value * condCheck = b->CreateICmpEQ(symTableIdxHash, b->getSize(0x1bd1));
    b->CreateCondBr(condCheck, printPhrase, proceed);
    b->SetInsertPoint(printPhrase);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr11, symLength);
    b->CallPrintInt("symTableIdxHash", symTableIdxHash);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symTblPtr1, symLength);
    b->CallPrintInt("symTableIdxHash_H2", symTableIdxHash_H2);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symTblPtr1_H2, symLength);
    b->CreateBr(proceed);
    b->SetInsertPoint(proceed);
#endif
    // Mark the last bit of phrase
    Value * overlapConditionCheck = b->CreateICmpUGE(b->getSize(mNumSym), sz_ONE);
    b->CreateCondBr(overlapConditionCheck, continueOverlapCheck, markSymCompression);
    b->SetInsertPoint(continueOverlapCheck);

    Value * symStartBase = b->CreateSub(symStartPos, b->CreateURem(symStartPos, b->getSize(8)));
    Value * offset = b->CreateSub(symStartPos, symStartBase);
    Value * const outputMarkBasePtr = b->CreateBitCast(b->getRawOutputPointer("hashMarks", symStartBase), sizeTy->getPointerTo());
    Value * initialOutputMark = b->CreateAlignedLoad(outputMarkBasePtr, 1);

    // Value * curGroupMark = b->CreateOr(initialOutputMark, b->CreateShl(sz_ONE, offset)); // include current phrase's mark
    Value * sameGroupMark = initialOutputMark; // only has previously marked phrases
    sameGroupMark = b->CreateLShr(sameGroupMark, offset);
    Value * sameGrpLShrFZ = b->CreateCountForwardZeroes(sameGroupMark);
    sameGrpLShrFZ = b->CreateSelect(b->CreateICmpEQ(sameGrpLShrFZ, b->getSize(64)), sz_ZERO, sameGrpLShrFZ);
    Value * sameGrpLShrFZOverlapPos = b->CreateAdd(symStartPos, sameGrpLShrFZ); // correct sym end pos for same group
    sameGrpLShrFZOverlapPos = b->CreateSelect(b->CreateICmpEQ(sameGrpLShrFZOverlapPos, symStartPos), symMarkPos, sameGrpLShrFZOverlapPos);

    Value * sameGrpSymHash = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", sameGrpLShrFZOverlapPos)), sizeTy);
    Value * sameGrpSymLength = b->CreateAdd(b->CreateLShr(sameGrpSymHash, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET, "sameGrpSymLength");
    Value * sameGrpStartPos = b->CreateSub(sameGrpLShrFZOverlapPos, b->CreateSub(sameGrpSymLength, sz_ONE), "sameGrpStartPos"); // position of phrase-end in the middle of current phrase

    Value * sameGrpLShrOverlapPart1 = b->CreateAnd(b->CreateICmpUGT(sameGrpStartPos, symStartPos), b->CreateICmpULE(sameGrpStartPos, symMarkPos));
    Value * sameGrpLShrOverlapPart2 = b->CreateAnd(b->CreateICmpUGT(sameGrpLShrFZOverlapPos, symStartPos), b->CreateICmpULT(sameGrpLShrFZOverlapPos, symMarkPos));
    Value * sameGrpLShrOverlap = b->CreateOr(sameGrpLShrOverlapPart1, sameGrpLShrOverlapPart2);

    b->CreateCondBr(b->CreateICmpULT(b->getSize(mGroupNo), b->getSize(3)),
                    compareOverlappingSymWithinAndAcrossGroups,
                    compareOverlappingSymInLastGroup); // cmpMarksSoFar is symEndMarks for last group; dont want to compare phrases with all sym end marks!

    b->SetInsertPoint(compareOverlappingSymInLastGroup);
    b->CreateCondBr(b->CreateICmpEQ(sameGrpLShrOverlap, b->getInt1(0)), markSymCompression, updateFreq);//nextSym);

    b->SetInsertPoint(compareOverlappingSymWithinAndAcrossGroups);
    Value * currentSymFreq = b->CreateZExt(b->CreateLoad(b->getRawOutputPointer("freqUpdated", symMarkPos)), sizeTy);
    currentSymFreq = b->CreateMul(currentSymFreq, symLength);

    Value * const cmpMarkBasePtr = b->CreateBitCast(b->getRawInputPointer("cmpMarksSoFar", symStartBase), sizeTy->getPointerTo());
    Value * initialCmpMark = b->CreateAlignedLoad(cmpMarkBasePtr, 1);
    Value * prevGroupMark = initialCmpMark;
    Value * prevGroupMarkLShr = b->CreateLShr(prevGroupMark, offset); // uncommented works
    Value * prevGrpLShrFZ = b->CreateCountForwardZeroes(prevGroupMarkLShr);
    prevGrpLShrFZ = b->CreateSelect(b->CreateICmpEQ(prevGrpLShrFZ, b->getSize(64)), sz_ZERO, prevGrpLShrFZ);
    Value * prevGrpLShrFZOverlapPos = b->CreateAdd(symStartPos, prevGrpLShrFZ); // correct sym end pos for prev group
    prevGrpLShrFZOverlapPos = b->CreateSelect(b->CreateICmpEQ(prevGrpLShrFZOverlapPos, symStartPos), symMarkPos, prevGrpLShrFZOverlapPos);

    Value * prevGrpSymHash = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", prevGrpLShrFZOverlapPos)), sizeTy);
    Value * prevGrpSymLength = b->CreateAdd(b->CreateLShr(prevGrpSymHash, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET);
    Value * prevGrpStartPos = b->CreateSub(prevGrpLShrFZOverlapPos, b->CreateSub(prevGrpSymLength, sz_ONE), "prevGrpStartPos");

    // overlap happens when the start or end position of previous group phrase is in between current phrase's start and end position.
    Value * prevGrpOverlapPart1 = b->CreateAnd(b->CreateICmpUGT(prevGrpStartPos, symStartPos), b->CreateICmpULE(prevGrpStartPos, symMarkPos));
    Value * prevGrpOverlapPart2 = b->CreateAnd(b->CreateICmpUGT(prevGrpLShrFZOverlapPos, symStartPos), b->CreateICmpULT(prevGrpLShrFZOverlapPos, symMarkPos));
    Value * prevGrpLShrOverlap = b->CreateOr(prevGrpOverlapPart1, prevGrpOverlapPart2);
    // b->CallPrintInt("prevGrpLShrOverlap", prevGrpLShrOverlap); //BIGRAMDEBUGGING
    b->CreateCondBr(b->CreateICmpEQ(prevGrpLShrOverlap, b->getInt1(0)), checkSameGrpOverlap, updateFreq); //ignore previous group overlaps; do not have access to their absolute frequencies

    b->SetInsertPoint(checkSameGrpOverlap);
    b->CreateCondBr(b->CreateICmpEQ(sameGrpLShrOverlap, b->getInt1(0)), markSymCompression, updateFreq);
    // update the frequency of phrase that cannot be compressed.
    b->SetInsertPoint(updateFreq);
    Value * updatedFreq = b->CreateSub(symFreq, sz_ONE);
    b->CreateMonitoredScalarFieldStore("freqTable", updatedFreq, symFreqTblPtr);
    b->CreateCondBr(b->CreateICmpULT(updatedFreq, minFreqReqForCmp), removeHashTableEntry, nextSym);

    b->SetInsertPoint(removeHashTableEntry);
    b->CreateMonitoredScalarFieldStore("freqTable", sz_ZERO, symFreqTblPtr);
    b->CreateMonitoredScalarFieldStore("hashTable", Constant::getNullValue(lg.halfLengthTy), symTblPtr1);
    b->CreateMonitoredScalarFieldStore("hashTable", Constant::getNullValue(lg.halfLengthTy), symTblPtr2);
    b->CreateBr(nextSym);

    b->SetInsertPoint(checkUnmark);
    Value * sameGrpPhraseFreq = b->CreateZExt(b->CreateLoad(b->getRawOutputPointer("freqUpdated", sameGrpLShrFZOverlapPos)), sizeTy);

    sameGrpPhraseFreq = b->CreateMul(sameGrpPhraseFreq, sameGrpSymLength);
    Value * checkUnMarkSameGrp = b->CreateICmpUGT(sameGrpPhraseFreq, currentSymFreq);
    b->CreateCondBr(checkUnMarkSameGrp, nextSym, unMarkSameGrpPhrase);

    b->SetInsertPoint(unMarkSameGrpPhrase);
    Value * base = b->CreateSub(sameGrpLShrFZOverlapPos, b->CreateURem(sameGrpLShrFZOverlapPos, sz_BITS));
    Value * overlapSymOffset = b->CreateSub(sameGrpLShrFZOverlapPos, base);
    Value * const basePtr = b->CreateBitCast(b->getRawOutputPointer("hashMarks", base), sizeTy->getPointerTo());
    Value * origMask = b->CreateAlignedLoad(basePtr, 1);
    Value * unmarkedMask = b->CreateXor(origMask, b->CreateShl(sz_ONE, overlapSymOffset));
    b->CreateAlignedStore(unmarkedMask, basePtr, 1);

    // update the hashtable frequency -> not like hashtbale is compared against segment table for future phrases. But helpful for any future segments
    // What this does: this acts like an evacuation policy?
    Value * tblHash = b->CreateZExt(b->CreateLoad(b->getRawOutputPointer("freqUpdated", b->CreateSub(sameGrpLShrFZOverlapPos, sz_ONE))), sizeTy);
    Value * globalSymUpdateFreqSubTablePtr = b->CreateGEP(globalFreqTableBasePtr, b->CreateMul(b->CreateSub(sameGrpSymLength, lg.LO), lg.FREQ_SUBTABLE_SIZE));
    Value * globalSymUpdateFreqTblEntryPtr = b->CreateInBoundsGEP(globalSymUpdateFreqSubTablePtr, tblHash);
    Value * globalSymUpdateFreqTblPtr = b->CreateBitCast(globalSymUpdateFreqTblEntryPtr, sizeTy->getPointerTo());
    Value * curFreq = b->CreateMonitoredScalarFieldLoad("freqTable", globalSymUpdateFreqTblPtr);
    b->CreateMonitoredScalarFieldStore("freqTable", b->CreateZExtOrTrunc(b->CreateSub(curFreq, sz_ONE), sizeTy), globalSymUpdateFreqTblPtr);
    b->CreateBr(markSymCompression);

    b->SetInsertPoint(markSymCompression);
#ifdef USE_CUCKOO_HASHING
    b->CreateCondBr(symIsEqEntry1_H2, secHashPhrases, secHashSymMarked);

    b->SetInsertPoint(secHashPhrases);
    Value * pMarkBase = b->CreateSub(symMarkPos, b->CreateURem(symMarkPos, sz_BITS));
    Value * pOffset = b->CreateSub(symMarkPos, pMarkBase);
    Value * const pOoutputPtr = b->CreateBitCast(b->getRawOutputPointer("secHashMarks", pMarkBase), sizeTy->getPointerTo());
    Value * pInitMark = b->CreateAlignedLoad(pOoutputPtr, 1);
    Value * pUpdatedMask = b->CreateOr(pInitMark, b->CreateShl(sz_ONE, pOffset));
    b->CreateAlignedStore(pUpdatedMask, pOoutputPtr, 1);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr11, symLength);
    b->CreateBr(secHashSymMarked);

    b->SetInsertPoint(secHashSymMarked);
#endif
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
    b->setScalarField("lastSegIndex", b->getScalarField("segIndex"));
    b->setScalarField("segIndex", b->CreateAdd(sz_ONE, b->getScalarField("segIndex")));
    b->setScalarField("absBlocksProcessed", b->CreateUDiv(lfPos, sz_BLOCKWIDTH));
    strideNo->addIncoming(nextStrideNo, symsDone);
    // Value * hashTableSz = b->getSize((mEncodingScheme.byLength[mGroupNo].hi * phraseHashSubTableSize(mEncodingScheme, mGroupNo, mNumSym)) * (mEncodingScheme.byLength[mGroupNo].hi - mEncodingScheme.byLength[mGroupNo].lo + 1));
    // Value * freqTableSz = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo, mNumSym) * (mEncodingScheme.byLength[mGroupNo].hi - mEncodingScheme.byLength[mGroupNo].lo + 1));
    // b->CreateMemZero(hashTableBasePtr, hashTableSz);
    // b->CreateMemZero(freqTableBasePtr, freqTableSz);
    b->CreateMemZero(phraseVectorBasePtr, b->getSize(mEncodingScheme.byLength[mGroupNo].hi * 
                                                     phraseVectorSize(mEncodingScheme, mGroupNo) * 
                                                     (mEncodingScheme.byLength[mGroupNo].hi - mEncodingScheme.byLength[mGroupNo].lo + 1)));
    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), stridePrologue, stridesDone);
    b->SetInsertPoint(stridesDone);

    // Although we have written the last block mask, we do not include it as
    // produced, because we may need to update it in the event that there is
    // a compressible symbol starting in this segment and finishing in the next.
    Value * producedBlocks = b->CreateUDiv(lfPos, sz_BLOCKWIDTH);
    Value * produced = b->CreateSelect(b->isFinal(), avail, b->CreateMul(producedBlocks, sz_BLOCKWIDTH));
    b->setProducedItemCount("hashMarks", produced);
    b->setProducedItemCount("secHashMarks", produced);
    b->setProducedItemCount("freqUpdated", produced);
    Value * processed = b->CreateSelect(b->isFinal(), avail, b->CreateMul(producedBlocks, sz_BLOCKWIDTH));
    b->setProcessedItemCount("symEndMarks", processed);
    b->setProcessedItemCount("cmpMarksSoFar", processed);
    b->setProcessedItemCount("hashValues", processed);
    b->setProcessedItemCount("initFreq", processed);
    b->setProcessedItemCount("byteData", processed);
    b->setProcessedItemCount("lfPos", b->getScalarField("segIndex"));
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
                                               StreamSet * secHashMark,
                                               StreamSet * hashValues,
                                               StreamSet * allHashValuesFinal,
                                               StreamSet * const byteData,
                                               StreamSet * compressionMask,
                                               StreamSet * encodedBytes,
                                               StreamSet * codewordMask,
                                               unsigned strideBlocks)
: MultiBlockKernel(b, "SymbolGroupCompression" + std::to_string(numSyms) + std::to_string(groupNo) + lengthGroupSuffix(encodingScheme, groupNo) + std::to_string(plen) + (GetSegWiseDict() ? "_sd" : ""),
                   {Binding{"lfPos", lfData, GreedyRate(), Deferred()},
                    Binding{"symbolMarks", symbolMarks,  FixedRate(1), Deferred()},
                    Binding{"secHashMark", secHashMark, FixedRate(1), Deferred()},
                    Binding{"hashValues", hashValues,  FixedRate(1), Deferred()},
                    Binding{"allHashValuesFinal", allHashValuesFinal, FixedRate(1), Deferred()},
                    Binding{"byteData", byteData,  FixedRate(1), Deferred()}},
                   {}, {}, {},
                   {InternalScalar{b->getBitBlockType(), "pendingMaskInverted"},
                    InternalScalar{b->getBitBlockType(), "pendingPhraseMask"},
                    InternalScalar{b->getSizeTy(), "segIndex"},
                    InternalScalar{b->getSizeTy(), "absBlocksProcessed"},
                    InternalScalar{b->getSizeTy(), "lastLfPos"},
                    InternalScalar{ArrayType::get(ArrayType::get(ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), phraseHashSubTableSize(encodingScheme, groupNo, numSyms)), 
+                                  (encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1)), "hashTable"},
                    InternalScalar{ArrayType::get(b->getSizeTy(), phraseHashSubTableSize(encodingScheme, groupNo, numSyms) * (encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1)), "lastSeenSeg"}}),
mEncodingScheme(encodingScheme), mGroupNo(groupNo), mNumSym(numSyms), mSubStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS)), mOffset(offset), mStrideSize(1048576) {
        mOutputStreamSets.emplace_back("compressionMask", compressionMask, FixedRate(), Delayed(1048576) );
        mOutputStreamSets.emplace_back("encodedBytes", encodedBytes, FixedRate(), Delayed(1048576) );
        mOutputStreamSets.emplace_back("codewordMask", codewordMask, FixedRate(), Delayed(1048576) );
        setStride(1048576);
}

void SymbolGroupCompression::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    ScanWordParameters sw(b, mStrideSize);
    LengthGroupParameters lg(b, mEncodingScheme, mGroupNo, mNumSym);
    Constant * sz_DELAYED = b->getSize(mEncodingScheme.maxSymbolLength());
    Constant * sz_SUB_STRIDE = b->getSize(mSubStride);
    Constant * sz_BLOCKS_PER_SUB_STRIDE = b->getSize(mSubStride/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_BITS = b->getSize(SIZE_T_BITS);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    // Constant * sz_PLEN = b->getSize(mPlen);
    Constant * sz_PHRASE_LEN_OFFSET = b->getSize(mOffset);
    Value * sz_HALF_TBL_IDX = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo, mNumSym) / 2);
    Value * sz_HALF_TBL_IDX_0 = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo, mNumSym) / 3);
    Value * checkGroupNum = b->CreateICmpUGT(b->getSize(mGroupNo), sz_ZERO);
    sz_HALF_TBL_IDX = b->CreateSelect(checkGroupNum, sz_HALF_TBL_IDX, sz_HALF_TBL_IDX_0);
    checkGroupNum = b->CreateICmpEQ(b->getSize(mGroupNo), b->getSize(3));
    sz_HALF_TBL_IDX = b->CreateSelect(checkGroupNum, sz_ZERO, sz_HALF_TBL_IDX);
    Value * mGroupNoVal = b->getSize(mGroupNo);

    assert ((mStrideSize % mSubStride) == 0);
    Value * totalSubStrides =  b->getSize(mStrideSize / mSubStride);

    Type * sizeTy = b->getSizeTy();
    Type * bitBlockPtrTy = b->getBitBlockType()->getPointerTo();

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
    BasicBlock * const updateLastSeen = b->CreateBasicBlock("updateLastSeen");
    BasicBlock * const tryCompression = b->CreateBasicBlock("tryCompression");
#ifdef USE_CUCKOO_HASHING
    BasicBlock * const storeInFirstHash = b->CreateBasicBlock("storeInFirstHash");
    BasicBlock * const storeInSecHash = b->CreateBasicBlock("storeInSecHash");
    BasicBlock * const calcSuffixMask = b->CreateBasicBlock("calcSuffixMask");
    BasicBlock * const calcPfxMask = b->CreateBasicBlock("calcPfxMask");
    BasicBlock * const writeSecLastSfx = b->CreateBasicBlock("writeSecLastSfx");
    BasicBlock * const writePfx = b->CreateBasicBlock("writePfx");
#endif
    BasicBlock * const writeSfx3 = b->CreateBasicBlock("writeSfx3");
    BasicBlock * const checkSfx2 = b->CreateBasicBlock("checkSfx2");
    BasicBlock * const writeSfx2 = b->CreateBasicBlock("writeSfx2");
    BasicBlock * const writeSfx1 = b->CreateBasicBlock("writeSfx1");
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
    Value * const avail = b->getAvailableItemCount("symbolMarks");

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
    Value * lastSeenTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("lastSeenSeg"), sizeTy->getPointerTo());
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
    //b->CreateSub(b->CreateSub(lfPos, b->getScalarField("lastLfPos")), sz_ONE); ////// fixes the segfaults 
    Value * memCpyPos = b->getScalarField("lastLfPos");

    b->CreateMemCpy(b->getRawOutputPointer("encodedBytes", memCpyPos), b->getRawInputPointer("byteData", memCpyPos), toCopy, 1); 

    Value * totalProcessed = b->CreateMul(b->getScalarField("absBlocksProcessed"), sz_BLOCKWIDTH);
    Value * stridePos =  totalProcessed;
    Value * strideBlockOffset = b->getScalarField("absBlocksProcessed");
    Value * processBeforeThisPos = lfPos;
    Value * processAfterThisPos = b->getScalarField("lastLfPos");
    b->setScalarField("lastLfPos", lfPos);
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
    // Value * hashExtBit = b->CreateAnd(hashValue, b->getSize(0x80));
    Value * keyLength = b->CreateAdd(b->CreateLShr(hashValue, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET, "keyLength");
    Value * keyStartPos = b->CreateSub(keyMarkPos, b->CreateSub(keyLength, sz_ONE), "keyStartPos");
    // keyOffset for accessing the final half of an entry.
    Value * keyOffset = b->CreateSub(keyLength, lg.HALF_LENGTH);
#ifdef USE_CUCKOO_HASHING
    Value * keyMarkPos_H2 = b->CreateSub(keyMarkPos, sz_ONE, "keyMarkPos_H2");
    // Get the hash of this key.
    // Value * keyHash = b->CreateAnd(hashValue, lg.HASH_MASK_NEW, "keyHash");
    /*
    For 2-byte codeword, extract 32-bits of hashvalue
    hi 8 bits of both 16-bits are length part -> discarded
    Hence HASH_MASK_NEW -> mask of FFFFFFFF, FFFFFFFFFFFF, FFFFFFFFFFFFFFFF for LG {0,1,2}, 3, 4 respectively.
    */
    // Build up a single encoded value for table lookup from the hashcode sequence.
    Value * codewordVal = b->CreateAnd(hashValue, lg.LAST_SUFFIX_MASK);
    Value * codewordVal_H2 = b->CreateAnd(b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", keyMarkPos_H2)), sizeTy), lg.LAST_SUFFIX_MASK);
    // codewordVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(codewordVal, sz_ONE), b->CreateShl(codewordVal, sz_ONE)),
    //                               codewordVal);
    Value * hashcodePos = keyMarkPos;
    Value * hashcodePos_H2 = keyMarkPos_H2;
    #ifdef PRINT_DICT_ONLY
    Value * writtenVal = b->CreateAdd(lg.LAST_SUFFIX_BASE, b->CreateAnd(hashValue, lg.LAST_SUFFIX_MASK));;
    #endif
    b->CreateCondBr(b->CreateICmpUGT(mGroupNoVal, sz_ZERO), calcSuffixMask, calcPfxMask);

    b->SetInsertPoint(calcSuffixMask);
    Value * hcReadPos = b->CreateSub(hashcodePos, sz_ONE);
    Value * hcReadPos_H2 = b->CreateSub(hashcodePos_H2, sz_ONE);
    Value * secondLastSuffix = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", hcReadPos)), sizeTy);
    Value * secondLastSuffix_H2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", hcReadPos_H2)), sizeTy);
    Value * cwVal = b->CreateShl(codewordVal, lg.SEC_LAST_SFX);
    Value * cwVal_H2 = b->CreateShl(codewordVal_H2, lg.SEC_LAST_SFX);
    cwVal = b->CreateOr(cwVal, b->CreateAnd(secondLastSuffix, lg.SEC_LAST_SUFFIX_MASK));
    cwVal_H2 = b->CreateOr(cwVal_H2, b->CreateAnd(secondLastSuffix_H2, lg.SEC_LAST_SUFFIX_MASK));
    #ifdef PRINT_DICT_ONLY
    writtenVal = b->CreateOr(b->CreateShl(writtenVal, lg.SEC_LAST_SFX), b->CreateAnd(secondLastSuffix, lg.SEC_LAST_SUFFIX_MASK));
    #endif
    b->CreateBr(calcPfxMask);

    b->SetInsertPoint(calcPfxMask);
    PHINode * hcPos = b->CreatePHI(sizeTy, 2);
    hcPos->addIncoming(hcReadPos, calcSuffixMask);
    hcPos->addIncoming(keyMarkPos, processKey);
    PHINode * hcPos_H2 = b->CreatePHI(sizeTy, 2);
    hcPos_H2->addIncoming(hcReadPos_H2, calcSuffixMask);
    hcPos_H2->addIncoming(keyMarkPos_H2, processKey);
    PHINode * cwValPhi = b->CreatePHI(sizeTy, 2, "cwValPhi");
    cwValPhi->addIncoming(cwVal, calcSuffixMask);
    cwValPhi->addIncoming(codewordVal, processKey);
    PHINode * cwValPhi_H2 = b->CreatePHI(sizeTy, 2, "cwValPhi_H2");
    cwValPhi_H2->addIncoming(cwVal_H2, calcSuffixMask);
    cwValPhi_H2->addIncoming(codewordVal_H2, processKey);
    Value * codewordValFin = cwValPhi;
    Value * codewordValFin_H2 = cwValPhi_H2;
    // add PREFIX_LENGTH_MASK bits for larger index space
    Value * byteReadPos = b->CreateSub(hcPos, sz_ONE);
    Value * byteReadPos_H2 = b->CreateSub(hcPos_H2, sz_ONE);
    Value * pfxByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", byteReadPos)), sizeTy);
    Value * pfxByte_H2 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", byteReadPos_H2)), sizeTy);

    pfxByte = b->CreateTrunc(b->CreateAnd(pfxByte, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    pfxByte_H2 = b->CreateTrunc(b->CreateAnd(pfxByte_H2, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    #ifdef PRINT_DICT_ONLY
    Value * extBit = b->CreateLShr(hashExtBit, b->getSize(7));
    pfxByte = b->CreateSelect(b->CreateICmpEQ(b->CreateAnd(extBit, sz_ONE), sz_ONE),
                                  b->CreateOr(pfxByte, sz_ONE),
                                  b->CreateAnd(pfxByte, b->getSize(0x6)));
    pfxByte = b->CreateTrunc(pfxByte, b->getInt64Ty());
    Value * lgthBase1 = b->CreateSub(keyLength, lg.LO);
    Value * pfxOffset1 = b->CreateAdd(lg.PREFIX_BASE, lgthBase1);
    Value * multiplier1 = b->CreateMul(lg.RANGE, pfxByte);
    Value * ZTF_prefix1 = b->CreateAdd(pfxOffset1, multiplier1);
    #endif
    codewordValFin = b->CreateOr(b->CreateAnd(pfxByte, lg.EXTRA_BITS_MASK), b->CreateShl(codewordValFin, lg.EXTRA_BITS));
    codewordValFin_H2 = b->CreateOr(b->CreateAnd(pfxByte_H2, lg.EXTRA_BITS_MASK), b->CreateShl(codewordValFin_H2, lg.EXTRA_BITS));
    Value * tableIdxHash = b->CreateAnd(codewordValFin, lg.TABLE_MASK, "tableIdx");
    Value * tableIdxHash_H2 = b->CreateAnd(codewordValFin_H2, lg.TABLE_MASK, "tableIdxH2");
    Value * keyIdxPtr_H2 = b->CreateGEP(subTablePtr, b->CreateMul(tableIdxHash_H2, keyLength));
    Value * tblEntryPtr_H2 = b->CreateInBoundsGEP(keyIdxPtr_H2, sz_ZERO);
    Value * tblPtr1_H2 = b->CreateBitCast(tblEntryPtr_H2, lg.halfSymPtrTy);
    Value * tblPtr2_H2 = b->CreateBitCast(b->CreateGEP(tblEntryPtr_H2, keyOffset), lg.halfSymPtrTy);
    Value * entry1_H2 = b->CreateMonitoredScalarFieldLoad("hashTable", tblPtr1_H2);
    Value * entry2_H2 = b->CreateMonitoredScalarFieldLoad("hashTable", tblPtr2_H2);
#endif
    Value * codewordValFin = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("allHashValuesFinal", b->CreateSub(keyMarkPos, sz_ONE))), sizeTy);
    Value * subTablePtr = b->CreateGEP(hashTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    Value * tableIdxHash = b->CreateAnd(codewordValFin, lg.TABLE_MASK, "tableIdx");
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
    Value * lastSeenSubTablePtr = b->CreateGEP(lastSeenTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.FREQ_SUBTABLE_SIZE));
    Value * lastSeenSymIdxPtr = b->CreateGEP(lastSeenSubTablePtr, tableIdxHash);
    Value * lastSeenSymTblEntryPtr = b->CreateBitCast(lastSeenSymIdxPtr, sizeTy->getPointerTo());
/*
    All the marked symMarks indicate hashMarks for only repeated phrases.
    Among those marks,
    1. If any symbol is being seen for the first time and has no hash table entry, store that hashcode in the hashtable
    and mark its compression mask.
    2. If the hashcode exists in the hashtable but the current phrase and hash table entry do not match, go to next symbol.
*/
    Value * symIsEqEntry = b->CreateAnd(b->CreateICmpEQ(entry1, sym1), b->CreateICmpEQ(entry2, sym2));
#ifdef USE_CUCKOO_HASHING
    Value * symIsEqEntry_H2 = b->CreateAnd(b->CreateICmpEQ(entry1_H2, sym1), b->CreateICmpEQ(entry2_H2, sym2));
    symIsEqEntry = b->CreateOr(symIsEqEntry, symIsEqEntry_H2);
    Value * sfxReadPos = b->CreateSelect(symIsEqEntry_H2, keyMarkPos_H2, keyMarkPos);
#endif
    b->CreateCondBr(symIsEqEntry, tryCompression, storeKey);

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
#ifdef USE_CUCKOO_HASHING
    Value * secHashMarkBase = b->CreateSub(keyMarkPos, b->CreateURem(keyMarkPos, b->getSize(8)));
    Value * const secHashBasePtr = b->CreateBitCast(b->getRawInputPointer("secHashMark", secHashMarkBase), sizeTy->getPointerTo());
    Value * secHashOffset = b->CreateSub(keyMarkPos, secHashMarkBase);
    Value * secHashInitMark = b->CreateAlignedLoad(secHashBasePtr, 1);
    Value * isSecHash = b->CreateAnd(secHashInitMark, b->CreateShl(sz_ONE, secHashOffset));
    b->CreateCondBr(b->CreateICmpUGT(isSecHash, sz_ZERO), storeInSecHash, storeInFirstHash);

    b->SetInsertPoint(storeInSecHash);
    b->CreateMonitoredScalarFieldStore("hashTable", sym1, tblPtr1_H2);
    b->CreateMonitoredScalarFieldStore("hashTable", sym2, tblPtr2_H2);
    b->CreateBr(markCompression);

    b->SetInsertPoint(storeInFirstHash);
#endif
    // We have a new symbol that allows future occurrences of the symbol to
    // be compressed using the hash code.
    b->CreateMonitoredScalarFieldStore("hashTable", sym1, tblPtr1);
    b->CreateMonitoredScalarFieldStore("hashTable", sym2, tblPtr2);
    b->CreateMonitoredScalarFieldStore("lastSeenSeg", b->getScalarField("segIndex"), lastSeenSymTblEntryPtr);
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
    b->CreateBr(tryCompression);

    b->SetInsertPoint(tryCompression);
    Value * symLastSeenSeg  = b->CreateMonitoredScalarFieldLoad("lastSeenSeg", lastSeenSymTblEntryPtr);
    // if table entry belongs to segment (i-1) and sym is in segment i, do not compress the first occurrence of sym in segment i.
    // update the table entry's last seen to segment i; compress all the subsequent matches with the table entry in segment i.
    // Simplifies tracking any dictionary entry's usage in a segment without requiring the repeated dictionary entry.
    b->CreateCondBr(b->CreateAnd(symIsEqEntry, b->CreateICmpNE(symLastSeenSeg, b->getScalarField("segIndex"))), updateLastSeen, markCompression);

    b->SetInsertPoint(updateLastSeen);
    if (GetSegWiseDict()) {
        // Mark the last byte of phrase -> subtract 1 from keyMarkPos for safe markPos calculation
        Value * phraseEndPosNewEntry = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE), sz_ZERO, sz_ONE);
        Value * phraseMarkBaseNewEntry = b->CreateSub(b->CreateSub(keyMarkPos, phraseEndPosNewEntry), b->CreateURem(b->CreateSub(keyMarkPos, phraseEndPosNewEntry), sz_BITS));
        Value * markOffsetNewEntry = b->CreateSub(b->CreateSub(keyMarkPos, phraseEndPosNewEntry), phraseMarkBaseNewEntry);
        Value * const codewordMaskBasePtrNewEntry = b->CreateBitCast(b->getRawOutputPointer("codewordMask", phraseMarkBaseNewEntry), sizeTy->getPointerTo());
        Value * initialMarkNewEntry = b->CreateAlignedLoad(codewordMaskBasePtrNewEntry, 1);
        Value * updatedMaskNewEntry = b->CreateOr(initialMarkNewEntry, b->CreateShl(sz_ONE, markOffsetNewEntry));
        b->CreateAlignedStore(updatedMaskNewEntry, codewordMaskBasePtrNewEntry, 1);
    }
    b->CreateMonitoredScalarFieldStore("lastSeenSeg", b->getScalarField("segIndex"), lastSeenSymTblEntryPtr);
    b->CreateBr(nextKey); // 1. do not compress the first occurrence of sym in segment i.
    // b->CreateBr(markCompression);

    b->SetInsertPoint(markCompression);
#ifdef USE_CUCKOO_HASHING
    PHINode * const readPosPhi = b->CreatePHI(sizeTy, 3);
    readPosPhi->addIncoming(keyMarkPos_H2, storeInSecHash);
    readPosPhi->addIncoming(keyMarkPos, storeInFirstHash);
    readPosPhi->addIncoming(sfxReadPos, calcPfxMask);
#endif

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

    Value * writePos = keyMarkPos;

#ifdef USE_CUCKOO_HASHING
    Value * readPos = keyMarkPos;
    readPos = readPosPhi;
    Value * curHash = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", readPos)), sizeTy);
    // Write the suffixes.
    Value * last_suffix = b->CreateTrunc(b->CreateAdd(lg.LAST_SUFFIX_BASE, b->CreateAnd(curHash, lg.LAST_SUFFIX_MASK, "ZTF_suffix_last")), b->getInt8Ty());
#if 0
    Value * last_suffix_i64 = b->CreateAdd(lg.LAST_SUFFIX_BASE, b->CreateAnd(curHash, lg.LAST_SUFFIX_MASK, "ZTF_suffix_last"));
#endif
    b->CreateStore(last_suffix, b->getRawOutputPointer("encodedBytes", writePos));
    readPos = b->CreateSub(readPos, sz_ONE);
    writePos = b->CreateSub(writePos, sz_ONE);
    b->CreateCondBr(b->CreateICmpUGT(mGroupNoVal, sz_ZERO), writeSecLastSfx, writePfx);

    b->SetInsertPoint(writeSecLastSfx);
    Value * nextReadPos = readPos;
    Value * nextWritePos = writePos;
    Value * secLastSuffix = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", nextReadPos)), sizeTy);
#if 0
    Value * writtenVal = b->CreateOr(b->CreateShl(last_suffix_i64, lg.MAX_HASH_BITS), b->CreateAdd(lg.SEC_LAST_SUFFIX_BASE, 
                                                                                               b->CreateAnd(secLastSuffix, lg.SEC_LAST_SUFFIX_MASK, "ZTF_suffix_last")));
#endif
    secLastSuffix = b->CreateTrunc(b->CreateAdd(lg.SEC_LAST_SUFFIX_BASE, b->CreateAnd(secLastSuffix, lg.SEC_LAST_SUFFIX_MASK, "ZTF_sec_last_suffix")), b->getInt8Ty());
    b->CreateStore(secLastSuffix, b->getRawOutputPointer("encodedBytes", nextWritePos));
    nextReadPos = b->CreateSub(nextReadPos, sz_ONE);
    nextWritePos = b->CreateSub(nextWritePos, sz_ONE);

    for (unsigned j = 1; j < lg.groupInfo.encoding_bytes - 2; j++) {
        Value * suffixByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", nextReadPos)), sizeTy);
#if 0
        writtenVal = b->CreateOr(b->CreateShl(writtenVal, lg.MAX_HASH_BITS), b->CreateAnd(suffixByte, lg.SUFFIX_MASK));
#endif
        b->CreateStore(b->CreateTrunc(b->CreateAnd(suffixByte, lg.SUFFIX_MASK), b->getInt8Ty()), b->getRawOutputPointer("encodedBytes", nextWritePos));
        nextReadPos = b->CreateSub(nextReadPos, sz_ONE);
        nextWritePos = b->CreateSub(nextWritePos, sz_ONE);
    }
    b->CreateBr(writePfx);

    b->SetInsertPoint(writePfx);
    PHINode * pfxReadPos = b->CreatePHI(sizeTy, 2);
    pfxReadPos->addIncoming(nextReadPos, writeSecLastSfx);
    pfxReadPos->addIncoming(readPos, markCompression);
    PHINode * pfxWritePos = b->CreatePHI(sizeTy, 2);
    pfxWritePos->addIncoming(nextWritePos, writeSecLastSfx);
    pfxWritePos->addIncoming(writePos, markCompression);
#if 0
    PHINode * writtenValPhi = b->CreatePHI(sizeTy, 2);
    writtenValPhi->addIncoming(last_suffix_i64, markCompression);
    writtenValPhi->addIncoming(writtenVal, writeSecLastSfx);
#endif
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
            2      0-2             2               11          4
            3      0               1                1          8
            4      0-15            0                0         16
            (PFX_BASE + RANGE) + (numRows * (keyHash AND hashMask))
    */
    Value * pfxLgthMask = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", pfxReadPos)), sizeTy);
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
    b->CreateStore(b->CreateTrunc(ZTF_prefix, b->getInt8Ty()), b->getRawOutputPointer("encodedBytes", pfxWritePos));
#if 0
    Value * writtenValFin = writtenValPhi;
    writtenValFin = b->CreateOr(b->CreateShl(writtenValFin, lg.MAX_HASH_BITS), ZTF_prefix);
    b->CreateCondBr(/*b->CreateICmpUGT(isSecHash, sz_ZERO)*/symIsEqEntry_H2, group1Codewords, nextKey);
    b->SetInsertPoint(group1Codewords);
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength);
    b->CallPrintInt("writtenValFin", writtenValFin);
    b->CallPrintInt("readPosPhi", readPosPhi);
    b->CallPrintInt("keyMarkPos", keyMarkPos);
    // b->CallPrintInt("isSecHash", isSecHash);
    b->CallPrintInt("symIsEqEntry_H2", symIsEqEntry_H2);
#endif
#endif

    Value * pfxBits = b->CreateAnd(codewordValFin, lg.PREFIX_LENGTH_MASK);
    Value * lgthBase = b->CreateSub(keyLength, lg.LO);
    Value * pfxOffset = b->CreateAdd(lg.PREFIX_BASE, lgthBase);
    Value * multiplier = b->CreateMul(lg.RANGE, pfxBits);
    Value * ZTF_prefix = b->CreateAdd(pfxOffset, multiplier, "ZTF_prefix");

    codewordValFin = b->CreateLShr(codewordValFin, lg.EXTRA_BITS);
    Value * sfx1 = b->CreateAnd(codewordValFin, lg.SUFFIX1_MASK);
    codewordValFin = b->CreateLShr(codewordValFin, lg.SUFFIX1_BITS);
    Value * sfx2 = b->CreateAnd(codewordValFin, lg.SUFFIX2_MASK);
    sfx2 = b->CreateSelect(b->CreateICmpEQ(mGroupNoVal, b->getSize(3)), b->CreateAdd(lg.SEC_LAST_SUFFIX_BASE, sfx2), b->CreateAdd(lg.LAST_SUFFIX_BASE, sfx2));
    codewordValFin = b->CreateLShr(codewordValFin, lg.SUFFIX2_BITS);
    Value * sfx3 = b->CreateAnd(codewordValFin, lg.SUFFIX3_MASK);

    Value * newSfx1 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", b->CreateSub(writePos, b->getSize(2)))), sizeTy);
    newSfx1 = b->CreateAnd(newSfx1, lg.SUFFIX_MASK);
    sfx1 = b->CreateSelect(b->CreateICmpEQ(mGroupNoVal, b->getSize(3)), newSfx1, sfx1);
    b->CreateCondBr(b->CreateICmpEQ(mGroupNoVal, b->getSize(3)), writeSfx3, checkSfx2);

    b->SetInsertPoint(writeSfx3);
    b->CreateStore(b->CreateTrunc(b->CreateAdd(sfx3, lg.LAST_SUFFIX_BASE), b->getInt8Ty()), b->getRawOutputPointer("encodedBytes", writePos));
    Value * nextWritePos = b->CreateSub(writePos, sz_ONE);
    b->CreateBr(writeSfx2);

    b->SetInsertPoint(checkSfx2);
    b->CreateCondBr(b->CreateICmpUGT(mGroupNoVal, sz_ZERO), writeSfx2, writeSfx1);

    b->SetInsertPoint(writeSfx2);
    PHINode * sfx2WritePosPhi = b->CreatePHI(sizeTy, 2, "sfx2WritePosPhi");
    sfx2WritePosPhi->addIncoming(nextWritePos, writeSfx3);
    sfx2WritePosPhi->addIncoming(writePos, checkSfx2);
    // sfx2WritePosPhi->addIncoming(writePos, markCompression);
    Value * sfx2writePos = sfx2WritePosPhi;
    b->CreateStore(b->CreateTrunc(sfx2, b->getInt8Ty()), b->getRawOutputPointer("encodedBytes", sfx2writePos));
    Value * nextWritePos1 = b->CreateSub(sfx2writePos, sz_ONE);
    b->CreateBr(writeSfx1);

    b->SetInsertPoint(writeSfx1);
    PHINode * sfx1WritePosPhi = b->CreatePHI(sizeTy, 2, "sfx1WritePosPhi");
    sfx1WritePosPhi->addIncoming(nextWritePos1, writeSfx2);
    sfx1WritePosPhi->addIncoming(writePos, checkSfx2);
    Value * sfx1writePos = sfx1WritePosPhi;
    b->CreateStore(b->CreateTrunc(sfx1, b->getInt8Ty()), b->getRawOutputPointer("encodedBytes", sfx1writePos));
    sfx1writePos = b->CreateSub(sfx1writePos, sz_ONE);
    b->CreateStore(b->CreateTrunc(ZTF_prefix, b->getInt8Ty()), b->getRawOutputPointer("encodedBytes", sfx1writePos));
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
    b->setProcessedItemCount("secHashMark", processed);
    b->setProcessedItemCount("hashValues", processed);
    b->setProcessedItemCount("allHashValuesFinal", processed);
    b->setProcessedItemCount("lfPos", b->getScalarField("segIndex"));
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
                                StreamSet * lfData,
                                StreamSet * byteData,
                                StreamSet * combinedMask,
                                StreamSet * cmpBytes,
                                StreamSet * partialSum,
                                unsigned strideBlocks)
: MultiBlockKernel(b, "FilterCompressedData" +  std::to_string(strideBlocks) + "_" + std::to_string(numSyms),
                   {Binding{"lfPos", lfData, GreedyRate(), Deferred()},
                    Binding{"phraseMask", combinedMask, FixedRate()},
                    Binding{"byteData", byteData, FixedRate()}},
                   {}, {}, {},{
                    InternalScalar{b->getSizeTy(), "segIndex"},
                    InternalScalar{b->getSizeTy(), "processBeforeThisPos"},
                   }),
mSubStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS)), mStrideSize(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS)) {
    mOutputStreamSets.emplace_back("cmpBytes", cmpBytes, BoundedRate(0, 1));
    mOutputStreamSets.emplace_back("partialSum", partialSum, BoundedRate(0, ceiling(ProcessingRate::Rational{1, 1048576})), Add1());
    setStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS));
}
void FilterCompressedData::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    ScanWordParameters sw(b, mStrideSize);
    Constant * sz_STRIDE = b->getSize(mStrideSize);
    Constant * sz_BLOCKS_PER_STRIDE = b->getSize(mStrideSize/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Type * sizeTy = b->getSizeTy();

    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const stridePrologue = b->CreateBasicBlock("stridePrologue");
    BasicBlock * const strideMasksReady = b->CreateBasicBlock("strideMasksReady");
    BasicBlock * const filteringLoop = b->CreateBasicBlock("filteringLoop");
    BasicBlock * const updateScalars = b->CreateBasicBlock("updateScalars");
    BasicBlock * const checkWriteOutput = b->CreateBasicBlock("checkWriteOutput");
    BasicBlock * const writeOutput = b->CreateBasicBlock("writeOutput");
    BasicBlock * const stridePhrasesDone = b->CreateBasicBlock("stridePhrasesDone");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const updatePending = b->CreateBasicBlock("updatePending");
    BasicBlock * const filteringMaskDone = b->CreateBasicBlock("filteringMaskDone");
    BasicBlock * const processPhrase = b->CreateBasicBlock("processPhrase");

    Value * const initialPos = b->getProcessedItemCount("phraseMask");
    Value * const initialProducedBytes = b->getProducedItemCount("cmpBytes");
    // b->CallPrintInt("initialProducedBytes", initialProducedBytes);
    b->CreateBr(stridePrologue);

    b->SetInsertPoint(stridePrologue);
    PHINode * const strideNo = b->CreatePHI(sizeTy, 2);
    strideNo->addIncoming(sz_ZERO, entryBlock);
    PHINode * const segWritePosPhi = b->CreatePHI(sizeTy, 2);
    segWritePosPhi->addIncoming(initialProducedBytes, entryBlock);
    Value * nextStrideNo = b->CreateAdd(strideNo, sz_ONE);
    Value * stridePos = b->CreateAdd(initialPos, b->CreateMul(strideNo, sz_STRIDE));
    Value * strideBlockOffset = b->CreateMul(strideNo, sz_BLOCKS_PER_STRIDE);
    std::vector<Value *> phraseMasks = initializeCompressionMasks1(b, sw, sz_BLOCKS_PER_STRIDE, 1, strideBlockOffset, strideMasksReady);
    Value * phraseMask = phraseMasks[0];

    b->SetInsertPoint(strideMasksReady);
    Value * phraseWordBasePtr = b->getInputStreamBlockPtr("phraseMask", sz_ZERO, strideBlockOffset);
    phraseWordBasePtr = b->CreateBitCast(phraseWordBasePtr, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(phraseMask, sz_ZERO), stridePhrasesDone, filteringLoop);

    b->SetInsertPoint(filteringLoop);
    PHINode * const phraseMaskPhi = b->CreatePHI(sizeTy, 2);
    phraseMaskPhi->addIncoming(phraseMask, strideMasksReady);
    PHINode * const phraseWordPhi = b->CreatePHI(sizeTy, 2);
    phraseWordPhi->addIncoming(sz_ZERO, strideMasksReady);
    PHINode * const writePosPhi = b->CreatePHI(sizeTy, 2);
    writePosPhi->addIncoming(segWritePosPhi, strideMasksReady);
    Value * phraseWordIdx = b->CreateCountForwardZeroes(phraseMaskPhi, "symIdx");
    Value * nextphraseWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(phraseWordBasePtr, phraseWordIdx)), sizeTy);
    Value * thephraseWord = b->CreateSelect(b->CreateICmpEQ(phraseWordPhi, sz_ZERO), nextphraseWord, phraseWordPhi);
    Value * phraseWordPos = b->CreateAdd(stridePos, b->CreateMul(phraseWordIdx, sw.WIDTH));
    Value * phraseMarkPosInWord = b->CreateCountForwardZeroes(thephraseWord);
    Value * phraseMarkPos = b->CreateAdd(phraseWordPos, phraseMarkPosInWord);

    Value * const processBeforeThisPos = b->getScalarField("processBeforeThisPos");
    // if phraseMarkPos is exceeding processBeforeThisPos, update processBeforeThisPos
    // also write the partial sum in output stream
    Value * checkPhrasePos = b->CreateICmpUGE(phraseMarkPos, processBeforeThisPos);
    b->CreateCondBr(checkPhrasePos, checkWriteOutput, processPhrase);

    b->SetInsertPoint(checkWriteOutput);  
    // b->CallPrintInt("processBeforeThisPos", processBeforeThisPos);
    // b->CallPrintInt("phraseMarkPos", phraseMarkPos);
    b->CreateCondBr(b->CreateICmpUGT(processBeforeThisPos, sz_ZERO), writeOutput, updateScalars);

    b->SetInsertPoint(writeOutput); 
    Value * const segProcessed = b->getScalarField("segIndex");

    // b->CallPrintInt("segProcessed", segProcessed);
    // b->CallPrintInt("writePosPhi", b->CreateSub(writePosPhi, sz_ONE));

    b->CreateStore(b->CreateTrunc(b->CreateSub(writePosPhi, sz_ONE), b->getInt64Ty()), b->getRawOutputPointer("partialSum", segProcessed));
    b->setScalarField("segIndex", b->CreateAdd(sz_ONE, segProcessed));
    b->CreateBr(updateScalars);

    b->SetInsertPoint(updateScalars);
    Value * const curIdx = b->getScalarField("segIndex");
    Value * lfPosPtr = b->CreateBitCast(b->getRawInputPointer("lfPos", curIdx), b->getSizeTy()->getPointerTo());
    Value * lfPos = b->CreateAlignedLoad(lfPosPtr, 1);
    // b->CallPrintInt("curIdx", curIdx);
    // b->CallPrintInt("lfPos", lfPos);
    b->setScalarField("processBeforeThisPos", b->CreateAdd(sz_ONE, lfPos));
    b->CreateBr(processPhrase);

    b->SetInsertPoint(processPhrase);
    // b->CallPrintInt("writePosPhi", writePosPhi);
    b->CreateMemCpy(b->getRawOutputPointer("cmpBytes", writePosPhi), b->getRawInputPointer("byteData", phraseMarkPos), sz_ONE, 1);
    
    // Value * symPtr = b->CreateBitCast(b->getRawInputPointer("byteData", phraseMarkPos), b->getInt8PtrTy());
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr, b->CreateAdd(sz_ZERO, sz_ONE));
    Value * const nextWritePos = b->CreateAdd(writePosPhi, sz_ONE, "nextWritePos");
    Value * dropPhrase = b->CreateResetLowestBit(thephraseWord);
    Value * thisWordDone = b->CreateICmpEQ(dropPhrase, sz_ZERO);
    // There may be more phrases in the phrase mask.
    Value * nextphraseMask = b->CreateSelect(thisWordDone, b->CreateResetLowestBit(phraseMaskPhi), phraseMaskPhi);
    BasicBlock * currentBB = b->GetInsertBlock();
    phraseMaskPhi->addIncoming(nextphraseMask, currentBB);
    phraseWordPhi->addIncoming(dropPhrase, currentBB);
    writePosPhi->addIncoming(nextWritePos, currentBB);
    b->CreateCondBr(b->CreateICmpNE(nextphraseMask, sz_ZERO), filteringLoop, stridePhrasesDone);

    b->SetInsertPoint(stridePhrasesDone);
    PHINode * const nextWritePosPhi = b->CreatePHI(sizeTy, 2, "nextWritePosPhi");
    nextWritePosPhi->addIncoming(segWritePosPhi, strideMasksReady);
    nextWritePosPhi->addIncoming(nextWritePos, processPhrase);

    strideNo->addIncoming(nextStrideNo, stridePhrasesDone);
    segWritePosPhi->addIncoming(nextWritePosPhi, stridePhrasesDone);
    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), stridePrologue, stridesDone);
    b->SetInsertPoint(stridesDone);
    b->setProducedItemCount("partialSum", b->getScalarField("segIndex"));
    // b->CallPrintInt("nextWritePosPhi-produced", nextWritePosPhi);
    b->setProducedItemCount("cmpBytes", nextWritePosPhi);
    b->CreateCondBr(b->isFinal(), updatePending, filteringMaskDone);

    b->SetInsertPoint(updatePending);
    // b->CallPrintInt("segIndex-updatePending", b->getScalarField("segIndex"));
    // b->CallPrintInt("nextWritePosPhi-updatePending", nextWritePosPhi);
    b->CreateStore(b->CreateTrunc(/*b->CreateSub(*/nextWritePosPhi,/* sz_ONE),*/ b->getInt64Ty()), b->getRawOutputPointer("partialSum", b->getScalarField("segIndex")));
    b->setScalarField("segIndex", b->CreateAdd(sz_ONE, b->getScalarField("segIndex")));
    // b->CallPrintInt("partialSum-produced-updatePending", b->getScalarField("segIndex"));
    b->setProducedItemCount("partialSum", b->getScalarField("segIndex"));
    b->CreateBr(filteringMaskDone);

    b->SetInsertPoint(filteringMaskDone);
    // update processed count for lfPos
    // b->CallPrintInt("segIndex-filteringMaskDone", b->getScalarField("segIndex"));
    b->setProcessedItemCount("lfPos", b->getScalarField("segIndex"));
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
                   {Binding{"lfPos", lfData, GreedyRate(), Deferred()},
                    Binding{"phraseMask", phraseMask, FixedRate(), Deferred()},
                    Binding{"byteData", byteData, FixedRate(), Deferred()},
                    Binding{"codedBytes", codedBytes, FixedRate(), Deferred()},
                    Binding{"lengthData", allLenHashValues, FixedRate(), Deferred()}},
                   {}, {}, {}, {
                    InternalScalar{b->getSizeTy(), "segIndex"},
                    InternalScalar{b->getSizeTy(), "absBlocksProcessed"},
                    InternalScalar{b->getSizeTy(), "lastLfPos"},
                   }),
mEncodingScheme(encodingScheme), mNumSym(numSyms), mSubStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS)), mStrideSize(1048576) {
    mOutputStreamSets.emplace_back("dictionaryBytes", dictionaryBytes, BoundedRate(0, 1));
    mOutputStreamSets.emplace_back("dictPartialSum", dictPartialSum, BoundedRate(0, ceiling(ProcessingRate::Rational{1, 1048576})), Add1());
    addInternalScalar(ArrayType::get(b->getInt8Ty(), encodingScheme.maxSymbolLength()), "pendingPhrase");
    addInternalScalar(ArrayType::get(b->getInt8Ty(), encodingScheme.maxEncodingBytes()), "pendingCodeword");
    addInternalScalar(b->getInt8Ty(), "pendingPhraseLen");
    addInternalScalar(b->getInt8Ty(), "pendingCodewordLen");
    setStride(1048576);
}

void WriteDictionary::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    // b->CallPrintInt("numOfStrides-dict", numOfStrides);
    ScanWordParameters sw(b, mStrideSize);
    Constant * sz_STRIDE = b->getSize(mStrideSize);
    Constant * sz_SUB_STRIDE = b->getSize(mSubStride);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    Constant * sz_BLOCKS_PER_SUB_STRIDE = b->getSize(mSubStride/b->getBitBlockWidth());
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_TWO = b->getSize(2);
    Constant * sz_SYM_MASK = b->getSize(0x1F);
    Constant * sz_HASH_TABLE_START = b->getSize(65278);
    Constant * sz_HASH_TABLE_END = b->getSize(65535);
    assert ((mStrideSize % mSubStride) == 0);
    Value * totalSubStrides =  b->getSize(mStrideSize / mSubStride); // 102400/2048 with BitBlock=256
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
    BasicBlock * const strideMasksReady = b->CreateBasicBlock("strideMasksReady");
    BasicBlock * const dictProcessingLoop = b->CreateBasicBlock("dictProcessingLoop");
    BasicBlock * const writePhrase = b->CreateBasicBlock("writePhrase");
    BasicBlock * const writeSegPhrase = b->CreateBasicBlock("writeSegPhrase");
    BasicBlock * const phraseWritten = b->CreateBasicBlock("phraseWritten");
    BasicBlock * const writeCodeword = b->CreateBasicBlock("writeCodeword");
    BasicBlock * const codewordWritten = b->CreateBasicBlock("codewordWritten");
    BasicBlock * const nextPhrase = b->CreateBasicBlock("nextPhrase");
    BasicBlock * const checkWriteHTEnd = b->CreateBasicBlock("checkWriteHTEnd");
    BasicBlock * const writeHTEnd = b->CreateBasicBlock("writeHTEnd");
    BasicBlock * const subStridePhrasesDone = b->CreateBasicBlock("subStridePhrasesDone");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
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
    Value * const avail = b->getAvailableItemCount("phraseMask");
    Value * const initialProducedBytes = b->getProducedItemCount("dictionaryBytes");
    Value * const processedBlocks = b->getScalarField("absBlocksProcessed");
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
    b->setScalarField("lastLfPos", lfPos);
    // b->CallPrintInt("strideNo-writeDict", strideNo);
    b->CreateBr(subStrideMaskPrep);

    b->SetInsertPoint(subStrideMaskPrep);
    PHINode * const subStrideNo = b->CreatePHI(sizeTy, 2);
    subStrideNo->addIncoming(sz_ZERO, stridePrologue);
    // starts from 1MB boundary for every 1MB stride - starts where the prev segment dictionary ended
    PHINode * const writePosPhi = b->CreatePHI(sizeTy, 2);
    writePosPhi->addIncoming(segWritePosPhi, stridePrologue);
    // b->CallPrintInt("writePosPhi", writePosPhi);
    // b->CallPrintInt("subStrideNo", subStrideNo);
    Value * nextSubStrideNo = b->CreateAdd(subStrideNo, sz_ONE);
    Value * subStridePos = b->CreateAdd(stridePos, b->CreateMul(subStrideNo, sz_SUB_STRIDE));
    // b->CallPrintInt("subStridePos", subStridePos);
    Value * readSubStrideBlockOffset = b->CreateAdd(strideBlockOffset,
                                                b->CreateMul(subStrideNo, sz_BLOCKS_PER_SUB_STRIDE));
    // b->CallPrintInt("readSubStrideBlockOffset", readSubStrideBlockOffset);
    std::vector<Value *> phraseMasks = initializeCompressionMasks11(b, sw, sz_BLOCKS_PER_SUB_STRIDE, 1, readSubStrideBlockOffset, strideMasksReady);
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
    Value * symMarkPosShiftNeeded = b->CreateICmpULT(numSymInPhrase, b->getSize(2));
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
    cwLenInit = b->CreateSelect(b->CreateICmpUGT(phraseLengthFinal, b->getSize(4)), b->CreateAdd(cwLenInit, sz_ONE), cwLenInit);
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
    b->CreateCondBr(b->CreateAnd(checkStartBoundary, b->CreateICmpNE(nextLoopIdx, maxLoopIdx)), writeHTStart, writeSegPhrase);


    b->SetInsertPoint(writeSegPhrase);
    // If not first phrase of the segment
    // Write phrase followed by codeword
    PHINode * const segWritePos = b->CreatePHI(sizeTy, 2);
    PHINode * const segLoopIdx = b->CreatePHI(sizeTy, 2);
    segWritePos->addIncoming(subStrideWritePos, firstCodewordDone);
    segLoopIdx->addIncoming(sz_ZERO, firstCodewordDone);

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

    Value * const startBoundaryLen = b->CreateSelect(checkStartBoundary, sz_TWO, sz_ZERO);
    Value * const nextWritePosition = b->CreateAdd(subStrideWritePos, b->CreateAdd(startBoundaryLen,
                                 b->CreateAdd(codeWordLen, phraseLengthFinal)), "nextWritePosition");
    b->CreateCondBr(b->CreateICmpNE(nextSegLoopIdx, b->getSize(2)), writeSegPhrase, nextPhrase);


    b->SetInsertPoint(nextPhrase);
    PHINode * const nextWritePos = b->CreatePHI(sizeTy, 3);
    nextWritePos->addIncoming(nextWritePosition, codewordWritten);
    nextWritePos->addIncoming(subStrideWritePos, dictProcessingLoop);
    nextWritePos->addIncoming(subStrideWritePos, storeInPending);

    Value * dropPhrase = b->CreateResetLowestBit(thephraseWord);
    Value * thisWordDone = b->CreateICmpEQ(dropPhrase, sz_ZERO);
    // There may be more phrases in the phrase mask.
    Value * nextphraseMask = b->CreateSelect(thisWordDone, b->CreateResetLowestBit(phraseMaskPhi), phraseMaskPhi);
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
    b->setScalarField("absBlocksProcessed", b->CreateUDiv(lfPos, sz_BLOCKWIDTH));
    Value * segWritePosUpdate = b->CreateSelect(b->CreateICmpEQ(nextSubStrideWritePos, segWritePosPhi), nextSubStrideWritePos, b->CreateAdd(nextSubStrideWritePos, sz_TWO), "segWritePosUpdate");

    // Value * producedBase = b->CreateSub(segWritePosUpdate, b->CreateURem(segWritePosUpdate, sz_BLOCK_SIZE));
    // Value * producedBitOffset = b->CreateSub(segWritePosUpdate, producedBase);
    // Value * nextAlignedOffset = b->CreateSub(sz_BLOCK_SIZE, producedBitOffset);
    // Value * producedByteOffset = b->CreateSelect(b->CreateICmpEQ(producedBitOffset, sz_ZERO), producedBitOffset, nextAlignedOffset);
    // Value * const producedCurSegment = b->CreateAdd(segWritePosUpdate, producedByteOffset);

    segWritePosPhi->addIncoming(segWritePosUpdate, checkFinalLoopCond);
    // b->CallPrintInt("nextSubStrideWritePos", nextSubStrideWritePos);
    // b->CallPrintInt("producedByteOffset", producedByteOffset);

    // Write the produced dictionary count to integer-stream
    Value * const segProcessed = b->getScalarField("segIndex");
    b->setScalarField("segIndex", b->CreateAdd(sz_ONE, b->getScalarField("segIndex")));
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
    b->setProducedItemCount("dictPartialSum", b->getScalarField("segIndex"));
    Value * producedBlocks = b->CreateUDiv(lfPos, sz_BLOCKWIDTH);
    Value * processed = b->CreateSelect(b->isFinal(), avail, b->CreateMul(producedBlocks, sz_BLOCKWIDTH));
    b->setProcessedItemCount("phraseMask", processed);
    b->setProcessedItemCount("byteData", processed);
    b->setProcessedItemCount("codedBytes", processed);
    b->setProcessedItemCount("lengthData", processed);
    // NOTE: does not require to write the last segment's dicitonary end
}

InterleaveCompressionSegment::InterleaveCompressionSegment(BuilderRef b,
                                    StreamSet * dictData,
                                    StreamSet * codedBytes,
                                    StreamSet * dictPartialSum,
                                    StreamSet * cmpPartialSum,
                                    unsigned strideBlocks)
: MultiBlockKernel(b, "InterleaveCompressionSegment" + std::to_string(strideBlocks) + "_" + std::to_string(dictPartialSum->getNumElements()) + "_" + std::to_string(cmpPartialSum->getNumElements()),
                   {Binding{"dictPartialSum", dictPartialSum, FixedRate(1)},
                    Binding{"cmpPartialSum", cmpPartialSum, FixedRate(1)},
                    Binding{"dictData", dictData, GreedyRate(1048576), Deferred() /*PartialSum("dictPartialSum")*/}, // partialSun requires countable produced items
                    Binding{"codedBytes", codedBytes, GreedyRate(1048576), Deferred() /*PartialSum("cmpPartialSum")*/}},
                   {}, {}, {}, {
                    InternalScalar{b->getSizeTy(), "segIndex"},
                    InternalScalar{b->getSizeTy(), "lastSegDict"},
                    InternalScalar{b->getSizeTy(), "lastSegCmp"},
                   }) {
    setStride(1);
    addAttribute(SideEffecting());
    addAttribute(ExecuteStridesIndividually());
}

void InterleaveCompressionSegment::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {

    Constant * sz_ONE = b->getSize(1);
    Constant * sz_ZERO = b->getSize(0);
    Value * const dictAvail = b->getAccessibleItemCount("dictData");
    Value * const cmpAvail = b->getAccessibleItemCount("codedBytes");
    Value * const dictProcessed = b->getProcessedItemCount("dictData");
    Value * const cmpProcessed = b->getProcessedItemCount("codedBytes");

    // b->CallPrintInt("dictData-avail", b->getAvailableItemCount("dictData"));
    // b->CallPrintInt("codedBytes-avail", b->getAvailableItemCount("codedBytes"));

    Value * const curIdx = b->getScalarField("segIndex");
    Value * dictPosPtr = b->CreateBitCast(b->getRawInputPointer("dictPartialSum", curIdx), b->getSizeTy()->getPointerTo());
    Value * dictPos = b->CreateAlignedLoad(dictPosPtr, 1);
    Value * cmpPosPtr = b->CreateBitCast(b->getRawInputPointer("cmpPartialSum", curIdx), b->getSizeTy()->getPointerTo());
    Value * cmpPos = b->CreateAlignedLoad(cmpPosPtr, 1);
    Value * dictWrite = b->CreateSub(dictPos, b->getScalarField("lastSegDict"));
    Value * cmpWrite = b->CreateSub(cmpPos, b->getScalarField("lastSegCmp"));
    dictWrite = b->CreateSelect(b->isFinal(), b->CreateAdd(dictWrite, sz_ONE), dictWrite);
    cmpWrite = b->CreateSelect(b->isFinal(), b->CreateAdd(cmpWrite, sz_ONE), cmpWrite);

    dictWrite = b->CreateSelect(b->CreateICmpEQ(dictAvail, sz_ZERO), sz_ZERO, dictWrite);
    cmpWrite = b->CreateSelect(b->CreateICmpEQ(cmpAvail, sz_ZERO), sz_ZERO, cmpWrite);
    Constant * const stdOutFd = b->getInt32(STDOUT_FILENO);
    b->CreateWriteCall(stdOutFd, b->getRawInputPointer("dictData", dictProcessed), dictWrite); //dictAvail);
    b->CreateWriteCall(stdOutFd, b->getRawInputPointer("codedBytes", cmpProcessed), cmpWrite); //cmpAvail);
    
    b->setScalarField("lastSegDict", dictPos);
    b->setScalarField("lastSegCmp", cmpPos);
    b->setScalarField("segIndex", b->CreateAdd(sz_ONE, b->getScalarField("segIndex")));
    b->setProcessedItemCount("dictData", b->CreateSelect(b->isFinal(), dictAvail, dictPos));
    b->setProcessedItemCount("codedBytes", b->CreateSelect(b->isFinal(), cmpAvail, cmpPos));

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
                       Binding{"byteData", byteData, FixedRate(), LookBehind(encodingScheme.maxSymbolLength()+1)}
                   },
                   {}, {}, {},
                   {InternalScalar{ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), "pendingOutput"},
                    // Hash table 8 length-based tables with 256 16-byte entries each.
                    InternalScalar{ArrayType::get(ArrayType::get(ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), phraseHashSubTableSize(encodingScheme, groupNo, numSym)),
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

    Value * sz_HALF_TBL_IDX = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo, mNumSym) / 2);
    Value * sz_HALF_TBL_IDX_0 = b->getSize(phraseHashSubTableSize(mEncodingScheme, mGroupNo, mNumSym) / 3);
    Value * checkGroupNum = b->CreateICmpUGT(b->getSize(mGroupNo), sz_ZERO);
    sz_HALF_TBL_IDX = b->CreateSelect(checkGroupNum, sz_HALF_TBL_IDX, sz_HALF_TBL_IDX_0);
    checkGroupNum = b->CreateICmpEQ(b->getSize(mGroupNo), b->getSize(3));
    sz_HALF_TBL_IDX = b->CreateSelect(checkGroupNum, sz_ZERO, sz_HALF_TBL_IDX);
    Value * mGroupNoVal = b->getSize(mGroupNo);

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
    BasicBlock * const calcSecLastSuffixMask = b->CreateBasicBlock("calcSecLastSuffixMask");
    BasicBlock * const calcRemBits = b->CreateBasicBlock("calcRemBits");
    BasicBlock * const calcSecLastSuffixMask_1 = b->CreateBasicBlock("calcSecLastSuffixMask_1");
    BasicBlock * const calcRemBits_1 = b->CreateBasicBlock("calcRemBits_1");


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
    b->CreateCondBr(b->CreateICmpUGT(mGroupNoVal, sz_ZERO), calcSecLastSuffixMask, calcRemBits);

    b->SetInsertPoint(calcSecLastSuffixMask);
    hashcodePos = b->CreateSub(hashcodePos, sz_ONE);
    Value * symSecondLastSuffix = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("byteData", hashcodePos)), sizeTy);
#ifdef PRINT_DECOMPRESSION_DICT_INFO
    Value * cw_debug = b->CreateOr(b->CreateShl(codewordVal_debug, lg.MAX_HASH_BITS), symSecondLastSuffix);
#endif
    symSecondLastSuffix = b->CreateSelect(b->CreateICmpUGE(symSecondLastSuffix, b->getSize(0x80)), b->CreateSub(symSecondLastSuffix, b->getSize(0x80)), symSecondLastSuffix);
    Value * cwVal = b->CreateShl(codewordVal, lg.SEC_LAST_SFX);
    cwVal = b->CreateOr(cwVal, b->CreateAnd(symSecondLastSuffix, lg.SEC_LAST_SUFFIX_MASK));

    b->CreateBr(calcRemBits);

    b->SetInsertPoint(calcRemBits);
    PHINode * cwValPhi = b->CreatePHI(sizeTy, 2);
    cwValPhi->addIncoming(cwVal, calcSecLastSuffixMask);
    cwValPhi->addIncoming(codewordVal, keyProcessingLoop);
#ifdef PRINT_DECOMPRESSION_DICT_INFO
    PHINode * cwValDebugPhi = b->CreatePHI(sizeTy, 2);
    cwValDebugPhi->addIncoming(cw_debug, calcSecLastSuffixMask);
    cwValDebugPhi->addIncoming(codewordVal_debug, keyProcessingLoop);
#endif
    Value * codewordValFin = cwValPhi;
    // Value * pfxByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("byteData", hashcodePos)), sizeTy);
    Value * keylen_range = b->CreateSub(keyLength, lg.LO);
    Value * thePfxOffset = b->CreateAdd(lg.PREFIX_BASE, keylen_range);
    Value * theMultiplier = b->CreateSub(thePfx, thePfxOffset);
    Value * thePfxHashBits = b->CreateUDiv(theMultiplier, lg.RANGE);
    thePfxHashBits = b->CreateTrunc(thePfxHashBits, b->getInt64Ty());
    /// CHECK: Assertion for CreateUDiv(multiplier, lg.RANGE)

#if 0
    b->CallPrintInt("decmp-tableIdxHash", b->CreateAnd(codewordValFin, lg.TABLE_MASK));
#endif

    Value * subTablePtr = b->CreateGEP(hashTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    codewordValFin = b->CreateOr(b->CreateAnd(thePfxHashBits, lg.EXTRA_BITS_MASK), b->CreateShl(codewordValFin, lg.EXTRA_BITS));
    Value * tableIdxHash = b->CreateAnd(codewordValFin, lg.TABLE_MASK, "tableIdx");
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
    Value * cwValDebugFin = cwValDebugPhi;
    b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength);
    b->CallPrintInt("hashCode", b->CreateOr(b->CreateShl(cwValDebugFin, lg.MAX_HASH_BITS), thePfx));
    b->CallPrintInt("tableIdxHash", tableIdxHash);
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
    //b->CallPrintInt("lastSuffixByte", encodedVal);
    encodedVal = b->CreateSelect(b->CreateICmpUGE(encodedVal, b->getSize(0x80)), b->CreateSub(encodedVal, b->getSize(0x80)), encodedVal);
    // encodedVal = b->CreateSelect(b->CreateICmpEQ(b->getSize(mNumSym), sz_ONE),
    //                               b->CreateOr(b->CreateAnd(encodedVal, sz_ONE), b->CreateShl(encodedVal, sz_ONE)),
    //                               encodedVal);
    b->CreateCondBr(b->CreateICmpUGT(mGroupNoVal, sz_ZERO), calcSecLastSuffixMask_1, calcRemBits_1);

    b->SetInsertPoint(calcSecLastSuffixMask_1);
    Value * cPos = b->CreateSub(curPos, sz_ONE);
    Value * symSecondLastSuffix_1 = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("byteData", cPos)), sizeTy);
    symSecondLastSuffix_1 = b->CreateSelect(b->CreateICmpUGE(symSecondLastSuffix_1, b->getSize(0x80)), b->CreateSub(symSecondLastSuffix_1, b->getSize(0x80)), symSecondLastSuffix_1);
    Value * encVal = b->CreateShl(encodedVal, lg.SEC_LAST_SFX);
    encVal = b->CreateOr(encVal, b->CreateAnd(symSecondLastSuffix_1, lg.SEC_LAST_SUFFIX_MASK));

    b->CreateBr(calcRemBits_1);

    b->SetInsertPoint(calcRemBits_1);
    PHINode * encValPhi = b->CreatePHI(sizeTy, 2);
    encValPhi->addIncoming(encVal, calcSecLastSuffixMask_1);
    encValPhi->addIncoming(encodedVal, hashProcessingLoop);
    Value * encodedValFin = encValPhi;
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
#if 0
    Value * encodedVal_debug = encodedValFin;
    encodedVal_debug = b->CreateOr(b->CreateShl(encodedVal_debug, lg.MAX_HASH_BITS), hashPfx);
#endif
    Value * validLength = b->CreateAnd(b->CreateICmpUGE(symLength, lg.LO), b->CreateICmpULE(symLength, lg.HI));
    DEBUG_PRINT("symLength", symLength);
    b->CreateCondBr(validLength, lookupSym, nextHash);
    b->SetInsertPoint(lookupSym);
#if 0
    b->CallPrintInt("DhashVal-lookup", b->CreateAnd(encodedValFin, lg.TABLE_MASK));
#endif
    Value * symStartPos = b->CreateSub(hashMarkPos, b->CreateSub(symLength, sz_ONE), "symStartPos");
    Value * symOffset = b->CreateSub(symLength, lg.HALF_LENGTH);

    subTablePtr = b->CreateGEP(hashTableBasePtr, b->CreateMul(b->CreateSub(symLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    encodedValFin = b->CreateOr(b->CreateAnd(pfxHashBits, lg.EXTRA_BITS_MASK), b->CreateShl(encodedValFin, lg.EXTRA_BITS));
    tableIdxHash = b->CreateAnd(encodedValFin, lg.TABLE_MASK);
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
    // Value * const processedBytes = b->getProcessedItemCount("byteData");
    // Value * const availStarts = b->getAvailableItemCount("offsetStartData");
    // Value * const processedStarts = b->getProcessedItemCount("offsetStartData");
    // Value * const availEnds = b->getAvailableItemCount("offsetEndData");
    // Value * const processedEnds = b->getProcessedItemCount("offsetEndData");
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

    Value * const nextWritePosAfterDict = b->CreateAdd(segProduced, dictSize); //segProduced;
    // b->CallPrintInt("nextWritePosAfterDict", nextWritePosAfterDict);
    b->CreateBr(segmentsDone);

    b->SetInsertPoint(segmentsDone);
    PHINode * const strideProduced = b->CreatePHI(sizeTy, 3, "strideProduced");
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

FilterByMask_new::FilterByMask_new(BuilderRef b,
                                StreamSet * const mask,
                                StreamSet * const byteData,
                                StreamSet * const filtereData,
                                unsigned strideBlocks)
: MultiBlockKernel(b, "FilterByMask_new_" +  std::to_string(mask->getNumElements()) + "_" + std::to_string(byteData->getNumElements()),
                   {Binding{"mask", mask, FixedRate()},
                    Binding{"byteData", byteData, FixedRate()}},
                   {}, {}, {}, {}) {
    mOutputStreamSets.emplace_back("filtereData", filtereData, PopcountOf("mask"));
    setStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS));
    addInternalScalar(b->getSizeTy(), "lastKnownStart");
}
void FilterByMask_new::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
    Type * const sizeTy = b->getSizeTy();
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_STRIDE = b->getSize(mStride);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    Constant * sz_BLOCKS_PER_STRIDE = b->getSize(mStride/b->getBitBlockWidth());

    BasicBlock * const entry = b->GetInsertBlock();
    BasicBlock * const startSegment = b->CreateBasicBlock("startSegment");
    BasicBlock * const maskInit = b->CreateBasicBlock("maskInit");
    BasicBlock * const updateLastStartPos = b->CreateBasicBlock("updateLastStartPos");
    BasicBlock * const nextBlock = b->CreateBasicBlock("nextBlock");
    BasicBlock * const strideProcessed = b->CreateBasicBlock("strideProcessed");
    BasicBlock * const checkPrint = b->CreateBasicBlock("checkPrint");
    BasicBlock * const filterData = b->CreateBasicBlock("filterData");
    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const finalFiltering = b->CreateBasicBlock("finalFiltering");
    BasicBlock * const segmentDone = b->CreateBasicBlock("segmentDone");

    Value * const produced = b->getProducedItemCount("filtereData");
    Value * const availBytes = b->getAvailableItemCount("byteData");
    Value * const initialProcessedLines = b->getProcessedItemCount("mask");
    // b->CallPrintInt("initialProcessedLines", initialProcessedLines);
    b->CreateBr(startSegment);

    b->SetInsertPoint(startSegment);
    PHINode * strideNo = b->CreatePHI(sizeTy, 2);
    strideNo->addIncoming(sz_ZERO, entry);
    PHINode * segProducedPhi = b->CreatePHI(sizeTy, 2);
    segProducedPhi->addIncoming(produced, entry);
    PHINode * segProcessedPhi = b->CreatePHI(sizeTy, 2);
    segProcessedPhi->addIncoming(initialProcessedLines, entry);

    Value * nextStrideNo = b->CreateAdd(strideNo, sz_ONE);
    Value * segProcessedUpdate = b->CreateAdd(segProcessedPhi, sz_STRIDE);
    Value * strideBlockOffset = b->CreateMul(strideNo, sz_BLOCKS_PER_STRIDE);
    b->CreateBr(maskInit);

    b->SetInsertPoint(maskInit);
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2);
    blockNo->addIncoming(sz_ZERO, startSegment);
    PHINode * const strideProduced = b->CreatePHI(sizeTy, 2);
    strideProduced->addIncoming(segProducedPhi, startSegment);

    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    Value * strideBlockIndex = b->CreateAdd(strideBlockOffset, blockNo);
    Value * blockOffset = b->CreateMul(blockNo, sz_BLOCKWIDTH);
    Value * block = b->loadInputStreamBlock("mask", sz_ZERO, strideBlockIndex);
    Value * const popCnt = b->simd_popcount(b->getBitBlockWidth(), block);
    Value * const countOnes = b->CreateZExtOrTrunc(b->CreateExtractElement(b->fwCast(16, popCnt), b->getInt32(0)), sizeTy);
    Value * const countZeroes = b->CreateSub(sz_BLOCKWIDTH, countOnes);
    Value * const lastKnownStart = b->getScalarField("lastKnownStart");

    b->CreateCondBr(b->CreateAnd(b->CreateICmpUGT(countOnes, sz_ZERO),
                                 b->CreateICmpEQ(lastKnownStart, sz_ZERO)), 
                                 updateLastStartPos, checkPrint);
    b->SetInsertPoint(updateLastStartPos);
    Value * const newStart = b->CreateAdd(countZeroes, b->CreateAdd(segProcessedPhi, b->CreateMul(blockNo, sz_BLOCKWIDTH)));
    b->setScalarField("lastKnownStart", newStart);
    b->CreateBr(nextBlock);

    b->SetInsertPoint(checkPrint);
    b->CreateCondBr(b->CreateAnd(b->CreateICmpUGT(countZeroes, sz_ZERO),
                                 b->CreateICmpUGT(lastKnownStart, sz_ZERO)),
                                 filterData, nextBlock);

    b->SetInsertPoint(filterData);
    Value * const filterDataStartPos = b->getScalarField("lastKnownStart");
    Value * const filterDataEndPos = b->CreateAdd(countOnes, b->CreateAdd(segProcessedPhi, b->CreateMul(blockNo, sz_BLOCKWIDTH)));
    Value * const filterDataSize = b->CreateSub(filterDataEndPos, filterDataStartPos);
    // b->CallPrintInt("produced-filterData", segProducedPhi);
    // b->CallPrintInt("startPos-filterData", filterDataStartPos);
    // b->CallPrintInt("size-filterData", filterDataSize);
    b->CreateMemCpy(b->getRawOutputPointer("filtereData", segProducedPhi), b->getRawInputPointer("byteData", filterDataStartPos), filterDataSize, 1);
    b->setScalarField("lastKnownStart", sz_ZERO);
    Value * strideProducedUpdate = b->CreateAdd(strideProduced, filterDataSize);
    b->CreateBr(nextBlock);

    b->SetInsertPoint(nextBlock);
    PHINode * strideProducedUpdatePhi = b->CreatePHI(sizeTy, 2);
    strideProducedUpdatePhi->addIncoming(strideProducedUpdate, filterData);
    strideProducedUpdatePhi->addIncoming(strideProduced, checkPrint);
    strideProducedUpdatePhi->addIncoming(strideProduced, updateLastStartPos);

    blockNo->addIncoming(nextBlockNo, nextBlock);
    strideProduced->addIncoming(strideProducedUpdatePhi, nextBlock);
    b->CreateCondBr(b->CreateICmpNE(nextBlockNo, sz_BLOCKS_PER_STRIDE), maskInit, strideProcessed);

    b->SetInsertPoint(strideProcessed);
    strideNo->addIncoming(nextStrideNo, strideProcessed);
    segProducedPhi->addIncoming(strideProducedUpdatePhi, strideProcessed);
    segProcessedPhi->addIncoming(segProcessedUpdate, strideProcessed);

    b->CreateCondBr(b->CreateICmpNE(nextStrideNo, numOfStrides), startSegment, stridesDone);

    b->SetInsertPoint(stridesDone);
    b->CreateCondBr(b->CreateICmpEQ(b->getScalarField("lastKnownStart"), sz_ZERO), segmentDone, finalFiltering);
    b->SetInsertPoint(finalFiltering);
    Value * const startPos = b->getScalarField("lastKnownStart");
    Value * const size = b->CreateSub(segProcessedUpdate, startPos);
    // b->CallPrintInt("produced-stridesDone", strideProducedUpdatePhi);
    // b->CallPrintInt("startPos-stridesDone", startPos);
    // b->CallPrintInt("size-stridesDone", size);
    b->CreateMemCpy(b->getRawOutputPointer("filtereData", strideProducedUpdatePhi), b->getRawInputPointer("byteData", startPos), size, 1);
    b->setScalarField("lastKnownStart", sz_ZERO);
    b->CreateBr(segmentDone);
    b->SetInsertPoint(segmentDone);
}