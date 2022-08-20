#include "ztf-phrase-freq.h"
#include <llvm/IR/Function.h>                      // for Function, Function...
#include <llvm/IR/Module.h>                        // for Module
#include <llvm/Support/CommandLine.h>              // for ParseCommandLineOp...
#include <llvm/Support/Debug.h>                    // for dbgs
#include <kernel/core/kernel_builder.h>
#include <kernel/core/streamset.h>
#include <kernel/ztf/common.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/Support/raw_ostream.h>
#include <boost/intrusive/detail/math.hpp>
#include <sstream>

using namespace kernel;
using namespace llvm;

using BuilderRef = Kernel::BuilderRef;
// For every segment, if a table slot is empty, insert the compressible phrase in the entry and update the segment index of phrase.
// in the second iteration, if there's a collision, check the segment number of phrase and decide on replacing the phrase. 
// replace the phrase if freq > existing phrase AND existing phrase does not exist in the segment. 
// Otherwise, find the next empty/ unused slot in the current segment.
MarkFreqPhrases::MarkFreqPhrases(BuilderRef b,
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
: MultiBlockKernel(b, "MarkFreqPhrases" + std::to_string(numSyms) + std::to_string(groupNo) + lengthGroupSuffix(encodingScheme, groupNo),
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
                    InternalScalar{ArrayType::get(b->getSizeTy(), phraseHashSubTableSize(encodingScheme, groupNo, numSyms) * (encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1)), "segNoTable"},
                    InternalScalar{ArrayType::get(ArrayType::get(ArrayType::get(b->getInt8Ty(), encodingScheme.byLength[groupNo].hi), phraseVectorSize(encodingScheme, groupNo)), encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1), "phraseVector"},
                    InternalScalar{ArrayType::get(b->getSizeTy(), phraseVectorSize(encodingScheme, groupNo) * (encodingScheme.byLength[groupNo].hi - encodingScheme.byLength[groupNo].lo + 1)), "phraseFreqCount"}}),
mEncodingScheme(encodingScheme), mStrideSize(1048576), mGroupNo(groupNo), mNumSym(numSyms), mSubStride(std::min(b->getBitBlockWidth() * strideBlocks, SIZE_T_BITS * SIZE_T_BITS)), mOffset(offset) {
    mOutputStreamSets.emplace_back("hashMarks", hashMarks, FixedRate(), Delayed(1048576));
    mOutputStreamSets.emplace_back("secHashMarks", secHashMarks, FixedRate(), Delayed(1048576));
    mOutputStreamSets.emplace_back("freqUpdated", freqUpdated, FixedRate(), Delayed(1048576));
    setStride(1048576);
}

void MarkFreqPhrases::generateMultiBlockLogic(BuilderRef b, Value * const numOfStrides) {
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
    // b->CallPrintInt("sz_HASH_TBL", sz_HASH_TBL);
    Value * minFreqReqForCmp = b->CreateSelect(b->CreateICmpEQ(mGroupNoVal, sz_ZERO), b->getSize(4), sz_TWO);

    assert ((mStrideSize % mSubStride) == 0);
    Value * totalSubStrides =  b->getSize(mStrideSize / mSubStride); // 102400/2048 with BitBlock=256

    Type * sizeTy = b->getSizeTy();
    Type * bitBlockPtrTy = b->getBitBlockType()->getPointerTo();

    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const stridePrologue = b->CreateBasicBlock("stridePrologue");
    // BasicBlock * const subStrideMaskPrep = b->CreateBasicBlock("subStrideMaskPrep"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const strideMasksReady = b->CreateBasicBlock("strideMasksReady"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const keyProcessingLoop = b->CreateBasicBlock("keyProcessingLoop"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const processKey = b->CreateBasicBlock("processKey"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const nextKey = b->CreateBasicBlock("nextKey"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const checkAltIndex = b->CreateBasicBlock("checkAltIndex"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const findAltIdx = b->CreateBasicBlock("findAltIdx"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const writeAltNextIdx = b->CreateBasicBlock("writeAltNextIdx"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const checkAltIdxCond = b->CreateBasicBlock("checkAltIdxCond"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const calcSuffixMask = b->CreateBasicBlock("calcSuffixMask"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const calcPfxMask = b->CreateBasicBlock("calcPfxMask"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const calcSymSuffixMask_1 = b->CreateBasicBlock("calcSymSuffixMask_1");
    // BasicBlock * const calcSymPfxMask_1 = b->CreateBasicBlock("calcSymPfxMask_1");
    // BasicBlock * const updatePhraseHash = b->CreateBasicBlock("updatePhraseHash"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const tryStore = b->CreateBasicBlock("tryStore"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const storeKey = b->CreateBasicBlock("storeKey"); // RETAIN_PREV_SEG_ENTRIES
    // BasicBlock * const hashTableDone = b->CreateBasicBlock("hashTableDone"); // RETAIN_PREV_SEG_ENTRIES

    BasicBlock * const stridesDone = b->CreateBasicBlock("stridesDone");
    BasicBlock * const updatePending = b->CreateBasicBlock("updatePending");
    BasicBlock * const hashMarksDone = b->CreateBasicBlock("hashMarksDone");
    BasicBlock * const symProcessingLoop = b->CreateBasicBlock("symProcessingLoop");
    BasicBlock * const processSym = b->CreateBasicBlock("processSym");
    BasicBlock * const checkSymCompression = b->CreateBasicBlock("checkSymCompression");
    BasicBlock * const continueOverlapCheck = b->CreateBasicBlock("continueOverlapCheck");
    BasicBlock * const markSymCompression = b->CreateBasicBlock("markSymCompression");
    BasicBlock * const removeHashTableEntry = b->CreateBasicBlock("removeHashTableEntry");
    BasicBlock * const updateFreq = b->CreateBasicBlock("updateFreq");
    BasicBlock * const nextSym = b->CreateBasicBlock("nextSym");
    BasicBlock * const subStridePhrasesDone = b->CreateBasicBlock("subStridePhrasesDone");

    BasicBlock * const symsDone = b->CreateBasicBlock("symsDone");
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
    BasicBlock * const writeFreqAsOne = b->CreateBasicBlock("writeFreqAsOne");
    BasicBlock * const nextPhrase_part2 = b->CreateBasicBlock("nextPhrase_part2");
    BasicBlock * const lookupPhrase = b->CreateBasicBlock("lookupPhrase");
    BasicBlock * const checkNextIdx_part2 = b->CreateBasicBlock("checkNextIdx_part2");
    BasicBlock * const writeFreqInBuffer = b->CreateBasicBlock("writeFreqInBuffer");
    BasicBlock * const subStridePhrasesDone_1 = b->CreateBasicBlock("subStridePhrasesDone_1");

    BasicBlock * const checkSameGrpOverlap = b->CreateBasicBlock("checkSameGrpOverlap");
    BasicBlock * const unMarkSameGrpPhrase = b->CreateBasicBlock("unMarkSameGrpPhrase");
    BasicBlock * const checkUnmark = b->CreateBasicBlock("checkUnmark");

    BasicBlock * const checkIdxCond  = b->CreateBasicBlock("checkIdxCond ");
    BasicBlock * const storeInNextEmptyHash  = b->CreateBasicBlock("storeInNextEmptyHash ");
    BasicBlock * const tryHandleCollision = b->CreateBasicBlock("tryHandleCollision");
    BasicBlock * const indexReady = b->CreateBasicBlock("indexReady");

    BasicBlock * const writeNextIdx = b->CreateBasicBlock("writeNextIdx");
    BasicBlock * const tryStoreInNextIdx = b->CreateBasicBlock("tryStoreInNextIdx");

    BasicBlock * const collisionHandlingPrepLoop = b->CreateBasicBlock("collisionHandlingPrepLoop");
    BasicBlock * const chStrideMasksReady = b->CreateBasicBlock("chStrideMasksReady");
    BasicBlock * const collisionHandlingLoop = b->CreateBasicBlock("collisionHandlingLoop");
    BasicBlock * const processKeyCh = b->CreateBasicBlock("processKeyCh");
    BasicBlock * const calcSuffixMaskCh = b->CreateBasicBlock("calcSuffixMaskCh");
    BasicBlock * const calcPfxMaskCh = b->CreateBasicBlock("calcPfxMaskCh");
    BasicBlock * const storeOrReplaceEntry = b->CreateBasicBlock("storeOrReplaceEntry");
    BasicBlock * const tryReplaceTblEntry = b->CreateBasicBlock("tryReplaceTblEntry");
    BasicBlock * const relpaceTblEntry = b->CreateBasicBlock("relpaceTblEntry");
    BasicBlock * const checkPhraseFromPrevSeg = b->CreateBasicBlock("checkPhraseFromPrevSeg");
    BasicBlock * const storeIdx = b->CreateBasicBlock("storeIdx");
    BasicBlock * const collisionHandlingFailed = b->CreateBasicBlock("collisionHandlingFailed");
    BasicBlock * const nextKeyCh = b->CreateBasicBlock("nextKeyCh");
    BasicBlock * const collisionHandlingDone = b->CreateBasicBlock("collisionHandlingDone");

    Value * const avail = b->getAvailableItemCount("symEndMarks");

    Value * const processedBlocks = b->getScalarField("absBlocksProcessed");
    Value * const actualProcessed = b->CreateMul(processedBlocks, sz_BLOCKWIDTH);
    Value * globalHashTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("hashTable"), b->getInt8PtrTy());
    Value * globalFreqTableBasePtr = b->CreateBitCast(b->getScalarFieldPtr("freqTable"), sizeTy->getPointerTo());
    Value * segNoTblBasePtr = b->CreateBitCast(b->getScalarFieldPtr("segNoTable"), sizeTy->getPointerTo());
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

    Value * curHash = b->CreateAnd(phraseHashValue, lg.MAX_HASH_BITS);
    Value * curPos = phraseMarkPos;
    for (unsigned i = 0; i < lg.groupInfo.encoding_bytes + 1; i++) {
        curPos = b->CreateSub(curPos, sz_ONE);
        Value * hashByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", curPos)), sizeTy);
        curHash = b->CreateOr(b->CreateShl(curHash, lg.MAX_HASH_BITS), b->CreateAnd(hashByte, lg.MAX_HASH_BITS));
    }
    curHash = b->CreateAnd(curHash, lg.PHRASE_IDX_MASK);
    Value * lastIdx = maxIdx;//b->CreateAdd(curHash, b->CreateMul(phraseLength, b->getSize(1500))); //b->getSize(0x50)); // takes the same amount of time as that of having maxIdx0; worsens the cmp ratio
    lastIdx = b->CreateSelect(b->CreateICmpUGE(lastIdx, maxIdx), maxIdx, lastIdx);
    b->CreateBr(getOrAddPhrase);

    b->SetInsertPoint(getOrAddPhrase);
    PHINode * idx = b->CreatePHI(sizeTy, 2);
    idx->addIncoming(sz_ZERO, processPhrase); // curHash
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
    b->CreateCondBr(b->CreateICmpEQ(nextIdx, lastIdx), nextPhrase, getOrAddPhrase);

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
    Value * curHash0 = b->CreateAnd(phraseHashValue0, lg.MAX_HASH_BITS);
    Value * curPos0 = phraseMarkPos0;
    for (unsigned i = 0; i < lg.groupInfo.encoding_bytes + 1; i++) {
        curPos0 = b->CreateSub(curPos0, sz_ONE);
        Value * hashByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", curPos0)), sizeTy);
        curHash0 = b->CreateOr(b->CreateShl(curHash0, lg.MAX_HASH_BITS), b->CreateAnd(hashByte, lg.MAX_HASH_BITS));
    }
    curHash0 = b->CreateAnd(curHash0, lg.PHRASE_IDX_MASK);
    Value * lastIdx0 = maxIdx0; //b->CreateAdd(curHash0, b->CreateMul(phraseLength0, b->getSize(1500))); //b->getSize(0x50));
    lastIdx0 = b->CreateSelect(b->CreateICmpUGE(lastIdx0, maxIdx0), maxIdx0, lastIdx0);

    b->CreateBr(lookupPhrase);
    b->SetInsertPoint(lookupPhrase);
    PHINode * idx0 = b->CreatePHI(sizeTy, 2);
    idx0->addIncoming(sz_ZERO, processPhrase_part2); // curHash0
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
    b->CreateCondBr(b->CreateICmpEQ(nextIdx0, lastIdx0), writeFreqAsOne, lookupPhrase);

    b->SetInsertPoint(writeFreqAsOne);
    b->CreateStore(b->CreateTrunc(b->CreateAnd(sz_ONE, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", phraseMarkPos0));
    b->CreateBr(nextPhrase_part2);

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
    b->CreateCondBr(b->CreateICmpNE(step01nextSubStrideNo, totalSubStrides), freqCalcPrep_part2, collisionHandlingPrepLoop); //subStrideMaskPrep);

// ========================================================================================================================================================================
//                                 final freq buffer created
// ========================================================================================================================================================================
// iterate through all the phrases in the segment. Retain the hash-table entries which are useful in current segment -> update the segIdx of those phrases.
// RETAIN_PREV_SEG_ENTRIES start
    // b->SetInsertPoint(subStrideMaskPrep);
    // PHINode * const subStrideNo = b->CreatePHI(sizeTy, 2);
    // subStrideNo->addIncoming(sz_ZERO, subStridePhrasesDone_1);
    // Value * nextSubStrideNo = b->CreateAdd(subStrideNo, sz_ONE);
    // Value * subStridePos = b->CreateAdd(stridePos, b->CreateMul(subStrideNo, sz_SUB_STRIDE));
    // Value * subStrideBlockOffset = b->CreateAdd(strideBlockOffset, b->CreateMul(subStrideNo, sz_BLOCKS_PER_SUB_STRIDE));
    // std::vector<Value *> keyMasks = initializeCompressionMasks2(b, sw, sz_BLOCKS_PER_SUB_STRIDE, 1, subStrideBlockOffset, hashMarksPtr, strideMasksReady);
    // Value * keyMask = keyMasks[0];

    // b->SetInsertPoint(strideMasksReady);
    // subStrideBlockOffset = b->CreateSub(subStrideBlockOffset, processedBlocks); // relative block offset
    // Value * keyWordBasePtr = b->getInputStreamBlockPtr("symEndMarks", sz_ZERO, subStrideBlockOffset);
    // keyWordBasePtr = b->CreateBitCast(keyWordBasePtr, sw.pointerTy);
    // b->CreateUnlikelyCondBr(b->CreateICmpEQ(keyMask, sz_ZERO), hashTableDone, keyProcessingLoop);

    // b->SetInsertPoint(keyProcessingLoop);
    // PHINode * const keyMaskPhi = b->CreatePHI(sizeTy, 2);
    // keyMaskPhi->addIncoming(keyMask, strideMasksReady);
    // PHINode * const keyWordPhi = b->CreatePHI(sizeTy, 2);
    // keyWordPhi->addIncoming(sz_ZERO, strideMasksReady);
    // Value * keyWordIdx = b->CreateCountForwardZeroes(keyMaskPhi, "keyWordIdx");
    // Value * nextKeyWord = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(keyWordBasePtr, keyWordIdx)), sizeTy);
    // Value * theKeyWord = b->CreateSelect(b->CreateICmpEQ(keyWordPhi, sz_ZERO), nextKeyWord, keyWordPhi);
    // Value * keyWordPos = b->CreateAdd(subStridePos, b->CreateMul(keyWordIdx, sw.WIDTH));
    // Value * keyMarkPosInWord = b->CreateCountForwardZeroes(theKeyWord);
    // Value * keyMarkPos = b->CreateAdd(keyWordPos, keyMarkPosInWord, "keyEndPos");
    // Value * keyProcessCond = b->CreateAnd(b->CreateICmpULE(keyMarkPos, processBeforeThisPos), b->CreateICmpUGT(keyMarkPos, processAfterThisPos));
    // b->CreateCondBr(keyProcessCond, processKey, nextKey);

    // b->SetInsertPoint(processKey);
    // /* Determine the key length. */
    // Value * hashValue = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", keyMarkPos)), sizeTy);
    // Value * keyLength = b->CreateAdd(b->CreateLShr(hashValue, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET, "keyLength");
    // Value * keyStartPos = b->CreateSub(keyMarkPos, b->CreateSub(keyLength, sz_ONE, "keyStartPos1"), "keyStartPos2");
    // // keyOffset for accessing the final half of an entry.
    // Value * keyOffset = b->CreateSub(keyLength, lg.HALF_LENGTH, "keyOffset");
    // // Build up a single encoded value for table lookup from the hashcode sequence.
    // Value * codewordVal = b->CreateAnd(hashValue, lg.LAST_SUFFIX_MASK);
    // Value * hashcodePos = keyMarkPos;
    // // group #      codewordVal bits
    // //  0                   7 + 5 (pfx)
    // //  1                   7 + 1 (pfx)
    // //  2                   7+7 + 1 (pfx)
    // //  3                   7+7+7(not used) + 1(pfx)
    // b->CreateCondBr(b->CreateICmpUGT(mGroupNoVal, sz_ZERO), calcSuffixMask, calcPfxMask);

    // b->SetInsertPoint(calcSuffixMask);
    // hashcodePos = b->CreateSub(hashcodePos, sz_ONE);
    // Value * secondLastSuffix = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", hashcodePos)), sizeTy);
    // Value * cwVal = b->CreateShl(codewordVal, lg.SEC_LAST_SFX);
    // cwVal = b->CreateOr(cwVal, b->CreateAnd(secondLastSuffix, lg.SEC_LAST_SUFFIX_MASK));
    // b->CreateBr(calcPfxMask);

    // b->SetInsertPoint(calcPfxMask);
    // PHINode * hcPos = b->CreatePHI(sizeTy, 2);
    // hcPos->addIncoming(hashcodePos, calcSuffixMask);
    // hcPos->addIncoming(keyMarkPos, processKey);
    // PHINode * codewordValPhi = b->CreatePHI(sizeTy, 2, "codewordValPhi");
    // codewordValPhi->addIncoming(cwVal, calcSuffixMask);
    // codewordValPhi->addIncoming(codewordVal, processKey);
    // Value * codewordValFin = codewordValPhi;
    // // add PREFIX_LENGTH_MASK bits for larger index space
    // Value * readPos = b->CreateSub(hcPos, sz_ONE);
    // Value * pfxByte = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", readPos)), sizeTy);
    // // shift by pfx len bits
    // pfxByte = b->CreateTrunc(b->CreateAnd(pfxByte, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    // codewordValFin = b->CreateOr(b->CreateShl(codewordValFin, lg.EXTRA_BITS), b->CreateAnd(pfxByte, lg.EXTRA_BITS_MASK)); // shifts 6 bits for 2-sym phrases; group 2 & 3 - FIXED!

    // Value * tableIdxHash = b->CreateAnd(codewordValFin, lg.TABLE_MASK, "tableIdxHash");
    // Value * altStartIdx = b->CreateAdd(tableIdxHash, sz_ONE);
    // altStartIdx = b->CreateSelect(b->CreateICmpUGE(altStartIdx, sz_HASH_TBL), tableIdxHash, altStartIdx);

    // Value * globalSubTablePtr = b->CreateGEP(globalHashTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    // Value * segNoSubTablePtr = b->CreateGEP(segNoTblBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.FREQ_SUBTABLE_SIZE));
    // Value * freqSubTablePtr = b->CreateGEP(globalFreqTableBasePtr, b->CreateMul(b->CreateSub(keyLength, lg.LO), lg.FREQ_SUBTABLE_SIZE));

    // Value * symPtr1 = b->CreateBitCast(b->getRawInputPointer("byteData", keyStartPos), lg.halfSymPtrTy);
    // Value * symPtr2 = b->CreateBitCast(b->getRawInputPointer("byteData", b->CreateAdd(keyStartPos, keyOffset)), lg.halfSymPtrTy);
    // // Check if the hash table entry is nonzero (already assigned).
    // Value * sym1 = b->CreateAlignedLoad(symPtr1, 1);
    // Value * sym2 = b->CreateAlignedLoad(symPtr2, 1);

    // // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength); //BIGRAMDEBUGGING
    // // b->CallPrintInt("keyLength-init", keyLength); //BIGRAMDEBUGGING
    // // b->CallPrintInt("keyMarkPos-init", keyMarkPos); //BIGRAMDEBUGGING
    // // b->CallPrintInt("tableIdxHash-init", tableIdxHash); //BIGRAMDEBUGGING

    // Value * hash1IdxPtr = b->CreateGEP(globalSubTablePtr, b->CreateMul(tableIdxHash, keyLength));
    // Value * hash1EntryPtr = b->CreateInBoundsGEP(hash1IdxPtr, sz_ZERO);
    // Value * hash1Ptr1 = b->CreateBitCast(hash1EntryPtr, lg.halfSymPtrTy);
    // Value * hash1Ptr2 = b->CreateBitCast(b->CreateGEP(hash1EntryPtr, keyOffset), lg.halfSymPtrTy);
    // Value * entry1hash1 = b->CreateMonitoredScalarFieldLoad("hashTable", hash1Ptr1);
    // Value * entry2hash1 = b->CreateMonitoredScalarFieldLoad("hashTable", hash1Ptr2);
    // Value * freqTblEntryPtr = b->CreateInBoundsGEP(freqSubTablePtr, tableIdxHash, "freqTblEntryPtr");
    // Value * freqTblPtr = b->CreateBitCast(freqTblEntryPtr, sizeTy->getPointerTo());
    // Value * segNoTblEntryPtr = b->CreateInBoundsGEP(segNoSubTablePtr, tableIdxHash, "segNoTblEntryPtr");
    // Value * segNoTblPtr = b->CreateBitCast(segNoTblEntryPtr, sizeTy->getPointerTo());

    // Value * phraseFreq = b->CreateZExt(b->CreateLoad(b->getRawOutputPointer("freqUpdated", keyMarkPos)), sizeTy, "phraseFreq");
    // Value * isPhraseCompressible = b->CreateICmpUGE(phraseFreq, minFreqReqForCmp);
    // Value * tableIdxEmpty = b->CreateICmpEQ(b->CreateOr(entry1hash1, entry2hash1), Constant::getNullValue(lg.halfLengthTy));
    // Value * phraseMatches = b->CreateAnd(b->CreateICmpEQ(entry1hash1, sym1), b->CreateICmpEQ(entry2hash1, sym2));
    // b->CreateCondBr(b->CreateAnd(phraseMatches, isPhraseCompressible), updatePhraseHash, tryStore);

    // b->SetInsertPoint(updatePhraseHash);
    // // ---> you store a hash in freqUpdated but calculate the hash again from scratch in the collision handling loop!
    // b->CreateStore(b->CreateTrunc(b->CreateAnd(tableIdxHash, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPos, sz_ONE)));
    // b->CreateMonitoredScalarFieldStore("segNoTable", b->getScalarField("segIndex"), segNoTblPtr);
    // b->CreateBr(nextKey);

    // b->SetInsertPoint(tryStore);
    // b->CreateCondBr(b->CreateAnd(isPhraseCompressible, tableIdxEmpty), storeKey, checkAltIndex); // check if the phrase exists in any other index using linear probing.

    // b->SetInsertPoint(storeKey);
    // b->CreateStore(b->CreateTrunc(b->CreateAnd(tableIdxHash, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPos, sz_ONE)));

    // // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength);
    // // b->CallPrintInt("tableIdxHash", tableIdxHash);
    // // b->CallPrintInt("phraseFreq", phraseFreq);
    // // b->CallPrintInt("segNo", b->getScalarField("segIndex"));
    // // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1, keyLength); //BIGRAMDEBUGGING
    // // b->CallPrintInt("keyLength-storeKey", keyLength); //BIGRAMDEBUGGING
    // // b->CallPrintInt("keyMarkPos-storeKey", keyMarkPos); //BIGRAMDEBUGGING

    // b->CreateMonitoredScalarFieldStore("hashTable", sym1, hash1Ptr1);
    // b->CreateMonitoredScalarFieldStore("hashTable", sym2, hash1Ptr2);
    // b->CreateMonitoredScalarFieldStore("freqTable", phraseFreq, freqTblPtr);
    // b->CreateMonitoredScalarFieldStore("segNoTable", b->getScalarField("segIndex"), segNoTblPtr);
    // b->CreateBr(nextKey);

    // b->SetInsertPoint(checkAltIndex);
    // // b->CallPrintInt("tableIdxHash-checkAltIndex", tableIdxHash); //BIGRAMDEBUGGING
    // Value * const altEndIdx = b->CreateSelect(b->CreateICmpUGE(b->CreateAdd(altStartIdx, b->getSize(0x50)), sz_HASH_TBL), b->CreateSub(sz_HASH_TBL, sz_ONE), b->CreateAdd(altStartIdx, b->getSize(0x50)));
    // Value * findPhraseInAltIdx = b->CreateAnd(isPhraseCompressible, b->CreateICmpULT(altStartIdx, altEndIdx));
    // b->CreateCondBr(findPhraseInAltIdx, findAltIdx, nextKey); // same segment collision

    // b->SetInsertPoint(findAltIdx);
    // PHINode * curAltIndex = b->CreatePHI(sizeTy, 2, "curAltIndex");
    // curAltIndex->addIncoming(altStartIdx, checkAltIndex);
    // Value * nextAltIndex = b->CreateAdd(curAltIndex, sz_ONE);

    // Value * nextAltSymIdxPtr = b->CreateGEP(globalSubTablePtr, b->CreateMul(curAltIndex, keyLength));
    // Value * nextAltSymEntryPtr = b->CreateInBoundsGEP(nextAltSymIdxPtr, sz_ZERO);
    // Value * nextAltSymPtr1 = b->CreateBitCast(nextAltSymEntryPtr, lg.halfSymPtrTy);
    // Value * nextAltSymPtr2 = b->CreateBitCast(b->CreateGEP(nextAltSymEntryPtr, keyOffset), lg.halfSymPtrTy);
    // Value * nextAltSym1 = b->CreateMonitoredScalarFieldLoad("hashTable", nextAltSymPtr1);
    // Value * nextAltSym2 = b->CreateMonitoredScalarFieldLoad("hashTable", nextAltSymPtr2);
    // Value * altSymSegNoTblEntryPtr = b->CreateInBoundsGEP(segNoSubTablePtr, tableIdxHash, "altSymSegNoTblEntryPtr");
    // Value * altSymSegNoTblPtr = b->CreateBitCast(altSymSegNoTblEntryPtr, sizeTy->getPointerTo());
    // // b->CallPrintInt("curAltIndex", curAltIndex);
    // Value * phraseMatchAtAltIdx = b->CreateAnd(b->CreateICmpEQ(nextAltSym1, sym1), b->CreateICmpEQ(nextAltSym2, sym2));
    // b->CreateCondBr(phraseMatchAtAltIdx, writeAltNextIdx, checkAltIdxCond);

    // b->SetInsertPoint(writeAltNextIdx);
    // b->CreateStore(b->CreateTrunc(b->CreateAnd(curAltIndex, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPos, sz_ONE)));
    // b->CreateMonitoredScalarFieldStore("segNoTable", b->getScalarField("segIndex"), altSymSegNoTblPtr);
    // b->CreateBr(nextKey);

    // b->SetInsertPoint(checkAltIdxCond);
    // curAltIndex->addIncoming(nextAltIndex, checkAltIdxCond);
    // b->CreateCondBr(b->CreateICmpNE(nextAltIndex, altEndIdx), findAltIdx, nextKey);

    // b->SetInsertPoint(nextKey);
    // Value * dropKey = b->CreateResetLowestBit(theKeyWord);
    // Value * thisWordDone = b->CreateICmpEQ(dropKey, sz_ZERO);
    // // There may be more keys in the key mask.
    // Value * nextKeyMask = b->CreateSelect(thisWordDone, b->CreateResetLowestBit(keyMaskPhi), keyMaskPhi);
    // BasicBlock * currentBB = b->GetInsertBlock();
    // keyMaskPhi->addIncoming(nextKeyMask, currentBB);
    // keyWordPhi->addIncoming(dropKey, currentBB);
    // b->CreateCondBr(b->CreateICmpNE(nextKeyMask, sz_ZERO), keyProcessingLoop, hashTableDone);

    // b->SetInsertPoint(hashTableDone);
    // subStrideNo->addIncoming(nextSubStrideNo, hashTableDone);
    // b->CreateCondBr(b->CreateICmpNE(nextSubStrideNo, totalSubStrides), subStrideMaskPrep, collisionHandlingPrepLoop);
// RETAIN_PREV_SEG_ENTRIES end
// =================== collision handling loop start ====================
// in case of collision, compare the segment number of the new phrase with already existing phrase.
// if new phrase is from different segment than that of the exiting phrase, replace the hash-table entry.
// else find the new empty slot in hash-table for the new phrase.

    b->SetInsertPoint(collisionHandlingPrepLoop);
    PHINode * const subStNo = b->CreatePHI(sizeTy, 2, "subStNo");
    subStNo->addIncoming(sz_ZERO, subStridePhrasesDone_1); //hashTableDone);
    Value * nextSubStNo = b->CreateAdd(subStNo, sz_ONE);
    Value * subStPos = b->CreateAdd(stridePos, b->CreateMul(subStNo, sz_SUB_STRIDE));
    Value * subStrideBO = b->CreateAdd(strideBlockOffset, b->CreateMul(subStNo, sz_BLOCKS_PER_SUB_STRIDE));
    std::vector<Value *> keyMasks1 = initializeCompressionMasks2(b, sw, sz_BLOCKS_PER_SUB_STRIDE, 1, subStrideBO, hashMarksPtr, chStrideMasksReady);
    Value * keyMaskCh = keyMasks1[0];

    b->SetInsertPoint(chStrideMasksReady);
    subStrideBO = b->CreateSub(subStrideBO, processedBlocks); // relative block offset
    Value * keyWordBasePtrCh = b->getInputStreamBlockPtr("symEndMarks", sz_ZERO, subStrideBO);
    keyWordBasePtrCh = b->CreateBitCast(keyWordBasePtrCh, sw.pointerTy);
    b->CreateUnlikelyCondBr(b->CreateICmpEQ(keyMaskCh, sz_ZERO), collisionHandlingDone, collisionHandlingLoop);

    b->SetInsertPoint(collisionHandlingLoop);
    PHINode * const keyMaskPhiCh = b->CreatePHI(sizeTy, 2, "keyMaskPhiCh");
    keyMaskPhiCh->addIncoming(keyMaskCh, chStrideMasksReady);
    PHINode * const keyWordPhiCh = b->CreatePHI(sizeTy, 2, "keyWordPhiCh");
    keyWordPhiCh->addIncoming(sz_ZERO, chStrideMasksReady);
    Value * keyWordIdxCh = b->CreateCountForwardZeroes(keyMaskPhiCh, "keyWordIdxCh");
    Value * nextKeyWordCh = b->CreateZExtOrTrunc(b->CreateLoad(b->CreateGEP(keyWordBasePtrCh, keyWordIdxCh)), sizeTy);
    Value * theKeyWordCh = b->CreateSelect(b->CreateICmpEQ(keyWordPhiCh, sz_ZERO), nextKeyWordCh, keyWordPhiCh);
    Value * keyWordPosCh = b->CreateAdd(subStPos, b->CreateMul(keyWordIdxCh, sw.WIDTH));
    Value * keyMarkPosInWordCh = b->CreateCountForwardZeroes(theKeyWordCh);
    Value * keyMarkPosCh = b->CreateAdd(keyWordPosCh, keyMarkPosInWordCh, "keyEndPosCh");
    Value * keyProcessCondCh = b->CreateAnd(b->CreateICmpULE(keyMarkPosCh, processBeforeThisPos), b->CreateICmpUGT(keyMarkPosCh, processAfterThisPos));
    b->CreateCondBr(keyProcessCondCh, processKeyCh, nextKeyCh);

    b->SetInsertPoint(processKeyCh);
    /* Determine the key length. */
    Value * hashValueCh = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", keyMarkPosCh)), sizeTy);
    Value * keyLengthCh = b->CreateAdd(b->CreateLShr(hashValueCh, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET, "keyLengthCh");
    Value * keyStartPosCh = b->CreateSub(keyMarkPosCh, b->CreateSub(keyLengthCh, sz_ONE), "keyStartPosCh");
    // keyOffset for accessing the final half of an entry.
    Value * keyOffsetCh = b->CreateSub(keyLengthCh, lg.HALF_LENGTH);
    // Build up a single encoded value for table lookup from the hashcode sequence.
    Value * codewordValCh = b->CreateAnd(hashValueCh, lg.LAST_SUFFIX_MASK);
    Value * hashcodePosCh = keyMarkPosCh;
    // group #              codewordValCh bits
    //  0                   7 + 5 (pfx)
    //  1                   7 + 1 (pfx)
    //  2                   7+7 + 1 (pfx)
    //  3                   7+7+7(not used) + 1(pfx)
    b->CreateCondBr(b->CreateICmpUGT(mGroupNoVal, sz_ZERO), calcSuffixMaskCh, calcPfxMaskCh);

    b->SetInsertPoint(calcSuffixMaskCh);
    hashcodePosCh = b->CreateSub(hashcodePosCh, sz_ONE);
    Value * secondLastSuffixCh = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", hashcodePosCh)), sizeTy);
    Value * cwValCh = b->CreateShl(codewordValCh, lg.SEC_LAST_SFX);
    cwValCh = b->CreateOr(cwValCh, b->CreateAnd(secondLastSuffixCh, lg.SEC_LAST_SUFFIX_MASK));
    b->CreateBr(calcPfxMaskCh);

    b->SetInsertPoint(calcPfxMaskCh);
    PHINode * hcPosCh = b->CreatePHI(sizeTy, 2, "hcPosCh");
    hcPosCh->addIncoming(hashcodePosCh, calcSuffixMaskCh);
    hcPosCh->addIncoming(keyMarkPosCh, processKeyCh);
    PHINode * codewordValPhiCh = b->CreatePHI(sizeTy, 2, "codewordValPhiCh");
    codewordValPhiCh->addIncoming(cwValCh, calcSuffixMaskCh);
    codewordValPhiCh->addIncoming(codewordValCh, processKeyCh);
    Value * codewordValFinCh = codewordValPhiCh;
    // add PREFIX_LENGTH_MASK bits for larger index space
    Value * readPosCh = b->CreateSub(hcPosCh, sz_ONE);
    Value * pfxByteCh = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", readPosCh)), sizeTy);
    // shift by pfx len bits
    pfxByteCh = b->CreateTrunc(b->CreateAnd(pfxByteCh, lg.PREFIX_LENGTH_MASK), b->getInt64Ty());
    codewordValFinCh = b->CreateOr(b->CreateShl(codewordValFinCh, lg.EXTRA_BITS), b->CreateAnd(pfxByteCh, lg.EXTRA_BITS_MASK));

    // verify startIdx is in bounds of hashtable indices
    Value * tableIdxHashCh = b->CreateAnd(codewordValFinCh, lg.TABLE_MASK, "tableIdxHashCh");
    // if phrase exists at tableIdxHashCh1, it has already been updated. Go to next phrase.
    // Value * tableIdxHashCh1 = b->CreateZExt(b->CreateLoad(b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPosCh, sz_ONE))), sizeTy, "tableIdxHashCh1"); // RETAIN_PREV_SEG_ENTRIES
    Value * startIdx = b->CreateAdd(tableIdxHashCh, sz_ONE);
    startIdx = b->CreateSelect(b->CreateICmpUGE(startIdx, sz_HASH_TBL), tableIdxHashCh, startIdx);
    Value * endIdx = b->CreateAdd(startIdx, b->getSize(0x50));
    endIdx = b->CreateSelect(b->CreateICmpUGE(endIdx, sz_HASH_TBL), b->CreateSub(sz_HASH_TBL, sz_ONE), endIdx);

    Value * globalSubTablePtrCh = b->CreateGEP(globalHashTableBasePtr, b->CreateMul(b->CreateSub(keyLengthCh, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    Value * segNoSubTablePtrCh = b->CreateGEP(segNoTblBasePtr, b->CreateMul(b->CreateSub(keyLengthCh, lg.LO), lg.FREQ_SUBTABLE_SIZE));
    Value * freqSubTablePtrCh = b->CreateGEP(globalFreqTableBasePtr, b->CreateMul(b->CreateSub(keyLengthCh, lg.LO), lg.FREQ_SUBTABLE_SIZE));

    Value * symPtr1Ch = b->CreateBitCast(b->getRawInputPointer("byteData", keyStartPosCh), lg.halfSymPtrTy);
    Value * symPtr2Ch = b->CreateBitCast(b->getRawInputPointer("byteData", b->CreateAdd(keyStartPosCh, keyOffsetCh)), lg.halfSymPtrTy);
    // Check if the hash table entry is nonzero (already assigned).
    Value * sym1Ch = b->CreateAlignedLoad(symPtr1Ch, 1);
    Value * sym2Ch = b->CreateAlignedLoad(symPtr2Ch, 1);

    Value * hash1IdxPtrCh = b->CreateGEP(globalSubTablePtrCh, b->CreateMul(tableIdxHashCh, keyLengthCh));
    Value * hash1EntryPtrCh = b->CreateInBoundsGEP(hash1IdxPtrCh, sz_ZERO);
    Value * hash1Ptr1Ch = b->CreateBitCast(hash1EntryPtrCh, lg.halfSymPtrTy);
    Value * hash1Ptr2Ch = b->CreateBitCast(b->CreateGEP(hash1EntryPtrCh, keyOffsetCh), lg.halfSymPtrTy);
    Value * entry1hash1Ch = b->CreateMonitoredScalarFieldLoad("hashTable", hash1Ptr1Ch);
    Value * entry2hash1Ch = b->CreateMonitoredScalarFieldLoad("hashTable", hash1Ptr2Ch);

    // Value * hash1IdxPtrCh1 = b->CreateGEP(globalSubTablePtrCh, b->CreateMul(tableIdxHashCh1, keyLengthCh)); // RETAIN_PREV_SEG_ENTRIES
    // Value * hash1EntryPtrCh1 = b->CreateInBoundsGEP(hash1IdxPtrCh1, sz_ZERO); // RETAIN_PREV_SEG_ENTRIES
    // Value * hash1Ptr1Ch1 = b->CreateBitCast(hash1EntryPtrCh1, lg.halfSymPtrTy); // RETAIN_PREV_SEG_ENTRIES
    // Value * hash1Ptr2Ch1 = b->CreateBitCast(b->CreateGEP(hash1EntryPtrCh1, keyOffsetCh), lg.halfSymPtrTy); // RETAIN_PREV_SEG_ENTRIES
    // Value * entry1hash1Ch1 = b->CreateMonitoredScalarFieldLoad("hashTable", hash1Ptr1Ch1); // RETAIN_PREV_SEG_ENTRIES
    // Value * entry2hash1Ch1 = b->CreateMonitoredScalarFieldLoad("hashTable", hash1Ptr2Ch1); // RETAIN_PREV_SEG_ENTRIES

    Value * segNoTblEntryPtrCh = b->CreateInBoundsGEP(segNoSubTablePtrCh, tableIdxHashCh);
    Value * segNoTblPtrCh = b->CreateBitCast(segNoTblEntryPtrCh, sizeTy->getPointerTo());
    Value * phraseSegNo = b->CreateMonitoredScalarFieldLoad("segNoTable", segNoTblPtrCh);
    Value * freqTblEntryPtrCh = b->CreateInBoundsGEP(freqSubTablePtrCh, tableIdxHashCh);
    Value * freqTblPtrCh = b->CreateBitCast(freqTblEntryPtrCh, sizeTy->getPointerTo());
    // Value * phrasefreqInTbl = b->CreateMonitoredScalarFieldLoad("freqTable", freqTblPtrCh);

    Value * phraseFreqCh = b->CreateZExt(b->CreateLoad(b->getRawOutputPointer("freqUpdated", keyMarkPosCh)), sizeTy);
    // Value * hasGreaterFreq = b->CreateICmpUGT(phraseFreqCh, phrasefreqInTbl);
    Value * phraseFreqGood = b->CreateICmpUGE(phraseFreqCh, minFreqReqForCmp); // b->CreateAnd(b->CreateICmpUGE(phraseFreqCh, minFreqReqForCmp), hasGreaterFreq);
    Value * tableIdxEmptyCh = b->CreateICmpEQ(b->CreateOr(entry1hash1Ch, entry2hash1Ch), Constant::getNullValue(lg.halfLengthTy));
    Value * phraseInTableOrigIdx = b->CreateAnd(b->CreateICmpEQ(entry1hash1Ch, sym1Ch), b->CreateICmpEQ(entry2hash1Ch, sym2Ch));
    // Value * phraseMatchesInTbl_updatedIdx = b->CreateAnd(b->CreateICmpEQ(entry1hash1Ch1, sym1Ch), b->CreateICmpEQ(entry2hash1Ch1, sym2Ch)); // RETAIN_PREV_SEG_ENTRIES
    b->CreateCondBr(phraseInTableOrigIdx, storeIdx, storeOrReplaceEntry); // b->CreateOr(phraseMatchesInTbl_updatedIdx, phraseMatchesInTbl) // RETAIN_PREV_SEG_ENTRIES

    b->SetInsertPoint(storeIdx);
    b->CreateStore(b->CreateTrunc(b->CreateAnd(tableIdxHashCh, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPosCh, sz_ONE)));
    b->CreateMonitoredScalarFieldStore("segNoTable", b->getScalarField("segIndex"), segNoTblPtrCh);
    b->CreateBr(nextKeyCh);

    b->SetInsertPoint(storeOrReplaceEntry);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1Ch, keyLengthCh); //BIGRAMDEBUGGING
    // b->CallPrintInt("tableIdxHashCh", tableIdxHashCh);
    // b->CallPrintInt("tableIdxHashCh1", tableIdxHashCh1);
    b->CreateCondBr(b->CreateAnd(tableIdxEmptyCh, phraseFreqGood), relpaceTblEntry, tryReplaceTblEntry);

    b->SetInsertPoint(tryReplaceTblEntry);
    // increasing the difference between last seen and current segment number reduces the dictionary size
    Value * replacePrevSegEntry = b->CreateICmpULT(phraseSegNo, b->getScalarField("segIndex")); //b->CreateICmpUGT(b->CreateSub(b->getScalarField("segIndex"), phraseSegNo), b->getSize(1));
    b->CreateCondBr(b->CreateAnd(replacePrevSegEntry, phraseFreqGood), relpaceTblEntry, tryHandleCollision);

    b->SetInsertPoint(relpaceTblEntry);

    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1Ch, keyLength);
    // b->CallPrintInt("tableIdxHashCh", tableIdxHashCh);
    // b->CallPrintInt("phraseFreqCh", phraseFreqCh);
    // b->CallPrintInt("segNoCh", b->getScalarField("segIndex"));
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1Ch, keyLengthCh); //BIGRAMDEBUGGING
    // b->CallPrintInt("keyLengthCh-0", keyLengthCh); //BIGRAMDEBUGGING
    // b->CallPrintInt("keyMarkPosCh-0", keyMarkPosCh); //BIGRAMDEBUGGING

    b->CreateMonitoredScalarFieldStore("hashTable", sym1Ch, hash1Ptr1Ch);
    b->CreateMonitoredScalarFieldStore("hashTable", sym2Ch, hash1Ptr2Ch);
    b->CreateMonitoredScalarFieldStore("freqTable", phraseFreqCh, freqTblPtrCh);
    b->CreateMonitoredScalarFieldStore("segNoTable", b->getScalarField("segIndex"), segNoTblPtrCh);
    b->CreateStore(b->CreateTrunc(b->CreateAnd(tableIdxHashCh, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPosCh, sz_ONE)));
    b->CreateBr(nextKeyCh);

    b->SetInsertPoint(tryHandleCollision);
    Value * findNextAvailIdxCond = b->CreateICmpUGE(phraseFreqCh, minFreqReqForCmp);
    findNextAvailIdxCond = b->CreateAnd(findNextAvailIdxCond, b->CreateICmpULT(startIdx, endIdx)); // TRY: reset index if cond is false
    b->CreateCondBr(findNextAvailIdxCond, indexReady, nextKeyCh); // same segment collision

    b->SetInsertPoint(indexReady);
    PHINode * curIndex = b->CreatePHI(sizeTy, 2, "curIndex");
    curIndex->addIncoming(startIdx, tryHandleCollision);
    Value * nextIndex = b->CreateAdd(curIndex, sz_ONE);

    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1Ch, keyLengthCh);
    // b->CallPrintInt("curIndex-tryHandleCollision", curIndex); //BIGRAMDEBUGGING

    Value * nextSymIdxPtr = b->CreateGEP(globalSubTablePtrCh, b->CreateMul(curIndex, keyLengthCh));
    Value * nextSymEntryPtr = b->CreateInBoundsGEP(nextSymIdxPtr, sz_ZERO);
    Value * nextSymPtr1 = b->CreateBitCast(nextSymEntryPtr, lg.halfSymPtrTy);
    Value * nextSymPtr2 = b->CreateBitCast(b->CreateGEP(nextSymEntryPtr, keyOffsetCh), lg.halfSymPtrTy);
    Value * nextSym1 = b->CreateMonitoredScalarFieldLoad("hashTable", nextSymPtr1);
    Value * nextSym2 = b->CreateMonitoredScalarFieldLoad("hashTable", nextSymPtr2);
    Value * nextSymFreqTblEntryPtr = b->CreateInBoundsGEP(freqSubTablePtrCh, curIndex);
    Value * nextSymFreqTblPtr = b->CreateBitCast(nextSymFreqTblEntryPtr, sizeTy->getPointerTo());
    // Value * nextSymFreq = b->CreateMonitoredScalarFieldLoad("freqTable", nextSymFreqTblPtr);

    Value * nextSymSegTblEntryPtr = b->CreateInBoundsGEP(segNoSubTablePtrCh, curIndex);
    Value * nextSymSegTblPtr = b->CreateBitCast(nextSymSegTblEntryPtr, sizeTy->getPointerTo());
    Value * nextSymSegNo = b->CreateMonitoredScalarFieldLoad("segNoTable", nextSymSegTblPtr);

    Value * phraseMatch = b->CreateAnd(b->CreateICmpEQ(nextSym1, sym1Ch), b->CreateICmpEQ(nextSym2, sym2Ch));
    b->CreateCondBr(phraseMatch, writeNextIdx, tryStoreInNextIdx);

    b->SetInsertPoint(writeNextIdx);
    b->CreateStore(b->CreateTrunc(b->CreateAnd(curIndex, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPosCh, sz_ONE)));
    b->CreateMonitoredScalarFieldStore("segNoTable", b->getScalarField("segIndex"), nextSymSegTblPtr);
    b->CreateBr(nextKeyCh);

    b->SetInsertPoint(tryStoreInNextIdx);
    // store in any subsequent index if any of the following is true:
    // 1. subsequent index phrase is from prev segment.
    // 2. subsequent index is empty
    // 3. if no empty slot found, keep not of the lowest freq phrase in the range; replace with current syn. -> FOR LATER
    Value * isEmptyNextSymEntry = b->CreateICmpEQ(b->CreateOr(nextSym1, nextSym2), Constant::getNullValue(lg.halfLengthTy));
    b->CreateCondBr(b->CreateOr(b->CreateICmpUGE(phraseFreqCh, minFreqReqForCmp), isEmptyNextSymEntry), storeInNextEmptyHash, checkPhraseFromPrevSeg); //checkIdxCond);

    b->SetInsertPoint(checkPhraseFromPrevSeg);
    b->CreateCondBr(b->CreateICmpULT(nextSymSegNo, b->getScalarField("segIndex")), storeInNextEmptyHash, checkIdxCond); // TRY: compare freq with exiting phrase freq
    //b->CreateICmpUGT(b->CreateSub(b->getScalarField("segIndex"), nextSymSegNo), b->getSize(1))

    b->SetInsertPoint(storeInNextEmptyHash);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1Ch, keyLength);
    // b->CallPrintInt("tableIdxHashCh-EmptyHash", tableIdxHashCh);
    // b->CallPrintInt("phraseFreqCh-EmptyHash", phraseFreqCh);
    // b->CallPrintInt("segNoCh-EmptyHash", b->getScalarField("segIndex"));

    b->CreateMonitoredScalarFieldStore("hashTable", sym1Ch, nextSymPtr1);
    b->CreateMonitoredScalarFieldStore("hashTable", sym2Ch, nextSymPtr2);
    b->CreateMonitoredScalarFieldStore("freqTable", phraseFreqCh, nextSymFreqTblPtr);
    b->CreateMonitoredScalarFieldStore("segNoTable", b->getScalarField("segIndex"), nextSymSegTblPtr);
    b->CreateStore(b->CreateTrunc(b->CreateAnd(curIndex, sz_FFFF), b->getInt16Ty()), b->getRawOutputPointer("freqUpdated", b->CreateSub(keyMarkPosCh, sz_ONE))); // AND curIndex with TABLE_MASK ??
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), nextSymPtr1, keyLengthCh); //BIGRAMDEBUGGING
    // b->CallPrintInt("keyLengthCh", keyLengthCh); //BIGRAMDEBUGGING
    // b->CallPrintInt("keyMarkPosCh", keyMarkPosCh); //BIGRAMDEBUGGING
    b->CreateBr(nextKeyCh);

    b->SetInsertPoint(checkIdxCond);
    curIndex->addIncoming(nextIndex, checkIdxCond);
    b->CreateCondBr(b->CreateICmpNE(nextIndex, endIdx), indexReady, collisionHandlingFailed);

    b->SetInsertPoint(collisionHandlingFailed);
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr1Ch, keyLengthCh); // COLLISION_STATS_SAME_SEGMENT
    // b->CallPrintInt("phraseFreqCh", phraseFreqCh) // COLLISION_STATS_SAME_SEGMENT
    // b->CallPrintInt("segIndex", b->getScalarField("segIndex")) // COLLISION_STATS_SAME_SEGMENT
    b->CreateBr(nextKeyCh);

    b->SetInsertPoint(nextKeyCh);
    Value * dropKeyCh = b->CreateResetLowestBit(theKeyWordCh);
    Value * thisWordDoneCh = b->CreateICmpEQ(dropKeyCh, sz_ZERO);
    // There may be more keys in the key mask.
    Value * nextKeyMaskCh = b->CreateSelect(thisWordDoneCh, b->CreateResetLowestBit(keyMaskPhiCh), keyMaskPhiCh);
    BasicBlock * currentBBCh = b->GetInsertBlock();
    keyMaskPhiCh->addIncoming(nextKeyMaskCh, currentBBCh);
    keyWordPhiCh->addIncoming(dropKeyCh, currentBBCh);
    b->CreateCondBr(b->CreateICmpNE(nextKeyMaskCh, sz_ZERO), collisionHandlingLoop, collisionHandlingDone);

    b->SetInsertPoint(collisionHandlingDone);
    subStNo->addIncoming(nextSubStNo, collisionHandlingDone);
    b->CreateCondBr(b->CreateICmpNE(nextSubStNo, totalSubStrides), collisionHandlingPrepLoop, symProcessingPrep);

// =================== collision handling loop end ======================

    b->SetInsertPoint(symProcessingPrep);
    PHINode * const step2subStrideNo = b->CreatePHI(sizeTy, 2, "step2subStrideNo");
    step2subStrideNo->addIncoming(sz_ZERO, collisionHandlingDone);
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
    Value * symTblIndex = b->CreateZExt(b->CreateLoad(b->getRawOutputPointer("freqUpdated", b->CreateSub(symMarkPos, sz_ONE))), sizeTy);
    Value * symSubTablePtr = b->CreateGEP(globalHashTableBasePtr, b->CreateMul(b->CreateSub(symLength, lg.LO), lg.PHRASE_SUBTABLE_SIZE));
    Value * symTableIdxHash = b->CreateAnd(/*symCodewordValFin*/symTblIndex, lg.TABLE_MASK, "tableIdx"); // >>>>>>> CHECK: AND with TABLE_MASK needed?
    Value * symIdxPtr = b->CreateGEP(symSubTablePtr, b->CreateMul(symTableIdxHash, symLength));
    Value * symTblEntryPtr = b->CreateInBoundsGEP(symIdxPtr, sz_ZERO);
    // Use two 8-byte loads to get hash and symbol values.
    Value * symTblPtr1 = b->CreateBitCast(symTblEntryPtr, lg.halfSymPtrTy);
    Value * symTblPtr2 = b->CreateBitCast(b->CreateGEP(symTblEntryPtr, symOffset), lg.halfSymPtrTy);
    Value * symPtr11 = b->CreateBitCast(b->getRawInputPointer("byteData", symStartPos), lg.halfSymPtrTy);
    Value * symPtr22 = b->CreateBitCast(b->getRawInputPointer("byteData", b->CreateAdd(symStartPos, symOffset)), lg.halfSymPtrTy);

    Value * symFreqSubTablePtr = b->CreateGEP(globalFreqTableBasePtr, b->CreateMul(b->CreateSub(symLength, lg.LO), lg.FREQ_SUBTABLE_SIZE));
    Value * symFreqTblEntryPtr = b->CreateInBoundsGEP(symFreqSubTablePtr, symTableIdxHash, "symFreqTblEntryPtr");
    Value * symFreqTblPtr = b->CreateBitCast(symFreqTblEntryPtr, sizeTy->getPointerTo());
    Value * symFreq = b->CreateMonitoredScalarFieldLoad("freqTable", symFreqTblPtr);

    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr11, symLength);
    // b->CallPrintInt("symTblIndex-read", b->CreateAnd(/*symCodewordValFin*/symTblIndex, lg.TABLE_MASK));

    // Check to see if the hash table entry is nonzero (already assigned).
    Value * sym11 = b->CreateAlignedLoad(symPtr11, 1);
    Value * sym22 = b->CreateAlignedLoad(symPtr22, 1);
    Value * entry11 = b->CreateMonitoredScalarFieldLoad("hashTable", symTblPtr1);
    Value * entry22 = b->CreateMonitoredScalarFieldLoad("hashTable", symTblPtr2);

    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr11, symLength); //BIGRAMDEBUGGING
    // b->CallPrintInt("symLength-processSym", symLength); //BIGRAMDEBUGGING
    // b->CallPrintInt("symMarkPos-processSym", symMarkPos); //BIGRAMDEBUGGING
    // b->CallPrintInt("symTableIdxHash-processSym", symTableIdxHash); //BIGRAMDEBUGGING

    // check the freq is >= minFreqReqForCmp
    Value * symIsEqEntry1 = b->CreateAnd(b->CreateICmpEQ(entry11, sym11), b->CreateICmpEQ(entry22, sym22));
    b->CreateCondBr(b->CreateAnd(b->CreateICmpUGE(symFreq, minFreqReqForCmp), symIsEqEntry1), checkSymCompression, nextSym);
    b->SetInsertPoint(checkSymCompression);
    
    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr11, symLength); //BIGRAMDEBUGGING
    // b->CallPrintInt("symLength-checkSymCompression", symLength); //BIGRAMDEBUGGING
    // b->CallPrintInt("symMarkPos-checkSymCompression", symMarkPos); //BIGRAMDEBUGGING

    // Mark the last bit of phrase
    Value * overlapConditionCheck = b->CreateICmpUGE(b->getSize(mNumSym), sz_ONE);
    b->CreateCondBr(overlapConditionCheck, continueOverlapCheck, markSymCompression);
    b->SetInsertPoint(continueOverlapCheck);

    Value * symStartBase = b->CreateSub(symStartPos, b->CreateURem(symStartPos, b->getSize(8)));
    Value * offset = b->CreateSub(symStartPos, symStartBase);
    // Value * symLenMask = b->CreateSub(b->CreateShl(sz_ONE, symLength), sz_ONE);
    Value * const outputMarkBasePtr = b->CreateBitCast(b->getRawOutputPointer("hashMarks", symStartBase), sizeTy->getPointerTo());
    Value * initialOutputMark = b->CreateAlignedLoad(outputMarkBasePtr, 1);

    // Value * curGroupMark = b->CreateOr(initialOutputMark, b->CreateShl(sz_ONE, offset)); // include current phrase's mark
    Value * sameGroupMark = initialOutputMark; // only has previously marked phrases
    sameGroupMark = b->CreateLShr(sameGroupMark, offset);
    Value * sameGrpLShrFZ = b->CreateCountForwardZeroes(sameGroupMark);
    // b->CallPrintInt("sameGrpLShrFZ", sameGrpLShrFZ); //BIGRAMDEBUGGING
    sameGrpLShrFZ = b->CreateSelect(b->CreateICmpEQ(sameGrpLShrFZ, b->getSize(64)), sz_ZERO, sameGrpLShrFZ);
    Value * sameGrpLShrFZOverlapPos = b->CreateAdd(symStartPos, sameGrpLShrFZ); // correct sym end pos for same group
    // b->CallPrintInt("sameGrpLShrFZOverlapPos", sameGrpLShrFZOverlapPos); //BIGRAMDEBUGGING
    sameGrpLShrFZOverlapPos = b->CreateSelect(b->CreateICmpEQ(sameGrpLShrFZOverlapPos, symStartPos), symMarkPos, sameGrpLShrFZOverlapPos);
    // b->CallPrintInt("sameGrpLShrFZOverlapPos-updated", sameGrpLShrFZOverlapPos); //BIGRAMDEBUGGING
    // calculate second hash here as well
    Value * sameGrpSymHash = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", sameGrpLShrFZOverlapPos)), sizeTy);
    Value * sameGrpSymLength = b->CreateAdd(b->CreateLShr(sameGrpSymHash, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET, "sameGrpSymLength");
    // Value * sameGrpSymLenMask = b->CreateSelect(b->CreateICmpEQ(sameGrpSymLength, sz_ZERO), sz_ZERO, b->CreateSub(b->CreateShl(sz_ONE, sameGrpSymLength), sz_ONE));
    Value * sameGrpStartPos = b->CreateSub(sameGrpLShrFZOverlapPos, b->CreateSub(sameGrpSymLength, sz_ONE), "sameGrpStartPos"); // position of phrase-end in the middle of current phrase

    Value * sameGrpLShrOverlapPart1 = b->CreateAnd(b->CreateICmpUGT(sameGrpStartPos, symStartPos), b->CreateICmpULE(sameGrpStartPos, symMarkPos));
    Value * sameGrpLShrOverlapPart2 = b->CreateAnd(b->CreateICmpUGT(sameGrpLShrFZOverlapPos, symStartPos), b->CreateICmpULT(sameGrpLShrFZOverlapPos, symMarkPos));

    Value * sameGrpLShrOverlap = b->CreateOr(sameGrpLShrOverlapPart1, sameGrpLShrOverlapPart2);
    // b->CallPrintInt("sameGrpLShrOverlap", sameGrpLShrOverlap); //BIGRAMDEBUGGING
    //b->CreateXor(sameGrpSymLenMask, symLenMask);

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
    // b->CallPrintInt("prevGrpLShrFZ", prevGrpLShrFZ); //BIGRAMDEBUGGING
    Value * prevGrpLShrFZOverlapPos = b->CreateAdd(symStartPos, prevGrpLShrFZ); // correct sym end pos for prev group
    // b->CallPrintInt("prevGrpLShrFZOverlapPos", prevGrpLShrFZOverlapPos); //BIGRAMDEBUGGING
    prevGrpLShrFZOverlapPos = b->CreateSelect(b->CreateICmpEQ(prevGrpLShrFZOverlapPos, symStartPos), symMarkPos, prevGrpLShrFZOverlapPos);
    // b->CallPrintInt("prevGrpLShrFZOverlapPos-updated", prevGrpLShrFZOverlapPos); //BIGRAMDEBUGGING

    Value * prevGrpSymHash = b->CreateZExt(b->CreateLoad(b->getRawInputPointer("hashValues", prevGrpLShrFZOverlapPos)), sizeTy);
    Value * prevGrpSymLength = b->CreateAdd(b->CreateLShr(prevGrpSymHash, lg.MAX_HASH_BITS), sz_PHRASE_LEN_OFFSET);
    // Value * prevGrpSymLenMask = b->CreateSelect(b->CreateICmpEQ(prevGrpSymLength, sz_ZERO), sz_ZERO, b->CreateSub(b->CreateShl(sz_ONE, prevGrpSymLength), sz_ONE));
    Value * prevGrpStartPos = b->CreateSub(prevGrpLShrFZOverlapPos, b->CreateSub(prevGrpSymLength, sz_ONE), "prevGrpStartPos");

    // Value * prevGrpMaskShiftBits = b->CreateSelect(b->CreateICmpUGT(symMarkPos, prevGrpLShrFZOverlapPos),
    //                                                b->CreateSub(symMarkPos, prevGrpLShrFZOverlapPos),
    //                                                b->CreateSub(prevGrpLShrFZOverlapPos, symMarkPos));
    // // b->CallPrintInt("prevGrpMaskShiftBits", prevGrpMaskShiftBits);
    // prevGrpSymLenMask = b->CreateSelect(b->CreateICmpUGT(symMarkPos, prevGrpLShrFZOverlapPos),
    //                                     b->CreateShl(prevGrpSymLenMask, prevGrpMaskShiftBits),
    //                                     b->CreateLShr(prevGrpSymLenMask, prevGrpMaskShiftBits));
    // Value * prevGrpLShrOverlap = b->CreateXor(prevGrpSymLenMask, symLenMask);

    // overlap happens when the start or end position of previous group phrase is in between current phrase's start and end position.
    Value * prevGrpOverlapPart1 = b->CreateAnd(b->CreateICmpUGT(prevGrpStartPos, symStartPos), b->CreateICmpULE(prevGrpStartPos, symMarkPos));
    Value * prevGrpOverlapPart2 = b->CreateAnd(b->CreateICmpUGT(prevGrpLShrFZOverlapPos, symStartPos), b->CreateICmpULT(prevGrpLShrFZOverlapPos, symMarkPos));
    Value * prevGrpLShrOverlap = b->CreateOr(prevGrpOverlapPart1, prevGrpOverlapPart2);
    // b->CallPrintInt("prevGrpLShrOverlap", prevGrpLShrOverlap); //BIGRAMDEBUGGING
    b->CreateCondBr(b->CreateICmpEQ(prevGrpLShrOverlap, b->getInt1(0)), checkSameGrpOverlap, updateFreq); //ignore previous group overlaps; do not have access to their absolute frequencies

    b->SetInsertPoint(checkSameGrpOverlap);
    b->CreateCondBr(b->CreateICmpEQ(sameGrpLShrOverlap, b->getInt1(0)), markSymCompression, updateFreq); // --------> checkUnmark);

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
// debug
    // b->CallPrintInt("sameGrpLShrFZOverlapPos", sameGrpLShrFZOverlapPos); //BIGRAMDEBUGGING
    // b->CallPrintInt("sameGrpSymLength", sameGrpSymLength); //BIGRAMDEBUGGING
    // b->CallPrintInt("sameGrpPhraseFreq", sameGrpPhraseFreq); //BIGRAMDEBUGGING

    sameGrpPhraseFreq = b->CreateMul(sameGrpPhraseFreq, sameGrpSymLength);
    Value * checkUnMarkSameGrp = b->CreateICmpUGT(sameGrpPhraseFreq, currentSymFreq);
    b->CreateCondBr(checkUnMarkSameGrp, nextSym, unMarkSameGrpPhrase);

    b->SetInsertPoint(unMarkSameGrpPhrase); // NOTE: reduces the compression ratio strangely!
    Value * base = b->CreateSub(sameGrpLShrFZOverlapPos, b->CreateURem(sameGrpLShrFZOverlapPos, sz_BITS));
    Value * overlapSymOffset = b->CreateSub(sameGrpLShrFZOverlapPos, base);
    Value * const basePtr = b->CreateBitCast(b->getRawOutputPointer("hashMarks", base), sizeTy->getPointerTo());
    Value * origMask = b->CreateAlignedLoad(basePtr, 1);
    Value * unmarkedMask = b->CreateXor(origMask, b->CreateShl(sz_ONE, overlapSymOffset));
    b->CreateAlignedStore(unmarkedMask, basePtr, 1);

    // update the hashtable frequency -> not like hashtbale is compared against segment table for future phrases. But helpful for any future segments
    // What this does: this acts like an evacuation policy?
    // PROBLEMETIC!!! ---> issue in sameGrpLShrFZOverlapPos!
    Value * tblHash = b->CreateZExt(b->CreateLoad(b->getRawOutputPointer("freqUpdated", b->CreateSub(sameGrpLShrFZOverlapPos, sz_ONE))), sizeTy);
    Value * globalSymUpdateFreqSubTablePtr = b->CreateGEP(globalFreqTableBasePtr, b->CreateMul(b->CreateSub(sameGrpSymLength, lg.LO), lg.FREQ_SUBTABLE_SIZE));
    Value * globalSymUpdateFreqTblEntryPtr = b->CreateInBoundsGEP(globalSymUpdateFreqSubTablePtr, tblHash);
    Value * globalSymUpdateFreqTblPtr = b->CreateBitCast(globalSymUpdateFreqTblEntryPtr, sizeTy->getPointerTo());
    Value * curFreq = b->CreateMonitoredScalarFieldLoad("freqTable", globalSymUpdateFreqTblPtr);
    b->CreateMonitoredScalarFieldStore("freqTable", b->CreateZExtOrTrunc(b->CreateSub(curFreq, sz_ONE), sizeTy), globalSymUpdateFreqTblPtr);
    b->CreateBr(markSymCompression);

    b->SetInsertPoint(markSymCompression);

    // b->CreateWriteCall(b->getInt32(STDERR_FILENO), symPtr11, symLength); //BIGRAMDEBUGGING
    // b->CallPrintInt("symLength-markSymCompression", symLength); //BIGRAMDEBUGGING
    // b->CallPrintInt("symMarkPos--markSymCompression", symMarkPos); //BIGRAMDEBUGGING

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
    b->CreateMemZero(phraseVectorBasePtr, b->getSize(mEncodingScheme.byLength[mGroupNo].hi * phraseVectorSize(mEncodingScheme, mGroupNo) * 
                                                    (mEncodingScheme.byLength[mGroupNo].hi - mEncodingScheme.byLength[mGroupNo].lo + 1)));
    // b->CreateMemZero(phraseFreqVecBasePtr, freqTblSize);

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
    b->CreateCondBr(b->isFinal(), hashMarksDone, updatePending);

    b->SetInsertPoint(updatePending);
    Value * pendingPtr = b->CreateBitCast(b->getRawOutputPointer("hashMarks", produced), bitBlockPtrTy);
    Value * lastMask = b->CreateBlockAlignedLoad(pendingPtr);
    b->setScalarField("pendingMaskInverted", b->CreateNot(lastMask));
    b->CreateBr(hashMarksDone);
    b->SetInsertPoint(hashMarksDone);
}
