
#include "common.h"
#include <boost/intrusive/detail/math.hpp>
#include <llvm/Support/CommandLine.h>

using namespace kernel;
using namespace llvm;

static cl::opt<bool> DeferredAttribute("deferred", cl::desc("Use Deferred attribute instead of Lookbehind for source data"), cl::init(false));
static cl::opt<bool> DelayedAttribute("delayed", cl::desc("Use Delayed Attribute instead of BoundedRate for output"), cl::init(true));
static cl::opt<bool> PrefixCheck("prefix-check-mode", cl::desc("Use experimental prefix check mode"), cl::init(false));

bool LLVM_READONLY DeferredAttributeIsSet() {
    return DeferredAttribute;
}

bool LLVM_READONLY DelayedAttributeIsSet() {
    return DelayedAttribute;
}

bool LLVM_READONLY PrefixCheckIsSet() {
    return PrefixCheck;
}

using BuilderRef = Kernel::BuilderRef;

ScanWordParameters::ScanWordParameters(BuilderRef b, unsigned stride) :
#ifdef PREFER_NARROW_SCANWIDTH
    width(std::max(BITS_PER_BYTE, stride/SIZE_T_BITS)),
#else
    width(std::min(SIZE_T_BITS, stride/BITS_PER_BYTE)),
#endif
    indexWidth(stride/width),
    Ty(b->getIntNTy(width)),
    pointerTy(Ty->getPointerTo()),
    WIDTH(b->getSize(width)),
    ix_MAXBIT(b->getSize(indexWidth - 1)),
    WORDS_PER_BLOCK(b->getSize(b->getBitBlockWidth()/width)),
    WORDS_PER_STRIDE(b->getSize(indexWidth))
    {   //  The stride must be a power of 2 and a multiple of the BitBlock width.
        //assert((((stride & (stride - 1)) == 0) && (stride >= b->getBitBlockWidth()) && (stride <= SIZE_T_BITS * SIZE_T_BITS)));
    }

LengthGroupParameters::LengthGroupParameters(BuilderRef b, EncodingInfo encodingScheme, unsigned groupNo, unsigned numSym) :
    groupInfo(encodingScheme.byLength[groupNo]),
    MAX_HASH_BITS(b->getSize(encodingScheme.MAX_HASH_BITS)),
    HASH_SHIFT_BITS(b->getSize(7)),
    SEC_LAST_SFX(b->getSize(encodingScheme.secLastSuffixShiftBits(numSym, groupNo))),
    SUFFIX_BITS(b->getSize(7)),
    SUFFIX_MASK(b->getSize(0x7F)),
    LAST_SUFFIX_BASE(b->getSize(encodingScheme.lastSuffixBase(groupNo, numSym))),
    SEC_LAST_SUFFIX_BASE(b->getSize(encodingScheme.secLastSuffixBase(groupNo, numSym))),
    LAST_SUFFIX_SHIFT_BITS(b->getSize(encodingScheme.lastSuffixShiftBits(groupNo, numSym))),
    LAST_SUFFIX_MASK(b->getSize((1UL << encodingScheme.lastSuffixHashBits(numSym, groupNo)) - 1)),
    SEC_LAST_SUFFIX_MASK(b->getSize((1UL << encodingScheme.secLastSuffixHashBits(numSym, groupNo)) - 1)),
    groupHalfLength(1UL << boost::intrusive::detail::floor_log2(groupInfo.lo)),
    halfLengthTy(b->getIntNTy(8U * groupHalfLength)),
    halfSymPtrTy(halfLengthTy->getPointerTo()),
    symLengthTy(b->getIntNTy(8U * (1UL << groupInfo.hi))),
    symLengthPtrTy(symLengthTy->getPointerTo()),
    HALF_LENGTH(b->getSize(groupHalfLength)),
    LO(b->getSize(groupInfo.lo)),
    HI(b->getSize(groupInfo.hi)),
    RANGE(b->getSize(encodingScheme.getRange(groupNo))),
    // All subtables are sized the same.
    SUBTABLE_SIZE(b->getSize((1UL << groupInfo.hash_bits) * groupInfo.hi)),
    PHRASE_SUBTABLE_SIZE(b->getSize(encodingScheme.getSubtableSize(groupNo, numSym))),
    FREQ_SUBTABLE_SIZE(b->getSize(encodingScheme.getFreqSubtableSize(groupNo, numSym))),
    HASH_BITS(b->getSize(groupInfo.hash_bits)),
    EXTENDED_BITS(b->getSize(std::max((groupInfo.hash_bits + groupInfo.length_extension_bits), ((groupInfo.encoding_bytes - 1U) * 7U)))),
    PHRASE_EXTENSION_MASK(b->getSize(( 1UL << encodingScheme.getPhraseExtensionBits(groupNo, encodingScheme.byLength.size())) - 1UL)),
    HASH_MASK(b->getSize((1UL << ((groupInfo.hash_bits >> 1UL) * groupInfo.encoding_bytes)) - 1UL)),
    HASH_MASK_NEW(b->getSize((1UL << ((groupInfo.hash_bits) * groupInfo.encoding_bytes)) - 1UL)),
    ENC_BYTES(b->getSize(groupInfo.encoding_bytes)),
    MAX_INDEX(b->getSize(groupInfo.encoding_bytes - 1UL)),
    PREFIX_BASE(b->getSize(encodingScheme.getPfxBase(groupNo, numSym))),
    PREFIX_LENGTH_OFFSET(b->getSize(encodingScheme.prefixLengthOffset(groupInfo.lo))),
    PREFIX_LENGTH_MASK(b->getSize((1UL << encodingScheme.prefixLengthMaskBits(groupInfo.lo, numSym)) - 1UL)),
    LENGTH_MASK(b->getSize(2UL * groupHalfLength - 1UL)),
    EXTENSION_MASK(b->getSize((1UL << groupInfo.length_extension_bits) - 1UL)),
    TABLE_MASK(b->getSize((1U << encodingScheme.tableSizeBits(groupNo, numSym)) -1)),
    EXTRA_BITS(b->getSize(encodingScheme.tableSizeBits(groupNo, /*numSym = */ 0) % 7U)),
    EXTRA_BITS_MASK(b->getSize((1UL << (encodingScheme.tableSizeBits(groupNo, /*numSym = */ 0) % 7U)) - 1UL)),
    TABLE_IDX_MASK(b->getSize((1U << (8 * groupInfo.encoding_bytes)) -1)),
    FREQ_TABLE_MASK(b->getSize((1UL << (18U - groupNo)) - 1)) {
        // llvm::errs() << groupNo << " ->TABLE_MASK : " << ((1U << encodingScheme.tableSizeBits(groupNo)) -1 ) << "\n";
        // llvm::errs() << groupNo << " ->EXTRA_BITS " << (encodingScheme.tableSizeBits(groupNo) % 7U) << "\n";
        // llvm::errs() << groupNo << " ->EXTRA_BITS_MASK " << ((1UL << (encodingScheme.tableSizeBits(groupNo) % 7U)) - 1UL) << "\n";
        assert(groupInfo.hi <= (1UL << (boost::intrusive::detail::floor_log2(groupInfo.lo) + 1UL)));
    }

unsigned hashTableSize(LengthGroupInfo g) {
    unsigned numSubTables = (g.hi - g.lo + 1);
    return numSubTables * g.hi * (1<<g.hash_bits);
}

unsigned phraseHashSubTableSize(EncodingInfo encodingScheme, unsigned groupNo, unsigned numSym) {
    if (numSym == 0) {
        switch(groupNo) {
            case 0: return 4096;
            break;
            case 1: return 32768;
            break;
            case 2: return 16384;
            break;
            case 3: return 16384;
            break;
        }
    }
    else {
        switch(groupNo) {
            case 0: return 0; // not done
            break;
            case 1: return 16384;
            break;
            case 2: return 8192;
            break;
            case 3: return 8192;
            break;
        }
    }
}

unsigned phraseVectorSize(EncodingInfo encodingScheme, unsigned groupNo) {
    LengthGroupInfo g = encodingScheme.byLength[groupNo];
    return (1048576 / g.hi);
}
unsigned phraseHashTableSize(LengthGroupInfo g) {
    // llvm::errs() << "lo " << g.lo << "phraseHashTableSize " <<  g.hi * (1<<(g.hash_bits + g.encoding_bytes)) << "\n";
    return g.hi * (1<<(g.hash_bits + g.encoding_bytes));
}

unsigned freqTableSize(LengthGroupInfo g) {
    unsigned numSubTables = (g.hi - g.lo + 1);
    if (g.hi - g.lo == 0) {
        numSubTables *= 5;
    }
    return numSubTables * g.hi * (1<<(g.hash_bits + g.encoding_bytes));
}

std::string lengthRangeSuffix(EncodingInfo encodingScheme, unsigned lo, unsigned hi) {
    std::stringstream suffix;
    suffix << encodingScheme.uniqueSuffix() << "_" << lo << "_" << hi;
    if (DeferredAttributeIsSet()) suffix << "deferred";
    if (DelayedAttributeIsSet()) suffix << "_delayed";
    return suffix.str();
}

std::string lengthGroupSuffix(EncodingInfo encodingScheme, unsigned groupNo) {
    LengthGroupInfo g = encodingScheme.byLength[groupNo];
    return lengthRangeSuffix(encodingScheme, g.lo, g.hi);
}

// indicate which block contain a symbol to be considered for compression
// skip the block that does not contain any symbol
std::vector<Value *> initializeCompressionMasks(BuilderRef b,
                                                ScanWordParameters & sw,
                                                Constant * sz_BLOCKS_PER_STRIDE,
                                                unsigned maskCount,
                                                Value * strideBlockOffset,
                                                Value * compressMaskPtr,
                                                BasicBlock * strideMasksReady) {
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Type * sizeTy = b->getSizeTy();
    std::vector<Value *> keyMasks(maskCount);
    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const maskInitialization = b->CreateBasicBlock("maskInitialization");
    b->CreateBr(maskInitialization);
    b->SetInsertPoint(maskInitialization);
    std::vector<PHINode *> keyMaskAccum(maskCount);
    for (unsigned i = 0; i < maskCount; i++) {
        keyMaskAccum[i] = b->CreatePHI(sizeTy, 2);
        keyMaskAccum[i]->addIncoming(sz_ZERO, entryBlock);
    }
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2);
    blockNo->addIncoming(sz_ZERO, entryBlock);
    Value * strideBlockIndex = b->CreateAdd(strideBlockOffset, blockNo);
    for (unsigned i = 0; i < maskCount; i++) {
        Value * keyBitBlock = b->loadInputStreamBlock("symbolMarks" + (i > 0 ? std::to_string(i) : ""), sz_ZERO, strideBlockIndex);
        Value * const anyKey = b->simd_any(sw.width, keyBitBlock);
        Value * keyWordMask = b->CreateZExtOrTrunc(b->hsimd_signmask(sw.width, anyKey), sizeTy);
        //b->CallPrintRegister("keyBitBlock", keyBitBlock);
        //b->CallPrintRegister("anyKey", anyKey);
        //b->CallPrintInt("keyWordMask", keyWordMask);
        // number of symbols in a block at 64 bit boundaries
        keyMasks[i] = b->CreateOr(keyMaskAccum[i], b->CreateShl(keyWordMask, b->CreateMul(blockNo, sw.WORDS_PER_BLOCK)));
        //b->CallPrintInt("keyMasks"+std::to_string(i), keyMasks[i]);
        keyMaskAccum[i]->addIncoming(keyMasks[i], maskInitialization);
    }
    // Initialize the compression mask.
    // Default initial compression mask is all ones (no zeroes => no compression).
    b->CreateBlockAlignedStore(b->allOnes(), b->CreateGEP(compressMaskPtr, strideBlockIndex));
    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    blockNo->addIncoming(nextBlockNo, maskInitialization);
    // Default initial compression mask is all ones (no zeroes => no compression).
    b->CreateCondBr(b->CreateICmpNE(nextBlockNo, sz_BLOCKS_PER_STRIDE), maskInitialization, strideMasksReady);
    return keyMasks;
}

std::vector<Value *> initializeCompressionMasks(BuilderRef b,
                                                ScanWordParameters & sw,
                                                Constant * sz_BLOCKS_PER_STRIDE,
                                                unsigned maskCount,
                                                Value * absBlockOffset,
                                                Value * compressMaskPtr,
                                                Value * phraseMaskPtr,
                                                BasicBlock * strideMasksReady) {
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    Type * sizeTy = b->getSizeTy();
    Type * bitBlockPtrTy = b->getBitBlockType()->getPointerTo();
    std::vector<Value *> keyMasks(maskCount);
    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const maskInitialization = b->CreateBasicBlock("maskInitialization");
    Value * const absoluteProcessed = b->CreateMul(absBlockOffset, sz_BLOCKWIDTH);
    Value * const lastBlockToProcess = b->CreateAdd(absoluteProcessed, b->CreateMul(sz_BLOCKS_PER_STRIDE, sz_BLOCKWIDTH));
    b->CreateBr(maskInitialization);
    b->SetInsertPoint(maskInitialization);
    std::vector<PHINode *> keyMaskAccum(maskCount);
    for (unsigned i = 0; i < maskCount; i++) {
        keyMaskAccum[i] = b->CreatePHI(sizeTy, 2);
        keyMaskAccum[i]->addIncoming(sz_ZERO, entryBlock);
    }
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2);
    blockNo->addIncoming(sz_ZERO, entryBlock);
    PHINode * const blockPos = b->CreatePHI(sizeTy, 2, "blockPos");
    blockPos->addIncoming(absoluteProcessed, entryBlock);
    for (unsigned i = 0; i < maskCount; i++) {
        Value * keyBitBlockPtr = b->CreateBitCast(b->getRawInputPointer("symbolMarks" + (i > 0 ? std::to_string(i) : ""), blockPos), bitBlockPtrTy);
        Value * keyBitBlock = b->CreateBlockAlignedLoad(keyBitBlockPtr);
        Value * const anyKey = b->simd_any(sw.width, keyBitBlock);
        Value * keyWordMask = b->CreateZExtOrTrunc(b->hsimd_signmask(sw.width, anyKey), sizeTy);
        //b->CallPrintRegister("keyBitBlock", keyBitBlock);
        //b->CallPrintRegister("anyKey", anyKey);
        //b->CallPrintInt("keyWordMask", keyWordMask);
        // number of symbols in a block at 64 bit boundaries
        keyMasks[i] = b->CreateOr(keyMaskAccum[i], b->CreateShl(keyWordMask, b->CreateMul(blockNo, sw.WORDS_PER_BLOCK)));
        //b->CallPrintInt("keyMasks"+std::to_string(i), keyMasks[i]);
        keyMaskAccum[i]->addIncoming(keyMasks[i], maskInitialization);
    }
    // Initialize the compression mask.
    // Default initial compression mask is all ones (no zeroes => no compression).
    Value * compressMaskCurPtr = b->CreateBitCast(b->getRawOutputPointer("compressionMask", blockPos), bitBlockPtrTy);
    Value * phraseMaskCurPtr = b->CreateBitCast(b->getRawOutputPointer("codewordMask", blockPos), bitBlockPtrTy);
    b->CreateBlockAlignedStore(b->allOnes(), compressMaskCurPtr);
    b->CreateBlockAlignedStore(b->allZeroes(), phraseMaskCurPtr);

    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    Value * const nextBlockPos = b->CreateAdd(blockPos, sz_BLOCKWIDTH);
    blockNo->addIncoming(nextBlockNo, maskInitialization);
    blockPos->addIncoming(nextBlockPos, maskInitialization);
    // Default initial compression mask is all ones (no zeroes => no compression).
    b->CreateCondBr(b->CreateICmpNE(nextBlockPos, lastBlockToProcess), maskInitialization, strideMasksReady);
    return keyMasks;
}

// TODO: Parameterize initializeCompressionMasks1 and initializeCompressionMasks11
std::vector<Value *> initializeCompressionMasks1(BuilderRef b,
                                                ScanWordParameters & sw,
                                                Constant * sz_BLOCKS_PER_STRIDE,
                                                unsigned maskCount,
                                                Value * strideBlockOffset,
                                                BasicBlock * strideMasksReady) {
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Type * sizeTy = b->getSizeTy();
    std::vector<Value *> keyMasks(maskCount);
    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const maskInitialization = b->CreateBasicBlock("maskInitialization");
    b->CreateBr(maskInitialization);
    b->SetInsertPoint(maskInitialization);
    std::vector<PHINode *> keyMaskAccum(maskCount);
    for (unsigned i = 0; i < maskCount; i++) {
        keyMaskAccum[i] = b->CreatePHI(sizeTy, 2);
        keyMaskAccum[i]->addIncoming(sz_ZERO, entryBlock);
    }
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2);
    blockNo->addIncoming(sz_ZERO, entryBlock);

    Value * strideBlockIndex = b->CreateAdd(strideBlockOffset, blockNo);
    for (unsigned i = 0; i < maskCount; i++) {
        Value * keyBitBlock = b->loadInputStreamBlock("phraseMask" + (i > 0 ? std::to_string(i) : ""), sz_ZERO, strideBlockIndex);//b->CreateBlockAlignedLoad(keyBitBlockPtr);
        Value * const anyKey = b->simd_any(sw.width, keyBitBlock);
        Value * keyWordMask = b->CreateZExtOrTrunc(b->hsimd_signmask(sw.width, anyKey), sizeTy);
        // number of symbols in a block at 64 bit boundaries
        keyMasks[i] = b->CreateOr(keyMaskAccum[i], b->CreateShl(keyWordMask, b->CreateMul(blockNo, sw.WORDS_PER_BLOCK)));
        keyMaskAccum[i]->addIncoming(keyMasks[i], maskInitialization);
    }
    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    blockNo->addIncoming(nextBlockNo, maskInitialization);
    b->CreateCondBr(b->CreateICmpNE(nextBlockNo, sz_BLOCKS_PER_STRIDE), maskInitialization, strideMasksReady);
    return keyMasks;
}

std::vector<Value *> initializeCompressionMasks11(BuilderRef b,
                                                ScanWordParameters & sw,
                                                Constant * sz_BLOCKS_PER_STRIDE,
                                                unsigned maskCount,
                                                Value * absBlockOffset,
                                                BasicBlock * strideMasksReady) {
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    Type * sizeTy = b->getSizeTy();
    Type * bitBlockPtrTy = b->getBitBlockType()->getPointerTo();
    std::vector<Value *> keyMasks(maskCount);
    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const maskInitialization = b->CreateBasicBlock("maskInitialization");
    Value * const absoluteProcessed = b->CreateMul(absBlockOffset, sz_BLOCKWIDTH);
    b->CreateBr(maskInitialization);
    b->SetInsertPoint(maskInitialization);
    std::vector<PHINode *> keyMaskAccum(maskCount);
    for (unsigned i = 0; i < maskCount; i++) {
        keyMaskAccum[i] = b->CreatePHI(sizeTy, 2);
        keyMaskAccum[i]->addIncoming(sz_ZERO, entryBlock);
    }
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2);
    blockNo->addIncoming(sz_ZERO, entryBlock);
    PHINode * const blockPos = b->CreatePHI(sizeTy, 2, "blockPos");
    blockPos->addIncoming(absoluteProcessed, entryBlock);
    for (unsigned i = 0; i < maskCount; i++) {
        Value * keyBitBlockPtr = b->CreateBitCast(b->getRawInputPointer("phraseMask" + (i > 0 ? std::to_string(i) : ""), blockPos), bitBlockPtrTy);
        Value * keyBitBlock = b->CreateBlockAlignedLoad(keyBitBlockPtr);
        Value * const anyKey = b->simd_any(sw.width, keyBitBlock);
        Value * keyWordMask = b->CreateZExtOrTrunc(b->hsimd_signmask(sw.width, anyKey), sizeTy);
        // number of symbols in a block at 64 bit boundaries
        keyMasks[i] = b->CreateOr(keyMaskAccum[i], b->CreateShl(keyWordMask, b->CreateMul(blockNo, sw.WORDS_PER_BLOCK)));
        keyMaskAccum[i]->addIncoming(keyMasks[i], maskInitialization);
    }
    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    Value * const nextBlockPos = b->CreateAdd(blockPos, sz_BLOCKWIDTH);
    blockNo->addIncoming(nextBlockNo, maskInitialization);
    blockPos->addIncoming(nextBlockPos, maskInitialization);
    b->CreateCondBr(b->CreateICmpNE(nextBlockNo, sz_BLOCKS_PER_STRIDE), maskInitialization, strideMasksReady);
    return keyMasks;
}

std::vector<Value *> initializeCompressionMasks2(BuilderRef b,
                                                ScanWordParameters & sw,
                                                Constant * sz_BLOCKS_PER_STRIDE,
                                                unsigned maskCount,
                                                Value * absBlockOffset,
                                                Value * dictMaskPtr,
                                                BasicBlock * strideMasksReady) {
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Constant * sz_BLOCKWIDTH = b->getSize(b->getBitBlockWidth());
    Type * sizeTy = b->getSizeTy();
    Type * bitBlockPtrTy = b->getBitBlockType()->getPointerTo();
    std::vector<Value *> keyMasks(maskCount);
    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const maskInit = b->CreateBasicBlock("maskInit");

    Value * const absoluteProcessed = b->CreateMul(absBlockOffset, sz_BLOCKWIDTH);
    // b->CallPrintInt("absoluteProcessed", absoluteProcessed);
    Value * const lastBlockToProcess = b->CreateAdd(absoluteProcessed, b->CreateMul(sz_BLOCKS_PER_STRIDE, sz_BLOCKWIDTH));
    // b->CallPrintInt("lastBlockToProcess", lastBlockToProcess);

    b->CreateBr(maskInit);
    b->SetInsertPoint(maskInit);
    std::vector<PHINode *> keyMaskAccum(maskCount);
    for (unsigned i = 0; i < maskCount; i++) {
        keyMaskAccum[i] = b->CreatePHI(sizeTy, 2);
        keyMaskAccum[i]->addIncoming(sz_ZERO, entryBlock);
    }
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2);
    blockNo->addIncoming(sz_ZERO, entryBlock);
    PHINode * const blockPos = b->CreatePHI(sizeTy, 2, "blockPos");
    blockPos->addIncoming(absoluteProcessed, entryBlock);

    for (unsigned i = 0; i < maskCount; i++) {
        Value * keyBitBlockPtr = b->CreateBitCast(b->getRawInputPointer("symEndMarks" + (i > 0 ? std::to_string(i) : ""), blockPos), bitBlockPtrTy);
        Value * keyBitBlock = b->CreateBlockAlignedLoad(keyBitBlockPtr);
        Value * const anyKey = b->simd_any(sw.width, keyBitBlock);
        Value * keyWordMask = b->CreateZExtOrTrunc(b->hsimd_signmask(sw.width, anyKey), sizeTy);
        // number of symbols in a block at 64 bit boundaries
        keyMasks[i] = b->CreateOr(keyMaskAccum[i], b->CreateShl(keyWordMask, b->CreateMul(blockNo, sw.WORDS_PER_BLOCK)));
        keyMaskAccum[i]->addIncoming(keyMasks[i], maskInit);
    }
    Value * dictMaskCurPtr = b->CreateBitCast(b->getRawOutputPointer("hashMarks", blockPos), bitBlockPtrTy);
    b->CreateBlockAlignedStore(b->allZeroes(), dictMaskCurPtr);
    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    Value * const nextBlockPos = b->CreateAdd(blockPos, sz_BLOCKWIDTH);
    blockNo->addIncoming(nextBlockNo, maskInit);
    blockPos->addIncoming(nextBlockPos, maskInit);
    b->CreateCondBr(b->CreateICmpNE(nextBlockPos, lastBlockToProcess), maskInit, strideMasksReady);
    return keyMasks;
}

void initializeDecompressionMasks(BuilderRef b,
                                  ScanWordParameters & sw,
                                  Constant * sz_BLOCKS_PER_STRIDE,
                                  unsigned maskCount,
                                  Value * strideBlockOffset,
                                  std::vector<Value *> & keyMasks,
                                  std::vector<Value *> & hashMasks,
                                  BasicBlock * strideMasksReady) {
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Type * sizeTy = b->getSizeTy();
    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const maskInitialization = b->CreateBasicBlock("maskInitialization");
    b->CreateBr(maskInitialization);
    b->SetInsertPoint(maskInitialization);
    std::vector<PHINode *> keyMaskAccum(maskCount);
    std::vector<PHINode *> hashMaskAccum(maskCount);
    for (unsigned i = 0; i < maskCount; i++) {
        keyMaskAccum[i] = b->CreatePHI(sizeTy, 2);
        hashMaskAccum[i] = b->CreatePHI(sizeTy, 2);
        keyMaskAccum[i]->addIncoming(sz_ZERO, entryBlock);
        hashMaskAccum[i]->addIncoming(sz_ZERO, entryBlock);
    }
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2);
    blockNo->addIncoming(sz_ZERO, entryBlock);
    Value * strideBlockIndex = b->CreateAdd(strideBlockOffset, blockNo);
    for (unsigned i = 0; i < maskCount; i++) {
        Value * keyBitBlock = b->loadInputStreamBlock("keyMarks" + std::to_string(i), sz_ZERO, strideBlockIndex);
        Value * hashBitBlock = b->loadInputStreamBlock("hashMarks" + std::to_string(i), sz_ZERO, strideBlockIndex);
        Value * const anyKey = b->simd_any(sw.width, keyBitBlock);
        Value * const anyHash = b->simd_any(sw.width, hashBitBlock);
        Value * keyWordMask = b->CreateZExtOrTrunc(b->hsimd_signmask(sw.width, anyKey), sizeTy);
        Value * hashWordMask = b->CreateZExtOrTrunc(b->hsimd_signmask(sw.width, anyHash), sizeTy);
        keyMasks[i] = b->CreateOr(keyMaskAccum[i], b->CreateShl(keyWordMask, b->CreateMul(blockNo, sw.WORDS_PER_BLOCK)));
        hashMasks[i] = b->CreateOr(hashMaskAccum[i], b->CreateShl(hashWordMask, b->CreateMul(blockNo, sw.WORDS_PER_BLOCK)));
        keyMaskAccum[i]->addIncoming(keyMasks[i], maskInitialization);
        hashMaskAccum[i]->addIncoming(hashMasks[i], maskInitialization);
    }
    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    blockNo->addIncoming(nextBlockNo, maskInitialization);
    // Default initial compression mask is all ones (no zeroes => no compression).
    b->CreateCondBr(b->CreateICmpNE(nextBlockNo, sz_BLOCKS_PER_STRIDE), maskInitialization, strideMasksReady);
}

void initializeCodeWordMasks(BuilderRef b,
                             struct ScanWordParameters & sw,
                             Constant * sz_BLOCKS_PER_STRIDE,
                             unsigned maskCount,
                             Value * strideBlockOffset,
                             std::vector<Value *> & keyMasks0,
                             std::vector<Value *> & keyMasks1,
                             std::vector<Value *> & hashMasks,
                             BasicBlock * strideMasksReady) {
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Type * sizeTy = b->getSizeTy();
    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const maskInitialization = b->CreateBasicBlock("maskInitialization");
    b->CreateBr(maskInitialization);
    b->SetInsertPoint(maskInitialization);
    std::vector<PHINode *> keyMask0Accum(maskCount);
    std::vector<PHINode *> keyMask1Accum(maskCount);
    std::vector<PHINode *> hashMaskAccum(maskCount);
    for (unsigned i = 0; i < maskCount; i++) {
        keyMask0Accum[i] = b->CreatePHI(sizeTy, 2);
        keyMask1Accum[i] = b->CreatePHI(sizeTy, 2);
        hashMaskAccum[i] = b->CreatePHI(sizeTy, 2);
        keyMask0Accum[i]->addIncoming(sz_ZERO, entryBlock);
        keyMask1Accum[i]->addIncoming(sz_ZERO, entryBlock);
        hashMaskAccum[i]->addIncoming(sz_ZERO, entryBlock);
    }
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2);
    blockNo->addIncoming(sz_ZERO, entryBlock);
    Value * strideBlockIndex = b->CreateAdd(strideBlockOffset, blockNo);
    for (unsigned i = 0; i < maskCount; i++) {
        Value * key0BitBlock = b->loadInputStreamBlock("keyMarks0" + std::to_string(i), sz_ZERO, strideBlockIndex);
        Value * key1BitBlock = b->loadInputStreamBlock("keyMarks1" + std::to_string(i), sz_ZERO, strideBlockIndex);
        Value * hashBitBlock = b->loadInputStreamBlock("hashMarks" + std::to_string(i), sz_ZERO, strideBlockIndex);
        Value * const anyKey0 = b->simd_any(sw.width, key0BitBlock);
        Value * const anyKey1 = b->simd_any(sw.width, key1BitBlock);
        Value * const anyHash = b->simd_any(sw.width, hashBitBlock);
        Value * key0WordMask = b->CreateZExtOrTrunc(b->hsimd_signmask(sw.width, anyKey0), sizeTy);
        Value * key1WordMask = b->CreateZExtOrTrunc(b->hsimd_signmask(sw.width, anyKey1), sizeTy);
        Value * hashWordMask = b->CreateZExtOrTrunc(b->hsimd_signmask(sw.width, anyHash), sizeTy);
        keyMasks0[i] = b->CreateOr(keyMask0Accum[i], b->CreateShl(key0WordMask, b->CreateMul(blockNo, sw.WORDS_PER_BLOCK)));
        keyMasks1[i] = b->CreateOr(keyMask1Accum[i], b->CreateShl(key1WordMask, b->CreateMul(blockNo, sw.WORDS_PER_BLOCK)));
        hashMasks[i] = b->CreateOr(hashMaskAccum[i], b->CreateShl(hashWordMask, b->CreateMul(blockNo, sw.WORDS_PER_BLOCK)));
        keyMask0Accum[i]->addIncoming(keyMasks0[i], maskInitialization);
        keyMask1Accum[i]->addIncoming(keyMasks1[i], maskInitialization);
        hashMaskAccum[i]->addIncoming(hashMasks[i], maskInitialization);
    }
    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    blockNo->addIncoming(nextBlockNo, maskInitialization);
    // Default initial compression mask is all ones (no zeroes => no compression).
    b->CreateCondBr(b->CreateICmpNE(nextBlockNo, sz_BLOCKS_PER_STRIDE), maskInitialization, strideMasksReady);
}

void initializeOutputMasks(BuilderRef b,
                           ScanWordParameters & sw,
                           Constant * sz_BLOCKS_PER_STRIDE,
                           Value * strideBlockOffset,
                           Value * outputMaskPtr,
                           BasicBlock * outputMasksReady) {
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Type * sizeTy = b->getSizeTy();
    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const maskInit = b->CreateBasicBlock("maskInit");
    b->CreateBr(maskInit);

    b->SetInsertPoint(maskInit);
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2);
    blockNo->addIncoming(sz_ZERO, entryBlock);
    Value * strideBlockIndex = b->CreateAdd(strideBlockOffset, blockNo);
    b->CreateBlockAlignedStore(b->allZeroes(), b->CreateGEP(outputMaskPtr, strideBlockIndex));
    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    blockNo->addIncoming(nextBlockNo, maskInit);
    b->CreateCondBr(b->CreateICmpNE(nextBlockNo, sz_BLOCKS_PER_STRIDE), maskInit, outputMasksReady);
}

Value * getLastLineBreakPos(BuilderRef b,
                           ScanWordParameters & sw,
                           Constant * sz_BLOCKWIDTH,
                           Value * sz_BLOCKS_PER_STRIDE,
                           Value * absBlockOffset,
                           BasicBlock * lbPosCalculated) {
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Type * sizeTy = b->getSizeTy();
    Type * bitBlockPtrTy = b->getBitBlockType()->getPointerTo();
    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const maskInit = b->CreateBasicBlock("maskInit");

    Value * const absoluteProcessed = b->CreateMul(absBlockOffset, sz_BLOCKWIDTH);
    Value * const lastBlockToProcess = b->CreateAdd(absoluteProcessed, b->CreateMul(sz_BLOCKS_PER_STRIDE, sz_BLOCKWIDTH));
    b->CreateBr(maskInit);

    b->SetInsertPoint(maskInit);
    PHINode * const blockPos = b->CreatePHI(sizeTy, 2, "blockPos");
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2, "blockNo");
    PHINode * const lineBreakPos = b->CreatePHI(sizeTy, 2, "lineBreakPos");
    blockPos->addIncoming(absoluteProcessed, entryBlock);
    blockNo->addIncoming(sz_ZERO, entryBlock);
    lineBreakPos->addIncoming(sz_ZERO, entryBlock);
    Value * const nextBlockPos = b->CreateAdd(blockPos, sz_BLOCKWIDTH);
    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    Value * blockOffset = b->CreateMul(blockNo, sz_BLOCKWIDTH);
    // cases:
    // 1. there is/are linebreaks in the bitblock -> add to lbPos the position of the last line break ([blockPos * blockSize] + lastLineBreakPosInBitblock)
    // 2. No linebreaks in the bitblock -> add blockSize to lbPos

    Value * lineBitBlockPtr = b->CreateBitCast(b->getRawInputPointer("lineBreaks", blockPos), bitBlockPtrTy);
    Value * lineBitBlock = b->CreateBlockAlignedLoad(lineBitBlockPtr);
    Value * const lastLB = b->simd_ctlz(b->getBitBlockWidth(), lineBitBlock);
    Value * lbPos = b->CreateZExtOrTrunc(b->CreateExtractElement(b->fwCast(16, lastLB), b->getInt32(0)), sizeTy);
    // b->CallPrintInt("lbPos", lbPos);
    // update lineBreakPos only when a new linebreak is seen in the bitblock
    Value * newLinebreakPos = b->CreateSelect(b->CreateICmpEQ(lbPos, sz_BLOCKWIDTH), lineBreakPos, b->CreateAdd(blockOffset, b->CreateSub(sz_BLOCKWIDTH, lbPos)));
    lineBreakPos->addIncoming(newLinebreakPos, maskInit);
    blockPos->addIncoming(nextBlockPos, maskInit);
    blockNo->addIncoming(nextBlockNo, maskInit);
    b->CreateCondBr(b->CreateICmpNE(nextBlockPos, lastBlockToProcess), maskInit, lbPosCalculated);
    return newLinebreakPos;
}

void initializeLinebreakMasks(BuilderRef b,
                                  ScanWordParameters & sw,
                                  Constant * sz_BLOCKS_PER_STRIDE,
                                  unsigned maskCount,
                                  Value * strideBlockOffset,
                                  std::vector<Value *> & keyMasks,
                                  BasicBlock * strideMasksReady) {
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Type * sizeTy = b->getSizeTy();
    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const maskInitialization = b->CreateBasicBlock("maskInitialization");
    b->CreateBr(maskInitialization);
    b->SetInsertPoint(maskInitialization);
    std::vector<PHINode *> keyMaskAccum(maskCount);
    for (unsigned i = 0; i < maskCount; i++) {
        keyMaskAccum[i] = b->CreatePHI(sizeTy, 2);
        keyMaskAccum[i]->addIncoming(sz_ZERO, entryBlock);
    }
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2);
    blockNo->addIncoming(sz_ZERO, entryBlock);
    Value * strideBlockIndex = b->CreateAdd(strideBlockOffset, blockNo);
    for (unsigned i = 0; i < maskCount; i++) {
        Value * keyBitBlock = b->loadInputStreamBlock("lineBreaks" + (i > 0 ? std::to_string(i) : ""), sz_ZERO, strideBlockIndex);
        Value * const anyKey = b->simd_any(sw.width, keyBitBlock);
        Value * keyWordMask = b->CreateZExtOrTrunc(b->hsimd_signmask(sw.width, anyKey), sizeTy);
        keyMasks[i] = b->CreateOr(keyMaskAccum[i], b->CreateShl(keyWordMask, b->CreateMul(blockNo, sw.WORDS_PER_BLOCK)));
        keyMaskAccum[i]->addIncoming(keyMasks[i], maskInitialization);
    }
    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    blockNo->addIncoming(nextBlockNo, maskInitialization);
    // Default initial compression mask is all ones (no zeroes => no compression).
    b->CreateCondBr(b->CreateICmpNE(nextBlockNo, sz_BLOCKS_PER_STRIDE), maskInitialization, strideMasksReady);
}

Value * getSegBoundaryPos(BuilderRef b,
                           ScanWordParameters & sw,
                           Constant * sz_BLOCKWIDTH,
                           Constant * sz_BLOCKS_PER_STRIDE,
                           Value * strideBlockOffset,
                           BasicBlock * segEndCalculated) {
    Constant * sz_ZERO = b->getSize(0);
    Constant * sz_ONE = b->getSize(1);
    Type * sizeTy = b->getSizeTy();
    BasicBlock * const entryBlock = b->GetInsertBlock();
    BasicBlock * const maskInit = b->CreateBasicBlock("maskInit");
    b->CreateBr(maskInit);

    b->SetInsertPoint(maskInit);
    PHINode * const blockNo = b->CreatePHI(sizeTy, 2);
    PHINode * const segEndPos = b->CreatePHI(sizeTy, 2);
    blockNo->addIncoming(sz_ZERO, entryBlock);
    segEndPos->addIncoming(sz_ZERO, entryBlock);
    Value * strideBlockIndex = b->CreateAdd(strideBlockOffset, blockNo);
    Value * const nextBlockNo = b->CreateAdd(blockNo, sz_ONE);
    Value * blockOffset = b->CreateMul(blockNo, sz_BLOCKWIDTH);
    Value * segBlock = b->loadInputStreamBlock("segBreaks", sz_ZERO, strideBlockIndex);
    Value * const hasSegEnd = b->simd_cttz(b->getBitBlockWidth(), segBlock);
    Value * segPos = b->CreateZExtOrTrunc(b->CreateExtractElement(b->fwCast(16, hasSegEnd), b->getInt32(0)), sizeTy);
    // b->CallPrintRegister("segBlock", segBlock);
    // b->CallPrintInt("segPos", segPos);
    // update segEndPos only when a new segEnd is seen in the bitblock
    Value * newSegEndPos = b->CreateSelect(b->CreateICmpEQ(segPos, sz_BLOCKWIDTH), segEndPos, b->CreateAdd(blockOffset, segPos));
    segEndPos->addIncoming(newSegEndPos, maskInit);
    blockNo->addIncoming(nextBlockNo, maskInit);
    b->CreateCondBr(b->CreateICmpNE(nextBlockNo, sz_BLOCKS_PER_STRIDE), maskInit, segEndCalculated);
    return newSegEndPos;
}
