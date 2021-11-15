/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */

#include <kernel/core/streamset.h>

#include <kernel/core/kernel.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>
#include <kernel/core/kernel_builder.h>
#include <toolchain/toolchain.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/Format.h>
#include <boost/intrusive/detail/math.hpp>
#include <llvm/Analysis/ConstantFolding.h>
#include <array>

namespace llvm { class Constant; }
namespace llvm { class Function; }

using namespace llvm;
using namespace IDISA;
using IDISA::IDISA_Builder;

using boost::intrusive::detail::is_pow2;

namespace kernel {

using Rational = KernelBuilder::Rational;

using BuilderPtr = StreamSetBuffer::BuilderPtr;

LLVM_ATTRIBUTE_NORETURN void unsupported(const char * const function, const char * const bufferType) {
    report_fatal_error(StringRef{function} + " is not supported by " + bufferType + "Buffers");
}

LLVM_READNONE inline Constant * nullPointerFor(BuilderPtr & b, Type * type, const unsigned underflow) {
    if (LLVM_LIKELY(underflow == 0)) {
        return ConstantPointerNull::get(cast<PointerType>(type));
    } else {
        DataLayout DL(b->getModule());
        Type * const intPtrTy = DL.getIntPtrType(type);
        Constant * const U = ConstantInt::get(intPtrTy, underflow);
        Constant * const P = ConstantExpr::getSizeOf(type->getPointerElementType());
        return ConstantExpr::getIntToPtr(ConstantExpr::getMul(U, P), type);
    }
}

LLVM_READNONE inline Constant * nullPointerFor(BuilderPtr & b, Value * ptr, const unsigned underflow) {
    return nullPointerFor(b, ptr->getType(), underflow);
}

LLVM_READNONE inline unsigned getItemWidth(const Type * ty ) {
    if (LLVM_LIKELY(isa<ArrayType>(ty))) {
        ty = ty->getArrayElementType();
    }
    ty = cast<FixedVectorType>(ty)->getElementType();
    return cast<IntegerType>(ty)->getBitWidth();
}

LLVM_READNONE inline size_t getArraySize(const Type * ty) {
    if (LLVM_LIKELY(isa<ArrayType>(ty))) {
        return ty->getArrayNumElements();
    } else {
        return 1;
    }
}

LLVM_READNONE inline Value * addUnderflow(BuilderPtr & b, Value * ptr, const unsigned underflow) {
    if (LLVM_LIKELY(underflow == 0)) {
        return ptr;
    } else {
        assert ("unspecified module" && b.get() && b->getModule());
        DataLayout DL(b->getModule());
        Type * const intPtrTy = DL.getIntPtrType(ptr->getType());
        Constant * offset = ConstantInt::get(intPtrTy, underflow);
        return b->CreateInBoundsGEP(ptr, offset);
    }
}

LLVM_READNONE inline Value * subtractUnderflow(BuilderPtr & b, Value * ptr, const unsigned underflow) {
    if (LLVM_LIKELY(underflow == 0)) {
        return ptr;
    } else {
        DataLayout DL(b->getModule());
        Type * const intPtrTy = DL.getIntPtrType(ptr->getType());
        Constant * offset = ConstantExpr::getNeg(ConstantInt::get(intPtrTy, underflow));
        return b->CreateInBoundsGEP(ptr, offset);
    }
}

void StreamSetBuffer::assertValidStreamIndex(BuilderPtr b, Value * streamIndex) const {
    if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
        Value * const count = getStreamSetCount(b);
        Value * const index = b->CreateZExtOrTrunc(streamIndex, count->getType());
        Value * const withinSet = b->CreateICmpULT(index, count);
        b->CreateAssert(withinSet, "out-of-bounds stream access: %i of %i", index, count);
    }
}

Value * StreamSetBuffer::getStreamBlockPtr(BuilderPtr b, Value * const baseAddress, Value * const streamIndex, Value * const blockIndex) const {
   // assertValidStreamIndex(b, streamIndex);
    return b->CreateInBoundsGEP(baseAddress, {blockIndex, streamIndex});
}

Value * StreamSetBuffer::getStreamPackPtr(BuilderPtr b, Value * const baseAddress, Value * const streamIndex, Value * blockIndex, Value * const packIndex) const {
   // assertValidStreamIndex(b, streamIndex);
    return b->CreateInBoundsGEP(baseAddress, {blockIndex, streamIndex, packIndex});
}

Value * StreamSetBuffer::getStreamSetCount(BuilderPtr b) const {
    size_t count = 1;
    if (isa<ArrayType>(getBaseType())) {
        count = getBaseType()->getArrayNumElements();
    }
    return b->getSize(count);
}

size_t StreamSetBuffer::getUnderflowCapacity(BuilderPtr b) const {
    return mUnderflow * b->getBitBlockWidth();
}

size_t StreamSetBuffer::getOverflowCapacity(BuilderPtr b) const {
    return mOverflow * b->getBitBlockWidth();
}

bool StreamSetBuffer::isEmptySet() const {
    return getArraySize(mBaseType) == 0;
}

unsigned StreamSetBuffer::getFieldWidth() const {
    return getItemWidth(mBaseType);
}

/**
 * @brief getRawItemPointer
 *
 * get a raw pointer the iN field at position absoluteItemPosition of the stream number streamIndex of the stream set.
 * In the case of a stream whose fields are less than one byte (8 bits) in size, the pointer is to the containing byte.
 * The type of the pointer is i8* for fields of 8 bits or less, otherwise iN* for N-bit fields.
 */
Value * StreamSetBuffer::getRawItemPointer(BuilderPtr b, Value * streamIndex, Value * absolutePosition) const {
    Type * const elemTy = cast<ArrayType>(mBaseType)->getElementType();
    Type * const itemTy = cast<VectorType>(elemTy)->getElementType();
    #if LLVM_VERSION_CODE < LLVM_VERSION_CODE(12, 0, 0)
    const unsigned itemWidth = itemTy->getPrimitiveSizeInBits();
    #else
    const unsigned itemWidth = itemTy->getPrimitiveSizeInBits().getFixedSize();
    #endif
    IntegerType * const sizeTy = b->getSizeTy();
    streamIndex = b->CreateZExt(streamIndex, sizeTy);
    absolutePosition = b->CreateZExt(absolutePosition, sizeTy);

    const auto blockWidth = b->getBitBlockWidth();
    Constant * const BLOCK_WIDTH = b->getSize(blockWidth);
    Value * blockIndex = b->CreateUDiv(absolutePosition, BLOCK_WIDTH);
    Value * positionInBlock = b->CreateURem(absolutePosition, BLOCK_WIDTH);
    Value * blockPtr = getStreamBlockPtr(b, getBaseAddress(b), streamIndex, blockIndex);
    if (LLVM_UNLIKELY(itemWidth < 8)) {
        const Rational itemsPerByte{8, itemWidth};
        if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
            b->CreateAssertZero(b->CreateURemRational(absolutePosition, itemsPerByte),
                                "absolutePosition (%" PRIu64 " * %" PRIu64 "x%" PRIu64 ") must be byte aligned",
                                absolutePosition, getStreamSetCount(b), b->getSize(itemWidth));
        }
        positionInBlock = b->CreateUDivRational(positionInBlock, itemsPerByte);
        PointerType * const itemPtrTy = b->getInt8Ty()->getPointerTo(mAddressSpace);
        blockPtr = b->CreatePointerCast(blockPtr, itemPtrTy);
        return b->CreateInBoundsGEP(blockPtr, positionInBlock);
    }
    PointerType * const itemPtrTy = itemTy->getPointerTo(mAddressSpace);
    blockPtr = b->CreatePointerCast(blockPtr, itemPtrTy);
    return b->CreateInBoundsGEP(blockPtr, positionInBlock);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addOverflow
 ** ------------------------------------------------------------------------------------------------------------- */
Value * StreamSetBuffer::addOverflow(BuilderPtr b, Value * const bufferCapacity, Value * const overflowItems, Value * const consumedOffset) const {
    if (overflowItems) {
        if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
            Value * const overflowCapacity = b->getSize(getOverflowCapacity(b));
            Value * const valid = b->CreateICmpULE(overflowItems, overflowCapacity);
            b->CreateAssert(valid, "overflow items exceeds overflow capacity");
        }
        if (consumedOffset) {
            // limit the overflow so that we do not overwrite our unconsumed data during a copyback
            Value * const effectiveOverflow = b->CreateUMin(consumedOffset, overflowItems);
            return b->CreateAdd(bufferCapacity, effectiveOverflow);
        } else {
            return b->CreateAdd(bufferCapacity, overflowItems);
        }
    } else { // no overflow
        return bufferCapacity;
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief resolveType
 ** ------------------------------------------------------------------------------------------------------------- */
Type * StreamSetBuffer::resolveType(BuilderPtr b, Type * const streamSetType) {
    unsigned numElements = 1;
    Type * type = streamSetType;
    if (LLVM_LIKELY(type->isArrayTy())) {
        numElements = type->getArrayNumElements();
        type = type->getArrayElementType();
    }
    if (LLVM_LIKELY(type->isVectorTy() && cast<FixedVectorType>(type)->getNumElements() == 0)) {
        type = cast<FixedVectorType>(type)->getElementType();
        if (LLVM_LIKELY(type->isIntegerTy())) {
            const auto fieldWidth = cast<IntegerType>(type)->getBitWidth();
            type = b->getBitBlockType();
            if (fieldWidth != 1) {
                type = ArrayType::get(type, fieldWidth);
            }
            return ArrayType::get(type, numElements);
        }
    }
    std::string tmp;
    raw_string_ostream out(tmp);
    streamSetType->print(out);
    out << " is an unvalid stream set buffer type.";
    report_fatal_error(out.str());
}

// External Buffer

Type * ExternalBuffer::getHandleType(BuilderPtr b) const {
    PointerType * const ptrTy = getPointerType();
    IntegerType * const sizeTy = b->getSizeTy();
    return StructType::get(b->getContext(), {ptrTy, sizeTy});
}

void ExternalBuffer::allocateBuffer(BuilderPtr /* b */, Value * const /* capacityMultiplier */) {
    unsupported("allocateBuffer", "External");
}

void ExternalBuffer::releaseBuffer(BuilderPtr /* b */) const {
    // this buffer is not responsible for free-ing th data associated with it
}

void ExternalBuffer::setBaseAddress(BuilderPtr b, Value * const addr) const {
    assert (mHandle && "has not been set prior to calling setBaseAddress");
    Value * const p = b->CreateInBoundsGEP(mHandle, {b->getInt32(0), b->getInt32(BaseAddress)});
    b->CreateStore(b->CreatePointerBitCastOrAddrSpaceCast(addr, getPointerType()), p);
}

Value * ExternalBuffer::getBaseAddress(BuilderPtr b) const {
    assert (mHandle && "has not been set prior to calling getBaseAddress");
    Value * const p = b->CreateInBoundsGEP(mHandle, {b->getInt32(0), b->getInt32(BaseAddress)});
    return b->CreateLoad(p);
}

Value * ExternalBuffer::getOverflowAddress(BuilderPtr b) const {
    assert (mHandle && "has not been set prior to calling getBaseAddress");
    Value * const p = b->CreateInBoundsGEP(mHandle, {b->getInt32(0), b->getInt32(EffectiveCapacity)});
    return b->CreateLoad(p);
}

void ExternalBuffer::setCapacity(BuilderPtr b, Value * const capacity) const {
    assert (mHandle && "has not been set prior to calling setCapacity");
//    if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
//        b->CreateAssert(capacity, "External buffer capacity cannot be 0.");
//    }
    Value *  const p = b->CreateInBoundsGEP(mHandle, {b->getInt32(0), b->getInt32(EffectiveCapacity)});
    b->CreateStore(b->CreateZExt(capacity, b->getSizeTy()), p);
}

Value * ExternalBuffer::getCapacity(BuilderPtr b) const {
    assert (mHandle && "has not been set prior to calling getCapacity");
    Value * const p = b->CreateInBoundsGEP(mHandle, {b->getInt32(0), b->getInt32(EffectiveCapacity)});
    return b->CreateLoad(p);
}

Value * ExternalBuffer::getInternalCapacity(BuilderPtr b) const {
    return getCapacity(b);
}

Value * ExternalBuffer::modByCapacity(BuilderPtr /* b */, Value * const offset) const {
    assert (offset->getType()->isIntegerTy());
    return offset;
}

Value * ExternalBuffer::getLinearlyAccessibleItems(BuilderPtr b, Value * const fromPosition, Value * const totalItems, Value * /* overflowItems */) const {
    return b->CreateSub(totalItems, fromPosition);
}

Value * ExternalBuffer::getLinearlyWritableItems(BuilderPtr b, Value * const fromPosition, Value * const /* consumed */, Value * /* overflowItems */) const {
    assert (fromPosition);
    Value * const capacity = getCapacity(b);
    assert (fromPosition->getType() == capacity->getType());
    return b->CreateSub(capacity, fromPosition);
}

Value * ExternalBuffer::getStreamLogicalBasePtr(BuilderPtr b, Value * baseAddress, Value * const streamIndex, Value * /* blockIndex */) const {
    return StreamSetBuffer::getStreamBlockPtr(b, baseAddress, streamIndex, b->getSize(0));
}

inline void ExternalBuffer::assertValidBlockIndex(BuilderPtr b, Value * blockIndex) const {
    if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
        Value * const blockCount = b->CreateCeilUDiv(getCapacity(b), b->getSize(b->getBitBlockWidth()));
        blockIndex = b->CreateZExtOrTrunc(blockIndex, blockCount->getType());
        Value * const withinCapacity = b->CreateICmpULT(blockIndex, blockCount);
        b->CreateAssert(withinCapacity, "blockIndex exceeds buffer capacity");
    }
}

void ExternalBuffer::copyBackLinearOutputBuffer(BuilderPtr /* b */, llvm::Value * /* consumed */) const {
    /* do nothing */
}

Value * ExternalBuffer::reserveCapacity(BuilderPtr /* b */, Value * /* produced */, Value * /* consumed */, Value * const /* required */, Value * /* syncLock */, Value * const /* segNo */, const unsigned /* syncStep */) const  {
    unsupported("reserveCapacity", "External");
}

Value * ExternalBuffer::getMallocAddress(BuilderPtr /* b */) const {
    unsupported("getMallocAddress", "External");
}

// Internal Buffer

Value * InternalBuffer::getStreamBlockPtr(BuilderPtr b, Value * const baseAddress, Value * const streamIndex, Value * const blockIndex) const {
    Value * offset = nullptr;
    if (mLinear) {
        offset = blockIndex;
    } else {
        offset = modByCapacity(b, blockIndex);
    }
    return StreamSetBuffer::getStreamBlockPtr(b, baseAddress, streamIndex, offset);
}

Value * InternalBuffer::getStreamPackPtr(BuilderPtr b, Value * const baseAddress, Value * const streamIndex, Value * const blockIndex, Value * const packIndex) const {
    Value * offset = nullptr;
    if (mLinear) {
        offset = blockIndex;
    } else {
        offset = modByCapacity(b, blockIndex);
    }
    return StreamSetBuffer::getStreamPackPtr(b, baseAddress, streamIndex, offset, packIndex);
}

Value * InternalBuffer::getStreamLogicalBasePtr(BuilderPtr b, Value * const baseAddress, Value * const streamIndex, Value * const blockIndex) const {
    Value * baseBlockIndex = nullptr;
    if (mLinear) {
        // NOTE: the base address of a linear buffer is always the virtual base ptr; just return it.
        baseBlockIndex = b->getSize(0);
    } else {
        baseBlockIndex = b->CreateSub(modByCapacity(b, blockIndex), blockIndex);
    }
    return StreamSetBuffer::getStreamBlockPtr(b, baseAddress, streamIndex, baseBlockIndex);
}

Value * InternalBuffer::getRawItemPointer(BuilderPtr b, Value * const streamIndex, Value * absolutePosition) const {
    Value * pos = nullptr;
    if (mLinear) {
        pos = absolutePosition;
    } else {
        pos = b->CreateURem(absolutePosition, getCapacity(b));
    }
    return StreamSetBuffer::getRawItemPointer(b, streamIndex, pos);
}

Value * InternalBuffer::getLinearlyAccessibleItems(BuilderPtr b, Value * const processedItems, Value * const totalItems, Value * const overflowItems) const {
    if (mLinear) {
        return b->CreateSub(totalItems, processedItems);
    } else {
        Value * const capacity = getCapacity(b);
        Value * const fromOffset = b->CreateURem(processedItems, capacity);
        Value * const capacityWithOverflow = addOverflow(b, capacity, overflowItems, nullptr);
        Value * const linearSpace = b->CreateSub(capacityWithOverflow, fromOffset);
        Value * const availableItems = b->CreateSub(totalItems, processedItems);
        return b->CreateUMin(availableItems, linearSpace);
    }
}

Value * InternalBuffer::getLinearlyWritableItems(BuilderPtr b, Value * const producedItems, Value * const consumedItems, Value * const overflowItems) const {
    Value * const capacity = getCapacity(b);
    ConstantInt * const ZERO = b->getSize(0);
    if (mLinear) {
        Value * const capacityWithOverflow = addOverflow(b, capacity, overflowItems, nullptr);
        if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
            Value * const valid = b->CreateICmpULE(producedItems, capacityWithOverflow);
            b->CreateAssert(valid, "produced item count (%" PRIu64 ") exceeds capacity (%" PRIu64 ").",
                            producedItems, capacityWithOverflow);
        }
        return b->CreateSub(capacityWithOverflow, producedItems);
     } else {
        Value * const unconsumedItems = b->CreateSub(producedItems, consumedItems);
        Value * const full = b->CreateICmpUGE(unconsumedItems, capacity);
        Value * const fromOffset = b->CreateURem(producedItems, capacity);
        Value * const consumedOffset = b->CreateURem(consumedItems, capacity);
        Value * const toEnd = b->CreateICmpULE(consumedOffset, fromOffset);
        Value * const capacityWithOverflow = addOverflow(b, capacity, overflowItems, consumedOffset);
        Value * const limit = b->CreateSelect(toEnd, capacityWithOverflow, consumedOffset);
        Value * const remaining = b->CreateSub(limit, fromOffset);
        return b->CreateSelect(full, ZERO, remaining);
    }
}

// Static Buffer

Type * StaticBuffer::getHandleType(BuilderPtr b) const {
    auto & C = b->getContext();
    PointerType * const typePtr = getPointerType();
    FixedArray<Type *, 4> types;
    types[BaseAddress] = typePtr;    
    IntegerType * const sizeTy = b->getSizeTy();
    if (mLinear) {
        types[EffectiveCapacity] = sizeTy;
        types[MallocedAddress] = typePtr;
    } else {
        Type * const emptyTy = StructType::get(C);
        types[EffectiveCapacity] = emptyTy;
        types[MallocedAddress] = emptyTy;
    }
    types[InternalCapacity] = sizeTy;
    return StructType::get(C, types);
}

void StaticBuffer::allocateBuffer(BuilderPtr b, Value * const capacityMultiplier) {
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    Value * const handle = getHandle();
    assert (handle && "has not been set prior to calling allocateBuffer");
    Value * const capacity = b->CreateMul(capacityMultiplier, b->getSize(mCapacity));

    if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
        b->CreateAssert(capacity, "Static buffer capacity cannot be 0.");
    }

    indices[1] = b->getInt32(InternalCapacity);
    Value * const intCapacityField = b->CreateInBoundsGEP(handle, indices);
    b->CreateStore(capacity, intCapacityField);

    indices[1] = b->getInt32(BaseAddress);
    Value * const size = b->CreateAdd(capacity, b->getSize(mUnderflow + mOverflow));
    Value * const mallocAddr = b->CreatePageAlignedMalloc(mType, size, mAddressSpace);
    Value * const buffer = addUnderflow(b, mallocAddr, mUnderflow);
    Value * const baseAddressField = b->CreateInBoundsGEP(handle, indices);
    b->CreateStore(buffer, baseAddressField);

    if (mLinear) {
        indices[1] = b->getInt32(EffectiveCapacity);
        Value * const capacityField = b->CreateInBoundsGEP(handle, indices);
        b->CreateStore(capacity, capacityField);

        indices[1] = b->getInt32(MallocedAddress);
        Value * const concreteAddrField = b->CreateInBoundsGEP(handle, indices);
        b->CreateStore(buffer, concreteAddrField);
    }
}

void StaticBuffer::releaseBuffer(BuilderPtr b) const {
    Value * const handle = getHandle();
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(mLinear ? MallocedAddress : BaseAddress);
    Value * const addressField = b->CreateInBoundsGEP(handle, indices);
    Value * buffer = b->CreateLoad(addressField);
    b->CreateFree(subtractUnderflow(b, buffer, mUnderflow));
    b->CreateStore(nullPointerFor(b, buffer, mUnderflow), addressField);
}

inline bool isCapacityGuaranteed(const Value * const index, const size_t capacity) {
    return isa<ConstantInt>(index) ? cast<ConstantInt>(index)->getLimitedValue() < capacity : false;
}

Value * StaticBuffer::modByCapacity(BuilderPtr b, Value * const offset) const {
    assert (offset->getType()->isIntegerTy());
    if (LLVM_UNLIKELY(mLinear || isCapacityGuaranteed(offset, mCapacity))) {
        return offset;
    } else {
        FixedArray<Value *, 2> indices;
        indices[0] = b->getInt32(0);
        indices[1] = b->getInt32(InternalCapacity);
        Value * ptr = b->CreateInBoundsGEP(getHandle(), indices);
        Value * const capacity = b->CreateLoad(ptr);
        return b->CreateURem(offset, capacity);
    }
}

Value * StaticBuffer::getCapacity(BuilderPtr b) const {
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(mLinear ? EffectiveCapacity : InternalCapacity);
    Value * ptr = b->CreateInBoundsGEP(getHandle(), indices);
    ConstantInt * const BLOCK_WIDTH = b->getSize(b->getBitBlockWidth());
    Value * const capacity = b->CreateLoad(ptr);
    assert (capacity->getType()->isIntegerTy());
    return b->CreateMul(capacity, BLOCK_WIDTH, "capacity");
}

Value * StaticBuffer::getInternalCapacity(BuilderPtr b) const {
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(InternalCapacity);
    Value * const intCapacityField = b->CreateInBoundsGEP(getHandle(), indices);
    ConstantInt * const BLOCK_WIDTH = b->getSize(b->getBitBlockWidth());
    Value * const capacity = b->CreateLoad(intCapacityField);
    assert (capacity->getType()->isIntegerTy());
    return b->CreateMul(capacity, BLOCK_WIDTH, "internalCapacity");
}

void StaticBuffer::setCapacity(BuilderPtr b, Value * capacity) const {
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(InternalCapacity);
    Value * const handle = getHandle(); assert (handle);
    Value * capacityField = b->CreateInBoundsGEP(handle, indices);
    ConstantInt * const BLOCK_WIDTH = b->getSize(b->getBitBlockWidth());
    assert (capacity->getType()->isIntegerTy());
    Value * const cap = b->CreateExactUDiv(capacity, BLOCK_WIDTH);
    b->CreateStore(cap, capacityField);
    if (mLinear) {
        indices[1] = b->getInt32(EffectiveCapacity);
        Value * const effCapacityField = b->CreateInBoundsGEP(handle, indices);
        b->CreateStore(cap, effCapacityField);
    }
}

Value * StaticBuffer::getBaseAddress(BuilderPtr b) const {
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(BaseAddress);
    Value * const handle = getHandle(); assert (handle);
    Value * const base = b->CreateInBoundsGEP(handle, indices);
    return b->CreateLoad(base, "baseAddress");
}

void StaticBuffer::setBaseAddress(BuilderPtr b, Value * addr) const {
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(BaseAddress);
    Value * const handle = getHandle(); assert (handle);
    b->CreateStore(addr, b->CreateInBoundsGEP(handle, indices));
    if (mLinear) {
         indices[1] = b->getInt32(MallocedAddress);
         b->CreateStore(addr, b->CreateInBoundsGEP(handle, indices));
    }
}

Value * StaticBuffer::getMallocAddress(BuilderPtr b) const {
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(mLinear ? MallocedAddress : BaseAddress);
    return b->CreateLoad(b->CreateInBoundsGEP(getHandle(), indices));
}

Value * StaticBuffer::getOverflowAddress(BuilderPtr b) const {
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(mLinear ? MallocedAddress : BaseAddress);
    Value * const handle = getHandle(); assert (handle);
    Value * const base = b->CreateLoad(b->CreateInBoundsGEP(handle, indices));
    indices[1] = b->getInt32(InternalCapacity);
    Value * const capacityField = b->CreateInBoundsGEP(handle, indices);
    Value * const capacity = b->CreateLoad(capacityField);
    assert (capacity->getType() == b->getSizeTy());
    return b->CreateInBoundsGEP(base, capacity, "overflow");
}

void StaticBuffer::copyBackLinearOutputBuffer(BuilderPtr b, llvm::Value * consumed) const {

    const auto blockWidth = b->getBitBlockWidth();
    assert (is_pow2(blockWidth));

    ConstantInt * const BLOCK_WIDTH = b->getSize(blockWidth);

    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(EffectiveCapacity);
    Value * const capacityField = b->CreateInBoundsGEP(mHandle, indices);
    Value * consumedChunks = b->CreateUDiv(consumed, BLOCK_WIDTH);

    indices[1] = b->getInt32(MallocedAddress);
    Value * const mallocedAddrField = b->CreateInBoundsGEP(mHandle, indices);
    Value * const bufferStart = b->CreateLoad(mallocedAddrField);
    assert (bufferStart->getType()->isPointerTy());
    Value * const newBaseAddress = b->CreateGEP(bufferStart, b->CreateNeg(consumedChunks));
    Value * const effectiveCapacity = b->CreateAdd(consumedChunks, b->getSize(mCapacity));

    indices[1] = b->getInt32(BaseAddress);
    Value * const baseAddrField = b->CreateInBoundsGEP(mHandle, indices);

    b->CreateStore(newBaseAddress, baseAddrField);
    b->CreateStore(effectiveCapacity, capacityField);

}

Value * StaticBuffer::reserveCapacity(BuilderPtr b, Value * produced, Value * consumed, Value * const required, Value * syncLock, Value * const segNo, const unsigned syncStep) const  {
    if (mLinear) {

        SmallVector<char, 200> buf;
        raw_svector_ostream name(buf);

        assert ("unspecified module" && b.get() && b->getModule());

        name << "__StaticLinearBuffer_linearCopyBack_";

        Type * ty = getBaseType();
        const auto streamCount = ty->getArrayNumElements();
        name << streamCount << 'x';
        ty = ty->getArrayElementType();
        ty = cast<FixedVectorType>(ty)->getElementType();;
        const auto itemWidth = ty->getIntegerBitWidth();
        name << itemWidth << '_' << mAddressSpace;

        Value * const myHandle = getHandle();


        Module * const m = b->getModule();
        IntegerType * const sizeTy = b->getSizeTy();
        FunctionType * funcTy = FunctionType::get(b->getVoidTy(), {myHandle->getType(), sizeTy, sizeTy, sizeTy, sizeTy}, false);
        Function * func = m->getFunction(name.str());
        if (func == nullptr) {

            const auto ip = b->saveIP();

            LLVMContext & C = m->getContext();
            func = Function::Create(funcTy, Function::InternalLinkage, name.str(), m);

            b->SetInsertPoint(BasicBlock::Create(C, "entry", func));

            auto arg = func->arg_begin();
            auto nextArg = [&]() {
                assert (arg != func->arg_end());
                Value * const v = &*arg;
                std::advance(arg, 1);
                return v;
            };

            Value * const handle = nextArg();
            handle->setName("handle");
            Value * const produced = nextArg();
            produced->setName("produced");
            Value * const consumed = nextArg();
            consumed->setName("consumed");
            Value * const underflow = nextArg();
            underflow->setName("underflow");
            Value * const overflow = nextArg();
            overflow->setName("overflow");
            assert (arg == func->arg_end());

            setHandle(handle);

            const auto blockWidth = b->getBitBlockWidth();
            assert (is_pow2(blockWidth));
            const auto blockSize = blockWidth / 8;

            ConstantInt * const BLOCK_WIDTH = b->getSize(blockWidth);
            Constant * const CHUNK_SIZE = ConstantExpr::getSizeOf(mType);

            FixedArray<Value *, 2> indices;
            indices[0] = b->getInt32(0);

            Value * const consumedChunks = b->CreateUDiv(consumed, BLOCK_WIDTH);
            Value * const producedChunks = b->CreateCeilUDiv(produced, BLOCK_WIDTH);
            Value * const unconsumedChunks = b->CreateSub(producedChunks, consumedChunks);

            indices[1] = b->getInt32(BaseAddress);
            Value * const virtualBaseField = b->CreateInBoundsGEP(handle, indices);
            Value * const virtualBase = b->CreateLoad(virtualBaseField);
            assert (virtualBase->getType()->getPointerElementType() == mType);

            indices[1] = b->getInt32(MallocedAddress);
            Value * const mallocAddrField = b->CreateInBoundsGEP(handle, indices);
            Value * const mallocAddress = b->CreateLoad(mallocAddrField);
            Value * const bytesToCopy = b->CreateMul(unconsumedChunks, CHUNK_SIZE);
            Value * const unreadDataPtr = b->CreateInBoundsGEP(virtualBase, consumedChunks);

            indices[1] = b->getInt32(InternalCapacity);
            Value * const intCapacityField = b->CreateInBoundsGEP(getHandle(), indices);
            Value * const bufferCapacity = b->CreateLoad(intCapacityField);

            b->CreateMemCpy(mallocAddress, unreadDataPtr, bytesToCopy, blockSize);

            Value * const newBaseAddress = b->CreateGEP(mallocAddress, b->CreateNeg(consumedChunks));
            b->CreateStore(newBaseAddress, virtualBaseField);

            indices[1] = b->getInt32(EffectiveCapacity);

            Value * const capacityField = b->CreateInBoundsGEP(handle, indices);
            Value * const effectiveCapacity = b->CreateAdd(consumedChunks, bufferCapacity);
            b->CreateStore(effectiveCapacity, capacityField);
            b->CreateRetVoid();

            b->restoreIP(ip);
            setHandle(myHandle);
        }

        b->CreateCall(funcTy, func, { myHandle, produced, consumed, b->getSize(mUnderflow), b->getSize(mOverflow) });
    }

    if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
        Value * const writable = getLinearlyWritableItems(b, produced, consumed, b->getSize(mOverflow * b->getBitBlockWidth()));
        b->CreateAssert(b->CreateICmpULE(required, writable),
                        "Static buffer does not have sufficient capacity "
                        "(%" PRId64 ") for required items (%" PRId64 ")",
                        writable, required);
    }

    return b->getFalse();
}

// Dynamic Buffer

Type * DynamicBuffer::getHandleType(BuilderPtr b) const {
    auto & C = b->getContext();
    PointerType * const typePtr = getPointerType();
    IntegerType * const sizeTy = b->getSizeTy();
    Type * const emptyTy = StructType::get(C);
    FixedArray<Type *, 7> types;

    types[BaseAddress] = typePtr;
    types[InternalCapacity] = sizeTy;
    types[AlternateAddress] = typePtr;
    if (mLinear) {
        types[MallocedAddress] = typePtr;
        types[EffectiveCapacity] = sizeTy;
        types[AlternateCapacity] = sizeTy;
        types[DelayUntilAcquiringSyncNumber] = sizeTy;
    } else {
        types[MallocedAddress] = emptyTy;
        types[EffectiveCapacity] = emptyTy;
        types[AlternateCapacity] = emptyTy;
        types[DelayUntilAcquiringSyncNumber] = emptyTy;
    }

    return StructType::get(C, types);
}

void DynamicBuffer::allocateBuffer(BuilderPtr b, Value * const capacityMultiplier) {
    assert (mHandle && "has not been set prior to calling allocateBuffer");
    // note: when adding extensible stream sets, make sure to set the initial count here.
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);

    Value * const handle = getHandle();
    Value * const capacity = b->CreateMul(capacityMultiplier, b->getSize(mInitialCapacity));

    if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
        b->CreateAssert(capacity, "Dynamic buffer capacity cannot be 0.");
    }

    indices[1] = b->getInt32(BaseAddress);
    Value * const baseAddressField = b->CreateInBoundsGEP(handle, indices);
    Value * const size = b->CreateAdd(capacity, b->getSize(mUnderflow + mOverflow));
    Value * const baseAddress = b->CreatePageAlignedMalloc(mType, size, mAddressSpace);

    Value * const adjBaseAddress = addUnderflow(b, baseAddress, mUnderflow);
    b->CreateStore(adjBaseAddress, baseAddressField);

    indices[1] = b->getInt32(EffectiveCapacity);
    Value * const effCapacityField = b->CreateInBoundsGEP(handle, indices);
    b->CreateStore(capacity, effCapacityField);

    if (mLinear) {
        indices[1] = b->getInt32(MallocedAddress);
        Value * const initialField = b->CreateInBoundsGEP(handle, indices);
        b->CreateStore(adjBaseAddress, initialField);

        indices[1] = b->getInt32(InternalCapacity);
        Value * const capacityField = b->CreateInBoundsGEP(handle, indices);
        b->CreateStore(capacity, capacityField);

        indices[1] = b->getInt32(AlternateAddress);
        Value * const priorAddressField = b->CreateInBoundsGEP(handle, indices);
        Value * const altAddress = b->CreatePageAlignedMalloc(mType, size, mAddressSpace);
        Value * const adjAltBaseAddress = addUnderflow(b, altAddress, mUnderflow);
        b->CreateStore(adjAltBaseAddress, priorAddressField);

        indices[1] = b->getInt32(AlternateCapacity);
        Value * const altCapacityField = b->CreateInBoundsGEP(handle, indices);
        b->CreateStore(capacity, altCapacityField);

        indices[1] = b->getInt32(DelayUntilAcquiringSyncNumber);
        Value * const delayField = b->CreateInBoundsGEP(handle, indices);
        b->CreateStore(b->getSize(0), delayField);

    } else {

        indices[1] = b->getInt32(InternalCapacity);
        Value * const capacityField = b->CreateInBoundsGEP(handle, indices);
        b->CreateStore(capacity, capacityField);

        indices[1] = b->getInt32(AlternateAddress);
        Value * const priorAddressField = b->CreateInBoundsGEP(handle, indices);
        b->CreateStore(nullPointerFor(b, baseAddress, mUnderflow), priorAddressField);
    }
}

void DynamicBuffer::releaseBuffer(BuilderPtr b) const {
    /* Free the dynamically allocated buffer(s). */
    Value * const handle = getHandle();
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(AlternateAddress);
    Value * const priorAddressField = b->CreateInBoundsGEP(handle, indices);
    Value * const priorAddress = b->CreateLoad(priorAddressField);
    b->CreateFree(subtractUnderflow(b, priorAddress, mUnderflow));
    Constant * const nullPtr = nullPointerFor(b, priorAddress, mUnderflow);
    b->CreateStore(nullPtr, priorAddressField);
    indices[1] = b->getInt32(mLinear ? MallocedAddress : BaseAddress);
    Value * const baseAddressField = b->CreateInBoundsGEP(handle, indices);
    Value * const baseAddress = b->CreateLoad(baseAddressField);
    b->CreateFree(subtractUnderflow(b, baseAddress, mUnderflow));
    b->CreateStore(nullPtr, baseAddressField);
}

void DynamicBuffer::setBaseAddress(BuilderPtr /* b */, Value * /* addr */) const {
    unsupported("setBaseAddress", "Dynamic");
}

Value * DynamicBuffer::getBaseAddress(BuilderPtr b) const {
    assert (getHandle());
    Value * const ptr = b->CreateInBoundsGEP(getHandle(), {b->getInt32(0), b->getInt32(BaseAddress)});
    return b->CreateLoad(ptr);
}

Value * DynamicBuffer::getMallocAddress(BuilderPtr b) const {
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(mLinear ? MallocedAddress : BaseAddress);
    return b->CreateLoad(b->CreateInBoundsGEP(getHandle(), indices));
}

Value * DynamicBuffer::getOverflowAddress(BuilderPtr b) const {
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(mLinear ? MallocedAddress : BaseAddress);
    Value * const handle = getHandle(); assert (handle);
    Value * const base = b->CreateLoad(b->CreateInBoundsGEP(handle, indices));
    indices[1] = b->getInt32(mLinear ? EffectiveCapacity : InternalCapacity);
    Value * const capacityField = b->CreateInBoundsGEP(handle, indices);
    Value * const capacity = b->CreateLoad(capacityField);
    assert (capacity->getType() == b->getSizeTy());
    return b->CreateInBoundsGEP(base, capacity);
}

Value * DynamicBuffer::modByCapacity(BuilderPtr b, Value * const offset) const {
    assert (offset->getType()->isIntegerTy());
    if (mLinear || isCapacityGuaranteed(offset, mInitialCapacity)) {
        return offset;
    } else {
        assert (getHandle());
        FixedArray<Value *, 2> indices;
        indices[0] = b->getInt32(0);
        indices[1] = b->getInt32(InternalCapacity);
        Value * const capacityPtr = b->CreateInBoundsGEP(getHandle(), indices);
        Value * const capacity = b->CreateLoad(capacityPtr);
        assert (capacity->getType()->isIntegerTy());
        return b->CreateURem(offset, capacity);
    }
}

Value * DynamicBuffer::getCapacity(BuilderPtr b) const {
    assert (getHandle());
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(mLinear ? EffectiveCapacity : InternalCapacity);
    Value * ptr = b->CreateInBoundsGEP(getHandle(), indices);
    ConstantInt * const BLOCK_WIDTH = b->getSize(b->getBitBlockWidth());
    Value * const capacity = b->CreateLoad(ptr);
    assert (capacity->getType()->isIntegerTy());
    return b->CreateMul(capacity, BLOCK_WIDTH, "capacity");
}

Value * DynamicBuffer::getInternalCapacity(BuilderPtr b) const {
    FixedArray<Value *, 2> indices;
    indices[0] = b->getInt32(0);
    indices[1] = b->getInt32(InternalCapacity);
    Value * const intCapacityField = b->CreateInBoundsGEP(getHandle(), indices);
    ConstantInt * const BLOCK_WIDTH = b->getSize(b->getBitBlockWidth());
    Value * const capacity = b->CreateLoad(intCapacityField);
    assert (capacity->getType()->isIntegerTy());
    return b->CreateMul(capacity, BLOCK_WIDTH);
}

void DynamicBuffer::setCapacity(BuilderPtr /* b */, Value * /* capacity */) const {
    unsupported("setCapacity", "Dynamic");
}

void DynamicBuffer::copyBackLinearOutputBuffer(BuilderPtr /* b */, llvm::Value * /* consumed */) const {
    /* do nothing */
}

#if 0

Value * DynamicBuffer::reserveCapacity(BuilderPtr b, Value * const produced, Value * const consumed, Value * const required) const {

    SmallVector<char, 200> buf;
    raw_svector_ostream name(buf);

    assert ("unspecified module" && b.get() && b->getModule());

    name << "__DynamicBuffer_";
    if (mLinear) {
        name << "linearCopyBackOrExpand_";
    } else {
        name << "reserveCapacity_";
    }

    Type * ty = getBaseType();
    const auto streamCount = ty->getArrayNumElements();
    name << streamCount << 'x';
    ty = ty->getArrayElementType();
    ty = ty->getVectorElementType();
    const auto itemWidth = ty->getIntegerBitWidth();
    name << itemWidth << '_' << mAddressSpace;

    Value * const myHandle = getHandle();

    Module * const m = b->getModule();
    IntegerType * const sizeTy = b->getSizeTy();
    FunctionType * funcTy = FunctionType::get(b->getInt1Ty(), {myHandle->getType(), sizeTy, sizeTy, sizeTy, sizeTy, sizeTy}, false);
    Function * func = m->getFunction(name.str());
    if (func == nullptr) {

        const auto ip = b->saveIP();

        LLVMContext & C = m->getContext();
        func = Function::Create(funcTy, Function::InternalLinkage, name.str(), m);

        b->SetInsertPoint(BasicBlock::Create(C, "entry", func));

        auto arg = func->arg_begin();
        auto nextArg = [&]() {
            assert (arg != func->arg_end());
            Value * const v = &*arg;
            std::advance(arg, 1);
            return v;
        };

        Value * const handle = nextArg();
        handle->setName("handle");
        Value * const produced = nextArg();
        produced->setName("produced");
        Value * const consumed = nextArg();
        consumed->setName("consumed");
        Value * const required = nextArg();
        required->setName("required");
        Value * const underflow = nextArg();
        underflow->setName("underflow");
        Value * const overflow = nextArg();
        overflow->setName("overflow");
        assert (arg == func->arg_end());

        setHandle(handle);

        const auto blockWidth = b->getBitBlockWidth();
        assert (is_pow2(blockWidth));
        const auto blockSize = blockWidth / 8;

        DataLayout DL(b->getModule());

        ConstantInt * const BLOCK_WIDTH = b->getSize(blockWidth);
        ConstantInt * const sz_ZERO = b->getSize(0);
        Constant * const CHUNK_SIZE = ConstantFoldConstant(ConstantExpr::getSizeOf(mType), DL);
        assert (isa<ConstantInt>(CHUNK_SIZE));
        const auto bytesPerChunk = cast<ConstantInt>(CHUNK_SIZE)->getLimitedValue();
        assert ((bytesPerChunk % blockSize) == 0 && bytesPerChunk >= blockSize);
        const auto blocksPerChunk = bytesPerChunk / blockSize;
        assert (blocksPerChunk > 0);
        ConstantInt * const BLOCKS_PER_CHUNK = b->getSize(blocksPerChunk);

        PointerType * const blockAlignedPtrTy = b->getBitBlockType()->getPointerTo();

        FixedArray<Value *, 2> indices;
        indices[0] = b->getInt32(0);
        indices[1] = b->getInt32(InternalCapacity);

        Value * const intCapacityField = b->CreateInBoundsGEP(handle, indices);
        Value * const internalCapacity = b->CreateLoad(intCapacityField);

        Value * const consumedChunks = b->CreateUDiv(consumed, BLOCK_WIDTH);
        Value * const producedChunks = b->CreateCeilUDiv(produced, BLOCK_WIDTH);
        Value * const requiredCapacity = b->CreateAdd(produced, required);
        Value * const requiredChunks = b->CreateCeilUDiv(requiredCapacity, BLOCK_WIDTH);
        Value * const unconsumedChunks = b->CreateSub(producedChunks, consumedChunks);

        indices[1] = b->getInt32(BaseAddress);
        Value * const virtualBaseField = b->CreateInBoundsGEP(handle, indices);
        Value * const virtualBase = b->CreateLoad(virtualBaseField);
        assert (virtualBase->getType()->getPointerElementType() == mType);

        const auto sizeTyWidth = sizeTy->getBitWidth() / 8;

        if (mLinear) {

            indices[1] = b->getInt32(MallocedAddress);
            Value * const mallocAddrField = b->CreateInBoundsGEP(handle, indices);
            Value * const mallocAddress = b->CreateLoad(mallocAddrField);

            BasicBlock * const copyBack = BasicBlock::Create(C, "copyBack", func);
            BasicBlock * const expandAndCopyBack = BasicBlock::Create(C, "expandAndCopyBack", func);
            BasicBlock * const updateBaseAddress = BasicBlock::Create(C, "updateBaseAddress", func);

            BasicBlock * const memCopyLoop = BasicBlock::Create(C, "memCopyLoop", func);
            BasicBlock * const memCopyExit = BasicBlock::Create(C, "memCopyExit", func);



            Value * const unreadDataPtr = b->CreateInBoundsGEP(virtualBase, consumedChunks);
            Value * const chunksToReserve = b->CreateSub(requiredChunks, consumedChunks);
            Value * const wouldWriteUpToPtr = b->CreateInBoundsGEP(mallocAddress, chunksToReserve);
            Value * const cannotCopy = b->CreateICmpUGT(wouldWriteUpToPtr, unreadDataPtr);
            b->CreateUnlikelyCondBr(cannotCopy, expandAndCopyBack, copyBack);

            b->SetInsertPoint(copyBack);
            // b->CreateMemCpy(mallocAddress, unreadDataPtr, bytesToCopy, blockSize);
            BasicBlock * const copyBackExit = b->GetInsertBlock();
            b->CreateBr(updateBaseAddress);

            b->SetInsertPoint(expandAndCopyBack);
            // newInternalCapacity tends to be 2x internalCapacity
            Value * const reserveCapacity = b->CreateAdd(chunksToReserve, internalCapacity);
            Value * const newInternalCapacity = b->CreateRoundUp(reserveCapacity, internalCapacity);
            Value * const additionalCapacity = b->CreateAdd(underflow, overflow);
            Value * const mallocCapacity = b->CreateAdd(newInternalCapacity, additionalCapacity);
            Value * expandedBuffer = b->CreatePageAlignedMalloc(mType, mallocCapacity, mAddressSpace);
            expandedBuffer = b->CreateInBoundsGEP(expandedBuffer, underflow);
            b->CreateStore(newInternalCapacity, intCapacityField);

            indices[1] = b->getInt32(PriorAddress);
            Value * const priorBufferField = b->CreateInBoundsGEP(handle, indices);
            Value * priorBuffer = b->CreateLoad(priorBufferField);
            b->CreateFree(b->CreateInBoundsGEP(priorBuffer, b->CreateNeg(underflow)));
            b->CreateStore(mallocAddress, priorBufferField);
            // b->CreateMemCpy(expandedBuffer, unreadDataPtr, bytesToCopy, blockSize);
            b->CreateStore(expandedBuffer, mallocAddrField);
            BasicBlock * const expandAndCopyBackExit = b->GetInsertBlock();
            b->CreateBr(updateBaseAddress);

            b->SetInsertPoint(updateBaseAddress);
            PHINode * const newBaseBuffer = b->CreatePHI(virtualBase->getType(), 2);
            newBaseBuffer->addIncoming(mallocAddress, copyBackExit);
            newBaseBuffer->addIncoming(expandedBuffer, expandAndCopyBackExit);
            PHINode * const internalCapacityPhi = b->CreatePHI(sizeTy, 2);
            internalCapacityPhi->addIncoming(internalCapacity, copyBackExit);
            internalCapacityPhi->addIncoming(newInternalCapacity, expandAndCopyBackExit);

            Value * initialCond = b->CreateICmpNE(unconsumedChunks, sz_ZERO);
            Value * const copyTo = b->CreatePointerCast(newBaseBuffer, blockAlignedPtrTy);
            Value * const copyFrom = b->CreatePointerCast(unreadDataPtr, blockAlignedPtrTy);
            Value * const blocksToCopy = b->CreateMul(unconsumedChunks, BLOCKS_PER_CHUNK);
            b->CreateCondBr(initialCond, memCopyLoop, memCopyExit);

            b->SetInsertPoint(memCopyLoop);
            PHINode * const offset = b->CreatePHI(sizeTy, 2);
            offset->addIncoming(sz_ZERO, updateBaseAddress);
            SmallVector<Value *, 64> idx(blocksPerChunk);
            SmallVector<Value *, 64> loads(blocksPerChunk);
            for (unsigned i = 0; i < blocksPerChunk; ++i) {
                idx[i] = b->CreateAdd(offset, b->getSize(i));
                loads[i] = b->CreateAlignedLoad(b->CreateGEP(copyFrom, idx[i]), blockSize);
            }
            for (unsigned i = 0; i < blocksPerChunk; ++i) {
                b->CreateAlignedStore(loads[i], b->CreateGEP(copyTo, idx[i]), blockSize);
            }
            Value * const nextOffset = b->CreateAdd(offset, BLOCKS_PER_CHUNK);
            offset->addIncoming(nextOffset, memCopyLoop);
            Value * const innerCond = b->CreateICmpNE(offset, blocksToCopy);
            b->CreateCondBr(innerCond, memCopyLoop, memCopyExit);


            b->SetInsertPoint(memCopyExit);
//            Function * fSleep = m->getFunction("usleep");
//            if (fSleep == nullptr) {
//                FunctionType * fty = FunctionType::get(b->getInt32Ty(), {b->getInt32Ty()}, false);
//                fSleep = Function::Create(fty, Function::ExternalLinkage, "usleep", m);
//                fSleep->setCallingConv(CallingConv::C);
//            }
//            b->CreateCall(fSleep, b->getInt32(10));

            Value * const effectiveCapacity = b->CreateAdd(consumedChunks, internalCapacityPhi);
            Value * const newBaseAddress = b->CreateGEP(newBaseBuffer, b->CreateNeg(consumedChunks));

            indices[1] = b->getInt32(EffectiveCapacity);
            Value * const effCapacityField = b->CreateInBoundsGEP(handle, indices);
            b->CreateAlignedStore(effectiveCapacity, effCapacityField, sizeTyWidth);
            b->CreateAlignedStore(newBaseAddress, virtualBaseField, sizeTyWidth);

            b->CreateRet(cannotCopy);

        } else { // Circular

            Type * const intPtrTy = DL.getIntPtrType(virtualBase->getType());

            Value * const bytesToCopy = b->CreateMul(unconsumedChunks, CHUNK_SIZE);

            // make sure the new capacity is at least 2x the current capacity and a multiple of it
            if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
                Value * const check = b->CreateICmpUGE(requiredChunks, internalCapacity);
                b->CreateAssert(check, "unnecessary buffer expansion occurred");
            }

            Value * const newChunks = b->CreateSub(requiredChunks, consumedChunks);
            Value * const newCapacity = b->CreateRoundUp(newChunks, internalCapacity);
            Value * const additionalCapacity = b->CreateAdd(underflow, overflow);
            Value * const requiredCapacity = b->CreateAdd(newCapacity, additionalCapacity);

            Value * newBuffer = b->CreatePageAlignedMalloc(mType, requiredCapacity, mAddressSpace);
            newBuffer = b->CreateInBoundsGEP(newBuffer, { underflow });

            Value * const consumedOffset = b->CreateURem(consumedChunks, internalCapacity);
            Value * const producedOffset = b->CreateURem(producedChunks, internalCapacity);
            Value * const newConsumedOffset = b->CreateURem(consumedChunks, newCapacity);
            Value * const newProducedOffset = b->CreateURem(producedChunks, newCapacity);
            Value * const consumedOffsetEnd = b->CreateAdd(consumedOffset, unconsumedChunks);
            Value * const sourceLinear = b->CreateICmpULE(consumedOffsetEnd, producedOffset);
            Value * const newConsumedOffsetEnd = b->CreateAdd(newConsumedOffset, unconsumedChunks);
            Value * const targetLinear = b->CreateICmpULE(newConsumedOffsetEnd, newProducedOffset);
            Value * const linearCopy = b->CreateAnd(sourceLinear, targetLinear);

            Value * const consumedOffsetPtr = b->CreateInBoundsGEP(virtualBase, consumedOffset);
            Value * const newConsumedOffsetPtr = b->CreateInBoundsGEP(newBuffer, newConsumedOffset);

            BasicBlock * const copyLinear = BasicBlock::Create(C, "copyLinear", func);
            BasicBlock * const copyNonLinear = BasicBlock::Create(C, "copyNonLinear", func);
            BasicBlock * const storeNewBuffer = BasicBlock::Create(C, "storeNewBuffer", func);
            b->CreateCondBr(linearCopy, copyLinear, copyNonLinear);

            b->SetInsertPoint(copyLinear);
            b->CreateMemCpy(newConsumedOffsetPtr, consumedOffsetPtr, bytesToCopy, blockSize);
            b->CreateBr(storeNewBuffer);

            b->SetInsertPoint(copyNonLinear);
            Value * const bufferLength1 = b->CreateSub(internalCapacity, consumedOffset);
            Value * const newBufferLength1 = b->CreateSub(newCapacity, newConsumedOffset);
            Value * const partialLength1 = b->CreateUMin(bufferLength1, newBufferLength1);
            Value * const copyEndPtr = b->CreateInBoundsGEP(virtualBase, b->CreateAdd(consumedOffset, partialLength1));
            Value * const copyEndPtrInt = b->CreatePtrToInt(copyEndPtr, intPtrTy);
            Value * const consumedOffsetPtrInt = b->CreatePtrToInt(consumedOffsetPtr, intPtrTy);
            Value * const bytesToCopy1 = b->CreateSub(copyEndPtrInt, consumedOffsetPtrInt);
            b->CreateMemCpy(newConsumedOffsetPtr, consumedOffsetPtr, bytesToCopy1, blockSize);
            Value * const sourceOffset = b->CreateURem(b->CreateAdd(consumedOffset, partialLength1), internalCapacity);
            Value * const sourcePtr = b->CreateInBoundsGEP(virtualBase, sourceOffset);
            Value * const targetOffset = b->CreateURem(b->CreateAdd(newConsumedOffset, partialLength1), newCapacity);
            Value * const targetPtr = b->CreateInBoundsGEP(newBuffer, targetOffset);
            Value * const bytesToCopy2 = b->CreateSub(bytesToCopy, bytesToCopy1);
            b->CreateMemCpy(targetPtr, sourcePtr, bytesToCopy2, blockSize);
            b->CreateBr(storeNewBuffer);

            b->SetInsertPoint(storeNewBuffer);
            indices[1] = b->getInt32(PriorAddress);
            Value * const priorBufferField = b->CreateInBoundsGEP(handle, indices);
            Value * const priorBuffer = b->CreateLoad(priorBufferField);
            b->CreateStore(newBuffer, virtualBaseField);
            b->CreateAlignedStore(newCapacity, intCapacityField, sizeTyWidth);
            b->CreateAlignedStore(virtualBase, priorBufferField, sizeTyWidth);
            b->CreateFree(b->CreateInBoundsGEP(priorBuffer, { b->CreateNeg(underflow) }));

            b->CreateRet(b->getTrue());
        }

        b->restoreIP(ip);
        setHandle(myHandle);
    }

    return b->CreateCall(funcTy, func, { myHandle, produced, consumed, required, b->getSize(mUnderflow), b->getSize(mOverflow) });
}

#else

Value * DynamicBuffer::reserveCapacity(BuilderPtr b, Value * const produced, Value * const consumed, Value * const required, Value * const syncLock, Value * const segNo, const unsigned syncStep) const {

    SmallVector<char, 200> buf;
    raw_svector_ostream name(buf);

    assert ("unspecified module" && b.get() && b->getModule());

    name << "__DynamicBuffer_";
    if (mLinear) {
        name << "linearCopyBackOrExpand_";
    } else {
        name << "reserveCapacity_";
    }

    Type * ty = getBaseType();
    const auto streamCount = ty->getArrayNumElements();
    name << streamCount << 'x';
    ty = ty->getArrayElementType();
    ty = cast<FixedVectorType>(ty)->getElementType();
    const auto itemWidth = ty->getIntegerBitWidth();
    name << itemWidth << '@' << mAddressSpace;

    const bool hasSyncLock = mLinear && syncLock;

    if (hasSyncLock) {
        name << '_' << syncStep;
    }

    Value * const myHandle = getHandle();

    Module * const m = b->getModule();

    Function * func = m->getFunction(name.str());
    if (func == nullptr) {

        IntegerType * const sizeTy = b->getSizeTy();
        PointerType * const sizePtrTy = sizeTy->getPointerTo(mAddressSpace);
        FunctionType * funcTy = nullptr;
        if (hasSyncLock) {
            funcTy = FunctionType::get(b->getInt1Ty(), {myHandle->getType(), sizeTy, sizeTy, sizeTy, sizeTy, sizeTy, sizePtrTy, sizeTy}, false);
        } else {
            funcTy = FunctionType::get(b->getInt1Ty(), {myHandle->getType(), sizeTy, sizeTy, sizeTy, sizeTy, sizeTy}, false);
        }


        const auto ip = b->saveIP();

        LLVMContext & C = m->getContext();
        func = Function::Create(funcTy, Function::InternalLinkage, name.str(), m);

        b->SetInsertPoint(BasicBlock::Create(C, "entry", func));

        auto arg = func->arg_begin();
        auto nextArg = [&]() {
            assert (arg != func->arg_end());
            Value * const v = &*arg;
            std::advance(arg, 1);
            return v;
        };

        Value * const handle = nextArg();
        handle->setName("handle");
        Value * const produced = nextArg();
        produced->setName("produced");
        Value * const consumed = nextArg();
        consumed->setName("consumed");
        Value * const required = nextArg();
        required->setName("required");
        Value * const underflow = nextArg();
        underflow->setName("underflow");
        Value * const overflow = nextArg();
        overflow->setName("overflow");
        Value * syncLock = nullptr;
        Value * segNo = nullptr;
        if (hasSyncLock) {
            syncLock = nextArg();
            syncLock->setName("syncLock");
            segNo = nextArg();
            segNo->setName("segNo");
        }
        assert (arg == func->arg_end());

        setHandle(handle);


        const auto blockWidth = b->getBitBlockWidth();
        assert (is_pow2(blockWidth));
        const auto blockSize = blockWidth / 8;

        ConstantInt * const BLOCK_WIDTH = b->getSize(blockWidth);
        Constant * const CHUNK_SIZE = ConstantExpr::getSizeOf(mType);

        FixedArray<Value *, 2> indices;
        indices[0] = b->getInt32(0);


        Value * const consumedChunks = b->CreateUDiv(consumed, BLOCK_WIDTH);
        Value * const producedChunks = b->CreateCeilUDiv(produced, BLOCK_WIDTH);
        Value * const requiredCapacity = b->CreateAdd(produced, required);
        Value * const requiredChunks = b->CreateCeilUDiv(requiredCapacity, BLOCK_WIDTH);

        Value * const unconsumedChunks = b->CreateSub(producedChunks, consumedChunks);        
        Value * const bytesToCopy = b->CreateMul(unconsumedChunks, CHUNK_SIZE);

        indices[1] = b->getInt32(BaseAddress);
        Value * const virtualBaseField = b->CreateInBoundsGEP(handle, indices);
        Value * const virtualBase = b->CreateLoad(virtualBaseField);
        assert (virtualBase->getType()->getPointerElementType() == mType);

        DataLayout DL(b->getModule());
        Type * const intPtrTy = DL.getIntPtrType(virtualBase->getType());

        const auto sizeTyWidth = sizeTy->getBitWidth() / 8;

        if (mLinear) {

            indices[1] = b->getInt32(MallocedAddress);
            Value * const primaryAddressField = b->CreateInBoundsGEP(handle, indices);
            Value * const primaryAddress = b->CreateAlignedLoad(primaryAddressField, sizeTyWidth);
            assert (virtualBase->getType()->getPointerElementType() == mType);

            indices[1] = b->getInt32(InternalCapacity);
            Value * const intCapacityField = b->CreateInBoundsGEP(handle, indices);
            Value * const internalCapacity = b->CreateAlignedLoad(intCapacityField, sizeTyWidth);

            indices[1] = b->getInt32(AlternateAddress);
            Value * const alternateAddrField = b->CreateInBoundsGEP(handle, indices);
            Value * const alternateAddress = b->CreateAlignedLoad(alternateAddrField, sizeTyWidth);
            b->CreateAlignedStore(primaryAddress, alternateAddrField, sizeTyWidth);

            indices[1] = b->getInt32(AlternateCapacity);
            Value * const altCapacityField = b->CreateInBoundsGEP(handle, indices);
            Value * const alternateCapacity = b->CreateAlignedLoad(altCapacityField, sizeTyWidth);
            b->CreateAlignedStore(internalCapacity, altCapacityField, sizeTyWidth);

            if (hasSyncLock) {

                BasicBlock * const checkForPendingConsumer = BasicBlock::Create(C, "checkForPendingConsumer", func);
                BasicBlock * const updateBaseAddress = BasicBlock::Create(C, "updateBaseAddress", func);

                indices[1] = b->getInt32(DelayUntilAcquiringSyncNumber);
                Value * const requiredDelayPtr = b->CreateInBoundsGEP(handle, indices);
                Value * const requiredDelay = b->CreateAlignedLoad(requiredDelayPtr, sizeTyWidth);
                b->CreateAlignedStore(segNo, requiredDelayPtr, sizeTyWidth);

                b->CreateBr(checkForPendingConsumer);

                // If the segment number of the syncLock is at least the value of our required delay then all consumers
                // must be looking at the current buffer. We can safely reuse the alternate buffer as our current one.
                b->SetInsertPoint(checkForPendingConsumer);
                Value * const consumerSegNo = b->CreateAtomicLoadAcquire(syncLock);
                Value * const cond = b->CreateICmpUGE(consumerSegNo, requiredDelay);
                b->CreateLikelyCondBr(cond, updateBaseAddress, checkForPendingConsumer);

                // Check whether we have enough space to satisfy our required capacity
                b->SetInsertPoint(updateBaseAddress);
            }

            BasicBlock * const checkCapacityRequirement = b->GetInsertBlock();

            BasicBlock * const expandAndCopyBack = BasicBlock::Create(C, "expandAndCopyBack", func);
            BasicBlock * const copyBack = BasicBlock::Create(C, "copyBack", func);

            Value * const chunksToReserve = b->CreateSub(requiredChunks, consumedChunks);
            Value * const mustExpand = b->CreateICmpUGT(chunksToReserve, alternateCapacity);
            b->CreateUnlikelyCondBr(mustExpand, expandAndCopyBack, copyBack);

            b->SetInsertPoint(expandAndCopyBack);
            // if not, discard the alternate buffer create a larger one
            b->CreateFree(b->CreateInBoundsGEP(alternateAddress, b->CreateNeg(underflow)));
            // newInternalCapacity tends to be 2x internalCapacity
            Value * const reserveCapacity = b->CreateAdd(chunksToReserve, internalCapacity);
            Value * const newInternalCapacity = b->CreateRoundUp(reserveCapacity, internalCapacity);
            Value * const additionalCapacity = b->CreateAdd(underflow, overflow);
            Value * const mallocCapacity = b->CreateAdd(newInternalCapacity, additionalCapacity);
            Value * expandedBuffer = b->CreatePageAlignedMalloc(mType, mallocCapacity, mAddressSpace);
            expandedBuffer = b->CreateInBoundsGEP(expandedBuffer, underflow);
            BasicBlock * const expandAndCopyBackExit = b->GetInsertBlock();
            b->CreateBr(copyBack);


            b->SetInsertPoint(copyBack);
            PHINode * const newBaseBuffer = b->CreatePHI(virtualBase->getType(), 2);
            newBaseBuffer->addIncoming(alternateAddress, checkCapacityRequirement);
            newBaseBuffer->addIncoming(expandedBuffer, expandAndCopyBackExit);
            PHINode * const internalCapacityPhi = b->CreatePHI(sizeTy, 2);
            internalCapacityPhi->addIncoming(alternateCapacity, checkCapacityRequirement);
            internalCapacityPhi->addIncoming(newInternalCapacity, expandAndCopyBackExit);

            Value * const unreadDataPtr = b->CreateInBoundsGEP(virtualBase, consumedChunks);
            b->CreateMemCpy(newBaseBuffer, unreadDataPtr, bytesToCopy, blockSize);

            b->CreateAlignedStore(internalCapacityPhi, intCapacityField, sizeTyWidth);

            Value * const effectiveCapacity = b->CreateAdd(consumedChunks, internalCapacityPhi);
            indices[1] = b->getInt32(EffectiveCapacity);
            Value * const effCapacityField = b->CreateInBoundsGEP(handle, indices);
            b->CreateAlignedStore(effectiveCapacity, effCapacityField, sizeTyWidth);

            b->CreateAlignedStore(newBaseBuffer, primaryAddressField, sizeTyWidth);

            Value * const newVirtualAddress = b->CreateGEP(newBaseBuffer, b->CreateNeg(consumedChunks));
            b->CreateAlignedStore(newVirtualAddress, virtualBaseField, sizeTyWidth);

            b->CreateRet(mustExpand);

        } else { // Circular

            indices[1] = b->getInt32(InternalCapacity);

            Value * const intCapacityField = b->CreateInBoundsGEP(handle, indices);
            Value * const internalCapacity = b->CreateLoad(intCapacityField);

            // make sure the new capacity is at least 2x the current capacity and a multiple of it
            if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
                Value * const check = b->CreateICmpUGE(requiredChunks, internalCapacity);
                b->CreateAssert(check, "unnecessary buffer expansion occurred");                
            }


            Value * const newChunks = b->CreateSub(requiredChunks, consumedChunks);
            Value * const newCapacity = b->CreateRoundUp(newChunks, internalCapacity);
            Value * const additionalCapacity = b->CreateAdd(underflow, overflow);
            Value * const requiredCapacity = b->CreateAdd(newCapacity, additionalCapacity);

            Value * newBuffer = b->CreatePageAlignedMalloc(mType, requiredCapacity, mAddressSpace);
            newBuffer = b->CreateInBoundsGEP(newBuffer, { underflow });

            Value * const consumedOffset = b->CreateURem(consumedChunks, internalCapacity);
            Value * const producedOffset = b->CreateURem(producedChunks, internalCapacity);
            Value * const newConsumedOffset = b->CreateURem(consumedChunks, newCapacity);
            Value * const newProducedOffset = b->CreateURem(producedChunks, newCapacity);
            Value * const consumedOffsetEnd = b->CreateAdd(consumedOffset, unconsumedChunks);
            Value * const sourceLinear = b->CreateICmpULE(consumedOffsetEnd, producedOffset);
            Value * const newConsumedOffsetEnd = b->CreateAdd(newConsumedOffset, unconsumedChunks);
            Value * const targetLinear = b->CreateICmpULE(newConsumedOffsetEnd, newProducedOffset);
            Value * const linearCopy = b->CreateAnd(sourceLinear, targetLinear);

            Value * const consumedOffsetPtr = b->CreateInBoundsGEP(virtualBase, consumedOffset);
            Value * const newConsumedOffsetPtr = b->CreateInBoundsGEP(newBuffer, newConsumedOffset);

            BasicBlock * const copyLinear = BasicBlock::Create(C, "copyLinear", func);
            BasicBlock * const copyNonLinear = BasicBlock::Create(C, "copyNonLinear", func);
            BasicBlock * const storeNewBuffer = BasicBlock::Create(C, "storeNewBuffer", func);
            b->CreateCondBr(linearCopy, copyLinear, copyNonLinear);

            b->SetInsertPoint(copyLinear);
            b->CreateMemCpy(newConsumedOffsetPtr, consumedOffsetPtr, bytesToCopy, blockSize);
            b->CreateBr(storeNewBuffer);

            b->SetInsertPoint(copyNonLinear);
            Value * const bufferLength1 = b->CreateSub(internalCapacity, consumedOffset);
            Value * const newBufferLength1 = b->CreateSub(newCapacity, newConsumedOffset);
            Value * const partialLength1 = b->CreateUMin(bufferLength1, newBufferLength1);
            Value * const copyEndPtr = b->CreateInBoundsGEP(virtualBase, b->CreateAdd(consumedOffset, partialLength1));
            Value * const copyEndPtrInt = b->CreatePtrToInt(copyEndPtr, intPtrTy);
            Value * const consumedOffsetPtrInt = b->CreatePtrToInt(consumedOffsetPtr, intPtrTy);
            Value * const bytesToCopy1 = b->CreateSub(copyEndPtrInt, consumedOffsetPtrInt);
            b->CreateMemCpy(newConsumedOffsetPtr, consumedOffsetPtr, bytesToCopy1, blockSize);
            Value * const sourceOffset = b->CreateURem(b->CreateAdd(consumedOffset, partialLength1), internalCapacity);
            Value * const sourcePtr = b->CreateInBoundsGEP(virtualBase, sourceOffset);
            Value * const targetOffset = b->CreateURem(b->CreateAdd(newConsumedOffset, partialLength1), newCapacity);
            Value * const targetPtr = b->CreateInBoundsGEP(newBuffer, targetOffset);
            Value * const bytesToCopy2 = b->CreateSub(bytesToCopy, bytesToCopy1);
            b->CreateMemCpy(targetPtr, sourcePtr, bytesToCopy2, blockSize);
            b->CreateBr(storeNewBuffer);

            b->SetInsertPoint(storeNewBuffer);
            indices[1] = b->getInt32(AlternateAddress);
            Value * const priorBufferField = b->CreateInBoundsGEP(handle, indices);
            Value * const priorBuffer = b->CreateLoad(priorBufferField);
            b->CreateStore(newBuffer, virtualBaseField);
            b->CreateAlignedStore(newCapacity, intCapacityField, sizeTyWidth);
            b->CreateAlignedStore(virtualBase, priorBufferField, sizeTyWidth);
            b->CreateFree(b->CreateInBoundsGEP(priorBuffer, { b->CreateNeg(underflow) }));

            b->CreateRet(b->getTrue());
        }

        b->restoreIP(ip);
        setHandle(myHandle);
    }

    SmallVector<Value *, 8> args(6);
    args[0] = myHandle;
    args[1] = produced;
    args[2] = consumed;
    args[3] = required;
    args[4] = b->getSize(mUnderflow);
    args[5] = b->getSize(mOverflow);
    if (hasSyncLock) {
        args.push_back(syncLock);
        args.push_back(segNo);
    }
    return b->CreateCall(func->getFunctionType(), func, args);
}

#endif

// Constructors

ExternalBuffer::ExternalBuffer(const unsigned id, BuilderPtr b, Type * const type,
                               const bool linear,
                               const unsigned AddressSpace)
: StreamSetBuffer(id, BufferKind::ExternalBuffer, b, type, 0, 0, linear, AddressSpace) {

}

StaticBuffer::StaticBuffer(const unsigned id, BuilderPtr b, Type * const type,
                           const size_t capacity, const size_t overflowSize, const size_t underflowSize,
                           const bool linear, const unsigned AddressSpace)
: InternalBuffer(id, BufferKind::StaticBuffer, b, type, overflowSize, underflowSize, linear, AddressSpace)
, mCapacity(capacity) {
    #ifndef NDEBUG
    assert ("static buffer cannot have 0 capacity" && capacity);
    assert ("static buffer capacity must be at least twice its max(underflow, overflow)"
            && (capacity >= (std::max(underflowSize, overflowSize) * 2)));
    #endif
}

DynamicBuffer::DynamicBuffer(const unsigned id, BuilderPtr b, Type * const type,
                             const size_t initialCapacity, const size_t overflowSize, const size_t underflowSize,
                             const bool linear, const unsigned AddressSpace)
: InternalBuffer(id, BufferKind::DynamicBuffer, b, type, overflowSize, underflowSize, linear, AddressSpace)
, mInitialCapacity(initialCapacity) {
    #ifndef NDEBUG
    assert ("dynamic buffer cannot have 0 initial capacity" && initialCapacity);
    assert ("dynamic buffer initial capacity must be at least twice its max(underflow, overflow)"
            && (initialCapacity >= (std::max(underflowSize, overflowSize) * 2)));
    #endif
}

inline InternalBuffer::InternalBuffer(const unsigned id, const BufferKind k, BuilderPtr b, Type * const baseType,
                                      const size_t overflowSize, const size_t underflowSize,
                                      const bool linear, const unsigned AddressSpace)
: StreamSetBuffer(id, k, b, baseType, overflowSize, underflowSize, linear, AddressSpace) {

}

inline StreamSetBuffer::StreamSetBuffer(const unsigned id, const BufferKind k, BuilderPtr b, Type * const baseType,
                                        const size_t overflowSize, const size_t underflowSize,
                                        const bool linear, const unsigned AddressSpace)
: mId(id)
, mBufferKind(k)
, mHandle(nullptr)
, mType(resolveType(b, baseType))
, mBaseType(baseType)
, mOverflow(overflowSize)
, mUnderflow(underflowSize)
, mAddressSpace(AddressSpace)
, mLinear(linear || isEmptySet()) {

}

StreamSetBuffer::~StreamSetBuffer() { }

}
