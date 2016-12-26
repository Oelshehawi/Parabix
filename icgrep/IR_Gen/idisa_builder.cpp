/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include "idisa_builder.h"
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/TypeBuilder.h>

namespace IDISA {

VectorType * IDISA_Builder::fwVectorType(unsigned fw) {
    int fieldCount = mBitBlockWidth/fw;
    return VectorType::get(getIntNTy(fw), fieldCount);
}

Value * IDISA_Builder::fwCast(unsigned fw, Value * a) {
    return a->getType() == fwVectorType(fw) ? a : CreateBitCast(a, fwVectorType(fw));
}

std::string IDISA_Builder::getBitBlockTypeName() const {
    const auto type = getBitBlockType();
    if (type->isIntegerTy()) {
        return "i" + std::to_string(getBitBlockWidth());
    }
    assert("BitBlockType is neither integer nor vector" && type->isVectorTy());
    const auto fw = type->getScalarSizeInBits();
    return "v" + std::to_string(getBitBlockWidth() / fw) + "i" + std::to_string(fw);
}

    
static Function * create_printf(Module * const mod, IDISA_Builder * builder) {
    Function * printf = mod->getFunction("printf");
    if (printf == nullptr) {
        printf = cast<Function>(mod->getOrInsertFunction("printf"
                                , FunctionType::get(builder->getInt32Ty(), {builder->getInt8PtrTy()}, true)
                                , AttributeSet().addAttribute(mod->getContext(), 1U, Attribute::NoAlias)));

    }
    return printf;
}

void IDISA_Builder::CallPrintRegister(const std::string & name, Value * const value) {
    Constant * printRegister = mMod->getFunction("PrintRegister");
    if (LLVM_UNLIKELY(printRegister == nullptr)) {
        FunctionType *FT = FunctionType::get(getVoidTy(), { PointerType::get(getInt8Ty(), 0), mBitBlockType }, false);
        Function * function = Function::Create(FT, Function::InternalLinkage, "PrintRegister", mMod);
        auto arg = function->arg_begin();
        std::string tmp;
        raw_string_ostream out(tmp);
        out << "%-40s =";
        for(unsigned i = 0; i < (mBitBlockWidth / 8); ++i) {
            out << " %02x";
        }
        out << '\n';
        BasicBlock * entry = BasicBlock::Create(mMod->getContext(), "entry", function);
        IRBuilder<> builder(entry);
        std::vector<Value *> args;
        args.push_back(CreateGlobalStringPtr(out.str().c_str()));
        Value * const name = &*(arg++);
        name->setName("name");
        args.push_back(name);
        Value * value = &*arg;
        value->setName("value");
        Type * const byteVectorType = VectorType::get(getInt8Ty(), (mBitBlockWidth / 8));
        value = builder.CreateBitCast(value, byteVectorType);
        for(unsigned i = (mBitBlockWidth / 8); i != 0; --i) {
            args.push_back(builder.CreateExtractElement(value, builder.getInt32(i - 1)));
        }
        builder.CreateCall(create_printf(mMod, this), args);
        builder.CreateRetVoid();

        printRegister = function;
    }
    if (value->getType()->canLosslesslyBitCastTo(mBitBlockType)) {
        CreateCall(printRegister, {CreateGlobalStringPtr(name.c_str()), CreateBitCast(value, mBitBlockType)});
    }
}

void IDISA_Builder::CallPrintInt(const std::string & name, Value * const value) {
    Constant * printRegister = mMod->getFunction("PrintInt");
    if (LLVM_UNLIKELY(printRegister == nullptr)) {
        FunctionType *FT = FunctionType::get(getVoidTy(), { PointerType::get(getInt8Ty(), 0), getSizeTy() }, false);
        Function * function = Function::Create(FT, Function::InternalLinkage, "PrintInt", mMod);
        auto arg = function->arg_begin();
        std::string out = "%-40s = %" PRIx64 "\n";
        BasicBlock * entry = BasicBlock::Create(mMod->getContext(), "entry", function);
        IRBuilder<> builder(entry);
        std::vector<Value *> args;
        args.push_back(CreateGlobalStringPtr(out.c_str()));
        Value * const name = &*(arg++);
        name->setName("name");
        args.push_back(name);
        Value * value = &*arg;
        value->setName("value");
        args.push_back(value);
        builder.CreateCall(create_printf(mMod, this), args);
        builder.CreateRetVoid();

        printRegister = function;
    }
    Value * num = nullptr;
    if (value->getType()->isPointerTy()) {
        num = CreatePtrToInt(value, getSizeTy());
    } else {
        num = CreateZExtOrBitCast(value, getSizeTy());
    }
    assert (num->getType()->isIntegerTy());
    CreateCall(printRegister, {CreateGlobalStringPtr(name.c_str()), num});
}

Value * IDISA_Builder::CreateMalloc(Type * type, Value * size) {
    DataLayout DL(getModule());
    Type * const intTy = getIntPtrTy(DL);
    Type * const voidPtrTy = getVoidPtrTy();
    Function * malloc = cast<Function>(getModule()->getOrInsertFunction("malloc", voidPtrTy, intTy, nullptr));
    malloc->setDoesNotAlias(0);
    const auto width = ConstantExpr::getSizeOf(type);
    if (!width->isOneValue()) {
        if (isa<Constant>(size)) {
            size = ConstantExpr::getMul(cast<Constant>(size), width);
        } else {
            size = CreateMul(size, width);
        }
    }
    size = CreateTruncOrBitCast(size, intTy);
    CallInst * ci = CreateCall(malloc, {size});
    ci->setTailCall();
    ci->setCallingConv(malloc->getCallingConv());
    return CreateBitOrPointerCast(ci, type->getPointerTo());
}

Value * IDISA_Builder::CreateAlignedMalloc(Type * type, Value * size, const unsigned alignment) {
    assert ((alignment & (alignment - 1)) == 0); // is power of 2
    DataLayout DL(getModule());
    IntegerType * const intTy = getIntPtrTy(DL);
    const auto byteWidth = (intTy->getBitWidth() / 8);
    const auto offset = ConstantInt::get(intTy, alignment + byteWidth - 1);
    const auto width = ConstantExpr::getSizeOf(type);
    if (!width->isOneValue()) {
        if (isa<Constant>(size)) {
            size = ConstantExpr::getMul(cast<Constant>(size), width);
        } else {
            size = CreateMul(size, width);
        }
    }
    if (isa<Constant>(size)) {
        size = ConstantExpr::getAdd(cast<Constant>(size), offset);
    } else {
        size = CreateAdd(size, offset);
    }
    size = CreateTruncOrBitCast(size, intTy);
    Value * unaligned = CreateMalloc(getInt8Ty(), size);
    Value * aligned = CreateBitOrPointerCast(unaligned, intTy);
    aligned = CreateAnd(CreateAdd(aligned, offset), ConstantExpr::getNot(ConstantInt::get(intTy, alignment - 1)));
    Value * ptr = CreateBitOrPointerCast(CreateSub(aligned, ConstantInt::get(intTy, byteWidth)), intTy->getPointerTo());
    CreateAlignedStore(CreateBitOrPointerCast(unaligned, intTy), ptr, byteWidth);
    return CreateBitOrPointerCast(aligned, type->getPointerTo());
}

void IDISA_Builder::CreateFree(Value * ptr) {
    PointerType * const voidPtrTy = getVoidPtrTy();
    Function * const free = cast<Function>(getModule()->getOrInsertFunction("free", getVoidTy(), voidPtrTy, nullptr));
    CallInst * const ci = CreateCall(free, {CreateBitOrPointerCast(ptr, voidPtrTy)});
    ci->setTailCall();
    ci->setCallingConv(free->getCallingConv());
}

void IDISA_Builder::CreateAlignedFree(Value * ptr) {
    DataLayout DL(getModule());
    IntegerType * const intTy = getIntPtrTy(DL);
    const auto byteWidth = (intTy->getBitWidth() / 8);
    ptr = CreateBitOrPointerCast(ptr, intTy);
    ptr = CreateSub(ptr, ConstantInt::get(intTy, byteWidth));
    ptr = CreateBitOrPointerCast(ptr, getInt8PtrTy());
    CreateFree(CreateAlignedLoad(ptr, byteWidth));
}

Value * IDISA_Builder::CreateRealloc(Value * ptr, Value * size) {
    assert (ptr->getType()->isPointerTy());
    DataLayout DL(getModule());
    IntegerType * const intTy = getIntPtrTy(DL);
    PointerType * const voidPtrTy = getVoidPtrTy();
    Function * realloc = cast<Function>(getModule()->getOrInsertFunction("realloc", voidPtrTy, voidPtrTy, intTy, nullptr));
    realloc->setDoesNotAlias(0);
    Type * const type = ptr->getType();
    // calculate our new size parameter
    size = CreateMul(size, ConstantExpr::getSizeOf(type->getPointerElementType()));
    size = CreateTruncOrBitCast(size, intTy);
    // call realloc with the pointer and adjusted size
    CallInst * ci = CreateCall(realloc, {ptr, size});
    ci->setTailCall();
    ci->setCallingConv(realloc->getCallingConv());
    return CreateBitOrPointerCast(ci, type);
}

Value * IDISA_Builder::CreateAlignedRealloc(Value * ptr, Value * size, const unsigned alignment) {
    assert ((alignment & (alignment - 1)) == 0); // is power of 2
    assert (ptr->getType()->isPointerTy());
    DataLayout DL(getModule());
    IntegerType * const intTy = getIntPtrTy(DL);
    PointerType * const bpTy = getInt8PtrTy();
    Type * const type = ptr->getType();
    // calculate our new size parameter
    const auto byteWidth = (intTy->getBitWidth() / 8);
    const auto offset = ConstantInt::get(intTy, alignment + byteWidth - 1);
    const auto width = ConstantExpr::getSizeOf(type);
    if (!width->isOneValue()) {
        if (isa<Constant>(size)) {
            size = ConstantExpr::getMul(cast<Constant>(size), width);
        } else {
            size = CreateMul(size, width);
        }
    }
    if (isa<Constant>(size)) {
        size = ConstantExpr::getAdd(cast<Constant>(size), offset);
    } else {
        size = CreateAdd(size, offset);
    }
    size = CreateTruncOrBitCast(size, intTy);
    // calculate the offset containing the unaligned pointer address
    ptr = CreateBitOrPointerCast(ptr, bpTy);
    ptr = CreateSub(ptr, ConstantInt::get(intTy, byteWidth));
    ptr = CreateBitOrPointerCast(ptr, intTy->getPointerTo());
    // load the unaligned pointer as an uint8 *
    ptr = CreateAlignedLoad(ptr, byteWidth);
    ptr = CreateBitOrPointerCast(ptr, bpTy);
    // call realloc with the unaligned pointer and adjusted size
    Value * unaligned = CreateRealloc(ptr, size);
    Value * aligned = CreateBitOrPointerCast(unaligned, intTy);
    aligned = CreateAnd(CreateAdd(aligned, offset), ConstantExpr::getNot(ConstantInt::get(intTy, alignment - 1)));
    Value * prefix = CreateBitOrPointerCast(CreateSub(aligned, ConstantInt::get(intTy, byteWidth)), intTy->getPointerTo());
    CreateAlignedStore(CreateBitOrPointerCast(unaligned, intTy), prefix, byteWidth);
    return CreateBitOrPointerCast(aligned, type);
}

void IDISA_Builder::CreateMemZero(Value * ptr, Value * size, const unsigned alignment) {
    assert (ptr->getType()->isPointerTy() && size->getType()->isIntegerTy());
    Type * const type = ptr->getType();
    const auto width = ConstantExpr::getSizeOf(type->getPointerElementType());
    if (isa<Constant>(size)) {
        size = ConstantExpr::getMul(cast<Constant>(size), width);
    } else {
        size = CreateMul(size, width);
    }
    CreateMemSet(CreateBitOrPointerCast(ptr, getInt8PtrTy()), getInt8(0), size, alignment);
}

PointerType * IDISA_Builder::getVoidPtrTy() const {
    return TypeBuilder<void *, false>::get(getContext());
}

Constant * IDISA_Builder::simd_himask(unsigned fw) {
    return Constant::getIntegerValue(getIntNTy(mBitBlockWidth), APInt::getSplat(mBitBlockWidth, APInt::getHighBitsSet(fw, fw/2)));
}

Constant * IDISA_Builder::simd_lomask(unsigned fw) {
    return Constant::getIntegerValue(getIntNTy(mBitBlockWidth), APInt::getSplat(mBitBlockWidth, APInt::getLowBitsSet(fw, fw/2)));
}

Value * IDISA_Builder::simd_fill(unsigned fw, Value * a) {
    unsigned field_count = mBitBlockWidth/fw;
    Type * singleFieldVecTy = VectorType::get(getIntNTy(fw), 1);
    Value * aVec = CreateBitCast(a, singleFieldVecTy);
    return CreateShuffleVector(aVec, UndefValue::get(singleFieldVecTy), Constant::getNullValue(VectorType::get(getInt32Ty(), field_count)));
}

Value * IDISA_Builder::simd_add(unsigned fw, Value * a, Value * b) {
    return CreateAdd(fwCast(fw, a), fwCast(fw, b));
}

Value * IDISA_Builder::simd_sub(unsigned fw, Value * a, Value * b) {
    return CreateSub(fwCast(fw, a), fwCast(fw, b));
}

Value * IDISA_Builder::simd_mult(unsigned fw, Value * a, Value * b) {
    return CreateMul(fwCast(fw, a), fwCast(fw, b));
}

Value * IDISA_Builder::simd_eq(unsigned fw, Value * a, Value * b) {
    return CreateSExt(CreateICmpEQ(fwCast(fw, a), fwCast(fw, b)), fwVectorType(fw));
}

Value * IDISA_Builder::simd_gt(unsigned fw, Value * a, Value * b) {
    return CreateSExt(CreateICmpSGT(fwCast(fw, a), fwCast(fw, b)), fwVectorType(fw));
}

Value * IDISA_Builder::simd_ugt(unsigned fw, Value * a, Value * b) {
    return CreateSExt(CreateICmpUGT(fwCast(fw, a), fwCast(fw, b)), fwVectorType(fw));
}

Value * IDISA_Builder::simd_lt(unsigned fw, Value * a, Value * b) {
    return CreateSExt(CreateICmpSLT(fwCast(fw, a), fwCast(fw, b)), fwVectorType(fw));
}

Value * IDISA_Builder::simd_ult(unsigned fw, Value * a, Value * b) {
    return CreateSExt(CreateICmpULT(fwCast(fw, a), fwCast(fw, b)), fwVectorType(fw));
}

Value * IDISA_Builder::simd_max(unsigned fw, Value * a, Value * b) {
    Value * aVec = fwCast(fw, a);
    Value * bVec = fwCast(fw, b);
    return CreateSelect(CreateICmpSGT(aVec, bVec), aVec, bVec);
}

Value * IDISA_Builder::simd_umax(unsigned fw, Value * a, Value * b) {
    Value * aVec = fwCast(fw, a);
    Value * bVec = fwCast(fw, b);
    return CreateSelect(CreateICmpUGT(aVec, bVec), aVec, bVec);
}

Value * IDISA_Builder::simd_min(unsigned fw, Value * a, Value * b) {
    Value * aVec = fwCast(fw, a);
    Value * bVec = fwCast(fw, b);
    return CreateSelect(CreateICmpSLT(aVec, bVec), aVec, bVec);
}

Value * IDISA_Builder::simd_umin(unsigned fw, Value * a, Value * b) {
    Value * aVec = fwCast(fw, a);
    Value * bVec = fwCast(fw, b);
    return CreateSelect(CreateICmpULT(aVec, bVec), aVec, bVec);
}

Value * IDISA_Builder::simd_slli(unsigned fw, Value * a, unsigned shift) {
    return CreateShl(fwCast(fw, a), shift);
}

Value * IDISA_Builder::simd_srli(unsigned fw, Value * a, unsigned shift) {
    return CreateLShr(fwCast(fw, a), shift);
}

Value * IDISA_Builder::simd_srai(unsigned fw, Value * a, unsigned shift) {
    return CreateAShr(fwCast(fw, a), shift);
}

Value * IDISA_Builder::simd_cttz(unsigned fw, Value * a) {
    Value * cttzFunc = Intrinsic::getDeclaration(mMod, Intrinsic::cttz, fwVectorType(fw));
    Value * rslt = CreateCall(cttzFunc, std::vector<Value *>({fwCast(fw, a), ConstantInt::get(getInt1Ty(), 0)}));
    return rslt;
}

Value * IDISA_Builder::simd_popcount(unsigned fw, Value * a) {
    Value * ctpopFunc = Intrinsic::getDeclaration(mMod, Intrinsic::ctpop, fwVectorType(fw));
    Value * rslt = CreateCall(ctpopFunc, std::vector<Value *>({fwCast(fw, a)}));
    return rslt;
}

Value * IDISA_Builder::simd_if(unsigned fw, Value * cond, Value * a, Value * b) {
    if (fw == 1) {
        Value * a1 = bitCast(a);
        Value * b1 = bitCast(b);
        Value * c = bitCast(cond);
        return CreateOr(CreateAnd(a1, c), CreateAnd(CreateXor(c, b1), b1));
    }
    else {
        Value * aVec = fwCast(fw, a);
        Value * bVec = fwCast(fw, b);
        return CreateSelect(CreateICmpSLT(cond, mZeroInitializer), aVec, bVec);
    }
}

    
Value * IDISA_Builder::esimd_mergeh(unsigned fw, Value * a, Value * b) {
    unsigned field_count = mBitBlockWidth/fw;
    Value * aVec = fwCast(fw, a);
    Value * bVec = fwCast(fw, b);
    std::vector<Constant*> Idxs;
    for (unsigned i = field_count/2; i < field_count; i++) {
        Idxs.push_back(getInt32(i));    // selects elements from first reg.
        Idxs.push_back(getInt32(i + field_count)); // selects elements from second reg.
    }
    return CreateShuffleVector(aVec, bVec, ConstantVector::get(Idxs));
}

Value * IDISA_Builder::esimd_mergel(unsigned fw, Value * a, Value * b) {
    unsigned field_count = mBitBlockWidth/fw;
    Value * aVec = fwCast(fw, a);
    Value * bVec = fwCast(fw, b);
    std::vector<Constant*> Idxs;
    for (unsigned i = 0; i < field_count/2; i++) {
        Idxs.push_back(getInt32(i));    // selects elements from first reg.
        Idxs.push_back(getInt32(i + field_count)); // selects elements from second reg.
    }
    return CreateShuffleVector(aVec, bVec, ConstantVector::get(Idxs));
}

Value * IDISA_Builder::esimd_bitspread(unsigned fw, Value * bitmask) {
    unsigned field_count = mBitBlockWidth/fw;
    Type * field_type = getIntNTy(fw);
    if (bitmask->getType()->getIntegerBitWidth() < fw) {
        bitmask = CreateZExt(bitmask, field_type);
    }
    else if (bitmask->getType()->getIntegerBitWidth() > fw) {
        bitmask = CreateTrunc(bitmask, field_type);
    }
    Value * spread_field = CreateBitCast(bitmask, VectorType::get(getIntNTy(fw), 1));
    Value * undefVec = UndefValue::get(VectorType::get(getIntNTy(fw), 1));
    Value * broadcast = CreateShuffleVector(spread_field, undefVec, Constant::getNullValue(VectorType::get(getInt32Ty(), field_count)));
    std::vector<Constant*> bitSel;
    std::vector<Constant*> bitShift;
    for (unsigned i = 0; i < field_count; i++) {
        bitSel.push_back(ConstantInt::get(field_type, 1 << i));
        bitShift.push_back(ConstantInt::get(field_type, i));
    }
    Value * bitSelVec = ConstantVector::get(bitSel);
    Value * bitShiftVec = ConstantVector::get(bitShift);
    return CreateLShr(CreateAnd(bitSelVec, broadcast), bitShiftVec);
}

Value * IDISA_Builder::hsimd_packh(unsigned fw, Value * a, Value * b) {
    unsigned field_count = 2 * mBitBlockWidth/fw;
    Value * aVec = fwCast(fw/2, a);
    Value * bVec = fwCast(fw/2, b);
    std::vector<Constant*> Idxs;
    for (unsigned i = 0; i < field_count; i++) {
        Idxs.push_back(getInt32(2*i+1));
    }
    return CreateShuffleVector(aVec, bVec, ConstantVector::get(Idxs));
}

Value * IDISA_Builder::hsimd_packl(unsigned fw, Value * a, Value * b) {
    unsigned field_count = 2 * mBitBlockWidth/fw;
    Value * aVec = fwCast(fw/2, a);
    Value * bVec = fwCast(fw/2, b);
    std::vector<Constant*> Idxs;
    for (unsigned i = 0; i < field_count; i++) {
        Idxs.push_back(getInt32(2*i));
    }
    return CreateShuffleVector(aVec, bVec, ConstantVector::get(Idxs));
}

    
Value * IDISA_Builder::hsimd_packh_in_lanes(unsigned lanes, unsigned fw, Value * a, Value * b) {
    unsigned fw_out = fw/2;
    unsigned fields_per_lane = mBitBlockWidth/(fw_out * lanes);
    unsigned field_offset_for_b = mBitBlockWidth/fw_out;
    Value * aVec = fwCast(fw_out, a);
    Value * bVec = fwCast(fw_out, b);
    std::vector<Constant*> Idxs;
    for (unsigned lane = 0; lane < lanes; lane++) {
        unsigned first_field_in_lane = lane * fields_per_lane; // every second field
        for (unsigned i = 0; i < fields_per_lane/2; i++) {
            Idxs.push_back(getInt32(first_field_in_lane + 2*i + 1));
        }
        for (unsigned i = 0; i < fields_per_lane/2; i++) {
            Idxs.push_back(getInt32(field_offset_for_b + first_field_in_lane + 2*i + 1));
        }
    }
    Value * pack = CreateShuffleVector(aVec, bVec, ConstantVector::get(Idxs));
    return pack;
}

Value * IDISA_Builder::hsimd_packl_in_lanes(unsigned lanes, unsigned fw, Value * a, Value * b) {
    unsigned fw_out = fw/2;
    unsigned fields_per_lane = mBitBlockWidth/(fw_out * lanes);
    unsigned field_offset_for_b = mBitBlockWidth/fw_out;
    Value * aVec = fwCast(fw_out, a);
    Value * bVec = fwCast(fw_out, b);
    std::vector<Constant*> Idxs;
    for (unsigned lane = 0; lane < lanes; lane++) {
        unsigned first_field_in_lane = lane * fields_per_lane; // every second field
        for (unsigned i = 0; i < fields_per_lane/2; i++) {
            Idxs.push_back(getInt32(first_field_in_lane + 2*i));
        }
        for (unsigned i = 0; i < fields_per_lane/2; i++) {
            Idxs.push_back(getInt32(field_offset_for_b + first_field_in_lane + 2*i));
        }
    }
    Value * pack = CreateShuffleVector(aVec, bVec, ConstantVector::get(Idxs));
    return pack;
}

    
Value * IDISA_Builder::hsimd_signmask(unsigned fw, Value * a) {
    Value * mask = CreateICmpSLT(fwCast(fw, a), ConstantAggregateZero::get(fwVectorType(fw)));
    return CreateZExt(CreateBitCast(mask, getIntNTy(mBitBlockWidth/fw)), getInt32Ty());
}

Value * IDISA_Builder::mvmd_extract(unsigned fw, Value * a, unsigned fieldIndex) {
    return CreateExtractElement(fwCast(fw, a), getInt32(fieldIndex));
}

Value * IDISA_Builder::mvmd_insert(unsigned fw, Value * blk, Value * elt, unsigned fieldIndex) {
    Value * vec = fwCast(fw, blk);
    return CreateInsertElement(vec, elt, getInt32(fieldIndex));
}

Value * IDISA_Builder::mvmd_slli(unsigned fw, Value * a, unsigned shift) {
    unsigned field_count = mBitBlockWidth/fw;
    return mvmd_dslli(fw, a, Constant::getNullValue(fwVectorType(fw)), field_count - shift);
}

Value * IDISA_Builder::mvmd_srli(unsigned fw, Value * a, unsigned shift) {
    return mvmd_dslli(fw, Constant::getNullValue(fwVectorType(fw)), a, shift);
}

Value * IDISA_Builder::mvmd_dslli(unsigned fw, Value * a, Value * b, unsigned shift) {
    unsigned field_count = mBitBlockWidth/fw;
    Value * aVec = fwCast(fw, a);
    Value * bVec = fwCast(fw, b);
    std::vector<Constant*> Idxs;
    for (unsigned i = 0; i < field_count; i++) {
        Idxs.push_back(getInt32(i + shift));
    }
    return CreateShuffleVector(bVec, aVec, ConstantVector::get(Idxs));
}

Value * IDISA_Builder::bitblock_any(Value * a) {
    Type * iBitBlock = getIntNTy(mBitBlockWidth);
    return CreateICmpNE(CreateBitCast(a, iBitBlock),  ConstantInt::get(iBitBlock, 0));
}

// full add producing {carryout, sum}
std::pair<Value *, Value *> IDISA_Builder::bitblock_add_with_carry(Value * a, Value * b, Value * carryin) {
    Value * carrygen = simd_and(a, b);
    Value * carryprop = simd_or(a, b);
    Value * sum = simd_add(mBitBlockWidth, simd_add(mBitBlockWidth, a, b), carryin);
    Value * carryout = CreateBitCast(simd_or(carrygen, simd_and(carryprop, CreateNot(sum))), getIntNTy(mBitBlockWidth));
    return std::pair<Value *, Value *>(bitCast(simd_srli(mBitBlockWidth, carryout, mBitBlockWidth - 1)), bitCast(sum));
}

// full shift producing {shiftout, shifted}
std::pair<Value *, Value *> IDISA_Builder::bitblock_advance(Value * a, Value * shiftin, unsigned shift) {
    Value * shiftin_bitblock = CreateBitCast(shiftin, getIntNTy(mBitBlockWidth));
    Value * a_bitblock = CreateBitCast(a, getIntNTy(mBitBlockWidth));
    Value * shifted = bitCast(CreateOr(CreateShl(a_bitblock, shift), shiftin_bitblock));
    Value * shiftout = bitCast(CreateLShr(a_bitblock, mBitBlockWidth - shift));
    return std::pair<Value *, Value *>(shiftout, shifted);
}

Value * IDISA_Builder::bitblock_mask_from(Value * pos) {
    Type * bitBlockInt = getIntNTy(getBitBlockWidth());
    return bitCast(CreateShl(ConstantInt::getAllOnesValue(bitBlockInt), CreateZExt(pos, bitBlockInt)));
    
}
Value * IDISA_Builder::bitblock_set_bit(Value * pos) {
    Type * bitBlockInt = getIntNTy(getBitBlockWidth());
    return bitCast(CreateShl(ConstantInt::get(bitBlockInt, 1), CreateZExt(pos, bitBlockInt)));
}


Value * IDISA_Builder::simd_and(Value * a, Value * b) {
    return a->getType() == b->getType() ? CreateAnd(a, b) : CreateAnd(bitCast(a), bitCast(b));
}

Value * IDISA_Builder::simd_or(Value * a, Value * b) {
    return a->getType() == b->getType() ? CreateOr(a, b) : CreateOr(bitCast(a), bitCast(b));
}
    
Value * IDISA_Builder::simd_xor(Value * a, Value * b) {
    return a->getType() == b->getType() ? CreateXor(a, b) : CreateXor(bitCast(a), bitCast(b));
}

Value * IDISA_Builder::simd_not(Value * a) {
    return simd_xor(a, Constant::getAllOnesValue(a->getType()));
}

LoadInst * IDISA_Builder::CreateAtomicLoadAcquire(Value * ptr) {
    unsigned alignment = dyn_cast<PointerType>(ptr->getType())->getElementType()->getPrimitiveSizeInBits()/8;
    LoadInst * inst = CreateAlignedLoad(ptr, alignment);
    inst->setOrdering(AtomicOrdering::Acquire);
    return inst;
    
}
StoreInst * IDISA_Builder::CreateAtomicStoreRelease(Value * val, Value * ptr) {
    unsigned alignment = dyn_cast<PointerType>(ptr->getType())->getElementType()->getPrimitiveSizeInBits()/8;
    StoreInst * inst = CreateAlignedStore(val, ptr, alignment);
    inst->setOrdering(AtomicOrdering::Release);
    return inst;
}

Type * IDISA_Builder::getStreamTy(const unsigned FieldWidth) {
    const auto f = mStreamTypes.find(FieldWidth);
    if (LLVM_LIKELY(f != mStreamTypes.end())) {
        return f->second;
    } else {
        StreamType * const T = new StreamType(getContext(), FieldWidth);
        mStreamTypes.emplace(FieldWidth, T);
        return T;
    }
}

}