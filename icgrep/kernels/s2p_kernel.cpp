/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */
#include "s2p_kernel.h"
#include <kernels/kernel.h>
#include <IDISA/idisa_builder.h>
#include <llvm/Support/raw_ostream.h>

namespace kernel {
using namespace llvm;

const int PACK_LANES = 1;

void s2p_step(IDISA::IDISA_Builder * iBuilder, Value * s0, Value * s1, Value * hi_mask, unsigned shift, Value * &p0, Value * &p1) {
    Value * t0 = nullptr;
    Value * t1 = nullptr;
    if ((iBuilder->getBitBlockWidth() == 256) && (PACK_LANES == 2)) {
        Value * x0 = iBuilder->esimd_mergel(128, s0, s1);
        Value * x1 = iBuilder->esimd_mergeh(128, s0, s1);
        t0 = iBuilder->hsimd_packh_in_lanes(PACK_LANES, 16, x0, x1);
        t1 = iBuilder->hsimd_packl_in_lanes(PACK_LANES, 16, x0, x1);
    }
    else {
        t0 = iBuilder->hsimd_packh(16, s0, s1);
        t1 = iBuilder->hsimd_packl(16, s0, s1);
    }
    p0 = iBuilder->simd_if(1, hi_mask, t0, iBuilder->simd_srli(16, t1, shift));
    p1 = iBuilder->simd_if(1, hi_mask, iBuilder->simd_slli(16, t0, shift), t1);
}

void s2p(IDISA::IDISA_Builder * iBuilder, Value * input[], Value * output[]) {
    Value * bit00224466[4];
    Value * bit11335577[4];

    for (unsigned i = 0; i < 4; i++) {
        Value * s0 = input[2 * i];
        Value * s1 = input[2 * i + 1];
        s2p_step(iBuilder, s0, s1, iBuilder->simd_himask(2), 1, bit00224466[i], bit11335577[i]);
    }
    Value * bit00004444[2];
    Value * bit22226666[2];
    Value * bit11115555[2];
    Value * bit33337777[2];
    for (unsigned j = 0; j<2; j++) {
        s2p_step(iBuilder, bit00224466[2*j], bit00224466[2*j+1],
                 iBuilder->simd_himask(4), 2, bit00004444[j], bit22226666[j]);
        s2p_step(iBuilder, bit11335577[2*j], bit11335577[2*j+1],
                 iBuilder->simd_himask(4), 2, bit11115555[j], bit33337777[j]);
    }
    s2p_step(iBuilder, bit00004444[0], bit00004444[1], iBuilder->simd_himask(8), 4, output[0], output[4]);
    s2p_step(iBuilder, bit11115555[0], bit11115555[1], iBuilder->simd_himask(8), 4, output[1], output[5]);
    s2p_step(iBuilder, bit22226666[0], bit22226666[1], iBuilder->simd_himask(8), 4, output[2], output[6]);
    s2p_step(iBuilder, bit33337777[0], bit33337777[1], iBuilder->simd_himask(8), 4, output[3], output[7]);
}

/* Alternative transposition model, but small field width packs are problematic. */
#if 0
void s2p_ideal(IDISA::IDISA_Builder * iBuilder, Value * input[], Value * output[]) {
    Value * hi_nybble[4];
    Value * lo_nybble[4];
    for (unsigned i = 0; i<4; i++) {
        Value * s0 = input[2*i];
        Value * s1 = input[2*i+1];
        hi_nybble[i] = iBuilder->hsimd_packh(8, s0, s1);
        lo_nybble[i] = iBuilder->hsimd_packl(8, s0, s1);
    }
    Value * pair01[2];
    Value * pair23[2];
    Value * pair45[2];
    Value * pair67[2];
    for (unsigned i = 0; i<2; i++) {
        pair01[i] = iBuilder->hsimd_packh(4, hi_nybble[2*i], hi_nybble[2*i+1]);
        pair23[i] = iBuilder->hsimd_packl(4, hi_nybble[2*i], hi_nybble[2*i+1]);
        pair45[i] = iBuilder->hsimd_packh(4, lo_nybble[2*i], lo_nybble[2*i+1]);
        pair67[i] = iBuilder->hsimd_packl(4, lo_nybble[2*i], lo_nybble[2*i+1]);
    }
    output[0] = iBuilder->hsimd_packh(2, pair01[0], pair01[1]);
    output[1] = iBuilder->hsimd_packl(2, pair01[0], pair01[1]);
    output[2] = iBuilder->hsimd_packh(2, pair23[0], pair23[1]);
    output[3] = iBuilder->hsimd_packl(2, pair23[0], pair23[1]);
    output[4] = iBuilder->hsimd_packh(2, pair45[0], pair45[1]);
    output[5] = iBuilder->hsimd_packl(2, pair45[0], pair45[1]);
    output[6] = iBuilder->hsimd_packh(2, pair67[0], pair67[1]);
    output[7] = iBuilder->hsimd_packl(2, pair67[0], pair67[1]);
}
#endif
    
    
#if 0


void generateS2P_16Kernel(Module *, IDISA::IDISA_Builder * iBuilder, KernelBuilder * kBuilder) {
    kBuilder->addInputStream(16, "unit_pack");
    for(unsigned i = 0; i < 16; i++) {
	    kBuilder->addOutputStream(1);
    }
    kBuilder->prepareFunction();

    Value * ptr = kBuilder->getInputStream(0);

    Value * lo[8];
    Value * hi[8];
    for (unsigned i = 0; i < 8; i++) {
        Value * s0 = iBuilder->CreateBlockAlignedLoad(ptr, {iBuilder->getInt32(0), iBuilder->getInt32(2 * i)});
        Value * s1 = iBuilder->CreateBlockAlignedLoad(ptr, {iBuilder->getInt32(0), iBuilder->getInt32(2 * i + 1)});
        lo[i] = iBuilder->hsimd_packl(16, s0, s1);
        hi[i] = iBuilder->hsimd_packh(16, s0, s1);
    }

    Value * output[16];
    s2p(iBuilder, lo, output);
    s2p(iBuilder, hi, output + 8);
    for (unsigned j = 0; j < 16; j++) {
        iBuilder->CreateBlockAlignedStore(output[j], kBuilder->getOutputStream(j));
    }
    kBuilder->finalize();
}
    
#endif
    
void S2PKernel::generateFinalBlockMethod() {
    /* Prepare the s2p final block function:
     assumption: if remaining bytes is greater than 0, it is safe to read a full block of bytes.
     if remaining bytes is zero, no read should be performed (e.g. for mmapped buffer).
     */
    auto savePoint = iBuilder->saveIP();
    Module * m = iBuilder->getModule();
    Function * doBlockFunction = m->getFunction(mKernelName + doBlock_suffix);
    Function * finalBlockFunction = m->getFunction(mKernelName + finalBlock_suffix);
    iBuilder->SetInsertPoint(BasicBlock::Create(iBuilder->getContext(), "fb_entry", finalBlockFunction, 0));
    
    Value * self = getParameter(finalBlockFunction, "self");
    Value * remainingBytes = getParameter(finalBlockFunction, "remainingBytes");
    
    BasicBlock * finalPartialBlock = BasicBlock::Create(iBuilder->getContext(), "partial", finalBlockFunction, 0);
    BasicBlock * finalEmptyBlock = BasicBlock::Create(iBuilder->getContext(), "empty", finalBlockFunction, 0);
    BasicBlock * exitBlock = BasicBlock::Create(iBuilder->getContext(), "exit", finalBlockFunction, 0);
    
    Value * emptyBlockCond = iBuilder->CreateICmpEQ(remainingBytes, iBuilder->getSize(0));
    iBuilder->CreateCondBr(emptyBlockCond, finalEmptyBlock, finalPartialBlock);
    iBuilder->SetInsertPoint(finalPartialBlock);
    iBuilder->CreateCall(doBlockFunction, {self});
    /* Adjust the produced item count */
    Value * produced = getProducedItemCount(self);
    produced = iBuilder->CreateSub(produced, ConstantInt::get(iBuilder->getSizeTy(), iBuilder->getStride()));
    setProducedItemCount(self, iBuilder->CreateAdd(produced, remainingBytes));
    
    iBuilder->CreateBr(exitBlock);
    
    iBuilder->SetInsertPoint(finalEmptyBlock);
    Value * blockNo = getScalarField(self, blockNoScalar);
    Value * basisBitsBlock_ptr = getStreamSetBlockPtr(self, "basisBits", blockNo);
    iBuilder->CreateStore(Constant::getNullValue(basisBitsBlock_ptr->getType()->getPointerElementType()), basisBitsBlock_ptr);
    iBuilder->CreateBr(exitBlock);
    
    iBuilder->SetInsertPoint(exitBlock);
    iBuilder->CreateRetVoid();
    iBuilder->restoreIP(savePoint);
}

    
void S2PKernel::generateDoBlockLogic(Value * self, Value * blockNo) {

    Value * byteStream = getStreamSetBlockPtr(self, "byteStream", blockNo);
    Value * basisBits = getStreamSetBlockPtr(self, "basisBits", blockNo);

    Value * bytepack[8];
    for (unsigned i = 0; i < 8; i++) {
        Value * ptr = iBuilder->CreateGEP(byteStream, {iBuilder->getInt32(0), iBuilder->getInt32(0), iBuilder->getInt32(i)});
        bytepack[i] = iBuilder->CreateBlockAlignedLoad(ptr);
    }
    Value * bitblock[8];
    s2p(iBuilder, bytepack, bitblock);
    for (unsigned i = 0; i < 8; ++i) {
        iBuilder->CreateBlockAlignedStore(bitblock[i], basisBits, {iBuilder->getInt32(0), iBuilder->getInt32(i)});
    }
    Value * produced = getProducedItemCount(self);
    produced = iBuilder->CreateAdd(produced, ConstantInt::get(iBuilder->getSizeTy(), iBuilder->getStride()));
    setProducedItemCount(self, produced);    
}
    
void S2PKernel::generateDoBlockMethod() {
    auto savePoint = iBuilder->saveIP();

    Function * doBlockFunction = iBuilder->getModule()->getFunction(mKernelName + doBlock_suffix);
    
    iBuilder->SetInsertPoint(BasicBlock::Create(iBuilder->getContext(), "entry", doBlockFunction, 0));
    
    Value * self = getParameter(doBlockFunction, "self");
    Value * blockNo = getScalarField(self, blockNoScalar);
    
    generateDoBlockLogic(self, blockNo);

    iBuilder->CreateRetVoid();
    iBuilder->restoreIP(savePoint);
}
}
