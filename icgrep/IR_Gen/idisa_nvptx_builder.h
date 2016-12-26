#ifndef IDISA_NVPTX_BUILDER_H
#define IDISA_NVPTX_BUILDER_H

/*
 *  Copyright (c) 2015 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
*/

#include <IR_Gen/idisa_builder.h>
#include <IR_Gen/idisa_i64_builder.h>
#include <iostream>
using namespace llvm;

namespace IDISA {

class IDISA_NVPTX20_Builder : public IDISA_I64_Builder {
public:
    
    IDISA_NVPTX20_Builder(Module * m, unsigned groupSize)
    : IDISA_I64_Builder(m, 64, 64, 64 * groupSize)
    , groupThreads(groupSize) {
        CreateGlobals();
        CreateBuiltinFunctions();
        CreateLongAdvanceFunc();
        CreateLongAddFunc();
        CreateBallotFunc();
    }
    
    ~IDISA_NVPTX20_Builder() {}

    int getGroupThreads();
    
    Value * bitblock_any(Value * a) override;
    std::pair<Value *, Value *> bitblock_add_with_carry(Value * a, Value * b, Value * carryin) override;
    virtual std::pair<Value *, Value *> bitblock_advance(Value * a, Value * shiftin, unsigned shift) override;
    Value * bitblock_mask_from(Value * pos) override;
    Value * bitblock_set_bit(Value * pos) override;

    Value * getEOFMask(Value * remainingBytes);

    Value * Advance(const unsigned index, const unsigned shiftAmount, Value * const value);
    Value * LongAdd(Value * const valA, Value * const valB, Value * carryIn);

    LoadInst * CreateAtomicLoadAcquire(Value * ptr) override;
    StoreInst * CreateAtomicStoreRelease(Value * val, Value * ptr) override; 

private:
    void CreateGlobals();
    void CreateBuiltinFunctions();
    void CreateLongAdvanceFunc();
    void CreateLongAddFunc();
    void CreateBallotFunc();

    int                                 groupThreads;
    Function *                          barrierFunc;
    Function *                          tidFunc;
    Function *                          mLongAdvanceFunc;
    Function *                          mLongAddFunc;
    GlobalVariable*                     carry;
    GlobalVariable*                     bubble;
};

#if 0

class IDISA_NVPTX35_Builder : public IDISA_NVPTX20_Builder {
    IDISA_NVPTX35_Builder(Module * m, int groupSize) : IDISA_NVPTX30_Builder(m, groupSize) {}
    
    std::pair<Value *, Value *> bitblock_advance(Value * a, Value * shiftin, unsigned shift) override;

    ~IDISA_NVPTX35_Builder() {};

};
#endif    
    
}
#endif // IDISA_NVPTX_BUILDER_H