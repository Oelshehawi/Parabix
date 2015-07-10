/*
 *  Copyright (c) 2015 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#ifndef CARRY_MANAGER_H
#define CARRY_MANAGER_H
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Module.h>
#include <IDISA/idisa_builder.h>

/* 
 * Carry Data Manager.
 * 
 * Each PabloBlock (Main, If, While) has a contiguous data area for carry information.
 * The data area may be at a fixed or variable base offset from the base of the 
 * main function carry data area.
 * The data area for each block consists of contiguous space for the local carries and 
 * advances of the block plus the areas of any ifs/whiles nested within the block.

*/

using namespace llvm;

namespace pablo {

class PabloBlock;

class CarryManager {
public:
  
    CarryManager(Module * m, IRBuilder <> * b, VectorType * bitBlockType, ConstantAggregateZero * zero, Constant * one) :
        mMod(m), mBuilder(b), mBitBlockType(bitBlockType), mZeroInitializer(zero), mOneInitializer(one) {}
    
    unsigned initialize(PabloBlock * blk, Value * carryDataPtr);  
    
    void generateBlockNoIncrement();
    
    Value * getBlockNoPtr();
    
    /* Methods for processing individual carry-generating operations. */
    
    Value * getCarryOpCarryIn(PabloBlock * blk, int localIndex);

    void setCarryOpCarryOut(PabloBlock * blk, unsigned idx, Value * carry_out);

    Value * advanceCarryInCarryOut(PabloBlock * blk, int localIndex, int shift_amount, Value * strm);
 
    /* Methods for getting and setting carry summary values for If statements */
   
    bool blockHasCarries(PabloBlock & blk);
    
    Value * getCarrySummaryExpr(PabloBlock & blk);
    
    void generateCarryOutSummaryCode(PabloBlock & blk);
    
    bool summaryNeededInParentBlock(PabloBlock & blk);
    
    void addSummaryPhi(PabloBlock & blk, BasicBlock * ifEntryBlock, BasicBlock * ifBodyFinalBlock);
    
    /* Methods for load/store of carries for non-while blocks. */
    
    void ensureCarriesLoadedLocal(PabloBlock & blk);

    void ensureCarriesStoredLocal(PabloBlock & blk);
    
    /* Methods for handling while statements */
    
    void ensureCarriesLoadedRecursive(PabloBlock & whileBlk);

    void initializeCarryDataPhisAtWhileEntry(PabloBlock & whileBlk, BasicBlock * whileBodyFinalBlock);

    void extendCarryDataPhisAtWhileBodyFinalBlock(PabloBlock & whileBlk, BasicBlock * whileBodyFinalBlock);

    void ensureCarriesStoredRecursive(PabloBlock & whileBlk);

    
private:
    Module * mMod;
    IRBuilder <> * mBuilder;
    VectorType * mBitBlockType;
    ConstantAggregateZero * mZeroInitializer;
    Constant * mOneInitializer;
    IDISA::IDISA_Builder * iBuilder;
    PabloBlock * mPabloRoot;
    Value * mCarryDataPtr;
    Value * mBlockNoPtr;
    Value * mBlockNo;
    unsigned mTotalCarryDataSize;

    std::vector<Value *> mCarryInVector;
    std::vector<PHINode *> mCarryInPhis;  
    std::vector<PHINode *> mCarryOutAccumPhis;  
    std::vector<Value *> mCarryOutVector;

    Value * unitAdvanceCarryInCarryOut(PabloBlock * blk, int localIndex, Value * strm);
    Value * shortAdvanceCarryInCarryOut(PabloBlock * blk, int localIndex, int shift_amount, Value * strm);
    Value * longAdvanceCarryInCarryOut(PabloBlock * blk, int localIndex, int shift_amount, Value * strm);
    
};

}

#endif // CARRY_MANAGER_H
