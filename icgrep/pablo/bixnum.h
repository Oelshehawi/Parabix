/*
 *  Copyright (c) 2019 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */

#ifndef PARABIX_ARITHMETIC_COMPILER_H
#define PARABIX_ARITHMETIC_COMPILER_H

#include <pablo/pabloAST.h>
#include <pablo/builder.hpp>

namespace pablo {

using BixNum = std::vector<PabloAST *>;
    
    
class BixNumCompiler {
public:
    BixNumCompiler(PabloBuilder & pb) : mPB(pb) {}
    PabloAST * EQ(BixNum value, unsigned test);
    PabloAST * EQ(BixNum value, BixNum test);
    PabloAST * NEQ(BixNum value, unsigned test);
    PabloAST * NEQ(BixNum value, BixNum test);
    PabloAST * UGE(BixNum value, unsigned floor);
    PabloAST * UGE(BixNum value, BixNum floor);
    PabloAST * UGT(BixNum value, unsigned floor);
    PabloAST * UGT(BixNum value, BixNum floor);
    PabloAST * ULE(BixNum value, unsigned floor);
    PabloAST * ULE(BixNum value, BixNum floor);
    PabloAST * ULT(BixNum value, unsigned floor);
    PabloAST * ULT(BixNum value, BixNum floor);
    BixNum ZeroExtend(BixNum value, unsigned extended_size);
    BixNum SignExtend(BixNum value, unsigned extended_size);
    BixNum Truncate(BixNum value, unsigned truncated_size);
    BixNum HighBits(BixNum value, unsigned highBitCount);
    //
    // Modular arithmetic operations
    BixNum AddModular(BixNum augend, unsigned addend);
    BixNum AddModular(BixNum augend, BixNum addend);
    BixNum SubModular(BixNum minuend, unsigned subtrahend);
    BixNum SubModular(BixNum minuend, BixNum subtrahend);
    BixNum MulModular(BixNum multiplicand, unsigned multiplier);
    //
    // Full arithmetic operations
    BixNum AddFull(BixNum augend, BixNum addend);
    BixNum MulFull(BixNum multiplicand, unsigned multiplier);

private:
    PabloBuilder & mPB;
};

// 
// A compiler that implements parallel bitwise table lookup for fixed tables.
// 
class BixNumTableCompiler {
public:
    BixNumTableCompiler(std::vector<unsigned> & table, BixNum & input, std::vector<Var *> & output) :
        mTable(table), mBitsPerOutputUnit(output.size()), mInput(input), mU16(output) {}
    void compileSubTable(PabloBuilder & pb, unsigned lo, unsigned hi, PabloAST * partitionSelect);

private:
    std::vector<unsigned> & mTable;
    unsigned mBitsPerOutputUnit;
    BixNum & mInput;
    std::vector<Var *> & mU16;
};

}


#endif

