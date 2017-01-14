/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */
#ifndef DELETION_H
#define DELETION_H

#include "streamset.h"
#include "interface.h"
#include "kernel.h"


namespace llvm { class Module; class Value;}

namespace IDISA { class IDISA_Builder; }

//
// Parallel Prefix Deletion 
// see Parallel Prefix Compress in Henry S. Warren, Hacker's Delight, Chapter 7
// 
// Given that we want to delete bits within fields of width fw, moving
// nondeleted bits to the right, the parallel prefix compress method can
// be applied.   This requires a preprocessing step to compute log2(fw) 
// masks that can be used to select bits to be moved in each step of the
// algorithm.
//

using namespace parabix;

namespace kernel {

class DeletionKernel : public kernel::KernelBuilder {
public:

    DeletionKernel(IDISA::IDISA_Builder * iBuilder, unsigned fw, unsigned streamCount);
    
protected:

    void generateDoBlockMethod() const override;

    void generateFinalBlockMethod() const override;

private:
    unsigned mDeletionFieldWidth;
    unsigned mStreamCount;
};

}
    
#endif

