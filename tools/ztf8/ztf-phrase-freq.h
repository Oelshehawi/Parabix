/*
 *  Copyright (c) 2019 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */
#ifndef ZTF_PHRASE_FREQ_H
#define ZTF_PHRASE_FREQ_H

#include <pablo/pablo_kernel.h>
#include <kernel/core/kernel_builder.h>
#include "ztf-logic.h"

namespace kernel {

class MarkFreqPhrases final : public MultiBlockKernel {
public:
    MarkFreqPhrases(BuilderRef b,
                           EncodingInfo encodingScheme,
                           unsigned groupNo,
                           unsigned numSyms,
                           unsigned offset,
                           StreamSet * lfData,
                           StreamSet * symEndMarks,
                           StreamSet * cmpMarksSoFar,
                           StreamSet * const hashValues,
                           StreamSet * const initFreq,
                           StreamSet * const byteData,
                           StreamSet * hashMarks,
                           StreamSet * secHashMarks,
                           StreamSet * hashValuesUpdated,
                           unsigned strideBlocks = 8);
private:
    void generateMultiBlockLogic(BuilderRef iBuilder, llvm::Value * const numOfStrides) override;

    const EncodingInfo mEncodingScheme;
    const unsigned mStrideSize;
    const unsigned mGroupNo;
    const unsigned mNumSym;
    const unsigned mSubStride;
    const unsigned mOffset;
};

}
#endif