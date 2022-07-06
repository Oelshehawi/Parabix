/*
 *  Copyright (c) 2019 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */
#ifndef ZTF_PHRASE_SCAN_H
#define ZTF_PHRASE_SCAN_H

#include <pablo/pablo_kernel.h>
#include <kernel/core/kernel_builder.h>
#include "ztf-logic.h"

namespace kernel {

class FinalizeCandidateMatches final : public MultiBlockKernel {
public:
    FinalizeCandidateMatches(BuilderRef b,
                           EncodingInfo encodingScheme,
                           StreamSet * const byteData,
                           StreamSet * candidateMatchesInDict,
                           StreamSet * nonCandidateMatchesInDict,
                           StreamSet * codeWordInCipherText,
                           StreamSet * allCandidateMatches,
                           unsigned strideBlocks = 8);
private:
    void generateMultiBlockLogic(BuilderRef iBuilder, llvm::Value * const numOfStrides) override;

    const EncodingInfo mEncodingScheme;
};


class MarkRepeatedHashvalue final : public MultiBlockKernel {
public:
    MarkRepeatedHashvalue(BuilderRef b,
                           EncodingInfo encodingScheme,
                           unsigned groupNo,
                           unsigned numSyms,
                           unsigned offset,
                           StreamSet * lfData,
                           StreamSet * symEndMarks,
                           StreamSet * cmpMarksSoFar,
                           StreamSet * const hashValues,
                           StreamSet * const byteData,
                           StreamSet * hashMarks,
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

class SymbolGroupCompression final : public MultiBlockKernel {
public:
    SymbolGroupCompression(BuilderRef b,
                           unsigned pLen,
                           EncodingInfo encodingScheme,
                           unsigned groupNo,
                           unsigned numSyms,
                           unsigned offset,
                           StreamSet * lfData,
                           StreamSet * symbolMarks,
                           StreamSet * hashValues,
                           StreamSet * const byteData,
                           StreamSet * compressionMask,
                           StreamSet * encodedBytes,
                           StreamSet * codewordMask,
                           unsigned strideBlocks = 8);
private:
    void generateMultiBlockLogic(BuilderRef iBuilder, llvm::Value * const numOfStrides) override;

    const EncodingInfo mEncodingScheme;
    const unsigned mGroupNo;
    const unsigned mNumSym;
    const unsigned mSubStride;
    const unsigned mOffset;
    const unsigned mStrideSize;
};

class FilterCompressedData final : public MultiBlockKernel {
public:
    FilterCompressedData(BuilderRef b,
                    EncodingInfo encodingScheme,
                    unsigned numSyms,
                    StreamSet * lfData,
                    StreamSet * byteData,
                    StreamSet * combinedMask,
                    StreamSet * cmpBytes,
                    StreamSet * partialSum,
                    unsigned strideBlocks = 8);
private:
    void generateMultiBlockLogic(BuilderRef iBuilder, llvm::Value * const numOfStrides) override;
    const unsigned mSubStride;
    const unsigned mStrideSize;
};

class WriteDictionary final : public MultiBlockKernel {
public:
    WriteDictionary(BuilderRef b,
    unsigned plen,
                    EncodingInfo encodingScheme,
                    unsigned numSyms,
                    unsigned offset,
                    StreamSet * lfData,
                    StreamSet * byteData,
                    StreamSet * codedBytes,
                    StreamSet * phraseMask,
                    StreamSet * allLenHashValues,
                    StreamSet * dictBytes,
                    StreamSet * dictPartialSum,
                    unsigned strideBlocks = 8);
private:
    void generateMultiBlockLogic(BuilderRef iBuilder, llvm::Value * const numOfStrides) override;
    const EncodingInfo mEncodingScheme;
    const unsigned mNumSym;
    const unsigned mSubStride;
    const unsigned mStrideSize;
};

class InterleaveCompressionSegment final : public MultiBlockKernel {
public:
    InterleaveCompressionSegment(BuilderRef b,
                           StreamSet * byteData,
                           StreamSet * codedBytes,
                           StreamSet * dictPartialSum,
                           StreamSet * compressedMask,
                           unsigned strideBlocks = 8);
private:
    void generateMultiBlockLogic(BuilderRef iBuilder, llvm::Value * const numOfStrides) override;
};

class OffsetCalcKernel final : public MultiBlockKernel {
public:
    OffsetCalcKernel(BuilderRef b,
                     StreamSet * LF,
                     StreamSet * LFpartialSum,
                     unsigned strideBlocks = 8);
private:
    void generateMultiBlockLogic(BuilderRef iBuilder, llvm::Value * const numOfStrides) override;
};

class SymbolGroupDecompression final : public MultiBlockKernel {
public:
    SymbolGroupDecompression(BuilderRef b,
                             EncodingInfo encodingScheme,
                             unsigned numSym,
                             unsigned groupNo,
                             StreamSet * const codeWordMarks,
                             StreamSet * const hashMarks,
                             StreamSet * const byteData,
                             StreamSet * const result,
                             unsigned strideBlocks = 8);
private:
    void generateMultiBlockLogic(BuilderRef iBuilder, llvm::Value * const numOfStrides) override;

    const EncodingInfo mEncodingScheme;
    const unsigned mGroupNo;
    const unsigned mNumSym;
};

class SegOffsetCalcKernel final : public MultiBlockKernel {
public:
    SegOffsetCalcKernel(BuilderRef b,
                     StreamSet * byteData,
                     StreamSet * segBoundary,
                     StreamSet * segmentPartialSum,
                     bool offsetFlag,
                     unsigned strideBlocks = 8);
private:
    void generateMultiBlockLogic(BuilderRef iBuilder, llvm::Value * const numOfStrides) override;

    const bool mOffsetFlag;
};

class SegmentFilter final : public MultiBlockKernel {
public:
    SegmentFilter(BuilderRef b,
                    StreamSet * const MatchesBySegment,
                    StreamSet * const offsetStartData,
                    StreamSet * const offsetEndData,
                    StreamSet * const byteData,
                    StreamSet * const filtereData);
private:
    void generateMultiBlockLogic(BuilderRef iBuilder, llvm::Value * const numOfStrides) override;
};

}
#endif
