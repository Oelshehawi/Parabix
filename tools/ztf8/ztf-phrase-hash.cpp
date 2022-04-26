/*
 *  Copyright (c) 2019 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include <kernel/streamutils/deletion.h>                      // for DeletionKernel
#include <kernel/io/source_kernel.h>
#include <kernel/basis/p2s_kernel.h>
#include <kernel/basis/s2p_kernel.h>                    // for S2PKernel
#include <kernel/io/stdout_kernel.h>                 // for StdOutKernel_
#include <kernel/streamutils/pdep_kernel.h>
#include <llvm/IR/Function.h>                      // for Function, Function...
#include <llvm/IR/Module.h>                        // for Module
#include <llvm/Support/CommandLine.h>              // for ParseCommandLineOp...
#include <llvm/Support/Debug.h>                    // for dbgs
#include <pablo/pablo_kernel.h>                    // for PabloKernel
#include <toolchain/pablo_toolchain.h>
#include <pablo/parse/pablo_source_kernel.h>
#include <pablo/parse/pablo_parser.h>
#include <pablo/parse/simple_lexer.h>
#include <pablo/parse/rd_parser.h>
#include <re/adt/re_name.h>
#include <re/adt/re_re.h>
#include <grep/grep_kernel.h>
#include <re/cc/cc_compiler.h>
#include <re/cc/cc_compiler_target.h>
#include <re/ucd/ucd_compiler.hpp>
#include <re/unicode/resolve_properties.h>
#include <re/unicode/re_name_resolve.h>
#include <pablo/bixnum/bixnum.h>
#include <kernel/core/kernel_builder.h>
#include <pablo/pe_zeroes.h>
#include <toolchain/toolchain.h>
#include <kernel/pipeline/driver/cpudriver.h>
#include <kernel/core/streamset.h>
#include <kernel/streamutils/run_index.h>
#include <kernel/streamutils/stream_select.h>
#include <kernel/streamutils/streams_merge.h>
#include <kernel/streamutils/stream_shift.h>
#include <kernel/util/bixhash.h>
#include <kernel/util/debug_display.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/Support/raw_ostream.h>
#include <pablo/builder.hpp>
#include <pablo/pe_ones.h>
#include <fcntl.h>
#include <iostream>
#include <iomanip>
#include <kernel/pipeline/pipeline_builder.h>
#include "ztf-logic.h"
#include "ztf-scan.h"
#include "ztf-phrase-scan.h"
#include "ztf-phrase-logic.h"

using namespace pablo;
using namespace parse;
using namespace kernel;
using namespace llvm;
using namespace codegen;

static cl::OptionCategory ztfHashOptions("ztfHash Options", "ZTF-Hash options.");
static cl::opt<std::string> inputFile(cl::Positional, cl::desc("<input file>"), cl::Required, cl::cat(ztfHashOptions));
static cl::opt<std::string> dictFile(cl::Positional, cl::desc("<dictionary output file>"), cl::cat(ztfHashOptions));
static cl::opt<std::string> outputFile(cl::Positional, cl::desc("<compressed output file>"), cl::cat(ztfHashOptions));
static cl::opt<bool> Decompression("d", cl::desc("Decompress from ZTF-Runs to UTF-8."), cl::cat(ztfHashOptions), cl::init(false));
static cl::alias DecompressionAlias("decompress", cl::desc("Alias for -d"), cl::aliasopt(Decompression));
static cl::opt<bool> LengthBasedCompression("len-cmp", cl::desc("Phrase selection based on length of phrases"), cl::cat(ztfHashOptions), cl::init(true));
static cl::opt<bool> FreqBasedCompression("freq-cmp", cl::desc("Phrase selection based on frequency of phrases"), cl::cat(ztfHashOptions), cl::init(false));
static cl::opt<unsigned> SymCount("length", cl::desc("Length of words."), cl::init(2));
static cl::opt<unsigned> PhraseLen("plen", cl::desc("Debug - length of phrase."), cl::init(0), cl::cat(ztfHashOptions));
static cl::opt<unsigned> PhraseLenOffset("offset", cl::desc("Offset to actual length of phrase"), cl::init(1), cl::cat(ztfHashOptions));
static cl::opt<bool> UseParallelFilterByMask("fbm-p", cl::desc("Use default FilterByMask"), cl::cat(ztfHashOptions), cl::init(false));
static cl::opt<unsigned> Grouping("g", cl::desc("Experimental symbol grouping techniques"), cl::init(0), cl::cat(ztfHashOptions));
static cl::opt<unsigned> EncodingScheme("es", cl::desc("Select the encoding scheme to be used"), cl::init(1), cl::cat(ztfHashOptions));

typedef void (*ztfHashFunctionType)(uint32_t fd, const char *, const char *);
// typedef void (*ztfHashDecmpFunctionType)(uint32_t fd);
// typedef uint32_t (*ztfHashFunctionType)(uint32_t fd, const char *, const char *);
typedef uint32_t (*ztfHashDecmpFunctionType)(uint32_t fd);
#if 0
EncodingInfo encodingScheme1(8,
                             {{3, 3, 2, 0xC0, 8, 0}, //minLen, maxLen, hashBytes, pfxBase, hashBits, length_extension_bits
                              {4, 4, 2, 0xC8, 8, 0},
                              {5, 8, 2, 0xD0, 8, 0},
                              {9, 16, 3, 0xE0, 8, 0},
                              {17, 32, 4, 0xF0, 8, 0},
                             });
#endif
EncodingInfo encodingScheme1(8,
                             {{4, 4, 2, 0xC0, 8, 0},
                              {5, 8, 2, 0xC8, 8, 0},
                              {9, 16, 3, 0xE0, 8, 0},
                              {17, 32, 4, 0xF0, 8, 0},
                             });
ztfHashFunctionType ztfHash_compression_gen (CPUDriver & driver) {
    auto & b = driver.getBuilder();
    Type * const int32Ty = b->getInt32Ty();
    auto P = driver.makePipeline({Binding{int32Ty, "fd"},
                                 Binding{b->getInt8PtrTy(), "dictFileName"},
                                 Binding{b->getInt8PtrTy(), "outputFileName"}});

    Scalar * const fileDescriptor = P->getInputScalar("fd");

    // Source data
    StreamSet * const codeUnitStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<MMapSourceKernel>(fileDescriptor, codeUnitStream);

    StreamSet * u8basis = P->CreateStreamSet(8);
    P->CreateKernelCall<S2PKernel>(codeUnitStream, u8basis);

    StreamSet * WordChars = P->CreateStreamSet(1);
    StreamSet * symStart = P->CreateStreamSet(1);
    // Mark all the Unicode words in the input
    P->CreateKernelCall<WordMarkKernel>(u8basis, WordChars, symStart);
    // P->CreateKernelCall<DebugDisplayKernel>("WordChars", WordChars);

    StreamSet * symEnd = P->CreateStreamSet(1);
    P->CreateKernelCall<MarkSymEnds>(WordChars, symEnd);
    StreamSet * const phraseRuns = P->CreateStreamSet(1);
    // Mark ZTF symbols among the Unicode words
    P->CreateKernelCall<ZTF_Phrases>(u8basis, WordChars, symStart, symEnd, Grouping, phraseRuns);
    // P->CreateKernelCall<DebugDisplayKernel>("phraseRuns", phraseRuns);

    std::vector<StreamSet *> phraseLenBixnum(SymCount);
    std::vector<StreamSet *> phraseLenOverflow(SymCount);
    StreamSet * const runIndex = P->CreateStreamSet(5);
    StreamSet * const overflow = P->CreateStreamSet(1);
    // Calculate the length of individual symbols as a bixnum
    if (PhraseLenOffset == 2) {
        // P->CreateKernelCall<RunIndexOld>(phraseRuns, runIndex, overflow);
    }
    else {
        P->CreateKernelCall<RunIndex>(phraseRuns, runIndex, overflow, RunIndex::Kind::RunOf1, RunIndex::Numbering::RunPlus1);
    }
    //P->CreateKernelCall<DebugDisplayKernel>("runIndex", runIndex);

    StreamSet * const phraseRunIndex = P->CreateStreamSet(8); //7 bits are enough
    StreamSet * const phraseOverflow = P->CreateStreamSet(1);
    //write 4,3,2,1-symbol phrase lengths at (n-3),(n-2),(n-1) and n-th byte of the phrase
    P->CreateKernelCall<AccumRunIndexNew>(SymCount, phraseRuns, runIndex, overflow, phraseRunIndex, phraseOverflow);
    StreamSet * const phraseLenBytes = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<P2SKernel>(phraseRunIndex, phraseLenBytes);
    StreamSet * const allLenHashValues = P->CreateStreamSet(1, 16); // unused
    phraseLenBixnum[0] = runIndex;
    phraseLenOverflow[0] = overflow;

    // Calculate the length of k-symbol phrases as bixnum
    // Last byte of each symbol indicates the prev (k-1)-symbol + current_symbol_length
    for(unsigned i = 1; i < SymCount; i++) {
        StreamSet * const accumRunIndex = P->CreateStreamSet(5);
        StreamSet * const accumOverflow = P->CreateStreamSet(1);
        P->CreateKernelCall<AccumRunIndex>(i/*sum_offset*/, phraseRuns, runIndex/*phraseLenBixnum[i-1] -> has 8 bitstreams*/, phraseLenOverflow[i-1], accumRunIndex, accumOverflow);
        phraseLenBixnum[i]= accumRunIndex;
        phraseLenOverflow[i] = accumOverflow;
        //P->CreateKernelCall<DebugDisplayKernel>("accumRunIndex", accumRunIndex);
    }
    // P->CreateKernelCall<DebugDisplayKernel>("phraseLenBixnum[0]", phraseLenBixnum[0]);
    // P->CreateKernelCall<DebugDisplayKernel>("phraseLenBixnum[1]", phraseLenBixnum[1]);
    // Calculate k-hashCodes for each symbol. Each hashCode is unique to the number of symbols comprised.
    std::vector<StreamSet *> bixHashes(SymCount);
    std::vector<StreamSet *> allHashValues(SymCount);
    StreamSet * basisStart = u8basis;
    for(unsigned i = 0; i < SymCount; i++) {
        StreamSet * const bixHash = P->CreateStreamSet(encodingScheme1.MAX_HASH_BITS);
        P->CreateKernelCall<BixHash>(basisStart, phraseRuns, bixHash, i);
        bixHashes[i] = bixHash;
        //P->CreateKernelCall<DebugDisplayKernel>("bixHashes"+std::to_string(i), bixHashes[i]);
        basisStart = bixHash;
        // only 1-symbol hashes have cumulative runLength appened to every byte of hash value
        // for 2-symbol phrase onwards, total runLength is written at the last byte of the symbol
        std::vector<StreamSet *> combinedHashData = {bixHashes[i], phraseLenBixnum[i]};
        StreamSet * const hashValues = P->CreateStreamSet(1, 16);
        P->CreateKernelCall<P2S16Kernel>(combinedHashData, hashValues);
        allHashValues[i] = hashValues;
    }
    // unused
    std::vector<StreamSet *> combinedData = {bixHashes[0], phraseRunIndex};
    P->CreateKernelCall<P2S16Kernel>(combinedData, allLenHashValues);

    // Mark all the repeated hashCodes
    std::vector<StreamSet *> allHashMarks;
    StreamSet * const inputBytes = codeUnitStream;
    for (unsigned sym = 0; sym < SymCount; sym++) {
        unsigned startLgIdx = 0;
        unsigned endIdx = encodingScheme1.byLength.size();
        if (sym > 0) {
            startLgIdx = 3;
            if (encodingScheme1.byLength.size() == 4) {
                startLgIdx = 1;
            }
        }
        std::vector<StreamSet *> symHashMarks;
        StreamSet * hashValues = allHashValues[sym];
        for (unsigned i = startLgIdx; i < endIdx; i++) { // k-sym phrases length range 5-32
            StreamSet * const groupMarks = P->CreateStreamSet(1);
            P->CreateKernelCall<LengthGroupSelector>(encodingScheme1, i, phraseRuns, phraseLenBixnum[sym], phraseLenOverflow[sym]/*overflow*/, groupMarks, PhraseLenOffset);
            StreamSet * const hashMarks = P->CreateStreamSet(1);
            StreamSet * const hashValuesUpdated = P->CreateStreamSet(1, 16);
            P->CreateKernelCall<MarkRepeatedHashvalue>(encodingScheme1, sym, i, PhraseLenOffset, groupMarks, hashValues, inputBytes, hashMarks, hashValuesUpdated);
            symHashMarks.push_back(hashMarks);
            hashValues = hashValuesUpdated;
        }
        allHashValues[sym] = hashValues;
        StreamSet * const combinedSymHashMarks = P->CreateStreamSet(1);
        P->CreateKernelCall<StreamsMerge>(symHashMarks, combinedSymHashMarks);
        // if(sym ==1) {
        //     P->CreateKernelCall<DebugDisplayKernel>("combinedSymHashMarks", combinedSymHashMarks);
        // }
        allHashMarks.push_back(combinedSymHashMarks);
    }

    if (LengthBasedCompression) {
        for (unsigned sym = 1; sym < SymCount; sym++) {
            StreamSet * const lenSortedHashMarks = P->CreateStreamSet(28);
            P->CreateKernelCall<LengthSelector>(encodingScheme1, phraseLenBixnum[sym], allHashMarks[sym], lenSortedHashMarks, PhraseLenOffset);
            StreamSet * lenSortedHashMarksFiltered = P->CreateStreamSet(28);
            P->CreateKernelCall<LengthBasedHashMarkSelection>(encodingScheme1, 5/*offset*/, 5/*currLen*/, lenSortedHashMarks, lenSortedHashMarksFiltered);
            for (unsigned i = encodingScheme1.maxSymbolLength(); i >= 5; i--) {
                StreamSet * const selectedHashMarks = P->CreateStreamSet(1);
                StreamSet * const lenSortedHashMarksFilteredFinal = P->CreateStreamSet(28);
                P->CreateKernelCall<OverlappingLookaheadMarkSelect>(i, 5/*offset*/, lenSortedHashMarksFiltered, lenSortedHashMarksFilteredFinal, selectedHashMarks);
                lenSortedHashMarksFiltered = lenSortedHashMarksFilteredFinal;
                if (i == 5) {
                    // P->CreateKernelCall<DebugDisplayKernel>("selectedHashMarks", selectedHashMarks);
                    allHashMarks[sym] = selectedHashMarks;
                }
            }
        }
    }

    if (FreqBasedCompression) {
        // TODO
        // needs a phrase frequency stream for comparison and selection
    }

    StreamSet * u8bytes = codeUnitStream;
    std::vector<StreamSet *> extractionMasks;
    std::vector<StreamSet *> phraseMasks;
    std::vector<StreamSet *> dictBoundaryMasks;
    for (int sym = SymCount-1; sym >= 0; sym--) {
        unsigned startLgIdx = 0;
        unsigned endIdx = encodingScheme1.byLength.size();
        if (sym > 0) {
            startLgIdx = 3; //2; k-symbol compressible phrase min length = 9 bytes
            if (encodingScheme1.byLength.size() == 4) {
                startLgIdx = 1;
            }
        }
        for (unsigned i = startLgIdx; i < endIdx; i++) {
            StreamSet * const extractionMask = P->CreateStreamSet(1);
            StreamSet * const input_bytes = u8bytes;
            StreamSet * const output_bytes = P->CreateStreamSet(1, 8);
            StreamSet * const groupMarks = P->CreateStreamSet(1);
            StreamSet * const codewordMask = P->CreateStreamSet(1);
            StreamSet * const dictBoundaryMask = P->CreateStreamSet(1);  // unused
            P->CreateKernelCall<LengthGroupSelector>(encodingScheme1, i, allHashMarks[sym], phraseLenBixnum[sym], /*phraseLenOverflow[sym]*/ overflow, groupMarks, PhraseLenOffset);
            // mask of dictionary codeword positions
            P->CreateKernelCall<SymbolGroupCompression>(PhraseLen, encodingScheme1, sym, i, PhraseLenOffset, groupMarks, allHashValues[sym], input_bytes, extractionMask, output_bytes, codewordMask, dictBoundaryMask);
            extractionMasks.push_back(extractionMask);
            phraseMasks.push_back(codewordMask);
            dictBoundaryMasks.push_back(dictBoundaryMask);
            u8bytes = output_bytes;
            //Update sym-1 hashMarks to avoid compressing sub-phrases of any of the already compressed phrases
            for (int j = 0; j < sym; j++) {
                StreamSet * const updatedHashMark = P->CreateStreamSet(1);
                P->CreateKernelCall<UpdateNextHashMarks>(encodingScheme1, extractionMask, allHashMarks[j], i, updatedHashMark);
                allHashMarks[j] = updatedHashMark;
            }
        }
    }

    StreamSet * const combinedPhraseMask = P->CreateStreamSet(1);
    P->CreateKernelCall<StreamsMerge>(phraseMasks, combinedPhraseMask);

    StreamSet * const combinedMask = P->CreateStreamSet(1);
    P->CreateKernelCall<StreamsIntersect>(extractionMasks, combinedMask);
    // P->CreateKernelCall<PopcountKernel>(combinedMask, P->getOutputScalar("count1"));

    StreamSet * const dict_bytes = P->CreateStreamSet(1, 8);
    StreamSet * const dict_partialSum = P->CreateStreamSet(1, 64);
    P->CreateKernelCall<WriteDictionary>(PhraseLen, encodingScheme1, SymCount, PhraseLenOffset, codeUnitStream, u8bytes, combinedPhraseMask, phraseLenBytes, dict_bytes, dict_partialSum);
    // P->CreateKernelCall<DebugDisplayKernel>("dict_partialSum", dict_partialSum);

    // Scalar * dictFileName = P->getInputScalar("dictFileName");
    // P->CreateKernelCall<FileSink>(dictFileName, dict_bytes);

    StreamSet * const compressed_bytes = P->CreateStreamSet(1, 8);
    StreamSet * const partialSum = P->CreateStreamSet(1, 64);
    StreamSet * const phraseEndMarks = P->CreateStreamSet(1);
    P->CreateKernelCall<InverseStream>(phraseRuns, phraseEndMarks);
    P->CreateKernelCall<FilterCompressedData>(encodingScheme1, SymCount, u8bytes, combinedMask, phraseEndMarks, compressed_bytes, partialSum);
    // P->CreateKernelCall<DebugDisplayKernel>("partialSum", partialSum);
    // P->CreateKernelCall<StdOutKernel>(compressed_bytes);

    // Print compressed output
    // Scalar * outputFileName = P->getInputScalar("outputFileName");
    // P->CreateKernelCall<FileSink>(outputFileName, compressed_bytes);

    P->CreateKernelCall<InterleaveCompressionSegment>(dict_bytes, compressed_bytes, dict_partialSum, partialSum /*combinedMask*/ );
    return reinterpret_cast<ztfHashFunctionType>(P->compile());
}


ztfHashDecmpFunctionType ztfHash_decompression_gen (CPUDriver & driver) {
    auto & b = driver.getBuilder();
    Type * const int32Ty = b->getInt32Ty();
 // auto P = driver.makePipeline({Binding{int32Ty, "fd"}});
    auto P = driver.makePipeline({Binding{int32Ty, "fd"}}, {Binding{b->getSizeTy(), "count2"}});
    Scalar * const fileDescriptor = P->getInputScalar("fd");

    // Source data
    StreamSet * const source = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<MMapSourceKernel>(fileDescriptor, source);
    StreamSet * const ztfHashBasis = P->CreateStreamSet(8);
    P->CreateKernelCall<S2PKernel>(source, ztfHashBasis);
    StreamSet * const ztfInsertionLengths = P->CreateStreamSet(5);
    StreamSet * const countStream = P->CreateStreamSet(1);
    StreamSet * const ztfHash_Basis_updated = P->CreateStreamSet(8);
    P->CreateKernelCall<ZTF_PhraseExpansionDecoder>(encodingScheme1, ztfHashBasis, ztfInsertionLengths, countStream, ztfHash_Basis_updated);
    //P->CreateKernelCall<DebugDisplayKernel>("countStream", countStream);
    //P->CreateKernelCall<codeword_index>(ztfHashBasis, countStream);
    P->CreateKernelCall<PopcountKernel>(countStream, P->getOutputScalar("count2"));
    StreamSet * const ztfRunSpreadMask = InsertionSpreadMask(P, ztfInsertionLengths);
    StreamSet * const ztfHash_u8_Basis = P->CreateStreamSet(8);
    //P->CreateKernelCall<DebugDisplayKernel>("ztfRunSpreadMask", ztfRunSpreadMask);
    SpreadByMask(P, ztfRunSpreadMask, ztfHashBasis, ztfHash_u8_Basis);

    StreamSet * decodedMarks = P->CreateStreamSet(SymCount * encodingScheme1.byLength.size());
    StreamSet * hashtableMarks = P->CreateStreamSet(SymCount * encodingScheme1.byLength.size());
    StreamSet * hashtableSpan = P->CreateStreamSet(1);
    P->CreateKernelCall<ZTF_PhraseDecodeLengths>(encodingScheme1, SymCount, ztfHash_u8_Basis, decodedMarks, hashtableMarks, hashtableSpan);

    // P->CreateKernelCall<PopcountKernel>(hashtableSpan, P->getOutputScalar("count2"));
    //P->CreateKernelCall<DebugDisplayKernel>("hashtableSpan", hashtableSpan);

    StreamSet * const ztfHash_u8bytes = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<P2SKernel>(ztfHash_u8_Basis, ztfHash_u8bytes);
    //P->CreateKernelCall<StdOutKernel>(ztfHash_u8bytes);

    const auto n = encodingScheme1.byLength.size();

    StreamSet * u8bytes = ztfHash_u8bytes;
    for(unsigned sym = 0; sym < SymCount; sym++) {
        unsigned startIdx = 0;
        if (sym > 0) {
            startIdx = 3;
            if (encodingScheme1.byLength.size() == 4) startIdx = 1;
        }
        for (unsigned i = startIdx; i < n; i++) {
            StreamSet * const hashGroupMarks = P->CreateStreamSet(1);

            const unsigned idx = (sym * encodingScheme1.byLength.size()) + i;

            P->CreateKernelCall<StreamSelect>(hashGroupMarks, Select(hashtableMarks, {idx}));
            //P->CreateKernelCall<DebugDisplayKernel>("hashGroupMarks", hashGroupMarks);
            StreamSet * const groupDecoded = P->CreateStreamSet(1);
            P->CreateKernelCall<StreamSelect>(groupDecoded, Select(decodedMarks, {idx}));
            //P->CreateKernelCall<DebugDisplayKernel>("groupDecoded", groupDecoded);

            StreamSet * const input_bytes = u8bytes;
            StreamSet * const output_bytes = P->CreateStreamSet(1, 8);
            // hashGroupMarks -> hashtable codeword group marks
            // groupDecoded -> to decompress codeword marks
            P->CreateKernelCall<SymbolGroupDecompression>(encodingScheme1, sym, i, hashGroupMarks, groupDecoded, input_bytes, output_bytes);
            u8bytes = output_bytes;
        }
    }
    StreamSet * const decoded = P->CreateStreamSet(8);
    P->CreateKernelCall<S2PKernel>(u8bytes, decoded);

    StreamSet * const decoded_basis = P->CreateStreamSet(8);
    FilterByMask(P, hashtableSpan, decoded, decoded_basis);

    StreamSet * const decoded_bytes = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<P2SKernel>(decoded_basis, decoded_bytes);
    P->CreateKernelCall<StdOutKernel>(decoded_bytes);
    return reinterpret_cast<ztfHashDecmpFunctionType>(P->compile());
}

int main(int argc, char *argv[]) {
    codegen::ParseCommandLineOptions(argc, argv, {&ztfHashOptions, pablo_toolchain_flags(), codegen::codegen_flags()});

    CPUDriver pxDriver("ztfPhraseHash");
    const int fd = open(inputFile.c_str(), O_RDONLY);
    if (LLVM_UNLIKELY(fd == -1)) {
        errs() << "Error: cannot open " << inputFile << " for processing. Skipped.\n";
    } else {
        if (Decompression) {
            auto ztfHashDecompressionFunction = ztfHash_decompression_gen(pxDriver);
         // ztfHashDecompressionFunction(fd);
            uint64_t count2 = ztfHashDecompressionFunction(fd);
            errs() << count2 << " count2" << "\n";
        } else {
            auto ztfHashCompressionFunction = ztfHash_compression_gen(pxDriver);
            ztfHashCompressionFunction(fd, dictFile.c_str(), outputFile.c_str());
            // ztfHashCompressionFunction(fd, dictFile.c_str(), outputFile.c_str());
            // uint64_t count1 = ztfHashCompressionFunction(fd, dictFile.c_str(), outputFile.c_str());
            // errs() << count1 << " count1" << "\n";
        }
        close(fd);
    }
    return 0;
}
