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
static cl::opt<int> SymCount("length", cl::desc("Length of words."), cl::init(2));
static cl::opt<int> PhraseLen("plen", cl::desc("Debug - length of phrase."), cl::init(0), cl::cat(ztfHashOptions));
static cl::opt<int> PhraseLenOffset("offset", cl::desc("Offset to actual length of phrase"), cl::init(1), cl::cat(ztfHashOptions));

typedef void (*ztfHashFunctionType)(uint32_t fd);
typedef void (*ztfHashDecmpFunctionType)(uint32_t fd);

EncodingInfo encodingScheme1(8,
                             {{3, 3, 2, 0xC0, 8, 0}, //minLen, maxLen, hashBytes, pfxBase, hashBits, length_extension_bits
                              {4, 4, 2, 0xC8, 8, 0},
                              {5, 8, 2, 0xD0, 8, 0},
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
    // Mark all the Unicode words in the input
    P->CreateKernelCall<WordMarkKernel>(u8basis, WordChars);

    StreamSet * const phraseRuns = P->CreateStreamSet(1);
    // Mark ZTF symbols among the Unicode words
    P->CreateKernelCall<ZTF_Phrases>(u8basis, WordChars, phraseRuns);
    //P->CreateKernelCall<DebugDisplayKernel>("phraseRuns", phraseRuns);

    std::vector<StreamSet *> phraseLenBixnum(SymCount);
    std::vector<StreamSet *> phraseLenOverflow(SymCount);
    StreamSet * const runIndex = P->CreateStreamSet(5);
    StreamSet * const overflow = P->CreateStreamSet(1);
    // Calculate the length of individual symbols as a bixnum
    if (PhraseLenOffset == 2) {
        P->CreateKernelCall<RunIndexOld>(phraseRuns, runIndex, overflow);
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
        if (sym > 0) {
            startLgIdx = 3;
        }
        std::vector<StreamSet *> symHashMarks;
        StreamSet * hashMarksNonFinal = P->CreateStreamSet(1);
        for (unsigned i = startLgIdx; i < encodingScheme1.byLength.size(); i++) { // k-sym phrases length range 5-32
            StreamSet * const groupMarks = P->CreateStreamSet(1);
            P->CreateKernelCall<LengthGroupSelector>(encodingScheme1, i, phraseRuns, phraseLenBixnum[sym], phraseLenOverflow[sym]/*overflow*/, groupMarks, PhraseLenOffset);
            StreamSet * const hashMarks = P->CreateStreamSet(1);
            // StreamSet * const dictEndMask = P->CreateStreamSet(1);
            // StreamSet * const cmpPhraseMask = P->CreateStreamSet(1); // unused
            // P->CreateKernelCall<MarkRepeatedHashvalue>(encodingScheme1, sym, i, groupMarks, allHashValues[sym], hashMarks);
            P->CreateKernelCall<MarkRepeatedHashvalue>(encodingScheme1, sym, i, PhraseLenOffset, groupMarks, allHashValues[sym], inputBytes, hashMarks);//, dictEndMask), cmpPhraseMask);
            symHashMarks.push_back(hashMarks);
        }
        StreamSet * const combinedSymHashMarks = P->CreateStreamSet(1);
        P->CreateKernelCall<StreamsMerge>(symHashMarks, combinedSymHashMarks);
        allHashMarks.push_back(combinedSymHashMarks);
    }

    if (LengthBasedCompression) {
        for (unsigned sym = 1; sym < SymCount; sym++) {
            StreamSet * const selectedHashMarks = P->CreateStreamSet(24);
            //StreamSet * const countStream2 = P->CreateStreamSet(1);
            P->CreateKernelCall<LengthSelector>(encodingScheme1, phraseLenBixnum[sym], allHashMarks[sym], selectedHashMarks, PhraseLenOffset);
            //P->CreateKernelCall<PopcountKernel>(countStream2, P->getOutputScalar("count1"));
            //P->CreateKernelCall<DebugDisplayKernel>("selectedHashMarks"+std::to_string(sym), selectedHashMarks);

            StreamSet * hmSelectedSoFar = P->CreateStreamSet(1);
            for(unsigned i = encodingScheme1.maxSymbolLength(); i >= 9 /*encodingScheme1.minSymbolLength()*/; i--) {
                if (i == encodingScheme1.maxSymbolLength()) {
                    hmSelectedSoFar = allHashMarks[sym];
                }
                StreamSet * const selectedStep1 = P->CreateStreamSet(1);
                // 1. select max number of non-overlapping phrases of length i+3 (currLen)
                // 2. eliminate all the currLen phrases preceeded by longer length phrases

                //StreamSet * const countStream1 = P->CreateStreamSet(1);
                P->CreateKernelCall<OverlappingLengthGroupMarker>(i, selectedHashMarks, hmSelectedSoFar, selectedStep1);
                // 3. eliminate all the curLen phrases preceeding longer length phrases
                /*if (i == 32) {
                    hmSelectedSoFar = selectedStep1;
                }
                unsigned toUpdateHashMarksCount = encodingScheme1.maxSymbolLength() - i + 1;
                StreamSet * accumHashMarks = P->CreateStreamSet(toUpdateHashMarksCount);
                P->CreateKernelCall<BixnumHashMarks>(encodingScheme1, selectedHashMarks, hmSelectedSoFar, i, accumHashMarks);
                P->CreateKernelCall<DebugDisplayKernel>("accumHashMarks", accumHashMarks);*/
                // without accumHashMarks, more than expected hashMarks from selectedStep1 may be eliminated
                StreamSet * const selectedStep2 = P->CreateStreamSet(1);
                // no need to invoke OverlappingLookaheadMarker for maxSymbolLength
                P->CreateKernelCall<OverlappingLookaheadMarker>(i, selectedHashMarks, hmSelectedSoFar, selectedStep1, selectedStep2);
                hmSelectedSoFar = selectedStep2;
            }
            //P->CreateKernelCall<DebugDisplayKernel>("hmSelectedSoFar", hmSelectedSoFar);
            allHashMarks[sym] = hmSelectedSoFar;
        }
    }

    if (FreqBasedCompression) {
        // TODO
        // allHashValues will have the frequency of the phrase written at the last byte
    }

    StreamSet * u8bytes = codeUnitStream;
    std::vector<StreamSet *> extractionMasks;
    std::vector<StreamSet *> phraseMasks;
    std::vector<StreamSet *> dictBoundaryMasks;
    for (int sym = SymCount-1; sym >= 0; sym--) {
        unsigned startLgIdx = 0;
        if (sym > 0) {
            startLgIdx = 3; //2; k-symbol compressible phrase min length = 9 bytes
        }
        for (unsigned i = startLgIdx; i < encodingScheme1.byLength.size(); i++) {
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
            for (unsigned j = 0; j < sym; j++) {
                StreamSet * const updatedHashMark = P->CreateStreamSet(1);
                P->CreateKernelCall<UpdateNextHashMarks>(extractionMask, allHashMarks[j], i, updatedHashMark);
                allHashMarks[j] = updatedHashMark;
            }
        }
    }

    StreamSet * const combinedPhraseMask = P->CreateStreamSet(1);
    P->CreateKernelCall<StreamsMerge>(phraseMasks, combinedPhraseMask);

    // StreamSet * const combinedDictBoundaryMask = P->CreateStreamSet(1);
    // P->CreateKernelCall<StreamsMerge>(dictBoundaryMasks, combinedDictBoundaryMask);

    StreamSet * const combinedMask = P->CreateStreamSet(1);
    P->CreateKernelCall<StreamsIntersect>(extractionMasks, combinedMask);

    StreamSet * const dict_bytes = P->CreateStreamSet(1, 8);
    StreamSet * const dict_mask = P->CreateStreamSet(1);
    P->CreateKernelCall<WriteDictionary>(PhraseLen, encodingScheme1, SymCount, PhraseLenOffset, codeUnitStream, u8bytes, combinedPhraseMask, phraseLenBytes, dict_bytes, dict_mask);
    // P->CreateKernelCall<PopcountKernel>(dict_mask, P->getOutputScalar("count1"));
    // P->CreateKernelCall<DebugDisplayKernel>("u8bytes", u8bytes);
    // P->CreateKernelCall<DebugDisplayKernel>("dict_bytes", dict_bytes);
    // P->CreateKernelCall<DebugDisplayKernel>("dict_mask", dict_mask);

    StreamSet * const nonfinal_output_bytes = P->CreateStreamSet(1, 8);
    StreamSet * const nonfinal_filter_mask = P->CreateStreamSet(1);
    P->CreateKernelCall<InterleaveCompressionSegment>(codeUnitStream, u8bytes, combinedMask, combinedPhraseMask, nonfinal_output_bytes, nonfinal_filter_mask);
    // P->CreateKernelCall<PopcountKernel>(nonfinal_filter_mask, P->getOutputScalar("count1"));
    // P->CreateKernelCall<StdOutKernel>(nonfinal_output_bytes);

    StreamSet * const dictStream = P->CreateStreamSet(8);
    P->CreateKernelCall<S2PKernel>(dict_bytes, dictStream);

    StreamSet * const dict_basis = P->CreateStreamSet(8);
    FilterByMask(P, dict_mask, dictStream, dict_basis);

    StreamSet * const dictBytes = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<P2SKernel>(dict_basis, dictBytes);

    Scalar * dictFileName = P->getInputScalar("dictFileName");
    P->CreateKernelCall<FileSink>(dictFileName, dictBytes);

    StreamSet * const encoded = P->CreateStreamSet(8);
    P->CreateKernelCall<S2PKernel>(u8bytes, encoded);

    StreamSet * const ZTF_basis = P->CreateStreamSet(8);
    FilterByMask(P, combinedMask, encoded, ZTF_basis);

    StreamSet * const ZTF_bytes = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<P2SKernel>(ZTF_basis, ZTF_bytes);

    Scalar * outputFileName = P->getInputScalar("outputFileName");
    P->CreateKernelCall<FileSink>(outputFileName, ZTF_bytes);
    // P->CreateKernelCall<StdOutKernel>(ZTF_bytes);
    return reinterpret_cast<ztfHashFunctionType>(P->compile());
}


ztfHashDecmpFunctionType ztfHash_decompression_gen (CPUDriver & driver) {
    auto & b = driver.getBuilder();
    Type * const int32Ty = b->getInt32Ty();
    auto P = driver.makePipeline({Binding{int32Ty, "fd"}});
    Scalar * const fileDescriptor = P->getInputScalar("fd");

    // Source data
    StreamSet * const source = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<MMapSourceKernel>(fileDescriptor, source);
    StreamSet * const ztfHashBasis = P->CreateStreamSet(8);
    P->CreateKernelCall<S2PKernel>(source, ztfHashBasis);
    StreamSet * const ztfInsertionLengths = P->CreateStreamSet(5);
    StreamSet * const countStream = P->CreateStreamSet(1);
    P->CreateKernelCall<ZTF_PhraseExpansionDecoder>(encodingScheme1, ztfHashBasis, ztfInsertionLengths, countStream);
    //P->CreateKernelCall<DebugDisplayKernel>("countStream", countStream);
    //P->CreateKernelCall<codeword_index>(ztfHashBasis, countStream);
    //P->CreateKernelCall<PopcountKernel>(countStream, P->getOutputScalar("count1"));
    StreamSet * const ztfRunSpreadMask = InsertionSpreadMask(P, ztfInsertionLengths);
    StreamSet * const ztfHash_u8_Basis = P->CreateStreamSet(8);
    //P->CreateKernelCall<DebugDisplayKernel>("ztfRunSpreadMask", ztfRunSpreadMask);
    SpreadByMask(P, ztfRunSpreadMask, ztfHashBasis, ztfHash_u8_Basis);

    StreamSet * decodedMarks = P->CreateStreamSet(SymCount * encodingScheme1.byLength.size());
    StreamSet * hashtableMarks = P->CreateStreamSet(SymCount * encodingScheme1.byLength.size());
    StreamSet * hashtableSpan = P->CreateStreamSet(1);
    P->CreateKernelCall<ZTF_PhraseDecodeLengths>(encodingScheme1, SymCount, ztfHash_u8_Basis, decodedMarks, hashtableMarks, hashtableSpan);

    //P->CreateKernelCall<PopcountKernel>(hashtableSpan, P->getOutputScalar("count1"));
    //P->CreateKernelCall<DebugDisplayKernel>("hashtableSpan", hashtableSpan);

    StreamSet * const ztfHash_u8bytes = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<P2SKernel>(ztfHash_u8_Basis, ztfHash_u8bytes);
    //P->CreateKernelCall<StdOutKernel>(ztfHash_u8bytes);

    /// TODO: use length group decompression which builds the hashtable using the compressed data
    // and replaces the codewords with phrases.
    StreamSet * u8bytes = ztfHash_u8bytes;
    for(unsigned sym = 0; sym < SymCount; sym++) {
        unsigned startIdx = 0;
        if (sym > 0) {
            startIdx = 3;
        }
        for (unsigned i = startIdx; i < encodingScheme1.byLength.size(); i++) {
            StreamSet * const hashGroupMarks = P->CreateStreamSet(1);
            P->CreateKernelCall<StreamSelect>(hashGroupMarks, Select(hashtableMarks, {(sym * encodingScheme1.byLength.size()) + i}));
            //P->CreateKernelCall<DebugDisplayKernel>("hashGroupMarks", hashGroupMarks);
            StreamSet * const groupDecoded = P->CreateStreamSet(1);
            P->CreateKernelCall<StreamSelect>(groupDecoded, Select(decodedMarks, {(sym * encodingScheme1.byLength.size()) + i}));
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
            /*uint64_t count1 = */ztfHashDecompressionFunction(fd);
            //errs() << count1 << " count2" << "\n";
        } else {
            auto ztfHashCompressionFunction = ztfHash_compression_gen(pxDriver);
            ztfHashCompressionFunction(fd);
        }
        close(fd);
    }
    return 0;
}
