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
#include <pablo/pablo_toolchain.h>
#include <pablo/parse/pablo_source_kernel.h>
#include <pablo/parse/pablo_parser.h>
#include <pablo/parse/simple_lexer.h>
#include <pablo/parse/rd_parser.h>
#include <re/adt/re_name.h>
#include <re/adt/re_re.h>
#include <grep/grep_kernel.h>
#include <re/cc/cc_compiler.h>
#include <re/cc/cc_compiler_target.h>
#include <re/unicode/resolve_properties.h>
#include <pablo/bixnum/bixnum.h>
#include <kernel/core/kernel_builder.h>
#include <pablo/pe_zeroes.h>
#include <toolchain/toolchain.h>
#include <kernel/pipeline/driver/cpudriver.h>
#include <kernel/core/streamset.h>
#include <kernel/scan/index_generator.h>
#include <kernel/scan/reader.h>
#include <kernel/streamutils/run_index.h>
#include <kernel/streamutils/stream_select.h>
#include <kernel/streamutils/streams_merge.h>
#include <kernel/util/bixhash.h>
#include <kernel/util/debug_display.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/Support/raw_ostream.h>
#include <pablo/bixnum/bixnum.h>
#include <pablo/pe_zeroes.h>
#include <pablo/builder.hpp>
#include <pablo/pe_ones.h>
#include <unicode/utf/utf_compiler.h>
#include <re/unicode/resolve_properties.h>
#include <re/cc/cc_compiler.h>
#include <re/cc/cc_compiler_target.h>
#include <fcntl.h>
#include <iostream>
#include <iomanip>
#include <kernel/pipeline/pipeline_builder.h>

#define SHOW_STREAM(name) if (illustratorAddr) illustrator.captureBitstream(P, #name, name)
#define SHOW_BIXNUM(name) if (illustratorAddr) illustrator.captureBixNum(P, #name, name)
#define SHOW_BYTES(name) if (illustratorAddr) illustrator.captureByteData(P, #name, name)

using namespace pablo;
using namespace parse;
using namespace kernel;
using namespace llvm;
using namespace codegen;

static cl::OptionCategory HashDemoOptions("Hash Demo Options", "Hash demo options.");
static cl::opt<std::string> inputFile(cl::Positional, cl::desc("<input file>"), cl::Required, cl::cat(HashDemoOptions));


class WordMarkKernel : public pablo::PabloKernel {
public:
    WordMarkKernel(BuilderRef kb, StreamSet * BasisBits, StreamSet * WordMarks);
protected:
    void generatePabloMethod() override;
};

WordMarkKernel::WordMarkKernel(BuilderRef kb, StreamSet * BasisBits, StreamSet * WordMarks)
: PabloKernel(kb, "WordMarks", {Binding{"source", BasisBits}}, {Binding{"WordMarks", WordMarks}}) { }

void WordMarkKernel::generatePabloMethod() {
    pablo::PabloBuilder pb(getEntryScope());
    re::RE * word_prop = re::makePropertyExpression("word");
    word_prop = UCD::linkAndResolve(word_prop);
    re::CC * word_CC = cast<re::CC>(cast<re::PropertyExpression>(word_prop)->getResolvedRE());
    Var * wordChar = pb.createVar("word");
    UTF::UTF_Compiler unicodeCompiler(getInputStreamVar("source"), pb);
    unicodeCompiler.addTarget(wordChar, word_CC);
    unicodeCompiler.compile();
    pb.createAssign(pb.createExtract(getOutputStreamVar("WordMarks"), pb.getInteger(0)), wordChar);
}

class ParseSymbols : public pablo::PabloKernel {
public:
    ParseSymbols(BuilderRef kb,
                StreamSet * basisBits, StreamSet * wordChar, StreamSet * symbolRuns)
    : pablo::PabloKernel(kb, "ParseSymbols",
                         {Binding{"basisBits", basisBits, FixedRate(1), LookAhead(1)},
                             Binding{"wordChar", wordChar, FixedRate(1), LookAhead(3)}},
                         {Binding{"symbolRuns", symbolRuns}}) { }
protected:
    void generatePabloMethod() override;
};

void ParseSymbols::generatePabloMethod() {
    pablo::PabloBuilder pb(getEntryScope());
    std::vector<PabloAST *> basis = getInputStreamSet("basisBits");
    cc::Parabix_CC_Compiler_Builder ccc(getEntryScope(), basis);
    pablo::PabloAST * wordChar = getInputStreamSet("wordChar")[0];
    // Find start bytes of word characters.
    PabloAST * ASCII = ccc.compileCC(re::makeCC(0x0, 0x7F));
    PabloAST * prefix2 = ccc.compileCC(re::makeCC(0xC2, 0xDF));
    PabloAST * prefix3 = ccc.compileCC(re::makeCC(0xE0, 0xEF));
    PabloAST * prefix4 = ccc.compileCC(re::makeCC(0xF0, 0xF4));
    PabloAST * wc1 = pb.createAnd(ASCII, wordChar);
    wc1 = pb.createOr(wc1, pb.createAnd(prefix2, pb.createLookahead(wordChar, 1)));
    wc1 = pb.createOr(wc1, pb.createAnd(prefix3, pb.createLookahead(wordChar, 2)));
    wc1 = pb.createOr(wc1, pb.createAnd(prefix4, pb.createLookahead(wordChar, 3)));
    //
    PabloAST * wordStart = pb.createAnd(pb.createNot(pb.createAdvance(wordChar, 1)), wc1, "wordStart");
    // runs are the bytes after a start symbol until the next symStart byte.
    pablo::PabloAST * runs = pb.createInFile(pb.createAnd(pb.createNot(wordStart), wc1));
    pb.createAssign(pb.createExtract(getOutputStreamVar("symbolRuns"), pb.getInteger(0)), runs);
}


class RunLengthSelector final: public pablo::PabloKernel {
public:
    RunLengthSelector(BuilderRef b,
                      unsigned lo,
                      unsigned hi,
                      StreamSet * symbolRun, StreamSet * const lengthBixNum,
                      StreamSet * overflow,
                      StreamSet * selected);
protected:
    void generatePabloMethod() override;
    unsigned mLo;
    unsigned mHi;
};

RunLengthSelector::RunLengthSelector(BuilderRef b,
                           unsigned lo,
                           unsigned hi,
                           StreamSet * symbolRun,
                           StreamSet * const lengthBixNum,
                           StreamSet * overflow,
                           StreamSet * selected)
: PabloKernel(b, "RunLengthSelector" + std::to_string(lengthBixNum->getNumElements()) + "x1:" + std::to_string(lo) + "-" + std::to_string(lo),
              {Binding{"symbolRun", symbolRun, FixedRate(), LookAhead(1)},
                  Binding{"lengthBixNum", lengthBixNum},
                  Binding{"overflow", overflow}},
              {Binding{"selected", selected}}), mLo(lo), mHi(hi) { }

void RunLengthSelector::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    BixNumCompiler bnc(pb);
    PabloAST * run = getInputStreamSet("symbolRun")[0];
    std::vector<PabloAST *> lengthBixNum = getInputStreamSet("lengthBixNum");
    PabloAST * overflow = getInputStreamSet("overflow")[0];
    PabloAST * runFinal = pb.createAnd(run, pb.createNot(pb.createLookahead(run, 1)));
    runFinal = pb.createAnd(runFinal, pb.createNot(overflow));
    Var * groupStreamVar = getOutputStreamVar("selected");
    // Run index codes count from 0 on the 2nd byte of a symbol.
    // So the length is 2 more than the bixnum.
    unsigned offset = 2;
    PabloAST * groupStream = pb.createAnd3(bnc.UGE(lengthBixNum, mLo - offset), bnc.ULE(lengthBixNum, mHi - offset), runFinal);
    pb.createAssign(pb.createExtract(groupStreamVar, pb.getInteger(0)), groupStream);
}

typedef void (*HashDemoFunctionType)(uint32_t fd, ParabixIllustrator * illustrator);


extern "C" void callback(const char * L6end_ptr, uint8_t hashval) {
    const char * L6_start_ptr = L6end_ptr - 5;
    std::cout << std::string(L6_start_ptr, 6) << " " << std::to_string(hashval) << "\n";
}

HashDemoFunctionType hashdemo_gen (CPUDriver & driver, ParabixIllustrator & illustrator) {

    auto & b = driver.getBuilder();
    auto P = driver.makePipeline({Binding{b->getInt32Ty(), "inputFileDecriptor"},
                                    Binding{b->getIntAddrTy(), "illustratorAddr"}}, {});

    Scalar * fileDescriptor = P->getInputScalar("inputFileDecriptor");
    Scalar * illustratorAddr = nullptr;
    if (codegen::IllustratorDisplay > 0) {
        illustratorAddr = P->getInputScalar("illustratorAddr");
        illustrator.registerIllustrator(illustratorAddr);
    }

    // Source data
    StreamSet * const codeUnitStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<MMapSourceKernel>(fileDescriptor, codeUnitStream);

    StreamSet * const u8basis = P->CreateStreamSet(8);
    P->CreateKernelCall<S2PKernel>(codeUnitStream, u8basis);

    StreamSet * WordChars = P->CreateStreamSet(1);
    P->CreateKernelCall<WordMarkKernel>(u8basis, WordChars);
    SHOW_STREAM(WordChars);
    
    StreamSet * const SymbolRuns = P->CreateStreamSet(1);
    P->CreateKernelCall<ParseSymbols>(u8basis, WordChars, SymbolRuns);
    SHOW_STREAM(SymbolRuns);
    
    StreamSet * const runIndex = P->CreateStreamSet(4);
    StreamSet * const overflow = P->CreateStreamSet(1);
    P->CreateKernelCall<RunIndex>(SymbolRuns, runIndex, overflow);
    SHOW_BIXNUM(runIndex);
    SHOW_STREAM(overflow);
    
    const unsigned hash_bits = 8;
    
    StreamSet * const BixHashes = P->CreateStreamSet(hash_bits);
    P->CreateKernelCall<BixHash>(u8basis, SymbolRuns, BixHashes, 3);
    SHOW_BIXNUM(BixHashes);


    StreamSet * Lgth6symEnds = P->CreateStreamSet(1);
    P->CreateKernelCall<RunLengthSelector>(6, 6, SymbolRuns, runIndex, overflow, Lgth6symEnds);
    SHOW_STREAM(Lgth6symEnds);
    
    StreamSet * const L6_Hashes = P->CreateStreamSet(hash_bits);
    FilterByMask(P, Lgth6symEnds, BixHashes, L6_Hashes);
    SHOW_BIXNUM(L6_Hashes);
    
    StreamSet * const hashValues = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<P2SKernel>(L6_Hashes, hashValues);

    StreamSet * const scanIndices = P->CreateStreamSet(1, 64);
    P->CreateKernelCall<ScanIndexGenerator>(Lgth6symEnds, scanIndices);
    
    scan::Reader(P, driver, SCAN_CALLBACK(callback), codeUnitStream, scanIndices, { hashValues });
    
    return reinterpret_cast<HashDemoFunctionType>(P->compile());
}

int main(int argc, char *argv[]) {
    codegen::ParseCommandLineOptions(argc, argv, {&HashDemoOptions, pablo_toolchain_flags(), codegen::codegen_flags()});

    ParabixIllustrator illustrator(codegen::IllustratorDisplay);
    CPUDriver pxDriver("hashdemo");
    const int fd = open(inputFile.c_str(), O_RDONLY);
    if (LLVM_UNLIKELY(fd == -1)) {
        errs() << "Error: cannot open " << inputFile << " for processing. Skipped.\n";
    } else {
        HashDemoFunctionType func = nullptr;
        func = hashdemo_gen(pxDriver, illustrator);
        func(fd, &illustrator);
        close(fd);
        if (codegen::IllustratorDisplay > 0) {
            illustrator.displayAllCapturedData();
        }
    }
    return 0;
}
