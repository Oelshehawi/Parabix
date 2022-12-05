/*
 *  Copyright (c) 2020 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */


#include <cstdio>
#include <vector>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/ErrorHandling.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/Module.h>
#include <re/adt/re_name.h>
#include <re/adt/re_re.h>
#include <kernel/core/kernel_builder.h>
#include <kernel/pipeline/pipeline_builder.h>
#include <kernel/streamutils/deletion.h>
#include <kernel/streamutils/pdep_kernel.h>
#include <kernel/streamutils/run_index.h>
#include <kernel/streamutils/stream_select.h>
#include <kernel/streamutils/stream_shift.h>
#include <kernel/streamutils/string_insert.h>
#include <kernel/basis/s2p_kernel.h>
#include <kernel/basis/p2s_kernel.h>
#include <kernel/io/source_kernel.h>
#include <kernel/io/stdout_kernel.h>
#include <kernel/util/debug_display.h>
#include <kernel/scan/scanmatchgen.h>
#include <re/adt/re_name.h>
#include <re/cc/cc_kernel.h>
#include <re/cc/cc_compiler.h>
#include <re/cc/cc_compiler_target.h>
#include <string>
#include <toolchain/toolchain.h>
#include <pablo/pablo_toolchain.h>
#include <fcntl.h>
#include <iostream>
#include <kernel/pipeline/driver/cpudriver.h>
#include "csv_util.hpp"
#ifdef ENABLE_PAPI
#include <util/papi_helper.hpp>
#endif

#define SHOW_STREAM(name) if (illustratorAddr) illustrator.captureBitstream(P, #name, name)
#define SHOW_BIXNUM(name) if (illustratorAddr) illustrator.captureBixNum(P, #name, name)

using namespace kernel;
using namespace llvm;
using namespace pablo;

//  These declarations are for command line processing.
//  See the LLVM CommandLine Library Manual https://llvm.org/docs/CommandLine.html
static cl::OptionCategory CSV_Options("CSV Processing Options", "CSV Processing Options.");
static cl::opt<std::string> inputFile(cl::Positional, cl::desc("<input file>"), cl::Required, cl::cat(CSV_Options));
static cl::opt<bool> HeaderSpecNamesFile("f", cl::desc("Interpret headers parameter as file name with header line"), cl::init(false), cl::cat(CSV_Options));
static cl::opt<std::string> HeaderSpec("headers", cl::desc("CSV column headers (explicit string or filename"), cl::init(""), cl::cat(CSV_Options));
static cl::opt<bool> UseFilterByMaskKernel("filter-by-mask-kernel", cl::desc("Use experimental FilterByMaskKernel"), cl::init(false), cl::cat(CSV_Options));
static cl::opt<bool> FilterOnly("filter-only", cl::desc("Perform initial CSV filtering only"), cl::init(false), cl::cat(CSV_Options));

typedef void (*CSVFunctionType)(uint32_t fd, ParabixIllustrator * illustrator);

CSVFunctionType generatePipeline(CPUDriver & pxDriver, std::vector<std::string> templateStrs, ParabixIllustrator & illustrator) {
    // A Parabix program is build as a set of kernel calls called a pipeline.
    // A pipeline is construction using a Parabix driver object.
    auto & b = pxDriver.getBuilder();
    auto P = pxDriver.makePipeline({Binding{b->getInt32Ty(), "inputFileDecriptor"},
                                    Binding{b->getIntAddrTy(), "illustratorAddr"}}, {});
    //  The program will use a file descriptor as an input.
    Scalar * fileDescriptor = P->getInputScalar("inputFileDecriptor");
    Scalar * illustratorAddr = nullptr;
    if (codegen::IllustratorDisplay > 0) {
        illustratorAddr = P->getInputScalar("illustratorAddr");
        illustrator.registerIllustrator(illustratorAddr);
    }
    // File data from mmap
    StreamSet * ByteStream = P->CreateStreamSet(1, 8);
    //  MMapSourceKernel is a Parabix Kernel that produces a stream of bytes
    //  from a file descriptor.
    P->CreateKernelCall<MMapSourceKernel>(fileDescriptor, ByteStream);

    //  The Parabix basis bits representation is created by the Parabix S2P kernel.
    //  S2P stands for serial-to-parallel.
    StreamSet * BasisBits = P->CreateStreamSet(8);
    Selected_S2P(P, ByteStream, BasisBits);
    SHOW_BIXNUM(BasisBits);
    //  We need to know which input positions are dquotes and which are not.
    StreamSet * csvCCs = P->CreateStreamSet(5);
    P->CreateKernelCall<CSVlexer>(BasisBits, csvCCs);
    StreamSet * recordSeparators = P->CreateStreamSet(1);
    StreamSet * fieldSeparators = P->CreateStreamSet(1);
    StreamSet * quoteEscape = P->CreateStreamSet(1);
    SHOW_STREAM(recordSeparators);
    SHOW_STREAM(fieldSeparators);
    SHOW_STREAM(quoteEscape);

    P->CreateKernelCall<CSVparser>(csvCCs, recordSeparators, fieldSeparators, quoteEscape);
    StreamSet * toKeep = P->CreateStreamSet(1);
    P->CreateKernelCall<CSVdataFieldMask>(csvCCs, recordSeparators, quoteEscape, toKeep, HeaderSpec == "");
    SHOW_STREAM(toKeep);
    //
    // Create a short stream which is 1-to-1 with the (field/record) separators,
    // having 0 bits for field separators and 1 bits for record separators.
    // Normally this will be a stream having exactly one bit set for every
    // N positions, where N is the number of entries per row.
    StreamSet * recordsByField = P->CreateStreamSet(1);
    FilterByMask(P, fieldSeparators, recordSeparators, recordsByField);
    SHOW_STREAM(recordsByField);

    StreamSet * translatedBasis = P->CreateStreamSet(8);
    P->CreateKernelCall<CSV_Char_Replacement>(recordSeparators, fieldSeparators, quoteEscape, BasisBits, translatedBasis);
    SHOW_BIXNUM(translatedBasis);
    StreamSet * filteredBasis = P->CreateStreamSet(8);
    StreamSet * filteredFieldSeparators = P->CreateStreamSet(1);
    FilterByMask(P, toKeep, translatedBasis, filteredBasis);
    SHOW_BIXNUM(filteredBasis);
    FilterByMask(P, toKeep, fieldSeparators, filteredFieldSeparators);
    SHOW_STREAM(filteredFieldSeparators);
    
    const unsigned fieldCount = templateStrs.size();
    const unsigned fieldCountBits = ceil_log2(fieldCount + 1);  // 1-based numbering
    StreamSet * compressedSepNum = P->CreateStreamSet(fieldCountBits);
    P->CreateKernelCall<RunIndex>(recordsByField, compressedSepNum, nullptr, RunIndex::Kind::RunOf0);
    SHOW_BIXNUM(compressedSepNum);

    StreamSet * compressedFieldNum = P->CreateStreamSet(fieldCountBits);
    P->CreateKernelCall<FieldNumberingKernel>(compressedSepNum, recordsByField, compressedFieldNum);
    SHOW_BIXNUM(compressedFieldNum);

    StreamSet * fieldNum = P->CreateStreamSet(fieldCountBits);
    SpreadByMask(P, filteredFieldSeparators, compressedFieldNum, fieldNum);
    SHOW_BIXNUM(fieldNum);

    std::vector<unsigned> insertionAmts;
    unsigned maxInsertAmt = 0;
    for (auto & s : templateStrs) {
        unsigned insertAmt = s.size();
        insertionAmts.push_back(insertAmt);
        if (insertAmt > maxInsertAmt) maxInsertAmt = insertAmt;
    }
    const unsigned insertLengthBits = ceil_log2(maxInsertAmt+1);

    StreamSet * InsertBixNum = P->CreateStreamSet(insertLengthBits);
    P->CreateKernelCall<ZeroInsertBixNum>(insertionAmts, fieldNum, InsertBixNum);
    SHOW_BIXNUM(InsertBixNum);

    // TODO: these aren't very tight bounds but works for now
    StreamSet * const SpreadMask = InsertionSpreadMask(P, InsertBixNum, InsertPosition::Before,
                                                       GammaDistribution(5.0f, 0.1f), NormalDistribution(0.7f, 0.05f));
    SHOW_STREAM(SpreadMask);

    // Baais bit streams expanded with 0 bits for each string to be inserted.
    StreamSet * ExpandedBasis = P->CreateStreamSet(8);
    SpreadByMask(P, SpreadMask, filteredBasis, ExpandedBasis, 0, GammaDistribution(5.0f, 0.1f));
    SHOW_BIXNUM(ExpandedBasis);

    // We need to insert strings at all positions marked by 0s in the
    // SpreadMask, plus the additional 0 at the delimiter position.
    //StreamSet * InsertMask = P->CreateStreamSet(1);
    //P->CreateKernelCall<Extend1Zeroes>(SpreadMask, InsertMask);

    // For each run of 0s marking insert positions, create a parallel
    // bixnum sequentially numbering the string insert positions.
    StreamSet * const InsertIndex = P->CreateStreamSet(insertLengthBits);
    P->CreateKernelCall<RunIndex>(SpreadMask, InsertIndex, nullptr, RunIndex::Kind::RunOf0);
    SHOW_BIXNUM(InsertIndex);

    StreamSet * expandedFieldNum = P->CreateStreamSet(fieldCountBits);
    SpreadByMask(P, SpreadMask, fieldNum, expandedFieldNum, 0, GammaDistribution(5.0f, 0.1f));
    SHOW_BIXNUM(expandedFieldNum);

    StreamSet * InstantiatedBasis = P->CreateStreamSet(8);
    P->CreateKernelCall<StringReplaceKernel>(templateStrs, ExpandedBasis, SpreadMask, expandedFieldNum, InsertIndex, InstantiatedBasis, /* offset = */ -1);
    SHOW_BIXNUM(InstantiatedBasis);
    // The computed output can be converted back to byte stream form by the
    // P2S kernel (parallel-to-serial).
    StreamSet * Instantiated = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<P2SKernel>(InstantiatedBasis, Instantiated);

    //  The StdOut kernel writes a byte stream to standard output.
    P->CreateKernelCall<StdOutKernel>(Instantiated);
    return reinterpret_cast<CSVFunctionType>(P->compile());
}

const unsigned MaxHeaderSize = 24;

int main(int argc, char *argv[]) {
    //  ParseCommandLineOptions uses the LLVM CommandLine processor, but we also add
    //  standard Parabix command line options such as -help, -ShowPablo and many others.
    codegen::ParseCommandLineOptions(argc, argv, {&CSV_Options, pablo::pablo_toolchain_flags(), codegen::codegen_flags()});

    ParabixIllustrator illustrator(codegen::IllustratorDisplay);
    std::vector<std::string> headers;
    if (HeaderSpec == "") {
        headers = get_CSV_headers(inputFile);
    } else if (HeaderSpecNamesFile) {
        headers = get_CSV_headers(HeaderSpec);
    } else {
        headers = parse_CSV_headers(HeaderSpec);
    }
    for (auto & s : headers) {
        if (s.size() > MaxHeaderSize) {
            s = s.substr(0, MaxHeaderSize);
        }
    }
    std::vector<std::string> templateStrs = createJSONtemplateStrings(headers);
    //for (auto & s : templateStrs) {
    //    llvm::errs() << "template string: |" << s << "|\n";
    //}
    std::string templatePrologue = "[\n{\"" + headers[0] + "\":\"";
    std::string templateEpilogue = "\"}\n]\n";
    //  A CPU driver is capable of compiling and running Parabix programs on the CPU.
    CPUDriver driver("csv_function");
    //  Build and compile the Parabix pipeline by calling the Pipeline function above.
    CSVFunctionType fn = generatePipeline(driver, templateStrs, illustrator);
    //  The compile function "fn"  can now be used.   It takes a file
    //  descriptor as an input, which is specified by the filename given by
    //  the inputFile command line option.]

    const int fd = open(inputFile.c_str(), O_RDONLY);
    if (LLVM_UNLIKELY(fd == -1)) {
        llvm::errs() << "Error: cannot open " << inputFile << " for processing. Skipped.\n";
    } else {
        #ifdef REPORT_PAPI_TESTS
        papi::PapiCounter<4> jitExecution{{PAPI_L3_TCM, PAPI_L3_TCA, PAPI_TOT_INS, PAPI_TOT_CYC}};
        // papi::PapiCounter<3> jitExecution{{PAPI_FUL_ICY, PAPI_STL_CCY, PAPI_RES_STL}};
        jitExecution.start();
        #endif
        //  Run the pipeline.
        printf("%s", templatePrologue.c_str());
        fflush(stdout);
        fn(fd, &illustrator);
        close(fd);
        printf("%s", templateEpilogue.c_str());
        #ifdef REPORT_PAPI_TESTS
        jitExecution.stop();
        jitExecution.write(std::cerr);
        #endif
        if (codegen::IllustratorDisplay > 0) {
            illustrator.displayAllCapturedData();
        }
    }
    return 0;
}
