/*
 *  Part of the Parabix Project, under the Open Software License 3.0.
 *  SPDX-License-Identifier: OSL-3.0
 */

#include <kernel/core/idisa_target.h>
#include <boost/filesystem.hpp>
#include <re/cc/cc_compiler.h>
#include <re/cc/cc_compiler_target.h>
#include <re/adt/adt.h>
#include <re/parse/parser.h>
#include <re/unicode/resolve_properties.h>
#include <re/cc/cc_kernel.h>
#include <kernel/core/kernel_builder.h>
#include <kernel/pipeline/pipeline_builder.h>
#include <kernel/basis/s2p_kernel.h>
#include <kernel/io/source_kernel.h>
#include <kernel/core/streamset.h>
#include <kernel/unicode/utf8_decoder.h>
#include <kernel/unicode/UCD_property_kernel.h>
#include <kernel/util/debug_display.h>
#include <kernel/streamutils/stream_select.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/raw_ostream.h>
#include <pablo/pablo_kernel.h>
#include <pablo/builder.hpp>
#include <pablo/pe_zeroes.h>
#include <pablo/pablo_toolchain.h>
#include <kernel/pipeline/driver/cpudriver.h>
#include <grep/grep_kernel.h>
#include <toolchain/toolchain.h>
#include <fileselect/file_select.h>
#include <fcntl.h>
#include <iomanip>
#include <iostream>
#include <string>
#include <sys/stat.h>
#include <vector>
#include <map>

namespace fs = boost::filesystem;

using namespace llvm;
using namespace codegen;
using namespace kernel;

static cl::OptionCategory ucFlags("Command Flags", "ucount options");

static cl::opt<std::string> CC_expr(cl::Positional, cl::desc("<Unicode character class expression>"), cl::Required, cl::cat(ucFlags));
static cl::list<std::string> inputFiles(cl::Positional, cl::desc("<input file ...>"), cl::OneOrMore, cl::cat(ucFlags));

static cl::opt<bool> U21("u21", cl::desc("Use Unicode 21 bits"), cl::cat(ucFlags));
static cl::opt<bool> ShowStreams("show-streams", cl::desc("Show UTF streams"), cl::init(false), cl::cat(ucFlags));


std::vector<fs::path> allFiles;

ParabixIllustrator illustrator(50);  // display width 50

typedef uint64_t (*UCountFunctionType)(uint32_t fd,  ParabixIllustrator * illustrator);

UCountFunctionType pipelineGen(CPUDriver & pxDriver, re::Name * CC_name) {

    auto & B = pxDriver.getBuilder();

    auto P = pxDriver.makePipeline(
                {Binding{B->getInt32Ty(), "fileDescriptor"},
                 Binding{B->getIntAddrTy(), "illustratorAddr"}},
                {Binding{B->getInt64Ty(), "countResult"}});

    Scalar * const fileDescriptor = P->getInputScalar("fileDescriptor");

    //  Create a stream set consisting of a single stream of 8-bit units (bytes).
    StreamSet * const ByteStream = P->CreateStreamSet(1, 8);

    //  Read the file into the ByteStream.
    P->CreateKernelCall<ReadSourceKernel>(fileDescriptor, ByteStream);

    //  Create a set of 8 parallel streams of 1-bit units (bits).
    StreamSet * BasisBits = P->CreateStreamSet(8, 1);

    //  Transpose the ByteSteam into parallel bit stream form.
    P->CreateKernelCall<S2PKernel>(ByteStream, BasisBits);

    if (U21) {
        StreamSet * const u21_Basis = P->CreateStreamSet(21, 1);
        P->CreateKernelCall<UTF8_Decoder>(BasisBits, u21_Basis, pablo::MovementMode);
        BasisBits = u21_Basis;
        if (ShowStreams) {
            Scalar * illustratorAddr = P->getInputScalar("illustratorAddr");
            illustrator.registerIllustrator(illustratorAddr);
            illustrator.captureByteData(P, "bytedata", ByteStream, '.');
            for (unsigned i = 0; i < 21; i++) {
                StreamSet * u21_basis_i = streamutils::Select(P, u21_Basis, i);
                illustrator.captureBitstream(P, "u21_" + std::to_string(i), u21_basis_i);
            }
        }

    }


    //  Create a character class bit stream.
    StreamSet * CCstream = P->CreateStreamSet(1, 1);
    
    std::map<std::string, StreamSet *> propertyStreamMap;
    auto nameString = CC_name->getFullName();
    propertyStreamMap.emplace(nameString, CCstream);
    P->CreateKernelFamilyCall<UnicodePropertyKernelBuilder>(CC_name, BasisBits, CCstream);

    P->CreateKernelCall<PopcountKernel>(CCstream, P->getOutputScalar("countResult"));

    return reinterpret_cast<UCountFunctionType>(P->compile());
}

uint64_t ucount1(UCountFunctionType fn_ptr, const uint32_t fileIdx) {
    std::string fileName = allFiles[fileIdx].string();
    struct stat sb;
    const int fd = open(fileName.c_str(), O_RDONLY);
    if (LLVM_UNLIKELY(fd == -1)) {
        if (errno == EACCES) {
            std::cerr << "ucount: " << fileName << ": Permission denied.\n";
        }
        else if (errno == ENOENT) {
            std::cerr << "ucount: " << fileName << ": No such file.\n";
        }
        else {
            std::cerr << "ucount: " << fileName << ": Failed.\n";
        }
        return 0;
    }
    if (stat(fileName.c_str(), &sb) == 0 && S_ISDIR(sb.st_mode)) {
        std::cerr << "ucount: " << fileName << ": Is a directory.\n";
        close(fd);
        return 0;
    }
    auto r = fn_ptr(fd, &illustrator);
    close(fd);
    return r;
}

int main(int argc, char *argv[]) {
    codegen::ParseCommandLineOptions(argc, argv, {&ucFlags, codegen::codegen_flags()});
    if (argv::RecursiveFlag || argv::DereferenceRecursiveFlag) {
        argv::DirectoriesFlag = argv::Recurse;
    }
    CPUDriver pxDriver("wc");

    allFiles = argv::getFullFileList(pxDriver, inputFiles);
    const auto fileCount = allFiles.size();

    UCountFunctionType uCountFunctionPtr = nullptr;
    re::RE * CC_re = re::RE_Parser::parse(CC_expr);
    CC_re = UCD::linkAndResolve(CC_re);
    CC_re = UCD::externalizeProperties(CC_re);
    if (re::Name * UCD_property_name = dyn_cast<re::Name>(CC_re)) {
        uCountFunctionPtr = pipelineGen(pxDriver, UCD_property_name);
    } else if (re::CC * CC_ast = dyn_cast<re::CC>(CC_re)) {
        uCountFunctionPtr = pipelineGen(pxDriver, makeName(CC_ast));
    } else {
        std::cerr << "Input expression must be a Unicode property or CC but found: " << CC_expr << " instead.\n";
        exit(1);
    }
    
    std::vector<uint64_t> theCounts;
    
    theCounts.resize(fileCount);
    uint64_t totalCount = 0;

    for (unsigned i = 0; i < fileCount; ++i) {
        theCounts[i] = ucount1(uCountFunctionPtr, i);
        totalCount += theCounts[i];
    }
    
    const int defaultDisplayColumnWidth = 7;
    int displayColumnWidth = std::to_string(totalCount).size() + 1;
    if (displayColumnWidth < defaultDisplayColumnWidth) displayColumnWidth = defaultDisplayColumnWidth;

    for (unsigned i = 0; i < fileCount; ++i) {
        std::cout << std::setw(displayColumnWidth);
        std::cout << theCounts[i] << std::setw(displayColumnWidth);
        std::cout << " " << allFiles[i].string() << std::endl;
    }
    if (inputFiles.size() > 1) {
        std::cout << std::setw(displayColumnWidth-1);
        std::cout << totalCount;
        std::cout << " total" << std::endl;
    }
    if (ShowStreams) {
        illustrator.displayAllCapturedData();
    }

    return 0;
}
