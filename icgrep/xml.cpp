/*
 *  Copyright (c) 2019 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include <IR_Gen/idisa_target.h>
#include <boost/filesystem.hpp>
#include <kernels/kernel_builder.h>
#include <kernels/pipeline_builder.h>
#include <kernels/s2p_kernel.h>
#include <kernels/source_kernel.h>
#include <kernels/error_monitor_kernel.h>
#include <kernels/linebreak_kernel.h>
#include <kernels/p2s_kernel.h>
#include <kernels/scan_kernel.h>
#include <kernels/scanning.h>
#include <kernels/stdout_kernel.h>
#include <kernels/stream_select.h>
#include <kernels/streams_merge.h>
#include <kernels/streamset_collapse.h>
#include <kernels/core/streamset.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Path.h>
#include <pablo/pablo_toolchain.h>
#include <pablo/pablo_source_kernel.h>
#include <pablo/parser/pablo_parser.h>
#include <pablo/parser/simple_lexer.h>
#include <pablo/parser/rd_parser.h>
#include <toolchain/cpudriver.h>
#include <toolchain/toolchain.h>
#include <bitset>
#include <fcntl.h>
#include <iostream>
#include <iomanip>
#include <string>
#include <sys/stat.h>

namespace fs = boost::filesystem;
namespace so = kernel::streamops;

using namespace llvm;
using namespace kernel;
using namespace pablo;
using namespace pablo::parse;


static cl::OptionCategory xmlFlags("Command Flags", "xml options");

std::string inputFile;
static cl::opt<std::string, true> inputFileOption(cl::Positional, cl::location(inputFile), cl::desc("<input file>"), cl::Required, cl::cat(xmlFlags));


extern "C" void printErrorCode(uint64_t errCode) {
    std::cout << "Exit with error code: " << errCode << "\n";
}

extern "C" void xmlErrorCallback(const char * ptr, size_t pos) {
    // std::cout << "error: stream position = " << pos << ", at char: '" << *ptr << "'\n";
}

extern "C" void xmlTagCallback(const char * ptr, size_t pos, size_t idx) {
    // std::cout << "tag callback: stream index = " << idx << ", stream position = " << pos << ", at char: '" << *ptr << "'\n";
}

extern "C" void testLineCallback(const char * ptr, const char * begin, const char * end, uint64_t lineNo) {
    std::cout << "Callback:\n";
    ptrdiff_t pos = ptr - begin;
    if (pos < 0 || ptr > end) {
        std::cerr << "\u001b[31mERROR\u001b[0m: pointer is not within line span\n";
        std::cerr << "ptr: " << (void *) ptr << ", begin: " << (void *) begin << ", end: " << (void *) end << "\n";
        std::cerr << "line # " << lineNo << ", line: " << std::string(begin, end) << "\n";
        std::cerr << "ptr char: \"" << std::string(ptr - 4, ptr) << "\u001b[31m" << *ptr << "\u001b[0m" << std::string(ptr + 1, ptr + 5) << "\"\n\n";
        return;
    }
    std::string line(begin, end);
    line = line.substr(0, (size_t) pos) + "\u001b[32m" + line[pos] + "\u001b[0m" + line.substr((size_t) pos + 1);
    std::string cursor = std::string((size_t) pos, ' ') + "^";
    std::cout << std::setw(4) << std::right << lineNo << " | " << line << "\n";
    std::cout << "       " << "\u001b[32m" << cursor << "\u001b[0m" << "\n";
}


typedef void(*XMLProcessFunctionType)(uint32_t fd);

XMLProcessFunctionType xmlPipelineGen(CPUDriver & pxDriver, std::shared_ptr<PabloParser> parser, std::shared_ptr<SourceFile> xmlPabloSrc, std::shared_ptr<SourceFile> debugSource) {
    const size_t ERROR_STREAM_COUNT = 9;
    auto & iBuilder = pxDriver.getBuilder();
    Type * const i32Ty = iBuilder->getInt32Ty();
    auto P = pxDriver.makePipeline({Binding{i32Ty, "fd"}});
    Scalar * const fileDescriptor = P->getInputScalar("fd");

    StreamSet * const ByteStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<MMapSourceKernel>(fileDescriptor, ByteStream);

    StreamSet * const BasisBits = P->CreateStreamSet(8, 1);
    P->CreateKernelCall<S2PKernel>(ByteStream, BasisBits);

    StreamSet * const Lex = P->CreateStreamSet(27, 1);
    StreamSet * const U8 = P->CreateStreamSet(1, 1);
    StreamSet * const LexError = P->CreateStreamSet(ERROR_STREAM_COUNT, 1);
    P->CreateKernelCall<PabloSourceKernel>(
        parser,
        xmlPabloSrc,
        "ClassifyBytesValidateUtf8",
        Bindings { // Input Stream Bindings
            Binding {"basis_bits", BasisBits} 
        }, 
        Bindings { // Output Stream Bindings
            Binding {"lex", Lex}, 
            Binding {"u8", U8}, 
            Binding {"err", LexError} 
        }
    );

    StreamSet * const Marker = P->CreateStreamSet(3, 1);
    StreamSet * const CtCDPI_Callouts = P->CreateStreamSet(8, 1);
    StreamSet * const CT_CD_PI_CheckStreams = P->CreateStreamSet(6, 1);
    StreamSet * const CT_CD_PI_Error = P->CreateStreamSet(ERROR_STREAM_COUNT, 1);
    P->CreateKernelCall<PabloSourceKernel>(
        parser,
        xmlPabloSrc,
        "Parse_CtCDPI",
        Bindings { // Input Stream Bindings
            Binding {"lex", Lex}
        },
        Bindings { // Output Stream Bindings
            Binding {"marker", Marker},
            Binding {"ctCDPI_Callouts", CtCDPI_Callouts},
            Binding {"check_streams", CT_CD_PI_CheckStreams},
            Binding {"err", CT_CD_PI_Error}
        }
    );

    StreamSet * const TagError = P->CreateStreamSet(ERROR_STREAM_COUNT, 1);
    StreamSet * const TagCallouts = P->CreateStreamSet(9, 1);
    P->CreateKernelCall<PabloSourceKernel>(
        parser,
        xmlPabloSrc,
        "ParseTags",
        Bindings { // Input Stream Bindings
            Binding {"lex", Lex},
            Binding {"marker", Marker}
        },
        Bindings { // Output Stream Bindings
            Binding {"tag_Callouts", TagCallouts},
            Binding {"err", TagError}
        }
    );

    StreamSet * const RefError = P->CreateStreamSet(ERROR_STREAM_COUNT, 1);
    StreamSet * const RefCallouts = P->CreateStreamSet(6, 1);
    P->CreateKernelCall<PabloSourceKernel>(
        parser,
        xmlPabloSrc,
        "ParseRef",
        Bindings { // Input Stream Bindings
            Binding {"lex", Lex},
            Binding {"marker", Marker}
        },
        Bindings { // Output Stream Bindings
            Binding {"ref_Callouts", RefCallouts},
            Binding {"err", RefError}
        }
    );

    StreamSet * const Name_CheckStreams = P->CreateStreamSet(6, 1);
    StreamSet * const NameError = P->CreateStreamSet(ERROR_STREAM_COUNT, 1);
    P->CreateKernelCall<PabloSourceKernel>(
        parser,
        xmlPabloSrc,
        "ValidateXmlNames",
        Bindings { // Input Stream Bindings
            Binding {"ctCDPI_Callouts", CtCDPI_Callouts},
            Binding {"ref_Callouts", RefCallouts},
            Binding {"tag_Callouts", TagCallouts},
            Binding {"lex", Lex},
            Binding {"u8", U8}
        },
        Bindings { // Output Stream Bindings
            Binding {"check_streams", Name_CheckStreams},
            Binding {"err", NameError}
        }
    );

    StreamSet * const CS_CheckStreams = P->CreateStreamSet(6, 1);
    StreamSet * const CheckStreamsError = P->CreateStreamSet(ERROR_STREAM_COUNT, 1);
    P->CreateKernelCall<PabloSourceKernel>(
        parser,
        xmlPabloSrc,
        "DoCheckStreams",
        Bindings { // Input Stream Bindings
            Binding {"marker", Marker},
            Binding {"tag_Callouts", TagCallouts}
        },
        Bindings { // Output Stream Bindings
            Binding {"check_streams", CS_CheckStreams},
            Binding {"err", CheckStreamsError}
        }
    );

    StreamSet * const LineBreaks = P->CreateStreamSet();
    P->CreateKernelCall<UnixLinesKernelBuilder>(ByteStream, LineBreaks);

    StreamSet * const LineSpans = P->CreateStreamSet(2, 64);
    P->CreateKernelCall<LineSpanGenerator>(LineBreaks, ByteStream, LineSpans);

    StreamSet * const ScanPositions = P->CreateStreamSet(2, 64);
    P->CreateKernelCall<ScanPositionGenerator>(so::Select(P, TagCallouts, 2), LineBreaks, ByteStream, ScanPositions);

    Kernel * const reader = P->CreateKernelCall<LineBasedScanPositionReader>(ScanPositions, LineSpans, "testLineCallback");
    pxDriver.LinkFunction(reader, "testLineCallback", testLineCallback);

    StreamSet * const ErrorSet = P->CreateStreamSet(ERROR_STREAM_COUNT, 1);
    P->CreateKernelCall<StreamsMerge>(
        std::vector<StreamSet *>{LexError, CT_CD_PI_Error, TagError, RefError, NameError, CheckStreamsError}, 
        ErrorSet
    );

    StreamSet * const Errors = P->CreateStreamSet(1, 1);
    P->CreateKernelCall<CollapseStreamSet>(ErrorSet, Errors);

    Kernel * const scanKernel = P->CreateKernelCall<ScanKernel>(Errors, ByteStream, "xmlErrorCallback");
    pxDriver.LinkFunction(scanKernel, "xmlErrorCallback", xmlErrorCallback);

    Kernel * const mssk = P->CreateKernelCall<MultiStreamScanKernel>(TagCallouts, ByteStream, "xmlTagCallback");
    pxDriver.LinkFunction(mssk, "xmlTagCallback", xmlTagCallback);

    StreamSet * const CheckStreams = P->CreateStreamSet(6, 1);
    P->CreateKernelCall<StreamsMerge>(
        std::vector<StreamSet *>{CT_CD_PI_CheckStreams, Name_CheckStreams, CS_CheckStreams},
        CheckStreams
    );

    // StreamSet * const MaskedBasisBits = P->CreateStreamSet(8, 1);
    // P->CreateKernelCall<PabloSourceKernel>(
    //     parser,
    //     debugSource,
    //     "MaskBasisBits",
    //     Bindings {
    //         Binding {"basisBits", BasisBits},
    //         Binding {"mask", so::Select(P, TagCallouts, 0)}
    //     },
    //     Bindings {
    //         Binding {"masked", MaskedBasisBits}
    //     }
    // );

    // StreamSet * const PrintBytes = P->CreateStreamSet(1, 8);
    // P->CreateKernelCall<P2SKernel>(MaskedBasisBits, PrintBytes);
    // P->CreateKernelCall<StdOutKernel>(PrintBytes);

    Kernel * const emk = P->CreateKernelCall<ErrorMonitorKernel>(ErrorSet, ErrorMonitorKernel::IOStreamBindings{});
    Scalar * const errCode = emk->getOutputScalar("errorCode");
    P->CreateCall("printErrorCode", printErrorCode, {errCode});

    return reinterpret_cast<XMLProcessFunctionType>(P->compile());
}


int main(int argc, char ** argv) {
    codegen::ParseCommandLineOptions(argc, argv, {&xmlFlags, pablo_toolchain_flags(), codegen::codegen_flags()});

    struct stat sb;
    const int fd = open(inputFile.c_str(), O_RDONLY);
    if (LLVM_UNLIKELY(fd == -1)) {
        if (errno == EACCES) {
            std::cerr << "xml: " << inputFile << ": Permission denied.\n";
        }
        else if (errno == ENOENT) {
            std::cerr << "xml: " << inputFile << ": No such file.\n";
        }
        else {
            std::cerr << "xml: " << inputFile << ": Failed.\n";
        }
        return errno;
    }
    if (stat(inputFile.c_str(), &sb) == 0 && S_ISDIR(sb.st_mode)) {
        std::cerr << "xml: " << inputFile << ": Is a directory.\n";
        close(fd);
        return -1;
    }

    CPUDriver pxDriver("xml-pablo");
    auto em = ErrorManager::Create();
    auto parser = RecursiveParser::Create(SimpleLexer::Create(em), em);
    auto xmlSource = SourceFile::Relative("xml.pablo");
    auto debugSource = SourceFile::Relative("debug.pablo");
    if (xmlSource == nullptr) {
        std::cerr << "pablo-parser: error loading pablo source file: xml.pablo\n";
    }
    if (debugSource == nullptr) {
        std::cerr << "pablo-parser: error loading pablo source file: debug.pablo\n";
    }
    auto xmlProcessFuncPtr = xmlPipelineGen(pxDriver, parser, xmlSource, debugSource);

    xmlProcessFuncPtr(fd);
    close(fd);
}
