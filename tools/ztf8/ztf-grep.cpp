/*
 *  Copyright (c) 2014-8 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include <cstdio>
#include <vector>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/ErrorHandling.h>
#include <llvm/Support/PrettyStackTrace.h>
#include <llvm/Support/Signals.h>
#include <llvm/Support/ManagedStatic.h>
#include <llvm/Support/raw_ostream.h>
#include <re/adt/re_alt.h>
#include <re/adt/re_seq.h>
#include <re/adt/re_start.h>
#include <re/adt/re_end.h>
#include <re/adt/re_utility.h>
#include <re/parse/parser.h>
#include <re/toolchain/toolchain.h>
#include <grep/grep_engine.h>
#include <fstream>
#include <string>
#include <toolchain/toolchain.h>
#include <toolchain/pablo_toolchain.h>
#include <boost/filesystem.hpp>
#include <fileselect/file_select.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <llvm/ADT/STLExtras.h> // for make_unique
#include <kernel/pipeline/driver/cpudriver.h>
#ifdef ENABLE_PAPI
#include <util/papi_helper.hpp>
#endif

#include <kernel/ztf/ztf-logic.h>
#include <kernel/ztf/ztf-phrase-logic.h>
#include <kernel/ztf/ztf-phrase-scan.h>
#include "ztf-scan.h"
#include "../tools/icgrep/grep_interface.h"

using namespace llvm;

static cl::list<std::string> inputFiles(cl::Positional, cl::desc("<regex> <input file ...>"), cl::OneOrMore);

static cl::opt<bool> ByteMode("enable-byte-mode", cl::desc("Process regular expressions in byte mode"));

static cl::opt<int> REsPerGroup("re-num", cl::desc("Number of regular expressions processed by each kernel."), cl::init(0));

static re::ModeFlagSet globalFlags = re::MULTILINE_MODE_FLAG;

re::RE * readRE() {

    if (argv::FileFlag != "") {
        std::ifstream regexFile(argv::FileFlag.c_str());
        std::string r;
        if (regexFile.is_open()) {
            while (std::getline(regexFile, r)) {
                argv::RegexpVector.push_back(r);
            }
            regexFile.close();
        }
    }

    // if there are no regexes specified through -e or -f, the first positional argument
    // must be a regex, not an input file.

    if (argv::RegexpVector.size() == 0) {
        argv::RegexpVector.push_back(inputFiles[0]);
        inputFiles.erase(inputFiles.begin());
    }
    if (argv::IgnoreCaseFlag) {
        globalFlags |= re::CASE_INSENSITIVE_MODE_FLAG;
    }

    std::vector<re::RE *> REs;
    for (unsigned i = 0; i < argv::RegexpVector.size(); i++) {
        re::RE * re_ast = re::RE_Parser::parse(argv::RegexpVector[i], globalFlags, argv::RegexpSyntax, ByteMode);
        REs.push_back(re_ast);
    }
    re::RE * fullRE = makeAlt(REs.begin(), REs.end());

    if (argv::WordRegexpFlag) {
        fullRE = re::makeSeq({re::makeWordBoundary(), fullRE, re::makeWordBoundary()});
    }
    if (argv::LineRegexpFlag) {
        fullRE = re::makeSeq({re::makeStart(), fullRE, re::makeEnd()});
    }

    return fullRE;
}

namespace fs = boost::filesystem;

int main(int argc, char *argv[]) {
    llvm_shutdown_obj shutdown;
    argv::InitializeCommandLineInterface(argc, argv);
    CPUDriver driver("ztfGrep");

    auto RE = readRE();

    const auto allFiles = argv::getFullFileList(driver, inputFiles);
    if (inputFiles.empty()) {
        argv::UseStdIn = true;
    } else if ((allFiles.size() > 1) && !argv::NoFilenameFlag) {
        argv::WithFilenameFlag = true;
    }

    std::unique_ptr<grep::GrepEngine> grep;
    switch (argv::Mode) {
        case argv::NormalMode:
            grep = std::make_unique<grep::ZTFGrepEngine>(driver);
            if (argv::MaxCountFlag) grep->setMaxCount(argv::MaxCountFlag);
            if (argv::WithFilenameFlag) grep->showFileNames();
            if (argv::LineNumberFlag) grep->showLineNumbers();
            if (argv::InitialTabFlag) grep->setInitialTab();
            if (argv::FullyDecompressFlag) grep->setFullyDecompressOption(argv::FullyDecompressFlag);
           break;
        case argv::CountOnly:
            grep = std::make_unique<grep::CountOnlyEngine>(driver);
            if (argv::WithFilenameFlag) grep->showFileNames();
            if (argv::MaxCountFlag) grep->setMaxCount(argv::MaxCountFlag);
           break;
        case argv::FilesWithMatch:
        case argv::FilesWithoutMatch:
            grep = std::make_unique<grep::MatchOnlyEngine>(driver, argv::Mode == argv::FilesWithMatch, argv::NullFlag);
            break;
        case argv::QuietMode:
            grep = std::make_unique<grep::QuietModeEngine>(driver);
            break;
        default: llvm_unreachable("Invalid grep mode!");
    }
    if (argv::IgnoreCaseFlag) grep->setCaseInsensitive();
    if (argv::InvertMatchFlag) grep->setInvertMatches();
    if (argv::UnicodeLinesFlag) { // not needed?
        grep->setRecordBreak(grep::GrepRecordBreakKind::Unicode);
    } else if (argv::NullDataFlag) {
        grep->setRecordBreak(grep::GrepRecordBreakKind::Null);
    } else {
        grep->setRecordBreak(grep::GrepRecordBreakKind::LF);
    }
    grep->setContextLines(argv::BeforeContext, argv::AfterContext);

    grep->setStdinLabel(argv::LabelFlag);
    if (argv::UseStdIn) grep->setGrepStdIn();
    if (argv::NoMessagesFlag) grep->suppressFileMessages();
    if (argv::MmapFlag) grep->setPreferMMap();
    // grep->setBinaryFilesOption(argv::BinaryFilesFlag);
    if ((argv::ColorFlag == argv::alwaysColor) ||
        ((argv::ColorFlag == argv::autoColor) && isatty(STDOUT_FILENO))) {
        grep->setColoring();
    }    
    grep->initFileResult(allFiles); // unnecessary copy!
    grep->initRE(RE);
    grep->grepCodeGen();
    const bool matchFound = grep->searchAllFiles();
    return matchFound ? argv::MatchFoundExitCode : argv::MatchNotFoundExitCode;
}
