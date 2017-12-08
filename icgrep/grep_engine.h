/*
 *  Copyright (c) 2017 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */
#ifndef GREP_ENGINE_H
#define GREP_ENGINE_H
#include <grep_interface.h>
#include <kernels/streamset.h>
#include <toolchain/grep_pipeline.h>
#include <string>       // for string
#include <vector>
#include <sstream>
#include <mutex>
#include <atomic>

namespace re { class CC; }
namespace re { class RE; }
namespace llvm { namespace cl { class OptionCategory; } }
class Driver;


namespace grep {

class GrepEngine {
    enum class FileStatus {Pending, GrepComplete, PrintComplete};
public:

    GrepEngine();
    virtual ~GrepEngine();
    
    void initFileResult(std::vector<std::string> & filenames);
    virtual void grepCodeGen(std::vector<re::RE *> REs);
    bool searchAllFiles();
    void * DoGrepThreadMethod();

protected:
    std::pair<parabix::StreamSetBuffer *, parabix::StreamSetBuffer *> grepPipeline(std::vector<re::RE *> & REs, parabix::StreamSetBuffer * ByteStream);

    virtual uint64_t doGrep(const std::string & fileName, const uint32_t fileIdx);
    std::string linePrefix(std::string fileName);
    int32_t openFile(const std::string & fileName, std::stringstream * msgstrm);

    Driver * mGrepDriver;

    std::atomic<unsigned> mNextFileToGrep;
    std::atomic<unsigned> mNextFileToPrint;
    std::vector<std::string> inputFiles;
    std::vector<std::unique_ptr<std::stringstream>> mResultStrs;
    std::vector<FileStatus> mFileStatus;
    std::mutex mWriteMutex;
    std::mutex mCacheMutex;


    bool grepMatchFound;
    
    std::string mFileSuffix;
    bool mMoveMatchesToEOL;
    pthread_t mEngineThread;
};

class EmitMatchesEngine : public GrepEngine {
public:
    EmitMatchesEngine();
    void grepCodeGen(std::vector<re::RE *> REs) override;
private:
    uint64_t doGrep(const std::string & fileName, const uint32_t fileIdx) override;
};

class CountOnlyEngine : public GrepEngine {
public:
    CountOnlyEngine();
private:
    uint64_t doGrep(const std::string & fileName, const uint32_t fileIdx) override;
};

class MatchOnlyEngine : public GrepEngine {
public:
    MatchOnlyEngine(bool showFilesWithoutMatch);
private:
    uint64_t doGrep(const std::string & fileName, const uint32_t fileIdx) override;
    unsigned mRequiredCount;
};

class QuietModeEngine : public GrepEngine {
public:
    QuietModeEngine();
};

}

#endif
