/*
 *  Copyright (c) 2015 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include <string>
#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>

#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/ExecutionEngine/MCJIT.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/Debug.h>

#include <llvm/Support/CommandLine.h>
#include <llvm/CodeGen/CommandFlags.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/Host.h>
#include <llvm/Support/raw_ostream.h>

#include <utf_encoding.h>
#include <re/re_cc.h>
#include <cc/cc_compiler.h>
#include <pablo/function.h>
#include <IDISA/idisa_builder.h>
#include <IDISA/idisa_target.h>
#include <kernels/instance.h>
#include <kernels/kernel.h>
#include <kernels/s2p_kernel.h>

#include <pablo/pablo_compiler.h>
#include <pablo/pablo_toolchain.h>

// Dynamic processor detection
#define ISPC_LLVM_VERSION ISPC_LLVM_3_6
#include <util/ispc.cpp>

#include <utf_encoding.h>

// mmap system
#include <boost/filesystem.hpp>
#include <boost/iostreams/device/mapped_file.hpp>
using namespace boost::iostreams;
using namespace boost::filesystem;

#include <fcntl.h>

static cl::list<std::string> inputFiles(cl::Positional, cl::desc("<input file ...>"), cl::OneOrMore);

static cl::opt<bool> CountLines("l", cl::desc("Report the number of lines in each input file."), cl::init(false));
static cl::opt<bool> CountWords("w", cl::desc("Report the number of lines in each input file."), cl::init(false));
static cl::opt<bool> CountBytes("c", cl::desc("Report the number of bytes in each input file."), cl::init(false));
static cl::opt<bool> CountChars("m", cl::desc("Report the number of characters in each input file."), cl::init(false));


static cl::OptionCategory eIRDumpOptions("LLVM IR Dump Options", "These options control dumping of LLVM IR.");
static cl::opt<bool> DumpGeneratedIR("dump-generated-IR", cl::init(false), cl::desc("Print LLVM IR generated by Pablo Compiler."), cl::cat(eIRDumpOptions));

static cl::OptionCategory cMachineCodeOptimization("Machine Code Optimizations", "These options control back-end compilier optimization levels.");

static cl::opt<char> OptLevel("O", cl::desc("Optimization level. [-O0, -O1, -O2, or -O3] (default = '-O0')"),
                              cl::cat(cMachineCodeOptimization), cl::Prefix, cl::ZeroOrMore, cl::init('0'));

static cl::opt<unsigned> SegmentSize("segment-size", cl::desc("Segment Size"), cl::value_desc("positive integer"), cl::init(1));


static int defaultFieldWidth = 7;  // default field width

std::vector<uint64_t> lineCount;
std::vector<uint64_t> wordCount;
std::vector<uint64_t> charCount;
std::vector<uint64_t> byteCount;

uint64_t TotalLines = 0;
uint64_t TotalWords = 0;
uint64_t TotalChars = 0;
uint64_t TotalBytes = 0;

//
//
extern "C" {
    void report_counts(uint64_t lines, uint64_t words, uint64_t chars, uint64_t bytes, uint64_t fileIdx) {
        lineCount[fileIdx] = lines;
        wordCount[fileIdx] = words;
        charCount[fileIdx] = chars;
        byteCount[fileIdx] = bytes;
        TotalLines += lines;
        TotalWords += words;
        TotalChars += chars;
        TotalBytes += bytes;
    }
}



//
//  Functions taken from toolchain.cpp and modified for casefold 
//  JIT_t_ExecutionEngine : remove object cache
//  icgrep_Linking:   unneeded?
//  all others: definitely unneeded
//

ExecutionEngine * JIT_to_ExecutionEngine (Module * m) {

    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();

    PassRegistry * Registry = PassRegistry::getPassRegistry();
    initializeCore(*Registry);
    initializeCodeGen(*Registry);
    initializeLowerIntrinsicsPass(*Registry);

    std::string errMessage;
    EngineBuilder builder(std::move(std::unique_ptr<Module>(m)));
    builder.setErrorStr(&errMessage);
    builder.setMCPU(sys::getHostCPUName());
    CodeGenOpt::Level optLevel = CodeGenOpt::Level::None;
    switch (OptLevel) {
        case '0': optLevel = CodeGenOpt::None; break;
        case '1': optLevel = CodeGenOpt::Less; break;
        case '2': optLevel = CodeGenOpt::Default; break;
        case '3': optLevel = CodeGenOpt::Aggressive; break;
        default: errs() << OptLevel << " is an invalid optimization level.\n";
    }
    builder.setOptLevel(optLevel);

    if ((strncmp(lGetSystemISA(), "avx2", 4) == 0)) {
            std::vector<std::string> attrs;
            attrs.push_back("avx2");
            builder.setMAttrs(attrs);
    }

    // builder.selectTarget();

    //builder.setOptLevel(mMaxWhileDepth ? CodeGenOpt::Level::Less : CodeGenOpt::Level::None);
    ExecutionEngine * engine = builder.create();
    if (engine == nullptr) {
        throw std::runtime_error("Could not create ExecutionEngine: " + errMessage);
    }
    return engine;
}


pablo::PabloFunction * wc_gen(Encoding encoding) {
    //  input: 8 basis bit streams
    //  output: 3 count streams
    
    pablo::PabloFunction * function = pablo::PabloFunction::Create("wc", 8, 3);
    cc::CC_Compiler ccc(*function, encoding);
    
    pablo::PabloBuilder pBuilder(ccc.getBuilder().getPabloBlock(), ccc.getBuilder());
    const std::vector<pablo::Var *> u8_bits = ccc.getBasisBits();

    if (CountLines) {
        pablo::PabloAST * LF = ccc.compileCC(re::makeCC(0x0A));
        function->setResult(0, pBuilder.createAssign("lineCount", pBuilder.createCount(LF)));
    }
    else function->setResult(0, pBuilder.createAssign("lineCount", pBuilder.createZeroes()));
    // FIXME - we need to limit this to pablo.inFile() because null bytes past EOF are matched by wordChar
    if (CountWords) {
        pablo::PabloAST * WS = ccc.compileCC(re::makeCC(re::makeCC(0x09, 0x0D), re::makeCC(0x20)));
        
        pablo::PabloAST * wordChar = ccc.compileCC(re::makeCC(re::makeCC(re::makeCC(0x00, 0x08), re::makeCC(0xE, 0x1F)), re::makeCC(0x21, 0xFF)));
        // WS_follow_or_start = 1 past WS or at start of file
        pablo::PabloAST * WS_follow_or_start = pBuilder.createNot(pBuilder.createAdvance(pBuilder.createNot(WS), 1));
        //
        pablo::PabloAST * wordStart = pBuilder.createAnd(wordChar, WS_follow_or_start);
        function->setResult(1, pBuilder.createAssign("wordCount", pBuilder.createCount(wordStart)));
    }
    else function->setResult(1, pBuilder.createAssign("wordCount", pBuilder.createZeroes()));
    if (CountChars) {
        //
        // FIXME: This correctly counts characters assuming valid UTF-8 input.  But what if input is
        // not UTF-8, or is not valid?
        //
        pablo::PabloAST * u8Begin = ccc.compileCC(re::makeCC(re::makeCC(0, 0x7F), re::makeCC(0xC2, 0xF4)));
        function->setResult(2, pBuilder.createAssign("charCount", pBuilder.createCount(u8Begin)));
    }
    else function->setResult(2, pBuilder.createAssign("charCount", pBuilder.createZeroes()));
    return function;
}

using namespace kernel;


class PipelineBuilder {
public:
    PipelineBuilder(llvm::Module * m, IDISA::IDISA_Builder * b);
    
    ~PipelineBuilder();
    
    void CreateKernels(pablo::PabloFunction * function);
    llvm::Function * ExecuteKernels();
    
private:
    llvm::Module *                      mMod;
    IDISA::IDISA_Builder *              iBuilder;
    KernelBuilder *                     mS2PKernel;
    KernelBuilder *                     mWC_Kernel;
    llvm::Type *                        mBitBlockType;
    int                                 mBlockSize;
};


Function *  PipelineBuilder::ExecuteKernels() {
    Constant * report_counts_routine;
    Type * const int64ty = iBuilder->getInt64Ty();
    Type * const voidTy = Type::getVoidTy(mMod->getContext());
    report_counts_routine = mMod->getOrInsertFunction("report_counts", voidTy, int64ty, int64ty, int64ty, int64ty, int64ty, nullptr);
    Type * const inputType = PointerType::get(ArrayType::get(StructType::get(mMod->getContext(), std::vector<Type *>({ArrayType::get(mBitBlockType, 8)})), 1), 0);
    
    Function * const main = cast<Function>(mMod->getOrInsertFunction("Main", voidTy, inputType, int64ty, int64ty, nullptr));
    main->setCallingConv(CallingConv::C);
    Function::arg_iterator args = main->arg_begin();
    
    Value * const inputStream = &*(args++);
    inputStream->setName("input");
    Value * const bufferSize = &*(args++);
    bufferSize->setName("bufferSize");
    Value * const fileIdx = &*(args++);
    fileIdx->setName("fileIdx");
    
    iBuilder->SetInsertPoint(BasicBlock::Create(mMod->getContext(), "entry", main,0));
    
    BasicBlock * entryBlock = iBuilder->GetInsertBlock();

    BasicBlock * segmentCondBlock = nullptr;
    BasicBlock * segmentBodyBlock = nullptr;
    const unsigned segmentSize = SegmentSize;
    if (segmentSize > 1) {
        segmentCondBlock = BasicBlock::Create(mMod->getContext(), "segmentCond", main, 0);
        segmentBodyBlock = BasicBlock::Create(mMod->getContext(), "segmentBody", main, 0);
    }
    BasicBlock * fullCondBlock = BasicBlock::Create(mMod->getContext(), "fullCond", main, 0);
    BasicBlock * fullBodyBlock = BasicBlock::Create(mMod->getContext(), "fullBody", main, 0);
    BasicBlock * finalBlock = BasicBlock::Create(mMod->getContext(), "final", main, 0);
    BasicBlock * finalPartialBlock = BasicBlock::Create(mMod->getContext(), "partial", main, 0);
    BasicBlock * finalEmptyBlock = BasicBlock::Create(mMod->getContext(), "empty", main, 0);
    BasicBlock * endBlock = BasicBlock::Create(mMod->getContext(), "end", main, 0);

    Instance * s2pInstance = mS2PKernel->instantiate(inputStream);
    Instance * wcInstance = mWC_Kernel->instantiate(s2pInstance->getOutputStreamBuffer());

    Value * initialBufferSize = nullptr;
    BasicBlock * initialBlock = nullptr;
    
    if (segmentSize > 1) {
        iBuilder->CreateBr(segmentCondBlock);
        iBuilder->SetInsertPoint(segmentCondBlock);
        PHINode * remainingBytes = iBuilder->CreatePHI(int64ty, 2, "remainingBytes");
        remainingBytes->addIncoming(bufferSize, entryBlock);
        Constant * const step = ConstantInt::get(int64ty, mBlockSize * segmentSize);
        Value * segmentCondTest = iBuilder->CreateICmpULT(remainingBytes, step);
        iBuilder->CreateCondBr(segmentCondTest, fullCondBlock, segmentBodyBlock);
        iBuilder->SetInsertPoint(segmentBodyBlock);
        for (unsigned i = 0; i < segmentSize; ++i) {
            s2pInstance->CreateDoBlockCall();
        }
        for (unsigned i = 0; i < segmentSize; ++i) {
            wcInstance->CreateDoBlockCall();
        }
        remainingBytes->addIncoming(iBuilder->CreateSub(remainingBytes, step), segmentBodyBlock);
        iBuilder->CreateBr(segmentCondBlock);
        initialBufferSize = remainingBytes;
        initialBlock = segmentCondBlock;
    } else {
        initialBufferSize = bufferSize;
        initialBlock = entryBlock;
        iBuilder->CreateBr(fullCondBlock);
    }

    iBuilder->SetInsertPoint(fullCondBlock);
    PHINode * remainingBytes = iBuilder->CreatePHI(int64ty, 2, "remainingBytes");
    remainingBytes->addIncoming(initialBufferSize, initialBlock);

    Constant * const step = ConstantInt::get(int64ty, mBlockSize);
    Value * fullCondTest = iBuilder->CreateICmpULT(remainingBytes, step);
    iBuilder->CreateCondBr(fullCondTest, finalBlock, fullBodyBlock);
    
    iBuilder->SetInsertPoint(fullBodyBlock);

    s2pInstance->CreateDoBlockCall();
    wcInstance->CreateDoBlockCall();

    Value * diff = iBuilder->CreateSub(remainingBytes, step);

    remainingBytes->addIncoming(diff, fullBodyBlock);
    iBuilder->CreateBr(fullCondBlock);
    
    iBuilder->SetInsertPoint(finalBlock);
    Value * emptyBlockCond = iBuilder->CreateICmpEQ(remainingBytes, ConstantInt::get(int64ty, 0));
    iBuilder->CreateCondBr(emptyBlockCond, finalEmptyBlock, finalPartialBlock);
    
    
    iBuilder->SetInsertPoint(finalPartialBlock);
    s2pInstance->CreateDoBlockCall();
    iBuilder->CreateBr(endBlock);
    
    iBuilder->SetInsertPoint(finalEmptyBlock);
    s2pInstance->clearOutputStreamSet();
    iBuilder->CreateBr(endBlock);
    
    iBuilder->SetInsertPoint(endBlock);

    wcInstance->CreateDoBlockCall();
    
    Value * lineCount = iBuilder->CreateExtractElement(iBuilder->CreateBlockAlignedLoad(wcInstance->getOutputStream((int) 0)), iBuilder->getInt32(0));
    Value * wordCount = iBuilder->CreateExtractElement(iBuilder->CreateBlockAlignedLoad(wcInstance->getOutputStream(1)), iBuilder->getInt32(0));
    Value * charCount = iBuilder->CreateExtractElement(iBuilder->CreateBlockAlignedLoad(wcInstance->getOutputStream(2)), iBuilder->getInt32(0));
    
    iBuilder->CreateCall(report_counts_routine, std::vector<Value *>({lineCount, wordCount, charCount, bufferSize, fileIdx}));
    
    iBuilder->CreateRetVoid();
    
    return main;
}


typedef void (*wcFunctionType)(char * byte_data, size_t filesize, size_t fileIdx);

static ExecutionEngine * wcEngine = nullptr;

wcFunctionType wcCodeGen(void) {
                            
    Module * M = new Module("wc", getGlobalContext());
    
    IDISA::IDISA_Builder * idb = GetIDISA_Builder(M);

    PipelineBuilder pipelineBuilder(M, idb);

    Encoding encoding(Encoding::Type::UTF_8, 8);
    
    pablo::PabloFunction * function = wc_gen(encoding);
    

    pipelineBuilder.CreateKernels(function);

    llvm::Function * main_IR = pipelineBuilder.ExecuteKernels();
    
    if (DumpGeneratedIR) {
        M->dump();
    }
    
    //verifyModule(*M, &dbgs());
    //std::cerr << "ExecuteKernels(); done\n";
    wcEngine = JIT_to_ExecutionEngine(M);
    
    wcEngine->finalizeObject();
    //std::cerr << "finalizeObject(); done\n";

    delete idb;
    return reinterpret_cast<wcFunctionType>(wcEngine->getPointerToFunction(main_IR));
}

void wc(wcFunctionType fn_ptr, const int64_t fileIdx) {
    std::string fileName = inputFiles[fileIdx];
    size_t fileSize;
    char * fileBuffer;
    
    const path file(fileName);
    if (exists(file)) {
        if (is_directory(file)) {
            return;
        }
    } else {
        std::cerr << "Error: cannot open " << fileName << " for processing. Skipped.\n";
        return;
    }
    
    fileSize = file_size(file);
    mapped_file mappedFile;
    if (fileSize == 0) {
        fileBuffer = nullptr;
    }
    else {
        try {
            mappedFile.open(fileName, mapped_file::priv, fileSize, 0);
        } catch (std::ios_base::failure e) {
            std::cerr << "Error: Boost mmap of " << fileName << ": " << e.what() << std::endl;
            return;
        }
        fileBuffer = mappedFile.data();
    }
    //std::cerr << "mFileSize =" << mFileSize << "\n";
    //std::cerr << "fn_ptr =" << std::hex << reinterpret_cast<intptr_t>(fn_ptr) << "\n";

    fn_ptr(fileBuffer, fileSize, fileIdx);

    mappedFile.close();
    
}


using namespace pablo;
using namespace kernel;

PipelineBuilder::PipelineBuilder(Module * m, IDISA::IDISA_Builder * b)
: mMod(m)
, iBuilder(b)
, mBitBlockType(b->getBitBlockType())
, mBlockSize(b->getBitBlockWidth()){

}

PipelineBuilder::~PipelineBuilder(){
    delete mS2PKernel;
    delete mWC_Kernel;
}

void PipelineBuilder::CreateKernels(PabloFunction * function){
    mS2PKernel = new KernelBuilder(iBuilder, "s2p", SegmentSize);
    mWC_Kernel = new KernelBuilder(iBuilder, "wc", SegmentSize);

    generateS2PKernel(mMod, iBuilder, mS2PKernel);

    pablo_function_passes(function);

    PabloCompiler pablo_compiler(mMod, iBuilder);
    try {
        pablo_compiler.setKernel(mWC_Kernel);
        pablo_compiler.compile(function);
        delete function;
        releaseSlabAllocatorMemory();
    } catch (std::runtime_error e) {
        delete function;
        releaseSlabAllocatorMemory();
        std::cerr << "Runtime error: " << e.what() << std::endl;
        exit(1);
    }
    
}


int main(int argc, char *argv[]) {
    StringMap<cl::Option*> Map;
    cl::getRegisteredOptions(Map);
    Map["time-passes"]->setHiddenFlag(cl::Hidden);
    Map["disable-spill-fusing"]->setHiddenFlag(cl::Hidden);
    Map["enable-misched"]->setHiddenFlag(cl::Hidden);
    Map["enable-tbaa"]->setHiddenFlag(cl::Hidden);
    Map["exhaustive-register-search"]->setHiddenFlag(cl::Hidden);
    Map["join-liveintervals"]->setHiddenFlag(cl::Hidden);
    Map["limit-float-precision"]->setHiddenFlag(cl::Hidden);
    Map["mc-x86-disable-arith-relaxation"]->setHiddenFlag(cl::Hidden);
    Map["limit-float-precision"]->setHiddenFlag(cl::Hidden);
    Map["print-after-all"]->setHiddenFlag(cl::Hidden);
    Map["print-before-all"]->setHiddenFlag(cl::Hidden);
    Map["print-machineinstrs"]->setHiddenFlag(cl::Hidden);
    Map["regalloc"]->setHiddenFlag(cl::Hidden);
    Map["rng-seed"]->setHiddenFlag(cl::Hidden);
    Map["stackmap-version"]->setHiddenFlag(cl::Hidden);
    Map["x86-asm-syntax"]->setHiddenFlag(cl::Hidden);
    Map["verify-debug-info"]->setHiddenFlag(cl::Hidden);
    Map["verify-dom-info"]->setHiddenFlag(cl::Hidden);
    Map["verify-loop-info"]->setHiddenFlag(cl::Hidden);
    Map["verify-regalloc"]->setHiddenFlag(cl::Hidden);
    Map["verify-scev"]->setHiddenFlag(cl::Hidden);
    Map["x86-recip-refinement-steps"]->setHiddenFlag(cl::Hidden);
    Map["rewrite-map-file"]->setHiddenFlag(cl::Hidden);

    cl::ParseCommandLineOptions(argc, argv);
    if (!(CountLines || CountWords || CountChars || CountBytes)) {
        CountLines = true;
        CountWords = true;
        CountBytes = true;
    }
    
    wcFunctionType fn_ptr = wcCodeGen();

    int fileCount = inputFiles.size();
    lineCount.resize(fileCount);
    wordCount.resize(fileCount);
    charCount.resize(fileCount);
    byteCount.resize(fileCount);
    
    for (unsigned i = 0; i < inputFiles.size(); ++i) {
        wc(fn_ptr, i);
    }
    
    delete wcEngine;
    
    int maxCount = 0;
    if (CountLines) maxCount = TotalLines;
    if (CountWords) maxCount = TotalWords;
    if (CountChars) maxCount = TotalChars;
    if (CountBytes) maxCount = TotalBytes;
    
    int fieldWidth = std::to_string(maxCount).size() + 1;
    if (fieldWidth < defaultFieldWidth) fieldWidth = defaultFieldWidth;

    for (unsigned i = 0; i < inputFiles.size(); ++i) {
        if (CountLines) {
            std::cout << std::setw(fieldWidth) << lineCount[i];
        }
        if (CountWords) {
            std::cout << std::setw(fieldWidth) << wordCount[i];
        }
        if (CountChars) {
            std::cout << std::setw(fieldWidth) << charCount[i];
        }
        if (CountBytes) {
            std::cout << std::setw(fieldWidth) << byteCount[i];
        }
        std::cout << " " << inputFiles[i] << std::endl;
    }
    if (inputFiles.size() > 1) {
        if (CountLines) {
            std::cout << std::setw(fieldWidth) << TotalLines;
        }
        if (CountWords) {
            std::cout << std::setw(fieldWidth) << TotalWords;
        }
        if (CountChars) {
            std::cout << std::setw(fieldWidth) << TotalChars;
        }
        if (CountBytes) {
            std::cout << std::setw(fieldWidth) << TotalBytes;
        }
        std::cout << " total" << std::endl;
    }

    return 0;
}

                       
