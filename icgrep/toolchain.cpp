/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include <string>
#include <iostream>
#include <fstream>
#include <sstream>

#include <toolchain.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/ExecutionEngine/MCJIT.h>
#include "llvm/IR/LegacyPassManager.h"

#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/CodeGen/CommandFlags.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/Host.h>
#include <llvm/Support/raw_ostream.h>

#include <object_cache.h>

using namespace llvm;

namespace codegen {

static cl::OptionCategory CodeGenOptions("Code Generation Options", "These options control code generation.");


static cl::opt<bool> DumpGeneratedIR("dump-generated-IR", cl::init(false), cl::desc("Print LLVM IR generated by Pablo Compiler."), cl::cat(CodeGenOptions));
static cl::opt<std::string> IROutputFilename("dump-generated-IR-output", cl::init(""), cl::desc("output IR filename"), cl::cat(CodeGenOptions));
static cl::opt<bool> DumpASM("DumpASM", cl::init(false), cl::desc("Print Assembly Code."), cl::cat(CodeGenOptions));

char OptLevel;
static cl::opt<char, true> OptLevelOption("O", cl::desc("Optimization level. [-O0, -O1, -O2, or -O3] (default = '-O1')"), cl::location(OptLevel),
                              cl::cat(CodeGenOptions), cl::Prefix, cl::ZeroOrMore, cl::init('1'));


static cl::opt<bool> EnableObjectCache("enable-object-cache", cl::init(false), cl::desc("Enable object caching"), cl::cat(CodeGenOptions));

static cl::opt<std::string> ObjectCacheDir("object-cache-dir", cl::init(""), cl::desc("Path to the object cache diretory"), cl::cat(CodeGenOptions));


int BlockSize;
int SegmentSize;

static cl::opt<int, true> BlockSizeOption("BlockSize", cl::location(BlockSize), cl::init(0), cl::desc("specify a block size (defaults to widest SIMD register width in bits)."), cl::cat(CodeGenOptions));
static cl::opt<int, true> SegmentSizeOption("segment-size", cl::location(SegmentSize), cl::desc("Segment Size"), cl::value_desc("positive integer"), cl::init(1));

const cl::OptionCategory * codegen_flags() {return &CodeGenOptions;}

}


void setAllFeatures(EngineBuilder &builder) {
    llvm::StringMap<bool> HostCPUFeatures;
    if (llvm::sys::getHostCPUFeatures(HostCPUFeatures)) {
        std::vector<std::string> attrs;
        for (auto &flag : HostCPUFeatures) {
            auto enabled = flag.second ? "+" : "-";
            attrs.push_back(enabled + flag.first().str());
        }
        builder.setMAttrs(attrs);
    }
}

bool AVX2_available() {
    llvm::StringMap<bool> HostCPUFeatures;
    if (llvm::sys::getHostCPUFeatures(HostCPUFeatures)) {
        auto f = HostCPUFeatures.find("avx2");
        return ((f != HostCPUFeatures.end()) && f->second);
    }
    return false;
}


void WriteAssembly (llvm::TargetMachine *TM, Module * m) {
    llvm::legacy::PassManager PM;

    llvm::SmallString<128> Str;
    llvm::raw_svector_ostream dest(Str); 

    if (TM->addPassesToEmitFile( PM , dest , llvm::TargetMachine::CGFT_AssemblyFile ) ) {
      std::cout << "addPassesToEmitFile failed\n";
      exit(1);
    }
    PM.run(*m);
    std::cerr << std::string( Str.c_str() ) << "\n";
}

ExecutionEngine * JIT_to_ExecutionEngine (Module * m) {

    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();

    PassRegistry * Registry = PassRegistry::getPassRegistry();
    initializeCore(*Registry);
    initializeCodeGen(*Registry);
    initializeLowerIntrinsicsPass(*Registry);

    std::string errMessage;
    EngineBuilder builder{std::unique_ptr<Module>(m)};
    builder.setErrorStr(&errMessage);
    TargetOptions opts = InitTargetOptionsFromCodeGenFlags();
    builder.setTargetOptions(opts);
    CodeGenOpt::Level optLevel = CodeGenOpt::Level::None;
    switch (codegen::OptLevel) {
        case '0': optLevel = CodeGenOpt::None; break;
        case '1': optLevel = CodeGenOpt::Less; break;
        case '2': optLevel = CodeGenOpt::Default; break;
        case '3': optLevel = CodeGenOpt::Aggressive; break;
        default: errs() << codegen::OptLevel << " is an invalid optimization level.\n";
    }
    builder.setOptLevel(optLevel);

    setAllFeatures(builder);

    if (LLVM_UNLIKELY(codegen::DumpGeneratedIR)) {
        if (codegen::IROutputFilename.empty()) {
            m->dump();
        } else {
            std::error_code error;
            llvm::raw_fd_ostream out(codegen::IROutputFilename, error, sys::fs::OpenFlags::F_None);
            m->print(out, nullptr);
        }
    }

    if (codegen::DumpASM) {
      WriteAssembly(builder.selectTarget(), m);
    }
    ExecutionEngine * engine = builder.create();
    if (engine == nullptr) {
        throw std::runtime_error("Could not create ExecutionEngine: " + errMessage);
    }    
    return engine;
}

void ApplyObjectCache(ExecutionEngine * e) {
    ICGrepObjectCache * cache = nullptr;
    if (codegen::EnableObjectCache) {
        if (codegen::ObjectCacheDir.empty())
            // Default is $HOME/.cache/icgrep
            cache = new ICGrepObjectCache();
        else
            cache = new ICGrepObjectCache(codegen::ObjectCacheDir);
        e->setObjectCache(cache);
    }    
}


