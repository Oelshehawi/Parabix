#include <kernel/io/source_kernel.h>
#include <kernel/io/stdout_kernel.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include <kernel/core/kernel_builder.h>
#include <toolchain/toolchain.h>
#include <kernel/pipeline/driver/cpudriver.h>
#include <kernel/core/streamset.h>
#include <kernel/pipeline/pipeline_builder.h>
#include <fcntl.h>
#include <kernel/basis/s2p_kernel.h>
#include <immintrin.h>  // AVX-512 intrinsics
#include <iostream>     // Standard input/output streams
#include <fstream>      // File input/output streams
#include <vector>       // std::vector
#include <cstring>      // C-style string operations
#include <llvm/IR/Type.h>
#include <llvm/IR/DerivedTypes.h>
#include <signal.h>

#define SHOW_STREAM(name) if (codegen::EnableIllustrator) P->captureBitstream(#name, name)
#define SHOW_BIXNUM(name) if (codegen::EnableIllustrator) P->captureBixNum(#name, name)
#define SHOW_BYTES(name) if (codegen::EnableIllustrator) P->captureByteData(#name, name)

using namespace kernel;
using namespace llvm;
using namespace codegen;

/*SpreadByMask - spread out the bits of input streams according to a mask.
    Outputs are 1-to-1 with mask positions.   For a mask bit of 0, the corresponding
    output bits are always 0.   Otherwise, the nth 1 bit in the mask selects
    an input bit from position n in the input stream.

    Input stream:    abcdef
    Mask stream:     ...1.1...111..1..     . represents 0
    Output stream:   ...a.b...cde..f..     . represents 0
*/

static cl::OptionCategory spreadbymaskOptions("spreadbymask Options.", "spreadbymask Options");
static cl::opt<std::string> inputFile(cl::Positional, cl::desc("<input file>"), cl::Required, cl::cat(spreadbymaskOptions));
static cl::opt<std::string> maskFile(cl::Positional, cl::desc("<mask file>"), cl::Required, cl::cat(spreadbymaskOptions));

class SpreadByMask final : public BlockOrientedKernel {
public:
    SpreadByMask(KernelBuilder & b, StreamSet * const input, StreamSet * const mask, StreamSet * const output);
    void generateDoBlockMethod(KernelBuilder & b) override;
};

SpreadByMask::SpreadByMask(KernelBuilder & b, 
                           StreamSet * const input,
                           StreamSet * const mask,
                           StreamSet * const output)
    : BlockOrientedKernel(b, "spread_by_mask",
    {Binding{"input", input},
     Binding{"mask", mask}},
    {Binding{"output", output}},
    {}, {}, {}) {
    assert(input->getNumElements() == 1);
    assert(mask->getNumElements() == 1);
    assert(output->getNumElements() == 1);

     if (input == nullptr || mask == nullptr || output == nullptr) {
        throw std::runtime_error("SpreadByMask: Null stream set pointer");
    }
    if (input->getNumElements() != 1 || mask->getNumElements() != 1 || output->getNumElements() != 1) {
        throw std::runtime_error("SpreadByMask: All stream sets must have exactly one element");
    }
}

void SpreadByMask::generateDoBlockMethod(KernelBuilder & b) {
    
    llvm::errs() << "Entering generateDoBlockMethod\n";

    Value * const blockSize = b.getSize(b.getBitBlockWidth());

    llvm::errs() << "Block size: "<< *blockSize << "\n";

    BasicBlock * const entry = b.GetInsertBlock();
    BasicBlock * const processBlock = b.CreateBasicBlock("processBlock");
    BasicBlock * const exit = b.CreateBasicBlock("exit");

    b.CreateBr(processBlock);
    b.SetInsertPoint(processBlock);

    PHINode * const idx = b.CreatePHI(b.getSizeTy(), 2);
    idx->addIncoming(b.getSize(0), entry);

    llvm::errs() << "Loading input and mask bits\n";
    Value * const inputBits = b.loadInputStreamBlock("input", b.getInt32(0), idx);
    Value * const maskBits = b.loadInputStreamBlock("mask", b.getInt32(0), idx);


    if(!inputBits || !maskBits){
        llvm::errs() << "Error: simd_pdep returned null\n";
        return;  
    }

    llvm::errs() << "Performing simd_pdep\n";
    // Perform the spread operation using AVX-512 pdep instruction
    Value * spreadBits = b.simd_pdep(b.getBitBlockWidth(), inputBits, maskBits);

    if(!spreadBits) {
        llvm::errs() << "error: simd_pdep returned null\n";
    }

    llvm::errs() << "Storing output\n";

    b.storeOutputStreamBlock("output", b.getInt32(0), idx, spreadBits);

    Value * const nextIdx = b.CreateAdd(idx, b.getSize(1));
    idx->addIncoming(nextIdx, processBlock);

    Value * const done = b.CreateICmpEQ(nextIdx, blockSize);
    b.CreateCondBr(done, exit, processBlock);

    b.SetInsertPoint(exit);
    b.CreateRetVoid();

    llvm::errs() << "Exiting generateDoBlockMethod\n";
}

typedef void (*spreadbymaskFunctionType)(uint32_t fd, uint32_t mask_fd);

spreadbymaskFunctionType spreadbymask_gen(CPUDriver & driver) {

    llvm::errs() << "Entering spreadbymask Gen\n";
    auto & b = driver.getBuilder();
    auto P = driver.makePipeline({Binding{b.getInt32Ty(), "inputFileDescriptor"}, Binding{b.getInt32Ty(), "maskFileDescriptor"}}, {});

    if (!P) {
        llvm::errs() << "Error: Failed to create pipeline\n";
        return nullptr;
    }

    Scalar * inputFileDescriptor = P->getInputScalar("inputFileDescriptor");
    Scalar * maskFileDescriptor = P->getInputScalar("maskFileDescriptor");


    if (!inputFileDescriptor || !maskFileDescriptor) {
        llvm::errs() << "Error: Failed to get file descriptors\n";
        return nullptr;
    }

    llvm::errs() << "Creating mask stream\n";
    StreamSet * const maskStream = P->CreateStreamSet(1, 8);

    if (!maskStream) {
        llvm::errs() << "Error: Failed to create mask stream\n";
        return nullptr;
    }


    P->CreateKernelCall<ReadSourceKernel>(maskFileDescriptor, maskStream);
    SHOW_BIXNUM(maskStream);

    llvm::errs() << "Creating byte stream\n";
    StreamSet * const byteStream = P->CreateStreamSet(1, 8);

     if (!byteStream) {
        llvm::errs() << "Error: Failed to create byte stream\n";
        return nullptr;
     }

    P->CreateKernelCall<ReadSourceKernel>(inputFileDescriptor, byteStream);
    SHOW_BYTES(byteStream);

    llvm::errs() << "Creating spread stream\n";
    StreamSet * const spreadStream = P->CreateStreamSet(1, 8);

    if (!spreadStream) {
        llvm::errs() << "Error: Failed to create spread stream\n";
        return nullptr;
    }

    llvm::errs() << "Creating SpreadByMask kernel\n";

    try {
        P->CreateKernelCall<SpreadByMask>(byteStream, maskStream, spreadStream);
    } catch (const std::exception& e) {
        llvm::errs() << "Error creating SpreadByMask kernel: " << e.what() << "\n";
        return nullptr;
    }

    SHOW_BYTES(spreadStream);

    llvm::errs() << "Creating stdOutKernel\n";

    P->CreateKernelCall<StdOutKernel>(spreadStream);

    llvm::errs() << "Compiling Pipeline\n";
    spreadbymaskFunctionType func = nullptr;
    try {
        func = reinterpret_cast<spreadbymaskFunctionType>(P->compile());
    } catch (const std::exception& e) {
        llvm::errs() << "Error compiling pipeline: " << e.what() << "\n";
        return nullptr;
    }

    llvm::errs() << "Exiting spreadbymask_gen\n";
    return func;
}


void segfault_handler(int signal) {
    llvm::errs() << "Caught segmentation fault (signal " << signal << ")\n";
    exit(1);
}


int main(int argc, char *argv[]) {

    signal(SIGSEGV, segfault_handler);

    codegen::ParseCommandLineOptions(argc, argv, {&spreadbymaskOptions, codegen::codegen_flags()});
    CPUDriver pxDriver("spreadbymask");
    const int fd = open(inputFile.c_str(), O_RDONLY);
    const int mask_fd = open(maskFile.c_str(), O_RDONLY);
    if (LLVM_UNLIKELY(fd == -1)) {
        errs() << "Error: cannot open " << inputFile << " for processing. Skipped.\n";
        return 1;
    }
    if (LLVM_UNLIKELY(mask_fd == -1)) {
        errs() << "Error: cannot open " << maskFile << " for processing. Skipped.\n";
        close(fd);
        return 1;
    }

    llvm::errs() << "Generating spreadbymask function\n";

    /*spreadbymaskFunctionType func = spreadbymask_gen(pxDriver);
    if (func == nullptr) {
        errs() << "Error: Failed to generate spreadbymask function\n";
        close(fd);
        close(mask_fd);
        return 1;
    }*/

   spreadbymaskFunctionType fun = nullptr;
   fun = spreadbymask_gen(pxDriver);
   fun(fd,mask_fd);
   close(fd);
   close(mask_fd);

    llvm::errs() <<"Executing spreadbymask function\n";

    /*try {

        if(fd < 0 || mask_fd < 0){
            throw std::runtime_error("INvalid file descriptor");
        }
        func(fd, mask_fd);
    } catch (const std::exception& e) {
        errs() << "Error executing spreadbymask function: " << e.what() << "\n";
    }catch(...){
        errs() << "Unknown error occured during execution\n";
    }

    close(fd);
    close(mask_fd);*/
    return 0;
}