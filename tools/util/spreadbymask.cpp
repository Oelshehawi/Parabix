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



//  These declarations are for command line processing.
//  See the LLVM CommandLine 2.0 Library Manual https://llvm.org/docs/CommandLine.html
static cl::OptionCategory spreadbymaskOptions("spreadbymask Options.", "spreadbymask Options");
static cl::opt<std::string> inputFile(cl::Positional, cl::desc("<input file>"), cl::Required, cl::cat(spreadbymaskOptions));
static cl::opt<std::string> maskFile(cl::Positional, cl::desc("<mask file>"), cl::Required, cl::cat(spreadbymaskOptions));


class spreadbymaskKernel final : public MultiBlockKernel {
public:
    spreadbymaskKernel(KernelBuilder & b, StreamSet * const maskStream, StreamSet * const byteStream, StreamSet * const spreadStream)
    : MultiBlockKernel(b, "spreadbymask_kernel",
    {Binding{"maskStream", maskStream, FixedRate(1)}, Binding{"byteStream", byteStream, FixedRate(1)}},
    {Binding{"spreadStream", spreadStream, PopcountOf("maskStream")}}, {}, {}, {}) {}

protected:
void generateMultiBlockLogic(KernelBuilder & b, llvm::Value * const numOfStrides) override {
    const unsigned fieldWidth = 32;
    Value * mask = b.loadInputStreamBlock("maskStream", b.getInt32(0));
    Value * input = b.loadInputStreamBlock("byteStream", b.getInt32(0));

    //  bnc is an object that can perform arithmetic on sets of parallel bit streams
    

     /*Iterate over each bit in mask
        for (unsigned i = 0; i < 16; i++) {
            // Check if mask bit is 1
            Value * mask_bit = b.getValue(mask, i);
            if (b.getbit(mask, i) == 1) {
                // If mask bit is 1, copy corresponding input bit to output
                Value * input_bit = b.getValue(input, i);
                spread = b.or(spread, input_bit);
            }
        }*/


    // Initialize the spread stream with zeros
        Type * vec512Ty = VectorType::get(b.getInt32Ty(), int); // 16 * 32 = 512 bits
        Value * spreadVec = Constant::getNullValue(vec512Ty);

        // Create AVX-512 intrinsics to load mask and input vectors
        Function * fn = b.GetInsertBlock()->getParent();
        IRBuilder<> builder(b.getContext());
        builder.SetInsertPoint(b.GetInsertBlock());

        // Load mask and input as vectors
        Value * maskVec = builder.CreateBitCast(mask, vec512Ty);
        Value * inputVec = builder.CreateBitCast(input, vec512Ty);

        // Iterate over each bit in the mask and spread the corresponding input bits
        for (int i = 0; i < 512; i++) {
            // Extract the bit from the mask
            Value * maskBit = builder.CreateAnd(maskVec, ConstantInt::get(vec512Ty, 1 << i));
            maskBit = builder.CreateICmpNE(maskBit, Constant::getNullValue(vec512Ty));
            if (maskBit) {
                // Extract the corresponding input bit
                Value * inputBit = builder.CreateAnd(inputVec, ConstantInt::get(vec512Ty, 1 << i));
                inputBit = builder.CreateICmpNE(inputBit, Constant::getNullValue(vec512Ty));
                // Set the corresponding bit in the spread stream
                spreadVec = builder.CreateOr(spreadVec, builder.CreateShl(inputBit, i));
            }
        }

        // Store the result in the output stream
        Value * spreadCast = builder.CreateBitCast(spreadVec, b.getInt32Ty());
        b.storeOutputStreamBlock("spreadStream", b.getInt32(0), spreadCast);
    }

};

typedef void (*spreadbymaskFunctionType)(uint32_t fd, uint32_t mask_fd);

spreadbymaskFunctionType spreadbymask_gen(CPUDriver & driver) {

    auto & b = driver.getBuilder();
    auto P = driver.makePipeline({Binding{b.getInt32Ty(), "inputFileDescriptor"}, Binding{b.getInt32Ty(), "maskFileDescriptor"}}, {});

    Scalar * inputFileDescriptor = P->getInputScalar("inputFileDescriptor");
    Scalar * maskFileDescriptor = P->getInputScalar("maskFileDescriptor");


    StreamSet * const maskStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<ReadSourceKernel>(maskFileDescriptor, maskStream);
    SHOW_BIXNUM(maskStream);

    StreamSet * const byteStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<ReadSourceKernel>(inputFileDescriptor, byteStream);
    SHOW_BYTES(byteStream);

    StreamSet * const spreadStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<spreadbymaskKernel>(maskStream, byteStream, spreadStream);
    SHOW_BYTES(spreadStream);

    P->CreateKernelCall<StdOutKernel>(spreadStream);

    return reinterpret_cast<spreadbymaskFunctionType>(P->compile());



}

int main(int argc, char *argv[]) {
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

    spreadbymaskFunctionType func = nullptr;
    func = spreadbymask_gen(pxDriver);
    func(fd,mask_fd);

    close(fd);
    close(mask_fd);
    return 0;
}

