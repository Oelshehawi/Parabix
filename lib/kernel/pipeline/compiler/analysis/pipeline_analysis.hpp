#ifndef PIPELINE_KERNEL_ANALYSIS_HPP
#define PIPELINE_KERNEL_ANALYSIS_HPP

#include "../config.h"
#include "../common/common.hpp"
#include <kernel/pipeline/pipeline_builder.h>

namespace kernel {

class PipelineAnalysis : public PipelineCommonGraphFunctions {
public:

    using KernelPartitionIds = flat_map<ProgramGraph::vertex_descriptor, unsigned>;

    static PipelineAnalysis analyze(BuilderRef b, PipelineKernel * const pipelineKernel) {

        PipelineAnalysis P(pipelineKernel);

//SEED: 2622027106
//SEED: 388749444

        std::random_device rd;
        //pipeline_random_engine rng{rd()};

//        const unsigned seed = rd();
        const unsigned seed = 388749444;
        pipeline_random_engine rng{seed};

//        P.generateRandomPipelineGraph(b, graphSeed, 50, 70, 10);

        P.generateInitialPipelineGraph(b);


        // Initially, we gather information about our partition to determine what kernels
        // are within each partition in a topological order
        auto initialGraph = P.initialPartitioningPass();

        P.computeIntraPartitionRepetitionVectors(initialGraph);

        switch (codegen::PipelineCompilationMode) {
            case codegen::PipelineCompilationModeOptions::DefaultFast:
                P.simpleEstimateInterPartitionDataflow(initialGraph, rng);
                break;
            case codegen::PipelineCompilationModeOptions::Expensive:
                P.estimateInterPartitionDataflow(initialGraph, rng);
                break;
        }

        auto partitionGraph = P.postDataflowAnalysisPartitioningPass(initialGraph);

        switch (codegen::PipelineCompilationMode) {
            case codegen::PipelineCompilationModeOptions::DefaultFast:
                P.simpleSchedulePartitionedProgram(partitionGraph, rng);
                break;
            case codegen::PipelineCompilationModeOptions::Expensive:
                P.schedulePartitionedProgram(partitionGraph, rng);
                break;
        }

        // Construct the Stream and Scalar graphs
        P.transcribeRelationshipGraph(initialGraph, partitionGraph);

        P.generateInitialBufferGraph();

        P.updateInterPartitionThreadLocalBuffers();

        P.identifyOutputNodeIds();

        P.identifyInterPartitionSymbolicRates();


        P.identifyTerminationChecks();

        P.determinePartitionJumpIndices();

        #ifdef USE_PARTITION_GUIDED_SYNCHRONIZATION_VARIABLE_REGIONS
        P.identifyPartitionGuidedSynchronizationVariables();
        #endif

        P.annotateBufferGraphWithAddAttributes();

        // Finish annotating the buffer graph
        P.identifyOwnedBuffers();
        P.identifyZeroExtendedStreamSets();
        P.identifyLinearBuffers();

        P.determineBufferSize(b);


        P.makeConsumerGraph();

        P.calculatePartialSumStepFactors(b);

        P.makeTerminationPropagationGraph();

        P.determineNumOfThreads();

        P.numberDynamicRepeatingStreamSets();

        P.identifyPortsThatModifySegmentLength();

        // Finish the buffer graph
        P.determineInitialThreadLocalBufferLayout(b, rng);
        P.addStreamSetsToBufferGraph(b);

        P.gatherInfo();

        if (codegen::DebugOptionIsSet(codegen::PrintPipelineGraph)) {
            assert (b->getModule() == pipelineKernel->getModule());
            P.printBufferGraph(b, errs());
        }

        return P;
    }

private:

    // constructor

    PipelineAnalysis(PipelineKernel * const pipelineKernel)
    : PipelineCommonGraphFunctions(mStreamGraph, mBufferGraph)
    , mPipelineKernel(pipelineKernel)
    , mNumOfThreads(pipelineKernel->getNumOfThreads())
    , mKernels(pipelineKernel->mKernels)
    , mTraceProcessedProducedItemCounts(codegen::DebugOptionIsSet(codegen::TraceCounts))
    , mTraceDynamicBuffers(codegen::DebugOptionIsSet(codegen::TraceDynamicBuffers))
    , mTraceIndividualConsumedItemCounts(mTraceProcessedProducedItemCounts || mTraceDynamicBuffers)
    , IsNestedPipeline(pipelineKernel->hasAttribute(AttrId::InternallySynchronized)) {

    }

    // pipeline analysis functions

    void generateInitialPipelineGraph(BuilderRef b);

    void identifyPipelineInputs();

    void transcribeRelationshipGraph(const PartitionGraph & initialGraph, const PartitionGraph & partitionGraph);

    void gatherInfo() {
        MaxNumOfInputPorts = in_degree(PipelineOutput, mBufferGraph);
        MaxNumOfOutputPorts = out_degree(PipelineInput, mBufferGraph);
        for (auto i = FirstKernel; i <= LastKernel; ++i) {
            MaxNumOfInputPorts = std::max<unsigned>(MaxNumOfInputPorts, in_degree(i, mBufferGraph));
            MaxNumOfOutputPorts = std::max<unsigned>(MaxNumOfOutputPorts, out_degree(i, mBufferGraph));
        }
    }

    static void addKernelRelationshipsInReferenceOrdering(const unsigned kernel, const RelationshipGraph & G,
                                                          std::function<void(PortType, unsigned, unsigned)> insertionFunction);


    // partitioning analysis
    PartitionGraph initialPartitioningPass();
    PartitionGraph postDataflowAnalysisPartitioningPass(PartitionGraph & initial);

    PartitionGraph identifyKernelPartitions();

    void determinePartitionJumpIndices();

    #ifdef USE_PARTITION_GUIDED_SYNCHRONIZATION_VARIABLE_REGIONS
    void identifyPartitionGuidedSynchronizationVariables();
    #endif

    // simple scheduling analysis

    void simpleSchedulePartitionedProgram(PartitionGraph & P, pipeline_random_engine & rng);

    // scheduling analysis

    void schedulePartitionedProgram(PartitionGraph & P, pipeline_random_engine & rng);

    void analyzeDataflowWithinPartitions(PartitionGraph & P, pipeline_random_engine & rng) const;

    SchedulingGraph makeIntraPartitionSchedulingGraph(const PartitionGraph & P, const unsigned currentPartitionId) const;

    PartitionDependencyGraph makePartitionDependencyGraph(const unsigned numOfKernels, const SchedulingGraph & S) const;

    OrderingDAWG scheduleProgramGraph(const PartitionGraph & P, pipeline_random_engine & rng) const;

    OrderingDAWG assembleFullSchedule(const PartitionGraph & P, const OrderingDAWG & partial) const;

    std::vector<unsigned> selectScheduleFromDAWG(const OrderingDAWG & schedule) const;

    void addSchedulingConstraints(const std::vector<unsigned> & program);

    static bool isNonSynchronousRate(const Binding & binding);

    // buffer management analysis functions

    void addStreamSetsToBufferGraph(BuilderRef b);
    void generateInitialBufferGraph();

    void determineBufferSize(BuilderRef b);

    void identifyOwnedBuffers();

    void identifyLinearBuffers();

    void identifyOutputNodeIds();

    void identifyPortsThatModifySegmentLength();

    // thread local analysis

    void determineInitialThreadLocalBufferLayout(BuilderRef b, pipeline_random_engine & rng);

    void updateInterPartitionThreadLocalBuffers();

    // consumer analysis functions

    void makeConsumerGraph();

    // dataflow analysis functions
    void computeIntraPartitionRepetitionVectors(PartitionGraph & P);
    void estimateInterPartitionDataflow(PartitionGraph & P, pipeline_random_engine & rng);

    void computeMinimumExpectedDataflow(PartitionGraph & P);

    void identifyInterPartitionSymbolicRates();

    void calculatePartialSumStepFactors(BuilderRef b);

    void numberDynamicRepeatingStreamSets();

    void determineNumOfThreads();

    void simpleEstimateInterPartitionDataflow(PartitionGraph & P, pipeline_random_engine & rng);

    // zero extension analysis function

    void identifyZeroExtendedStreamSets();

    // termination analysis functions

    void identifyTerminationChecks();
    void makeTerminationPropagationGraph();

    // add(k) analysis functions

    void annotateBufferGraphWithAddAttributes();

    // Input truncation analysis functions

    void makeInputTruncationGraph();


public:

    // Debug functions
    void printBufferGraph(BuilderRef b, raw_ostream & out) const;
    static void printRelationshipGraph(const RelationshipGraph & G, raw_ostream & out, const StringRef name = "G");

public:

    PipelineKernel * const          mPipelineKernel;
    const unsigned					mNumOfThreads;
    Kernels                         mKernels;
    ProgramGraph                    Relationships;
    KernelPartitionIds              PartitionIds;

    const bool                      mTraceProcessedProducedItemCounts;
    const bool                      mTraceDynamicBuffers;
    const bool                      mTraceIndividualConsumedItemCounts;

    const bool                      IsNestedPipeline;

    static const unsigned           PipelineInput = 0U;
    static const unsigned           FirstKernel = 1U;
    unsigned                        LastKernel = 0;
    unsigned                        PipelineOutput = 0;
    unsigned                        FirstStreamSet = 0;
    unsigned                        LastStreamSet = 0;
    unsigned                        FirstBinding = 0;
    unsigned                        LastBinding = 0;
    unsigned                        FirstCall = 0;
    unsigned                        LastCall = 0;
    unsigned                        FirstScalar = 0;
    unsigned                        LastScalar = 0;
    unsigned                        PartitionCount = 0;
    unsigned                        NumOfThreads = 0;
    bool                            HasZeroExtendedStream = false;

    size_t                          RequiredThreadLocalStreamSetMemory = 0;

    unsigned                        MaxNumOfInputPorts = 0;
    unsigned                        MaxNumOfOutputPorts = 0;

    RelationshipGraph               mStreamGraph;
    RelationshipGraph               mScalarGraph;

    KernelIdVector                  KernelPartitionId;
    KernelIdVector                  FirstKernelInPartition;
    std::vector<unsigned>           MinimumNumOfStrides;
    std::vector<unsigned>           MaximumNumOfStrides;
    std::vector<unsigned>           StrideRepetitionVector;
    std::vector<Rational>           PartitionRootStridesPerThreadLocalPage;
    std::vector<Rational>           NumOfPartialOverflowStridesPerPartitionRootStride;

    BufferGraph                     mBufferGraph;

    std::vector<unsigned>           PartitionJumpTargetId;

    ConsumerGraph                   mConsumerGraph;

    PartialSumStepFactorGraph       mPartialSumStepFactorGraph;

    flat_set<unsigned>              mNonThreadLocalStreamSets;

    TerminationChecks               mTerminationCheck;

    TerminationPropagationGraph     mTerminationPropagationGraph;
    BitVector                       HasTerminationSignal;

    std::vector<unsigned>           mDynamicRepeatingStreamSetId;

    OwningVector<Kernel>            mInternalKernels;
    OwningVector<Binding>           mInternalBindings;
    OwningVector<StreamSetBuffer>   mInternalBuffers;
};

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief determineNumOfThreads
 ** ------------------------------------------------------------------------------------------------------------- */
inline void PipelineAnalysis::determineNumOfThreads() {
    if (IsNestedPipeline) {
        NumOfThreads = 1U;
    } else {
        const auto numKernels = LastKernel - FirstKernel + 1U;
        NumOfThreads = mPipelineKernel->getNumOfThreads();
        if (LLVM_UNLIKELY(numKernels < NumOfThreads)) {
            for (auto k = FirstKernel; k <= LastKernel; ++k) {
                if (LLVM_LIKELY(!isKernelStateFree(k))) {
                    NumOfThreads = numKernels;
                    break;
                }
            }
        }
    }
}


/** ------------------------------------------------------------------------------------------------------------- *
 * @brief printGraph
 ** ------------------------------------------------------------------------------------------------------------- */
template <typename Graph>
void printGraph(const Graph & G, raw_ostream & out, const StringRef name = "G") {

    out << "digraph \"" << name << "\" {\n";
    for (auto v : make_iterator_range(vertices(G))) {
        out << "v" << v << " [label=\"" << v << "\"];\n";
    }
    for (auto e : make_iterator_range(edges(G))) {
        const auto s = source(e, G);
        const auto t = target(e, G);
        out << "v" << s << " -> v" << t << ";\n";
    }

    out << "}\n\n";
    out.flush();
}


}

#endif
