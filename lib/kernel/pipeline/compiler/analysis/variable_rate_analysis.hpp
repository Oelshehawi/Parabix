﻿#ifndef VARIABLE_RATE_ANALYSIS_HPP
#define VARIABLE_RATE_ANALYSIS_HPP

#define PRINT_SIMULATION_DEBUG_STATISTICS

#include "pipeline_analysis.hpp"

#ifdef USE_EXPERIMENTAL_SIMULATION_BASED_VARIABLE_RATE_ANALYSIS

#include <util/slab_allocator.h>

namespace kernel {

namespace {

// #define PRINT_SIMULATION_DEBUG_STATISTICS

constexpr uint64_t DEMAND_ITERATIONS = 1000;

constexpr uint64_t DATA_ITERATIONS =   100000;

using SimulationAllocator = SlabAllocator<uint8_t>;

using length_t = int64_t;

struct SimulationPort {

    length_t QueueLength;

    virtual bool consume(length_t & pending, random_engine & rng) = 0;

    virtual void produce(random_engine & rng) = 0;

    virtual void commit(const length_t pending) {
        QueueLength -= pending;
    }

    virtual void produce_zero_if_not_fixed(random_engine & rng) {
        return produce(rng);
    }

    void * operator new (std::size_t size, SimulationAllocator & allocator) noexcept {
        return allocator.allocate<uint8_t>(size);
    }

    virtual void reset(const length_t delay) {
        QueueLength = -delay;
    }

protected:

    SimulationPort() : QueueLength(0) { }

};

struct FixedPort final : public SimulationPort {

    FixedPort(const uint32_t amount)
    : SimulationPort()
    ,  mAmount(amount) { }

    bool consume(length_t & pending, random_engine & /* rng */) override {
        pending = mAmount;
        return (QueueLength >= mAmount) ;
    }

    void produce(random_engine & /* rng */) override {
        QueueLength += mAmount;
    }

private:
    const length_t mAmount;
};


struct UniformBoundedPort final : public SimulationPort {

    UniformBoundedPort(const unsigned min, const unsigned max)
    : SimulationPort()
    ,  mMin(min), mMax(max) { }

    bool consume(length_t & pending, random_engine & rng) override {
        // The pipeline does not know how many tokens are required
        // of the streamset until after it invokes the kernel.
        if (QueueLength < mMax) {
            pending = mMax;
            return false;
        }
        std::uniform_int_distribution<uint32_t> dst(mMin, mMax);
        pending = dst(rng);
        return true;
    }

    void produce(random_engine & rng) override {
        std::uniform_int_distribution<uint32_t> dst(mMin, mMax);
        const auto m = dst(rng);
        QueueLength += m;
    }

    virtual void produce_zero_if_not_fixed(random_engine & /* rng */) { }

private:
    const uint32_t mMin;
    const uint32_t mMax;
};

struct PartialSumGenerator {

    length_t readStepValue(const uint64_t start, const uint64_t end, random_engine & rng) {

        // Since PartialSum rates can have multiple ports referring to the same reference streamset, we store the
        // history of partial sum values in a circular buffer but silently drop entries after every user has read
        // the value.

        // NOTE: since lazy generation is *not* an optimization here, this algorithm assumes the history array is
        // always fully populated with values in which at least one PartialSum port has yet to read.

        assert (end > start);
        assert (start >= HeadPosition);

        const auto required = (end - HeadPosition);

        if (LLVM_UNLIKELY(required >= Capacity)) {

            const auto r = (required + Capacity * 2 - 1);
            const auto newCapacity = r - (r % required);
            assert (newCapacity >= Capacity * 2);
            uint64_t * const newHistory = Allocator.allocate<uint64_t>(newCapacity);

            size_t k = 0;
            for (;;) {
                const auto l = (HeadOffset + k) % Capacity;
                newHistory[k] = History[l];
                if (l == TailOffset) break;
                ++k;
                assert (k < Capacity);
            }
            Allocator.deallocate(History);
            HeadOffset = 0;
            TailOffset = k;
            History = newHistory;
            Capacity = newCapacity;
        }

        assert ((HeadOffset < Capacity) && (TailOffset < Capacity));
        auto t = (TailOffset + 1) % Capacity;
        while (t != HeadOffset) {
            History[t] = History[TailOffset] + generateStepValue(rng);
            TailOffset = t;
            t = (t + 1) % Capacity;
        }

        const auto i = ((start - HeadPosition) + HeadOffset) % Capacity;
        const auto j = ((end - HeadPosition) + HeadOffset) % Capacity;
        const auto a = History[i];
        const auto b = History[j];
        assert (a <= b);
        const auto c = b - a;
        assert (c <= (MaxStepSize * (end - start)));
        return static_cast<length_t>(c) ;
    }

    void updateReadPosition(const unsigned userId, const uint64_t position) {
        assert (userId < Users);
        UserReadPosition[userId] = position;
        auto min = position;
        for (unsigned i = 0; i < Users; ++i) {
            min = std::min(min, UserReadPosition[i]);
        }
        assert (HeadPosition <= min);
        const auto k = (min - HeadPosition);
        HeadOffset = (HeadOffset + k) % Capacity;
        HeadPosition = min;
    }

    PartialSumGenerator(const unsigned users, const unsigned historyLength, const unsigned maxSize, SimulationAllocator & allocator)
    : MaxStepSize(maxSize)
    , Users(users)
    , HeadPosition(0)
    , HeadOffset(0)
    , TailOffset(0)
    , Capacity(std::max<unsigned>(historyLength * 2, 32))
    , History(allocator.allocate<uint64_t>(Capacity))
    , UserReadPosition(allocator.allocate<uint64_t>(users))
    , Allocator(allocator) {
        assert (historyLength > 0);
    }

    void initializeGenerator(random_engine & rng) {
        uint64_t partialSum = 0;
        History[0] = 0;
        for (unsigned i = 1; i < Capacity; ++i) {
            partialSum += generateStepValue(rng);
            History[i] = partialSum;
        }
        TailOffset = Capacity - 1;
        for (unsigned i = 0; i < Users; ++i) {
            UserReadPosition[i] = 0;
        }
    }

    void * operator new (std::size_t size, SimulationAllocator & allocator) noexcept {
        return allocator.allocate<uint8_t>(size);
    }

protected:

    virtual uint32_t generateStepValue(random_engine & rng) const = 0;

    const uint32_t MaxStepSize;

private:
    const unsigned Users;
    uint64_t HeadPosition;
    unsigned HeadOffset;
    unsigned TailOffset;
    unsigned Capacity;

    uint64_t * History;
    uint64_t * const UserReadPosition;

    SimulationAllocator & Allocator;
};

struct UniformDistributionPartialSumGenerator : public PartialSumGenerator {

    UniformDistributionPartialSumGenerator(const uint32_t users,
                                           const uint32_t maxValuePerStep,
                                           const unsigned historyLength,
                                           SimulationAllocator & allocator)
    : PartialSumGenerator(users, historyLength, maxValuePerStep, allocator) {
        assert (maxValuePerStep > 0);
    }

protected:

    uint32_t generateStepValue(random_engine & rng) const override {
        std::uniform_int_distribution<uint32_t> dst(0U, MaxStepSize);
        const auto r = dst(rng);
        assert (r <= MaxStepSize);
        return r;
    }

};

struct PartialSumPort final : public SimulationPort {

    PartialSumPort(PartialSumGenerator & generator, const unsigned userId, const unsigned step)
    : SimulationPort()
    , Generator(generator), UserId(userId), Step(step), Index(0)
    #ifndef NDEBUG
    , PreviousValue(-1U) // temporary sanity test value
    #endif
    {
        assert (step > 0);
    }

    bool consume(length_t & pending, random_engine & rng) override {
        const auto m = Generator.readStepValue(Index, Index + Step, rng);
        assert (m == PreviousValue || PreviousValue == -1U);
        pending = m;
        #ifndef NDEBUG
        PreviousValue = m;
        #endif
        return (QueueLength >= m);
    }

    void commit(const length_t pending) override {
        QueueLength -= pending;
        Index += Step;
        #ifndef NDEBUG
        PreviousValue = -1U;
        #endif
        Generator.updateReadPosition(UserId, Index);
    }

    void produce(random_engine & rng) override {
        const auto m = Generator.readStepValue(Index, Index + Step, rng);
        QueueLength += m;
        Index += Step;
        Generator.updateReadPosition(UserId, Index);
    }

    virtual void produce_zero_if_not_fixed(random_engine & /* rng */) { }

private:
    PartialSumGenerator & Generator;
    const unsigned UserId;
    const unsigned Step;
    unsigned Index;
    #ifndef NDEBUG
    unsigned PreviousValue;
    #endif
};


struct RelativePort final : public SimulationPort {

    RelativePort(const length_t & baseRateValue)
    : SimulationPort()
    , BaseRateValue(baseRateValue){ }

    bool consume(length_t & pending, random_engine & /* rng */) override {
        pending = BaseRateValue;
        return (QueueLength >= BaseRateValue);
    }

    void produce(random_engine & /* rng */) override {
        const auto m = BaseRateValue;
        QueueLength += m;
    }

private:
    const length_t & BaseRateValue;
};

struct GreedyPort final : public SimulationPort {

    GreedyPort(const uint32_t min)
    : SimulationPort()
    , LowerBound(min){ }

    bool consume(length_t & pending, random_engine & /* rng */) override {
        if (QueueLength < LowerBound || QueueLength == 0) {
            pending = LowerBound;
            return false;
        } else {
            pending = QueueLength;
        }
        return true;
    }

    void produce(random_engine & /* rng */) override {
        llvm_unreachable("uncaught program error? greedy rate cannot be an output rate");
    }

private:
    const uint32_t LowerBound;
};

struct SimulationNode {
    SimulationPort ** const Input;
    SimulationPort ** const Output;
    const unsigned Inputs;
    const unsigned Outputs;

    virtual void demand(length_t * const pendingArray, random_engine & rng) = 0;

    virtual void fire(length_t * const pendingArray, random_engine & rng, uint64_t *& history) = 0;

    virtual void fire_produce_zero_if_not_fixed(length_t * const pendingArray, random_engine & rng, uint64_t *& history) {
        return fire(pendingArray, rng, history);
    }

    void * operator new (std::size_t size, SimulationAllocator & allocator) noexcept {
        return allocator.allocate<uint8_t>(size);
    }

    virtual void reset() {}

protected:

    SimulationNode(const unsigned inputs, const unsigned outputs, SimulationAllocator & allocator)
    : Input(inputs ? allocator.allocate<SimulationPort *>(inputs) : nullptr),
      Output(outputs ? allocator.allocate<SimulationPort *>(outputs) : nullptr),
      Inputs(inputs), Outputs(outputs) {

    }
};

// we use a fork for both streamsets and relative rates
struct SimulationFork final : public SimulationNode {

    SimulationFork(const unsigned inputs, const unsigned outputs, SimulationAllocator & allocator)
    : SimulationNode(inputs, outputs, allocator) {

    }

    void demand(length_t * const /* endingArray */, random_engine & /* rng */) override {
        assert (Inputs == 1);
        SimulationPort * const I = Input[0];
        const auto ql = I->QueueLength;
        assert (ql >= 0);
        length_t demand = 0;
        for (unsigned i = 0; i < Outputs; ++i) {
            SimulationPort * const O = Output[i];
            O->QueueLength += ql;
            demand = std::min(demand, O->QueueLength);
        }
        assert (demand <= 0);
        I->QueueLength = demand;
        for (unsigned i = 0; i < Outputs; ++i) {
            SimulationPort * const O = Output[i];
            O->QueueLength -= demand;
            assert (O->QueueLength >= 0);
        }
    }

    void fire(length_t * const /* endingArray */, random_engine & /* rng */, uint64_t *& /* history */) override {
        assert (Inputs == 1);
        SimulationPort * const I = Input[0];
        const auto ql = I->QueueLength;
        assert (ql >= 0);
        I->QueueLength = 0;
        for (unsigned i = 0; i < Outputs; ++i) {
            Output[i]->QueueLength += ql;
        }
    }

};

struct SimulationActor : public SimulationNode {

    SimulationActor(const unsigned inputs, const unsigned outputs, SimulationAllocator & allocator)
    : SimulationNode(inputs, outputs, allocator)
    , SumOfStrides(0)
    , SumOfStridesSquared(0) {

    }

    void demand(length_t * const pendingArray, random_engine & rng) override {
        uint64_t strides = 0;
        assert (Inputs > 0 && Outputs > 0);
        // Greedily consume any input on the incoming channels
        for (;;) {
            // can't remove any items until we determine we can execute a full stride
            for (unsigned i = 0; i < Inputs; ++i) {
                SimulationPort * const I = Input[i];
                if (!I->consume(pendingArray[i], rng)) {
                    goto no_more_pending_input;
                }
            }
            for (unsigned i = 0; i < Inputs; ++i) {
                Input[i]->commit(pendingArray[i]);
            }
            for (unsigned i = 0; i < Outputs; ++i) {
                Output[i]->produce(rng);
            }
            ++strides;
        }
no_more_pending_input:
        // Then satisfy any demands on the output channels
        uint64_t additionalStrides = 0;
        for (unsigned i = 0; i < Outputs; ++i) {
            while (Output[i]->QueueLength < 0L) {
                for (unsigned j = 0; j < Outputs; ++j) {
                    Output[j]->produce(rng);
                }
                ++additionalStrides;
            }
        }

        // Demand enough input to satisfy the output channels
        for (unsigned i = 0; i < Inputs; ++i) {
            SimulationPort * const I = Input[i];
            for (auto d = additionalStrides; d--; ) {
                I->consume(pendingArray[i], rng);
                I->commit(pendingArray[i]);
            }
        }
        #ifndef NDEBUG
        for (unsigned i = 0; i < Outputs; ++i) {
            assert (Output[i]->QueueLength >= 0);
        }
        #endif
        strides += additionalStrides;

        SumOfStrides += strides;
        SumOfStridesSquared += (strides * strides);
    }

    void fire(length_t * const pendingArray, random_engine & rng, uint64_t *& history) override {
        uint64_t strides = 0;
        for (;;) {
            // can't remove any items until we determine we can execute a full stride
            for (unsigned i = 0; i < Inputs; ++i) {
                SimulationPort * const I = Input[i];
                if (!I->consume(pendingArray[i], rng)) {
                    SumOfStrides += strides;
                    SumOfStridesSquared += (strides * strides);
                    *history++ = strides;
                    return;
                }
            }
            for (unsigned i = 0; i < Inputs; ++i) {
                Input[i]->commit(pendingArray[i]);
            }
            for (unsigned i = 0; i < Outputs; ++i) {
                Output[i]->produce(rng);
            }
            ++strides;
        }
    }

    virtual void fire_produce_zero_if_not_fixed(length_t * const pendingArray, random_engine & rng, uint64_t *& history) {
        uint64_t strides = 0;
        for (;;) {
            // can't remove any items until we determine we can execute a full stride
            for (unsigned i = 0; i < Inputs; ++i) {
                SimulationPort * const I = Input[i];
                if (!I->consume(pendingArray[i], rng)) {
                    SumOfStrides += strides;
                    SumOfStridesSquared += (strides * strides);
                    *history++ = strides;
                    return;
                }
            }
            for (unsigned i = 0; i < Inputs; ++i) {
                Input[i]->commit(pendingArray[i]);
            }
            for (unsigned i = 0; i < Outputs; ++i) {
                Output[i]->produce_zero_if_not_fixed(rng);
            }
            ++strides;
        }
    }

    void reset() override {
        SimulationNode::reset();
        SumOfStrides = 0;
        SumOfStridesSquared = 0;
    }

    uint64_t SumOfStrides;
    uint64_t SumOfStridesSquared;
};

struct SimulationSourceActor final : public SimulationActor {

    SimulationSourceActor(const unsigned outputs,
                          SimulationAllocator & allocator)
    : SimulationActor(0, outputs, allocator)
    , RequiredIterations(1) {

    }

    void demand(length_t * const /* pendingArray */, random_engine & rng) override {
        for (auto r = RequiredIterations; r--; ){
            for (unsigned i = 0; i < Outputs; ++i) {
                Output[i]->produce(rng);
            }
        }
        uint64_t strides = RequiredIterations;
        // First we satisfy any demands on the output channels
        for (unsigned i = 0; i < Outputs; ++i) {
            while (Output[i]->QueueLength < 0L) {
                for (unsigned j = 0; j < Outputs; ++j) {
                    Output[j]->produce(rng);
                }
                ++strides;
            }
        }
        SumOfStrides += strides;
        SumOfStridesSquared += (strides * strides);
        #ifndef NDEBUG
        for (unsigned i = 0; i < Outputs; ++i) {
            assert (Output[i]->QueueLength >= 0);
        }
        #endif
    }

    void fire(length_t * const /* pendingArray */, random_engine & rng, uint64_t *& history) override {
        for (auto r = RequiredIterations; r--; ){
            for (unsigned i = 0; i < Outputs; ++i) {
                Output[i]->produce(rng);
            }
        }
        const uint64_t strides = RequiredIterations;
        SumOfStrides += strides;
        SumOfStridesSquared += (strides * strides);
        *history++ = strides;
    }

    virtual void fire_produce_zero_if_not_fixed(length_t * const /* pendingArray */, random_engine & rng, uint64_t *& history) {
        for (auto r = RequiredIterations; r--; ){
            for (unsigned i = 0; i < Outputs; ++i) {
                Output[i]->produce_zero_if_not_fixed(rng);
            }
        }
        const uint64_t strides = RequiredIterations;
        SumOfStrides += strides;
        SumOfStridesSquared += (strides * strides);
        *history++ = strides;
    }

    unsigned RequiredIterations;
};

struct SimulationSinkActor final : public SimulationActor {

    SimulationSinkActor(const unsigned inputs, SimulationAllocator & allocator)
    : SimulationActor(inputs, 0, allocator) {

    }

    void demand(length_t * const pendingArray, random_engine & rng) override {
        // In a demand-driven system, a sink actor must always require at least
        // one iteration to enforce the demands on the preceding network.
        for (unsigned i = 0; i < Inputs; ++i) {
            Input[i]->consume(pendingArray[i], rng);
        }
        uint64_t strides = 1;
        // can't remove any items until we determine we can execute a full stride
        for (;;) {
            for (unsigned i = 0; i < Inputs; ++i) {
                Input[i]->commit(pendingArray[i]);
            }
            for (unsigned i = 0; i < Inputs; ++i) {
                if (!Input[i]->consume(pendingArray[i], rng)) {
                    SumOfStrides += strides;
                    SumOfStridesSquared += (strides * strides);
                    return;
                }
            }
            ++strides;
        }
    }

};

struct BlockSizeActor final : public SimulationActor {

    BlockSizeActor(const unsigned blockSize, SimulationAllocator & allocator)
    : SimulationActor(1, 1, allocator)
    , BlockSize(blockSize) { }

    void demand(length_t * const /* pendingArray */, random_engine & /* rng */) override {
        assert (Inputs == 1 && Outputs == 1);
        // round up the demand but deposit "added" items in the output port
        SimulationPort * const I = Input[0];
        assert (I->QueueLength >= 0);
        SimulationPort * const O = Output[0];
        const auto ql = I->QueueLength + O->QueueLength;
        if (LLVM_LIKELY(ql < 0)) {
            const length_t bs = BlockSize;
            const auto r = ((-ql) % bs);
            const auto d = (ql + r) + bs;
            assert ((d % bs) == 0);
            SimulationPort * const I = Input[0];
            I->QueueLength -= d;
            assert ((I->QueueLength % bs) == 0);
            O->QueueLength = (r - bs);
        } else {
            I->QueueLength = 0;
            O->QueueLength = ql;
        }
    }

    void fire(length_t * const /* pendingArray */, random_engine & /* rng */, uint64_t *& /* history */) override {
        assert (Inputs == 1 && Outputs == 1);
        SimulationPort * const I = Input[0];
        const auto ql = I->QueueLength;
        assert (ql >= 0);
        SimulationPort * const O = Output[0];
        assert ((O->QueueLength % BlockSize) == 0);
        const auto r = (ql % BlockSize);
        O->QueueLength += (ql - r);
        assert ((O->QueueLength % BlockSize) == 0);
        I->QueueLength = r;
    }

private:
    const unsigned BlockSize;
};


} // end of anonymous namespace

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief computeExpectedVariableRateDataflow
 *
 * This algorithm uses simulation to try and determine the expected number of strides per segment and standard
 * deviation. It executes a data-driven simulation to converge upon a solution.
 *
 * Since we're only interested in modelling the steady state with an infinite input stream, we ignore attributes
 * such as Add and ZeroExtend but do consider Delay, LookAhead, and BlockSize.
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineAnalysis::estimateInterPartitionDataflow(PartitionGraph & P, random_engine & rng) {

    struct PortNode {
        unsigned Binding;
        unsigned StreamSet;
        PortNode() = default;
        PortNode(const unsigned binding, const unsigned streamSet)
        : Binding(binding)
        , StreamSet(streamSet) {

        }
    };

    using PortGraph = adjacency_list<vecS, vecS, bidirectionalS, PortNode>;

    struct PartitionPort {
        RateId Type;
        unsigned LowerBound;
        unsigned UpperBound;
        unsigned Delay;
        unsigned Reference;
        unsigned MaxStepSize;

        SimulationPort * PortObject;

        PartitionPort() = default;
        PartitionPort(RateId type, const unsigned lb, const unsigned ub,
                      const unsigned delay, const unsigned refId, const unsigned maxStepSize)
        : Type(type), LowerBound(lb), UpperBound(ub)
        , Delay(delay)
        , Reference(refId)
        , MaxStepSize(maxStepSize)
        , PortObject(nullptr) {

        }

        bool operator == (const PartitionPort & other) const {
            if (Type != other.Type) return false;
            if (UpperBound != other.UpperBound) return false;
            if (Reference != other.Reference) return false;
            if (LowerBound != other.LowerBound) return false;
            if (Delay != other.Delay) return false;
            if (MaxStepSize != other.MaxStepSize) return false;
            return true;
        }
    };

    struct NodeData {
        unsigned BlockSize = 0;
        NodeData(const unsigned blockSize = 0) : BlockSize(blockSize) { }
    };


    using Graph = adjacency_list<vecS, vecS, bidirectionalS, NodeData, PartitionPort>;


    struct PartialSumData {
        unsigned StepSize;
        unsigned RequiredCapacity;
        unsigned GCD;
        unsigned Count;
        unsigned Index;

        PartialSumData(const unsigned stepSize, unsigned capacity = 1, unsigned count = 0)
        : StepSize(stepSize), RequiredCapacity(capacity), GCD(capacity), Count(count), Index(0) {

        }
    };

    // scan through the graph and build up a temporary graph first so we can hopefully lay the
    // memory out for the simulation graph in a more prefetch friendly way.

    // TODO: we need a more systematic approach for reasoning about the maximum value of
    // any partialsum value. We can reason about it easily when they're translated from a
    // popcount but not as directly when from an arbitrary partialsum.

    const auto numOfPartitions = num_vertices(P);

    #ifndef NDEBUG
    BEGIN_SCOPED_REGION
    const reverse_traversal tmp(numOfPartitions);
    assert (is_valid_topological_sorting(tmp, P));
    END_SCOPED_REGION
    #endif

    Graph G(numOfPartitions);

    flat_map<unsigned, PartialSumData> partialSumMap;

    flat_map<unsigned, unsigned> streamSetMap;

    std::vector<unsigned> ordering;

    for (unsigned partitionId = 0; partitionId < numOfPartitions; ++partitionId) {
        const PartitionData & N = P[partitionId];
        const auto n = N.Kernels.size();
        assert (N.LinkedGroupId < numOfPartitions);
        assert (N.Repetitions.size() == n);
        for (unsigned idx = 0; idx < n; ++idx) {
            const auto kernelId = N.Kernels[idx];
            assert (Relationships[kernelId].Type == RelationshipNode::IsKernel);
            const RelationshipNode & producerNode = Relationships[kernelId];
            const Kernel * const kernelObj = producerNode.Kernel;
            const auto reps = N.Repetitions[idx] * kernelObj->getStride();

            if (LLVM_UNLIKELY(isa<PopCountKernel>(kernelObj))) {
                const Binding & input = cast<PopCountKernel>(kernelObj)->getInputStreamSetBinding(0);
                const ProcessingRate & rate = input.getRate();
                assert (rate.isFixed());
                const auto stepSize = rate.getRate() * reps;
                assert (stepSize.denominator() == 1);
                const unsigned k = stepSize.numerator();
                const auto output = child(kernelId, Relationships);
                assert (Relationships[output].Type == RelationshipNode::IsBinding);
                const auto streamSet = child(output, Relationships);
                assert (Relationships[streamSet].Type == RelationshipNode::IsRelationship);
                assert (isa<StreamSet>(Relationships[streamSet].Relationship));
                partialSumMap.emplace(streamSet, PartialSumData{k});
            }

            // We cannot assume that the ports for this kernel ensure that a referred port
            // occurs prior to the referee.

            PortGraph H;

            for (const auto e : make_iterator_range(in_edges(kernelId, Relationships))) {
                const auto input = source(e, Relationships);
                if (Relationships[input].Type == RelationshipNode::IsBinding) {
                    const auto f = first_in_edge(input, Relationships);
                    assert (Relationships[f].Reason != ReasonType::Reference);
                    const auto streamSet = source(f, Relationships);
                    assert (Relationships[streamSet].Type == RelationshipNode::IsRelationship);
                    assert (isa<StreamSet>(Relationships[streamSet].Relationship));
                    const auto g = first_in_edge(streamSet, Relationships);
                    assert (Relationships[g].Reason != ReasonType::Reference);
                    const auto output = source(g, Relationships);
                    assert (Relationships[output].Type == RelationshipNode::IsBinding);
                    const auto h = first_in_edge(output, Relationships);
                    assert (Relationships[h].Reason != ReasonType::Reference);
                    const auto producer = source(h, Relationships);
                    assert (Relationships[producer].Type == RelationshipNode::IsKernel);
                    const auto c = PartitionIds.find(producer);
                    assert (c != PartitionIds.end());
                    const auto producerPartitionId = c->second;
                    assert (producerPartitionId <= partitionId);
                    if (producerPartitionId != partitionId) {
                        add_vertex(PortNode{static_cast<unsigned>(input), static_cast<unsigned>(streamSet)}, H);
                    }
                }
            }

            const auto numOfInputs = num_vertices(H);

            for (const auto e : make_iterator_range(out_edges(kernelId, Relationships))) {
                const auto output = target(e, Relationships);
                if (Relationships[output].Type == RelationshipNode::IsBinding) {
                    const auto f = first_out_edge(output, Relationships);
                    assert (Relationships[f].Reason != ReasonType::Reference);
                    const auto streamSet = target(f, Relationships);
                    assert (Relationships[streamSet].Type == RelationshipNode::IsRelationship);
                    assert (isa<StreamSet>(Relationships[streamSet].Relationship));
                    for (const auto e : make_iterator_range(out_edges(streamSet, Relationships))) {
                        const auto input = target(e, Relationships);
                        const RelationshipNode & inputNode = Relationships[input];
                        assert (inputNode.Type == RelationshipNode::IsBinding);
                        const auto f = first_out_edge(input, Relationships);
                        assert (Relationships[f].Reason != ReasonType::Reference);
                        const auto consumer = target(f, Relationships);
                        const auto c = PartitionIds.find(consumer);
                        assert (c != PartitionIds.end());
                        const auto consumerPartitionId = c->second;
                        assert (partitionId <= consumerPartitionId);
                        if (consumerPartitionId != partitionId) {
                            add_vertex(PortNode{static_cast<unsigned>(output), static_cast<unsigned>(streamSet)}, H);
                            break;
                        }
                    }
                }
            }

            const auto numOfPorts = num_vertices(H);

            if (numOfPorts > 0) {
                for (unsigned i = 0; i < numOfPorts; ++i) {
                    const auto & portNode = H[i];
                    const RelationshipNode & node = Relationships[portNode.Binding];
                    assert (node.Type == RelationshipNode::IsBinding);
                    const Binding & binding = node.Binding;
                    const ProcessingRate & rate = binding.getRate();
                    if (LLVM_UNLIKELY(rate.isRelative() || rate.isPartialSum())) {
                        RelationshipGraph::in_edge_iterator ei, ei_end;
                        std::tie(ei, ei_end) = in_edges(portNode.Binding, Relationships);
                        assert (in_degree(portNode.Binding, Relationships) == 2);
                        const auto input = *ei++;
                        assert (Relationships[*ei].Reason == ReasonType::Reference);
                        const auto ref = source(*ei, Relationships);
                        assert (Relationships[ref].Type == RelationshipNode::IsBinding);
                        assert (ref != portNode.Binding);

                        if (LLVM_LIKELY(rate.isPartialSum())) {

                            const Binding & refBinding = Relationships[ref].Binding;
                            const ProcessingRate & refRate = refBinding.getRate();
                            assert (refRate.isFixed());
                            const auto R = refRate.getRate() * reps;
                            assert (R.denominator() == 1);
                            const unsigned cap = R.numerator();
                            assert (cap > 0);

                            const auto partialSumStreamSet = parent(ref, Relationships);
                            assert (Relationships[partialSumStreamSet].Type == RelationshipNode::IsRelationship);
                            assert (isa<StreamSet>(Relationships[partialSumStreamSet].Relationship));
                            auto p = partialSumMap.find(partialSumStreamSet);
                            if (p == partialSumMap.end()) {

                                // TODO: make a way to infer the max (diff) value of PartialSum streams
                                // outside of this process.

                                // A PartialSum port may refer to a generated streamset. We still want to
                                // infer the maximum value of the counter.

                                assert (Relationships[input].Reason != ReasonType::Reference);
                                const auto streamSet = source(input, Relationships);
                                assert (Relationships[streamSet].Type == RelationshipNode::IsRelationship);
                                const auto output = parent(streamSet, Relationships);
                                assert (Relationships[output].Type == RelationshipNode::IsBinding);
                                const auto producer = parent(output, Relationships);
                                assert (Relationships[producer].Type == RelationshipNode::IsKernel);

                                const Binding & outputBinding = Relationships[output].Binding;
                                const ProcessingRate & outputRate = outputBinding.getRate();

                                const Kernel * const kernelObj = Relationships[producer].Kernel;
                                const auto strideSize = kernelObj->getStride();

                                const auto c = PartitionIds.find(producer);
                                assert (c != PartitionIds.end());
                                const auto producerPartitionId = c->second;
                                assert (producerPartitionId <= partitionId);

                                const PartitionData & D = P[producerPartitionId];
                                const auto h = std::find(D.Kernels.begin(), D.Kernels.end(), producer);
                                assert (h != D.Kernels.end());
                                const auto j = std::distance(D.Kernels.begin(), h);

                                const auto reps = D.Repetitions[j] * strideSize;
                                const auto stepSize = outputRate.getUpperBound() * reps;
                                assert (stepSize.denominator() == 1);
                                const unsigned k = stepSize.numerator();
                                assert (k > 0);

                                partialSumMap.emplace(partialSumStreamSet, PartialSumData{k, cap, 1});
                            } else {
                                PartialSumData & P = p->second;
                                if (P.Count == 0) {
                                    P.RequiredCapacity = cap;
                                    P.GCD = cap;
                                    P.Count = 1;
                                } else {
                                    P.RequiredCapacity = boost::lcm<unsigned>(P.RequiredCapacity, cap);
                                    P.GCD = boost::gcd<unsigned>(P.GCD, cap);
                                    P.Count++;
                                }
                            }
                        }

                        for (unsigned j = 0; j < numOfPorts; ++j) {
                            if (H[j].Binding == ref) {
                                add_edge(i, j, H);
                                break;
                            }
                        }

                    }
                }
                assert (ordering.empty());
                lexical_ordering(H, ordering);
                assert (ordering.size() == numOfPorts);

                // A relative rate can be either relative to an input or an output rate. Only an output port can be
                // relative to an output port and output base ports can be handled easily by contracting the output
                // streamsets.

                // When a port is relative to an input rate, we need to produce or consume data at an equivalent
                // rate. If the base rate is a PartialSum, we could subsitute the Relative rate with the PartialSum
                // rate but if its a Bounded rate, we need to reuse the same random number. Because its a Bounded
                // rate, we know that the partitioning algorithm must place the producer and consumer(s) of the
                // Bounded rate into separate partitions so the base rate will exist somewhere in the simulation
                // graph. Since this is computationally cheaper than using a PartialSum look-up, we use the
                // RelativePort for PartialSums whenever possible.

                // TODO: this still assumes ports relative to a PartialSum will have the PartialSum in the graph.
                // We need to make it so that the relative port is considered a PartialSum itself.

                for (unsigned i = 0; i < numOfPorts; ++i) {
                    const auto j = ordering[i];
                    const auto & portNode = H[j];
                    const RelationshipNode & node = Relationships[portNode.Binding];
                    assert (node.Type == RelationshipNode::IsBinding);
                    const Binding & binding = node.Binding;
                    const ProcessingRate & rate = binding.getRate();

                    unsigned streamSet = 0;
                    unsigned refId = 0;
                    unsigned stepLength = 0;

                    unsigned blockSize = 0;
                    unsigned delay = 0;
                    for (const Attribute & attr : binding.getAttributes()) {
                        switch (attr.getKind()) {
                            case AttrId::Delayed:
                            case AttrId::LookAhead:
                                delay = attr.amount();
                                break;
                            case AttrId::BlockSize:
                                BEGIN_SCOPED_REGION
                                const auto b = attr.amount() * N.Repetitions[idx];
                                assert (b.denominator() == 1);
                                blockSize = b.numerator();
                                END_SCOPED_REGION
                                break;
                            default:
                                break;
                        }
                    }

                    auto getRelativeRefId = [&](const unsigned k) {
                        unsigned r = 0;
                        for (; r < i; ++r) {
                            if (ordering[r] == k) {
                                return r;
                            }
                        }
                        llvm_unreachable("cannot find relative ref port?");
                    };

                    auto getPartialSumRefId = [&](const unsigned binding) {
                        RelationshipGraph::in_edge_iterator ei, ei_end;
                        std::tie(ei, ei_end) = in_edges(binding, Relationships);
                        assert (in_degree(binding, Relationships) > 1);
                        while (++ei != ei_end) {
                            if (LLVM_LIKELY(Relationships[*ei].Reason == ReasonType::Reference)) {
                                const auto ref = source(*ei, Relationships);
                                assert (Relationships[ref].Type == RelationshipNode::IsBinding);
                                const Binding & refBinding = Relationships[ref].Binding;
                                const ProcessingRate & refRate = refBinding.getRate();
                                assert (refRate.getKind() == RateId::Fixed);
                                const auto r = refRate.getRate() * reps;
                                assert (r.denominator() == 1);
                                stepLength = r.numerator();
                                const auto id = parent(ref, Relationships);
                                assert (partialSumMap.count(id) != 0);
                                return id;
                            }
                        }
                        llvm_unreachable("cannot find partialsum ref port?");
                    };

                    auto makePartitionPort = [&]() -> PartitionPort {
                        unsigned lb = 0, ub = 0;
                        switch (rate.getKind()) {
                            case RateId::Fixed:
                            case RateId::Bounded:
                                BEGIN_SCOPED_REGION
                                const auto a = reps * rate.getLowerBound();
                                assert (a.denominator() == 1);
                                lb = a.numerator();
                                const auto b = reps * rate.getUpperBound();
                                assert (b.denominator() == 1);
                                ub = b.numerator();
                                END_SCOPED_REGION
                                break;
                            case RateId::PartialSum:
                                BEGIN_SCOPED_REGION
                                const auto b = (N.Repetitions[idx] * rate.getUpperBound());
                                assert (b.denominator() == 1);
                                assert (stepLength > 0);
                                assert (refId > 0);
                                ub = b.numerator();
                                END_SCOPED_REGION
                                break;
                            case RateId::Greedy:
                            case RateId::Unknown:
                                assert (rate.getLowerBound().denominator() == 1);
                                lb = rate.getLowerBound().numerator();
                                break;
                            default:
                                llvm_unreachable("unhandled processing rate type in variable rate simulator");
                        }
                        return PartitionPort{rate.getKind(), lb, ub, delay, refId, stepLength};
                    };

                    if (j < numOfInputs) {
                        const auto itr = streamSetMap.find(portNode.StreamSet);
                        assert (itr != streamSetMap.end());
                        streamSet = itr->second;
                        assert (in_degree(streamSet, G) == 1);
                        if (rate.isRelative()) {
                            const auto k = parent(j, H);
                            assert (k < numOfInputs);
                            refId = getRelativeRefId(k);
                        } else if (rate.isPartialSum()) {
                            refId = getPartialSumRefId(portNode.Binding);
                        }
                        // if we already have a matching countable rate, use that intead.
                        const auto port = makePartitionPort();
                        if (rate.isFixed() || rate.isPartialSum()) {
                            for (const auto e : make_iterator_range(in_edges(partitionId, G))) {
                                const auto u = source(e, G);
                                if (LLVM_UNLIKELY(u == streamSet)) {
                                    if (port == G[e]) {
                                        if (LLVM_UNLIKELY(blockSize == 0 || G[u].BlockSize == blockSize)) {
                                            goto equivalent_port_exists;
                                        } else {
                                            for (const auto f : make_iterator_range(out_edges(streamSet, G))) {
                                                const auto v = target(f, G);
                                                assert (v < numOfPartitions || G[v].BlockSize != 0);
                                                if (G[v].BlockSize == blockSize) {
                                                    for (const auto g : make_iterator_range(out_edges(v, G))) {
                                                        assert (target(g, G) < numOfPartitions);
                                                        if (target(g, G) == partitionId) {
                                                            goto equivalent_port_exists;
                                                        }
                                                    }
                                                    add_edge(v, partitionId, PartitionPort{RateId::Fixed, blockSize, blockSize, 0, 0, 0}, G);
                                                    goto equivalent_port_exists;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        assert (in_degree(streamSet, G) == 1);
                        if (blockSize) {
                            const auto blockSizeNode = add_vertex(blockSize, G);
                            add_edge(streamSet, blockSizeNode, port, G);
                            add_edge(blockSizeNode, partitionId, PartitionPort{RateId::Fixed, blockSize, blockSize, 0, 0, 0}, G);
                        } else {
                            add_edge(streamSet, partitionId, port, G);
                        }
                    } else { // is an output
                        assert (streamSetMap.find(portNode.StreamSet) == streamSetMap.end());
                        if (LLVM_UNLIKELY(rate.isRelative())) {
                            const auto k = parent(j, H);
                            if (k >= numOfInputs) {
                                const auto itr = streamSetMap.find(H[k].StreamSet);
                                assert (itr != streamSetMap.end());
                                streamSet = itr->second;
                                assert (in_degree(streamSet, G) == 1);
                                goto fuse_existing_streamset;
                            }
                            refId = getRelativeRefId(k);
                        } else {
                            if (rate.isFixed() || rate.isPartialSum()) {

                                if (rate.isPartialSum()) {
                                    refId = getPartialSumRefId(portNode.Binding);
                                }
                                const auto port = makePartitionPort();
                                // if we already have a fixed rate output with the same outgoing rate,
                                // fuse the output streamsets to simplify the simulator.
                                for (const auto e : make_iterator_range(out_edges(partitionId, G))) {
                                    if (port == G[e]) {
                                        streamSet = target(e, G);
                                        assert (in_degree(streamSet, G) == 1);
                                        if (LLVM_UNLIKELY(blockSize != 0 && G[streamSet].BlockSize != blockSize)) {
                                            for (const auto f : make_iterator_range(out_edges(streamSet, G))) {
                                                const auto v = target(f, G);
                                                if (G[v].BlockSize == blockSize) {
                                                    streamSet = v;
                                                    assert (in_degree(streamSet, G) == 1);
                                                    goto fuse_existing_streamset;
                                                }
                                            }
                                            goto make_blocksize_node_for_existing_streamset;
                                        } else {
                                            goto fuse_existing_streamset;
                                        }
                                    }
                                }
                            }
                        }
                        streamSet = add_vertex(G);
                        add_edge(partitionId, streamSet, makePartitionPort(), G);
                        if (LLVM_UNLIKELY(blockSize != 0)) {
make_blocksize_node_for_existing_streamset:
                            assert (in_degree(streamSet, G) == 1);
                            const auto blockSizeNode = add_vertex(blockSize, G);
                            add_edge(streamSet, blockSizeNode, PartitionPort{RateId::Fixed, blockSize, blockSize, 0, 0, 0}, G);
                            streamSet = blockSizeNode;
                        }
fuse_existing_streamset:
                        assert (in_degree(streamSet, G) == 1);
                        streamSetMap.emplace(std::make_pair(portNode.StreamSet, streamSet));
                    }
equivalent_port_exists:
                    assert (streamSetMap.find(portNode.StreamSet) != streamSetMap.end());
                    continue;
                }
                ordering.clear();

            }
        }
    }

    if (LLVM_UNLIKELY(num_edges(G) == 0)) {
        return;
    }


    // Normalize purely fixed-rate streamset I/O rates by their GCD. Do not alter
    // ports if they are adjacent to a blocksize node.

    const auto nodeCount = num_vertices(G);

    for (auto u = numOfPartitions; u < nodeCount; ++u) {
        if (G[u].BlockSize == 0) {
            auto canNormalizePort = [&](const Graph::edge_descriptor e, const unsigned t) {
                const PartitionPort & p = G[e];
                return (p.Type == RateId::Fixed) && (p.Delay == 0) && t < numOfPartitions;
            };

            const auto input = in_edge(u, G);
            if (canNormalizePort(input, source(input, G))) {
                bool normalize = true;
                for (const auto output : make_iterator_range(out_edges(u, G))) {
                    if (!canNormalizePort(output, target(output, G))) {
                        normalize = false;
                        break;
                    }
                }
                if (normalize) {
                    PartitionPort & I = G[input];
                    auto gcd = I.LowerBound;
                    for (const auto output : make_iterator_range(out_edges(u, G))) {
                        gcd = boost::gcd(gcd, G[output].LowerBound);
                    }
                    assert (I.LowerBound == I.UpperBound);
                    I.LowerBound /= gcd;
                    I.UpperBound = I.LowerBound;
                    for (const auto output : make_iterator_range(out_edges(u, G))) {
                        auto & O = G[output];
                        assert (O.LowerBound == O.UpperBound);
                        O.LowerBound /= gcd;
                        O.UpperBound = O.LowerBound;
                    }
                }
            }
        }
    }

    // Contract out any duplicate streamsets revealed by the GCD normalization
    for (auto u = 0UL; u < numOfPartitions; ++u) {
        Graph::out_edge_iterator ei, ei_end;
restart:
        std::tie(ei, ei_end) = out_edges(u, G);
        for (; ei != ei_end; ++ei) {
            const PartitionPort & O = G[*ei];
            if (O.Type == RateId::Fixed) {
                for (auto ej = ei; ++ej != ei_end; ) {
                    if (O == G[*ej]) { // if output rates match
                        const auto a = target(*ei, G);
                        assert (a >= numOfPartitions);
                        const auto b = target(*ej, G);
                        assert (b >= numOfPartitions);
                        Graph::out_edge_iterator eb, eb_end;
                        std::tie(eb, eb_end) = out_edges(b, G);
                        for (; eb != eb_end; ++eb) {
                            const auto v = target(*eb, G);
                            bool toAdd = true;
                            Graph::out_edge_iterator ea, ea_end;
                            std::tie(ea, ea_end) = out_edges(a, G);
                            for (; ea != ea_end; ++ea) {
                                const auto w = target(*ea, G);
                                if (v == w && G[*ea] == G[*eb]) {
                                    toAdd = false;
                                    break;
                                }
                            }
                            if (toAdd) {
                                add_edge(a, v, G[*eb], G);
                            }
                        }
                        clear_vertex(b, G);
                        goto restart;
                    }
                }
            }
        }
    }

    // Any streamset with exactly one fixed-rate input and output fixed-rate port
    // whose rates are identical can be edge contracted. Because the GCD pass would
    // normalize such rates, we know that they will both be Fixed(1) in this case.

    for (auto u = numOfPartitions; u < nodeCount; ++u) {
        assert (in_degree(u, G) <= 1);
        if (G[u].BlockSize == 0 && out_degree(u, G) == 1 && in_degree(u, G) == 1) {
            const auto output = in_edge(u, G);
            const PartitionPort & O = G[output];
            if (O.Type == RateId::Fixed && O.LowerBound == 1) {
                const auto input = out_edge(u, G);
                const PartitionPort & I = G[input];
                if (I.Type == RateId::Fixed && I.LowerBound == 1) {
                    clear_vertex(u, G);
                    const auto s = source(output, G);
                    const auto t = target(input, G);
                    assert (s != t);
                    add_edge(s, t, PartitionPort{RateId::Fixed, 1, 1, 0, 0, 0}, G);
                }
            }
        }
    }

    // TODO: we could apply transitive-reduction-like pass to fixed rates to further
    // simplify the graph

#ifdef PRINT_SIMULATION_DEBUG_STATISTICS

    BEGIN_SCOPED_REGION

    auto & out = errs();

    std::array<char, RateId::__Count> C;
    C[RateId::Fixed] = 'F';
    C[RateId::PopCount] = 'P';
    C[RateId::NegatedPopCount] = 'N';
    C[RateId::PartialSum] = 'S';
    C[RateId::Relative] = 'R';
    C[RateId::Bounded] = 'B';
    C[RateId::Greedy] = 'G';
    C[RateId::Unknown] = 'U';

    out << "digraph \"G\" {\n";
    for (auto v : make_iterator_range(vertices(G))) {
        out << "v" << v;
        if (v < numOfPartitions) {
            out << " [shape=\"box\",label=\"" << v << "\"]";
        } else if (G[v].BlockSize) {
            assert (in_degree(v, G) == 1 && out_degree(v, G) == 1);
            out  << " [shape=\"box\",style=\"rounded\",label=\"" << G[v].BlockSize << "\"]";
        }
        out << ";\n";
    }

    for (const auto e : make_iterator_range(edges(G))) {
        const auto s = source(e, G);
        const auto t = target(e, G);
        out << "v" << s << " -> v" << t << " [label=\"";
        const PartitionPort & p = G[e];
        switch (p.Type) {
            case RateId::Fixed:
            case RateId::Greedy:
            case RateId::Unknown:
                out << C[p.Type] << p.LowerBound;
                break;
            case RateId::Relative:
                out << C[RateId::Relative];
                break;
            case RateId::Bounded:
                out << C[RateId::Bounded] << p.LowerBound << '-' << p.UpperBound;
                break;
            case RateId::PartialSum:
                BEGIN_SCOPED_REGION
                out << C[RateId::PartialSum];
                const auto f = partialSumMap.find(p.Reference);
                assert (f != partialSumMap.end());
                PartialSumData & data = f->second;
                out << data.StepSize << "x" << data.GCD;
                END_SCOPED_REGION
                break;
            default:
                llvm_unreachable("unknown processing rate");
        }
        if (p.Reference) {
            out << " ref=" << p.Reference;
        }
        if (p.Delay) {
            out << " delay=" << p.Delay;
        }
        out << "\"];\n";
    }


    out << "}\n\n";
    out.flush();

    END_SCOPED_REGION
#endif

    assert (ordering.empty());
    ordering.reserve(nodeCount);
    topological_sort(G, std::back_inserter(ordering)); // reverse topological ordering
    assert (ordering.size() == nodeCount);

    size_t maxInDegree = 0;

    unsigned m = 0;
    for (unsigned i = 0; i < nodeCount; ++i) {
        const auto u = ordering[i];
        const auto in = in_degree(u, G);
        if (in != 0 || out_degree(u, G) != 0) {
            maxInDegree = std::max(maxInDegree, in);
            ordering[m++] = u;
        }
    }
    ordering.erase(ordering.begin() + m, ordering.end());

    flat_map<unsigned, PartialSumGenerator *> partialSumGeneratorMap;

    flat_map<Graph::edge_descriptor, SimulationPort *> portMap;

    std::vector<uint64_t> initialSumOfStrides(nodeCount);

    auto makePortNode = [&](const Graph::edge_descriptor e, length_t * const pendingArray, SimulationAllocator & allocator) {
        PartitionPort & p = G[e];
        SimulationPort * port = nullptr;
        switch (p.Type) {
            case RateId::Fixed:
                port = new (allocator) FixedPort(p.LowerBound);
                break;
            case RateId::Bounded:
                port = new (allocator) UniformBoundedPort(p.LowerBound, p.UpperBound);
                break;
            case RateId::PartialSum:
                BEGIN_SCOPED_REGION
                const auto f = partialSumMap.find(p.Reference);
                assert (f != partialSumMap.end());
                PartialSumData & data = f->second;
                const auto g = partialSumGeneratorMap.find(p.Reference);
                PartialSumGenerator * gen = nullptr;
                if (LLVM_LIKELY(g == partialSumGeneratorMap.end())) {
                    assert (Relationships[p.Reference].Type == RelationshipNode::IsRelationship);
                    assert ((data.RequiredCapacity % data.GCD) == 0);
                    gen = new (allocator) UniformDistributionPartialSumGenerator(
                                data.Count, data.StepSize * data.GCD, data.RequiredCapacity / data.GCD, allocator);
                    gen->initializeGenerator(rng);
                    partialSumGeneratorMap.emplace(p.Reference, gen);
                } else {
                    gen = g->second;
                }
                assert (data.Count > 0);
                const auto userId = data.Index++;
                assert (userId < data.Count);
                const auto stepLength = p.MaxStepSize;
                assert (stepLength <= data.RequiredCapacity);
                assert ((stepLength % data.GCD) == 0);
                assert (stepLength >= data.GCD);
                port = new (allocator) PartialSumPort(*gen, userId, stepLength / data.GCD);
                END_SCOPED_REGION
                break;
            case kernel::ProcessingRate::Relative:
                port = new (allocator) RelativePort(pendingArray[p.Reference]);
                break;
            case kernel::ProcessingRate::Greedy:
                port = new (allocator) GreedyPort(p.LowerBound);
                break;
            default:
                llvm_unreachable("unhandled processing rate");
        }
        port->reset(p.Delay);
        assert (portMap.count(e) == 0);
        portMap.emplace(std::make_pair(e, port));
        p.PortObject = port;
        return port;
    };

    SimulationAllocator allocator;

    SimulationNode ** const nodes = allocator.allocate<SimulationNode *>(nodeCount);

    length_t * const pendingArray = allocator.allocate<length_t>(maxInDegree);

    #ifdef NDEBUG
    for (unsigned i = 0; i < nodeCount; ++i) {
        nodes[i] = nullptr;
    }
    #endif

    std::vector<unsigned> actorNodes;
    actorNodes.reserve(m);

    for (unsigned i = 0; i != m; ++i) {

        const auto u = ordering[m - i - 1]; // forward topological ordering
        const auto inputs = in_degree(u, G);
        const auto outputs = out_degree(u, G);
        assert (inputs != 0 || outputs != 0);

        SimulationNode * sn = nullptr;
        if (u < numOfPartitions) {
            if (inputs == 0) {
                sn = new (allocator) SimulationSourceActor(outputs, allocator);
            } else if (outputs == 0) {
                sn = new (allocator) SimulationSinkActor(inputs, allocator);
            } else {
                sn = new (allocator) SimulationActor(inputs, outputs, allocator);
            }
            actorNodes.push_back(u);
        } else if (G[u].BlockSize) {
            assert (inputs == 1 && outputs == 1);
            sn = new (allocator) BlockSizeActor(G[u].BlockSize, allocator);
        } else {
            assert (inputs == 1 && outputs > 0);
            sn = new (allocator) SimulationFork(inputs, outputs, allocator);
        }
        nodes[i] = sn;
        BEGIN_SCOPED_REGION
        unsigned inputIdx = 0;
        for (const auto e : make_iterator_range(in_edges(u, G))) {
            assert (inputIdx < inputs);
            const auto f = portMap.find(e);
            assert (f != portMap.end());
            sn->Input[inputIdx++] = f->second;
        }
        assert (inputIdx == inputs);
        END_SCOPED_REGION

        BEGIN_SCOPED_REGION
        unsigned outputIdx = 0;
        for (const auto e : make_iterator_range(out_edges(u, G))) {
            assert (outputIdx < outputs);
            sn->Output[outputIdx++] = makePortNode(e, pendingArray, allocator);
        }
        assert (outputIdx == outputs);
        END_SCOPED_REGION
    }

    assert (actorNodes.size() <= m);

    // run the simulation

    // TODO: run this for K seconds instead of a fixed number of iterations

    for (uint64_t r = 0; r < DEMAND_ITERATIONS; ++r) {
        for (auto i = m; i--; ) { // reverse topological ordering
            nodes[i]->demand(pendingArray, rng);
        }
    }

    // Now calculate the expected dataflow from the simulation. since it is up
    // to the user/programmer to decide what the base segment length is, we
    // normalize the number of strides based on the (smallest) segment length
    // of the program's source kernel(s)

    // At run-time, we execute using a "data-driven" process since estimating
    // demands of future kernels is imprecise and costly at best and impossible
    // at worst so the source kernels will always execute a fixed number of
    // strides.

    // We cannot assume that we'll require only one stride here. For example,
    // ztf-phrase-hash processes 1 MB segments but MMap might supply only 4KB
    // per stride.

    // Instead we want the output rates of every source to satisfy the input
    // demands of their immediate consumers.


    // TODO: right now, we silently drop the stddev from the inputs but we could
    // instead use what we've learned from the initial run as segment length
    // bounds to limit the exploration space of a GA and deduce what might
    // lead to the most thread-balanced program. The problem of course here
    // would be time as the GA approach would require many magnitutes more time
    // to complete than a single simulation run.



    // TODO: If the output is supposed to be sparse, I don't want the input to be scaled so
    // high that it always satisfies the output but would want it to do so if the output
    // is expected to be dense. Should the output kernels actually be marked as to
    // their expected output? We could infer it ports were marked to indicate expected
    // transfer rates.

    for (unsigned i = 0; i < m; ++i) {
        const auto u = ordering[m - i - 1]; // forward topological ordering
        if (u < numOfPartitions) {
            if (in_degree(u, G) == 0) {
                SimulationSourceActor * const A = reinterpret_cast<SimulationSourceActor *>(nodes[i]);
                Rational X{A->SumOfStrides, DEMAND_ITERATIONS};
                const auto strides = (X.numerator() + (X.denominator() / 2)) / X.denominator();
                assert (strides > 0);
                A->RequiredIterations = strides;
            }
        }
        nodes[i]->reset();
    }

    for (const auto e : make_iterator_range(edges(G))) {
        const PartitionPort & p = G[e];
        p.PortObject->reset(p.Delay);
    }

    // Rerun this process in a pure data-driven mode once using the segment length
    // information gathered from the demand-driven execution. It is unclear how we
    // can correctly handle the standard deviation for the source kernels at run-time.

    using LinkingGraph = adjacency_list<vecS, vecS, undirectedS, no_property, Rational>;

    const auto numOfActors = actorNodes.size();

    uint64_t * const strideHistory = allocator.allocate<uint64_t>(numOfActors);

    LinkingGraph L(numOfActors);

    BEGIN_SCOPED_REGION
    uint64_t * current = strideHistory;
    for (unsigned i = 0; i < m; ++i) { // forward topological ordering
        assert (current >= strideHistory);
        assert ((current - strideHistory) < numOfActors);
        nodes[i]->fire(pendingArray, rng, current);
    }
    assert (current >= strideHistory);
    assert ((current - strideHistory) == numOfActors);
    // if at every timestep, the number of strides that two partition nodes execute
    // are aligned (i.e., identical or one is a constant multiple of the other)
    // then these partitions are linked with at least 1.0 - 1/(2^n) probability
    for (unsigned j = 1; j < numOfActors; ++j) {
        if (strideHistory[j]) {
            for (unsigned i = 0; i != j; ++i) {
                if (strideHistory[i]) {
                    Rational r(strideHistory[i], strideHistory[j]);
                    // We want an integer (or reciprocal thereof) relationship between
                    // the actors to avoid scenarios in which fusing both partitions
                    // would require executing a large number of strides.
                    if (r.numerator() == 1 || r.denominator() == 1) {
                        add_edge(i, j, r, L);
                    }
                }
            }
        }
    }
    END_SCOPED_REGION

    for (uint64_t r = 1; r < DATA_ITERATIONS; ++r) { // numOfActors +
        uint64_t * current = strideHistory;
        for (unsigned i = 0; i < m; ++i) { // forward topological ordering
            assert (current >= strideHistory);
            assert ((current - strideHistory) < numOfActors);
            nodes[i]->fire(pendingArray, rng, current);
        }
        assert (current >= strideHistory);
        assert ((current - strideHistory) == numOfActors);
        // update the linked partition graph; we expect this graph
        // to be very sparse after a few iterations and likely not
        // change afterwards.
        remove_edge_if([&](const LinkingGraph::edge_descriptor e) {
            const auto i = source(e, L);
            const auto a = strideHistory[i];
            const auto j = target(e, L);
            const auto b = strideHistory[j];
            assert (i < j);
            return (b == 0) || Rational{a, b} != L[e];
        }, L);
    }

#if 0
    // In the final pass, we want to iteratively attempt to break any
    // partition links that might have arisen from a high production
    // probability

    for (uint64_t r = 0; r < numOfActors; ++r) {
        uint64_t * current = strideHistory;
        for (unsigned i = 0; i < m; ++i) { // forward topological ordering
            assert (current >= strideHistory);
            assert ((current - strideHistory) < numOfActors);
            if (i == actorNodes[r]) {
                nodes[i]->fire_produce_zero_if_not_fixed(pendingArray, rng, current);
            } else {
                nodes[i]->fire(pendingArray, rng, current);
            }
        }
        assert (current >= strideHistory);
        assert ((current - strideHistory) == numOfActors);
        // update the linked partition graph; we expect this graph
        // to be very sparse after a few iterations and likely not
        // change afterwards.
        remove_edge_if([&](const LinkingGraph::edge_descriptor e) {
            const auto i = source(e, L);
            const auto a = strideHistory[i];
            const auto j = target(e, L);
            const auto b = strideHistory[j];
            assert (i < j);
            return (b == 0) || Rational{a, b} != L[e];
        }, L);
    }
#endif

    // We could have a scenario in which a kernel has only greedy inputs that
    // consumes data from one that produces it at a variable rate which in turn
    // consumes it from a purely fixed rate source. This could lead the system
    // to wrongly conclude both the source and "greedy" kernel is linked despite
    // having an interleaving kernel that violates this contract.

    // Since reasoning about that later can only lead to a worse solution for
    // the max. clique identification, cut such violations from the graph here.

    std::vector<unsigned> component(numOfActors);
    const auto numOfComponents = connected_components(L, component.data());

    std::vector<unsigned> componentInG(nodeCount, -1U);
    for (unsigned i = 0; i < numOfActors; ++i) {
        const auto j = actorNodes[i];
        assert (j < m);
        componentInG[j] = component[i];
    }

    dynamic_bitset<size_t> visited(nodeCount);

    remove_edge_if([&](const LinkingGraph::edge_descriptor e) {
        // all paths between these vertices in G must belong to the same
        // connected component in L
        assert (source(e, L) < target(e, L));
        const auto s = actorNodes[source(e, L)];
        const auto t = actorNodes[target(e, L)];
        assert (s < t);
        const auto c = componentInG[s];
        assert (c != -1U);
        assert (c == component[source(e, L)]);
        assert (c == componentInG[t]);
        assert (c == component[target(e, L)]);
        // init the new dfs search
        visited.reset();
        visited.set(t);
        std::function<bool(Graph::vertex_descriptor)> not_all_paths = [&](const Graph::vertex_descriptor u) {
            for (const auto f : make_iterator_range(out_edges(u, G))) {
                const auto v = target(f, G);
                if (visited.test(v)) { // we've found or gone past our target
                    return false;
                }
                const auto x = componentInG[v];
                assert (x < numOfComponents || x == -1U);
                if ((x != c && x != -1U) || not_all_paths(v)) {
                    return true;
                }
                // visited.set(v);
            }
            return false;
        };
        return not_all_paths(s);
    }, L);

    // Now identify all of the max. cliques. We want to ensure that we only
    // link partitions that will not force the system to wait for large
    // amounts of data. E.g., if one partition happens to execute one stride per
    // timestep, it could be aligned with every fixed-rate partition but
    // those partitions might have stride rates that do not have an integer
    // relationship between them.

    unsigned numOfLinkedGroups = 0;

    struct MarkLinkedPartitionsFunctor {
        using VertexSet = std::deque<LinkingGraph::vertex_descriptor>;
        void clique(const VertexSet & V, const LinkingGraph &) {
            const auto id = ++numOfLinkedGroups;
            for (const auto v : V) {
                assert (v < M.size());
                const auto p = M[v];
                assert (p < num_vertices(P));
                assert (P[p].LinkedGroupId == 0);
                P[p].LinkedGroupId = id;
            }
        }
        MarkLinkedPartitionsFunctor(PartitionGraph & P, const std::vector<unsigned> & M, unsigned & numOfLinkedGroups)
        : P(P), M(M), numOfLinkedGroups(numOfLinkedGroups) {}
        PartitionGraph & P;
        const std::vector<unsigned> & M;
        unsigned & numOfLinkedGroups;
    };

    // NOTE: ugly workaround here. this algorithm copies the functor at each recursion
    // level, leading to an incorrect notion of state. Even when I try forcing the
    // template type to be a reference type, this gets stripped away. To maintain the
    // state and minimize the copy cost, we make everything in the functor a reference.

    bron_kerbosch_all_cliques(L, MarkLinkedPartitionsFunctor{P, actorNodes, numOfLinkedGroups}, 1);

    for (unsigned i = 0; i < m; ++i) {
        const auto u = ordering[m - i - 1];
        assert (in_degree(u, G) != 0 || out_degree(u, G) != 0);
        if (u < numOfPartitions) {
            const SimulationActor * const A =
                reinterpret_cast<SimulationActor *>(nodes[i]);
            const uint64_t SQS = A->SumOfStrides;
            const uint64_t SSQ = A->SumOfStridesSquared;

            Rational expected{SQS, DATA_ITERATIONS};
            Rational cov;

            if (LLVM_UNLIKELY(in_degree(u, G) == 0 || SQS == 0)) {
                cov = Rational{0};
            } else {
                const uint64_t a = (DATA_ITERATIONS * SSQ);
                const uint64_t b = (SQS * SQS);
                assert (a >= b);
                // We don't need the stddev to be too precise but do want a rational number
                // to simplify the rest of the system. We use Newton's method but initially
                // scale the value by 100^2 to get 2 digits of precision.
                uint64_t val = (a - b) * 10000UL;
                if (LLVM_LIKELY(val > 1)) {
                    auto a = 1UL << (floor_log2(val) / 2UL); // <- approximates sqrt(val)
                    auto b = val;
                    // while (std::max(a, b) - std::min(a, b)) > 1
                    while (((a < b) ? (b - a) : (a - b)) > 1) {
                        b = val / a;
                        a = (a + b) / 2;
                    }
                    val = a; // a ought to equal ceil(sqrt(val) * 100)
                }
                // (val / (Iterations * 100L)) / (SQS / Iterations)
                cov = Rational{val, SQS * 100UL};
            }

            PartitionData & D = P[u];
            D.ExpectedStridesPerSegment = expected;
            D.StridesPerSegmentCoV = cov;

            #ifdef PRINT_SIMULATION_DEBUG_STATISTICS
            errs() << u << ":\tmean="
                   << expected.numerator() << "/" << expected.denominator()
                   << ",cov="
                   << cov.numerator() << "/" << cov.denominator()
                   << ",linkId=" << D.LinkedGroupId
                   << "\n";
            #endif

            assert (D.LinkedGroupId != 0);
        }
    }
}

}

#endif // VARIABLE_RATE_ANALYSIS_HPP

#endif
