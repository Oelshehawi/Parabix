#include "pipeline_analysis.hpp"
#include <boost/tokenizer.hpp>
#include <boost/format.hpp>

namespace kernel {

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief makeConsumerGraph
 *
 * Copy the buffer graph but amalgamate any multi-edges into a single one
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineAnalysis::makeConsumerGraph() {

    mConsumerGraph = ConsumerGraph(LastStreamSet + 1);

    for (auto streamSet = FirstStreamSet; streamSet <= LastStreamSet; ++streamSet) {
        // If we have no consumers, we do not want to update the consumer count on exit
        // as we would then have to retain a scalar for it. If this streamset is
        // returned to the outside environment, we cannot ever release data from it
        // even if it has an internal consumer.

        if (LLVM_UNLIKELY(out_degree(streamSet, mBufferGraph) == 0)) {
            continue;
        }

        const BufferNode & bn = mBufferGraph[streamSet];
        if (bn.Locality != BufferLocality::GloballyShared || bn.isReturned()) {
            continue;
        }



        // copy the producing edge
        const auto pe = in_edge(streamSet, mBufferGraph);
        const BufferPort & output = mBufferGraph[pe];
        const auto producer = source(pe, mBufferGraph);
        add_edge(producer, streamSet, ConsumerEdge{output.Port, 0, ConsumerEdge::None}, mConsumerGraph);

        const auto partitionId = KernelPartitionId[producer];

        // TODO: check gb18030. we can reduce the number of tests by knowing that kernel processes
        // the same amount of data so we only need to update this value after invoking the last one.

        auto lastConsumer = PipelineInput;

        unsigned index = 0;

        for (const auto ce : make_iterator_range(out_edges(streamSet, mBufferGraph))) {
            const auto consumer = target(ce, mBufferGraph);

            lastConsumer = std::max<unsigned>(lastConsumer, consumer);

            const auto consumerPartId = KernelPartitionId[consumer];
            if (consumerPartId != partitionId) {
                const BufferPort & input = mBufferGraph[ce];
                add_edge(streamSet, consumer, ConsumerEdge{input.Port, ++index, ConsumerEdge::UpdateConsumedCount}, mConsumerGraph);
            }
        }

        assert (lastConsumer != 0);

        const auto lastConsumerPartitionId = KernelPartitionId[lastConsumer];

        unsigned flags = ConsumerEdge::WriteConsumedCount;
        for (const auto ce : make_iterator_range(out_edges(streamSet, mConsumerGraph))) {
            const auto consumer = target(ce, mConsumerGraph);
            const auto jumpId = PartitionJumpTargetId[KernelPartitionId[consumer]];
            if (jumpId <= lastConsumerPartitionId) {
                flags |= ConsumerEdge::MayHaveJumpedConsumer;
                goto found_potentially_jumped_consumer;
            }
        }

found_potentially_jumped_consumer:

        // Although we may already know the final consumed item count prior
        // to executing the last consumer, we need to defer writing the final
        // consumed item count until the very last consumer reads the data.

        if (lastConsumer) {
            ConsumerGraph::edge_descriptor e;
            bool exists;
            std::tie(e, exists) = edge(streamSet, lastConsumer, mConsumerGraph);
            if (exists) {
                ConsumerEdge & cn = mConsumerGraph[e];
                cn.Flags |= flags;
            } else {
                add_edge(streamSet, lastConsumer, ConsumerEdge{output.Port, ++index, flags}, mConsumerGraph);
            }
        }
    }

    // If this is a pipeline input, we want to update the count at the end of the loop.
    for (const auto e : make_iterator_range(out_edges(PipelineInput, mBufferGraph))) {
        const auto streamSet = target(e, mBufferGraph);
        ConsumerGraph::edge_descriptor f;
        bool exists;
        std::tie(f, exists) = edge(streamSet, PipelineOutput, mConsumerGraph);
        const auto flags = ConsumerEdge::UpdateExternalCount;
        if (exists) {
            ConsumerEdge & cn = mConsumerGraph[f];
            cn.Flags |= flags;
        } else {
            const BufferPort & br = mBufferGraph[e];
            add_edge(streamSet, PipelineOutput, ConsumerEdge{br.Port, 0, flags}, mConsumerGraph);
        }
    }

#if 0

    auto & out = errs();

    out << "digraph \"ConsumerGraph\" {\n";
    for (auto v : make_iterator_range(vertices(mConsumerGraph))) {
        out << "v" << v << " [label=\"" << v << "\"];\n";
    }
    for (auto e : make_iterator_range(edges(mConsumerGraph))) {
        const auto s = source(e, mConsumerGraph);
        const auto t = target(e, mConsumerGraph);
        out << "v" << s << " -> v" << t <<
               " [label=\"";
        const ConsumerEdge & c = mConsumerGraph[e];
        if (c.Flags & ConsumerEdge::UpdatePhi) {
            out << 'U';
        }
        if (c.Flags & ConsumerEdge::WriteConsumedCount) {
            out << 'W';
        }
        if (c.Flags & ConsumerEdge::UpdateExternalCount) {
            out << 'E';
        }
        out << "\"];\n";
    }

    out << "}\n\n";
    out.flush();

#endif

}

}
