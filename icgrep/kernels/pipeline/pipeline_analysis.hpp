#include "pipeline_compiler.hpp"
#include "lexographic_ordering.hpp"
#include <boost/graph/topological_sort.hpp>
#include <util/extended_boost_graph_containers.h>

namespace kernel {

// TODO: support call bindings that produce output that are inputs of
// other call bindings or become scalar outputs of the pipeline

// TODO: with a better model of stride rates, we could determine whether
// being unable to execute a kernel implies we won't be able to execute
// another and "skip" over the unnecessary kernels.

#if 1

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief printBufferGraph
 ** ------------------------------------------------------------------------------------------------------------- */
template <typename Graph>
void printGraph(const Graph & G, raw_ostream & out) {

    out << "digraph G {\n";
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

#endif

namespace {

    using ScalarDependencyMap = RelationshipMap<ScalarDependencyGraph::vertex_descriptor>;

    void enumerateScalarProducerBindings(const unsigned producerVertex, const Bindings & bindings,
                                         ScalarDependencyGraph & G, ScalarDependencyMap & M) {
        const auto n = bindings.size();
        for (unsigned i = 0; i < n; ++i) {
            const Relationship * const rel = getRelationship(bindings[i]);
            assert (M.count(rel) == 0);
            const auto bufferVertex = add_vertex(nullptr, G);
            add_edge(producerVertex, bufferVertex, i, G);
            M.emplace(rel, bufferVertex);
        }
    }

    ScalarDependencyGraph::vertex_descriptor makeIfConstant(const Relationship * const rel,
                                                            ScalarDependencyGraph & G, ScalarDependencyMap & M) {
        const auto f = M.find(rel);
        if (LLVM_LIKELY(f != M.end())) {
            return f->second;
        } else if (LLVM_LIKELY(isa<ScalarConstant>(rel))) {
            const auto bufferVertex = add_vertex(cast<ScalarConstant>(rel)->value(), G);
            M.emplace(rel, bufferVertex);
            return bufferVertex;
        } else {
            report_fatal_error("unknown scalar value");
        }
    }

    template <typename Array>
    void enumerateScalarConsumerBindings(const unsigned consumerVertex, const Array & array,
                                         ScalarDependencyGraph & G, ScalarDependencyMap & M) {
        const auto n = array.size();
        for (unsigned i = 0; i < n; ++i) {
            const auto bufferVertex = makeIfConstant(getRelationship(array[i]), G, M);
            assert (bufferVertex < num_vertices(G));
            add_edge(bufferVertex, consumerVertex, i, G);
        }
    }

} // end of anonymous namespace

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief makeScalarDependencyGraph
 *
 * producer -> buffer/scalar -> consumer
 ** ------------------------------------------------------------------------------------------------------------- */
ScalarDependencyGraph PipelineCompiler::makeScalarDependencyGraph() const {

    const auto pipelineInput = 0;
    const auto pipelineOutput = mLastKernel;
    const auto & call = mPipelineKernel->getCallBindings();
    const auto numOfCalls = call.size();
    const auto firstCall = mLastKernel + 1;
    const auto initialSize = firstCall + numOfCalls;

    ScalarDependencyGraph G(initialSize);
    ScalarDependencyMap M;

    enumerateScalarProducerBindings(pipelineInput, mPipelineKernel->getInputScalarBindings(), G, M);
    // verify each scalar input of the kernel is an input to the pipeline
    for (unsigned i = mFirstKernel; i < mLastKernel; ++i) {
        enumerateScalarConsumerBindings(i, mPipeline[i]->getInputScalarBindings(), G, M);
    }
    // enumerate the output scalars
    for (unsigned i = mFirstKernel; i < mLastKernel; ++i) {
        enumerateScalarProducerBindings(i, mPipeline[i]->getOutputScalarBindings(), G, M);
    }
    // enumerate the call bindings
    for (unsigned i = 0; i < numOfCalls; ++i) {
        enumerateScalarConsumerBindings(firstCall + i, call[i].Args, G, M);
    }
    // enumerate the pipeline outputs
    enumerateScalarConsumerBindings(pipelineOutput, mPipelineKernel->getOutputScalarBindings(), G, M);

    return G;
}

namespace {

    template <typename Graph, typename Vertex = typename graph_traits<Graph>::vertex_descriptor>
    bool add_edge_if_no_induced_cycle(const Vertex s, const Vertex t, Graph & G) {
        // If s-t exists, skip adding this edge
        if (edge(s, t, G).second) {
            return true;
        }
        // If G is a DAG and there is a t-s path, adding s-t will induce a cycle.
        const auto d = in_degree(s, G);
        if (d != 0) {
            flat_set<Vertex> V;
            V.reserve(num_vertices(G) - 2);
            std::queue<Vertex> Q;
            // do a BFS to search for a t-s path
            Q.push(t);
            for (;;) {
                const auto u = Q.front();
                Q.pop();
                for (auto e : make_iterator_range(out_edges(u, G))) {
                    const auto v = target(e, G);
                    if (LLVM_UNLIKELY(v == s)) {
                        // we found a t-s path
                        return false;
                    }
                    assert ("G was not initially acyclic!" && v != s);
                    if (LLVM_LIKELY(V.insert(v).second)) {
                        Q.push(v);
                    }
                }
                if (Q.empty()) {
                    break;
                }
            }
        }
        add_edge(s, t, G);
        return true;
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief makePortDependencyGraph
 *
 * Returns a lexographically sorted list of ports s.t. the inputs will be ordered as close as possible (baring
 * any constraints) to the kernel's original I/O ordering.
 ** ------------------------------------------------------------------------------------------------------------- */
std::vector<unsigned> PipelineCompiler::lexicalOrderingOfStreamIO() const {

    using Graph = adjacency_list<hash_setS, vecS, bidirectionalS>;

    const auto pipelineInput = 0;
    const auto pipelineOutput = mLastKernel;

    const auto numOfInputs = mKernel->getNumOfStreamInputs();
    const auto numOfOutputs = mKernel->getNumOfStreamOutputs();
    const auto firstOutput = numOfInputs;
    const auto numOfPorts = numOfInputs + numOfOutputs;

    Graph G(numOfPorts);

    // enumerate the input relations
    for (unsigned i = 0; i < numOfInputs; ++i) {
        const Binding & input = mKernel->getInputStreamSetBinding(i);
        const ProcessingRate & rate = input.getRate();
        if (rate.hasReference()) {
            Port port; unsigned j;
            std::tie(port, j) = mKernel->getStreamPort(rate.getReference());
            assert ("input stream cannot refer to an output stream" && port == Port::Input);
            add_edge(j, i, G);
        }
    }
    // and then enumerate the output relations
    for (unsigned i = 0; i < numOfOutputs; ++i) {
        const Binding & output = mKernel->getOutputStreamSetBinding(i);
        const ProcessingRate & rate = output.getRate();
        if (rate.hasReference()) {
            Port port; unsigned j;
            std::tie(port, j) = mKernel->getStreamPort(rate.getReference());
            add_edge(j + ((port == Port::Output) ? numOfInputs : 0), (i + numOfInputs), G);
        }
    }
    // check any pipeline input first
    if (out_degree(pipelineInput, mBufferGraph)) {
        for (unsigned i = 0; i < numOfInputs; ++i) {
            const auto buffer = getInputBufferVertex(i);
            if (LLVM_UNLIKELY(parent(buffer, mBufferGraph) == pipelineInput)) {
                for (unsigned j = 0; j < i; ++j) {
                    add_edge_if_no_induced_cycle(i, j, G);
                }
                for (unsigned j = i + 1; j < numOfPorts; ++j) {
                    add_edge_if_no_induced_cycle(i, j, G);
                }
            }
        }
    }

    // ... and check any pipeline output first
    if (out_degree(pipelineInput, mBufferGraph)) {
        for (unsigned i = 0; i < numOfOutputs; ++i) {
            const auto buffer = getOutputBufferVertex(i);
            if (LLVM_UNLIKELY(has_child(buffer, pipelineOutput, mBufferGraph))) {
                const auto k = firstOutput + i;
                for (unsigned j = 0; j < k; ++j) {
                    add_edge_if_no_induced_cycle(k, j, G);
                }
                for (unsigned j = k + 1; j < numOfPorts; ++j) {
                    add_edge_if_no_induced_cycle(k, j, G);
                }
            }
        }
    }
    // check any dynamic buffer last
    std::vector<unsigned> D;
    D.reserve(numOfOutputs);
    for (unsigned i = 0; i < numOfOutputs; ++i) {
        if (LLVM_UNLIKELY(isa<DynamicBuffer>(getOutputBuffer(i)))) {
            D.push_back(i);
        }
    }

    for (const auto i : D) {
        for (unsigned j = 0; j < numOfInputs; ++j) {
            add_edge_if_no_induced_cycle(j, firstOutput + i, G);
        }
        auto Dj = D.begin();
        for (unsigned j = 0; j < numOfOutputs; ++j) {
            if (*Dj == j) {
                ++Dj;
            } else {
                add_edge_if_no_induced_cycle(firstOutput + j, firstOutput + i, G);
            }
        }
        assert (Dj == D.end());
    }

    // TODO: add additional constraints on input ports to indicate the ones
    // likely to have fewest number of strides?

    return lexicalOrdering(std::move(G), mKernel->getName() + " has cyclic port dependencies.");
}

namespace {

#if 0

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief minimumConsumed
 ** ------------------------------------------------------------------------------------------------------------- */
inline LLVM_READNONE RateValue minimumConsumed(const Kernel * const kernel, const Binding & binding) {
    if (LLVM_UNLIKELY(binding.hasAttribute(AttrId::Deferred))) {
        return RateValue{0};
    }
    return lowerBound(kernel, binding);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief maximumConsumed
 ** ------------------------------------------------------------------------------------------------------------- */
inline LLVM_READNONE RateValue maximumConsumed(const Kernel * const kernel, const Binding & binding) {
    auto ub = upperBound(kernel, binding);
    if (binding.hasLookahead()) {
        ub += binding.getLookahead();
    }
    return ub;
}

#endif

}
/** ------------------------------------------------------------------------------------------------------------- *
 * @brief makeConsumerGraph
 *
 * Copy the buffer graph but amalgamate any multi-edges into a single one
 ** ------------------------------------------------------------------------------------------------------------- */
ConsumerGraph PipelineCompiler::makeConsumerGraph()  const {

    const auto firstBuffer = mLastKernel + 1;
    const auto lastBuffer = num_vertices(mBufferGraph);
    ConsumerGraph G(lastBuffer);

#if 0

    #warning TODO: ConsumerGraph assumes the dataflow is transitively bounded by the same initial source

    #warning REVISIT: ConsumerGraph is not optimal for handling relative rate inputs

    struct ConsumerData {
        unsigned Kernel{0};
        unsigned Port{0};
        RateValue Minimum{0};
        RateValue Maximum{0};

        inline bool operator < (const ConsumerData & other) const {
            return (Kernel < other.Kernel) || (Port < other.Port);
        }
    };

    std::vector<ConsumerData> consumers;
#endif

    for (auto bufferVertex = firstBuffer; bufferVertex < lastBuffer; ++bufferVertex) {

        const BufferNode & bn = mBufferGraph[bufferVertex];

        if (LLVM_UNLIKELY(bn.Type == BufferType::External)) {
            continue;
        }

        // copy the producing edge
        const auto pe = in_edge(bufferVertex, mBufferGraph);
        add_edge(source(pe, mBufferGraph), bufferVertex, mBufferGraph[pe].Port, G);

        for (const auto ce : make_iterator_range(out_edges(bufferVertex, mBufferGraph))) {
            add_edge(bufferVertex, target(ce, mBufferGraph), mBufferGraph[ce].Port, G);
        }

#if 0

        // collect the consumers of the i-th buffer
        consumers.clear();
        for (const auto e : make_iterator_range(out_edges(bufferVertex, mBufferGraph))) {
            ConsumerData cd;
            cd.Kernel = target(e, mBufferGraph);
            const BufferNode & bn = mBufferGraph[cd.Kernel];
            const BufferRateData & rd = mBufferGraph[e];
            cd.Port = rd.Port;
            const Kernel * const kernel = mPipeline[cd.Kernel];
            const Binding & input = kernel->getInputStreamSetBinding(cd.Port);
            if (LLVM_UNLIKELY(input.hasAttribute(AttrId::Deferred))) {
                cd.Minimum = RateValue{0};
            } else {
                cd.Minimum = bn.Lower * rd.Minimum;
            }
            cd.Maximum = bn.Upper * rd.Maximum;
            if (LLVM_UNLIKELY(input.hasLookahead())) {
                cd.Maximum += input.getLookahead();
            }
            consumers.emplace_back(cd);
        }

        // If the minimum input rate of the j-th consumer is greater than or equal to the maximum input
        // rate of the k-th consumer, we do not need to test the j-th consumer. This also ensures that
        // for each *FIXED* rate stream, keep only the minimum such rate. However, we may need to insert
        // a "fake" edge to mark the last consumer otherwise we'll set it too soon.

        // NOTE: here we need to consider the impact of lookahead on the use of a buffer since it may
        // limit how much work we can perform when nearing the end of the buffer.

        // TODO: this takes too narrow of a view of the problem. By considering a buffer's consumers
        // in isolation, it does not take into account that a particular kernel may be executed fewer
        // times than another because of I/O constraints independent of the buffer we're considering.
        // Essentially, to make this optimization safe we need to prove that if a consumer has performed
        // k strides, all other consumers performed k.

        if (LLVM_LIKELY(consumers.size() > 1)) {

            std::sort(consumers.begin(), consumers.end());

            const auto finalConsumer = consumers.back().first;

            for (auto j = consumers.begin() + 1; j != consumers.end(); ) {

                const ConsumerData & Cj = *j;
                for (auto k = consumers.begin(); k != j; ++k) {
                    const ConsumerData & Ck = *k;
                    if (LLVM_UNLIKELY(Cj.Minimum >= Ck.Maximum)) {
                        j = consumers.erase(j);
                        goto next;
                    }
                }

                for (auto k = j + 1; k != consumers.end(); ++k) {
                    const ConsumerData & Ck = *k;
                    if (LLVM_UNLIKELY(Cj.Minimum >= Ck.Maximum)) {
                        j = consumers.erase(j);
                        goto next;
                    }
                }

                ++j;
next:           continue;
            }
            if (LLVM_UNLIKELY(consumers.back().first != finalConsumer)) {
                consumers.emplace_back(finalConsumer, FAKE_CONSUMER);
            }
        }

        for (const auto & consumer : consumers) {
            add_edge(bufferVertex, consumer.first, consumer.second, G);
        }
#endif

    }

    return G;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief makeTerminationGraph
 *
 * The termination graph is a transitive reduction of I/O dependency graph. It models which kernels to be checked
 * to determine whether it is safe to terminate once it has finished processing its current input.
 ** ------------------------------------------------------------------------------------------------------------- */
TerminationGraph PipelineCompiler::makeTerminationGraph() const {

    // A pipeline will end for one or two reasons:

    // 1) no progress can be made by any kernel.

    // 2) all pipeline sinks have terminated (i.e., any kernel that writes
    // to a pipeline output, is marked as having a side-effect, or produces
    // an input for some call).

    using VertexVector = std::vector<TerminationGraph::vertex_descriptor>;

    const auto numOfCalls = mPipelineKernel->getCallBindings().size();
    const auto pipelineOutput = mLastKernel;
    const auto firstCall = pipelineOutput + 1;
    const auto lastCall = firstCall + numOfCalls;

    TerminationGraph G(pipelineOutput + 1);

    // copy and summarize producer -> consumer relations from the buffer graph
    for (unsigned i = mFirstKernel; i < mLastKernel; ++i) {
        for (auto buffer : make_iterator_range(out_edges(i, mBufferGraph))) {
            const auto bufferVertex = target(buffer, mBufferGraph);
            for (auto consumer : make_iterator_range(out_edges(bufferVertex, mBufferGraph))) {
                const auto j = target(consumer, mBufferGraph);
                add_edge(i, j, G);
            }
        }
    }

    // copy and summarize any output scalars of the pipeline or any calls
    for (unsigned i = pipelineOutput; i < lastCall; ++i) {
        for (auto relationship : make_iterator_range(in_edges(i, mScalarDependencyGraph))) {
            const auto relationshipVertex = source(relationship, mScalarDependencyGraph);
            for (auto producer : make_iterator_range(in_edges(relationshipVertex, mScalarDependencyGraph))) {
                const auto j = source(producer, mScalarDependencyGraph);
                add_edge(j, pipelineOutput, G);
            }
        }
    }

    // create a k_i -> P_out edge for every kernel with a side effect attribute
    for (unsigned i = mFirstKernel; i < mLastKernel; ++i) {
        if (LLVM_UNLIKELY(mPipeline[i]->hasAttribute(AttrId::SideEffecting))) {
            add_edge(i, pipelineOutput, G);
        }
    }

    // generate a transitive closure
    VertexVector ordering;
    ordering.reserve(num_vertices(G));
    topological_sort(G, std::back_inserter(ordering));

    for (unsigned u : ordering) {
        for (auto e : make_iterator_range(in_edges(u, G))) {
            const auto s = source(e, G);
            for (auto f : make_iterator_range(out_edges(u, G))) {
                add_edge(s, target(f, G), G);
            }
        }
    }

    // then take the transitive reduction
    VertexVector sources;
    for (unsigned u = pipelineOutput; u--; ) {
        for (auto e : make_iterator_range(in_edges(u, G))) {
            sources.push_back(source(e, G));
        }
        std::sort(sources.begin(), sources.end());
        for (auto e : make_iterator_range(out_edges(u, G))) {
            remove_in_edge_if(target(e, G), [&G, &sources](const TerminationGraph::edge_descriptor f) {
                return std::binary_search(sources.begin(), sources.end(), source(f, G));
            }, G);
        }
        sources.clear();
    }

    return G;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief makePopCountGraph
 *
 * Kernel -> Port -> Buffer ordering. Edge between a Kernel and a port indicates the port # of the source
 * items stream. Edges between a port and buffer state the ref port #. The kernel and buffer vertices are
 * aligned with the BufferGraph. Any buffer vertex with an in-degree > 0 is the reference of a pop count
 * rate stream.
 ** ------------------------------------------------------------------------------------------------------------- */
PopCountGraph PipelineCompiler::makePopCountGraph() const {

    using PopCountVertex = PopCountGraph::vertex_descriptor;
    using PortMapping = flat_map<unsigned, PopCountVertex>;

    PopCountGraph G(num_vertices(mBufferGraph));
    PortMapping M;

    auto addPopCountDependency = [&](
        const Kernel * const kernel,
        const PopCountVertex kernelVertex,
        const unsigned portIndex,
        const Binding & binding) {

        const ProcessingRate & rate = binding.getRate();
        if (LLVM_UNLIKELY(rate.isPopCount() || rate.isNegatedPopCount())) {
            // determine which port this I/O port refers to
            Port portType; unsigned refPort;
            std::tie(portType, refPort) = kernel->getStreamPort(rate.getReference());

            // verify the reference stream is an input port
            if (LLVM_UNLIKELY(portType != Port::Input)) {
                std::string tmp;
                raw_string_ostream msg(tmp);
                msg << kernel->getName();
                msg << ": pop count rate for ";
                msg << binding.getName();
                msg << " cannot refer to an output stream";
                report_fatal_error(msg.str());
            }

            const auto type = rate.isPopCount() ? CountingType::Positive : CountingType::Negative;

            // check if we've already created a vertex for the ref port ...
            const auto f = M.find(refPort);
            if (LLVM_UNLIKELY(f != M.end())) {
                const auto refPortVertex = f->second;
                add_edge(kernelVertex, refPortVertex, PopCountEdge{type, portIndex}, G);
                // update the ref -> buffer edge with the counting type
                for (const auto e : make_iterator_range(out_edges(refPortVertex, G))) {
                    G[e].Type |= type;
                }
            } else { // ... otherwise map a new vertex to it.

                // verify the reference stream is a Fixed rate stream
                const Binding & refBinding = kernel->getInputStreamSetBinding(refPort);
                if (LLVM_UNLIKELY(refBinding.isDeferred() || !refBinding.getRate().isFixed())) {
                    std::string tmp;
                    raw_string_ostream msg(tmp);
                    msg << kernel->getName();
                    msg << ": pop count reference ";
                    msg << refBinding.getName();
                    msg << " must be a non-deferred Fixed rate stream";
                    report_fatal_error(msg.str());
                }

                const auto refPortVertex = add_vertex(G);
                M.emplace(refPort, refPortVertex);
                add_edge(kernelVertex, refPortVertex, PopCountEdge{type, portIndex}, G);

                // determine which buffer this port refers to by inspecting the buffer graph
                const auto bufferVertex = getInputBufferVertex(kernelVertex, refPort);
                add_edge(refPortVertex, bufferVertex, PopCountEdge{type, refPort}, G);
            }
        }
    };

    for (unsigned i = mFirstKernel; i < mLastKernel; ++i) {
        const Kernel * const kernel = mPipeline[i];
        const auto numOfInputs = kernel->getNumOfStreamInputs();
        const auto numOfOutputs = kernel->getNumOfStreamOutputs();
        for (unsigned j = 0; j < numOfInputs; ++j) {
            const auto & input = kernel->getInputStreamSetBinding(j);
            addPopCountDependency(kernel, i, j, input);
        }
        const auto firstOutput = numOfInputs;
        for (unsigned j = 0; j < numOfOutputs; ++j) {
            const auto & output = kernel->getOutputStreamSetBinding(j);
            addPopCountDependency(kernel, i, firstOutput + j, output);
        }
        M.clear();
    }

    return G;
}


} // end of namespace
