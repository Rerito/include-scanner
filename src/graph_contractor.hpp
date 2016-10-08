

#include <stdexcept>
#include <unordered_map>
#include <vector>
#include <stack>

#include <boost/range/iterator_range.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/depth_first_search.hpp>

/**
 * refiner_dfs_visitor - A DFS Visitor to contract a graph
 * Template parameters:
 * InputGraph - The type of the input graph
 * OutputGraph - The type of the output graph
 * VxPredicate - The functor type for the vertex predicate
 * 
 * Restrictions:
 * - The edge property for the output graph must have a push_back() method to add edges on the fly
 * - The vertex property for the output graph must be constructible from the vertex property of the input graph
 * - The predicate has two arguments: (vertex, graph) where vertex is constructible from an input graph vertex and graph from the input graph
 * 
 */
template <typename InputGraph, typename OutputGraph, typename VxPredicate>
struct refiner_dfs_visitor : boost::default_dfs_visitor {
    
    typedef typename boost::graph_traits<InputGraph>::vertex_descriptor input_vertex_t;
    typedef typename boost::graph_traits<InputGraph>::edge_descriptor input_edge_t;
    
    typedef typename boost::graph_traits<OutputGraph>::vertex_descriptor vertex_t;
    typedef typename boost::graph_traits<OutputGraph>::edge_descriptor edge_t;
    typedef typename std::remove_reference<decltype((std::declval<OutputGraph>())[std::declval<vertex_t>()])>::type vertex_property_t;
    typedef typename std::remove_reference<decltype((std::declval<OutputGraph>())[std::declval<edge_t>()])>::type edge_property_t;
    
    template <typename Predicate>
    refiner_dfs_visitor(OutputGraph& out_graph, Predicate&& predicate) : vx_predicate(std::forward<Predicate>(predicate)), out_graph(out_graph), path(), path_start(), vertex_mapping() {}
    
    /**
     * discover_vertex - Called whenever a vertex is examined
     * @vertex[in] The vertex being examined
     * @graph[in]  The graph the vertex belongs to
     *
     * This function is called only once per vertex. We add @vertex to the
     * @path. This way we keep track of the vertices we visited (like an
     * Ariane's thread).
     * Furthermore, if the vertex is marked (ie. vx_predicate(@vertex, @graph)
     * is true), then we add its position in @path on the top of @path_start.
     *
     */
    void discover_vertex(input_vertex_t const& vertex, InputGraph const& graph) {
        path.push_back(vertex);
        if (vx_predicate(vertex, graph)) {
            auto v = add_vertex(out_graph);
            out_graph[v] = graph[vertex];
            vertex_mapping.emplace(vertex, v);
            perform_edge_insertion(vertex, graph);
            path_start.push(path.cend() - path.cbegin() - 1);
        }
    }
    
    /**
     * finish_vertex - Called once we examined all the out-edge of a vertex.
     * @vertex[in] The vertex we finished focusing on
     * @graph[in]  The graph the vertex belongs to
     *
     * When we hit this function, it means we are about to step back in the
     * search. Thus we erase the last entry of the @path (which is @vertex).
     * Furthermore, if the vertex is marked, we must also remove the top element
     * of the stack.
     */
    void finish_vertex(input_vertex_t const& vertex, InputGraph const& graph) {
        if (vx_predicate(vertex, graph)) {
            path_start.pop();
        }
        path.pop_back();
    }
        
    /**
     * forward_or_cross_edge - Callback for forward or cross edges
     * @edge[in]  The edge being focused on
     * @graph[in] The graph to which the edge belongs
     *
     * A forward or cross edge (u,v) is an edge that goes from a vertex u to an already
     * discovered vertex v that is not an ancestor of u.
     *
     * If we find such an edge we must make sure to add the relevent edges in
     * the output graph
     */
    void forward_or_cross_edge(input_edge_t const& edge, InputGraph const& graph) {
        edge_callback_impl(edge, graph);
    }
    
    /** back_edge - Callback for back edges
     *
     * Same as @forward_or_cross_edge except that for a back edge (u, v), v is an ancestor of u.
     */
    void back_edge(input_edge_t const& edge, InputGraph const& graph) {
        edge_callback_impl(edge, graph);
    }
    
private:

    /**
     * build_edge_property
     *
     * @graph[in] Input graph
     *
     * Builds the edge property for the graph, represented by the current path.
     */
    edge_property_t build_edge_property(InputGraph const& graph) const {
        edge_property_t prop;
        if (path_start.empty()) {
            throw std::runtime_error("No path");
        }
        for (auto i = path_start.top(); i < path.size() - 1; ++i) {
            auto e_desc = edge(path[i], path[i+1], graph);
            if (e_desc.second) {
                prop.push_back(e_desc.first);
            } else {
                throw std::runtime_error("Shit mate");
            }
        }
        return prop;
    }
    
    bool perform_edge_insertion(input_edge_t const& source, InputGraph const& graph) {
        if (path_start.empty()) {
            return false;
        }
        
        auto tgt = target(source, graph);
        auto used_source = path[path_start.top()];
        
        try {
            auto prop = build_edge_property(graph);
            prop.push_back(source);
            if (vx_predicate(tgt, graph)) {
                add_edge_to_out_graph(vertex_mapping[used_source],
                        vertex_mapping[tgt], prop);
                update_crossroads(std::begin(prop)+1, std::end(prop), graph);
            } else {
                add_crossroad_edges_to_out_graph(used_source, tgt, graph, prop);
            }
            return true;
        } catch (std::runtime_error& e) {
            return false;
        }
    }
    
    bool perform_edge_insertion(input_vertex_t const& tgt, InputGraph const& graph) {
        if (path_start.empty()) {
            return false;
        }
        auto used_source = path[path_start.top()];
        
        try {
            auto prop = build_edge_property(graph);
            update_crossroads(std::begin(prop)+1, std::end(prop), graph);
            return add_edge_to_out_graph(vertex_mapping[used_source], vertex_mapping[tgt], prop);
        } catch (std::runtime_error& e) {
            return false;
        }    
    }
    
    bool edge_callback_impl(input_edge_t const& edge, InputGraph const& graph) {
        return perform_edge_insertion(edge, graph);
    }
    
    bool add_edge_to_out_graph(vertex_t const& src, vertex_t const& target, edge_property_t const& prop) {
        auto e = add_edge(src, target, out_graph);
        if (e.second) {
            out_graph[e.first] = prop;
        }
        return e.second;
    }

    /**
     * Crossroad handling:
     *
     * Sometimes we can end up in an already visited vertex which can lead to several marked vertices
     * When that happens, we must make sure we add the relevant edge from the current marked source to
     * all the crossroad marked destinations.
     * 
     * To that end, we use a multimap as a bookkeeper of each path from an unmarked vertex to an already discovered
     * marked vertex.
     */

    /**
     * update_crossroads - Update the crossroad map
     * @beg[in]   Begin Iterator for the edges to handle
     * @end[in]   End Iterator for the edges to handle
     * @graph[in] The input graph
     *
     * For any iterator e in the range [beg, end), this function adds the path [e, end) to the key source(*e, graph)
     * of the crossroad map
     */
    template <typename EdgeIterator>
    void update_crossroads(EdgeIterator beg, EdgeIterator end, InputGraph const& graph) {
        for (auto it = beg; it != end; ++it) {
            auto src = source(*it, graph);
            crossroad_map.emplace(src, std::vector<input_edge_t>(it, end));
        }
    }

    /**
     * add_crossroad_edges_to_out_graph
     * @src[in]          The source vertex (marked) we want to connect with @cross_src destinations.
     * @cross_src[in]    The crossroad vertex
     * @graph[in]        The input graph
     * @partial_prop[in] The prefilled property object, containing edges of the path from @src to @cross_src
     *
     * This function will examine the paths from @cross_src to any discovered marked vertex registered in @crossroad_map
     * For each such path, an edge will be added with a complete property object.
     */
    void add_crossroad_edges_to_out_graph(input_vertex_t const& src, input_vertex_t const& cross_src, InputGraph const& graph,
            edge_property_t const& partial_prop) {
        auto dest_range = crossroad_map.equal_range(cross_src);
        for (auto const& path_end : boost::make_iterator_range(dest_range)) {
            auto prop_full = partial_prop;
            auto const& cur_tgt = target(*(path_end.second.crbegin()), graph);
            for (auto const& e : path_end.second) {
                prop_full.push_back(e);
            }
            add_edge_to_out_graph(vertex_mapping[src],
                    vertex_mapping[cur_tgt], prop_full);
        }
    }
    
    VxPredicate vx_predicate;
    OutputGraph& out_graph;
    
    // Keeping track of the path
    std::vector<input_vertex_t> path;
    std::stack<std::size_t> path_start;
    std::unordered_multimap<input_vertex_t, std::vector<input_edge_t>> crossroad_map;
    std::unordered_map<input_vertex_t, vertex_t> vertex_mapping;
};
