// Port of org.semanticweb.HermiT.tableau.DescriptionGraphManager.
//
// HermiT keeps each description graph's tuples in its own N-ary extension table
// (arity `number_of_vertices + 1`, tuple `[graph, v0, v1, ...]`) that rides the
// tableau's delta-new propagation and dependency-directed backtracking exactly
// like the binary/ternary tables. Alongside, for every tableau node it tracks
// the list of places that node occurs in a graph tuple: each occurrence records
// the graph index, the tuple index, and the position within the tuple. These
// occurrence records are kept in a manually managed free-list of fixed-size
// records (a node's list threads through them via a `next` link), maintained by
// `descriptionGraphTupleAdded` / `descriptionGraphTupleRemoved` and walked by
// `checkGraphConstraints` / `mergeGraphs`.
//
// The Java `OccurrenceManager` pages a flat `int[]`; this port uses a single
// growable `Vec<i32>` with the same record layout and free-list semantics. The
// per-graph tables reuse the arity-generic `ExtensionTable`, so backtracking a
// branch correctly removes the graph tuples it created (and unlinks their
// occurrence records) rather than leaving them to be resurrected.
//
// The description-graph existential *expansion* (`expand`) -- creating the
// graph's vertex nodes, the per-vertex concept assertions and the per-edge role
// assertions -- is also ported here, on the binary/ternary tables for the
// concept/role assertions and the per-graph table for the graph tuple itself.
#![allow(dead_code)]

use rustc_hash::FxHashMap as HashMap;

use crate::model::{Concept, DescriptionGraph, ExistsDescriptionGraph, Role};
use crate::tableau::dependency_set::{
    DependencySet, DependencySetFactory, PermanentDependencySet, UnionDependencySet,
};
use crate::tableau::extension_table::{ExtensionTable, StoreOutcome, View};
use crate::tableau::node::NodeId;
use crate::tableau::object::TableauObject;
use crate::tableau::tableau::Tableau;

/// The graph-tuple bookkeeping of `DescriptionGraphManager`: the per-graph
/// N-ary extension tables and, via the `OccurrenceManager`, the constraint check
/// that keeps a description graph rigid -- if a node occurs in two tuples of the
/// same graph at the *same* position the tuples are merged componentwise, and at
/// *different* positions a clash is raised (`checkGraphConstraints`).
///
/// Each graph `g` has its own extension table of arity `g.number_of_vertices()+1`
/// holding tuples `[g, v0, v1, ...]` (the leading object is the graph itself, so
/// position `i+1` is HermiT's position for vertex `i`). These tables ride the
/// tableau's delta-new propagation and backtracking lifecycle exactly like the
/// binary/ternary tables, with `description_graph_tuple_added` /
/// `description_graph_tuple_removed` maintaining the occurrence lists.
pub struct DescriptionGraphManager {
    /// The description graphs, indexed by the same `graph_index` used everywhere
    /// (the port of `m_descriptionGraphsByIndex`).
    graphs: Vec<DescriptionGraph>,
    /// Maps a graph to its index (`m_descriptionGraphIndices`).
    graph_indices: HashMap<DescriptionGraph, usize>,
    /// The per-graph N-ary extension tables (`m_extensionTablesByIndex`), one per
    /// graph, of arity `number_of_vertices + 1`.
    tables: Vec<ExtensionTable>,
    occurrences: OccurrenceManager,
    occurrence_head: HashMap<NodeId, i32>,
}

impl Default for DescriptionGraphManager {
    /// An empty, no-op manager (an ontology without description graphs). Also the
    /// placeholder used by `std::mem::take` while the manager calls back into the
    /// tableau.
    fn default() -> Self {
        DescriptionGraphManager::new(&[], true)
    }
}

impl DescriptionGraphManager {
    /// Port of the `DescriptionGraphManager` constructor: builds the
    /// graph→index map and the per-graph N-ary extension tables from the
    /// ontology's description graphs. An empty slice (an ontology without
    /// description graphs) yields an empty, no-op manager.
    pub fn new(graphs: &[DescriptionGraph], needs_dependency_sets: bool) -> DescriptionGraphManager {
        let mut graph_indices = HashMap::default();
        let mut tables = Vec::with_capacity(graphs.len());
        for (index, graph) in graphs.iter().enumerate() {
            graph_indices.insert(graph.clone(), index);
            // Java builds an `ExtensionTableWithFullIndex(numberOfVertices+1, ...)`
            // with a `NoCoreManager` (isCore always true) per graph; here a single
            // full-tuple index over all columns plays the role of the full index.
            let arity = graph.number_of_vertices() + 1;
            let full_index: Vec<usize> = (0..arity).collect();
            tables.push(ExtensionTable::new(
                arity,
                needs_dependency_sets,
                vec![full_index],
                false,
            ));
        }
        DescriptionGraphManager {
            graphs: graphs.to_vec(),
            graph_indices,
            tables,
            occurrences: OccurrenceManager::new(),
            occurrence_head: HashMap::default(),
        }
    }

    /// Port of the lifecycle hooks the N-ary extension tables share with the
    /// binary/ternary tables. `propagate_delta_new` mirrors
    /// `ExtensionManager.propagateDeltaNew`, returning whether any table had a
    /// non-empty delta.
    pub fn propagate_delta_new(&mut self) -> bool {
        let mut any = false;
        for table in &mut self.tables {
            if table.propagate_delta_new() {
                any = true;
            }
        }
        any
    }

    /// `ExtensionTable.branchingPointPushed` for every graph table.
    pub fn branching_point_pushed(&mut self, level: usize) {
        for table in &mut self.tables {
            table.branching_point_pushed(level);
        }
    }

    /// `ExtensionTable.backtrack` for every graph table; each removed tuple fires
    /// `descriptionGraphTupleRemoved` (occurrence-list unlink), in the
    /// most-recent-first order `backtrack` returns.
    pub fn backtrack(&mut self, level: usize, factory: &mut DependencySetFactory) {
        for graph_index in 0..self.tables.len() {
            let removed = self.tables[graph_index].backtrack(level, factory);
            for (tuple, _is_core) in removed {
                self.description_graph_tuple_removed(&tuple);
            }
        }
    }

    /// Whether the manager carries any description graphs. Mirrors HermiT's
    /// `m_hasDescriptionGraphs` guard (`!getAllDescriptionGraphs().isEmpty()`):
    /// every hook is a no-op when this is `false`, so an ontology without
    /// description graphs behaves exactly as before.
    pub fn has_description_graphs(&self) -> bool {
        !self.graphs.is_empty()
    }

    fn graph_index(&self, graph: &DescriptionGraph) -> usize {
        self.graph_indices[graph]
    }

    /// Port of `DescriptionGraphManager.clear()` (DescriptionGraphManager.java:
    /// 87-102): resets the per-test work state -- the per-graph extension tables,
    /// the graph-occurrence manager, the per-node occurrence heads (Java's
    /// `m_newNodes`/aux tuples/`m_deltaOldRetrievals` are transient buffers, the
    /// extension tables are cleared via their owning `ExtensionManager` analogue).
    /// The graph definitions (`graphs`/`graph_indices`) are permanent
    /// (clause/ontology-derived) and are NOT reset, matching Java keeping
    /// `m_descriptionGraphsByIndex`/`m_extensionTablesByIndex` (structure) intact.
    pub fn clear(&mut self) {
        for table in &mut self.tables {
            table.clear();
        }
        self.occurrences.clear();
        self.occurrence_head.clear();
    }

    /// Port of `intializeNode`: a fresh node has no graph occurrences. The
    /// `occurrence_head` map omits an entry for a node with no occurrences (the
    /// `-1`/`m_firstGraphOccurrenceNode==-1` of the Java field), so this clears
    /// any stale entry from a reused node slot.
    pub fn initialize_node(&mut self, node: NodeId) {
        self.occurrence_head.remove(&node);
    }

    /// Port of `destroyNode`: walk the node's occurrence list returning every
    /// record to the free list, then drop the head (set it back to `-1`).
    pub fn destroy_node(&mut self, node: NodeId) {
        let mut list_node = *self.occurrence_head.get(&node).unwrap_or(&-1);
        while list_node != -1 {
            let next = self.occurrences.next_node(list_node as usize);
            self.occurrences.delete_list_node(list_node as usize);
            list_node = next;
        }
        self.occurrence_head.remove(&node);
    }

    /// Port of `isSatisfied`: the existential is satisfied iff `node` already
    /// occurs in a tuple of the existential's graph at the existential's vertex
    /// position (HermiT's `positionInTuple = vertex+1`, the leading graph label
    /// occupying position 0).
    pub fn is_satisfied(&self, exists: &ExistsDescriptionGraph, node: NodeId) -> bool {
        if self.graphs.is_empty() {
            return false;
        }
        let graph_index = self.graph_index(exists.get_description_graph()) as i32;
        let position = exists.get_vertex() + 1;
        let mut list_node = *self.occurrence_head.get(&node).unwrap_or(&-1);
        while list_node != -1 {
            if self.occurrences.graph_index(list_node as usize) == graph_index
                && self.occurrences.position_in_tuple(list_node as usize) == position
            {
                return true;
            }
            list_node = self.occurrences.next_node(list_node as usize);
        }
        false
    }

    /// Stores `tuple` (`[graph, v0, v1, ...]`) in the graph's extension table and,
    /// if newly added, registers each node's occurrence
    /// (`descriptionGraphTupleAdded`). An already-present tuple only upgrades its
    /// core flag, matching `ExtensionManager.addTuple`.
    fn add_tuple(
        &mut self,
        graph_index: usize,
        tuple: Vec<TableauObject>,
        dependency_set: PermanentDependencySet,
        is_core: bool,
        factory: &mut DependencySetFactory,
    ) {
        match self.tables[graph_index].store_tuple(&tuple, dependency_set, is_core, factory) {
            StoreOutcome::Added(tuple_index) => {
                self.description_graph_tuple_added(graph_index, tuple_index, &tuple);
            }
            StoreOutcome::AlreadyPresent(tuple_index) => {
                self.tables[graph_index].upgrade_core(tuple_index, is_core);
            }
        }
    }

    /// Port of `descriptionGraphTupleAdded`: push an occurrence record onto each
    /// node's list (positions `arity-1 ..= 1`, reverse, matching Java).
    fn description_graph_tuple_added(
        &mut self,
        graph_index: usize,
        tuple_index: usize,
        tuple: &[TableauObject],
    ) {
        for position in (1..tuple.len()).rev() {
            let node = tuple[position]
                .as_node()
                .expect("description-graph tuple argument is a node");
            let head = *self.occurrence_head.get(&node).unwrap_or(&-1);
            let list_node = self.occurrences.new_list_node();
            self.occurrences.initialize_list_node(
                list_node,
                graph_index as i32,
                tuple_index as i32,
                position as i32,
                head,
            );
            self.occurrence_head.insert(node, list_node as i32);
        }
    }

    /// Port of `descriptionGraphTupleRemoved`: unlink each node's head occurrence
    /// record (the LIFO invariant guarantees it is exactly this tuple's record at
    /// this position). Fired for every tuple `backtrack` removes.
    fn description_graph_tuple_removed(&mut self, tuple: &[TableauObject]) {
        for position in (1..tuple.len()).rev() {
            let node = tuple[position]
                .as_node()
                .expect("description-graph tuple argument is a node");
            let list_node = *self.occurrence_head.get(&node).unwrap_or(&-1);
            debug_assert!(list_node != -1, "occurrence-list underflow on backtrack");
            debug_assert_eq!(
                self.occurrences.position_in_tuple(list_node as usize),
                position as i32
            );
            let next = self.occurrences.next_node(list_node as usize);
            if next == -1 {
                self.occurrence_head.remove(&node);
            } else {
                self.occurrence_head.insert(node, next);
            }
            self.occurrences.delete_list_node(list_node as usize);
        }
    }

    /// Port of `ExtensionTable.isTupleActive(tupleIndex)`: every node argument of
    /// the tuple (positions `1..arity`) is active.
    fn tuple_is_active(&self, graph_index: usize, tuple_index: usize, tableau: &Tableau) -> bool {
        let table = &self.tables[graph_index];
        for position in 1..table.arity() {
            let node = table
                .get_tuple_object(tuple_index, position)
                .as_node()
                .expect("description-graph tuple argument is a node");
            if !tableau.nodes[node].is_active() {
                return false;
            }
        }
        true
    }

    /// Port of `mergeGraphs` (`MergingManager.java:187`): when `merge_from` is
    /// merged into `merge_into`, every *active* graph tuple in which `merge_from`
    /// occurs is re-added with `merge_from` replaced by `merge_into` at that
    /// position. The rewritten tuples are collected first (the occurrence walk
    /// only reads), then re-added (which mutates the tables/occurrence lists).
    fn merge_graphs_impl(
        &mut self,
        merge_from: NodeId,
        merge_into: NodeId,
        merge_dependency_set: &DependencySet,
        tableau: &mut Tableau,
    ) {
        let mut rewritten: Vec<(usize, Vec<TableauObject>, DependencySet, bool)> = Vec::new();
        let mut list_node = *self.occurrence_head.get(&merge_from).unwrap_or(&-1);
        while list_node != -1 {
            let graph_index = self.occurrences.graph_index(list_node as usize) as usize;
            let tuple_index = self.occurrences.tuple_index(list_node as usize) as usize;
            let position = self.occurrences.position_in_tuple(list_node as usize) as usize;
            // HermiT only re-adds tuples that are still active (isTupleActive).
            if self.tuple_is_active(graph_index, tuple_index, tableau) {
                let arity = self.tables[graph_index].arity();
                let mut tuple: Vec<TableauObject> = Vec::with_capacity(arity);
                for i in 0..arity {
                    tuple.push(self.tables[graph_index].get_tuple_object(tuple_index, i).clone());
                }
                tuple[position] = TableauObject::Node(merge_into);
                let is_core = self.tables[graph_index].is_core(tuple_index);
                let empty = tableau.dependency_set_factory.empty_set();
                let mut union = UnionDependencySet::new(2);
                union.add_constituent(DependencySet::Permanent(
                    self.tables[graph_index].get_dependency_set(tuple_index, &empty),
                ));
                union.add_constituent(merge_dependency_set.clone());
                rewritten.push((graph_index, tuple, DependencySet::Union(union), is_core));
            }
            list_node = self.occurrences.next_node(list_node as usize);
        }
        for (graph_index, tuple, dependency_set, is_core) in rewritten {
            let permanent = tableau.dependency_set_factory.get_permanent(&dependency_set);
            self.add_tuple(
                graph_index,
                tuple,
                permanent,
                is_core,
                &mut tableau.dependency_set_factory,
            );
        }
    }

    /// Port of `checkGraphConstraints`: enforce graph rigidity. Returns whether
    /// it changed anything (a merge or a clash). Iterates each graph table's
    /// `DELTA_OLD` view (HermiT's `m_deltaOldRetrievals`) and, for every node
    /// position, walks the node's occurrence list for an *active* other tuple in
    /// the same graph: same position forces a component-wise merge, different
    /// position is a rigidity clash.
    fn check_graph_constraints_impl(&self, tableau: &mut Tableau) -> bool {
        let mut has_change = false;
        for graph_index in 0..self.tables.len() {
            if tableau.contains_clash() {
                break;
            }
            let arity = self.tables[graph_index].arity();
            let (start, after_last) = self.tables[graph_index].view_range(View::DeltaOld);
            for this_tuple_index in start..after_last {
                if tableau.contains_clash() {
                    break;
                }
                for position in 1..arity {
                    let node = self.tables[graph_index]
                        .get_tuple_object(this_tuple_index, position)
                        .as_node()
                        .expect("description-graph tuple argument is a node");
                    let mut list_node = *self.occurrence_head.get(&node).unwrap_or(&-1);
                    while list_node != -1 {
                        let other_graph = self.occurrences.graph_index(list_node as usize) as usize;
                        let other_tuple = self.occurrences.tuple_index(list_node as usize) as usize;
                        let other_position =
                            self.occurrences.position_in_tuple(list_node as usize) as usize;
                        if other_graph == graph_index
                            && (other_tuple != this_tuple_index || other_position != position)
                            && self.tuple_is_active(graph_index, other_tuple, tableau)
                        {
                            // The union of the two participating tuples' dependency
                            // sets (HermiT's `m_binaryUnionDependencySet`), passed to
                            // both the merge and the clash.
                            let pair_dependency_set = {
                                let empty = tableau.dependency_set_factory.empty_set();
                                let mut union = UnionDependencySet::new(2);
                                union.add_constituent(DependencySet::Permanent(
                                    self.tables[graph_index]
                                        .get_dependency_set(this_tuple_index, &empty),
                                ));
                                union.add_constituent(DependencySet::Permanent(
                                    self.tables[graph_index].get_dependency_set(other_tuple, &empty),
                                ));
                                DependencySet::Union(union)
                            };
                            // `DescriptionGraphManager.checkGraphConstraints`:133 —
                            // descriptionGraphCheckingStarted around the merge/clash.
                            tableau.monitor_event(|m| m.description_graph_checking_started());
                            if other_position == position {
                                // Same position -> the two tuples must coincide
                                // component-wise (HermiT merges positions arity-1 ..= 1).
                                for merge_position in (1..arity).rev() {
                                    // HermiT merges the RAW stored nodes (it does
                                    // not gate the "this" tuple on activity, so an
                                    // inactive node must merge as the stored node,
                                    // not its canonical survivor); `merge_nodes`
                                    // is a no-op for an inactive or equal pair.
                                    let node_first = self.tables[graph_index]
                                        .get_tuple_object(this_tuple_index, merge_position)
                                        .as_node()
                                        .expect("description-graph tuple argument is a node");
                                    let node_second = self.tables[graph_index]
                                        .get_tuple_object(other_tuple, merge_position)
                                        .as_node()
                                        .expect("description-graph tuple argument is a node");
                                    if node_first != node_second {
                                        tableau.merge_nodes(
                                            node_first,
                                            node_second,
                                            &pair_dependency_set,
                                        );
                                        has_change = true;
                                    }
                                    // DescriptionGraphManager.checkGraphConstraints:142.
                                    tableau.note_interrupt();
                                }
                            } else {
                                // Different positions -> rigidity violated.
                                tableau.set_clash(&pair_dependency_set);
                                has_change = true;
                            }
                            // `DescriptionGraphManager.checkGraphConstraints`:150 —
                            // descriptionGraphCheckingFinished.
                            tableau.monitor_event(|m| m.description_graph_checking_finished());
                        }
                        list_node = self.occurrences.next_node(list_node as usize);
                        // DescriptionGraphManager.checkGraphConstraints:153.
                        tableau.note_interrupt();
                    }
                }
            }
            // DescriptionGraphManager.checkGraphConstraints:159.
            tableau.note_interrupt();
        }
        has_change
    }

    /// Port of `checkGraphConstraints`, callable directly in tests. The
    /// tableau-driven path goes through `Tableau::check_graph_constraints`.
    pub fn check_graph_constraints(&self, tableau: &mut Tableau) -> bool {
        self.check_graph_constraints_impl(tableau)
    }
}

impl Tableau {
    /// Port of `DescriptionGraphManager.expand`: lay out a description graph for
    /// `for_node`, which plays the existential's anchor vertex. Fresh graph
    /// nodes are created for the other vertices; the graph tuple is recorded (so
    /// `isSatisfied`/`checkGraphConstraints`/`mergeGraphs` see this occurrence);
    /// then every vertex gets its atomic concept and every edge its atomic role.
    ///
    /// `dependency_set` should be the existential's concept-assertion dependency
    /// set (HermiT: `getConceptAssertionDependencySet(existsDescriptionGraph,
    /// forNode)`); the public expansion path computes it. Older direct callers
    /// may pass an explicit set.
    pub fn expand_description_graph(
        &mut self,
        exists: &ExistsDescriptionGraph,
        for_node: NodeId,
        dependency_set: &DependencySet,
    ) {
        let graph = exists.get_description_graph().clone();
        let anchor_vertex = exists.get_vertex();

        let mut new_nodes: Vec<NodeId> = Vec::with_capacity(graph.number_of_vertices());
        for vertex in 0..graph.number_of_vertices() {
            let node = if vertex as i32 == anchor_vertex {
                for_node
            } else {
                // HermiT: createNewGraphNode(forNode.getClusterAnchor(), ..).
                let anchor = self.cluster_anchor(for_node);
                self.create_new_graph_node(anchor, dependency_set)
            };
            new_nodes.push(node);
        }
        // Record the graph tuple (HermiT `m_extensionManager.addTuple` ->
        // `descriptionGraphTupleAdded`): the N-ary tuple `[graph, v0, v1, ...]`
        // goes into the graph's extension table before canonicalization, exactly
        // as Java stores `auxiliaryTuple`. The graph may be unregistered (no
        // index); then there is no occurrence bookkeeping.
        if let Some(graph_index) = self.description_graph_manager.graph_indices.get(&graph).copied()
        {
            let mut tuple: Vec<TableauObject> = Vec::with_capacity(new_nodes.len() + 1);
            tuple.push(TableauObject::DescriptionGraph(graph.clone()));
            for &node in &new_nodes {
                tuple.push(TableauObject::Node(node));
            }
            let permanent = self.dependency_set_factory.get_permanent(dependency_set);
            self.description_graph_manager.add_tuple(
                graph_index,
                tuple,
                permanent,
                true,
                &mut self.dependency_set_factory,
            );
        }
        // Replace each node with its canonical node and accumulate the
        // dependency set (Java: dependencySet=newNode.addCanonicalNodeDependencySet(dependencySet),
        // DescriptionGraphManager.java:243-244). The accumulated dep is then
        // used for all concept/role assertions (Java:248,251).
        let mut accumulated_dep = self.add_canonical_node_dependency_set(new_nodes[0], dependency_set);
        new_nodes[0] = self.get_canonical_node(new_nodes[0]);
        for node in new_nodes.iter_mut().skip(1) {
            accumulated_dep = self.add_canonical_node_dependency_set(*node, &DependencySet::Permanent(accumulated_dep));
            *node = self.get_canonical_node(*node);
        }
        let dep = DependencySet::Permanent(accumulated_dep);
        // The graph layout: a concept per vertex and a role per edge.
        for vertex in 0..graph.number_of_vertices() {
            let concept = Concept::AtomicConcept(graph.get_atomic_concept_for_vertex(vertex).clone());
            self.add_concept_assertion(concept, new_nodes[vertex], &dep, true);
        }
        for edge_index in 0..graph.number_of_edges() {
            let edge = graph.get_edge(edge_index);
            let role = Role::AtomicRole(edge.get_atomic_role().clone());
            let from = new_nodes[edge.get_from_vertex() as usize];
            let to = new_nodes[edge.get_to_vertex() as usize];
            self.add_role_assertion(role, from, to, &dep, true);
        }
    }

    /// Port of `AbstractExpansionStrategy.expandExistentials`'s
    /// `ExistsDescriptionGraph` branch: if the existential is not already
    /// satisfied (`DescriptionGraphManager.isSatisfied`) expand it
    /// (`DescriptionGraphManager.expand`) and report a change; either way the
    /// caller marks it processed. Returns whether an expansion happened.
    pub fn expand_exists_description_graph(
        &mut self,
        exists: &ExistsDescriptionGraph,
        for_node: NodeId,
    ) -> bool {
        if self.description_graph_manager.is_satisfied(exists, for_node) {
            return false;
        }
        // HermiT: dependencySet = getConceptAssertionDependencySet(exists, forNode).
        let dependency_set = DependencySet::Permanent(
            self.get_concept_assertion_dependency_set(
                &Concept::ExistsDescriptionGraph(exists.clone()),
                for_node,
            )
            .unwrap_or_else(|| self.dependency_set_factory.empty_set()),
        );
        self.monitor_event(|m| m.existential_expansion_started());
        self.expand_description_graph(exists, for_node, &dependency_set);
        self.monitor_event(|m| m.existential_expansion_finished());
        true
    }

    /// Port of `DescriptionGraphManager.checkGraphConstraints`, driven from
    /// `doIteration` (`Tableau.java:415-416`). Delegates to the owned manager
    /// (taken out temporarily so it can call back into `&mut self`).
    pub fn check_graph_constraints(&mut self) -> bool {
        if !self.description_graph_manager.has_description_graphs() {
            return false;
        }
        let manager = std::mem::take(&mut self.description_graph_manager);
        let changed = manager.check_graph_constraints_impl(self);
        self.description_graph_manager = manager;
        changed
    }

    /// Port of the `m_descriptionGraphManager.mergeGraphs` call in
    /// `MergingManager.mergeNodes` (`MergingManager.java:187`).
    pub fn merge_graphs(
        &mut self,
        merge_from: NodeId,
        merge_into: NodeId,
        dependency_set: &DependencySet,
    ) {
        if !self.description_graph_manager.has_description_graphs() {
            return;
        }
        // mergeGraphs re-adds rewritten tuples to the per-graph extension tables;
        // the manager is taken out temporarily so it can read node activity and
        // intern dependency sets through `&mut self`.
        let mut manager = std::mem::take(&mut self.description_graph_manager);
        manager.merge_graphs_impl(merge_from, merge_into, dependency_set, self);
        self.description_graph_manager = manager;
    }
}

/// Offsets of the four components within a list-node record.
const GRAPH_INDEX: usize = 0;
const TUPLE_INDEX: usize = 1;
const POSITION_IN_TUPLE: usize = 2;
const NEXT_NODE: usize = 3;
const LIST_NODE_SIZE: usize = 4;

/// A free-list of occurrence records. A "list node" is the base index of a
/// record (always a multiple of `LIST_NODE_SIZE`); `-1` is the null link.
pub struct OccurrenceManager {
    store: Vec<i32>,
    first_free_list_node: usize,
}

impl Default for OccurrenceManager {
    fn default() -> Self {
        OccurrenceManager::new()
    }
}

impl OccurrenceManager {
    pub fn new() -> OccurrenceManager {
        let mut store = vec![0; LIST_NODE_SIZE];
        store[NEXT_NODE] = -1;
        OccurrenceManager { store, first_free_list_node: 0 }
    }

    pub fn clear(&mut self) {
        self.first_free_list_node = 0;
        self.set_component(0, NEXT_NODE, -1);
    }

    pub fn get_component(&self, list_node: usize, component: usize) -> i32 {
        self.store[list_node + component]
    }

    pub fn set_component(&mut self, list_node: usize, component: usize, value: i32) {
        self.store[list_node + component] = value;
    }

    pub fn graph_index(&self, list_node: usize) -> i32 {
        self.get_component(list_node, GRAPH_INDEX)
    }
    pub fn tuple_index(&self, list_node: usize) -> i32 {
        self.get_component(list_node, TUPLE_INDEX)
    }
    pub fn position_in_tuple(&self, list_node: usize) -> i32 {
        self.get_component(list_node, POSITION_IN_TUPLE)
    }
    pub fn next_node(&self, list_node: usize) -> i32 {
        self.get_component(list_node, NEXT_NODE)
    }

    /// `initializeListNode`.
    pub fn initialize_list_node(
        &mut self,
        list_node: usize,
        graph_index: i32,
        tuple_index: i32,
        position_in_tuple: i32,
        next_list_node: i32,
    ) {
        self.set_component(list_node, GRAPH_INDEX, graph_index);
        self.set_component(list_node, TUPLE_INDEX, tuple_index);
        self.set_component(list_node, POSITION_IN_TUPLE, position_in_tuple);
        self.set_component(list_node, NEXT_NODE, next_list_node);
    }

    /// `newListNode`: a fresh record from the free list (or a freshly grown one).
    pub fn new_list_node(&mut self) -> usize {
        let new_list_node = self.first_free_list_node;
        let next_free = self.get_component(self.first_free_list_node, NEXT_NODE);
        if next_free != -1 {
            self.first_free_list_node = next_free as usize;
        } else {
            self.first_free_list_node += LIST_NODE_SIZE;
            if self.first_free_list_node + LIST_NODE_SIZE > self.store.len() {
                self.store.resize(self.first_free_list_node + LIST_NODE_SIZE, 0);
            }
            self.set_component(self.first_free_list_node, NEXT_NODE, -1);
        }
        new_list_node
    }

    /// `deleteListNode`: return a record to the free list.
    pub fn delete_list_node(&mut self, list_node: usize) {
        let head = self.first_free_list_node as i32;
        self.set_component(list_node, NEXT_NODE, head);
        self.first_free_list_node = list_node;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{
        AtomicConcept, AtomicRole, Concept, DescriptionGraph, Edge, ExistsDescriptionGraph,
    };
    use crate::tableau::object::TableauObject;
    use crate::tableau::View;
    use std::collections::{BTreeSet, HashSet};

    #[test]
    fn expand_creates_graph_layout() {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());

        // A two-vertex graph: V0:C0, V1:C1, with an edge r from V0 to V1.
        let c0 = AtomicConcept::create("http://example.org/C0");
        let c1 = AtomicConcept::create("http://example.org/C1");
        let r = AtomicRole::create("http://example.org/r");
        let graph = DescriptionGraph::new(
            "http://example.org/G",
            vec![c0.clone(), c1.clone()],
            vec![Edge::new(r.clone(), 0, 1)],
            HashSet::default(),
        );
        // Expand for an anchor node playing vertex 0.
        let anchor = tableau.create_new_named_node(&empty);
        let exists = ExistsDescriptionGraph::create(graph, 0);
        tableau.expand_description_graph(&exists, anchor, &empty);

        // The anchor (vertex 0) has concept C0; its r-successor has C1.
        assert!(tableau
            .contains_concept_assertion(&Concept::AtomicConcept(c0.clone()), anchor));

        // Find the r-successor of the anchor.
        let retrieval = tableau.create_ternary_retrieval(
            [0, 1, -1],
            [
                Some(TableauObject::DLPredicate(crate::model::DLPredicate::AtomicRole(r.clone()))),
                Some(TableauObject::Node(anchor)),
                None,
            ],
            View::Total,
        );
        let successors: BTreeSet<NodeId> = retrieval
            .tuple_indices
            .iter()
            .filter_map(|&idx| tableau.ternary_extension_table.get_tuple_object(idx, 2).as_node())
            .collect();
        assert_eq!(successors.len(), 1);
        let v1 = *successors.iter().next().unwrap();
        assert_ne!(v1, anchor);
        assert!(tableau.contains_concept_assertion(&Concept::AtomicConcept(c1.clone()), v1));
    }

    /// Test helper: store the graph tuple `[graph, nodes...]` in `manager`'s
    /// table for `graph_index` (the leading object is the graph itself, so node
    /// `nodes[i]` lands at position `i+1`), via the private `add_tuple`.
    fn add_graph_tuple(
        manager: &mut DescriptionGraphManager,
        graph: &DescriptionGraph,
        graph_index: usize,
        nodes: &[NodeId],
        factory: &mut DependencySetFactory,
    ) {
        let mut tuple = vec![TableauObject::DescriptionGraph(graph.clone())];
        for &node in nodes {
            tuple.push(TableauObject::Node(node));
        }
        let permanent = factory.empty_set();
        manager.add_tuple(graph_index, tuple, permanent, true, factory);
    }

    #[test]
    fn same_position_occurrence_merges_tuples() {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let b = tableau.create_new_named_node(&empty);
        let cc = tableau.create_new_named_node(&empty);

        // Two tuples of graph 0 sharing node `a` at the anchor vertex (position 1)
        // -> the other positions (b and cc) must be merged.
        let graph = dummy_graph();
        let mut manager = DescriptionGraphManager::new(std::slice::from_ref(&graph), true);
        add_graph_tuple(&mut manager, &graph, 0, &[a, b], &mut tableau.dependency_set_factory);
        add_graph_tuple(&mut manager, &graph, 0, &[a, cc], &mut tableau.dependency_set_factory);
        manager.propagate_delta_new();
        assert!(manager.check_graph_constraints(&mut tableau));
        assert_eq!(tableau.get_canonical_node(b), tableau.get_canonical_node(cc));
        assert!(!tableau.contains_clash());
    }

    #[test]
    fn different_position_occurrence_clashes() {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let b = tableau.create_new_named_node(&empty);
        let cc = tableau.create_new_named_node(&empty);

        // Node `b` occurs at vertex position 2 of the first tuple and position 1 of
        // the second -> rigidity violated -> clash.
        let graph = dummy_graph();
        let mut manager = DescriptionGraphManager::new(std::slice::from_ref(&graph), true);
        add_graph_tuple(&mut manager, &graph, 0, &[a, b], &mut tableau.dependency_set_factory);
        add_graph_tuple(&mut manager, &graph, 0, &[b, cc], &mut tableau.dependency_set_factory);
        manager.propagate_delta_new();
        assert!(manager.check_graph_constraints(&mut tableau));
        assert!(tableau.contains_clash());
    }

    fn dummy_graph() -> DescriptionGraph {
        DescriptionGraph::new(
            "http://example.org/G",
            vec![
                AtomicConcept::create("http://example.org/V0"),
                AtomicConcept::create("http://example.org/V1"),
            ],
            Vec::new(),
            HashSet::default(),
        )
    }

    #[test]
    fn allocates_initializes_and_reuses_records() {
        let mut occ = OccurrenceManager::new();

        // Allocate two records, prepending the second to the first's list.
        let a = occ.new_list_node();
        occ.initialize_list_node(a, 1, 10, 2, -1);
        let b = occ.new_list_node();
        occ.initialize_list_node(b, 1, 11, 3, a as i32);
        assert_ne!(a, b);

        // Components read back correctly.
        assert_eq!(occ.graph_index(b), 1);
        assert_eq!(occ.tuple_index(b), 11);
        assert_eq!(occ.position_in_tuple(b), 3);
        assert_eq!(occ.next_node(b), a as i32);
        assert_eq!(occ.next_node(a), -1);

        // Walk the list b -> a.
        let mut node = b as i32;
        let mut visited = Vec::new();
        while node != -1 {
            visited.push(occ.tuple_index(node as usize));
            node = occ.next_node(node as usize);
        }
        assert_eq!(visited, vec![11, 10]);

        // Deleting a record returns it to the free list; the next allocation
        // reuses it.
        occ.delete_list_node(b);
        let c = occ.new_list_node();
        assert_eq!(c, b);
    }

    // ---- Wired tableau-lifecycle hooks -------------------------------------

    /// A two-vertex graph V0:C0 -r-> V1:C1, registered on the tableau and used
    /// by an `ExistsDescriptionGraph` existential. Returns the graph and `r`.
    fn two_vertex_graph() -> (DescriptionGraph, AtomicConcept, AtomicConcept, AtomicRole) {
        let c0 = AtomicConcept::create("http://example.org/C0");
        let c1 = AtomicConcept::create("http://example.org/C1");
        let r = AtomicRole::create("http://example.org/r");
        let graph = DescriptionGraph::new(
            "http://example.org/G",
            vec![c0.clone(), c1.clone()],
            vec![Edge::new(r.clone(), 0, 1)],
            HashSet::default(),
        );
        (graph, c0, c1, r)
    }

    /// The wired existential-expansion branch. An
    /// `ExistsDescriptionGraph` existential on a node is expanded by
    /// `expand_existentials` (mirroring `AbstractExpansionStrategy`'s graph
    /// branch -> `DescriptionGraphManager.isSatisfied`/`.expand`): the graph
    /// layout is created, the tuple recorded (so `is_satisfied` is now true),
    /// the existential marked processed, and there is no clash.
    #[test]
    fn wired_expansion_creates_graph_records_tuple_and_marks_processed() {
        let (graph, c0, c1, r) = two_vertex_graph();
        let mut tableau = Tableau::new();
        tableau.set_description_graphs(std::slice::from_ref(&graph));
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());

        let anchor = tableau.create_new_named_node(&empty);
        let exists = ExistsDescriptionGraph::create(graph.clone(), 0);
        // Assert the existential as a concept -> queues it as unprocessed.
        tableau.add_concept_assertion(
            Concept::ExistsDescriptionGraph(exists.clone()),
            anchor,
            &empty,
            true,
        );
        assert!(tableau.node(anchor).has_unprocessed_existentials());
        assert!(!tableau.description_graph_manager.is_satisfied(&exists, anchor));

        // Drive expansion (the wired branch).
        let changed = tableau.expand_existentials();
        assert!(changed, "the graph existential must expand");

        // The existential is now processed and satisfied (the tuple is recorded).
        assert!(!tableau.node(anchor).has_unprocessed_existentials());
        assert!(tableau.description_graph_manager.is_satisfied(&exists, anchor));
        assert!(!tableau.contains_clash());

        // The graph layout exists: V0 (the anchor) carries C0 with an r-successor
        // carrying C1.
        assert!(tableau.contains_concept_assertion(&Concept::AtomicConcept(c0.clone()), anchor));
        let retrieval = tableau.create_ternary_retrieval(
            [0, 1, -1],
            [
                Some(TableauObject::DLPredicate(crate::model::DLPredicate::AtomicRole(r.clone()))),
                Some(TableauObject::Node(anchor)),
                None,
            ],
            View::Total,
        );
        let successors: BTreeSet<NodeId> = retrieval
            .tuple_indices
            .iter()
            .filter_map(|&idx| tableau.ternary_extension_table.get_tuple_object(idx, 2).as_node())
            .collect();
        assert_eq!(successors.len(), 1);
        let v1 = *successors.iter().next().unwrap();
        assert!(tableau.contains_concept_assertion(&Concept::AtomicConcept(c1.clone()), v1));

        // Re-running expansion is a no-op: already satisfied (isSatisfied true),
        // nothing more is created.
        assert!(!tableau.expand_existentials());
    }

    /// A graph-constraint violation drives a clash through
    /// the tableau-level `check_graph_constraints` (the `doIteration` hook).
    /// A node occurring in the same graph at two DIFFERENT positions violates
    /// rigidity -> `setClash`.
    #[test]
    fn wired_check_graph_constraints_clashes_on_rigidity_violation() {
        let (graph, _c0, _c1, _r) = two_vertex_graph();
        let mut tableau = Tableau::new();
        tableau.set_description_graphs(std::slice::from_ref(&graph));
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let b = tableau.create_new_named_node(&empty);
        let cc = tableau.create_new_named_node(&empty);

        // `b` at vertex position 2 of tuple 0, position 1 of tuple 1 -> rigidity
        // violated.
        add_graph_tuple(
            &mut tableau.description_graph_manager,
            &graph,
            0,
            &[a, b],
            &mut tableau.dependency_set_factory,
        );
        add_graph_tuple(
            &mut tableau.description_graph_manager,
            &graph,
            0,
            &[b, cc],
            &mut tableau.dependency_set_factory,
        );
        assert!(!tableau.contains_clash());

        tableau.propagate_delta_new_all();
        let changed = tableau.check_graph_constraints();
        assert!(changed);
        assert!(tableau.contains_clash(), "rigidity violation must clash");
    }

    /// Two tuples sharing a node at the SAME position force
    /// the other positions to merge (componentwise), driven through the wired
    /// `check_graph_constraints`.
    #[test]
    fn wired_check_graph_constraints_merges_same_position() {
        let (graph, _c0, _c1, _r) = two_vertex_graph();
        let mut tableau = Tableau::new();
        tableau.set_description_graphs(std::slice::from_ref(&graph));
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let b = tableau.create_new_named_node(&empty);
        let cc = tableau.create_new_named_node(&empty);

        add_graph_tuple(
            &mut tableau.description_graph_manager,
            &graph,
            0,
            &[a, b],
            &mut tableau.dependency_set_factory,
        );
        add_graph_tuple(
            &mut tableau.description_graph_manager,
            &graph,
            0,
            &[a, cc],
            &mut tableau.dependency_set_factory,
        );

        tableau.propagate_delta_new_all();
        assert!(tableau.check_graph_constraints());
        assert_eq!(tableau.get_canonical_node(b), tableau.get_canonical_node(cc));
        assert!(!tableau.contains_clash());
    }

    /// A node merge merges graph tuples. `merge_nodes`
    /// (MergingManager) calls `merge_graphs`, so the surviving node inherits
    /// the merged-away node's graph-tuple occurrence at the same position.
    #[test]
    fn wired_merge_merges_graph_tuples() {
        let (graph, _c0, _c1, _r) = two_vertex_graph();
        let mut tableau = Tableau::new();
        tableau.set_description_graphs(std::slice::from_ref(&graph));
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let b = tableau.create_new_named_node(&empty);

        // `a` occurs in a graph tuple at vertex position 1 (the anchor vertex V0).
        add_graph_tuple(
            &mut tableau.description_graph_manager,
            &graph,
            0,
            &[a, b],
            &mut tableau.dependency_set_factory,
        );
        let exists_v0 = ExistsDescriptionGraph::create(graph.clone(), 0);
        assert!(tableau.description_graph_manager.is_satisfied(&exists_v0, a));

        // A fresh node `s` that will survive the merge of `a` into it.
        let s = tableau.create_new_named_node(&empty);
        // `s` does not yet occur in the graph.
        assert!(!tableau.description_graph_manager.is_satisfied(&exists_v0, s));

        // Merge `a` and `s`: merge_graphs re-records `a`'s tuple with the
        // survivor at position 0.
        assert!(tableau.merge_nodes(a, s, &empty));
        let survivor = tableau.get_canonical_node(a);
        // The survivor now occupies V0 in a graph tuple.
        assert!(
            tableau.description_graph_manager.is_satisfied(&exists_v0, survivor),
            "the merge survivor must inherit the graph-tuple occurrence"
        );
    }

    /// A tableau without description graphs has an empty manager whose every
    /// hook is a no-op.
    #[test]
    fn empty_manager_is_a_noop_at_every_hook() {
        let mut tableau = Tableau::new();
        assert!(!tableau.description_graph_manager.has_description_graphs());
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let b = tableau.create_new_named_node(&empty);
        // Every wired hook returns immediately and changes nothing.
        assert!(!tableau.check_graph_constraints());
        tableau.merge_graphs(a, b, &empty);
        assert!(!tableau.contains_clash());
    }

    /// Backtracking removes a graph tuple created in the abandoned branch and
    /// unlinks its occurrence records, so a later branch does not see the stale
    /// tuple. This is the behaviour the `Vec`-based storage lacked.
    #[test]
    fn backtracking_removes_graph_tuple_and_occurrences() {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let b = tableau.create_new_named_node(&empty);
        let graph = dummy_graph();
        let mut manager = DescriptionGraphManager::new(std::slice::from_ref(&graph), true);
        let exists_v0 = ExistsDescriptionGraph::create(graph.clone(), 0);

        // Save the state of a branching point, then create a graph tuple inside it.
        manager.branching_point_pushed(1);
        add_graph_tuple(&mut manager, &graph, 0, &[a, b], &mut tableau.dependency_set_factory);
        assert!(manager.is_satisfied(&exists_v0, a));

        // Backtracking the branch removes the tuple and its occurrence records.
        manager.backtrack(1, &mut tableau.dependency_set_factory);
        assert!(
            !manager.is_satisfied(&exists_v0, a),
            "a backtracked graph tuple must not persist"
        );

        // The freed table slot is reusable: a fresh tuple lands cleanly.
        let cc = tableau.create_new_named_node(&empty);
        add_graph_tuple(&mut manager, &graph, 0, &[a, cc], &mut tableau.dependency_set_factory);
        assert!(manager.is_satisfied(&exists_v0, a));
    }
}
