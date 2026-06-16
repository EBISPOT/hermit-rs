// Port of org.semanticweb.HermiT.hierarchy.QuasiOrderClassification.
//
// HermiT's "quasi-order" classifier builds a concept hierarchy with two graphs:
//   * `known_subsumptions`   -- subsumptions established for certain, and
//   * `possible_subsumptions` -- candidate subsumptions read off a model that
//                                still need an explicit subsumption test.
// It seeds the known graph from told subsumers, then uses a "leaf-node strategy"
// (build a model for each concept, read its deterministic subsumers as known and
// its remaining label as possible, propagate unsatisfiability downward), and
// finally resolves the leftover possible subsumptions with the enhanced-traversal
// search over a small hierarchy of the unknown possible subsumers. The result is
// the transitively reduced hierarchy.
//
// HermiT's original works directly against the tableau (extension tables, node
// labels, dependency sets). Just like the `InstanceManager` port, this version
// is parameterized by an oracle so the algorithm is decoupled from the engine and
// testable in isolation:
//   * `build_model(concept)` returns `None` if `concept` is unsatisfiable, else
//     the `(known_subsumers, possible_subsumers)` read from its model's root node
//     (deterministic label vs. the rest), and
//   * `does_subsume(parent, child)` is the explicit subsumption test.
// Because the per-concept readout already yields each concept's own possible
// subsumers, the driver builds a model for every satisfiable concept rather than
// harvesting cross-node labels (a performance difference only; the resulting
// hierarchy is identical).

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

use crate::graph::Graph;
use crate::hierarchy::{
    build_hierarchy_with_monitor, ClassificationProgressMonitor, NoProgressMonitor, Hierarchy,
    NodeRef,
};

/// The read-off of one saturated model, used by the leaf-node strategy.
pub struct ModelReadOff<E> {
    /// `readKnownSubsumersFromRootNode`: the query concept's deterministic
    /// (empty-dependency-set) subsumers, read off the model's root node when the
    /// root was not merged non-deterministically.
    pub query_known: HashSet<E>,
    /// The query concept's possible subsumers. Used only when `node_labels` is
    /// `None` (an oracle, like the role classifier's edge read-off, that does not
    /// expose full node labels for cross-concept harvesting).
    pub query_possible: HashSet<E>,
    /// `updatePossibleSubsumers`: the concept label of every active, unblocked node
    /// in the model. Every concept that appears in a label gets its possible
    /// subsumers harvested (first occurrence) or pruned/intersected (later
    /// occurrences) against the label, so one model build populates the possible
    /// subsumers of many concepts. `None` disables cross-concept harvesting.
    pub node_labels: Option<Vec<HashSet<E>>>,
}

/// The outcome of the batched union test (`isEveryPossibleSubsumerNonSubsumer`).
/// When `subsumed` is true, the witnessing model also yields the query's
/// deterministic known subsumers (`readKnownSubsumersFromRootNode`), which the
/// classifier records and removes from the possible set to avoid redundant
/// pairwise tests. `query_known` is empty (and ignored) when `subsumed` is false.
pub struct UnionTestResult<E> {
    pub subsumed: bool,
    pub query_known: HashSet<E>,
}

/// The model/subsumption oracle the classifier runs against (the tableau in
/// HermiT). `E` is the element type (atomic concepts, identified by value).
pub trait SubsumptionOracle<E> {
    /// `buildModelForConcept` + `readKnownSubsumersFromRootNode` +
    /// `updatePossibleSubsumers`: `None` if `concept` is unsatisfiable, else the
    /// model read-off (query's known subsumers, and either the query's possible
    /// subsumers or the full node labels for cross-concept harvesting).
    fn build_model(&mut self, concept: &E) -> Option<ModelReadOff<E>>;
    /// `Relation.doesSubsume`: the explicit subsumption test `parent ⊒ child`.
    fn does_subsume(&mut self, parent: &E, child: &E) -> bool;
    /// `Relation.doesSubsume` together with the model read-off it harvests:
    /// `readKnownSubsumersFromRootNode` (the deterministic subsumers of `child`,
    /// returned in [`ModelReadOff::query_known`]) and, when `child` is NOT subsumed
    /// by `parent`, the witnessing model's node labels for `prunePossibleSubsumers`
    /// (returned in [`ModelReadOff::node_labels`]). The boolean is the subsumption
    /// result; the read-off is `None` when `parent ⊒ child` (the test is
    /// unsatisfiable, so no model exists to harvest). The default implementation
    /// performs no harvesting (for oracles that do not expose model internals).
    fn does_subsume_with_read_off(
        &mut self,
        parent: &E,
        child: &E,
    ) -> (bool, Option<ModelReadOff<E>>) {
        (self.does_subsume(parent, child), None)
    }
    /// The batched test of `isEveryPossibleSubsumerNonSubsumer`: whether `child`
    /// is subsumed by the *union* of `candidates` (one satisfiability test). When
    /// it is NOT subsumed by the union, no candidate individually subsumes it, so
    /// all are non-subsumers. When it IS subsumed, the returned
    /// [`UnionTestResult::query_known`] carries the deterministic subsumers read
    /// off the witnessing model (`readKnownSubsumersFromRootNode`). `None` if the
    /// oracle does not support the batched test (the caller then falls back to the
    /// per-candidate traversal).
    fn is_subsumed_by_union(
        &mut self,
        _child: &E,
        _candidates: &HashSet<E>,
    ) -> Option<UnionTestResult<E>> {
        None
    }
}

/// Port of `QuasiOrderClassification`.
pub struct QuasiOrderClassification<E: Eq + Hash + Clone, O> {
    oracle: O,
    top_element: E,
    bottom_element: E,
    elements: HashSet<E>,
    known_subsumptions: Graph<E>,
    possible_subsumptions: Graph<E>,
    /// Port of `QuasiOrderClassificationForRoles`: in role mode with inverses,
    /// `inverse_concept[c]` is the element for the inverse of the role `c`
    /// represents. When present, every known / possible subsumption is mirrored
    /// to the inverse concepts (the subclass's `addKnownSubsumption` /
    /// `addPossibleSubsumption` overrides).
    inverse_concept: Option<HashMap<E, E>>,
}

impl<E, O> QuasiOrderClassification<E, O>
where
    E: Eq + Hash + Clone,
    O: SubsumptionOracle<E>,
{
    pub fn new(
        oracle: O,
        top_element: E,
        bottom_element: E,
        elements: HashSet<E>,
    ) -> QuasiOrderClassification<E, O> {
        QuasiOrderClassification {
            oracle,
            top_element,
            bottom_element,
            elements,
            known_subsumptions: Graph::new(),
            possible_subsumptions: Graph::new(),
            inverse_concept: None,
        }
    }

    /// Port of `QuasiOrderClassificationForRoles`'s constructor: the role
    /// classifier. `inverse_concept` maps each role-concept to the concept of its
    /// inverse role; when the ontology has inverses this drives the mirroring of
    /// every subsumption onto the inverse concepts. Pass `None` for no inverses.
    pub fn new_for_roles(
        oracle: O,
        top_element: E,
        bottom_element: E,
        elements: HashSet<E>,
        inverse_concept: Option<HashMap<E, E>>,
    ) -> QuasiOrderClassification<E, O> {
        QuasiOrderClassification {
            oracle,
            top_element,
            bottom_element,
            elements,
            known_subsumptions: Graph::new(),
            possible_subsumptions: Graph::new(),
            inverse_concept,
        }
    }

    /// `m_conceptsForRoles.get(m_rolesForConcepts.get(concept).getInverse())`:
    /// the concept of the inverse role, in role mode with inverses.
    fn inverse_of(&self, concept: &E) -> Option<E> {
        self.inverse_concept.as_ref().and_then(|map| map.get(concept).cloned())
    }

    /// `getAllKnownSubsumers`.
    fn all_known_subsumers(&self, child: &E) -> HashSet<E> {
        self.known_subsumptions.get_reachable_successors(child)
    }
    /// `addKnownSubsumption` (mirroring to the inverse concepts in role mode).
    fn add_known_subsumption(&mut self, sub: &E, sup: &E) {
        self.known_subsumptions.add_edge(sub.clone(), sup.clone());
        if let (Some(sub_inv), Some(sup_inv)) = (self.inverse_of(sub), self.inverse_of(sup)) {
            self.known_subsumptions.add_edge(sub_inv, sup_inv);
        }
    }
    /// `addKnownSubsumptions`: adds the edges directly. Unlike the singular
    /// `addKnownSubsumption`, this is *not* overridden for roles, so it does not
    /// mirror to the inverse concepts (matching Java's plural variant).
    fn add_known_subsumptions(&mut self, sub: &E, sups: &HashSet<E>) {
        self.known_subsumptions.add_edges(sub.clone(), sups);
    }
    /// `addPossibleSubsumption` (mirroring to the inverse concepts in role mode).
    fn add_possible_subsumption(&mut self, sub: &E, sup: &E) {
        self.possible_subsumptions.add_edge(sub.clone(), sup.clone());
        if let (Some(sub_inv), Some(sup_inv)) = (self.inverse_of(sub), self.inverse_of(sup)) {
            self.possible_subsumptions.add_edge(sub_inv, sup_inv);
        }
    }
    /// `isUnsatisfiable`.
    fn is_unsatisfiable(&self, concept: &E) -> bool {
        self.known_subsumptions.successors(concept).contains(&self.bottom_element)
    }
    /// `makeConceptUnsatisfiable`.
    fn make_concept_unsatisfiable(&mut self, concept: &E) {
        let bottom = self.bottom_element.clone();
        self.add_known_subsumption(concept, &bottom);
        self.possible_subsumptions.clear_successors(concept);
    }
    /// `conceptHasBeenProcessedAlready`.
    fn concept_has_been_processed_already(&self, concept: &E) -> bool {
        !self.possible_subsumptions.successors(concept).is_empty()
            || self.is_unsatisfiable(concept)
    }

    /// `initialiseKnownSubsumptionsUsingToldSubsumers`: seed the known graph with
    /// told subsumptions `(sub, sup)` (HermiT reads these off the binary DL
    /// clauses; the caller supplies the equivalent pairs).
    pub fn initialise_known_subsumptions_using_told_subsumers(&mut self, told: &[(E, E)]) {
        for (sub, sup) in told {
            if self.elements.contains(sub) && self.elements.contains(sup) {
                self.add_known_subsumption(sub, sup);
            }
        }
    }

    /// Port of `QuasiOrderClassificationForRoles.initialiseKnownSubsumptionsUsingToldSubsumers`:
    /// seed the known graph from told role inclusions. Each told inclusion is
    /// `(body_concept, head_concept, args_differ)`: when the body and head atoms'
    /// first arguments differ (`r → s⁻`), the inverse of the body concept is the
    /// sub-concept; otherwise the body concept is. `add_known_subsumption` then
    /// mirrors onto the inverse concepts as needed.
    pub fn initialise_known_subsumptions_for_roles(&mut self, told: &[(E, E, bool)]) {
        for (body_concept, head_concept, args_differ) in told {
            if !self.elements.contains(body_concept) || !self.elements.contains(head_concept) {
                continue;
            }
            if *args_differ {
                if let Some(body_inv) = self.inverse_of(body_concept) {
                    self.add_known_subsumption(&body_inv, head_concept);
                }
            } else {
                self.add_known_subsumption(body_concept, head_concept);
            }
        }
    }

    /// `classify`: the public entry point.
    pub fn classify(self) -> Hierarchy<E> {
        self.classify_with_monitor(&mut NoProgressMonitor)
    }

    /// As [`classify`](Self::classify), but reports progress through a
    /// [`ClassificationProgressMonitor`]: `monitor.element_classified(e)` fires
    /// once per element of the final hierarchy's subsumer graph, matching Java's
    /// `classifyClasses` firing `elementClassified(AtomicConcept)` per concept.
    /// The intermediate hierarchies built during the leaf-node strategy and the
    /// possible-subsumer resolution use a no-op monitor; only the final
    /// transitively-reduced hierarchy is reported, so the monitor sees each
    /// classified element exactly once. Answer-neutral.
    pub fn classify_with_monitor<M>(mut self, monitor: &mut M) -> Hierarchy<E>
    where
        M: ClassificationProgressMonitor<E> + ?Sized,
    {
        let bottom = self.bottom_element.clone();
        self.make_concept_unsatisfiable(&bottom);
        self.update_subsumptions_using_leaf_node_strategy();

        // Keep only genuinely-unknown possible subsumptions per element.
        let mut unclassified: Vec<E> = Vec::new();
        let elements: Vec<E> = self.elements.iter().cloned().collect();
        for element in &elements {
            if !self.is_unsatisfiable(element) {
                let known = self.all_known_subsumers(element);
                self.possible_subsumptions.remove_successors(element, &known);
                if !self.possible_subsumptions.successors(element).is_empty() {
                    unclassified.push(element.clone());
                }
            }
        }

        // Resolve the remaining possible subsumptions.
        while !unclassified.is_empty() {
            let mut picked: Option<E> = None;
            let mut classified: HashSet<E> = HashSet::new();
            for element in &unclassified {
                let known = self.all_known_subsumers(element);
                self.possible_subsumptions.remove_successors(element, &known);
                if !self.possible_subsumptions.successors(element).is_empty() {
                    picked = Some(element.clone());
                    break;
                }
                classified.insert(element.clone());
            }
            unclassified.retain(|e| !classified.contains(e));
            let picked = match picked {
                Some(p) if unclassified.iter().any(|e| *e == p) => p,
                _ => {
                    if unclassified.is_empty() {
                        break;
                    }
                    continue;
                }
            };
            // `buildHierarchy` calls `isEveryPossibleSubsumerNonSubsumer` first
            // (always, even for an empty set) and only then checks the set is
            // non-empty -- on the set as left by the batched test, which removes
            // the now-known subsumers it reads off the witnessing model.
            let unknown_possible = self.possible_subsumptions.get_successors(&picked);
            if !self.is_every_possible_subsumer_non_subsumer(&unknown_possible, &picked) {
                // The batched test mutated the live possible-subsumer set, so the
                // small hierarchy is built over the pruned live set and the
                // non-empty guard is applied to it, matching Java's `!isEmpty()`.
                let unknown_possible = self.possible_subsumptions.get_successors(&picked);
                if !unknown_possible.is_empty() {
                    let small = self.build_hierarchy_of_unknown_possible(&unknown_possible);
                    self.check_unknown_subsumers_using_enhanced_traversal(
                        &small,
                        small.top_node(),
                        &picked,
                    );
                }
            }
            self.possible_subsumptions.clear_successors(&picked);
        }

        self.build_transitively_reduced_hierarchy_with_monitor(
            &self.known_subsumptions.clone(),
            &self.elements.clone(),
            monitor,
        )
    }

    /// `updateSubsumptionsUsingLeafNodeStrategy`: build a model for each not-yet
    /// processed concept (walking up from the bottom node's parents); record its
    /// deterministic subsumers as known and the rest as possible, propagating
    /// unsatisfiability down to descendants.
    fn update_subsumptions_using_leaf_node_strategy(&mut self) {
        let hierarchy = self.build_transitively_reduced_hierarchy(
            &self.known_subsumptions.clone(),
            &self.elements.clone(),
        );
        let mut to_process: Vec<NodeRef> =
            hierarchy.node(hierarchy.bottom_node()).parent_nodes().iter().copied().collect();
        let mut unsat_nodes: HashSet<NodeRef> = HashSet::new();

        while let Some(current_node) = to_process.pop() {
            let current_concept = hierarchy.node(current_node).representative().clone();
            if self.concept_has_been_processed_already(&current_concept) {
                continue;
            }
            match self.oracle.build_model(&current_concept) {
                None => {
                    self.make_concept_unsatisfiable(&current_concept);
                    unsat_nodes.insert(current_node);
                    for &parent in hierarchy.node(current_node).parent_nodes() {
                        to_process.push(parent);
                    }
                    // Propagate unsatisfiability to all descendants.
                    let mut visited: HashSet<NodeRef> = HashSet::new();
                    let mut to_visit: VecDeque<NodeRef> =
                        hierarchy.node(current_node).child_nodes().iter().copied().collect();
                    while let Some(child) = to_visit.pop_front() {
                        if visited.insert(child) && !unsat_nodes.contains(&child) {
                            for &grandchild in hierarchy.node(child).child_nodes() {
                                to_visit.push_back(grandchild);
                            }
                            unsat_nodes.insert(child);
                            self.make_concept_unsatisfiable(
                                &hierarchy.node(child).representative().clone(),
                            );
                            to_process.retain(|&n| n != child);
                            for &parent in hierarchy.node(child).parent_nodes() {
                                let parent_concept =
                                    hierarchy.node(parent).representative().clone();
                                if !self.concept_has_been_processed_already(&parent_concept) {
                                    to_process.push(parent);
                                }
                            }
                        }
                    }
                }
                Some(read_off) => {
                    // readKnownSubsumersFromRootNode: add each deterministic subsumer
                    // via the singular addKnownSubsumption (mirrored to inverses in
                    // role mode), not the plural addKnownSubsumptions.
                    for sup in &read_off.query_known {
                        if self.elements.contains(sup) {
                            self.add_known_subsumption(&current_concept, sup);
                        }
                    }
                    match read_off.node_labels {
                        // updatePossibleSubsumers: harvest every concept's possibles
                        // from the model's node labels (one model serves many concepts).
                        Some(node_labels) => self.update_possible_subsumers(&node_labels),
                        // No node labels exposed: just the query's own possibles.
                        None => {
                            for sup in read_off.query_possible {
                                if self.elements.contains(&sup) {
                                    self.add_possible_subsumption(&current_concept, &sup);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// `updatePossibleSubsumers`: for every concept appearing on a node of the
    /// model, harvest or prune its possible subsumers against that node's label.
    /// A concept seen for the first time (`possible` empty) takes the node's whole
    /// label (`readPossibleSubsumersFromNodeLabel`, mirrored to inverses in role
    /// mode via `add_possible_subsumption`); a concept already seen has its possible
    /// subsumers intersected with the label (`prunePossibleSubsumersOfConcept`,
    /// which removes directly and is *not* mirrored).
    fn update_possible_subsumers(&mut self, node_labels: &[HashSet<E>]) {
        for label in node_labels {
            let label: HashSet<E> =
                label.iter().filter(|c| self.elements.contains(c)).cloned().collect();
            for concept in &label {
                if self.possible_subsumptions.successors(concept).is_empty() {
                    for sup in &label {
                        self.add_possible_subsumption(concept, sup);
                    }
                } else {
                    let current = self.possible_subsumptions.get_successors(concept);
                    let to_remove: HashSet<E> =
                        current.into_iter().filter(|s| !label.contains(s)).collect();
                    self.possible_subsumptions.remove_successors(concept, &to_remove);
                }
            }
        }
    }

    /// `prunePossibleSubsumers`: for every concept appearing on a node of the model,
    /// remove from its possible subsumers any candidate not asserted on that node
    /// (`prunePossibleSubsumersOfConcept`). Unlike [`update_possible_subsumers`] this
    /// is prune-only -- it never *adds* a concept's whole node label as fresh
    /// possibles, matching HermiT's `doesSubsume`, which only narrows the already
    /// established possible-subsumer sets.
    fn prune_possible_subsumers(&mut self, node_labels: &[HashSet<E>]) {
        for label in node_labels {
            let label: HashSet<E> =
                label.iter().filter(|c| self.elements.contains(c)).cloned().collect();
            for concept in &label {
                if self.possible_subsumptions.successors(concept).is_empty() {
                    continue;
                }
                let current = self.possible_subsumptions.get_successors(concept);
                let to_remove: HashSet<E> =
                    current.into_iter().filter(|s| !label.contains(s)).collect();
                self.possible_subsumptions.remove_successors(concept, &to_remove);
            }
        }
    }

    /// `buildHierarchyOfUnknownPossible`: the small hierarchy over the unknown
    /// possible subsumers (plus top and bottom), ordered by known subsumption.
    fn build_hierarchy_of_unknown_possible(&self, unknown: &HashSet<E>) -> Hierarchy<E> {
        let mut small: Graph<E> = Graph::new();
        for u0 in unknown {
            small.add_edge(self.bottom_element.clone(), u0.clone());
            small.add_edge(u0.clone(), self.top_element.clone());
            let known = self.all_known_subsumers(u0);
            for u1 in unknown {
                if known.contains(u1) {
                    small.add_edge(u0.clone(), u1.clone());
                }
            }
        }
        let mut with_top_bottom = unknown.clone();
        with_top_bottom.insert(self.bottom_element.clone());
        with_top_bottom.insert(self.top_element.clone());
        self.build_transitively_reduced_hierarchy(&small, &with_top_bottom)
    }

    /// `checkUnknownSubsumersUsingEnhancedTraversal`: walk the small hierarchy top
    /// down, testing `does_subsume(child, picked)` and recording confirmed
    /// subsumptions (with the child node's equivalents).
    fn check_unknown_subsumers_using_enhanced_traversal(
        &mut self,
        hierarchy: &Hierarchy<E>,
        start_node: NodeRef,
        picked: &E,
    ) {
        let mut visited: HashSet<NodeRef> = HashSet::new();
        visited.insert(start_node);
        let mut to_process: VecDeque<NodeRef> = VecDeque::new();
        to_process.push_back(start_node);
        while let Some(current) = to_process.pop_front() {
            let children: Vec<NodeRef> =
                hierarchy.node(current).child_nodes().iter().copied().collect();
            for child in children {
                if visited.contains(&child) {
                    continue;
                }
                let element = hierarchy.node(child).representative().clone();
                // `Relation.doesSubsume` shortcuts (QuasiOrderClassification.classify):
                // an already-known subsumer needs no test, and an element that is not
                // even a possible subsumer of `picked` cannot subsume it.
                let subsumes = if self.all_known_subsumers(picked).contains(&element) {
                    true
                } else if !self.possible_subsumptions.successors(picked).contains(&element) {
                    false
                } else {
                    // `Relation.doesSubsume`: run the tableau test and harvest the
                    // model read-off it produces.
                    let (subsumed, read_off) =
                        self.oracle.does_subsume_with_read_off(&element, picked);
                    if let Some(read_off) = read_off {
                        // Not subsumed: a witnessing model exists. Harvest `picked`'s
                        // deterministic subsumers (readKnownSubsumersFromRootNode) and
                        // prune every concept's possible subsumers against the model
                        // (prunePossibleSubsumers).
                        for sup in &read_off.query_known {
                            if self.elements.contains(sup) {
                                self.add_known_subsumption(picked, sup);
                            }
                        }
                        if let Some(node_labels) = read_off.node_labels {
                            self.prune_possible_subsumers(&node_labels);
                        }
                    }
                    // m_possibleSubsumptions.getSuccessors(picked)
                    //   .removeAll(getAllKnownSubsumers(picked)).
                    let known = self.all_known_subsumers(picked);
                    self.possible_subsumptions.remove_successors(picked, &known);
                    subsumed
                };
                if subsumes {
                    self.add_known_subsumption(picked, &element);
                    let equivalents = hierarchy.node(child).equivalent_elements().clone();
                    self.add_known_subsumptions(picked, &equivalents);
                    if visited.insert(child) {
                        to_process.push_back(child);
                    }
                }
                visited.insert(child);
            }
        }
    }

    /// `isEveryPossibleSubsumerNonSubsumer`: for a small possible-subsumer set
    /// (`lowerBound < size < upperBound`, i.e. 3..=6), a single batched test asks
    /// whether `picked` is subsumed by the union of the unknown possibles. If it
    /// is NOT, none of them subsume `picked`, so the enhanced traversal can be
    /// skipped (the caller clears the possibles afterwards regardless). If it IS,
    /// HermiT reads the deterministic known subsumers off the witnessing model
    /// (`readKnownSubsumersFromRootNode`) and removes the (transitively) known
    /// subsumers from `picked`'s possible set, an answer-neutral optimization that
    /// avoids redundant pairwise subsumption tests in the enhanced traversal. If
    /// the oracle cannot run the batched test, fall back to the traversal.
    fn is_every_possible_subsumer_non_subsumer(
        &mut self,
        unknown: &HashSet<E>,
        picked: &E,
    ) -> bool {
        // `isEveryPossibleSubsumerNonSubsumer(...,2,7)`: only worth a batched
        // satisfiability test for a possible-subsumer set whose size is in (2,7).
        if unknown.len() > 2 && unknown.len() < 7 {
            if let Some(result) = self.oracle.is_subsumed_by_union(picked, unknown) {
                if result.subsumed {
                    // readKnownSubsumersFromRootNode(pickedElement, ...) then
                    // m_possibleSubsumptions.getSuccessors(pickedElement)
                    //   .removeAll(getAllKnownSubsumers(pickedElement)).
                    for sup in &result.query_known {
                        if self.elements.contains(sup) {
                            self.add_known_subsumption(picked, sup);
                        }
                    }
                    let known = self.all_known_subsumers(picked);
                    self.possible_subsumptions.remove_successors(picked, &known);
                }
                return !result.subsumed;
            }
        }
        false
    }

    /// `buildTransitivelyReducedHierarchy`: each element's subsumers are its known
    /// successors plus top and itself; bottom's subsumers are all elements. Then
    /// `DeterministicClassification.buildHierarchy` does the SCC + reduction.
    fn build_transitively_reduced_hierarchy(
        &self,
        known_subsumptions: &Graph<E>,
        elements: &HashSet<E>,
    ) -> Hierarchy<E> {
        self.build_transitively_reduced_hierarchy_with_monitor(
            known_subsumptions,
            elements,
            &mut NoProgressMonitor,
        )
    }

    /// As [`build_transitively_reduced_hierarchy`](Self::build_transitively_reduced_hierarchy),
    /// but fires `monitor` once per element of the subsumer graph (via
    /// `build_hierarchy_with_monitor`). The intermediate hierarchy builds call the
    /// `NoProgressMonitor` variant; only the final result build (in
    /// [`classify_with_monitor`](Self::classify_with_monitor)) passes a real
    /// monitor, so each classified element is reported exactly once.
    fn build_transitively_reduced_hierarchy_with_monitor<M>(
        &self,
        known_subsumptions: &Graph<E>,
        elements: &HashSet<E>,
        monitor: &mut M,
    ) -> Hierarchy<E>
    where
        M: ClassificationProgressMonitor<E> + ?Sized,
    {
        use std::collections::HashMap;
        let mut subsumers: HashMap<E, HashSet<E>> = HashMap::new();
        for element in elements {
            let mut extended = known_subsumptions.get_successors(element);
            extended.insert(self.top_element.clone());
            extended.insert(element.clone());
            subsumers.insert(element.clone(), extended);
        }
        subsumers.insert(self.bottom_element.clone(), elements.clone());
        build_hierarchy_with_monitor(
            self.top_element.clone(),
            self.bottom_element.clone(),
            subsumers,
            monitor,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    /// An in-memory oracle backed by a ground-truth subsumption table:
    /// `truth[x]` is the set of concepts that subsume `x` (reflexive, including
    /// top). `unsat` lists unsatisfiable concepts. `build_model` returns no
    /// deterministic known subsumers (so everything is a *possible* subsumer to be
    /// confirmed by `does_subsume`), exercising the possible-resolution path.
    struct TruthOracle {
        truth: HashMap<&'static str, HashSet<&'static str>>,
        unsat: HashSet<&'static str>,
    }
    impl SubsumptionOracle<&'static str> for TruthOracle {
        fn build_model(&mut self, concept: &&'static str) -> Option<ModelReadOff<&'static str>> {
            if self.unsat.contains(concept) {
                return None;
            }
            // Possible subsumers: every concept's label includes its true
            // subsumers; expose them as "possible" (no deterministic knowns, no
            // cross-concept harvesting).
            let possible: HashSet<&'static str> =
                self.truth.get(concept).cloned().unwrap_or_default();
            Some(ModelReadOff {
                query_known: HashSet::new(),
                query_possible: possible,
                node_labels: None,
            })
        }
        fn does_subsume(&mut self, parent: &&'static str, child: &&'static str) -> bool {
            self.truth.get(child).map_or(false, |s| s.contains(parent))
        }
        fn is_subsumed_by_union(
            &mut self,
            child: &&'static str,
            candidates: &HashSet<&'static str>,
        ) -> Option<UnionTestResult<&'static str>> {
            // In the single ground-truth model, `child` is subsumed by the union
            // iff at least one candidate actually subsumes it. This oracle exposes
            // no deterministic known subsumers off the witnessing model.
            let subsumers = self.truth.get(child).cloned().unwrap_or_default();
            Some(UnionTestResult {
                subsumed: candidates.iter().any(|c| subsumers.contains(c)),
                query_known: HashSet::new(),
            })
        }
    }

    // The batched test returns "all non-subsumers" exactly when `picked` is not
    // subsumed by the union of the unknown possibles (3..=6 of them, top excluded).
    #[test]
    fn batched_non_subsumer_test() {
        let mut truth: HashMap<&str, HashSet<&str>> = HashMap::new();
        truth.insert("A", ["A", "B", "top"].into_iter().collect());
        let oracle = TruthOracle { truth, unsat: HashSet::new() };
        let elements: HashSet<&str> =
            ["top", "A", "B", "C", "D", "E", "bottom"].into_iter().collect();
        let mut classifier = QuasiOrderClassification::new(oracle, "top", "bottom", elements);
        // None of C, D, E subsume A -> every possible subsumer is a non-subsumer.
        let none: HashSet<&str> = ["C", "D", "E"].into_iter().collect();
        assert!(classifier.is_every_possible_subsumer_non_subsumer(&none, &"A"));
        // B subsumes A -> not every possible is a non-subsumer.
        let some: HashSet<&str> = ["B", "C", "D"].into_iter().collect();
        assert!(!classifier.is_every_possible_subsumer_non_subsumer(&some, &"A"));
        // Outside the (2,7) size window, the batched test is not used.
        let pair: HashSet<&str> = ["C", "D"].into_iter().collect();
        assert!(!classifier.is_every_possible_subsumer_non_subsumer(&pair, &"A"));
        // top among the unknowns -> skip the batched test (top trivially subsumes).
        let with_top: HashSet<&str> = ["top", "C", "D"].into_iter().collect();
        assert!(!classifier.is_every_possible_subsumer_non_subsumer(&with_top, &"A"));
    }

    #[test]
    fn classifies_a_chain_via_possible_resolution() {
        // A ⊑ B ⊑ C, all satisfiable. truth[x] = subsumers of x (incl. top, self).
        let mut truth: HashMap<&str, HashSet<&str>> = HashMap::new();
        truth.insert("top", ["top"].into_iter().collect());
        truth.insert("C", ["C", "top"].into_iter().collect());
        truth.insert("B", ["B", "C", "top"].into_iter().collect());
        truth.insert("A", ["A", "B", "C", "top"].into_iter().collect());
        truth.insert("bottom", ["bottom", "A", "B", "C", "top"].into_iter().collect());

        let oracle = TruthOracle { truth, unsat: HashSet::new() };
        let elements: HashSet<&str> = ["top", "A", "B", "C", "bottom"].into_iter().collect();
        let classifier = QuasiOrderClassification::new(oracle, "top", "bottom", elements);
        let hierarchy = classifier.classify();

        let a = hierarchy.node_for_element(&"A").unwrap();
        let b = hierarchy.node_for_element(&"B").unwrap();
        let c = hierarchy.node_for_element(&"C").unwrap();
        // A < B < C in the ancestor relation.
        assert!(hierarchy.ancestor_nodes(a).contains(&b));
        assert!(hierarchy.ancestor_nodes(b).contains(&c));
        assert!(hierarchy.ancestor_nodes(a).contains(&c));
        // Transitive reduction: B is a direct child of C, A is not.
        assert!(hierarchy.node(c).child_nodes().contains(&b));
        assert!(!hierarchy.node(c).child_nodes().contains(&a));
    }

    #[test]
    fn unsatisfiable_concept_goes_to_bottom() {
        // A ⊑ B, but A is unsatisfiable -> A collapses into the bottom node.
        let mut truth: HashMap<&str, HashSet<&str>> = HashMap::new();
        truth.insert("top", ["top"].into_iter().collect());
        truth.insert("B", ["B", "top"].into_iter().collect());
        truth.insert("A", ["A", "B", "top"].into_iter().collect());
        truth.insert("bottom", ["bottom", "A", "B", "top"].into_iter().collect());

        let oracle = TruthOracle {
            truth,
            unsat: ["A"].into_iter().collect(),
        };
        let elements: HashSet<&str> = ["top", "A", "B", "bottom"].into_iter().collect();
        let classifier = QuasiOrderClassification::new(oracle, "top", "bottom", elements);
        let hierarchy = classifier.classify();

        assert_eq!(
            hierarchy.node_for_element(&"A").unwrap(),
            hierarchy.bottom_node()
        );
    }

    #[test]
    fn role_mode_mirrors_subsumptions_to_inverses() {
        // Roles r ⊑ s with inverses r⁻, s⁻. Concepts: r, s, ri (=r⁻), si (=s⁻).
        // A told inclusion r ⊑ s must also yield r⁻ ⊑ s⁻ via the inverse mirror.
        let mut truth: HashMap<&str, HashSet<&str>> = HashMap::new();
        truth.insert("top", ["top"].into_iter().collect());
        truth.insert("s", ["s", "top"].into_iter().collect());
        truth.insert("si", ["si", "top"].into_iter().collect());
        truth.insert("r", ["r", "s", "top"].into_iter().collect());
        truth.insert("ri", ["ri", "si", "top"].into_iter().collect());
        truth.insert("bottom", ["bottom", "r", "s", "ri", "si", "top"].into_iter().collect());
        let oracle = TruthOracle { truth, unsat: HashSet::new() };

        let mut inverse: HashMap<&str, &str> = HashMap::new();
        inverse.insert("r", "ri");
        inverse.insert("ri", "r");
        inverse.insert("s", "si");
        inverse.insert("si", "s");

        let elements: HashSet<&str> =
            ["top", "r", "s", "ri", "si", "bottom"].into_iter().collect();
        let mut classifier = QuasiOrderClassification::new_for_roles(
            oracle,
            "top",
            "bottom",
            elements,
            Some(inverse),
        );
        // Told: r ⊑ s (same arguments). The mirror should add r⁻ ⊑ s⁻ as well.
        classifier.initialise_known_subsumptions_for_roles(&[("r", "s", false)]);
        let hierarchy = classifier.classify();

        let r = hierarchy.node_for_element(&"r").unwrap();
        let s = hierarchy.node_for_element(&"s").unwrap();
        let ri = hierarchy.node_for_element(&"ri").unwrap();
        let si = hierarchy.node_for_element(&"si").unwrap();
        assert!(hierarchy.ancestor_nodes(r).contains(&s), "r ⊑ s");
        assert!(hierarchy.ancestor_nodes(ri).contains(&si), "r⁻ ⊑ s⁻ (mirrored)");
    }

    #[test]
    fn equivalent_concepts_share_a_node() {
        // P ≡ Q (each subsumes the other), unrelated to the rest.
        let mut truth: HashMap<&str, HashSet<&str>> = HashMap::new();
        truth.insert("top", ["top"].into_iter().collect());
        truth.insert("P", ["P", "Q", "top"].into_iter().collect());
        truth.insert("Q", ["Q", "P", "top"].into_iter().collect());
        truth.insert("bottom", ["bottom", "P", "Q", "top"].into_iter().collect());

        let oracle = TruthOracle { truth, unsat: HashSet::new() };
        let elements: HashSet<&str> = ["top", "P", "Q", "bottom"].into_iter().collect();
        let classifier = QuasiOrderClassification::new(oracle, "top", "bottom", elements);
        let hierarchy = classifier.classify();

        assert_eq!(
            hierarchy.node_for_element(&"P").unwrap(),
            hierarchy.node_for_element(&"Q").unwrap()
        );
    }
}
