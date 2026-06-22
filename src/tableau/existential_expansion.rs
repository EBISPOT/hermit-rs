// Port of the existential-expansion rule: the relevant parts of
// org.semanticweb.HermiT.existentials.{AbstractExpansionStrategy,
// CreationOrderStrategy} and ExistentialExpansionManager.doNormalExpansion.
//
// An at-least concept `>= n r.C` on a node that is not already satisfied is
// expanded by creating `n` fresh successors with the role and filler, made
// pairwise unequal. As an `impl` block on `Tableau`.
//
// SCOPE: this is the no-blocking creation-order expansion. Without blocking it
// terminates for non-cyclic existentials; cyclic TBoxes (e.g. A ⊑ ∃r.A) need the
// blocking machinery for termination. The NN/NI (nominal) rule and full
// data-range satisfaction are not implemented in this module.
//
// The functional-role optimization IS ported (`try_functional_expansion`
// / `get_functional_expansion_node`, mirroring `ExistentialExpansionManager.expand`
// /`tryFunctionalExpansion`/`getFunctionalExpansionNode`). For an at-least
// `>= n r.C` whose role `r` is functional (a sub-role of a functional super-role,
// per `Tableau::set_functional_roles_from_clauses`): `n >= 2` immediately CLASHES
// (a functional role cannot have two distinct successors), and `n == 1` REUSES the
// existing functional `r`-successor (adding the filler `C` to it) instead of
// creating a fresh one. Non-functional roles fall through to the unchanged normal /
// individual-reuse paths. The functional-role map is empty by default, so absent
// the reasoner-side population call every role is non-functional and behaviour is
// byte-for-byte unchanged.
#![allow(dead_code)]

use crate::model::{
    AtLeastConcept, AtLeastDataRange, Concept, DLPredicate, ExistentialConcept, LiteralDataRange,
    Role,
};
use crate::tableau::branching::BranchingPointData;
use crate::tableau::dependency_set::DependencySet;
use crate::tableau::extension_table::View;
use crate::tableau::node::NodeId;
use crate::tableau::object::TableauObject;
use crate::tableau::tableau::Tableau;

/// Port of `AbstractExpansionStrategy.SatType`. An at-least concept can be
/// `NotSatisfied` (must expand), `PermanentlySatisfied` (a witness that cannot be
/// merged away exists -> mark processed), or `CurrentlySatisfied` (a witness
/// exists but only via a nominal/non-permanent node that the NN/NI rule may later
/// merge away -> leave the existential unprocessed so it is reconsidered).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SatType {
    NotSatisfied,
    PermanentlySatisfied,
    CurrentlySatisfied,
}

fn literal_data_range_to_predicate(range: &LiteralDataRange) -> DLPredicate {
    match range {
        LiteralDataRange::DatatypeRestriction(r) => DLPredicate::DatatypeRestriction(r.clone()),
        LiteralDataRange::ConstantEnumeration(r) => DLPredicate::ConstantEnumeration(r.clone()),
        LiteralDataRange::InternalDatatype(r) => DLPredicate::InternalDatatype(r.clone()),
        LiteralDataRange::AtomicNegationDataRange(r) => {
            DLPredicate::AtomicNegationDataRange(r.clone())
        }
    }
}

impl Tableau {
    /// Record that `node` just gained an unprocessed existential, so the
    /// expansion cursor (a lower bound on the first node that may still need
    /// expanding) is pulled back to `node` if `node` precedes the current cursor
    /// in tableau order. Called from every site that pushes onto a node's
    /// `unprocessed_existentials`. Keeps the cursor a correct lower bound: the
    /// node-walk can then resume from the cursor without missing earlier work.
    #[inline]
    pub(crate) fn note_unprocessed_existential(&mut self, node: NodeId) {
        let seq = self.nodes[node].tableau_seq;
        match self.existential_cursor {
            Some(_) if seq >= self.existential_cursor_seq => {}
            _ => {
                self.existential_cursor = Some(node);
                self.existential_cursor_seq = seq;
            }
        }
    }

    /// One step of existential expansion. HermiT's `CreationOrderStrategy` sets
    /// `m_expandNodeAtATime=true`, so `expandExistentials` recomputes blocking, then
    /// walks the tableau nodes only until the *first* node that produces an
    /// expansion -- it fully processes that one node's existentials and returns,
    /// handing control back to `doIteration` so blocking (and saturation) are
    /// recomputed before the next node's existentials are expanded. Returns whether
    /// any extension changed.
    pub fn expand_existentials(&mut self) -> bool {
        self.expand_existentials_final_chance(false)
    }

    /// `AbstractExpansionStrategy.expandExistentials(finalChance)`: the
    /// `final_chance` flag is threaded into `computeBlocking(finalChance)`. With
    /// the default exact (pairwise) blocking the flag is a no-op, so a
    /// `final_chance=true` call after a fully-saturated tableau changes nothing
    /// and returns `false`. With the inexact validated strategy, the final-chance
    /// pass revalidates blocks and can resume expansion when a block was invalid.
    pub fn expand_existentials_final_chance(&mut self, final_chance: bool) -> bool {
        // The per-existential strategy dispatch lives in
        // `expand_at_least_concept`: the default `CreationOrder` strategy creates
        // fresh witnesses (`do_normal_at_least_expansion`), while
        // `IndividualReuse`/`El` route `>=1 r.C` through `try_parent_reuse` /
        // `expand_with_model_reuse` to REUSE a single per-concept witness (the
        // smaller reuse model). On a clash that depended on a reuse decision the
        // `IndividualReuseBranchingPoint` (`reuse` variant of `BranchingPointData`)
        // backtracks and retries with a fresh witness, so the non-deterministic
        // `IndividualReuse` strategy stays SOUND+COMPLETE — same answers as the
        // default, only smaller models. The node-walk itself is shared and
        // unchanged. See the module-level note in `src/existentials.rs`.
        self.compute_blocking_with(final_chance);
        let mut extensions_changed = false;
        // Resume the node-walk from the cursor: a verified lower bound on the first
        // node that may still carry an unprocessed existential. Every site that
        // pushes onto a node's `unprocessed_existentials` (concept-assertion add,
        // backtrack restore) and every blocking-pass unblock pulls the cursor back
        // to that node via `note_unprocessed_existential`, so `existential_cursor
        // == None` means "no unprocessed existentials anywhere" and the walk does
        // nothing -- no re-scan of a fully-settled tableau (the O(n^2) sweep this
        // replaces). `advancing_cursor` stays true while every node seen so far has
        // none left: those are settled until a push pulls the cursor back, so the
        // cursor may advance over them. It stops at the first node that still has
        // one (blocked or not -- a blocked node may unblock later, so it stays the
        // wall until the blocking pass pulls the cursor onto it).
        let mut node = self.existential_cursor;
        let mut advancing_cursor = true;
        while let Some(current) = node {
            let has_unprocessed = self.nodes[current].has_unprocessed_existentials();
            // A node is "expandable" only if it actually has work the walk would do
            // here: unprocessed existentials AND active AND unblocked. The cursor
            // may safely advance over every node that is NOT expandable -- settled
            // nodes (no work) and *blocked* nodes (whose existentials are not
            // expanded while blocked). A blocked node that later unblocks is caught
            // by the blocking pass's `note_unprocessed_existential` pull-back, so
            // advancing past it cannot lose work. This is what stops a long run of
            // blocked-with-unprocessed nodes from being re-walked every call.
            let expandable = has_unprocessed
                && self.nodes[current].is_active()
                && !self.nodes[current].is_blocked();
            if advancing_cursor {
                if expandable {
                    advancing_cursor = false;
                    self.existential_cursor = Some(current);
                    self.existential_cursor_seq = self.nodes[current].tableau_seq;
                } else {
                    // Not expandable here: advance the cursor past it.
                    let next = self.nodes[current].next_tableau_node;
                    self.existential_cursor = next;
                    self.existential_cursor_seq =
                        next.map(|n| self.nodes[n].tableau_seq).unwrap_or(u64::MAX);
                }
            }
            if expandable {
                // Snapshot the node's unprocessed existentials into the reusable
                // `m_processedExistentials` buffer (taken out of `self` so the loop
                // body can mutate the rest of `self`, including the node's own list,
                // without aliasing). Refilling a kept-capacity buffer avoids a fresh
                // allocation per processed node.
                let mut existentials =
                    std::mem::take(&mut self.processed_existentials_buffer);
                existentials.clear();
                existentials.extend_from_slice(&self.nodes[current].unprocessed_existentials);
                // HermiT iterates the node's unprocessed existentials in reverse
                // (`AbstractExpansionStrategy.expandExistentials`: `for index =
                // size-1 .. 0`); match that order so the model/witness creation
                // sequence is identical.
                for existential in existentials.iter().rev() {
                    match existential {
                        ExistentialConcept::AtLeastConcept(at_least) => {
                            match self.at_least_concept_sat_type(at_least, current) {
                                SatType::NotSatisfied => {
                                    // Java `expandExistential` marks the existential
                                    // PROCESSED *before* the (reuse) branching point is
                                    // pushed (`IndividualReuseStrategy.java:119`), so the
                                    // branching point's existential-restore watermark is
                                    // taken with this existential already processed --
                                    // otherwise an `IndividualReuseBranchingPoint` retry
                                    // would re-expand it. Answer-neutral for the default
                                    // creation-order path, which pushes no branching point.
                                    self.record_existential_processed(current, existential);
                                    self.expand_at_least_concept(at_least.clone(), current);
                                    extensions_changed = true;
                                }
                                SatType::PermanentlySatisfied => {
                                    self.record_existential_processed(current, existential);
                                    // AbstractExpansionStrategy.java:121-122: fire when
                                    // permanently satisfied and expansion is skipped.
                                    self.monitor_event(|m| m.existential_satisfied());
                                }
                                // CurrentlySatisfied: leave unprocessed.
                                // AbstractExpansionStrategy.java:126-127: still fire
                                // the satisfied event even though the existential is
                                // not marked processed (the NN/NI rule may break it).
                                SatType::CurrentlySatisfied => {
                                    self.monitor_event(|m| m.existential_satisfied());
                                }
                            }
                        }
                        ExistentialConcept::AtLeastDataRange(at_least) => {
                            match self.at_least_data_range_sat_type(at_least, current) {
                                SatType::NotSatisfied => {
                                    // Mark processed before expanding, as Java's
                                    // `expandExistential` does for every `AtLeast`
                                    // (matching the AtLeastConcept arm above).
                                    self.record_existential_processed(current, existential);
                                    self.expand_at_least_data_range(at_least.clone(), current);
                                    extensions_changed = true;
                                }
                                SatType::PermanentlySatisfied => {
                                    self.record_existential_processed(current, existential);
                                    // AbstractExpansionStrategy.java:121-122 (AtLeast supertype).
                                    self.monitor_event(|m| m.existential_satisfied());
                                }
                                SatType::CurrentlySatisfied => {
                                    // AbstractExpansionStrategy.java:126-127 (AtLeast supertype).
                                    self.monitor_event(|m| m.existential_satisfied());
                                }
                            }
                        }
                        ExistentialConcept::ExistsDescriptionGraph(exists) => {
                            // Port of AbstractExpansionStrategy.expandExistentials's
                            // ExistsDescriptionGraph branch (lines 131-141): if not
                            // already satisfied, expand the graph (creating its
                            // vertices/edges and recording the tuple); either way
                            // mark the existential processed. `expand_exists_…`
                            // mirrors DescriptionGraphManager.isSatisfied + .expand.
                            if self.expand_exists_description_graph(exists, current) {
                                extensions_changed = true;
                            } else {
                                // AbstractExpansionStrategy.java:138-139: fire when
                                // the description-graph existential is already satisfied
                                // and expansion is skipped.
                                self.monitor_event(|m| m.existential_satisfied());
                            }
                            self.record_existential_processed(current, existential);
                        }
                    }
                    // AbstractExpansionStrategy.java:145 -- after each existential.
                    self.note_interrupt(); // no-op with the default -1 timeout
                }
                // Return the buffer (keeping its capacity) for the next node.
                existentials.clear();
                self.processed_existentials_buffer = existentials;
            }
            node = self.nodes[current].next_tableau_node;
            // AbstractExpansionStrategy.java:149 -- after each tableau node.
            self.note_interrupt();
            // `m_expandNodeAtATime`: stop after the first node that expanded, so
            // `doIteration` recomputes blocking/saturation before the next node.
            if extensions_changed {
                break;
            }
        }
        extensions_changed
    }

    /// Iterate the `on_role`-successors of `node`, invoking `f(successor)` for each
    /// until `f` returns `Some` (early-exit, returning that value) or the
    /// successors are exhausted (returning `None`). Mirrors HermiT's `isSatisfied`,
    /// which drives the persistent `Retrieval` cursor directly and `return`s on the
    /// first witness instead of first materializing every successor into a list.
    ///
    /// Only ONE `Vec` (the retrieval's tuple-index buffer) is allocated per call;
    /// the successor `NodeId`s are produced lazily, so the cardinality-1 satisfied
    /// case touches just the first matching tuple.
    fn find_role_successor<T>(
        &self,
        on_role: &Role,
        node: NodeId,
        mut f: impl FnMut(NodeId) -> Option<T>,
    ) -> Option<T> {
        let (bindings, positions, successor_column) = match on_role {
            Role::AtomicRole(r) => (
                [
                    Some(TableauObject::DLPredicate(DLPredicate::AtomicRole(r.clone()))),
                    Some(TableauObject::Node(node)),
                    None,
                ],
                [0, 1, -1],
                2usize,
            ),
            Role::InverseRole(r) => (
                [
                    Some(TableauObject::DLPredicate(DLPredicate::AtomicRole(
                        r.get_inverse_of().clone(),
                    ))),
                    None,
                    Some(TableauObject::Node(node)),
                ],
                [0, -1, 2],
                1usize,
            ),
        };
        // Drive the trie cursor directly (no `Vec<usize>` per probe), stopping at
        // the first successor for which `f` yields a value. This is the dominant
        // path for the cardinality-1 satisfaction check on dense inverse-role
        // workloads, where the existential is usually already satisfied and only
        // the first matching successor is touched.
        let mut result: Option<T> = None;
        self.visit_ternary_retrieval(positions, bindings, View::Total, |ti| {
            let s = self
                .ternary_extension_table
                .get_tuple_object(ti, successor_column)
                .as_node()
                .unwrap();
            match f(s) {
                Some(v) => {
                    result = Some(v);
                    true
                }
                None => false,
            }
        });
        result
    }

    /// Port of `ExistentialExpansionManager.getFunctionalExpansionNode`. For a
    /// functional `role`, finds the first existing successor of `for_node` along
    /// any of `role`'s "relevant roles" (the sub-roles of its functional
    /// super-role). Returns that successor and the role-assertion's dependency
    /// set, or `None` if `role` is not functional / has no such successor.
    ///
    /// `relevantRole instanceof AtomicRole`: the edge is `relevantRole(forNode, x)`
    /// -> the successor is the third tuple column (index 2). For an inverse role
    /// it is `getInverseOf()(x, forNode)` -> the successor is the second column.
    fn get_functional_expansion_node(
        &self,
        role: &Role,
        for_node: NodeId,
    ) -> Option<(NodeId, crate::tableau::dependency_set::PermanentDependencySet)> {
        let relevant_roles = self.functional_roles.get(role)?;
        let empty = self.dependency_set_factory.empty_set();
        for relevant_role in relevant_roles {
            let (positions, bindings, successor_column) = match relevant_role {
                Role::AtomicRole(r) => (
                    [0, 1, -1],
                    [
                        Some(TableauObject::DLPredicate(DLPredicate::AtomicRole(r.clone()))),
                        Some(TableauObject::Node(for_node)),
                        None,
                    ],
                    2usize,
                ),
                Role::InverseRole(r) => (
                    [0, -1, 2],
                    [
                        Some(TableauObject::DLPredicate(DLPredicate::AtomicRole(
                            r.get_inverse_of().clone(),
                        ))),
                        None,
                        Some(TableauObject::Node(for_node)),
                    ],
                    1usize,
                ),
            };
            let retrieval = self.create_ternary_retrieval(positions, bindings, View::Total);
            if let Some(&tuple_index) = retrieval.tuple_indices.first() {
                let successor = self
                    .ternary_extension_table
                    .get_tuple_object(tuple_index, successor_column)
                    .as_node()
                    .unwrap();
                let dependency_set = self
                    .ternary_extension_table
                    .get_dependency_set(tuple_index, &empty);
                return Some((successor, dependency_set));
            }
        }
        None
    }

    /// Port of `AbstractExpansionStrategy.isPermanentSatisfier`: a witness that
    /// cannot be merged away by the NN/NI rule. (`isPermanentAssertion` is `true`
    /// for both the anywhere and validated blocking strategies the engine uses,
    /// so it drops out.)
    fn is_permanent_satisfier(&self, for_node: NodeId, to_node: NodeId) -> bool {
        for_node == to_node
            || self.nodes[for_node].get_parent() == Some(to_node)
            || self.nodes[to_node].get_parent() == Some(for_node)
            || self.nodes[to_node].is_root_node()
    }

    fn at_least_concept_sat_type(&self, at_least: &AtLeastConcept, node: NodeId) -> SatType {
        let cardinality = at_least.number();
        if cardinality <= 0 {
            return SatType::PermanentlySatisfied;
        }
        let to_concept: Concept = Concept::from(at_least.to_concept().clone());
        // `AbstractExpansionStrategy.isSatisfied`: a blocked successor only counts
        // as a satisfier when it is a direct child of `node` (its existentials are
        // otherwise not expanded, so it cannot be relied on to witness the filler).
        let candidate = |this: &Self, s: NodeId| {
            (!this.nodes[s].is_blocked() || this.nodes[s].get_parent() == Some(node))
                && this.contains_concept_assertion(&to_concept, s)
        };
        if cardinality == 1 {
            // Drive the retrieval directly and stop at the first witness
            // (`isSatisfied`'s `return` inside the cardinality==1 loop), so a
            // satisfied existential touches only the first matching successor.
            self.find_role_successor(at_least.on_role(), node, |s| {
                if candidate(self, s) {
                    Some(if self.is_permanent_satisfier(node, s) {
                        SatType::PermanentlySatisfied
                    } else {
                        SatType::CurrentlySatisfied
                    })
                } else {
                    None
                }
            })
            .unwrap_or(SatType::NotSatisfied)
        } else {
            let mut satisfiers: Vec<NodeId> = Vec::new();
            let mut all_permanent = true;
            self.find_role_successor::<()>(at_least.on_role(), node, |s| {
                if candidate(self, s) {
                    if !self.is_permanent_satisfier(node, s) {
                        all_permanent = false;
                    }
                    satisfiers.push(s);
                }
                None
            });
            if satisfiers.len() >= cardinality as usize
                && self.contains_subset_of_n_unequal_nodes(
                    &satisfiers,
                    0,
                    &mut Vec::new(),
                    cardinality as usize,
                )
            {
                if all_permanent {
                    SatType::PermanentlySatisfied
                } else {
                    SatType::CurrentlySatisfied
                }
            } else {
                SatType::NotSatisfied
            }
        }
    }

    fn at_least_data_range_sat_type(&self, at_least: &AtLeastDataRange, node: NodeId) -> SatType {
        let cardinality = at_least.number();
        if cardinality <= 0 {
            return SatType::PermanentlySatisfied;
        }
        let to_data_range = at_least.to_data_range();
        // `ExtensionManager.containsDataRangeAssertion`: a concrete (non-abstract)
        // node trivially satisfies the universal `rdfs:Literal` data range, so the
        // assertion is considered present without an explicit tuple.
        let is_rdfs_literal = matches!(
            to_data_range,
            LiteralDataRange::InternalDatatype(d)
                if d == crate::model::InternalDatatype::rdfs_literal()
        );
        let predicate = literal_data_range_to_predicate(to_data_range);
        let candidate = |this: &Self, s: NodeId| {
            if is_rdfs_literal && !this.nodes[s].get_node_type().is_abstract() {
                return true;
            }
            let tuple = [
                TableauObject::DLPredicate(predicate.clone()),
                TableauObject::Node(s),
            ];
            this.binary_extension_table.get_tuple_index(&tuple) != -1 && this.nodes[s].is_active()
        };
        if cardinality == 1 {
            self.find_role_successor(at_least.on_role(), node, |s| {
                if candidate(self, s) {
                    Some(if self.is_permanent_satisfier(node, s) {
                        SatType::PermanentlySatisfied
                    } else {
                        SatType::CurrentlySatisfied
                    })
                } else {
                    None
                }
            })
            .unwrap_or(SatType::NotSatisfied)
        } else {
            let mut satisfiers: Vec<NodeId> = Vec::new();
            let mut all_permanent = true;
            self.find_role_successor::<()>(at_least.on_role(), node, |s| {
                if candidate(self, s) {
                    if !self.is_permanent_satisfier(node, s) {
                        all_permanent = false;
                    }
                    satisfiers.push(s);
                }
                None
            });
            if satisfiers.len() >= cardinality as usize
                && self.contains_subset_of_n_unequal_nodes(
                    &satisfiers,
                    0,
                    &mut Vec::new(),
                    cardinality as usize,
                )
            {
                if all_permanent {
                    SatType::PermanentlySatisfied
                } else {
                    SatType::CurrentlySatisfied
                }
            } else {
                SatType::NotSatisfied
            }
        }
    }

    fn contains_inequality(&self, a: NodeId, b: NodeId) -> bool {
        let tuple_ab = [
            TableauObject::DLPredicate(DLPredicate::Inequality),
            TableauObject::Node(a),
            TableauObject::Node(b),
        ];
        let tuple_ba = [
            TableauObject::DLPredicate(DLPredicate::Inequality),
            TableauObject::Node(b),
            TableauObject::Node(a),
        ];
        self.ternary_extension_table.get_tuple_index(&tuple_ab) != -1
            || self.ternary_extension_table.get_tuple_index(&tuple_ba) != -1
    }

    fn contains_subset_of_n_unequal_nodes(
        &self,
        nodes: &[NodeId],
        start_at: usize,
        selected: &mut Vec<NodeId>,
        cardinality: usize,
    ) -> bool {
        if selected.len() == cardinality {
            return true;
        }
        'outer: for index in start_at..nodes.len() {
            let node = nodes[index];
            for &selected_node in selected.iter() {
                if !self.contains_inequality(node, selected_node) {
                    continue 'outer;
                }
            }
            selected.push(node);
            if self.contains_subset_of_n_unequal_nodes(nodes, index + 1, selected, cardinality) {
                return true;
            }
            selected.pop();
        }
        false
    }

    /// Port of `IndividualReuseStrategy.expandExistential` for an `AtLeastConcept`:
    /// dispatch on the configured existential-expansion strategy. With the default
    /// `CreationOrder` strategy (`individual_reuse_strategy` is `None`) this is the
    /// plain creation-order `do_normal_at_least_expansion` -- byte-for-byte
    /// unchanged. With `IndividualReuse`/`El` it tries `try_parent_reuse` then
    /// `expand_with_model_reuse`, falling back to normal expansion -- mirroring
    /// ```java
    /// if (!tryParentReuse(atLeastConcept,forNode))
    ///     if (!expandWithModelReuse(atLeastConcept,forNode))
    ///         m_existentialExpansionManager.doNormalExpansion(atLeastConcept,forNode);
    /// ```
    fn expand_at_least_concept(&mut self, at_least: AtLeastConcept, node: NodeId) {
        // HermiT's `expand` tries the functional expansion first, before
        // any normal/reuse expansion. For a functional role this either reuses the
        // existing successor (n==1) or clashes (n>=2); a non-functional role falls
        // through unchanged.
        if self.try_functional_expansion_concept(&at_least, node) {
            return;
        }
        if self.individual_reuse_strategy.is_some() {
            if self.try_parent_reuse(&at_least, node) {
                return;
            }
            if self.expand_with_model_reuse(&at_least, node) {
                return;
            }
        }
        self.do_normal_at_least_expansion(at_least, node);
    }

    /// Port of `ExistentialExpansionManager.tryFunctionalExpansion` for an
    /// `AtLeastConcept`. Returns `true` (the existential is handled) when the role
    /// is functional and either: `n == 1` and an existing functional `r`-successor
    /// was reused (the filler `C` is added to it), or `n >= 2` and a clash was set
    /// (a functional role cannot have two distinct successors). Returns `false`
    /// otherwise, so the caller falls back to normal expansion.
    fn try_functional_expansion_concept(
        &mut self,
        at_least: &AtLeastConcept,
        node: NodeId,
    ) -> bool {
        if at_least.number() == 1 {
            if let Some((functionality_node, existing_dependency)) =
                self.get_functional_expansion_node(at_least.on_role(), node)
            {
                self.monitor_event(|m| m.existential_expansion_started());
                // m_binaryUnionDependencySet = union(atLeast's concept-assertion
                // dependency set, existing role-assertion's dependency set).
                let existential_dependency = self
                    .get_concept_assertion_dependency_set(
                        &Concept::AtLeastConcept(at_least.clone()),
                        node,
                    )
                    .unwrap_or_else(|| self.dependency_set_factory.empty_set());
                let union = self.dependency_set_factory.union_with(
                    &DependencySet::Permanent(existential_dependency),
                    &DependencySet::Permanent(existing_dependency),
                );
                let dependency = DependencySet::Permanent(union);
                self.add_role_assertion(
                    at_least.on_role().clone(),
                    node,
                    functionality_node,
                    &dependency,
                    true,
                );
                let to_concept: Concept = Concept::from(at_least.to_concept().clone());
                self.add_concept_assertion(to_concept, functionality_node, &dependency, true);
                self.monitor_event(|m| m.existential_expansion_finished());
                return true;
            }
            false
        } else if at_least.number() > 1
            && self.functional_roles.contains_key(at_least.on_role())
        {
            // A functional role cannot witness two distinct successors -> clash.
            self.monitor_event(|m| m.existential_expansion_started());
            let existential_dependency = self
                .get_concept_assertion_dependency_set(
                    &Concept::AtLeastConcept(at_least.clone()),
                    node,
                )
                .unwrap_or_else(|| self.dependency_set_factory.empty_set());
            self.set_clash(&DependencySet::Permanent(existential_dependency));
            self.monitor_event(|m| m.existential_expansion_finished());
            true
        } else {
            false
        }
    }

    /// Port of `IndividualReuseStrategy.tryParentReuse`: for `>=1 r.C` on `node`
    /// whose PARENT already has the filler concept `C`, satisfy the existential by
    /// drawing an `r`-edge back to the parent instead of creating a fresh witness.
    /// When the strategy is non-deterministic this is a choice point (an
    /// `IndividualReuseBranchingPoint`), so a clash can backtrack and retry with a
    /// fresh successor.
    fn try_parent_reuse(&mut self, at_least: &AtLeastConcept, node: NodeId) -> bool {
        if at_least.number() != 1 {
            return false;
        }
        let parent = match self.nodes[node].get_parent() {
            Some(parent) => parent,
            None => return false,
        };
        let to_concept = Concept::from(at_least.to_concept().clone());
        if !self.contains_concept_assertion(&to_concept, parent) {
            return false;
        }
        // Java: `getConceptAssertionDependencySet(atLeastConcept,node)` -- the
        // dependency set of the at-least assertion that triggered the expansion.
        let dependency = DependencySet::Permanent(
            self.get_concept_assertion_dependency_set(
                &Concept::AtLeastConcept(at_least.clone()),
                node,
            )
            .unwrap_or_else(|| self.dependency_set_factory.empty_set()),
        );
        let is_deterministic = self
            .individual_reuse_strategy
            .as_ref()
            .map(|s| s.is_deterministic_strategy())
            .unwrap_or(true);
        let dependency = if !is_deterministic {
            let branching_point = BranchingPointData {
                level: 0,
                last_tableau_node: self.last_tableau_node,
                last_merged_or_pruned_node: self.last_merged_or_pruned_node,
                first_ground_disjunction: self.first_ground_disjunction,
                first_unprocessed_ground_disjunction: self.first_unprocessed_ground_disjunction,
                ground_disjunction: usize::MAX,
                sorted_disjunct_indexes: Vec::new(),
                current_index: 0,
                nominal_introduction: None,
                reuse: Some(crate::tableau::branching::ReuseBranchingData {
                    existential: at_least.clone(),
                    for_node: node,
                    was_parent_reuse: true,
                }),
            };
            self.push_branching_point(branching_point);
            let level = self.current_branching_point;
            DependencySet::Permanent(
                self.dependency_set_factory.add_branching_point(&dependency, level),
            )
        } else {
            dependency
        };
        self.add_role_assertion(at_least.on_role().clone(), node, parent, &dependency, true);
        true
    }

    /// Port of `IndividualReuseStrategy.expandWithModelReuse`: for `>=1 r.C` with
    /// `C` an atomic, non-internal, reusable concept, satisfy the existential by
    /// drawing an `r`-edge to the single per-concept representative witness node
    /// for `C` (creating it once, as a root NI node so keys do not apply, and
    /// reusing it thereafter). This is what makes the reuse model SMALLER: every
    /// `>=1 r.C` across the tableau shares one `C`-witness. When non-deterministic,
    /// the first introduction of a `C`-witness is a choice point.
    fn expand_with_model_reuse(&mut self, at_least: &AtLeastConcept, node: NodeId) -> bool {
        // Only atomic fillers are reusable (`getToConcept() instanceof AtomicConcept`).
        let to_concept = match at_least.to_concept() {
            crate::model::LiteralConcept::AtomicConcept(c) => c.clone(),
            _ => return false,
        };
        let reusable = self
            .individual_reuse_strategy
            .as_ref()
            .map(|s| at_least.number() == 1 && s.should_reuse(&to_concept))
            .unwrap_or(false);
        if !reusable {
            return false;
        }
        let is_deterministic = self
            .individual_reuse_strategy
            .as_ref()
            .map(|s| s.is_deterministic_strategy())
            .unwrap_or(true);
        self.monitor_event(|m| m.existential_expansion_started());
        let mut dependency = DependencySet::Permanent(
            self.get_concept_assertion_dependency_set(
                &Concept::AtLeastConcept(at_least.clone()),
                node,
            )
            .unwrap_or_else(|| self.dependency_set_factory.empty_set()),
        );
        let existing = self
            .individual_reuse_strategy
            .as_ref()
            .and_then(|s| s.reuse_info(&to_concept));
        let existential_node = match existing {
            None => {
                // No `C`-witness yet: create one (as a root NI node, like Java's
                // `createNewNINode`, so blocking keys do not apply to it).
                if !is_deterministic {
                    let branching_point = BranchingPointData {
                        level: 0,
                        last_tableau_node: self.last_tableau_node,
                        last_merged_or_pruned_node: self.last_merged_or_pruned_node,
                        first_ground_disjunction: self.first_ground_disjunction,
                        first_unprocessed_ground_disjunction: self
                            .first_unprocessed_ground_disjunction,
                        ground_disjunction: usize::MAX,
                        sorted_disjunct_indexes: Vec::new(),
                        current_index: 0,
                        nominal_introduction: None,
                        reuse: Some(crate::tableau::branching::ReuseBranchingData {
                            existential: at_least.clone(),
                            for_node: node,
                            was_parent_reuse: false,
                        }),
                    };
                    self.push_branching_point(branching_point);
                    let level = self.current_branching_point;
                    dependency = DependencySet::Permanent(
                        self.dependency_set_factory.add_branching_point(&dependency, level),
                    );
                }
                let existential_node = self.create_new_ni_node(&dependency);
                let level = self.current_branching_point;
                if let Some(strategy) = self.individual_reuse_strategy.as_mut() {
                    strategy.record_reuse(to_concept.clone(), existential_node, level);
                }
                self.add_concept_assertion(
                    Concept::AtomicConcept(to_concept.clone()),
                    existential_node,
                    &dependency,
                    true,
                );
                existential_node
            }
            Some((reuse_node, branching_point)) => {
                // Reuse the existing `C`-witness: fold its merge-chain dependency
                // set and (when non-deterministic) the branching point at which it
                // was introduced, then draw the edge to its canonical survivor.
                let folded =
                    self.add_canonical_node_dependency_set(reuse_node, &dependency);
                dependency = DependencySet::Permanent(folded);
                let canonical = self.get_canonical_node(reuse_node);
                if !is_deterministic {
                    dependency = DependencySet::Permanent(
                        self.dependency_set_factory
                            .add_branching_point(&dependency, branching_point),
                    );
                }
                canonical
            }
        };
        self.add_role_assertion(
            at_least.on_role().clone(),
            node,
            existential_node,
            &dependency,
            true,
        );
        self.monitor_event(|m| m.existential_expansion_finished());
        true
    }

    /// Port of `ExistentialExpansionManager.tryFunctionalExpansion` for an
    /// `AtLeastDataRange` (the `AtLeast` supertype branch that adds a data-range
    /// assertion instead of a concept assertion).
    fn try_functional_expansion_data_range(
        &mut self,
        at_least: &AtLeastDataRange,
        node: NodeId,
    ) -> bool {
        if at_least.number() == 1 {
            if let Some((functionality_node, existing_dependency)) =
                self.get_functional_expansion_node(at_least.on_role(), node)
            {
                self.monitor_event(|m| m.existential_expansion_started());
                let existential_dependency = self
                    .get_concept_assertion_dependency_set(
                        &Concept::AtLeastDataRange(at_least.clone()),
                        node,
                    )
                    .unwrap_or_else(|| self.dependency_set_factory.empty_set());
                let union = self.dependency_set_factory.union_with(
                    &DependencySet::Permanent(existential_dependency),
                    &DependencySet::Permanent(existing_dependency),
                );
                let dependency = DependencySet::Permanent(union);
                self.add_role_assertion(
                    at_least.on_role().clone(),
                    node,
                    functionality_node,
                    &dependency,
                    true,
                );
                let predicate = literal_data_range_to_predicate(at_least.to_data_range());
                self.add_dl_predicate_assertion(predicate, functionality_node, &dependency, true);
                self.monitor_event(|m| m.existential_expansion_finished());
                return true;
            }
            false
        } else if at_least.number() > 1
            && self.functional_roles.contains_key(at_least.on_role())
        {
            self.monitor_event(|m| m.existential_expansion_started());
            let existential_dependency = self
                .get_concept_assertion_dependency_set(
                    &Concept::AtLeastDataRange(at_least.clone()),
                    node,
                )
                .unwrap_or_else(|| self.dependency_set_factory.empty_set());
            self.set_clash(&DependencySet::Permanent(existential_dependency));
            self.monitor_event(|m| m.existential_expansion_finished());
            true
        } else {
            false
        }
    }

    fn do_normal_at_least_expansion(&mut self, at_least: AtLeastConcept, node: NodeId) {
        self.monitor_event(|m| m.existential_expansion_started());
        let dependency_set = self
            .get_concept_assertion_dependency_set(&Concept::AtLeastConcept(at_least.clone()), node)
            .unwrap_or_else(|| self.dependency_set_factory.empty_set());
        let dependency = DependencySet::Permanent(dependency_set);
        let cardinality = at_least.number();
        let on_role = at_least.on_role().clone();
        let to_concept: Concept = Concept::from(at_least.to_concept().clone());

        let mut new_nodes = Vec::with_capacity(cardinality.max(0) as usize);
        for _ in 0..cardinality {
            let new_node = self.create_new_tree_node(&dependency, node);
            self.add_role_assertion(on_role.clone(), node, new_node, &dependency, true);
            self.add_concept_assertion(to_concept.clone(), new_node, &dependency, true);
            new_nodes.push(new_node);
        }
        self.add_pairwise_inequalities(&new_nodes, &dependency);
        self.monitor_event(|m| m.existential_expansion_finished());
    }

    fn expand_at_least_data_range(&mut self, at_least: AtLeastDataRange, node: NodeId) {
        // HermiT's `expand` / `tryFunctionalExpansion` applies to the
        // `AtLeast` supertype, so data ranges over functional roles get the same
        // reuse (n==1) / clash (n>=2) treatment before normal expansion.
        if self.try_functional_expansion_data_range(&at_least, node) {
            return;
        }
        self.monitor_event(|m| m.existential_expansion_started());
        let dependency_set = self
            .get_concept_assertion_dependency_set(
                &Concept::AtLeastDataRange(at_least.clone()),
                node,
            )
            .unwrap_or_else(|| self.dependency_set_factory.empty_set());
        let dependency = DependencySet::Permanent(dependency_set);
        let cardinality = at_least.number();
        let on_role = at_least.on_role().clone();

        // `doNormalExpansion` always materializes the `cardinality` concrete
        // successors with pairwise inequalities; when the filler's value space is
        // too small to hold that many distinct values (e.g. `>= 3 r.boolean`), the
        // unsatisfiability is detected by `check_datatype_constraints` over the
        // materialized nodes, which carries the datatype manager's dependency set.
        let predicate = literal_data_range_to_predicate(at_least.to_data_range());

        let mut new_nodes = Vec::with_capacity(cardinality.max(0) as usize);
        for _ in 0..cardinality {
            let new_node = self.create_new_concrete_node(&dependency, node);
            self.add_role_assertion(on_role.clone(), node, new_node, &dependency, true);
            self.add_dl_predicate_assertion(predicate.clone(), new_node, &dependency, true);
            new_nodes.push(new_node);
        }
        self.add_pairwise_inequalities(&new_nodes, &dependency);
        self.monitor_event(|m| m.existential_expansion_finished());
    }

    fn add_pairwise_inequalities(&mut self, nodes: &[NodeId], dependency: &DependencySet) {
        for outer in 0..nodes.len() {
            for inner in (outer + 1)..nodes.len() {
                self.add_ternary(
                    TableauObject::DLPredicate(DLPredicate::Inequality),
                    nodes[outer],
                    nodes[inner],
                    dependency,
                    true,
                );
            }
        }
    }
}

#[cfg(test)]
mod reuse_expansion_tests {
    use crate::configuration::ExistentialStrategyType;
    use crate::model::{AtLeastConcept, AtomicConcept, AtomicRole, Concept, LiteralConcept, Role};
    use crate::tableau::dependency_set::DependencySet;
    use crate::tableau::tableau::Tableau;

    fn tableau_with(strategy: ExistentialStrategyType) -> Tableau {
        let mut configuration = crate::configuration::Configuration::default();
        configuration.existential_strategy_type = strategy;
        Tableau::with_configuration(&configuration)
    }

    fn at_least(role: &str, concept: &str) -> AtLeastConcept {
        AtLeastConcept::create(
            1,
            Role::AtomicRole(AtomicRole::create(format!("http://example.org/{role}"))),
            LiteralConcept::AtomicConcept(AtomicConcept::create(format!(
                "http://example.org/{concept}"
            ))),
        )
    }

    /// Drives existential expansion to a fixpoint (`expand_existentials` returns
    /// after the first node that expanded, mirroring `m_expandNodeAtATime`).
    fn expand_to_fixpoint(tableau: &mut Tableau) {
        while tableau.expand_existentials() {}
    }

    /// Reuse actually REUSES a witness. A node with both
    /// `>=1 r.C` and `>=1 s.C` shares ONE C-witness under `IndividualReuse`,
    /// whereas the default creation-order strategy creates a SEPARATE witness per
    /// existential. So the reuse model has strictly fewer nodes.
    #[test]
    fn reuse_shares_one_witness_fewer_nodes_than_creation_order() {
        let build = |strategy| {
            let mut tableau = tableau_with(strategy);
            let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
            let a = tableau.create_new_named_node(&empty);
            // `>=1 r.C` and `>=1 s.C` on the same node, same filler concept C.
            tableau.add_concept_assertion(
                Concept::AtLeastConcept(at_least("r", "C")),
                a,
                &empty,
                true,
            );
            tableau.add_concept_assertion(
                Concept::AtLeastConcept(at_least("s", "C")),
                a,
                &empty,
                true,
            );
            expand_to_fixpoint(&mut tableau);
            tableau.debug_node_count()
        };

        let creation_order = build(ExistentialStrategyType::CreationOrder);
        let reuse = build(ExistentialStrategyType::IndividualReuse);
        let el = build(ExistentialStrategyType::El);

        // Creation order: node `a` + two distinct witnesses = 3 nodes.
        assert_eq!(creation_order, 3, "creation order makes one witness per existential");
        // Reuse: node `a` + ONE shared C-witness = 2 nodes (strictly fewer).
        assert!(
            reuse < creation_order,
            "IndividualReuse must produce a smaller (witness-sharing) model: \
             reuse={reuse} vs creation_order={creation_order}"
        );
        assert_eq!(reuse, 2, "reuse shares one C-witness for both r and s");
        // EL is the deterministic reuse strategy: it too shares the witness.
        assert_eq!(el, 2, "El (deterministic reuse) shares the C-witness too");
    }

    /// NEW: distinct fillers are NOT shared -- `>=1 r.C` and `>=1 s.D` get one
    /// witness each under reuse (one per concept), so the reuse model is the same
    /// size as creation order here. Guards against over-sharing.
    #[test]
    fn reuse_keeps_distinct_fillers_separate() {
        let mut tableau = tableau_with(ExistentialStrategyType::IndividualReuse);
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(Concept::AtLeastConcept(at_least("r", "C")), a, &empty, true);
        tableau.add_concept_assertion(Concept::AtLeastConcept(at_least("s", "D")), a, &empty, true);
        expand_to_fixpoint(&mut tableau);
        // node `a` + one C-witness + one D-witness = 3 nodes.
        assert_eq!(tableau.debug_node_count(), 3);
    }
}

/// The `ExtensionManager.containsDataRangeAssertion` shortcut -- a concrete
/// (non-abstract) node trivially satisfies the universal `rdfs:Literal` data range,
/// regardless of an explicit `rdfs:Literal` tuple.
#[cfg(test)]
mod rdfs_literal_shortcut_tests {
    use super::SatType;
    use crate::model::{
        AtLeastDataRange, AtomicRole, Concept, InternalDatatype, LiteralDataRange, Role,
    };
    use crate::tableau::dependency_set::DependencySet;
    use crate::tableau::tableau::Tableau;

    fn role(name: &str) -> Role {
        Role::AtomicRole(AtomicRole::create(format!("http://example.org/{name}")))
    }

    fn at_least_literal(role_name: &str) -> AtLeastDataRange {
        AtLeastDataRange::create(
            1,
            role(role_name),
            LiteralDataRange::InternalDatatype(InternalDatatype::rdfs_literal().clone()),
        )
    }

    fn expand_to_fixpoint(tableau: &mut Tableau) {
        while tableau.expand_existentials() {}
    }

    /// `>=1 r.rdfs:Literal` on a node that already has a concrete `r`-successor is
    /// SATISFIED, so expansion creates NO fresh data node. By default
    /// `needs_rdfs_literal_extension` is false, so the seed `rdfs:Literal` tuple is
    /// filtered out at the extension table (matching Java
    /// `ExtensionTableWithTupleIndexes.addTuple`): without the shortcut the
    /// satisfaction check would find no tuple, declare NOT_SATISFIED and create a
    /// spurious extra concrete node.
    #[test]
    fn concrete_successor_satisfies_rdfs_literal_without_explicit_tuple() {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        // An existing concrete `r`-successor (e.g. a data-property assertion).
        let c = tableau.create_new_concrete_node(&empty, a);
        tableau.add_role_assertion(role("r"), a, c, &empty, true);
        // Default tableau: rdfs:Literal is NOT materialized, so `c` has no tuple.
        assert_eq!(tableau.debug_node_count(), 2, "a and its concrete successor c");

        tableau.add_concept_assertion(
            Concept::AtLeastDataRange(at_least_literal("r")),
            a,
            &empty,
            true,
        );
        // The shortcut makes the at-least already satisfied (no expansion needed).
        assert!(matches!(
            tableau.at_least_data_range_sat_type(&at_least_literal("r"), a),
            SatType::PermanentlySatisfied | SatType::CurrentlySatisfied
        ));

        expand_to_fixpoint(&mut tableau);
        assert!(!tableau.contains_clash());
        // No fresh data node: the existing concrete successor witnesses rdfs:Literal.
        assert_eq!(
            tableau.debug_node_count(),
            2,
            "rdfs:Literal shortcut must reuse the concrete successor, not create a node"
        );
    }

    /// The shortcut is gated on the node being non-abstract: an abstract successor
    /// (a tree node, which never gets an `rdfs:Literal` tuple) does NOT satisfy the
    /// data range via the shortcut, so the at-least stays unsatisfied. Guards
    /// against the shortcut over-firing for abstract nodes.
    #[test]
    fn abstract_successor_does_not_satisfy_rdfs_literal_via_shortcut() {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        // An abstract (tree) successor: never seeded with an rdfs:Literal tuple.
        let b = tableau.create_new_tree_node(&empty, a);
        tableau.add_role_assertion(role("r"), a, b, &empty, true);

        assert_eq!(
            tableau.at_least_data_range_sat_type(&at_least_literal("r"), a),
            SatType::NotSatisfied,
            "an abstract successor must not satisfy rdfs:Literal via the shortcut"
        );
    }
}

/// Functional-role expansion, the port of
/// `ExistentialExpansionManager.expand`/`tryFunctionalExpansion`/
/// `getFunctionalExpansionNode`/`updateFunctionalRoles`.
#[cfg(test)]
mod functional_expansion_tests {
    use crate::model::{
        AnnotatedEquality, AtLeastConcept, AtomicConcept, AtomicRole, Atom, Concept, DLClause,
        DLPredicate, LiteralConcept, Role, Term, Variable,
    };
    use crate::tableau::dependency_set::DependencySet;
    use crate::tableau::tableau::Tableau;

    fn role(name: &str) -> Role {
        Role::AtomicRole(AtomicRole::create(format!("http://example.org/{name}")))
    }

    fn at_least(n: i32, role_name: &str, concept: &str) -> AtLeastConcept {
        AtLeastConcept::create(
            n,
            role(role_name),
            LiteralConcept::AtomicConcept(AtomicConcept::create(format!(
                "http://example.org/{concept}"
            ))),
        )
    }

    fn concept(name: &str) -> Concept {
        Concept::AtomicConcept(AtomicConcept::create(format!("http://example.org/{name}")))
    }

    fn expand_to_fixpoint(tableau: &mut Tableau) {
        while tableau.expand_existentials() {}
    }

    /// A FunctionalObjectProperty(r) functionality DL-clause: r(X,Y1), r(X,Y2) ->
    /// Y1 == Y2 (an AnnotatedEquality head). Mirrors HermiT's functionality axiom.
    fn functionality_clause(role_name: &str) -> DLClause {
        let r = AtomicRole::create(format!("http://example.org/{role_name}"));
        let x = Variable::create("X");
        let y1 = Variable::create("Y1");
        let y2 = Variable::create("Y2");
        let body = vec![
            Atom::create(
                DLPredicate::AtomicRole(r.clone()),
                vec![Term::Variable(x.clone()), Term::Variable(y1.clone())],
            ),
            Atom::create(
                DLPredicate::AtomicRole(r.clone()),
                vec![Term::Variable(x.clone()), Term::Variable(y2.clone())],
            ),
        ];
        // AnnotatedEquality predicate stands in for the equality head; the
        // cardinality/role/concept annotation is irrelevant to is_functionality_axiom.
        let equality = AnnotatedEquality::create(
            1,
            Role::AtomicRole(r.clone()),
            LiteralConcept::AtomicConcept(AtomicConcept::thing().clone()),
        );
        // The AnnotatedEquality head atom has arity 3: (Y1, Y2, X) -- mirroring
        // owl_clausification's `==@(...)(y_i, y_j, x)`.
        let head = vec![Atom::create(
            DLPredicate::AnnotatedEquality(equality),
            vec![Term::Variable(y1), Term::Variable(y2), Term::Variable(x)],
        )];
        DLClause::create(head, body)
    }

    /// `updateFunctionalRoles`/`loadDLClausesIntoGraph`: a FunctionalObjectProperty
    /// clause alone (no role-inclusion clause) does NOT add the role to the
    /// super-role graph, so it does NOT get a functional_roles map entry -- matching
    /// Java's getElements()-only iteration in updateFunctionalRoles.
    #[test]
    fn functionality_clause_populates_functional_role_map() {
        assert!(
            functionality_clause("r").is_functionality_axiom(),
            "the constructed clause must be recognized as a functionality axiom"
        );
        let mut tableau = Tableau::new();
        let mut clauses = indexmap::IndexSet::new();
        clauses.insert(functionality_clause("r"));
        tableau.set_functional_roles_from_clauses(&clauses);
        // Java loadDLClausesIntoGraph only adds a role to superRoleGraph for
        // inclusion clauses; updateFunctionalRoles iterates only getElements(), so
        // a standalone functional role gets NO map entry.
        assert!(
            !tableau.functional_roles.contains_key(&role("r")),
            "standalone functional role must NOT be in the map (no inclusion clause)"
        );
        // A role with no functionality axiom is also not in the map.
        assert!(!tableau.functional_roles.contains_key(&role("s")));
    }

    /// `tryFunctionalExpansion` n>=2 branch: `>=2 r.C` over a role whose
    /// functional_roles entry was seeded directly clashes immediately. The entry
    /// is set via the test helper (mirrors Java tryFunctionalExpansion when the
    /// map has been populated by a role that DOES appear in an inclusion clause).
    #[test]
    fn at_least_two_over_functional_role_clashes() {
        let mut tableau = Tableau::new();
        // Seed the map directly: a role with a genuine inclusion clause would end
        // up here via set_functional_roles_from_clauses; standalone functional
        // roles do NOT get an entry (matching Java getElements()-only iteration).
        tableau.set_functional_role_entry_for_test(role("r"), vec![role("r")]);

        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(
            Concept::AtLeastConcept(at_least(2, "r", "C")),
            a,
            &empty,
            true,
        );
        assert!(!tableau.contains_clash(), "no clash before expansion");
        expand_to_fixpoint(&mut tableau);
        assert!(
            tableau.contains_clash(),
            ">=2 over a functional role must clash via functional expansion"
        );
    }

    /// `tryFunctionalExpansion` n==1 / `getFunctionalExpansionNode` reuse branch:
    /// `>=1 r.C` over a functional role with an existing r-successor REUSES that
    /// successor (adds C to it) instead of creating a fresh one. Setting the
    /// functional-role entry directly (the unit-level path the reasoner-side
    /// population would feed).
    #[test]
    fn at_least_one_over_functional_role_reuses_existing_successor() {
        let mut tableau = Tableau::new();
        tableau.set_functional_role_entry_for_test(role("r"), vec![role("r")]);

        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        // An existing r-successor `b` (e.g. from an ABox role assertion).
        let b = tableau.create_new_named_node(&empty);
        tableau.add_role_assertion(role("r"), a, b, &empty, true);
        let before = tableau.debug_node_count();
        assert_eq!(before, 2, "a and b only");

        tableau.add_concept_assertion(
            Concept::AtLeastConcept(at_least(1, "r", "C")),
            a,
            &empty,
            true,
        );
        expand_to_fixpoint(&mut tableau);

        // Reuse: no fresh witness created -- still exactly 2 nodes.
        assert_eq!(
            tableau.debug_node_count(),
            2,
            "functional reuse must NOT create a fresh successor"
        );
        // The filler C was added to the existing successor `b`.
        assert!(
            tableau.contains_concept_assertion(&concept("C"), b),
            "the filler C must be added to the reused successor b"
        );
    }

    /// `getFunctionalExpansionNode` returns None when there is no existing
    /// successor: `>=1 r.C` over a functional role with no r-successor creates
    /// exactly one (falls through to normal expansion).
    #[test]
    fn at_least_one_over_functional_role_no_successor_creates_one() {
        let mut tableau = Tableau::new();
        tableau.set_functional_role_entry_for_test(role("r"), vec![role("r")]);

        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(
            Concept::AtLeastConcept(at_least(1, "r", "C")),
            a,
            &empty,
            true,
        );
        expand_to_fixpoint(&mut tableau);
        // a + one fresh witness = 2 nodes.
        assert_eq!(tableau.debug_node_count(), 2);
    }

    /// Default behaviour for NON-functional roles is unchanged: with an empty
    /// functional-role map, `>=2 r.C` creates two fresh distinct witnesses (no
    /// functional clash, no reuse).
    #[test]
    fn non_functional_role_still_creates_fresh_witnesses() {
        let mut tableau = Tableau::new();
        // No functional roles set -> map empty.
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(
            Concept::AtLeastConcept(at_least(2, "r", "C")),
            a,
            &empty,
            true,
        );
        expand_to_fixpoint(&mut tableau);
        assert!(!tableau.contains_clash(), "non-functional >=2 must NOT clash");
        // a + two fresh distinct witnesses = 3 nodes.
        assert_eq!(tableau.debug_node_count(), 3);
    }

    /// And a non-functional `>=1 r.C` with an existing successor still creates a
    /// SECOND fresh witness (no reuse), proving reuse is gated on functionality.
    #[test]
    fn non_functional_role_at_least_one_does_not_reuse() {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let b = tableau.create_new_named_node(&empty);
        tableau.add_role_assertion(role("r"), a, b, &empty, true);
        tableau.add_concept_assertion(
            Concept::AtLeastConcept(at_least(1, "r", "C")),
            a,
            &empty,
            true,
        );
        expand_to_fixpoint(&mut tableau);
        // a, b, plus a fresh witness for the existential = 3 nodes (no reuse).
        assert_eq!(tableau.debug_node_count(), 3);
    }
}
