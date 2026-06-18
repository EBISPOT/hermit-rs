// Port of org.semanticweb.HermiT.tableau.ExtensionManager (the parts that drive
// the binary/ternary extension tables). HermiT's `ExtensionManager` holds a
// back-reference to the `Tableau`; here it is an `impl` block on `Tableau`,
// since both the tables and the node arena it must touch live on the `Tableau`.
//
// The `postAdd`/`postRemove` node-counter updates are applied here; the
// existential-strategy callbacks (`assertionAdded`, `assertionCoreSet`) are
// not forwarded — the `ExistentialExpansionStrategy` trait does not expose them.
#![allow(dead_code)]

use crate::model::{AtomicConcept, Concept, DLPredicate, ExistentialConcept, InternalDatatype, Role};
use crate::tableau::dependency_set::{DependencySet, PermanentDependencySet};
use crate::tableau::extension_table::{Retrieval, StoreOutcome, View};
use crate::tableau::node::NodeId;
use crate::tableau::object::TableauObject;
use crate::tableau::tableau::Tableau;

fn is_thing_label(object: &TableauObject) -> bool {
    matches!(object,
        TableauObject::Concept(Concept::AtomicConcept(c)) if c == AtomicConcept::thing())
}
fn is_rdfs_literal_label(object: &TableauObject) -> bool {
    matches!(object,
        TableauObject::DLPredicate(DLPredicate::InternalDatatype(d)) if d == InternalDatatype::rdfs_literal())
}

pub(crate) fn concept_to_existential(concept: &Concept) -> Option<ExistentialConcept> {
    match concept {
        Concept::AtLeastConcept(a) => Some(ExistentialConcept::AtLeastConcept(a.clone())),
        Concept::AtLeastDataRange(a) => Some(ExistentialConcept::AtLeastDataRange(a.clone())),
        Concept::ExistsDescriptionGraph(e) => {
            Some(ExistentialConcept::ExistsDescriptionGraph(e.clone()))
        }
        _ => None,
    }
}

impl Tableau {
    // -- Clash ---------------------------------------------------------------

    pub fn set_clash(&mut self, clash_dependency_set: &DependencySet) {
        if let Some(existing) = self.clash_dependency_set.take() {
            self.dependency_set_factory.remove_usage(&existing);
        }
        let permanent = self.dependency_set_factory.get_permanent(clash_dependency_set);
        self.dependency_set_factory.add_usage(&permanent);
        self.clash_dependency_set = Some(permanent);
        // ExtensionManager.setClash line 182-183: emit once per set_clash call.
        self.monitor_event(|m| m.clash_detected());
    }
    pub fn clear_clash(&mut self) {
        if let Some(existing) = self.clash_dependency_set.take() {
            self.dependency_set_factory.remove_usage(&existing);
        }
    }
    pub fn contains_clash(&self) -> bool {
        self.clash_dependency_set.is_some()
    }

    /// Advances both extension tables' delta windows, returning whether either
    /// had a non-empty delta-new (the Java `ExtensionManager.propagateDeltaNew`).
    pub fn propagate_delta_new_all(&mut self) -> bool {
        let binary = self.binary_extension_table.propagate_delta_new();
        let ternary = self.ternary_extension_table.propagate_delta_new();
        let graphs = self.description_graph_manager.propagate_delta_new();
        binary || ternary || graphs
    }
    pub fn get_clash_dependency_set(&self) -> Option<&PermanentDependencySet> {
        self.clash_dependency_set.as_ref()
    }

    // -- Activity checks -----------------------------------------------------

    fn binary_tuple_active(&self, node: NodeId) -> bool {
        self.nodes[node].is_active()
    }
    fn ternary_tuple_active(&self, node0: NodeId, node1: NodeId) -> bool {
        self.nodes[node0].is_active() && self.nodes[node1].is_active()
    }

    // -- Binary table additions ---------------------------------------------

    fn add_binary(
        &mut self,
        label: TableauObject,
        node: NodeId,
        dependency_set: &DependencySet,
        is_core: bool,
    ) -> bool {
        // ExtensionManager.java:329-331: guard against reentrant add calls.
        debug_assert!(!self.add_active, "ExtensionManager is not reentrant.");
        self.add_active = true;
        let result = self.add_binary_core(label, node, dependency_set, is_core);
        self.add_active = false;
        result
    }

    fn add_binary_core(
        &mut self,
        label: TableauObject,
        node: NodeId,
        dependency_set: &DependencySet,
        is_core: bool,
    ) -> bool {
        let tuple = [label, TableauObject::Node(node)];
        // ExtensionTableWithTupleIndexes.addTuple line 50-51: addFactStarted fires
        // unconditionally at entry, before the active/Thing/Literal guard.
        self.monitor_event(|m| m.add_fact_started());
        let passes = self.binary_tuple_active(node)
            && (self.needs_thing_extension || !is_thing_label(&tuple[0]))
            && (self.needs_rdfs_literal_extension || !is_rdfs_literal_label(&tuple[0]));
        if !passes {
            // line 76-77: addFactFinished(tuple,isCore,false) on the not-added exit.
            self.monitor_event(|m| m.add_fact_finished());
            return false;
        }
        let permanent = self.dependency_set_factory.get_permanent(dependency_set);
        let outcome = self.binary_extension_table.store_tuple(
            &tuple,
            permanent.clone(),
            is_core,
            &mut self.dependency_set_factory,
        );
        match outcome {
            StoreOutcome::Added(idx) => {
                // line 62-63: addFactFinished(tuple,isCore,true) before postAdd.
                self.monitor_event(|m| m.add_fact_finished());
                self.post_add_binary(&tuple, idx, is_core, permanent);
                // AnywhereBlocking assertionAdded: an atomic-concept assertion
                // changes the node's blocking signature.
                if matches!(&tuple[0], TableauObject::Concept(Concept::AtomicConcept(_))) {
                    if self.blocking_validator.is_some() && !is_core {
                        // Validated blocking signs on the *core* concept label, so a
                        // NON-core atomic concept changes only the validation label,
                        // not the blocking signature: `ValidatedDirectBlockingChecker
                        // .addConcept` sets `m_hasChangedForBlocking` (and returns the
                        // node, driving `updateNodeChange`/`first_changed_node`) only
                        // when `isCore`, while `m_hasChangedForValidation` is set for
                        // any concept. Invalidate the cached labels and mark the node
                        // (and its parent) validation-changed, but leave the blocking
                        // frontier and blocking-info-changed flag untouched.
                        self.nodes[node].invalidate_blocking_cache();
                        self.nodes[node].has_blocking_info_changed = false;
                        self.validation_info_changed(node);
                        self.validation_info_changed_parent(node);
                    } else {
                        self.note_blocking_node_changed(node);
                        // AnywhereValidatedBlocking.assertionAdded(Concept) also marks
                        // the node's parent validation info.
                        self.validation_info_changed_parent(node);
                    }
                }
                // An assertion on a data node may add a data range it must be
                // re-checked against.
                if !self.nodes[node].get_node_type().is_abstract() {
                    self.datatype_check_needed = true;
                }
                true
            }
            StoreOutcome::AlreadyPresent(idx) => {
                if self.binary_extension_table.upgrade_core(idx, is_core) {
                    // Java ExtensionManager also calls existentialExpansionStrategy
                    // .assertionCoreSet here; that callback is not forwarded.
                    // Validated blocking uses the *core* concept label, so a
                    // non-core -> core upgrade of an atomic concept changes the
                    // node's validated signature even though no tuple was added.
                    if self.blocking_validator.is_some()
                        && matches!(&tuple[0], TableauObject::Concept(Concept::AtomicConcept(_)))
                    {
                        self.note_blocking_node_changed(node);
                        // AnywhereValidatedBlocking.assertionCoreSet(Concept) also
                        // marks the node's parent validation info.
                        self.validation_info_changed_parent(node);
                    }
                }
                // line 76-77: addFactFinished(tuple,isCore,false) — tuple already present.
                self.monitor_event(|m| m.add_fact_finished());
                false
            }
        }
    }

    pub fn add_concept_assertion(
        &mut self,
        concept: Concept,
        node: NodeId,
        dependency_set: &DependencySet,
        is_core: bool,
    ) -> bool {
        self.add_binary(TableauObject::Concept(concept), node, dependency_set, is_core)
    }

    /// Adds a binary assertion whose label is a DL predicate (e.g. a data range).
    pub fn add_dl_predicate_assertion(
        &mut self,
        dl_predicate: DLPredicate,
        node: NodeId,
        dependency_set: &DependencySet,
        is_core: bool,
    ) -> bool {
        self.add_binary(TableauObject::DLPredicate(dl_predicate), node, dependency_set, is_core)
    }

    fn post_add_binary(
        &mut self,
        tuple: &[TableauObject],
        _tuple_index: usize,
        _is_core: bool,
        dependency_set: PermanentDependencySet,
    ) {
        if let TableauObject::Concept(concept) = &tuple[0] {
            let node = tuple[1].as_node().expect("binary tuple argument is a node");
            match concept {
                Concept::AtomicConcept(_) => {
                    self.nodes[node].number_of_positive_atomic_concepts += 1;
                }
                Concept::AtomicNegationConcept(_) => {
                    self.nodes[node].number_of_negated_atomic_concepts += 1;
                }
                _ => {
                    if let Some(existential) = concept_to_existential(concept) {
                        self.nodes[node].unprocessed_existentials.push(existential);
                    }
                }
            }
            // Java ExtensionManager also calls existentialExpansionStrategy
            // .assertionAdded here; that callback is not forwarded in this port.
        }
        self.clash_check_binary(tuple, dependency_set);
    }

    // -- Ternary table additions --------------------------------------------

    pub(crate) fn add_ternary(
        &mut self,
        label: TableauObject,
        node0: NodeId,
        node1: NodeId,
        dependency_set: &DependencySet,
        is_core: bool,
    ) -> bool {
        // ExtensionManager.addAssertion guards against reentrant add calls: the
        // flag is set for the duration of the add (including postAdd) and a nested
        // ExtensionManager add trips the assertion. The one legitimate reentrant
        // add -- the ClashManager generating an Inequality during postAdd -- goes
        // straight to the table via `add_ternary_core`, exactly as HermiT calls
        // `m_ternaryExtensionTable.addTuple` to dodge this guard.
        debug_assert!(!self.add_active, "ExtensionManager is not reentrant.");
        self.add_active = true;
        let result = self.add_ternary_core(label, node0, node1, dependency_set, is_core);
        self.add_active = false;
        result
    }

    /// The guard-free ternary add (HermiT's direct `m_ternaryExtensionTable.addTuple`).
    pub(crate) fn add_ternary_core(
        &mut self,
        label: TableauObject,
        node0: NodeId,
        node1: NodeId,
        dependency_set: &DependencySet,
        is_core: bool,
    ) -> bool {
        let tuple = [label, TableauObject::Node(node0), TableauObject::Node(node1)];
        // ExtensionTableWithTupleIndexes.addTuple line 50-51: addFactStarted at entry.
        self.monitor_event(|m| m.add_fact_started());
        // ExtensionTableWithTupleIndexes.addTuple line 52: the active/Thing/Literal
        // guard is shared by the binary and ternary tables.
        let passes = self.ternary_tuple_active(node0, node1)
            && (self.needs_thing_extension || !is_thing_label(&tuple[0]))
            && (self.needs_rdfs_literal_extension || !is_rdfs_literal_label(&tuple[0]));
        if !passes {
            // line 76-77: addFactFinished(tuple,isCore,false) on the not-added exit.
            self.monitor_event(|m| m.add_fact_finished());
            return false;
        }
        let permanent = self.dependency_set_factory.get_permanent(dependency_set);
        let outcome = self.ternary_extension_table.store_tuple(
            &tuple,
            permanent.clone(),
            is_core,
            &mut self.dependency_set_factory,
        );
        match outcome {
            StoreOutcome::Added(idx) => {
                // line 62-63: addFactFinished(tuple,isCore,true) before postAdd.
                self.monitor_event(|m| m.add_fact_finished());
                self.post_add_ternary(&tuple, idx, is_core, permanent);
                if matches!(&tuple[0], TableauObject::DLPredicate(DLPredicate::AtomicRole(_))) {
                    if self.blocking_validator.is_some() {
                        // AnywhereValidatedBlocking.assertionAdded(AtomicRole,from,to,isCore):
                        //   if (isCore) { updateNodeChange(from); updateNodeChange(to); }
                        //   validationInfoChanged(from); validationInfoChanged(to);
                        // The validated direct checker's assertionAdded(AtomicRole) returns
                        // null, so the blocking labels are NOT invalidated and the
                        // blocking-change flag is NOT set; only the reprocessing range
                        // (when core) and the validation frontier move.
                        if is_core {
                            self.update_node_change(node0);
                            self.update_node_change(node1);
                        }
                        self.validation_info_changed(node0);
                        self.validation_info_changed(node1);
                    } else if self.direct_blocking_kind
                        == crate::tableau::blocking_strategy::DirectBlockingKind::Pairwise
                    {
                        // PairWiseDirectBlockingChecker.assertionAdded: only a
                        // parent-child edge changes the child's pairwise signature, so
                        // mark just that child (a non-parent-child edge is irrelevant).
                        if self.nodes[node1].get_parent() == Some(node0) {
                            self.note_blocking_node_changed(node1);
                        } else if self.nodes[node0].get_parent() == Some(node1) {
                            self.note_blocking_node_changed(node0);
                        }
                    }
                }
                // An assertion touching a data node (e.g. an Inequality between
                // concrete nodes) requires a datatype re-check.
                if !self.nodes[node0].get_node_type().is_abstract()
                    || !self.nodes[node1].get_node_type().is_abstract()
                {
                    self.datatype_check_needed = true;
                }
                true
            }
            StoreOutcome::AlreadyPresent(idx) => {
                if self.ternary_extension_table.upgrade_core(idx, is_core) {
                    // Java ExtensionManager also calls existentialExpansionStrategy
                    // .assertionCoreSet here; that callback is not forwarded in this port.
                }
                // line 76-77: addFactFinished(tuple,isCore,false) — tuple already present.
                self.monitor_event(|m| m.add_fact_finished());
                false
            }
        }
    }

    /// Adds a role assertion, orienting inverse roles onto the named property
    /// (the Java `ExtensionManager.addRoleAssertion`).
    pub fn add_role_assertion(
        &mut self,
        role: Role,
        node_from: NodeId,
        node_to: NodeId,
        dependency_set: &DependencySet,
        is_core: bool,
    ) -> bool {
        match role {
            Role::AtomicRole(r) => self.add_ternary(
                TableauObject::DLPredicate(DLPredicate::AtomicRole(r)),
                node_from,
                node_to,
                dependency_set,
                is_core,
            ),
            Role::InverseRole(r) => self.add_ternary(
                TableauObject::DLPredicate(DLPredicate::AtomicRole(r.get_inverse_of().clone())),
                node_to,
                node_from,
                dependency_set,
                is_core,
            ),
        }
    }

    fn post_add_ternary(
        &mut self,
        tuple: &[TableauObject],
        _tuple_index: usize,
        _is_core: bool,
        dependency_set: PermanentDependencySet,
    ) {
        match &tuple[0] {
            TableauObject::DLPredicate(DLPredicate::AtomicRole(_)) => {
                // Java ExtensionManager also calls existentialExpansionStrategy
                // .assertionAdded here; that callback is not forwarded in this port.
            }
            TableauObject::NegatedAtomicRole(_) => {
                let node = tuple[1].as_node().expect("ternary tuple argument is a node");
                self.nodes[node].number_of_negated_role_assertions += 1;
            }
            _ => {}
        }
        self.clash_check_ternary(tuple, dependency_set);
    }

    // -- Containment / dependency sets --------------------------------------

    pub fn contains_concept_assertion(&self, concept: &Concept, node: NodeId) -> bool {
        if self.nodes[node].get_node_type().is_abstract()
            && matches!(concept, Concept::AtomicConcept(c) if c == AtomicConcept::thing())
        {
            return true;
        }
        let tuple = [
            TableauObject::Concept(concept.clone()),
            TableauObject::Node(node),
        ];
        self.binary_contains(&tuple)
    }

    pub fn contains_role_assertion(&self, role: &Role, node_from: NodeId, node_to: NodeId) -> bool {
        let tuple = match role {
            Role::AtomicRole(r) => [
                TableauObject::DLPredicate(DLPredicate::AtomicRole(r.clone())),
                TableauObject::Node(node_from),
                TableauObject::Node(node_to),
            ],
            Role::InverseRole(r) => [
                TableauObject::DLPredicate(DLPredicate::AtomicRole(r.get_inverse_of().clone())),
                TableauObject::Node(node_to),
                TableauObject::Node(node_from),
            ],
        };
        self.ternary_contains(&tuple)
    }

    fn binary_contains(&self, tuple: &[TableauObject]) -> bool {
        let index = self.binary_extension_table.get_tuple_index(tuple);
        index != -1 && self.nodes[tuple[1].as_node().unwrap()].is_active()
    }
    fn ternary_contains(&self, tuple: &[TableauObject]) -> bool {
        let index = self.ternary_extension_table.get_tuple_index(tuple);
        index != -1
            && self.nodes[tuple[1].as_node().unwrap()].is_active()
            && self.nodes[tuple[2].as_node().unwrap()].is_active()
    }

    pub fn get_concept_assertion_dependency_set(
        &self,
        concept: &Concept,
        node: NodeId,
    ) -> Option<PermanentDependencySet> {
        if matches!(concept, Concept::AtomicConcept(c) if c == AtomicConcept::thing()) {
            return Some(self.empty_dependency_set());
        }
        let tuple = [
            TableauObject::Concept(concept.clone()),
            TableauObject::Node(node),
        ];
        let index = self.binary_extension_table.get_tuple_index(tuple.as_slice());
        if index == -1 {
            None
        } else {
            Some(
                self.binary_extension_table
                    .get_dependency_set(index as usize, &self.empty_dependency_set()),
            )
        }
    }

    fn empty_dependency_set(&self) -> PermanentDependencySet {
        self.dependency_set_factory.empty_set()
    }

    /// Adds a unary (binary-table) assertion whose predicate comes from a DL
    /// clause head. Concept-like predicates (atomic concepts, at-least concepts,
    /// description graphs) are stored under the `Concept` label so that concept
    /// lookups match; data-range predicates are stored as DL predicates.
    pub(crate) fn add_unary_from_predicate(
        &mut self,
        predicate: DLPredicate,
        node: NodeId,
        dependency_set: &DependencySet,
        is_core: bool,
    ) -> bool {
        match predicate {
            DLPredicate::AtomicConcept(c) => {
                self.add_concept_assertion(Concept::AtomicConcept(c), node, dependency_set, is_core)
            }
            DLPredicate::AtLeastConcept(c) => {
                self.add_concept_assertion(Concept::AtLeastConcept(c), node, dependency_set, is_core)
            }
            DLPredicate::AtLeastDataRange(c) => self.add_concept_assertion(
                Concept::AtLeastDataRange(c),
                node,
                dependency_set,
                is_core,
            ),
            DLPredicate::ExistsDescriptionGraph(c) => self.add_concept_assertion(
                Concept::ExistsDescriptionGraph(c),
                node,
                dependency_set,
                is_core,
            ),
            other => self.add_dl_predicate_assertion(other, node, dependency_set, is_core),
        }
    }

    /// Adds an arity-3 assertion from a DL clause head. An `AnnotatedEquality`
    /// (the at-most rule) merges its two equated arguments, routing through
    /// `apply_annotated_equality` which handles the NI rule for nominals.
    pub(crate) fn add_ternary_from_predicate(
        &mut self,
        predicate: DLPredicate,
        node0: NodeId,
        node1: NodeId,
        node2: NodeId,
        dependency_set: &DependencySet,
        _is_core: bool,
    ) -> bool {
        match predicate {
            // A derived `AnnotatedEquality` (the at-most rule, e.g. the single
            // head atom of `<= 1 r.C` or a functional role) must be routed
            // through the nominal-introduction manager, exactly as Java's
            // `ExtensionManager.addAssertion` dispatches every annotated
            // equality to `NominalIntroductionManager.addAnnotatedEquality`.
            // `add_annotated_equality` forgets the annotation (direct merge),
            // applies the NI rule immediately for a `<= 1`/functional annotation,
            // or buffers a cardinality-`> 1` annotation for the deferred
            // `process_annotated_equalities` phase. A direct `merge_nodes` here is
            // unsound when nominals/root nodes are involved (and can hit the
            // `unsupported merge type` panic in `choose_merge_direction`).
            DLPredicate::AnnotatedEquality(annotated_equality) => {
                self.add_annotated_equality(&annotated_equality, node0, node1, node2, dependency_set)
            }
            _ => false, // DescriptionGraph tuples require N-ary extension tables, which are not supported.
        }
    }

    /// Adds a binary (ternary-table) assertion whose predicate comes from a DL
    /// clause head, routing Equality to the merge rule.
    pub(crate) fn add_binary_from_predicate(
        &mut self,
        predicate: DLPredicate,
        node0: NodeId,
        node1: NodeId,
        dependency_set: &DependencySet,
        is_core: bool,
    ) -> bool {
        match predicate {
            DLPredicate::Equality => self.merge_nodes(node0, node1, dependency_set),
            DLPredicate::AnnotatedEquality(_) => {
                // AnnotatedEquality has arity 3 and is only ever dispatched through
                // add_ternary_from_predicate (ExtensionManager.java:411-412 routes it
                // to nominalIntroductionManager, which takes 3 node args). Reaching
                // here would silently drop an at-most/NI rule; fail loudly instead.
                unreachable!("AnnotatedEquality has arity 3 and is never dispatched through the binary head path")
            }
            other => self.add_ternary(
                TableauObject::DLPredicate(other),
                node0,
                node1,
                dependency_set,
                is_core,
            ),
        }
    }

    // -- Retrievals (materialized) ------------------------------------------

    pub fn create_binary_retrieval(
        &self,
        binding_positions: [i32; 2],
        bindings_buffer: [Option<TableauObject>; 2],
        view: View,
    ) -> Retrieval {
        let table = &self.binary_extension_table;
        let keep = |tuple_index: usize| -> bool {
            let node = table.get_tuple_object(tuple_index, 1).as_node().unwrap();
            self.nodes[node].is_active()
                && self.selection_matches(table, tuple_index, &binding_positions, &bindings_buffer)
        };
        // Java `createRetrieval` uses an IndexedRetrieval (trie walk, reverse-
        // insertion order) when some leading column is bound, otherwise an
        // ascending UnindexedRetrieval scan over the view window.
        let mut tuple_indices = Vec::new();
        if table.indexed_tuple_indices_into(&binding_positions, &bindings_buffer, view, &mut tuple_indices) {
            tuple_indices.retain(|&t| keep(t));
        } else {
            let (start, after_last) = table.view_range(view);
            tuple_indices.extend((start..after_last).filter(|&t| keep(t)));
        }
        Retrieval { tuple_indices, position: 0, view }
    }

    /// All atomic concepts asserted on `node` (TOTAL view). This is how
    /// `DeterministicClassification` reads a concept's subsumers off the single
    /// saturated model: every atomic concept on the fresh node `x` after asserting
    /// `element(x)` is a subsumer of `element`.
    pub fn atomic_concepts_on_node(&self, node: NodeId) -> Vec<crate::model::AtomicConcept> {
        let retrieval = self.create_binary_retrieval(
            [-1, 1],
            [None, Some(TableauObject::Node(node))],
            View::Total,
        );
        let mut concepts = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            if let TableauObject::Concept(crate::model::Concept::AtomicConcept(c)) =
                self.binary_extension_table.get_tuple_object(tuple_index, 0)
            {
                concepts.push(c.clone());
            }
        }
        concepts
    }

    pub fn create_ternary_retrieval(
        &self,
        binding_positions: [i32; 3],
        bindings_buffer: [Option<TableauObject>; 3],
        view: View,
    ) -> Retrieval {
        let table = &self.ternary_extension_table;
        let keep = |tuple_index: usize| -> bool {
            let n1 = table.get_tuple_object(tuple_index, 1).as_node().unwrap();
            let n2 = table.get_tuple_object(tuple_index, 2).as_node().unwrap();
            self.nodes[n1].is_active()
                && self.nodes[n2].is_active()
                && self.selection_matches(table, tuple_index, &binding_positions, &bindings_buffer)
        };
        // As for the binary table: indexed trie walk when a leading column is
        // bound (reverse-insertion order), else an ascending unindexed scan.
        let mut tuple_indices = Vec::new();
        if table.indexed_tuple_indices_into(&binding_positions, &bindings_buffer, view, &mut tuple_indices) {
            tuple_indices.retain(|&t| keep(t));
        } else {
            let (start, after_last) = table.view_range(view);
            tuple_indices.extend((start..after_last).filter(|&t| keep(t)));
        }
        Retrieval { tuple_indices, position: 0, view }
    }

    fn selection_matches(
        &self,
        table: &ExtensionTableRef,
        tuple_index: usize,
        binding_positions: &[i32],
        bindings_buffer: &[Option<TableauObject>],
    ) -> bool {
        for (column, &position) in binding_positions.iter().enumerate() {
            if position != -1 {
                let stored = table.get_tuple_object(tuple_index, column);
                match &bindings_buffer[position as usize] {
                    Some(expected) if stored == expected => {}
                    _ => return false,
                }
            }
        }
        true
    }
}

use crate::tableau::extension_table::ExtensionTable as ExtensionTableRef;
