// Port of org.semanticweb.HermiT.tableau.MergingManager.
//
// Implements the merge rule: when two nodes are made equal, it picks the merge
// direction, prunes the successors of the merged-away node, copies that node's
// unary and binary assertions onto the surviving node, and finally records the
// merge. Driven from `add_assertion` on an `Equality`.
#![allow(dead_code)]

use crate::tableau::dependency_set::{DependencySet, UnionDependencySet};
use crate::tableau::node::NodeId;
use crate::tableau::node_type::NodeType;
use crate::tableau::object::TableauObject;
use crate::tableau::tableau::Tableau;
use crate::tableau::View;

impl Tableau {
    fn merge_precedence(&self, node: NodeId) -> i32 {
        self.nodes[node].get_node_type().get_merge_precedence()
    }

    pub(crate) fn cluster_anchor(&self, node: NodeId) -> Option<NodeId> {
        if self.nodes[node].get_node_type() == NodeType::TreeNode {
            Some(node)
        } else {
            self.nodes[node].parent
        }
    }

    fn is_descendant_of_at_most_three_levels(
        &self,
        descendant: Option<NodeId>,
        ancestor: Option<NodeId>,
    ) -> bool {
        if let Some(descendant) = descendant {
            let parent = self.nodes[descendant].parent;
            if parent == ancestor {
                return true;
            }
            if let Some(parent) = parent {
                let grandparent = self.nodes[parent].parent;
                if grandparent == ancestor {
                    return true;
                }
                if let Some(grandparent) = grandparent {
                    let great = self.nodes[grandparent].parent;
                    if great == ancestor {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Merges `node0` and `node1`, returning whether a merge happened.
    pub fn merge_nodes(
        &mut self,
        node0: NodeId,
        node1: NodeId,
        dependency_set: &DependencySet,
    ) -> bool {
        // MergingManager.mergeNodes: both nodes must share abstractness. Java checks
        // this assertion before the active/identity guard.
        debug_assert_eq!(
            self.nodes[node0].get_node_type().is_abstract(),
            self.nodes[node1].get_node_type().is_abstract()
        );
        if !self.nodes[node0].is_active() || !self.nodes[node1].is_active() || node0 == node1 {
            return false;
        }
        let (merge_from, merge_into) = self.choose_merge_direction(node0, node1);

        // MergingManager.mergeNodes line 114-115: mergeStarted(mergeFrom,mergeInto).
        self.monitor_event(|m| m.merge_started());

        // Prune the successors of merge_from.
        let mut node = Some(merge_from);
        while let Some(current) = node {
            let next = self.nodes[current].next_tableau_node;
            let parent = self.nodes[current].parent;
            if self.nodes[current].is_active() {
                if let Some(parent) = parent {
                    if !self.nodes[parent].is_active() || parent == merge_from {
                        // line 123-124: nodePruned(node) before pruneNode.
                        self.monitor_event(|m| m.node_pruned());
                        self.prune_node(current);
                    }
                }
            }
            node = next;
        }

        // Copy unary assertions (binary table, merge_from at position 1).
        let binary = self.create_binary_retrieval(
            [-1, 1],
            [None, Some(TableauObject::Node(merge_from))],
            View::Total,
        );
        for &tuple_index in &binary.tuple_indices {
            let predicate = self
                .binary_extension_table
                .get_tuple_object(tuple_index, 0)
                .clone();
            if matches!(predicate, TableauObject::DescriptionGraph(_)) {
                continue;
            }
            let assertion_dep = self
                .binary_extension_table
                .get_dependency_set(tuple_index, &self.dependency_set_factory.empty_set());
            let is_core = self.binary_extension_table.is_core(tuple_index);
            let union = self.merge_union(assertion_dep, dependency_set);
            // line 139-140: mergeFactStarted before the copy addTuple.
            self.monitor_event(|m| m.merge_fact_started());
            self.add_binary_object(predicate, merge_into, &union, is_core);
            // line 143-144: mergeFactFinished after the copy addTuple.
            self.monitor_event(|m| m.merge_fact_finished());
        }

        // Copy binary assertions where merge_from is in the first position.
        let ternary1 = self.create_ternary_retrieval(
            [-1, 1, -1],
            [None, Some(TableauObject::Node(merge_from)), None],
            View::Total,
        );
        for &tuple_index in &ternary1.tuple_indices {
            let predicate = self
                .ternary_extension_table
                .get_tuple_object(tuple_index, 0)
                .clone();
            if matches!(predicate, TableauObject::DescriptionGraph(_)) {
                continue;
            }
            let other = self
                .ternary_extension_table
                .get_tuple_object(tuple_index, 2)
                .as_node()
                .unwrap();
            let other = if other == merge_from { merge_into } else { other };
            let assertion_dep = self
                .ternary_extension_table
                .get_dependency_set(tuple_index, &self.dependency_set_factory.empty_set());
            let is_core = self.ternary_extension_table.is_core(tuple_index);
            let union = self.merge_union(assertion_dep, dependency_set);
            // line 158-159: mergeFactStarted before the copy addTuple (first position).
            self.monitor_event(|m| m.merge_fact_started());
            self.add_ternary_object(predicate, merge_into, other, &union, is_core);
            // line 162-163: mergeFactFinished after the copy addTuple.
            self.monitor_event(|m| m.merge_fact_finished());
        }

        // Copy binary assertions where merge_from is in the second position.
        let ternary2 = self.create_ternary_retrieval(
            [-1, -1, 2],
            [None, None, Some(TableauObject::Node(merge_from))],
            View::Total,
        );
        for &tuple_index in &ternary2.tuple_indices {
            let predicate = self
                .ternary_extension_table
                .get_tuple_object(tuple_index, 0)
                .clone();
            if matches!(predicate, TableauObject::DescriptionGraph(_)) {
                continue;
            }
            let other = self
                .ternary_extension_table
                .get_tuple_object(tuple_index, 1)
                .as_node()
                .unwrap();
            let other = if other == merge_from { merge_into } else { other };
            let assertion_dep = self
                .ternary_extension_table
                .get_dependency_set(tuple_index, &self.dependency_set_factory.empty_set());
            let is_core = self.ternary_extension_table.is_core(tuple_index);
            let union = self.merge_union(assertion_dep, dependency_set);
            // line 177-178: mergeFactStarted before the copy addTuple (second position).
            self.monitor_event(|m| m.merge_fact_started());
            self.add_ternary_object(predicate, other, merge_into, &union, is_core);
            // line 181-182: mergeFactFinished after the copy addTuple.
            self.monitor_event(|m| m.merge_fact_finished());
        }

        // MergingManager.mergeNodes line 186-188 --
        // m_descriptionGraphManager.mergeGraphs(mergeFrom,mergeInto,..): every
        // graph tuple in which `merge_from` occurs is re-recorded with
        // `merge_from` replaced by `merge_into`. A no-op when the ontology has no
        // description graphs.
        self.merge_graphs(merge_from, merge_into, dependency_set);

        // No Java counterpart: the standard unary loop above (lines 88-111) already
        // copied the ConstantEnumeration binary tuple from merge_from onto merge_into
        // with the correct union dependency set and source is_core flag, matching
        // MergingManager.java exactly. The constant_value field remains on Node for
        // the datatype clash check in datatype_manager.rs.
        self.merge_node(merge_from, merge_into, dependency_set);
        // MergingManager.mergeNodes line 191-192: mergeFinished(mergeFrom,mergeInto).
        self.monitor_event(|m| m.merge_finished());
        true
    }

    fn choose_merge_direction(&self, node0: NodeId, node1: NodeId) -> (NodeId, NodeId) {
        let p0 = self.merge_precedence(node0);
        let p1 = self.merge_precedence(node1);
        if p0 < p1 {
            (node1, node0)
        } else if p0 > p1 {
            (node0, node1)
        } else {
            let anchor0 = self.cluster_anchor(node0);
            let anchor1 = self.cluster_anchor(node1);
            let same_parent = self.nodes[node0].parent == self.nodes[node1].parent;
            let can_0_into_1 =
                same_parent || self.is_descendant_of_at_most_three_levels(Some(node0), anchor1);
            let can_1_into_0 =
                same_parent || self.is_descendant_of_at_most_three_levels(Some(node1), anchor0);
            if can_0_into_1 && can_1_into_0 {
                if self.nodes[node0].number_of_positive_atomic_concepts
                    > self.nodes[node1].number_of_positive_atomic_concepts
                {
                    (node1, node0)
                } else {
                    (node0, node1)
                }
            } else if can_0_into_1 {
                (node0, node1)
            } else if can_1_into_0 {
                (node1, node0)
            } else {
                panic!("Internal error: unsupported merge type.")
            }
        }
    }

    fn merge_union(
        &mut self,
        assertion_dependency_set: crate::tableau::dependency_set::PermanentDependencySet,
        merge_dependency_set: &DependencySet,
    ) -> DependencySet {
        let mut union = UnionDependencySet::new(2);
        union.add_constituent(DependencySet::Permanent(assertion_dependency_set));
        union.add_constituent(merge_dependency_set.clone());
        DependencySet::Union(union)
    }

    /// Adds a binary assertion given its label object (used by the merge copy).
    fn add_binary_object(
        &mut self,
        label: TableauObject,
        node: NodeId,
        dependency_set: &DependencySet,
        is_core: bool,
    ) -> bool {
        match label {
            TableauObject::Concept(c) => self.add_concept_assertion(c, node, dependency_set, is_core),
            TableauObject::DLPredicate(p) => {
                self.add_dl_predicate_assertion(p, node, dependency_set, is_core)
            }
            _ => false,
        }
    }

    /// Adds a ternary assertion given its label object (used by the merge copy).
    fn add_ternary_object(
        &mut self,
        label: TableauObject,
        node0: NodeId,
        node1: NodeId,
        dependency_set: &DependencySet,
        is_core: bool,
    ) -> bool {
        self.add_ternary(label, node0, node1, dependency_set, is_core)
    }
}

#[cfg(test)]
mod tests {
    use crate::model::{AtomicConcept, AtomicRole, Concept, Role};
    use crate::monitor::CountingMonitor;
    use crate::tableau::dependency_set::DependencySet;
    use crate::tableau::tableau::Tableau;

    /// Drives a real merge (C(a), r(a,c); merge a,b) and records the surviving
    /// node and its assertions, optionally with a `CountingMonitor` attached.
    /// Returns (survivor_carries_C, survivor_carries_r, optional counter).
    fn run_merge_scenario(with_monitor: bool) -> (bool, bool, Option<CountingMonitor>) {
        let mut tableau = Tableau::new();
        if with_monitor {
            tableau.set_monitor(Some(Box::new(CountingMonitor::new())));
        }
        let empty =
            DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let b = tableau.create_new_named_node(&empty);
        let c = tableau.create_new_named_node(&empty);

        let concept_c = Concept::AtomicConcept(AtomicConcept::create("http://example.org/C"));
        let concept_d = Concept::AtomicConcept(AtomicConcept::create("http://example.org/D"));
        let concept_e = Concept::AtomicConcept(AtomicConcept::create("http://example.org/E"));
        let role_r = Role::AtomicRole(AtomicRole::create("http://example.org/r"));

        // C(a), r(a,c) — these `add_*_assertion` calls go through add_binary /
        // add_ternary, so they exercise the addFactStarted/addFactFinished events.
        tableau.add_concept_assertion(concept_c.clone(), a, &empty, true);
        tableau.add_role_assertion(role_r.clone(), a, c, &empty, true);
        // D(b), E(b): give b a higher positive-atomic-concept count than a, so the
        // merge direction makes `a` the merge_from node and its C(a)/r(a,c)
        // assertions are *copied* onto b — exercising the mergeFact* events.
        tableau.add_concept_assertion(concept_d.clone(), b, &empty, true);
        tableau.add_concept_assertion(concept_e.clone(), b, &empty, true);

        // The merge exercises mergeStarted / nodePruned / mergeFactStarted /
        // mergeFactFinished / mergeFinished.
        assert!(tableau.merge_nodes(a, b, &empty));

        let survivor = tableau.get_canonical_node(a);
        let carries_c = tableau.contains_concept_assertion(&concept_c, survivor);
        let carries_r = tableau.contains_role_assertion(&role_r, survivor, c);

        let counter = if with_monitor {
            tableau
                .take_monitor()
                .and_then(|m| m.as_any().downcast::<CountingMonitor>().ok())
                .map(|b| *b)
        } else {
            None
        };
        (carries_c, carries_r, counter)
    }

    /// After a real merge run with a `CountingMonitor` attached, the new finer
    /// counters (added facts, merges, merge-facts, pruned nodes) are non-zero,
    /// and the reasoning RESULT (survivor's assertions) is identical with vs
    /// without the monitor — i.e. emission is answer-neutral.
    #[test]
    fn merge_emits_events_and_is_answer_neutral() {
        let (with_c, with_r, counter) = run_merge_scenario(true);
        let (without_c, without_r, none) = run_merge_scenario(false);

        // Answer-neutral: identical result with and without the monitor.
        assert!(none.is_none());
        assert_eq!(with_c, without_c);
        assert_eq!(with_r, without_r);
        assert!(with_c && with_r, "survivor must carry C and the r-edge");

        let counter = counter.expect("monitor attached, should yield a counter");
        // ExtensionManager addFact events fired for C(a)/r(a,c) and the merge copy.
        assert!(counter.number_of_added_facts > 0, "addFact events fired");
        // MergingManager mergeStarted fired exactly once for the one merge.
        assert_eq!(counter.number_of_merges, 1, "exactly one merge");
        // The merge copied the unary (C) and binary (r) assertions: mergeFact events.
        assert!(counter.number_of_merge_facts > 0, "mergeFact events fired");
    }
}
