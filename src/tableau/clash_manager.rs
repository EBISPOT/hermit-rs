// Port of org.semanticweb.HermiT.tableau.ClashManager.
//
// Notified when a tuple is added, it detects whether the addition caused a
// clash: an owl:Nothing / ¬rdfs:Literal / self-inequality assertion, a concept
// together with its negation, a role together with its negation, etc. Here it is
// an `impl` block on `Tableau`, driven from the extension manager's `postAdd`.
//
// The concrete-node inequality generation (for datatype completeness) IS
// implemented in clash_check_ternary (the `!is_abstract` branch), mirroring
// Java ClashManager.tupleAdded lines 112-137.
#![allow(dead_code)]

use crate::model::{
    AtomicConcept, AtomicDataRange, Concept, DLPredicate, InternalDatatype, LiteralConcept,
    LiteralDataRange, NegatedAtomicRole,
};
use crate::tableau::dependency_set::{DependencySet, PermanentDependencySet, UnionDependencySet};
use crate::tableau::node::NodeId;
use crate::tableau::object::TableauObject;
use crate::tableau::tableau::Tableau;

fn is_nothing_label(object: &TableauObject) -> bool {
    matches!(object,
        TableauObject::Concept(Concept::AtomicConcept(c)) if c == AtomicConcept::nothing())
}

/// `¬rdfs:Literal`, i.e. the negation of the internal rdfs:Literal datatype.
fn is_not_rdfs_literal_label(object: &TableauObject) -> bool {
    match object {
        TableauObject::DLPredicate(DLPredicate::AtomicNegationDataRange(r)) => {
            matches!(r.get_negated_data_range(), AtomicDataRange::InternalDatatype(d)
                if d == InternalDatatype::rdfs_literal())
        }
        _ => false,
    }
}

fn literal_data_range_to_predicate(range: LiteralDataRange) -> DLPredicate {
    match range {
        LiteralDataRange::DatatypeRestriction(r) => DLPredicate::DatatypeRestriction(r),
        LiteralDataRange::ConstantEnumeration(r) => DLPredicate::ConstantEnumeration(r),
        LiteralDataRange::InternalDatatype(r) => DLPredicate::InternalDatatype(r),
        LiteralDataRange::AtomicNegationDataRange(r) => DLPredicate::AtomicNegationDataRange(r),
    }
}

/// The negation of a binary-table label (concept or data range), or `None` if
/// the label is not one that participates in a binary clash.
fn negation_label(object: &TableauObject) -> Option<TableauObject> {
    match object {
        TableauObject::Concept(Concept::AtomicConcept(c)) => {
            Some(TableauObject::Concept(Concept::from(c.get_negation())))
        }
        TableauObject::Concept(Concept::AtomicNegationConcept(c)) => {
            let negation: LiteralConcept = c.get_negation();
            Some(TableauObject::Concept(Concept::from(negation)))
        }
        TableauObject::DLPredicate(DLPredicate::InternalDatatype(d)) => Some(
            TableauObject::DLPredicate(literal_data_range_to_predicate(d.get_negation())),
        ),
        TableauObject::DLPredicate(DLPredicate::AtomicNegationDataRange(r)) => Some(
            TableauObject::DLPredicate(literal_data_range_to_predicate(r.get_negation())),
        ),
        _ => None,
    }
}

impl Tableau {
    fn set_clash_union(&mut self, ds0: PermanentDependencySet, ds1: PermanentDependencySet) {
        let mut union = UnionDependencySet::new(2);
        union.add_constituent(DependencySet::Permanent(ds0));
        union.add_constituent(DependencySet::Permanent(ds1));
        self.set_clash(&DependencySet::Union(union));
    }

    pub(crate) fn clash_check_binary(
        &mut self,
        tuple: &[TableauObject],
        dependency_set: PermanentDependencySet,
    ) {
        let label = &tuple[0];
        let node0 = tuple[1].as_node().expect("binary tuple argument is a node");
        if is_nothing_label(label) || is_not_rdfs_literal_label(label) {
            // `ClashManager.tupleAdded`:76/79 — clashDetectionStarted/Finished
            // around the owl:Nothing / ¬rdfs:Literal setClash.
            self.monitor_event(|m| m.clash_detection_started());
            self.set_clash(&DependencySet::Permanent(dependency_set));
            self.monitor_event(|m| m.clash_detection_finished());
            return;
        }
        let should_check = match label {
            TableauObject::DLPredicate(DLPredicate::InternalDatatype(_)) => true,
            TableauObject::DLPredicate(DLPredicate::AtomicNegationDataRange(r)) => {
                matches!(r.get_negated_data_range(), AtomicDataRange::InternalDatatype(_))
            }
            TableauObject::Concept(Concept::AtomicConcept(_)) => {
                self.nodes[node0].number_of_negated_atomic_concepts > 0
            }
            TableauObject::Concept(Concept::AtomicNegationConcept(_)) => {
                self.nodes[node0].number_of_positive_atomic_concepts > 0
            }
            _ => false,
        };
        if should_check {
            if let Some(negation) = negation_label(label) {
                let aux = [negation, TableauObject::Node(node0)];
                let index = self.binary_extension_table.get_tuple_index(&aux);
                // Java tests `extensionTable.containsTuple(...)`, which requires
                // the tuple's node to be active in addition to existing.
                if index != -1 && self.nodes[node0].is_active() {
                    let empty = self.dependency_set_factory.empty_set();
                    let other = self
                        .binary_extension_table
                        .get_dependency_set(index as usize, &empty);
                    // `ClashManager.tupleAdded`:88/91 —
                    // clashDetectionStarted/Finished around the concept/negation
                    // (binary auxiliary tuple) setClash.
                    self.monitor_event(|m| m.clash_detection_started());
                    self.set_clash_union(dependency_set, other);
                    self.monitor_event(|m| m.clash_detection_finished());
                }
            }
        }
    }

    pub(crate) fn clash_check_ternary(
        &mut self,
        tuple: &[TableauObject],
        dependency_set: PermanentDependencySet,
    ) {
        let label = &tuple[0];
        let node0 = tuple[1].as_node().expect("ternary tuple argument is a node");
        let node1 = tuple[2].as_node().expect("ternary tuple argument is a node");
        if matches!(label, TableauObject::DLPredicate(DLPredicate::Inequality)) && node0 == node1 {
            // `ClashManager.tupleAdded`:76/79 — the self-inequality case shares
            // Java's first branch; clashDetectionStarted/Finished around setClash.
            self.monitor_event(|m| m.clash_detection_started());
            self.set_clash(&DependencySet::Permanent(dependency_set));
            self.monitor_event(|m| m.clash_detection_finished());
            return;
        }
        let search_predicate = match label {
            TableauObject::DLPredicate(DLPredicate::AtomicRole(r))
                if self.nodes[node0].number_of_negated_role_assertions > 0 =>
            {
                Some(TableauObject::NegatedAtomicRole(NegatedAtomicRole::create(r.clone())))
            }
            TableauObject::NegatedAtomicRole(r) => Some(TableauObject::DLPredicate(
                DLPredicate::AtomicRole(r.get_negated_atomic_role().clone()),
            )),
            _ => None,
        };
        if let Some(search_predicate) = search_predicate {
            let aux = [
                search_predicate.clone(),
                TableauObject::Node(node0),
                TableauObject::Node(node1),
            ];
            let index = self.ternary_extension_table.get_tuple_index(&aux);
            // Java tests `extensionTable.containsTuple(...)`, which requires both
            // of the tuple's nodes to be active in addition to existing.
            if index != -1 && self.nodes[node0].is_active() && self.nodes[node1].is_active() {
                let empty = self.dependency_set_factory.empty_set();
                let other = self
                    .ternary_extension_table
                    .get_dependency_set(index as usize, &empty);
                // `ClashManager.tupleAdded`:107/110 —
                // clashDetectionStarted/Finished around the role/negation (ternary
                // auxiliary tuple) setClash.
                self.monitor_event(|m| m.clash_detection_started());
                self.set_clash_union(dependency_set, other);
                self.monitor_event(|m| m.clash_detection_finished());
            } else if !self.nodes[node1].get_node_type().is_abstract() {
                // ClashManager.tupleAdded, the `else if (!((Node)tuple[2])
                // .getNodeType().isAbstract())` branch: node1 (tuple[2]) is a
                // concrete node, so the negated role r and the positive role r
                // jointly demand that node1 differ in value from every other
                // r-successor of node0. We enumerate those successors and add an
                // `Inequality(node1, successor)` for each, so the datatype manager
                // can detect a value-space clash.
                let empty = self.dependency_set_factory.empty_set();
                // Search r(node0, ?) — `searchPredicate` with the first two
                // positions bound. (When `label` is a positive AtomicRole the
                // search predicate is its negation, and vice versa; either way
                // we look for the *other* polarity's successors of node0.)
                let retrieval = self.create_ternary_retrieval(
                    [0, 1, -1],
                    [
                        Some(search_predicate),
                        Some(TableauObject::Node(node0)),
                        None,
                    ],
                    // Java (ClashManager.java:55) builds this retrieval with
                    // View.TOTAL; we match it exactly here — Total scans
                    // 0..after_delta_new, covering every r-successor that holds.
                    crate::tableau::View::Total,
                );
                // Collect (target, dependencySet) under the immutable borrow, then
                // add the inequalities (which mutates the tableau).
                let mut targets: Vec<(NodeId, PermanentDependencySet)> = Vec::new();
                for &tuple_index in &retrieval.tuple_indices {
                    let target = self
                        .ternary_extension_table
                        .get_tuple_object(tuple_index, 2)
                        .as_node()
                        .expect("ternary tuple argument is a node");
                    let other = self
                        .ternary_extension_table
                        .get_dependency_set(tuple_index, &empty);
                    targets.push((target, other));
                }
                for (target, other) in targets {
                    let mut union = UnionDependencySet::new(2);
                    union.add_constituent(DependencySet::Permanent(dependency_set.clone()));
                    union.add_constituent(DependencySet::Permanent(other));
                    // `ClashManager.tupleAdded`:126/134 —
                    // clashDetectionStarted/Finished around each generated
                    // Inequality addition in the concrete-successor loop.
                    self.monitor_event(|m| m.clash_detection_started());
                    // Inequality(node1, target). This add happens during another
                    // add's postAdd, so it goes straight to the table via
                    // `add_ternary_core`, exactly as HermiT calls
                    // `m_ternaryExtensionTable.addTuple` to bypass the reentrancy
                    // guard (an Inequality tuple only triggers the self-inequality
                    // clash check, which terminates).
                    self.add_ternary_core(
                        TableauObject::DLPredicate(DLPredicate::Inequality),
                        node1,
                        target,
                        &DependencySet::Union(union),
                        true,
                    );
                    self.monitor_event(|m| m.clash_detection_finished());
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::AtomicRole;

    /// When `¬dp(a, c2)` is added and `dp(a, c1)` already holds (c1, c2 both
    /// concrete and distinct), ClashManager must enumerate the other dp-successors
    /// of `a` and add `Inequality(c2, c1)` so the datatype manager can detect a
    /// value-space clash. Mirrors ClashManager.tupleAdded's `!isAbstract()` branch.
    #[test]
    fn concrete_negated_role_generates_inequalities() {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty);
        let c1 = tableau.create_new_concrete_node(&empty, a);
        let c2 = tableau.create_new_concrete_node(&empty, a);

        let dp = AtomicRole::create("http://example.org/dp");
        // dp(a, c1): a positive role assertion to a concrete node.
        tableau.add_ternary(
            TableauObject::DLPredicate(DLPredicate::AtomicRole(dp.clone())),
            a,
            c1,
            &empty,
            true,
        );
        // No inequality yet.
        let ineq_c2_c1 = [
            TableauObject::DLPredicate(DLPredicate::Inequality),
            TableauObject::Node(c2),
            TableauObject::Node(c1),
        ];
        assert_eq!(tableau.ternary_extension_table.get_tuple_index(&ineq_c2_c1), -1);

        // ¬dp(a, c2): the negated role assertion to another concrete node triggers
        // the concrete-successor branch, which should add Inequality(c2, c1).
        tableau.add_ternary(
            TableauObject::NegatedAtomicRole(NegatedAtomicRole::create(dp.clone())),
            a,
            c2,
            &empty,
            true,
        );
        assert_ne!(
            tableau.ternary_extension_table.get_tuple_index(&ineq_c2_c1),
            -1,
            "ClashManager should have generated Inequality(c2, c1)"
        );
    }
}
