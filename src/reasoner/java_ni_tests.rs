// Mechanically ported from java 37ec30ac: tableau.NIRuleTest.
// Regenerate with scripts/java-tests/port_ni.py.
#![allow(non_snake_case, unused_mut, unused_variables)]
use super::*;
use crate::model::*;
use crate::tableau::DependencySetOps;
#[test]
fn testNIRuleDeterministic() {
    let (mut t, mut manager) = ni_tableau();
    let Symbols {
        A,
        B,
        NEG_A,
        R,
        S,
        T,
        AT_MOST_ONE_R_A,
        AT_MOST_TWO_R_A,
        EQ_ONE_R_A,
        EQ_TWO_R_A,
        EQ_ONE_S_A,
    } = symbols();
    let mut emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let mut a = t.create_new_ni_node(&emptySet);
    let mut b = t.create_new_ni_node(&emptySet);
    let mut b1 = t.create_new_tree_node(&emptySet, b);
    let mut b11 = t.create_new_tree_node(&emptySet, b1);
    let mut b111 = t.create_new_tree_node(&emptySet, b11);
    add(&mut t, S, &[b, b1], &emptySet, false);
    add(&mut t, S, &[b1, b11], &emptySet, false);
    add(&mut t, S, &[b11, b111], &emptySet, false);
    add(&mut t, R, &[a, b11], &emptySet, false);
    add(&mut t, A, &[b11], &emptySet, false);
    assert_eq!(0, t.annotated_equalities.len());
    t.add_annotated_equality(&eq(EQ_ONE_R_A), b11, b11, a, &emptySet);
    assert_eq!(0, t.annotated_equalities.len());
    let mut newRoot = root(&t, a, EQ_ONE_R_A, 1);
    assert!(t.nodes[newRoot].is_active());
    assert!(!(t.nodes[b11].is_active()));
    assert_eq!(newRoot, t.get_canonical_node(b11));
    assert!(!(t.nodes[b111].is_active()));
    assert!(!(contains(&t, S, &[b11, b111])));
    assert!(contains(&t, S, &[b1, newRoot]));
    assert_dependency(dependency(&t, S, &[b1, newRoot]), &[]);
    assert!(contains(&t, R, &[a, newRoot]));
    assert_dependency(dependency(&t, R, &[a, newRoot]), &[]);
}
#[test]
fn testNondeterministicEquality() {
    let (mut t, mut manager) = ni_tableau();
    let Symbols {
        A,
        B,
        NEG_A,
        R,
        S,
        T,
        AT_MOST_ONE_R_A,
        AT_MOST_TWO_R_A,
        EQ_ONE_R_A,
        EQ_TWO_R_A,
        EQ_ONE_S_A,
    } = symbols();
    let mut emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let mut a = t.create_new_ni_node(&emptySet);
    let mut b = t.create_new_ni_node(&emptySet);
    let mut b1 = t.create_new_tree_node(&emptySet, b);
    let mut b11 = t.create_new_tree_node(&emptySet, b1);
    let mut b111 = t.create_new_tree_node(&emptySet, b11);
    add(&mut t, S, &[b, b1], &emptySet, false);
    add(&mut t, S, &[b1, b11], &emptySet, false);
    add(&mut t, S, &[b11, b111], &emptySet, false);
    add(&mut t, R, &[a, b11], &emptySet, false);
    add(&mut t, A, &[b11], &emptySet, false);
    assert_eq!(0, t.annotated_equalities.len());
    t.add_annotated_equality(&eq(EQ_TWO_R_A), b11, b11, a, &emptySet);
    assert_eq!(1, t.annotated_equalities.len());
    let mut newRoot1 = root(&t, a, EQ_TWO_R_A, 1);
    assert_eq!(newRoot1, usize::MAX);
    assert!(t.nodes[b11].is_active());
    assert!(t.nodes[b111].is_active());
    assert!(do_iteration(&mut t, &mut manager, None));
    newRoot1 = root(&t, a, EQ_TWO_R_A, 1);
    assert!(t.nodes[newRoot1].is_active());
    assert!(!(t.nodes[b11].is_active()));
    assert_eq!(newRoot1, t.get_canonical_node(b11));
    assert!(!(t.nodes[b111].is_active()));
    assert!(!(contains(&t, S, &[b11, b111])));
    assert!(contains(&t, S, &[b1, newRoot1]));
    assert_dependency(dependency(&t, S, &[b1, newRoot1]), &[0]);
    assert!(contains(&t, R, &[a, newRoot1]));
    assert_dependency(dependency(&t, R, &[a, newRoot1]), &[0]);
    add(&mut t, NEG_A, &[newRoot1], &emptySet, false);
    assert!(do_iteration(&mut t, &mut manager, None));
    newRoot1 = root(&t, a, EQ_TWO_R_A, 1);
    assert_eq!(newRoot1, usize::MAX);
    let mut newRoot2 = root(&t, a, EQ_TWO_R_A, 2);
    assert!(t.nodes[newRoot2].is_active());
    assert!(!(t.nodes[b11].is_active()));
    assert_eq!(newRoot2, t.get_canonical_node(b11));
    assert!(!(t.nodes[b111].is_active()));
    assert!(!(contains(&t, S, &[b11, b111])));
    assert!(contains(&t, S, &[b1, newRoot2]));
    assert_dependency(dependency(&t, S, &[b1, newRoot2]), &[]);
    assert!(contains(&t, R, &[a, newRoot2]));
    assert_dependency(dependency(&t, R, &[a, newRoot2]), &[]);
    add(&mut t, NEG_A, &[newRoot2], &emptySet, false);
    assert!(!(do_iteration(&mut t, &mut manager, None)));
}
#[test]
fn testNIPrunesOneNode() {
    let (mut t, mut manager) = ni_tableau();
    let Symbols {
        A,
        B,
        NEG_A,
        R,
        S,
        T,
        AT_MOST_ONE_R_A,
        AT_MOST_TWO_R_A,
        EQ_ONE_R_A,
        EQ_TWO_R_A,
        EQ_ONE_S_A,
    } = symbols();
    let mut emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let mut a = t.create_new_ni_node(&emptySet);
    let mut b = t.create_new_ni_node(&emptySet);
    let mut b1 = t.create_new_tree_node(&emptySet, b);
    let mut b11 = t.create_new_tree_node(&emptySet, b1);
    let mut b111 = t.create_new_tree_node(&emptySet, b11);
    add(&mut t, S, &[b, b1], &emptySet, false);
    add(&mut t, S, &[b1, b11], &emptySet, false);
    add(&mut t, S, &[b11, b111], &emptySet, false);
    add(&mut t, R, &[a, b1], &emptySet, false);
    add(&mut t, R, &[a, b11], &emptySet, false);
    add(&mut t, A, &[b11], &emptySet, false);
    assert_eq!(0, t.annotated_equalities.len());
    t.add_annotated_equality(&eq(EQ_ONE_R_A), b1, b11, a, &emptySet);
    assert_eq!(0, t.annotated_equalities.len());
    let mut newRoot = root(&t, a, EQ_ONE_R_A, 1);
    assert!(t.nodes[newRoot].is_active());
    assert!(t.nodes[b1].is_merged());
    assert_eq!(newRoot, t.get_canonical_node(b1));
    assert!(t.nodes[b11].is_pruned());
    assert!(t.nodes[b111].is_pruned());
    assert!(!(contains(&t, A, &[newRoot])));
    assert!(contains(&t, R, &[a, newRoot]));
    assert!(contains(&t, S, &[b, newRoot]));
}
#[test]
fn testNIDoesNotPrune() {
    let (mut t, mut manager) = ni_tableau();
    let Symbols {
        A,
        B,
        NEG_A,
        R,
        S,
        T,
        AT_MOST_ONE_R_A,
        AT_MOST_TWO_R_A,
        EQ_ONE_R_A,
        EQ_TWO_R_A,
        EQ_ONE_S_A,
    } = symbols();
    let mut emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let mut a = t.create_new_ni_node(&emptySet);
    let mut b = t.create_new_ni_node(&emptySet);
    let mut b1 = t.create_new_tree_node(&emptySet, b);
    let mut b11 = t.create_new_tree_node(&emptySet, b1);
    let mut c = t.create_new_ni_node(&emptySet);
    let mut c1 = t.create_new_tree_node(&emptySet, c);
    let mut c11 = t.create_new_tree_node(&emptySet, c1);
    add(&mut t, S, &[b, b1], &emptySet, false);
    add(&mut t, S, &[b1, b11], &emptySet, false);
    add(&mut t, A, &[b1], &emptySet, false);
    add(&mut t, R, &[a, b1], &emptySet, false);
    add(&mut t, T, &[c, c1], &emptySet, false);
    add(&mut t, T, &[c1, c11], &emptySet, false);
    add(&mut t, B, &[c1], &emptySet, false);
    add(&mut t, R, &[a, c1], &emptySet, false);
    assert_eq!(0, t.annotated_equalities.len());
    t.add_annotated_equality(&eq(EQ_ONE_R_A), b1, c1, a, &emptySet);
    assert_eq!(0, t.annotated_equalities.len());
    let mut newRoot = root(&t, a, EQ_ONE_R_A, 1);
    assert!(t.nodes[newRoot].is_active());
    assert!(t.nodes[b1].is_merged());
    assert_eq!(newRoot, t.get_canonical_node(b1));
    assert!(t.nodes[b11].is_pruned());
    assert!(t.nodes[c11].is_pruned());
    assert!(contains(&t, A, &[newRoot]));
    assert!(contains(&t, B, &[newRoot]));
    assert!(contains(&t, R, &[a, newRoot]));
    assert!(contains(&t, S, &[b, newRoot]));
    assert!(contains(&t, T, &[c, newRoot]));
}
#[test]
fn testRepeatedNIApplications() {
    let (mut t, mut manager) = ni_tableau();
    let Symbols {
        A,
        B,
        NEG_A,
        R,
        S,
        T,
        AT_MOST_ONE_R_A,
        AT_MOST_TWO_R_A,
        EQ_ONE_R_A,
        EQ_TWO_R_A,
        EQ_ONE_S_A,
    } = symbols();
    let mut emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let mut a = t.create_new_ni_node(&emptySet);
    let mut b = t.create_new_ni_node(&emptySet);
    let mut b1 = t.create_new_tree_node(&emptySet, b);
    add(&mut t, S, &[b, b1], &emptySet, false);
    add(&mut t, R, &[a, b1], &emptySet, false);
    add(&mut t, A, &[b1], &emptySet, false);
    t.add_annotated_equality(&eq(EQ_TWO_R_A), b1, b1, a, &emptySet);
    assert_eq!(root(&t, a, EQ_TWO_R_A, 1), usize::MAX);
    assert!(do_iteration(&mut t, &mut manager, None));
    let mut a_n1 = root(&t, a, EQ_TWO_R_A, 1);
    assert_eq!(a_n1, t.get_canonical_node(b1));
    assert!(contains(&t, A, &[a_n1]));
    assert_dependency(dependency(&t, A, &[a_n1]), &[0]);
    let mut b11 = t.create_new_tree_node(&emptySet, a_n1);
    add(&mut t, S, &[a_n1, b11], &emptySet, false);
    add(&mut t, R, &[a, b11], &emptySet, false);
    add(&mut t, A, &[b11], &emptySet, false);
    t.add_annotated_equality(&eq(EQ_TWO_R_A), b11, b11, a, &emptySet);
    assert!(do_iteration(&mut t, &mut manager, None));
    assert_eq!(a_n1, t.get_canonical_node(b11));
    assert!(contains(&t, S, &[a_n1, a_n1]));
    assert_dependency(dependency(&t, S, &[a_n1, a_n1]), &[1]);
    let saved_dependency = dependency(&t, S, &[a_n1, a_n1]);
    add(
        &mut t,
        NEG_A,
        &[a_n1],
        &DependencySet::Permanent(saved_dependency),
        false,
    );
    assert!(do_iteration(&mut t, &mut manager, None));
    let mut a_n2 = root(&t, a, EQ_TWO_R_A, 2);
    assert_ne!(a_n1, a_n2);
    assert_eq!(a_n2, t.get_canonical_node(b11));
    assert!(!(contains(&t, S, &[a_n1, a_n1])));
    assert!(contains(&t, S, &[a_n1, a_n2]));
    assert!(!(contains(&t, S, &[a_n2, a_n2])));
}
#[test]
fn testContentingNIs() {
    let (mut t, mut manager) = ni_tableau();
    let Symbols {
        A,
        B,
        NEG_A,
        R,
        S,
        T,
        AT_MOST_ONE_R_A,
        AT_MOST_TWO_R_A,
        EQ_ONE_R_A,
        EQ_TWO_R_A,
        EQ_ONE_S_A,
    } = symbols();
    let mut emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let mut a = t.create_new_ni_node(&emptySet);
    let mut b = t.create_new_ni_node(&emptySet);
    let mut c = t.create_new_ni_node(&emptySet);
    let mut c1 = t.create_new_tree_node(&emptySet, c);
    let mut d = t.create_new_ni_node(&emptySet);
    let mut d1 = t.create_new_tree_node(&emptySet, d);
    add(&mut t, T, &[c, c1], &emptySet, false);
    add(&mut t, A, &[c1], &emptySet, false);
    add(&mut t, R, &[c1, a], &emptySet, false);
    add(&mut t, S, &[c1, b], &emptySet, false);
    add(&mut t, T, &[d, d1], &emptySet, false);
    add(&mut t, B, &[d1], &emptySet, false);
    add(&mut t, R, &[d1, a], &emptySet, false);
    add(&mut t, S, &[d1, b], &emptySet, false);
    t.add_annotated_equality(&eq(EQ_TWO_R_A), c1, d1, a, &emptySet);
    assert!(t.nodes[c1].is_active());
    assert!(t.nodes[d1].is_active());
    t.add_annotated_equality(&eq(EQ_ONE_S_A), d1, d1, b, &emptySet);
    let mut b_n1 = root(&t, b, EQ_ONE_S_A, 1);
    assert_eq!(b_n1, t.get_canonical_node(d1));
    assert!(do_iteration(&mut t, &mut manager, None));
    assert_eq!(root(&t, a, EQ_TWO_R_A, 1), usize::MAX);
    assert_eq!(root(&t, a, EQ_TWO_R_A, 2), usize::MAX);
    assert_eq!(b_n1, t.get_canonical_node(c1));
    assert_eq!(1, t.annotated_equalities.len());
    assert!(contains(&t, T, &[c, b_n1]));
    assert_dependency(dependency(&t, T, &[c, b_n1]), &[]);
}
#[test]
fn testNIAndPruning() {
    let (mut t, mut manager) = ni_tableau();
    let Symbols {
        A,
        B,
        NEG_A,
        R,
        S,
        T,
        AT_MOST_ONE_R_A,
        AT_MOST_TWO_R_A,
        EQ_ONE_R_A,
        EQ_TWO_R_A,
        EQ_ONE_S_A,
    } = symbols();
    let mut emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let mut a = t.create_new_ni_node(&emptySet);
    let mut a1 = t.create_new_tree_node(&emptySet, a);
    let mut b = t.create_new_ni_node(&emptySet);
    let mut b1 = t.create_new_tree_node(&emptySet, b);
    let mut b11 = t.create_new_tree_node(&emptySet, b1);
    let mut c = t.create_new_ni_node(&emptySet);
    add(&mut t, S, &[a, a1], &emptySet, false);
    add(&mut t, R, &[c, a1], &emptySet, false);
    add(&mut t, T, &[b, b1], &emptySet, false);
    add(&mut t, T, &[b1, b11], &emptySet, false);
    add(&mut t, R, &[c, b11], &emptySet, false);
    t.add_annotated_equality(&eq(EQ_TWO_R_A), a1, b11, c, &emptySet);
    add(&mut t, DLPredicate::Equality, &[b1, c], &emptySet, false);
    assert!(t.nodes[b11].is_pruned());
    assert!(do_iteration(&mut t, &mut manager, None));
    assert!(t.nodes[a1].is_active());
    assert_eq!(1, t.annotated_equalities.len());
}
#[test]
fn testDeterministicRuleApplication() {
    let (mut t, mut manager) = ni_tableau();
    let Symbols {
        A,
        B,
        NEG_A,
        R,
        S,
        T,
        AT_MOST_ONE_R_A,
        AT_MOST_TWO_R_A,
        EQ_ONE_R_A,
        EQ_TWO_R_A,
        EQ_ONE_S_A,
    } = symbols();
    let mut emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let mut a = t.create_new_ni_node(&emptySet);
    let mut a1 = t.create_new_tree_node(&emptySet, a);
    let mut b = t.create_new_ni_node(&emptySet);
    let mut b1 = t.create_new_tree_node(&emptySet, b);
    let mut c = t.create_new_ni_node(&emptySet);
    add(&mut t, S, &[a, a1], &emptySet, false);
    add(&mut t, R, &[c, a1], &emptySet, false);
    add(&mut t, A, &[a1], &emptySet, false);
    add(&mut t, S, &[b, b1], &emptySet, false);
    add(&mut t, R, &[c, b1], &emptySet, false);
    add(&mut t, A, &[b1], &emptySet, false);
    add(&mut t, AT_MOST_ONE_R_A, &[c], &emptySet, false);
    assert!(do_iteration(&mut t, &mut manager, None));
    let mut c_n1 = root(&t, c, EQ_ONE_R_A, 1);
    assert_eq!(c_n1, t.get_canonical_node(a1));
    assert_eq!(c_n1, t.get_canonical_node(b1));
    assert!(contains(&t, S, &[a, c_n1]));
    assert!(contains(&t, S, &[b, c_n1]));
    assert!(contains(&t, R, &[c, c_n1]));
}
#[test]
fn testDisjunctionDerivation() {
    let (mut t, mut manager) = ni_tableau();
    let Symbols {
        A,
        B,
        NEG_A,
        R,
        S,
        T,
        AT_MOST_ONE_R_A,
        AT_MOST_TWO_R_A,
        EQ_ONE_R_A,
        EQ_TWO_R_A,
        EQ_ONE_S_A,
    } = symbols();
    let mut emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let mut a = t.create_new_ni_node(&emptySet);
    let mut a1 = t.create_new_tree_node(&emptySet, a);
    let mut b = t.create_new_ni_node(&emptySet);
    let mut b1 = t.create_new_tree_node(&emptySet, b);
    let mut c = t.create_new_ni_node(&emptySet);
    add(&mut t, S, &[a, a1], &emptySet, false);
    add(&mut t, R, &[c, a1], &emptySet, false);
    add(&mut t, A, &[a1], &emptySet, false);
    add(&mut t, S, &[b, b1], &emptySet, false);
    add(&mut t, R, &[c, b1], &emptySet, false);
    add(&mut t, A, &[b1], &emptySet, false);
    add(&mut t, AT_MOST_TWO_R_A, &[c], &emptySet, false);
    assert!(do_iteration(&mut t, &mut manager, None));
    assert_disjunctions(&t,false,&["[2 == 2]@atMost(2 <R> <A>)(5) v [2 == 2]@atMost(2 <R> <A>)(5) v [2 == 2]@atMost(2 <R> <A>)(5)","[4 == 4]@atMost(2 <R> <A>)(5) v [4 == 4]@atMost(2 <R> <A>)(5) v [4 == 4]@atMost(2 <R> <A>)(5)"]);
    assert!(do_iteration(&mut t, &mut manager, None));
    assert_eq!(1, t.annotated_equalities.len());
    assert!(t.nodes[a1].is_active());
    assert!(t.nodes[b1].is_active());
    assert!(do_iteration(&mut t, &mut manager, None));
    let mut c_n1 = root(&t, c, EQ_TWO_R_A, 1);
    assert_eq!(c_n1, t.get_canonical_node(a1));
    assert!(!(t.nodes[b1].is_merged()));
    assert_disjunctions(&t,true,&["[4 == 4]@atMost(2 <R> <A>)(5) v [4 == 4]@atMost(2 <R> <A>)(5) v [4 == 4]@atMost(2 <R> <A>)(5)"]);
    assert!(do_iteration(&mut t, &mut manager, None));
    assert_eq!(2, t.annotated_equalities.len());
    assert!(t.nodes[b1].is_active());
    assert!(do_iteration(&mut t, &mut manager, None));
    assert_eq!(c_n1, t.get_canonical_node(a1));
    assert_eq!(c_n1, t.get_canonical_node(b1));
    assert_disjunctions(&t, true, &[]);
    assert!(!(do_iteration(&mut t, &mut manager, None)));
}
#[test]
fn testDisjunctionsInTreePart() {
    let (mut t, mut manager) = ni_tableau();
    let Symbols {
        A,
        B,
        NEG_A,
        R,
        S,
        T,
        AT_MOST_ONE_R_A,
        AT_MOST_TWO_R_A,
        EQ_ONE_R_A,
        EQ_TWO_R_A,
        EQ_ONE_S_A,
    } = symbols();
    let mut emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let mut a = t.create_new_ni_node(&emptySet);
    let mut a1 = t.create_new_tree_node(&emptySet, a);
    let mut a11 = t.create_new_tree_node(&emptySet, a1);
    let mut a12 = t.create_new_tree_node(&emptySet, a1);
    add(&mut t, R, &[a1, a11], &emptySet, false);
    add(&mut t, A, &[a11], &emptySet, false);
    add(&mut t, R, &[a1, a12], &emptySet, false);
    add(&mut t, A, &[a12], &emptySet, false);
    add(&mut t, AT_MOST_TWO_R_A, &[a1], &emptySet, false);
    assert!(do_iteration(&mut t, &mut manager, None));
    assert_disjunctions(&t, false, &[]);
}

#[allow(non_snake_case)]
struct Symbols {
    A: DLPredicate,
    B: DLPredicate,
    NEG_A: DLPredicate,
    R: DLPredicate,
    S: DLPredicate,
    T: DLPredicate,
    AT_MOST_ONE_R_A: DLPredicate,
    AT_MOST_TWO_R_A: DLPredicate,
    EQ_ONE_R_A: DLPredicate,
    EQ_TWO_R_A: DLPredicate,
    EQ_ONE_S_A: DLPredicate,
}
fn symbols() -> Symbols {
    let c = |s| DLPredicate::AtomicConcept(AtomicConcept::create(s));
    let role = |s| DLPredicate::AtomicRole(AtomicRole::create(s));
    let eq = |n, r| {
        DLPredicate::AnnotatedEquality(AnnotatedEquality::create(
            n,
            Role::AtomicRole(AtomicRole::create(r)),
            LiteralConcept::AtomicConcept(AtomicConcept::create("A")),
        ))
    };
    Symbols {
        A: c("A"),
        B: c("B"),
        NEG_A: DLPredicate::AtomicConcept(AtomicConcept::create("NEG_A")),
        R: role("R"),
        S: role("S"),
        T: role("T"),
        AT_MOST_ONE_R_A: c("AT_MOST_ONE_R_A"),
        AT_MOST_TWO_R_A: c("AT_MOST_TWO_R_A"),
        EQ_ONE_R_A: eq(1, "R"),
        EQ_TWO_R_A: eq(2, "R"),
        EQ_ONE_S_A: eq(1, "S"),
    }
}
fn eq(p: DLPredicate) -> AnnotatedEquality {
    if let DLPredicate::AnnotatedEquality(e) = p {
        e
    } else {
        panic!("equality")
    }
}
fn root(t: &Tableau, n: NodeId, p: DLPredicate, i: i32) -> NodeId {
    t.ni_roots
        .get(&(n, eq(p), i))
        .copied()
        .unwrap_or(usize::MAX)
}
fn add(t: &mut Tableau, p: DLPredicate, n: &[NodeId], ds: &DependencySet, core: bool) {
    match p {
        DLPredicate::AtomicConcept(c) => {
            let concept = if c.iri() == "NEG_A" {
                Concept::AtomicNegationConcept(AtomicNegationConcept::create(
                    AtomicConcept::create("A"),
                ))
            } else {
                Concept::AtomicConcept(c)
            };
            t.add_concept_assertion(concept, n[0], ds, core);
        }
        DLPredicate::AtomicRole(r) => {
            t.add_role_assertion(Role::AtomicRole(r), n[0], n[1], ds, core);
        }
        DLPredicate::Equality => {
            t.merge_nodes(n[0], n[1], ds);
        }
        _ => panic!("unexpected predicate"),
    }
}
fn contains(t: &Tableau, p: DLPredicate, n: &[NodeId]) -> bool {
    if n.len() == 1 {
        t.contains_assertion_unary(&p, n[0])
    } else {
        t.contains_assertion_binary(&p, n[0], n[1])
    }
}
fn dependency(t: &Tableau, p: DLPredicate, n: &[NodeId]) -> crate::tableau::PermanentDependencySet {
    let mut tuple = vec![match p {
        DLPredicate::AtomicConcept(c) => TableauObject::Concept(Concept::AtomicConcept(c)),
        _ => TableauObject::DLPredicate(p),
    }];
    tuple.extend(n.iter().map(|n| TableauObject::Node(*n)));
    let table = if n.len() == 1 {
        &t.binary_extension_table
    } else {
        &t.ternary_extension_table
    };
    table
        .get_dependency_set(
            table.get_tuple_index(&tuple) as usize,
            &t.dependency_set_factory.empty_set(),
        )
        .clone()
}
fn assert_dependency(ds: crate::tableau::PermanentDependencySet, expected: &[i32]) {
    let got: Vec<_> = (0..=ds.get_maximum_branching_point())
        .filter(|i| ds.contains_branching_point(*i))
        .collect();
    assert_eq!(got, expected);
}
fn ni_tableau() -> (Tableau, HyperresolutionManager) {
    let Symbols {
        A,
        B,
        R,
        AT_MOST_ONE_R_A,
        AT_MOST_TWO_R_A,
        EQ_ONE_R_A,
        EQ_TWO_R_A,
        ..
    } = symbols();
    let atom = |p, names: &[&str]| {
        Atom::create(
            p,
            names
                .iter()
                .map(|n| Term::Variable(Variable::create(*n)))
                .collect(),
        )
    };
    let clauses = vec![
        DLClause::create(
            vec![atom(A, &["X"]), atom(B, &["X"])],
            vec![atom(B, &["X"])],
        ),
        DLClause::create(
            vec![atom(EQ_ONE_R_A, &["Y1", "Y2", "X"])],
            vec![
                atom(AT_MOST_ONE_R_A, &["X"]),
                atom(R, &["X", "Y1"]),
                atom(A, &["Y1"]),
                atom(R, &["X", "Y2"]),
                atom(A, &["Y2"]),
            ],
        ),
        DLClause::create(
            vec![
                atom(EQ_TWO_R_A, &["Y1", "Y2", "X"]),
                atom(EQ_TWO_R_A, &["Y2", "Y3", "X"]),
                atom(EQ_TWO_R_A, &["Y1", "Y3", "X"]),
            ],
            vec![
                atom(AT_MOST_TWO_R_A, &["X"]),
                atom(R, &["X", "Y1"]),
                atom(A, &["Y1"]),
                atom(R, &["X", "Y2"]),
                atom(A, &["Y2"]),
                atom(R, &["X", "Y3"]),
                atom(A, &["Y3"]),
                atom(DLPredicate::NodeIdLessEqualThan, &["Y1", "Y2"]),
                atom(DLPredicate::NodeIdLessEqualThan, &["Y2", "Y3"]),
                atom(
                    DLPredicate::NodeIDsAscendingOrEqual(NodeIDsAscendingOrEqual::create(3)),
                    &["Y1", "Y2", "Y3"],
                ),
            ],
        ),
    ];
    let dl = DLOntology::new(
        "test",
        clauses.into_iter().collect(),
        Default::default(),
        Default::default(),
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        false,
        true,
        false,
        false,
    );
    let config = crate::configuration::Configuration {
        blocking_strategy_type: crate::configuration::BlockingStrategyType::Anywhere,
        direct_blocking_type: crate::configuration::DirectBlockingType::PairWise,
        ..Default::default()
    };
    let r = Reasoner::with_configuration(&dl, config);
    let manager = r.new_manager();
    (r.build_test_tableau(&manager), manager)
}
fn assert_disjunctions(t: &Tableau, only_unsatisfied: bool, expected: &[&str]) {
    let mut actual = std::collections::BTreeSet::new();
    let mut current = t.first_unprocessed_ground_disjunction;
    while let Some(index) = current {
        let gd = t.ground_disjunctions[index].as_ref().unwrap();
        if !only_unsatisfied || !t.ground_disjunction_satisfied(index) {
            let header = t.ground_disjunction_header_manager.header(gd.header_index);
            let parts: Vec<_> = header
                .dl_predicates()
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    let start = header.disjunct_start(i);
                    let args = gd.arguments[start..start + p.arity()]
                        .iter()
                        .map(|n| Term::Variable(Variable::create((n + 1).to_string())))
                        .collect();
                    Atom::create(*p, args).to_string_prefixes(&crate::prefixes::Prefixes::new())
                })
                .collect();
            actual.insert(parts.join(" v "));
        }
        current = gd.previous;
    }
    assert_eq!(actual, expected.iter().map(|s| s.to_string()).collect());
}
