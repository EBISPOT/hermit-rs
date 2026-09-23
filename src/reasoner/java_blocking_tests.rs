// Direct translation of the corrected Java BlockingValidatorTest
// (tests/java/corrected/); regenerate with port_blocking.py.
#![allow(non_snake_case, unused_variables)]
use super::java_tableau_tests::*;
use super::*;
use crate::model::*;
#[test]
fn testOneInvalidBlock() {
    if crate::java_test_support::isolated(
        concat!(module_path!(), "::testOneInvalidBlock").trim_start_matches("hermit_rs::"),
    ) {
        return;
    }
    let mut clauses = indexmap::IndexSet::new();
    clauses.insert(DLClause::create(
        vec![atom(predicate("ATLEAST2RA"), &["X"])],
        vec![atom(predicate("B"), &["X"])],
    ));
    clauses.insert(DLClause::create(
        vec![atom(predicate("ATLEAST2INVRB"), &["X"])],
        vec![atom(predicate("A"), &["X"])],
    ));
    clauses.insert(DLClause::create(
        vec![atom(predicate("ATLEAST1SA"), &["X"])],
        vec![atom(predicate("C"), &["X"])],
    ));
    clauses.insert(DLClause::create(
        vec![atom(predicate("ATLEAST2RA"), &["X"])],
        vec![atom(predicate("C"), &["X"])],
    ));
    clauses.insert(DLClause::create(
        vec![atom(predicate("ATLEAST1INVRE"), &["X"])],
        vec![atom(predicate("D"), &["X"])],
    ));
    clauses.insert(DLClause::create(
        vec![atom(predicate("B"), &["X"])],
        vec![atom(predicate("E"), &["X"])],
    ));
    clauses.insert(DLClause::create(
        vec![atom(predicate("D"), &["X"])],
        vec![
            atom(predicate("R"), &["Y", "X"]),
            atom(predicate("B"), &["Y"]),
        ],
    ));
    clauses.insert(DLClause::create(
        vec![atom(
            DLPredicate::AnnotatedEquality(AnnotatedEquality::create(
                1,
                Role::AtomicRole(AtomicRole::create("R")),
                LiteralConcept::AtomicConcept(AtomicConcept::create("D")),
            )),
            &["Y1", "Y2", "X"],
        )],
        vec![
            atom(predicate("C"), &["X"]),
            atom(predicate("R"), &["X", "Y1"]),
            atom(predicate("D"), &["Y1"]),
            atom(predicate("R"), &["X", "Y2"]),
            atom(predicate("D"), &["Y2"]),
        ],
    ));
    let dl = test_dl(clauses.into_iter().collect());
    let (mut t, _manager) = tableau(&dl, true);
    let emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let r = t.create_new_ni_node(&emptySet);
    let a = t.create_new_tree_node(&emptySet, r);
    let b = t.create_new_tree_node(&emptySet, r);
    let a1 = t.create_new_tree_node(&emptySet, a);
    let a2 = t.create_new_tree_node(&emptySet, a);
    let a11 = t.create_new_tree_node(&emptySet, a1);
    let a111 = t.create_new_tree_node(&emptySet, a11);
    let b1 = t.create_new_tree_node(&emptySet, b);
    let b2 = t.create_new_tree_node(&emptySet, b);
    let b3 = t.create_new_tree_node(&emptySet, b);
    let a12 = t.create_new_tree_node(&emptySet, a1);
    let a121 = t.create_new_tree_node(&emptySet, a12);
    add(&mut t, predicate("R"), &[a, a1], &emptySet, true);
    add(&mut t, predicate("R"), &[a, a2], &emptySet, true);
    add(&mut t, predicate("R"), &[a11, a1], &emptySet, true);
    add(&mut t, predicate("R"), &[a11, a111], &emptySet, true);
    add(&mut t, predicate("S"), &[b, b1], &emptySet, true);
    add(&mut t, predicate("R"), &[b, b2], &emptySet, true);
    add(&mut t, predicate("R"), &[b, b3], &emptySet, true);
    add(&mut t, predicate("R"), &[a12, a1], &emptySet, true);
    add(&mut t, predicate("R"), &[a12, a121], &emptySet, true);
    add(&mut t, predicate("B"), &[a], &emptySet, true);
    add(&mut t, predicate("ATLEAST2RA"), &[a], &emptySet, false);
    add(&mut t, predicate("C"), &[b], &emptySet, true);
    add(&mut t, predicate("ATLEAST1SA"), &[b], &emptySet, false);
    add(&mut t, predicate("ATLEAST2RA"), &[b], &emptySet, false);
    add(&mut t, predicate("A"), &[a1], &emptySet, true);
    add(&mut t, predicate("ATLEAST2INVRB"), &[a1], &emptySet, false);
    add(&mut t, predicate("D"), &[a1], &emptySet, false);
    add(&mut t, predicate("ATLEAST1INVRE"), &[a1], &emptySet, false);
    add(&mut t, predicate("A"), &[a2], &emptySet, true);
    add(&mut t, predicate("ATLEAST2INVRB"), &[a2], &emptySet, false);
    add(&mut t, predicate("D"), &[a2], &emptySet, false);
    add(&mut t, predicate("ATLEAST1INVRE"), &[a2], &emptySet, false);
    add(&mut t, predicate("B"), &[a11], &emptySet, true);
    add(&mut t, predicate("ATLEAST2RA"), &[a11], &emptySet, false);
    add(&mut t, predicate("A"), &[a111], &emptySet, true);
    add(
        &mut t,
        predicate("ATLEAST2INVRB"),
        &[a111],
        &emptySet,
        false,
    );
    add(&mut t, predicate("D"), &[a111], &emptySet, false);
    add(
        &mut t,
        predicate("ATLEAST1INVRE"),
        &[a111],
        &emptySet,
        false,
    );
    add(&mut t, predicate("A"), &[b1], &emptySet, true);
    add(&mut t, predicate("ATLEAST2INVRB"), &[b1], &emptySet, false);
    add(&mut t, predicate("A"), &[b2], &emptySet, true);
    add(&mut t, predicate("ATLEAST2INVRB"), &[b2], &emptySet, false);
    add(&mut t, predicate("A"), &[b3], &emptySet, true);
    add(&mut t, predicate("ATLEAST2INVRB"), &[b3], &emptySet, false);
    add(&mut t, predicate("E"), &[a12], &emptySet, true);
    add(&mut t, predicate("B"), &[a12], &emptySet, false);
    add(&mut t, predicate("ATLEAST2RA"), &[a12], &emptySet, false);
    add(&mut t, predicate("A"), &[a121], &emptySet, true);
    add(
        &mut t,
        predicate("ATLEAST2INVRB"),
        &[a121],
        &emptySet,
        false,
    );
    add(&mut t, predicate("D"), &[a121], &emptySet, false);
    add(
        &mut t,
        predicate("ATLEAST1INVRE"),
        &[a121],
        &emptySet,
        false,
    );
    assert!(!(t.contains_clash()));
    t.compute_blocking();
    assert!(t.nodes[a111].is_directly_blocked() && t.nodes[a111].get_blocker() == Some(a1));
    assert!(t.nodes[a2].is_directly_blocked() && t.nodes[a2].get_blocker() == Some(a1));
    assert!(t.nodes[b1].is_directly_blocked() && t.nodes[b1].get_blocker() == Some(a1));
    assert!(t.nodes[b2].is_directly_blocked() && t.nodes[b2].get_blocker() == Some(a1));
    assert!(t.nodes[b3].is_directly_blocked() && t.nodes[b3].get_blocker() == Some(a1));
    assert!(t.nodes[a121].is_directly_blocked() && t.nodes[a121].get_blocker() == Some(a1));
    assert!(!(t.nodes[a].is_blocked()));
    assert!(!(t.nodes[b].is_blocked()));
    assert!(!(t.nodes[a1].is_blocked()));
    assert!(!(t.nodes[a11].is_blocked()));
    assert!(!(t.nodes[a12].is_blocked()));
    let validator = crate::tableau::blocking_validator::BlockingValidator::new(dl.get_dl_clauses());
    assert!(validator.is_block_valid(&mut t, a2));
    assert!(validator.is_block_valid(&mut t, a111));
    assert!(validator.is_block_valid(&mut t, b1));
    assert!(validator.is_block_valid(&mut t, b2) != validator.is_block_valid(&mut t, b3));
    assert!(validator.is_block_valid(&mut t, a121));
}
#[test]
fn testInvalidBlockWithAnnotatedEqualities() {
    if crate::java_test_support::isolated(
        concat!(module_path!(), "::testInvalidBlockWithAnnotatedEqualities")
            .trim_start_matches("hermit_rs::"),
    ) {
        return;
    }
    let mut clauses = indexmap::IndexSet::new();
    clauses.insert(DLClause::create(
        vec![atom(predicate("ATLEAST1SB"), &["X"])],
        vec![atom(predicate("A"), &["X"])],
    ));
    clauses.insert(DLClause::create(
        vec![atom(predicate("ATLEAST1INVRB"), &["X"])],
        vec![atom(predicate("A"), &["X"])],
    ));
    clauses.insert(DLClause::create(
        vec![atom(predicate("ATLEAST1RC"), &["X"])],
        vec![
            atom(predicate("S"), &["Y", "X"]),
            atom(predicate("A"), &["Y"]),
        ],
    ));
    clauses.insert(DLClause::create(
        vec![atom(predicate("ATLEAST1TD"), &["X"])],
        vec![atom(predicate("B"), &["X"])],
    ));
    clauses.insert(DLClause::create(
        vec![atom(predicate("ATLEAST1INVRB"), &["X"])],
        vec![atom(predicate("E"), &["X"])],
    ));
    clauses.insert(DLClause::create(
        vec![atom(predicate("C"), &["X"])],
        vec![atom(predicate("E"), &["X"])],
    ));
    clauses.insert(DLClause::create(
        vec![atom(
            DLPredicate::AnnotatedEquality(AnnotatedEquality::create(
                1,
                Role::AtomicRole(AtomicRole::create("R")),
                LiteralConcept::AtomicConcept(AtomicConcept::create("C")),
            )),
            &["Y1", "Y2", "X"],
        )],
        vec![
            atom(predicate("B"), &["X"]),
            atom(predicate("R"), &["X", "Y1"]),
            atom(predicate("C"), &["Y1"]),
            atom(predicate("R"), &["X", "Y2"]),
            atom(predicate("C"), &["Y2"]),
        ],
    ));
    let dl = test_dl(clauses.into_iter().collect());
    let (mut t, _manager) = tableau(&dl, true);
    let emptySet = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let r = t.create_new_ni_node(&emptySet);
    let a = t.create_new_tree_node(&emptySet, r);
    let a1 = t.create_new_tree_node(&emptySet, a);
    let a2 = t.create_new_tree_node(&emptySet, a);
    let a11 = t.create_new_tree_node(&emptySet, a1);
    let a12 = t.create_new_tree_node(&emptySet, a1);
    add(&mut t, predicate("S"), &[a, a1], &emptySet, true);
    add(&mut t, predicate("R"), &[a2, a], &emptySet, true);
    add(&mut t, predicate("R"), &[a1, a11], &emptySet, true);
    add(&mut t, predicate("T"), &[a1, a12], &emptySet, true);
    add(&mut t, predicate("A"), &[a], &emptySet, true);
    add(&mut t, predicate("C"), &[a], &emptySet, false);
    add(&mut t, predicate("ATLEAST1SB"), &[a], &emptySet, false);
    add(&mut t, predicate("ATLEAST1INVRB"), &[a], &emptySet, false);
    add(&mut t, predicate("B"), &[a1], &emptySet, true);
    add(&mut t, predicate("ATLEAST1TD"), &[a1], &emptySet, false);
    add(&mut t, predicate("B"), &[a2], &emptySet, true);
    add(&mut t, predicate("ATLEAST1TD"), &[a2], &emptySet, false);
    add(&mut t, predicate("C"), &[a11], &emptySet, true);
    add(&mut t, predicate("D"), &[a12], &emptySet, true);
    assert!(!(t.contains_clash()));
    t.compute_blocking();
    assert!(t.nodes[a2].is_directly_blocked() && t.nodes[a2].get_blocker() == Some(a1));
    assert!(!(t.nodes[a].is_blocked()));
    assert!(!(t.nodes[a1].is_blocked()));
    assert!(!(t.nodes[a11].is_blocked()));
    assert!(!(t.nodes[a12].is_blocked()));
    let validator = crate::tableau::blocking_validator::BlockingValidator::new(dl.get_dl_clauses());
    assert!(!(validator.is_block_valid(&mut t, a2)));
}
