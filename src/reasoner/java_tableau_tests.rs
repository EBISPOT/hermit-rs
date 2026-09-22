//! Original Java tableau regression scenarios and shared port helpers.
#![allow(non_snake_case)]
use super::*;
use crate::model::*;
use crate::tableau::{dependency_set::DependencySet, View};
pub(super) fn predicate(name: &str) -> DLPredicate {
    if let Some(s) = name.strip_prefix("ATLEAST") {
        let n = s[..1].parse().unwrap();
        let s = &s[1..];
        let filler = AtomicConcept::create(&s[s.len() - 1..]);
        let role = &s[..s.len() - 1];
        let r = AtomicRole::create(role.strip_prefix("INV").unwrap_or(role));
        let role = if role.starts_with("INV") {
            Role::InverseRole(InverseRole::create(r))
        } else {
            Role::AtomicRole(r)
        };
        return DLPredicate::AtLeastConcept(AtLeastConcept::create(
            n,
            role,
            LiteralConcept::AtomicConcept(filler),
        ));
    }
    match name {
        "R" | "S" | "T" | "U" => DLPredicate::AtomicRole(AtomicRole::create(name)),
        _ => DLPredicate::AtomicConcept(AtomicConcept::create(name)),
    }
}
pub(super) fn atom(p: DLPredicate, names: &[&str]) -> Atom {
    Atom::create(
        p,
        names
            .iter()
            .map(|n| Term::Variable(Variable::create(*n)))
            .collect(),
    )
}
pub(super) fn test_dl(clauses: Vec<DLClause>) -> DLOntology {
    DLOntology::new(
        "opaque:test",
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
        true,
        false,
        false,
        false,
    )
}
pub(super) fn tableau(dl: &DLOntology, validated: bool) -> (Tableau, HyperresolutionManager) {
    use crate::configuration::*;
    let r = Reasoner::with_configuration(
        dl,
        Configuration {
            blocking_strategy_type: if validated {
                BlockingStrategyType::SimpleCore
            } else {
                BlockingStrategyType::Anywhere
            },
            direct_blocking_type: if validated {
                DirectBlockingType::Single
            } else {
                DirectBlockingType::PairWise
            },
            ..Default::default()
        },
    );
    let manager = r.new_manager();
    (r.build_test_tableau(&manager), manager)
}
pub(super) fn add(t: &mut Tableau, p: DLPredicate, n: &[NodeId], ds: &DependencySet, core: bool) {
    match p {
        DLPredicate::AtomicConcept(c) => {
            t.add_concept_assertion(Concept::AtomicConcept(c), n[0], ds, core);
        }
        DLPredicate::AtLeastConcept(c) => {
            t.add_concept_assertion(Concept::AtLeastConcept(c), n[0], ds, core);
        }
        DLPredicate::AtomicRole(r) => {
            t.add_role_assertion(Role::AtomicRole(r), n[0], n[1], ds, core);
        }
        _ => panic!("predicate"),
    }
}
fn role_pairs(
    t: &Tableau,
    p: DLPredicate,
    view: View,
) -> std::collections::BTreeSet<(NodeId, NodeId)> {
    let r = t.create_ternary_retrieval(
        [0, -1, -1],
        [Some(TableauObject::DLPredicate(p)), None, None],
        view,
    );
    r.tuple_indices
        .iter()
        .map(|i| {
            (
                t.ternary_extension_table
                    .get_tuple_object(*i, 1)
                    .as_node()
                    .unwrap(),
                t.ternary_extension_table
                    .get_tuple_object(*i, 2)
                    .as_node()
                    .unwrap(),
            )
        })
        .collect()
}
fn concept_nodes(t: &Tableau, c: Concept) -> std::collections::BTreeSet<NodeId> {
    let r = t.create_binary_retrieval(
        [0, -1],
        [Some(TableauObject::Concept(c)), None],
        View::Total,
    );
    r.tuple_indices
        .iter()
        .map(|i| {
            t.binary_extension_table
                .get_tuple_object(*i, 1)
                .as_node()
                .unwrap()
        })
        .collect()
}
fn label(t: &Tableau, n: NodeId, expected: &[Concept]) {
    let r = t.create_binary_retrieval([-1, 1], [None, Some(TableauObject::Node(n))], View::Total);
    let actual: std::collections::HashSet<_> = r
        .tuple_indices
        .iter()
        .filter_map(|i| {
            if let TableauObject::Concept(c) = t.binary_extension_table.get_tuple_object(*i, 0) {
                Some(*c)
            } else {
                None
            }
        })
        .collect();
    assert_eq!(actual, expected.iter().copied().collect());
}
#[test]
fn testEvaluator() {
    if crate::java_test_support::isolated("reasoner::java_tableau_tests::testEvaluator") {
        return;
    }
    let [R, S, T, U] = ["R", "S", "T", "U"].map(predicate);
    let dl = test_dl(vec![DLClause::create(
        vec![atom(U, &["Z", "W"])],
        vec![
            atom(R, &["X", "Y"]),
            atom(S, &["Y", "Z"]),
            atom(T, &["W", "W"]),
        ],
    )]);
    let (mut t, mut m) = tableau(&dl, false);
    let e = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let [a, b, c, d, f] = std::array::from_fn(|_| t.create_new_ni_node(&e));
    for (p, x, y) in [(R, a, b), (R, a, c), (S, b, d), (T, f, f), (T, c, d)] {
        add(&mut t, p, &[x, y], &e, false);
    }
    assert!(run_calculus(&mut t, &mut m).unwrap());
    assert_eq!(
        role_pairs(&t, U, View::ExtensionThis),
        [(d, f)].into_iter().collect()
    );
}
#[test]
fn testMergeAndBacktrack() {
    if crate::java_test_support::isolated("reasoner::java_tableau_tests::testMergeAndBacktrack") {
        return;
    }
    let [A, B, C, D] =
        ["A", "B", "C", "D"].map(|s| Concept::AtomicConcept(AtomicConcept::create(s)));
    let neg =
        Concept::AtomicNegationConcept(AtomicNegationConcept::create(AtomicConcept::create("A")));
    let R = predicate("R");
    let exists = AtLeastConcept::create(
        1,
        Role::AtomicRole(AtomicRole::create("R")),
        LiteralConcept::AtomicNegationConcept(AtomicNegationConcept::create(
            AtomicConcept::create("A"),
        )),
    );
    let dl = test_dl(vec![DLClause::create(
        vec![atom(DLPredicate::AtLeastConcept(exists), &["X"])],
        vec![atom(R, &["X", "Y"]), atom(predicate("A"), &["Y"])],
    )]);
    let (mut t, _) = tableau(&dl, false);
    let e = DependencySet::Permanent(t.dependency_set_factory.empty_set());
    let a = t.create_new_ni_node(&e);
    let b = t.create_new_ni_node(&e);
    let a1 = t.create_new_tree_node(&e, a);
    let a2 = t.create_new_tree_node(&e, a);
    let a11 = t.create_new_tree_node(&e, a1);
    let a12 = t.create_new_tree_node(&e, a1);
    for (x, y) in [(a, a1), (a, a2), (a1, a11), (a1, a12), (a1, b)] {
        add(&mut t, R, &[x, y], &e, false);
    }
    for (c, n) in [
        (A, a1),
        (Concept::AtLeastConcept(exists), a1),
        (neg, a2),
        (B, a2),
        (C, a2),
        (D, a2),
        (A, a11),
        (A, a12),
    ] {
        t.add_concept_assertion(c, n, &e, false);
    }
    t.push_dummy_dependency_branching_point();
    let bp = t.current_branching_point;
    t.merge_nodes(a1, a2, &e);
    assert!(t.contains_clash());
    label(&t, a2, &[A, B, C, D, neg, Concept::AtLeastConcept(exists)]);
    assert!(t.nodes[a1].is_merged());
    assert_eq!(t.get_canonical_node(a1), a2);
    assert!(!t.nodes[a11].is_active());
    assert!(!t.nodes[a12].is_active());
    assert_eq!(
        role_pairs(&t, R, View::Total),
        [(a, a2), (a2, b)].into_iter().collect()
    );
    assert_eq!(concept_nodes(&t, A), [a2].into_iter().collect());
    t.java_backtrack_to(bp);
    assert!(!t.contains_clash());
    label(&t, a2, &[B, C, D, neg]);
    assert!(!t.nodes[a1].is_merged());
    assert_eq!(t.get_canonical_node(a1), a1);
    assert!(t.nodes[a11].is_active());
    assert!(t.nodes[a12].is_active());
    assert_eq!(
        role_pairs(&t, R, View::Total),
        [(a, a1), (a1, a11), (a1, a12), (a1, b), (a, a2)]
            .into_iter()
            .collect()
    );
    assert_eq!(concept_nodes(&t, A), [a1, a11, a12].into_iter().collect());
    t.add_binary_from_predicate(DLPredicate::Inequality, a11, a12, &e, false);
    assert_eq!(
        role_pairs(&t, DLPredicate::Inequality, View::Total),
        [(a11, a12)].into_iter().collect()
    );
    t.merge_nodes(a11, a12, &e);
    assert!(t.contains_clash());
    t.java_backtrack_to(bp);
    assert!(!t.contains_clash());
    assert!(role_pairs(&t, DLPredicate::Inequality, View::Total).is_empty());
}
