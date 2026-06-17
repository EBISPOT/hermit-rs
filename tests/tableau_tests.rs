// Tests for the dependency-set infrastructure.

use hermit_rs::tableau::{
    DependencySet, DependencySetFactory, DependencySetOps, UnionDependencySet,
};

#[test]
fn empty_set_semantics() {
    let factory = DependencySetFactory::new();
    let empty = factory.empty_set();
    assert!(empty.is_empty());
    assert_eq!(empty.get_maximum_branching_point(), -1);
    assert!(!empty.contains_branching_point(0));
}

#[test]
fn add_and_remove_branching_points_are_canonical() {
    let mut factory = DependencySetFactory::new();
    let empty = DependencySet::Permanent(factory.empty_set());

    let s1 = factory.add_branching_point(&empty, 3);
    let s2 = factory.add_branching_point(&DependencySet::Permanent(s1.clone()), 7);
    assert!(s2.contains_branching_point(3));
    assert!(s2.contains_branching_point(7));
    assert_eq!(s2.get_maximum_branching_point(), 7);
    assert!(!s2.is_empty());

    // Adding in the opposite order yields the canonical (identical) instance.
    let t1 = factory.add_branching_point(&empty, 7);
    let t2 = factory.add_branching_point(&DependencySet::Permanent(t1), 3);
    assert_eq!(s2, t2);
    assert!(s2.ptr_eq(&t2));

    // Removing a branching point.
    let s3 = factory.remove_branching_point(&DependencySet::Permanent(s2.clone()), 3);
    assert!(!s3.contains_branching_point(3));
    assert!(s3.contains_branching_point(7));
    // Adding an absent point is a no-op set-wise.
    let s4 = factory.add_branching_point(&DependencySet::Permanent(s2.clone()), 7);
    assert_eq!(s4, s2);
}

#[test]
fn union_flattening() {
    let mut factory = DependencySetFactory::new();
    let empty = DependencySet::Permanent(factory.empty_set());
    let a = factory.add_branching_point(&empty, 1);
    let b = factory.add_branching_point(&empty, 5);

    let mut union = UnionDependencySet::new(2);
    union.add_constituent(DependencySet::Permanent(a.clone()));
    union.add_constituent(DependencySet::Permanent(b.clone()));
    assert!(union.contains_branching_point(1));
    assert!(union.contains_branching_point(5));
    assert_eq!(union.get_maximum_branching_point(), 5);

    let permanent = factory.get_permanent(&DependencySet::Union(union));
    assert!(permanent.contains_branching_point(1));
    assert!(permanent.contains_branching_point(5));

    // unionWith of the two permanent sets gives the same canonical set.
    let combined = factory.union_with(
        &DependencySet::Permanent(a),
        &DependencySet::Permanent(b),
    );
    assert_eq!(permanent, combined);
}

#[test]
fn usage_counting_prunes_unused() {
    let mut factory = DependencySetFactory::new();
    let empty = DependencySet::Permanent(factory.empty_set());
    let s = factory.add_branching_point(&empty, 42);
    factory.add_usage(&s);
    factory.remove_unused_sets();
    // Still retrievable / canonical after pruning while in use.
    let s_again = factory.add_branching_point(&empty, 42);
    assert_eq!(s, s_again);
    factory.remove_usage(&s);
    factory.remove_unused_sets();
}

#[test]
fn node_type_properties() {
    use hermit_rs::tableau::NodeType;
    assert_eq!(NodeType::NamedNode.get_merge_precedence(), 0);
    assert_eq!(NodeType::NiNode.get_merge_precedence(), 1);
    assert_eq!(NodeType::TreeNode.get_merge_precedence(), 2);
    assert!(NodeType::TreeNode.is_ni_target());
    assert!(!NodeType::NamedNode.is_ni_target());
    assert!(NodeType::TreeNode.is_abstract());
    assert!(!NodeType::ConcreteNode.is_abstract());
}

#[test]
fn interrupt_flag_signals() {
    use hermit_rs::tableau::{InterruptError, InterruptFlag};
    let mut flag = InterruptFlag::new(0); // no timeout
    flag.start_task();
    assert!(flag.check_interrupt().is_ok());
    let handle = flag.interrupt_handle();
    handle.interrupt();
    assert_eq!(flag.check_interrupt(), Err(InterruptError::Interrupted));
    flag.end_task();
    assert!(flag.check_interrupt().is_ok());
}

#[test]
fn reasoning_task_description_message() {
    use hermit_rs::model::AtomicConcept;
    use hermit_rs::tableau::ReasoningTaskDescription;

    let a = AtomicConcept::create("http://www.w3.org/2002/07/owl#Thing");
    let task = ReasoningTaskDescription::is_concept_satisfiable(
        hermit_rs::model::DLPredicate::AtomicConcept(a),
    );
    assert!(!task.flip_satisfiability_result());
    assert_eq!(task.to_string(), "satisfiability of concept 'owl:Thing'");

    let consistency = ReasoningTaskDescription::is_abox_satisfiable();
    assert_eq!(consistency.to_string(), "ABox satisfiability");
}

#[test]
fn tuple_table_store_retrieve_and_equality() {
    use hermit_rs::tableau::TupleTable;
    let mut table: TupleTable<i32> = TupleTable::new(3);
    let i0 = table.add_tuple(&[1, 2, 3]);
    let i1 = table.add_tuple(&[4, 5, 6]);
    assert_eq!(i0, 0);
    assert_eq!(i1, 1);
    assert_eq!(table.get_first_free_tuple_index(), 2);
    assert_eq!(table.get_tuple_object(1, 0), Some(&4));
    assert_eq!(table.get_tuple_object(0, 2), Some(&3));
    assert_eq!(table.retrieve_tuple(0), vec![Some(1), Some(2), Some(3)]);

    assert!(table.tuple_equals(&[1, 2, 3], 0, 3));
    assert!(table.tuple_equals(&[1, 2, 9], 0, 2)); // only first two compared
    assert!(!table.tuple_equals(&[1, 9, 3], 0, 3));

    // Indexed projection: read positions [2,0] of the buffer.
    assert!(table.tuple_equals_indexed(&[2, 0, 1], &[2, 0], 0, 2));

    table.nullify_tuple(0);
    assert_eq!(table.get_tuple_object(0, 0), None);
    assert!(!table.tuple_equals(&[1, 2, 3], 0, 3));

    // Growth past a page boundary preserves indices.
    let mut big: TupleTable<i32> = TupleTable::new(1);
    for n in 0..1000 {
        assert_eq!(big.add_tuple(&[n]), n as usize);
    }
    assert_eq!(big.get_tuple_object(777, 0), Some(&777));

    table.truncate(0);
    assert_eq!(table.get_first_free_tuple_index(), 0);
}

#[test]
fn tuple_index_add_get_remove_and_retrieval() {
    use hermit_rs::tableau::{TupleIndex, TupleIndexRetrieval};

    // Index on columns [0, 1].
    let mut index: TupleIndex<i32> = TupleIndex::new(vec![0, 1]);
    assert_eq!(index.add_tuple(&[1, 2, 100], 10), 10);
    assert_eq!(index.add_tuple(&[1, 3, 101], 11), 11);
    assert_eq!(index.add_tuple(&[2, 4, 102], 12), 12);
    // Re-adding the same key returns the existing tuple index.
    assert_eq!(index.add_tuple(&[1, 2, 999], 99), 10);

    assert_eq!(index.get_tuple_index(&[1, 2, 0]), 10);
    assert_eq!(index.get_tuple_index(&[1, 3, 0]), 11);
    assert_eq!(index.get_tuple_index(&[9, 9, 0]), -1);

    // Retrieve all tuples whose column 0 == 1 (selection on the first column).
    // bindings buffer holds the value to match at position 0.
    let mut retrieval = TupleIndexRetrieval::new(&index, &[Some(1), None, None], vec![0]);
    retrieval.open();
    let mut found = Vec::new();
    while !retrieval.after_last() {
        found.push(retrieval.get_current_tuple_index());
        retrieval.next();
    }
    found.sort();
    assert_eq!(found, vec![10, 11]);

    // Remove a tuple and confirm it is gone.
    assert_eq!(index.remove_tuple(&[1, 2, 0]), 10);
    assert_eq!(index.get_tuple_index(&[1, 2, 0]), -1);
    assert_eq!(index.get_tuple_index(&[1, 3, 0]), 11);
}

#[test]
fn ground_disjunction_header_ordering() {
    use hermit_rs::model::{
        AtLeastConcept, AtomicConcept, DLPredicate, LiteralConcept, Role, AtomicRole,
    };
    use hermit_rs::tableau::GroundDisjunctionHeader;

    let a = DLPredicate::AtomicConcept(AtomicConcept::create("http://example.org/A"));
    let r = Role::AtomicRole(AtomicRole::create("http://example.org/r"));
    let b = AtomicConcept::create("http://example.org/B");
    let at_least_pos = DLPredicate::AtLeastConcept(AtLeastConcept::create(
        1,
        r.clone(),
        LiteralConcept::AtomicConcept(b.clone()),
    ));
    let neg = b.get_negation();
    let at_least_neg =
        DLPredicate::AtLeastConcept(AtLeastConcept::create(1, r, neg));

    // Order: atomic disjuncts, then at-least-negative, then at-least-positive.
    let header = GroundDisjunctionHeader::new(vec![
        at_least_pos.clone(),
        a.clone(),
        at_least_neg.clone(),
    ]);
    // Argument offsets: arity 1 each.
    assert_eq!(header.disjunct_start(0), 0);
    assert_eq!(header.disjunct_start(1), 1);
    assert_eq!(header.disjunct_start(2), 2);
    // Sorted order puts the atomic disjunct (index 1) first, then the
    // at-least-negative (index 2), then the at-least-positive (index 0).
    assert_eq!(header.get_sorted_disjunct_indexes(), vec![1, 2, 0]);
    assert!(header.is_equal(&[at_least_pos, a, at_least_neg]));
}

#[test]
fn tableau_node_arena_lifecycle() {
    use hermit_rs::tableau::{DependencySet, Tableau};

    let mut tableau = Tableau::new();
    let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());

    let root = tableau.create_new_named_node(&empty);
    let child = tableau.create_new_tree_node(&empty, root);
    let grandchild = tableau.create_new_tree_node(&empty, child);

    assert_eq!(tableau.get_number_of_nodes_in_tableau(), 3);
    assert!(tableau.node(root).is_root_node());
    assert_eq!(tableau.node(child).get_parent(), Some(root));
    assert_eq!(tableau.node(child).get_tree_depth(), 1);
    assert_eq!(tableau.node(grandchild).get_tree_depth(), 2);

    // Ancestor relation through the parent chain.
    assert!(tableau.is_ancestor_of(root, grandchild));
    assert!(!tableau.is_ancestor_of(grandchild, root));

    // Merge child into root: the canonical node of child becomes root.
    tableau.merge_node(child, root, &empty);
    assert!(tableau.node(child).is_merged());
    assert_eq!(tableau.get_canonical_node(child), root);
    assert_eq!(tableau.node(root).get_node_id(), 1);

    // The tableau node linked list is traversable.
    let first = tableau.get_first_tableau_node().unwrap();
    assert_eq!(first, root);
}

#[test]
fn extension_tables_store_and_retrieve_assertions() {
    use hermit_rs::model::{AtomicConcept, AtomicRole, Concept, Role};
    use hermit_rs::tableau::{DependencySet, Tableau, TableauObject, View};

    let mut tableau = Tableau::new();
    let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());

    let a = tableau.create_new_named_node(&empty);
    let b = tableau.create_new_named_node(&empty);

    let concept_c = Concept::AtomicConcept(AtomicConcept::create("http://example.org/C"));
    let role_r = Role::AtomicRole(AtomicRole::create("http://example.org/r"));

    // Add C(a) and r(a, b).
    assert!(tableau.add_concept_assertion(concept_c.clone(), a, &empty, true));
    // Adding the same assertion again returns false (already present).
    assert!(!tableau.add_concept_assertion(concept_c.clone(), a, &empty, true));
    assert!(tableau.add_role_assertion(role_r.clone(), a, b, &empty, true));

    // Containment.
    assert!(tableau.contains_concept_assertion(&concept_c, a));
    assert!(!tableau.contains_concept_assertion(&concept_c, b));
    assert!(tableau.contains_role_assertion(&role_r, a, b));
    assert!(!tableau.contains_role_assertion(&role_r, b, a));

    // owl:Thing is implicitly asserted on abstract nodes.
    let thing = Concept::AtomicConcept(AtomicConcept::create(
        "http://www.w3.org/2002/07/owl#Thing",
    ));
    assert!(tableau.contains_concept_assertion(&thing, a));

    // A retrieval over the binary table (unbound) finds the C(a) assertion.
    let retrieval = tableau.create_binary_retrieval(
        [-1, -1],
        [None, None],
        View::Total,
    );
    assert!(!retrieval.after_last());

    // The concept counter was incremented by post_add.
    assert_eq!(tableau.node(a).get_number_of_positive_atomic_concepts(), 1);

    // A bound retrieval: r(a, ?) finds exactly the r(a,b) tuple.
    let r_obj = TableauObject::DLPredicate(hermit_rs::model::DLPredicate::AtomicRole(
        AtomicRole::create("http://example.org/r"),
    ));
    let a_obj = TableauObject::Node(a);
    let retrieval = tableau.create_ternary_retrieval(
        [0, 1, -1],
        [Some(r_obj), Some(a_obj), None],
        View::Total,
    );
    let mut count = 0;
    let mut r = retrieval;
    while !r.after_last() {
        count += 1;
        r.next();
    }
    assert_eq!(count, 1);
}

#[test]
fn clash_detection_concept_and_negation() {
    use hermit_rs::model::{AtomicConcept, Concept, LiteralConcept};
    use hermit_rs::tableau::{DependencySet, Tableau};

    let mut tableau = Tableau::new();
    let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
    let node = tableau.create_new_named_node(&empty);

    let a = AtomicConcept::create("http://example.org/A");
    let pos = Concept::AtomicConcept(a.clone());
    let neg = match a.get_negation() {
        LiteralConcept::AtomicNegationConcept(n) => Concept::AtomicNegationConcept(n),
        _ => unreachable!(),
    };

    // Assert A(node); no clash yet.
    tableau.add_concept_assertion(pos.clone(), node, &empty, true);
    assert!(!tableau.contains_clash());
    // Assert ¬A(node); now A and ¬A clash.
    tableau.add_concept_assertion(neg, node, &empty, true);
    assert!(tableau.contains_clash());
}

#[test]
fn clash_detection_nothing() {
    use hermit_rs::model::{AtomicConcept, Concept};
    use hermit_rs::tableau::{DependencySet, Tableau};

    let mut tableau = Tableau::new();
    let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
    let node = tableau.create_new_named_node(&empty);

    let nothing = Concept::AtomicConcept(AtomicConcept::nothing().clone());
    tableau.add_concept_assertion(nothing, node, &empty, true);
    assert!(tableau.contains_clash());
}

#[test]
fn merging_copies_assertions_and_merges() {
    use hermit_rs::model::{AtomicConcept, AtomicRole, Concept, Role};
    use hermit_rs::tableau::{DependencySet, Tableau};

    let mut tableau = Tableau::new();
    let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
    let a = tableau.create_new_named_node(&empty);
    let b = tableau.create_new_named_node(&empty);
    let c = tableau.create_new_named_node(&empty);

    let concept_c = Concept::AtomicConcept(AtomicConcept::create("http://example.org/C"));
    let role_r = Role::AtomicRole(AtomicRole::create("http://example.org/r"));

    // C(a), r(a,c).
    tableau.add_concept_assertion(concept_c.clone(), a, &empty, true);
    tableau.add_role_assertion(role_r.clone(), a, c, &empty, true);

    // Merge a into b (or b into a depending on direction). After the merge, the
    // surviving node carries C and the r-edge.
    assert!(tableau.merge_nodes(a, b, &empty));

    // One of a/b is now merged; its canonical node carries the assertions.
    let survivor = tableau.get_canonical_node(a);
    assert!(survivor == a || survivor == b);
    assert!(tableau.contains_concept_assertion(&concept_c, survivor));
    assert!(tableau.contains_role_assertion(&role_r, survivor, c));

    // Merging identical / inactive nodes is a no-op.
    assert!(!tableau.merge_nodes(b, b, &empty));
}

#[test]
fn values_buffer_manager_layout() {
    use std::collections::HashMap;
    use hermit_rs::model::{Atom, AtomicConcept, AtomicRole, DLClause, DLPredicate, Term, Variable};
    use hermit_rs::tableau::hyperresolution::ValuesBufferManager;

    // Clause B(X) :- A(X), r(X, Y) -- body has 2 variables {X,Y} and 2 body
    // predicates {A, r}.
    let a = AtomicConcept::create("http://example.org/A");
    let b = AtomicConcept::create("http://example.org/B");
    let r = AtomicRole::create("http://example.org/r");
    let x = || Term::Variable(Variable::create("X"));
    let y = || Term::Variable(Variable::create("Y"));
    let clause = DLClause::create(
        vec![Atom::create(DLPredicate::AtomicConcept(b), vec![x()])],
        vec![
            Atom::create(DLPredicate::AtomicConcept(a), vec![x()]),
            Atom::create(DLPredicate::AtomicRole(r), vec![x(), y()]),
        ],
    );
    let manager = ValuesBufferManager::new(&[clause], &HashMap::new()).unwrap();
    assert_eq!(manager.max_number_of_variables, 2);
    assert_eq!(manager.body_dl_predicates_to_indexes.len(), 2);
    // Buffer length = 2 variables + 2 predicates + 0 nonvariable terms.
    assert_eq!(manager.values_buffer.borrow().len(), 4);
}

#[test]
fn ground_disjunction_header_manager_interns() {
    use hermit_rs::model::{AtomicConcept, DLPredicate};
    use hermit_rs::tableau::hyperresolution::GroundDisjunctionHeaderManager;

    let mut manager = GroundDisjunctionHeaderManager::new();
    let a = DLPredicate::AtomicConcept(AtomicConcept::create("http://example.org/A"));
    let b = DLPredicate::AtomicConcept(AtomicConcept::create("http://example.org/B"));
    let i1 = manager.get(vec![a.clone(), b.clone()]);
    let i2 = manager.get(vec![a.clone(), b.clone()]);
    let i3 = manager.get(vec![b, a]);
    assert_eq!(i1, i2);
    assert_ne!(i1, i3);
    assert_eq!(manager.len(), 2);
}

#[test]
fn dl_clause_evaluator_derives_fact() {
    // The keystone: evaluating the clause B(X) :- A(X) against A(node) must
    // derive B(node).
    use std::collections::HashMap;
    use hermit_rs::model::{Atom, AtomicConcept, Concept, DLClause, DLPredicate, Term, Variable};
    use hermit_rs::tableau::hyperresolution::ValuesBufferManager;
    use hermit_rs::tableau::{DLClauseEvaluator, DependencySet, Tableau, TableauObject};

    let mut tableau = Tableau::new();
    let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
    let node = tableau.create_new_named_node(&empty);

    let a = AtomicConcept::create("http://example.org/A");
    let b = AtomicConcept::create("http://example.org/B");

    // Assert A(node).
    tableau.add_concept_assertion(Concept::AtomicConcept(a.clone()), node, &empty, true);
    assert!(!tableau.contains_concept_assertion(&Concept::AtomicConcept(b.clone()), node));

    // Clause B(X) :- A(X).
    let x = || Term::Variable(Variable::create("X"));
    let clause = DLClause::create(
        vec![Atom::create(DLPredicate::AtomicConcept(b.clone()), vec![x()])],
        vec![Atom::create(DLPredicate::AtomicConcept(a.clone()), vec![x()])],
    );
    let vbm = ValuesBufferManager::new(std::slice::from_ref(&clause), &HashMap::new()).unwrap();
    let mut evaluator = DLClauseEvaluator::compile(
        &clause,
        std::slice::from_ref(&clause),
        &vbm,
        hermit_rs::tableau::dl_clause_evaluator::CoreVariablePolicy::AllTrue,
    );

    // The delta tuple is A(node).
    let empty_perm = tableau.dependency_set_factory().empty_set();
    evaluator.set_delta_row(
        vec![
            TableauObject::Concept(Concept::AtomicConcept(a)),
            TableauObject::Node(node),
        ],
        empty_perm,
        true,
    );
    evaluator.evaluate(&mut tableau);

    // B(node) is now derived.
    assert!(tableau.contains_concept_assertion(&Concept::AtomicConcept(b), node));
}

#[test]
fn saturation_decides_horn_consistency() {
    use hermit_rs::model::{Atom, AtomicConcept, Concept, DLClause, DLPredicate, Term, Variable};
    use hermit_rs::tableau::{DependencySet, HyperresolutionManager, Tableau};

    let a = AtomicConcept::create("http://example.org/A");
    let b = AtomicConcept::create("http://example.org/B");
    let x = || Term::Variable(Variable::create("X"));

    // B(X) :- A(X).
    let b_from_a = DLClause::create(
        vec![Atom::create(DLPredicate::AtomicConcept(b.clone()), vec![x()])],
        vec![Atom::create(DLPredicate::AtomicConcept(a.clone()), vec![x()])],
    );
    // :- A(X), B(X)   (A and B are disjoint).
    let a_b_disjoint = DLClause::create(
        vec![],
        vec![
            Atom::create(DLPredicate::AtomicConcept(a.clone()), vec![x()]),
            Atom::create(DLPredicate::AtomicConcept(b.clone()), vec![x()]),
        ],
    );

    // Consistent: A(a) with only B(X):-A(X) derives B(a), no clash.
    {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let node = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(Concept::AtomicConcept(a.clone()), node, &empty, true);
        let mut manager = HyperresolutionManager::new(&indexmap::IndexSet::from([b_from_a.clone()]));
        manager.saturate(&mut tableau);
        assert!(!tableau.contains_clash());
        assert!(tableau.contains_concept_assertion(&Concept::AtomicConcept(b.clone()), node));
    }

    // Inconsistent: A(a) with B(X):-A(X) AND disjoint(A,B) clashes.
    {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let node = tableau.create_new_named_node(&empty);
        tableau.add_concept_assertion(Concept::AtomicConcept(a.clone()), node, &empty, true);
        let mut manager =
            HyperresolutionManager::new(&indexmap::IndexSet::from([b_from_a, a_b_disjoint]));
        manager.saturate(&mut tableau);
        assert!(tableau.contains_clash());
    }
}
