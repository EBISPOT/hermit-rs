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
