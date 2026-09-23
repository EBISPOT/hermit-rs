//! Issue #26: `ObjectInverseOf(owl:topObjectProperty)` is owl:topObjectProperty
//! and `ObjectInverseOf(owl:bottomObjectProperty)` is owl:bottomObjectProperty.
//! Under the OWL 2 Direct Semantics the universal role holds every pair of
//! elements and the empty role none (§2.2), and `ObjectInverseOf` swaps the pairs
//! of its property (Table 1), so each of the two is its own inverse, as HermiT's
//! `AtomicRole.getInverse` has it. A query on either inverse therefore has the
//! answer of the same query on the property itself. The property hierarchy
//! looked the inverses up as fresh properties, between its top and bottom nodes,
//! so the sub-properties of `ObjectInverseOf(owl:bottomObjectProperty)` included
//! owl:bottomObjectProperty (`ReasonerTest.testSubProperties`, operation 13), and
//! the disjoint properties of that inverse were searched as for an ordinary role.
use hermit_rs::{configuration::*, hierarchy::Hierarchy, reasoner, structural::A};
use horned_owl::{model::*, ontology::set::SetOntology};
use std::collections::HashSet;

type Ope = ObjectPropertyExpression<A>;

fn parse(axioms: &str) -> SetOntology<A> {
    let source = format!(
        r#"Prefix(:=<urn:issue26:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(
{axioms}
)"#
    );
    horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
        .unwrap()
        .0
}

fn iri(name: &str) -> String {
    match name {
        "top" => "http://www.w3.org/2002/07/owl#topObjectProperty".into(),
        "bottom" => "http://www.w3.org/2002/07/owl#bottomObjectProperty".into(),
        _ => format!("urn:issue26:{name}"),
    }
}

fn op(name: &str) -> Ope {
    Ope::ObjectProperty(Build::new_arc().object_property(iri(name)))
}

fn inv(name: &str) -> Ope {
    Ope::InverseObjectProperty(Build::new_arc().object_property(iri(name)))
}

fn set(properties: &[Ope]) -> HashSet<Ope> {
    properties.iter().cloned().collect()
}

/// The configurations of the Java suites (the defaults, core blocking and
/// individual reuse), and the quasi-order classifier on Horn ontologies too.
fn configurations() -> Vec<Configuration> {
    vec![
        Configuration::default(),
        Configuration {
            blocking_strategy_type: BlockingStrategyType::SimpleCore,
            direct_blocking_type: DirectBlockingType::Single,
            blocking_signature_cache_type: BlockingSignatureCacheType::NotCached,
            ..Configuration::default()
        },
        Configuration {
            existential_strategy_type: ExistentialStrategyType::IndividualReuse,
            ..Configuration::default()
        },
        Configuration { force_quasi_order_classification: true, ..Configuration::default() },
    ]
}

/// Whether the hierarchy places `sub` at or below `sup`. The nodes list the
/// built-in properties, not their inverses, so this compares nodes.
fn subsumed(h: &Hierarchy<Ope>, sub: &Ope, sup: &Ope) -> bool {
    let node = |p: &Ope| h.node_for_element(p).expect("an element of the hierarchy");
    h.ancestor_nodes(node(sub)).contains(&node(sup))
}

/// The ontology of `ReasonerTest.testSubProperties`.
const SUB_PROPERTIES: &str = "SubObjectPropertyOf(:r1 ObjectInverseOf(:s1))
SubObjectPropertyOf(:r1 ObjectInverseOf(:s3))
SubObjectPropertyOf(:r2 ObjectInverseOf(:s2))
SubObjectPropertyOf(:r3 ObjectInverseOf(:s2))
SubObjectPropertyOf(:r3 ObjectInverseOf(:s4))
SubObjectPropertyOf(ObjectInverseOf(:s1) :t1)
SubObjectPropertyOf(ObjectInverseOf(:s2) :t1)
SubObjectPropertyOf(ObjectInverseOf(:s3) :t2)
SubObjectPropertyOf(ObjectInverseOf(:s4) :t2)
SubObjectPropertyOf(:t1 ObjectInverseOf(:u))
SubObjectPropertyOf(:t2 ObjectInverseOf(:u))";

/// Each declares `:r`, `:s`, `:u` and `:e` and asserts one `:r` pair.
const ONTOLOGIES: [&str; 4] = [
    // Neither built-in property occurs, so neither is axiomatized.
    "SubObjectPropertyOf(:r ObjectInverseOf(:s))",
    // `:u` holds every pair.
    "SubObjectPropertyOf(:r ObjectInverseOf(:s)) SubObjectPropertyOf(owl:topObjectProperty :u)",
    // `:e` holds no pair.
    "SubObjectPropertyOf(:r ObjectInverseOf(:s)) SubObjectPropertyOf(:e owl:bottomObjectProperty)",
    // The same two, through the inverses.
    "SubObjectPropertyOf(:r ObjectInverseOf(:s))
     SubObjectPropertyOf(ObjectInverseOf(owl:topObjectProperty) :u)
     SubObjectPropertyOf(:e ObjectInverseOf(owl:bottomObjectProperty))",
];

fn ontology(axioms: &str) -> SetOntology<A> {
    parse(&format!(
        "Declaration(ObjectProperty(:u)) Declaration(ObjectProperty(:e))
         ObjectPropertyAssertion(:r :a :b) {axioms}"
    ))
}

#[test]
fn the_hierarchy_finds_the_built_in_properties_for_their_inverses() {
    let o = parse(SUB_PROPERTIES);
    for c in configurations() {
        let h = reasoner::classify_object_property_expressions_with_configuration(&o, &c).unwrap();
        for name in ["top", "bottom"] {
            let (property, inverse) = (op(name), inv(name));
            assert_eq!(h.node_for_element(&inverse), h.node_for_element(&property));
            assert_eq!(h.equivalent_elements_of(&inverse), h.equivalent_elements_of(&property));
            for direct in [true, false] {
                assert_eq!(h.sub_elements(&inverse, direct), h.sub_elements(&property, direct));
                assert_eq!(h.super_elements(&inverse, direct), h.super_elements(&property, direct));
            }
            // No node lists the inverse: it is the property, not another element.
            assert!(h.all_elements().all(|e| *e != inverse));
        }
        // Operations 13, 24, 37 and 48 of testSubProperties.
        assert_eq!(h.sub_elements(&inv("bottom"), true), set(&[]));
        assert_eq!(h.sub_elements(&inv("top"), true), set(&[op("u"), inv("u")]));
        let minimal = [op("r1"), op("r2"), op("r3"), inv("r1"), inv("r2"), inv("r3")];
        assert_eq!(h.super_elements(&inv("bottom"), true), set(&minimal));
        assert_eq!(h.super_elements(&inv("top"), true), set(&[]));
        // getInverseObjectProperties of each built-in property is its own node.
        assert_eq!(h.equivalent_elements_of(&inv("top")), set(&[op("top")]));
        assert_eq!(h.equivalent_elements_of(&inv("bottom")), set(&[op("bottom")]));
    }
}

#[test]
fn the_hierarchy_of_the_inverses_agrees_with_the_subsumption_test() {
    // isSubObjectPropertyExpressionOf reduces each subsumption to the
    // inconsistency of the ontology with a counterexample pair, independently of
    // the hierarchy.
    let o = parse(SUB_PROPERTIES);
    let h = reasoner::classify_object_property_expressions(&o).unwrap();
    let mut properties: Vec<Ope> = h.all_elements().cloned().collect();
    properties.extend([inv("top"), inv("bottom")]);
    for sub in &properties {
        for sup in [inv("top"), inv("bottom")] {
            for (sub, sup) in [(sub.clone(), sup.clone()), (sup, sub.clone())] {
                let entailed =
                    reasoner::is_object_property_subsumed_by(&o, sub.clone(), sup.clone()).unwrap();
                assert_eq!(subsumed(&h, &sub, &sup), entailed, "{sub:?} ⊑ {sup:?}");
            }
        }
    }
}

#[test]
fn axioms_on_the_inverses_have_the_built_in_meaning() {
    // `ObjectInverseOf(owl:topObjectProperty) ⊑ :u` makes `:u` hold every pair,
    // and `:e ⊑ ObjectInverseOf(owl:bottomObjectProperty)` makes `:e` hold none.
    let o = ontology(ONTOLOGIES[3]);
    for c in configurations() {
        let h = reasoner::classify_object_property_expressions_with_configuration(&o, &c).unwrap();
        let universal = set(&[op("top"), op("u"), inv("u")]);
        let empty = set(&[op("bottom"), op("e"), inv("e")]);
        assert_eq!(h.equivalent_elements_of(&op("top")), universal);
        assert_eq!(h.equivalent_elements_of(&inv("top")), universal);
        assert_eq!(h.equivalent_elements_of(&op("bottom")), empty);
        assert_eq!(h.equivalent_elements_of(&inv("bottom")), empty);
    }
}

/// Asserts that `query` answers alike for the built-in property and its inverse.
/// Errors compare equal whatever their message, which names the expression.
fn same<T: PartialEq + std::fmt::Debug>(
    query: &str,
    property: &Ope,
    inverse: &Ope,
    answer: impl Fn(&Ope) -> Result<T, String>,
) {
    let answer = |p: &Ope| answer(p).map_err(|_| ());
    assert_eq!(answer(inverse), answer(property), "{query} of {inverse:?}");
}

#[test]
fn every_property_query_answers_for_the_inverse_as_for_the_property() {
    let (a, b) =
        (Build::new_arc().named_individual(iri("a")), Build::new_arc().named_individual(iri("b")));
    let others =
        [op("top"), inv("top"), op("bottom"), inv("bottom"), op("r"), inv("r"), op("u"), op("e")];
    for axioms in ONTOLOGIES {
        let o = ontology(axioms);
        for name in ["top", "bottom"] {
            let (p, i) = (&op(name), &inv(name));
            for direct in [true, false] {
                same("sub-properties", p, i, |x| {
                    reasoner::get_sub_object_properties(&o, x, direct)
                });
                same("super-properties", p, i, |x| {
                    reasoner::get_super_object_properties(&o, x, direct)
                });
                same("domains", p, i, |x| reasoner::get_object_property_domains(&o, x, direct));
                same("ranges", p, i, |x| reasoner::get_object_property_ranges(&o, x, direct));
            }
            same("equivalents", p, i, |x| reasoner::get_equivalent_object_properties(&o, x));
            same("inverses", p, i, |x| reasoner::get_inverse_object_properties(&o, x));
            same("node", p, i, |x| reasoner::equivalent_object_property_node(&o, x.clone()));
            same("disjoints", p, i, |x| reasoner::get_disjoint_object_properties(&o, x));
            for q in &others {
                same("sub-property", p, i, |x| {
                    reasoner::is_object_property_subsumed_by(&o, x.clone(), q.clone())
                });
                same("super-property", p, i, |x| {
                    reasoner::is_object_property_subsumed_by(&o, q.clone(), x.clone())
                });
                same("chain", p, i, |x| {
                    reasoner::is_object_property_chain_subsumed_by(
                        &o,
                        &[x.clone(), q.clone()],
                        op("u"),
                    )
                });
                same("chain super-property", p, i, |x| {
                    reasoner::is_object_property_chain_subsumed_by(
                        &o,
                        &[q.clone(), q.clone()],
                        x.clone(),
                    )
                });
                same("equivalence", p, i, |x| {
                    let axiom = EquivalentObjectProperties(vec![x.clone(), q.clone()]);
                    reasoner::is_entailed(&o, &Component::EquivalentObjectProperties(axiom))
                });
                same("disjointness", p, i, |x| {
                    let axiom = DisjointObjectProperties(vec![x.clone(), q.clone()]);
                    reasoner::is_entailed(&o, &Component::DisjointObjectProperties(axiom))
                });
                same("inverse", p, i, |x| {
                    let axiom = InverseObjectProperties(x.clone(), q.clone());
                    reasoner::is_entailed(&o, &Component::InverseObjectProperties(axiom))
                });
            }
            same("symmetric", p, i, |x| reasoner::is_symmetric(&o, x.clone()));
            same("functional", p, i, |x| reasoner::is_functional(&o, x.clone()));
            same("inverse-functional", p, i, |x| reasoner::is_inverse_functional(&o, x.clone()));
            same("irreflexive", p, i, |x| reasoner::is_irreflexive(&o, x.clone()));
            same("asymmetric", p, i, |x| reasoner::is_asymmetric(&o, x.clone()));
            same("reflexive", p, i, |x| reasoner::is_reflexive(&o, x.clone()));
            same("transitive", p, i, |x| reasoner::is_transitive(&o, x.clone()));
            same("instances", p, i, |x| reasoner::object_property_instances(&o, x.clone()));
            same("incremental instances", p, i, |x| {
                reasoner::IncrementalReasoner::new(o.clone()).object_property_instances(x.clone())
            });
            for (s, t) in [(&a, &b), (&b, &a), (&a, &a)] {
                same("values", p, i, |x| reasoner::get_object_property_values(&o, s, x.clone()));
                same("relationship", p, i, |x| {
                    reasoner::has_object_property_relationship(&o, s, x.clone(), t)
                });
            }
        }
    }
}

#[test]
fn the_inverse_of_bottom_is_disjoint_from_every_property() {
    // Deliberate deviation from Java. getDisjointObjectProperties tests
    // isOWLBottomObjectProperty(), which does not unwrap
    // ObjectInverseOf(owl:bottomObjectProperty), and so searches the hierarchy
    // below owl:topObjectProperty with the atom bottom(a, b), which clashes only
    // if the ontology mentions owl:bottomObjectProperty: Java answers the bottom
    // node alone for the first ontology, and every node but the top node for the
    // second. The empty role is disjoint from every role, the universal one
    // included (Table 6).
    for axioms in [ONTOLOGIES[0], ONTOLOGIES[2]] {
        let o = ontology(axioms);
        let every: HashSet<Ope> = reasoner::classify_object_property_expressions(&o)
            .unwrap()
            .all_elements()
            .cloned()
            .collect();
        let disjoint = reasoner::get_disjoint_object_properties(&o, &inv("bottom")).unwrap();
        assert!(disjoint.contains(&op("top")) && disjoint.contains(&op("r")), "{disjoint:?}");
        assert_eq!(disjoint, every);
    }
}
