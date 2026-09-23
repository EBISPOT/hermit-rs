//! Issues #18, #20, #22, #23, #24, #25 and #27: a property hierarchy holds every
//! subsumption the ontology entails. Under the OWL 2 Direct Semantics
//! `SubObjectPropertyOf(R S)` holds when every pair of `R` is a pair of `S` in
//! every model (Table 6), whatever forces it: a role chain, transitivity,
//! nominals, data values or a single-element domain. Reading role labels off one
//! model edge misses subsumptions forced only through the role automata or
//! through equalities. Following HermiT's `classifyObjectProperties` and
//! `classifyDataProperties`, each role `R` is reduced to a proxy concept `∃R.M`
//! for a fresh concept `M` with an instance, and each data property `P` to
//! `∃P.U` for a fresh unknown datatype `U`; `R ⊑ S` holds exactly when the
//! proxy of `R` is subsumed by the proxy of `S`.
//!
//! Each hierarchy is compared, pair by pair, with the separate entailment tests
//! (`isSubObjectPropertyExpressionOf` and `isSubDataPropertyOf`), which reduce a
//! single subsumption to the inconsistency of the ontology with a
//! counterexample pair.
use hermit_rs::{configuration::*, hierarchy::Hierarchy, reasoner, structural::A};
use horned_owl::{model::*, ontology::set::SetOntology};

type Ope = ObjectPropertyExpression<A>;

fn parse(axioms: &str) -> SetOntology<A> {
    let source = format!(
        r#"Prefix(:=<urn:issue22:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)
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
        _ => format!("urn:issue22:{name}"),
    }
}

fn op(name: &str) -> Ope {
    Ope::ObjectProperty(Build::new_arc().object_property(iri(name)))
}

fn inv(name: &str) -> Ope {
    Ope::InverseObjectProperty(Build::new_arc().object_property(iri(name)))
}

fn dp(name: &str) -> DataProperty<A> {
    Build::new_arc().data_property(match name {
        "top" => "http://www.w3.org/2002/07/owl#topDataProperty".into(),
        "bottom" => "http://www.w3.org/2002/07/owl#bottomDataProperty".into(),
        _ => format!("urn:issue22:{name}"),
    })
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

fn subsumed<E: Eq + std::hash::Hash + Clone>(h: &Hierarchy<E>, sub: &E, sup: &E) -> bool {
    h.equivalent_elements_of(sub).contains(sup) || h.super_elements(sub, false).contains(sup)
}

/// Whether two hierarchies over `elements` hold the same subsumptions.
fn assert_same_subsumptions<E>(a: &Hierarchy<E>, b: &Hierarchy<E>, elements: &[E])
where
    E: Eq + std::hash::Hash + Clone + std::fmt::Debug,
{
    for sub in elements {
        for sup in elements {
            assert_eq!(subsumed(a, sub, sup), subsumed(b, sub, sup), "{sub:?} ⊑ {sup:?}");
        }
    }
}

/// The object-property hierarchy of `o` under every configuration. The first is
/// checked pair by pair against the entailment test, the others against it.
fn object_hierarchies(o: &SetOntology<A>) -> Vec<Hierarchy<Ope>> {
    let hierarchies: Vec<Hierarchy<Ope>> = configurations()
        .iter()
        .map(|c| reasoner::classify_object_property_expressions_with_configuration(o, c).unwrap())
        .collect();
    let elements: Vec<Ope> = hierarchies[0].all_elements().cloned().collect();
    for sub in &elements {
        for sup in &elements {
            let entailed =
                reasoner::is_object_property_subsumed_by(o, sub.clone(), sup.clone()).unwrap();
            assert_eq!(subsumed(&hierarchies[0], sub, sup), entailed, "{sub:?} ⊑ {sup:?}");
        }
    }
    for h in &hierarchies[1..] {
        assert_same_subsumptions(&hierarchies[0], h, &elements);
    }
    hierarchies
}

/// The data-property hierarchy of `o` under every configuration. The first is
/// checked pair by pair against the entailment test, the others against it.
/// owl:topDataProperty may occur only as a superproperty (OWL 2 Structural
/// Specification §11.2), so it is compared as one only. In these ontologies no
/// data property holds every pair of an individual and a data value, so
/// owl:topDataProperty shares its node with none.
fn data_hierarchies(o: &SetOntology<A>) -> Vec<Hierarchy<DataProperty<A>>> {
    let hierarchies: Vec<Hierarchy<DataProperty<A>>> = configurations()
        .iter()
        .map(|c| reasoner::classify_data_properties_with_configuration(o, c).unwrap())
        .collect();
    let elements: Vec<DataProperty<A>> = hierarchies[0].all_elements().cloned().collect();
    for sub in elements.iter().filter(|p| **p != dp("top")) {
        for sup in &elements {
            let entailed = reasoner::is_sub_data_property_of(o, sub.clone(), sup.clone()).unwrap();
            assert_eq!(subsumed(&hierarchies[0], sub, sup), entailed, "{sub:?} ⊑ {sup:?}");
        }
    }
    for h in &hierarchies {
        assert_same_subsumptions(&hierarchies[0], h, &elements);
        assert_eq!(h.equivalent_elements_of(&dp("top")).len(), 1);
    }
    hierarchies
}

const CHAIN: &str = "SubClassOf(owl:Thing ObjectSomeValuesFrom(:r owl:Thing))
SubObjectPropertyOf(ObjectPropertyChain(:s1 :r ObjectInverseOf(:r)) :s2)";

#[test]
fn a_chain_back_to_the_start_subsumes_its_first_role() {
    // ReasonerTest.testRoleChains (#22): every element has an `r`-successor, so
    // every `s1` pair (x, y) extends to the chain x s1 y r z r⁻ y, whose ends are
    // an `s2` pair. So s1 ⊑ s2 (and s1⁻ ⊑ s2⁻), but not s2 ⊑ s1.
    for h in object_hierarchies(&parse(CHAIN)) {
        assert!(h.super_elements(&op("s1"), true).contains(&op("s2")));
        assert!(h.super_elements(&inv("s1"), true).contains(&inv("s2")));
        assert!(!subsumed(&h, &op("s2"), &op("s1")));
    }
    // Without the existential, an `s1` pair with no `r`-successor is no `s2` pair.
    let chain_only = CHAIN.lines().nth(1).unwrap();
    for h in object_hierarchies(&parse(chain_only)) {
        assert!(!subsumed(&h, &op("s1"), &op("s2")));
    }
}

#[test]
fn a_disjunction_does_not_hide_a_chain_subsumption() {
    // The same entailment in a non-Horn ontology, classified by the quasi-order
    // classifier with the inverse roles mirrored.
    let o = parse(&format!("{CHAIN}\nSubClassOf(owl:Thing ObjectUnionOf(:A :B))"));
    for h in object_hierarchies(&o) {
        assert!(h.super_elements(&op("s1"), true).contains(&op("s2")));
        assert!(h.super_elements(&inv("s1"), true).contains(&inv("s2")));
    }
}

const NOMINALS: &str = "ObjectPropertyAssertion(:r :a :b)
ObjectPropertyAssertion(:t :a :c)
ObjectPropertyAssertion(:t :c :b)
ObjectPropertyDomain(:r ObjectOneOf(:a))
ObjectPropertyRange(:r ObjectOneOf(:b))";

#[test]
fn nominals_and_transitivity_force_a_subsumption() {
    // ReasonerTest.testRoleSubsumption (#23): `r` holds only the pair (a, b),
    // and the transitive `t` holds (a, c) and (c, b), hence (a, b). So r ⊑ t,
    // while `t`'s pair (a, c) need not be an `r` pair.
    let o = parse(&format!("{NOMINALS}\nTransitiveObjectProperty(:t)"));
    for h in object_hierarchies(&o) {
        assert_eq!(h.super_elements(&op("r"), true), [op("t")].into_iter().collect());
        assert!(!subsumed(&h, &op("t"), &op("r")));
    }
    // Without transitivity, (a, b) need not be a `t` pair.
    for h in object_hierarchies(&parse(NOMINALS)) {
        assert!(!subsumed(&h, &op("r"), &op("t")));
    }
}

#[test]
fn chains_transitivity_and_symmetry_force_a_subsumption() {
    // ReasonerTest.testRoleSubsumptionWithChainsTransitiveSymmetric (#24): for an
    // `r` pair (x, y), x has an `s`-successor z, and y r⁻ x s z gives s(y, z). As
    // s ⊑ t, t(x, z) and t(y, z); `t` is symmetric and transitive, so t(x, y).
    // So r ⊑ t, and t ≡ t⁻.
    let o = parse(
        "SubClassOf(ObjectSomeValuesFrom(:r owl:Thing) ObjectSomeValuesFrom(:s owl:Thing))
SubObjectPropertyOf(:r :p)
SubObjectPropertyOf(:s :t)
SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:r) :s) :s)
SymmetricObjectProperty(:t)
TransitiveObjectProperty(:t)",
    );
    for h in object_hierarchies(&o) {
        let direct = h.super_elements(&op("r"), true);
        assert_eq!(direct, [op("p"), op("t"), inv("t")].into_iter().collect());
        assert!(!subsumed(&h, &op("r"), &op("s")));
    }
}

#[test]
fn a_role_holding_every_pair_is_the_universal_role() {
    // ReasonerTest.testTopOPEquivalence (#27): the domain is {a}, and a has an
    // `op`-successor, which is a. So `op` holds the only pair (a, a).
    let o = parse(
        "SubClassOf(owl:Thing ObjectOneOf(:a))
SubClassOf(ObjectOneOf(:a) ObjectSomeValuesFrom(:op owl:Thing))",
    );
    for h in object_hierarchies(&o) {
        let universal = [op("op"), op("top")].into_iter().collect();
        assert_eq!(h.equivalent_elements_of(&op("op")), universal);
    }
    // With two elements, each with an `op`-successor, `op` may still miss a pair.
    let o = parse(
        "SubClassOf(owl:Thing ObjectOneOf(:a :b))
SubClassOf(owl:Thing ObjectSomeValuesFrom(:op owl:Thing))",
    );
    for h in object_hierarchies(&o) {
        assert_eq!(h.equivalent_elements_of(&op("top")), [op("top")].into_iter().collect());
    }
}

#[test]
fn a_role_above_the_universal_role_is_the_universal_role() {
    // ReasonerTest.testHierarchyPrinting1 (#20): owl:topObjectProperty holds
    // every pair, so `op` above it does too, and so does its inverse, while
    // `qi` below `op`, and its inverse `q`, need not.
    let o = parse(
        "SubObjectPropertyOf(owl:topObjectProperty :op)
InverseObjectProperties(:q :qi)
SubObjectPropertyOf(:qi :op)",
    );
    for h in object_hierarchies(&o) {
        let universal: std::collections::HashSet<Ope> =
            [op("top"), op("op"), inv("op")].into_iter().collect();
        assert_eq!(h.equivalent_elements_of(&op("top")), universal);
        assert_eq!(h.equivalent_elements_of(&op("q")), [op("q"), inv("qi")].into_iter().collect());
        assert_eq!(h.super_elements(&op("q"), true), universal);
    }
}

const SINGLETON: &str = "SubClassOf(owl:Thing DataAllValuesFrom(:d1 DatatypeRestriction(xsd:int xsd:minInclusive \"1\"^^xsd:int xsd:maxInclusive \"1\"^^xsd:int)))
SubClassOf(owl:Thing DataSomeValuesFrom(:d1 xsd:int))
SubClassOf(owl:Thing DataSomeValuesFrom(:d2 DataOneOf(\"1\"^^xsd:int)))";

#[test]
fn a_shared_singleton_value_forces_a_data_subsumption() {
    // ReasonerTest.testDataPropertyEntailment (#18): every `d1` value is 1, and
    // every element has the `d2` value 1. So d1 ⊑ d2, but a `d2` value need not
    // be a `d1` value.
    for h in data_hierarchies(&parse(SINGLETON)) {
        assert_eq!(h.super_elements(&dp("d1"), true), [dp("d2")].into_iter().collect());
        assert!(!subsumed(&h, &dp("d2"), &dp("d1")));
    }
    // A `d1` value may be 2, which need not be a `d2` value.
    let wider = SINGLETON.replacen("xsd:maxInclusive \"1\"", "xsd:maxInclusive \"2\"", 1);
    for h in data_hierarchies(&parse(&wider)) {
        assert!(!subsumed(&h, &dp("d1"), &dp("d2")));
    }
}

#[test]
fn ranges_forced_to_one_value_make_data_properties_equivalent() {
    // ReasonerTest.testSemanticDataPropertyClassification (#25): the only value
    // of `r` and `s` is 0, and an element with a value of one has a value of the
    // other. So r ≡ s.
    let ranges = "DataPropertyRange(:r xsd:nonNegativeInteger)
DataPropertyRange(:s xsd:nonNegativeInteger)
EquivalentClasses(DataSomeValuesFrom(:r rdfs:Literal) DataSomeValuesFrom(:s rdfs:Literal))";
    let o = parse(&format!(
        "{ranges}
DataPropertyRange(:r xsd:nonPositiveInteger)
DataPropertyRange(:s xsd:nonPositiveInteger)"
    ));
    for h in data_hierarchies(&o) {
        assert_eq!(h.equivalent_elements_of(&dp("r")), [dp("r"), dp("s")].into_iter().collect());
    }
    // With the non-negative integers as range, the values may differ.
    for h in data_hierarchies(&parse(ranges)) {
        assert_eq!(h.equivalent_elements_of(&dp("r")), [dp("r")].into_iter().collect());
    }
}

#[test]
fn a_functional_value_shared_by_every_element_forces_a_data_subsumption() {
    // The only `p` value of every element is 5, and every element has the `q`
    // value 5. So p ⊑ q. The fresh `p` value of the proxy is merged with the
    // enumerated 5, which the unknown datatype does not exclude, so `p` is not
    // empty.
    let o = parse(
        "FunctionalDataProperty(:p)
SubClassOf(owl:Thing DataHasValue(:p \"5\"^^xsd:integer))
SubClassOf(owl:Thing DataHasValue(:q \"5\"^^xsd:integer))",
    );
    for h in data_hierarchies(&o) {
        assert_eq!(h.super_elements(&dp("p"), true), [dp("q")].into_iter().collect());
        assert!(!subsumed(&h, &dp("p"), &dp("bottom")));
        assert!(!subsumed(&h, &dp("q"), &dp("p")));
    }
}

#[test]
fn a_functional_value_asserted_for_the_only_element_is_not_excluded() {
    // The domain is {a}, whose only `p` value is the asserted 5, so the fresh
    // `p` value of the proxy is the constant 5, which the unknown datatype does
    // not exclude. `p` is not empty and is subsumed by `q`, which has that value.
    let o = parse(
        "SubClassOf(owl:Thing ObjectOneOf(:a))
FunctionalDataProperty(:p)
DataPropertyAssertion(:p :a \"5\"^^xsd:integer)
DataPropertyAssertion(:q :a \"5\"^^xsd:integer)",
    );
    for h in data_hierarchies(&o) {
        assert_eq!(h.super_elements(&dp("p"), true), [dp("q")].into_iter().collect());
        assert!(!subsumed(&h, &dp("p"), &dp("bottom")));
    }
}
