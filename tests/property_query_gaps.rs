//! Two property-query gaps without an issue.
//!
//! The empty role is disjoint from every role, the universal one included
//! (OWL 2 Direct Semantics, Table 6: `DisjointObjectProperties` holds when no
//! pair is in the extensions of two of the properties, and
//! owl:bottomObjectProperty has none). The entailment test asserted a role atom
//! of owl:bottomObjectProperty on the ontology's tableau, where the property is
//! axiomatized only when the ontology mentions it, so
//! `DisjointObjectProperties(owl:bottomObjectProperty :r)` was not entailed for
//! an ontology that does not mention it, as in Java. The same holds for
//! owl:bottomDataProperty, and for a property that is empty in every model, which
//! the disjoint-property getters did not report disjoint from the top property.
//! `DisjointDataProperties` entailment threw on every axiom: its reduction put
//! owl:topDataProperty in `≤1`, which normalization rejects, as Java's does.
//!
//! `FunctionalObjectProperty(R)` is entailed iff `⊤ ⊑ ≤1 R.⊤`, which is well
//! defined for every role, but the test built `≤1 R.⊤` and so rejected a
//! non-simple `R` (a transitive or chain-defined property, or
//! owl:topObjectProperty). Only the ontology's own axioms are restricted to
//! simple roles.
use hermit_rs::{reasoner, structural::A};
use horned_owl::{model::*, ontology::set::SetOntology};

type Ope = ObjectPropertyExpression<A>;

fn parse(axioms: &str) -> SetOntology<A> {
    let source = format!(
        r#"Prefix(:=<urn:gaps:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
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
        "top" | "bottom" => format!("http://www.w3.org/2002/07/owl#{name}ObjectProperty"),
        "dtop" => "http://www.w3.org/2002/07/owl#topDataProperty".into(),
        "dbottom" => "http://www.w3.org/2002/07/owl#bottomDataProperty".into(),
        _ => format!("urn:gaps:{name}"),
    }
}

fn op(name: &str) -> Ope {
    Ope::ObjectProperty(Build::new_arc().object_property(iri(name)))
}

fn inv(name: &str) -> Ope {
    Ope::InverseObjectProperty(Build::new_arc().object_property(iri(name)))
}

fn dp(name: &str) -> DataProperty<A> {
    Build::new_arc().data_property(iri(name))
}

fn disjoint(o: &SetOntology<A>, properties: &[Ope]) -> bool {
    let axiom = DisjointObjectProperties(properties.to_vec());
    reasoner::is_entailed(o, &Component::DisjointObjectProperties(axiom)).unwrap()
}

fn disjoint_data(o: &SetOntology<A>, properties: &[DataProperty<A>]) -> bool {
    let axiom = DisjointDataProperties(properties.to_vec());
    reasoner::is_entailed(o, &Component::DisjointDataProperties(axiom)).unwrap()
}

fn functional(o: &SetOntology<A>, p: Ope) -> bool {
    let entailed = reasoner::is_entailed(
        o,
        &Component::FunctionalObjectProperty(FunctionalObjectProperty(p.clone())),
    )
    .unwrap();
    assert_eq!(reasoner::is_functional(o, p).unwrap(), entailed);
    entailed
}

fn inverse_functional(o: &SetOntology<A>, p: Ope) -> bool {
    let entailed = reasoner::is_entailed(
        o,
        &Component::InverseFunctionalObjectProperty(InverseFunctionalObjectProperty(p.clone())),
    )
    .unwrap();
    assert_eq!(reasoner::is_inverse_functional(o, p.clone()).unwrap(), entailed);
    // R is inverse-functional iff Inv(R) is functional.
    assert_eq!(functional(o, match p {
        Ope::ObjectProperty(q) => Ope::InverseObjectProperty(q),
        Ope::InverseObjectProperty(q) => Ope::ObjectProperty(q),
    }), entailed);
    entailed
}

fn functional_data(o: &SetOntology<A>, p: DataProperty<A>) -> bool {
    let axiom = FunctionalDataProperty(p);
    reasoner::is_entailed(o, &Component::FunctionalDataProperty(axiom)).unwrap()
}

#[test]
fn the_empty_roles_are_disjoint_from_every_role_when_unmentioned() {
    let o = parse("Declaration(ObjectProperty(:r)) Declaration(DataProperty(:d))");
    assert!(disjoint(&o, &[op("bottom"), op("r")]));
    assert!(disjoint(&o, &[op("r"), inv("bottom")]));
    assert!(disjoint(&o, &[op("bottom"), op("top")]));
    assert!(disjoint(&o, &[op("bottom"), op("bottom")]));
    assert!(!disjoint(&o, &[op("r"), op("top")]));
    assert!(!disjoint(&o, &[op("bottom"), op("r"), op("top")]));
    assert!(disjoint_data(&o, &[dp("dbottom"), dp("d")]));
    assert!(disjoint_data(&o, &[dp("d"), dp("dbottom")]));
    assert!(disjoint_data(&o, &[dp("dbottom"), dp("dtop")]));
    assert!(!disjoint_data(&o, &[dp("d"), dp("dtop")]));
    assert!(!disjoint_data(&o, &[dp("d"), dp("e")]));
    assert!(!disjoint_data(&o, &[dp("dtop"), dp("dtop")]));
}

#[test]
fn data_property_disjointness_is_answered() {
    let o = parse(
        "DisjointDataProperties(:d :e)
         DataPropertyRange(:i xsd:integer) DataPropertyRange(:s xsd:string)
         DataPropertyDomain(:n owl:Nothing)",
    );
    assert!(disjoint_data(&o, &[dp("d"), dp("e")]));
    assert!(disjoint_data(&o, &[dp("i"), dp("s")]));
    assert!(disjoint_data(&o, &[dp("n"), dp("dtop")]));
    assert!(!disjoint_data(&o, &[dp("d"), dp("i")]));
    assert!(!disjoint_data(&o, &[dp("d"), dp("e"), dp("i")]));
    // Without any data property in the ontology.
    let o = parse("Declaration(ObjectProperty(:r))");
    assert!(disjoint_data(&o, &[dp("d"), dp("dbottom")]));
    assert!(!disjoint_data(&o, &[dp("d"), dp("e")]));
    let disjoints = reasoner::get_disjoint_data_properties(&o, &dp("d")).unwrap();
    assert!(disjoints.contains(&dp("dbottom")), "{disjoints:?}");
}

#[test]
fn an_empty_role_is_disjoint_from_the_top_role() {
    let o = parse(
        "Declaration(ObjectProperty(:r)) ObjectPropertyDomain(:z owl:Nothing)
         Declaration(DataProperty(:d)) DataPropertyDomain(:dz owl:Nothing)",
    );
    assert!(disjoint(&o, &[op("z"), op("top")]));
    assert!(disjoint_data(&o, &[dp("dz"), dp("dtop")]));
    let disjoints = reasoner::get_disjoint_object_properties(&o, &op("z")).unwrap();
    for p in [op("top"), op("r"), op("z"), op("bottom")] {
        assert!(disjoints.contains(&p), "{p:?} in {disjoints:?}");
    }
    let disjoints = reasoner::get_disjoint_data_properties(&o, &dp("dz")).unwrap();
    for p in [dp("dtop"), dp("d"), dp("dz"), dp("dbottom")] {
        assert!(disjoints.contains(&p), "{p:?} in {disjoints:?}");
    }
    // A satisfiable property is not disjoint from the top property.
    let disjoints = reasoner::get_disjoint_object_properties(&o, &op("r")).unwrap();
    assert!(!disjoints.contains(&op("top")) && disjoints.contains(&op("z")), "{disjoints:?}");
}

#[test]
fn functionality_of_non_simple_roles_is_answered() {
    // Nothing bounds the successors: a transitive, a chain-defined and the
    // universal role are not functional in either direction.
    let o = parse(
        "TransitiveObjectProperty(:t)
         SubObjectPropertyOf(ObjectPropertyChain(:r :r) :c)",
    );
    for p in [op("t"), inv("t"), op("c"), inv("c"), op("top"), inv("top")] {
        assert!(!functional(&o, p.clone()), "{p:?}");
        assert!(!inverse_functional(&o, p.clone()), "{p:?}");
    }
    // The empty role is functional both ways.
    for p in [op("bottom"), inv("bottom")] {
        assert!(functional(&o, p.clone()) && inverse_functional(&o, p.clone()), "{p:?}");
    }

    // Every successor of t is :o, and every predecessor of c is :o: t is
    // functional and c inverse-functional, but not the other way round.
    let o = parse(
        "TransitiveObjectProperty(:t) ObjectPropertyRange(:t ObjectOneOf(:o))
         SubObjectPropertyOf(ObjectPropertyChain(:r :r) :c)
         ObjectPropertyDomain(:c ObjectOneOf(:o))",
    );
    assert!(functional(&o, op("t")));
    assert!(!functional(&o, inv("t")));
    assert!(inverse_functional(&o, inv("t")));
    assert!(!inverse_functional(&o, op("t")));
    assert!(inverse_functional(&o, op("c")));
    assert!(functional(&o, inv("c")));
    assert!(!functional(&o, op("c")));
    assert!(!functional(&o, op("top")));

    // With a one-element domain every role, the universal one included, is
    // functional; a data property still has infinitely many values.
    let o = parse("SubClassOf(owl:Thing ObjectOneOf(:o)) TransitiveObjectProperty(:t)");
    for p in [op("top"), inv("top"), op("t"), inv("t"), op("r")] {
        assert!(functional(&o, p.clone()) && inverse_functional(&o, p.clone()), "{p:?}");
    }
    assert!(!functional_data(&o, dp("dtop")));
    assert!(!functional_data(&o, dp("d")));
}

#[test]
fn functionality_of_simple_roles_is_unchanged() {
    let o = parse(
        "FunctionalObjectProperty(:f) InverseFunctionalObjectProperty(:g)
         SubObjectPropertyOf(:h :f) FunctionalDataProperty(:fd)",
    );
    assert!(functional(&o, op("f")) && !inverse_functional(&o, op("f")));
    assert!(functional(&o, op("h")));
    assert!(inverse_functional(&o, op("g")) && !functional(&o, op("g")));
    assert!(!functional(&o, op("r")));
    assert!(functional_data(&o, dp("fd")));
    assert!(!functional_data(&o, dp("d")));
    assert!(!functional_data(&o, dp("dtop")));
    assert!(functional_data(&o, dp("dbottom")));
}
