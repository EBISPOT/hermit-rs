//! `SubObjectPropertyOf(R ObjectInverseOf(S))` with a transitive `S` must not
//! give `R` the language of `Inv(S)`.
//!
//! `R ⊑ Inv(S)` only makes `Inv(S)`, and therefore `S` through the mirror, grow:
//! every `R`-chain is an `Inv(S)`-chain by transitivity. It says nothing about
//! `Inv(S) ⊑ R`. Java HermiT's `buildInversePropertiesMap` records the inclusion
//! as if `R` and `S` were declared inverses, so `∀R.C` also propagated along
//! `Inv(S)`: an unsound subsumption, an unsound property subsumption and an
//! unsound property hierarchy. hermit-rs deliberately does not reproduce that.

use hermit_rs::reasoner::{
    classify_object_property_expressions, is_concept_satisfiable, is_object_property_subsumed_by,
    is_subsumed_by,
};
use horned_owl::model::{Build, ClassExpression as CE, ObjectPropertyExpression as OPE};
use horned_owl::ontology::set::SetOntology;

type Onto = SetOntology<hermit_rs::structural::A>;

fn parse(text: &str) -> Onto {
    let (onto, _): (
        horned_owl::ontology::component_mapped::ComponentMappedOntology<
            hermit_rs::structural::A,
            horned_owl::model::AnnotatedComponent<hermit_rs::structural::A>,
        >,
        _,
    ) = horned_owl::io::ofn::reader::read(
        &mut std::io::Cursor::new(text),
        horned_owl::io::ParserConfiguration::new(Build::new_arc()),
    )
    .expect("parse");
    onto.into()
}

fn ontology(extra: &str) -> Onto {
    parse(&format!(
        "Prefix(:=<http://example.org/>)\n\
         Ontology(<http://example.org/inverse-transitive>\n\
         Declaration(ObjectProperty(:R)) Declaration(ObjectProperty(:S))\n\
         Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
         Declaration(Class(:D))\n\
         TransitiveObjectProperty(:S)\n\
         SubObjectPropertyOf(:R ObjectInverseOf(:S))\n\
         {extra}\
         )\n"
    ))
}

fn class(name: &str) -> CE<hermit_rs::structural::A> {
    CE::Class(Build::new_arc().class(format!("http://example.org/{name}")))
}

fn named(name: &str) -> OPE<hermit_rs::structural::A> {
    OPE::ObjectProperty(Build::new_arc().object_property(format!("http://example.org/{name}")))
}

fn inverse(name: &str) -> OPE<hermit_rs::structural::A> {
    OPE::InverseObjectProperty(Build::new_arc().object_property(format!("http://example.org/{name}")))
}

/// `A ⊑ ∀R.B`, `C ⊑ A ⊓ ∃Inv(S).D`, `D ⊑ ¬B`: `C` is satisfiable (its
/// `Inv(S)`-successor need not be an `R`-successor). The flawed automaton
/// pushed `B` along the `Inv(S)` edge and made `C` unsatisfiable.
#[test]
fn all_values_from_r_does_not_propagate_along_inverse_s() {
    let onto = ontology(
        "SubClassOf(:A ObjectAllValuesFrom(:R :B))\n\
         SubClassOf(:C :A)\n\
         SubClassOf(:C ObjectSomeValuesFrom(ObjectInverseOf(:S) :D))\n\
         SubClassOf(:D ObjectComplementOf(:B))\n",
    );
    assert!(is_concept_satisfiable(&onto, class("C")).expect("reason"));
    let some_inv_s_d = CE::ObjectSomeValuesFrom {
        ope: inverse("S"),
        bce: Box::new(class("D")),
    };
    let query = CE::ObjectIntersectionOf(vec![class("A"), some_inv_s_d]);
    let some_inv_s_b = CE::ObjectSomeValuesFrom {
        ope: inverse("S"),
        bce: Box::new(class("B")),
    };
    assert!(!is_subsumed_by(&onto, query, some_inv_s_b).expect("reason"));
}

/// The valid direction survives: `R ∘ R ⊑ Inv(S) ∘ Inv(S) ⊑ Inv(S)`, so
/// `∀Inv(S).B` reaches the end of an `R`-chain, and `∀S.B` reaches the start of
/// one from its end.
#[test]
fn r_chains_compose_into_inverse_s_chains() {
    let onto = ontology(
        "SubClassOf(:A ObjectAllValuesFrom(ObjectInverseOf(:S) :B))\n\
         SubClassOf(:C ObjectAllValuesFrom(:S :B))\n",
    );
    let r_r_not_b = CE::ObjectSomeValuesFrom {
        ope: named("R"),
        bce: Box::new(CE::ObjectSomeValuesFrom {
            ope: named("R"),
            bce: Box::new(CE::ObjectComplementOf(Box::new(class("B")))),
        }),
    };
    let query = CE::ObjectIntersectionOf(vec![class("A"), r_r_not_b]);
    assert!(!is_concept_satisfiable(&onto, query).expect("reason"));
    let inv_r_inv_r_not_b = CE::ObjectSomeValuesFrom {
        ope: inverse("R"),
        bce: Box::new(CE::ObjectSomeValuesFrom {
            ope: inverse("R"),
            bce: Box::new(CE::ObjectComplementOf(Box::new(class("B")))),
        }),
    };
    let query = CE::ObjectIntersectionOf(vec![class("C"), inv_r_inv_r_not_b]);
    assert!(!is_concept_satisfiable(&onto, query).expect("reason"));
}

#[test]
fn inverse_s_is_not_a_sub_property_of_r() {
    let onto = ontology("");
    assert!(is_object_property_subsumed_by(&onto, named("R"), inverse("S")).expect("reason"));
    assert!(is_object_property_subsumed_by(&onto, inverse("R"), named("S")).expect("reason"));
    assert!(!is_object_property_subsumed_by(&onto, inverse("S"), named("R")).expect("reason"));
    assert!(!is_object_property_subsumed_by(&onto, named("S"), inverse("R")).expect("reason"));
}

#[test]
fn property_hierarchy_keeps_r_strictly_below_inverse_s() {
    let hierarchy = classify_object_property_expressions(&ontology("")).expect("classify");
    let sub_of_r = hierarchy.sub_elements(&named("R"), false);
    assert!(!sub_of_r.contains(&inverse("S")), "{sub_of_r:?}");
    assert!(!hierarchy.equivalent_elements_of(&named("R")).contains(&inverse("S")));
    assert!(hierarchy.super_elements(&named("R"), false).contains(&inverse("S")));
}
