//! The role-automaton construction must derive the inverse + chain entailment
//! whatever the property IRIs are called (EBISPOT/hermit-rs#5).
//!
//! Java HermiT's `connectAllAutomata` seeds its recursion from
//! `propertiesToStartRecursion`, a `java.util.HashSet`, and when a property `R`
//! has both a chain-bearing sub-property and a declared inverse, the automaton `R`
//! ends up with depends on whether `R` or `Inv(R)` is built first: built from the
//! inverse side, `R` is stored as a plain mirror that never saw its own sub-chain.
//! Java's hashing is content-based, so its answer is stable per ontology but not
//! invariant under renaming — verified against ROBOT 1.9.7 / HermiT 1.4.5.519:
//!
//! ```text
//! robot reason -i tests/data/role_automaton/<f>.ofn -r hermit -o out.owl
//!   inverse_chain_completeness.ofn  ->  M ⊑ C            entailed
//!   efo_pattern.ofn                 ->  MONDO_0004785 ⊑ EFO_0000524   NOT entailed
//!   efo_pattern_renamed.ofn         ->  M ⊑ C            entailed
//! ```
//!
//! and on the four-property pattern below Java misses the entailment on 18 of the
//! 24 spellings. hermit-rs splices the sub-properties of both `R` and `Inv(R)`
//! into `R`'s automaton, so it derives the entailment on all of them.

use hermit_rs::reasoner::is_subsumed_by;
use horned_owl::model::{Build, ClassExpression as CE};
use horned_owl::ontology::set::SetOntology;
use std::path::Path;

type Onto = SetOntology<hermit_rs::structural::A>;

fn parse<R: std::io::BufRead>(mut reader: R) -> Onto {
    let (onto, _): (
        horned_owl::ontology::component_mapped::ComponentMappedOntology<
            hermit_rs::structural::A,
            horned_owl::model::AnnotatedComponent<hermit_rs::structural::A>,
        >,
        _,
    ) = horned_owl::io::ofn::reader::read_with_build(&mut reader, &Build::new_arc())
        .expect("parse");
    onto.into()
}

fn load(name: &str) -> Onto {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/role_automaton")
        .join(name);
    parse(std::io::BufReader::new(
        std::fs::File::open(&path).expect("fixture"),
    ))
}

fn subsumed(onto: &Onto, sub: &str, sup: &str) -> bool {
    let b = Build::new_arc();
    is_subsumed_by(onto, CE::Class(b.class(sub)), CE::Class(b.class(sup))).expect("classify")
}

#[test]
fn minimal_inverse_chain_case_is_entailed() {
    assert!(subsumed(
        &load("inverse_chain_completeness.ofn"),
        "http://ex.org/M",
        "http://ex.org/C"
    ));
}

#[test]
fn efo_pattern_is_entailed_on_the_real_iris() {
    // Java HermiT does not derive this one: with these IRIs its seed order builds
    // Inv(EFO_0000784) first and EFO_0000784 loses its RO_0004027 ∘ BFO_0000050*
    // sub-chain. The entailment is valid (ELK, JFact and Whelk derive it) and it
    // is what places EFO's otitis / sinusitis / uveitis / ... classes under
    // "head and neck disorder".
    assert!(subsumed(
        &load("efo_pattern.ofn"),
        "http://purl.obolibrary.org/obo/MONDO_0004785",
        "http://www.ebi.ac.uk/efo/EFO_0000524"
    ));
}

#[test]
fn efo_pattern_is_entailed_after_renaming() {
    assert!(subsumed(
        &load("efo_pattern_renamed.ofn"),
        "http://ex.org/M",
        "http://ex.org/C"
    ));
}

/// The issue's six-axiom pattern. `S ⊑ H`, `S ∘ P ⊑ S`, `H` has the declared
/// inverse `I`, and the entailment `Otitis ⊑ HeadDisorder` never touches `I`:
///
/// ```text
/// Otitis ⊑ ∃S.ExtEar,  ExtEar ⊑ ∃P.Head,  S∘P ⊑ S   ⟹  Otitis ⊑ ∃S.Head
/// S ⊑ H                                            ⟹  Otitis ⊑ ∃H.Head ≡ HeadDisorder
/// ```
///
/// `order` gives the four roles in the lexical order their IRIs get, e.g. `"HPSI"`
/// names them `p0_H`, `p1_P`, `p2_S`, `p3_I`. `with_inverse = false` drops the
/// inverse declaration, which must never change the answer.
fn issue_5_pattern(order: &str, with_inverse: bool) -> String {
    let iri = |role: char| {
        let i = order.find(role).expect("role");
        format!("<http://example.org/p{i}_{role}>")
    };
    let (h, p, s, i) = (iri('H'), iri('P'), iri('S'), iri('I'));
    let inverse = if with_inverse {
        format!("InverseObjectProperties({h} {i})\n")
    } else {
        String::new()
    };
    format!(
        "Prefix(:=<http://example.org/>)\n\
         Ontology(<http://example.org/repro>\n\
         Declaration(Class(:Otitis)) Declaration(Class(:ExtEar))\n\
         Declaration(Class(:Head)) Declaration(Class(:HeadDisorder))\n\
         Declaration(ObjectProperty({s})) Declaration(ObjectProperty({h}))\n\
         Declaration(ObjectProperty({i})) Declaration(ObjectProperty({p}))\n\
         SubObjectPropertyOf({s} {h})\n\
         {inverse}\
         SubObjectPropertyOf(ObjectPropertyChain({s} {p}) {s})\n\
         SubClassOf(:Otitis ObjectSomeValuesFrom({s} :ExtEar))\n\
         SubClassOf(:ExtEar ObjectSomeValuesFrom({p} :Head))\n\
         EquivalentClasses(:HeadDisorder ObjectSomeValuesFrom({h} :Head))\n\
         )\n"
    )
}

const ALL_ORDERS: [&str; 24] = [
    "HIPS", "HISP", "HPIS", "HPSI", "HSIP", "HSPI", "IHPS", "IHSP", "IPHS", "IPSH", "ISHP", "ISPH",
    "PHIS", "PHSI", "PIHS", "PISH", "PSHI", "PSIH", "SHIP", "SHPI", "SIHP", "SIPH", "SPHI", "SPIH",
];

#[test]
fn issue_5_pattern_is_entailed_on_every_property_iri_order() {
    let mut missed = Vec::new();
    for order in ALL_ORDERS {
        for with_inverse in [true, false] {
            let onto = parse(std::io::Cursor::new(issue_5_pattern(order, with_inverse)));
            if !subsumed(
                &onto,
                "http://example.org/Otitis",
                "http://example.org/HeadDisorder",
            ) {
                missed.push(format!(
                    "{order}{}",
                    if with_inverse { "" } else { " (no inverse)" }
                ));
            }
        }
    }
    assert!(
        missed.is_empty(),
        "Otitis ⊑ HeadDisorder missed on: {missed:?}"
    );
}
