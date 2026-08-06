//! The role-automaton construction must answer exactly as Java HermiT does,
//! including where Java's answer depends on how its `HashSet`s happen to bucket
//! the property IRIs.
//!
//! `ObjectPropertyInclusionManager.connectAllAutomata` seeds its recursion from
//! `propertiesToStartRecursion`, a `java.util.HashSet`, and the automaton a
//! property ends up with depends on the order that set is walked. Java's hashing
//! is content-based, so the answer is stable per ontology — but it is *not*
//! invariant under renaming: the three fixtures below are pairwise logically
//! identical in the relevant part, and Java derives the subsumption on two of
//! them and not on the third. Reproducing Java means reproducing that.
//!
//! Verified against ROBOT 1.9.10 / HermiT 1.4.5.519:
//!
//! ```text
//! robot reason -i tests/data/role_automaton/<f>.ofn -r hermit -o out.owl
//!   inverse_chain_completeness.ofn  ->  M ⊑ C            entailed
//!   efo_pattern.ofn                 ->  MONDO_0004785 ⊑ EFO_0000524   NOT entailed
//!   efo_pattern_renamed.ofn         ->  M ⊑ C            entailed
//! ```

use horned_owl::model::{Build, ClassExpression as CE};
use horned_owl::ontology::set::SetOntology;
use hermit_rs::reasoner::is_subsumed_by;
use std::path::Path;

fn load(name: &str) -> SetOntology<hermit_rs::structural::A> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/role_automaton").join(name);
    let mut f = std::io::BufReader::new(std::fs::File::open(&path).expect("fixture"));
    let (onto, _): (horned_owl::ontology::component_mapped::ComponentMappedOntology<
        hermit_rs::structural::A,
        horned_owl::model::AnnotatedComponent<hermit_rs::structural::A>,
    >, _) = horned_owl::io::ofn::reader::read_with_build(&mut f, &Build::new_arc()).expect("parse");
    onto.into()
}

fn subsumed(name: &str, sub: &str, sup: &str) -> bool {
    let onto = load(name);
    let b = Build::new_arc();
    is_subsumed_by(&onto, CE::Class(b.class(sub)), CE::Class(b.class(sup))).expect("classify")
}

#[test]
fn minimal_inverse_chain_case_is_entailed_as_in_java() {
    assert!(
        subsumed("inverse_chain_completeness.ofn", "http://ex.org/M", "http://ex.org/C"),
        "Java derives M ⊑ C here: u's chain-bearing sub-property is reached by the recursion"
    );
}

#[test]
fn efo_pattern_is_not_entailed_as_in_java() {
    // Logically the same shape as the two cases above, and Java does NOT derive it:
    // with these IRIs the seed order reaches Inv(EFO_0000784) first, so the forward
    // property is filled in as the mirror of its inverse and loses the sub-chain.
    // Seeding the recursion with every property (rather than Java's sinks only)
    // derived it anyway and put eight subclass edges into EFO's `efo.owl` that
    // ROBOT does not emit.
    assert!(
        !subsumed(
            "efo_pattern.ofn",
            "http://purl.obolibrary.org/obo/MONDO_0004785",
            "http://www.ebi.ac.uk/efo/EFO_0000524"
        ),
        "Java does not derive MONDO_0004785 ⊑ EFO_0000524 on these IRIs"
    );
}

#[test]
fn efo_pattern_renamed_is_entailed_as_in_java() {
    // The same axioms as `efo_pattern.ofn` under different IRIs — and Java's answer
    // flips, which is the whole point: the construction is IRI-order sensitive and
    // a faithful port has to be sensitive the same way.
    assert!(
        subsumed("efo_pattern_renamed.ofn", "http://ex.org/M", "http://ex.org/C"),
        "Java derives M ⊑ C once the IRIs are renamed"
    );
}
