//! Issue #9: `anyURI[minLength 0] ⊓ ¬anyURI[minLength 1]` contains exactly the
//! empty URI (XSD 1.1 Part 2 §3.3.17.1, §4.3.2.3). The Java suite expects the
//! range to be empty because dk.brics `getFiniteStrings` omits the empty word of
//! a non-singleton automaton; `tests/java/corrections.json` documents the
//! corrected replay oracle. These checks establish membership and cardinality
//! without that trace.
use hermit_rs::{reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;

/// Consistency of `reasoner.AnyURITest.testIntersection`'s axioms plus `extra`:
/// `a` has a `dp` value, and every `dp` value of `a` lies in the range.
fn consistent_with(extra: &str) -> bool {
    let source = format!(
        r#"Prefix(:=<urn:issue9:>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(
ClassAssertion(:A :a)
SubClassOf(:A DataAllValuesFrom(:dp DatatypeRestriction(xsd:anyURI xsd:minLength "0"^^xsd:integer)))
SubClassOf(:A DataAllValuesFrom(:dp DataComplementOf(DatatypeRestriction(xsd:anyURI xsd:minLength "1"^^xsd:integer))))
SubClassOf(:A DataMinCardinality(1 :dp))
{extra}
)"#
    );
    let ontology: SetOntology<A> =
        horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
            .unwrap()
            .0;
    reasoner::is_ontology_consistent(&ontology).unwrap()
}

#[test]
fn the_empty_uri_is_a_value_of_the_range() {
    // A model: dp = {(a, ""^^xsd:anyURI)}.
    assert!(consistent_with(""));
    assert!(consistent_with(
        r#"DataPropertyAssertion(:dp :a ""^^xsd:anyURI)"#
    ));
    assert!(consistent_with(
        "SubClassOf(:A DataExactCardinality(1 :dp))"
    ));
}

#[test]
fn the_range_has_no_other_value() {
    // One value only: a second, distinct value cannot exist.
    assert!(!consistent_with("SubClassOf(:A DataMinCardinality(2 :dp))"));
    // A one-character URI satisfies minLength 1, so its complement excludes it.
    assert!(!consistent_with(
        r#"DataPropertyAssertion(:dp :a "a"^^xsd:anyURI)"#
    ));
    // The empty string is not an anyURI value (OWL 2 Structural Specification §4.6).
    assert!(!consistent_with(
        r#"DataPropertyAssertion(:dp :a ""^^xsd:string)"#
    ));
}
