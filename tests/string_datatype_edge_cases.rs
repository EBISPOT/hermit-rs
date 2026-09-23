//! Three string datatype corrections, two of which deviate from Java HermiT.
//!
//! Lengths. The XSD 1.1 length facets of xsd:string, rdf:PlainLiteral and
//! xsd:anyURI count characters (Part 2 §4.3.1; a character is a code point,
//! §2.4), so U+10000 has length 1. HermiT counts UTF-16 code units (Java
//! `String.length()`), 2 for it.
//!
//! Patterns. `.` is `[^\n\r]` over every character, `\d` is `\p{Nd}` and `\w`
//! is every character but `\p{P}`, `\p{Z}` and `\p{C}` (Part 2 §G.4.2.5); `^`
//! and `$` are normal characters (§G.4.2.3). The `regex` crate and HermiT's
//! approximations of the class escapes disagree. (An anyURI may contain U+FFFE,
//! which is no XML character, so `.` must match it; the reasoner rejects pattern
//! facets on anyURI, so the datatype manager's unit tests check that.)
//!
//! Long length windows. A length window near 2^31 with a pattern is reasoned
//! about symbolically, not with one automaton state per length, which exhausts
//! memory in HermiT. The test binary runs under the 512 MiB allocation budget.
use hermit_rs::{reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;

#[path = "support/memory_budget.rs"]
mod memory_budget;

fn consistent(axioms: &str) -> bool {
    let source = format!(
        r#"Prefix(:=<urn:string-edge-cases:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(
Declaration(NamedIndividual(:a))
Declaration(DataProperty(:dp))
{axioms}
)"#
    );
    let ontology: SetOntology<A> =
        horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
            .unwrap()
            .0;
    reasoner::is_ontology_consistent(&ontology).unwrap()
}

/// Whether `a` can have at least `n` distinct `dp` values in `range`.
fn has_values(n: usize, range: &str) -> bool {
    consistent(&format!("ClassAssertion(DataMinCardinality({n} :dp {range}) :a)"))
}

/// Whether `a` can have the value `literal` in `range`.
fn admits(range: &str, literal: &str) -> bool {
    consistent(&format!(
        "DataPropertyRange(:dp {range})\nDataPropertyAssertion(:dp :a {literal})"
    ))
}

#[test]
fn length_counts_characters() {
    let supplementary = "\"\u{10000}\"";
    for datatype in ["xsd:string", "rdf:PlainLiteral"] {
        assert!(admits(&format!("DatatypeRestriction({datatype} xsd:length \"1\"^^xsd:integer)"), supplementary));
        assert!(!admits(&format!("DatatypeRestriction({datatype} xsd:length \"2\"^^xsd:integer)"), supplementary));
    }
    assert!(admits(
        "DatatypeRestriction(rdf:PlainLiteral xsd:maxLength \"1\"^^xsd:integer)",
        "\"\u{10000}\"@en"
    ));
    let uri = "\"http://x/\u{10000}\"^^xsd:anyURI";
    assert!(admits("DatatypeRestriction(xsd:anyURI xsd:length \"10\"^^xsd:integer)", uri));
    assert!(!admits("DatatypeRestriction(xsd:anyURI xsd:length \"11\"^^xsd:integer)", uri));
    // The value spaces agree: [a U+10000]{1,2} holds 2 + 4 strings of one or
    // two characters.
    let pattern = "DatatypeRestriction(xsd:string xsd:pattern \"[a\u{10000}]+\" xsd:maxLength \"2\"^^xsd:integer)";
    assert!(has_values(6, pattern));
    assert!(!has_values(7, pattern));
}

#[test]
fn pattern_escapes_have_their_xsd_meaning() {
    let pattern = |p: &str| format!("DatatypeRestriction(xsd:string xsd:pattern \"{p}\")");
    // ARABIC-INDIC DIGIT THREE is a decimal digit.
    assert!(admits(&pattern("\\\\d"), "\"\u{663}\""));
    // Symbols are word characters, `_` (connector punctuation) is not.
    assert!(admits(&pattern("\\\\w"), "\"+\""));
    assert!(!admits(&pattern("\\\\w"), "\"_\""));
    assert!(admits(&pattern("^a$"), "\"^a$\""));
    // `.` is every character but the line terminators.
    assert!(admits(&pattern("."), "\"\u{10000}\""));
    assert!(!admits(&pattern("."), "\"\r\""));
}

#[test]
fn length_windows_near_two_to_the_31_stay_small() {
    let window = |pattern: &str, facets: &str| {
        format!("DatatypeRestriction(xsd:string xsd:pattern \"{pattern}\" {facets})")
    };
    let min = "xsd:minLength \"2147483000\"^^xsd:integer";
    let exact = "xsd:length \"2147483000\"^^xsd:integer";
    let max = "xsd:maxLength \"2147483001\"^^xsd:integer";
    assert!(has_values(100, &window("a*", min)));
    // One string of each length.
    assert!(has_values(1, &window("a*", exact)));
    assert!(!has_values(2, &window("a*", exact)));
    assert!(has_values(2, &window("a*", &format!("{min} {max}"))));
    assert!(!has_values(3, &window("a*", &format!("{min} {max}"))));
    // Only even lengths, and 2^n strings of length n.
    assert!(!has_values(1, &window("(aa)*", "xsd:length \"2147483001\"^^xsd:integer")));
    assert!(has_values(100, &window("[ab]*", exact)));
    // A negated window leaves the other lengths.
    let not_short = "DataComplementOf(DatatypeRestriction(xsd:string xsd:maxLength \"2147482999\"^^xsd:integer))";
    let long_a = format!("DataIntersectionOf({} {not_short})", window("a*", max));
    assert!(has_values(2, &long_a));
    assert!(!has_values(3, &long_a));
}
