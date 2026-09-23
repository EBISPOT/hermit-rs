//! Datatype reasoning robustness fixes, none with an issue.
//!
//! * Large value spaces: a string value space over a length window longer
//!   than 4096 characters, whose automaton has more than 160 states, was
//!   counted as `u128::MAX` ("at least") instead of exactly, so a pigeonhole
//!   clash was missed. (The clique comparison by ranges instead of counts and
//!   the full listing of large survivors are checked by the datatype manager's
//!   unit tests, since a tableau with 5000 data nodes is slow.)
//! * `ignoreUnsupportedDatatypes`: a literal of an unsupported datatype
//!   becomes an anonymous constant, HermiT's `AnonymousConstantValue`, a value
//!   equal only to itself and in no supported datatype. A `DataOneOf` holding
//!   one was taken to have infinitely many values.
//! * dateTime values beyond ±9999 or finer than milliseconds are valid XSD 1.1
//!   values that are not supported; they are rejected with their own error,
//!   not as malformed literals.
//! * `"Infinity"` is not an XSD 1.1 spelling of xsd:double or xsd:float (Part 2
//!   §3.3.4.2, §3.3.5.2); `INF` is. HermiT accepts Java's spelling.
use hermit_rs::reasoner::Reasoner;
use hermit_rs::structural::{
    Configuration, OWLAxioms, OWLAxiomsExpressivity, OWLClausification, OWLNormalization, A,
};
use horned_owl::ontology::set::SetOntology;

#[path = "support/memory_budget.rs"]
mod memory_budget;

fn ontology(axioms: &str) -> SetOntology<A> {
    let source = format!(
        r#"Prefix(:=<urn:datatype-robustness:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)
Ontology(
Declaration(NamedIndividual(:a))
Declaration(DataProperty(:dp))
Declaration(Datatype(:U))
{axioms}
)"#
    );
    horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
        .unwrap()
        .0
}

fn consistent(axioms: &str) -> Result<bool, String> {
    hermit_rs::reasoner::is_ontology_consistent(&ontology(axioms))
}

/// Consistency with `ignoreUnsupportedDatatypes` in the clausifier and the
/// reasoner.
fn consistent_ignoring_unsupported(axioms: &str) -> bool {
    let clausify_config = Configuration { ignore_unsupported_datatypes: true };
    let reasoner_config = hermit_rs::configuration::Configuration {
        ignore_unsupported_datatypes: true,
        ..hermit_rs::configuration::Configuration::default()
    };
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(&ontology(axioms)).unwrap();
    let axioms = normalization.into_axioms();
    let expressivity = OWLAxiomsExpressivity::new(&axioms);
    let dl_ontology = OWLClausification::new(clausify_config)
        .clausify("urn:datatype-robustness", &axioms, &expressivity)
        .unwrap();
    Reasoner::with_configuration(&dl_ontology, reasoner_config).is_consistent()
}

#[test]
fn long_windows_over_large_automata_are_counted_exactly() {
    // (a{200})* has 200 string states; of length 5000 it holds a^5000 only.
    let range = "DatatypeRestriction(xsd:string xsd:pattern \"(a{200})*\" xsd:length \"5000\"^^xsd:integer)";
    let values = |n: usize| consistent(&format!("ClassAssertion(DataMinCardinality({n} :dp {range}) :a)")).unwrap();
    assert!(values(1));
    assert!(!values(2));
    // Of length 5000 or 5200: two values.
    let range = "DatatypeRestriction(xsd:string xsd:pattern \"(a{200})*\" xsd:minLength \"5000\"^^xsd:integer xsd:maxLength \"5399\"^^xsd:integer)";
    let values = |n: usize| consistent(&format!("ClassAssertion(DataMinCardinality({n} :dp {range}) :a)")).unwrap();
    assert!(values(2));
    assert!(!values(3));
}

#[test]
fn anonymous_constants_are_values_of_no_supported_datatype() {
    let at_least = |n: usize, range: &str| {
        consistent_ignoring_unsupported(&format!("ClassAssertion(DataMinCardinality({n} :dp {range}) :a)"))
    };
    // Three members, so at most three values; "x"^^:U is not true or false.
    let one_of = "DataOneOf(\"x\"^^:U \"true\"^^xsd:boolean \"false\"^^xsd:boolean)";
    assert!(at_least(3, one_of));
    assert!(!at_least(4, one_of));
    // Only the booleans are booleans.
    let booleans = "DataIntersectionOf(xsd:boolean DataOneOf(\"x\"^^:U \"true\"^^xsd:boolean \"false\"^^xsd:boolean \"y\"^^:U))";
    assert!(at_least(2, booleans));
    assert!(!at_least(3, booleans));
    // Two anonymous constants of one name are one value.
    let same = "DataOneOf(\"x\"^^:U \"x\"^^:U)";
    assert!(at_least(1, same));
    assert!(!at_least(2, same));
}

#[test]
fn unsupported_datetime_values_are_rejected_explicitly() {
    let assert_value = |literal: &str| format!("DataPropertyAssertion(:dp :a {literal})");
    for lexical in [
        "10000-01-01T00:00:00Z",
        "-10000-01-01T00:00:00",
        "2000-01-01T00:00:00.0001Z",
        "123456-02-29T12:00:00.1234567+01:00",
    ] {
        let error = consistent(&assert_value(&format!("\"{lexical}\"^^xsd:dateTime"))).unwrap_err();
        assert!(error.starts_with("UnsupportedDatatypeValue"), "{lexical}: {error}");
        let error = consistent(&format!(
            "DataPropertyRange(:dp DatatypeRestriction(xsd:dateTime xsd:minInclusive \"{lexical}\"^^xsd:dateTime))"
        ))
        .unwrap_err();
        assert!(error.starts_with("UnsupportedDatatypeValue"), "{lexical}: {error}");
    }
    // Invalid forms stay malformed: a padded year, a February 29 of a common
    // year and a nonzero fraction at 24:00:00.
    for lexical in ["010000-01-01T00:00:00", "10001-02-29T00:00:00", "2000-01-01T24:00:00.0001"] {
        let error = consistent(&assert_value(&format!("\"{lexical}\"^^xsd:dateTime"))).unwrap_err();
        assert!(error.starts_with("MalformedLiteralException"), "{lexical}: {error}");
    }
    assert_eq!(consistent(&assert_value("\"2000-01-01T00:00:00.123Z\"^^xsd:dateTime")), Ok(true));
}

#[test]
fn infinity_is_not_an_xsd_spelling() {
    for datatype in ["xsd:double", "xsd:float"] {
        for lexical in ["Infinity", "+Infinity", "-Infinity"] {
            let error = consistent(&format!("DataPropertyAssertion(:dp :a \"{lexical}\"^^{datatype})")).unwrap_err();
            assert!(error.starts_with("MalformedLiteralException"), "{error}");
        }
        for lexical in ["INF", "+INF", "-INF"] {
            assert_eq!(consistent(&format!("DataPropertyAssertion(:dp :a \"{lexical}\"^^{datatype})")), Ok(true));
        }
    }
    // DatatypesTest.testINF with the XSD spelling: inconsistent, as Java found.
    let test_inf = "Declaration(Class(:A))
        SubClassOf(:A DataAllValuesFrom(:dp DataOneOf(\"INF\"^^xsd:double)))
        SubClassOf(:A DataSomeValuesFrom(:dp rdfs:Literal))
        ClassAssertion(:A :a)
        NegativeDataPropertyAssertion(:dp :a \"INF\"^^xsd:double)";
    assert_eq!(consistent(test_inf), Ok(false));
}

#[test]
fn short_uris_are_not_only_ascii() {
    // anyURI[maxLength 1] holds the empty URI, the one-character ASCII URIs
    // and every character above U+0080 that is no space or control character,
    // so 100 distinct values fit. Its values over an ASCII alphabet, 86, were
    // taken as all of them.
    let range = "DatatypeRestriction(xsd:anyURI xsd:maxLength \"1\"^^xsd:integer)";
    assert_eq!(consistent(&format!("ClassAssertion(DataMinCardinality(100 :dp {range}) :a)")), Ok(true));
    let empty = "DatatypeRestriction(xsd:anyURI xsd:maxLength \"0\"^^xsd:integer)";
    assert_eq!(consistent(&format!("ClassAssertion(DataMinCardinality(2 :dp {empty}) :a)")), Ok(false));
}

#[test]
fn a_constant_is_not_taken_for_a_node_with_the_same_ranges() {
    // The value of :a's dp must differ from "1"; neither node has a datatype
    // range, but the constant has one value and the fresh node infinitely many.
    for literal in ["\"1\"^^xsd:integer", "\"x\""] {
        let axioms = format!(
            "ClassAssertion(DataSomeValuesFrom(:dp rdfs:Literal) :a)\nNegativeDataPropertyAssertion(:dp :a {literal})"
        );
        assert_eq!(consistent(&axioms), Ok(true), "{literal}");
    }
}
