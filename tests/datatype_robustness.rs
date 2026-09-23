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
//!   values. They were rejected; their instants are now held exactly.
//! * A large bounded repetition in a pattern, such as `a{2147483000}`, built
//!   one automaton state per copy; it is now a length window, also inside
//!   groups that are neither quantified nor hold an alternation. Where it
//!   cannot be one, a pattern whose automaton would pass
//!   `MAX_PATTERN_STATES` states is rejected with a resource error.
//! * A string count over a long window and a large, densely connected
//!   automaton, and an anyURI count of a space too large to list, were upper
//!   bounds; they are now exact, capped at one more than the data nodes.
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
fn long_windows_over_dense_automata_are_counted_exactly() {
    // Over two thousand states that remember the last ten letters, the
    // matrix powers are dense and passed the work budget, so the count was
    // "at least u128::MAX". The dense part has even lengths only; of this odd
    // length there is one string, x^2147483001.
    let range = "DatatypeRestriction(xsd:string xsd:pattern \"(xx)*x|yy(([ab]c)*ac([ab]c){9})\" xsd:length \"2147483001\"^^xsd:integer)";
    let values = |n: usize| consistent(&format!("ClassAssertion(DataMinCardinality({n} :dp {range}) :a)")).unwrap();
    assert!(values(1));
    assert!(!values(2));
}

#[test]
fn large_bounded_repetitions_are_reasoned_about_symbolically() {
    // a{2147483000} holds one string. Its automaton had a state per copy and
    // exhausted memory.
    let range = "DatatypeRestriction(xsd:string xsd:pattern \"a{2147483000}\")";
    let values = |n: usize| consistent(&format!("ClassAssertion(DataMinCardinality({n} :dp {range}) :a)")).unwrap();
    assert!(values(1));
    assert!(!values(2));
    // Emptiness: the string is too long for maxLength, and not in b*.
    for other in [
        "DatatypeRestriction(xsd:string xsd:maxLength \"2147482999\"^^xsd:integer)",
        "DatatypeRestriction(xsd:string xsd:pattern \"b*\")",
    ] {
        let axiom = format!("ClassAssertion(DataSomeValuesFrom(:dp DataIntersectionOf({range} {other})) :a)");
        assert!(!consistent(&axiom).unwrap(), "{other}");
    }
    // Membership: x, 300 to 3000000 digits and y.
    let digits = "DatatypeRestriction(xsd:string xsd:pattern \"x[0-9]{300,3000000}y\")";
    let member = |value: &str| {
        consistent(&format!("DataPropertyRange(:dp {digits}) DataPropertyAssertion(:dp :a \"{value}\")")).unwrap()
    };
    assert!(member(&format!("x{}y", "7".repeat(300))));
    assert!(member(&format!("x{}y", "0".repeat(4000))));
    assert!(!member(&format!("x{}y", "7".repeat(299))));
    assert!(!member(&format!("x{}zy", "7".repeat(300))));
    // Counting: x, 300 or 301 copies of `a` and y are two strings.
    let two = "DatatypeRestriction(xsd:string xsd:pattern \"xa{300,301}y\")";
    let values = |n: usize| consistent(&format!("ClassAssertion(DataMinCardinality({n} :dp {two}) :a)")).unwrap();
    assert!(values(2));
    assert!(!values(3));
}

#[test]
fn large_repetitions_elsewhere_are_windows_or_a_resource_error() {
    // Inside plain groups the repetition is still a length window: one string.
    let range = "DatatypeRestriction(xsd:string xsd:pattern \"x(y(a{2147483000})z)\")";
    let values = |n: usize| consistent(&format!("ClassAssertion(DataMinCardinality({n} :dp {range}) :a)")).unwrap();
    assert!(values(1));
    assert!(!values(2));
    // In a quantified group, beside a piece of varying length or beside a
    // second large repetition it would be built one state per copy, which
    // exhausted memory: the ontology is rejected instead.
    for pattern in ["(a{2147483000})*", "a*b{2147483000}", "a{2147483000}b{2147483000}"] {
        let range = format!("DatatypeRestriction(xsd:string xsd:pattern \"{pattern}\")");
        let result = consistent(&format!("ClassAssertion(DataSomeValuesFrom(:dp {range}) :a)"));
        assert!(result.as_ref().is_err_and(|e| e.starts_with("Resource limit")), "{pattern}: {result:?}");
    }
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
fn datetime_values_are_exact_beyond_milliseconds_and_four_digit_years() {
    let assert_value = |literal: &str| format!("DataPropertyAssertion(:dp :a {literal})");
    for lexical in [
        "10000-01-01T00:00:00Z",
        "-10000-01-01T00:00:00",
        "2000-01-01T00:00:00.0001Z",
        "123456-02-29T12:00:00.1234567+01:00",
    ] {
        assert_eq!(consistent(&assert_value(&format!("\"{lexical}\"^^xsd:dateTime"))), Ok(true), "{lexical}");
        assert_eq!(
            consistent(&format!(
                "DataPropertyRange(:dp DatatypeRestriction(xsd:dateTime xsd:minInclusive \"{lexical}\"^^xsd:dateTime))"
            )),
            Ok(true),
            "{lexical}"
        );
    }
    // Invalid forms stay malformed: a padded year, a February 29 of a common
    // year and a nonzero fraction at 24:00:00.
    for lexical in ["010000-01-01T00:00:00", "10100-02-29T00:00:00", "2000-01-01T24:00:00.0001"] {
        let error = consistent(&assert_value(&format!("\"{lexical}\"^^xsd:dateTime"))).unwrap_err();
        assert!(error.starts_with("MalformedLiteralException"), "{lexical}: {error}");
    }
    // Whether two literals are one value: with a functional property, the
    // ontology is consistent exactly when they are.
    let same_value = |x: &str, y: &str| {
        consistent(&format!(
            "FunctionalDataProperty(:dp)
             DataPropertyAssertion(:dp :a \"{x}\"^^xsd:dateTime)
             DataPropertyAssertion(:dp :a \"{y}\"^^xsd:dateTime)"
        ))
        .unwrap()
    };
    // Fractions are exact: trailing zeros do not matter, a tenth of a
    // millisecond does.
    assert!(same_value("2000-01-01T00:00:00.0001Z", "2000-01-01T00:00:00.000100Z"));
    assert!(!same_value("2000-01-01T00:00:00.0001Z", "2000-01-01T00:00:00.0002Z"));
    assert!(!same_value("2000-01-01T00:00:00.0001Z", "2000-01-01T00:00:00Z"));
    // Years beyond 9999, with the 24:00:00 normalisation and the 400-year
    // leap rule (10000 is a leap year).
    assert!(same_value("10000-12-31T24:00:00Z", "10001-01-01T00:00:00Z"));
    assert!(same_value("10000-02-28T24:00:00Z", "10000-02-29T00:00:00Z"));
    assert!(!same_value("10000-02-29T00:00:00Z", "10000-03-01T00:00:00Z"));
    assert!(!same_value("-123456-01-01T00:00:00", "-123455-01-01T00:00:00"));
    // The same instant at another offset is equal but not identical (OWL 2
    // §4.7), so it is another value.
    assert!(!same_value("10000-01-01T00:00:00Z", "10000-01-01T01:00:00+01:00"));

    // A bound finer than a millisecond: 0.0001 s lies strictly between 0 and
    // 0.001 s, 0.0011 s does not.
    let between = |x: &str| {
        consistent(&format!(
            "DataPropertyRange(:dp DatatypeRestriction(xsd:dateTime
                xsd:minExclusive \"2000-01-01T00:00:00Z\"^^xsd:dateTime
                xsd:maxExclusive \"2000-01-01T00:00:00.001Z\"^^xsd:dateTime))
             DataPropertyAssertion(:dp :a \"{x}\"^^xsd:dateTime)"
        ))
        .unwrap()
    };
    assert!(between("2000-01-01T00:00:00.0001Z"));
    assert!(between("2000-01-01T00:00:00.0009999999999Z"));
    assert!(!between("2000-01-01T00:00:00.0011Z"));
    // Far years are ordered too.
    assert!(!consistent(
        "DataPropertyRange(:dp DatatypeRestriction(xsd:dateTime xsd:maxInclusive \"9999-12-31T23:59:59Z\"^^xsd:dateTime))
         DataPropertyAssertion(:dp :a \"123456-01-01T00:00:00Z\"^^xsd:dateTime)"
    )
    .unwrap());

    // A single instant without an offset is one value, however far and fine
    // it is (the values with an offset lie more than 14 hours inside the
    // bounds, so none does); two instants a ten-millionth of a second apart
    // are two.
    let values = |n: usize, upper: &str| {
        consistent(&format!(
            "ClassAssertion(DataMinCardinality({n} :dp DatatypeRestriction(xsd:dateTime
                xsd:minInclusive \"-123456-01-01T00:00:00.0000001\"^^xsd:dateTime
                xsd:maxInclusive \"{upper}\"^^xsd:dateTime)) :a)"
        ))
        .unwrap()
    };
    assert!(values(1, "-123456-01-01T00:00:00.0000001"));
    assert!(!values(2, "-123456-01-01T00:00:00.0000001"));
    assert!(values(2, "-123456-01-01T00:00:00.0000002"));
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
fn uris_too_many_to_list_are_counted_exactly() {
    // anyURI[pattern "%3."] matches a million strings, too many to list, of
    // which 22 are URIs: "%3" and a hex digit. The strings were counted, an
    // upper bound, so 23 distinct values fitted.
    let range = "DatatypeRestriction(xsd:anyURI xsd:pattern \"%3.\")";
    let values = |n: usize| consistent(&format!("ClassAssertion(DataMinCardinality({n} :dp {range}) :a)")).unwrap();
    assert!(values(22));
    assert!(!values(23));
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
