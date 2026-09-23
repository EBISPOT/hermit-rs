//! Two datatype corrections that deviate from Java HermiT.
//!
//! NaN bounds. NaN is incomparable with every xsd:float and xsd:double value,
//! itself included (XSD 1.1 Part 2 §3.3.4.1, §3.3.5.1), so no value satisfies a
//! bounding facet whose value is NaN, and the restricted value space is empty
//! (the note in §3.3.4.1 states this case). NaN is in the value space, so it is
//! a valid facet value. The complement of such a range is then every value of
//! the datatype, NaN included (OWL 2 Direct Semantics, Table 3). HermiT drops
//! a NaN xsd:double bound and a NaN xsd:float max* bound, keeping every value
//! but NaN.
//!
//! Lexical forms. A literal whose lexical form is not in the lexical space of
//! its datatype is rejected as malformed, as the repo does for every ill-typed
//! literal of a supported datatype (Java's MalformedLiteralException). The XSD
//! 1.1 grammars reject forms HermiT accepts: base64Binary with nonzero padding
//! bits (§3.3.16.2), boolean in other cases (§3.3.2.2), decimal with an
//! exponent (§3.3.3.1), float/double with a Java type suffix (§3.3.4.2,
//! §3.3.5.2), and dateTime years with a leading zero past four digits (§D.2.2).
//! `"+INF"` is a float/double lexical form (§3.3.4.2), which HermiT rejects.
use hermit_rs::{reasoner, structural::A};
use horned_owl::ontology::set::SetOntology;

fn check(axioms: &str) -> Result<bool, String> {
    let source = format!(
        r#"Prefix(:=<urn:nan-bounds:>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(
Declaration(NamedIndividual(:a))
Declaration(Class(:A))
Declaration(DataProperty(:dp))
{axioms}
)"#
    );
    let ontology: SetOntology<A> =
        horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
            .unwrap()
            .0;
    reasoner::is_ontology_consistent(&ontology)
}

/// Consistency of an ontology where `a` has at least `n` distinct `dp` values,
/// each in every one of `ranges`, and `extra` holds.
fn consistent(n: usize, ranges: &[&str], extra: &str) -> bool {
    let ranges: String = ranges
        .iter()
        .map(|range| format!("SubClassOf(:A DataAllValuesFrom(:dp {range}))\n"))
        .collect();
    check(&format!("ClassAssertion(:A :a)\nSubClassOf(:A DataMinCardinality({n} :dp))\n{ranges}{extra}"))
        .unwrap()
}

fn nan_bound(datatype: &str, facet: &str) -> String {
    format!(r#"DatatypeRestriction(xsd:{datatype} xsd:{facet} "NaN"^^xsd:{datatype})"#)
}

const FACETS: [&str; 4] = ["minInclusive", "minExclusive", "maxInclusive", "maxExclusive"];

#[test]
fn nan_bound_range_is_empty() {
    for datatype in ["float", "double"] {
        for facet in FACETS {
            let range = nan_bound(datatype, facet);
            assert!(!consistent(1, &[&range], ""), "{range} must be empty");
            for value in ["1", "INF", "-INF", "NaN"] {
                let assertion = format!(r#"DataPropertyAssertion(:dp :a "{value}"^^xsd:{datatype})"#);
                assert!(
                    !check(&format!("DataPropertyRange(:dp {range})\n{assertion}")).unwrap(),
                    "{value} must not be in {range}"
                );
            }
        }
    }
}

#[test]
fn complement_of_nan_bound_range_is_the_whole_datatype() {
    for datatype in ["float", "double"] {
        for facet in FACETS {
            let not_range = format!("DataComplementOf({})", nan_bound(datatype, facet));
            let whole = format!("xsd:{datatype}");
            // Every value of the datatype remains, NaN and the ordered ones.
            for value in ["1", "-0", "INF", "NaN"] {
                let assertion = format!(r#"DataPropertyAssertion(:dp :a "{value}"^^xsd:{datatype})"#);
                assert!(
                    consistent(1, &[&whole, &not_range], &assertion),
                    "{value} must be in {not_range}"
                );
            }
            // Counting and enumeration: NaN and 1 are two values of it.
            let two = format!(r#"DataOneOf("NaN"^^xsd:{datatype} "1"^^xsd:{datatype})"#);
            assert!(consistent(2, &[&whole, &not_range, &two], ""), "{not_range} ∩ {two}");
            assert!(!consistent(3, &[&whole, &not_range, &two], ""), "{not_range} ∩ {two}");
        }
    }
}

fn ill_typed(literal: &str) -> bool {
    check(&format!("DataPropertyAssertion(:dp :a {literal})"))
        .is_err_and(|e| e.contains("MalformedLiteralException"))
}

#[test]
fn lexical_forms_outside_the_xsd_grammars_are_ill_typed() {
    for literal in [
        r#""QR=="^^xsd:base64Binary"#,
        r#""QUJ="^^xsd:base64Binary"#,
        r#""TRUE"^^xsd:boolean"#,
        r#""False"^^xsd:boolean"#,
        r#""1E2"^^xsd:decimal"#,
        r#""1.0f"^^xsd:float"#,
        r#""1.0d"^^xsd:double"#,
        r#""01999-01-01T00:00:00"^^xsd:dateTime"#,
        r#""2000-0é-01T00:00:00"^^xsd:dateTime"#,
        r#""2000-01-01T0é:00:00"^^xsd:dateTime"#,
    ] {
        assert!(ill_typed(literal), "{literal} must be ill-typed");
    }
    for literal in [
        r#""QQ=="^^xsd:base64Binary"#,
        r#""Q Q = ="^^xsd:base64Binary"#,
        r#""QUI="^^xsd:base64Binary"#,
        r#""true"^^xsd:boolean"#,
        r#""0"^^xsd:boolean"#,
        r#""+1.50"^^xsd:decimal"#,
        r#""1E2"^^xsd:float"#,
        r#""+INF"^^xsd:double"#,
        r#""0999-01-01T00:00:00"^^xsd:dateTime"#,
    ] {
        assert!(!ill_typed(literal), "{literal} must be well-typed");
    }
}

#[test]
fn plus_inf_is_positive_infinity() {
    // "+INF" and "INF" are one value, so a functional property holds both.
    for datatype in ["float", "double"] {
        assert!(check(&format!(
            r#"FunctionalDataProperty(:dp)
DataPropertyAssertion(:dp :a "+INF"^^xsd:{datatype})
DataPropertyAssertion(:dp :a "INF"^^xsd:{datatype})"#
        ))
        .unwrap());
        assert!(!check(&format!(
            r#"FunctionalDataProperty(:dp)
DataPropertyAssertion(:dp :a "+INF"^^xsd:{datatype})
DataPropertyAssertion(:dp :a "-INF"^^xsd:{datatype})"#
        ))
        .unwrap());
    }
}
