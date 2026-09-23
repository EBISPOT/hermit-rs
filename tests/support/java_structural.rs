use super::*;
use hermit_rs::structural::{Fact, OWLAxioms, OWLNormalization};
use std::collections::BTreeSet;

pub(super) fn canonical(text: &str) -> String {
    fn expression(tokens: &[String], at: &mut usize) -> String {
        let name = tokens[*at].clone();
        *at += 1;
        if tokens.get(*at).is_none_or(|s| s != "(") {
            return name;
        }
        *at += 1;
        let mut args = Vec::new();
        while tokens[*at] != ")" {
            args.push(expression(tokens, at));
        }
        *at += 1;
        if matches!(
            name.as_str(),
            "ObjectUnionOf"
                | "ObjectIntersectionOf"
                | "ObjectOneOf"
                | "DataUnionOf"
                | "DataIntersectionOf"
                | "DataOneOf"
                | "EquivalentClasses"
                | "EquivalentObjectProperties"
                | "EquivalentDataProperties"
                | "SameIndividual"
                | "DifferentIndividuals"
                | "DisjointClasses"
        ) {
            args.sort();
        }
        format!("{name}({})", args.join(" "))
    }
    static TOKENIZER: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
    let re = TOKENIZER.get_or_init(|| {
        regex::Regex::new(r#""(?:\\.|[^"\\])*"(?:\^\^<[^>]*>|@[\w-]+)?|<[^>]*>|[^\s()]+|[()]"#)
            .unwrap()
    });
    let tokens: Vec<String> = re.find_iter(text).map(|m| m.as_str().to_string()).collect();
    let mut at = 0;
    let mut out = Vec::new();
    while at < tokens.len() {
        out.push(expression(&tokens, &mut at));
    }
    out.join(" ")
}
fn normalized(o: &O) -> HashSet<String> {
    let b = Build::new_arc();
    let mut n = OWLNormalization::new(OWLAxioms::new(), 0);
    n.process_ontology(o).unwrap();
    let a = n.into_axioms();
    let mut components = Vec::<Component<A>>::new();
    for inclusion in a.concept_inclusions {
        let sup = if inclusion.len() == 1 {
            inclusion[0].clone()
        } else {
            CE::ObjectUnionOf(inclusion)
        };
        components.push(
            SubClassOf {
                sub: CE::Class(b.class("http://www.w3.org/2002/07/owl#Thing")),
                sup,
            }
            .into(),
        );
    }
    for [sub, sup] in a.simple_object_property_inclusions {
        components.push(
            SubObjectPropertyOf {
                sub: SubObjectPropertyExpression::ObjectPropertyExpression(sub),
                sup,
            }
            .into(),
        );
    }
    for [sub, sup] in a.data_property_inclusions {
        components.push(SubDataPropertyOf { sub, sup }.into());
    }
    for key in a.has_keys {
        components.push(
            HasKey {
                ce: key.class_expression,
                vpe: key.property_expressions,
            }
            .into(),
        );
    }
    for fact in a.facts {
        components.push(match fact {
            Fact::SameIndividual(v) => SameIndividual(v).into(),
            Fact::DifferentIndividuals(v) => DifferentIndividuals(v).into(),
            Fact::ClassAssertion {
                class_expression,
                individual,
            } => ClassAssertion {
                ce: class_expression,
                i: individual,
            }
            .into(),
            Fact::ObjectPropertyAssertion { ope, from, to } => {
                ObjectPropertyAssertion { ope, from, to }.into()
            }
            Fact::NegativeObjectPropertyAssertion { ope, from, to } => {
                NegativeObjectPropertyAssertion { ope, from, to }.into()
            }
            Fact::DataPropertyAssertion { dp, from, to } => {
                DataPropertyAssertion { dp, from, to }.into()
            }
            Fact::NegativeDataPropertyAssertion { dp, from, to } => {
                NegativeDataPropertyAssertion { dp, from, to }.into()
            }
        });
    }
    components
        .iter()
        .map(|a| canonical(&a.as_functional().to_string()))
        .collect()
}
/// The ontology IRI that Java's `getDLClauses` declares as the default prefix
/// (with `#` appended). The recorded snapshots drop the ontology header, so it
/// is recovered from the original test: a resource-based test loads the upstream
/// fixture, whose header names it; `loadOntologyWithAxioms` uses
/// `AbstractOntologyTest.ONTOLOGY_IRI`.
fn ontology_iri(java: &str) -> String {
    const ONTOLOGY_IRI: &str = "file:/c/test.owl";
    let (class, method) = java
        .strip_prefix("structural.")
        .and_then(|name| name.split_once('.'))
        .expect("structural test name");
    let upstream = Path::new(ROOT).join("upstream");
    let package = "org/semanticweb/HermiT/structural";
    let source = std::fs::read_to_string(
        upstream
            .join("java")
            .join(package)
            .join(format!("{class}.java")),
    )
    .unwrap();
    let body = &source[source
        .find(&format!("public void {method}()"))
        .expect("upstream test method")..];
    let body = &body[..body[1..].find("\n    p").map_or(body.len(), |end| end + 1)];
    let Some(resource) = regex::Regex::new(r#"assertClausification\("([^"]+)""#)
        .unwrap()
        .captures(body)
    else {
        return ONTOLOGY_IRI.into();
    };
    let fixture =
        std::fs::read_to_string(upstream.join("resources").join(package).join(&resource[1]))
            .unwrap();
    let capture = |pattern: &str| {
        regex::Regex::new(pattern)
            .unwrap()
            .captures(&fixture)
            .map(|c| c[1].to_string())
    };
    match capture(r#"<owl:Ontology\s+rdf:about="([^"]*)""#) {
        Some(about) if about.contains(':') => about,
        Some(about) if about.is_empty() => {
            capture(r#"xml:base="([^"]+)""#).expect("xml:base of the upstream fixture")
        }
        Some(about) => panic!("relative ontology IRI {about:?} in {}", &resource[1]),
        None => capture(r"Ontology\(<([^>]+)>").expect("ontology IRI of the upstream fixture"),
    }
}
pub(super) fn run(java: &str, row: &Value) {
    let o = ontology(&row["ontology"]);
    if row["op"] == "normalize" {
        let expected: HashSet<_> = row["expected"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| canonical(&axiom(v.as_str().unwrap()).as_functional().to_string()))
            .collect();
        assert_eq!(normalized(&o), expected);
        return;
    }
    let mut reasoner = r::IncrementalReasoner::new(o);
    let dl = reasoner.dl_ontology();
    let mut prefixes = hermit_rs::prefixes::Prefixes::new();
    prefixes.declare_semantic_web_prefixes();
    // As getDLClauses: one nom:/anon: prefix per namespace of the (anonymous)
    // individuals, and the ontology IRI as the default prefix. Java numbers
    // several namespaces in hash order; they are sorted here.
    let (mut named, mut anonymous) = (BTreeSet::new(), BTreeSet::new());
    for individual in dl.get_all_individuals() {
        let iri = individual.iri();
        if let Some(hash) = iri.rfind('#') {
            if !hermit_rs::prefixes::Prefixes::is_internal_iri(iri) {
                let namespaces = if individual.is_anonymous() {
                    &mut anonymous
                } else {
                    &mut named
                };
                namespaces.insert(&iri[..=hash]);
            }
        }
    }
    prefixes.declare_internal_prefixes(named, anonymous);
    prefixes
        .declare_default_prefix(&format!("{}#", ontology_iri(java)))
        .unwrap();
    let mut actual = std::collections::BTreeSet::new();
    for clause in dl.get_dl_clauses() {
        let mut head: Vec<_> = clause
            .get_head_atoms()
            .iter()
            .map(|a| a.to_string_prefixes(&prefixes))
            .collect();
        head.sort();
        let mut body: Vec<_> = clause
            .get_body_atoms()
            .iter()
            .map(|a| a.to_string_prefixes(&prefixes))
            .collect();
        body.sort();
        actual.insert(format!("{} :- {}", head.join(" v "), body.join(", ")));
    }
    for a in dl.get_positive_facts() {
        actual.insert(a.to_string_prefixes(&prefixes));
    }
    for a in dl.get_negative_facts() {
        actual.insert(format!("not {}", a.to_string_prefixes(&prefixes)));
    }
    let expected: std::collections::BTreeSet<String> = row["expected"]
        .as_array()
        .unwrap()
        .iter()
        .map(|s| s.as_str().unwrap().to_string())
        .collect();
    // The controls spell literals, enumeration order, fresh auxiliary names,
    // clause variables and role automata differently from equivalent clauses;
    // see clause_compare.rs.
    if !clause_compare::equivalent(&actual, &expected) {
        assert_eq!(actual, expected);
    }
}
