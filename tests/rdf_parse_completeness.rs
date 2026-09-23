use hermit_rs::structural::A;
use horned_owl::{
    io::rdf::reader,
    model::{AnnotatedComponent, Build, Component},
};
fn parse(shared: bool) -> (usize, bool) {
    let uses = if shared {
        r#"<owl:Class rdf:about="urn:A"><rdfs:subClassOf rdf:nodeID="restriction"/></owl:Class><owl:Class rdf:about="urn:B"><rdfs:subClassOf rdf:nodeID="restriction"/></owl:Class>"#
    } else {
        ""
    };
    let rdf = format!(
        r#"<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#" xmlns:owl="http://www.w3.org/2002/07/owl#"><owl:ObjectProperty rdf:about="urn:p"/><owl:Class rdf:about="urn:C"/><owl:Restriction rdf:nodeID="restriction"><owl:onProperty rdf:resource="urn:p"/><owl:someValuesFrom rdf:resource="urn:C"/></owl:Restriction>{uses}</rdf:RDF>"#
    );
    let b: Build<A> = Build::new();
    let (o, incomplete) = reader::read_with_build::<A, AnnotatedComponent<A>, _>(
        &mut std::io::Cursor::new(rdf),
        &b,
        Default::default(),
    )
    .unwrap();
    let o: horned_owl::ontology::set::SetOntology<A> = o.into();
    let count = o
        .into_iter()
        .filter(|a| matches!(a.component, Component::SubClassOf(_)))
        .count();
    (count, incomplete.is_complete())
}
#[test]
fn shared_class_expression_is_consumed_once_and_reused() {
    assert_eq!(parse(true), (2, true));
}
#[test]
fn unused_class_expression_is_still_reported() {
    assert_eq!(parse(false), (0, false));
}

/// Parse RDF/XML body content and return its logical components, asserting
/// that no triple was left unconsumed apart from the anonymous ontology header.
fn parse_components(body: &str) -> Vec<Component<A>> {
    let rdf = format!(
        r#"<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#" xmlns:owl="http://www.w3.org/2002/07/owl#" xmlns:ex="urn:ex#">{body}</rdf:RDF>"#
    );
    let b: Build<A> = Build::new();
    let (o, incomplete) = reader::read_with_build::<A, AnnotatedComponent<A>, _>(
        &mut std::io::Cursor::new(rdf),
        &b,
        Default::default(),
    )
    .unwrap();
    assert!(incomplete.is_complete(), "{incomplete:?}");
    let o: horned_owl::ontology::set::SetOntology<A> = o.into();
    o.into_iter()
        .map(|a| a.component)
        .filter(|c| !matches!(c, Component::OntologyID(_)) && !format!("{c:?}").starts_with("Declare"))
        .collect()
}

fn show(components: &[Component<A>]) -> String {
    let mut v: Vec<String> = components.iter().map(|c| format!("{c:?}")).collect();
    v.sort();
    v.join("\n")
}

#[test]
fn blank_node_individuals_are_anonymous_individuals() {
    let c = parse_components(
        r#"<owl:Class rdf:about="urn:ex#C"/><owl:ObjectProperty rdf:about="urn:ex#p"/>
        <owl:DatatypeProperty rdf:about="urn:ex#d"/>
        <rdf:Description rdf:about="urn:ex#a"><ex:p rdf:nodeID="x"/></rdf:Description>
        <ex:C rdf:nodeID="x"><ex:p rdf:nodeID="y"/><ex:d>1</ex:d></ex:C>
        <owl:Thing rdf:nodeID="y"/>"#,
    );
    let s = show(&c);
    assert_eq!(c.len(), 5, "{s}");
    for expected in [
        r#"ObjectPropertyAssertion { ope: ObjectProperty(ObjectProperty(IRI("urn:ex#p"))), from: Named(NamedIndividual(IRI("urn:ex#a"))), to: Anonymous(AnonymousIndividual("_:x")) }"#,
        r#"ClassAssertion { ce: Class(Class(IRI("urn:ex#C"))), i: Anonymous(AnonymousIndividual("_:x")) }"#,
        r#"ObjectPropertyAssertion { ope: ObjectProperty(ObjectProperty(IRI("urn:ex#p"))), from: Anonymous(AnonymousIndividual("_:x")), to: Anonymous(AnonymousIndividual("_:y")) }"#,
        r#"DataPropertyAssertion { dp: DataProperty(IRI("urn:ex#d")), from: Anonymous(AnonymousIndividual("_:x"))"#,
        r#"ClassAssertion { ce: Class(Class(IRI("http://www.w3.org/2002/07/owl#Thing"))), i: Anonymous(AnonymousIndividual("_:y")) }"#,
    ] {
        assert!(s.contains(expected), "missing {expected} in\n{s}");
    }
}

#[test]
fn blank_node_with_non_assertion_triples_stays_unparsed() {
    // A malformed restriction (no filler) must not be read as an individual.
    let rdf = r#"<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:owl="http://www.w3.org/2002/07/owl#"><owl:ObjectProperty rdf:about="urn:ex#p"/><owl:Restriction rdf:nodeID="r"><owl:onProperty rdf:resource="urn:ex#p"/></owl:Restriction></rdf:RDF>"#;
    let b: Build<A> = Build::new();
    let (_, incomplete) = reader::read_with_build::<A, AnnotatedComponent<A>, _>(
        &mut std::io::Cursor::new(rdf),
        &b,
        Default::default(),
    )
    .unwrap();
    assert!(!incomplete.is_complete());
}

#[test]
fn owl1_named_class_connectives_are_equivalences() {
    // OWL 2 Mapping to RDF Graphs, Table 18.
    let c = parse_components(
        r#"<owl:Class rdf:about="urn:ex#A"/><owl:Class rdf:about="urn:ex#B"/>
        <owl:Class rdf:about="urn:ex#AB"><owl:intersectionOf rdf:parseType="Collection"><owl:Class rdf:about="urn:ex#A"/><owl:Class rdf:about="urn:ex#B"/></owl:intersectionOf></owl:Class>
        <owl:Class rdf:about="urn:ex#AorB"><owl:unionOf rdf:parseType="Collection"><owl:Class rdf:about="urn:ex#A"/></owl:unionOf></owl:Class>
        <owl:Class rdf:about="urn:ex#Top"><owl:intersectionOf rdf:parseType="Collection"/></owl:Class>
        <owl:Class rdf:about="urn:ex#NotA"><owl:complementOf rdf:resource="urn:ex#A"/></owl:Class>
        <owl:Class rdf:about="urn:ex#I"><owl:oneOf rdf:parseType="Collection"><owl:Thing rdf:about="urn:ex#i"/></owl:oneOf></owl:Class>"#,
    );
    let s = show(&c);
    for expected in [
        r#"EquivalentClasses([Class(Class(IRI("urn:ex#AB"))), ObjectIntersectionOf([Class(Class(IRI("urn:ex#A"))), Class(Class(IRI("urn:ex#B")))])])"#,
        r#"EquivalentClasses([Class(Class(IRI("urn:ex#AorB"))), Class(Class(IRI("urn:ex#A")))])"#,
        r#"EquivalentClasses([Class(Class(IRI("urn:ex#Top"))), Class(Class(IRI("http://www.w3.org/2002/07/owl#Thing")))])"#,
        r#"EquivalentClasses([Class(Class(IRI("urn:ex#NotA"))), ObjectComplementOf(Class(Class(IRI("urn:ex#A"))))])"#,
        r#"EquivalentClasses([Class(Class(IRI("urn:ex#I"))), ObjectOneOf([Named(NamedIndividual(IRI("urn:ex#i")))])])"#,
    ] {
        assert!(s.contains(expected), "missing {expected} in\n{s}");
    }
}

#[test]
fn owl1_compatibility_vocabulary_is_parsed() {
    // Tables 5, 6 and 14: redundant rdfs:Class types, implied object-property
    // declarations and owl:DataRange enumerations; plus an unqualified
    // cardinality on a data property.
    let c = parse_components(
        r#"<owl:Class rdf:about="urn:ex#A"><rdf:type rdf:resource="http://www.w3.org/2000/01/rdf-schema#Class"/></owl:Class>
        <owl:SymmetricProperty rdf:about="urn:ex#s"><rdfs:range rdf:resource="urn:ex#A"/></owl:SymmetricProperty>
        <owl:DatatypeProperty rdf:about="urn:ex#d"><rdfs:range><owl:DataRange><owl:oneOf rdf:parseType="Collection"/></owl:DataRange></rdfs:range></owl:DatatypeProperty>
        <owl:Thing rdf:about="urn:ex#i"><rdf:type><owl:Restriction><rdf:type rdf:resource="http://www.w3.org/2000/01/rdf-schema#Class"/><owl:onProperty rdf:resource="urn:ex#d"/><owl:maxCardinality rdf:datatype="http://www.w3.org/2001/XMLSchema#nonNegativeInteger">1</owl:maxCardinality></owl:Restriction></rdf:type></owl:Thing>"#,
    );
    let s = show(&c);
    for expected in [
        r#"ObjectPropertyRange(ObjectPropertyRange { ope: ObjectProperty(ObjectProperty(IRI("urn:ex#s"))), ce: Class(Class(IRI("urn:ex#A"))) })"#,
        r#"SymmetricObjectProperty"#,
        r#"DataPropertyRange(DataPropertyRange { dp: DataProperty(IRI("urn:ex#d")), dr: DataComplementOf(Datatype(Datatype(IRI("http://www.w3.org/2000/01/rdf-schema#Literal")))) })"#,
        r#"DataMaxCardinality { n: 1, dp: DataProperty(IRI("urn:ex#d"))"#,
    ] {
        assert!(s.contains(expected), "missing {expected} in\n{s}");
    }
    assert!(!s.contains("rdf-schema#Class"), "{s}");
}
