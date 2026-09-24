use hermit_rs::structural::A;
use horned_owl::{
    io::rdf::reader,
    model::{AnnotatedComponent, Build, ClassExpression, Component, Individual},
};
fn parse(uses: &str) -> (usize, bool) {
    let (count, incomplete) = parse_with_residue(uses);
    (count, incomplete.is_complete())
}
fn unused_class_expressions(uses: &str) -> usize {
    parse_with_residue(uses).1.class_expression.len()
}
fn parse_with_residue(uses: &str) -> (usize, reader::IncompleteParse<A>) {
    let rdf = format!(
        r#"<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#" xmlns:owl="http://www.w3.org/2002/07/owl#"><owl:ObjectProperty rdf:about="urn:p"/><owl:Class rdf:about="urn:C"/><owl:Restriction rdf:nodeID="restriction"><owl:onProperty rdf:resource="urn:p"/><owl:someValuesFrom rdf:resource="urn:C"/></owl:Restriction>{uses}</rdf:RDF>"#
    );
    let b: Build<A> = Build::new();
    let (o, incomplete) = reader::read::<A, AnnotatedComponent<A>, _, _>(
        &mut std::io::Cursor::new(rdf),
        horned_owl::io::ParserConfiguration::new(&b).into(),
    )
    .unwrap();
    let o: horned_owl::ontology::set::SetOntology<A> = o.into();
    let count = o
        .into_iter()
        .filter(|a| matches!(a.component, Component::SubClassOf(_)))
        .count();
    (count, incomplete)
}
#[test]
fn shared_class_expression_is_consumed_once_and_reused() {
    let uses = r#"<owl:Class rdf:about="urn:A"><rdfs:subClassOf rdf:nodeID="restriction"/></owl:Class><owl:Class rdf:about="urn:B"><rdfs:subClassOf rdf:nodeID="restriction"/></owl:Class>"#;
    assert_eq!(parse(uses), (2, true));
}
/// A class expression that no triple references is consumed when its
/// pattern is matched (OWL 2 Mapping to RDF Graphs, Section 3.2.4) and
/// yields no axiom, so the parse is complete (WebOnt I5.26-001/010, I5.5-005).
#[test]
fn standalone_class_expression_is_consumed_without_axiom() {
    assert_eq!(parse(""), (0, true));
}
/// A class expression that is referenced but never used as one (here the
/// value of an annotation) is still reported: its reference was lost.
#[test]
fn referenced_but_unused_class_expression_is_still_reported() {
    let uses = r#"<owl:Class rdf:about="urn:A"><rdfs:comment rdf:nodeID="restriction"/></owl:Class>"#;
    assert_eq!(parse(uses), (0, false));
    assert_eq!(unused_class_expressions(uses), 1);
}

/// Parse RDF/XML body content and return its logical components, asserting
/// that no triple was left unconsumed apart from the anonymous ontology header.
fn parse_components(body: &str) -> Vec<Component<A>> {
    let rdf = format!(
        r#"<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#" xmlns:owl="http://www.w3.org/2002/07/owl#" xmlns:ex="urn:ex#">{body}</rdf:RDF>"#
    );
    let b: Build<A> = Build::new();
    let (o, incomplete) = reader::read::<A, AnnotatedComponent<A>, _, _>(
        &mut std::io::Cursor::new(rdf),
        horned_owl::io::ParserConfiguration::new(&b).into(),
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
    // A blank node names one anonymous individual for the whole parse, whatever
    // the reader calls it: `_:x` in all four of its triples, `_:y` in both of
    // its, and the two apart.
    let typed_by = |class: &str| {
        c.iter()
            .find_map(|c| match c {
                Component::ClassAssertion(ca)
                    if matches!(&ca.ce, ClassExpression::Class(cls) if cls.0.as_ref() == class) =>
                {
                    Some(ca.i.clone())
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("no class assertion by {class} in\n{s}"))
    };
    let x = typed_by("urn:ex#C");
    let y = typed_by("http://www.w3.org/2002/07/owl#Thing");
    assert!(matches!(x, Individual::Anonymous(_)), "{s}");
    assert!(matches!(y, Individual::Anonymous(_)), "{s}");
    assert_ne!(x, y, "{s}");
    let has = |f: &dyn Fn(&Component<A>) -> bool| c.iter().any(f);
    assert!(
        has(&|c| matches!(c, Component::ObjectPropertyAssertion(a)
            if matches!(&a.from, Individual::Named(n) if n.0.as_ref() == "urn:ex#a") && a.to == x)),
        "a p _:x missing in\n{s}"
    );
    assert!(
        has(&|c| matches!(c, Component::ObjectPropertyAssertion(a) if a.from == x && a.to == y)),
        "_:x p _:y missing in\n{s}"
    );
    assert!(
        has(&|c| matches!(c, Component::DataPropertyAssertion(a) if a.from == x)),
        "_:x d \"1\" missing in\n{s}"
    );
}

#[test]
fn blank_node_with_non_assertion_triples_stays_unparsed() {
    // A malformed restriction (no filler) must not be read as an individual.
    let rdf = r#"<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:owl="http://www.w3.org/2002/07/owl#"><owl:ObjectProperty rdf:about="urn:ex#p"/><owl:Restriction rdf:nodeID="r"><owl:onProperty rdf:resource="urn:ex#p"/></owl:Restriction></rdf:RDF>"#;
    let b: Build<A> = Build::new();
    let (_, incomplete) = reader::read::<A, AnnotatedComponent<A>, _, _>(
        &mut std::io::Cursor::new(rdf),
        horned_owl::io::ParserConfiguration::new(&b).into(),
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

#[test]
fn untyped_enumeration_of_individuals_is_object_one_of() {
    // Lenient reading, as OWLAPI's (owl2-rl-valid-oneof): Table 13 types the
    // node owl:Class, but IRI members can only form an ObjectOneOf.
    let c = parse_components(
        r#"<owl:Class rdf:about="urn:ex#C"/>
        <rdf:Description><rdfs:subClassOf rdf:resource="urn:ex#C"/><owl:oneOf rdf:parseType="Collection"><owl:NamedIndividual rdf:about="urn:ex#x"/><owl:NamedIndividual rdf:about="urn:ex#y"/></owl:oneOf></rdf:Description>"#,
    );
    assert_eq!(
        show(&c),
        r#"SubClassOf(SubClassOf { sup: Class(Class(IRI("urn:ex#C"))), sub: ObjectOneOf([Named(NamedIndividual(IRI("urn:ex#x"))), Named(NamedIndividual(IRI("urn:ex#y")))]) })"#
    );
}

#[test]
fn untyped_enumeration_of_literals_or_nothing_stays_unparsed() {
    // A literal list would be a data range, and an empty list is ambiguous
    // between owl:Nothing and an empty data range: neither is guessed.
    for list in [r#"<rdf:first>1</rdf:first><rdf:rest rdf:resource="http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"/>"#, ""] {
        let one_of = if list.is_empty() {
            r#"<owl:oneOf rdf:resource="http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"/>"#.to_string()
        } else {
            format!(r#"<owl:oneOf><rdf:Description>{list}</rdf:Description></owl:oneOf>"#)
        };
        let rdf = format!(
            r#"<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#" xmlns:owl="http://www.w3.org/2002/07/owl#"><owl:Class rdf:about="urn:ex#C"/><rdf:Description><rdfs:subClassOf rdf:resource="urn:ex#C"/>{one_of}</rdf:Description></rdf:RDF>"#
        );
        let b: Build<A> = Build::new();
        let (_, incomplete) = reader::read::<A, AnnotatedComponent<A>, _, _>(
            &mut std::io::Cursor::new(rdf),
            horned_owl::io::ParserConfiguration::new(&b).into(),
        )
        .unwrap();
        assert!(!incomplete.is_complete(), "{one_of}");
    }
}

#[test]
fn blank_node_typed_named_individual_is_anonymous_individual() {
    // Lenient reading, as OWLAPI's (owl2-rl-anonymous-individual): Table 7
    // declares only IRIs, so the type triple is redundant and not a declaration.
    let c = parse_components(
        r#"<owl:ObjectProperty rdf:about="urn:ex#p"/><owl:NamedIndividual rdf:about="urn:ex#i"/>
        <owl:NamedIndividual><ex:p rdf:resource="urn:ex#i"/></owl:NamedIndividual>"#,
    );
    let s = show(&c);
    assert_eq!(c.len(), 1, "{s}");
    assert!(
        s.starts_with(r#"ObjectPropertyAssertion(ObjectPropertyAssertion { ope: ObjectProperty(ObjectProperty(IRI("urn:ex#p"))), from: Anonymous("#)
            && s.ends_with(r#"to: Named(NamedIndividual(IRI("urn:ex#i"))) })"#),
        "{s}"
    );
}
