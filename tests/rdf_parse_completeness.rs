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
