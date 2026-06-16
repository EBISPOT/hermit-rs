// End-to-end smoke tests for the DL-safe datalog query engine (`DatalogEngine`
// / `ConjunctiveQuery`). The engine has no Java-side unit tests; these exercise
// the ABox-loading and Horn-saturation paths that the audit touched (lazy node
// creation, anonymous-constant handling, the full doIteration saturation loop).

use horned_owl::model::{
    Build, Class, ClassExpression as CE, Component, Individual, MutableOntology, NamedIndividual,
    ObjectProperty, ObjectPropertyAssertion, ObjectPropertyExpression as OPE, SubClassOf,
    SubObjectPropertyOf, ClassAssertion, SubObjectPropertyExpression as SOPE,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::datalog::{ConjunctiveQuery, DatalogEngine, QueryAtom, QueryTerm};

type Ae = hermit_rs::structural::A;

fn cls(b: &Build<std::sync::Arc<str>>, n: &str) -> Class<Ae> {
    b.class(format!("http://example.org/{n}"))
}
fn op(b: &Build<std::sync::Arc<str>>, n: &str) -> ObjectProperty<Ae> {
    b.object_property(format!("http://example.org/{n}"))
}
fn ind(b: &Build<std::sync::Arc<str>>, n: &str) -> NamedIndividual<Ae> {
    b.named_individual(format!("http://example.org/{n}"))
}

#[test]
fn concept_inclusion_materializes_for_query() {
    // A(a), A ⊑ B  ⊨  B(a). The Horn saturation must derive B(a).
    let b = Build::new_arc();
    let mut o: SetOntology<Ae> = SetOntology::new();
    let a_class = cls(&b, "A");
    let b_class = cls(&b, "B");
    o.insert(Component::SubClassOf(SubClassOf {
        sup: CE::Class(b_class.clone()),
        sub: CE::Class(a_class.clone()),
    }));
    o.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::Class(a_class),
        i: Individual::Named(ind(&b, "a")),
    }));

    let engine = DatalogEngine::new(&o).expect("engine");
    // Query B(?x): a is the only answer.
    let query = ConjunctiveQuery::new(
        vec![QueryAtom::Concept(
            CE::Class(b_class),
            QueryTerm::Variable("x".to_string()),
        )],
        vec![QueryTerm::Variable("x".to_string())],
    );
    let mut answers: Vec<Vec<String>> = Vec::new();
    query.evaluate(&engine, &mut answers).expect("evaluate");
    assert_eq!(answers, vec![vec!["http://example.org/a".to_string()]]);
}

#[test]
fn role_inclusion_materializes_for_query() {
    // r(a,b), r ⊑ s  ⊨  s(a,b).
    let b = Build::new_arc();
    let mut o: SetOntology<Ae> = SetOntology::new();
    let r = op(&b, "r");
    let s = op(&b, "s");
    o.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sup: OPE::ObjectProperty(s.clone()),
        sub: SOPE::ObjectPropertyExpression(OPE::ObjectProperty(r.clone())),
    }));
    o.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: OPE::ObjectProperty(r),
        from: Individual::Named(ind(&b, "a")),
        to: Individual::Named(ind(&b, "b")),
    }));

    let engine = DatalogEngine::new(&o).expect("engine");
    // Query s(a, ?y): b is the only answer.
    let query = ConjunctiveQuery::new(
        vec![QueryAtom::Role(
            OPE::ObjectProperty(s),
            QueryTerm::Individual("http://example.org/a".to_string()),
            QueryTerm::Variable("y".to_string()),
        )],
        vec![QueryTerm::Variable("y".to_string())],
    );
    let mut answers: Vec<Vec<String>> = Vec::new();
    query.evaluate(&engine, &mut answers).expect("evaluate");
    assert_eq!(answers, vec![vec!["http://example.org/b".to_string()]]);
}
