// Issue #94: with nominals in the TBox the ABox takes part in every class test.
// The reasoner saturates it once per test tableau and starts each test from that
// checkpoint. A clash that depends on one of the ABox's own disjunction choices
// is not answered from the checkpoint: the test runs again on a fresh ABox.
// These tests pin the answers on both paths.

use hermit_rs::hierarchy::Hierarchy;
use hermit_rs::reasoner::classify;
use hermit_rs::structural::A;
use horned_owl::model::{Build, Class};
use horned_owl::ontology::set::SetOntology;

fn parse(s: &str) -> SetOntology<A> {
    horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(s), Default::default())
        .unwrap()
        .0
}

fn node(hierarchy: &Hierarchy<Class<A>>, iri: &str) -> usize {
    hierarchy
        .node_for_element(&Build::new_arc().class(iri))
        .unwrap_or_else(|| panic!("{iri} is not in the hierarchy"))
}

fn is_unsatisfiable(hierarchy: &Hierarchy<Class<A>>, iri: &str) -> bool {
    node(hierarchy, iri) == hierarchy.bottom_node()
}

fn is_subsumed(hierarchy: &Hierarchy<Class<A>>, sub: &str, sup: &str) -> bool {
    hierarchy
        .ancestor_nodes(node(hierarchy, sub))
        .contains(&node(hierarchy, sup))
}

/// `a` is asserted to be `C` or `D`. Whichever the ABox saturation picks, one of
/// `NeedsNotC` and `NeedsNotD` clashes with that choice on its first run and is
/// answered on a fresh ABox, while the other is answered from the checkpoint.
/// Both are satisfiable; `NeedsNeither` is not, under any choice.
const ABOX_CHOICE: &str = r#"Prefix(:=<http://ex/>)
Ontology(
Declaration(Class(:C)) Declaration(Class(:D)) Declaration(Class(:Sup))
Declaration(Class(:NeedsNotC)) Declaration(Class(:NeedsNotD)) Declaration(Class(:NeedsNeither))
Declaration(ObjectProperty(:r)) Declaration(NamedIndividual(:a))
ClassAssertion(ObjectUnionOf(:C :D) :a)
SubClassOf(:NeedsNotC ObjectIntersectionOf(:Sup ObjectHasValue(:r :a) ObjectAllValuesFrom(:r ObjectComplementOf(:C))))
SubClassOf(:NeedsNotD ObjectIntersectionOf(:Sup ObjectHasValue(:r :a) ObjectAllValuesFrom(:r ObjectComplementOf(:D))))
SubClassOf(:NeedsNeither ObjectIntersectionOf(ObjectHasValue(:r :a) ObjectAllValuesFrom(:r ObjectComplementOf(:C)) ObjectAllValuesFrom(:r ObjectComplementOf(:D))))
)"#;

#[test]
fn a_test_that_clashes_with_an_abox_choice_is_answered_on_a_fresh_abox() {
    let hierarchy = classify(&parse(ABOX_CHOICE)).unwrap();
    assert!(!is_unsatisfiable(&hierarchy, "http://ex/NeedsNotC"));
    assert!(!is_unsatisfiable(&hierarchy, "http://ex/NeedsNotD"));
    assert!(is_unsatisfiable(&hierarchy, "http://ex/NeedsNeither"));
    assert!(is_subsumed(&hierarchy, "http://ex/NeedsNotC", "http://ex/Sup"));
    assert!(is_subsumed(&hierarchy, "http://ex/NeedsNotD", "http://ex/Sup"));
    assert!(!is_subsumed(&hierarchy, "http://ex/NeedsNotC", "http://ex/NeedsNotD"));
    assert!(!is_subsumed(&hierarchy, "http://ex/Sup", "http://ex/NeedsNotC"));
}

/// The shape of the issue: individuals typed with existential restrictions, a
/// nominal in the TBox that loads them into every test, and defined classes
/// whose classification must come out the same as without the ABox.
fn cohorts(with_nominal: bool) -> String {
    let mut text = String::from(
        r#"Prefix(:=<http://ex/>)
Ontology(
Declaration(Class(:Disease)) Declaration(Class(:Flu)) Declaration(Class(:Measles))
Declaration(Class(:Cohort)) Declaration(Class(:FluCohort)) Declaration(Class(:DiseaseCohort))
Declaration(ObjectProperty(:studies))
SubClassOf(:Flu :Disease) SubClassOf(:Measles :Disease)
EquivalentClasses(:FluCohort ObjectIntersectionOf(:Cohort ObjectSomeValuesFrom(:studies :Flu)))
EquivalentClasses(:DiseaseCohort ObjectIntersectionOf(:Cohort ObjectSomeValuesFrom(:studies :Disease)))
"#,
    );
    if with_nominal {
        text.push_str(
            "Declaration(Class(:Status)) Declaration(NamedIndividual(:s)) EquivalentClasses(:Status ObjectOneOf(:s))\n",
        );
    }
    for i in 0..20 {
        let disease = if i % 2 == 0 { ":Flu" } else { ":Measles" };
        text.push_str(&format!(
            "Declaration(NamedIndividual(:c{i})) ClassAssertion(:Cohort :c{i}) ClassAssertion(ObjectSomeValuesFrom(:studies {disease}) :c{i})\n"
        ));
    }
    text.push(')');
    text
}

#[test]
fn the_kept_abox_does_not_change_the_class_hierarchy() {
    for with_nominal in [false, true] {
        let hierarchy = classify(&parse(&cohorts(with_nominal))).unwrap();
        assert!(is_subsumed(&hierarchy, "http://ex/FluCohort", "http://ex/DiseaseCohort"));
        assert!(is_subsumed(&hierarchy, "http://ex/FluCohort", "http://ex/Cohort"));
        assert!(is_subsumed(&hierarchy, "http://ex/DiseaseCohort", "http://ex/Cohort"));
        assert!(!is_subsumed(&hierarchy, "http://ex/DiseaseCohort", "http://ex/FluCohort"));
        assert!(!is_subsumed(&hierarchy, "http://ex/Cohort", "http://ex/DiseaseCohort"));
        assert!(is_subsumed(&hierarchy, "http://ex/Flu", "http://ex/Disease"));
        assert!(!is_subsumed(&hierarchy, "http://ex/Flu", "http://ex/Measles"));
        for class in ["FluCohort", "DiseaseCohort", "Cohort", "Flu", "Measles", "Disease"] {
            assert!(!is_unsatisfiable(&hierarchy, &format!("http://ex/{class}")), "{class}");
        }
    }
}
