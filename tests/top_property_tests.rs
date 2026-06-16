// Regression tests for the unsound handling of universal restrictions over
// owl:topObjectProperty. `owl:topObjectProperty` is the universal object
// property -- every pair (x,y) is related -- so `∀owl:topObjectProperty.C` on
// any individual forces C on EVERYTHING. These ontologies are unsatisfiable and
// must be reported `Consistent: false`.

use horned_owl::model::{
    Build, ClassAssertion, ClassExpression as CE, Component, Individual, MutableOntology,
    ObjectPropertyAssertion, ObjectPropertyExpression,
};
use horned_owl::ontology::set::SetOntology;

use hermit_rs::reasoner::is_ontology_consistent;

const TOP_OBJECT_PROPERTY: &str = "http://www.w3.org/2002/07/owl#topObjectProperty";

fn top_op(build: &Build<hermit_rs::structural::A>) -> ObjectPropertyExpression<hermit_rs::structural::A> {
    ObjectPropertyExpression::ObjectProperty(build.object_property(TOP_OBJECT_PROPERTY))
}

fn all_top_c(
    build: &Build<hermit_rs::structural::A>,
    c: &CE<hermit_rs::structural::A>,
) -> CE<hermit_rs::structural::A> {
    CE::ObjectAllValuesFrom {
        ope: top_op(build),
        bce: Box::new(c.clone()),
    }
}

// Reproducer 1: ∀top.C(a) ⊓ ¬C(a). top is symmetric+transitive and `a`
// top-relates to itself (a -> topIndividual -> a), so C(a) and ¬C(a) clash.
#[test]
fn all_top_c_and_not_c_on_same_individual_is_inconsistent() {
    let build = Build::new_arc();
    let c = CE::Class(build.class("http://example.org/C"));
    let a = build.named_individual("http://example.org/a");

    let mut onto: SetOntology<_> = SetOntology::new();
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectIntersectionOf(vec![
            all_top_c(&build, &c),
            CE::ObjectComplementOf(Box::new(c.clone())),
        ]),
        i: Individual::Named(a),
    }));

    assert!(!is_ontology_consistent(&onto).unwrap());
}

// Reproducer 2: ∀top.C(a) forces C on all individuals, clashing with ¬C(c).
#[test]
fn all_top_c_forces_c_on_other_individual_is_inconsistent() {
    let build = Build::new_arc();
    let c = CE::Class(build.class("http://example.org/C"));
    let a = build.named_individual("http://example.org/a");
    let c_ind = build.named_individual("http://example.org/c");

    let mut onto: SetOntology<_> = SetOntology::new();
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: all_top_c(&build, &c),
        i: Individual::Named(a),
    }));
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectComplementOf(Box::new(c.clone())),
        i: Individual::Named(c_ind),
    }));

    assert!(!is_ontology_consistent(&onto).unwrap());
}

// Reproducer 3: ∀top.C(a), r(a,b), ¬C(b). b is top-related to a (and to all),
// so C(b) is forced, clashing with ¬C(b).
#[test]
fn all_top_c_with_explicit_edge_is_inconsistent() {
    let build = Build::new_arc();
    let c = CE::Class(build.class("http://example.org/C"));
    let r = build.object_property("http://example.org/r");
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");

    let mut onto: SetOntology<_> = SetOntology::new();
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: all_top_c(&build, &c),
        i: Individual::Named(a.clone()),
    }));
    onto.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: ObjectPropertyExpression::ObjectProperty(r),
        from: Individual::Named(a),
        to: Individual::Named(b.clone()),
    }));
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectComplementOf(Box::new(c.clone())),
        i: Individual::Named(b),
    }));

    assert!(!is_ontology_consistent(&onto).unwrap());
}

// Contrast 1 (must stay consistent): ∀top.C(a) with C satisfiable and nothing
// forcing ¬C anywhere. Everything is C, which is fine.
#[test]
fn all_top_c_alone_is_consistent() {
    let build = Build::new_arc();
    let c = CE::Class(build.class("http://example.org/C"));
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");

    let mut onto: SetOntology<_> = SetOntology::new();
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: all_top_c(&build, &c),
        i: Individual::Named(a),
    }));
    // A second, unrelated individual that is freely allowed to be C.
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: c.clone(),
        i: Individual::Named(b),
    }));

    assert!(is_ontology_consistent(&onto).unwrap());
}

// Contrast 2 (known-good, must keep working): ∀ over an explicit
// transitive+symmetric role propagates correctly.
#[test]
fn all_explicit_transitive_symmetric_role_propagates() {
    use horned_owl::model::{
        SymmetricObjectProperty, TransitiveObjectProperty,
    };
    let build = Build::new_arc();
    let c = CE::Class(build.class("http://example.org/C"));
    let r = build.object_property("http://example.org/r");
    let rope = ObjectPropertyExpression::ObjectProperty(r.clone());
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");

    // TransitiveObjectProperty(r), SymmetricObjectProperty(r),
    // ∀r.C(a), r(a,b), ¬C(b) -> b is r-related to a (symmetry), C(b) forced,
    // clashing with ¬C(b).
    let mut onto: SetOntology<_> = SetOntology::new();
    onto.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(
        rope.clone(),
    )));
    onto.insert(Component::SymmetricObjectProperty(SymmetricObjectProperty(
        rope.clone(),
    )));
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectAllValuesFrom {
            ope: rope.clone(),
            bce: Box::new(c.clone()),
        },
        i: Individual::Named(a.clone()),
    }));
    onto.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: rope,
        from: Individual::Named(a),
        to: Individual::Named(b.clone()),
    }));
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectComplementOf(Box::new(c)),
        i: Individual::Named(b),
    }));

    assert!(!is_ontology_consistent(&onto).unwrap());
}
