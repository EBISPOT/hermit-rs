// Transitivity expressed as an explicit inverse-property chain
// (`Inv(r) o Inv(r) ⊑ Inv(r)`) must drive `∀r.C` propagation along `r` just like
// `TransitiveObjectProperty(r)` does: the role-box automaton handles both
// orientations.

use horned_owl::model::{
    Build, ClassAssertion, ClassExpression as CE, Component, Individual, InverseObjectProperties,
    MutableOntology, ObjectPropertyAssertion, ObjectPropertyExpression as OPE,
    SubObjectPropertyExpression as SOPE, SubObjectPropertyOf, SubClassOf, TransitiveObjectProperty,
};
use horned_owl::ontology::set::SetOntology;
use hermit_rs::reasoner::is_ontology_consistent;

#[test]
fn transitivity_via_explicit_inverse_chain_propagates_all_values() {
    let build = Build::new_arc();
    let r = build.object_property("http://example.org/r");
    let inv_r = OPE::InverseObjectProperty(r.clone());
    let r_e = OPE::ObjectProperty(r.clone());
    let c = CE::Class(build.class("http://example.org/C"));
    let x = CE::Class(build.class("http://example.org/X"));
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");
    let cc = build.named_individual("http://example.org/c");

    let mut onto: SetOntology<_> = SetOntology::new();
    // Inv(r) o Inv(r) ⊑ Inv(r)  ==> Inv(r) (hence r) is transitive.
    onto.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SOPE::ObjectPropertyChain(vec![inv_r.clone(), inv_r.clone()]),
        sup: inv_r.clone(),
    }));
    // X ⊑ ∀r.C
    onto.insert(Component::SubClassOf(SubClassOf {
        sub: x.clone(),
        sup: CE::ObjectAllValuesFrom { ope: r_e.clone(), bce: Box::new(c.clone()) },
    }));
    onto.insert(Component::ClassAssertion(ClassAssertion { ce: x, i: Individual::Named(a.clone()) }));
    onto.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: r_e.clone(),
        from: Individual::Named(a.clone()),
        to: Individual::Named(b.clone()),
    }));
    onto.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: r_e.clone(),
        from: Individual::Named(b.clone()),
        to: Individual::Named(cc.clone()),
    }));
    // ¬C(c)
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectComplementOf(Box::new(c)),
        i: Individual::Named(cc),
    }));

    // r transitive + a:∀r.C + a r b r c forces c:C, clashing with ¬C(c).
    let consistent = is_ontology_consistent(&onto).unwrap();
    assert!(!consistent, "expected INCONSISTENT (c:C forced via transitive ∀r.C)");

    // Control: WITHOUT the transitivity chain axiom, c:C is not forced -> consistent.
    let mut onto2: SetOntology<_> = SetOntology::new();
    onto2.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(build.class("http://example.org/X")),
        sup: CE::ObjectAllValuesFrom { ope: r_e.clone(), bce: Box::new(CE::Class(build.class("http://example.org/C"))) },
    }));
    onto2.insert(Component::ClassAssertion(ClassAssertion { ce: CE::Class(build.class("http://example.org/X")), i: Individual::Named(a.clone()) }));
    onto2.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion { ope: r_e.clone(), from: Individual::Named(a.clone()), to: Individual::Named(b.clone()) }));
    onto2.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion { ope: r_e.clone(), from: Individual::Named(b.clone()), to: Individual::Named(build.named_individual("http://example.org/c")) }));
    onto2.insert(Component::ClassAssertion(ClassAssertion { ce: CE::ObjectComplementOf(Box::new(CE::Class(build.class("http://example.org/C")))), i: Individual::Named(build.named_individual("http://example.org/c")) }));
    assert!(is_ontology_consistent(&onto2).unwrap(), "control: expected CONSISTENT without transitivity");
}

// A *non-transitive* chain inclusion whose SUPER property is an inverse
// (anonymous), `s1 o s2 ⊑ Inv(r)`, must be handled by keying the automaton on
// the anonymous super `Inv(r)` exactly as Java does. Semantically
// `s1(a,b) ∧ s2(b,c) → Inv(r)(a,c) ≡ r(c,a)`, so with `X ⊑ ∀r.C` and `X(c)`
// the value `C` propagates to `a`.
#[test]
fn inverse_super_chain_propagates_all_values() {
    let build = Build::new_arc();
    let r = build.object_property("http://example.org/r");
    let s1 = build.object_property("http://example.org/s1");
    let s2 = build.object_property("http://example.org/s2");
    let inv_r = OPE::InverseObjectProperty(r.clone());
    let r_e = OPE::ObjectProperty(r.clone());
    let s1_e = OPE::ObjectProperty(s1.clone());
    let s2_e = OPE::ObjectProperty(s2.clone());
    let c = CE::Class(build.class("http://example.org/C"));
    let x = CE::Class(build.class("http://example.org/X"));
    let a = build.named_individual("http://example.org/a");
    let b = build.named_individual("http://example.org/b");
    let cc = build.named_individual("http://example.org/c");

    let mut onto: SetOntology<_> = SetOntology::new();
    // s1 o s2 ⊑ Inv(r)  (super property is anonymous)
    onto.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
        sub: SOPE::ObjectPropertyChain(vec![s1_e.clone(), s2_e.clone()]),
        sup: inv_r.clone(),
    }));
    // X ⊑ ∀r.C
    onto.insert(Component::SubClassOf(SubClassOf {
        sub: x.clone(),
        sup: CE::ObjectAllValuesFrom { ope: r_e.clone(), bce: Box::new(c.clone()) },
    }));
    // X(c)
    onto.insert(Component::ClassAssertion(ClassAssertion { ce: x, i: Individual::Named(cc.clone()) }));
    // s1(a,b), s2(b,c)  ==> Inv(r)(a,c) ==> r(c,a) ==> C(a)
    onto.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: s1_e.clone(),
        from: Individual::Named(a.clone()),
        to: Individual::Named(b.clone()),
    }));
    onto.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
        ope: s2_e.clone(),
        from: Individual::Named(b.clone()),
        to: Individual::Named(cc.clone()),
    }));
    // ¬C(a)
    onto.insert(Component::ClassAssertion(ClassAssertion {
        ce: CE::ObjectComplementOf(Box::new(c.clone())),
        i: Individual::Named(a.clone()),
    }));

    let consistent = is_ontology_consistent(&onto).unwrap();
    assert!(!consistent, "expected INCONSISTENT (C(a) forced via s1 o s2 ⊑ Inv(r) and ∀r.C)");

    // Control: drop the chain axiom -> C(a) not forced -> consistent.
    let mut onto2: SetOntology<_> = SetOntology::new();
    onto2.insert(Component::SubClassOf(SubClassOf {
        sub: CE::Class(build.class("http://example.org/X")),
        sup: CE::ObjectAllValuesFrom { ope: r_e.clone(), bce: Box::new(c.clone()) },
    }));
    onto2.insert(Component::ClassAssertion(ClassAssertion { ce: CE::Class(build.class("http://example.org/X")), i: Individual::Named(cc.clone()) }));
    onto2.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion { ope: s1_e, from: Individual::Named(a.clone()), to: Individual::Named(b.clone()) }));
    onto2.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion { ope: s2_e, from: Individual::Named(b), to: Individual::Named(cc) }));
    onto2.insert(Component::ClassAssertion(ClassAssertion { ce: CE::ObjectComplementOf(Box::new(c)), i: Individual::Named(a) }));
    assert!(is_ontology_consistent(&onto2).unwrap(), "control: expected CONSISTENT without the inverse-super chain");
}

// A property `u` with a chain-bearing complex sub-property (`a ⊑ u`, `a ∘ b ⊑ a`,
// `b` transitive) AND a declared inverse (`InverseObjectProperties(u, ui)`). The
// forward sub-chain `a ∘ b*` must remain in u's automaton even though u also has an
// inverse representation; otherwise `∀u.C` under-propagates and entailments are
// missed. This is the minimal form of the EFO `MONDO_* ⊑ EFO_0000524` pattern (see
// tests/data/role_automaton/ and ROLE_AUTOMATON_CONSTRUCTION.md).
//
// With `m : ∃a.Y1`, `Y1 ⊑ ∃b.Y2`, `Y2 ⊑ ∃b.Z` and `m : ∀u.¬Z`, the chain lifts the
// two `b` steps onto `a ⊑ u`, forcing a u-successor in `Z` that clashes with
// `∀u.¬Z` ⇒ INCONSISTENT. (Before the completeness fix u lost `a ∘ b*`, the value
// did not propagate, and this came out consistent.)
#[test]
fn forward_sub_chain_survives_declared_inverse() {
    let build = Build::new_arc();
    let u = build.object_property("http://example.org/u");
    let ui = build.object_property("http://example.org/ui");
    let a = build.object_property("http://example.org/a");
    let b = build.object_property("http://example.org/b");
    let u_e = OPE::ObjectProperty(u.clone());
    let a_e = OPE::ObjectProperty(a.clone());
    let b_e = OPE::ObjectProperty(b.clone());
    let y1 = CE::Class(build.class("http://example.org/Y1"));
    let y2 = CE::Class(build.class("http://example.org/Y2"));
    let z = CE::Class(build.class("http://example.org/Z"));
    let m = build.named_individual("http://example.org/m");

    let role_box = |onto: &mut SetOntology<_>, with_chain: bool| {
        // a ⊑ u
        onto.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
            sub: SOPE::ObjectPropertyExpression(a_e.clone()),
            sup: u_e.clone(),
        }));
        // b transitive
        onto.insert(Component::TransitiveObjectProperty(TransitiveObjectProperty(b_e.clone())));
        // u has a declared inverse ui (the trigger that previously lost u's sub-chain)
        onto.insert(Component::InverseObjectProperties(InverseObjectProperties(
            u_e.clone(),
            OPE::ObjectProperty(ui.clone()),
        )));
        if with_chain {
            // a ∘ b ⊑ a
            onto.insert(Component::SubObjectPropertyOf(SubObjectPropertyOf {
                sub: SOPE::ObjectPropertyChain(vec![a_e.clone(), b_e.clone()]),
                sup: a_e.clone(),
            }));
        }
        // Y1 ⊑ ∃b.Y2 ; Y2 ⊑ ∃b.Z
        onto.insert(Component::SubClassOf(SubClassOf {
            sub: y1.clone(),
            sup: CE::ObjectSomeValuesFrom { ope: b_e.clone(), bce: Box::new(y2.clone()) },
        }));
        onto.insert(Component::SubClassOf(SubClassOf {
            sub: y2.clone(),
            sup: CE::ObjectSomeValuesFrom { ope: b_e.clone(), bce: Box::new(z.clone()) },
        }));
        // m : ∃a.Y1
        onto.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::ObjectSomeValuesFrom { ope: a_e.clone(), bce: Box::new(y1.clone()) },
            i: Individual::Named(m.clone()),
        }));
        // m : ∀u.¬Z
        onto.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::ObjectAllValuesFrom {
                ope: u_e.clone(),
                bce: Box::new(CE::ObjectComplementOf(Box::new(z.clone()))),
            },
            i: Individual::Named(m.clone()),
        }));
    };

    let mut onto: SetOntology<_> = SetOntology::new();
    role_box(&mut onto, true);
    assert!(
        !is_ontology_consistent(&onto).unwrap(),
        "expected INCONSISTENT: a∘b⊑a⊑u lifts m's part-of chain onto u, forcing a \
         u-successor in Z that clashes with ∀u.¬Z (regression: u must keep a∘b* even \
         with a declared inverse)"
    );

    // Control: without the `a ∘ b ⊑ a` chain, m's only u-successor is in Y1, not Z.
    let mut control: SetOntology<_> = SetOntology::new();
    role_box(&mut control, false);
    assert!(
        is_ontology_consistent(&control).unwrap(),
        "control: expected CONSISTENT without the a∘b⊑a chain"
    );
}
