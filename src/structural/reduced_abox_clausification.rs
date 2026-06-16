// Port of org.semanticweb.HermiT.structural.ReducedABoxOnlyclausification.
//
// Clausifies only the ABox (the individual axioms) into `model` facts, given an
// already-clausified TBox -- the incremental path HermiT uses when the TBox is
// fixed and only assertions change (instance retrieval / realisation). It is the
// ABox-only specialization of the full clausifier: class assertions over named
// (or negated named) classes, object/data-property assertions and their
// negations, and same/different-individual axioms become positive/negative
// facts.

use std::collections::HashSet;

use horned_owl::model::{
    ClassExpression as CE, Component, Individual as OwlIndividual, ObjectPropertyExpression as OPE,
};
use horned_owl::ontology::set::SetOntology;

use crate::model::{Atom, AtomicConcept, AtomicRole, DLPredicate, Individual, Term};
use crate::structural::A;

/// The ABox-only clausification result.
#[derive(Default)]
pub struct ReducedABoxClausification {
    pub positive_facts: HashSet<Atom>,
    pub negative_facts: HashSet<Atom>,
    pub individuals: HashSet<Individual>,
}

fn individual(i: &OwlIndividual<A>) -> Individual {
    match i {
        OwlIndividual::Named(n) => Individual::create(n.0.to_string()),
        OwlIndividual::Anonymous(a) => Individual::create_anonymous(&a.0.to_string()),
    }
}

fn role(ope: &OPE<A>) -> AtomicRole {
    match ope {
        OPE::ObjectProperty(p) => AtomicRole::create(p.0.to_string()),
        // Inv(r)(a,b) is the fact r(b,a); handled by the caller swapping.
        OPE::InverseObjectProperty(p) => AtomicRole::create(p.0.to_string()),
    }
}

/// The vocabulary (atomic concepts and roles) already loaded for the fixed
/// TBox. Mirrors `ReducedABoxOnlyClausification`'s `m_allAtomicConcepts`,
/// `m_allAtomicObjectRoles` and `m_allAtomicDataRoles`: the reduced/incremental
/// ABox path only accepts assertions whose predicates already exist, since
/// introducing fresh classes/roles is not compatible with incremental loading.
#[derive(Default)]
pub struct Vocabulary {
    pub atomic_concepts: HashSet<AtomicConcept>,
    pub atomic_object_roles: HashSet<AtomicRole>,
    pub atomic_data_roles: HashSet<AtomicRole>,
}

impl ReducedABoxClausification {
    /// Clausifies the ABox of `ontology` (its individual axioms), returning the
    /// facts and the individuals they mention. Complex class assertions (those
    /// not over a named class, HasSelf, HasValue, or their negations) are
    /// rejected, as the reduced path assumes a pre-normalized ABox.
    ///
    /// `vocabulary` carries the atomic concepts/roles of the fixed TBox; any
    /// assertion mentioning a predicate outside it is rejected, mirroring the
    /// `IllegalArgumentException` thrown by Java `getConceptAtom`/`getRoleAtom`
    /// ("fresh classes/properties are not compatible with incremental ABox
    /// loading").
    pub fn clausify(
        ontology: &SetOntology<A>,
        vocabulary: &Vocabulary,
        ignore_unsupported_datatypes: bool,
    ) -> Result<ReducedABoxClausification, String> {
        let mut result = ReducedABoxClausification::default();
        for annotated in ontology.iter() {
            result.visit(&annotated.component, vocabulary, ignore_unsupported_datatypes)?;
        }
        Ok(result)
    }

    fn note(&mut self, individual: Individual) {
        self.individuals.insert(individual);
    }

    /// Port of `getConceptAtom`: builds the concept atom, rejecting classes that
    /// are not part of the loaded vocabulary.
    fn concept_atom(
        vocabulary: &Vocabulary,
        iri: String,
        term: Term,
    ) -> Result<Atom, String> {
        let atomic_concept = AtomicConcept::create(iri);
        if vocabulary.atomic_concepts.contains(&atomic_concept) {
            Ok(Atom::create(
                DLPredicate::AtomicConcept(atomic_concept),
                vec![term],
            ))
        } else {
            Err("Internal error: fresh classes in class assertions are not compatible \
                 with incremental ABox loading!"
                .into())
        }
    }

    /// Port of `getRoleAtom(OWLObjectPropertyExpression,...)`: builds the role
    /// atom (swapping arguments for inverse/anonymous properties, as `order`
    /// does) and rejects object roles outside the loaded vocabulary.
    fn object_role_atom(
        vocabulary: &Vocabulary,
        ope: &OPE<A>,
        first: Individual,
        second: Individual,
    ) -> Result<Atom, String> {
        let atomic_role = role(ope);
        if vocabulary.atomic_object_roles.contains(&atomic_role) {
            let (from, to) = order(ope, first, second);
            Ok(Atom::create(
                DLPredicate::AtomicRole(atomic_role),
                vec![Term::Individual(from), Term::Individual(to)],
            ))
        } else {
            Err("Internal error: fresh properties in property assertions are not \
                 compatible with incremental ABox loading!"
                .into())
        }
    }

    /// Port of `getRoleAtom(OWLDataPropertyExpression,...)`: rejects data roles
    /// outside the loaded vocabulary.
    fn data_role_atom(
        vocabulary: &Vocabulary,
        iri: String,
        first: Term,
        second: Term,
    ) -> Result<Atom, String> {
        let atomic_role = AtomicRole::create(iri);
        if vocabulary.atomic_data_roles.contains(&atomic_role) {
            Ok(Atom::create(
                DLPredicate::AtomicRole(atomic_role),
                vec![first, second],
            ))
        } else {
            Err("Internal error: fresh properties in property assertions are not \
                 compatible with incremental ABox loading!"
                .into())
        }
    }

    fn visit(
        &mut self,
        component: &Component<A>,
        vocabulary: &Vocabulary,
        ignore_unsupported_datatypes: bool,
    ) -> Result<(), String> {
        match component {
            // Port of visit(OWLClassAssertionAxiom): named class, HasSelf,
            // HasValue, and their negations all produce positive/negative facts.
            Component::ClassAssertion(ax) => {
                let subject = individual(&ax.i);
                self.note(subject.clone());
                match &ax.ce {
                    CE::Class(c) => {
                        let atom = Self::concept_atom(
                            vocabulary,
                            c.0.to_string(),
                            Term::Individual(subject),
                        )?;
                        self.positive_facts.insert(atom);
                    }
                    CE::ObjectHasSelf(ope) => {
                        let atom = Self::object_role_atom(
                            vocabulary,
                            ope,
                            subject.clone(),
                            subject,
                        )?;
                        self.positive_facts.insert(atom);
                    }
                    CE::ObjectHasValue { ope, i } => {
                        let filler = individual(i);
                        self.note(filler.clone());
                        let atom =
                            Self::object_role_atom(vocabulary, ope, subject, filler)?;
                        self.positive_facts.insert(atom);
                    }
                    CE::ObjectComplementOf(inner) => match &**inner {
                        CE::Class(c) => {
                            let atom = Self::concept_atom(
                                vocabulary,
                                c.0.to_string(),
                                Term::Individual(subject),
                            )?;
                            self.negative_facts.insert(atom);
                        }
                        CE::ObjectHasSelf(ope) => {
                            let atom = Self::object_role_atom(
                                vocabulary,
                                ope,
                                subject.clone(),
                                subject,
                            )?;
                            self.negative_facts.insert(atom);
                        }
                        CE::ObjectHasValue { ope, i } => {
                            let filler = individual(i);
                            self.note(filler.clone());
                            let atom =
                                Self::object_role_atom(vocabulary, ope, subject, filler)?;
                            self.negative_facts.insert(atom);
                        }
                        _ => {
                            return Err("Internal error: invalid normal form for ABox \
                                        updates (class assertion with negated class)."
                                .into())
                        }
                    },
                    _ => {
                        return Err(
                            "Internal error: invalid normal form for ABox updates.".into()
                        )
                    }
                }
            }
            Component::ObjectPropertyAssertion(ax) => {
                let from = individual(&ax.from);
                let to = individual(&ax.to);
                self.note(from.clone());
                self.note(to.clone());
                let atom = Self::object_role_atom(vocabulary, &ax.ope, from, to)?;
                self.positive_facts.insert(atom);
            }
            Component::NegativeObjectPropertyAssertion(ax) => {
                let from = individual(&ax.from);
                let to = individual(&ax.to);
                self.note(from.clone());
                self.note(to.clone());
                let atom = Self::object_role_atom(vocabulary, &ax.ope, from, to)?;
                self.negative_facts.insert(atom);
            }
            Component::DataPropertyAssertion(ax) => {
                let from = individual(&ax.from);
                self.note(from.clone());
                let atom = Self::data_role_atom(
                    vocabulary,
                    ax.dp.0.to_string(),
                    Term::Individual(from),
                    Term::Constant(constant_for(&ax.to, ignore_unsupported_datatypes)?),
                )?;
                self.positive_facts.insert(atom);
            }
            // Port of visit(OWLNegativeDataPropertyAssertionAxiom): adds the data
            // role atom to the negative facts.
            Component::NegativeDataPropertyAssertion(ax) => {
                let from = individual(&ax.from);
                self.note(from.clone());
                let atom = Self::data_role_atom(
                    vocabulary,
                    ax.dp.0.to_string(),
                    Term::Individual(from),
                    Term::Constant(constant_for(&ax.to, ignore_unsupported_datatypes)?),
                )?;
                self.negative_facts.insert(atom);
            }
            Component::SameIndividual(ax) => {
                let inds: Vec<Individual> = ax.0.iter().map(individual).collect();
                // Java's `getIndividual` (which records the individual) is only
                // invoked inside the consecutive-pair loop, so a singleton
                // SameIndividual axiom records no individual at all.
                if inds.len() >= 2 {
                    for i in &inds {
                        self.note(i.clone());
                    }
                }
                // Java emits only the consecutive-pair chain
                // `Eq(i0,i1), Eq(i1,i2), ...` (`individuals.length-1` atoms),
                // not the full pairwise set. See
                // `ReducedABoxOnlyClausification.visit(OWLSameIndividualAxiom)`.
                for pair in inds.windows(2) {
                    self.positive_facts.insert(Atom::create(
                        DLPredicate::Equality,
                        vec![
                            Term::Individual(pair[0].clone()),
                            Term::Individual(pair[1].clone()),
                        ],
                    ));
                }
            }
            Component::DifferentIndividuals(ax) => {
                let inds: Vec<Individual> = ax.0.iter().map(individual).collect();
                // Java's `getIndividual` is only invoked inside the nested pair
                // loop, so a singleton DifferentIndividuals axiom records nothing.
                if inds.len() >= 2 {
                    for i in &inds {
                        self.note(i.clone());
                    }
                }
                for i in 0..inds.len() {
                    for j in (i + 1)..inds.len() {
                        self.positive_facts.insert(Atom::create(
                            DLPredicate::Inequality,
                            vec![
                                Term::Individual(inds[i].clone()),
                                Term::Individual(inds[j].clone()),
                            ],
                        ));
                    }
                }
            }
            _ => {} // TBox / declarations / annotations: ignored by the ABox path
        }
        Ok(())
    }
}

/// For an inverse object property, the fact `Inv(r)(a,b)` is `r(b,a)`.
fn order(ope: &OPE<A>, from: Individual, to: Individual) -> (Individual, Individual) {
    match ope {
        OPE::ObjectProperty(_) => (from, to),
        OPE::InverseObjectProperty(_) => (to, from),
    }
}

const XSD_STRING: &str = "http://www.w3.org/2001/XMLSchema#string";
const RDF_PLAIN_LITERAL: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";

/// Build a validated constant for a data-property-assertion object literal,
/// mirroring Java `ReducedABoxOnlyClausification.getConstant` (which is identical
/// to `OWLClausification.getConstant`): parse/validate via the shared
/// [`build_validated_constant`], rejecting a malformed literal of a supported
/// datatype or (when not ignoring) an unsupported datatype.
fn constant_for(
    literal: &horned_owl::model::Literal<A>,
    ignore_unsupported_datatypes: bool,
) -> Result<crate::model::Constant, String> {
    use horned_owl::model::Literal;
    let (lexical, datatype_uri) = match literal {
        Literal::Simple { literal } => (literal.clone(), XSD_STRING.to_string()),
        // An rdf:PlainLiteral lexical is "string@lang" (HermiT's
        // RDFPlainLiteralDataValue, parsed by splitting on the last '@'). The lang
        // tag is kept so the value space matches the full-reload clausifier and Java.
        Literal::Language { literal, lang } => {
            (format!("{literal}@{lang}"), RDF_PLAIN_LITERAL.to_string())
        }
        // A typed rdf:PlainLiteral with NO language tag canonicalizes to
        // "lexical@" (trailing '@'), matching OWLClausification.getConstant.
        Literal::Datatype { literal, datatype_iri } => {
            let datatype_uri = datatype_iri.to_string();
            if datatype_uri == RDF_PLAIN_LITERAL {
                (format!("{literal}@"), datatype_uri)
            } else {
                (literal.clone(), datatype_uri)
            }
        }
    };
    crate::structural::owl_clausification::build_validated_constant(
        lexical,
        datatype_uri,
        ignore_unsupported_datatypes,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use horned_owl::model::{
        Build, ClassAssertion, DataPropertyAssertion, DifferentIndividuals, Literal,
        MutableOntology, NegativeDataPropertyAssertion, ObjectPropertyAssertion,
    };

    const A_IRI: &str = "http://example.org/A";
    const R_IRI: &str = "http://example.org/r";
    const D_IRI: &str = "http://example.org/d";

    /// A vocabulary containing the A class, the r object role and the d data role.
    fn vocab() -> Vocabulary {
        let mut v = Vocabulary::default();
        v.atomic_concepts.insert(AtomicConcept::create(A_IRI));
        v.atomic_object_roles.insert(AtomicRole::create(R_IRI));
        v.atomic_data_roles.insert(AtomicRole::create(D_IRI));
        v
    }

    fn single(facts: &HashSet<Atom>) -> &Atom {
        assert_eq!(facts.len(), 1);
        facts.iter().next().unwrap()
    }

    fn expect_err(result: Result<ReducedABoxClausification, String>) -> String {
        match result {
            Ok(_) => panic!("expected an error for an out-of-vocabulary predicate"),
            Err(e) => e,
        }
    }

    fn args(atom: &Atom) -> Vec<Term> {
        (0..atom.get_arity())
            .map(|i| atom.get_argument(i).clone())
            .collect()
    }

    #[test]
    fn abox_clausifies_to_facts() {
        let build = Build::new_arc();
        let a_class = build.class(A_IRI);
        let r = build.object_property(R_IRI);
        let a = build.named_individual("http://example.org/a");
        let b = build.named_individual("http://example.org/b");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(a_class.clone()),
            i: OwlIndividual::Named(a.clone()),
        }));
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::ObjectComplementOf(Box::new(CE::Class(a_class.clone()))),
            i: OwlIndividual::Named(b.clone()),
        }));
        ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
            ope: OPE::ObjectProperty(r.clone()),
            from: OwlIndividual::Named(a.clone()),
            to: OwlIndividual::Named(b.clone()),
        }));
        ontology.insert(Component::DifferentIndividuals(DifferentIndividuals(vec![
            OwlIndividual::Named(a.clone()),
            OwlIndividual::Named(b.clone()),
        ])));

        let result = ReducedABoxClausification::clausify(&ontology, &vocab(), false).unwrap();
        assert_eq!(result.positive_facts.len(), 3); // A(a), r(a,b), a != b
        assert_eq!(result.negative_facts.len(), 1); // ¬A(b)
        assert_eq!(result.individuals.len(), 2);
    }

    // visit(OWLNegativeDataPropertyAssertionAxiom) adds the data role atom
    // to the negative facts (and nothing to the positive facts).
    #[test]
    fn negative_data_property_assertion_produces_negative_fact() {
        let build = Build::new_arc();
        let d = build.data_property(D_IRI);
        let a = build.named_individual("http://example.org/a");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::NegativeDataPropertyAssertion(
            NegativeDataPropertyAssertion {
                dp: d.clone(),
                from: OwlIndividual::Named(a.clone()),
                to: Literal::Simple {
                    literal: "v".to_string(),
                },
            },
        ));

        let result = ReducedABoxClausification::clausify(&ontology, &vocab(), false).unwrap();
        assert!(result.positive_facts.is_empty());
        let atom = single(&result.negative_facts);
        assert_eq!(
            atom.get_dl_predicate(),
            &DLPredicate::AtomicRole(AtomicRole::create(D_IRI))
        );
        assert_eq!(result.individuals.len(), 1);
    }

    // A positive data property assertion goes to positive facts.
    #[test]
    fn positive_data_property_assertion_produces_positive_fact() {
        let build = Build::new_arc();
        let d = build.data_property(D_IRI);
        let a = build.named_individual("http://example.org/a");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
            dp: d.clone(),
            from: OwlIndividual::Named(a.clone()),
            to: Literal::Simple {
                literal: "v".to_string(),
            },
        }));

        let result = ReducedABoxClausification::clausify(&ontology, &vocab(), false).unwrap();
        assert!(result.negative_facts.is_empty());
        let atom = single(&result.positive_facts);
        assert_eq!(
            atom.get_dl_predicate(),
            &DLPredicate::AtomicRole(AtomicRole::create(D_IRI))
        );
    }

    // ClassAssertion(ObjectHasSelf(r), a) -> positive self fact r(a,a).
    #[test]
    fn class_assertion_has_self_produces_positive_self_fact() {
        let build = Build::new_arc();
        let r = build.object_property(R_IRI);
        let a = build.named_individual("http://example.org/a");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::ObjectHasSelf(OPE::ObjectProperty(r.clone())),
            i: OwlIndividual::Named(a.clone()),
        }));

        let result = ReducedABoxClausification::clausify(&ontology, &vocab(), false).unwrap();
        assert!(result.negative_facts.is_empty());
        let atom = single(&result.positive_facts);
        assert_eq!(
            atom.get_dl_predicate(),
            &DLPredicate::AtomicRole(AtomicRole::create(R_IRI))
        );
        let ind = Term::Individual(individual(&OwlIndividual::Named(a.clone())));
        assert_eq!(args(atom), vec![ind.clone(), ind]);
    }

    // ClassAssertion(ObjectComplementOf(ObjectHasSelf(r)), a) -> negative
    // self fact.
    #[test]
    fn class_assertion_negated_has_self_produces_negative_self_fact() {
        let build = Build::new_arc();
        let r = build.object_property(R_IRI);
        let a = build.named_individual("http://example.org/a");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::ObjectComplementOf(Box::new(CE::ObjectHasSelf(OPE::ObjectProperty(
                r.clone(),
            )))),
            i: OwlIndividual::Named(a.clone()),
        }));

        let result = ReducedABoxClausification::clausify(&ontology, &vocab(), false).unwrap();
        assert!(result.positive_facts.is_empty());
        let atom = single(&result.negative_facts);
        assert_eq!(
            atom.get_dl_predicate(),
            &DLPredicate::AtomicRole(AtomicRole::create(R_IRI))
        );
    }

    // ClassAssertion(ObjectHasValue(r, b), a) -> positive fact r(a,b).
    #[test]
    fn class_assertion_has_value_produces_positive_role_fact() {
        let build = Build::new_arc();
        let r = build.object_property(R_IRI);
        let a = build.named_individual("http://example.org/a");
        let b = build.named_individual("http://example.org/b");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::ObjectHasValue {
                ope: OPE::ObjectProperty(r.clone()),
                i: OwlIndividual::Named(b.clone()),
            },
            i: OwlIndividual::Named(a.clone()),
        }));

        let result = ReducedABoxClausification::clausify(&ontology, &vocab(), false).unwrap();
        assert!(result.negative_facts.is_empty());
        let atom = single(&result.positive_facts);
        assert_eq!(
            atom.get_dl_predicate(),
            &DLPredicate::AtomicRole(AtomicRole::create(R_IRI))
        );
        assert_eq!(
            args(atom),
            vec![
                Term::Individual(individual(&OwlIndividual::Named(a.clone()))),
                Term::Individual(individual(&OwlIndividual::Named(b.clone()))),
            ]
        );
        // Both the subject and the filler are recorded.
        assert_eq!(result.individuals.len(), 2);
    }

    // Negated HasValue -> negative role fact.
    #[test]
    fn class_assertion_negated_has_value_produces_negative_role_fact() {
        let build = Build::new_arc();
        let r = build.object_property(R_IRI);
        let a = build.named_individual("http://example.org/a");
        let b = build.named_individual("http://example.org/b");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::ObjectComplementOf(Box::new(CE::ObjectHasValue {
                ope: OPE::ObjectProperty(r.clone()),
                i: OwlIndividual::Named(b.clone()),
            })),
            i: OwlIndividual::Named(a.clone()),
        }));

        let result = ReducedABoxClausification::clausify(&ontology, &vocab(), false).unwrap();
        assert!(result.positive_facts.is_empty());
        let atom = single(&result.negative_facts);
        assert_eq!(
            atom.get_dl_predicate(),
            &DLPredicate::AtomicRole(AtomicRole::create(R_IRI))
        );
    }

    // HasValue over an inverse property swaps the arguments, mirroring the
    // anonymous-property branch of Java getRoleAtom: Inv(r)(a,b) is r(b,a).
    #[test]
    fn class_assertion_has_value_inverse_swaps_arguments() {
        let build = Build::new_arc();
        let r = build.object_property(R_IRI);
        let a = build.named_individual("http://example.org/a");
        let b = build.named_individual("http://example.org/b");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::ObjectHasValue {
                ope: OPE::InverseObjectProperty(r.clone()),
                i: OwlIndividual::Named(b.clone()),
            },
            i: OwlIndividual::Named(a.clone()),
        }));

        let result = ReducedABoxClausification::clausify(&ontology, &vocab(), false).unwrap();
        let atom = single(&result.positive_facts);
        // r(b, a): swapped relative to HasValue(r, b) on a.
        assert_eq!(
            args(atom),
            vec![
                Term::Individual(individual(&OwlIndividual::Named(b.clone()))),
                Term::Individual(individual(&OwlIndividual::Named(a.clone()))),
            ]
        );
    }

    // An assertion using a class outside the loaded vocabulary is rejected,
    // mirroring the IllegalArgumentException thrown by Java getConceptAtom.
    #[test]
    fn unknown_class_predicate_is_rejected() {
        let build = Build::new_arc();
        let fresh = build.class("http://example.org/Fresh");
        let a = build.named_individual("http://example.org/a");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::ClassAssertion(ClassAssertion {
            ce: CE::Class(fresh.clone()),
            i: OwlIndividual::Named(a.clone()),
        }));

        let err = expect_err(ReducedABoxClausification::clausify(&ontology, &vocab(), false));
        assert!(err.contains("incremental ABox loading"));
    }

    // An assertion using an object role outside the vocabulary is rejected.
    #[test]
    fn unknown_object_role_predicate_is_rejected() {
        let build = Build::new_arc();
        let fresh = build.object_property("http://example.org/fresh");
        let a = build.named_individual("http://example.org/a");
        let b = build.named_individual("http://example.org/b");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::ObjectPropertyAssertion(ObjectPropertyAssertion {
            ope: OPE::ObjectProperty(fresh.clone()),
            from: OwlIndividual::Named(a.clone()),
            to: OwlIndividual::Named(b.clone()),
        }));

        let err = expect_err(ReducedABoxClausification::clausify(&ontology, &vocab(), false));
        assert!(err.contains("incremental ABox loading"));
    }

    // An assertion using a data role outside the vocabulary is rejected.
    #[test]
    fn unknown_data_role_predicate_is_rejected() {
        let build = Build::new_arc();
        let fresh = build.data_property("http://example.org/fresh");
        let a = build.named_individual("http://example.org/a");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
            dp: fresh.clone(),
            from: OwlIndividual::Named(a.clone()),
            to: Literal::Simple {
                literal: "v".to_string(),
            },
        }));

        let err = expect_err(ReducedABoxClausification::clausify(&ontology, &vocab(), false));
        assert!(err.contains("incremental ABox loading"));
    }

    // A data-property-assertion object literal with a malformed lexical
    // form of a SUPPORTED datatype is rejected (MalformedLiteralException analogue),
    // mirroring the full clausifier and Java ReducedABoxOnlyClausification.getConstant.
    #[test]
    fn malformed_literal_is_rejected() {
        let build = Build::new_arc();
        let d = build.data_property(D_IRI);
        let a = build.named_individual("http://example.org/a");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
            dp: d.clone(),
            from: OwlIndividual::Named(a.clone()),
            to: Literal::Datatype {
                literal: "abc".to_string(),
                datatype_iri: build.iri("http://www.w3.org/2001/XMLSchema#integer"),
            },
        }));
        let err = expect_err(ReducedABoxClausification::clausify(&ontology, &vocab(), false));
        assert!(err.contains("Malformed"), "expected a malformed-literal error, got: {err}");
    }

    // An unsupported (non-internal) datatype is rejected by default and
    // anonymized under ignore_unsupported_datatypes (UnsupportedDatatypeException
    // analogue).
    #[test]
    fn unsupported_datatype_literal_rejected_or_anonymized() {
        let build = Build::new_arc();
        let d = build.data_property(D_IRI);
        let a = build.named_individual("http://example.org/a");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
            dp: d.clone(),
            from: OwlIndividual::Named(a.clone()),
            to: Literal::Datatype {
                literal: "v".to_string(),
                datatype_iri: build.iri("http://example.org/MyType"),
            },
        }));
        assert!(ReducedABoxClausification::clausify(&ontology, &vocab(), false).is_err());
        let ok = ReducedABoxClausification::clausify(&ontology, &vocab(), true)
            .expect("ignore_unsupported_datatypes substitutes an anonymous constant");
        let atom = single(&ok.positive_facts);
        let constant = atom.get_argument(1).as_constant().expect("data value is a constant");
        assert!(constant.is_anonymous());
    }

    // CRITICAL: internal:* datatypes are always valid (the reductions'
    // internal:anonymous-constants must pass through this path unchanged).
    #[test]
    fn internal_datatype_literal_is_accepted() {
        let build = Build::new_arc();
        let d = build.data_property(D_IRI);
        let a = build.named_individual("http://example.org/a");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
            dp: d.clone(),
            from: OwlIndividual::Named(a.clone()),
            to: Literal::Datatype {
                literal: "c1".to_string(),
                datatype_iri: build.iri("internal:anonymous-constants"),
            },
        }));
        let ok = ReducedABoxClausification::clausify(&ontology, &vocab(), false)
            .expect("internal:* datatypes are always valid");
        let atom = single(&ok.positive_facts);
        let constant = atom.get_argument(1).as_constant().expect("data value is a constant");
        assert_eq!(constant.lexical_form(), "c1");
        assert_eq!(constant.datatype_uri(), "internal:anonymous-constants");
    }

    // A typed rdf:PlainLiteral with NO language tag canonicalizes its lexical
    // form to "lexical@" on the reduced path too (parity with the full clausifier).
    #[test]
    fn typed_plain_literal_without_lang_gets_trailing_at() {
        let build = Build::new_arc();
        let d = build.data_property(D_IRI);
        let a = build.named_individual("http://example.org/a");

        let mut ontology: SetOntology<A> = SetOntology::new();
        ontology.insert(Component::DataPropertyAssertion(DataPropertyAssertion {
            dp: d.clone(),
            from: OwlIndividual::Named(a.clone()),
            to: Literal::Datatype {
                literal: "abc".to_string(),
                datatype_iri: build.iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral"),
            },
        }));
        let ok = ReducedABoxClausification::clausify(&ontology, &vocab(), false).unwrap();
        let atom = single(&ok.positive_facts);
        let constant = atom.get_argument(1).as_constant().expect("data value is a constant");
        assert_eq!(constant.lexical_form(), "abc@");
    }
}
