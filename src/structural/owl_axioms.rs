// Port of org.semanticweb.HermiT.structural.OWLAxioms (and its nested
// ComplexObjectPropertyInclusion and DisjunctiveRule classes).
//
// A mutable container that accumulates the result of normalization: the
// vocabulary plus the normalized concept/role/data inclusions and the ABox
// facts. Populated by OWLNormalization and consumed by OWLClausification.

use std::collections::HashSet;

use horned_owl::model::{
    Class, DataProperty, NamedIndividual, ObjectProperty,
};

use super::{ClassExpr, DataRangeExpr, Individ, Lit, ObjectPropExpr, PropExpr, SwrlAtom};

#[derive(Default)]
pub struct OWLAxioms {
    pub classes: HashSet<Class<super::A>>,
    pub object_properties: HashSet<ObjectProperty<super::A>>,
    pub object_properties_occurring_in_owl_axioms: HashSet<ObjectProperty<super::A>>,
    pub complex_object_property_expressions: HashSet<ObjectPropExpr>,
    pub data_properties: HashSet<DataProperty<super::A>>,
    pub named_individuals: HashSet<NamedIndividual<super::A>>,
    /// Each entry is a disjunction of class expressions standing for the
    /// inclusion `owl:Thing ⊑ C_1 ⊔ ... ⊔ C_n`.
    pub concept_inclusions: Vec<Vec<ClassExpr>>,
    pub data_range_inclusions: Vec<Vec<DataRangeExpr>>,
    /// Each entry is a `[sub, super]` pair.
    pub simple_object_property_inclusions: Vec<[ObjectPropExpr; 2]>,
    pub complex_object_property_inclusions: Vec<ComplexObjectPropertyInclusion>,
    pub disjoint_object_properties: Vec<Vec<ObjectPropExpr>>,
    pub reflexive_object_properties: HashSet<ObjectPropExpr>,
    pub irreflexive_object_properties: HashSet<ObjectPropExpr>,
    pub asymmetric_object_properties: HashSet<ObjectPropExpr>,
    /// Each entry is a `[sub, super]` pair of data properties.
    pub data_property_inclusions: Vec<[DataProperty<super::A>; 2]>,
    pub disjoint_data_properties: Vec<Vec<DataProperty<super::A>>>,
    pub facts: Vec<Fact>,
    pub has_keys: Vec<HasKeyAxiom>,
    /// Custom datatypes introduced by DatatypeDefinition axioms.
    pub defined_datatype_iris: HashSet<String>,
    pub rules: Vec<DisjunctiveRule>,
}

impl OWLAxioms {
    pub fn new() -> OWLAxioms {
        OWLAxioms::default()
    }
}

/// Port of OWLAxioms.ComplexObjectPropertyInclusion.
pub struct ComplexObjectPropertyInclusion {
    pub sub_object_properties: Vec<ObjectPropExpr>,
    pub super_object_property: ObjectPropExpr,
}

impl ComplexObjectPropertyInclusion {
    pub fn new(
        sub_object_properties: Vec<ObjectPropExpr>,
        super_object_property: ObjectPropExpr,
    ) -> ComplexObjectPropertyInclusion {
        ComplexObjectPropertyInclusion { sub_object_properties, super_object_property }
    }
    /// The single-argument constructor used for transitive properties:
    /// `p ∘ p ⊑ p`.
    pub fn transitive(transitive_object_property: ObjectPropExpr) -> ComplexObjectPropertyInclusion {
        ComplexObjectPropertyInclusion {
            sub_object_properties: vec![
                transitive_object_property.clone(),
                transitive_object_property.clone(),
            ],
            super_object_property: transitive_object_property,
        }
    }
}

/// Port of OWLAxioms.DisjunctiveRule (a SWRL rule with a disjunctive head).
///
/// Java stores rules in `m_rules`, a `HashSet`, so equal rules collapse;
/// `Hash`/`Eq` here mirror that to allow deduplication on consumption.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct DisjunctiveRule {
    pub body: Vec<SwrlAtom>,
    pub head: Vec<SwrlAtom>,
}

impl DisjunctiveRule {
    pub fn new(body: Vec<SwrlAtom>, head: Vec<SwrlAtom>) -> DisjunctiveRule {
        DisjunctiveRule { body, head }
    }
}

/// A HasKey axiom, retaining the OWL-API split between object and data
/// property expressions.
pub struct HasKeyAxiom {
    pub class_expression: ClassExpr,
    pub property_expressions: Vec<PropExpr>,
}

/// The individual (ABox) axioms collected in `OWLAxioms.m_facts`
/// (`OWLIndividualAxiom`).
///
/// Java stores facts in `m_facts`, a `HashSet`, so equal assertions collapse;
/// `Hash`/`Eq` here mirror that to allow deduplication on consumption.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Fact {
    SameIndividual(Vec<Individ>),
    DifferentIndividuals(Vec<Individ>),
    ClassAssertion { class_expression: ClassExpr, individual: Individ },
    ObjectPropertyAssertion { ope: ObjectPropExpr, from: Individ, to: Individ },
    NegativeObjectPropertyAssertion { ope: ObjectPropExpr, from: Individ, to: Individ },
    DataPropertyAssertion { dp: DataProperty<super::A>, from: Individ, to: Lit },
    NegativeDataPropertyAssertion { dp: DataProperty<super::A>, from: Individ, to: Lit },
}
