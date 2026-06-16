// Port of org.semanticweb.HermiT.structural.OWLAxiomsExpressivity.
//
// Computes the expressivity flags of a normalized `OWLAxioms` by walking the
// class expressions and properties it contains. The OWL-API class-expression
// visitor becomes the recursive `visit_class_expression` match below.

use horned_owl::model::ClassExpression as CE;

use super::owl_axioms::{Fact, OWLAxioms};
use super::{is_anonymous_property, ClassExpr, ObjectPropExpr};

#[derive(Default)]
pub struct OWLAxiomsExpressivity {
    pub has_at_most_restrictions: bool,
    pub has_inverse_roles: bool,
    pub has_nominals: bool,
    pub has_datatypes: bool,
    pub has_swrl_rules: bool,
}

impl OWLAxiomsExpressivity {
    pub fn new(axioms: &OWLAxioms) -> OWLAxiomsExpressivity {
        let mut e = OWLAxiomsExpressivity::default();
        for inclusion in &axioms.concept_inclusions {
            for description in inclusion {
                e.visit_class_expression(description);
            }
        }
        for inclusion in &axioms.simple_object_property_inclusions {
            e.visit_property(&inclusion[0]);
            e.visit_property(&inclusion[1]);
        }
        for inclusion in &axioms.complex_object_property_inclusions {
            for sub_object_property in &inclusion.sub_object_properties {
                e.visit_property(sub_object_property);
            }
            e.visit_property(&inclusion.super_object_property);
        }
        for disjoint in &axioms.disjoint_object_properties {
            for a_disjoint in disjoint {
                e.visit_property(a_disjoint);
            }
        }
        for property in &axioms.reflexive_object_properties {
            e.visit_property(property);
        }
        for property in &axioms.irreflexive_object_properties {
            e.visit_property(property);
        }
        for property in &axioms.asymmetric_object_properties {
            e.visit_property(property);
        }
        if !axioms.data_properties.is_empty()
            || !axioms.disjoint_data_properties.is_empty()
            || !axioms.data_property_inclusions.is_empty()
            || !axioms.data_range_inclusions.is_empty()
            || !axioms.defined_datatype_iris.is_empty()
        {
            e.has_datatypes = true;
        }
        for fact in &axioms.facts {
            e.visit_fact(fact);
        }
        e.has_swrl_rules = !axioms.rules.is_empty();
        e
    }

    fn visit_property(&mut self, object: &ObjectPropExpr) {
        if is_anonymous_property(object) {
            self.has_inverse_roles = true;
        }
    }

    fn visit_fact(&mut self, fact: &Fact) {
        match fact {
            Fact::ClassAssertion { class_expression, .. } => {
                self.visit_class_expression(class_expression);
            }
            Fact::ObjectPropertyAssertion { ope, .. } => self.visit_property(ope),
            Fact::NegativeObjectPropertyAssertion { ope, .. } => self.visit_property(ope),
            Fact::DataPropertyAssertion { .. } => self.has_datatypes = true,
            // SameIndividual, DifferentIndividuals and negative data property
            // assertions are not overridden in the Java visitor: no-ops.
            Fact::SameIndividual(_)
            | Fact::DifferentIndividuals(_)
            | Fact::NegativeDataPropertyAssertion { .. } => {}
        }
    }

    fn visit_class_expression(&mut self, ce: &ClassExpr) {
        match ce {
            CE::Class(_) => {}
            CE::ObjectComplementOf(operand) => self.visit_class_expression(operand),
            CE::ObjectIntersectionOf(operands) | CE::ObjectUnionOf(operands) => {
                for description in operands {
                    self.visit_class_expression(description);
                }
            }
            CE::ObjectOneOf(_) => self.has_nominals = true,
            CE::ObjectSomeValuesFrom { ope, bce } => {
                self.visit_property(ope);
                self.visit_class_expression(bce);
            }
            CE::ObjectHasValue { ope, .. } => {
                self.has_nominals = true;
                self.visit_property(ope);
            }
            CE::ObjectHasSelf(ope) => self.visit_property(ope),
            CE::ObjectAllValuesFrom { ope, bce } => {
                self.visit_property(ope);
                self.visit_class_expression(bce);
            }
            CE::ObjectMinCardinality { ope, bce, .. } => {
                self.visit_property(ope);
                self.visit_class_expression(bce);
            }
            CE::ObjectMaxCardinality { ope, bce, .. } => {
                self.has_at_most_restrictions = true;
                self.visit_property(ope);
                self.visit_class_expression(bce);
            }
            CE::ObjectExactCardinality { ope, bce, .. } => {
                self.has_at_most_restrictions = true;
                self.visit_property(ope);
                self.visit_class_expression(bce);
            }
            CE::DataHasValue { .. }
            | CE::DataSomeValuesFrom { .. }
            | CE::DataAllValuesFrom { .. }
            | CE::DataMinCardinality { .. }
            | CE::DataMaxCardinality { .. }
            | CE::DataExactCardinality { .. } => self.has_datatypes = true,
        }
    }
}
