// Port of org.semanticweb.HermiT.structural.BuiltInPropertyManager.
//
// Adds the axioms that give owl:topObjectProperty / owl:bottomObjectProperty /
// owl:topDataProperty / owl:bottomDataProperty their built-in meaning, but only
// when they actually occur in the ontology (determined by the nested Checker).
// The OWL-API data factory is replaced by horned-owl's `Build`.

use horned_owl::model::{
    Build, ClassExpression as CE, DataProperty, DataRange, Individual, Literal, ObjectProperty,
    ObjectPropertyExpression,
};

use crate::model::AtomicRole;

use super::owl_axioms::{ComplexObjectPropertyInclusion, Fact, OWLAxioms};
use super::{named_property, ClassExpr, ObjectPropExpr};

pub struct BuiltInPropertyManager {
    build: Build<super::A>,
    top_object_property: ObjectProperty<super::A>,
    bottom_object_property: ObjectProperty<super::A>,
    top_data_property: DataProperty<super::A>,
    bottom_data_property: DataProperty<super::A>,
}

impl BuiltInPropertyManager {
    pub fn new() -> BuiltInPropertyManager {
        let build = Build::new_arc();
        let top_object_property = build.object_property(AtomicRole::top_object_role().iri());
        let bottom_object_property = build.object_property(AtomicRole::bottom_object_role().iri());
        let top_data_property = build.data_property(AtomicRole::top_data_role().iri());
        let bottom_data_property = build.data_property(AtomicRole::bottom_data_role().iri());
        BuiltInPropertyManager {
            build,
            top_object_property,
            bottom_object_property,
            top_data_property,
            bottom_data_property,
        }
    }

    pub fn axiomatize_built_in_properties_as_needed_with_skips(
        &self,
        axioms: &mut OWLAxioms,
        skip_top_object_property: bool,
        skip_bottom_object_property: bool,
        skip_top_data_property: bool,
        skip_bottom_data_property: bool,
    ) {
        let checker = Checker::new(self, axioms);
        if checker.uses_top_object_property && !skip_top_object_property {
            self.axiomatize_top_object_property(axioms);
        }
        if checker.uses_bottom_object_property && !skip_bottom_object_property {
            self.axiomatize_bottom_object_property(axioms);
        }
        if checker.uses_top_data_property && !skip_top_data_property {
            self.axiomatize_top_data_property(axioms);
        }
        if checker.uses_bottom_data_property && !skip_bottom_data_property {
            self.axiomatize_bottom_data_property(axioms);
        }
    }

    pub fn axiomatize_built_in_properties_as_needed(&self, axioms: &mut OWLAxioms) {
        self.axiomatize_built_in_properties_as_needed_with_skips(axioms, false, false, false, false);
    }

    fn top_object_property_expr(&self) -> ObjectPropExpr {
        ObjectPropertyExpression::ObjectProperty(self.top_object_property.clone())
    }

    fn axiomatize_top_object_property(&self, axioms: &mut OWLAxioms) {
        // TransitiveObjectProperty( owl:topObjectProperty )
        axioms
            .complex_object_property_inclusions
            .push(ComplexObjectPropertyInclusion::transitive(
                self.top_object_property_expr(),
            ));
        // SymmetricObjectProperty( owl:topObjectProperty )
        axioms.simple_object_property_inclusions.push([
            self.top_object_property_expr(),
            ObjectPropertyExpression::InverseObjectProperty(self.top_object_property.clone()),
        ]);
        // SubClassOf( owl:Thing
        //   ObjectSomeValuesFrom( owl:topObjectProperty
        //     ObjectOneOf( <internal:nam#topIndividual> ) ) )
        let new_individual =
            Individual::Named(self.build.named_individual("internal:nam#topIndividual"));
        let one_of_new_individual = CE::ObjectOneOf(vec![new_individual]);
        let has_top_new_individual = CE::ObjectSomeValuesFrom {
            ope: self.top_object_property_expr(),
            bce: Box::new(one_of_new_individual),
        };
        axioms.concept_inclusions.push(vec![has_top_new_individual]);
    }

    fn axiomatize_bottom_object_property(&self, axioms: &mut OWLAxioms) {
        let nothing = CE::Class(self.build.class("http://www.w3.org/2002/07/owl#Nothing"));
        let all_values = CE::ObjectAllValuesFrom {
            ope: ObjectPropertyExpression::ObjectProperty(self.bottom_object_property.clone()),
            bce: Box::new(nothing),
        };
        axioms.concept_inclusions.push(vec![all_values]);
    }

    fn axiomatize_top_data_property(&self, axioms: &mut OWLAxioms) {
        let new_constant = Literal::Datatype {
            literal: "internal:constant".to_string(),
            datatype_iri: self.build.iri("internal:anonymous-constants"),
        };
        let one_of_new_constant = DataRange::DataOneOf(vec![new_constant]);
        let has_top_new_constant = CE::DataSomeValuesFrom {
            dp: self.top_data_property.clone(),
            dr: one_of_new_constant,
        };
        axioms.concept_inclusions.push(vec![has_top_new_constant]);
    }

    fn axiomatize_bottom_data_property(&self, axioms: &mut OWLAxioms) {
        let top_datatype =
            DataRange::Datatype(self.build.datatype("http://www.w3.org/2000/01/rdf-schema#Literal"));
        let all_values = CE::DataAllValuesFrom {
            dp: self.bottom_data_property.clone(),
            dr: DataRange::DataComplementOf(Box::new(top_datatype)),
        };
        axioms.concept_inclusions.push(vec![all_values]);
    }
}

impl Default for BuiltInPropertyManager {
    fn default() -> Self {
        BuiltInPropertyManager::new()
    }
}

/// Port of the nested BuiltInPropertyManager.Checker: records which of the four
/// built-in properties are actually used in the ontology.
struct Checker {
    uses_top_object_property: bool,
    uses_bottom_object_property: bool,
    uses_top_data_property: bool,
    uses_bottom_data_property: bool,
    top_object_property: ObjectProperty<super::A>,
    bottom_object_property: ObjectProperty<super::A>,
    top_data_property: DataProperty<super::A>,
    bottom_data_property: DataProperty<super::A>,
}

impl Checker {
    fn new(manager: &BuiltInPropertyManager, axioms: &OWLAxioms) -> Checker {
        let mut checker = Checker {
            uses_top_object_property: false,
            uses_bottom_object_property: false,
            uses_top_data_property: false,
            uses_bottom_data_property: false,
            top_object_property: manager.top_object_property.clone(),
            bottom_object_property: manager.bottom_object_property.clone(),
            top_data_property: manager.top_data_property.clone(),
            bottom_data_property: manager.bottom_data_property.clone(),
        };
        for inclusion in &axioms.concept_inclusions {
            for description in inclusion {
                checker.visit_class_expression(description);
            }
        }
        for inclusion in &axioms.simple_object_property_inclusions {
            checker.visit_object_property(&inclusion[0]);
            checker.visit_object_property(&inclusion[1]);
        }
        for inclusion in &axioms.complex_object_property_inclusions {
            for sub_object_property in &inclusion.sub_object_properties {
                checker.visit_object_property(sub_object_property);
            }
            checker.visit_object_property(&inclusion.super_object_property);
        }
        for disjoint in &axioms.disjoint_object_properties {
            for a_disjoint in disjoint {
                checker.visit_object_property(a_disjoint);
            }
        }
        for property in &axioms.reflexive_object_properties {
            checker.visit_object_property(property);
        }
        for property in &axioms.irreflexive_object_properties {
            checker.visit_object_property(property);
        }
        for property in &axioms.asymmetric_object_properties {
            checker.visit_object_property(property);
        }
        for inclusion in &axioms.data_property_inclusions {
            checker.visit_data_property(&inclusion[0]);
            checker.visit_data_property(&inclusion[1]);
        }
        for disjoint in &axioms.disjoint_data_properties {
            for a_disjoint in disjoint {
                checker.visit_data_property(a_disjoint);
            }
        }
        for fact in &axioms.facts {
            checker.visit_fact(fact);
        }
        checker
    }

    fn visit_object_property(&mut self, object: &ObjectPropExpr) {
        let named = named_property(object);
        if named == &self.top_object_property {
            self.uses_top_object_property = true;
        } else if named == &self.bottom_object_property {
            self.uses_bottom_object_property = true;
        }
    }

    fn visit_data_property(&mut self, object: &DataProperty<super::A>) {
        if object == &self.top_data_property {
            self.uses_top_data_property = true;
        } else if object == &self.bottom_data_property {
            self.uses_bottom_data_property = true;
        }
    }

    fn visit_fact(&mut self, fact: &Fact) {
        match fact {
            Fact::SameIndividual(_) | Fact::DifferentIndividuals(_) => {}
            Fact::ClassAssertion { class_expression, .. } => {
                self.visit_class_expression(class_expression)
            }
            Fact::ObjectPropertyAssertion { ope, .. } => self.visit_object_property(ope),
            Fact::NegativeObjectPropertyAssertion { ope, .. } => self.visit_object_property(ope),
            Fact::DataPropertyAssertion { dp, .. } => self.visit_data_property(dp),
            Fact::NegativeDataPropertyAssertion { dp, .. } => self.visit_data_property(dp),
        }
    }

    fn visit_class_expression(&mut self, ce: &ClassExpr) {
        match ce {
            CE::Class(_) | CE::ObjectOneOf(_) => {}
            CE::ObjectComplementOf(operand) => self.visit_class_expression(operand),
            CE::ObjectIntersectionOf(operands) | CE::ObjectUnionOf(operands) => {
                for description in operands {
                    self.visit_class_expression(description);
                }
            }
            CE::ObjectSomeValuesFrom { ope, bce }
            | CE::ObjectAllValuesFrom { ope, bce }
            | CE::ObjectMinCardinality { ope, bce, .. }
            | CE::ObjectMaxCardinality { ope, bce, .. }
            | CE::ObjectExactCardinality { ope, bce, .. } => {
                self.visit_object_property(ope);
                self.visit_class_expression(bce);
            }
            CE::ObjectHasValue { ope, .. } | CE::ObjectHasSelf(ope) => {
                self.visit_object_property(ope)
            }
            CE::DataHasValue { dp, .. }
            | CE::DataSomeValuesFrom { dp, .. }
            | CE::DataAllValuesFrom { dp, .. }
            | CE::DataMinCardinality { dp, .. }
            | CE::DataMaxCardinality { dp, .. }
            | CE::DataExactCardinality { dp, .. } => self.visit_data_property(dp),
        }
    }
}
