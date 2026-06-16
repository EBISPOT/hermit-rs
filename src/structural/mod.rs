// Port of the org.semanticweb.HermiT.structural package: the structural
// transformation that normalizes an OWL 2 ontology and clausifies it into a
// `model::DLOntology`.
//
// HermiT's structural package is written against the OWL API. This port targets
// `horned-owl` instead: the OWL-API class-expression/axiom visitor patterns
// become recursive `match`es over horned-owl's `ClassExpression`, `DataRange`,
// `ObjectPropertyExpression` and `Component` enums.
//
// All horned-owl types are instantiated with the thread-safe `ArcStr` string
// backing (`A`).

pub mod automaton;
pub mod built_in_property_manager;
pub mod expression_manager;
pub mod expressivity;
pub mod object_property_inclusion_manager;
pub mod owl_axioms;
pub mod owl_clausification;
pub mod reduced_abox_clausification;
pub mod owl_normalization;

/// The string backing used for all horned-owl model types in this port.
pub type A = horned_owl::model::ArcStr;

pub type ClassExpr = horned_owl::model::ClassExpression<A>;
pub type ObjectPropExpr = horned_owl::model::ObjectPropertyExpression<A>;
pub type DataRangeExpr = horned_owl::model::DataRange<A>;
pub type PropExpr = horned_owl::model::PropertyExpression<A>;
pub type Individ = horned_owl::model::Individual<A>;
pub type Lit = horned_owl::model::Literal<A>;
pub type SwrlAtom = horned_owl::model::Atom<A>;

pub use built_in_property_manager::BuiltInPropertyManager;
pub use expression_manager::ExpressionManager;
pub use expressivity::OWLAxiomsExpressivity;
pub use object_property_inclusion_manager::ObjectPropertyInclusionManager;
pub use owl_clausification::{Configuration, OWLClausification};
pub use owl_normalization::OWLNormalization;
pub use owl_axioms::{ComplexObjectPropertyInclusion, DisjunctiveRule, Fact, HasKeyAxiom, OWLAxioms};

use horned_owl::model::{ObjectProperty, ObjectPropertyExpression};

/// Returns the named object property underlying an object property expression
/// (the OWL-API `getNamedProperty()`).
pub fn named_property(ope: &ObjectPropExpr) -> &ObjectProperty<A> {
    match ope {
        ObjectPropertyExpression::ObjectProperty(p) => p,
        ObjectPropertyExpression::InverseObjectProperty(p) => p,
    }
}

/// Whether an object property expression is anonymous, i.e. an inverse
/// (the OWL-API `isAnonymous()`).
pub fn is_anonymous_property(ope: &ObjectPropExpr) -> bool {
    matches!(ope, ObjectPropertyExpression::InverseObjectProperty(_))
}

/// The inverse of an object property expression (the OWL-API
/// `getInverseProperty()`).
pub fn inverse_property(ope: &ObjectPropExpr) -> ObjectPropExpr {
    match ope {
        ObjectPropertyExpression::ObjectProperty(p) => {
            ObjectPropertyExpression::InverseObjectProperty(p.clone())
        }
        ObjectPropertyExpression::InverseObjectProperty(p) => {
            ObjectPropertyExpression::ObjectProperty(p.clone())
        }
    }
}
