// Port of org.semanticweb.HermiT.structural.OWLNormalization.
//
// Implements the structural transformation: it puts axioms into negation normal
// form, breaks them into disjunctions, rewrites exact cardinalities, and
// introduces fresh "definition" concepts for complex sub-expressions so that
// the result is a set of normalized concept/role/data inclusions plus ABox
// facts (accumulated in `OWLAxioms`).
//
// The OWL-API axiom and class-expression visitors become the methods below.
//
// SCOPE: the full OWL 2 DL pipeline is ported here, including SWRL rule
// normalization (the Java `RuleNormalizer` and `Rule2FactConverter` inner
// classes): empty-body rules become facts, body `SameIndividualAtom`s become
// variable unification, individual arguments are grounded to fresh variables
// bound by `ObjectOneOf` body atoms, complex class/data-range atoms get fresh
// definitions, and the conjunctive head is split into one rule per head atom
// (Lloyd-Topor). The result is a set of `DisjunctiveRule`s whose atoms use only
// variables and named classes, ready for the `NormalizedRuleClausifier` port in
// `owl_clausification.rs`.

use std::collections::{HashMap, HashSet};

use horned_owl::model::{
    Build, Class, ClassExpression as CE, Component, DataProperty, DataRange as DR, Datatype,
    Individual, NamedIndividual, ObjectProperty, SubObjectPropertyExpression as SOPE,
};
use horned_owl::ontology::set::SetOntology;
use horned_owl::visitor::immutable::{Visit, Walk};

use super::expression_manager::ExpressionManager;
use super::owl_axioms::{ComplexObjectPropertyInclusion, Fact, HasKeyAxiom, OWLAxioms};
use super::{
    inverse_property, named_property, ClassExpr, DataRangeExpr, Individ, ObjectPropExpr as OPE,
    SwrlAtom, A,
};
use crate::model::AtomicRole;

use horned_owl::model::{
    Atom as SwrlAtomKind, DArgument, IArgument, Variable as SwrlVariable,
};

const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";
const OWL_NOTHING: &str = "http://www.w3.org/2002/07/owl#Nothing";
const RDFS_LITERAL: &str = "http://www.w3.org/2000/01/rdf-schema#Literal";

// is_built_in_class / is_built_in_object_property / is_built_in_data_property
// were removed: process_ontology now mirrors Java getXInSignature(INCLUDED)
// and includes built-ins verbatim (downstream consumers already deduplicate them).

/// Collects the ontology signature (used or declared) via horned-owl's `Walk`,
/// the analogue of the OWL API `getXInSignature` calls in
/// `OWLNormalization.processOntology`.
#[derive(Default)]
struct SignatureCollector {
    classes: HashSet<Class<A>>,
    object_properties: HashSet<ObjectProperty<A>>,
    data_properties: HashSet<DataProperty<A>>,
    named_individuals: HashSet<NamedIndividual<A>>,
}

impl Visit<A> for SignatureCollector {
    fn visit_class(&mut self, c: &Class<A>) {
        self.classes.insert(c.clone());
    }
    fn visit_object_property(&mut self, p: &ObjectProperty<A>) {
        self.object_properties.insert(p.clone());
    }
    fn visit_data_property(&mut self, p: &DataProperty<A>) {
        self.data_properties.insert(p.clone());
    }
    fn visit_named_individual(&mut self, i: &NamedIndividual<A>) {
        self.named_individuals.insert(i.clone());
    }
}

/// The work lists collected by the Java `AxiomVisitor`.
#[derive(Default)]
struct AxiomState {
    class_expression_inclusions: Vec<Vec<ClassExpr>>,
    data_range_inclusions: Vec<Vec<DataRangeExpr>>,
    /// The (non-empty-body) SWRL rules collected by `AxiomVisitor.m_rules`,
    /// kept as raw `(body, head)` atom lists awaiting `RuleNormalizer`.
    rules: Vec<(Vec<SwrlAtom>, Vec<SwrlAtom>)>,
}

pub struct OWLNormalization {
    factory: Build<A>,
    axioms: OWLAxioms,
    first_replacement_index: usize,
    definitions: HashMap<ClassExpr, ClassExpr>,
    definitions_for_negative_nominals: HashMap<ClassExpr, Class<A>>,
    data_range_definitions: HashMap<DataRangeExpr, Datatype<A>>,
    expression_manager: ExpressionManager,
    top_object_property: OPE,
    bottom_object_property: OPE,
    top_data_property: DataProperty<A>,
    bottom_data_property: DataProperty<A>,
    has_rules: bool,
    /// Counters for the fresh entities created by `Rule2FactConverter`
    /// (`freshIndividuals` / `freshDataProperties`).
    fresh_rule_individuals: u32,
    fresh_rule_data_properties: u32,
}

impl OWLNormalization {
    pub fn new(axioms: OWLAxioms, first_replacement_index: usize) -> OWLNormalization {
        let factory = Build::new_arc();
        let top_object_property =
            OPE::ObjectProperty(factory.object_property(AtomicRole::top_object_role().iri()));
        let bottom_object_property =
            OPE::ObjectProperty(factory.object_property(AtomicRole::bottom_object_role().iri()));
        let top_data_property = factory.data_property(AtomicRole::top_data_role().iri());
        let bottom_data_property = factory.data_property(AtomicRole::bottom_data_role().iri());
        OWLNormalization {
            factory,
            axioms,
            first_replacement_index,
            definitions: HashMap::new(),
            definitions_for_negative_nominals: HashMap::new(),
            data_range_definitions: HashMap::new(),
            expression_manager: ExpressionManager::new(),
            top_object_property,
            bottom_object_property,
            top_data_property,
            bottom_data_property,
            has_rules: false,
            fresh_rule_individuals: 0,
            fresh_rule_data_properties: 0,
        }
    }

    /// Consumes the normalizer and returns the populated axioms.
    pub fn into_axioms(self) -> OWLAxioms {
        self.axioms
    }

    pub fn axioms(&self) -> &OWLAxioms {
        &self.axioms
    }

    /// The number of fresh "definition" concepts introduced so far
    /// (`OWLNormalization.m_definitions.size()`), used to seed the replacement
    /// index for the object-property inclusion manager.
    pub fn definitions_count(&self) -> usize {
        self.definitions.len()
    }

    pub fn process_ontology(&mut self, ontology: &SetOntology<A>) -> Result<(), String> {
        // Collect the full signature -- every class / object property / data
        // property / named individual that occurs anywhere in the ontology,
        // whether declared or merely used. Mirrors Java's
        // getClassesInSignature(Imports.INCLUDED) etc. in OWLNormalization.processOntology
        // (OWLNormalization.java:156-159): built-ins such as owl:Thing, owl:Nothing,
        // topObjectProperty, bottomObjectProperty are included unconditionally; downstream
        // consumers (BuiltInPropertyManager, DLOntology) already re-seed / deduplicate them.
        let mut walk = Walk::new(SignatureCollector::default());
        walk.set_ontology(ontology);
        let signature = walk.into_visit();
        for class in signature.classes {
            self.axioms.classes.insert(class);
        }
        for property in signature.object_properties {
            self.axioms.object_properties.insert(property);
        }
        for property in signature.data_properties {
            self.axioms.data_properties.insert(property);
        }
        for individual in signature.named_individuals {
            self.axioms.named_individuals.insert(individual);
        }
        let components: Vec<Component<A>> =
            ontology.iter().map(|ac| ac.component.clone()).collect();
        self.process_axioms(&components)
    }

    pub fn process_axioms(&mut self, components: &[Component<A>]) -> Result<(), String> {
        let mut state = AxiomState::default();
        for component in components {
            self.visit_axiom(component, &mut state)?;
        }
        // Normalize rules; this might add new concept and data range inclusions
        // in case a rule atom uses a complex concept or data range. We keep these
        // inclusions in the same work lists, applied later in `normalizeInclusions`.
        // (OWLNormalization.processAxioms: RuleNormalizer loop over m_rules.)
        self.normalize_rules(&mut state)?;
        self.normalize_inclusions(
            &mut state.class_expression_inclusions,
            &mut state.data_range_inclusions,
        )?;
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Helpers mirroring the static predicates and factory builders.
    // -----------------------------------------------------------------------

    fn owl_thing(&self) -> ClassExpr {
        CE::Class(self.factory.class(OWL_THING))
    }
    fn owl_nothing(&self) -> ClassExpr {
        CE::Class(self.factory.class(OWL_NOTHING))
    }
    fn top_datatype(&self) -> DataRangeExpr {
        DR::Datatype(self.factory.datatype(RDFS_LITERAL))
    }

    fn is_simple(description: &ClassExpr) -> bool {
        matches!(description, CE::Class(_))
            || matches!(description, CE::ObjectComplementOf(o) if matches!(**o, CE::Class(_)))
    }
    fn is_atomic(dr: &DataRangeExpr) -> bool {
        matches!(dr, DR::Datatype(_) | DR::DatatypeRestriction(..) | DR::DataOneOf(_))
    }
    fn is_negated_atomic(dr: &DataRangeExpr) -> bool {
        matches!(dr, DR::DataComplementOf(inner) if Self::is_atomic(inner))
    }
    pub(crate) fn is_literal(dr: &DataRangeExpr) -> bool {
        Self::is_atomic(dr) || Self::is_negated_atomic(dr)
    }
    fn is_nominal(description: &ClassExpr) -> bool {
        matches!(description, CE::ObjectOneOf(_))
    }
    fn is_negated_one_nominal(description: &ClassExpr) -> bool {
        matches!(description, CE::ObjectComplementOf(o)
            if matches!(&**o, CE::ObjectOneOf(inds) if inds.len() == 1))
    }

    fn is_owl_top_object_property(&self, ope: &OPE) -> bool {
        ope == &self.top_object_property
    }
    fn is_owl_bottom_object_property(&self, ope: &OPE) -> bool {
        ope == &self.bottom_object_property
    }
    fn is_owl_top_data_property(&self, dp: &DataProperty<A>) -> bool {
        dp == &self.top_data_property
    }
    fn is_owl_bottom_data_property(&self, dp: &DataProperty<A>) -> bool {
        dp == &self.bottom_data_property
    }

    fn positive(&self, description: &ClassExpr) -> ClassExpr {
        self.expression_manager
            .get_nnf(&self.expression_manager.get_simplified(description))
    }
    fn negative(&self, description: &ClassExpr) -> ClassExpr {
        self.expression_manager
            .get_complement_nnf(&self.expression_manager.get_simplified(description))
    }
    fn positive_dr(&self, data_range: &DataRangeExpr) -> DataRangeExpr {
        self.expression_manager
            .get_nnf_data(&self.expression_manager.get_simplified_data(data_range))
    }
    fn negative_dr(&self, data_range: &DataRangeExpr) -> DataRangeExpr {
        self.expression_manager
            .get_complement_nnf_data(&self.expression_manager.get_simplified_data(data_range))
    }

    fn add_object_inclusion(&mut self, sub: OPE, sup: OPE) {
        self.axioms.simple_object_property_inclusions.push([sub, sup]);
    }
    fn add_object_chain_inclusion(&mut self, sub: Vec<OPE>, sup: OPE) {
        self.axioms
            .complex_object_property_inclusions
            .push(ComplexObjectPropertyInclusion::new(sub, sup));
    }
    fn add_data_inclusion(&mut self, sub: DataProperty<A>, sup: DataProperty<A>) {
        self.axioms.data_property_inclusions.push([sub, sup]);
    }
    fn make_transitive(&mut self, ope: OPE) {
        self.axioms
            .complex_object_property_inclusions
            .push(ComplexObjectPropertyInclusion::transitive(ope));
    }
    fn note_object_property(&mut self, ope: &OPE) {
        self.axioms
            .object_properties_occurring_in_owl_axioms
            .insert(named_property(ope).clone());
    }

    // -----------------------------------------------------------------------
    // Definition introduction.
    // -----------------------------------------------------------------------

    fn pl_visit(&self, description: &ClassExpr) -> bool {
        match description {
            CE::Class(c) => !c.is_thing() && !c.is_nothing(),
            CE::ObjectIntersectionOf(operands) | CE::ObjectUnionOf(operands) => {
                operands.iter().any(|d| self.pl_visit(d))
            }
            CE::ObjectComplementOf(_) => false,
            CE::ObjectOneOf(_)
            | CE::ObjectSomeValuesFrom { .. }
            | CE::ObjectHasValue { .. }
            | CE::ObjectHasSelf(_)
            | CE::DataSomeValuesFrom { .. }
            | CE::DataAllValuesFrom { .. }
            | CE::DataHasValue { .. }
            | CE::DataMinCardinality { .. }
            | CE::DataMaxCardinality { .. }
            | CE::DataExactCardinality { .. } => true,
            CE::ObjectAllValuesFrom { bce, .. } => self.pl_visit(bce),
            CE::ObjectMinCardinality { n, .. } => *n > 0,
            CE::ObjectMaxCardinality { n, bce, .. } | CE::ObjectExactCardinality { n, bce, .. } => {
                if *n > 0 {
                    true
                } else {
                    self.pl_visit(&self.expression_manager.get_complement_nnf(bce))
                }
            }
        }
    }

    /// (definition, already_existed)
    fn get_definition_for(
        &mut self,
        description: &ClassExpr,
        force_positive: bool,
    ) -> (ClassExpr, bool) {
        let existing = self.definitions.get(description).cloned();
        match existing {
            Some(definition) if !(force_positive && !matches!(definition, CE::Class(_))) => {
                (definition, true)
            }
            _ => {
                let iri = format!(
                    "internal:def#{}",
                    self.definitions.len() + self.first_replacement_index
                );
                let mut definition = CE::Class(self.factory.class(iri));
                if !force_positive && !self.pl_visit(description) {
                    definition = CE::ObjectComplementOf(Box::new(definition));
                }
                self.definitions.insert(description.clone(), definition.clone());
                (definition, false)
            }
        }
    }

    // Used by the SWRL RuleNormalizer (RuleNormalizer.getClassFor).
    fn get_class_for(&mut self, description: &ClassExpr) -> (Class<A>, bool) {
        let (definition, already_exists) = self.get_definition_for(description, true);
        match definition {
            CE::Class(c) => (c, already_exists),
            _ => unreachable!("force_positive definition must be a class"),
        }
    }

    fn get_data_definition_for(&mut self, dr: &DataRangeExpr) -> (Datatype<A>, bool) {
        if let Some(existing) = self.data_range_definitions.get(dr).cloned() {
            (existing, true)
        } else {
            let iri = format!("internal:defdata#{}", self.data_range_definitions.len());
            let definition = self.factory.datatype(iri);
            self.data_range_definitions.insert(dr.clone(), definition.clone());
            (definition, false)
        }
    }

    fn get_definition_for_negative_nominal(&mut self, nominal: &ClassExpr) -> (Class<A>, bool) {
        if let Some(existing) = self.definitions_for_negative_nominals.get(nominal).cloned() {
            (existing, true)
        } else {
            let iri = format!("internal:nnq#{}", self.definitions_for_negative_nominals.len());
            let definition = self.factory.class(iri);
            self.definitions_for_negative_nominals
                .insert(nominal.clone(), definition.clone());
            (definition, false)
        }
    }
}

// ---------------------------------------------------------------------------
// Axiom visitor (the Java AxiomVisitor).
// ---------------------------------------------------------------------------

impl OWLNormalization {
    fn add_fact(&mut self, fact: Fact) {
        self.axioms.facts.push(fact);
    }

    fn check_top_data_property_use(&self, dp: &DataProperty<A>) -> Result<(), String> {
        if self.is_owl_top_data_property(dp) {
            Err("Error: In OWL 2 DL, owl:topDataProperty is only allowed to occur in the super \
                 property position of SubDataPropertyOf axioms, but the ontology contains an axiom \
                 that violates this condition."
                .to_string())
        } else {
            Ok(())
        }
    }

    fn is_anonymous_individual(individual: &Individual<A>) -> bool {
        matches!(individual, Individual::Anonymous(_))
    }

    fn visit_axiom(
        &mut self,
        component: &Component<A>,
        state: &mut AxiomState,
    ) -> Result<(), String> {
        match component {
            // Class axioms ---------------------------------------------------
            Component::SubClassOf(ax) => {
                let inclusion = vec![self.negative(&ax.sub), self.positive(&ax.sup)];
                state.class_expression_inclusions.push(inclusion);
            }
            Component::EquivalentClasses(ax) => {
                // HermiT iterates `axiom.getClassExpressions()`, a *Set*, so
                // duplicate operands collapse before the equivalence cycle is
                // built (otherwise a repeated operand yields a vacuous `C ⊑ C`).
                let mut classes: Vec<ClassExpr> = ax.0.clone();
                classes.sort();
                classes.dedup();
                if classes.len() > 1 {
                    for window in classes.windows(2) {
                        let inclusion = vec![self.negative(&window[0]), self.positive(&window[1])];
                        state.class_expression_inclusions.push(inclusion);
                    }
                    let last = self.negative(&classes[classes.len() - 1]);
                    let first = self.positive(&classes[0]);
                    state.class_expression_inclusions.push(vec![last, first]);
                }
            }
            Component::DisjointClasses(ax) => {
                // HermiT iterates `axiom.getClassExpressions()`, a *Set* -- so
                // duplicate operands are collapsed. Deduplicate before forming the
                // pairwise disjointness clauses; otherwise `DisjointClasses(C C D)`
                // yields the pair `{¬C, ¬C}` = `C ⊑ ⊥`, wrongly making every `C`
                // instance inconsistent. The size check is on the deduplicated set.
                let mut deduped: Vec<ClassExpr> = ax.0.clone();
                deduped.sort();
                deduped.dedup();
                if deduped.len() <= 1 {
                    return Err(
                        "A DisjointClasses axiom in OWL 2 DL must have at least two classes."
                            .to_string(),
                    );
                }
                let complements: Vec<ClassExpr> = deduped
                    .iter()
                    .map(|c| self.expression_manager.get_complement_nnf(c))
                    .collect();
                for i in 0..complements.len() {
                    for j in (i + 1)..complements.len() {
                        state
                            .class_expression_inclusions
                            .push(vec![complements[i].clone(), complements[j].clone()]);
                    }
                }
            }
            Component::DisjointUnion(ax) => {
                let owl_class = &ax.0;
                let class_expressions = &ax.1;
                // 1. C -> CE1 or ... or CEn, i.e. { not C, CE1, ..., CEn }.
                let mut inclusion: Vec<ClassExpr> = class_expressions.clone();
                inclusion.push(
                    self.expression_manager
                        .get_complement_nnf(&CE::Class(owl_class.clone())),
                );
                inclusion.sort();
                inclusion.dedup();
                state.class_expression_inclusions.push(inclusion);
                // 2. CEi -> C, i.e. { not CEi, C }.
                for description in class_expressions {
                    let neg = self.negative(description);
                    state
                        .class_expression_inclusions
                        .push(vec![neg, CE::Class(owl_class.clone())]);
                }
                // 3. CEi and CEj -> bottom for i < j. Deduplicate the disjuncts
                // first (HermiT's `getClassExpressions()` is a Set), so a repeated
                // disjunct cannot produce `CEi ⊓ CEi ⊑ ⊥` = `CEi ⊑ ⊥`.
                let mut deduped_disjuncts: Vec<ClassExpr> = class_expressions.clone();
                deduped_disjuncts.sort();
                deduped_disjuncts.dedup();
                let complements: Vec<ClassExpr> = deduped_disjuncts
                    .iter()
                    .map(|c| self.expression_manager.get_complement_nnf(c))
                    .collect();
                for i in 0..complements.len() {
                    for j in (i + 1)..complements.len() {
                        state
                            .class_expression_inclusions
                            .push(vec![complements[i].clone(), complements[j].clone()]);
                    }
                }
            }

            // Object property axioms ----------------------------------------
            Component::SubObjectPropertyOf(ax) => {
                let sup = &ax.sup;
                match &ax.sub {
                    SOPE::ObjectPropertyExpression(sub) => {
                        if !self.is_owl_bottom_object_property(sub)
                            && !self.is_owl_top_object_property(sup)
                        {
                            self.add_object_inclusion(sub.clone(), sup.clone());
                        }
                        self.note_object_property(sub);
                        self.note_object_property(sup);
                    }
                    SOPE::ObjectPropertyChain(chain) => {
                        let contains_bottom =
                            chain.iter().any(|p| self.is_owl_bottom_object_property(p));
                        if !contains_bottom && !self.is_owl_top_object_property(sup) {
                            match chain.len() {
                                1 => self.add_object_inclusion(chain[0].clone(), sup.clone()),
                                2 if &chain[0] == sup && &chain[1] == sup => {
                                    self.make_transitive(sup.clone())
                                }
                                0 => {
                                    return Err("Error: an empty property chain is not allowed."
                                        .to_string())
                                }
                                _ => self.add_object_chain_inclusion(chain.clone(), sup.clone()),
                            }
                        }
                        for ope in chain {
                            self.note_object_property(ope);
                        }
                        self.note_object_property(sup);
                    }
                }
            }
            Component::EquivalentObjectProperties(ax) => {
                // Java iterates `axiom.getProperties()`, a *Set*: duplicate
                // operands collapse before the equivalence cycle is built.
                let mut properties: Vec<_> = ax.0.clone();
                properties.sort();
                properties.dedup();
                if properties.len() > 1 {
                    for window in properties.windows(2) {
                        self.add_object_inclusion(window[0].clone(), window[1].clone());
                    }
                    self.add_object_inclusion(
                        properties[properties.len() - 1].clone(),
                        properties[0].clone(),
                    );
                }
                for ope in &properties {
                    self.note_object_property(ope);
                }
            }
            Component::DisjointObjectProperties(ax) => {
                // Java reads axiom.getProperties() which is a Set, so duplicates are
                // removed before pairwise i<j clausification; mirror that here.
                let mut properties = ax.0.clone();
                for ope in &properties {
                    self.note_object_property(ope);
                }
                properties.sort();
                properties.dedup();
                self.axioms.disjoint_object_properties.push(properties);
            }
            Component::InverseObjectProperties(ax) => {
                // horned-owl models both operands as ObjectPropertyExpression already.
                let first = ax.0.clone();
                let second = ax.1.clone();
                self.add_object_inclusion(first.clone(), inverse_property(&second));
                self.add_object_inclusion(second.clone(), inverse_property(&first));
                self.note_object_property(&first);
                self.note_object_property(&second);
            }
            Component::ObjectPropertyDomain(ax) => {
                let all_property_nothing = CE::ObjectAllValuesFrom {
                    ope: ax.ope.clone(),
                    bce: Box::new(self.owl_nothing()),
                };
                let domain = self.positive(&ax.ce);
                state
                    .class_expression_inclusions
                    .push(vec![domain, all_property_nothing]);
                self.note_object_property(&ax.ope);
            }
            Component::ObjectPropertyRange(ax) => {
                let range = self.positive(&ax.ce);
                let all_property_range = CE::ObjectAllValuesFrom {
                    ope: ax.ope.clone(),
                    bce: Box::new(range),
                };
                state.class_expression_inclusions.push(vec![all_property_range]);
            }
            Component::FunctionalObjectProperty(ax) => {
                let restriction = CE::ObjectMaxCardinality {
                    n: 1,
                    ope: ax.0.clone(),
                    bce: Box::new(self.owl_thing()),
                };
                state.class_expression_inclusions.push(vec![restriction]);
                self.note_object_property(&ax.0);
            }
            Component::InverseFunctionalObjectProperty(ax) => {
                let restriction = CE::ObjectMaxCardinality {
                    n: 1,
                    ope: inverse_property(&ax.0),
                    bce: Box::new(self.owl_thing()),
                };
                state.class_expression_inclusions.push(vec![restriction]);
                self.note_object_property(&ax.0);
            }
            Component::ReflexiveObjectProperty(ax) => {
                self.axioms.reflexive_object_properties.insert(ax.0.clone());
                self.note_object_property(&ax.0);
            }
            Component::IrreflexiveObjectProperty(ax) => {
                self.axioms.irreflexive_object_properties.insert(ax.0.clone());
                self.note_object_property(&ax.0);
            }
            Component::SymmetricObjectProperty(ax) => {
                self.add_object_inclusion(ax.0.clone(), inverse_property(&ax.0));
                self.note_object_property(&ax.0);
            }
            Component::AsymmetricObjectProperty(ax) => {
                self.axioms.asymmetric_object_properties.insert(ax.0.clone());
                self.note_object_property(&ax.0);
            }
            Component::TransitiveObjectProperty(ax) => {
                self.make_transitive(ax.0.clone());
                self.note_object_property(&ax.0);
            }

            // Data property axioms ------------------------------------------
            Component::SubDataPropertyOf(ax) => {
                self.check_top_data_property_use(&ax.sub)?;
                if !self.is_owl_bottom_data_property(&ax.sub)
                    && !self.is_owl_top_data_property(&ax.sup)
                {
                    self.add_data_inclusion(ax.sub.clone(), ax.sup.clone());
                }
            }
            Component::EquivalentDataProperties(ax) => {
                // Java iterates `axiom.getProperties()`, a *Set*: duplicate
                // operands collapse before the equivalence cycle is built.
                let mut properties: Vec<_> = ax.0.clone();
                properties.sort();
                properties.dedup();
                for dp in &properties {
                    self.check_top_data_property_use(dp)?;
                }
                if properties.len() > 1 {
                    for window in properties.windows(2) {
                        self.add_data_inclusion(window[0].clone(), window[1].clone());
                    }
                    self.add_data_inclusion(
                        properties[properties.len() - 1].clone(),
                        properties[0].clone(),
                    );
                }
            }
            Component::DisjointDataProperties(ax) => {
                // Java reads axiom.getProperties() which is a Set, so duplicates are
                // removed before pairwise i<j clausification; mirror that here.
                let mut properties = ax.0.clone();
                for dp in &properties {
                    self.check_top_data_property_use(dp)?;
                }
                properties.sort();
                properties.dedup();
                self.axioms.disjoint_data_properties.push(properties);
            }
            Component::DataPropertyDomain(ax) => {
                self.check_top_data_property_use(&ax.dp)?;
                let data_nothing = DR::DataComplementOf(Box::new(self.top_datatype()));
                let all_property_data_nothing = CE::DataAllValuesFrom {
                    dp: ax.dp.clone(),
                    dr: data_nothing,
                };
                let domain = self.positive(&ax.ce);
                state
                    .class_expression_inclusions
                    .push(vec![domain, all_property_data_nothing]);
            }
            Component::DataPropertyRange(ax) => {
                self.check_top_data_property_use(&ax.dp)?;
                let range = self.positive_dr(&ax.dr);
                let all_property_range = CE::DataAllValuesFrom {
                    dp: ax.dp.clone(),
                    dr: range,
                };
                state.class_expression_inclusions.push(vec![all_property_range]);
            }
            Component::FunctionalDataProperty(ax) => {
                self.check_top_data_property_use(&ax.0)?;
                let restriction = CE::DataMaxCardinality {
                    n: 1,
                    dp: ax.0.clone(),
                    dr: self.top_datatype(),
                };
                state.class_expression_inclusions.push(vec![restriction]);
            }

            // Assertions ----------------------------------------------------
            Component::SameIndividual(ax) => {
                if ax.0.iter().any(Self::is_anonymous_individual) {
                    return Err("SameIndividual with anonymous individuals is not allowed.".into());
                }
                self.add_fact(Fact::SameIndividual(ax.0.clone()));
            }
            Component::DifferentIndividuals(ax) => {
                if ax.0.iter().any(Self::is_anonymous_individual) {
                    return Err(
                        "DifferentIndividuals with anonymous individuals is not allowed.".into(),
                    );
                }
                self.add_fact(Fact::DifferentIndividuals(ax.0.clone()));
            }
            Component::ClassAssertion(ax) => {
                let individual = &ax.i;
                if let CE::DataHasValue { dp, l } = &ax.ce {
                    self.add_fact(Fact::DataPropertyAssertion {
                        dp: dp.clone(),
                        from: individual.clone(),
                        to: l.clone(),
                    });
                    return Ok(());
                }
                if let CE::DataSomeValuesFrom { dp, dr } = &ax.ce {
                    if let DR::DataOneOf(values) = dr {
                        if values.len() == 1 {
                            self.add_fact(Fact::DataPropertyAssertion {
                                dp: dp.clone(),
                                from: individual.clone(),
                                to: values[0].clone(),
                            });
                            return Ok(());
                        }
                    }
                }
                let mut class_expression = self.positive(&ax.ce);
                if !Self::is_simple(&class_expression) {
                    let (definition, already_exists) =
                        self.get_definition_for(&class_expression, false);
                    if !already_exists {
                        let neg = self.negative(&definition);
                        state
                            .class_expression_inclusions
                            .push(vec![neg, class_expression.clone()]);
                    }
                    class_expression = definition;
                }
                self.add_fact(Fact::ClassAssertion {
                    class_expression,
                    individual: individual.clone(),
                });
            }
            Component::ObjectPropertyAssertion(ax) => {
                self.add_fact(Fact::ObjectPropertyAssertion {
                    ope: ax.ope.clone(),
                    from: ax.from.clone(),
                    to: ax.to.clone(),
                });
                self.note_object_property(&ax.ope);
            }
            Component::NegativeObjectPropertyAssertion(ax) => {
                if Self::is_anonymous_individual(&ax.from) || Self::is_anonymous_individual(&ax.to) {
                    return Err(
                        "NegativeObjectPropertyAssertion with anonymous individuals is not allowed."
                            .into(),
                    );
                }
                self.add_fact(Fact::NegativeObjectPropertyAssertion {
                    ope: ax.ope.clone(),
                    from: ax.from.clone(),
                    to: ax.to.clone(),
                });
                self.note_object_property(&ax.ope);
            }
            Component::DataPropertyAssertion(ax) => {
                self.check_top_data_property_use(&ax.dp)?;
                self.add_fact(Fact::DataPropertyAssertion {
                    dp: ax.dp.clone(),
                    from: ax.from.clone(),
                    to: ax.to.clone(),
                });
            }
            Component::NegativeDataPropertyAssertion(ax) => {
                self.check_top_data_property_use(&ax.dp)?;
                if Self::is_anonymous_individual(&ax.from) {
                    return Err(
                        "NegativeDataPropertyAssertion with anonymous individuals is not allowed."
                            .into(),
                    );
                }
                self.add_fact(Fact::NegativeDataPropertyAssertion {
                    dp: ax.dp.clone(),
                    from: ax.from.clone(),
                    to: ax.to.clone(),
                });
            }

            // Datatype definitions ------------------------------------------
            Component::DatatypeDefinition(ax) => {
                self.axioms
                    .defined_datatype_iris
                    .insert((*ax.kind.0).to_string());
                let datatype = DR::Datatype(ax.kind.clone());
                let inc1 = vec![self.negative_dr(&datatype), self.positive_dr(&ax.range)];
                state.data_range_inclusions.push(inc1);
                let inc2 = vec![self.negative_dr(&ax.range), self.positive_dr(&datatype)];
                state.data_range_inclusions.push(inc2);
            }

            // Keys ----------------------------------------------------------
            Component::HasKey(ax) => {
                use horned_owl::model::PropertyExpression as PE;
                for pe in &ax.vpe {
                    if let PE::DataProperty(dp) = pe {
                        self.check_top_data_property_use(dp)?;
                    }
                }
                let mut description = self.positive(&ax.ce);
                if !Self::is_simple(&description) {
                    let (definition, already_exists) = self.get_definition_for(&description, false);
                    if !already_exists {
                        let neg = self.negative(&definition);
                        state
                            .class_expression_inclusions
                            .push(vec![neg, description.clone()]);
                    }
                    description = definition;
                }
                self.axioms.has_keys.push(HasKeyAxiom {
                    class_expression: description,
                    property_expressions: ax.vpe.clone(),
                });
                for pe in &ax.vpe {
                    if let PE::ObjectPropertyExpression(ope) = pe {
                        self.note_object_property(ope);
                    }
                }
            }

            // Rules ---------------------------------------------------------
            Component::Rule(rule) => {
                // Port of AxiomVisitor.visit(SWRLRule). owl:topDataProperty may
                // only occur as the super-property of SubDataPropertyOf, so a
                // data-property atom using it is rejected. An empty-body rule is
                // an unconditional fact (Rule2FactConverter); a rule with a body
                // is collected for the RuleNormalizer.
                for atom in rule.body.iter().chain(rule.head.iter()) {
                    if let SwrlAtomKind::DataPropertyAtom { pred, .. } = atom {
                        self.check_top_data_property_use(pred)?;
                    }
                }
                self.has_rules = true;
                if rule.body.is_empty() {
                    self.fresh_rule_individuals = 0;
                    self.fresh_rule_data_properties = 0;
                    for head_atom in &rule.head {
                        self.rule_to_fact(head_atom, state)?;
                    }
                } else {
                    state.rules.push((rule.body.clone(), rule.head.clone()));
                }
            }

            // Declarations, annotations, ontology metadata: no logical effect.
            _ => {}
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// SWRL rule normalization (the Java Rule2FactConverter and RuleNormalizer
// inner classes).
// ---------------------------------------------------------------------------

impl OWLNormalization {
    fn require_named(individual: &Individ) -> Result<NamedIndividual<A>, String> {
        match individual {
            Individual::Named(n) => Ok(n.clone()),
            Individual::Anonymous(_) => Err(
                "A SWRL rule contains a fact with an anonymous individual, which is not allowed."
                    .into(),
            ),
        }
    }

    fn fresh_rule_individual(&mut self) -> NamedIndividual<A> {
        let ind = self
            .factory
            .named_individual(format!("internal:nom#swrlfact{}", self.fresh_rule_individuals));
        self.fresh_rule_individuals += 1;
        self.axioms.named_individuals.insert(ind.clone());
        ind
    }

    fn fresh_rule_data_property(&mut self) -> DataProperty<A> {
        self.fresh_rule_data_properties += 1;
        self.factory
            .data_property(format!("internal:freshDP#{}", self.fresh_rule_data_properties))
    }

    /// Port of `OWLNormalization.Rule2FactConverter`: a head atom of an
    /// empty-body rule becomes an ABox fact. Head atoms must be ground (their
    /// arguments must be individuals/literals, not variables that never occur in
    /// the body).
    fn rule_to_fact(&mut self, atom: &SwrlAtom, state: &mut AxiomState) -> Result<(), String> {
        match atom {
            SwrlAtomKind::ClassAtom { pred, arg } => {
                // visit(SWRLClassAtom)
                let ind = match arg {
                    IArgument::Individual(i) => Self::require_named(i)?,
                    IArgument::Variable(_) => {
                        return Err("A SWRL rule contains a head atom with a variable that does \
                                    not occur in the body."
                            .into())
                    }
                };
                let mut class_expression = pred.clone();
                if !Self::is_simple(&class_expression) {
                    let (definition, already_exists) =
                        self.get_definition_for(&class_expression, false);
                    if !already_exists {
                        let neg = self.negative(&definition);
                        state
                            .class_expression_inclusions
                            .push(vec![neg, class_expression.clone()]);
                    }
                    class_expression = definition;
                }
                self.add_fact(Fact::ClassAssertion {
                    class_expression,
                    individual: Individual::Named(ind),
                });
            }
            SwrlAtomKind::ObjectPropertyAtom { pred, args } => {
                // visit(SWRLObjectPropertyAtom)
                let first = match &args.0 {
                    IArgument::Individual(i) => Self::require_named(i)?,
                    IArgument::Variable(_) => return Err(Self::var_head_error()),
                };
                let second = match &args.1 {
                    IArgument::Individual(i) => Self::require_named(i)?,
                    IArgument::Variable(_) => return Err(Self::var_head_error()),
                };
                // For an inverse property, the named property is asserted with
                // the arguments swapped.
                match pred {
                    OPE::ObjectProperty(op) => {
                        self.add_fact(Fact::ObjectPropertyAssertion {
                            ope: OPE::ObjectProperty(op.clone()),
                            from: Individual::Named(first),
                            to: Individual::Named(second),
                        });
                    }
                    OPE::InverseObjectProperty(op) => {
                        self.add_fact(Fact::ObjectPropertyAssertion {
                            ope: OPE::ObjectProperty(op.clone()),
                            from: Individual::Named(second),
                            to: Individual::Named(first),
                        });
                    }
                }
                // `Rule2FactConverter.visit(SWRLObjectPropertyAtom)` only emits the
                // fact; unlike the ABox `visit(OWLObjectPropertyAssertionAxiom)` it
                // does NOT record the property in objectPropertiesOccurringInOWLAxioms.
            }
            SwrlAtomKind::DataPropertyAtom { args, .. } => {
                // visit(SWRLDataPropertyAtom). Java requires the subject to be an
                // SWRLIndividualArgument and the object a SWRLLiteralArgument,
                // producing DataPropertyAssertion(dp, individual, literal).
                //
                // horned-owl models BOTH data-property arguments as `DArgument`s,
                // which can only be a literal or a variable -- never an
                // individual. An empty-body rule fact thus cannot carry the named
                // individual subject HermiT requires, so this shape is not
                // representable in horned-owl's SWRL model. A variable in a
                // body-less rule head never occurs in the body, which HermiT
                // already rejects.
                let _ = args;
                return Err(
                    "A SWRL fact (empty-body rule) with a data-property atom is not representable: \
                     horned-owl models the data-property subject as a literal/variable rather than \
                     an individual."
                        .into(),
                );
            }
            SwrlAtomKind::SameIndividualAtom(a1, a2) => {
                let i1 = Self::iarg_named(a1)?;
                let i2 = Self::iarg_named(a2)?;
                // visit(SWRLSameIndividualAtom) gathers the arguments into a Set
                // before building the axiom, so identical arguments collapse.
                let mut inds = vec![Individual::Named(i1.clone())];
                if i2 != i1 {
                    inds.push(Individual::Named(i2));
                }
                self.add_fact(Fact::SameIndividual(inds));
            }
            SwrlAtomKind::DifferentIndividualsAtom(a1, a2) => {
                let i1 = Self::iarg_named(a1)?;
                let i2 = Self::iarg_named(a2)?;
                // visit(SWRLDifferentIndividualsAtom) likewise dedups via a Set: a
                // self-`differentFrom` yields a singleton (no inequality / no clash).
                let mut inds = vec![Individual::Named(i1.clone())];
                if i2 != i1 {
                    inds.push(Individual::Named(i2));
                }
                self.add_fact(Fact::DifferentIndividuals(inds));
            }
            SwrlAtomKind::DataRangeAtom { pred, arg } => {
                // visit(SWRLDataRangeAtom): dr(literal) becomes
                //   ClassAssertion(DataSomeValuesFrom(freshDP DataOneOf(lit)) freshInd)
                //   plus  Thing -> forall freshDP.dr
                let lit = match arg {
                    DArgument::Literal(l) => l.clone(),
                    DArgument::Variable(_) => {
                        return Err("A SWRL rule contains a head atom with a variable that does \
                                    not occur in the body."
                            .into())
                    }
                };
                let fresh_individual = self.fresh_rule_individual();
                let fresh_dp = self.fresh_rule_data_property();
                let some = CE::DataSomeValuesFrom {
                    dp: fresh_dp.clone(),
                    dr: DR::DataOneOf(vec![lit]),
                };
                let (definition, already_exists) = self.get_definition_for(&some, false);
                if !already_exists {
                    let neg = self.negative(&definition);
                    state
                        .class_expression_inclusions
                        .push(vec![neg, some.clone()]);
                }
                self.add_fact(Fact::ClassAssertion {
                    class_expression: definition,
                    individual: Individual::Named(fresh_individual),
                });
                state.class_expression_inclusions.push(vec![CE::DataAllValuesFrom {
                    dp: fresh_dp,
                    dr: pred.clone(),
                }]);
            }
            SwrlAtomKind::BuiltInAtom { .. } => {
                return Err(
                    "Error: A rule uses built-in atoms, but built-in atoms are not supported yet."
                        .into(),
                )
            }
        }
        Ok(())
    }

    fn iarg_named(arg: &IArgument<A>) -> Result<NamedIndividual<A>, String> {
        match arg {
            IArgument::Individual(i) => Self::require_named(i),
            IArgument::Variable(_) => Err(Self::var_head_error()),
        }
    }

    fn var_head_error() -> String {
        "A SWRL rule contains a head atom with a variable that does not occur in the body.".into()
    }

    /// Port of `OWLNormalization.RuleNormalizer`. For each rule, the conjunctive
    /// head is split into one DisjunctiveRule per head atom (Lloyd-Topor), every
    /// individual argument is replaced by a fresh variable bound to an
    /// `ObjectOneOf` body class atom, body `SameIndividualAtom`s become variable
    /// unifications, complex class atoms get fresh definitions, and the
    /// arguments of object-property atoms over inverse properties are swapped.
    fn normalize_rules(&mut self, state: &mut AxiomState) -> Result<(), String> {
        let raw_rules = std::mem::take(&mut state.rules);
        for (body, head) in raw_rules {
            for head_atom in &head {
                let mut nz = RuleNormalizerState::default();
                // Initialize body with all atoms; head with just this atom.
                let mut body_work: Vec<SwrlAtom> = body.clone();
                let mut head_work: Vec<SwrlAtom> = vec![head_atom.clone()];

                // First process body SameIndividualAtoms to set up variable
                // unifications and individual-to-variable mappings.
                body_work.retain(|atom| {
                    !matches!(atom, SwrlAtomKind::SameIndividualAtom(..))
                });
                for atom in &body {
                    if let SwrlAtomKind::SameIndividualAtom(a1, a2) = atom {
                        let variable1 = self.rn_variable_for(&mut nz, a1, &mut body_work)?;
                        match a2 {
                            IArgument::Variable(v2) => {
                                nz.variable_representative.insert(v2.clone(), variable1);
                            }
                            IArgument::Individual(individual) => {
                                let named = Self::require_named(individual)?;
                                nz.individuals_to_variables
                                    .insert(named.clone(), variable1.clone());
                                body_work.push(SwrlAtomKind::ClassAtom {
                                    pred: CE::ObjectOneOf(vec![Individual::Named(named)]),
                                    arg: IArgument::Variable(variable1),
                                });
                            }
                        }
                    }
                }

                // Process head atoms (positive); may grow body_work.
                let mut i = 0;
                while i < head_work.len() {
                    let atom = head_work[i].clone();
                    i += 1;
                    self.rn_visit_atom(&mut nz, &atom, true, &mut body_work, &mut head_work, state)?;
                }
                // Process body atoms (negative).
                let mut j = 0;
                while j < body_work.len() {
                    let atom = body_work[j].clone();
                    j += 1;
                    self.rn_visit_atom(&mut nz, &atom, false, &mut body_work, &mut head_work, state)?;
                }

                if !nz
                    .head_data_range_variables
                    .iter()
                    .all(|v| nz.body_data_range_variables.contains(v))
                {
                    return Err("A SWRL rule contains data range variables in the head, but not \
                                in the body, and this is not supported."
                        .into());
                }
                self.axioms.rules.push(crate::structural::owl_axioms::DisjunctiveRule::new(
                    nz.normalized_body_atoms.atoms.clone(),
                    nz.normalized_head_atoms.atoms.clone(),
                ));
            }
        }
        Ok(())
    }

    fn rn_fresh_variable(&self, nz: &mut RuleNormalizerState) -> SwrlVariable<A> {
        let variable = self
            .factory
            .variable(format!("internal:swrl#{}", nz.new_variable_index));
        nz.new_variable_index += 1;
        variable
    }

    /// Port of `RuleNormalizer.getVariableFor`. An individual argument is mapped
    /// to a fresh variable, recording an `ObjectOneOf` body class atom binding
    /// it. The variable representative (from SameIndividual unification) is then
    /// applied.
    fn rn_variable_for(
        &self,
        nz: &mut RuleNormalizerState,
        term: &IArgument<A>,
        body_work: &mut Vec<SwrlAtom>,
    ) -> Result<SwrlVariable<A>, String> {
        let variable = match term {
            IArgument::Individual(individual) => {
                let named = Self::require_named(individual)?;
                if let Some(existing) = nz.individuals_to_variables.get(&named) {
                    existing.clone()
                } else {
                    let fresh = self.rn_fresh_variable(nz);
                    nz.individuals_to_variables.insert(named.clone(), fresh.clone());
                    body_work.push(SwrlAtomKind::ClassAtom {
                        pred: CE::ObjectOneOf(vec![Individual::Named(named)]),
                        arg: IArgument::Variable(fresh.clone()),
                    });
                    fresh
                }
            }
            IArgument::Variable(v) => v.clone(),
        };
        Ok(nz
            .variable_representative
            .get(&variable)
            .cloned()
            .unwrap_or(variable))
    }

    /// Port of the per-atom `RuleNormalizer.visit(...)` methods. `head_work` and
    /// `body_work` may grow (e.g. a data property with a literal object pushes a
    /// `DataHasValue` class atom).
    fn rn_visit_atom(
        &mut self,
        nz: &mut RuleNormalizerState,
        atom: &SwrlAtom,
        is_positive: bool,
        body_work: &mut Vec<SwrlAtom>,
        head_work: &mut Vec<SwrlAtom>,
        state: &mut AxiomState,
    ) -> Result<(), String> {
        match atom {
            SwrlAtomKind::ClassAtom { pred, arg } => {
                let simplified = self
                    .expression_manager
                    .get_simplified(&self.expression_manager.get_nnf(pred));
                let variable = self.rn_variable_for(nz, arg, body_work)?;
                let is_named_class = matches!(simplified, CE::Class(_));
                if is_positive {
                    if is_named_class {
                        nz.normalized_head_atoms.insert(SwrlAtomKind::ClassAtom {
                            pred: simplified,
                            arg: IArgument::Variable(variable),
                        });
                    } else {
                        let (definition, already_exists) = self.get_class_for(pred);
                        if !already_exists {
                            let neg = self.negative(&CE::Class(definition.clone()));
                            state
                                .class_expression_inclusions
                                .push(vec![neg, pred.clone()]);
                        }
                        nz.normalized_head_atoms.insert(SwrlAtomKind::ClassAtom {
                            pred: CE::Class(definition),
                            arg: IArgument::Variable(variable),
                        });
                    }
                } else if is_named_class {
                    nz.normalized_body_atoms.insert(SwrlAtomKind::ClassAtom {
                        pred: simplified,
                        arg: IArgument::Variable(variable),
                    });
                } else {
                    let (definition, already_exists) = self.get_class_for(pred);
                    if !already_exists {
                        let neg = self.negative(pred);
                        state
                            .class_expression_inclusions
                            .push(vec![neg, CE::Class(definition.clone())]);
                    }
                    nz.normalized_body_atoms.insert(SwrlAtomKind::ClassAtom {
                        pred: CE::Class(definition),
                        arg: IArgument::Variable(variable),
                    });
                }
            }
            SwrlAtomKind::DataRangeAtom { pred, arg } => {
                let variable = match arg {
                    DArgument::Variable(v) => v.clone(),
                    DArgument::Literal(_) => {
                        return Err("A SWRL rule contains a data range with an argument that is \
                                    not a literal, and such rules are not supported."
                            .into())
                    }
                };
                let mut dr = pred.clone();
                if !is_positive {
                    dr = DR::DataComplementOf(Box::new(dr));
                }
                dr = self
                    .expression_manager
                    .get_nnf_data(&self.expression_manager.get_simplified_data(&dr));
                if matches!(dr, DR::DataIntersectionOf(_) | DR::DataUnionOf(_)) {
                    let (definition, already_exists) = self.get_data_definition_for(&dr);
                    if !already_exists {
                        let neg = self.negative_dr(&DR::Datatype(definition.clone()));
                        state.data_range_inclusions.push(vec![neg, dr.clone()]);
                    }
                    dr = DR::Datatype(definition);
                }
                nz.normalized_head_atoms.insert(SwrlAtomKind::DataRangeAtom {
                    pred: dr,
                    arg: DArgument::Variable(variable.clone()),
                });
                nz.head_data_range_variables.insert(variable);
            }
            SwrlAtomKind::ObjectPropertyAtom { pred, args } => {
                let (op, variable1, variable2) = match pred {
                    OPE::ObjectProperty(op) => {
                        let v1 = self.rn_variable_for(nz, &args.0, body_work)?;
                        let v2 = self.rn_variable_for(nz, &args.1, body_work)?;
                        (op.clone(), v1, v2)
                    }
                    OPE::InverseObjectProperty(op) => {
                        // Anonymous property: swap the arguments, use named prop.
                        let v1 = self.rn_variable_for(nz, &args.1, body_work)?;
                        let v2 = self.rn_variable_for(nz, &args.0, body_work)?;
                        (op.clone(), v1, v2)
                    }
                };
                let new_atom = SwrlAtomKind::ObjectPropertyAtom {
                    pred: OPE::ObjectProperty(op),
                    args: (
                        IArgument::Variable(variable1),
                        IArgument::Variable(variable2),
                    ),
                };
                if is_positive {
                    nz.normalized_head_atoms.insert(new_atom);
                } else {
                    nz.normalized_body_atoms.insert(new_atom);
                }
            }
            SwrlAtomKind::DataPropertyAtom { pred, args } => {
                let variable1 = match &args.0 {
                    DArgument::Variable(v) => nz
                        .variable_representative
                        .get(v)
                        .cloned()
                        .unwrap_or_else(|| v.clone()),
                    DArgument::Literal(_) => {
                        // Java models the subject as an SWRLIArgument; a literal
                        // subject is not representable in OWL-API. In horned-owl
                        // both args are DArguments, so a literal subject would be
                        // ill-formed input. Treat it as unsupported.
                        return Err("A SWRL rule contains a data property atom whose subject is \
                                    a literal, which is not allowed."
                            .into());
                    }
                };
                match &args.1 {
                    DArgument::Variable(v2) => {
                        let variable2 = nz
                            .variable_representative
                            .get(v2)
                            .cloned()
                            .unwrap_or_else(|| v2.clone());
                        if is_positive {
                            nz.normalized_head_atoms.insert(SwrlAtomKind::DataPropertyAtom {
                                pred: pred.clone(),
                                args: (
                                    DArgument::Variable(variable1),
                                    DArgument::Variable(variable2.clone()),
                                ),
                            });
                            nz.head_data_range_variables.insert(variable2);
                        } else if nz.body_data_range_variables.insert(variable2.clone()) {
                            nz.normalized_body_atoms.insert(SwrlAtomKind::DataPropertyAtom {
                                pred: pred.clone(),
                                args: (
                                    DArgument::Variable(variable1),
                                    DArgument::Variable(variable2),
                                ),
                            });
                        } else {
                            // The data-range variable already appears: use a
                            // fresh variable and require the two to differ.
                            let fresh = self.rn_fresh_variable(nz);
                            nz.normalized_body_atoms.insert(SwrlAtomKind::DataPropertyAtom {
                                pred: pred.clone(),
                                args: (
                                    DArgument::Variable(variable1),
                                    DArgument::Variable(fresh.clone()),
                                ),
                            });
                            nz.normalized_head_atoms.insert(
                                SwrlAtomKind::DifferentIndividualsAtom(
                                    IArgument::Variable(variable2),
                                    IArgument::Variable(fresh),
                                ),
                            );
                        }
                    }
                    DArgument::Literal(lit) => {
                        // p(x, "lit") becomes a DataHasValue class atom on x,
                        // re-queued into the appropriate work list.
                        let new_atom = SwrlAtomKind::ClassAtom {
                            pred: CE::DataHasValue {
                                dp: pred.clone(),
                                l: lit.clone(),
                            },
                            arg: IArgument::Variable(variable1),
                        };
                        if is_positive {
                            head_work.push(new_atom);
                        } else {
                            body_work.push(new_atom);
                        }
                    }
                }
            }
            SwrlAtomKind::SameIndividualAtom(a1, a2) => {
                if is_positive {
                    let v1 = self.rn_variable_for(nz, a1, body_work)?;
                    let v2 = self.rn_variable_for(nz, a2, body_work)?;
                    nz.normalized_head_atoms.insert(SwrlAtomKind::SameIndividualAtom(
                        IArgument::Variable(v1),
                        IArgument::Variable(v2),
                    ));
                } else {
                    // Body SameIndividualAtoms were already consumed for variable
                    // unification before this loop, so reaching one here is a bug.
                    return Err("Internal error: this SWRLSameIndividualAtom should have been \
                                processed earlier."
                        .into());
                }
            }
            SwrlAtomKind::DifferentIndividualsAtom(a1, a2) => {
                let v1 = self.rn_variable_for(nz, a1, body_work)?;
                let v2 = self.rn_variable_for(nz, a2, body_work)?;
                if is_positive {
                    nz.normalized_head_atoms.insert(SwrlAtomKind::DifferentIndividualsAtom(
                        IArgument::Variable(v1),
                        IArgument::Variable(v2),
                    ));
                } else {
                    // not(x != y) in the body means x = y in the head.
                    nz.normalized_head_atoms.insert(SwrlAtomKind::SameIndividualAtom(
                        IArgument::Variable(v1),
                        IArgument::Variable(v2),
                    ));
                }
            }
            SwrlAtomKind::BuiltInAtom { .. } => {
                return Err(
                    "A SWRL rule uses a built-in atom, but built-in atoms are not supported yet."
                        .into(),
                )
            }
        }
        Ok(())
    }
}

/// An insertion-ordered set of SWRL atoms (the Java `m_normalizedBodyAtoms` /
/// `m_normalizedHeadAtoms` are `HashSet`s; we keep insertion order for
/// deterministic output but match the Java set semantics on membership).
#[derive(Default)]
struct AtomSet {
    atoms: Vec<SwrlAtom>,
}

impl AtomSet {
    fn insert(&mut self, atom: SwrlAtom) {
        if !self.atoms.contains(&atom) {
            self.atoms.push(atom);
        }
    }
}

/// The mutable per-rule state of `OWLNormalization.RuleNormalizer`.
#[derive(Default)]
struct RuleNormalizerState {
    normalized_body_atoms: AtomSet,
    normalized_head_atoms: AtomSet,
    variable_representative: HashMap<SwrlVariable<A>, SwrlVariable<A>>,
    individuals_to_variables: HashMap<NamedIndividual<A>, SwrlVariable<A>>,
    body_data_range_variables: HashSet<SwrlVariable<A>>,
    head_data_range_variables: HashSet<SwrlVariable<A>>,
    new_variable_index: u32,
}

// ---------------------------------------------------------------------------
// Inclusion normalization (the Java normalizeInclusions plus the
// ClassExpressionNormalizer and DataRangeNormalizer visitors).
// ---------------------------------------------------------------------------

impl OWLNormalization {
    fn normalize_inclusions(
        &mut self,
        inclusions: &mut Vec<Vec<ClassExpr>>,
        data_range_inclusions: &mut Vec<Vec<DataRangeExpr>>,
    ) -> Result<(), String> {
        // Class expression inclusions.
        while let Some(entry) = inclusions.pop() {
            let union = CE::ObjectUnionOf(entry);
            let simplified = self
                .expression_manager
                .get_nnf(&self.expression_manager.get_simplified(&union));
            if matches!(&simplified, CE::Class(c) if c.is_thing()) {
                continue;
            }
            match simplified {
                CE::ObjectUnionOf(mut descriptions) => {
                    if !distribute_union_over_and(&mut descriptions, inclusions)
                        && !self.optimized_negative_one_of_translation(&descriptions)
                    {
                        let normalized: Vec<ClassExpr> = descriptions
                            .iter()
                            .map(|d| {
                                self.normalize_class_expression(d, inclusions, data_range_inclusions)
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        self.axioms.concept_inclusions.push(normalized);
                    }
                }
                CE::ObjectIntersectionOf(operands) => {
                    for conjunct in operands {
                        inclusions.push(vec![conjunct]);
                    }
                }
                other => {
                    let normalized =
                        self.normalize_class_expression(&other, inclusions, data_range_inclusions)?;
                    self.axioms.concept_inclusions.push(vec![normalized]);
                }
            }
        }
        // Data range inclusions.
        while let Some(entry) = data_range_inclusions.pop() {
            let union = DR::DataUnionOf(entry);
            let simplified = self
                .expression_manager
                .get_nnf_data(&self.expression_manager.get_simplified_data(&union));
            if self.is_top_datatype_dr(&simplified) {
                continue;
            }
            match simplified {
                DR::DataUnionOf(mut descriptions) => {
                    if !distribute_union_over_and_dr(&mut descriptions, data_range_inclusions) {
                        let normalized: Vec<DataRangeExpr> = descriptions
                            .iter()
                            .map(|d| self.normalize_data_range(d, data_range_inclusions))
                            .collect();
                        self.axioms.data_range_inclusions.push(normalized);
                    }
                }
                DR::DataIntersectionOf(operands) => {
                    for conjunct in operands {
                        data_range_inclusions.push(vec![conjunct]);
                    }
                }
                other => {
                    let normalized = self.normalize_data_range(&other, data_range_inclusions);
                    data_range_inclusions.push(vec![normalized]);
                }
            }
        }
        Ok(())
    }

    fn is_top_datatype_dr(&self, dr: &DataRangeExpr) -> bool {
        matches!(dr, DR::Datatype(dt) if *dt == self.factory.datatype(RDFS_LITERAL))
    }

    fn optimized_negative_one_of_translation(&mut self, descriptions: &[ClassExpr]) -> bool {
        if descriptions.len() == 2 {
            let mut nominal: Option<&ClassExpr> = None;
            let mut other: Option<&ClassExpr> = None;
            if let CE::ObjectComplementOf(o) = &descriptions[0] {
                if matches!(&**o, CE::ObjectOneOf(_)) {
                    nominal = Some(o);
                    other = Some(&descriptions[1]);
                }
            }
            if nominal.is_none() {
                if let CE::ObjectComplementOf(o) = &descriptions[1] {
                    if matches!(&**o, CE::ObjectOneOf(_)) {
                        other = Some(&descriptions[0]);
                        nominal = Some(o);
                    }
                }
            }
            if let (Some(nominal), Some(other)) = (nominal, other) {
                let other_is_simple = matches!(other, CE::Class(_))
                    || matches!(other, CE::ObjectComplementOf(o) if matches!(&**o, CE::Class(_)));
                if other_is_simple {
                    if let CE::ObjectOneOf(individuals) = nominal {
                        let other = other.clone();
                        let individuals = individuals.clone();
                        for individual in individuals {
                            self.add_fact(Fact::ClassAssertion {
                                class_expression: other.clone(),
                                individual,
                            });
                        }
                        return true;
                    }
                }
            }
        }
        false
    }

    fn normalize_class_expression(
        &mut self,
        object: &ClassExpr,
        new_inclusions: &mut Vec<Vec<ClassExpr>>,
        new_data_range_inclusions: &mut Vec<Vec<DataRangeExpr>>,
    ) -> Result<ClassExpr, String> {
        match object {
            CE::Class(_) => Ok(object.clone()),
            CE::ObjectIntersectionOf(operands) => {
                let (definition, already_exists) = self.get_definition_for(object, false);
                if !already_exists {
                    for description in operands {
                        let neg = self.negative(&definition);
                        new_inclusions.push(vec![neg, description.clone()]);
                    }
                }
                Ok(definition)
            }
            CE::ObjectUnionOf(_) => {
                panic!("OR should be broken down at the outermost level")
            }
            CE::ObjectComplementOf(operand) => {
                if let CE::ObjectOneOf(individuals) = &**operand {
                    let (definition, already_exists) =
                        self.get_definition_for_negative_nominal(operand);
                    if !already_exists {
                        for individual in individuals.clone() {
                            self.add_fact(Fact::ClassAssertion {
                                class_expression: CE::Class(definition.clone()),
                                individual,
                            });
                        }
                    }
                    Ok(CE::ObjectComplementOf(Box::new(CE::Class(definition))))
                } else {
                    Ok(object.clone())
                }
            }
            CE::ObjectOneOf(individuals) => {
                // HermiT rejects nominals containing anonymous individuals
                // (OWLNormalization.ClassExpressionNormalizer.visit(OWLObjectOneOf):
                // throws IllegalArgumentException when ind.isAnonymous()).
                for individual in individuals {
                    if matches!(individual, Individual::Anonymous(_)) {
                        return Err(format!(
                            "Error: The class expression {object:?} contains anonymous \
                             individuals, which is not allowed in OWL 2."
                        ));
                    }
                }
                Ok(object.clone())
            }
            CE::ObjectSomeValuesFrom { ope, bce } => {
                self.note_object_property(ope);
                if Self::is_simple(bce) || Self::is_nominal(bce) {
                    Ok(object.clone())
                } else {
                    let (definition, already_exists) = self.get_definition_for(bce, false);
                    if !already_exists {
                        let neg = self.negative(&definition);
                        new_inclusions.push(vec![neg, (**bce).clone()]);
                    }
                    Ok(CE::ObjectSomeValuesFrom {
                        ope: ope.clone(),
                        bce: Box::new(definition),
                    })
                }
            }
            CE::ObjectAllValuesFrom { ope, bce } => {
                self.note_object_property(ope);
                if Self::is_simple(bce) || Self::is_nominal(bce) || Self::is_negated_one_nominal(bce)
                {
                    Ok(object.clone())
                } else {
                    let (definition, already_exists) = self.get_definition_for(bce, false);
                    if !already_exists {
                        let neg = self.negative(&definition);
                        new_inclusions.push(vec![neg, (**bce).clone()]);
                    }
                    Ok(CE::ObjectAllValuesFrom {
                        ope: ope.clone(),
                        bce: Box::new(definition),
                    })
                }
            }
            CE::ObjectHasValue { .. } => {
                panic!("Internal error: object value restrictions should have been simplified.")
            }
            CE::ObjectHasSelf(ope) => {
                self.note_object_property(ope);
                Ok(object.clone())
            }
            CE::ObjectMinCardinality { n, ope, bce } => {
                self.note_object_property(ope);
                if Self::is_simple(bce) {
                    Ok(object.clone())
                } else {
                    let (definition, already_exists) = self.get_definition_for(bce, false);
                    if !already_exists {
                        let neg = self.negative(&definition);
                        new_inclusions.push(vec![neg, (**bce).clone()]);
                    }
                    Ok(CE::ObjectMinCardinality {
                        n: *n,
                        ope: ope.clone(),
                        bce: Box::new(definition),
                    })
                }
            }
            CE::ObjectMaxCardinality { n, ope, bce } => {
                self.note_object_property(ope);
                if Self::is_simple(bce) {
                    Ok(object.clone())
                } else {
                    let complement_description = self.expression_manager.get_complement_nnf(bce);
                    let (definition, already_exists) =
                        self.get_definition_for(&complement_description, false);
                    if !already_exists {
                        let neg = self.negative(&definition);
                        new_inclusions.push(vec![neg, complement_description.clone()]);
                    }
                    Ok(CE::ObjectMaxCardinality {
                        n: *n,
                        ope: ope.clone(),
                        bce: Box::new(self.expression_manager.get_complement_nnf(&definition)),
                    })
                }
            }
            CE::ObjectExactCardinality { .. } => {
                panic!("Internal error: exact object cardinality restrictions should have been simplified.")
            }
            CE::DataSomeValuesFrom { dp, dr } => {
                if self.is_owl_top_data_property(dp) {
                    // Java `checkTopDataPropertyUse` throws IllegalArgumentException:
                    // owl:topDataProperty may only occur in the super-property
                    // position of SubDataPropertyOf. Return a clean error (not a
                    // panic) so invalid input is rejected, not a process crash.
                    return Err(
                        "Error: In OWL 2 DL, owl:topDataProperty is only allowed to occur in \
                         the super property position of SubDataPropertyOf axioms."
                            .to_string(),
                    );
                }
                if Self::is_literal(dr) {
                    Ok(CE::DataSomeValuesFrom { dp: dp.clone(), dr: dr.clone() })
                } else {
                    let (definition, already_exists) = self.get_data_definition_for(dr);
                    if !already_exists {
                        let neg = self.negative_dr(&DR::Datatype(definition.clone()));
                        new_data_range_inclusions.push(vec![neg, dr.clone()]);
                    }
                    Ok(CE::DataSomeValuesFrom { dp: dp.clone(), dr: DR::Datatype(definition) })
                }
            }
            CE::DataAllValuesFrom { dp, dr } => {
                if self.is_owl_top_data_property(dp) {
                    // Java `checkTopDataPropertyUse` throws IllegalArgumentException:
                    // owl:topDataProperty may only occur in the super-property
                    // position of SubDataPropertyOf. Return a clean error (not a
                    // panic) so invalid input is rejected, not a process crash.
                    return Err(
                        "Error: In OWL 2 DL, owl:topDataProperty is only allowed to occur in \
                         the super property position of SubDataPropertyOf axioms."
                            .to_string(),
                    );
                }
                if Self::is_literal(dr) {
                    Ok(CE::DataAllValuesFrom { dp: dp.clone(), dr: dr.clone() })
                } else {
                    let (definition, already_exists) = self.get_data_definition_for(dr);
                    if !already_exists {
                        let neg = self.negative_dr(&DR::Datatype(definition.clone()));
                        new_data_range_inclusions.push(vec![neg, dr.clone()]);
                    }
                    Ok(CE::DataAllValuesFrom { dp: dp.clone(), dr: DR::Datatype(definition) })
                }
            }
            CE::DataHasValue { .. } => {
                panic!("Internal error: data value restrictions should have been simplified.")
            }
            CE::DataMinCardinality { n, dp, dr } => {
                if self.is_owl_top_data_property(dp) {
                    // Java `checkTopDataPropertyUse` throws IllegalArgumentException:
                    // owl:topDataProperty may only occur in the super-property
                    // position of SubDataPropertyOf. Return a clean error (not a
                    // panic) so invalid input is rejected, not a process crash.
                    return Err(
                        "Error: In OWL 2 DL, owl:topDataProperty is only allowed to occur in \
                         the super property position of SubDataPropertyOf axioms."
                            .to_string(),
                    );
                }
                if Self::is_literal(dr) {
                    Ok(CE::DataMinCardinality { n: *n, dp: dp.clone(), dr: dr.clone() })
                } else {
                    let (definition, already_exists) = self.get_data_definition_for(dr);
                    if !already_exists {
                        let neg = self.negative_dr(&DR::Datatype(definition.clone()));
                        new_data_range_inclusions.push(vec![neg, dr.clone()]);
                    }
                    Ok(CE::DataMinCardinality { n: *n, dp: dp.clone(), dr: DR::Datatype(definition) })
                }
            }
            CE::DataMaxCardinality { n, dp, dr } => {
                if self.is_owl_top_data_property(dp) {
                    // Java `checkTopDataPropertyUse` throws IllegalArgumentException:
                    // owl:topDataProperty may only occur in the super-property
                    // position of SubDataPropertyOf. Return a clean error (not a
                    // panic) so invalid input is rejected, not a process crash.
                    return Err(
                        "Error: In OWL 2 DL, owl:topDataProperty is only allowed to occur in \
                         the super property position of SubDataPropertyOf axioms."
                            .to_string(),
                    );
                }
                if Self::is_literal(dr) {
                    Ok(CE::DataMaxCardinality { n: *n, dp: dp.clone(), dr: dr.clone() })
                } else {
                    let complement_description =
                        self.expression_manager.get_complement_nnf_data(dr);
                    let (definition, already_exists) =
                        self.get_data_definition_for(&complement_description);
                    if !already_exists {
                        let neg = self.negative_dr(&DR::Datatype(definition.clone()));
                        new_data_range_inclusions.push(vec![neg, dr.clone()]);
                    }
                    Ok(CE::DataMaxCardinality {
                        n: *n,
                        dp: dp.clone(),
                        dr: self
                            .expression_manager
                            .get_complement_nnf_data(&DR::Datatype(definition)),
                    })
                }
            }
            CE::DataExactCardinality { .. } => {
                panic!("Internal error: exact data cardinality restrictions should have been simplified.")
            }
        }
    }

    fn normalize_data_range(
        &mut self,
        object: &DataRangeExpr,
        new_data_range_inclusions: &mut Vec<Vec<DataRangeExpr>>,
    ) -> DataRangeExpr {
        match object {
            DR::Datatype(_) | DR::DataComplementOf(_) | DR::DataOneOf(_) | DR::DatatypeRestriction(..) => {
                object.clone()
            }
            DR::DataIntersectionOf(operands) => {
                let (definition, already_exists) = self.get_data_definition_for(object);
                if !already_exists {
                    for description in operands {
                        let neg = self.negative_dr(&DR::Datatype(definition.clone()));
                        new_data_range_inclusions.push(vec![neg, description.clone()]);
                    }
                }
                DR::Datatype(definition)
            }
            DR::DataUnionOf(_) => {
                panic!("OR should be broken down at the outermost level")
            }
        }
    }
}

/// Port of the OWLClassExpression[] variant of distributeUnionOverAnd.
fn distribute_union_over_and(
    descriptions: &mut [ClassExpr],
    inclusions: &mut Vec<Vec<ClassExpr>>,
) -> bool {
    let is_simple = |d: &ClassExpr| {
        matches!(d, CE::Class(_))
            || matches!(d, CE::ObjectComplementOf(o) if matches!(**o, CE::Class(_)))
    };
    let mut and_index: isize = -1;
    for (index, description) in descriptions.iter().enumerate() {
        if !is_simple(description) {
            if matches!(description, CE::ObjectIntersectionOf(_)) {
                if and_index == -1 {
                    and_index = index as isize;
                } else {
                    return false;
                }
            } else {
                return false;
            }
        }
    }
    if and_index == -1 {
        return false;
    }
    let and_index = and_index as usize;
    if let CE::ObjectIntersectionOf(operands) = descriptions[and_index].clone() {
        for description in operands {
            let mut new_descriptions = descriptions.to_vec();
            new_descriptions[and_index] = description;
            inclusions.push(new_descriptions);
        }
    }
    true
}

/// Port of the OWLDataRange[] variant of distributeUnionOverAnd.
fn distribute_union_over_and_dr(
    descriptions: &mut [DataRangeExpr],
    inclusions: &mut Vec<Vec<DataRangeExpr>>,
) -> bool {
    let is_literal = |d: &DataRangeExpr| OWLNormalization::is_literal(d);
    let mut and_index: isize = -1;
    for (index, description) in descriptions.iter().enumerate() {
        if !is_literal(description) {
            if matches!(description, DR::DataIntersectionOf(_)) {
                if and_index == -1 {
                    and_index = index as isize;
                } else {
                    return false;
                }
            } else {
                return false;
            }
        }
    }
    if and_index == -1 {
        return false;
    }
    let and_index = and_index as usize;
    if let DR::DataIntersectionOf(operands) = descriptions[and_index].clone() {
        for description in operands {
            let mut new_descriptions = descriptions.to_vec();
            new_descriptions[and_index] = description;
            inclusions.push(new_descriptions);
        }
    }
    true
}

// ---------------------------------------------------------------------------
// SWRL rule normalization parity tests.
//
// These verify that the port matches HermiT's *actual* behavior for each SWRL
// rule atom shape, as implemented by the Java `RuleNormalizer`,
// `Rule2FactConverter`, and `NormalizedRuleClausifier`:
//
//   * Built-in atoms (`SWRLBuiltInAtom`): Java THROWS in all three visitors
//     (Rule2FactConverter.visit(SWRLBuiltInAtom):1054, RuleNormalizer.visit:1265,
//     NormalizedRuleClausifier.visit:1078). The port rejects with the same message.
//   * Data-range atoms (`SWRLDataRangeAtom`): Java ACCEPTS
//     (RuleNormalizer.visit(SWRLDataRangeAtom):1194). The port accepts and reasons.
//   * Complex class atoms (`SWRLClassAtom` with a complex class): Java ACCEPTS
//     by introducing a fresh definition (RuleNormalizer.visit(SWRLClassAtom):1168
//     via getClassFor). The port accepts and reasons.
//   * `SWRLDifferentIndividualsAtom` / `SWRLSameIndividualAtom` in the head:
//     Java ACCEPTS (RuleNormalizer.visit:1274/1268). The port accepts and reasons.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod swrl_parity_tests {
    use horned_owl::model::{
        Atom as SwrlAtom, Build, Class, Component, DArgument, DataProperty, DataRange,
        Datatype, IArgument, Individual, Literal, MutableOntology, NamedIndividual,
        ObjectProperty, ObjectPropertyExpression as OPE, Rule,
    };
    use horned_owl::ontology::set::SetOntology;

    use crate::reasoner::is_ontology_consistent;
    use crate::structural::{ClassExpr as CE, A};

    fn build() -> Build<A> {
        Build::new_arc()
    }
    fn class(b: &Build<A>, iri: &str) -> Class<A> {
        b.class(iri)
    }
    fn cls(c: &Class<A>) -> CE {
        CE::Class(c.clone())
    }
    fn oprop(b: &Build<A>, iri: &str) -> ObjectProperty<A> {
        ObjectProperty::from(b.object_property(iri))
    }
    fn dprop(b: &Build<A>, iri: &str) -> DataProperty<A> {
        b.data_property(iri)
    }
    fn named(b: &Build<A>, iri: &str) -> NamedIndividual<A> {
        b.named_individual(iri)
    }
    fn ind(b: &Build<A>, iri: &str) -> Individual<A> {
        Individual::Named(named(b, iri))
    }
    fn ivar(b: &Build<A>, name: &str) -> IArgument<A> {
        IArgument::Variable(b.variable(name))
    }
    fn dvar(b: &Build<A>, name: &str) -> DArgument<A> {
        DArgument::Variable(b.variable(name))
    }

    // -- Built-in atoms: Java REJECTS; the port's rejection is faithful. --------

    /// A rule with a non-empty body and a `SWRLBuiltInAtom` reaches the
    /// `RuleNormalizer`, which in Java throws
    /// `"A SWRL rule uses a built-in atom, but built-in atoms are not supported
    /// yet."` (OWLNormalization.RuleNormalizer.visit(SWRLBuiltInAtom):1265-1266).
    /// The port must reject with the same message rather than silently accept.
    #[test]
    fn builtin_atom_in_rule_body_rejected_like_java() {
        let b = build();
        let c = class(&b, "http://ex/C");
        let d = class(&b, "http://ex/D");
        let swrlb_equal = "http://www.w3.org/2003/11/swrlb#equal";

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: cls(&c),
            i: ind(&b, "http://ex/a"),
        }));
        // C(?x) ^ swrlb:equal(?x, ?x) -> D(?x)
        o.insert(Component::Rule(Rule {
            body: vec![
                SwrlAtom::ClassAtom { pred: cls(&c), arg: ivar(&b, "urn:x") },
                SwrlAtom::BuiltInAtom {
                    pred: b.iri(swrlb_equal),
                    args: vec![dvar(&b, "urn:x"), dvar(&b, "urn:x")],
                },
            ],
            head: vec![SwrlAtom::ClassAtom { pred: cls(&d), arg: ivar(&b, "urn:x") }],
        }));

        let err = is_ontology_consistent(&o).expect_err("Java RuleNormalizer rejects built-ins");
        assert!(
            err.contains("built-in atom"),
            "expected the RuleNormalizer built-in rejection, got: {err}"
        );
    }

    /// An empty-body rule whose head is a `SWRLBuiltInAtom` reaches the
    /// `Rule2FactConverter`, which in Java throws
    /// `"Error: A rule uses built-in atoms ..., but built-in atoms are not
    /// supported yet."` (Rule2FactConverter.visit(SWRLBuiltInAtom):1054-1055).
    #[test]
    fn builtin_atom_in_empty_body_rule_head_rejected_like_java() {
        let b = build();
        let swrlb_equal = "http://www.w3.org/2003/11/swrlb#equal";

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::Rule(Rule {
            body: vec![],
            head: vec![SwrlAtom::BuiltInAtom {
                pred: b.iri(swrlb_equal),
                args: vec![
                    DArgument::Literal(Literal::Simple { literal: "1".to_string() }),
                    DArgument::Literal(Literal::Simple { literal: "1".to_string() }),
                ],
            }],
        }));

        let err =
            is_ontology_consistent(&o).expect_err("Java Rule2FactConverter rejects built-ins");
        assert!(
            err.contains("built-in atoms"),
            "expected the Rule2FactConverter built-in rejection, got: {err}"
        );
    }

    // -- Data-range atoms ---------------------------------------------------------

    /// A rule with a data-range atom in the head:
    /// `dp(?x, ?y) -> xsd:integer(?y)`. Java's RuleNormalizer.visit(
    /// SWRLDataRangeAtom):1194 accepts this (the variable already occurs in a
    /// body data-property atom, so the head/body data-range-variable check
    /// passes). With `dp(a, "abc")` asserted, `?y` binds to the non-integer
    /// literal, forcing it to be an integer, which clashes -> INCONSISTENT.
    #[test]
    fn data_range_atom_in_head_accepted_and_reasons() {
        let b = build();
        let dp = dprop(&b, "http://ex/dp");
        let a = ind(&b, "http://ex/a");
        let xsd_integer: Datatype<A> = b.datatype("http://www.w3.org/2001/XMLSchema#integer");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareDataProperty(horned_owl::model::DeclareDataProperty(
            dp.clone(),
        )));
        // dp(a, "abc")  -- "abc" is an xsd:string, not an integer.
        o.insert(Component::DataPropertyAssertion(horned_owl::model::DataPropertyAssertion {
            dp: dp.clone(),
            from: a.clone(),
            to: Literal::Simple { literal: "abc".to_string() },
        }));
        // dp(?x, ?y) -> xsd:integer(?y)
        o.insert(Component::Rule(Rule {
            body: vec![SwrlAtom::DataPropertyAtom {
                pred: dp.clone(),
                args: (dvar(&b, "urn:x"), dvar(&b, "urn:y")),
            }],
            head: vec![SwrlAtom::DataRangeAtom {
                pred: DataRange::Datatype(xsd_integer),
                arg: dvar(&b, "urn:y"),
            }],
        }));

        let consistent =
            is_ontology_consistent(&o).expect("Java accepts data-range atoms; port must too");
        assert!(
            !consistent,
            "data-range head atom must force the string object to be an integer and clash"
        );
    }

    /// A data-range atom whose head variable does NOT occur in the body is
    /// rejected by Java (RuleNormalizer.visit(SWRLRule):1163 -- the
    /// `containsAll` check), with message containing "data range variables in
    /// the head, but not in the body". The port must match.
    #[test]
    fn data_range_head_variable_not_in_body_rejected_like_java() {
        let b = build();
        let c = class(&b, "http://ex/C");
        let xsd_integer: Datatype<A> = b.datatype("http://www.w3.org/2001/XMLSchema#integer");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: cls(&c),
            i: ind(&b, "http://ex/a"),
        }));
        // C(?x) -> xsd:integer(?y)  -- ?y is a fresh data-range variable.
        o.insert(Component::Rule(Rule {
            body: vec![SwrlAtom::ClassAtom { pred: cls(&c), arg: ivar(&b, "urn:x") }],
            head: vec![SwrlAtom::DataRangeAtom {
                pred: DataRange::Datatype(xsd_integer),
                arg: dvar(&b, "urn:y"),
            }],
        }));

        let err = is_ontology_consistent(&o)
            .expect_err("Java rejects head-only data-range variables");
        assert!(
            err.contains("data range variables in the head"),
            "expected the head-only data-range-variable rejection, got: {err}"
        );
    }

    // -- Complex class atoms: Java ACCEPTS via a fresh definition. ---------------

    /// A rule with a *complex* class atom in the body:
    /// `(exists p . Thing)(?x) -> C(?x)`. Java's RuleNormalizer.visit(
    /// SWRLClassAtom):1168 detects the non-named class and introduces a fresh
    /// definition `getClassFor(...)` plus an inclusion. With `p(a, b)` so that
    /// `a` is an instance of `exists p . Thing`, the rule fires and derives
    /// `C(a)`; together with `not C(a)` the ontology is INCONSISTENT.
    #[test]
    fn complex_class_atom_in_body_accepted_via_fresh_definition() {
        let b = build();
        let c = class(&b, "http://ex/C");
        let p = oprop(&b, "http://ex/p");
        let a = ind(&b, "http://ex/a");
        let bb = ind(&b, "http://ex/b");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareObjectProperty(horned_owl::model::DeclareObjectProperty(
            p.clone(),
        )));
        // p(a, b)
        o.insert(Component::ObjectPropertyAssertion(horned_owl::model::ObjectPropertyAssertion {
            ope: OPE::ObjectProperty(p.clone()),
            from: a.clone(),
            to: bb,
        }));
        // not C(a)
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::ObjectComplementOf(Box::new(cls(&c))),
            i: a.clone(),
        }));
        // (exists p . Thing)(?x) -> C(?x)
        let some_p = CE::ObjectSomeValuesFrom {
            ope: OPE::ObjectProperty(p.clone()),
            bce: Box::new(CE::Class(b.class("http://www.w3.org/2002/07/owl#Thing"))),
        };
        o.insert(Component::Rule(Rule {
            body: vec![SwrlAtom::ClassAtom { pred: some_p, arg: ivar(&b, "urn:x") }],
            head: vec![SwrlAtom::ClassAtom { pred: cls(&c), arg: ivar(&b, "urn:x") }],
        }));

        let consistent = is_ontology_consistent(&o)
            .expect("Java accepts complex class atoms via a fresh definition; port must too");
        assert!(
            !consistent,
            "complex body class atom must fire the rule and clash with not C(a)"
        );
    }

    // -- DifferentIndividuals / SameIndividual in the head: Java ACCEPTS. --------

    /// A rule deriving a `SWRLDifferentIndividualsAtom` in the head:
    /// `p(?x, ?y) -> differentFrom(?x, ?y)`. Java's
    /// RuleNormalizer.visit(SWRLDifferentIndividualsAtom):1274 keeps it as an
    /// Inequality head atom. With `p(a, a)` asserted, `?x = ?y = a`, so the rule
    /// derives `a != a`, which is INCONSISTENT.
    #[test]
    fn different_individuals_atom_in_head_accepted_and_reasons() {
        let b = build();
        let p = oprop(&b, "http://ex/p");
        let a = ind(&b, "http://ex/a");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareObjectProperty(horned_owl::model::DeclareObjectProperty(
            p.clone(),
        )));
        // p(a, a)
        o.insert(Component::ObjectPropertyAssertion(horned_owl::model::ObjectPropertyAssertion {
            ope: OPE::ObjectProperty(p.clone()),
            from: a.clone(),
            to: a.clone(),
        }));
        // p(?x, ?y) -> differentFrom(?x, ?y)
        o.insert(Component::Rule(Rule {
            body: vec![SwrlAtom::ObjectPropertyAtom {
                pred: OPE::ObjectProperty(p.clone()),
                args: (ivar(&b, "urn:x"), ivar(&b, "urn:y")),
            }],
            head: vec![SwrlAtom::DifferentIndividualsAtom(ivar(&b, "urn:x"), ivar(&b, "urn:y"))],
        }));

        let consistent = is_ontology_consistent(&o)
            .expect("Java accepts head differentFrom atoms; port must too");
        assert!(
            !consistent,
            "p(a,a) with rule deriving a != a must be inconsistent"
        );
    }

    /// A rule deriving a `SWRLSameIndividualAtom` in the head:
    /// `p(?x, ?y) -> sameAs(?x, ?y)`. Java's
    /// RuleNormalizer.visit(SWRLSameIndividualAtom):1268 keeps it as an Equality
    /// head atom (clausified to `Equality` by NormalizedRuleClausifier:1068).
    /// With `p(a, b)` and `differentFrom(a, b)` asserted, the rule derives
    /// `a = b`, contradicting `a != b` -> INCONSISTENT.
    #[test]
    fn same_individual_atom_in_head_accepted_and_reasons() {
        let b = build();
        let p = oprop(&b, "http://ex/p");
        let a = named(&b, "http://ex/a");
        let bind = named(&b, "http://ex/b");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareObjectProperty(horned_owl::model::DeclareObjectProperty(
            p.clone(),
        )));
        // p(a, b)
        o.insert(Component::ObjectPropertyAssertion(horned_owl::model::ObjectPropertyAssertion {
            ope: OPE::ObjectProperty(p.clone()),
            from: Individual::Named(a.clone()),
            to: Individual::Named(bind.clone()),
        }));
        // DifferentIndividuals(a, b)
        o.insert(Component::DifferentIndividuals(horned_owl::model::DifferentIndividuals(vec![
            Individual::Named(a.clone()),
            Individual::Named(bind.clone()),
        ])));
        // p(?x, ?y) -> sameAs(?x, ?y)
        o.insert(Component::Rule(Rule {
            body: vec![SwrlAtom::ObjectPropertyAtom {
                pred: OPE::ObjectProperty(p.clone()),
                args: (ivar(&b, "urn:x"), ivar(&b, "urn:y")),
            }],
            head: vec![SwrlAtom::SameIndividualAtom(ivar(&b, "urn:x"), ivar(&b, "urn:y"))],
        }));

        let consistent = is_ontology_consistent(&o)
            .expect("Java accepts head sameAs atoms; port must too");
        assert!(
            !consistent,
            "p(a,b) deriving a = b must contradict differentFrom(a, b)"
        );
    }

    // -- Forms the simplifier provably eliminates. ---------------------------------
    //
    // The `normalize_class_expression` / clausifier arms for ObjectHasValue,
    // ObjectExactCardinality, DataHasValue and DataExactCardinality `panic!`
    // with "should have been simplified" / "invalid normal form" — exactly
    // HermiT's `IllegalStateException` defensive invariants. They are unreachable
    // because every inclusion is run through `get_simplified` + `get_nnf` first
    // (`normalize_inclusions`), and `ExpressionManager::get_simplified` rewrites
    // each of these forms away (pinned by the unit tests in
    // `expression_manager::tests`). These end-to-end tests drive each form
    // through the full normalize+clausify+reason pipeline (`is_ontology_consistent`)
    // to PROVE no panic occurs and the reasoning result is correct.

    /// `ObjectHasValue(p, a)` reaches the reasoner without panicking. Asserting
    /// `(¬∃p.{a})(x)` together with `(ObjectHasValue p a)(x)` — i.e. x has p-value
    /// a AND x has no p-value a — must be INCONSISTENT. The simplifier rewrites
    /// `ObjectHasValue(p,a)` to `∃p.{a}`, so the panic arm is never hit.
    #[test]
    fn object_has_value_normalizes_without_panic_and_reasons() {
        let b = build();
        let p = oprop(&b, "http://ex/p");
        let x = ind(&b, "http://ex/x");
        let a = ind(&b, "http://ex/a");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareObjectProperty(horned_owl::model::DeclareObjectProperty(
            p.clone(),
        )));
        // (ObjectHasValue p a)(x)
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::ObjectHasValue { ope: OPE::ObjectProperty(p.clone()), i: a.clone() },
            i: x.clone(),
        }));
        // (¬ ObjectHasValue p a)(x)
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::ObjectComplementOf(Box::new(CE::ObjectHasValue {
                ope: OPE::ObjectProperty(p.clone()),
                i: a.clone(),
            })),
            i: x.clone(),
        }));

        let consistent = is_ontology_consistent(&o)
            .expect("ObjectHasValue must normalize without panic");
        assert!(!consistent, "x having and not having p-value a must be inconsistent");
    }

    /// `ObjectExactCardinality(0, p, Thing)(x)` together with `∃p.Thing (x)`
    /// (x has exactly 0 p-successors AND at least 1) must be INCONSISTENT. The
    /// simplifier rewrites the exact cardinality to `∀p.¬Thing`, so the
    /// `ObjectExactCardinality` panic arm is never reached.
    #[test]
    fn object_exact_cardinality_normalizes_without_panic_and_reasons() {
        let b = build();
        let p = oprop(&b, "http://ex/p");
        let x = ind(&b, "http://ex/x");
        let thing = b.class("http://www.w3.org/2002/07/owl#Thing");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareObjectProperty(horned_owl::model::DeclareObjectProperty(
            p.clone(),
        )));
        // (= 0 p Thing)(x)
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::ObjectExactCardinality {
                n: 0,
                ope: OPE::ObjectProperty(p.clone()),
                bce: Box::new(CE::Class(thing.clone())),
            },
            i: x.clone(),
        }));
        // (some p Thing)(x)
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::ObjectSomeValuesFrom {
                ope: OPE::ObjectProperty(p.clone()),
                bce: Box::new(CE::Class(thing)),
            },
            i: x.clone(),
        }));

        let consistent = is_ontology_consistent(&o)
            .expect("ObjectExactCardinality must normalize without panic");
        assert!(!consistent, "exactly-0 and at-least-1 p-successors must be inconsistent");
    }

    /// A *positive* exact cardinality `(= 2 p Thing)(x)` is satisfiable; this
    /// drives the `Min ⊓ Max` rewrite path through the clausifier without panic.
    #[test]
    fn object_exact_cardinality_positive_is_consistent_without_panic() {
        let b = build();
        let p = oprop(&b, "http://ex/p");
        let x = ind(&b, "http://ex/x");
        let thing = b.class("http://www.w3.org/2002/07/owl#Thing");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareObjectProperty(horned_owl::model::DeclareObjectProperty(
            p.clone(),
        )));
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::ObjectExactCardinality {
                n: 2,
                ope: OPE::ObjectProperty(p.clone()),
                bce: Box::new(CE::Class(thing)),
            },
            i: x.clone(),
        }));

        let consistent = is_ontology_consistent(&o)
            .expect("positive ObjectExactCardinality must normalize without panic");
        assert!(consistent, "(= 2 p Thing)(x) alone is satisfiable");
    }

    /// `DataHasValue(dp, "1"^^xsd:integer)(x)` with `(¬DataHasValue dp "1")(x)`
    /// must be INCONSISTENT. The simplifier rewrites `DataHasValue` to
    /// `∃dp.{"1"}`, so the `DataHasValue` panic arm is never reached.
    #[test]
    fn data_has_value_normalizes_without_panic_and_reasons() {
        let b = build();
        let dp = dprop(&b, "http://ex/dp");
        let x = ind(&b, "http://ex/x");
        let one = Literal::Datatype {
            literal: "1".to_string(),
            datatype_iri: b.iri("http://www.w3.org/2001/XMLSchema#integer"),
        };

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareDataProperty(horned_owl::model::DeclareDataProperty(
            dp.clone(),
        )));
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::DataHasValue { dp: dp.clone(), l: one.clone() },
            i: x.clone(),
        }));
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::ObjectComplementOf(Box::new(CE::DataHasValue {
                dp: dp.clone(),
                l: one.clone(),
            })),
            i: x.clone(),
        }));

        let consistent = is_ontology_consistent(&o)
            .expect("DataHasValue must normalize without panic");
        assert!(!consistent, "x having and not having dp-value 1 must be inconsistent");
    }

    /// `DataExactCardinality(0, dp, xsd:integer)(x)` with `∃dp.xsd:integer (x)`
    /// must be INCONSISTENT. The simplifier rewrites the exact cardinality to
    /// `∀dp.¬xsd:integer`, so the `DataExactCardinality` panic arm is never hit.
    #[test]
    fn data_exact_cardinality_normalizes_without_panic_and_reasons() {
        let b = build();
        let dp = dprop(&b, "http://ex/dp");
        let x = ind(&b, "http://ex/x");
        let xsd_integer: Datatype<A> = b.datatype("http://www.w3.org/2001/XMLSchema#integer");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareDataProperty(horned_owl::model::DeclareDataProperty(
            dp.clone(),
        )));
        // (= 0 dp xsd:integer)(x)
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::DataExactCardinality {
                n: 0,
                dp: dp.clone(),
                dr: DataRange::Datatype(xsd_integer.clone()),
            },
            i: x.clone(),
        }));
        // (some dp xsd:integer)(x)
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::DataSomeValuesFrom {
                dp: dp.clone(),
                dr: DataRange::Datatype(xsd_integer),
            },
            i: x.clone(),
        }));

        let consistent = is_ontology_consistent(&o)
            .expect("DataExactCardinality must normalize without panic");
        assert!(!consistent, "exactly-0 and at-least-1 dp integer values must be inconsistent");
    }

    /// A nested `ObjectUnionOf` in a SubClassOf super-position drives the
    /// outer-union flattening + `distribute_union_over_and` path of
    /// `normalize_inclusions` without ever hitting the `panic!("OR should be
    /// broken down")` arm. `C ⊑ (D ⊔ (E ⊔ F))`, `C(a)`, `¬D(a)`, `¬E(a)`, `¬F(a)`
    /// must be INCONSISTENT.
    #[test]
    fn nested_union_in_superclass_normalizes_without_panic_and_reasons() {
        let b = build();
        let c = class(&b, "http://ex/C");
        let d = class(&b, "http://ex/D");
        let e = class(&b, "http://ex/E");
        let f = class(&b, "http://ex/F");
        let a = ind(&b, "http://ex/a");

        let mut o: SetOntology<A> = SetOntology::new();
        // C ⊑ (D ⊔ (E ⊔ F))
        o.insert(Component::SubClassOf(horned_owl::model::SubClassOf {
            sub: cls(&c),
            sup: CE::ObjectUnionOf(vec![
                cls(&d),
                CE::ObjectUnionOf(vec![cls(&e), cls(&f)]),
            ]),
        }));
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: cls(&c),
            i: a.clone(),
        }));
        for neg in [&d, &e, &f] {
            o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
                ce: CE::ObjectComplementOf(Box::new(cls(neg))),
                i: a.clone(),
            }));
        }

        let consistent = is_ontology_consistent(&o)
            .expect("nested union must normalize without panic");
        assert!(
            !consistent,
            "C(a) ⊑ D⊔E⊔F with ¬D(a),¬E(a),¬F(a) must be inconsistent"
        );
    }
}
