// Port of org.semanticweb.HermiT.model.DLOntology.
//
// Represents a clausified DL ontology: a set of DL clauses plus positive and
// negative facts (the ABox), along with the vocabulary and expressivity flags
// derived from them.
//
// NOTE: the Java `save`/`load` methods use Java object serialization; they are
// infrastructure rather than reasoning logic and are intentionally omitted from
// this port.

use std::collections::{BTreeSet, HashMap, HashSet};

use indexmap::IndexSet;

use crate::model::atom::Atom;
use crate::model::clause::DLClause;
use crate::model::concept::{AtomicConcept, LiteralConcept};
use crate::model::datarange::DatatypeRestriction;
use crate::model::description_graph::DescriptionGraph;
use crate::model::predicate::DLPredicate;
use crate::model::role::{AtomicRole, Role};
use crate::model::term::{Constant, Individual, Term};
use crate::prefixes::Prefixes;

const CRLF: &str = "\n";

pub struct DLOntology {
    ontology_iri: String,
    // Insertion-ordered (mirroring Java's `LinkedHashSet<DLClause>`) so that rule
    // compilation and hyperresolution firing order are deterministic.
    dl_clauses: IndexSet<DLClause>,
    positive_facts: HashSet<Atom>,
    negative_facts: HashSet<Atom>,
    has_inverse_roles: bool,
    has_at_most_restrictions: bool,
    has_nominals: bool,
    has_datatypes: bool,
    is_horn: bool,
    all_atomic_concepts: BTreeSet<AtomicConcept>,
    number_of_external_concepts: usize,
    all_atomic_object_roles: BTreeSet<AtomicRole>,
    all_complex_object_roles: HashSet<Role>,
    all_atomic_data_roles: BTreeSet<AtomicRole>,
    all_unknown_datatype_restrictions: HashSet<DatatypeRestriction>,
    defined_datatype_iris: HashSet<String>,
    all_individuals: BTreeSet<Individual>,
    all_description_graphs: HashSet<DescriptionGraph>,
    data_property_assertions: HashMap<AtomicRole, HashMap<Individual, HashSet<Constant>>>,
}

impl DLOntology {
    /// Faithful translation of the Java constructor. Sets that are `None` are
    /// treated as the Java `null` arguments (defaulting to empty collections).
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        ontology_iri: impl Into<String>,
        dl_clauses: IndexSet<DLClause>,
        positive_facts: HashSet<Atom>,
        negative_facts: HashSet<Atom>,
        atomic_concepts: Option<BTreeSet<AtomicConcept>>,
        atomic_object_roles: Option<BTreeSet<AtomicRole>>,
        all_complex_object_roles: Option<HashSet<Role>>,
        atomic_data_roles: Option<BTreeSet<AtomicRole>>,
        all_unknown_datatype_restrictions: Option<HashSet<DatatypeRestriction>>,
        defined_datatype_iris: Option<HashSet<String>>,
        individuals: Option<BTreeSet<Individual>>,
        has_inverse_roles: bool,
        has_at_most_restrictions: bool,
        has_nominals: bool,
        has_datatypes: bool,
    ) -> DLOntology {
        let mut all_atomic_concepts = atomic_concepts.unwrap_or_default();
        // Counted over the *supplied* concept set, before the clause/fact loops
        // augment it with concepts discovered in bodies/heads and ABox facts --
        // matching the ordering in the Java `DLOntology` constructor.
        let number_of_external_concepts = all_atomic_concepts
            .iter()
            .filter(|c| !Prefixes::is_internal_iri(c.iri()))
            .count();
        let mut all_atomic_object_roles = atomic_object_roles.unwrap_or_default();
        let all_complex_object_roles = all_complex_object_roles.unwrap_or_default();
        let mut all_atomic_data_roles = atomic_data_roles.unwrap_or_default();
        let all_unknown_datatype_restrictions =
            all_unknown_datatype_restrictions.unwrap_or_default();
        let defined_datatype_iris = defined_datatype_iris.unwrap_or_default();
        let mut all_individuals = individuals.unwrap_or_default();
        let mut all_description_graphs: HashSet<DescriptionGraph> = HashSet::new();

        let mut is_horn = true;
        for dl_clause in &dl_clauses {
            if dl_clause.get_head_length() > 1 {
                is_horn = false;
            }
            for body_index in (0..dl_clause.get_body_length()).rev() {
                let dl_predicate = dl_clause.get_body_atom(body_index).get_dl_predicate().clone();
                Self::add_dl_predicate(
                    &dl_predicate,
                    &mut all_atomic_concepts,
                    &mut all_description_graphs,
                );
            }
            for head_index in (0..dl_clause.get_head_length()).rev() {
                let dl_predicate = dl_clause.get_head_atom(head_index).get_dl_predicate().clone();
                Self::add_dl_predicate(
                    &dl_predicate,
                    &mut all_atomic_concepts,
                    &mut all_description_graphs,
                );
            }
        }

        let mut data_property_assertions: HashMap<AtomicRole, HashMap<Individual, HashSet<Constant>>> =
            HashMap::new();
        for atom in &positive_facts {
            Self::add_dl_predicate(
                atom.get_dl_predicate(),
                &mut all_atomic_concepts,
                &mut all_description_graphs,
            );
            for i in 0..atom.get_arity() {
                if let Term::Individual(individual) = atom.get_argument(i) {
                    all_individuals.insert(individual.clone());
                }
            }
            if atom.get_arity() == 2 {
                if let Term::Constant(constant) = atom.get_argument(1) {
                    // A data role assertion: store it into the appropriate maps.
                    let source_individual = match atom.get_argument(0) {
                        Term::Individual(i) => i.clone(),
                        _ => unreachable!("data role assertion subject must be an individual"),
                    };
                    let atomic_role = match atom.get_dl_predicate() {
                        DLPredicate::AtomicRole(r) => r.clone(),
                        _ => unreachable!("data role assertion predicate must be an atomic role"),
                    };
                    data_property_assertions
                        .entry(atomic_role)
                        .or_default()
                        .entry(source_individual)
                        .or_default()
                        .insert(constant.clone());
                }
            }
        }
        for atom in &negative_facts {
            Self::add_dl_predicate(
                atom.get_dl_predicate(),
                &mut all_atomic_concepts,
                &mut all_description_graphs,
            );
            for i in 0..atom.get_arity() {
                if let Term::Individual(individual) = atom.get_argument(i) {
                    all_individuals.insert(individual.clone());
                }
            }
        }

        // (Data roles discovered through assertions remain in the data-role set;
        // the Java code preserves whatever was supplied.)
        let _ = &mut all_atomic_object_roles;
        let _ = &mut all_atomic_data_roles;

        DLOntology {
            ontology_iri: ontology_iri.into(),
            dl_clauses,
            positive_facts,
            negative_facts,
            has_inverse_roles,
            has_at_most_restrictions,
            has_nominals,
            has_datatypes,
            is_horn,
            all_atomic_concepts,
            number_of_external_concepts,
            all_atomic_object_roles,
            all_complex_object_roles,
            all_atomic_data_roles,
            all_unknown_datatype_restrictions,
            defined_datatype_iris,
            all_individuals,
            all_description_graphs,
            data_property_assertions,
        }
    }

    fn add_dl_predicate(
        dl_predicate: &DLPredicate,
        all_atomic_concepts: &mut BTreeSet<AtomicConcept>,
        all_description_graphs: &mut HashSet<DescriptionGraph>,
    ) {
        match dl_predicate {
            DLPredicate::AtomicConcept(c) => {
                all_atomic_concepts.insert(c.clone());
            }
            DLPredicate::AtLeastConcept(a) => {
                if let LiteralConcept::AtomicConcept(c) = a.to_concept() {
                    all_atomic_concepts.insert(c.clone());
                }
            }
            DLPredicate::DescriptionGraph(g) => {
                all_description_graphs.insert(g.clone());
            }
            DLPredicate::ExistsDescriptionGraph(e) => {
                all_description_graphs.insert(e.get_description_graph().clone());
            }
            _ => {}
        }
    }

    pub fn get_ontology_iri(&self) -> &str {
        &self.ontology_iri
    }
    pub fn get_all_atomic_concepts(&self) -> &BTreeSet<AtomicConcept> {
        &self.all_atomic_concepts
    }
    pub fn contains_atomic_concept(&self, concept: &AtomicConcept) -> bool {
        self.all_atomic_concepts.contains(concept)
    }
    pub fn get_number_of_external_concepts(&self) -> usize {
        self.number_of_external_concepts
    }
    pub fn get_all_atomic_object_roles(&self) -> &BTreeSet<AtomicRole> {
        &self.all_atomic_object_roles
    }
    pub fn contains_object_role(&self, role: &AtomicRole) -> bool {
        self.all_atomic_object_roles.contains(role)
    }
    pub fn get_all_complex_object_roles(&self) -> &HashSet<Role> {
        &self.all_complex_object_roles
    }
    pub fn is_complex_object_role(&self, role: &Role) -> bool {
        self.all_complex_object_roles.contains(role)
    }
    pub fn get_all_atomic_data_roles(&self) -> &BTreeSet<AtomicRole> {
        &self.all_atomic_data_roles
    }
    pub fn contains_data_role(&self, role: &AtomicRole) -> bool {
        self.all_atomic_data_roles.contains(role)
    }
    pub fn get_all_unknown_datatype_restrictions(&self) -> &HashSet<DatatypeRestriction> {
        &self.all_unknown_datatype_restrictions
    }
    pub fn get_all_individuals(&self) -> &BTreeSet<Individual> {
        &self.all_individuals
    }
    pub fn contains_individual(&self, individual: &Individual) -> bool {
        self.all_individuals.contains(individual)
    }
    pub fn get_all_description_graphs(&self) -> &HashSet<DescriptionGraph> {
        &self.all_description_graphs
    }
    pub fn get_dl_clauses(&self) -> &IndexSet<DLClause> {
        &self.dl_clauses
    }
    pub fn get_positive_facts(&self) -> &HashSet<Atom> {
        &self.positive_facts
    }
    pub fn get_data_property_assertions(
        &self,
    ) -> &HashMap<AtomicRole, HashMap<Individual, HashSet<Constant>>> {
        &self.data_property_assertions
    }
    pub fn get_negative_facts(&self) -> &HashSet<Atom> {
        &self.negative_facts
    }
    pub fn has_inverse_roles(&self) -> bool {
        self.has_inverse_roles
    }
    pub fn has_at_most_restrictions(&self) -> bool {
        self.has_at_most_restrictions
    }
    pub fn has_nominals(&self) -> bool {
        self.has_nominals
    }
    pub fn has_datatypes(&self) -> bool {
        self.has_datatypes
    }
    pub fn has_unknown_datatype_restrictions(&self) -> bool {
        !self.all_unknown_datatype_restrictions.is_empty()
    }
    pub fn is_horn(&self) -> bool {
        self.is_horn
    }
    pub fn get_defined_datatype_iris(&self) -> &HashSet<String> {
        &self.defined_datatype_iris
    }

    pub fn get_body_only_atomic_concepts(&self) -> HashSet<AtomicConcept> {
        let mut body_only_atomic_concepts: HashSet<AtomicConcept> =
            self.all_atomic_concepts.iter().cloned().collect();
        for dl_clause in &self.dl_clauses {
            for head_index in 0..dl_clause.get_head_length() {
                let dl_predicate = dl_clause.get_head_atom(head_index).get_dl_predicate();
                if let DLPredicate::AtomicConcept(c) = dl_predicate {
                    body_only_atomic_concepts.remove(c);
                }
                if let DLPredicate::AtLeastConcept(a) = dl_predicate {
                    if let LiteralConcept::AtomicConcept(c) = a.to_concept() {
                        body_only_atomic_concepts.remove(c);
                    }
                }
            }
        }
        body_only_atomic_concepts
    }

    pub fn compute_graph_atomic_roles(&self) -> HashSet<AtomicRole> {
        let mut graph_atomic_roles: HashSet<AtomicRole> = HashSet::new();
        for description_graph in &self.all_description_graphs {
            for edge_index in 0..description_graph.number_of_edges() {
                let edge = description_graph.get_edge(edge_index);
                graph_atomic_roles.insert(edge.get_atomic_role().clone());
            }
        }
        let mut change = true;
        while change {
            change = false;
            for dl_clause in &self.dl_clauses {
                if Self::contains_atomic_roles(dl_clause, &graph_atomic_roles)
                    && Self::add_atomic_roles(dl_clause, &mut graph_atomic_roles)
                {
                    change = true;
                }
            }
        }
        graph_atomic_roles
    }

    fn contains_atomic_roles(dl_clause: &DLClause, roles: &HashSet<AtomicRole>) -> bool {
        for atom_index in 0..dl_clause.get_body_length() {
            if let DLPredicate::AtomicRole(r) = dl_clause.get_body_atom(atom_index).get_dl_predicate()
            {
                if roles.contains(r) {
                    return true;
                }
            }
        }
        for atom_index in 0..dl_clause.get_head_length() {
            if let DLPredicate::AtomicRole(r) = dl_clause.get_head_atom(atom_index).get_dl_predicate()
            {
                if roles.contains(r) {
                    return true;
                }
            }
        }
        false
    }

    fn add_atomic_roles(dl_clause: &DLClause, roles: &mut HashSet<AtomicRole>) -> bool {
        let mut change = false;
        for atom_index in 0..dl_clause.get_body_length() {
            if let DLPredicate::AtomicRole(r) = dl_clause.get_body_atom(atom_index).get_dl_predicate()
            {
                if roles.insert(r.clone()) {
                    change = true;
                }
            }
        }
        for atom_index in 0..dl_clause.get_head_length() {
            if let DLPredicate::AtomicRole(r) = dl_clause.get_head_atom(atom_index).get_dl_predicate()
            {
                if roles.insert(r.clone()) {
                    change = true;
                }
            }
        }
        change
    }

    pub fn get_statistics(&self) -> String {
        let mut num_deterministic_clauses = 0;
        let mut num_nondeterministic_clauses = 0;
        let mut num_disjunctions = 0;
        for dl_clause in &self.dl_clauses {
            if dl_clause.get_head_length() <= 1 {
                num_deterministic_clauses += 1;
            } else {
                num_nondeterministic_clauses += 1;
                num_disjunctions += dl_clause.get_head_length();
            }
        }
        let mut buffer = String::new();
        buffer.push_str("DL clauses statistics: [");
        buffer.push_str(CRLF);
        buffer.push_str(&format!(
            "  Number of deterministic clauses: {num_deterministic_clauses}"
        ));
        buffer.push_str(CRLF);
        buffer.push_str(&format!(
            "  Number of nondeterministic clauses: {num_nondeterministic_clauses}"
        ));
        buffer.push_str(CRLF);
        buffer.push_str(&format!("  Overall number of disjunctions: {num_disjunctions}"));
        buffer.push_str(CRLF);
        buffer.push_str(&format!("  Number of positive facts: {}", self.positive_facts.len()));
        buffer.push_str(CRLF);
        buffer.push_str(&format!("  Number of negative facts: {}", self.negative_facts.len()));
        buffer.push_str(CRLF);
        buffer.push_str(&format!("  Inverses: {}", self.has_inverse_roles()));
        buffer.push_str(CRLF);
        buffer.push_str(&format!("  At-Mosts: {}", self.has_at_most_restrictions()));
        buffer.push_str(CRLF);
        buffer.push_str(&format!("  Datatypes: {}", self.has_datatypes()));
        buffer.push_str(CRLF);
        buffer.push_str(&format!("  Nominals: {}", self.has_nominals()));
        buffer.push_str(CRLF);
        buffer.push_str(&format!(
            "  Number of atomic concepts: {}",
            self.all_atomic_concepts.len()
        ));
        buffer.push_str(CRLF);
        buffer.push_str(&format!(
            "  Number of object properties: {}",
            self.all_atomic_object_roles.len()
        ));
        buffer.push_str(CRLF);
        buffer.push_str(&format!(
            "  Number of data properties: {}",
            self.all_atomic_data_roles.len()
        ));
        buffer.push_str(CRLF);
        buffer.push_str(&format!(
            "  Number of individuals: {}",
            self.all_individuals.len()
        ));
        buffer.push_str(CRLF);
        buffer.push(']');
        buffer
    }

    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        let mut buffer = String::new();
        // Mirror DLOntology.java:317-328: emit "Prefixes: [" block first.
        buffer.push_str("Prefixes: [");
        buffer.push_str(CRLF);
        for (name, iri) in prefixes.prefix_iris_by_prefix_name() {
            buffer.push_str("  ");
            buffer.push_str(name);
            buffer.push_str(" = <");
            buffer.push_str(iri);
            buffer.push('>');
            buffer.push_str(CRLF);
        }
        buffer.push(']');
        buffer.push_str(CRLF);
        buffer.push_str("Deterministic DL-clauses: [");
        buffer.push_str(CRLF);
        let mut num_deterministic_clauses = 0;
        for dl_clause in &self.dl_clauses {
            if dl_clause.get_head_length() <= 1 {
                num_deterministic_clauses += 1;
                buffer.push_str("  ");
                buffer.push_str(&dl_clause.to_string_prefixes(prefixes));
                buffer.push_str(CRLF);
            }
        }
        buffer.push(']');
        buffer.push_str(CRLF);
        buffer.push_str("Disjunctive DL-clauses: [");
        buffer.push_str(CRLF);
        let mut num_nondeterministic_clauses = 0;
        let mut num_disjunctions = 0;
        for dl_clause in &self.dl_clauses {
            if dl_clause.get_head_length() > 1 {
                num_nondeterministic_clauses += 1;
                num_disjunctions += dl_clause.get_head_length();
                buffer.push_str("  ");
                buffer.push_str(&dl_clause.to_string_prefixes(prefixes));
                buffer.push_str(CRLF);
            }
        }
        buffer.push(']');
        buffer.push_str(CRLF);
        buffer.push_str("ABox: [");
        buffer.push_str(CRLF);
        for atom in &self.positive_facts {
            buffer.push_str("  ");
            buffer.push_str(&atom.to_string_prefixes(prefixes));
            buffer.push_str(CRLF);
        }
        for atom in &self.negative_facts {
            buffer.push_str("  !");
            buffer.push_str(&atom.to_string_prefixes(prefixes));
            buffer.push_str(CRLF);
        }
        buffer.push(']');
        buffer.push_str(CRLF);
        buffer.push_str("Statistics: [");
        buffer.push_str(CRLF);
        buffer.push_str(&format!(
            "  Number of deterministic clauses: {num_deterministic_clauses}"
        ));
        buffer.push_str(CRLF);
        buffer.push_str(&format!(
            "  Number of nondeterministic clauses: {num_nondeterministic_clauses}"
        ));
        buffer.push_str(CRLF);
        buffer.push_str(&format!("  Number of disjunctions: {num_disjunctions}"));
        buffer.push_str(CRLF);
        buffer.push_str(&format!("  Number of positive facts: {}", self.positive_facts.len()));
        buffer.push_str(CRLF);
        buffer.push_str(&format!("  Number of negative facts: {}", self.negative_facts.len()));
        buffer.push_str(CRLF);
        buffer.push(']');
        buffer
    }
}

impl std::fmt::Display for DLOntology {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string_prefixes(Prefixes::standard()))
    }
}
