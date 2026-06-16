// Port of org.semanticweb.HermiT.tableau.ReasoningTaskDescription.
//
// Describes a reasoning task (consistency, satisfiability, subsumption,
// instance/entailment checks) for messages and monitoring. Heterogeneous
// `Object...` arguments become the `TaskArgument` enum.

use crate::model::{Concept, DLPredicate, Role, Term};
use crate::prefixes::Prefixes;

#[derive(Clone, Copy, Debug)]
pub enum StandardTestType {
    ConceptSatisfiability,
    Consistency,
    ConceptSubsumption,
    ObjectRoleSatisfiability,
    DataRoleSatisfiability,
    ObjectRoleSubsumption,
    DataRoleSubsumption,
    InstanceOf,
    ObjectRoleInstanceOf,
    DataRoleInstanceOf,
    Entailment,
    Domain,
    Range,
}

impl StandardTestType {
    pub fn message_pattern(self) -> &'static str {
        match self {
            StandardTestType::ConceptSatisfiability => "satisfiability of concept '{0}'",
            StandardTestType::Consistency => "ABox satisfiability",
            StandardTestType::ConceptSubsumption => "concept subsumption '{0}' => '{1}'",
            StandardTestType::ObjectRoleSatisfiability => "satisfiability of object role '{0}'",
            StandardTestType::DataRoleSatisfiability => "satisfiability of data role '{0}'",
            StandardTestType::ObjectRoleSubsumption => "object role subsumption '{0}' => '{1}'",
            StandardTestType::DataRoleSubsumption => "data role subsumption '{0}' => '{1}'",
            StandardTestType::InstanceOf => "class instance '{0}'('{1}')",
            StandardTestType::ObjectRoleInstanceOf => "object role instance '{0}'('{1}', '{2}')",
            StandardTestType::DataRoleInstanceOf => "data role instance '{0}'('{1}', '{2}')",
            StandardTestType::Entailment => "entailment of '{0}'",
            StandardTestType::Domain => "check if {0} is domain of {1}",
            StandardTestType::Range => "check if {0} is range of {1}",
        }
    }
}

/// A heterogeneous task argument (the Java `Object`).
#[derive(Clone, Debug)]
pub enum TaskArgument {
    DLPredicate(DLPredicate),
    Role(Role),
    Concept(Concept),
    Term(Term),
    Text(String),
}

impl TaskArgument {
    fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        match self {
            TaskArgument::DLPredicate(p) => p.to_string_prefixes(prefixes),
            TaskArgument::Role(r) => r.to_string_prefixes(prefixes),
            TaskArgument::Concept(c) => c.to_string_prefixes(prefixes),
            TaskArgument::Term(t) => t.to_string_prefixes(prefixes),
            TaskArgument::Text(s) => s.clone(),
        }
    }
}

impl From<DLPredicate> for TaskArgument {
    fn from(v: DLPredicate) -> Self {
        TaskArgument::DLPredicate(v)
    }
}
impl From<Role> for TaskArgument {
    fn from(v: Role) -> Self {
        TaskArgument::Role(v)
    }
}
impl From<Concept> for TaskArgument {
    fn from(v: Concept) -> Self {
        TaskArgument::Concept(v)
    }
}
impl From<Term> for TaskArgument {
    fn from(v: Term) -> Self {
        TaskArgument::Term(v)
    }
}
impl From<String> for TaskArgument {
    fn from(v: String) -> Self {
        TaskArgument::Text(v)
    }
}
impl From<&str> for TaskArgument {
    fn from(v: &str) -> Self {
        TaskArgument::Text(v.to_string())
    }
}

#[derive(Clone, Debug)]
pub struct ReasoningTaskDescription {
    flip_satisfiability_result: bool,
    message_pattern: String,
    arguments: Vec<TaskArgument>,
}

impl ReasoningTaskDescription {
    pub fn new(
        flip_satisfiability_result: bool,
        test_type: StandardTestType,
        arguments: Vec<TaskArgument>,
    ) -> ReasoningTaskDescription {
        ReasoningTaskDescription::with_message(
            flip_satisfiability_result,
            test_type.message_pattern().to_string(),
            arguments,
        )
    }
    pub fn with_message(
        flip_satisfiability_result: bool,
        message: String,
        arguments: Vec<TaskArgument>,
    ) -> ReasoningTaskDescription {
        ReasoningTaskDescription {
            flip_satisfiability_result,
            message_pattern: message,
            arguments,
        }
    }

    pub fn flip_satisfiability_result(&self) -> bool {
        self.flip_satisfiability_result
    }
    pub fn get_message_pattern(&self) -> &str {
        &self.message_pattern
    }
    pub fn get_task_description(&self, prefixes: &Prefixes) -> String {
        let mut result = self.message_pattern.clone();
        for (index, argument) in self.arguments.iter().enumerate() {
            result = result.replace(
                &format!("{{{index}}}"),
                &argument.to_string_prefixes(prefixes),
            );
        }
        result
    }

    pub fn is_abox_satisfiable() -> ReasoningTaskDescription {
        ReasoningTaskDescription::new(false, StandardTestType::Consistency, vec![])
    }
    pub fn is_concept_satisfiable(atomic_concept: impl Into<TaskArgument>) -> ReasoningTaskDescription {
        ReasoningTaskDescription::new(
            false,
            StandardTestType::ConceptSatisfiability,
            vec![atomic_concept.into()],
        )
    }
    pub fn is_concept_subsumed_by(
        atomic_subconcept: impl Into<TaskArgument>,
        atomic_superconcept: impl Into<TaskArgument>,
    ) -> ReasoningTaskDescription {
        ReasoningTaskDescription::new(
            true,
            StandardTestType::ConceptSubsumption,
            vec![atomic_subconcept.into(), atomic_superconcept.into()],
        )
    }
    pub fn is_concept_subsumed_by_list(
        atomic_subconcept: impl Into<TaskArgument>,
        atomic_superconcepts: Vec<TaskArgument>,
    ) -> ReasoningTaskDescription {
        let mut message = String::from("satisiability of concept '{0}' ");
        for index in 0..atomic_superconcepts.len() {
            message.push_str(&format!(" and not({{{}}})", index + 1));
        }
        let mut arguments = Vec::with_capacity(atomic_superconcepts.len() + 1);
        arguments.push(atomic_subconcept.into());
        arguments.extend(atomic_superconcepts);
        ReasoningTaskDescription::with_message(false, message, arguments)
    }
    pub fn is_role_subsumed_by_list(
        subrole: impl Into<TaskArgument>,
        superroles: Vec<TaskArgument>,
    ) -> ReasoningTaskDescription {
        let mut message = String::from("satisiability of role '{0}' ");
        for index in 0..superroles.len() {
            message.push_str(&format!(" and not({{{}}})", index + 1));
        }
        let mut arguments = Vec::with_capacity(superroles.len() + 1);
        arguments.push(subrole.into());
        arguments.extend(superroles);
        ReasoningTaskDescription::with_message(false, message, arguments)
    }
    pub fn is_role_satisfiable(
        role: impl Into<TaskArgument>,
        is_object_role: bool,
    ) -> ReasoningTaskDescription {
        let test_type = if is_object_role {
            StandardTestType::ObjectRoleSatisfiability
        } else {
            StandardTestType::DataRoleSatisfiability
        };
        ReasoningTaskDescription::new(false, test_type, vec![role.into()])
    }
    pub fn is_role_subsumed_by(
        subrole: impl Into<TaskArgument>,
        superrole: impl Into<TaskArgument>,
        is_object_role: bool,
    ) -> ReasoningTaskDescription {
        let test_type = if is_object_role {
            StandardTestType::ObjectRoleSubsumption
        } else {
            StandardTestType::DataRoleSubsumption
        };
        ReasoningTaskDescription::new(true, test_type, vec![subrole.into(), superrole.into()])
    }
    pub fn is_instance_of(
        atomic_concept: impl Into<TaskArgument>,
        individual: impl Into<TaskArgument>,
    ) -> ReasoningTaskDescription {
        ReasoningTaskDescription::new(
            true,
            StandardTestType::InstanceOf,
            vec![atomic_concept.into(), individual.into()],
        )
    }
    pub fn is_object_role_instance_of(
        atomic_role: impl Into<TaskArgument>,
        individual1: impl Into<TaskArgument>,
        individual2: impl Into<TaskArgument>,
    ) -> ReasoningTaskDescription {
        ReasoningTaskDescription::new(
            true,
            StandardTestType::ObjectRoleInstanceOf,
            vec![atomic_role.into(), individual1.into(), individual2.into()],
        )
    }
    pub fn is_data_role_instance_of(
        atomic_role: impl Into<TaskArgument>,
        individual1: impl Into<TaskArgument>,
        individual2: impl Into<TaskArgument>,
    ) -> ReasoningTaskDescription {
        ReasoningTaskDescription::new(
            true,
            StandardTestType::DataRoleInstanceOf,
            vec![atomic_role.into(), individual1.into(), individual2.into()],
        )
    }
    pub fn is_axiom_entailed(axiom: impl Into<TaskArgument>) -> ReasoningTaskDescription {
        ReasoningTaskDescription::new(true, StandardTestType::Entailment, vec![axiom.into()])
    }
    pub fn is_domain_of(
        domain: impl Into<TaskArgument>,
        role: impl Into<TaskArgument>,
    ) -> ReasoningTaskDescription {
        ReasoningTaskDescription::new(true, StandardTestType::Domain, vec![domain.into(), role.into()])
    }
    pub fn is_range_of(
        range: impl Into<TaskArgument>,
        role: impl Into<TaskArgument>,
    ) -> ReasoningTaskDescription {
        ReasoningTaskDescription::new(true, StandardTestType::Range, vec![range.into(), role.into()])
    }
}

impl std::fmt::Display for ReasoningTaskDescription {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.get_task_description(Prefixes::standard()))
    }
}
