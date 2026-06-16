// Port of org.semanticweb.HermiT.model.DLClause.
//
// A DL clause has a body (a conjunction of atoms) and a head (a disjunction of
// atoms): head_0 v ... v head_m :- body_0, ..., body_n.

use std::collections::HashSet;

use crate::model::atom::Atom;
use crate::model::concept::AtomicConcept;
use crate::model::predicate::DLPredicate;
use crate::model::term::{Term, Variable};
use crate::prefixes::Prefixes;
use crate::{impl_display_prefixes, interned};

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct DLClauseData {
    head_atoms: Vec<Atom>,
    body_atoms: Vec<Atom>,
}

interned!(pub DLClause => DLClauseData);

impl DLClause {
    pub fn create(head_atoms: Vec<Atom>, body_atoms: Vec<Atom>) -> DLClause {
        DLClause::intern(DLClauseData { head_atoms, body_atoms })
    }

    pub fn get_head_length(&self) -> usize {
        self.0.head_atoms.len()
    }
    pub fn get_head_atom(&self, atom_index: usize) -> &Atom {
        &self.0.head_atoms[atom_index]
    }
    pub fn get_head_atoms(&self) -> Vec<Atom> {
        self.0.head_atoms.clone()
    }
    pub fn get_body_length(&self) -> usize {
        self.0.body_atoms.len()
    }
    pub fn get_body_atom(&self, atom_index: usize) -> &Atom {
        &self.0.body_atoms[atom_index]
    }
    pub fn get_body_atoms(&self) -> Vec<Atom> {
        self.0.body_atoms.clone()
    }

    pub fn get_safe_version(&self, safe_making_predicate: DLPredicate) -> DLClause {
        let mut variables: HashSet<Variable> = HashSet::new();
        // Collect all variables that occur in the head.
        for atom in &self.0.head_atoms {
            for argument_index in 0..atom.get_arity() {
                if let Some(variable) = atom.get_argument_variable(argument_index) {
                    variables.insert(variable.clone());
                }
            }
        }
        // Remove all variables that occur in the body, leaving the unsafe ones.
        for atom in &self.0.body_atoms {
            for argument_index in 0..atom.get_arity() {
                if let Some(variable) = atom.get_argument_variable(argument_index) {
                    variables.remove(variable);
                }
            }
        }
        if self.0.head_atoms.is_empty() && self.0.body_atoms.is_empty() {
            variables.insert(Variable::create("X"));
        }
        if variables.is_empty() {
            self.clone()
        } else {
            // Add a concept atom with the top concept for each unsafe variable.
            let mut new_body_atoms = self.0.body_atoms.clone();
            for variable in variables {
                new_body_atoms.push(Atom::create(
                    safe_making_predicate.clone(),
                    vec![Term::Variable(variable)],
                ));
            }
            DLClause::create(self.0.head_atoms.clone(), new_body_atoms)
        }
    }

    pub fn get_changed_dl_clause(
        &self,
        head_atoms: Option<Vec<Atom>>,
        body_atoms: Option<Vec<Atom>>,
    ) -> DLClause {
        let head_atoms = head_atoms.unwrap_or_else(|| self.0.head_atoms.clone());
        let body_atoms = body_atoms.unwrap_or_else(|| self.0.body_atoms.clone());
        DLClause::create(head_atoms, body_atoms)
    }

    pub fn is_general_concept_inclusion(&self) -> bool {
        if self.0.head_atoms.is_empty() {
            // Not a GCI if all body atoms are data ranges; could also be an
            // asymmetry axiom of the form r(x,y) and r(y,x) -> bottom.
            if self.0.body_atoms.len() == 2
                && self.0.body_atoms[0].get_arity() == 2
                && self.0.body_atoms[1].get_arity() == 2
            {
                return false;
            }
            for body_atom in &self.0.body_atoms {
                if body_atom.get_arity() != 1 || !body_atom.get_dl_predicate().is_data_range() {
                    return true;
                }
            }
        }
        for head_atom in &self.0.head_atoms {
            let predicate = head_atom.get_dl_predicate();
            if predicate.is_at_least()
                || predicate.is_literal_concept()
                || predicate.is_annotated_equality()
                || predicate.is_node_id_less_equal_than()
                || predicate.is_node_ids_ascending_or_equal()
            {
                return true;
            }
            if predicate.is_equality() {
                // Could be a key, which we do not count as a GCI; check whether
                // the body uses the special "named" concept.
                for body_atom in &self.0.body_atoms {
                    let body_predicate = body_atom.get_dl_predicate();
                    if body_atom.get_arity() == 1 {
                        if let Some(concept) = body_predicate.as_atomic_concept() {
                            if concept == AtomicConcept::internal_named() {
                                return false;
                            }
                        }
                    }
                }
            }
            if predicate.is_data_range() {
                // Could be a data range inclusion or a universal, e.g.,
                // A -> for all dp.DR.
                for body_atom in &self.0.body_atoms {
                    if body_atom.get_arity() == 2 {
                        return true;
                    }
                }
                return false;
            }
            if predicate.is_role() {
                // Role inclusion.
                return false;
            }
        }
        false
    }

    pub fn is_atomic_concept_inclusion(&self) -> bool {
        if self.0.body_atoms.len() == 1 && self.0.head_atoms.len() == 1 {
            let body_atom = &self.0.body_atoms[0];
            let head_atom = &self.0.head_atoms[0];
            if body_atom.get_arity() == 1
                && head_atom.get_arity() == 1
                && body_atom.get_dl_predicate().is_atomic_concept()
                && head_atom.get_dl_predicate().is_atomic_concept()
            {
                let argument = body_atom.get_argument(0);
                return matches!(argument, Term::Variable(_)) && argument == head_atom.get_argument(0);
            }
        }
        false
    }

    pub fn is_atomic_role_inclusion(&self) -> bool {
        if self.0.body_atoms.len() == 1 && self.0.head_atoms.len() == 1 {
            let body_atom = &self.0.body_atoms[0];
            let head_atom = &self.0.head_atoms[0];
            if body_atom.get_arity() == 2
                && head_atom.get_arity() == 2
                && body_atom.get_dl_predicate().is_role()
                && head_atom.get_dl_predicate().is_role()
            {
                let argument0 = body_atom.get_argument(0);
                let argument1 = body_atom.get_argument(1);
                return matches!(argument0, Term::Variable(_))
                    && matches!(argument1, Term::Variable(_))
                    && argument0 != argument1
                    && argument0 == head_atom.get_argument(0)
                    && argument1 == head_atom.get_argument(1);
            }
        }
        false
    }

    pub fn is_atomic_role_inverse_inclusion(&self) -> bool {
        if self.0.body_atoms.len() == 1 && self.0.head_atoms.len() == 1 {
            let body_atom = &self.0.body_atoms[0];
            let head_atom = &self.0.head_atoms[0];
            if body_atom.get_arity() == 2
                && head_atom.get_arity() == 2
                && body_atom.get_dl_predicate().is_role()
                && head_atom.get_dl_predicate().is_role()
            {
                let argument0 = body_atom.get_argument(0);
                let argument1 = body_atom.get_argument(1);
                return matches!(argument0, Term::Variable(_))
                    && matches!(argument1, Term::Variable(_))
                    && argument0 != argument1
                    && argument0 == head_atom.get_argument(1)
                    && argument1 == head_atom.get_argument(0);
            }
        }
        false
    }

    pub fn is_functionality_axiom(&self) -> bool {
        if self.0.body_atoms.len() == 2 && self.0.head_atoms.len() == 1 {
            let atomic_role = self.get_body_atom(0).get_dl_predicate();
            if atomic_role.is_role()
                && self.get_body_atom(1).get_dl_predicate() == atomic_role
                && self.get_head_atom(0).get_dl_predicate().is_annotated_equality()
            {
                let x = self.get_body_atom(0).get_argument_variable(0);
                if let Some(x) = x {
                    if Term::Variable(x.clone()) == *self.get_body_atom(1).get_argument(0) {
                        let y1 = self.get_body_atom(0).get_argument_variable(1).cloned();
                        let y2 = self.get_body_atom(1).get_argument_variable(1).cloned();
                        let head_y1 = self.get_head_atom(0).get_argument_variable(0).cloned();
                        let head_y2 = self.get_head_atom(0).get_argument_variable(1).cloned();
                        return matching_functional_variables(y1, y2, head_y1, head_y2);
                    }
                }
            }
        }
        false
    }

    pub fn is_inverse_functionality_axiom(&self) -> bool {
        if self.get_body_length() == 2 && self.get_head_length() == 1 {
            let atomic_role = self.get_body_atom(0).get_dl_predicate();
            if atomic_role.is_role()
                && self.get_body_atom(1).get_dl_predicate() == atomic_role
                && self.get_head_atom(0).get_dl_predicate().is_annotated_equality()
            {
                let x = self.get_body_atom(0).get_argument_variable(1);
                if let Some(x) = x {
                    if Term::Variable(x.clone()) == *self.get_body_atom(1).get_argument(1) {
                        let y1 = self.get_body_atom(0).get_argument_variable(0).cloned();
                        let y2 = self.get_body_atom(1).get_argument_variable(0).cloned();
                        let head_y1 = self.get_head_atom(0).get_argument_variable(0).cloned();
                        let head_y2 = self.get_head_atom(0).get_argument_variable(1).cloned();
                        return matching_functional_variables(y1, y2, head_y1, head_y2);
                    }
                }
            }
        }
        false
    }

    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        let mut buffer = String::new();
        for (head_index, head_atom) in self.0.head_atoms.iter().enumerate() {
            if head_index != 0 {
                buffer.push_str(" v ");
            }
            buffer.push_str(&head_atom.to_string_prefixes(prefixes));
        }
        buffer.push_str(" :- ");
        for (body_index, body_atom) in self.0.body_atoms.iter().enumerate() {
            if body_index != 0 {
                buffer.push_str(", ");
            }
            buffer.push_str(&body_atom.to_string_prefixes(prefixes));
        }
        buffer
    }
}

/// Shared tail of the (inverse-)functionality checks: y1 and y2 are distinct
/// variables and {y1,y2} == {headY1,headY2} (in either order).
fn matching_functional_variables(
    y1: Option<Variable>,
    y2: Option<Variable>,
    head_y1: Option<Variable>,
    head_y2: Option<Variable>,
) -> bool {
    match (y1, y2, head_y1, head_y2) {
        (Some(y1), Some(y2), Some(head_y1), Some(head_y2)) => {
            y1 != y2
                && ((y1 == head_y1 && y2 == head_y2) || (y1 == head_y2 && y2 == head_y1))
        }
        _ => false,
    }
}

impl_display_prefixes!(DLClause);
