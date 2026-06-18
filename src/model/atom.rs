// Port of org.semanticweb.HermiT.model.Atom.

use std::collections::HashSet;

use crate::model::predicate::DLPredicate;
use crate::model::term::{Individual, Term, Variable};
use crate::prefixes::Prefixes;
use crate::{impl_display_prefixes, interned};

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct AtomData {
    dl_predicate: DLPredicate,
    arguments: Vec<Term>,
}

interned!(pub Atom => AtomData);

impl Atom {
    /// Creates an interned atom, checking that the predicate arity matches the
    /// number of arguments.
    pub fn create(dl_predicate: DLPredicate, arguments: Vec<Term>) -> Atom {
        assert!(
            dl_predicate.arity() == arguments.len(),
            "The arity of the predicate must be equal to the number of arguments."
        );
        Atom::intern(AtomData { dl_predicate, arguments })
    }

    pub fn get_dl_predicate(&self) -> &DLPredicate {
        &self.0.dl_predicate
    }
    pub fn get_arity(&self) -> usize {
        self.0.arguments.len()
    }
    pub fn get_argument(&self, argument_index: usize) -> &Term {
        &self.0.arguments[argument_index]
    }
    pub fn get_argument_variable(&self, argument_index: usize) -> Option<&Variable> {
        self.0.arguments[argument_index].as_variable()
    }
    pub fn get_variables<S: std::hash::BuildHasher>(
        &self,
        variables: &mut HashSet<Variable, S>,
    ) {
        for argument in self.0.arguments.iter().rev() {
            if let Term::Variable(v) = argument {
                variables.insert(v.clone());
            }
        }
    }
    pub fn get_individuals(&self, individuals: &mut HashSet<Individual>) {
        for argument in self.0.arguments.iter().rev() {
            if let Term::Individual(i) = argument {
                individuals.insert(i.clone());
            }
        }
    }
    pub fn contains_variable(&self, variable: &Variable) -> bool {
        self.0
            .arguments
            .iter()
            .rev()
            .any(|argument| matches!(argument, Term::Variable(v) if v == variable))
    }
    pub fn replace_dl_predicate(&self, new_dl_predicate: DLPredicate) -> Atom {
        Atom::create(new_dl_predicate, self.0.arguments.clone())
    }

    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        let mut buffer = String::new();
        let predicate = &self.0.dl_predicate;
        let is_infix = matches!(
            predicate,
            DLPredicate::Equality | DLPredicate::Inequality | DLPredicate::NodeIdLessEqualThan
        );
        if is_infix {
            buffer.push_str(&self.0.arguments[0].to_string_prefixes(prefixes));
            buffer.push(' ');
            buffer.push_str(&predicate.to_string_prefixes(prefixes));
            buffer.push(' ');
            buffer.push_str(&self.0.arguments[1].to_string_prefixes(prefixes));
        } else if let DLPredicate::AnnotatedEquality(annotated_equality) = predicate {
            buffer.push('[');
            buffer.push_str(&self.0.arguments[0].to_string_prefixes(prefixes));
            buffer.push(' ');
            buffer.push_str("==");
            buffer.push(' ');
            buffer.push_str(&self.0.arguments[1].to_string_prefixes(prefixes));
            buffer.push_str("]@atMost(");
            buffer.push_str(&annotated_equality.cardinality().to_string());
            buffer.push(' ');
            buffer.push_str(&annotated_equality.on_role().to_string_prefixes(prefixes));
            buffer.push(' ');
            buffer.push_str(&annotated_equality.to_concept().to_string_prefixes(prefixes));
            buffer.push_str(")(");
            buffer.push_str(&self.0.arguments[2].to_string_prefixes(prefixes));
            buffer.push(')');
        } else {
            buffer.push_str(&predicate.to_string_prefixes(prefixes));
            buffer.push('(');
            for (i, argument) in self.0.arguments.iter().enumerate() {
                if i != 0 {
                    buffer.push(',');
                }
                buffer.push_str(&argument.to_string_prefixes(prefixes));
            }
            buffer.push(')');
        }
        buffer
    }
}

impl_display_prefixes!(Atom);
