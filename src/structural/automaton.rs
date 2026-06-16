// A minimal nondeterministic finite automaton over object-property-expression
// labels, mirroring the subset of the `rationals.Automaton` API that HermiT's
// `ObjectPropertyInclusionManager` relies on.
//
// HermiT builds, for every (complex) object property, an automaton whose
// language is the set of role chains implied to be sub-roles of it; the
// `∀R.C` restrictions are then rewritten into per-state concept inclusions
// driven by this automaton (see `object_property_inclusion_manager`). The
// upstream code uses the external `rationals` library; we reproduce only the
// operations it actually calls.
//
// States are indices into the automaton's own `states` vector (`State` in
// `rationals` is an object with per-automaton identity; an index reproduces
// that identity faithfully because each automaton owns its own numbering).
// A transition label of `None` is an epsilon (ε) transition.

use std::collections::HashMap;

use super::{inverse_property, ObjectPropExpr};

pub type State = usize;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Transition {
    pub start: State,
    pub label: Option<ObjectPropExpr>,
    pub end: State,
}

#[derive(Clone, Debug)]
struct StateData {
    initial: bool,
    terminal: bool,
}

#[derive(Clone, Debug, Default)]
pub struct Automaton {
    states: Vec<StateData>,
    transitions: Vec<Transition>,
}

impl Automaton {
    pub fn new() -> Automaton {
        Automaton { states: Vec::new(), transitions: Vec::new() }
    }

    /// `Automaton.addState(boolean initial, boolean terminal)`.
    pub fn add_state(&mut self, initial: bool, terminal: bool) -> State {
        self.states.push(StateData { initial, terminal });
        self.states.len() - 1
    }

    /// `Automaton.addTransition` — the delta set, so duplicates are ignored.
    pub fn add_transition(&mut self, start: State, label: Option<ObjectPropExpr>, end: State) {
        let transition = Transition { start, label, end };
        if !self.transitions.contains(&transition) {
            self.transitions.push(transition);
        }
    }

    /// `Automaton.states()`.
    pub fn states(&self) -> Vec<State> {
        (0..self.states.len()).collect()
    }

    /// `Automaton.delta()` — all transitions.
    pub fn delta(&self) -> Vec<Transition> {
        self.transitions.clone()
    }

    /// `Automaton.initials()`.
    pub fn initials(&self) -> Vec<State> {
        (0..self.states.len()).filter(|&s| self.states[s].initial).collect()
    }

    /// `Automaton.terminals()`.
    pub fn terminals(&self) -> Vec<State> {
        (0..self.states.len()).filter(|&s| self.states[s].terminal).collect()
    }

    pub fn is_initial(&self, state: State) -> bool {
        self.states[state].initial
    }

    pub fn is_terminal(&self, state: State) -> bool {
        self.states[state].terminal
    }

    /// The single initial state (HermiT automata are normalized to one each).
    pub fn initial_state(&self) -> State {
        self.initials()[0]
    }

    /// The single terminal state.
    pub fn final_state(&self) -> State {
        self.terminals()[0]
    }

    /// `Automaton.deltaFrom(from, to)`.
    pub fn delta_from(&self, from: State, to: State) -> Vec<Transition> {
        self.transitions
            .iter()
            .filter(|t| t.start == from && t.end == to)
            .cloned()
            .collect()
    }

    /// `ObjectPropertyInclusionManager.addNewTransition`: adds a fresh
    /// non-initial/non-terminal state and a transition into it.
    pub fn add_new_transition(&mut self, from: State, label: ObjectPropExpr) -> State {
        let to = self.add_state(false, false);
        self.add_transition(from, Some(label), to);
        to
    }
}

/// `ObjectPropertyInclusionManager.getMirroredCopy`: the reverse automaton,
/// swapping initial/terminal flags and inverting every property label.
pub fn mirrored_copy(automaton: &Automaton) -> Automaton {
    let mut mirrored = Automaton::new();
    let mut map: HashMap<State, State> = HashMap::new();
    for state in automaton.states() {
        let new_state =
            mirrored.add_state(automaton.is_terminal(state), automaton.is_initial(state));
        map.insert(state, new_state);
    }
    for transition in automaton.delta() {
        let label = transition.label.as_ref().map(inverse_property);
        mirrored.add_transition(map[&transition.end], label, map[&transition.start]);
    }
    mirrored
}

/// `ObjectPropertyInclusionManager.getDisjointUnion`: copies `other`'s states
/// (as non-initial/non-terminal) and transitions into `automaton`, returning
/// the old→new state mapping.
fn disjoint_union(automaton: &mut Automaton, other: &Automaton) -> HashMap<State, State> {
    let mut map: HashMap<State, State> = HashMap::new();
    for state in other.states() {
        map.insert(state, automaton.add_state(false, false));
    }
    for transition in other.delta() {
        automaton.add_transition(map[&transition.start], transition.label, map[&transition.end]);
    }
    map
}

/// `ObjectPropertyInclusionManager.useStandardAutomataConnector`: splices
/// `smaller` into `bigger` in place of the transition `(from, to)` via ε edges.
pub fn automata_connector(bigger: &mut Automaton, smaller: &Automaton, from: State, to: State) {
    let map = disjoint_union(bigger, smaller);
    let old_start_of_smaller = map[&smaller.initial_state()];
    let old_final_of_smaller = map[&smaller.final_state()];
    bigger.add_transition(from, None, old_start_of_smaller);
    bigger.add_transition(old_final_of_smaller, None, to);
}
