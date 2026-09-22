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

use std::collections::{HashMap, HashSet};

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

    /// First labels of accepted words using only `live` labels, plus whether
    /// the empty word is accepted. Reverse reachability excludes prefixes whose
    /// suffix cannot occur; epsilon cycles are visited only once.
    pub(crate) fn live_first_labels(
        &self,
        live: &HashSet<ObjectPropExpr>,
    ) -> (bool, HashSet<ObjectPropExpr>) {
        let mut forward = vec![Vec::new(); self.states.len()];
        let mut backward = vec![Vec::new(); self.states.len()];
        for t in &self.transitions {
            if t.label.as_ref().is_none_or(|label| live.contains(label)) {
                forward[t.start].push(t);
                backward[t.end].push(t.start);
            }
        }
        let mut productive = vec![false; self.states.len()];
        let mut pending = self.terminals();
        while let Some(state) = pending.pop() {
            if !productive[state] {
                productive[state] = true;
                pending.extend(&backward[state]);
            }
        }
        let mut visited = vec![false; self.states.len()];
        let mut pending = self.initials();
        let mut labels = HashSet::new();
        let mut nullable = false;
        while let Some(state) = pending.pop() {
            if visited[state] || !productive[state] {
                continue;
            }
            visited[state] = true;
            nullable |= self.is_terminal(state);
            for t in &forward[state] {
                if productive[t.end] {
                    if let Some(label) = &t.label {
                        labels.insert(label.clone());
                    } else {
                        pending.push(t.end);
                    }
                }
            }
        }
        (nullable, labels)
    }

    /// Keep the paths whose labels can be generated by the permanent DL
    /// program. Used only for fresh read-off concepts, not ontology constraints.
    pub(crate) fn restricted_to_labels(&self, live: &HashSet<ObjectPropExpr>) -> Self {
        let edges: Vec<_> = self
            .transitions
            .iter()
            .filter(|t| t.label.as_ref().is_none_or(|label| live.contains(label)))
            .collect();
        let mut forward = vec![Vec::new(); self.states.len()];
        let mut backward = vec![Vec::new(); self.states.len()];
        for t in &edges {
            forward[t.start].push(t.end);
            backward[t.end].push(t.start);
        }
        let reach = |initial: Vec<usize>, links: &[Vec<usize>]| {
            let mut seen = vec![false; links.len()];
            let mut pending = initial;
            while let Some(s) = pending.pop() {
                if !seen[s] {
                    seen[s] = true;
                    pending.extend(&links[s]);
                }
            }
            seen
        };
        let from_start = reach(self.initials(), &forward);
        let to_end = reach(self.terminals(), &backward);
        let mut result = Self::new();
        let mut states = vec![None; self.states.len()];
        for s in self.states() {
            if (from_start[s] && to_end[s]) || self.is_initial(s) || self.is_terminal(s) {
                states[s] = Some(result.add_state(self.is_initial(s), self.is_terminal(s)));
            }
        }
        for t in edges {
            if from_start[t.start] && to_end[t.end] {
                result.add_transition(
                    states[t.start].unwrap(),
                    t.label.clone(),
                    states[t.end].unwrap(),
                );
            }
        }
        result
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

#[cfg(test)]
mod read_off_tests {
    use super::*;
    use horned_owl::model::{Build, ObjectPropertyExpression as OPE};

    fn accepts(a: &Automaton, word: &[ObjectPropExpr]) -> bool {
        let mut pending: Vec<_> = a.initials().into_iter().map(|s| (s, 0)).collect();
        let mut seen = HashSet::new();
        while let Some((s, pos)) = pending.pop() {
            if !seen.insert((s, pos)) {
                continue;
            }
            if pos == word.len() && a.is_terminal(s) {
                return true;
            }
            for t in a.transitions.iter().filter(|t| t.start == s) {
                match &t.label {
                    None => pending.push((t.end, pos)),
                    Some(label) if word.get(pos) == Some(label) => pending.push((t.end, pos + 1)),
                    _ => (),
                }
            }
        }
        false
    }

    #[test]
    fn restricted_automata_preserve_live_words_and_epsilon_cycles() {
        let b = Build::new_arc();
        let p = OPE::ObjectProperty(b.object_property("http://ex/p"));
        let q = OPE::InverseObjectProperty(b.object_property("http://ex/q"));
        let dead = OPE::ObjectProperty(b.object_property("http://ex/dead"));
        let live = HashSet::from([p.clone(), q.clone()]);
        for nullable in [false, true] {
            let mut original = Automaton::new();
            let start = original.add_state(true, nullable);
            let prefix = original.add_state(false, false);
            let end = original.add_state(false, true);
            let unused = original.add_state(false, false);
            original.add_transition(start, None, prefix);
            original.add_transition(prefix, None, start);
            original.add_transition(prefix, Some(p.clone()), end);
            original.add_transition(end, Some(q.clone()), end);
            original.add_transition(start, Some(dead.clone()), unused);
            original.add_transition(unused, Some(p.clone()), end);
            let restricted = original.restricted_to_labels(&live);
            assert_eq!(restricted.states().len(), 3);
            assert_eq!(
                restricted.live_first_labels(&live),
                (nullable, HashSet::from([p.clone()]))
            );
            for length in 0..6 {
                for bits in 0..(1 << length) {
                    let word: Vec<_> = (0..length)
                        .map(|i| {
                            if bits & (1 << i) == 0 {
                                p.clone()
                            } else {
                                q.clone()
                            }
                        })
                        .collect();
                    assert_eq!(accepts(&original, &word), accepts(&restricted, &word));
                }
            }
        }
    }
}
