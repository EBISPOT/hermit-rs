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

use std::collections::{BTreeSet, HashMap, HashSet};

use horned_owl::model::ObjectPropertyExpression as OPE;

use super::{inverse_property, ObjectPropExpr};

/// The order in which labels are taken wherever an automaton enumerates them:
/// named properties before inverses, then by IRI. A minimised automaton numbers
/// its states by discovering them in this order, so its states, and the clauses
/// they become, depend only on its language.
pub(crate) fn label_order_key(ope: &ObjectPropExpr) -> (u8, String) {
    match ope {
        OPE::ObjectProperty(p) => (0, p.0.to_string()),
        OPE::InverseObjectProperty(p) => (1, p.0.to_string()),
    }
}

/// The most states a determinisation builds before giving up and keeping the
/// automaton as it is. The role automata of real ontologies determinise to a
/// handful of states; the bound only guards against a pathological role box.
const MAX_DETERMINISTIC_STATES: usize = 4096;

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

impl Automaton {
    /// The labels of the transitions, in label order, each once.
    fn labels(&self) -> Vec<ObjectPropExpr> {
        let mut labels: Vec<ObjectPropExpr> =
            self.transitions.iter().filter_map(|t| t.label.clone()).collect();
        labels.sort_by_cached_key(label_order_key);
        labels.dedup();
        labels
    }

    /// The automaton accepting the reversed words: every transition reversed
    /// and the initial and terminal flags exchanged. The labels stay as they
    /// are; [`mirrored_copy`] is the reversal that also inverts them.
    fn reversed(&self) -> Automaton {
        let mut reversed = Automaton::new();
        for state in &self.states {
            reversed.add_state(state.terminal, state.initial);
        }
        for t in &self.transitions {
            reversed.add_transition(t.end, t.label.clone(), t.start);
        }
        reversed
    }

    /// The ε-free deterministic automaton with the same language, by the
    /// subset construction from the ε-closure of the initial states. The
    /// subsets are numbered as they are discovered, taking the labels in the
    /// order of `labels`, so the numbering depends only on the automaton's
    /// structure. Only subsets that a transition leads to are built, so no
    /// state is unreachable. `None` when more than
    /// [`MAX_DETERMINISTIC_STATES`] subsets arise.
    fn determinized(&self, labels: &[ObjectPropExpr]) -> Option<Automaton> {
        let n = self.states.len();
        let index: HashMap<&ObjectPropExpr, usize> =
            labels.iter().enumerate().map(|(i, l)| (l, i)).collect();
        let mut epsilon: Vec<Vec<State>> = vec![Vec::new(); n];
        let mut labelled: Vec<Vec<(usize, State)>> = vec![Vec::new(); n];
        for t in &self.transitions {
            match &t.label {
                None => epsilon[t.start].push(t.end),
                Some(label) => labelled[t.start].push((index[label], t.end)),
            }
        }
        let closure = |seed: Vec<State>| -> BTreeSet<State> {
            let mut set: BTreeSet<State> = BTreeSet::new();
            let mut pending = seed;
            while let Some(state) = pending.pop() {
                if set.insert(state) {
                    pending.extend(epsilon[state].iter().copied());
                }
            }
            set
        };
        let accepting = |subset: &BTreeSet<State>| subset.iter().any(|&s| self.states[s].terminal);

        let mut result = Automaton::new();
        let mut ids: HashMap<BTreeSet<State>, State> = HashMap::new();
        let mut subsets: Vec<BTreeSet<State>> = Vec::new();
        let start = closure(self.initials());
        ids.insert(start.clone(), result.add_state(true, accepting(&start)));
        subsets.push(start);
        let mut from = 0;
        while from < subsets.len() {
            let mut seeds: Vec<Vec<State>> = vec![Vec::new(); labels.len()];
            for &state in &subsets[from] {
                for &(label, end) in &labelled[state] {
                    seeds[label].push(end);
                }
            }
            for (label, seed) in seeds.into_iter().enumerate() {
                if seed.is_empty() {
                    continue;
                }
                let target = closure(seed);
                let to = match ids.get(&target) {
                    Some(&to) => to,
                    None => {
                        if subsets.len() >= MAX_DETERMINISTIC_STATES {
                            return None;
                        }
                        let to = result.add_state(false, accepting(&target));
                        ids.insert(target.clone(), to);
                        subsets.push(target);
                        to
                    }
                };
                result.add_transition(from, Some(labels[label].clone()), to);
            }
            from += 1;
        }
        Some(result)
    }

    /// The minimal deterministic automaton with this automaton's language,
    /// brought to one initial and one terminal state.
    ///
    /// It is Brzozowski's: determinising the reversal and then the reversal of
    /// that gives the minimal automaton, in which no state is unreachable or
    /// dead. Its states are numbered in the order the subset construction
    /// discovers them, following [`label_order_key`], so equal languages give
    /// equal automata whatever the shape they were assembled in. The one
    /// initial state is the construction's; when the terminal states are not
    /// exactly one, a fresh terminal state is reached from each by an ε
    /// transition, as every consumer of an automaton expects. Should the
    /// determinisation exceed [`MAX_DETERMINISTIC_STATES`], the automaton is
    /// returned as it is.
    pub fn minimized(&self) -> Automaton {
        let labels = self.labels();
        let minimal = self
            .reversed()
            .determinized(&labels)
            .and_then(|reversed| reversed.reversed().determinized(&labels));
        match minimal {
            Some(minimal) => normalized(minimal),
            None => self.clone(),
        }
    }
}

/// `automaton` with exactly one terminal state: its own when it has one, else a
/// fresh one that every former terminal state reaches by an ε transition.
fn normalized(mut automaton: Automaton) -> Automaton {
    let terminals = automaton.terminals();
    if terminals.len() != 1 {
        let terminal = automaton.add_state(false, true);
        for state in terminals {
            automaton.states[state].terminal = false;
            automaton.add_transition(state, None, terminal);
        }
    }
    automaton
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

/// Whether `a` accepts `word` (tests only).
#[cfg(test)]
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

#[cfg(test)]
mod read_off_tests {
    use super::*;
    use horned_owl::model::Build;

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

#[cfg(test)]
mod minimization_tests {
    use super::*;
    use horned_owl::model::Build;

    fn labels() -> [ObjectPropExpr; 2] {
        let b = Build::new_arc();
        [
            OPE::ObjectProperty(b.object_property("http://ex/l")),
            OPE::ObjectProperty(b.object_property("http://ex/p")),
        ]
    }

    /// Every word of up to `length` letters over `alphabet`.
    fn words(alphabet: &[ObjectPropExpr], length: usize) -> Vec<Vec<ObjectPropExpr>> {
        let mut words: Vec<Vec<ObjectPropExpr>> = vec![Vec::new()];
        let mut frontier = words.clone();
        for _ in 0..length {
            frontier = frontier
                .iter()
                .flat_map(|w| alphabet.iter().map(move |l| [w.clone(), vec![l.clone()]].concat()))
                .collect();
            words.extend(frontier.iter().cloned());
        }
        words
    }

    /// `p+` as a two-state automaton: `initial -p-> final -ε-> initial`.
    fn transitive(p: &ObjectPropExpr) -> Automaton {
        let mut a = Automaton::new();
        let initial = a.add_state(true, false);
        let terminal = a.add_state(false, true);
        a.add_transition(initial, Some(p.clone()), terminal);
        a.add_transition(terminal, None, initial);
        a
    }

    /// The automaton of `l` under `l ∘ p ⊑ l`, `p ∘ l ⊑ l`, `l ∘ l ⊑ l` and
    /// `p ∘ p ⊑ p`, assembled as the role-box construction assembles it: a
    /// skeleton with one path per chain, `p+` spliced in for each occurrence
    /// of `p`, and an ε edge for the transitivity of `l`. Its language is
    /// `p* l (l | p)*`.
    fn located_in(l: &ObjectPropExpr, p: &ObjectPropExpr, splice_first: bool) -> Automaton {
        let mut a = Automaton::new();
        let initial = a.add_state(true, false);
        let terminal = a.add_state(false, true);
        let p_plus = transitive(p);
        if splice_first {
            automata_connector(&mut a, &p_plus, terminal, initial);
            automata_connector(&mut a, &p_plus, initial, terminal);
        }
        a.add_transition(initial, Some(l.clone()), terminal);
        a.add_transition(terminal, None, initial);
        if !splice_first {
            automata_connector(&mut a, &p_plus, initial, terminal);
            automata_connector(&mut a, &p_plus, terminal, initial);
        }
        a
    }

    fn accepted(a: &Automaton, alphabet: &[ObjectPropExpr]) -> Vec<Vec<ObjectPropExpr>> {
        words(alphabet, 5).into_iter().filter(|w| accepts(a, w)).collect()
    }

    #[test]
    fn minimized_automaton_keeps_the_language_and_shrinks() {
        let [l, p] = labels();
        let original = located_in(&l, &p, false);
        assert_eq!(original.states().len(), 6);
        let minimal = original.minimized();
        assert_eq!(accepted(&original, &[l.clone(), p.clone()]), accepted(&minimal, &[l.clone(), p.clone()]));
        // `p* l (l | p)*`: before the first `l`, and after it.
        assert_eq!(minimal.states().len(), 2);
        assert_eq!(minimal.delta().len(), 4);
        assert_eq!(minimal.initials(), vec![0]);
        assert_eq!(minimal.terminals(), vec![1]);
        assert!(minimal.delta().iter().all(|t| t.label.is_some()));

        let p_plus = transitive(&p).minimized();
        let only_p = std::slice::from_ref(&p);
        assert_eq!(accepted(&transitive(&p), only_p), accepted(&p_plus, only_p));
        assert_eq!((p_plus.states().len(), p_plus.delta().len()), (2, 2));
    }

    #[test]
    fn minimized_automaton_depends_only_on_the_language() {
        let [l, p] = labels();
        let one = located_in(&l, &p, false).minimized();
        let other = located_in(&l, &p, true).minimized();
        assert_eq!(one.delta(), other.delta());
        assert_eq!(one.initials(), other.initials());
        assert_eq!(one.terminals(), other.terminals());
        assert_eq!(one.minimized().delta(), one.delta());
    }

    #[test]
    fn minimized_automaton_has_one_initial_and_one_terminal_state() {
        let [l, p] = labels();
        // `l | p+`: the minimal automaton has two terminal states, one that
        // accepts only the empty word and one that also accepts `p*`.
        let mut a = Automaton::new();
        let initial = a.add_state(true, false);
        let after_l = a.add_state(false, true);
        let after_p = a.add_state(false, true);
        a.add_transition(initial, Some(l.clone()), after_l);
        a.add_transition(initial, Some(p.clone()), after_p);
        a.add_transition(after_p, Some(p.clone()), after_p);
        let minimal = a.minimized();
        assert_eq!(accepted(&a, &[l.clone(), p.clone()]), accepted(&minimal, &[l, p]));
        assert_eq!(minimal.initials().len(), 1);
        assert_eq!(minimal.terminals().len(), 1);
        assert_eq!(minimal.final_state(), minimal.states().len() - 1);
        assert_eq!(minimal.delta().iter().filter(|t| t.label.is_none()).count(), 2);
    }

    #[test]
    fn mirrored_minimized_automaton_accepts_the_inverse_words() {
        let [l, p] = labels();
        let minimal = located_in(&l, &p, false).minimized();
        let mirrored = mirrored_copy(&minimal).minimized();
        let inverse: Vec<ObjectPropExpr> = [&l, &p].iter().map(|x| inverse_property(x)).collect();
        for word in words(&[l.clone(), p.clone()], 5) {
            let reversed: Vec<ObjectPropExpr> = word.iter().rev().map(inverse_property).collect();
            assert_eq!(accepts(&minimal, &word), accepts(&mirrored, &reversed), "{word:?}");
        }
        assert_eq!(mirrored.states().len(), 2);
        assert!(mirrored.delta().iter().all(|t| inverse.contains(t.label.as_ref().unwrap())));
    }
}

