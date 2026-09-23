// A focused, self-contained finite-automaton engine over Unicode code points,
// the Rust analogue of the parts of the dk.brics `automaton` library that HermiT
// uses to decide string/anyURI/rdf:PlainLiteral value-space emptiness and
// cardinality (`RDFPlainLiteralPatternValueSpaceSubset` and the
// `RDFPlainLiteralDatatypeHandler` automaton branch).
//
// dk.brics represents an automaton with interval-labelled transitions over the
// UTF-16 char range; we do the same over Rust `char` code points (`0..=0x10FFFF`),
// which is sound for the value spaces in question (the only supplementary handling
// HermiT needs is membership of `.`/char classes, all of which we model by
// code-point intervals). We provide exactly the operations the Java port calls:
//
//   * `RegExp(pattern).toAutomaton()`            -> `Automaton::from_xsd_pattern`
//   * `Automaton.intersection(other)`            -> `Automaton::intersection`
//   * `Automaton.minus(other)`  (a \ b = a ∩ ¬b) -> `Automaton::minus`
//   * `Automaton.complement()`                   -> `Automaton::complement`
//   * `Automaton.isEmpty()`                      -> `Automaton::is_empty`
//   * `Automaton.getFiniteStrings(n)`            -> `Automaton::finite_strings`
//   * `Automaton.concatenate(other)`             -> `Automaton::concatenate`
//   * `Automaton.repeat()` / `repeat(min[,max])` -> `Automaton::repeat*`
//   * `Automaton.union(other)`                   -> `Automaton::union`
//
// The XSD-Schema regular-expression flavour translated by `from_xsd_pattern`
// follows XSD 1.1 Part 2 Appendix G, where dk.brics `RegExp` as HermiT uses it
// differs (`.`, `\d` and `\w` have their XSD meaning over every character):
// anchored whole-string match, the XSD multi-character escapes
// (`\d \D \w \W \s \S`, the XML-name escapes `\i \I \c \C`), the category/block
// escapes `\p{...}`/`\P{...}` (the common categories), single-character escapes,
// char classes with ranges/negation/class-subtraction, the quantifiers
// `? * + {m} {m,} {m,n}`, grouping and alternation.
//
// Everything here is sound for the emptiness/cardinality questions: an automaton
// is built to recognise *exactly* the pattern's language (so an empty
// intersection is a real clash), and any pattern syntax we cannot translate makes
// `from_xsd_pattern` return `None`, which the caller treats as "undecided" (never
// a false clash).
#![allow(dead_code)]

use std::collections::{BTreeSet, HashMap, VecDeque};

/// The largest Unicode scalar value, as a `u32`. Our symbol alphabet is
/// `0..=MAX_CP` (with surrogates excluded by construction since they cannot label
/// a transition reached from a `char`).
const MAX_CP: u32 = 0x10_FFFF;

/// The combined-alphabet separator HermiT uses between the string part and the
/// language-tag part of an rdf:PlainLiteral value (`SEPARATOR=''`). It must
/// be a code point that never appears in any string/langtag sub-language; U+0001
/// is excluded from every XSD string automaton, so it serves as a clean separator.
pub const SEPARATOR: u32 = 0x0001;

/// A transition: on any symbol in `[min, max]` (inclusive) go to state `to`.
#[derive(Clone, Copy, Debug)]
struct Transition {
    min: u32,
    max: u32,
    to: usize,
}

/// A nondeterministic finite automaton with interval-labelled transitions and
/// explicit epsilon moves. States are indices into `trans`/`eps`/`accept`.
#[derive(Clone, Debug)]
pub struct Automaton {
    start: usize,
    trans: Vec<Vec<Transition>>,
    eps: Vec<Vec<usize>>,
    accept: Vec<bool>,
    /// Set once the automaton is known to be deterministic and complete-free of
    /// epsilon moves (after `determinize`). Purely an optimisation hint.
    deterministic: bool,
}

impl Automaton {
    fn new() -> Automaton {
        Automaton { start: 0, trans: vec![], eps: vec![], accept: vec![], deterministic: false }
    }

    fn add_state(&mut self) -> usize {
        self.trans.push(Vec::new());
        self.eps.push(Vec::new());
        self.accept.push(false);
        self.trans.len() - 1
    }

    /// The automaton recognising exactly the empty language (no accepting state).
    pub fn empty_language() -> Automaton {
        let mut a = Automaton::new();
        let s = a.add_state();
        a.start = s;
        a
    }

    /// The automaton recognising exactly `{ "" }` (epsilon only).
    pub fn epsilon() -> Automaton {
        let mut a = Automaton::new();
        let s = a.add_state();
        a.start = s;
        a.accept[s] = true;
        a
    }

    /// The automaton recognising exactly the one-symbol words in `[min, max]`.
    pub fn char_range(min: u32, max: u32) -> Automaton {
        let mut a = Automaton::new();
        let s = a.add_state();
        let e = a.add_state();
        a.start = s;
        if min <= max {
            a.trans[s].push(Transition { min, max, to: e });
            a.accept[e] = true;
        }
        a
    }

    /// The automaton recognising the single literal character `c`.
    pub fn char(c: u32) -> Automaton {
        Automaton::char_range(c, c)
    }

    /// The automaton recognising the literal string `s` (over its code points).
    pub fn literal(s: &str) -> Automaton {
        let mut a = Automaton::epsilon();
        for c in s.chars() {
            a = a.concatenate(&Automaton::char(c as u32));
        }
        a
    }

    /// The automaton recognising a word in any of the given (already-sorted or
    /// unsorted) inclusive code-point ranges. Empty input ⇒ empty language.
    pub fn ranges(ranges: &[(u32, u32)]) -> Automaton {
        let mut a = Automaton::new();
        let s = a.add_state();
        let e = a.add_state();
        a.start = s;
        let mut any = false;
        for &(min, max) in ranges {
            if min <= max {
                a.trans[s].push(Transition { min, max, to: e });
                any = true;
            }
        }
        a.accept[e] = any;
        a
    }

    // ---- structural combinators (Thompson construction over NFAs) -----------

    /// Concatenation `self · other`.
    pub fn concatenate(&self, other: &Automaton) -> Automaton {
        let mut a = self.clone();
        let offset = a.trans.len();
        a.append_states(other);
        for s in 0..self.trans.len() {
            if self.accept[s] {
                a.accept[s] = false;
                a.eps[s].push(other.start + offset);
            }
        }
        a.deterministic = false;
        a
    }

    /// Union `self ∪ other`.
    pub fn union(&self, other: &Automaton) -> Automaton {
        let mut a = self.clone();
        let offset = a.trans.len();
        a.append_states(other);
        let new_start = a.add_state();
        a.eps[new_start].push(self.start);
        a.eps[new_start].push(other.start + offset);
        a.start = new_start;
        a.deterministic = false;
        a
    }

    /// Kleene star `self*`.
    pub fn repeat(&self) -> Automaton {
        let mut a = self.clone();
        let new_start = a.add_state();
        a.accept[new_start] = true;
        a.eps[new_start].push(self.start);
        // Every original accepting state loops back to the original start.
        for s in 0..self.trans.len() {
            if self.accept[s] {
                a.eps[s].push(self.start);
            }
        }
        a.start = new_start;
        a.deterministic = false;
        a
    }

    /// `self{min,}` (at least `min` repetitions).
    pub fn repeat_min(&self, min: usize) -> Automaton {
        self.repeat_range(min, min).concatenate(&self.repeat())
    }

    /// `self{min,max}` (between `min` and `max` repetitions, inclusive).
    pub fn repeat_range(&self, min: usize, max: usize) -> Automaton {
        if max < min {
            return Automaton::empty_language();
        }
        // One copy after another, in time linear in the copies: the accepting
        // states of the copies so far lead to the next copy, and stay
        // accepting once there are `min` copies (the optional tail).
        let mut a = Automaton::epsilon();
        let mut finals = vec![a.start];
        let own_finals: Vec<usize> = (0..self.trans.len()).filter(|&s| self.accept[s]).collect();
        for copy in 0..max {
            let offset = a.trans.len();
            a.append_states(self);
            for &f in &finals {
                a.eps[f].push(self.start + offset);
                if copy < min {
                    a.accept[f] = false;
                }
            }
            finals = own_finals.iter().map(|&s| s + offset).collect();
        }
        a.deterministic = false;
        a
    }

    /// `self?` (zero or one).
    pub fn optional(&self) -> Automaton {
        self.union(&Automaton::epsilon())
    }

    /// Append `other`'s states (renumbered) onto `self`, leaving `self.start`
    /// and accepting flags untouched. Returns nothing; caller wires epsilons.
    fn append_states(&mut self, other: &Automaton) {
        let offset = self.trans.len();
        for s in 0..other.trans.len() {
            let ts: Vec<Transition> = other.trans[s]
                .iter()
                .map(|t| Transition { min: t.min, max: t.max, to: t.to + offset })
                .collect();
            let es: Vec<usize> = other.eps[s].iter().map(|&e| e + offset).collect();
            self.trans.push(ts);
            self.eps.push(es);
            self.accept.push(other.accept[s]);
        }
    }

    // ---- determinisation, intersection, complement --------------------------

    /// The epsilon-closure of a set of NFA states.
    fn eps_closure(&self, states: &BTreeSet<usize>) -> BTreeSet<usize> {
        let mut stack: Vec<usize> = states.iter().copied().collect();
        let mut closure: BTreeSet<usize> = states.clone();
        while let Some(s) = stack.pop() {
            for &e in &self.eps[s] {
                if closure.insert(e) {
                    stack.push(e);
                }
            }
        }
        closure
    }

    /// Subset-construction determinisation over interval transitions. The result
    /// is a complete-free (no dead-but-present) DFA: missing transitions are
    /// implicitly to a (non-existent) sink. Used before complement, which adds
    /// the explicit sink.
    fn determinize(&self) -> Automaton {
        let mut dfa = Automaton::new();
        let mut mapping: HashMap<BTreeSet<usize>, usize> = HashMap::new();
        let start_set = self.eps_closure(&BTreeSet::from([self.start]));
        let start_id = dfa.add_state();
        mapping.insert(start_set.clone(), start_id);
        dfa.start = start_id;
        let mut queue: VecDeque<BTreeSet<usize>> = VecDeque::new();
        queue.push_back(start_set);
        while let Some(set) = queue.pop_front() {
            let id = mapping[&set];
            dfa.accept[id] = set.iter().any(|&s| self.accept[s]);
            // Collect the boundary points of all outgoing intervals to partition
            // the alphabet into maximal homogeneous sub-intervals.
            let mut points: BTreeSet<u32> = BTreeSet::new();
            for &s in &set {
                for t in &self.trans[s] {
                    points.insert(t.min);
                    if t.max < MAX_CP {
                        points.insert(t.max + 1);
                    }
                }
            }
            // For each elementary interval [p, next_p-1], compute the target set.
            let pts: Vec<u32> = points.into_iter().collect();
            for i in 0..pts.len() {
                let lo = pts[i];
                let hi = if i + 1 < pts.len() { pts[i + 1] - 1 } else { MAX_CP };
                let mut target: BTreeSet<usize> = BTreeSet::new();
                for &s in &set {
                    for t in &self.trans[s] {
                        if t.min <= lo && hi <= t.max {
                            target.insert(t.to);
                        }
                    }
                }
                if target.is_empty() {
                    continue;
                }
                let closed = self.eps_closure(&target);
                let to = match mapping.get(&closed) {
                    Some(&id) => id,
                    None => {
                        let id = dfa.add_state();
                        mapping.insert(closed.clone(), id);
                        queue.push_back(closed);
                        id
                    }
                };
                dfa.trans[id].push(Transition { min: lo, max: hi, to });
            }
        }
        dfa.deterministic = true;
        dfa
    }

    /// Product-construction intersection `self ∩ other`.
    pub fn intersection(&self, other: &Automaton) -> Automaton {
        let a = self.determinize();
        let b = other.determinize();
        let mut out = Automaton::new();
        let mut mapping: HashMap<(usize, usize), usize> = HashMap::new();
        let start = (a.start, b.start);
        let start_id = out.add_state();
        mapping.insert(start, start_id);
        out.start = start_id;
        let mut queue: VecDeque<(usize, usize)> = VecDeque::new();
        queue.push_back(start);
        while let Some((sa, sb)) = queue.pop_front() {
            let id = mapping[&(sa, sb)];
            out.accept[id] = a.accept[sa] && b.accept[sb];
            // Overlap each pair of transitions.
            for ta in &a.trans[sa] {
                for tb in &b.trans[sb] {
                    let lo = ta.min.max(tb.min);
                    let hi = ta.max.min(tb.max);
                    if lo > hi {
                        continue;
                    }
                    let key = (ta.to, tb.to);
                    let to = match mapping.get(&key) {
                        Some(&id) => id,
                        None => {
                            let nid = out.add_state();
                            mapping.insert(key, nid);
                            queue.push_back(key);
                            nid
                        }
                    };
                    out.trans[id].push(Transition { min: lo, max: hi, to });
                }
            }
        }
        out.deterministic = true;
        out
    }

    /// Complement within the full alphabet `0..=MAX_CP`. `self` is determinised
    /// and completed with a sink state, then accepting flags are flipped.
    pub fn complement(&self) -> Automaton {
        let mut dfa = self.determinize();
        // Add a sink state; every gap in every state's outgoing intervals goes to
        // the sink, and the sink loops to itself over the whole alphabet.
        let sink = dfa.add_state();
        dfa.trans[sink].push(Transition { min: 0, max: MAX_CP, to: sink });
        let n = dfa.trans.len();
        for s in 0..n {
            if s == sink {
                continue;
            }
            // Sort the existing intervals and fill the gaps with sink transitions.
            let mut ivs: Vec<(u32, u32, usize)> =
                dfa.trans[s].iter().map(|t| (t.min, t.max, t.to)).collect();
            ivs.sort_by_key(|x| x.0);
            let mut next: u32 = 0;
            let mut fills: Vec<Transition> = Vec::new();
            for (min, max, _to) in &ivs {
                if *min > next {
                    fills.push(Transition { min: next, max: min - 1, to: sink });
                }
                next = max.saturating_add(1);
            }
            if next <= MAX_CP {
                fills.push(Transition { min: next, max: MAX_CP, to: sink });
            }
            dfa.trans[s].extend(fills);
        }
        for s in 0..n {
            dfa.accept[s] = !dfa.accept[s];
        }
        dfa.deterministic = true;
        dfa
    }

    /// `self \ other = self ∩ ¬other` (dk.brics `Automaton.minus`).
    pub fn minus(&self, other: &Automaton) -> Automaton {
        self.intersection(&other.complement())
    }

    // ---- emptiness and cardinality ------------------------------------------

    /// Whether the language is empty (no accepting state reachable from start).
    pub fn is_empty(&self) -> bool {
        let mut seen = vec![false; self.trans.len()];
        let start_closure = self.eps_closure(&BTreeSet::from([self.start]));
        let mut stack: Vec<usize> = start_closure.into_iter().collect();
        for &s in &stack {
            seen[s] = true;
        }
        while let Some(s) = stack.pop() {
            if self.accept[s] {
                return false;
            }
            for t in &self.trans[s] {
                if !seen[t.to] {
                    seen[t.to] = true;
                    stack.push(t.to);
                }
            }
            for &e in &self.eps[s] {
                if !seen[e] {
                    seen[e] = true;
                    stack.push(e);
                }
            }
        }
        true
    }

    /// The exact number of distinct accepted words, or `None` when the language
    /// is infinite. Mirrors dk.brics `getFiniteStrings`/state-counting: a
    /// determinised automaton with a cycle on a path between start and an
    /// accepting state has infinitely many words. Counts can be astronomically
    /// large, so we saturate at `u128::MAX` rather than overflow (the caller only
    /// compares against small clique sizes, so a saturated count is sound).
    pub fn cardinality(&self) -> Option<u128> {
        let dfa = self.determinize();
        let n = dfa.trans.len();
        let live = dfa.live_states();
        if !live[dfa.start] { return Some(0); }
        let mut color = vec![0u8; n];
        if dfa.has_cycle_live(dfa.start, &live, &mut color) { return None; }
        let mut memo: Vec<Option<u128>> = vec![None; n];
        Some(dfa.count_words(dfa.start, &live, &mut memo))
    }

    /// The length of every word, when the language is not empty and all its
    /// words have one length.
    pub fn fixed_length(&self) -> Option<u64> {
        let dfa = self.determinize();
        let live = dfa.live_states();
        if !live[dfa.start] {
            return None;
        }
        // Every live state lies at one distance from the start, and every
        // accepting state at the same one; so no live state is on a cycle.
        let mut distance: Vec<Option<u64>> = vec![None; dfa.trans.len()];
        distance[dfa.start] = Some(0);
        let mut queue = std::collections::VecDeque::from([dfa.start]);
        let mut length: Option<u64> = None;
        while let Some(q) = queue.pop_front() {
            let d = distance[q]?;
            if dfa.accept[q] {
                if length.is_some_and(|l| l != d) {
                    return None;
                }
                length = Some(d);
            }
            for t in &dfa.trans[q] {
                if !live[t.to] {
                    continue;
                }
                match distance[t.to] {
                    Some(e) if e != d + 1 => return None,
                    Some(_) => {}
                    None => {
                        distance[t.to] = Some(d + 1);
                        queue.push_back(t.to);
                    }
                }
            }
        }
        length
    }

    fn live_states(&self) -> Vec<bool> {
        let dfa = self;
        let n = dfa.trans.len();
        // Forward-reachable states (from start). All DFA states are by construction.
        // Determine which states can reach an accepting state ("live").
        let mut live = vec![false; n];
        // Build reverse adjacency.
        let mut rev: Vec<Vec<usize>> = vec![Vec::new(); n];
        for s in 0..n {
            for t in &dfa.trans[s] {
                rev[t.to].push(s);
            }
        }
        let mut stack: Vec<usize> = Vec::new();
        for s in 0..n {
            if dfa.accept[s] {
                live[s] = true;
                stack.push(s);
            }
        }
        while let Some(s) = stack.pop() {
            for &p in &rev[s] {
                if !live[p] {
                    live[p] = true;
                    stack.push(p);
                }
            }
        }
        live
    }

    fn has_cycle_live(&self, s: usize, live: &[bool], color: &mut [u8]) -> bool {
        color[s] = 1;
        for t in &self.trans[s] {
            if !live[t.to] {
                continue;
            }
            if color[t.to] == 1 {
                return true;
            }
            if color[t.to] == 0 && self.has_cycle_live(t.to, live, color) {
                return true;
            }
        }
        color[s] = 2;
        false
    }

    fn count_words(&self, s: usize, live: &[bool], memo: &mut Vec<Option<u128>>) -> u128 {
        if let Some(v) = memo[s] {
            return v;
        }
        let mut total: u128 = if self.accept[s] { 1 } else { 0 };
        for t in &self.trans[s] {
            if !live[t.to] {
                continue;
            }
            let width = (t.max - t.min) as u128 + 1;
            let sub = self.count_words(t.to, live, memo);
            total = total.saturating_add(width.saturating_mul(sub));
        }
        memo[s] = Some(total);
        total
    }

    /// Up to `cap` accepted words (for materialisation), or `None` when the
    /// language is infinite or larger than `cap`. Words are returned in BFS order.
    pub fn finite_strings(&self, cap: usize) -> Option<Vec<String>> {
        match self.cardinality() {
            None => return None,
            Some(c) if c > cap as u128 => return None,
            Some(_) => {}
        }
        let dfa = self.determinize();
        let live = dfa.live_states();
        let mut out: Vec<String> = Vec::new();
        // BFS over (state, prefix).
        let mut queue: VecDeque<(usize, String)> = VecDeque::new();
        queue.push_back((dfa.start, String::new()));
        while let Some((s, prefix)) = queue.pop_front() {
            if dfa.accept[s] {
                out.push(prefix.clone());
                if out.len() > cap {
                    return None;
                }
            }
            for t in &dfa.trans[s] {
                // Complement and difference introduce rejecting sink cycles.
                // They contribute no words and must never enter the BFS.
                if !live[t.to] { continue; }
                for code in t.min..=t.max {
                    if let Some(ch) = char::from_u32(code) {
                        let mut next = prefix.clone();
                        next.push(ch);
                        queue.push_back((t.to, next));
                    }
                    if out.len() > cap {
                        return None;
                    }
                }
            }
        }
        Some(out)
    }

    /// Whether the automaton accepts the exact string `s`.
    pub fn run(&self, s: &str) -> bool {
        let mut current = self.eps_closure(&BTreeSet::from([self.start]));
        for ch in s.chars() {
            let code = ch as u32;
            let mut next: BTreeSet<usize> = BTreeSet::new();
            for &st in &current {
                for t in &self.trans[st] {
                    if t.min <= code && code <= t.max {
                        next.insert(t.to);
                    }
                }
            }
            current = self.eps_closure(&next);
            if current.is_empty() {
                return false;
            }
        }
        current.iter().any(|&s| self.accept[s])
    }
}

// ===========================================================================
// XSD-Schema regular-expression -> Automaton
// (the dk.brics `RegExp` flavour HermiT constructs from an xsd:pattern facet).
// ===========================================================================

/// Translate an XSD-Schema regular expression to an `Automaton` recognising the
/// *whole-string* language it denotes (anchored, as XSD `pattern` is). Returns
/// `None` for any construct we do not model (so the caller stays sound). The
/// alphabet element of `.`/classes is the XML character set, matching dk.brics.
pub fn xsd_pattern_to_automaton(pattern: &str) -> Option<Automaton> {
    build_pattern(pattern).ok().flatten()
}

/// The automaton of a pattern, `Ok(None)` when it is not modelled, or
/// `Err(PatternTooLarge)` when it would have more than `MAX_PATTERN_STATES`
/// states.
fn build_pattern(pattern: &str) -> Result<Option<Automaton>, PatternTooLarge> {
    let chars: Vec<char> = pattern.chars().collect();
    let mut p = Parser { chars: &chars, pos: 0, depth: 0, defer: false, deferred: None, too_large: false };
    let a = p.parse_alternation();
    if p.too_large {
        return Err(PatternTooLarge);
    }
    Ok(a.filter(|_| p.pos == chars.len()))
}

/// The most states the automaton of a pattern may have. A bounded
/// repetition is built one copy of its body per repetition unless
/// `xsd_pattern_term` keeps it as a length window, so this bounds the memory
/// a pattern takes, and a pattern past it is rejected
/// (`pattern_resource_error`) rather than exhausting memory.
pub const MAX_PATTERN_STATES: usize = 1 << 16;

/// A pattern whose automaton would have more than `MAX_PATTERN_STATES` states.
#[derive(Debug)]
struct PatternTooLarge;

/// Why the automaton of an XSD pattern cannot be built within
/// `MAX_PATTERN_STATES` states, or `None` when it can (or when the pattern is
/// not modelled). The clausifier rejects such a pattern with this message.
pub fn pattern_resource_error(pattern: &str) -> Option<String> {
    pattern_term_result(pattern).err().map(|_| {
        format!(
            "Resource limit: the automaton of xsd:pattern \"{pattern}\" would have more than \
             {MAX_PATTERN_STATES} states. A bounded repetition of more than {LARGE_REPETITION} \
             copies is reasoned about as a length window only when it is the one such \
             repetition of the pattern, its body has words of one length, and every other \
             piece of the pattern, outside any alternation or quantified group, has words of \
             one length; otherwise it is built one state per copy."
        )
    })
}

/// A bounded repetition of more than this many copies is a large one:
/// `xsd_pattern_term` keeps it as a length window instead of a copy of its
/// body per repetition.
const LARGE_REPETITION: usize = 256;

/// An XSD pattern as an automaton and a window on the length of its words,
/// whose words together are exactly the pattern's. A pattern that is a
/// concatenation with one large bounded repetition `R{m,n}` of a body `R`
/// whose words all have one length `l > 0`, all its other pieces having words
/// of one length each (`l1` in all before it and `l2` after), is `F1 R* F2`
/// restricted to the lengths `l1 + l2 + k·l` for `k` in `[m, n]`: a word of
/// `F1 R* F2` of such a length holds exactly `k` copies of `R`. Groups that
/// are neither quantified nor hold an alternation are part of the
/// concatenation, so `x(y(a{3000})z)` is `xya*z` of length 3003. So
/// `a{2147483000}` is `a*` of length 2147483000 rather than 2147483000
/// states, and the length window is reasoned about over the automaton's
/// cycles (`is_empty_within`, `cardinality_within`). Any other pattern is its
/// automaton with no length bound, built one state per copy of a
/// repetition: a large repetition in a quantified group or an alternation,
/// beside a piece of varying length, or beside a second large repetition.
/// `None` when the pattern is not modelled, or when its automaton would have
/// more than `MAX_PATTERN_STATES` states (`pattern_resource_error`).
pub fn xsd_pattern_term(pattern: &str) -> Option<(Automaton, LengthWindow)> {
    pattern_term_result(pattern).ok().flatten()
}

/// Whether the group opened at `open` is neither quantified nor holds an
/// alternation of its own, so that it is part of the concatenation around
/// it. The parse checks both again; this only decides whether to try.
fn plain_group(chars: &[char], open: usize) -> bool {
    let mut depth = 0usize;
    let mut i = open;
    while i < chars.len() {
        match chars[i] {
            '\\' => i += 1,
            '[' => {
                // Skip the class, with its nested subtracted classes.
                let mut nesting = 0usize;
                while i < chars.len() {
                    match chars[i] {
                        '\\' => i += 1,
                        '[' => nesting += 1,
                        ']' => {
                            nesting -= 1;
                            if nesting == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                    i += 1;
                }
            }
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return !matches!(chars.get(i + 1), Some('?' | '*' | '+' | '{'));
                }
            }
            '|' if depth == 1 => return false,
            _ => {}
        }
        i += 1;
    }
    false
}

fn pattern_term_result(pattern: &str) -> Result<Option<(Automaton, LengthWindow)>, PatternTooLarge> {
    let chars: Vec<char> = pattern.chars().collect();
    let mut p = Parser { chars: &chars, pos: 0, depth: 0, defer: true, deferred: None, too_large: false };
    let mut automaton = Automaton::epsilon();
    let mut fixed: u64 = 0;
    let mut large: Option<(u64, Option<u64>)> = None;
    let mut symbolic = true;
    // The plain groups open around the current piece.
    let mut open_groups = 0usize;
    while let Some(c) = p.peek() {
        if c == '(' && plain_group(&chars, p.pos) {
            p.bump();
            if p.peek() == Some('?') && p.chars.get(p.pos + 1) == Some(&':') {
                p.bump();
                p.bump();
            }
            open_groups += 1;
            continue;
        }
        if c == ')' && open_groups > 0 {
            p.bump();
            open_groups -= 1;
            if matches!(p.peek(), Some('?' | '*' | '+' | '{')) {
                symbolic = false;
                break;
            }
            continue;
        }
        if c == '|' || c == ')' {
            symbolic = false;
            break;
        }
        let Some(piece) = p.parse_quantified() else {
            if p.too_large {
                return Err(PatternTooLarge);
            }
            return Ok(None);
        };
        let length = match p.deferred.take() {
            Some((body, min, max)) => match body.fixed_length() {
                Some(0) => Some(0),
                Some(l) if large.is_none() => {
                    if max.is_some_and(|max| max < min) {
                        return Ok(Some((Automaton::empty_language(), (0, None))));
                    }
                    let max = match max {
                        Some(max) => (max as u64).checked_mul(l).map(Some),
                        None => Some(None),
                    };
                    match ((min as u64).checked_mul(l), max) {
                        (Some(min), Some(max)) => {
                            large = Some((min, max));
                            Some(0)
                        }
                        _ => None,
                    }
                }
                _ => None,
            },
            None => piece.fixed_length(),
        };
        let Some(length) = length.and_then(|length| fixed.checked_add(length)) else {
            symbolic = false;
            break;
        };
        fixed = length;
        automaton = automaton.concatenate(&piece);
        if automaton.trans.len() > MAX_PATTERN_STATES {
            return Err(PatternTooLarge);
        }
    }
    match large {
        Some((min, max)) if symbolic && open_groups == 0 => {
            let (Some(min), Some(max)) = (min.checked_add(fixed), max.map_or(Some(None), |max| max.checked_add(fixed).map(Some)))
            else {
                return build_pattern(pattern).map(|a| a.map(|a| (a, (0, None))));
            };
            Ok(Some((automaton, (min, max))))
        }
        _ => build_pattern(pattern).map(|a| a.map(|a| (a, (0, None)))),
    }
}

struct Parser<'a> {
    chars: &'a [char],
    pos: usize,
    /// The nesting depth in groups.
    depth: usize,
    /// Whether a large bounded repetition outside every group is returned as
    /// its body's star, with the body and the bounds in `deferred`
    /// (`xsd_pattern_term`).
    defer: bool,
    deferred: Option<(Automaton, usize, Option<usize>)>,
    /// Set when a repetition or concatenation would build more than
    /// `MAX_PATTERN_STATES` states.
    too_large: bool,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }
    fn bump(&mut self) -> Option<char> {
        let c = self.chars.get(self.pos).copied();
        if c.is_some() {
            self.pos += 1;
        }
        c
    }

    fn parse_alternation(&mut self) -> Option<Automaton> {
        let mut a = self.parse_concat()?;
        while self.peek() == Some('|') {
            self.bump();
            let b = self.parse_concat()?;
            a = a.union(&b);
        }
        Some(a)
    }

    fn parse_concat(&mut self) -> Option<Automaton> {
        let mut a = Automaton::epsilon();
        while let Some(c) = self.peek() {
            if c == '|' || c == ')' {
                break;
            }
            let piece = self.parse_quantified()?;
            a = a.concatenate(&piece);
            if a.trans.len() > MAX_PATTERN_STATES {
                self.too_large = true;
                return None;
            }
        }
        Some(a)
    }

    fn parse_quantified(&mut self) -> Option<Automaton> {
        let atom = self.parse_atom()?;
        match self.peek() {
            Some('?') => {
                self.bump();
                Some(atom.optional())
            }
            Some('*') => {
                self.bump();
                Some(atom.repeat())
            }
            Some('+') => {
                self.bump();
                Some(atom.repeat_min(1))
            }
            Some('{') => {
                self.bump();
                let min = self.parse_number()?;
                if self.defer && self.depth == 0 {
                    // Read the bounds ahead; a large repetition is deferred.
                    let start = self.pos;
                    let max = match (self.peek(), self.chars.get(self.pos + 1)) {
                        (Some('}'), _) => Some(Some(min)),
                        (Some(','), Some('}')) => Some(None),
                        (Some(','), _) => {
                            self.bump();
                            let max = self.parse_number();
                            max.map(Some)
                        }
                        _ => None,
                    };
                    let large = match max {
                        Some(Some(max)) => min.max(max) > LARGE_REPETITION,
                        Some(None) => min > LARGE_REPETITION,
                        None => false,
                    };
                    if large {
                        // Consume the rest of the quantifier: `}` or `,}`.
                        if self.peek() == Some(',') {
                            self.bump();
                        }
                        if self.bump() != Some('}') {
                            return None;
                        }
                        self.deferred = Some((atom.clone(), min, max.flatten()));
                        return Some(atom.repeat());
                    }
                    self.pos = start;
                }
                // The copies are built one by one, within `MAX_PATTERN_STATES`.
                let states = atom.trans.len();
                let copies = |parser: &mut Parser, count: usize| -> Option<()> {
                    if states.saturating_mul(count.saturating_add(1)) > MAX_PATTERN_STATES {
                        parser.too_large = true;
                        return None;
                    }
                    Some(())
                };
                match self.peek() {
                    Some('}') => {
                        copies(self, min)?;
                        self.bump();
                        Some(atom.repeat_range(min, min))
                    }
                    Some(',') => {
                        self.bump();
                        if self.peek() == Some('}') {
                            copies(self, min)?;
                            self.bump();
                            Some(atom.repeat_min(min))
                        } else {
                            let max = self.parse_number()?;
                            if self.peek() != Some('}') {
                                return None;
                            }
                            if max >= min {
                                copies(self, max)?;
                            }
                            self.bump();
                            Some(atom.repeat_range(min, max))
                        }
                    }
                    _ => None,
                }
            }
            _ => Some(atom),
        }
    }

    fn parse_number(&mut self) -> Option<usize> {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                s.push(c);
                self.bump();
            } else {
                break;
            }
        }
        s.parse().ok()
    }

    fn parse_atom(&mut self) -> Option<Automaton> {
        let c = self.peek()?;
        match c {
            '(' => {
                self.bump();
                // Skip a `(?:` non-capturing prefix if present.
                if self.peek() == Some('?') && self.chars.get(self.pos + 1) == Some(&':') {
                    self.bump();
                    self.bump();
                }
                self.depth += 1;
                let inner = self.parse_alternation()?;
                self.depth -= 1;
                if self.peek() != Some(')') {
                    return None;
                }
                self.bump();
                Some(inner)
            }
            '[' => self.parse_char_class(),
            '.' => {
                self.bump();
                // XSD `.` is `[^\n\r]` (XSD 1.1 Part 2 §G.4.2.5): every
                // character but the line terminators. The datatype automaton it
                // is intersected with restricts it to the characters of the
                // value space, so it must not stop at the XML characters: an
                // anyURI may contain U+FFFE.
                Some(ranges_to_automaton(&dot_ranges()))
            }
            '\\' => {
                self.bump();
                let e = self.bump()?;
                self.escape_to_automaton(e)
            }
            // XSD patterns are implicitly anchored, and `^`/`$` are normal
            // characters (XSD 1.1 Part 2 §G.4.2.3, `NormalChar`).
            ')' | '|' | '*' | '+' | '?' | '{' | '}' | ']' => None,
            lit => {
                self.bump();
                Some(Automaton::char(lit as u32))
            }
        }
    }

    /// A backslash escape outside a character class -> automaton for the one
    /// symbol (or class) it denotes.
    fn escape_to_automaton(&mut self, e: char) -> Option<Automaton> {
        // Multi-character class escapes.
        if let Some(ranges) = class_escape_ranges(e) {
            return Some(ranges_to_automaton(&ranges));
        }
        if e == 'p' || e == 'P' {
            let ranges = self.parse_unicode_property(e == 'P')?;
            return Some(ranges_to_automaton(&ranges));
        }
        // Single-character escapes (the XSD set) and punctuation escapes.
        single_char_escape(e).map(|cp| Automaton::char(cp))
    }

    /// Parse a `\p{Name}` / `\P{Name}` property after the leading `p`/`P` has been
    /// consumed; `complemented` is true for `\P`. Returns the code-point ranges.
    fn parse_unicode_property(&mut self, complemented: bool) -> Option<Vec<(u32, u32)>> {
        if self.peek() != Some('{') {
            return None;
        }
        self.bump();
        let mut name = String::new();
        while let Some(c) = self.peek() {
            if c == '}' {
                break;
            }
            name.push(c);
            self.bump();
        }
        if self.peek() != Some('}') {
            return None;
        }
        self.bump();
        let base = unicode_property_ranges(&name)?;
        if complemented {
            Some(complement_ranges(&base))
        } else {
            Some(base)
        }
    }

    fn parse_char_class(&mut self) -> Option<Automaton> {
        let ranges = self.parse_char_class_ranges()?;
        Some(ranges_to_automaton(&ranges))
    }

    /// Parse a `[...]` class (with optional `^` negation and `-[...]` subtraction)
    /// into its normalised code-point range set. `self.pos` is at `[`.
    fn parse_char_class_ranges(&mut self) -> Option<Vec<(u32, u32)>> {
        self.bump(); // '['
        let negated = self.peek() == Some('^');
        if negated {
            self.bump();
        }
        let mut ranges: Vec<(u32, u32)> = Vec::new();
        let mut first = true;
        loop {
            match self.peek() {
                None => return None, // unterminated
                Some(']') if !first => {
                    self.bump();
                    break;
                }
                Some('-') if !first && self.chars.get(self.pos + 1) == Some(&'[') => {
                    // class subtraction: [...-[...]]
                    self.bump(); // '-'
                    let sub = self.parse_char_class_ranges()?;
                    if self.peek() != Some(']') {
                        return None;
                    }
                    self.bump();
                    let base =
                        if negated { complement_ranges(&ranges) } else { normalize_ranges(&ranges) };
                    return Some(subtract_ranges(&base, &sub));
                }
                _ => {}
            }
            first = false;
            // A class member is either a single char/escape, or a multi-char class
            // escape (whose ranges we fold in directly and which cannot be a range
            // endpoint).
            match self.parse_class_member()? {
                ClassMember::Set(rs) => ranges.extend(rs),
                ClassMember::Single(lo) => {
                    if self.peek() == Some('-')
                        && self.chars.get(self.pos + 1).is_some_and(|&c| c != ']')
                    {
                        self.bump(); // '-'
                        match self.parse_class_member()? {
                            ClassMember::Single(hi) => {
                                if lo > hi {
                                    return None;
                                }
                                ranges.push((lo, hi));
                            }
                            ClassMember::Set(_) => return None, // class escape as range end
                        }
                    } else {
                        ranges.push((lo, lo));
                    }
                }
            }
        }
        Some(if negated { complement_ranges(&ranges) } else { normalize_ranges(&ranges) })
    }

    /// Parse one member inside a character class.
    fn parse_class_member(&mut self) -> Option<ClassMember> {
        let c = self.bump()?;
        if c == '\\' {
            let e = self.bump()?;
            if let Some(rs) = class_escape_ranges(e) {
                return Some(ClassMember::Set(rs));
            }
            if e == 'p' || e == 'P' {
                let rs = self.parse_unicode_property(e == 'P')?;
                return Some(ClassMember::Set(rs));
            }
            return single_char_escape(e).map(ClassMember::Single);
        }
        Some(ClassMember::Single(c as u32))
    }
}

/// One parsed character-class member: a single code point (which may be a range
/// endpoint) or a whole range set (from a class escape, which may not be).
enum ClassMember {
    Single(u32),
    Set(Vec<(u32, u32)>),
}

/// The ranges denoted by `.` in an XSD pattern: `[^\n\r]`, every character
/// except `\n`/`\r`.
fn dot_ranges() -> Vec<(u32, u32)> {
    complement_ranges(&[(0x0A, 0x0A), (0x0D, 0x0D)])
}

/// The XML `Char` production, whose characters make up the xsd:string values
/// (XSD 1.1 Part 2 §3.3.1): `#x9 #xA #xD #x20-#xD7FF #xE000-#xFFFD
/// #x10000-#x10FFFF`. HermiT's `xmlChar()` leaves out `#xD`, `#x80-#x9F` and the
/// supplementary characters, although its xsd:string automaton
/// (dk.brics `Datatypes.get("string")`) has them; without them the automata
/// would miss string values.
pub fn xml_char_ranges() -> Vec<(u32, u32)> {
    vec![
        (0x09, 0x0A),
        (0x0D, 0x0D),
        (0x20, 0xD7FF),
        (0xE000, 0xFFFD),
        (0x10000, 0x10FFFF),
    ]
}

/// Build an automaton from a set of single-symbol ranges.
fn ranges_to_automaton(ranges: &[(u32, u32)]) -> Automaton {
    Automaton::ranges(ranges)
}

/// The XSD multi-character class escapes (`\d \D \w \W \s \S \i \I \c \C`).
/// Returns `None` for a non-class escape. The uppercase variants are the
/// complements over all characters (XSD 1.1 Part 2 §G.4.2.5); the datatype
/// automaton restricts them to the characters of the value space.
fn class_escape_ranges(e: char) -> Option<Vec<(u32, u32)>> {
    match e {
        // `\d` is `\p{Nd}`, every decimal digit, not only ASCII ones.
        'd' => Some(digit_ranges()),
        'D' => Some(complement_ranges(&digit_ranges())),
        's' => Some(vec![(0x09, 0x0A), (0x0D, 0x0D), (0x20, 0x20)]),
        'S' => Some(complement_ranges(&[(0x09, 0x0A), (0x0D, 0x0D), (0x20, 0x20)])),
        'w' => Some(word_char_ranges()),
        'W' => Some(complement_ranges(&word_char_ranges())),
        // XSD \i = the NameStartChar set restricted to the "initial name char"
        // production; \c = the NameChar set. dk.brics models these as the XML
        // productions. We approximate with the ASCII + common letter ranges that
        // HermiT actually exercises, plus the full letter blocks.
        'i' => Some(name_start_char_ranges()),
        'I' => Some(complement_ranges(&name_start_char_ranges())),
        'c' => Some(name_char_ranges()),
        'C' => Some(complement_ranges(&name_char_ranges())),
        _ => None,
    }
}

/// `\d`: `\p{Nd}` (XSD 1.1 Part 2 §G.4.2.5).
fn digit_ranges() -> Vec<(u32, u32)> {
    gencat_ranges("Nd").expect("the Nd category")
}

/// `\w`: `[#x0000-#x10FFFF]-[\p{P}\p{Z}\p{C}]` (XSD 1.1 Part 2 §G.4.2.5), every
/// character that is not punctuation, a separator or "other"; symbols such as
/// `$` and `+` are word characters.
fn word_char_ranges() -> Vec<(u32, u32)> {
    let mut non_word = Vec::new();
    for category in ["P", "Z", "C"] {
        non_word.extend(gencat_ranges(category).expect("a general category"));
    }
    complement_ranges(&non_word)
}

/// XML NameStartChar (the `\i` set, minus the colon, per XSD `\i`): letters and
/// underscore over the XML name-start blocks.
fn name_start_char_ranges() -> Vec<(u32, u32)> {
    let mut r = vec![
        (0x3Au32, 0x3Au32), // ':'  (XSD \i includes ':')
        (0x41, 0x5A),
        (0x5F, 0x5F),
        (0x61, 0x7A),
        (0xC0, 0xD6),
        (0xD8, 0xF6),
        (0xF8, 0x2FF),
        (0x370, 0x37D),
        (0x37F, 0x1FFF),
        (0x200C, 0x200D),
        (0x2070, 0x218F),
        (0x2C00, 0x2FEF),
        (0x3001, 0xD7FF),
        (0xF900, 0xFDCF),
        (0xFDF0, 0xFFFD),
        (0x10000, 0xEFFFF),
    ];
    r.sort();
    r
}

/// XML NameChar (the `\c` set): NameStartChar plus `-`, `.`, digits, and the
/// combining/extender ranges.
fn name_char_ranges() -> Vec<(u32, u32)> {
    let mut r = name_start_char_ranges();
    r.extend_from_slice(&[
        (0x2Du32, 0x2Eu32), // '-' '.'
        (0x30, 0x39),       // digits
        (0xB7, 0xB7),       // middle dot
        (0x300, 0x36F),     // combining
        (0x203F, 0x2040),
    ]);
    normalize_ranges(&r)
}

/// The single-character escapes XSD/dk.brics allow outside a class. The standard
/// XSD set is `\n \r \t \\ \| \. \- \^ \? \* \+ \{ \} \( \) \[ \] $`; any other
/// punctuation escape is treated as the literal punctuation char.
fn single_char_escape(e: char) -> Option<u32> {
    Some(match e {
        'n' => 0x0A,
        'r' => 0x0D,
        't' => 0x09,
        // The XSD metacharacter escapes (and any punctuation) denote themselves.
        '\\' | '|' | '.' | '-' | '^' | '?' | '*' | '+' | '{' | '}' | '(' | ')' | '[' | ']'
        | '$' | '/' => e as u32,
        // Other ASCII-letter escapes that are not class escapes are unknown.
        _ if e.is_ascii_alphanumeric() => return None,
        // Any other punctuation escape: the literal char.
        _ => e as u32,
    })
}

/// The code-point ranges for a `\p{Name}` Unicode property/category. Resolves the
/// full XSD-Schema set of Unicode general categories (C, Cc, Cf, Co, Cn, L, Lu, Ll,
/// Lt, Lm, Lo, M, Mn, Mc, Me, N, Nd, Nl, No, P, Pc, Pd, Ps, Pe, Pi, Pf, Po, S, Sm,
/// Sc, Sk, So, Z, Zs, Zl, Zp) — and the convenience name `Letter`/`Number` aliases —
/// to their EXACT code-point range set via regex-syntax's Unicode tables, and the
/// `Is<Block>` block names to their (fixed, XSD-spec) contiguous block ranges. An
/// unknown / misspelled name yields `None` (caller scopes out). Sound: each set is
/// the exact set of code points in that category/block.
fn unicode_property_ranges(name: &str) -> Option<Vec<(u32, u32)>> {
    // `Is<Block>` block names: XSD's blocks are fixed contiguous code-point ranges
    // (an enumerated spec list, not derived from the Unicode general-category data),
    // so they are resolved from the block table below.
    if let Some(block) = name.strip_prefix("Is") {
        return unicode_block_ranges(block);
    }
    // General categories (and the `Letter`/`Number` aliases): resolve the EXACT
    // ranges from regex-syntax's Unicode general-category tables by parsing the
    // single-class regex `[\p{Name}]` and walking the resulting Unicode class.
    let gc = match name {
        "Letter" => "L",
        "Number" => "N",
        other => other,
    };
    gencat_ranges(gc)
}

/// Resolve a Unicode general-category short name (e.g. `Lu`, `P`, `Cc`) to its
/// exact `(char,char)` range set, using regex-syntax's HIR parse of `[\p{Name}]`.
/// Returns `None` for an unknown category name (regex-syntax rejects the parse).
fn gencat_ranges(name: &str) -> Option<Vec<(u32, u32)>> {
    use regex_syntax::hir::{Class, HirKind};
    // `\p{<gc>}`. We wrap it in a class so the HIR is a single `Class::Unicode`
    // whose ranges we can read directly. A bad name makes `parse` return `Err`.
    let pattern = format!("[\\p{{{name}}}]");
    let hir = regex_syntax::parse(&pattern).ok()?;
    match hir.into_kind() {
        HirKind::Class(Class::Unicode(cls)) => Some(
            cls.ranges()
                .iter()
                .map(|r| (r.start() as u32, r.end() as u32))
                .collect(),
        ),
        // A category that contains exactly one code point (e.g. `Zl`, `Zp`) is
        // simplified by regex-syntax to a single-char literal.
        HirKind::Literal(lit) => {
            // The literal bytes are a single UTF-8 scalar; take its one char.
            let s = std::str::from_utf8(&lit.0).ok()?;
            let mut it = s.chars();
            let c = it.next()?;
            if it.next().is_some() {
                return None; // not a single code point — unexpected
            }
            Some(vec![(c as u32, c as u32)])
        }
        _ => None,
    }
}

/// The fixed XSD Unicode block range for an `Is<Block>` property. The accepted block
/// names are exactly those in [`XSD_UNICODE_BLOCKS`] (the dk.brics 1.11-8 set HermiT
/// uses). XSD block names are matched ignoring spaces/`_`/`-` and case, so
/// `IsLatin-1Supplement`, `IsLatin1Supplement` and `IsLatin_1_Supplement` all resolve.
///
/// An unrecognised block name returns `None`. This is NOT a value-space scope-out: in
/// the dk.brics XSD-regex grammar an unknown `\p{IsName}` is a malformed pattern, and
/// the `None` here propagates through `parse_unicode_property` and the rest of the
/// parser so that `xsd_pattern_to_automaton` rejects the whole pattern (returns
/// `None`) — it never widens the value space.
fn unicode_block_ranges(block: &str) -> Option<Vec<(u32, u32)>> {
    // Normalise: drop ASCII whitespace, '_' and '-' and compare case-insensitively,
    // so `Latin-1Supplement`, `Latin1Supplement` and `Latin_1_Supplement` all match.
    let norm = |s: &str| -> String {
        s.chars()
            .filter(|c| !c.is_ascii_whitespace() && *c != '_' && *c != '-')
            .flat_map(|c| c.to_lowercase())
            .collect()
    };
    let key = norm(block);
    let (lo, hi) = XSD_UNICODE_BLOCKS
        .iter()
        .find(|(name, _, _)| norm(name) == key)
        .map(|(_, lo, hi)| (*lo, *hi))?;
    Some(vec![(lo, hi)])
}

/// The XML Schema `Is<Block>` block list: `(canonical name, first cp, last cp)`.
///
/// This is the EXACT fixed set of `\p{IsBlock}` names HermiT accepts, taken verbatim
/// from the `dk.brics.automaton` `Datatypes` class (`unicodeblock_names_array`) in the
/// `automaton` 1.11-8 artifact HermiT pins (see Java `pom.xml`). That library is what
/// validates XSD patterns, so its block set is authoritative: it is the Unicode 3.1
/// block list referenced by the XSD 1.0 Datatypes spec — 92 blocks with the
/// pre-Unicode-3.2 names and ranges. dk.brics models supplementary-plane blocks as
/// UTF-16 surrogate pairs; here they are given as their true scalar code-point ranges.
///
/// A `\p{IsName}` whose name is NOT in this table is, exactly as in dk.brics, a
/// malformed XSD pattern: `unicode_block_ranges` returns `None`, which propagates up
/// through the parser so `xsd_pattern_to_automaton`/`pattern_automaton` reject the
/// pattern (return `None`) rather than silently widening the value space. Hence this
/// list must contain neither more nor fewer names than dk.brics: a missing name would
/// wrongly scope out, an extra name would wrongly accept a pattern Java rejects.
///
/// Notable pre-3.2 specifics (vs. modern Unicode): `Greek` not `GreekandCoptic`;
/// `CombiningMarksforSymbols` not `CombiningDiacriticalMarksforSymbols`;
/// `CJKUnifiedIdeographsExtensionA` ends at U+4DB5; `ArabicPresentationForms-B` ends
/// at U+FEFE; `Specials` is U+FFF0..U+FFFD; `CJKUnifiedIdeographsExtensionB` ends at
/// U+2A6D6; there are NO surrogate, private-use, or other post-3.1 blocks.
const XSD_UNICODE_BLOCKS: &[(&str, u32, u32)] = &[
    ("BasicLatin", 0x0000, 0x007F),
    ("Latin-1Supplement", 0x0080, 0x00FF),
    ("LatinExtended-A", 0x0100, 0x017F),
    ("LatinExtended-B", 0x0180, 0x024F),
    ("IPAExtensions", 0x0250, 0x02AF),
    ("SpacingModifierLetters", 0x02B0, 0x02FF),
    ("CombiningDiacriticalMarks", 0x0300, 0x036F),
    ("Greek", 0x0370, 0x03FF),
    ("Cyrillic", 0x0400, 0x04FF),
    ("Armenian", 0x0530, 0x058F),
    ("Hebrew", 0x0590, 0x05FF),
    ("Arabic", 0x0600, 0x06FF),
    ("Syriac", 0x0700, 0x074F),
    ("Thaana", 0x0780, 0x07BF),
    ("Devanagari", 0x0900, 0x097F),
    ("Bengali", 0x0980, 0x09FF),
    ("Gurmukhi", 0x0A00, 0x0A7F),
    ("Gujarati", 0x0A80, 0x0AFF),
    ("Oriya", 0x0B00, 0x0B7F),
    ("Tamil", 0x0B80, 0x0BFF),
    ("Telugu", 0x0C00, 0x0C7F),
    ("Kannada", 0x0C80, 0x0CFF),
    ("Malayalam", 0x0D00, 0x0D7F),
    ("Sinhala", 0x0D80, 0x0DFF),
    ("Thai", 0x0E00, 0x0E7F),
    ("Lao", 0x0E80, 0x0EFF),
    ("Tibetan", 0x0F00, 0x0FFF),
    ("Myanmar", 0x1000, 0x109F),
    ("Georgian", 0x10A0, 0x10FF),
    ("HangulJamo", 0x1100, 0x11FF),
    ("Ethiopic", 0x1200, 0x137F),
    ("Cherokee", 0x13A0, 0x13FF),
    ("UnifiedCanadianAboriginalSyllabics", 0x1400, 0x167F),
    ("Ogham", 0x1680, 0x169F),
    ("Runic", 0x16A0, 0x16FF),
    ("Khmer", 0x1780, 0x17FF),
    ("Mongolian", 0x1800, 0x18AF),
    ("LatinExtendedAdditional", 0x1E00, 0x1EFF),
    ("GreekExtended", 0x1F00, 0x1FFF),
    ("GeneralPunctuation", 0x2000, 0x206F),
    ("SuperscriptsandSubscripts", 0x2070, 0x209F),
    ("CurrencySymbols", 0x20A0, 0x20CF),
    ("CombiningMarksforSymbols", 0x20D0, 0x20FF),
    ("LetterlikeSymbols", 0x2100, 0x214F),
    ("NumberForms", 0x2150, 0x218F),
    ("Arrows", 0x2190, 0x21FF),
    ("MathematicalOperators", 0x2200, 0x22FF),
    ("MiscellaneousTechnical", 0x2300, 0x23FF),
    ("ControlPictures", 0x2400, 0x243F),
    ("OpticalCharacterRecognition", 0x2440, 0x245F),
    ("EnclosedAlphanumerics", 0x2460, 0x24FF),
    ("BoxDrawing", 0x2500, 0x257F),
    ("BlockElements", 0x2580, 0x259F),
    ("GeometricShapes", 0x25A0, 0x25FF),
    ("MiscellaneousSymbols", 0x2600, 0x26FF),
    ("Dingbats", 0x2700, 0x27BF),
    ("BraillePatterns", 0x2800, 0x28FF),
    ("CJKRadicalsSupplement", 0x2E80, 0x2EFF),
    ("KangxiRadicals", 0x2F00, 0x2FDF),
    ("IdeographicDescriptionCharacters", 0x2FF0, 0x2FFF),
    ("CJKSymbolsandPunctuation", 0x3000, 0x303F),
    ("Hiragana", 0x3040, 0x309F),
    ("Katakana", 0x30A0, 0x30FF),
    ("Bopomofo", 0x3100, 0x312F),
    ("HangulCompatibilityJamo", 0x3130, 0x318F),
    ("Kanbun", 0x3190, 0x319F),
    ("BopomofoExtended", 0x31A0, 0x31BF),
    ("EnclosedCJKLettersandMonths", 0x3200, 0x32FF),
    ("CJKCompatibility", 0x3300, 0x33FF),
    ("CJKUnifiedIdeographsExtensionA", 0x3400, 0x4DB5),
    ("CJKUnifiedIdeographs", 0x4E00, 0x9FFF),
    ("YiSyllables", 0xA000, 0xA48F),
    ("YiRadicals", 0xA490, 0xA4CF),
    ("HangulSyllables", 0xAC00, 0xD7A3),
    ("CJKCompatibilityIdeographs", 0xF900, 0xFAFF),
    ("AlphabeticPresentationForms", 0xFB00, 0xFB4F),
    ("ArabicPresentationForms-A", 0xFB50, 0xFDFF),
    ("CombiningHalfMarks", 0xFE20, 0xFE2F),
    ("CJKCompatibilityForms", 0xFE30, 0xFE4F),
    ("SmallFormVariants", 0xFE50, 0xFE6F),
    ("ArabicPresentationForms-B", 0xFE70, 0xFEFE),
    ("HalfwidthandFullwidthForms", 0xFF00, 0xFFEF),
    ("Specials", 0xFFF0, 0xFFFD),
    ("OldItalic", 0x10300, 0x1032F),
    ("Gothic", 0x10330, 0x1034F),
    ("Deseret", 0x10400, 0x1044F),
    ("ByzantineMusicalSymbols", 0x1D000, 0x1D0FF),
    ("MusicalSymbols", 0x1D100, 0x1D1FF),
    ("MathematicalAlphanumericSymbols", 0x1D400, 0x1D7FF),
    ("CJKUnifiedIdeographsExtensionB", 0x20000, 0x2A6D6),
    ("CJKCompatibilityIdeographsSupplement", 0x2F800, 0x2FA1F),
    ("Tags", 0xE0000, 0xE007F),
];

// ---- range-set utilities ----------------------------------------------------

/// Merge/sort overlapping or adjacent ranges into a canonical disjoint set.
pub fn normalize_ranges(ranges: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut rs: Vec<(u32, u32)> = ranges.iter().copied().filter(|(a, b)| a <= b).collect();
    rs.sort();
    let mut out: Vec<(u32, u32)> = Vec::new();
    for (a, b) in rs {
        if let Some(last) = out.last_mut() {
            if a <= last.1.saturating_add(1) {
                last.1 = last.1.max(b);
                continue;
            }
        }
        out.push((a, b));
    }
    out
}

/// The complement of a range set within `0..=MAX_CP`.
pub fn complement_ranges(ranges: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let norm = normalize_ranges(ranges);
    let mut out: Vec<(u32, u32)> = Vec::new();
    let mut next: u32 = 0;
    for (a, b) in norm {
        if a > next {
            out.push((next, a - 1));
        }
        next = b.saturating_add(1);
        if next == 0 {
            // overflow guard
            return out;
        }
    }
    if next <= MAX_CP {
        out.push((next, MAX_CP));
    }
    out
}

/// `a \ b` over range sets.
pub fn subtract_ranges(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let comp_b = complement_ranges(b);
    intersect_ranges(&normalize_ranges(a), &comp_b)
}

/// Intersection of two range sets.
pub fn intersect_ranges(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let a = normalize_ranges(a);
    let b = normalize_ranges(b);
    let mut out = Vec::new();
    let (mut i, mut j) = (0usize, 0usize);
    while i < a.len() && j < b.len() {
        let lo = a[i].0.max(b[j].0);
        let hi = a[i].1.min(b[j].1);
        if lo <= hi {
            out.push((lo, hi));
        }
        if a[i].1 < b[j].1 {
            i += 1;
        } else {
            j += 1;
        }
    }
    out
}

// ===========================================================================
// The combined-alphabet (string · SEPARATOR · langtag) automata HermiT uses.
// ===========================================================================

/// `s_anyChar` — the XML character automaton (one symbol).
pub fn any_char() -> Automaton {
    Automaton::ranges(&xml_char_ranges())
}

/// `s_anyString` — any XML string (`s_anyChar*`).
pub fn any_string() -> Automaton {
    any_char().repeat()
}

/// The character sequences over the characters of anyURI values: the XML
/// characters and U+FFFE and U+FFFF, which `is_valid_any_uri` admits too (as
/// `java.net.URI` does). The value space is the subset
/// `any_uri_value_automaton` accepts.
pub fn any_uri_string_automaton() -> Automaton {
    let mut chars = xml_char_ranges();
    chars.push((0xFFFE, 0xFFFF));
    Automaton::ranges(&normalize_ranges(&chars)).repeat()
}

/// The strings `datatype_value::is_valid_any_uri` accepts, the anyURI values:
/// the RFC 2396 URI references that `java.net.URI` parses, over the characters
/// the dk.brics `URI` grammar admits. A string is `before ['#' fragment]`,
/// with `before` either `scheme ':' ssp`, an opaque part (not starting with
/// `/`, and not empty) or a hierarchical part starting with `/`, or else a
/// relative reference; a hierarchical part is `['//' authority] path ['?'
/// query]`, and an authority `[userinfo '@'] host [':' port]` or an IPv6
/// reference. Each part is a sequence of its characters, the unreserved
/// ASCII characters, the characters above U+0080 that are no space or control
/// character, and the escapes `%` HEX HEX. So a count over the value space is
/// a count of this automaton's words.
pub fn any_uri_value_automaton() -> Automaton {
    let chars = |s: &str| -> Vec<(u32, u32)> { s.chars().map(|c| (c as u32, c as u32)).collect() };
    let set = |ranges: Vec<(u32, u32)>| Automaton::ranges(&normalize_ranges(&ranges));
    let mut unreserved = vec![(0x30, 0x39), (0x41, 0x5A), (0x61, 0x7A)];
    unreserved.extend(chars("-_.!~*'()"));
    // `java.net.URI`'s "other": above U+0080, no space and no control
    // character (U+0081 to U+009F are controls).
    let spaces = [(0xA0, 0xA0), (0x1680, 0x1680), (0x2000, 0x200A), (0x2028, 0x2029), (0x202F, 0x202F), (0x205F, 0x205F), (0x3000, 0x3000), (0xD800, 0xDFFF)];
    let other = subtract_ranges(&[(0xA1, MAX_CP)], &spaces);
    let hex = set(vec![(0x30, 0x39), (0x41, 0x46), (0x61, 0x66)]);
    let escape = Automaton::char('%' as u32).concatenate(&hex).concatenate(&hex);
    // The sequences of unreserved, other, escaped and `extra` characters.
    let part = |extra: &str| {
        let mut ranges = unreserved.clone();
        ranges.extend(other.iter().copied());
        ranges.extend(chars(extra));
        set(ranges).union(&escape).repeat()
    };
    let everything = Automaton::char_range(0, MAX_CP).repeat();
    let starting = |prefix: &str| Automaton::literal(prefix).concatenate(&everything);
    let c = |ch: char| Automaton::char(ch as u32);
    let digits = Automaton::char_range('0' as u32, '9' as u32).repeat();
    let uric = part(";/?:@&=+$,[]");
    let path = part(":@&=+$,/;");
    let port = c(':').concatenate(&digits);
    let host_port = part("$,;&=+").union(&part("$,;:&=+").concatenate(&port));
    let ipv6_chars = set(vec![(0x30, 0x39), (0x41, 0x46), (0x61, 0x66), (0x3A, 0x3A), (0x2E, 0x2E), (0x56, 0x56), (0x76, 0x76)]);
    let ipv6 = c('[').concatenate(&ipv6_chars.repeat_min(1)).concatenate(&c(']')).concatenate(&port.optional());
    let authority = part(";:&=+$,").concatenate(&c('@')).optional().concatenate(&host_port.union(&ipv6));
    let net_path = Automaton::literal("//").concatenate(&authority).concatenate(&c('/').concatenate(&path).optional());
    let path_part = net_path.union(&path.minus(&starting("//")));
    let hierarchical = path_part.concatenate(&c('?').concatenate(&uric).optional());
    let mut scheme_chars = vec![(0x30, 0x39), (0x41, 0x5A), (0x61, 0x7A)];
    scheme_chars.extend(chars("+-."));
    let scheme = set(vec![(0x41, 0x5A), (0x61, 0x7A)]).concatenate(&set(scheme_chars).repeat()).concatenate(&c(':'));
    let opaque = uric.minus(&starting("/")).minus(&Automaton::epsilon());
    let absolute = scheme.concatenate(&opaque.union(&hierarchical.intersection(&starting("/"))));
    let relative = hierarchical.minus(&scheme.concatenate(&everything));
    absolute.union(&relative).concatenate(&c('#').concatenate(&uric).optional()).determinize()
}

/// The `normalizedString` value-space automaton:
/// `([#x20-#x7F #xA0-#xD7FF #xE000-#xFFFD])*`.
pub fn normalized_string_automaton() -> Automaton {
    Automaton::ranges(&[(0x20, 0x7F), (0xA0, 0xD7FF), (0xE000, 0xFFFD)]).repeat()
}

/// The `token` value-space automaton:
/// `([#x21-#xD7FF #xE000-#xFFFD]+(#x20 [#x21-#xD7FF #xE000-#xFFFD]+)*)?`.
pub fn token_automaton() -> Automaton {
    let word_char = Automaton::ranges(&[(0x21, 0xD7FF), (0xE000, 0xFFFD)]);
    let word = word_char.repeat_min(1);
    let space = Automaton::char(0x20);
    let tail = space.concatenate(&word).repeat();
    word.concatenate(&tail).optional()
}

/// XML `Name` automaton (dk.brics `Datatypes.get("Name2")`):
/// `NameStartChar NameChar*` with the colon allowed.
pub fn name_automaton() -> Automaton {
    let start = Automaton::ranges(&name_start_char_ranges());
    let rest = Automaton::ranges(&name_char_ranges()).repeat();
    start.concatenate(&rest)
}

/// XML `NCName` automaton (`Datatypes.get("NCName")`): `Name` without a colon.
pub fn ncname_automaton() -> Automaton {
    let no_colon = |rs: Vec<(u32, u32)>| subtract_ranges(&rs, &[(0x3A, 0x3A)]);
    let start = Automaton::ranges(&no_colon(name_start_char_ranges()));
    let rest = Automaton::ranges(&no_colon(name_char_ranges())).repeat();
    start.concatenate(&rest)
}

/// XML `NMTOKEN` automaton (`Datatypes.get("Nmtoken2")`): `NameChar+`.
pub fn nmtoken_automaton() -> Automaton {
    Automaton::ranges(&name_char_ranges()).repeat_min(1)
}

/// The XSD `language` lexical automaton (`Datatypes.get("language")`):
/// `[a-zA-Z]{1,8}(-[a-zA-Z0-9]{1,8})*`.
pub fn language_automaton() -> Automaton {
    let alpha = Automaton::ranges(&[(0x41, 0x5A), (0x61, 0x7A)]);
    let alnum = Automaton::ranges(&[(0x30, 0x39), (0x41, 0x5A), (0x61, 0x7A)]);
    let primary = alpha.repeat_range(1, 8);
    let dash = Automaton::char(0x2D);
    let subtag = dash.concatenate(&alnum.repeat_range(1, 8)).repeat();
    primary.concatenate(&subtag)
}

/// The language tags of rdf:PlainLiteral values: the BCP 47 `langtag` production,
/// in lowercase. Tags are case-insensitive, and the value space holds them in
/// lowercase (rdf:PlainLiteral §3), so `"a"@EN` and `"a"@en` are one value.
/// Structure mirrors `RDFPlainLiteralPatternValueSpaceSubset.languageTagAutomaton`,
/// which also admits uppercase letters.
pub fn language_tag_automaton() -> Automaton {
    let alpha = || Automaton::ranges(&[(0x61, 0x7A)]);
    let digit = || Automaton::ranges(&[(0x30, 0x39)]);
    let alnum = || Automaton::ranges(&[(0x30, 0x39), (0x61, 0x7A)]);
    let dash = || Automaton::char(0x2D);
    // language: ([a-z]{2,3}((-[a-z]{3}){0,3})?) | [a-z]{4} | [a-z]{5,8}
    let extlang = dash().concatenate(&alpha().repeat_range(3, 3)).repeat_range(0, 3).optional();
    let lang23 = alpha().repeat_range(2, 3).concatenate(&extlang);
    let lang4 = alpha().repeat_range(4, 4);
    let lang58 = alpha().repeat_range(5, 8);
    let language = lang23.union(&lang4).union(&lang58);
    // script: (-[a-z]{4})?
    let script = dash().concatenate(&alpha().repeat_range(4, 4)).optional();
    // region: (-([a-z]{2}|[0-9]{3}))?
    let region = dash()
        .concatenate(&alpha().repeat_range(2, 2).union(&digit().repeat_range(3, 3)))
        .optional();
    // variant: (-([a-z0-9]{5,8}|([0-9][a-z0-9]{3})))*
    let var_long = alnum().repeat_range(5, 8);
    let var_dig = digit().concatenate(&alnum().repeat_range(3, 3));
    let variant = dash().concatenate(&var_long.union(&var_dig)).repeat();
    // extension: (-([a-wy-z0-9](-[a-z0-9]{2,8})+))*
    let singleton = Automaton::ranges(&[
        (0x30, 0x39),
        (0x61, 0x77),
        (0x79, 0x7A), // a-w, y-z
    ]);
    let ext_tail = dash().concatenate(&alnum().repeat_range(2, 8)).repeat_min(1);
    let extension = dash().concatenate(&singleton.concatenate(&ext_tail)).repeat();
    // privateuse: (-x(-[a-z0-9]{1,8})+)?
    let priv_tail = dash().concatenate(&alnum().repeat_range(1, 8)).repeat_min(1);
    let privateuse = dash()
        .concatenate(&Automaton::char('x' as u32))
        .concatenate(&priv_tail)
        .optional();
    language
        .concatenate(&script)
        .concatenate(&region)
        .concatenate(&variant)
        .concatenate(&extension)
        .concatenate(&privateuse)
}

/// `s_separator` — the single SEPARATOR symbol.
pub fn separator() -> Automaton {
    Automaton::char(SEPARATOR)
}

/// `s_emptyLangTag` = separator (an empty language tag).
pub fn empty_lang_tag() -> Automaton {
    separator()
}

/// `s_nonemptyLangTag` = separator · languageTag.
pub fn nonempty_lang_tag() -> Automaton {
    separator().concatenate(&language_tag_automaton())
}

/// `s_anyLangTag` = separator · (languageTag | epsilon).
pub fn any_lang_tag() -> Automaton {
    separator().concatenate(&language_tag_automaton().union(&Automaton::epsilon()))
}

/// `getDatatypeAutomaton(datatypeURI)` — the combined-alphabet automaton for a
/// base string/PlainLiteral datatype. Returns `None` for an unmodelled URI.
pub fn datatype_automaton(local_name: &str, is_plain_literal: bool) -> Option<Automaton> {
    if is_plain_literal {
        // xsd:string · anyLangTag
        return Some(any_string().concatenate(&any_lang_tag()));
    }
    let string_part = match local_name {
        "string" => any_string(),
        "normalizedString" => normalized_string_automaton(),
        "token" => token_automaton(),
        "Name" => name_automaton(),
        "NCName" => ncname_automaton(),
        "NMTOKEN" => nmtoken_automaton(),
        "language" => language_automaton(),
        "anyURI" => any_uri_value_automaton(),
        _ => return None,
    };
    Some(string_part.concatenate(&empty_lang_tag()))
}

/// `getPatternAutomaton(pattern)` — the string-part pattern automaton, in the
/// combined alphabet (`regex · anyLangTag`), with the window on the length of
/// the string part (see `xsd_pattern_term`). `None` if the regex is unmodelled.
pub fn pattern_term(pattern: &str) -> Option<(Automaton, LengthWindow)> {
    let (string_part, window) = xsd_pattern_term(pattern)?;
    Some((string_part.concatenate(&any_lang_tag()), window))
}

/// `getLanguageRangeAutomaton(languageRange)`: the values `< "abc" , tag >` whose
/// tag matches the range under the extended filtering of RFC 4647 §3.3.2, as
/// rdf:PlainLiteral §3 (Table 1) requires. Subtags compare case-insensitively.
/// The first subtag of the range must match the first subtag of the tag, `*`
/// matching any. Every later subtag other than `*` must match a later subtag of
/// the tag, and only subtags that are not singletons may lie between them. So
/// `de-DE` matches `de-latn-de`, but neither `de` nor `de-x-de`. HermiT uses
/// basic filtering instead, which admits only the range itself or the range
/// followed by `-` as a prefix of the tag; the specification's own example
/// follows it, which OWL 2 erratum 7 records as an error. A value without a tag
/// never matches, even for the range `*`.
pub fn language_range_automaton(language_range: &str) -> Automaton {
    let range = language_range.to_ascii_lowercase();
    let mut subtags = range.split('-');
    let subtag_char = Automaton::ranges(&[(0x30, 0x39), (0x61, 0x7A)]);
    let any_subtag = subtag_char.repeat_min(1);
    let dash = Automaton::char(0x2D);
    let mut tag = match subtags.next() {
        Some("*") => any_subtag.clone(),
        first => Automaton::literal(first.unwrap_or_default()),
    };
    let skipped = dash.concatenate(&subtag_char.repeat_min(2)).repeat();
    for subtag in subtags.filter(|subtag| *subtag != "*") {
        tag = tag.concatenate(&skipped).concatenate(&dash).concatenate(&Automaton::literal(subtag));
    }
    let tag = tag.concatenate(&dash.concatenate(&any_subtag).repeat());
    any_string()
        .concatenate(&separator())
        .concatenate(&tag.intersection(&language_tag_automaton()))
}

/// `toAutomaton(minLength, maxLength)` for a length-bounded restriction: the
/// words whose string part has a length in `[min_length, max_length]`,
/// followed by a tag of the given mode. `max == None` means unbounded. The
/// length counts characters (code points), as the XSD 1.1 length facets do
/// (Part 2 §4.3.1): a supplementary character has length 1, although HermiT
/// counts it twice (Java `String.length()`). The string part may hold any
/// symbol but SEPARATOR; the datatype automaton it is intersected with
/// restricts the characters.
///
/// The automaton has one state per length up to the largest bound, so it is
/// only built for small bounds; `Automaton::cardinality_within` and its
/// siblings reason about large windows without it.
pub fn length_automaton(min_length: usize, max_length: Option<usize>, lang: LangMode) -> Automaton {
    // One state per number of characters read, up to the upper bound, or up to
    // the lower bound, which then stands for every longer length too.
    let last = max_length.unwrap_or(min_length);
    let mut string_part = Automaton::new();
    for _ in 0..=last {
        string_part.add_state();
    }
    for length in 0..=last {
        string_part.accept[length] = length >= min_length;
        let to = if length < last {
            length + 1
        } else if max_length.is_none() {
            last
        } else {
            continue;
        };
        for (min, max) in complement_ranges(&[(SEPARATOR, SEPARATOR)]) {
            string_part.trans[length].push(Transition { min, max, to });
        }
    }
    let tag = match lang {
        LangMode::Any => any_lang_tag(),
        LangMode::Absent => empty_lang_tag(),
        LangMode::Present => nonempty_lang_tag(),
    };
    string_part.concatenate(&tag)
}

// ===========================================================================
// Length windows over the string part, reasoned about symbolically.
// ===========================================================================

/// A window `[min, max]` of string-part lengths (in characters); a `max` of
/// `None` is unbounded.
pub type LengthWindow = (u64, Option<u64>);

/// The windows in both lists, pairwise intersected.
pub fn window_intersection(a: &[LengthWindow], b: &[LengthWindow]) -> Vec<LengthWindow> {
    let mut out = Vec::new();
    for &(a_min, a_max) in a {
        for &(b_min, b_max) in b {
            let min = a_min.max(b_min);
            let max = match (a_max, b_max) {
                (Some(x), Some(y)) => Some(x.min(y)),
                (x, y) => x.or(y),
            };
            if max.is_none_or(|max| min <= max) {
                out.push((min, max));
            }
        }
    }
    out
}

/// The lengths of the windows `a` outside every window of `b`.
pub fn window_difference(a: &[LengthWindow], b: &[LengthWindow]) -> Vec<LengthWindow> {
    let mut rest: Vec<LengthWindow> = a.to_vec();
    for &(b_min, b_max) in b {
        if b_max.is_some_and(|max| b_min > max) {
            continue;
        }
        let mut next = Vec::with_capacity(rest.len() * 2);
        for (min, max) in rest {
            if min < b_min {
                next.push((min, Some(max.map_or(b_min - 1, |max| max.min(b_min - 1)))));
            }
            if let Some(above) = b_max.and_then(|b_max| b_max.checked_add(1)) {
                let min = min.max(above);
                if max.is_none_or(|max| min <= max) {
                    next.push((min, max));
                }
            }
        }
        rest = next;
    }
    rest
}

/// The length of the string part of a word: its characters before SEPARATOR.
pub fn string_part_length(word: &str) -> u64 {
    word.chars().take_while(|&c| c as u32 != SEPARATOR).count() as u64
}

/// Windows up to this length are handled by stepping through the lengths one
/// by one; longer ones by repeated squaring.
const STEP_LIMIT: u64 = 4096;

/// Words longer than this are never materialised.
const ENUMERATION_LENGTH_LIMIT: u64 = 4096;

/// The most work the capped matrix powers of one count may take, in
/// products of two small counts or bitset words. Counts are capped at the
/// number the caller asks about, so the entries of a densely connected
/// part, whose words grow exponentially, reach the cap after a few squarings
/// and are then kept as bitsets; only a count whose small entries stay dense
/// over many states would pass the budget, and it is then reported as the
/// cap ("at least"), which never causes a cardinality clash.
const MATRIX_WORK_LIMIT: u64 = 1 << 31;

/// The string part of a determinised automaton as a graph whose steps are the
/// characters before SEPARATOR, so that a word's string-part length is the
/// number of steps of its path. The states are the live ones (those that
/// reach an accepting state) reached before SEPARATOR; `tail[q]` counts the
/// ways to finish a word from `q` without another string character (accept
/// here, or read SEPARATOR and a tag), saturating, with `tail_infinite[q]`
/// set when there are infinitely many.
struct LengthView {
    start: Option<usize>,
    succ: Vec<Vec<(usize, u128)>>,
    tail: Vec<u128>,
    tail_infinite: Vec<bool>,
}

impl LengthView {
    fn new(automaton: &Automaton) -> LengthView {
        let dfa = automaton.determinize();
        // The nodes are pairs (state, after SEPARATOR).
        let mut ids: HashMap<(usize, bool), usize> = HashMap::new();
        let mut nodes: Vec<(usize, bool)> = vec![(dfa.start, false)];
        ids.insert((dfa.start, false), 0);
        // Edges: (target, width, whether the edge reads a string character).
        let mut edges: Vec<Vec<(usize, u128, bool)>> = vec![Vec::new()];
        let mut i = 0;
        while i < nodes.len() {
            let (state, after) = nodes[i];
            for t in &dfa.trans[state] {
                let mut parts: Vec<(u32, u32, bool)> = Vec::new();
                // SEPARATOR is U+0001, so only U+0000 lies below it.
                if t.min < SEPARATOR {
                    parts.push((t.min, SEPARATOR - 1, false));
                }
                if t.min <= SEPARATOR && SEPARATOR <= t.max {
                    parts.push((SEPARATOR, SEPARATOR, true));
                }
                if t.max > SEPARATOR {
                    parts.push((t.min.max(SEPARATOR + 1), t.max, false));
                }
                for (min, max, separator) in parts {
                    if separator && after {
                        continue; // a second SEPARATOR: no value
                    }
                    let key = (t.to, after || separator);
                    let to = *ids.entry(key).or_insert_with(|| {
                        nodes.push(key);
                        edges.push(Vec::new());
                        nodes.len() - 1
                    });
                    edges[i].push((to, (max - min) as u128 + 1, !after && !separator));
                }
            }
            i += 1;
        }
        let n = nodes.len();
        let mut live = vec![false; n];
        let mut reverse: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (from, out) in edges.iter().enumerate() {
            for &(to, _, _) in out {
                reverse[to].push(from);
            }
        }
        let mut stack: Vec<usize> = (0..n).filter(|&v| dfa.accept[nodes[v].0]).collect();
        for &v in &stack {
            live[v] = true;
        }
        while let Some(v) = stack.pop() {
            for &p in &reverse[v] {
                if !live[p] {
                    live[p] = true;
                    stack.push(p);
                }
            }
        }
        // The words after SEPARATOR, counted from each live node there.
        let mut tag_words: Vec<Option<(u128, bool)>> = vec![None; n];
        let mut on_stack = vec![false; n];
        fn count_tags(
            v: usize,
            edges: &[Vec<(usize, u128, bool)>],
            accept: &[bool],
            live: &[bool],
            memo: &mut [Option<(u128, bool)>],
            on_stack: &mut [bool],
        ) -> (u128, bool) {
            if let Some(known) = memo[v] {
                return known;
            }
            if on_stack[v] {
                return (u128::MAX, true); // a live cycle: infinitely many tags
            }
            on_stack[v] = true;
            let (mut total, mut infinite) = (accept[v] as u128, false);
            for &(to, width, _) in &edges[v] {
                if live[to] {
                    let (count, inf) = count_tags(to, edges, accept, live, memo, on_stack);
                    total = total.saturating_add(width.saturating_mul(count));
                    infinite |= inf;
                }
            }
            on_stack[v] = false;
            if infinite {
                total = u128::MAX;
            }
            memo[v] = Some((total, infinite));
            (total, infinite)
        }
        let accept: Vec<bool> = nodes.iter().map(|&(state, _)| dfa.accept[state]).collect();
        // The live string-part nodes, renumbered.
        let mut index = vec![usize::MAX; n];
        let mut count = 0;
        for v in 0..n {
            if live[v] && !nodes[v].1 {
                index[v] = count;
                count += 1;
            }
        }
        let mut view = LengthView {
            start: (index[0] != usize::MAX).then_some(index[0]),
            succ: vec![Vec::new(); count],
            tail: vec![0; count],
            tail_infinite: vec![false; count],
        };
        for v in 0..n {
            let q = index[v];
            if q == usize::MAX {
                continue;
            }
            let mut tail = accept[v] as u128;
            for &(to, width, character) in &edges[v] {
                if !live[to] {
                    continue;
                }
                if character {
                    view.succ[q].push((index[to], width));
                } else {
                    let (words, infinite) =
                        count_tags(to, &edges, &accept, &live, &mut tag_words, &mut on_stack);
                    tail = tail.saturating_add(width.saturating_mul(words));
                    view.tail_infinite[q] |= infinite;
                }
            }
            view.tail[q] = tail;
        }
        view
    }

    fn len(&self) -> usize {
        self.succ.len()
    }

    /// Whether a cycle runs through the string-part nodes. They are all live
    /// and reachable, so a cycle gives words of unbounded length.
    fn has_cycle(&self) -> bool {
        let mut indegree = vec![0usize; self.len()];
        for out in &self.succ {
            for &(to, _) in out {
                indegree[to] += 1;
            }
        }
        let mut ready: Vec<usize> = (0..self.len()).filter(|&q| indegree[q] == 0).collect();
        let mut seen = 0;
        while let Some(q) = ready.pop() {
            seen += 1;
            for &(to, _) in &self.succ[q] {
                indegree[to] -= 1;
                if indegree[to] == 0 {
                    ready.push(to);
                }
            }
        }
        seen < self.len()
    }

    /// The nodes reached from the start by exactly `steps` string characters.
    fn reached_at(&self, start: usize, steps: u64) -> Vec<bool> {
        let n = self.len();
        let mut current = vec![false; n];
        current[start] = true;
        // The sets reached repeat, usually soon: step through them first.
        let step_set = |set: &Vec<bool>| -> Vec<bool> {
            let mut next = vec![false; n];
            for (q, _) in set.iter().enumerate().filter(|(_, &b)| b) {
                for &(to, _) in &self.succ[q] {
                    next[to] = true;
                }
            }
            next
        };
        let edges: u64 = self.succ.iter().map(|out| out.len() as u64 + 1).sum();
        let limit = PERIODIC_WORK_LIMIT / edges.max(1);
        let cycle = if steps <= limit { Some((steps, 1)) } else { cycle_of(&current, step_set, limit) };
        if let Some((mu, period)) = cycle {
            let target = if steps < mu { steps } else { mu + (steps - mu) % period };
            for _ in 0..target {
                current = step_set(&current);
            }
            return current;
        }
        let step = |set: &[bool], matrix: &[Vec<u64>]| -> Vec<bool> {
            let mut next = vec![false; n];
            for (q, _) in set.iter().enumerate().filter(|(_, &b)| b) {
                for (word, bits) in matrix[q].iter().enumerate() {
                    let mut bits = *bits;
                    while bits != 0 {
                        next[word * 64 + bits.trailing_zeros() as usize] = true;
                        bits &= bits - 1;
                    }
                }
            }
            next
        };
        let words = n.div_ceil(64);
        // The one-step reachability matrix, as bitsets, squared repeatedly.
        let mut power: Vec<Vec<u64>> = vec![vec![0; words]; n];
        for (q, out) in self.succ.iter().enumerate() {
            for &(to, _) in out {
                power[q][to / 64] |= 1 << (to % 64);
            }
        }
        let mut remaining = steps;
        while remaining > 0 {
            if remaining & 1 == 1 {
                current = step(&current, &power);
            }
            remaining >>= 1;
            if remaining > 0 {
                let mut squared = vec![vec![0u64; words]; n];
                for q in 0..n {
                    for word in 0..words {
                        let mut bits = power[q][word];
                        while bits != 0 {
                            let via = word * 64 + bits.trailing_zeros() as usize;
                            for (target, source) in squared[q].iter_mut().zip(&power[via]) {
                                *target |= *source;
                            }
                            bits &= bits - 1;
                        }
                    }
                }
                power = squared;
            }
        }
        current
    }

    /// Whether some node in `target` is reached from the start by a number of
    /// string characters in the window.
    fn window_reaches(&self, (min, max): LengthWindow, target: &dyn Fn(usize) -> bool) -> bool {
        let Some(start) = self.start else {
            return false;
        };
        if max.is_some_and(|max| min > max) {
            return false;
        }
        // Every longer path passes a node reached after exactly `min` steps, so
        // the lengths at least `min` are `min` plus the distances from there.
        let reached = self.reached_at(start, min);
        let mut distance: Vec<Option<u64>> =
            reached.iter().map(|&r| r.then_some(0)).collect();
        let mut queue: VecDeque<usize> = (0..self.len()).filter(|&q| reached[q]).collect();
        while let Some(q) = queue.pop_front() {
            let d = distance[q].unwrap_or_default();
            if max.is_some_and(|max| d > max - min) {
                break;
            }
            if target(q) {
                return true;
            }
            for &(to, _) in &self.succ[q] {
                if distance[to].is_none() {
                    distance[to] = Some(d + 1);
                    queue.push_back(to);
                }
            }
        }
        false
    }

    /// The number of words whose string part has a length in `[min, max]`,
    /// capped at `cap`: exact when below it, and `cap` when there are at least
    /// `cap`; the caller has excluded infinitely many tags there. `None` only
    /// when the capped matrix powers pass `MATRIX_WORK_LIMIT`.
    fn count_between(&self, start: usize, min: u64, max: u64, cap: u128) -> Option<u128> {
        let n = self.len();
        let add = |a: u128, b: u128| a.saturating_add(b).min(cap);
        let mul = |a: u128, b: u128| a.saturating_mul(b).min(cap);
        if max <= STEP_LIMIT {
            let mut paths = vec![0u128; n];
            paths[start] = 1;
            let mut total: u128 = 0;
            for length in 0..=max {
                if length >= min {
                    for (count, tail) in paths.iter().zip(&self.tail) {
                        total = add(total, mul(*count, *tail));
                    }
                    if total == cap {
                        break;
                    }
                }
                if length == max {
                    break;
                }
                let mut next = vec![0u128; n];
                for (&count, out) in paths.iter().zip(&self.succ) {
                    if count == 0 {
                        continue;
                    }
                    for &(to, width) in out {
                        next[to] = add(next[to], mul(count, width));
                    }
                }
                paths = next;
            }
            return Some(total);
        }
        if let Some(total) = self.count_periodic(start, min, max, cap) {
            return Some(total);
        }
        // With M the step matrix and t the tails, A = [[M, t], [0, 1]] has
        // A^k = [[M^k, sum_{j<k} M^j t], [0, 1]]. The count is
        // e_start M^min sum_{j<=max-min} M^j t: the row e_start A^min, less
        // its last entry, times A^(max-min+1), at the last entry. Capping every
        // count at `cap` commutes with sums and products, so the capped powers
        // give the capped count.
        let size = n + 1;
        let mut a = CappedMatrix::new(size, cap);
        for (q, out) in self.succ.iter().enumerate() {
            let mut row: Vec<(usize, u128)> = Vec::new();
            for &(to, width) in out {
                match row.iter_mut().find(|(j, _)| *j == to) {
                    Some((_, count)) => *count = add(*count, width),
                    None => row.push((to, width.min(cap))),
                }
            }
            if self.tail[q] > 0 {
                row.push((n, self.tail[q].min(cap)));
            }
            a.set_row(q, row);
        }
        a.set_row(n, vec![(n, 1)]);
        let mut work = 0u64;
        let mut row = vec![0u128; size];
        row[start] = 1;
        let mut at_min = a.row_times_power(row, min, &mut work)?;
        at_min[n] = 0;
        let sums = a.row_times_power(at_min, max - min + 1, &mut work)?;
        Some(sums[n])
    }
}

impl LengthView {
    /// The capped counts of the paths from the start of one more step.
    fn step_row(&self, row: &[u128], cap: u128) -> Vec<u128> {
        let mut next = vec![0u128; row.len()];
        for (&count, out) in row.iter().zip(&self.succ) {
            if count == 0 {
                continue;
            }
            for &(to, width) in out {
                next[to] = next[to].saturating_add(count.saturating_mul(width)).min(cap);
            }
        }
        next
    }

    /// `count_between` by stepping through the lengths while the capped
    /// counts of the paths from the start, a sequence over a finite set,
    /// have not yet repeated (Brent's cycle detection), or `None` when they
    /// do not repeat within `PERIODIC_WORK_LIMIT`. Counts capped at a small
    /// number repeat soon wherever the words grow exponentially, as in a
    /// densely connected automaton, whose matrix powers are dense; a count
    /// that grows only polynomially, as over two long cycles in sequence,
    /// repeats late, and its sparse matrix powers are cheap instead.
    fn count_periodic(&self, start: usize, min: u64, max: u64, cap: u128) -> Option<u128> {
        let edges: u64 = self.succ.iter().map(|out| out.len() as u64 + 1).sum();
        let limit = PERIODIC_WORK_LIMIT / edges.max(1);
        let mut first = vec![0u128; self.len()];
        first[start] = 1;
        let (mu, period) = cycle_of(&first, |row| self.step_row(row, cap), limit)?;
        // The capped count of the words of each length below mu + period;
        // those of a longer length repeat with the period.
        let mut row = first;
        let mut words: Vec<u128> = Vec::with_capacity((mu + period) as usize);
        for _ in 0..mu + period {
            let count = row
                .iter()
                .zip(&self.tail)
                .fold(0u128, |total, (count, tail)| total.saturating_add(count.saturating_mul(*tail)).min(cap));
            words.push(count);
            row = self.step_row(&row, cap);
        }
        let mut total: u128 = 0;
        for length in min..max.saturating_add(1).min(mu) {
            total = total.saturating_add(words[length as usize]).min(cap);
        }
        let from = min.max(mu);
        if from <= max {
            for residue in 0..period {
                // The lengths from..=max that are mu + residue modulo period.
                let first = from + (mu + residue + period - from % period) % period;
                if first > max || total == cap {
                    continue;
                }
                let occurrences = ((max - first) / period + 1) as u128;
                let count = words[(mu + residue) as usize];
                total = total.saturating_add(count.saturating_mul(occurrences)).min(cap);
            }
        }
        Some(total)
    }
}

/// Where the sequence `first`, `step(first)`, ... repeats (Brent's cycle
/// detection): the first index `mu` of the cycle and its length, or `None`
/// after `limit` steps.
fn cycle_of<T: Clone + PartialEq>(first: &T, step: impl Fn(&T) -> T, limit: u64) -> Option<(u64, u64)> {
    let mut steps = 0u64;
    let (mut power, mut period) = (1u64, 1u64);
    let mut tortoise = first.clone();
    let mut hare = step(first);
    while tortoise != hare {
        if power == period {
            tortoise = hare.clone();
            power *= 2;
            period = 0;
        }
        hare = step(&hare);
        period += 1;
        steps += 1;
        if steps > limit {
            return None;
        }
    }
    let mut tortoise = first.clone();
    let mut hare = first.clone();
    for _ in 0..period {
        hare = step(&hare);
    }
    let mut mu = 0u64;
    while tortoise != hare {
        tortoise = step(&tortoise);
        hare = step(&hare);
        mu += 1;
        steps += 1;
        if steps > limit {
            return None;
        }
    }
    Some((mu, period))
}

/// The most work, in edges followed, that `count_periodic` and `reached_at`
/// may take stepping through the lengths.
const PERIODIC_WORK_LIMIT: u64 = 1 << 26;

/// A square matrix of counts capped at `cap`: per row, the columns whose
/// entry is `cap` as a bitset, and the other nonzero entries.
#[derive(Clone)]
struct CappedMatrix {
    cap: u128,
    words: usize,
    full: Vec<Vec<u64>>,
    small: Vec<Vec<(usize, u128)>>,
}

impl CappedMatrix {
    fn new(size: usize, cap: u128) -> CappedMatrix {
        let words = size.div_ceil(64);
        CappedMatrix { cap, words, full: vec![vec![0; words]; size], small: vec![Vec::new(); size] }
    }

    fn size(&self) -> usize {
        self.small.len()
    }

    /// Sets row `i` from its nonzero entries, each at most `cap`, with
    /// distinct columns.
    fn set_row(&mut self, i: usize, entries: Vec<(usize, u128)>) {
        self.full[i] = vec![0; self.words];
        self.small[i] = Vec::new();
        for (j, x) in entries {
            if x >= self.cap {
                self.full[i][j / 64] |= 1 << (j % 64);
            } else if x > 0 {
                self.small[i].push((j, x));
            }
        }
    }

    /// The capped product `self · other`, or `None` past the work budget. An
    /// entry is `cap` when a term has one factor at `cap` and the other
    /// nonzero; otherwise it is the capped sum of the terms of small factors.
    fn product(&self, other: &CappedMatrix, work: &mut u64) -> Option<CappedMatrix> {
        let size = self.size();
        let cap = self.cap;
        // Rows of `other` with the same columns at `cap`, and with the same
        // nonzero columns, are grouped, so that a row of the product ORs each
        // distinct bitset once: the saturated rows of a dense part repeat.
        fn groups(rows: impl Iterator<Item = Vec<u64>>) -> (Vec<usize>, Vec<Vec<u64>>) {
            let mut ids: HashMap<Vec<u64>, usize> = HashMap::new();
            let mut distinct: Vec<Vec<u64>> = Vec::new();
            let group = rows
                .map(|bits| {
                    *ids.entry(bits.clone()).or_insert_with(|| {
                        distinct.push(bits);
                        distinct.len() - 1
                    })
                })
                .collect();
            (group, distinct)
        }
        let (full_group, full_rows) = groups(other.full.iter().cloned());
        let (nonzero_group, nonzero_rows) = groups((0..size).map(|k| {
            let mut bits = other.full[k].clone();
            for &(j, _) in &other.small[k] {
                bits[j / 64] |= 1 << (j % 64);
            }
            bits
        }));
        let mut full_seen = vec![usize::MAX; full_rows.len()];
        let mut nonzero_seen = vec![usize::MAX; nonzero_rows.len()];
        let mut out = CappedMatrix::new(size, cap);
        let mut accumulator = vec![0u128; size];
        let mut touched: Vec<usize> = Vec::new();
        for i in 0..size {
            let full = &mut out.full[i];
            let mut row_work = self.words as u64;
            let or = |target: &mut [u64], source: &[u64]| {
                for (t, s) in target.iter_mut().zip(source) {
                    *t |= *s;
                }
            };
            for (word, &bits) in self.full[i].iter().enumerate() {
                let mut bits = bits;
                while bits != 0 {
                    let g = nonzero_group[word * 64 + bits.trailing_zeros() as usize];
                    if nonzero_seen[g] != i {
                        nonzero_seen[g] = i;
                        or(full, &nonzero_rows[g]);
                        row_work += self.words as u64;
                    }
                    bits &= bits - 1;
                }
            }
            for &(k, x) in &self.small[i] {
                let g = full_group[k];
                if full_seen[g] != i {
                    full_seen[g] = i;
                    or(full, &full_rows[g]);
                    row_work += self.words as u64;
                }
                row_work += other.small[k].len() as u64;
                for &(j, y) in &other.small[k] {
                    if accumulator[j] == 0 {
                        touched.push(j);
                    }
                    accumulator[j] = accumulator[j].saturating_add(x.saturating_mul(y)).min(cap);
                }
            }
            *work = work.saturating_add(row_work);
            if *work > MATRIX_WORK_LIMIT {
                return None;
            }
            touched.sort_unstable();
            for &j in &touched {
                let x = std::mem::take(&mut accumulator[j]);
                if full[j / 64] & (1 << (j % 64)) != 0 {
                    continue;
                }
                if x == cap {
                    full[j / 64] |= 1 << (j % 64);
                } else {
                    out.small[i].push((j, x));
                }
            }
            touched.clear();
        }
        Some(out)
    }

    /// The capped row `row · self`.
    fn row_times(&self, row: &[u128]) -> Vec<u128> {
        let cap = self.cap;
        let mut out = vec![0u128; row.len()];
        for (k, &x) in row.iter().enumerate().filter(|(_, &x)| x > 0) {
            for (word, &bits) in self.full[k].iter().enumerate() {
                let mut bits = bits;
                while bits != 0 {
                    out[word * 64 + bits.trailing_zeros() as usize] = cap;
                    bits &= bits - 1;
                }
            }
            for &(j, y) in &self.small[k] {
                out[j] = out[j].saturating_add(x.saturating_mul(y)).min(cap);
            }
        }
        out
    }

    /// The capped row `row · self^exponent`, or `None` past the work budget.
    fn row_times_power(&self, mut row: Vec<u128>, mut exponent: u64, work: &mut u64) -> Option<Vec<u128>> {
        let mut power = self.clone();
        while exponent > 0 {
            if exponent & 1 == 1 {
                row = power.row_times(&row);
            }
            exponent >>= 1;
            if exponent > 0 {
                power = power.product(&power, work)?;
            }
        }
        Some(row)
    }
}

impl Automaton {
    /// Whether no word has a string part whose length lies in a window. Only
    /// the determinised automaton is built, never one per length, so a window
    /// near 2^31 costs a logarithmic number of steps.
    pub fn is_empty_within(&self, windows: &[LengthWindow]) -> bool {
        let view = LengthView::new(self);
        !windows.iter().any(|&window| view.window_reaches(window, &|q| view.tail[q] > 0))
    }

    /// The number of words whose string part has a length in a window, or
    /// `None` when there are infinitely many. Counts saturate at `u128::MAX`,
    /// as `cardinality` does; the windows must be disjoint.
    pub fn cardinality_within(&self, windows: &[LengthWindow]) -> Option<u128> {
        self.cardinality_within_capped(windows, u128::MAX)
    }

    /// The number of words whose string part has a length in a window, capped
    /// at `cap`, or `None` when there are infinitely many: exact when below
    /// `cap`, and `cap` when there are at least `cap`, which is all that
    /// "at least `cap` values" needs. The windows must be disjoint.
    pub fn cardinality_within_capped(&self, windows: &[LengthWindow], cap: u128) -> Option<u128> {
        let cap = cap.max(1);
        let view = LengthView::new(self);
        let Some(start) = view.start else {
            return Some(0);
        };
        // Infinitely many tags after a string of a length in a window.
        if view.tail_infinite.iter().any(|&infinite| infinite)
            && windows.iter().any(|&window| view.window_reaches(window, &|q| view.tail_infinite[q]))
        {
            return None;
        }
        let cyclic = view.has_cycle();
        let longest = view.len() as u64; // no path is longer without a cycle
        let mut total: u128 = 0;
        for &(min, max) in windows {
            let max = match max {
                // A cycle gives words of every large enough length in some
                // progression, so an unbounded window holds infinitely many.
                None if cyclic => {
                    if view.window_reaches((min, None), &|q| view.tail[q] > 0) {
                        return None;
                    }
                    continue;
                }
                None => longest,
                Some(max) if cyclic => max,
                Some(max) => max.min(longest),
            };
            if min <= max && total < cap {
                // Past the work budget, "at least `cap`" never causes a clash.
                let count = view.count_between(start, min, max, cap - total).unwrap_or(cap);
                total = total.saturating_add(count).min(cap);
            }
        }
        Some(total)
    }

    /// Up to `cap` words whose string part has a length in a window, or `None`
    /// when there are more, or when one would be longer than
    /// `ENUMERATION_LENGTH_LIMIT` characters.
    pub fn finite_strings_within(&self, windows: &[LengthWindow], cap: usize) -> Option<Vec<String>> {
        let count = self.cardinality_within_capped(windows, (cap as u128).saturating_add(1))?;
        if count > cap as u128 {
            return None;
        }
        let view = LengthView::new(self);
        let longest = if view.has_cycle() { u64::MAX } else { view.len() as u64 };
        let mut lengths = Automaton::empty_language();
        for &(min, max) in windows {
            if !view.window_reaches((min, max), &|q| view.tail[q] > 0) {
                continue;
            }
            let max = max.unwrap_or(u64::MAX).min(longest);
            if max > ENUMERATION_LENGTH_LIMIT {
                return None;
            }
            if min <= max {
                lengths = lengths.union(&length_automaton(min as usize, Some(max as usize), LangMode::Any));
            }
        }
        self.intersection(&lengths).finite_strings(cap)
    }
}

/// Which language-tag mode a length window applies to.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LangMode {
    Any,
    Absent,
    Present,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_pattern_membership_and_emptiness() {
        let a = xsd_pattern_to_automaton("[ab]c").unwrap();
        assert!(a.run("ac"));
        assert!(a.run("bc"));
        assert!(!a.run("cc"));
        assert!(!a.run("ab"));
        assert!(!a.is_empty());
        assert_eq!(a.cardinality(), Some(2));
    }

    #[test]
    fn pattern_intersection_empty_and_nonempty() {
        // a+ ∩ b+ = ∅
        let a = xsd_pattern_to_automaton("a+").unwrap();
        let b = xsd_pattern_to_automaton("b+").unwrap();
        assert!(a.intersection(&b).is_empty());
        // [ab]+ ∩ a+ = a+ (non-empty, infinite)
        let ab = xsd_pattern_to_automaton("[ab]+").unwrap();
        let inter = ab.intersection(&a);
        assert!(!inter.is_empty());
        assert_eq!(inter.cardinality(), None); // infinite
    }

    #[test]
    fn complement_and_minus() {
        // a* minus (a a*) should leave just "" .
        let astar = xsd_pattern_to_automaton("a*").unwrap();
        let aplus = xsd_pattern_to_automaton("aa*").unwrap();
        let diff = astar.minus(&aplus);
        assert!(!diff.is_empty());
        assert_eq!(diff.cardinality(), Some(1)); // {""}
        // Unlike dk.brics getFiniteStrings (issue #9), the empty word is listed.
        assert_eq!(diff.finite_strings(10), Some(vec![String::new()]));
        assert!(diff.run(""));
        assert!(!diff.run("a"));
        // a+ minus a+ = ∅
        let aplus2 = xsd_pattern_to_automaton("a+").unwrap();
        assert!(aplus.minus(&aplus2).is_empty());
    }

    #[test]
    fn multi_negation_cover() {
        // [ab] minus a minus b = ∅
        let base = xsd_pattern_to_automaton("[ab]").unwrap();
        let a = xsd_pattern_to_automaton("a").unwrap();
        let b = xsd_pattern_to_automaton("b").unwrap();
        let r = base.minus(&a).minus(&b);
        assert!(r.is_empty());
        // but [abc] minus a minus b is not empty (c survives)
        let base3 = xsd_pattern_to_automaton("[abc]").unwrap();
        let r2 = base3.minus(&a).minus(&b);
        assert!(!r2.is_empty());
        assert!(r2.run("c"));
    }

    #[test]
    fn bounded_quantifier_cardinality() {
        let a = xsd_pattern_to_automaton("[01]{3}").unwrap();
        assert_eq!(a.cardinality(), Some(8));
        let words = a.finite_strings(100).unwrap();
        assert_eq!(words.len(), 8);
        assert!(words.contains(&"000".to_string()));
        assert!(words.contains(&"111".to_string()));
    }

    #[test]
    fn token_vs_normalized_subtype_automata() {
        let token = token_automaton();
        assert!(token.run("hello"));
        assert!(token.run("a b c"));
        assert!(!token.run(" a")); // leading space not allowed
        assert!(!token.run("a  b")); // double space not allowed
        assert!(token.run("")); // empty allowed
        let ncname = ncname_automaton();
        assert!(ncname.run("foo"));
        assert!(!ncname.run("a:b")); // colon not allowed in NCName
        assert!(!ncname.run("1abc")); // can't start with digit
        let name = name_automaton();
        assert!(name.run("a:b"));
    }

    #[test]
    fn token_minus_token_is_empty() {
        let token = token_automaton();
        let token2 = token_automaton();
        assert!(token.minus(&token2).is_empty());
    }

    #[test]
    fn unicode_general_categories_resolve_via_regex_syntax() {
        // Lu: A is uppercase, a is not.
        let lu = xsd_pattern_to_automaton("\\p{Lu}").unwrap();
        assert!(lu.run("A"));
        assert!(lu.run("Z"));
        assert!(!lu.run("a"));
        assert!(!lu.run("5"));
        // Ll: lowercase.
        let ll = xsd_pattern_to_automaton("\\p{Ll}").unwrap();
        assert!(ll.run("a"));
        assert!(!ll.run("A"));
        // The full category set XSD allows must all translate (no scope-out).
        for cat in [
            "C", "Cc", "Cf", "Co", "Cn", "L", "Lu", "Ll", "Lt", "Lm", "Lo", "M", "Mn", "Mc",
            "Me", "N", "Nd", "Nl", "No", "P", "Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po", "S",
            "Sm", "Sc", "Sk", "So", "Z", "Zs", "Zl", "Zp",
        ] {
            assert!(
                xsd_pattern_to_automaton(&format!("\\p{{{cat}}}")).is_some(),
                "category {cat} should resolve"
            );
        }
        // Categories nest: Lu ⊂ L, so L admits both 'A' and 'a'.
        let l = xsd_pattern_to_automaton("\\p{L}").unwrap();
        assert!(l.run("A") && l.run("a"));
        // Nd is the decimal digits.
        let nd = xsd_pattern_to_automaton("\\p{Nd}").unwrap();
        assert!(nd.run("0") && nd.run("9"));
        assert!(!nd.run("a"));
    }

    #[test]
    fn unicode_property_complement_and_unknown() {
        // \P{Lu} (complement) must NOT contain 'A' but must contain 'a'.
        let not_lu = xsd_pattern_to_automaton("\\P{Lu}").unwrap();
        assert!(!not_lu.run("A"));
        assert!(not_lu.run("a"));
        assert!(not_lu.run("5"));
        // A genuinely unknown / misspelled property name scopes out (None).
        assert!(xsd_pattern_to_automaton("\\p{NotACategory}").is_none());
        assert!(xsd_pattern_to_automaton("\\p{Lx}").is_none());
    }

    #[test]
    fn unicode_block_names_resolve_to_fixed_ranges() {
        // IsBasicLatin = U+0000..U+007F.
        let basic = xsd_pattern_to_automaton("\\p{IsBasicLatin}").unwrap();
        assert!(basic.run("A"));
        assert!(basic.run("~"));
        assert!(!basic.run("\u{00A1}")); // outside Basic Latin
        // Greek block U+0370..U+03FF.
        let greek = xsd_pattern_to_automaton("\\p{IsGreek}").unwrap();
        assert!(greek.run("\u{03B1}")); // alpha
        assert!(!greek.run("a"));
        // Punctuation-insensitive name matching for the hyphenated blocks.
        assert!(xsd_pattern_to_automaton("\\p{IsLatin-1Supplement}").is_some());
        assert!(xsd_pattern_to_automaton("\\p{IsLatin1Supplement}").is_some());
        // Unknown block scopes out.
        assert!(xsd_pattern_to_automaton("\\p{IsNotABlock}").is_none());
        // Negated block: \P{IsBasicLatin} excludes ASCII.
        let not_basic = xsd_pattern_to_automaton("\\P{IsBasicLatin}").unwrap();
        assert!(!not_basic.run("A"));
        assert!(not_basic.run("\u{00A1}"));
    }

    #[test]
    fn unicode_block_set_matches_dk_brics_exactly() {
        // The block set is the dk.brics 1.11-8 `unicodeblock_names_array` (Unicode 3.1
        // / XSD 1.0): exactly 92 blocks. Guard the count so neither over- nor
        // under-population slips in (every extra name would wrongly accept a pattern
        // Java rejects; every missing name would wrongly scope out a valid one).
        assert_eq!(XSD_UNICODE_BLOCKS.len(), 92);
        // The table is sorted by start code point and never overlaps.
        for w in XSD_UNICODE_BLOCKS.windows(2) {
            assert!(w[0].1 <= w[0].2, "{} has lo>hi", w[0].0);
            assert!(w[0].2 < w[1].1, "{} overlaps {}", w[0].0, w[1].0);
        }
    }

    #[test]
    fn unicode_blocks_bmp_membership() {
        // Several BMP blocks resolve to their exact (Unicode-3.1) ranges, with
        // membership in/out checks across boundaries.
        let cyr = xsd_pattern_to_automaton("\\p{IsCyrillic}").unwrap();
        assert!(cyr.run("\u{0400}") && cyr.run("\u{04FF}"));
        assert!(!cyr.run("\u{03FF}") && !cyr.run("\u{0500}"));

        // CJKUnifiedIdeographsExtensionA ends at U+4DB5 in the pinned dk.brics build
        // (NOT U+4DBF), so U+4DB6..U+4DBF are *outside* the block.
        let exta = xsd_pattern_to_automaton("\\p{IsCJKUnifiedIdeographsExtensionA}").unwrap();
        assert!(exta.run("\u{3400}") && exta.run("\u{4DB5}"));
        assert!(!exta.run("\u{4DB6}") && !exta.run("\u{4DBF}"));

        // Specials is U+FFF0..U+FFFD (pre-3.2): U+FFFE/U+FFFF are outside.
        let spec = xsd_pattern_to_automaton("\\p{IsSpecials}").unwrap();
        assert!(spec.run("\u{FFF0}") && spec.run("\u{FFFD}"));
        assert!(!spec.run("\u{FFEF}"));

        // The 3.2-era name `CombiningDiacriticalMarksforSymbols` is NOT a dk.brics
        // block name; only the pre-3.2 `CombiningMarksforSymbols` is valid.
        let cms = xsd_pattern_to_automaton("\\p{IsCombiningMarksforSymbols}").unwrap();
        assert!(cms.run("\u{20D0}") && cms.run("\u{20FF}"));
        assert!(xsd_pattern_to_automaton("\\p{IsCombiningDiacriticalMarksforSymbols}").is_none());
    }

    #[test]
    fn unicode_blocks_supplementary_plane_membership() {
        // A supplementary-plane block resolves to its true scalar code-point range
        // (dk.brics encodes these as UTF-16 surrogate pairs; the table uses real
        // code points). MathematicalAlphanumericSymbols = U+1D400..U+1D7FF.
        let math = xsd_pattern_to_automaton("\\p{IsMathematicalAlphanumericSymbols}").unwrap();
        assert!(math.run("\u{1D400}") && math.run("\u{1D7FF}"));
        assert!(!math.run("\u{1D3FF}") && !math.run("\u{1D800}"));

        // CJKUnifiedIdeographsExtensionB ends at U+2A6D6 (Unicode 3.1), not U+2A6DF.
        let extb = xsd_pattern_to_automaton("\\p{IsCJKUnifiedIdeographsExtensionB}").unwrap();
        assert!(extb.run("\u{20000}") && extb.run("\u{2A6D6}"));
        assert!(!extb.run("\u{2A6D7}"));
    }

    #[test]
    fn invalid_block_name_rejects_pattern() {
        // An invalid block name makes the whole pattern malformed (None), exactly as
        // dk.brics rejects it — it must NOT silently widen the value space. This holds
        // for both bare and embedded uses, and for names dropped from the over-broad
        // committed list (e.g. surrogates / private-use / newer-Unicode blocks that
        // dk.brics 1.11-8 does not know).
        for name in [
            "IsTotallyMadeUp",
            "IsHighSurrogates",       // not a dk.brics block
            "IsPrivateUseArea",       // not a dk.brics block
            "IsCyrillicSupplement",   // post-3.1, not in dk.brics 1.11-8
            "IsAegeanNumbers",        // post-3.1
            "IsVariationSelectors",   // post-3.1
        ] {
            let pat = format!("\\p{{{name}}}");
            assert!(xsd_pattern_to_automaton(&pat).is_none(), "{name} should reject");
            // Also malformed when used inside a larger pattern.
            assert!(xsd_pattern_to_automaton(&format!("a\\p{{{name}}}b")).is_none());
        }
    }

    #[test]
    fn large_bounded_repetitions_are_length_windows() {
        let states = |a: &Automaton| a.trans.len();
        // One large repetition of a fixed-length body among fixed-length
        // pieces: the body's star with a window, not a state per copy.
        let (a, window) = xsd_pattern_term("a{2147483000}").unwrap();
        assert_eq!(window, (2147483000, Some(2147483000)));
        assert!(states(&a) < 10);
        let term = a.concatenate(&empty_lang_tag());
        assert!(!term.is_empty_within(&[window]));
        assert_eq!(term.cardinality_within(&[window]), Some(1));
        let (a, window) = xsd_pattern_term("x[ab]{1000,2000}(cd)").unwrap();
        assert_eq!(window, (1003, Some(2003)));
        assert!(states(&a) < 20);
        // x, 300 to 400 copies of `a` and y: 101 words.
        let (a, window) = xsd_pattern_term("xa{300,400}y").unwrap();
        assert_eq!(window, (302, Some(402)));
        let term = a.concatenate(&empty_lang_tag());
        assert_eq!(term.cardinality_within(&[window]), Some(101));
        assert!(term.run(&format!("x{}y\u{1}", "a".repeat(300))));
        assert_eq!(term.cardinality_within(&window_intersection(&[window], &[(0, Some(301))])), Some(0));
        let (_, window) = xsd_pattern_term("(ab){300,}").unwrap();
        assert_eq!(window, (600, None));
        // An empty range of repetitions is the empty language.
        let (a, _) = xsd_pattern_term("a{5000,4000}").unwrap();
        assert!(a.is_empty());
        // A plain group is part of the concatenation around it.
        let (a, window) = xsd_pattern_term("x(y(?:a{3000})z)").unwrap();
        assert_eq!(window, (3003, Some(3003)));
        assert!(states(&a) < 20);
        let term = a.concatenate(&empty_lang_tag());
        assert!(term.run(&format!("xy{}z\u{1}", "a".repeat(3000))));
        assert_eq!(term.cardinality_within(&[window]), Some(1));
        let (a, window) = xsd_pattern_term("(a{300})b").unwrap();
        assert_eq!(window, (301, Some(301)));
        assert!(states(&a) < 10);
        // Small repetitions, repetitions inside a quantified group or an
        // alternation, beside a piece of varying length or beside a second
        // large repetition are built as before.
        for pattern in ["a{3}", "(a{300})*b", "(a{300}b)?", "a*b{300}", "a{300}|b", "(a{300}|c)b", "a{300}b{300}"] {
            let (a, window) = xsd_pattern_term(pattern).unwrap();
            assert_eq!(window, (0, None), "{pattern}");
            let expected = xsd_pattern_to_automaton(pattern).unwrap();
            assert!(a.minus(&expected).is_empty() && expected.minus(&a).is_empty(), "{pattern}");
        }
        assert_eq!(xsd_pattern_to_automaton("ab{2}c").unwrap().fixed_length(), Some(4));
        assert_eq!(xsd_pattern_to_automaton("a|bc").unwrap().fixed_length(), None);
        assert_eq!(xsd_pattern_to_automaton("[ab]c|dd").unwrap().fixed_length(), Some(2));
    }

    #[test]
    fn large_repetitions_that_are_not_length_windows_are_a_resource_error() {
        // Each would be built one state per copy, and exhausted memory.
        for pattern in [
            "(a{2147483000})*",
            "(a{2147483000}|b)",
            "a*b{2147483000}",
            "a{2147483000}b{2147483000}",
            "(ab{70000})c*",
            "([ab]{300}){250}",
        ] {
            assert!(xsd_pattern_term(pattern).is_none(), "{pattern}");
            let message = pattern_resource_error(pattern).expect(pattern);
            assert!(message.starts_with("Resource limit"), "{message}");
        }
        for pattern in ["a{2147483000}", "x(a{2147483000})y", "a{30000}b*", "([ab]{300}){300}"] {
            assert!(pattern_resource_error(pattern).is_none(), "{pattern}");
        }
        // Built one copy after another.
        let copies = xsd_pattern_to_automaton("a{3,30000}").unwrap();
        assert!(copies.run(&"a".repeat(30000)) && copies.run("aaa"));
        assert!(!copies.run("aa") && !copies.run(&"a".repeat(30001)));
    }

    #[test]
    fn unicode_property_in_char_class() {
        // \p inside a character class, combined with literals.
        let a = xsd_pattern_to_automaton("[\\p{Nd}abc]").unwrap();
        assert!(a.run("0") && a.run("a") && a.run("b"));
        assert!(!a.run("z"));
        // Class subtraction with a category.
        let b = xsd_pattern_to_automaton("[\\p{Lu}-[A]]").unwrap();
        assert!(!b.run("A"));
        assert!(b.run("B"));
    }

    #[test]
    fn strings_have_every_xml_character() {
        // xsd:string values are sequences of XML characters (XSD 1.1 Part 2
        // §3.3.1): #xD, #x80-#x9F and the supplementary characters included.
        let strings = any_string();
        for s in ["\r", "\u{85}", "\u{10000}", "a\u{10FFFF}"] {
            assert!(strings.run(s), "{s:?}");
        }
        for s in ["\u{1}", "\u{FFFE}", "\u{FFFF}"] {
            assert!(!strings.run(s), "{s:?}");
        }
        // `.` matches every XML character but the line terminators.
        let dot = xsd_pattern_to_automaton(".").unwrap();
        assert!(dot.run("\u{85}") && dot.run("\u{10000}"));
        assert!(!dot.run("\n") && !dot.run("\r"));
    }

    #[test]
    fn pattern_escapes_have_their_xsd_meaning() {
        // XSD 1.1 Part 2 §G.4.2.5: `.` is `[^\n\r]`, over every character, so
        // a datatype with U+FFFE (anyURI) keeps it.
        let dot = xsd_pattern_to_automaton(".").unwrap();
        assert!(dot.run("\u{FFFE}") && dot.run("\u{FFFF}"));
        // `\d` is `\p{Nd}`: ARABIC-INDIC DIGIT THREE is a digit.
        let digit = xsd_pattern_to_automaton("\\d").unwrap();
        assert!(digit.run("7") && digit.run("\u{663}") && !digit.run("a"));
        assert!(!xsd_pattern_to_automaton("\\D").unwrap().run("\u{663}"));
        // `\w` excludes only punctuation, separators and "other": symbols are
        // word characters, and `_` (Pc, connector punctuation) is not.
        let word = xsd_pattern_to_automaton("\\w").unwrap();
        for c in ["a", "$", "+", "\u{263A}", "\u{10000}"] {
            assert!(word.run(c), "{c:?}");
        }
        for c in ["!", "_", " ", "-", "\u{1}", "\u{2028}"] {
            assert!(!word.run(c), "{c:?}");
        }
        assert!(xsd_pattern_to_automaton("\\W").unwrap().run("-"));
        // `^` and `$` are normal characters.
        assert!(xsd_pattern_to_automaton("^a$").unwrap().run("^a$"));
    }

    #[test]
    fn length_windows_count_characters() {
        // XSD 1.1 length facets count characters (code points; Part 2 §4.3.1),
        // so U+10000 has length 1, although HermiT (Java String.length())
        // counts it twice.
        let separator = char::from_u32(SEPARATOR).unwrap();
        let word = |s: &str| format!("{s}{separator}");
        let one = length_automaton(1, Some(1), LangMode::Absent).intersection(&any_string().concatenate(&empty_lang_tag()));
        assert!(one.run(&word("a")) && one.run(&word("\r")) && one.run(&word("\u{10000}")));
        assert!(!one.run(&word("")) && !one.run(&word("ab")) && !one.run(&word("a\u{10000}")));
        // The strings of one character: every XML character.
        assert_eq!(one.cardinality(), Some(1_112_033));
        let at_least_two = length_automaton(2, None, LangMode::Absent);
        for s in ["\u{10000}\u{10000}", "abc", "a\u{10000}"] {
            assert!(at_least_two.run(&word(s)), "{s:?}");
        }
        assert!(!at_least_two.run(&word("\u{10000}")) && !at_least_two.run(&word("")));
        // The symbolic windows agree.
        let strings = any_string().concatenate(&empty_lang_tag());
        assert_eq!(strings.cardinality_within(&[(1, Some(1))]), Some(1_112_033));
        assert_eq!(string_part_length(&word("a\u{10000}")), 2);
    }

    #[test]
    fn length_windows_near_two_to_the_31_are_symbolic() {
        let separator = char::from_u32(SEPARATOR).unwrap();
        let a_star = xsd_pattern_to_automaton("a*").unwrap().concatenate(&empty_lang_tag());
        let huge = 2_147_483_000u64;
        // Exactly one word per length, without a state per length.
        assert!(!a_star.is_empty_within(&[(huge, None)]));
        assert_eq!(a_star.cardinality_within(&[(huge, None)]), None);
        assert_eq!(a_star.cardinality_within(&[(huge, Some(huge + 9))]), Some(10));
        assert_eq!(a_star.finite_strings_within(&[(huge, Some(huge))], 10), None);
        // Periodic lengths: `(ab)*` has only even lengths.
        let ab = xsd_pattern_to_automaton("(ab)*").unwrap().concatenate(&empty_lang_tag());
        assert!(ab.is_empty_within(&[(huge + 1, Some(huge + 1))]));
        assert_eq!(ab.cardinality_within(&[(huge - 1, Some(huge + 1))]), Some(1));
        // Two letters: 2^n words of length n, saturating.
        let ab_star = xsd_pattern_to_automaton("[ab]*").unwrap().concatenate(&empty_lang_tag());
        assert_eq!(ab_star.cardinality_within(&[(huge, Some(huge))]), Some(u128::MAX));
        assert_eq!(ab_star.cardinality_within(&[(3, Some(4))]), Some(8 + 16));
        // A finite pattern is bounded by its own length.
        let finite = xsd_pattern_to_automaton("a{2,5}").unwrap().concatenate(&empty_lang_tag());
        assert_eq!(finite.cardinality_within(&[(3, None)]), Some(3));
        assert!(finite.is_empty_within(&[(6, Some(huge))]));
        let words = finite.finite_strings_within(&[(0, Some(huge))], 10).unwrap();
        assert_eq!(words.len(), 4);
        assert!(words.contains(&format!("aa{separator}")));
        // Tags after the string: infinitely many language tags.
        let tagged = xsd_pattern_to_automaton("a").unwrap().concatenate(&nonempty_lang_tag());
        assert_eq!(tagged.cardinality_within(&[(1, Some(1))]), None);
        assert_eq!(tagged.cardinality_within(&[(2, Some(huge))]), Some(0));
    }

    #[test]
    fn long_windows_over_many_states_are_counted_exactly() {
        // `(a{200})*` has 200 string states; a long window was counted as
        // `u128::MAX` ("at least") above 160 states.
        let cycle = xsd_pattern_to_automaton("(a{200})*").unwrap().concatenate(&empty_lang_tag());
        assert_eq!(cycle.cardinality_within(&[(5000, Some(5000))]), Some(1));
        assert_eq!(cycle.cardinality_within(&[(5001, Some(5199))]), Some(0));
        assert_eq!(cycle.cardinality_within(&[(5000, Some(5399))]), Some(2));
        let huge = 2_147_483_000u64; // a multiple of 200
        assert_eq!(cycle.cardinality_within(&[(huge, Some(huge + 399))]), Some(2));
        // Two choices in a long cycle: 2^25 words of length 5000.
        let choices = xsd_pattern_to_automaton("([ab]a{199})*").unwrap().concatenate(&empty_lang_tag());
        assert_eq!(choices.cardinality_within(&[(5000, Some(5000))]), Some(1 << 25));
    }

    #[test]
    fn capped_counts_over_dense_automata_are_exact() {
        let huge = 2_147_483_001u64; // odd
        // Two thousand states that remember the last ten letters: the matrix
        // powers are dense, which passed the work budget, and the count was
        // reported as "at least u128::MAX". The dense part has even lengths
        // only, so of an odd length there is one word, x^huge.
        let dense = xsd_pattern_to_automaton("(xx)*x|yy(([ab]c)*ac([ab]c){9})")
            .unwrap()
            .concatenate(&empty_lang_tag());
        assert!(LengthView::new(&dense).len() > 2000);
        assert_eq!(dense.cardinality_within_capped(&[(huge, Some(huge))], 5), Some(1));
        assert_eq!(dense.cardinality_within_capped(&[(huge - 1, Some(huge))], 5), Some(5));
        assert_eq!(dense.cardinality_within_capped(&[(huge + 1, Some(huge + 1))], 3), Some(3));
        // The cap stops the count, and a count below it is exact.
        let last = xsd_pattern_to_automaton("[ab]*a[ab]{9}").unwrap().concatenate(&empty_lang_tag());
        assert_eq!(last.cardinality_within_capped(&[(huge, Some(huge))], 1000), Some(1000));
        assert_eq!(last.cardinality_within_capped(&[(11, Some(11))], 5000), Some(1024));
        // Two long cycles in sequence: few words per length, and a count that
        // grows with the length only polynomially.
        let cycles = xsd_pattern_to_automaton("(x{500})*(y{501})*").unwrap().concatenate(&empty_lang_tag());
        let window = [(huge - 1, Some(huge + 998))];
        let exact = cycles.cardinality_within(&window).unwrap();
        assert!(exact > 1000 && exact < u128::MAX);
        assert_eq!(cycles.cardinality_within_capped(&window, exact), Some(exact));
        assert_eq!(cycles.cardinality_within_capped(&window, exact + 1), Some(exact));
        assert_eq!(cycles.cardinality_within_capped(&window, 7), Some(7));
    }

    #[test]
    fn any_uri_value_automaton_accepts_the_valid_uris() {
        use crate::datatype_value::is_valid_any_uri;
        let uris = any_uri_value_automaton();
        // Every string of up to four characters over an alphabet that reaches
        // each branch of the grammar, and some longer ones.
        let alphabet: Vec<char> = "a1:/?#@[]%F.v-+ \u{80}\u{e9}\u{3000}".chars().collect();
        let mut strings = vec![String::new()];
        let mut layer = vec![String::new()];
        for _ in 0..4 {
            layer = layer
                .iter()
                .flat_map(|prefix| alphabet.iter().map(move |ch| format!("{prefix}{ch}")))
                .collect();
            strings.extend(layer.iter().cloned());
        }
        strings.extend(
            [
                "http://example.org/a?b#c", "http://u@[::1]:80/p", "http://[::1]x/", "urn:isbn:1",
                "mailto:a@b", "a:", "a:/b", "1a:b", "//host:8x/p", "//a@b@c/", "x#y#z", "%4g",
                "%41%42", "http://h:/p", "/p;q?r[s]", "p[q]", "s://[v1.a]", "s://[]/", "é:x",
                "a/b:c", "?:x", "http://a b", "\u{fffe}", "\u{10000}", "\u{2028}",
            ]
            .map(str::to_string),
        );
        for s in &strings {
            assert_eq!(uris.run(s), is_valid_any_uri(s), "{s:?}");
        }
    }

    #[test]
    fn language_tags_are_lowercase() {
        // The value space holds tags in lowercase (rdf:PlainLiteral §3).
        let lt = language_tag_automaton();
        for tag in ["en-gb", "de-latn-de-1996", "de-1abc", "sl-rozaj-biske", "en-a-bbb-x-a-ccc"] {
            assert!(lt.run(tag), "{tag}");
        }
        for tag in ["en-GB", "EN", "de-x"] {
            assert!(!lt.run(tag), "{tag}");
        }
    }

    #[test]
    fn language_tag_automaton_matches_grammar() {
        let lt = language_tag_automaton();
        assert!(lt.run("en"));
        assert!(lt.run("en")); // 2alpha
        assert!(lt.run("eng")); // 3alpha
        assert!(lt.run("en-GB".to_ascii_lowercase().as_str()) || lt.run("en-gb"));
        assert!(!lt.run("e")); // 1alpha invalid
        assert!(!lt.run("toolongprimary")); // >8 primary
    }
}
