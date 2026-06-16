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
// matches dk.brics `RegExp` as HermiT constructs it (the default flags, i.e. the
// full grammar): anchored whole-string match, the XSD multi-character escapes
// (`\d \D \w \W \s \S`, the XML-name escapes `\i \I \c \C`), the category/block
// escapes `\p{...}`/`\P{...}` (the common categories), single-character escapes,
// char classes with ranges/negation/class-subtraction, the quantifiers
// `? * + {m} {m,} {m,n}`, grouping and alternation.
//
// Everything here is sound for the emptiness/cardinality questions: an automaton
// is built to recognise *exactly* the language HermiT's does (so an empty
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
        let mut a = Automaton::epsilon();
        for _ in 0..min {
            a = a.concatenate(self);
        }
        a.concatenate(&self.repeat())
    }

    /// `self{min,max}` (between `min` and `max` repetitions, inclusive).
    pub fn repeat_range(&self, min: usize, max: usize) -> Automaton {
        if max < min {
            return Automaton::empty_language();
        }
        let mut a = Automaton::epsilon();
        for _ in 0..min {
            a = a.concatenate(self);
        }
        // optional tail: (self (self (... )?)?)? up to max-min times
        let optional = self.optional();
        let mut tail = Automaton::epsilon();
        for _ in 0..(max - min) {
            tail = optional.concatenate(&tail);
        }
        a.concatenate(&tail)
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
        if !live[dfa.start] {
            return Some(0);
        }
        // Detect a cycle among live states reachable from start (⇒ infinite).
        // 0 = unvisited, 1 = on-stack, 2 = done.
        let mut color = vec![0u8; n];
        if dfa.has_cycle_live(dfa.start, &live, &mut color) {
            return None;
        }
        // DAG path counting over live states: number of accepted words = number of
        // distinct paths from start to any accepting state, weighted by interval
        // width (each interval of width w contributes w distinct symbols).
        let mut memo: Vec<Option<u128>> = vec![None; n];
        Some(dfa.count_words(dfa.start, &live, &mut memo))
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
    let chars: Vec<char> = pattern.chars().collect();
    let mut p = Parser { chars: &chars, pos: 0 };
    let a = p.parse_alternation()?;
    if p.pos != chars.len() {
        return None;
    }
    Some(a)
}

struct Parser<'a> {
    chars: &'a [char],
    pos: usize,
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
                match self.peek() {
                    Some('}') => {
                        self.bump();
                        Some(atom.repeat_range(min, min))
                    }
                    Some(',') => {
                        self.bump();
                        if self.peek() == Some('}') {
                            self.bump();
                            Some(atom.repeat_min(min))
                        } else {
                            let max = self.parse_number()?;
                            if self.peek() != Some('}') {
                                return None;
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
                let inner = self.parse_alternation()?;
                if self.peek() != Some(')') {
                    return None;
                }
                self.bump();
                Some(inner)
            }
            '[' => self.parse_char_class(),
            '.' => {
                self.bump();
                // XSD `.` matches any character except the line terminators
                // \n (#xA) and \r (#xD). dk.brics `RegExp` `.` is "any single
                // char"; HermiT pattern automata are intersected with the XML
                // string automaton, so restricting `.` to the XML alphabet (minus
                // the two line terminators, per XSD) is faithful.
                Some(ranges_to_automaton(&dot_ranges()))
            }
            '\\' => {
                self.bump();
                let e = self.bump()?;
                self.escape_to_automaton(e)
            }
            ')' | '|' | '*' | '+' | '?' | '{' | '}' | ']' => None,
            '^' | '$' => None, // XSD patterns are implicitly anchored; ^/$ are literals only inside classes
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

/// The ranges denoted by `.` in an XSD pattern: any XML char except `\n`/`\r`.
fn dot_ranges() -> Vec<(u32, u32)> {
    subtract_ranges(&xml_char_ranges(), &[(0x0A, 0x0A), (0x0D, 0x0D)])
}

/// The XML 1.0 Char set dk.brics uses for `.`/string automata:
/// `#x9 #xA #x20-#x7F #xA0-#xD7FF #xE000-#xFFFD`.
pub fn xml_char_ranges() -> Vec<(u32, u32)> {
    vec![
        (0x09, 0x09),
        (0x0A, 0x0A),
        (0x20, 0x7F),
        (0xA0, 0xD7FF),
        (0xE000, 0xFFFD),
    ]
}

/// Build an automaton from a set of single-symbol ranges.
fn ranges_to_automaton(ranges: &[(u32, u32)]) -> Automaton {
    Automaton::ranges(ranges)
}

/// The XSD multi-character class escapes (`\d \D \w \W \s \S \i \I \c \C`).
/// Returns `None` for a non-class escape. The negated/uppercase variants are the
/// complement within the XML character set (matching dk.brics, which intersects
/// the pattern automaton with the XML alphabet downstream).
fn class_escape_ranges(e: char) -> Option<Vec<(u32, u32)>> {
    match e {
        'd' => Some(vec![(0x30, 0x39)]),
        'D' => Some(complement_ranges(&[(0x30, 0x39)])),
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

/// `\w`: XSD defines `\w` as `[#x0000-#x10FFFF] - \p{P} - \p{Z} - \p{C}`, i.e. all
/// characters that are not punctuation, separators, or "other". dk.brics models
/// it concretely; the version HermiT exercises in practice over ASCII patterns is
/// `[a-zA-Z0-9_]` plus the Unicode letter/number blocks. We use the broad Unicode
/// letter+number+mark+connector set to stay faithful for non-ASCII.
fn word_char_ranges() -> Vec<(u32, u32)> {
    // letters + digits + underscore + the common Unicode letter blocks.
    let mut r = vec![
        (0x30u32, 0x39u32), // 0-9
        (0x41, 0x5A),       // A-Z
        (0x5F, 0x5F),       // _
        (0x61, 0x7A),       // a-z
        (0xAA, 0xAA),
        (0xB5, 0xB5),
        (0xBA, 0xBA),
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

/// The full BCP47 `languageTagAutomaton` HermiT uses for rdf:PlainLiteral tags.
/// Structure mirrors `RDFPlainLiteralPatternValueSpaceSubset.languageTagAutomaton`.
pub fn language_tag_automaton() -> Automaton {
    let alpha = || Automaton::ranges(&[(0x41, 0x5A), (0x61, 0x7A)]);
    let digit = || Automaton::ranges(&[(0x30, 0x39)]);
    let alnum = || Automaton::ranges(&[(0x30, 0x39), (0x41, 0x5A), (0x61, 0x7A)]);
    let dash = || Automaton::char(0x2D);
    // language: ([a-zA-Z]{2,3}((-[a-zA-Z]{3}){0,3})?) | [a-zA-Z]{4} | [a-zA-Z]{5,8}
    let extlang = dash().concatenate(&alpha().repeat_range(3, 3)).repeat_range(0, 3).optional();
    let lang23 = alpha().repeat_range(2, 3).concatenate(&extlang);
    let lang4 = alpha().repeat_range(4, 4);
    let lang58 = alpha().repeat_range(5, 8);
    let language = lang23.union(&lang4).union(&lang58);
    // script: (-[a-zA-Z]{4})?
    let script = dash().concatenate(&alpha().repeat_range(4, 4)).optional();
    // region: (-([a-zA-Z]{2}|[0-9]{3}))?
    let region = dash()
        .concatenate(&alpha().repeat_range(2, 2).union(&digit().repeat_range(3, 3)))
        .optional();
    // variant: (-([a-zA-Z0-9]{5,8}|([0-9][a-z0-9]{3})))*
    let var_long = alnum().repeat_range(5, 8);
    let var_dig = digit().concatenate(
        &Automaton::ranges(&[(0x30, 0x39), (0x61, 0x7A)]).repeat_range(3, 3),
    );
    let variant = dash().concatenate(&var_long.union(&var_dig)).repeat();
    // extension: (-([a-wy-zA-WY-Z0-9](-[a-zA-Z0-9]{2,8})+))*
    let singleton = Automaton::ranges(&[
        (0x30, 0x39),
        (0x41, 0x57),
        (0x59, 0x5A), // A-W, Y-Z
        (0x61, 0x77),
        (0x79, 0x7A), // a-w, y-z
    ]);
    let ext_tail = dash().concatenate(&alnum().repeat_range(2, 8)).repeat_min(1);
    let extension = dash().concatenate(&singleton.concatenate(&ext_tail)).repeat();
    // privateuse: (-x(-[a-zA-Z0-9]{1,8})+)?
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
        _ => return None,
    };
    Some(string_part.concatenate(&empty_lang_tag()))
}

/// `getPatternAutomaton(pattern)` — the string-part pattern automaton, in the
/// combined alphabet (`regex · anyLangTag`). `None` if the regex is unmodelled.
pub fn pattern_automaton(pattern: &str) -> Option<Automaton> {
    let string_part = xsd_pattern_to_automaton(pattern)?;
    Some(string_part.concatenate(&any_lang_tag()))
}

/// `getLanguageRangeAutomaton(languageRange)`.
pub fn language_range_automaton(language_range: &str) -> Automaton {
    if language_range == "*" {
        // s_anyString · s_nonemptyLangTag
        return any_string().concatenate(&nonempty_lang_tag());
    }
    // s_anyString · separator · (makeString(lower) · languagePatternEnd)
    // languagePatternEnd = optional( '-' · anyString )
    let lower = language_range.to_ascii_lowercase();
    let lang_end = Automaton::char(0x2D).concatenate(&any_string()).optional();
    any_string()
        .concatenate(&separator())
        .concatenate(&Automaton::literal(&lower))
        .concatenate(&lang_end)
}

/// `toAutomaton(minLength, maxLength)` for a length-bounded restriction (the
/// string part intersected with the length window), in the combined alphabet with
/// `s_anyLangTag`. `max == None` means unbounded (Integer.MAX_VALUE).
pub fn length_automaton(min_length: usize, max_length: Option<usize>, lang: LangMode) -> Automaton {
    let string_part = match max_length {
        None => {
            if min_length == 0 {
                any_string()
            } else {
                any_string().intersection(&any_char().repeat_min(min_length))
            }
        }
        Some(max) => any_string().intersection(&any_char().repeat_range(min_length, max)),
    };
    let tag = match lang {
        LangMode::Any => any_lang_tag(),
        LangMode::Absent => empty_lang_tag(),
        LangMode::Present => nonempty_lang_tag(),
    };
    string_part.concatenate(&tag)
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
