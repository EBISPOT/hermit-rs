//! Semantic comparison of the clause and fact strings printed by the structural
//! clausification tests (`AbstractStructuralTest.getDLClauses`).
//!
//! Two printed clause sets are equivalent when they are equal after
//! * rewriting every literal to one key per data value, when its lexical form is
//!   valid for its datatype: OWL 2 / XSD 1.1 give `"18"^^xsd:int`,
//!   `"18"^^xsd:integer` and `"18.0"^^xsd:decimal` the same value, and a plain
//!   literal without a language tag abbreviates `xsd:string`;
//! * reading `{ ... }` enumerations and clause heads and bodies as sets;
//! * renaming the variables of each clause by a bijection of its own: a clause
//!   is universally closed, so a bijective renaming of its variables yields the
//!   same formula (alpha-equivalence). Merging two variables, or renaming a
//!   variable to a constant, is not a renaming;
//! * one bijection of fresh auxiliary predicates (`def:`, `defdata:`, `nnq:`,
//!   `all:`), each mapped only within its own family and applied consistently
//!   across the whole clause and fact set; and
//! * replacing the `all:` states of a transitive-role automaton by the
//!   languages they accept (see [`Automaton`]), when both sides encode their
//!   automata in the form that makes this exact.
//!
//! Nothing else is identified: ordinary and nominal names, negation, argument
//! order, numbers, distinct value spaces (such as `xsd:double` and
//! `xsd:decimal`) and ill-typed literals must match exactly.
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// The fresh predicate families that clausification numbers arbitrarily.
const AUXILIARY: [&str; 4] = ["def", "defdata", "nnq", "all"];
/// Bijections tried before giving up; far above any structural control.
const MAX_BIJECTIONS: usize = 40_320;
/// Clauses with more variables are compared with their variables as printed.
const MAX_RENAMED_VARIABLES: usize = 7;

pub fn equivalent<'a>(
    actual: impl IntoIterator<Item = &'a String>,
    expected: impl IntoIterator<Item = &'a String>,
) -> bool {
    let actual: Vec<Vec<String>> = actual.into_iter().map(|s| tokens(s)).collect();
    let expected: Vec<Vec<String>> = expected.into_iter().map(|s| tokens(s)).collect();
    // Automaton states are compared by language, the other auxiliaries by name.
    let (actual_automaton, expected_automaton) =
        match (Automaton::split(&actual), Automaton::split(&expected)) {
            (Some(a), Some(e)) => (Some(a), Some(e)),
            _ => (None, None),
        };
    let by_language = actual_automaton.is_some();
    let (mut actual_names, mut expected_names) = (auxiliaries(&actual), auxiliaries(&expected));
    if by_language {
        actual_names.remove("all");
        expected_names.remove("all");
    }
    if actual_names.len() != expected_names.len()
        || actual_names
            .iter()
            .any(|(kind, names)| expected_names.get(kind).map(Vec::len) != Some(names.len()))
    {
        return false;
    }
    let target = canonical_all(&actual, actual_automaton.as_ref(), &HashMap::new());
    let families: Vec<(Vec<String>, Vec<String>)> = expected_names
        .into_iter()
        .map(|(kind, names)| (names, actual_names[&kind].clone()))
        .collect();
    let mut budget = MAX_BIJECTIONS;
    search(
        &families,
        &mut HashMap::new(),
        &mut |rename| canonical_all(&expected, expected_automaton.as_ref(), rename) == target,
        &mut budget,
    )
}

/// Try every bijection family by family; `check` sees each complete renaming.
fn search(
    families: &[(Vec<String>, Vec<String>)],
    rename: &mut HashMap<String, String>,
    check: &mut dyn FnMut(&HashMap<String, String>) -> bool,
    budget: &mut usize,
) -> bool {
    let Some(((from, to), rest)) = families.split_first() else {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        return check(rename);
    };
    let mut used = vec![false; to.len()];
    permute(from, to, 0, &mut used, rename, &mut |rename| {
        search(rest, rename, check, budget)
    })
}

fn permute(
    from: &[String],
    to: &[String],
    at: usize,
    used: &mut [bool],
    rename: &mut HashMap<String, String>,
    next: &mut dyn FnMut(&mut HashMap<String, String>) -> bool,
) -> bool {
    if at == from.len() {
        return next(rename);
    }
    for i in 0..to.len() {
        if !used[i] {
            used[i] = true;
            rename.insert(from[at].clone(), to[i].clone());
            if permute(from, to, at + 1, used, rename, next) {
                return true;
            }
            used[i] = false;
        }
    }
    rename.remove(&from[at]);
    false
}

fn tokens(text: &str) -> Vec<String> {
    static TOKENIZER: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
    let re = TOKENIZER.get_or_init(|| {
        regex::Regex::new(
            r#""(?:\\.|[^"\\])*"(?:\^\^(?:<[^>]*>|[^\s(){}\[\],"<]+)|@[A-Za-z0-9-]+)?|<[^>]*>|[(){}\[\],]|[^\s(){}\[\],"<]+"#,
        )
        .unwrap()
    });
    re.find_iter(text)
        .map(|m| {
            let token = m.as_str();
            if token.starts_with('"') {
                literal(token)
            } else {
                name(token)
            }
        })
        .collect()
}

/// `<internal:def#0>` is the undeclared-prefix spelling of `def:0`.
fn name(token: &str) -> String {
    if let Some(inner) = token
        .strip_prefix("<internal:")
        .and_then(|t| t.strip_suffix('>'))
    {
        if let Some((kind, local)) = inner.split_once('#') {
            if AUXILIARY.contains(&kind) {
                return format!("{kind}:{local}");
            }
        }
    }
    token.to_string()
}

fn auxiliary_kind(token: &str) -> Option<&str> {
    let (kind, _) = token.split_once(':')?;
    AUXILIARY.contains(&kind).then_some(kind)
}

fn is_state(token: &str) -> bool {
    auxiliary_kind(token) == Some("all")
}

/// Clause variables as HermiT names them (`X`, `Y1`, `Z2`, ...). Every other
/// name is prefixed or bracketed, so a bare name of this shape is a variable.
fn is_variable(token: &str) -> bool {
    let mut chars = token.chars();
    matches!(chars.next(), Some('X' | 'Y' | 'Z')) && chars.all(|c| c.is_ascii_digit())
}

fn auxiliaries(items: &[Vec<String>]) -> BTreeMap<String, Vec<String>> {
    let mut names = BTreeMap::<String, BTreeSet<String>>::new();
    for token in items.iter().flatten() {
        if let Some(kind) = auxiliary_kind(token) {
            names
                .entry(kind.to_string())
                .or_default()
                .insert(token.clone());
        }
    }
    names
        .into_iter()
        .map(|(kind, names)| (kind, names.into_iter().collect()))
        .collect()
}

fn canonical_all(
    items: &[Vec<String>],
    automaton: Option<&Automaton>,
    rename: &HashMap<String, String>,
) -> BTreeSet<String> {
    let Some(automaton) = automaton else {
        return items
            .iter()
            .map(|item| canonical(&flatten(item, rename)))
            .collect();
    };
    let mut rename = rename.clone();
    rename.extend(automaton.languages(rename.clone()));
    automaton
        .rest
        .iter()
        .map(|&at| canonical(&flatten(&items[at], &rename)))
        .collect()
}

/// Apply `rename` and read each `{ ... }` enumeration as one sorted token.
fn flatten(item: &[String], rename: &HashMap<String, String>) -> Vec<String> {
    let mut flat = Vec::new();
    let mut at = 0;
    while at < item.len() {
        if item[at] == "{" {
            let mut values = BTreeSet::new();
            at += 1;
            while at < item.len() && item[at] != "}" {
                values.insert(item[at].clone());
                at += 1;
            }
            at += 1;
            flat.push(format!(
                "{{ {} }}",
                values.into_iter().collect::<Vec<_>>().join(" ")
            ));
        } else {
            flat.push(rename.get(&item[at]).unwrap_or(&item[at]).clone());
            at += 1;
        }
    }
    flat
}

/// The rendering of a flattened item that is least over all bijective
/// renamings of its variables, so alpha-equivalent clauses render alike.
fn canonical(flat: &[String]) -> String {
    let mut variables: Vec<&String> = Vec::new();
    for token in flat {
        if is_variable(token) && !variables.contains(&token) {
            variables.push(token);
        }
    }
    if variables.len() > MAX_RENAMED_VARIABLES {
        return render(flat);
    }
    let fresh: Vec<String> = (0..variables.len()).map(|i| format!("?{i}")).collect();
    let mut best: Option<String> = None;
    let mut used = vec![false; fresh.len()];
    let variables: Vec<String> = variables.into_iter().cloned().collect();
    permute(
        &variables,
        &fresh,
        0,
        &mut used,
        &mut HashMap::new(),
        &mut |map| {
            let renamed: Vec<String> = flat
                .iter()
                .map(|t| map.get(t).unwrap_or(t).clone())
                .collect();
            let text = render(&renamed);
            if best.as_ref().is_none_or(|b| text < *b) {
                best = Some(text);
            }
            false
        },
    );
    best.unwrap_or_else(|| render(flat))
}

/// The top-level atoms of a head (separated by `v`) or body (by `,`).
fn atoms(tokens: &[String], separator: &str) -> Vec<Vec<String>> {
    let mut atoms = Vec::new();
    let (mut depth, mut current) = (0usize, Vec::new());
    for token in tokens {
        match token.as_str() {
            "(" => depth += 1,
            ")" => depth -= 1,
            t if t == separator && depth == 0 => {
                atoms.push(std::mem::take(&mut current));
                continue;
            }
            _ => {}
        }
        current.push(token.clone());
    }
    if !current.is_empty() {
        atoms.push(current);
    }
    atoms
}

/// The atoms of a head or body, each as its tokens.
type Atoms = Vec<Vec<String>>;

/// A clause's head and body atoms; `None` for a fact.
fn clause(flat: &[String]) -> Option<(Atoms, Atoms)> {
    let arrow = flat.iter().position(|t| t == ":-")?;
    Some((atoms(&flat[..arrow], "v"), atoms(&flat[arrow + 1..], ",")))
}

fn join(atoms: &[Vec<String>], separator: &str) -> String {
    atoms
        .iter()
        .map(|atom| atom.join(" "))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>()
        .join(separator)
}

/// Render one flattened clause or fact with sorted heads and bodies.
fn render(flat: &[String]) -> String {
    match clause(flat) {
        None => flat.join(" "),
        Some((head, body)) => format!("{} :- {}", join(&head, " v "), join(&body, " , ")),
    }
}

/// `p ( t )` for a unary atom.
fn unary(atom: &[String]) -> Option<(&str, &str)> {
    match atom {
        [p, open, t, close] if open == "(" && close == ")" => Some((p, t)),
        _ => None,
    }
}

/// `r ( s , t )` for a binary atom.
fn binary(atom: &[String]) -> Option<(&str, &str, &str)> {
    match atom {
        [r, open, s, comma, t, close] if open == "(" && comma == "," && close == ")" => {
            Some((r, s, t))
        }
        _ => None,
    }
}

/// One step of a transitive-role automaton clause with head `p(X)`.
enum Step {
    /// `p(X) :- q(X)`
    Empty(String),
    /// `p(X) :- r(X,Y), q(Y)`, or `r(Y,X)` for the inverse role
    Role(String, String),
    /// `p(X) :- C(X), ...` with no state and no variable besides `X`
    Accept(String),
}

/// The `all:` states of the automata that encode `forall` restrictions over
/// non-simple (for example transitive) roles. HermiT spells them as clauses
/// that only ever derive a state, in one of three forms:
/// `p(X) :- q(X)`, `p(X) :- r(X,Y), q(Y)` (or `r(Y,X)`), and
/// `p(X) :- C1(X), ..., Cn(X)` with no state in the body.
///
/// When no other clause and no fact derives a state, and every other clause
/// uses a state only as a unary body atom, those clauses are a monotone
/// definition of the states: in the least extension of any interpretation of
/// the other predicates, `p` holds exactly where some path `r1 ... rk` leads to
/// a point satisfying a final body `C`, for a word `r1 ... rk C` accepted from
/// `p`. As the states occur only positively in the bodies of the other clauses,
/// a model extends to one of the whole set iff that least extension does. Two
/// clause sets therefore have the same models over the non-state predicates
/// when their other clauses coincide after each state is replaced by the
/// language it accepts. The language is spelled as its minimal DFA, which is
/// unique, so equal spellings mean equal languages and hence the same meaning,
/// however many states or clauses either encoding uses.
struct Automaton {
    /// The indices of the items that are not automaton clauses.
    rest: Vec<usize>,
    /// The automaton clauses, before renaming.
    steps: Vec<Vec<String>>,
}

impl Automaton {
    fn split(items: &[Vec<String>]) -> Option<Automaton> {
        let mut automaton = Automaton {
            rest: Vec::new(),
            steps: Vec::new(),
        };
        for (at, item) in items.iter().enumerate() {
            if !item.iter().any(|t| is_state(t)) {
                automaton.rest.push(at);
                continue;
            }
            let (head, body) = clause(&flatten(item, &HashMap::new()))?;
            if Self::step(&head, &body).is_some() {
                automaton.steps.push(item.clone());
            } else if head.iter().flatten().any(|t| is_state(t))
                || body.iter().any(|atom| {
                    atom.iter().any(|t| is_state(t))
                        && !unary(atom).is_some_and(|(p, _)| is_state(p))
                })
            {
                return None;
            } else {
                automaton.rest.push(at);
            }
        }
        (!automaton.steps.is_empty()).then_some(automaton)
    }

    fn step(head: &[Vec<String>], body: &[Vec<String>]) -> Option<(String, Step)> {
        let [head] = head else { return None };
        let (p, x) = unary(head)?;
        if !is_state(p) || !is_variable(x) {
            return None;
        }
        let step = match body {
            [atom] if unary(atom).is_some_and(|(q, t)| is_state(q) && t == x) => {
                Step::Empty(unary(atom)?.0.to_string())
            }
            [a, b]
                if [a, b]
                    .iter()
                    .any(|atom| unary(atom).is_some_and(|(q, _)| is_state(q))) =>
            {
                let (state, role) = if unary(a).is_some_and(|(q, _)| is_state(q)) {
                    (a, b)
                } else {
                    (b, a)
                };
                let (q, y) = unary(state)?;
                let (r, s, t) = binary(role)?;
                if is_state(r) || !is_variable(y) || y == x {
                    return None;
                }
                let label = match (s == x, t == y, s == y, t == x) {
                    (true, true, _, _) => r.to_string(),
                    (_, _, true, true) => format!("{r}^-"),
                    _ => return None,
                };
                Step::Role(label, q.to_string())
            }
            _ if !body.is_empty()
                && body
                    .iter()
                    .flatten()
                    .all(|t| !is_state(t) && (!is_variable(t) || t == x)) =>
            {
                Step::Accept(join(body, " , "))
            }
            _ => return None,
        };
        Some((p.to_string(), step))
    }

    /// The minimal-DFA spelling of each state's language after `rename`.
    fn languages(&self, rename: HashMap<String, String>) -> HashMap<String, String> {
        const ACCEPT: &str = "";
        let mut edges: BTreeMap<String, Vec<(Option<String>, String)>> = BTreeMap::new();
        for item in &self.steps {
            let (head, body) = clause(&flatten(item, &rename)).unwrap();
            let (p, step) = Self::step(&head, &body).unwrap();
            let edge = match step {
                Step::Empty(q) => (None, q),
                Step::Role(r, q) => (Some(format!("role {r}")), q),
                Step::Accept(c) => (Some(format!("accept {c}")), ACCEPT.to_string()),
            };
            edges.entry(edge.1.clone()).or_default();
            edges.entry(p).or_default().push(edge);
        }
        let closure = |states: BTreeSet<String>| {
            let mut closed = states.clone();
            let mut todo: Vec<String> = states.into_iter().collect();
            while let Some(p) = todo.pop() {
                for (label, q) in &edges[&p] {
                    if label.is_none() && closed.insert(q.clone()) {
                        todo.push(q.clone());
                    }
                }
            }
            closed
        };
        let alphabet: BTreeSet<&String> = edges
            .values()
            .flatten()
            .filter_map(|e| e.0.as_ref())
            .collect();
        let mut languages = HashMap::new();
        for start in edges.keys().filter(|p| p.as_str() != ACCEPT) {
            // Subset construction over the whole alphabet, the empty set included.
            let first = closure(BTreeSet::from([start.clone()]));
            let mut index = BTreeMap::from([(first.clone(), 0usize)]);
            let mut subsets = vec![first];
            let mut delta: Vec<Vec<usize>> = Vec::new();
            while delta.len() < subsets.len() {
                let from = subsets[delta.len()].clone();
                let mut row = Vec::new();
                for &symbol in &alphabet {
                    let next: BTreeSet<String> = from
                        .iter()
                        .flat_map(|p| &edges[p])
                        .filter(|(label, _)| label.as_ref() == Some(symbol))
                        .map(|(_, q)| q.clone())
                        .collect();
                    let next = closure(next);
                    let id = *index.entry(next.clone()).or_insert_with(|| {
                        subsets.push(next);
                        subsets.len() - 1
                    });
                    row.push(id);
                }
                delta.push(row);
            }
            let accepting: Vec<bool> = subsets.iter().map(|s| s.contains(ACCEPT)).collect();
            // Moore refinement to the minimal DFA.
            let mut class: Vec<usize> = accepting.iter().map(|&a| a as usize).collect();
            loop {
                let mut ids = BTreeMap::new();
                let refined: Vec<usize> = (0..subsets.len())
                    .map(|s| {
                        let signature = (
                            class[s],
                            delta[s].iter().map(|&t| class[t]).collect::<Vec<_>>(),
                        );
                        let next = ids.len();
                        *ids.entry(signature).or_insert(next)
                    })
                    .collect();
                let stable = ids.len() == class.iter().collect::<BTreeSet<_>>().len();
                class = refined;
                if stable {
                    break;
                }
            }
            // Live classes can still reach acceptance; transitions to the
            // (unique) dead class are left out, so unused symbols do not count.
            let classes = class.iter().max().map_or(0, |m| m + 1);
            let mut live = vec![false; classes];
            for s in 0..subsets.len() {
                live[class[s]] |= accepting[s];
            }
            loop {
                let mut changed = false;
                for s in 0..subsets.len() {
                    if !live[class[s]] && delta[s].iter().any(|&t| live[class[t]]) {
                        live[class[s]] = true;
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            // Number the live classes breadth-first in alphabet order.
            let representative: BTreeMap<usize, usize> =
                (0..subsets.len()).rev().map(|s| (class[s], s)).collect();
            let mut spelling = Vec::new();
            if live[class[0]] {
                let mut number = BTreeMap::from([(class[0], 0usize)]);
                let mut order = vec![class[0]];
                let mut at = 0;
                while at < order.len() {
                    let s = representative[&order[at]];
                    let mut row = vec![if accepting[s] { "final" } else { "state" }.to_string()];
                    for (symbol, &t) in alphabet.iter().zip(&delta[s]) {
                        if live[class[t]] {
                            let next = number.len();
                            let n = *number.entry(class[t]).or_insert_with(|| {
                                order.push(class[t]);
                                next
                            });
                            row.push(format!("{symbol} -> {n}"));
                        }
                    }
                    spelling.push(row.join("; "));
                    at += 1;
                }
            }
            languages.insert(start.clone(), format!("all:[{}]", spelling.join(" | ")));
        }
        languages
    }
}

/// One key per data value for the datatypes whose values the controls spell
/// differently; any other or ill-typed literal keeps its printed form.
fn literal(token: &str) -> String {
    let end = token.rfind('"').unwrap();
    let (lexical, suffix) = (&token[1..end], &token[end + 1..]);
    if suffix.is_empty() {
        return format!("\"{lexical}\"^^xsd:string");
    }
    if let Some(tag) = suffix.strip_prefix('@') {
        return format!("\"{lexical}\"@{}", tag.to_ascii_lowercase());
    }
    let datatype = suffix.strip_prefix("^^").unwrap();
    let local = datatype.strip_prefix("xsd:").or_else(|| {
        datatype
            .strip_prefix("<http://www.w3.org/2001/XMLSchema#")
            .and_then(|d| d.strip_suffix('>'))
    });
    let Some(local) = local else {
        return token.to_string();
    };
    let value = match local {
        "string" => Some(format!("\"{lexical}\"^^xsd:string")),
        "boolean" => match lexical {
            "true" | "1" => Some("\"true\"^^xsd:boolean".into()),
            "false" | "0" => Some("\"false\"^^xsd:boolean".into()),
            _ => None,
        },
        "double" => floating(lexical)
            .and_then(|l| l.parse::<f64>().ok())
            .map(|v| format!("\"{v:?}\"^^xsd:double")),
        "float" => floating(lexical)
            .and_then(|l| l.parse::<f32>().ok())
            .map(|v| format!("\"{v:?}\"^^xsd:float")),
        _ => decimal(local, lexical).map(|v| format!("\"{v}\"^^xsd:decimal")),
    };
    value.unwrap_or_else(|| format!("\"{lexical}\"^^xsd:{local}"))
}

/// A valid `xsd:double` or `xsd:float` lexical form, spelled for `str::parse`.
/// Debug formatting maps every NaN to one data value and keeps -0 apart from +0.
fn floating(lexical: &str) -> Option<String> {
    static LEXICAL: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
    let re = LEXICAL.get_or_init(|| {
        regex::Regex::new(
            r"^(?:[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?|[+-]?INF|NaN)$",
        )
        .unwrap()
    });
    if !re.is_match(lexical) {
        return None;
    }
    Some(lexical.replace("INF", "inf"))
}

/// The canonical decimal of a valid literal of `xsd:decimal` or one of its
/// integer subtypes, checking the subtype's range.
fn decimal(datatype: &str, lexical: &str) -> Option<String> {
    let bounds: (Option<i128>, Option<i128>) = match datatype {
        "decimal" | "integer" => (None, None),
        "nonNegativeInteger" => (Some(0), None),
        "positiveInteger" => (Some(1), None),
        "nonPositiveInteger" => (None, Some(0)),
        "negativeInteger" => (None, Some(-1)),
        "long" => (Some(i64::MIN.into()), Some(i64::MAX.into())),
        "int" => (Some(i32::MIN.into()), Some(i32::MAX.into())),
        "short" => (Some(i16::MIN.into()), Some(i16::MAX.into())),
        "byte" => (Some(i8::MIN.into()), Some(i8::MAX.into())),
        "unsignedLong" => (Some(0), Some(u64::MAX.into())),
        "unsignedInt" => (Some(0), Some(u32::MAX.into())),
        "unsignedShort" => (Some(0), Some(u16::MAX.into())),
        "unsignedByte" => (Some(0), Some(u8::MAX.into())),
        _ => return None,
    };
    let (negative, digits) = match lexical.as_bytes().first()? {
        b'-' => (true, &lexical[1..]),
        b'+' => (false, &lexical[1..]),
        _ => (false, lexical),
    };
    let (whole, fraction) = digits.split_once('.').unwrap_or((digits, ""));
    if (whole.is_empty() && fraction.is_empty())
        || !whole
            .bytes()
            .chain(fraction.bytes())
            .all(|b| b.is_ascii_digit())
        || (datatype != "decimal" && digits.contains('.'))
    {
        return None;
    }
    let whole = whole.trim_start_matches('0');
    let fraction = fraction.trim_end_matches('0');
    let magnitude = match (whole.is_empty(), fraction.is_empty()) {
        (true, true) => return check_range("0", false, bounds),
        (_, true) => whole.to_string(),
        (true, false) => format!("0.{fraction}"),
        (false, false) => format!("{whole}.{fraction}"),
    };
    if !fraction.is_empty() {
        return Some(format!("{}{magnitude}", if negative { "-" } else { "" }));
    }
    check_range(&magnitude, negative, bounds)
}

fn check_range(
    magnitude: &str,
    negative: bool,
    (lower, upper): (Option<i128>, Option<i128>),
) -> Option<String> {
    let text = format!(
        "{}{magnitude}",
        if negative && magnitude != "0" {
            "-"
        } else {
            ""
        }
    );
    if lower.is_some() || upper.is_some() {
        // Every bounded integer type fits in 20 digits; longer values violate it.
        let value: i128 = if magnitude.len() > 30 {
            if negative {
                i128::MIN
            } else {
                i128::MAX
            }
        } else {
            text.parse().ok()?
        };
        if lower.is_some_and(|l| value < l) || upper.is_some_and(|u| value > u) {
            return None;
        }
    }
    Some(text)
}

#[cfg(test)]
mod tests {
    use super::equivalent;

    // `java_parity` has no libtest harness, so it compiles but never runs these.
    #[allow(dead_code)]
    fn same(actual: &[&str], expected: &[&str]) -> bool {
        let actual: Vec<String> = actual.iter().map(|s| s.to_string()).collect();
        let expected: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        equivalent(&actual, &expected)
    }

    #[test]
    fn identifies_literals_denoting_the_same_value() {
        // testDataComplementOf3 as Rust (and current Java) print it, against the control.
        assert!(same(
            &[
                "defdata:0(Y) :- :dp(X,Y)",
                "not({ \"4.3\"^^xsd:double \"5\"^^xsd:nonNegativeInteger })(X) v not({ \"5\"^^xsd:integer })(X) :- defdata:0(X)",
            ],
            &[
                "not({ \"4.3\"^^xsd:double \"5\"^^xsd:int })(X) v not({ \"5\"^^xsd:int })(X) :- defdata:0(X)",
                "defdata:0(Y) :- :dp(X,Y)",
            ],
        ));
        assert!(same(
            &["{ \"Peter\"^^xsd:string \"19\"^^xsd:integer }(Y) :- :A(X), :dp(X,Y)"],
            &["{ \"Peter\" \"19\"^^xsd:int }(Y) :- :A(X), :dp(X,Y)"],
        ));
        assert!(same(
            &["{ \"+018.50\"^^xsd:decimal \"1\"^^<http://www.w3.org/2001/XMLSchema#boolean> \"4.30\"^^xsd:double }(X) :- :A(X)"],
            &["{ \"true\"^^xsd:boolean \"4.3E0\"^^xsd:double \"18.5\"^^xsd:decimal }(X) :- :A(X)"],
        ));
        assert!(same(
            &[":A(\"-0\"^^xsd:int)"],
            &[":A(\"0\"^^xsd:nonNegativeInteger)"]
        ));
    }

    #[test]
    fn rejects_literals_denoting_different_values() {
        let clause = |values: &str| format!("{{ {values} }}(Y) :- :A(X), :dp(X,Y)");
        let differ = |a: &str, b: &str| !same(&[&clause(a)], &[&clause(b)]);
        assert!(differ(
            "\"18\"^^xsd:integer \"19\"^^xsd:integer",
            "\"18\"^^xsd:int \"20\"^^xsd:int"
        ));
        assert!(differ(
            "\"18\"^^xsd:integer \"19\"^^xsd:integer",
            "\"18\"^^xsd:int"
        ));
        assert!(differ("\"5\"^^xsd:integer", "\"5\"^^xsd:double"));
        assert!(differ("\"5\"^^xsd:float", "\"5\"^^xsd:double"));
        assert!(differ("\"5\"^^xsd:integer", "\"5\"^^xsd:string"));
        assert!(differ("\"5\"^^xsd:integer", "\"5.1\"^^xsd:decimal"));
        assert!(differ("\"Peter\"", "\"Peter\"@en"));
        assert!(differ("\"Peter\"", "\"peter\"^^xsd:string"));
        // Ill-typed literals are never identified with a valid one.
        assert!(differ(
            "\"-5\"^^xsd:nonNegativeInteger",
            "\"-5\"^^xsd:integer"
        ));
        assert!(differ(
            "\"3000000000\"^^xsd:int",
            "\"3000000000\"^^xsd:integer"
        ));
        assert!(differ("\"5.0\"^^xsd:integer", "\"5\"^^xsd:integer"));
        assert!(differ("\"2\"^^xsd:boolean", "\"true\"^^xsd:boolean"));
    }

    #[test]
    fn renames_auxiliaries_with_one_bijection() {
        // testExistsSelf1 (#46): the two definitions are numbered the other way.
        let actual = [
            ":r(X,X) :- def:1(X)",
            "def:0(X) :- :r(X,Y)",
            "def:1(:a)",
            "not def:0(:a)",
        ];
        assert!(same(
            &actual,
            &[
                ":r(X,X) :- def:0(X)",
                "def:0(:a)",
                "def:1(X) :- :r(X,Y)",
                "not def:1(:a)"
            ],
        ));
        // The renaming must be consistent across clauses and facts.
        assert!(!same(
            &actual,
            &[
                ":r(X,X) :- def:0(X)",
                "def:1(:a)",
                "def:1(X) :- :r(X,Y)",
                "not def:0(:a)"
            ],
        ));
        assert!(!same(
            &actual,
            &[
                ":r(X,X) :- def:0(X)",
                "def:0(:a)",
                "def:0(X) :- :r(X,Y)",
                "not def:1(:a)"
            ],
        ));
        // Undeclared internal prefixes denote the same auxiliaries.
        assert!(same(
            &["<internal:defdata#0>(Y) :- :dp(X,Y)"],
            &["defdata:3(Y) :- :dp(X,Y)"]
        ));
    }

    #[test]
    fn keeps_everything_else_exact() {
        let differ = |a: &[&str], b: &[&str]| !same(a, b);
        // Families, ordinary names and nominals are never renamed.
        assert!(differ(
            &["def:0(Y) :- :dp(X,Y)"],
            &["defdata:0(Y) :- :dp(X,Y)"]
        ));
        assert!(differ(&[":A(X) :- :B(X)"], &[":C(X) :- :B(X)"]));
        assert!(differ(&["nom:i1(:i1)"], &["nom:i2(:i1)"]));
        // Direction, variables, negation, number restrictions and clause counts.
        assert!(differ(&[":A(X) :- :B(X)"], &[":B(X) :- :A(X)"]));
        assert!(differ(&[":A(X) :- :r(X,Y)"], &[":A(X) :- :r(Y,X)"]));
        assert!(differ(
            &["{ \"5\"^^xsd:int }(X) :- def:0(X)"],
            &["not({ \"5\"^^xsd:int })(X) :- def:0(X)"]
        ));
        assert!(differ(
            &["atLeast(1 :dp def:0)(X) :- :A(X)"],
            &["atLeast(2 :dp def:0)(X) :- :A(X)"]
        ));
        assert!(differ(
            &[":A(X) v :B(X) :- :C(X)"],
            &[":A(X) :- :C(X)", ":B(X) :- :C(X)"]
        ));
        assert!(differ(&["def:0(:a)"], &["def:0(:a)", "not def:1(:a)"]));
        assert!(differ(&["def:0(:a)"], &["not def:0(:a)"]));
        // Heads and bodies are sets; their order does not matter.
        assert!(same(
            &[":A(X) v :B(X) :- :C(X), :D(X)"],
            &[":B(X) v :A(X) :- :D(X), :C(X)"]
        ));
    }

    #[test]
    fn renames_variables_within_each_clause() {
        // testNominals1 and testNominals2 (#47, #48): current HermiT names the
        // nominal variables Z, Z1 where the controls have Y, Y1.
        assert!(same(
            &[
                ":r(X,Z) v :r(X,Z1) :- :c(X), nom:i1(Z), nom:i2(Z1)",
                "Y == Z v Y == Z1 :- :f(X), :r(X,Y), nom:i1(Z), nom:i2(Z1)",
                "nom:i1(:i1)",
            ],
            &[
                ":r(X,Y) v :r(X,Y1) :- :c(X), nom:i1(Y), nom:i2(Y1)",
                "Y == Y1 v Y == Y2 :- :f(X), :r(X,Y), nom:i1(Y1), nom:i2(Y2)",
                "nom:i1(:i1)",
            ],
        ));
        // Each clause has a renaming of its own.
        assert!(same(
            &[":A(X) :- :r(X,Y)", ":B(Z) :- :s(Z,Y1)"],
            &[":A(Y) :- :r(Y,X)", ":B(X) :- :s(X,Y)"],
        ));
        // Annotated equalities and ordering atoms are renamed with the rest.
        assert!(same(
            &[":e(X) v [Y1 == Y2]@atMost(2 :r :d)(X) :- :r(X,Y1), :r(X,Y2), Y1 <= Y2, NodeIDsAscendingOrEqual(Y1,Y2)"],
            &[":e(Z) v [Y == Y1]@atMost(2 :r :d)(Z) :- :r(Z,Y), :r(Z,Y1), Y <= Y1, NodeIDsAscendingOrEqual(Y,Y1)"],
        ));
        // Alpha-equivalent copies are one clause.
        assert!(same(
            &[":A(X) :- :B(X)", ":A(Y) :- :B(Y)"],
            &[":A(X) :- :B(X)"]
        ));
    }

    #[test]
    fn rejects_what_is_not_a_renaming_of_each_clause() {
        let differ = |a: &[&str], b: &[&str]| !same(a, b);
        // Swapping the arguments of an asymmetric role (testNominals1 against
        // testNominals3).
        assert!(differ(
            &[":r(X,Z) v :r(X,Z1) :- :c(X), nom:i1(Z), nom:i2(Z1)"],
            &[":r(Y,X) v :r(Y1,X) :- :c(X), nom:i1(Y), nom:i2(Y1)"],
        ));
        assert!(differ(
            &[":A(X) :- :r(X,Y), :B(Y)"],
            &[":A(Y) :- :r(X,Y), :B(Y)"]
        ));
        // A swap of two variables that changes which atom constrains which.
        assert!(differ(
            &[":r(X,Y) v :s(X,Y1) :- :c(X), nom:i1(Y), nom:i2(Y1)"],
            &[":r(X,Y) v :s(X,Y1) :- :c(X), nom:i1(Y1), nom:i2(Y)"],
        ));
        assert!(differ(
            &["Y1 <= Y2 :- :r(X,Y1), :s(X,Y2)"],
            &["Y2 <= Y1 :- :r(X,Y1), :s(X,Y2)"],
        ));
        // Merging variables is not a renaming, nor is replacing one by a name.
        assert!(differ(&[":A(X) :- :r(X,Y)"], &[":A(X) :- :r(X,X)"]));
        assert!(differ(
            &["Y == Z :- :f(X), :r(X,Y), :s(X,Z)"],
            &["Y == Y :- :f(X), :r(X,Y), :s(X,Y)"],
        ));
        assert!(differ(&[":A(X) :- :r(X,Y)"], &[":A(X) :- :r(X,:a)"]));
        assert!(differ(&[":A(:a)"], &[":A(:b)"]));
        // Atoms do not move between clauses.
        assert!(differ(
            &[":A(X) :- :r(X,Y), :B(Y)", ":C(X) :- :D(X)"],
            &[":A(X) :- :r(X,Y), :B(X)", ":C(Y) :- :D(Y)"],
        ));
        assert!(differ(
            &[":A(X) :- :B(X)", ":C(Y) :- :D(Y)"],
            &[":A(X) :- :D(X)", ":C(Y) :- :B(Y)"],
        ));
        assert!(differ(
            &[":A(X) :- :B(X)"],
            &[":A(X) :- :B(X)", ":C(Y) :- :B(Y)"]
        ));
    }

    /// testBasic (#45): `exists r.(exists s.c) <= d` with transitive `s`, as
    /// current HermiT (and Rust) encodes it.
    #[allow(dead_code)]
    const TRANSITIVE: [&str; 9] = [
        ":d(X) :- :r(X,Y), def:0(Y)",
        "def:0(X) :- all:0(X)",
        "all:0(X) :- all:2(X)",
        "all:2(X) :- :s(X,Y), all:3(Y)",
        "all:0(X) :- :s(X,Y), all:1(Y)",
        "all:3(X) :- all:1(X)",
        "all:1(X) :- all:0(X)",
        "all:3(X) :- all:2(X)",
        "all:1(X) :- :c(X)",
    ];

    #[test]
    fn compares_role_automata_by_language() {
        // The control's two-state automaton accepts the same words s s* c.
        let control = [
            ":d(X) :- :r(X,Y), def:0(Y)",
            "def:0(X) :- all:0_1(X)",
            "all:0_1(X) :- :s(X,Y), all:0_0(Y)",
            "all:0_0(X) :- :s(X,Y), all:0_0(Y)",
            "all:0_0(X) :- :c(X)",
        ];
        assert!(same(&TRANSITIVE, &control));
        let differ = |edit: &dyn Fn(&mut Vec<&'static str>)| {
            let mut changed = control.to_vec();
            edit(&mut changed);
            !same(&TRANSITIVE, &changed)
        };
        // Without the loop only s c is accepted: exists s.(exists s.c) is lost.
        assert!(differ(
            &|c| c.retain(|l| *l != "all:0_0(X) :- :s(X,Y), all:0_0(Y)")
        ));
        // s* c would also accept c itself: exists r.c <= d does not follow.
        assert!(differ(&|c| c[1] = "def:0(X) :- all:0_0(X)"));
        // Another role, the inverse role, or another final concept.
        assert!(differ(&|c| c[2] = "all:0_1(X) :- :r(X,Y), all:0_0(Y)"));
        assert!(differ(&|c| c[2] = "all:0_1(X) :- :s(Y,X), all:0_0(Y)"));
        assert!(differ(&|c| c[4] = "all:0_0(X) :- :d(X)"));
        // The non-automaton clauses still match exactly.
        assert!(differ(&|c| c[0] = ":d(X) :- :r(Y,X), def:0(Y)"));
        assert!(differ(&|c| c[1] = "def:0(X) :- all:0_1(X), :c(X)"));
        // A state derived outside the automaton clauses makes the least
        // extension argument inapplicable: states are then compared by name.
        let mut derived = TRANSITIVE.to_vec();
        derived.push(":e(X) v all:0(X) :- :c(X), :d(X)");
        let mut control_derived = control.to_vec();
        control_derived.push(":e(X) v all:0_1(X) :- :c(X), :d(X)");
        assert!(!same(&derived, &control_derived));
        assert!(same(&derived, &derived));
    }
}
