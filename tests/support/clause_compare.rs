//! Semantic comparison of the clause and fact strings printed by the structural
//! clausification tests (`AbstractStructuralTest.getDLClauses`).
//!
//! Two printed clause sets are equivalent when they are equal after
//! * rewriting every literal to one key per data value, when its lexical form is
//!   valid for its datatype: OWL 2 / XSD 1.1 give `"18"^^xsd:int`,
//!   `"18"^^xsd:integer` and `"18.0"^^xsd:decimal` the same value, and a plain
//!   literal without a language tag abbreviates `xsd:string`;
//! * reading `{ ... }` enumerations and clause heads and bodies as sets; and
//! * one bijection of fresh auxiliary predicates (`def:`, `defdata:`, `nnq:`,
//!   `all:`), each mapped only within its own family and applied consistently
//!   across the whole clause and fact set.
//!
//! Nothing else is identified: ordinary and nominal names, variables, negation,
//! numbers, distinct value spaces (such as `xsd:double` and `xsd:decimal`) and
//! ill-typed literals must match exactly.
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// The fresh predicate families that clausification numbers arbitrarily.
const AUXILIARY: [&str; 4] = ["def", "defdata", "nnq", "all"];
/// Bijections tried before giving up; far above any structural control.
const MAX_BIJECTIONS: usize = 40_320;

pub fn equivalent<'a>(
    actual: impl IntoIterator<Item = &'a String>,
    expected: impl IntoIterator<Item = &'a String>,
) -> bool {
    let actual: Vec<Vec<String>> = actual.into_iter().map(|s| tokens(s)).collect();
    let expected: Vec<Vec<String>> = expected.into_iter().map(|s| tokens(s)).collect();
    let (actual_names, expected_names) = (auxiliaries(&actual), auxiliaries(&expected));
    if actual_names.len() != expected_names.len()
        || actual_names
            .iter()
            .any(|(kind, names)| expected_names.get(kind).map(Vec::len) != Some(names.len()))
    {
        return false;
    }
    let target = render_all(&actual, &HashMap::new());
    let families: Vec<(Vec<String>, Vec<String>)> = expected_names
        .into_iter()
        .map(|(kind, names)| (names, actual_names[&kind].clone()))
        .collect();
    let mut budget = MAX_BIJECTIONS;
    search(
        &families,
        &mut HashMap::new(),
        &mut |rename| render_all(&expected, rename) == target,
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
            r#""(?:\\.|[^"\\])*"(?:\^\^(?:<[^>]*>|[^\s(){},"<]+)|@[A-Za-z0-9-]+)?|<[^>]*>|[(){},]|[^\s(){},"<]+"#,
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

fn render_all(items: &[Vec<String>], rename: &HashMap<String, String>) -> BTreeSet<String> {
    items.iter().map(|item| render(item, rename)).collect()
}

/// Render one clause or fact with sorted enumerations, heads and bodies.
fn render(item: &[String], rename: &HashMap<String, String>) -> String {
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
    let Some(arrow) = flat.iter().position(|t| t == ":-") else {
        return flat.join(" ");
    };
    let atoms = |tokens: &[String], separator: &str| -> BTreeSet<String> {
        let mut atoms = BTreeSet::new();
        let (mut depth, mut current) = (0usize, Vec::new());
        for token in tokens {
            match token.as_str() {
                "(" => depth += 1,
                ")" => depth -= 1,
                t if t == separator && depth == 0 => {
                    atoms.insert(std::mem::take(&mut current).join(" "));
                    continue;
                }
                _ => {}
            }
            current.push(token.clone());
        }
        if !current.is_empty() {
            atoms.insert(current.join(" "));
        }
        atoms
    };
    let join = |atoms: BTreeSet<String>, separator: &str| {
        atoms.into_iter().collect::<Vec<_>>().join(separator)
    };
    format!(
        "{} :- {}",
        join(atoms(&flat[..arrow], "v"), " v "),
        join(atoms(&flat[arrow + 1..], ","), " , ")
    )
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
}
