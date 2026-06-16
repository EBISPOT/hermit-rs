// A pragmatic, sound core of org.semanticweb.HermiT.tableau.DatatypeManager and
// the `datatypes` package: it checks that each data-constant node satisfies all
// the data ranges asserted on it, setting a clash otherwise.
//
// HermiT's full datatype reasoning computes value-space intersections across
// per-datatype handlers (owlreal, floatnum, datetime, ...). This port covers the
// common OWL 2 datatypes -- the numeric types (with the min/max facets and the
// derived integers' implicit bounds), strings (with length facets), booleans,
// `xsd:dateTime`/`xsd:date` (with the ordering facets, comparing instants only
// when their timezone-presence matches, per XSD), and the IEEE float types
// (`xsd:double`/`xsd:float`) with their special values `NaN`/`INF`/`-INF`
// (`NaN` is a single value-space point; the specials are rejected for
// `xsd:decimal`) -- and `oneOf` enumerations and their negations, by testing
// the constant value against each asserted range. `xsd:anyURI` and the binary
// types (`xsd:hexBinary`/`xsd:base64Binary`, with octet-counted length facets)
// are covered as their own disjoint value spaces.
// It is *sound* (a clash is reported only when a value provably violates a
// range or the conjunction is provably empty). Value comparisons use XSD
// value-space equality (so `1^^integer` equals `1.0^^decimal`, and `01` equals
// `1`), and ill-typed literals are detected as clashes -- both lexically
// invalid forms (`"abc"^^xsd:integer`) and values outside a derived integer
// type's implicit value space (`"-1"^^xsd:nonNegativeInteger`,
// `"256"^^xsd:unsignedByte`). The per-datatype value-space handlers are ported:
// the owl:real lattice, the dateTime interval lattice, the rdf:PlainLiteral
// length lattice, the binary/anyURI cardinality reasoning, the finite-pattern
// analyzer, and the inequality-graph decision procedure for the conjunction of
// data ranges on a node. The only residual approximations are: rdf:XMLLiteral
// canonicalization (C14N is approximate), xsd:anyURI validation (a
// java.net.URI gate only, not the brics URI automaton), and the alphabet used
// when materializing string values. A `value_space_size` upper bound
// additionally catches unsatisfiable cardinalities over small datatypes (e.g.
// `≥3 r.boolean`).
#![allow(dead_code)]

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::model::{
    Constant, DatatypeRestriction, LiteralDataRange,
};
use crate::tableau::dependency_set::DependencySet;
use crate::tableau::node::NodeId;
use crate::tableau::node_type::NodeType;
use crate::tableau::object::TableauObject;
use crate::tableau::tableau::Tableau;
use crate::tableau::View;

// The lexical->value parser, the parsed-value type, and the datatype/facet
// predicates now live in the shared leaf module `crate::datatype_value` (the
// single Rust analogue of Java's `DatatypeRegistry.parseLiteral`); the
// value-space reasoning below operates on that shared `DataValue`. The glob
// import keeps every reasoning call site (`integer_datatype_bounds`,
// `is_*_datatype`, `DataValue::*`, ...) unchanged.
use crate::datatype_value::*;

// Re-export so `crate::tableau::datatype_manager::is_supported_*` paths (used by
// the structural clausifier) keep resolving here.
pub use crate::datatype_value::{is_supported_datatype, is_supported_facet};

const XSD: &str = "http://www.w3.org/2001/XMLSchema#";
const OWL: &str = "http://www.w3.org/2002/07/owl#";
const RDF: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";

/// Parses a [`Constant`]'s lexical form against its datatype, via the shared
/// [`crate::datatype_value::parse_value`]. A thin `&Constant` adapter so the
/// value-space reasoning can keep calling `parse_value(constant)`.
fn parse_value(constant: &Constant) -> Option<DataValue> {
    crate::datatype_value::parse_value(constant.lexical_form(), constant.datatype_uri())
}


/// The numeric *order* of a value as an exact rational (`num/den`, `den > 0`),
/// for the ordering facets. HermiT compares owl:real values exactly
/// (`Numbers.compare` promotes to BigInteger/BigDecimal/BigRational), so large
/// integers / exact decimals near a tight bound must NOT be collapsed to `f64`.
/// Floats and doubles participate in the order too (XSD compares them
/// numerically, with `-0 = +0` in the order even though they are distinct
/// values); a finite float/double maps to its exact dyadic rational, while
/// NaN/±INF are unordered here (handled separately) so this returns `None`.
fn as_exact(value: &DataValue) -> Option<(BigInt, BigInt)> {
    match value {
        DataValue::Integer(i) => Some((i.clone(), BigInt::one())),
        DataValue::Decimal { num, den } => Some((num.clone(), den.clone())),
        DataValue::Float(bits) => f32_to_exact(f32::from_bits(*bits)),
        DataValue::Double(bits) => f64_to_exact(f64::from_bits(*bits)),
        _ => None,
    }
}

/// The exact rational value of a finite `f64` (its dyadic fraction), or `None`
/// for NaN / ±INF.
fn f64_to_exact(f: f64) -> Option<(BigInt, BigInt)> {
    if !f.is_finite() {
        return None;
    }
    if f == 0.0 {
        return Some((BigInt::zero(), BigInt::one()));
    }
    let bits = f.to_bits();
    let sign = if bits >> 63 == 1 { -1i64 } else { 1 };
    let exponent = ((bits >> 52) & 0x7ff) as i64;
    let mantissa = bits & 0x000f_ffff_ffff_ffff;
    let (mantissa, exp2) = if exponent == 0 {
        (mantissa, -1074i64) // subnormal
    } else {
        (mantissa | 0x0010_0000_0000_0000, exponent - 1075)
    };
    let mut num = BigInt::from(sign) * BigInt::from(mantissa);
    let mut den = BigInt::one();
    let two = BigInt::from(2);
    if exp2 >= 0 {
        for _ in 0..exp2 {
            num *= &two;
        }
    } else {
        for _ in 0..(-exp2) {
            den *= &two;
        }
    }
    Some((num, den))
}

fn f32_to_exact(f: f32) -> Option<(BigInt, BigInt)> {
    f64_to_exact(f as f64)
}

/// Value-space equality: two values are equal iff they denote the same point of
/// the XSD value space. The `owl:real` kinds (`integer` ⊂ `decimal` ⊂
/// `rational`) are compared by value, so `1^^xsd:integer` equals
/// `1.0^^xsd:decimal`; integers are compared exactly to avoid `f64` rounding
/// for large magnitudes. `xsd:float` and `xsd:double` values are compared by
/// bits (one NaN value equal to itself, `+0 ≠ -0`) and are never equal to a
/// real or to each other (disjoint value spaces).
fn values_equal(a: &DataValue, b: &DataValue) -> bool {
    match (a, b) {
        (DataValue::Integer(x), DataValue::Integer(y)) => x == y,
        (DataValue::Boolean(x), DataValue::Boolean(y)) => x == y,
        (DataValue::Text(x), DataValue::Text(y)) => x == y,
        // A language-tagged plain literal is a distinct value, never equal to a
        // bare string (RDFPlainLiteralDataValue.equals compares both fields).
        (
            DataValue::LangString { string: s1, lang: l1 },
            DataValue::LangString { string: s2, lang: l2 },
        ) => s1 == s2 && l1 == l2,
        // Reduced fractions are canonical, so equality is structural.
        (
            DataValue::Decimal { num: n1, den: d1 },
            DataValue::Decimal { num: n2, den: d2 },
        ) => n1 == n2 && d1 == d2,
        (DataValue::Float(x), DataValue::Float(y)) => x == y,
        (DataValue::Double(x), DataValue::Double(y)) => x == y,
        // Java `DateTime.equals` compares three fields: the instant on the
        // timeline, the last-day (hour==24) flag, and the timezone offset. So
        // `...T24:00:00` is distinct from the equal-instant `...T00:00:00` of the
        // next day, and `...Z` is distinct from `...+01:00` at the same instant.
        (
            DataValue::DateTime { millis: x, has_tz: xt, last_day: xl, tz_offset: xo },
            DataValue::DateTime { millis: y, has_tz: yt, last_day: yl, tz_offset: yo },
        ) => x == y && xt == yt && xl == yl && xo == yo,
        (
            DataValue::Typed { kind: k1, canonical: c1, .. },
            DataValue::Typed { kind: k2, canonical: c2, .. },
        ) => k1 == k2 && c1 == c2,
        // Mixed real kinds: an integer equals a fraction with denominator 1.
        // (Reduced fractions never have den == 1, so this is always false, but
        // kept for clarity/robustness.)
        (DataValue::Integer(i), DataValue::Decimal { num, den })
        | (DataValue::Decimal { num, den }, DataValue::Integer(i)) => den.is_one() && num == i,
        _ => false,
    }
}

/// Whether `constant` is ill-typed: its datatype is a recognized XSD datatype
/// but its lexical form is not a valid value of that datatype (e.g.
/// `"abc"^^xsd:integer`). Such a literal denotes nothing and clashes. Unknown
/// datatypes are not judged (soundness).
fn is_ill_typed(constant: &Constant) -> bool {
    let datatype = constant.datatype_uri();
    let recognized = is_integer_datatype(datatype)
        || is_decimal_datatype(datatype)
        || is_float_datatype(datatype)
        || is_rational_datatype(datatype)
        // owl:real has no literals at all; Java's parseLiteral throws
        // MalformedLiteralException for owl:real (OWLRealDatatypeHandler.java:115-116).
        || is_real_datatype(datatype)
        || is_boolean_datatype(datatype)
        || is_string_datatype(datatype)
        || is_anyuri_datatype(datatype)
        || is_datetime_datatype(datatype)
        || is_hex_binary_datatype(datatype)
        || is_base64_datatype(datatype)
        || is_xml_literal_datatype(datatype);
    recognized && parse_value(constant).is_none()
}

/// Whether `value` belongs to the datatype named `datatype_uri`. The numeric
/// memberships follow OWL 2's datatype map: the `owl:real` hierarchy
/// (`integer` ⊂ `decimal` ⊂ `rational` ⊂ `real`) is one value space, with the
/// derived integer types carving out sub-ranges of the integers, while
/// `xsd:float` and `xsd:double` are value spaces of their own, disjoint from
/// the reals and from each other.
fn value_in_datatype(value: &DataValue, datatype_uri: &str) -> bool {
    match value {
        DataValue::Integer(i) => {
            if let Some((min, max)) = integer_datatype_bounds(datatype_uri) {
                // A derived integer type contains only its sub-range (e.g.
                // 6542145 is an xsd:integer but not an xsd:byte). Compare as
                // BigInt: a 40-digit integer is in xsd:integer but
                // not in any bounded derived type.
                min.is_none_or(|m| *i >= BigInt::from(m))
                    && max.is_none_or(|m| *i <= BigInt::from(m))
            } else {
                is_decimal_datatype(datatype_uri)
                    || is_rational_datatype(datatype_uri)
                    || is_real_datatype(datatype_uri)
            }
        }
        DataValue::Decimal { num, den } => {
            // A fraction is an xsd:decimal iff its reduced denominator has only
            // the factors 2 and 5 (i.e. the value has a finite decimal form);
            // with denominator 1 it is also in the matching integer types.
            let mut d = den.clone();
            let two = BigInt::from(2);
            let five = BigInt::from(5);
            while (&d % &two).is_zero() {
                d /= &two;
            }
            while (&d % &five).is_zero() {
                d /= &five;
            }
            (is_decimal_datatype(datatype_uri) && d.is_one())
                || is_rational_datatype(datatype_uri)
                || is_real_datatype(datatype_uri)
                || (den.is_one()
                    && integer_datatype_bounds(datatype_uri).is_some_and(|(min, max)| {
                        min.is_none_or(|m| *num >= BigInt::from(m))
                            && max.is_none_or(|m| *num <= BigInt::from(m))
                    }))
        }
        DataValue::Float(_) => is_xsd_float(datatype_uri),
        DataValue::Double(_) => is_xsd_double(datatype_uri),
        DataValue::Boolean(_) => is_boolean_datatype(datatype_uri),
        // A bare string (no language tag) is in rdf:PlainLiteral and in an
        // xsd:string subtype only when its lexical form satisfies that subtype's
        // character/lexical constraints (Java decides this via the per-subtype
        // automaton in RDFPlainLiteralPatternValueSpaceSubset.containsDataValue):
        // e.g. "a b" is a valid xsd:string but not a valid xsd:NCName.
        DataValue::Text(s) => {
            is_string_datatype(datatype_uri) && string_lexical_valid(datatype_uri, s)
        }
        DataValue::LangString { .. } => datatype_uri == format!("{RDF}PlainLiteral"),
        // xsd:dateTime accepts values with or without a timezone; xsd:dateTimeStamp
        // mandates a timezone, so a timezone-less value is not a member of its value
        // space (DateTimeInterval.containsDateTime returns false for a WITH_TIMEZONE
        // interval when the value has no timezone offset).
        DataValue::DateTime { has_tz, .. } => {
            is_datetime_datatype(datatype_uri)
                && (datatype_uri.strip_prefix(XSD) != Some("dateTimeStamp") || *has_tz)
        }
        DataValue::Typed { kind, .. } => match *kind {
            "anyURI" => is_anyuri_datatype(datatype_uri),
            "hexBinary" => is_hex_binary_datatype(datatype_uri),
            "base64Binary" => is_base64_datatype(datatype_uri),
            "XMLLiteral" => is_xml_literal_datatype(datatype_uri),
            _ => false,
        },
    }
}

/// Whether `value` satisfies a facet `facet_uri = facet_value`. A facet that the
/// datatype's handler supports but the value does not is a violation; an
/// *unsupported* facet/datatype combination is caught earlier (HermiT
/// rejects it as `UnsupportedFacetException`), so here only the supported facets
/// are evaluated. An unrecognized facet is not silently accepted — see
/// `is_supported_facet`.
fn value_satisfies_facet(value: &DataValue, facet_uri: &str, facet_value: &Constant) -> bool {
    // rdf:langRange lives in the RDF namespace, not XSD.
    if facet_uri == format!("{RDF}langRange") {
        return value_satisfies_lang_range(value, facet_value.lexical_form());
    }
    let facet = match facet_uri.strip_prefix(XSD) {
        Some(f) => f,
        None => return true,
    };
    match facet {
        "minInclusive" | "maxInclusive" | "minExclusive" | "maxExclusive" => {
            // Compare owl:real values exactly (BigInt fraction arithmetic),
            // never via lossy f64. A finite float/double also maps to its exact
            // dyadic rational; NaN and ±INF (which have no exact rational) are
            // handled first: NaN is outside every interval, ±INF compares by sign.
            if matches!(value, DataValue::Float(_) | DataValue::Double(_)) {
                if let Some(special) = special_float_order(value, facet, facet_value) {
                    return special;
                }
                // A finite float/double is compared by the IEEE order key, not by
                // its dyadic rational: FloatInterval/DoubleInterval order `-0.0`
                // strictly below `+0.0`. The facet bound's zero sign is normalised
                // per facet first (`getIntervalFor`), so e.g. `minInclusive 0.0`
                // admits both `-0.0` and `+0.0` while `minExclusive -0.0` excludes
                // both. The exact-rational path would collapse `±0.0` to one point
                // and miss this distinction.
                if let Some(result) = finite_float_order(value, facet, facet_value) {
                    return result;
                }
            }
            if let (Some(v), Some(bound)) =
                (as_exact(value), parse_value(facet_value).and_then(|b| as_exact(&b)))
            {
                return compare_order_exact(&v, &bound, facet);
            }
            // Datetime comparison. When both carry (or both omit) a timezone the
            // instants compare directly. When timezone-presence differs, XSD/
            // HermiT widen the timezone-less value by the maximum timezone offset
            // (±14h) and compare strictly: a value satisfies `min*` only if it
            // exceeds bound+14h, and `max*` only if it precedes bound-14h
            // (DateTimeDatatypeHandler.getIntervalsFor). This is symmetric in
            // which side carries the timezone.
            if let (
                DataValue::DateTime { millis: v, has_tz: vt, .. },
                Some(DataValue::DateTime { millis: bound, has_tz: bt, .. }),
            ) = (value, parse_value(facet_value))
            {
                if *vt == bt {
                    return compare_order_i64(*v, bound, facet);
                }
                return match facet {
                    "minInclusive" | "minExclusive" => {
                        *v > bound.saturating_add(MAX_TZ_CORRECTION_MILLIS)
                    }
                    "maxInclusive" | "maxExclusive" => {
                        *v < bound.saturating_sub(MAX_TZ_CORRECTION_MILLIS)
                    }
                    _ => true,
                };
            }
            true
        }
        "length" | "minLength" | "maxLength" => {
            let len = match value {
                // HermiT counts UTF-16 code units (Java String.length()),
                // not Unicode code points (astral-plane chars count as 2).
                DataValue::Text(s) => s.encode_utf16().count(),
                // The length facet counts only the string part of a
                // language-tagged plain literal (RDFPlainLiteralLengthInterval
                // uses the string length, not the @lang tag).
                DataValue::LangString { string, .. } => string.encode_utf16().count(),
                DataValue::Typed { length, .. } => *length,
                _ => return true,
            };
            let Ok(bound) = facet_value.lexical_form().trim().parse::<usize>() else {
                return true;
            };
            match facet {
                "length" => len == bound,
                "minLength" => len >= bound,
                "maxLength" => len <= bound,
                _ => true,
            }
        }
        "pattern" => {
            // xsd:pattern applies to xsd:string subtypes, rdf:PlainLiteral
            // AND xsd:anyURI (AnyURIDatatypeHandler supports it). Binary types do
            // not support pattern (excluded). The matched string is the literal's
            // lexical/canonical form.
            let s: &str = match value {
                DataValue::Text(s) => s,
                DataValue::LangString { string, .. } => string,
                DataValue::Typed { kind: "anyURI", canonical, .. } => canonical,
                _ => return true,
            };
            // XSD regular expressions match the whole literal (implicitly
            // anchored). The XSD dialect is close enough to the `regex` crate's
            // for the common facets; an unparseable pattern is not judged.
            match regex::Regex::new(&format!("^(?:{})$", facet_value.lexical_form())) {
                Ok(re) => re.is_match(s),
                Err(_) => true,
            }
        }
        _ => true,
    }
}

/// RFC 4647 basic language-range filtering for rdf:langRange, mirroring
/// `RDFPlainLiteralPatternValueSpaceSubset.getLanguageRangeAutomaton`:
///   * range `"*"` matches any value that *has* a (non-empty) language tag;
///   * otherwise a case-insensitive match where the value's tag equals the
///     range or extends it after a `-` separator (`en` matches `en` and
///     `en-GB`, but not `eng`).
/// A value without a language tag never matches a langRange.
fn value_satisfies_lang_range(value: &DataValue, range: &str) -> bool {
    let DataValue::LangString { lang, .. } = value else {
        return false;
    };
    if range == "*" {
        return !lang.is_empty();
    }
    let range = range.to_ascii_lowercase();
    let tag = lang.to_ascii_lowercase();
    tag == range || tag.strip_prefix(&range).is_some_and(|rest| rest.starts_with('-'))
}

/// Ordering comparison for float/double specials (NaN / ±INF) that have no
/// exact rational. Returns `None` when `value` is a finite float/double (the
/// caller then uses the exact path), `Some(bool)` for a NaN or infinite value.
fn special_float_order(value: &DataValue, facet: &str, facet_value: &Constant) -> Option<bool> {
    let f = match value {
        DataValue::Float(bits) => f32::from_bits(*bits) as f64,
        DataValue::Double(bits) => f64::from_bits(*bits),
        _ => return None,
    };
    if f.is_nan() {
        // NaN is incomparable: it lies outside every ordering interval.
        return Some(false);
    }
    if f.is_infinite() {
        let bound_f = parse_value(facet_value).map(|bv| match bv {
            DataValue::Float(bits) => f32::from_bits(bits) as f64,
            DataValue::Double(bits) => f64::from_bits(bits),
            _ => f64::NAN,
        });
        // A NaN bound is handled like getIntervalFor does it, which differs by kind:
        //   * xsd:double's mask is correct, so a NaN bound is dropped and the facet
        //     is unconstraining: every value (incl. ±INF) satisfies it.
        //   * xsd:float's FloatInterval.isNaN mask is bugged (0x003fffff), so the
        //     canonical NaN bound 0x7fc00000 is mistaken for an ordinary positive
        //     value above +INF: a min* facet yields an empty interval (no value
        //     satisfies it), while a max* facet leaves the upper bound at +INF (the
        //     bound is effectively dropped, so every value satisfies it).
        if bound_f.is_some_and(|b| b.is_nan()) {
            return Some(match value {
                DataValue::Float(_) => matches!(facet, "maxInclusive" | "maxExclusive"),
                _ => true,
            });
        }
        // Java FloatInterval/DoubleInterval.isSmallerEqual: two infinities compare
        // equal when they have the same sign (same sign + same magnitude bits).
        // So +INF satisfies maxInclusive iff the bound is also +INF, and -INF
        // satisfies minInclusive iff the bound is also -INF.  The Exclusive
        // variants correctly reject the equal-bound case (nextFloat of +INF is a
        // finite number, so +INF is excluded; similarly for -INF).
        return Some(match facet {
            "minInclusive" => f > 0.0 || bound_f == Some(f64::NEG_INFINITY),
            "minExclusive" => f > 0.0,
            "maxInclusive" => f < 0.0 || bound_f == Some(f64::INFINITY),
            "maxExclusive" => f < 0.0,
            _ => true,
        });
    }
    None
}

/// Ordering comparison for a *finite* `xsd:float`/`xsd:double` value against a
/// facet bound of the same kind, by the IEEE monotone order key (so `-0.0` and
/// `+0.0` are distinct, with `-0.0` strictly below `+0.0`), mirroring
/// `FloatInterval`/`DoubleInterval.isSmallerEqual`. Returns `None` when the value
/// is not a finite float/double or the bound does not parse to the matching kind
/// (the caller then uses the exact-rational path).
fn finite_float_order(value: &DataValue, facet: &str, facet_value: &Constant) -> Option<bool> {
    match value {
        DataValue::Float(bits) => {
            let v = f32::from_bits(*bits);
            if !v.is_finite() {
                return None;
            }
            let Some(DataValue::Float(bbits)) = parse_value(facet_value) else {
                return None;
            };
            let b = f32::from_bits(bbits);
            // A ±INF bound compares by the IEEE order key; a NaN bound is treated as
            // Java's bugged FloatInterval.isNaN treats it — an ordinary positive
            // value of magnitude 0x7fc00000 (above +INF) — so a finite value never
            // satisfies a NaN min* bound and always satisfies a NaN max* bound,
            // matching FloatInterval/getIntervalFor. Both flow through f32_order_key
            // directly (no finite-bound bail).
            let b = normalize_zero_for_facet_f32(b, facet);
            let (vk, bk) = (f32_order_key(v), f32_order_key(b));
            Some(match facet {
                "minInclusive" => vk >= bk,
                "maxInclusive" => vk <= bk,
                "minExclusive" => vk > bk,
                "maxExclusive" => vk < bk,
                _ => true,
            })
        }
        DataValue::Double(bits) => {
            let v = f64::from_bits(*bits);
            if !v.is_finite() {
                return None;
            }
            let Some(DataValue::Double(bbits)) = parse_value(facet_value) else {
                return None;
            };
            let b = f64::from_bits(bbits);
            // xsd:double's DoubleInterval.isNaN mask is CORRECT (unlike float), so a
            // NaN bound is dropped by getIntervalFor (the facet is unconstraining);
            // returning None lets value_satisfies_facet fall through to `true`. A
            // ±INF bound, however, must compare by the IEEE order key.
            if b.is_nan() {
                return None;
            }
            let b = normalize_zero_for_facet_f64(b, facet);
            let (vk, bk) = (f64_order_key(v), f64_order_key(b));
            Some(match facet {
                "minInclusive" => vk >= bk,
                "maxInclusive" => vk <= bk,
                "minExclusive" => vk > bk,
                "maxExclusive" => vk < bk,
                _ => true,
            })
        }
        _ => None,
    }
}

/// Compares exact rationals `v = vn/vd` and `bound = bn/bd` (both with positive
/// denominators) for an ordering facet, cross-multiplying so the comparison is
/// exact. `vn*bd  ?  bn*vd`.
fn compare_order_exact(v: &(BigInt, BigInt), bound: &(BigInt, BigInt), facet: &str) -> bool {
    let lhs = &v.0 * &bound.1;
    let rhs = &bound.0 * &v.1;
    match facet {
        "minInclusive" => lhs >= rhs,
        "maxInclusive" => lhs <= rhs,
        "minExclusive" => lhs > rhs,
        "maxExclusive" => lhs < rhs,
        _ => true,
    }
}

/// Compares `v` against `bound` for an ordering facet (datetime instants, f64).
fn compare_order_i64(v: i64, bound: i64, facet: &str) -> bool {
    match facet {
        "minInclusive" => v >= bound,
        "maxInclusive" => v <= bound,
        "minExclusive" => v > bound,
        "maxExclusive" => v < bound,
        _ => true,
    }
}

/// Whether `range` (or, recursively, the range it negates) contains a datatype
/// restriction with a facet its handler does not support. Such a
/// restriction is an `UnsupportedFacetException` in HermiT.
/// Mirror of Java's `validateDatatypeRestriction`: for length facets on
/// length-bearing types, the value must be a non-negative integer strictly less
/// than `Integer.MAX_VALUE` (2147483647).  Returns `true` ("unsupported") when
/// the value is not an integer literal, is negative, or equals `i32::MAX`.
fn length_facet_value_unsupported(facet_value: &crate::model::Constant) -> bool {
    // BinaryData/AnyURI/RDFPlainLiteral validateDatatypeRestriction: the facet
    // value's dataValue must be a java.lang.Integer -- i.e. an integer-typed
    // literal that is non-negative and strictly less than Integer.MAX_VALUE.
    match parse_value(facet_value) {
        Some(DataValue::Integer(v)) => v < BigInt::from(0) || v >= BigInt::from(i32::MAX),
        _ => true,
    }
}

/// Mirror of the numeric / float / double / dateTime `validateDatatypeRestriction`
/// type checks for the ordering facets (min/max Inclusive/Exclusive): the facet
/// value's dataValue must be of the kind the datatype handler accepts. Returns
/// `true` ("unsupported") otherwise -- an `UnsupportedFacetException` in HermiT.
fn ordering_facet_value_unsupported(datatype_uri: &str, facet_value: &crate::model::Constant) -> bool {
    let value = match parse_value(facet_value) {
        Some(value) => value,
        None => return true,
    };
    if is_xsd_float(datatype_uri) {
        !matches!(value, DataValue::Float(_))
    } else if is_xsd_double(datatype_uri) {
        !matches!(value, DataValue::Double(_))
    } else if is_datetime_datatype(datatype_uri) {
        !matches!(value, DataValue::DateTime { .. })
    } else {
        // owl:real-derived datatypes: the value must be a valid Number, i.e.
        // an integer, a decimal, or a rational (Numbers.isValidNumber); Float
        // and Double are rejected.
        !matches!(value, DataValue::Integer(_) | DataValue::Decimal { .. })
    }
}

fn range_has_unsupported_facet(range: &LiteralDataRange) -> bool {
    match range {
        LiteralDataRange::DatatypeRestriction(r) => {
            let uri = r.datatype_uri();
            // Only judge datatypes we actually handle; an unknown datatype is
            // already rejected (or ignored) by the clausifier.
            if !is_supported_datatype(uri) {
                return false;
            }
            (0..r.number_of_facet_restrictions()).any(|i| {
                let facet_uri = r.facet_uri(i);
                if !is_supported_facet(uri, facet_uri) {
                    return true;
                }
                // validateDatatypeRestriction also rejects an ontology whose
                // facet *value* is of the wrong type for the datatype: a length
                // facet value must be an Integer; an ordering facet value must
                // be the numeric / float / double / dateTime kind the handler
                // accepts.
                match facet_uri.strip_prefix(XSD) {
                    Some("length" | "minLength" | "maxLength") => {
                        length_facet_value_unsupported(r.facet_value(i))
                    }
                    Some("minInclusive" | "maxInclusive" | "minExclusive" | "maxExclusive") => {
                        ordering_facet_value_unsupported(uri, r.facet_value(i))
                    }
                    _ => false,
                }
            })
        }
        LiteralDataRange::AtomicNegationDataRange(n) => {
            range_has_unsupported_facet(&n.get_negation())
        }
        _ => false,
    }
}

fn value_satisfies_restriction(value: &DataValue, restriction: &DatatypeRestriction) -> bool {
    if !value_in_datatype(value, restriction.datatype_uri()) {
        return false;
    }
    for i in 0..restriction.number_of_facet_restrictions() {
        if !value_satisfies_facet(value, restriction.facet_uri(i), restriction.facet_value(i)) {
            return false;
        }
    }
    true
}

/// Whether `value` is in the value space of `range` (None if it cannot be
/// determined soundly).
fn value_in_range(value: &DataValue, range: &LiteralDataRange) -> Option<bool> {
    match range {
        LiteralDataRange::InternalDatatype(_) => Some(true), // rdfs:Literal / internal: everything
        LiteralDataRange::DatatypeRestriction(r) => Some(value_satisfies_restriction(value, r)),
        LiteralDataRange::ConstantEnumeration(e) => {
            let mut found = false;
            for i in 0..e.number_of_constants() {
                match parse_value(e.constant(i)) {
                    Some(v) => {
                        if values_equal(&v, value) {
                            found = true;
                        }
                    }
                    None => return None, // unparseable member; cannot decide soundly
                }
            }
            Some(found)
        }
        LiteralDataRange::AtomicNegationDataRange(n) => {
            let inner: LiteralDataRange = n.get_negation();
            value_in_range(value, &inner).map(|b| !b)
        }
    }
}

/// A lower or upper numeric bound from a facet.
struct Bound {
    /// The bound is kept as an exact rational (`num/den`, `den > 0`) so the
    /// emptiness test compares exactly rather than via lossy f64.
    value: (BigInt, BigInt),
    inclusive: bool,
}

/// Exact ordering of two rationals `a = an/ad`, `b = bn/bd` (positive
/// denominators): returns `Ordering` via cross-multiplication.
fn cmp_exact(a: &(BigInt, BigInt), b: &(BigInt, BigInt)) -> std::cmp::Ordering {
    (&a.0 * &b.1).cmp(&(&b.0 * &a.1))
}

impl Tableau {
    /// Checks data nodes against their asserted data ranges, setting a clash if
    /// a node's value (or, for fresh data nodes, its data-range conjunction) is
    /// unsatisfiable. Returns whether a clash was found.
    ///
    /// Fires the `datatypeCheckingStarted`/`datatypeCheckingFinished` monitor
    /// events around the check, matching `DatatypeManager.checkDatatypeConstraints`
    /// (DatatypeManager.java:143-144,188-189). The finished event reports
    /// `!containsClash()`, as Java does. The finer-grained
    /// `datatypeConjunctionChecking*` events bracket each per-node conjunction
    /// satisfiability check, and the `clashDetection*` events bracket the
    /// directly-disjoint datatype-restriction pair clash
    /// (DatatypeManager.java:252-262,274-304); all are answer-neutral observers.
    pub fn check_datatype_constraints(&mut self) -> bool {
        // Consume the dirty flag: any data-node change *after* this point (e.g. a
        // clash inequality this very check generates) re-arms it, but a clash short
        // circuits the round anyway.
        self.datatype_check_needed = false;
        self.monitor_event(|m| m.datatype_checking_started());
        let clash = self.check_datatype_constraints_impl();
        self.monitor_event(|m| m.datatype_checking_finished());
        clash
    }

    fn check_datatype_constraints_impl(&mut self) -> bool {
        let mut node = self.first_tableau_node;
        while let Some(current) = node {
            node = self.nodes[current].next_tableau_node;
            if !self.nodes[current].is_active() {
                continue;
            }
            let node_type = self.nodes[current].get_node_type();
            if node_type != NodeType::RootConstantNode && node_type != NodeType::ConcreteNode {
                continue;
            }
            // An ill-typed fixed literal (e.g. "abc"^^xsd:integer) denotes
            // nothing and clashes regardless of any asserted ranges.
            if self.nodes[current].constant_value().is_some_and(is_ill_typed) {
                let dep = DependencySet::Permanent(self.dependency_set_factory.empty_set());
                self.set_clash(&dep);
                return true;
            }
            // Collect the positive data ranges asserted on the node.
            let ranges: Vec<(LiteralDataRange, _)> = self.node_data_ranges(current);
            if ranges.is_empty() {
                continue;
            }
            // A datatype restriction carrying a facet outside its handler's
            // supported set is an UnsupportedFacetException in HermiT (the
            // ontology is rejected at validateDatatypeRestriction, before
            // reasoning). HermiT never *silently ignores* the facet. Since the
            // clausifier already rejects unsupported *datatypes* via
            // is_supported_datatype, we mirror that for facets here: an
            // unsupported facet on an asserted range surfaces as a clash rather
            // than being treated as vacuously satisfied. (is_supported_facet is
            // also exported so the clausifier can reject earlier, exactly as it
            // does for unsupported datatypes.)
            if let Some((_, dep)) = ranges.iter().find(|(r, _)| range_has_unsupported_facet(r)) {
                let dep = DependencySet::Permanent(dep.clone());
                self.set_clash(&dep);
                return true;
            }
            let constant_value = self.nodes[current]
                .constant_value()
                .and_then(parse_value);

            // The per-node data-range conjunction satisfiability check, mirroring
            // DatatypeManager.checkConjunctionSatisfiability (DatatypeManager.java:274-304):
            // the conjunction-checking events bracket the satisfiability decision,
            // and the finished event reports the satisfiability result (no clash).
            self.monitor_event(|m| m.datatype_conjunction_checking_started());
            let unsatisfiable = if let Some(value) = &constant_value {
                // Fixed value: it must be in every asserted range.
                ranges.iter().any(|(r, _)| value_in_range(value, r) == Some(false))
            } else {
                // Fresh data node: its data-range conjunction must be non-empty.
                conjunction_is_empty(&ranges)
            };
            self.monitor_event(|m| m.datatype_conjunction_checking_finished(!unsatisfiable));
            if unsatisfiable {
                // The clash dependency set mirrors HermiT. A clash caused by a
                // directly-disjoint datatype pair on the node folds ONLY the two
                // conflicting assertions' dependency sets — this is the
                // `clashingRestriction` clash in
                // DatatypeChecker.DVariable.addDataRange
                // (DatatypeChecker.java:382-383), set in
                // DatatypeManager.checkDatatypeConstraints (DatatypeManager.java:247-249).
                // Any other empty conjunction folds every positive/negative
                // datatype-restriction assertion on the node, as
                // DatatypeManager.loadAssertionDependencySets does
                // (DatatypeManager.java:308-322).
                let pair = disjoint_datatype_pair_deps(&ranges);
                let deps: Vec<crate::tableau::dependency_set::PermanentDependencySet> =
                    match &pair {
                        Some((d1, d2)) => vec![d1.clone(), d2.clone()],
                        None => ranges.iter().map(|(_, d)| d.clone()).collect(),
                    };
                let mut dep = DependencySet::Permanent(self.dependency_set_factory.empty_set());
                for d in &deps {
                    let mut union = crate::tableau::dependency_set::UnionDependencySet::new(2);
                    union.add_constituent(dep);
                    union.add_constituent(DependencySet::Permanent(d.clone()));
                    dep = DependencySet::Union(union);
                }
                // The directly-disjoint datatype-restriction pair clash is bracketed
                // by the clashDetection events, exactly as in
                // getAndInitializeVariableFor (DatatypeManager.java:252-262). The
                // general empty-conjunction clash is set inside
                // checkConjunctionSatisfiability without those events.
                let directly_disjoint = pair.is_some();
                if directly_disjoint {
                    self.monitor_event(|m| m.clash_detection_started());
                }
                self.set_clash(&dep);
                if directly_disjoint {
                    self.monitor_event(|m| m.clash_detection_finished());
                }
                return true;
            }
        }
        // The per-node checks passed; now check that the data nodes can take
        // *distinct* values where the tableau requires them to differ.
        self.check_data_value_assignments()
    }

    /// The inequality-aware core of HermiT's `DatatypeManager`: data nodes
    /// related by `Inequality` (from at-most merging, at-least expansion or
    /// disjoint data properties), or forced apart by a negative data property
    /// assertion (`¬dp(u,c)` keeps every `dp`-successor of `u` away from `c`'s
    /// value), must be assignable pairwise-distinct values from their data
    /// ranges.
    ///
    /// This is a *complete* decision, mirroring
    /// `DatatypeChecker.getUnsatisfiabilityCauseOrCauses`. Every connected
    /// component of mutually-distinct nodes is decided — no component is skipped
    /// for being large, and no infinite-value-space node is silently dropped:
    ///   * a *symmetric clique* (all pairwise distinct, identical restrictions)
    ///     clashes exactly when its shared value-space cardinality is below the
    ///     clique size (the pigeonhole check, via `node_cardinality`, with no
    ///     enumeration — so e.g. ≥13 distinct `xsd:boolean` nodes, or N+1 nodes
    ///     over an N-value range, clash);
    ///   * otherwise nodes that can always sidestep their neighbours
    ///     (cardinality ≥ degree+1, which includes every infinite value space)
    ///     are eliminated to a fixpoint, exactly as
    ///     `eliminateTriviallySatisfiableVariables`. The survivors then have a
    ///     finite value space strictly smaller than their degree+1 (hence ≤ the
    ///     component size), so enumerating them and running the inequality-aware
    ///     backtracking assignment (`findAssignment`) is bounded and exact.
    ///
    /// An infinite value space (dense decimal/rational/real, unbounded integer,
    /// string) trivially satisfies any number of distinct nodes without
    /// enumeration.
    fn check_data_value_assignments(&mut self) -> bool {
        use crate::model::DLPredicate;
        use std::collections::HashMap;

        // The active data nodes (root constants + fresh concrete nodes).
        let mut data_nodes: Vec<NodeId> = Vec::new();
        let mut node = self.first_tableau_node;
        while let Some(current) = node {
            node = self.nodes[current].next_tableau_node;
            if self.nodes[current].is_active()
                && matches!(
                    self.nodes[current].get_node_type(),
                    NodeType::RootConstantNode | NodeType::ConcreteNode
                )
            {
                data_nodes.push(current);
            }
        }
        if data_nodes.is_empty() {
            return false;
        }
        let is_data = |n: NodeId| {
            self.nodes[n].is_active()
                && matches!(
                    self.nodes[n].get_node_type(),
                    NodeType::RootConstantNode | NodeType::ConcreteNode
                )
        };
        let empty = self.dependency_set_factory.empty_set();

        // Distinctness edges between data nodes, with the dependency sets of
        // the assertions that induce them.
        type Dep = crate::tableau::dependency_set::PermanentDependencySet;
        let mut edges: Vec<(NodeId, NodeId, Vec<Dep>)> = Vec::new();
        let retrieval =
            self.create_ternary_retrieval([-1, -1, -1], [None, None, None], View::Total);
        let mut role_edges: Vec<(TableauObject, NodeId, NodeId, Dep)> = Vec::new();
        let mut negated_roles: Vec<(TableauObject, NodeId, NodeId, Dep)> = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            let label = self.ternary_extension_table.get_tuple_object(tuple_index, 0);
            let n1 = self
                .ternary_extension_table
                .get_tuple_object(tuple_index, 1)
                .as_node()
                .unwrap();
            let n2 = self
                .ternary_extension_table
                .get_tuple_object(tuple_index, 2)
                .as_node()
                .unwrap();
            let dep = self.ternary_extension_table.get_dependency_set(tuple_index, &empty);
            match label {
                TableauObject::DLPredicate(DLPredicate::Inequality) => {
                    if is_data(n1) && is_data(n2) {
                        edges.push((n1, n2, vec![dep]));
                    }
                }
                TableauObject::DLPredicate(DLPredicate::AtomicRole(_)) => {
                    if is_data(n2) {
                        role_edges.push((label.clone(), n1, n2, dep));
                    }
                }
                TableauObject::NegatedAtomicRole(_) => {
                    if is_data(n2) {
                        negated_roles.push((label.clone(), n1, n2, dep));
                    }
                }
                _ => {}
            }
        }
        // ¬dp(u,c) demands value(y) ≠ value(c) for every dp(u,y).
        for (neg_label, u, c, neg_dep) in &negated_roles {
            let TableauObject::NegatedAtomicRole(nr) = neg_label else {
                continue;
            };
            for (role_label, u2, y, role_dep) in &role_edges {
                let TableauObject::DLPredicate(DLPredicate::AtomicRole(r)) = role_label else {
                    continue;
                };
                if r == nr.get_negated_atomic_role() && u2 == u {
                    edges.push((*y, *c, vec![neg_dep.clone(), role_dep.clone()]));
                }
            }
        }

        // Per-node ranges and value-space descriptions, computed lazily. The
        // value space mirrors a HermiT `DVariable`'s conjoined value-space
        // subset: `node_value_space` reports either an infinite cardinality
        // (`Infinite`) or an exact finite cardinality with the (optionally
        // materialized) value set.
        let mut value_space: HashMap<NodeId, NodeValueSpace> = HashMap::new();
        let mut ranges_by_node: HashMap<NodeId, Vec<(LiteralDataRange, Dep)>> = HashMap::new();
        let ensure = |slf: &Tableau,
                      value_space: &mut HashMap<NodeId, NodeValueSpace>,
                      ranges_by_node: &mut HashMap<NodeId, Vec<(LiteralDataRange, Dep)>>,
                      n: NodeId| {
            if value_space.contains_key(&n) {
                return;
            }
            let ranges = slf.node_data_ranges(n);
            let constant = slf.nodes[n].constant_value().and_then(parse_value);
            let vs = node_value_space(constant.as_ref(), &ranges);
            ranges_by_node.insert(n, ranges);
            value_space.insert(n, vs);
        };

        // A clash dependency-set helper: fold the given dependency sets into one
        // (the union of everything that shaped the conclusion).
        let fold_deps = |deps: &[Dep]| -> DependencySet {
            let mut dep = DependencySet::Permanent(empty.clone());
            for d in deps {
                let mut union = crate::tableau::dependency_set::UnionDependencySet::new(2);
                union.add_constituent(dep);
                union.add_constituent(DependencySet::Permanent(d.clone()));
                dep = DependencySet::Union(union);
            }
            dep
        };

        // Self-inequalities (dp(u,c) ∧ ¬dp(u,c)) clash immediately, and build the
        // distinctness graph over all data nodes (infinite-value-space nodes are
        // *kept*, then eliminated below — matching HermiT, which loads them as
        // variables and removes them via `eliminateTriviallySatisfiableVariables`).
        let mut component_edges: Vec<(NodeId, NodeId, Vec<Dep>)> = Vec::new();
        let mut adjacency: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
        for (a, b, deps) in edges {
            if a == b {
                self.set_clash(&fold_deps(&deps));
                return true;
            }
            ensure(self, &mut value_space, &mut ranges_by_node, a);
            ensure(self, &mut value_space, &mut ranges_by_node, b);
            adjacency.entry(a).or_default().push(b);
            adjacency.entry(b).or_default().push(a);
            component_edges.push((a, b, deps));
        }

        // A node whose value space is provably empty is unsatisfiable on its own
        // (e.g. a float interval with no representable member, or an enumeration
        // every member of which is excluded by another range).
        for &n in &data_nodes {
            if !value_space.contains_key(&n) && !self.node_data_ranges(n).is_empty() {
                ensure(self, &mut value_space, &mut ranges_by_node, n);
            }
            if let Some(NodeValueSpace::Finite { count: 0, .. }) = value_space.get(&n) {
                let deps: Vec<Dep> = ranges_by_node
                    .get(&n)
                    .into_iter()
                    .flatten()
                    .map(|(_, d)| d.clone())
                    .collect();
                self.set_clash(&fold_deps(&deps));
                return true;
            }
        }

        if component_edges.is_empty() {
            return false;
        }

        // Gather connected components by BFS over the inequality graph, but do NOT
        // expand through a ROOT_CONSTANT_NODE: a fixed-value node "breaks" the
        // conjunction (DatatypeManager.loadConjunctionFrom), so variables connected
        // only *through* a constant are analyzed independently. A constant is added
        // to each adjacent component as a non-expanding leaf (and may thus appear in
        // several components). Starting from the lowest-id variable keeps the
        // processing order -- and the clash dependency set signalled for the first
        // unsatisfiable component -- deterministic.
        let mut variables: Vec<NodeId> = adjacency
            .keys()
            .copied()
            .filter(|&n| self.nodes[n].get_node_type() != NodeType::RootConstantNode)
            .collect();
        variables.sort();
        let mut assigned: std::collections::HashSet<NodeId> = std::collections::HashSet::new();
        for &start in &variables {
            if assigned.contains(&start) {
                continue;
            }
            let mut component: Vec<NodeId> = Vec::new();
            let mut seen: std::collections::HashSet<NodeId> = std::collections::HashSet::new();
            let mut queue: std::collections::VecDeque<NodeId> = std::collections::VecDeque::new();
            queue.push_back(start);
            seen.insert(start);
            while let Some(node) = queue.pop_front() {
                component.push(node);
                if self.nodes[node].get_node_type() == NodeType::RootConstantNode {
                    continue; // breaker: a fixed-value node does not bridge.
                }
                assigned.insert(node);
                if let Some(neighbours) = adjacency.get(&node) {
                    for &neighbour in neighbours {
                        if seen.insert(neighbour) {
                            queue.push_back(neighbour);
                        }
                    }
                }
            }
            component.sort();
            component.dedup();
            if self.decide_component(
                &component,
                &component_edges,
                &value_space,
                &ranges_by_node,
                &empty,
            ) {
                return true;
            }
        }
        false
    }

    /// Decides one connected component of mutually-distinct data nodes,
    /// returning whether it clashes. Mirrors
    /// `DatatypeChecker.getUnsatisfiabilityCauseOrCauses` for a single
    /// inequality-connected group: the symmetric-clique cardinality shortcut,
    /// elimination of trivially-satisfiable (incl. infinite) variables, then a
    /// bounded backtracking assignment over the survivors' exact value spaces.
    fn decide_component(
        &mut self,
        nodes: &[NodeId],
        component_edges: &[(
            NodeId,
            NodeId,
            Vec<crate::tableau::dependency_set::PermanentDependencySet>,
        )],
        value_space: &std::collections::HashMap<NodeId, NodeValueSpace>,
        ranges_by_node: &std::collections::HashMap<
            NodeId,
            Vec<(LiteralDataRange, crate::tableau::dependency_set::PermanentDependencySet)>,
        >,
        empty: &crate::tableau::dependency_set::PermanentDependencySet,
    ) -> bool {
        use std::collections::HashMap;
        type Dep = crate::tableau::dependency_set::PermanentDependencySet;

        let n = nodes.len();
        let index: HashMap<NodeId, usize> = nodes.iter().enumerate().map(|(i, &m)| (m, i)).collect();
        // Adjacency (deduplicated) among the component's nodes, plus the
        // dependency sets that induced each edge (for the clash dependency set).
        let mut adjacency: Vec<std::collections::BTreeSet<usize>> =
            vec![std::collections::BTreeSet::new(); n];
        let mut edge_deps: Vec<Dep> = Vec::new();
        for (a, b, deps) in component_edges {
            if let (Some(&ia), Some(&ib)) = (index.get(a), index.get(b)) {
                if ia != ib && adjacency[ia].insert(ib) {
                    adjacency[ib].insert(ia);
                    edge_deps.extend(deps.iter().cloned());
                }
            }
        }

        // The clash dependency set: every node's ranges and every distinctness
        // edge that shaped the (sub)component. (HermiT folds the same set.)
        let clash_dep = |slf: &Tableau| -> DependencySet {
            let mut all: Vec<Dep> = Vec::new();
            for m in nodes {
                for (_, d) in ranges_by_node.get(m).into_iter().flatten() {
                    all.push(d.clone());
                }
            }
            all.extend(edge_deps.iter().cloned());
            let mut dep = DependencySet::Permanent(empty.clone());
            for d in &all {
                let mut union = crate::tableau::dependency_set::UnionDependencySet::new(2);
                union.add_constituent(dep);
                union.add_constituent(DependencySet::Permanent(d.clone()));
                dep = DependencySet::Union(union);
            }
            let _ = slf;
            dep
        };

        // Build the per-node value spaces in `nodes` order and the symmetric
        // adjacency (as `Vec`s), then run the pure decision.
        let infinite = NodeValueSpace::Infinite;
        let spaces: Vec<&NodeValueSpace> = nodes
            .iter()
            .map(|m| value_space.get(m).unwrap_or(&infinite))
            .collect();
        let adjacency_vec: Vec<Vec<usize>> =
            adjacency.iter().map(|s| s.iter().copied().collect()).collect();
        // The most-specific datatype URI per node, mirroring a HermiT
        // DVariable's `m_mostSpecificRestriction` (DatatypeChecker.java:371-385).
        // `eliminateTrivialInequalities` uses these to drop edges between nodes
        // whose most-specific restrictions are disjoint datatypes.
        let most_specific: Vec<Option<String>> = nodes
            .iter()
            .map(|m| {
                ranges_by_node
                    .get(m)
                    .map(|r| most_specific_datatype_uri(r))
                    .unwrap_or(None)
            })
            .collect();
        let most_specific_refs: Vec<Option<&str>> =
            most_specific.iter().map(|o| o.as_deref()).collect();

        // CHK-3: for each node whose value space is finite-but-unmaterialized,
        // enumerate its canonical distinct values (bounded by the cap) so the
        // backtracking assignment search can run over them, mirroring Java's
        // enumerateValueSpaceSubset().
        let materialized: Vec<Option<Vec<DataValue>>> = nodes
            .iter()
            .map(|m| match value_space.get(m) {
                Some(NodeValueSpace::Finite { values: None, .. }) => ranges_by_node
                    .get(m)
                    .and_then(|r| materialize_finite_value_space(r, MAX_ENUMERATED_VALUES)),
                _ => None,
            })
            .collect();

        if component_is_unsatisfiable(&spaces, &adjacency_vec, &most_specific_refs, &materialized) {
            let dep = clash_dep(self);
            self.set_clash(&dep);
            return true;
        }
        false
    }

    fn node_data_ranges(
        &self,
        node: NodeId,
    ) -> Vec<(LiteralDataRange, crate::tableau::dependency_set::PermanentDependencySet)> {
        let retrieval =
            self.create_binary_retrieval([-1, 1], [None, Some(TableauObject::Node(node))], View::Total);
        let empty = self.dependency_set_factory.empty_set();
        let mut ranges = Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            let label = self.binary_extension_table.get_tuple_object(tuple_index, 0);
            if let Some(range) = label_as_literal_data_range(label) {
                // Internal datatypes are skipped, as they do not contribute to
                // datatype checking (they encode rdfs:Literal, datatype
                // definitions and complex-data-range renamings). Java:
                // DatatypeChecker.DVariable.addDataRange explicitly ignores
                // InternalDatatype (DatatypeChecker.java:372-375,392-394), so it
                // contributes neither to the conjunction emptiness check nor to
                // any clash dependency set.
                if matches!(range, LiteralDataRange::InternalDatatype(_)) {
                    continue;
                }
                ranges.push((
                    range,
                    self.binary_extension_table.get_dependency_set(tuple_index, &empty),
                ));
            }
        }
        ranges
    }

    /// Port of `DatatypeManager.applyUnknownDatatypeRestrictionSemantics`
    /// (DatatypeManager.java:102-123). In the NON-default
    /// `ignoreUnsupportedDatatypes` mode each unsupported datatype restriction `D`
    /// is modelled as a fresh *infinite* value space; HermiT keeps the value space
    /// of `D` and of `¬D` disjoint by forcing apart every pair of nodes asserting
    /// one of `D`/`¬D` and the matching opposite. This phase walks the data-range
    /// assertions and, for an unknown `D` (resp. `¬D`), emits an inequality to
    /// every node carrying the opposite range.
    ///
    /// Faithfulness note: Java iterates only the *delta-old* slice of newly-added
    /// assertions; we scan the TOTAL view (a superset), which is sound and
    /// answer-identical because `Inequality` assertions are idempotent in the
    /// extension table -- exactly as `check_datatype_constraints` already scans
    /// TOTAL rather than delta-old. Gated by `check_unknown_datatype_restrictions`
    /// (only ever set under `ignoreUnsupportedDatatypes`), so the default path
    /// never enters here.
    pub fn apply_unknown_datatype_restriction_semantics(&mut self) {
        // Collect the (source range, node, dep, opposite range) work items first,
        // so the mutating `generate_inequalities_for` does not borrow the table
        // across the read. Java reads from delta-old (a stable slice); collecting
        // into a Vec gives the same stable snapshot.
        let empty = self.dependency_set_factory.empty_set();
        let mut work: Vec<(
            NodeId,
            crate::tableau::dependency_set::PermanentDependencySet,
            LiteralDataRange,
        )> = Vec::new();
        let retrieval =
            self.create_binary_retrieval([-1, -1], [None, None], View::Total);
        for &tuple_index in &retrieval.tuple_indices {
            let label = self.binary_extension_table.get_tuple_object(tuple_index, 0);
            let node = match self.binary_extension_table.get_tuple_object(tuple_index, 1).as_node() {
                Some(n) => n,
                None => continue,
            };
            let dep = self.binary_extension_table.get_dependency_set(tuple_index, &empty);
            match label_as_literal_data_range(label) {
                // A positive unknown restriction `D`: force apart from every `¬D`.
                Some(LiteralDataRange::DatatypeRestriction(r))
                    if self.unknown_datatype_restrictions.contains(&r) =>
                {
                    work.push((node, dep, r.get_negation()));
                }
                // A negated unknown restriction `¬D`: force apart from every `D`.
                Some(LiteralDataRange::AtomicNegationDataRange(n)) => {
                    if let crate::model::AtomicDataRange::DatatypeRestriction(r) =
                        n.get_negated_data_range()
                    {
                        if self.unknown_datatype_restrictions.contains(r) {
                            work.push((
                                node,
                                dep,
                                LiteralDataRange::DatatypeRestriction(r.clone()),
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
        for (node1, dep1, opposite) in work {
            if self.contains_clash() {
                break;
            }
            self.generate_inequalities_for(node1, &dep1, opposite);
        }
    }

    /// Port of `DatatypeManager.generateInequalitiesFor`
    /// (DatatypeManager.java:124-141): adds `Inequality(node1, node2)` for every
    /// node `node2` asserting `data_range2`, with the union of the source
    /// assertion's dependency set (`dep1`) and the `data_range2` assertion's
    /// dependency set (matching Java's `m_unionDependencySet` of the two
    /// constituents). The original (positive) range that induced this call only
    /// shapes the monitor event in Java; the assertion semantics depend solely on
    /// `node1`, `data_range2`, and the two dependency sets, so it is not needed.
    fn generate_inequalities_for(
        &mut self,
        node1: NodeId,
        dep1: &crate::tableau::dependency_set::PermanentDependencySet,
        data_range2: LiteralDataRange,
    ) {
        use crate::model::DLPredicate;
        let empty = self.dependency_set_factory.empty_set();
        let label2 = TableauObject::DLPredicate(match data_range2 {
            LiteralDataRange::DatatypeRestriction(r) => DLPredicate::DatatypeRestriction(r),
            LiteralDataRange::ConstantEnumeration(r) => DLPredicate::ConstantEnumeration(r),
            LiteralDataRange::InternalDatatype(r) => DLPredicate::InternalDatatype(r),
            LiteralDataRange::AtomicNegationDataRange(r) => {
                DLPredicate::AtomicNegationDataRange(r)
            }
        });
        // All nodes carrying `data_range2` (Java's m_assertions0Retrieval bound on
        // the data range in position 0), with their assertion dependency sets.
        let retrieval =
            self.create_binary_retrieval([0, -1], [Some(label2), None], View::Total);
        let mut targets: Vec<(NodeId, crate::tableau::dependency_set::PermanentDependencySet)> =
            Vec::new();
        for &tuple_index in &retrieval.tuple_indices {
            if let Some(node2) =
                self.binary_extension_table.get_tuple_object(tuple_index, 1).as_node()
            {
                targets.push((
                    node2,
                    self.binary_extension_table.get_dependency_set(tuple_index, &empty),
                ));
            }
        }
        for (node2, dep2) in targets {
            // m_unionDependencySet = { dep1, dep2 } (DatatypeManager.java:126-133).
            let mut union = crate::tableau::dependency_set::UnionDependencySet::new(2);
            union.add_constituent(DependencySet::Permanent(dep1.clone()));
            union.add_constituent(DependencySet::Permanent(dep2));
            let dep = DependencySet::Union(union);
            // addAssertion(Inequality.INSTANCE, node1, node2, dep, false), bracketed
            // by the unknownDatatypeRestrictionDetection monitor events.
            self.monitor_event(|m| m.unknown_datatype_restriction_detection_started());
            self.add_ternary(
                TableauObject::DLPredicate(DLPredicate::Inequality),
                node1,
                node2,
                &dep,
                false,
            );
            self.monitor_event(|m| m.unknown_datatype_restriction_detection_finished());
        }
    }
}

/// The pure, complete decision for one connected component of mutually-distinct
/// data nodes: given each node's value space (in a fixed order) and the
/// symmetric distinctness adjacency over those indices, returns whether the
/// component is *unsatisfiable* (no pairwise-distinct assignment exists). This
/// is the algorithmic core, mirroring
/// `DatatypeChecker.getUnsatisfiabilityCauseOrCauses`:
///   1. **Symmetric clique** (every node distinct from every other, all sharing
///      the same value space) — `isSymmetricClique` + `hasCardinalityAtLeast`:
///      unsatisfiable iff the shared value-space cardinality is below the clique
///      size. This decides the pigeonhole clashes (≥13 distinct booleans, N+1
///      distinct nodes over an N-value range) with no enumeration.
///   2. Otherwise, **eliminate trivially-satisfiable variables** to a fixpoint —
///      `eliminateTriviallySatisfiableVariables`: a node whose cardinality is at
///      least its residual degree + 1 (which includes every infinite value
///      space) can always be assigned a distinct value, so it is removed and its
///      neighbours' degrees decremented.
///   3. The survivors then have a finite value space strictly below their
///      residual degree + 1 (hence ≤ the surviving component size), so
///      enumerating them and running the inequality-aware backtracking
///      assignment (`findAssignment`, smallest-set-first) is bounded and exact.
///
/// CHK-3: materializes up to `cap` canonical, mutually-distinct values for a
/// node's finite value space when its `NodeValueSpace` did not already carry an
/// explicit list. Mirrors Java's `enumerateValueSpaceSubset()` (DatatypeChecker.java:505),
/// which turns a value-space subset into explicit data values for the assignment
/// search. Returns `Some(values)` (possibly empty ⇒ empty value space ⇒ clash) for
/// the families whose distinct values the Rust `DataValue` model can represent —
/// length-bounded `xsd:string` (distinct `Text` values). Returns `None` for
/// families whose distinct values this model collapses (datetime instants, where
/// the timezone-shifted points are not separately representable) or otherwise
/// cannot be enumerated, so the caller stays sound.
fn materialize_finite_value_space<D>(
    ranges: &[(LiteralDataRange, D)],
    cap: usize,
) -> Option<Vec<DataValue>> {
    let restrictions: Vec<&DatatypeRestriction> = ranges
        .iter()
        .filter_map(|(r, _)| match r {
            LiteralDataRange::DatatypeRestriction(r) => Some(r),
            _ => None,
        })
        .collect();
    if restrictions.is_empty() {
        return None;
    }
    let excluded = |candidate: &DataValue| {
        ranges.iter().any(|(r, _)| value_in_range(candidate, r) == Some(false))
    };

    // Length-bounded xsd:string: distinct strings of the allowed lengths over a
    // fixed ASCII alphabet. The actual value space is over the whole Unicode
    // character set, so this materialized prefix is a faithful (canonical) subset
    // of distinct values; enumerating up to `cap` of them is enough because a
    // survivor's needed cardinality is ≤ its degree (small).
    if restrictions.iter().all(|r| is_string_datatype(r.datatype_uri()))
        && restrictions.iter().all(|r| length_intervals_for(r).is_some())
    {
        let mut absent: Option<LengthInterval> = None;
        let mut has_present = false;
        for r in &restrictions {
            let (p, a) = length_intervals_for(r)?;
            if p.is_some() {
                has_present = true;
            }
            absent = match (absent, a) {
                (None, a) => a,
                (Some(old), Some(new_iv)) => old.intersect(new_iv),
                (Some(old), None) => Some(old),
            };
        }
        if has_present {
            return None; // rdf:PlainLiteral PRESENT mode is infinite
        }
        let Some(iv) = absent else {
            return Some(Vec::new()); // empty length window ⇒ empty value space
        };
        let max = iv.max_length?; // unbounded ⇒ infinite, not materializable
        let alphabet: Vec<char> = ('a'..='z').chain('A'..='Z').chain('0'..='9').collect();
        let mut out: Vec<DataValue> = Vec::new();
        let mut frontier: Vec<String> = vec![String::new()];
        for l in 0..=max {
            if l >= iv.min_length {
                for s in &frontier {
                    let candidate = DataValue::Text(s.clone());
                    if !excluded(&candidate) {
                        out.push(candidate);
                        if out.len() >= cap {
                            return Some(out);
                        }
                    }
                }
            }
            if l == max {
                break;
            }
            let mut next = Vec::with_capacity(frontier.len() * alphabet.len());
            for s in &frontier {
                for &ch in &alphabet {
                    let mut t = s.clone();
                    t.push(ch);
                    next.push(t);
                    if next.len() > cap {
                        break;
                    }
                }
            }
            frontier = next;
        }
        return Some(out);
    }

    None
}

/// No component is skipped for size and no infinite node is dropped.
fn component_is_unsatisfiable(
    spaces: &[&NodeValueSpace],
    adjacency: &[Vec<usize>],
    most_specific: &[Option<&str>],
    // CHK-3: per-node materialized value lists for finite value spaces whose
    // `NodeValueSpace` did not carry an explicit list (length-strings, etc.).
    // Java's `enumerateValueSpaceSubset()` materializes these before the
    // assignment search; this parallel array supplies the same explicit values
    // (bounded by a cap) so the backtracking search can run over them. An empty
    // slice means "nothing pre-materialized" (used by unit tests).
    materialized: &[Option<Vec<DataValue>>],
) -> bool {
    use std::collections::HashMap;
    let n = spaces.len();
    if n == 0 {
        return false;
    }
    let cardinality = |i: usize| -> Cardinality {
        match spaces[i] {
            NodeValueSpace::Finite { count, .. } => Cardinality::Finite(*count),
            NodeValueSpace::Infinite => Cardinality::Infinite,
        }
    };

    // --- 1. Symmetric-clique shortcut.
    // `DatatypeChecker.getUnsatisfiabilityCauseOrCauses` takes the clique branch
    // BEFORE `eliminateTrivialInequalities`, so the full adjacency is used here.
    let is_clique = (0..n).all(|i| adjacency[i].len() == n - 1);
    if is_clique {
        let same_value_space =
            (1..n).all(|i| node_value_spaces_equal(Some(spaces[0]), Some(spaces[i])));
        if same_value_space {
            return match cardinality(0) {
                Cardinality::Finite(c) => (c as usize) < n,
                Cardinality::Infinite => false,
            };
        }
    }

    // --- 1b. eliminateTrivialInequalities (DatatypeChecker.java:185-200): remove
    // every inequality edge between two nodes whose most-specific datatype
    // restrictions are disjoint datatypes — such nodes are automatically distinct,
    // so the edge cannot contribute to a clash and must not inflate node degree.
    let mut adjacency: Vec<std::collections::BTreeSet<usize>> =
        adjacency.iter().map(|a| a.iter().copied().collect()).collect();
    for i in 0..n {
        let Some(uri_i) = most_specific[i] else {
            continue;
        };
        let neighbors: Vec<usize> = adjacency[i].iter().copied().collect();
        for j in neighbors {
            if let Some(uri_j) = most_specific[j] {
                if datatypes_disjoint(uri_i, uri_j) {
                    adjacency[i].remove(&j);
                    adjacency[j].remove(&i);
                }
            }
        }
    }
    let adjacency: Vec<Vec<usize>> =
        adjacency.iter().map(|a| a.iter().copied().collect()).collect();
    let adjacency = &adjacency;

    // --- 2. Eliminate trivially-satisfiable variables to a fixpoint.
    let mut alive = vec![true; n];
    let mut degree: Vec<usize> = (0..n).map(|i| adjacency[i].len()).collect();
    let mut queue: Vec<usize> = (0..n).collect();
    while let Some(i) = queue.pop() {
        if !alive[i] {
            continue;
        }
        // `hasCardinalityAtLeast(degree + 1)`: at least one value per neighbour
        // plus one for the node itself, i.e. cardinality strictly exceeds degree.
        let enough = match cardinality(i) {
            Cardinality::Infinite => true,
            Cardinality::Finite(c) => c as usize > degree[i],
        };
        if enough {
            alive[i] = false;
            for &j in &adjacency[i] {
                if alive[j] {
                    degree[j] -= 1;
                    if !queue.contains(&j) {
                        queue.push(j);
                    }
                }
            }
        }
    }
    let survivors: Vec<usize> = (0..n).filter(|&i| alive[i]).collect();
    if survivors.is_empty() {
        return false;
    }

    // --- 3. Enumerate (materialize) the survivors' value spaces.
    // DatatypeChecker.enumerateValueSpaceSubsets (DatatypeChecker.java:220-227):
    // each survivor's value-space subset is turned into an explicit list of data
    // values; a survivor that enumerates to the empty set is itself the clash.
    // CHK-3: a finite value space not materialized at construction (length-strings,
    // etc.) is supplied here via the parallel `materialized` array.
    let mut explicit: Vec<Option<Vec<DataValue>>> = vec![None; n];
    for &i in &survivors {
        match spaces[i] {
            NodeValueSpace::Finite { values: Some(vals), .. } => {
                explicit[i] = Some(vals.clone());
            }
            NodeValueSpace::Finite { values: None, .. } => {
                match materialized.get(i).and_then(|m| m.clone()) {
                    // An empty enumeration ⇒ empty value space ⇒ the component
                    // clashes (Java: enumerateValueSpaceSubset returns false ⇒
                    // getUnsatisfiabilityCauseOrCauses returns the variable).
                    Some(vals) if vals.is_empty() => return true,
                    Some(vals) => explicit[i] = Some(vals),
                    // A finite value space we could not materialize: stay sound.
                    None => return false,
                }
            }
            // An infinite survivor cannot occur after elimination; stay sound.
            NodeValueSpace::Infinite => return false,
        }
    }

    // --- 4. eliminateTriviallySatisfiableVariables AGAIN (CHK-2,
    // DatatypeChecker.java:178): after enumeration some variables may now have a
    // value-set large enough to dominate their residual degree, so re-run the
    // elimination to a fixpoint over the (newly materialized) cardinalities.
    let card_after = |i: usize, explicit: &[Option<Vec<DataValue>>]| -> usize {
        explicit[i].as_ref().map_or(0, |v| v.len())
    };
    let mut queue2: Vec<usize> = survivors.clone();
    while let Some(i) = queue2.pop() {
        if !alive[i] {
            continue;
        }
        if card_after(i, &explicit) > degree[i] {
            alive[i] = false;
            for &j in &adjacency[i] {
                if alive[j] {
                    degree[j] -= 1;
                    if !queue2.contains(&j) {
                        queue2.push(j);
                    }
                }
            }
        }
    }
    let survivors: Vec<usize> = (0..n).filter(|&i| alive[i]).collect();
    if survivors.is_empty() {
        return false;
    }

    // --- 5. Backtracking distinct-assignment search over the survivors
    // (DatatypeChecker.checkAssignments / findAssignment, smallest-set-first).
    let candidate_sets: Vec<Vec<DataValue>> = survivors
        .iter()
        .map(|&i| explicit[i].clone().unwrap_or_default())
        .collect();
    let pos: HashMap<usize, usize> =
        survivors.iter().enumerate().map(|(k, &i)| (i, k)).collect();
    let mut radjacent: Vec<Vec<usize>> = vec![Vec::new(); survivors.len()];
    for (k, &i) in survivors.iter().enumerate() {
        for &j in &adjacency[i] {
            if let Some(&kj) = pos.get(&j) {
                radjacent[k].push(kj);
            }
        }
    }
    // Smallest candidate set first (HermiT's SmallestEnumerationFirst).
    let mut order: Vec<usize> = (0..survivors.len()).collect();
    order.sort_by_key(|&k| candidate_sets[k].len());

    fn search(
        position: usize,
        order: &[usize],
        candidate_sets: &[Vec<DataValue>],
        radjacent: &[Vec<usize>],
        chosen: &mut [Option<DataValue>],
    ) -> bool {
        if position == order.len() {
            return true;
        }
        let k = order[position];
        'next: for value in &candidate_sets[k] {
            for &nb in &radjacent[k] {
                if let Some(other) = &chosen[nb] {
                    if values_equal(value, other) {
                        continue 'next;
                    }
                }
            }
            chosen[k] = Some(value.clone());
            if search(position + 1, order, candidate_sets, radjacent, chosen) {
                return true;
            }
            chosen[k] = None;
        }
        false
    }
    let mut chosen: Vec<Option<DataValue>> = vec![None; survivors.len()];
    !search(0, &order, &candidate_sets, &radjacent, &mut chosen)
}

/// A datatype's *value-space class*: the (facet-free) set of values its base
/// datatype denotes, classified so that a positive-vs-negated subset test can be
/// decided without enumeration. This mirrors how Java's `OWLRealDatatypeHandler`
/// keeps a `NumberRange` (`INTEGER ⊂ DECIMAL ⊂ RATIONAL ⊂ REAL`) per numeric
/// datatype and how the other handlers each own a *disjoint* value space.
///
/// The `Numeric` variant carries the position in the `owl:real` lattice; the
/// rest are mutually-disjoint kinds. `IntegerBounded` records a derived integer
/// type's implicit `[min, max]` window (over the integer line) so that e.g.
/// `xsd:byte`'s value space is recognized as a subset of `xsd:integer`'s.
#[derive(Clone, PartialEq, Debug)]
enum ValueSpaceClass {
    /// A point of the `owl:real` lattice: 0 = integer, 1 = decimal,
    /// 2 = rational, 3 = real (`real` is the superset of all the numeric kinds).
    Numeric(u8),
    /// A derived integer type carving out `[min, max]` of the integer line
    /// (`None` = unbounded on that side). Plain `xsd:integer` is `(None, None)`.
    IntegerBounded(Option<i128>, Option<i128>),
    /// `xsd:float` and `xsd:double` are value spaces of their own, disjoint from
    /// `owl:real` and from each other.
    Float,
    Double,
    Boolean,
    /// A string-hierarchy type mirroring Java's `s_datatypeSupersets` levels:
    /// 0=rdf:PlainLiteral, 1=xsd:string, 2=normalizedString, 3=token,
    /// 4=Name, 5=NCName, 6=NMTOKEN, 7=language.
    /// `value_space_is_subset` uses these levels to reproduce `isSubsetOf`.
    StringType(u8),
    DateTime,
    AnyUri,
    HexBinary,
    Base64,
    XmlLiteral,
}

/// The value-space class of an atomic datatype URI, or `None` when it is not a
/// recognized datatype.
fn value_space_class(uri: &str) -> Option<ValueSpaceClass> {
    if let Some(bounds) = integer_datatype_bounds(uri) {
        // `xsd:integer` itself is the whole integer line; a derived integer type
        // is a sub-window of it.
        return Some(match bounds {
            (None, None) => ValueSpaceClass::Numeric(0),
            (min, max) => ValueSpaceClass::IntegerBounded(min, max),
        });
    }
    if is_decimal_datatype(uri) {
        return Some(ValueSpaceClass::Numeric(1));
    }
    if is_rational_datatype(uri) {
        return Some(ValueSpaceClass::Numeric(2));
    }
    if is_real_datatype(uri) {
        return Some(ValueSpaceClass::Numeric(3));
    }
    if is_xsd_float(uri) {
        return Some(ValueSpaceClass::Float);
    }
    if is_xsd_double(uri) {
        return Some(ValueSpaceClass::Double);
    }
    if is_boolean_datatype(uri) {
        return Some(ValueSpaceClass::Boolean);
    }
    if is_string_datatype(uri) {
        // Assign s_datatypeSupersets level (Java RDFPlainLiteralDatatypeHandler:51-69).
        let level: u8 = match uri.strip_prefix(XSD) {
            Some("string") => 1,
            Some("normalizedString") => 2,
            Some("token") => 3,
            Some("Name") => 4,
            Some("NCName") => 5,
            Some("NMTOKEN") => 6,
            Some("language") => 7,
            _ => 0, // rdf:PlainLiteral
        };
        return Some(ValueSpaceClass::StringType(level));
    }
    if is_datetime_datatype(uri) {
        return Some(ValueSpaceClass::DateTime);
    }
    if is_anyuri_datatype(uri) {
        return Some(ValueSpaceClass::AnyUri);
    }
    if is_hex_binary_datatype(uri) {
        return Some(ValueSpaceClass::HexBinary);
    }
    if is_base64_datatype(uri) {
        return Some(ValueSpaceClass::Base64);
    }
    if is_xml_literal_datatype(uri) {
        return Some(ValueSpaceClass::XmlLiteral);
    }
    None
}

/// Whether every value of the (facet-free) value-space class `sub` is also a
/// value of `sup` — i.e. `sub`'s value space ⊆ `sup`'s value space. This is the
/// subsumption the negated-range emptiness test needs: `A ⊓ ¬B` is empty when
/// `A`'s value space ⊆ `B`'s. The `owl:real` lattice is ordered
/// (`integer ⊂ decimal ⊂ rational ⊂ real`); a bounded derived integer type is a
/// subset of any numeric class at integer level or above; the float/double and
/// the non-numeric kinds are pairwise disjoint, so a subset only when identical.
fn value_space_is_subset(sub: &ValueSpaceClass, sup: &ValueSpaceClass) -> bool {
    use ValueSpaceClass::*;
    match (sub, sup) {
        // Numeric lattice: integer(0) ⊂ decimal(1) ⊂ rational(2) ⊂ real(3).
        (Numeric(a), Numeric(b)) => a <= b,
        // A bounded integer window is a subset of any numeric class (it is a
        // subset of the integers, which are a subset of every numeric kind),
        // and of a wider/equal integer window.
        (IntegerBounded(_, _), Numeric(_)) => true,
        (IntegerBounded(amin, amax), IntegerBounded(bmin, bmax)) => {
            // [amin,amax] ⊆ [bmin,bmax]: b's lower bound is no greater, b's upper
            // no smaller (None = unbounded).
            let lower_ok = match (bmin, amin) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some(b), Some(a)) => a >= b,
            };
            let upper_ok = match (bmax, amax) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some(b), Some(a)) => a <= b,
            };
            lower_ok && upper_ok
        }
        // Plain xsd:integer (Numeric(0)) is a subset of a derived integer window
        // only if that window is unbounded (i.e. is integer itself) — handled by
        // the Numeric/Numeric arm.
        // String hierarchy: Java RDFPlainLiteralDatatypeHandler.isSubsetOf (line 339-342)
        // returns s_datatypeSupersets[sub].contains(sup). Levels 0..=3 are a total
        // chain (higher = more restricted); levels 4..=7 branch off token(3) and are
        // not subsets of each other, except NCName(5) ⊆ Name(4).
        (StringType(a), StringType(b)) => {
            if a == b {
                return true;
            }
            if *b <= 3 {
                return a > b; // sub is more restricted than sup in the linear chain
            }
            // sup is a branch level (4..=7): the only proper sub-branch is NCName(5) ⊆ Name(4).
            *a == 5 && *b == 4
        }
        // Otherwise the disjoint/identical kinds:
        _ => sub == sup,
    }
}

/// Replicates the most-specific-restriction tracking of
/// `DatatypeChecker.DVariable.addDataRange` (DatatypeChecker.java:371-385) over a
/// node's positive datatype-restriction ranges (in assertion order; the
/// InternalDatatype ranges are already filtered out by `node_data_ranges`),
/// returning the dependency sets of the `(clashingRestriction, datatypeRestriction)`
/// pair the first time an added restriction's datatype is disjoint with the
/// running most-specific restriction's datatype. `None` when no such directly
/// disjoint pair exists. Mirrors:
///   * `m_mostSpecificRestriction` starts at the first positive restriction;
///   * a later restriction disjoint with it clashes (returns the pair);
///   * a later restriction that is a subset of it refines it.
fn disjoint_datatype_pair_deps<D: Clone>(
    ranges: &[(LiteralDataRange, D)],
) -> Option<(D, D)> {
    let mut most_specific: Option<(&str, D)> = None;
    for (range, dep) in ranges {
        let LiteralDataRange::DatatypeRestriction(r) = range else {
            continue;
        };
        let uri = r.datatype_uri();
        match &most_specific {
            None => most_specific = Some((uri, dep.clone())),
            Some((ms_uri, ms_dep)) => {
                if datatypes_disjoint(ms_uri, uri) {
                    return Some((ms_dep.clone(), dep.clone()));
                } else if let (Some(sub), Some(sup)) =
                    (value_space_class(uri), value_space_class(ms_uri))
                {
                    if value_space_is_subset(&sub, &sup) {
                        most_specific = Some((uri, dep.clone()));
                    }
                }
            }
        }
    }
    None
}

/// The most-specific datatype URI of a node's positive datatype-restriction
/// ranges, mirroring how `DatatypeChecker.DVariable.addDataRange`
/// (DatatypeChecker.java:371-385) maintains `m_mostSpecificRestriction`: it
/// starts at the first positive restriction and is refined to any later
/// restriction whose datatype is a subset of the current one. Returns `None`
/// when the node has no positive datatype restriction (InternalDatatype ranges
/// are already filtered out by `node_data_ranges`). If a disjoint pair is
/// encountered the variable would already have clashed in the per-node check, so
/// the running most-specific restriction is left unchanged.
fn most_specific_datatype_uri<D>(ranges: &[(LiteralDataRange, D)]) -> Option<String> {
    let mut most_specific: Option<String> = None;
    for (range, _) in ranges {
        let LiteralDataRange::DatatypeRestriction(r) = range else {
            continue;
        };
        let uri = r.datatype_uri();
        match &most_specific {
            None => most_specific = Some(uri.to_string()),
            Some(ms_uri) => {
                if datatypes_disjoint(ms_uri, uri) {
                    // Disjoint: addDataRange returns clashingRestriction and leaves
                    // m_mostSpecificRestriction unchanged.
                } else if let (Some(sub), Some(sup)) =
                    (value_space_class(uri), value_space_class(ms_uri))
                {
                    if value_space_is_subset(&sub, &sup) {
                        most_specific = Some(uri.to_string());
                    }
                }
            }
        }
    }
    most_specific
}

/// Port of `DatatypeRegistry.isDisjointWith(uri1, uri2)`
/// (DatatypeRegistry.java:119-125): two datatype URIs handled by *different*
/// handlers (different value-space kinds) are always disjoint; within the same
/// handler the per-handler `isDisjointWith` decides:
///   * owl:real (OWLRealDatatypeHandler.java:279-283): disjoint iff the base
///     `NumberInterval`s do not intersect — i.e. both are bounded integer
///     windows whose `[min,max]` ranges do not overlap (the dense decimal /
///     rational / real spaces and the unbounded integer line span the whole
///     real line, so they are never disjoint from any numeric kind);
///   * binary (BinaryDataDatatypeHandler.java:186-188): disjoint iff different
///     URI (hexBinary vs base64Binary);
///   * strings (RDFPlainLiteralDatatypeHandler.java:344-348): never disjoint;
///   * float / double / dateTime: never disjoint (single member each).
/// Unrecognized datatype URIs are treated conservatively as NOT disjoint.
fn datatypes_disjoint(uri1: &str, uri2: &str) -> bool {
    let (Some(c1), Some(c2)) = (value_space_class(uri1), value_space_class(uri2)) else {
        return false;
    };
    use ValueSpaceClass::*;
    // Numeric (owl:real) handler covers all owl:real-derived kinds.
    let is_real_kind = |c: &ValueSpaceClass| matches!(c, Numeric(_) | IntegerBounded(_, _));
    if is_real_kind(&c1) && is_real_kind(&c2) {
        // Both numeric: disjoint iff their base intervals do not intersect.
        // Only bounded integer windows can be disjoint; everything else spans
        // the whole real line.
        match (c1, c2) {
            (IntegerBounded(amin, amax), IntegerBounded(bmin, bmax)) => {
                // Intervals [amin,amax] and [bmin,bmax] (None = unbounded).
                let a_below_b = match (amax, bmin) {
                    (Some(am), Some(bm)) => am < bm,
                    _ => false,
                };
                let b_below_a = match (bmax, amin) {
                    (Some(bm), Some(am)) => bm < am,
                    _ => false,
                };
                a_below_b || b_below_a
            }
            _ => false,
        }
    } else if matches!(c1, HexBinary | Base64) && matches!(c2, HexBinary | Base64) {
        c1 != c2
    } else if matches!(c1, StringType(_)) && matches!(c2, StringType(_)) {
        false
    } else {
        // Different handlers / kinds ⇒ disjoint; identical singular kinds ⇒ not.
        c1 != c2
    }
}

// ===========================================================================
// owl:real value-space lattice (faithful port of org.semanticweb.HermiT.
// datatypes.owlreal.{NumberRange, NumberInterval, OWLRealValueSpaceSubset,
// OWLRealDatatypeHandler}). This decides numeric conjunction emptiness and
// exact cardinality over the whole owl:real lattice, INCLUDING facet-restricted
// negation subsumption (e.g. `integer[≥0] ⊓ ¬integer[≥-5]` empty) and exact
// cardinality of a huge bounded interval that also carries value-removing
// exclusions (a negated interval/enumeration). Bounds are exact `(num, den)`
// rationals (or ±infinity) so the decision is exact.
// ===========================================================================

/// `NumberRange` (NOTHING ⊂ INTEGER ⊂ DECIMAL ⊂ RATIONAL ⊂ REAL), by ordinal.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum NumRange {
    Nothing = 0,
    Integer = 1,
    Decimal = 2,
    Rational = 3,
    Real = 4,
}

impl NumRange {
    /// `NumberRange.isDense`: dense iff ordinal ≥ DECIMAL.
    fn is_dense(self) -> bool {
        self >= NumRange::Decimal
    }
    /// `NumberRange.intersection`: the min ordinal.
    fn intersection(a: NumRange, b: NumRange) -> NumRange {
        a.min(b)
    }
    /// `NumberRange.union`: the max ordinal.
    fn union(a: NumRange, b: NumRange) -> NumRange {
        a.max(b)
    }
    /// `NumberRange.isSubsetOf`: ordinal ≤.
    fn is_subset_of(sub: NumRange, sup: NumRange) -> bool {
        (sub as u8) <= (sup as u8)
    }
    /// The base `NumberRange` of a numeric datatype URI, or `None` when the URI
    /// is not a numeric (owl:real-derived) datatype.
    fn base_of(uri: &str) -> Option<NumRange> {
        if is_integer_datatype(uri) {
            Some(NumRange::Integer)
        } else if is_decimal_datatype(uri) {
            Some(NumRange::Decimal)
        } else if is_rational_datatype(uri) {
            Some(NumRange::Rational)
        } else if is_real_datatype(uri) {
            Some(NumRange::Real)
        } else {
            None
        }
    }
}

/// `NumberRange.getMostSpecificRange(number)`: the most specific range a given
/// exact rational belongs to. Java distinguishes by runtime type — `BigInteger`
/// ⇒ INTEGER, `BigDecimal` ⇒ DECIMAL, `BigRational` ⇒ RATIONAL — and
/// `Numbers.parseRational` only ever yields a `BigRational` when the value has
/// NO finite decimal form (its exact `BigDecimal` division throws
/// `ArithmeticException`; Numbers.java:117-122). Since our `(num, den)` carries
/// no origin tag, we recover the same three-way split mathematically: INTEGER
/// when den == 1; DECIMAL when the reduced denominator is 2^a·5^b (a finite
/// decimal, i.e. exactly what a `BigDecimal` can represent); RATIONAL otherwise.
/// This matters for the singleton-emptiness test in `is_empty`: e.g.
/// `xsd:decimal[minInclusive 1/3, maxInclusive 1/3]` is EMPTY because 1/3 is not
/// in the DECIMAL value space — `isSubsetOf(RATIONAL, DECIMAL)` is false.
fn most_specific_range(value: &(BigInt, BigInt)) -> NumRange {
    if value.1.is_one() {
        return NumRange::Integer;
    }
    // Strip the 2 and 5 factors from the (already reduced) denominator; if what
    // remains is 1 the value has a finite decimal expansion (DECIMAL), otherwise
    // it is a non-decimal rational (RATIONAL). Mirrors Java's BigDecimal-vs-
    // BigRational distinction.
    let mut d = value.1.clone();
    if d.is_negative() {
        d = -d;
    }
    let two = BigInt::from(2);
    let five = BigInt::from(5);
    while !d.is_zero() && (&d % &two).is_zero() {
        d /= &two;
    }
    while !d.is_zero() && (&d % &five).is_zero() {
        d /= &five;
    }
    if d.is_one() {
        NumRange::Decimal
    } else {
        NumRange::Rational
    }
}

/// A bound endpoint: −∞, an exact rational, or +∞. Mirrors HermiT's
/// `MinusInfinity` / `Number` / `PlusInfinity`.
#[derive(Clone, PartialEq, Debug)]
enum NumBound {
    MinusInf,
    Finite(BigInt, BigInt),
    PlusInf,
}

impl NumBound {
    /// `Numbers.compare`, lifted to include ±∞.
    fn compare(&self, other: &NumBound) -> std::cmp::Ordering {
        use std::cmp::Ordering::*;
        use NumBound::*;
        match (self, other) {
            (MinusInf, MinusInf) | (PlusInf, PlusInf) => Equal,
            (MinusInf, _) | (_, PlusInf) => Less,
            (PlusInf, _) | (_, MinusInf) => Greater,
            (Finite(an, ad), Finite(bn, bd)) => cmp_exact(&(an.clone(), ad.clone()), &(bn.clone(), bd.clone())),
        }
    }
}

/// `BoundType` (INCLUSIVE / EXCLUSIVE) — `false` = INCLUSIVE, `true` = EXCLUSIVE,
/// kept as a bool. The "more restrictive" of two bound types at an equal
/// endpoint is EXCLUSIVE (`getMoreRestrictive`); the "complement" flips it
/// (`getComplement`).
#[derive(Clone, Copy, PartialEq, Debug)]
struct ExclusiveFlag(bool);
impl ExclusiveFlag {
    const INCLUSIVE: ExclusiveFlag = ExclusiveFlag(false);
    fn is_exclusive(self) -> bool {
        self.0
    }
    fn more_restrictive(a: ExclusiveFlag, b: ExclusiveFlag) -> ExclusiveFlag {
        ExclusiveFlag(a.0 || b.0)
    }
    fn complement(self) -> ExclusiveFlag {
        ExclusiveFlag(!self.0)
    }
}

/// A faithful port of `NumberInterval`: values of `base_range` minus
/// `excluded_range`, restricted to `[lower, upper]`. Constructed only when
/// non-empty (callers use `try_new`, which returns `None` for an empty
/// interval, mirroring the `assert !isIntervalEmpty(...)` precondition).
#[derive(Clone, Debug)]
struct NumInterval {
    base_range: NumRange,
    excluded_range: NumRange,
    lower: NumBound,
    lower_excl: ExclusiveFlag,
    upper: NumBound,
    upper_excl: ExclusiveFlag,
}

/// `Numbers.getNearestIntegerInBound`: the first integer at or inside the bound,
/// for an INTEGER base range. `lower` selects the LOWER direction (ceil-ish),
/// else UPPER (floor-ish); `inclusive` matches `boundIsInclusive`.
fn nearest_integer_in_bound(value: &(BigInt, BigInt), lower: bool, inclusive: bool) -> BigInt {
    let (num, den) = value;
    if den.is_one() {
        // Integer-valued bound.
        if inclusive {
            num.clone()
        } else if lower {
            num + 1
        } else if *num == BigInt::from(i32::MIN) {
            // Java's `Numbers.getNearestIntegerInBound` INTEGER/UPPER/exclusive arm
            // subtracts 11 (not 1) when the bound equals Integer.MIN_VALUE
            // (`((long)value)-11`). A bound equal to -2147483648 always has Java
            // NumberType INTEGER, so this is the only value that triggers it.
            num - 11
        } else {
            num - 1
        }
    } else {
        // Non-integer bound: floor toward zero via truncating division, then
        // step in the requested direction past zero (matching BigDecimal/
        // BigRational arms, which round toward zero then adjust by sign).
        let quotient = num / den; // truncates toward zero
        if lower {
            if num.is_positive() {
                &quotient + 1
            } else {
                quotient
            }
        } else if num.is_negative() {
            &quotient - 1
        } else {
            quotient
        }
    }
}

impl NumInterval {
    /// `NumberInterval.isIntervalEmpty`.
    fn is_empty(
        base_range: NumRange,
        excluded_range: NumRange,
        lower: &NumBound,
        lower_excl: ExclusiveFlag,
        upper: &NumBound,
        upper_excl: ExclusiveFlag,
    ) -> bool {
        use std::cmp::Ordering::*;
        if NumRange::is_subset_of(base_range, excluded_range) {
            return true;
        }
        match lower.compare(upper) {
            Greater => true,
            Equal => {
                if lower_excl.is_exclusive()
                    || upper_excl.is_exclusive()
                    || matches!(lower, NumBound::MinusInf | NumBound::PlusInf)
                {
                    return true;
                }
                // Both inclusive, finite, equal point: present iff its most
                // specific range is in base and not in excluded.
                let NumBound::Finite(n, d) = lower else { unreachable!() };
                let msr = most_specific_range(&(n.clone(), d.clone()));
                !NumRange::is_subset_of(msr, base_range)
                    || NumRange::is_subset_of(msr, excluded_range)
            }
            Less => {
                if base_range.is_dense() {
                    return false;
                }
                // INTEGER base: empty iff no integer lies in [lower, upper].
                let (NumBound::Finite(ln, ld), NumBound::Finite(un, ud)) = (lower, upper) else {
                    // One side infinite ⇒ infinitely many integers.
                    return false;
                };
                let lo = nearest_integer_in_bound(&(ln.clone(), ld.clone()), true, !lower_excl.is_exclusive());
                let hi = nearest_integer_in_bound(&(un.clone(), ud.clone()), false, !upper_excl.is_exclusive());
                lo > hi
            }
        }
    }

    /// `new NumberInterval(...)` precondition-guarded: `None` when empty. Adjusts
    /// the endpoints to integers when the base range is INTEGER (so the bounds
    /// become inclusive integers), matching the Java constructor.
    fn try_new(
        base_range: NumRange,
        excluded_range: NumRange,
        lower: NumBound,
        lower_excl: ExclusiveFlag,
        upper: NumBound,
        upper_excl: ExclusiveFlag,
    ) -> Option<NumInterval> {
        if NumInterval::is_empty(base_range, excluded_range, &lower, lower_excl, &upper, upper_excl) {
            return None;
        }
        if base_range == NumRange::Integer {
            let (lower, lower_excl) = match &lower {
                NumBound::MinusInf => (lower.clone(), lower_excl),
                NumBound::Finite(n, d) => {
                    let i = nearest_integer_in_bound(&(n.clone(), d.clone()), true, !lower_excl.is_exclusive());
                    (NumBound::Finite(i, BigInt::one()), ExclusiveFlag::INCLUSIVE)
                }
                NumBound::PlusInf => (lower.clone(), lower_excl),
            };
            let (upper, upper_excl) = match &upper {
                NumBound::PlusInf => (upper.clone(), upper_excl),
                NumBound::Finite(n, d) => {
                    let i = nearest_integer_in_bound(&(n.clone(), d.clone()), false, !upper_excl.is_exclusive());
                    (NumBound::Finite(i, BigInt::one()), ExclusiveFlag::INCLUSIVE)
                }
                NumBound::MinusInf => (upper.clone(), upper_excl),
            };
            Some(NumInterval { base_range, excluded_range, lower, lower_excl, upper, upper_excl })
        } else {
            Some(NumInterval { base_range, excluded_range, lower, lower_excl, upper, upper_excl })
        }
    }

    /// `NumberInterval.intersectWith`: `None` when the intersection is empty.
    fn intersect_with(&self, that: &NumInterval) -> Option<NumInterval> {
        use std::cmp::Ordering::*;
        let new_base = NumRange::intersection(self.base_range, that.base_range);
        let new_excluded = NumRange::union(self.excluded_range, that.excluded_range);
        if NumRange::is_subset_of(new_base, new_excluded) {
            return None;
        }
        let (lower, lower_excl) = match self.lower.compare(&that.lower) {
            Less => (that.lower.clone(), that.lower_excl),
            Greater => (self.lower.clone(), self.lower_excl),
            Equal => (self.lower.clone(), ExclusiveFlag::more_restrictive(self.lower_excl, that.lower_excl)),
        };
        let (upper, upper_excl) = match self.upper.compare(&that.upper) {
            Less => (self.upper.clone(), self.upper_excl),
            Greater => (that.upper.clone(), that.upper_excl),
            Equal => (self.upper.clone(), ExclusiveFlag::more_restrictive(self.upper_excl, that.upper_excl)),
        };
        NumInterval::try_new(new_base, new_excluded, lower, lower_excl, upper, upper_excl)
    }

    /// `NumberInterval.subtractSizeFrom`: how many distinct values remain to be
    /// counted after this interval. Mirrors the Java exactly but over `u128`.
    /// `None` for the `argument <= 0` early return is represented by passing 0.
    fn subtract_size_from(&self, argument: u128) -> u128 {
        if argument == 0 {
            return 0;
        }
        if self.lower.compare(&self.upper) == std::cmp::Ordering::Equal {
            // Singleton.
            return argument - 1;
        }
        // Lower < upper.
        if self.base_range.is_dense() {
            return 0; // infinitely many
        }
        // INTEGER base with a proper-subset (NOTHING) excluded range.
        let (NumBound::Finite(ln, _), NumBound::Finite(un, _)) = (&self.lower, &self.upper) else {
            return 0; // unbounded ⇒ infinite
        };
        // Bounds were adjusted to inclusive integers in the constructor.
        let size = (un - ln) + BigInt::one();
        let size = u128::try_from(&size).unwrap_or(u128::MAX);
        argument.saturating_sub(size)
    }

    /// `NumberInterval.containsNumber` for an exact rational.
    fn contains_number(&self, value: &(BigInt, BigInt)) -> bool {
        use std::cmp::Ordering::*;
        let msr = most_specific_range(value);
        if !NumRange::is_subset_of(msr, self.base_range) || NumRange::is_subset_of(msr, self.excluded_range) {
            return false;
        }
        let v = NumBound::Finite(value.0.clone(), value.1.clone());
        match self.lower.compare(&v) {
            Greater => return false,
            Equal if self.lower_excl.is_exclusive() => return false,
            _ => {}
        }
        match self.upper.compare(&v) {
            Less => return false,
            Equal if self.upper_excl.is_exclusive() => return false,
            _ => {}
        }
        true
    }
}

/// A faithful port of `OWLRealValueSpaceSubset`: a (small) list of intervals.
#[derive(Clone, Debug)]
struct NumValueSpace {
    intervals: Vec<NumInterval>,
}

impl NumValueSpace {
    /// `OWLRealValueSpaceSubset.hasCardinalityAtLeast(number)`.
    fn has_cardinality_at_least(&self, number: u128) -> bool {
        let mut left = number;
        for interval in self.intervals.iter().rev() {
            if left == 0 {
                break;
            }
            left = interval.subtract_size_from(left);
        }
        left == 0
    }

    /// `OWLRealValueSpaceSubset.containsDataValue` for an exact rational.
    fn contains(&self, value: &(BigInt, BigInt)) -> bool {
        self.intervals.iter().rev().any(|i| i.contains_number(value))
    }

    /// The exact total cardinality of this value space: `Some(count)` when every
    /// interval is finite (each a bounded INTEGER interval, possibly a
    /// singleton), or `None` when any interval is infinite (dense, or an
    /// unbounded integer line). Equivalent to running `hasCardinalityAtLeast` to
    /// saturation, but returning the precise number. The intervals produced by
    /// `conjoin_with_*` over disjoint complement pieces are pairwise disjoint, so
    /// summing their sizes counts each value once (mirroring how Java's
    /// `subtractSizeFrom` accumulates across the interval list).
    fn exact_cardinality(&self) -> Option<u128> {
        let mut total: u128 = 0;
        for interval in &self.intervals {
            if interval.lower.compare(&interval.upper) == std::cmp::Ordering::Equal {
                total = total.saturating_add(1); // singleton
                continue;
            }
            if interval.base_range.is_dense() {
                return None; // infinitely many
            }
            let (NumBound::Finite(ln, _), NumBound::Finite(un, _)) =
                (&interval.lower, &interval.upper)
            else {
                return None; // unbounded integer line
            };
            let size = (un - ln) + BigInt::one();
            total = total.saturating_add(u128::try_from(&size).unwrap_or(u128::MAX));
        }
        Some(total)
    }

    /// `OWLRealDatatypeHandler.conjoinWithDR`: intersect every interval with the
    /// supplied positive interval, dropping empties.
    fn conjoin_with_interval(&self, interval: &NumInterval) -> NumValueSpace {
        let mut out = Vec::new();
        for old in &self.intervals {
            if let Some(i) = old.intersect_with(interval) {
                out.push(i);
            }
        }
        NumValueSpace { intervals: out }
    }

    /// `OWLRealDatatypeHandler.conjoinWithDRNegation`: intersect every interval
    /// with each of the (up to three) complement pieces of `interval`.
    fn conjoin_with_negation(&self, interval: &NumInterval) -> NumValueSpace {
        // complementInterval1: (-inf, lower) over REAL, if lower != -inf.
        let comp1 = if interval.lower != NumBound::MinusInf {
            NumInterval::try_new(
                NumRange::Real,
                NumRange::Nothing,
                NumBound::MinusInf,
                ExclusiveFlag::INCLUSIVE,
                interval.lower.clone(),
                interval.lower_excl.complement(),
            )
        } else {
            None
        };
        // complementInterval2: [lower, upper] over REAL excluding base_range, if
        // base_range != REAL (the "different base range" complement).
        let comp2 = if interval.base_range != NumRange::Real {
            NumInterval::try_new(
                NumRange::Real,
                interval.base_range,
                interval.lower.clone(),
                interval.lower_excl,
                interval.upper.clone(),
                interval.upper_excl,
            )
        } else {
            None
        };
        // complementInterval3: (upper, +inf) over REAL, if upper != +inf.
        let comp3 = if interval.upper != NumBound::PlusInf {
            NumInterval::try_new(
                NumRange::Real,
                NumRange::Nothing,
                interval.upper.clone(),
                interval.upper_excl.complement(),
                NumBound::PlusInf,
                ExclusiveFlag::INCLUSIVE,
            )
        } else {
            None
        };
        let mut out = Vec::new();
        for old in &self.intervals {
            for comp in [&comp1, &comp2, &comp3].into_iter().flatten() {
                if let Some(i) = old.intersect_with(comp) {
                    out.push(i);
                }
            }
        }
        NumValueSpace { intervals: out }
    }
}

/// `OWLRealDatatypeHandler.getIntervalFor`: the (single) `NumberInterval` for a
/// numeric datatype restriction (base interval tightened by its ordering
/// facets), or `None` when the restriction's value space is empty. Returns
/// `None` together with a flag when a facet value cannot be parsed (undecided),
/// distinguished so callers do not treat "undecided" as "empty".
fn num_interval_for(restriction: &DatatypeRestriction) -> NumIntervalResult {
    let uri = restriction.datatype_uri();
    let Some(base_range) = NumRange::base_of(uri) else {
        return NumIntervalResult::Undecided;
    };
    let mut lower = NumBound::MinusInf;
    let mut lower_excl = ExclusiveFlag::INCLUSIVE;
    let mut upper = NumBound::PlusInf;
    let mut upper_excl = ExclusiveFlag::INCLUSIVE;
    // Seed the implicit value-space bounds of a derived integer type.
    if let Some((implicit_min, implicit_max)) = integer_datatype_bounds(uri) {
        if let Some(m) = implicit_min {
            lower = NumBound::Finite(BigInt::from(m), BigInt::one());
        }
        if let Some(m) = implicit_max {
            upper = NumBound::Finite(BigInt::from(m), BigInt::one());
        }
    }
    for i in 0..restriction.number_of_facet_restrictions() {
        let Some(facet) = restriction.facet_uri(i).strip_prefix(XSD) else {
            continue;
        };
        if !matches!(facet, "minInclusive" | "minExclusive" | "maxInclusive" | "maxExclusive") {
            continue;
        }
        // OWLRealDatatypeHandler.validateDatatypeRestriction accepts a min/max
        // facet bound only when `Numbers.isValidNumber(value)`, which is
        // Integer/Long/BigInteger/BigDecimal/BigRational and EXCLUDES Float/Double.
        // A float/double-typed facet bound makes the restriction ill-formed (an
        // UnsupportedFacetException in Java), so we must not reason over it; treat
        // it like any other unsupported numeric facet on this path.
        let Some(parsed) = parse_value(restriction.facet_value(i)) else {
            return NumIntervalResult::Undecided; // unparseable numeric facet ⇒ undecided
        };
        if matches!(parsed, DataValue::Float(_) | DataValue::Double(_)) {
            return NumIntervalResult::Undecided;
        }
        let Some(bound) = as_exact(&parsed) else {
            return NumIntervalResult::Undecided;
        };
        let fb = NumBound::Finite(bound.0, bound.1);
        match facet {
            "minInclusive" => {
                if fb.compare(&lower) == std::cmp::Ordering::Greater {
                    lower = fb;
                    lower_excl = ExclusiveFlag::INCLUSIVE;
                }
            }
            "minExclusive" => match fb.compare(&lower) {
                std::cmp::Ordering::Greater => {
                    lower = fb;
                    lower_excl = ExclusiveFlag(true);
                }
                std::cmp::Ordering::Equal => lower_excl = ExclusiveFlag(true),
                _ => {}
            },
            "maxInclusive" => {
                if fb.compare(&upper) == std::cmp::Ordering::Less {
                    upper = fb;
                    upper_excl = ExclusiveFlag::INCLUSIVE;
                }
            }
            "maxExclusive" => match fb.compare(&upper) {
                std::cmp::Ordering::Less => {
                    upper = fb;
                    upper_excl = ExclusiveFlag(true);
                }
                std::cmp::Ordering::Equal => upper_excl = ExclusiveFlag(true),
                _ => {}
            },
            _ => {}
        }
    }
    match NumInterval::try_new(base_range, NumRange::Nothing, lower, lower_excl, upper, upper_excl) {
        Some(i) => NumIntervalResult::Interval(i),
        None => NumIntervalResult::Empty,
    }
}

enum NumIntervalResult {
    Interval(NumInterval),
    Empty,
    Undecided,
}

/// Builds the numeric value space for a node from its positive numeric datatype
/// restrictions and applies its negated numeric datatype restrictions, mirroring
/// the sequence of `conjoinWithDR` / `conjoinWithDRNegation` calls HermiT makes.
/// Returns `None` when the node carries no numeric restriction or any numeric
/// facet/datatype is undecided (so the caller falls back to its other logic and
/// never reports a false clash). The starting value space is `owl:real` itself
/// (the whole REAL line), matching HermiT seeding from the most general subset.
fn build_numeric_value_space<D>(ranges: &[(LiteralDataRange, D)]) -> Option<NumValueSpace> {
    // Collect positive and negated numeric datatype restrictions.
    let mut positives: Vec<&DatatypeRestriction> = Vec::new();
    let mut negatives: Vec<&DatatypeRestriction> = Vec::new();
    let mut saw_non_numeric_constraint = false;
    for (r, _) in ranges {
        match r {
            LiteralDataRange::DatatypeRestriction(dr) => {
                if NumRange::base_of(dr.datatype_uri()).is_some() {
                    positives.push(dr);
                } else {
                    saw_non_numeric_constraint = true;
                }
            }
            LiteralDataRange::AtomicNegationDataRange(n) => match n.get_negated_data_range() {
                crate::model::AtomicDataRange::DatatypeRestriction(dr)
                    if NumRange::base_of(dr.datatype_uri()).is_some() =>
                {
                    negatives.push(dr);
                }
                _ => saw_non_numeric_constraint = true,
            },
            _ => saw_non_numeric_constraint = true,
        }
    }
    if positives.is_empty() {
        return None;
    }
    // Other (non-numeric) constraints are handled elsewhere; here we only build
    // the numeric value space from the numeric restrictions. If any other range
    // is present we still build the numeric space (its emptiness is a sufficient
    // condition for the whole conjunction's emptiness), but we must not claim
    // the numeric space is the WHOLE node space for cardinality purposes — the
    // caller (build for cardinality) checks numeric-only nodes.
    let _ = saw_non_numeric_constraint;

    // Start from the whole owl:real line.
    let mut space = NumValueSpace {
        intervals: vec![NumInterval {
            base_range: NumRange::Real,
            excluded_range: NumRange::Nothing,
            lower: NumBound::MinusInf,
            lower_excl: ExclusiveFlag::INCLUSIVE,
            upper: NumBound::PlusInf,
            upper_excl: ExclusiveFlag::INCLUSIVE,
        }],
    };
    for dr in &positives {
        match num_interval_for(dr) {
            NumIntervalResult::Interval(i) => space = space.conjoin_with_interval(&i),
            NumIntervalResult::Empty => return Some(NumValueSpace { intervals: Vec::new() }),
            NumIntervalResult::Undecided => return None,
        }
    }
    for dr in &negatives {
        match num_interval_for(dr) {
            NumIntervalResult::Interval(i) => space = space.conjoin_with_negation(&i),
            // A negated empty interval removes nothing (¬∅ = everything).
            NumIntervalResult::Empty => {}
            NumIntervalResult::Undecided => return None,
        }
    }
    Some(space)
}

/// The exact finite cardinality of a node's numeric value space, when *every*
/// range on the node is numeric (a positive numeric DR or a negated numeric DR)
/// and the resulting value space is finite. `None` when a non-numeric range is
/// present, a facet/datatype is undecided, or the space is infinite — the caller
/// then falls back to its other (sound) handling. This is HermiT's exact
/// cardinality over `OWLRealValueSpaceSubset`: a huge bounded interval
/// minus a negated sub-interval has the precise leftover count.
fn numeric_node_cardinality<D>(ranges: &[(LiteralDataRange, D)]) -> Option<u128> {
    let all_numeric = ranges.iter().all(|(r, _)| match r {
        LiteralDataRange::DatatypeRestriction(dr) => NumRange::base_of(dr.datatype_uri()).is_some(),
        LiteralDataRange::AtomicNegationDataRange(n) => matches!(
            n.get_negated_data_range(),
            crate::model::AtomicDataRange::DatatypeRestriction(dr)
                if NumRange::base_of(dr.datatype_uri()).is_some()
        ),
        _ => false,
    });
    if !all_numeric {
        return None;
    }
    build_numeric_value_space(ranges)?.exact_cardinality()
}


/// FD-5: counts the xsd:float values whose order key lies in `[lower_key, upper_key]`
/// (the interval) that are removed by a value-removing range on the node. Mirrors
/// the way Java accounts for exclusions in NoNaNFloatSubset.hasCardinalityAtLeast
/// (it inflates the requested cardinality by m_forbiddenDataValues.size()) together
/// with FloatInterval.subtractIntervalSizeFrom for negated sub-intervals: the exact
/// leftover cardinality is (interval size) minus (excluded values inside it).
fn count_excluded_floats_in_range<D>(
    ranges: &[(LiteralDataRange, D)],
    lower_key: u32,
    upper_key: u32,
) -> u128 {
    let in_iv = |k: u32| k >= lower_key && k <= upper_key;
    let mut removed_points: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    let mut neg_windows: Vec<(u32, u32)> = Vec::new();
    for (r, _) in ranges {
        if let LiteralDataRange::AtomicNegationDataRange(n) = r {
            match n.get_negated_data_range() {
                crate::model::AtomicDataRange::ConstantEnumeration(e) => {
                    for i in 0..e.number_of_constants() {
                        if let Some(DataValue::Float(bits)) = parse_value(e.constant(i)) {
                            let f = f32::from_bits(bits);
                            if !f.is_nan() {
                                let k = f32_order_key(f);
                                if in_iv(k) {
                                    removed_points.insert(k);
                                }
                            }
                        }
                    }
                }
                crate::model::AtomicDataRange::DatatypeRestriction(dr)
                    if is_xsd_float(dr.datatype_uri()) =>
                {
                    if let Some((nlo, nhi)) = float_restriction_key_window(&dr) {
                        let lo = nlo.max(lower_key);
                        let hi = nhi.min(upper_key);
                        if lo <= hi {
                            neg_windows.push((lo, hi));
                        }
                    }
                }
                _ => {}
            }
        }
    }
    neg_windows.sort();
    let mut merged: Vec<(u32, u32)> = Vec::new();
    for (lo, hi) in neg_windows {
        if let Some(last) = merged.last_mut() {
            if lo <= last.1.saturating_add(1) {
                last.1 = last.1.max(hi);
                continue;
            }
        }
        merged.push((lo, hi));
    }
    let mut removed: u128 = 0;
    for (lo, hi) in &merged {
        removed = removed.saturating_add((*hi - *lo) as u128 + 1);
    }
    for k in removed_points {
        if !merged.iter().any(|(lo, hi)| k >= *lo && k <= *hi) {
            removed = removed.saturating_add(1);
        }
    }
    removed
}

/// FD-5: the order-key window `[lo, hi]` of a (positive) xsd:float datatype
/// restriction's min/max facets, mirroring FloatDatatypeHandler.getIntervalFor
/// (zero signs are normalised per facet; a NaN facet bound is handled exactly as
/// Java's bugged FloatInterval.isNaN does — see the body).
fn float_restriction_key_window(dr: &DatatypeRestriction) -> Option<(u32, u32)> {
    let mut lower_key = f32_order_key(f32::NEG_INFINITY);
    let mut upper_key = f32_order_key(f32::INFINITY);
    for i in 0..dr.number_of_facet_restrictions() {
        let facet = dr.facet_uri(i).strip_prefix(XSD)?;
        if !matches!(facet, "minInclusive" | "minExclusive" | "maxInclusive" | "maxExclusive") {
            return None;
        }
        let DataValue::Float(bits) = parse_value(dr.facet_value(i))? else { return None };
        let bound = f32::from_bits(bits);
        // Faithful to Java FloatInterval.isNaN, whose mantissa mask is 0x003fffff
        // (22 bits) instead of the correct 0x007fffff (23 bits). The canonical
        // float NaN bits 0x7fc00000 satisfy `(bits & 0x003fffff)==0`, so Java does
        // NOT recognise it as NaN inside getIntervalFor: it is treated as an
        // ordinary positive value of magnitude 0x7fc00000 (above +INF). Letting it
        // flow through f32_order_key (which keys it as 0xffc00000) reproduces this:
        // a NaN min* bound pushes lower_key above +INF (empty interval), while a
        // NaN max* bound leaves upper_key at +INF (the min() keeps +INF), exactly
        // matching Java. (Double's mask is correct, so the double window above does
        // drop a NaN bound.)
        let bound = normalize_zero_for_facet_f32(bound, facet);
        let key = f32_order_key(bound);
        match facet {
            "minInclusive" => lower_key = lower_key.max(key),
            "minExclusive" => lower_key = lower_key.max(key.saturating_add(1)),
            "maxInclusive" => upper_key = upper_key.min(key),
            "maxExclusive" => upper_key = upper_key.min(key.saturating_sub(1)),
            _ => {}
        }
    }
    Some((lower_key, upper_key))
}

/// FD-5: the xsd:double analogue of `count_excluded_floats_in_range`.
fn count_excluded_doubles_in_range<D>(
    ranges: &[(LiteralDataRange, D)],
    lower_key: u64,
    upper_key: u64,
) -> u128 {
    let in_iv = |k: u64| k >= lower_key && k <= upper_key;
    let mut removed_points: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
    let mut neg_windows: Vec<(u64, u64)> = Vec::new();
    for (r, _) in ranges {
        if let LiteralDataRange::AtomicNegationDataRange(n) = r {
            match n.get_negated_data_range() {
                crate::model::AtomicDataRange::ConstantEnumeration(e) => {
                    for i in 0..e.number_of_constants() {
                        if let Some(DataValue::Double(bits)) = parse_value(e.constant(i)) {
                            let f = f64::from_bits(bits);
                            if !f.is_nan() {
                                let k = f64_order_key(f);
                                if in_iv(k) {
                                    removed_points.insert(k);
                                }
                            }
                        }
                    }
                }
                crate::model::AtomicDataRange::DatatypeRestriction(dr)
                    if is_xsd_double(dr.datatype_uri()) =>
                {
                    if let Some((nlo, nhi)) = double_restriction_key_window(&dr) {
                        let lo = nlo.max(lower_key);
                        let hi = nhi.min(upper_key);
                        if lo <= hi {
                            neg_windows.push((lo, hi));
                        }
                    }
                }
                _ => {}
            }
        }
    }
    neg_windows.sort();
    let mut merged: Vec<(u64, u64)> = Vec::new();
    for (lo, hi) in neg_windows {
        if let Some(last) = merged.last_mut() {
            if lo <= last.1.saturating_add(1) {
                last.1 = last.1.max(hi);
                continue;
            }
        }
        merged.push((lo, hi));
    }
    let mut removed: u128 = 0;
    for (lo, hi) in &merged {
        removed = removed.saturating_add((*hi - *lo) as u128 + 1);
    }
    for k in removed_points {
        if !merged.iter().any(|(lo, hi)| k >= *lo && k <= *hi) {
            removed = removed.saturating_add(1);
        }
    }
    removed
}

fn double_restriction_key_window(dr: &DatatypeRestriction) -> Option<(u64, u64)> {
    let mut lower_key = f64_order_key(f64::NEG_INFINITY);
    let mut upper_key = f64_order_key(f64::INFINITY);
    for i in 0..dr.number_of_facet_restrictions() {
        let facet = dr.facet_uri(i).strip_prefix(XSD)?;
        if !matches!(facet, "minInclusive" | "minExclusive" | "maxInclusive" | "maxExclusive") {
            return None;
        }
        let DataValue::Double(bits) = parse_value(dr.facet_value(i))? else { return None };
        let bound = f64::from_bits(bits);
        if bound.is_nan() {
            continue;
        }
        let bound = normalize_zero_for_facet_f64(bound, facet);
        let key = f64_order_key(bound);
        match facet {
            "minInclusive" => lower_key = lower_key.max(key),
            "minExclusive" => lower_key = lower_key.max(key.saturating_add(1)),
            "maxInclusive" => upper_key = upper_key.min(key),
            "maxExclusive" => upper_key = upper_key.min(key.saturating_sub(1)),
            _ => {}
        }
    }
    Some((lower_key, upper_key))
}

/// Whether the entire xsd:double value space's NaN survives the node's ranges,
/// faithful to HermiT `DVariable.prepareAsValueSpaceSubset`. The subset starts
/// as `EntireDoubleSubset` (which DOES contain NaN, contributing the +1 to the
/// cardinality). It only loses its NaN when it becomes a `NoNaNDoubleSubset`,
/// which happens exactly when:
///   - a positive xsd:double DR with min/max facets is conjoined
///     (`conjoinWithDR` with `getNumberOfFacetRestrictions()!=0` builds a
///     `NoNaNDoubleSubset`; a facet-free positive DR is a no-op), OR
///   - a negated xsd:double DR with a non-empty interval is conjoined
///     (`conjoinWithDRNegation`; a vacuous/empty-interval negated DR
///     `getIntervalFor()==null` is a no-op).
/// Negated *enumerations* are NOT conjoined into the subset — they are kept as
/// `m_forbiddenDataValues` (concrete, non-NaN doubles) and subtracted from the
/// cardinality separately, so they do NOT remove the NaN. Hence the entire space
/// keeps its NaN over facet-free positive DRs, vacuously-negated DRs, and
/// negated enumerations alike.
fn entire_double_space_keeps_nan<D>(ranges: &[(LiteralDataRange, D)]) -> bool {
    for (r, _) in ranges {
        match r {
            LiteralDataRange::DatatypeRestriction(dr) if is_xsd_double(dr.datatype_uri()) => {
                // A positive double DR with any min/max facet shrinks the entire
                // space to a NoNaN subset (NaN removed). A facet-free DR is a no-op.
                if dr.number_of_facet_restrictions() != 0 {
                    return false;
                }
            }
            LiteralDataRange::AtomicNegationDataRange(n) => {
                if let crate::model::AtomicDataRange::DatatypeRestriction(dr) =
                    n.get_negated_data_range()
                {
                    if is_xsd_double(dr.datatype_uri()) {
                        // `conjoinWithDRNegation`: a negated DR with a non-empty
                        // interval (getIntervalFor!=null) produces a NoNaN subset.
                        // An empty interval (lo>hi) is a no-op and keeps NaN.
                        match double_restriction_key_window(&dr) {
                            // Non-empty interval => NaN removed.
                            Some((lo, hi)) if lo <= hi => return false,
                            // Empty interval (vacuous negation) => no-op, NaN kept.
                            Some(_) => {}
                            // Unparseable/unsupported: be conservative and treat as
                            // a real (non-empty) negation that removes NaN.
                            None => return false,
                        }
                    }
                }
                // A negated enumeration (or a negation of a non-double DR) does not
                // turn the subset into NoNaN: NaN is kept.
            }
            // Any other range kind on the entire double space is unexpected here;
            // be conservative and drop the NaN.
            _ => return false,
        }
    }
    true
}

/// xsd:float analogue of `entire_double_space_keeps_nan` (faithful to the float
/// equivalents: EntireFloatSubset / NoNaNFloatSubset / FloatDatatypeHandler).
fn entire_float_space_keeps_nan<D>(ranges: &[(LiteralDataRange, D)]) -> bool {
    for (r, _) in ranges {
        match r {
            LiteralDataRange::DatatypeRestriction(dr) if is_xsd_float(dr.datatype_uri()) => {
                if dr.number_of_facet_restrictions() != 0 {
                    return false;
                }
            }
            LiteralDataRange::AtomicNegationDataRange(n) => {
                if let crate::model::AtomicDataRange::DatatypeRestriction(dr) =
                    n.get_negated_data_range()
                {
                    if is_xsd_float(dr.datatype_uri()) {
                        match float_restriction_key_window(&dr) {
                            Some((lo, hi)) if lo <= hi => return false,
                            Some(_) => {}
                            None => return false,
                        }
                    }
                }
            }
            _ => return false,
        }
    }
    true
}

/// Counts the distinct integers in `[lo, hi]` that are removed by some
/// value-removing range on the node (a negated enumeration whose members are
/// concrete excluded points). Returns `None` when a removing range cannot be
/// resolved to a finite set of integer points (e.g. an unparseable enumeration
/// member, or a negated *interval* that could remove a sub-range rather than
/// finitely many points — those are handled by `numeric_node_cardinality`). Used
/// for the huge-interval-with-exclusions cardinality when the exclusions are
/// finite point-sets rather than numeric intervals.
fn count_excluded_integers_in_range<D>(
    ranges: &[(LiteralDataRange, D)],
    lo: &BigInt,
    hi: &BigInt,
) -> Option<u128> {
    let mut removed: Vec<BigInt> = Vec::new();
    for (r, _) in ranges {
        match r {
            // A positive integer datatype restriction defines the interval; it
            // removes nothing here (its bounds are already in [lo, hi]).
            LiteralDataRange::DatatypeRestriction(dr) if is_integer_datatype(dr.datatype_uri()) => {}
            // A negated enumeration removes its (finitely many) integer members
            // that fall inside the interval.
            LiteralDataRange::AtomicNegationDataRange(n) => {
                match n.get_negated_data_range() {
                    crate::model::AtomicDataRange::ConstantEnumeration(e) => {
                        for i in 0..e.number_of_constants() {
                            match parse_value(e.constant(i)) {
                                Some(DataValue::Integer(v)) => {
                                    if &v >= lo && &v <= hi && !removed.contains(&v) {
                                        removed.push(v);
                                    }
                                }
                                // A non-integer (or unparseable) member removes
                                // nothing from the integer line — but an
                                // unparseable one is undecidable, so bail.
                                Some(_) => {}
                                None => return None,
                            }
                        }
                    }
                    // A negated datatype / interval is not a finite point set.
                    _ => return None,
                }
            }
            // Any other removing range we cannot resolve precisely.
            _ => return None,
        }
    }
    Some(removed.len() as u128)
}

/// Whether the conjunction is provably empty because a positive datatype's
/// value space is entirely removed by a negated datatype — i.e. some positive
/// atomic, facet-free datatype `A` carries a negated atomic, facet-free datatype
/// `¬B` with value-space(A) ⊆ value-space(B). This is the case the interval/
/// enumeration logic misses when `A` is *infinite* (e.g. `integer ⊓ ¬integer`,
/// `integer ⊓ ¬decimal`, `integer ⊓ ¬real`): the negation deletes every value,
/// so the result is empty regardless of `A`'s (un)boundedness.
///
/// This mirrors Java's `conjoinWithDRNegation`, whose `complementInterval2`
/// (the "different base range" complement, e.g. the non-integers of the reals)
/// empties the intersection exactly when the positive interval's base range is a
/// subset of the negated datatype's base range. The non-numeric kinds
/// (string/datetime/binary/…) are decided by the facet-free value-space-class
/// subset test below; the numeric (owl:real) lattice is decided exactly — over
/// facets too — by `build_numeric_value_space` (so e.g.
/// `integer[≥0] ⊓ ¬integer[≥-5]` is detected empty even though both sides carry
/// facets and the positive side is infinite).
fn negation_subsumes<D>(ranges: &[(LiteralDataRange, D)]) -> bool {
    // Numeric lattice: build the exact value space and test for emptiness. This
    // covers facet-restricted negation subsumption over the infinite reals.
    let has_numeric_negation = ranges.iter().any(|(r, _)| match r {
        LiteralDataRange::AtomicNegationDataRange(n) => matches!(
            n.get_negated_data_range(),
            crate::model::AtomicDataRange::DatatypeRestriction(dr)
                if NumRange::base_of(dr.datatype_uri()).is_some()
        ),
        _ => false,
    });
    if has_numeric_negation {
        // Only decide via the numeric lattice when *every value-constraining*
        // range is numeric (a positive numeric DR or a negated numeric DR). The
        // value-non-constraining helper ranges that the live `∃p` witness path
        // adds — `rdfs:Literal` (the universal top) and the
        // `internal:defdata#`/`internal:defined` `InternalDatatype` placeholders
        // (whose real meaning is already carried by the inclusion-derived
        // positive/negated ranges) — are IGNORED here: they constrain nothing,
        // so they must not disable the numeric subsumption test. A genuinely
        // non-numeric range (e.g. a string DR) still scopes us out, mirroring
        // Java's per-handler structure. `build_numeric_value_space` itself only
        // looks at the numeric ranges, so the helper ranges are transparent to
        // it.
        let all_numeric = ranges.iter().all(|(r, _)| {
            is_value_non_constraining_helper(r)
                || match r {
                    LiteralDataRange::DatatypeRestriction(dr) => {
                        NumRange::base_of(dr.datatype_uri()).is_some()
                    }
                    LiteralDataRange::AtomicNegationDataRange(n) => matches!(
                        n.get_negated_data_range(),
                        crate::model::AtomicDataRange::DatatypeRestriction(dr)
                            if NumRange::base_of(dr.datatype_uri()).is_some()
                    ),
                    _ => false,
                }
        });
        if all_numeric {
            if let Some(space) = build_numeric_value_space(ranges) {
                if space.intervals.is_empty() {
                    return true;
                }
            }
        }
    }
    // String / rdf:PlainLiteral length lattice: covers the faceted-NEGATED case
    // outside the numeric lattice (e.g. `string[minLength 3] ⊓ ¬string[minLength
    // 1]` empty). Like the numeric branch, this only fires when a negated
    // length-handled string range is present; `length_value_space_is_empty`
    // itself scopes out (returns false) when any range is not a length range.
    let has_length_negation = ranges.iter().any(|(r, _)| match r {
        LiteralDataRange::AtomicNegationDataRange(n) => matches!(
            n.get_negated_data_range(),
            crate::model::AtomicDataRange::DatatypeRestriction(dr)
                if length_intervals_for(dr).is_some()
        ),
        _ => false,
    });
    if has_length_negation && length_value_space_is_empty(ranges) {
        return true;
    }
    // FIX C: string / rdf:PlainLiteral pattern + langRange value-space emptiness
    // (the AUTOMATON branch of RDFPlainLiteralDatatypeHandler). Fires when any range
    // carries a pattern or langRange facet (positive or negated); the routine itself
    // scopes out (returns false) for anything it cannot decide exactly.
    let has_pattern_or_langrange = ranges.iter().any(|(r, _)| {
        let dr = match r {
            LiteralDataRange::DatatypeRestriction(dr) => Some(dr),
            LiteralDataRange::AtomicNegationDataRange(n) => match n.get_negated_data_range() {
                crate::model::AtomicDataRange::DatatypeRestriction(dr) => Some(dr),
                _ => None,
            },
            _ => None,
        };
        dr.is_some_and(|dr| {
            (0..dr.number_of_facet_restrictions()).any(|i| {
                let f = dr.facet_uri(i);
                f == format!("{XSD}pattern") || f == format!("{RDF}langRange")
            })
        })
    });
    if has_pattern_or_langrange && pattern_langrange_value_space_is_empty(ranges) {
        return true;
    }
    // DateTime interval lattice: mirrors DateTimeDatatypeHandler.conjoinWithDRNegation,
    // which computes the complement of the negated DR's intervals and intersects with
    // the positive intervals. Fires only when a faceted negated datetime DR is present.
    let has_datetime_negation = ranges.iter().any(|(r, _)| match r {
        LiteralDataRange::AtomicNegationDataRange(n) => matches!(
            n.get_negated_data_range(),
            crate::model::AtomicDataRange::DatatypeRestriction(dr)
                if is_datetime_datatype(dr.datatype_uri()) && dr.number_of_facet_restrictions() > 0
        ),
        _ => false,
    });
    if has_datetime_negation && datetime_negation_value_space_is_empty(ranges) {
        return true;
    }
    base_datatype_negation_subsumes(ranges)
}

/// Whether `range` is a value-non-constraining helper range that the live
/// tableau path for `∃p.DataIntersectionOf(...)` adds onto the witness data node
/// in addition to the real positive/negated ranges: the universal `rdfs:Literal`
/// top, or an `internal:defdata#`/`internal:defined` `InternalDatatype`
/// placeholder (whose real meaning is already carried by the inclusion-derived
/// real ranges). Such a range admits every value, so it never affects whether
/// the conjunction is empty and must be IGNORED by the subsumption test (its
/// presence must not disable the check). A *negated* internal datatype is NOT a
/// helper (it removes values), so only the positive `InternalDatatype` form
/// matches.
fn is_value_non_constraining_helper(range: &LiteralDataRange) -> bool {
    matches!(range, LiteralDataRange::InternalDatatype(_))
}

// ===========================================================================
// rdf:PlainLiteral / xsd:string length value-space lattice (faithful port of
// org.semanticweb.HermiT.datatypes.rdfplainliteral.{RDFPlainLiteralLengthInterval,
// RDFPlainLiteralLengthValueSpaceSubset} and the length branch of
// RDFPlainLiteralDatatypeHandler.{getIntervalsFor,conjoinWithDR,
// conjoinWithDRNegation}). This decides string-conjunction emptiness over the
// ORDERABLE length facet space, INCLUDING a faceted-negated case outside the
// numeric lattice (e.g. `string[minLength 3] ⊓ ¬string[minLength 1]` is empty,
// `string[length 5] ⊓ ¬string[minLength 2]` is empty), mirroring exactly what
// the numeric lattice already does for the owl:real ordering facets.
// ===========================================================================

/// `RDFPlainLiteralLengthInterval.LanguageTagMode`: PRESENT (a non-empty
/// language tag) or ABSENT (a bare string).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LangTagMode {
    Present,
    Absent,
}

/// One `RDFPlainLiteralLengthInterval`: a `[min_length, max_length]` window of
/// the orderable length axis, for one language-tag mode. `max_length == None`
/// is `Integer.MAX_VALUE` (the unbounded upper end).
#[derive(Clone, Copy, Debug)]
struct LengthInterval {
    mode: LangTagMode,
    min_length: u64,
    /// `None` ⇒ `Integer.MAX_VALUE` (unbounded).
    max_length: Option<u64>,
}

impl LengthInterval {
    /// `RDFPlainLiteralLengthInterval.isIntervalEmpty`: empty iff
    /// `minLength > maxLength`.
    fn is_empty(mode: LangTagMode, min_length: u64, max_length: Option<u64>) -> bool {
        let _ = mode;
        match max_length {
            None => false,
            Some(max) => min_length > max,
        }
    }
    fn try_new(mode: LangTagMode, min_length: u64, max_length: Option<u64>) -> Option<Self> {
        if Self::is_empty(mode, min_length, max_length) {
            None
        } else {
            Some(LengthInterval { mode, min_length, max_length })
        }
    }
    /// `RDFPlainLiteralLengthInterval.intersectWith`: `None` when the two
    /// intervals do not intersect (different modes, or disjoint length windows).
    fn intersect(self, other: LengthInterval) -> Option<LengthInterval> {
        if self.mode != other.mode {
            return None;
        }
        let new_min = self.min_length.max(other.min_length);
        let new_max = match (self.max_length, other.max_length) {
            (None, m) | (m, None) => m,
            (Some(a), Some(b)) => Some(a.min(b)),
        };
        LengthInterval::try_new(self.mode, new_min, new_max)
    }
    /// `RDFPlainLiteralLengthInterval.subtractSizeFrom` / `getNumberOfValuesOfLength`:
    /// exact count of (xsd:string) values in this ABSENT-mode interval, for
    /// small bounded max (< 4). Returns `None` for PRESENT mode, unbounded max,
    /// or max ≥ 4 (those intervals are treated as infinite by Java too).
    /// Java: CHARACTER_COUNT = 1_112_033; getNumberOfValuesOfLength(L) =
    ///       1 + CHARACTER_COUNT + ... + CHARACTER_COUNT^L.
    fn size_of(&self) -> Option<u128> {
        // Java: m_languageTagMode==PRESENT ⇒ return 0 (≡ infinite for caller).
        if self.mode == LangTagMode::Present { return None; }
        let max = self.max_length?; // None = Integer.MAX_VALUE ⇒ infinite
        // Java guard: m_minLength>=4 || m_maxLength>=4 ⇒ return 0 (overflows long).
        if self.min_length >= 4 || max >= 4 { return None; }
        let values_up_to = |l: i64| -> u128 {
            if l < 0 { return 0; }
            let mut total: u128 = 1;
            let mut term: u128 = 1;
            for _ in 1..=l { term = term.saturating_mul(1_112_033); total = total.saturating_add(term); }
            total
        };
        Some(values_up_to(max as i64).saturating_sub(values_up_to(self.min_length as i64 - 1)))
    }
}

/// The two length intervals (PRESENT, ABSENT) implied by a positive string /
/// rdf:PlainLiteral datatype restriction's length facets, mirroring
/// `RDFPlainLiteralDatatypeHandler.getIntervalsFor`:
///   * `xsd:string`  ⇒ only the ABSENT interval `[min, max]`;
///   * `rdf:PlainLiteral` ⇒ both PRESENT and ABSENT intervals `[min, max]`.
///
/// Returns `(present, absent)`, each `None` when that mode is absent or the
/// `[min, max]` window is empty. Returns `None` (the outer Option) when the
/// datatype is not one of the two length-handled string datatypes, or it
/// carries a facet outside the length family (pattern / langRange go through
/// an automaton in Java, which we do not model here — we conservatively
/// scope out, never a false clash).
fn length_intervals_for(
    dr: &DatatypeRestriction,
) -> Option<(Option<LengthInterval>, Option<LengthInterval>)> {
    let uri = dr.datatype_uri();
    let is_plain_literal = uri == format!("{RDF}PlainLiteral");
    let is_xsd_string = uri.strip_prefix(XSD) == Some("string");
    if !is_plain_literal && !is_xsd_string {
        // Only xsd:string and rdf:PlainLiteral are length-handled in Java's
        // s_subsetsByDatatype; the string subtypes use pattern automatons.
        return None;
    }
    let mut min_length: u64 = 0;
    let mut max_length: Option<u64> = None; // None = Integer.MAX_VALUE
    for i in 0..dr.number_of_facet_restrictions() {
        let Some(facet) = dr.facet_uri(i).strip_prefix(XSD) else {
            // A non-XSD facet (rdf:langRange) ⇒ automaton territory: scope out.
            return None;
        };
        let lexical = dr.facet_value(i).lexical_form();
        let bound: u64 = match lexical.trim().parse() {
            Ok(b) => b,
            // An unparseable length value ⇒ undecided ⇒ scope out (no false clash).
            Err(_) => return None,
        };
        match facet {
            "minLength" => min_length = min_length.max(bound),
            "maxLength" => max_length = Some(max_length.map_or(bound, |m| m.min(bound))),
            "length" => {
                min_length = min_length.max(bound);
                max_length = Some(max_length.map_or(bound, |m| m.min(bound)));
            }
            // pattern ⇒ automaton territory; any other facet is unsupported here.
            _ => return None,
        }
    }
    let within = match max_length {
        None => true,
        Some(max) => min_length <= max,
    };
    let (mut present, mut absent) = (None, None);
    if within {
        if is_plain_literal {
            present = LengthInterval::try_new(LangTagMode::Present, min_length, max_length);
            absent = LengthInterval::try_new(LangTagMode::Absent, min_length, max_length);
        } else {
            absent = LengthInterval::try_new(LangTagMode::Absent, min_length, max_length);
        }
    }
    Some((present, absent))
}

/// The complement of a positive `(present, absent)` length-interval pair, as a
/// list of length intervals, mirroring the construction in
/// `RDFPlainLiteralDatatypeHandler.conjoinWithDRNegation`: for each mode, if the
/// mode's interval is present, its complement is `[0, min-1]` and `[max+1, ∞)`
/// (each only when non-degenerate); if the mode's interval is absent (the DR did
/// not constrain that mode), the complement is the whole mode `[0, ∞)`.
fn complement_length_intervals(
    present: Option<LengthInterval>,
    absent: Option<LengthInterval>,
) -> Vec<LengthInterval> {
    let mut out: Vec<LengthInterval> = Vec::with_capacity(4);
    for (mode, interval) in [
        (LangTagMode::Present, present),
        (LangTagMode::Absent, absent),
    ] {
        match interval {
            Some(iv) => {
                if iv.min_length > 0 {
                    if let Some(c) =
                        LengthInterval::try_new(mode, 0, Some(iv.min_length - 1))
                    {
                        out.push(c);
                    }
                }
                if let Some(max) = iv.max_length {
                    if let Some(c) = LengthInterval::try_new(mode, max + 1, None) {
                        out.push(c);
                    }
                }
            }
            None => {
                if let Some(c) = LengthInterval::try_new(mode, 0, None) {
                    out.push(c);
                }
            }
        }
    }
    out
}

/// Whether the conjunction of the string / rdf:PlainLiteral ranges on the node
/// is provably empty over the ORDERABLE length axis, mirroring the length branch
/// of `RDFPlainLiteralDatatypeHandler` (`getIntervalsFor` + `conjoinWithDR` +
/// `conjoinWithDRNegation`, then the empty-list test). This closes the
/// faceted-NEGATED string case the facet-free `base_datatype_negation_subsumes`
/// misses (e.g. `string[minLength 3] ⊓ ¬string[minLength 1]` empty,
/// `string[length 5] ⊓ ¬string[minLength 2]` empty), while staying sound
/// (`string[minLength 3] ⊓ ¬string[minLength 5]` keeps lengths 3, 4 ⇒ non-empty).
///
/// Only fires when EVERY value-constraining range on the node is a length-handled
/// string range (a positive or negated `xsd:string` / `rdf:PlainLiteral`
/// restriction whose facets are length facets); a pattern/langRange facet, a
/// non-string range, or an unparseable length bound scopes us out (returns
/// false ⇒ never a false clash). Value-non-constraining helper ranges
/// (`rdfs:Literal` / `internal:*`) are transparent.
fn length_value_space_is_empty<D>(ranges: &[(LiteralDataRange, D)]) -> bool {
    // Collect the positive and negated length-handled string restrictions, and
    // require there to be at least one positive (so the conjunction is bounded)
    // and at least one negated (otherwise the facet-free / numeric tests and the
    // direct interval logic already cover it).
    let mut positives: Vec<(Option<LengthInterval>, Option<LengthInterval>)> = Vec::new();
    let mut negatives: Vec<(Option<LengthInterval>, Option<LengthInterval>)> = Vec::new();
    for (r, _) in ranges {
        match r {
            LiteralDataRange::DatatypeRestriction(dr) => match length_intervals_for(dr) {
                Some(pair) => positives.push(pair),
                None => return false, // a non-length-handled positive range: scope out
            },
            LiteralDataRange::AtomicNegationDataRange(n) => match n.get_negated_data_range() {
                crate::model::AtomicDataRange::DatatypeRestriction(dr) => {
                    match length_intervals_for(dr) {
                        Some(pair) => negatives.push(pair),
                        None => return false,
                    }
                }
                // A negated enumeration / other: not a length range — scope out.
                _ => return false,
            },
            r if is_value_non_constraining_helper(r) => {}
            // Any other range (enumeration, etc.): scope out.
            _ => return false,
        }
    }
    if positives.is_empty() || negatives.is_empty() {
        return false;
    }
    // The starting value space is the conjunction of every positive interval pair
    // (conjoinWithDR), as a flat list of surviving intervals. Seed with the first
    // positive, then intersect each further positive into every surviving
    // interval (PRESENT against PRESENT, ABSENT against ABSENT).
    let mut space: Vec<LengthInterval> = {
        let (p, a) = positives[0];
        p.into_iter().chain(a).collect()
    };
    for (p, a) in positives.iter().skip(1) {
        let conj_intervals: Vec<LengthInterval> = p.iter().chain(a.iter()).copied().collect();
        let mut next: Vec<LengthInterval> = Vec::new();
        for old in &space {
            for ci in &conj_intervals {
                if let Some(isect) = old.intersect(*ci) {
                    next.push(isect);
                }
            }
        }
        space = next;
        if space.is_empty() {
            return true;
        }
    }
    // Conjoin each negated restriction: replace the space by its intersection
    // with the complement of the negated interval pair (conjoinWithDRNegation).
    for (p, a) in &negatives {
        let complemented = complement_length_intervals(*p, *a);
        let mut next: Vec<LengthInterval> = Vec::new();
        for old in &space {
            for ci in &complemented {
                if let Some(isect) = old.intersect(*ci) {
                    next.push(isect);
                }
            }
        }
        space = next;
        if space.is_empty() {
            return true;
        }
    }
    space.is_empty()
}

// ===========================================================================
// FIX C: string / rdf:PlainLiteral pattern + langRange value-space emptiness.
//
// Faithful port of the AUTOMATON branch of RDFPlainLiteralDatatypeHandler
// (needsAutomatons ⇒ getAutomatonFor + conjoinWithDR/conjoinWithDRNegation +
// Automaton.isEmpty / minus). Java encodes every value as
//   string · SEPARATOR('') · languageTag
// and each range's automaton is a CONCATENATION of an independent string-part and
// langtag-part (see getPatternAutomaton / getLanguageRangeAutomaton / getDatatype
// Automaton / toAutomaton). Because '' is a unique delimiter that occurs in
// neither factor (XML chars start at 	 and exclude ; language tags are
// `[A-Za-z0-9-]`), every accepted word splits uniquely at the separator and the
// intersection of two product languages factorizes:
//     (A1·B1) ∩ (A2·B2) = (A1∩A2) · (B1∩B2).
// So a POSITIVE conjunction is empty iff the string-dimension intersection is empty
// OR the langtag-dimension intersection is empty — each decidable in its own
// dimension. NEGATION (`minus`) does not factorize, but for the cases this handler
// commonly produces it still reduces to dimension reasoning: removing `¬(A·B)` from
// the survivor rectangle `S·T` leaves `{(s,t)∈S×T : ¬(s∈A ∧ t∈B)}`, which is empty
// iff `S⊆A ∧ T⊆B`. We decide that (single negation, or any negation that subsumes
// the positive rectangle); anything we cannot decide exactly scopes out (never a
// false clash).
// ===========================================================================

/// The langtag-dimension constraint a single string/PlainLiteral range imposes
/// (the langtag-part of its product automaton).
#[derive(Clone, Debug, PartialEq, Eq)]
enum TagClass {
    /// The empty tag only (`SEPARATOR` with nothing after): an `xsd:string`-rooted
    /// range, or a string subtype (concatenated with `s_emptyLangTag`).
    Absent,
    /// Any non-empty RFC 4646 language tag (`langRange "*"`).
    NonEmpty,
    /// The empty tag or any non-empty tag (`s_anyLangTag`): an `rdf:PlainLiteral`
    /// base, or a `pattern` facet (which concatenates `s_anyLangTag`).
    Any,
    /// A non-empty tag matching the basic-filter of `range` (RFC 4647): `range`
    /// itself or any extension after a `-` (`en` ⇒ `en`, `en-GB`). Lowercased.
    Range(String),
}

impl TagClass {
    /// Does the basic-filter range `a` (lowercased, non-"*") subsume range `b`?
    /// `a ⊇ b` iff every tag matching `b` also matches `a`, i.e. `a` is `b` or a
    /// prefix of `b` ending at a `-` boundary (`en ⊇ en-GB`, `en-GB ⊉ en`).
    fn range_subsumes(a: &str, b: &str) -> bool {
        a == b || b.strip_prefix(a).is_some_and(|rest| rest.starts_with('-'))
    }
    /// `self ∩ other`, or `None` when the intersection is empty.
    fn intersect(&self, other: &TagClass) -> Option<TagClass> {
        use TagClass::*;
        match (self, other) {
            (Any, x) | (x, Any) => Some(x.clone()),
            (Absent, Absent) => Some(Absent),
            (Absent, NonEmpty) | (NonEmpty, Absent) => None,
            (Absent, Range(_)) | (Range(_), Absent) => None,
            (NonEmpty, NonEmpty) => Some(NonEmpty),
            (NonEmpty, Range(r)) | (Range(r), NonEmpty) => Some(Range(r.clone())),
            (Range(a), Range(b)) => {
                if Self::range_subsumes(a, b) {
                    Some(Range(b.clone()))
                } else if Self::range_subsumes(b, a) {
                    Some(Range(a.clone()))
                } else {
                    // The two basic-filter ranges are incomparable. Their tag sets
                    // could still overlap only if neither subsumes the other — but
                    // basic filtering makes that impossible (a tag matching both
                    // would have both as prefixes ending at a boundary, so one is a
                    // prefix of the other). Hence disjoint ⇒ empty.
                    None
                }
            }
        }
    }
    /// Is every tag in `self` also in `other` (`self ⊆ other`)?
    fn subset_of(&self, other: &TagClass) -> bool {
        use TagClass::*;
        match (self, other) {
            (_, Any) => true,
            (Absent, Absent) => true,
            (Absent, _) => false,
            (NonEmpty, NonEmpty) => true,
            (NonEmpty, _) => false, // NonEmpty ⊄ Absent / a specific Range
            (Range(_), NonEmpty) => true,
            (Range(a), Range(b)) => Self::range_subsumes(b, a),
            (Range(_), Absent) => false,
            // `Any` is a subset only of `Any`, already handled by the first arm; for
            // any other `other` it is not a subset.
            (Any, _) => false,
        }
    }
}

/// The string-dimension constraint a single range imposes (the string-part of its
/// product automaton), to the extent we model it exactly. `None`-yielding parses
/// scope the whole emptiness test out.
#[derive(Clone, Debug)]
enum StrLang {
    /// Every XML string (the `xsd:string` / `rdf:PlainLiteral` base string-part,
    /// with no pattern/length constraint).
    Universe,
    /// A finite language, explicitly enumerated (from a finite `xsd:pattern`).
    Finite(std::collections::BTreeSet<String>),
}

impl StrLang {
    /// `self ∩ other`, or `None` when the intersection is provably empty. Returns
    /// `Some(Universe)`-style results only when exact.
    fn intersect(&self, other: &StrLang) -> Option<StrLang> {
        match (self, other) {
            (StrLang::Universe, x) | (x, StrLang::Universe) => Some(x.clone()),
            (StrLang::Finite(a), StrLang::Finite(b)) => {
                let inter: std::collections::BTreeSet<String> =
                    a.intersection(b).cloned().collect();
                if inter.is_empty() { None } else { Some(StrLang::Finite(inter)) }
            }
        }
    }
    /// Is every word of `self` in `other` (`self ⊆ other`)?
    fn subset_of(&self, other: &StrLang) -> bool {
        match (self, other) {
            (_, StrLang::Universe) => true,
            (StrLang::Universe, StrLang::Finite(_)) => false,
            (StrLang::Finite(a), StrLang::Finite(b)) => a.is_subset(b),
        }
    }
    fn is_empty(&self) -> bool {
        matches!(self, StrLang::Finite(s) if s.is_empty())
    }
}

/// A single range parsed into its (string-dimension, langtag-dimension) product.
struct StringRange {
    str_lang: StrLang,
    tag: TagClass,
}

/// Parse a string/PlainLiteral DatatypeRestriction into its product (string-dim ×
/// langtag-dim) constraint, for the pattern / langRange / subtype family. Returns
/// `None` for any datatype/facet we do not model exactly (length facets, large/
/// infinite patterns, unknown datatypes) ⇒ the caller scopes out.
fn parse_string_range(dr: &DatatypeRestriction) -> Option<StringRange> {
    let uri = dr.datatype_uri();
    let is_plain = uri == format!("{RDF}PlainLiteral");
    let subtype = uri.strip_prefix(XSD).filter(|s| {
        matches!(*s, "string" | "normalizedString" | "token" | "Name" | "NCName"
            | "NMTOKEN" | "language")
    });
    if !is_plain && subtype.is_none() {
        return None;
    }
    // The base string-part language (subtype automaton) and base tag class.
    let mut str_lang = match subtype {
        // We model only the unconstrained xsd:string base exactly. The other
        // subtypes have non-trivial automata we don't reproduce here; we can still
        // reason if no pattern is present by treating the subtype as a sub-universe
        // — but to stay sound we only model `string` (and PlainLiteral) as Universe
        // and scope out other subtypes that lack a finite pattern (handled below).
        Some("string") | None => StrLang::Universe,
        Some(_) => StrLang::Universe, // refined/intersected by facets below; see note
    };
    let mut tag = if is_plain { TagClass::Any } else { TagClass::Absent };
    // A subtype other than xsd:string: its base string-language is a STRICT subset
    // of the XML universe. Without a finite pattern to pin it down we cannot decide
    // emptiness exactly, so remember to scope out unless a finite pattern overrides.
    let mut subtype_unmodeled = matches!(subtype, Some(s) if s != "string");
    for i in 0..dr.number_of_facet_restrictions() {
        let facet = dr.facet_uri(i);
        let lexical = dr.facet_value(i).lexical_form();
        if facet == format!("{RDF}langRange") {
            // langRange concatenates the langtag filter onto the value; "*" ⇒ any
            // non-empty tag, otherwise a basic-filter range. The string-part stays
            // s_anyString, and (crucially) langRange forces the langtag dimension —
            // overriding an `xsd:string` Absent base would make it empty, but Java
            // applies langRange only on rdf:PlainLiteral/string; on xsd:string the
            // base is Absent and a langRange (NonEmpty/Range) intersects to empty.
            let lr = if lexical == "*" {
                TagClass::NonEmpty
            } else {
                TagClass::Range(lexical.to_ascii_lowercase())
            };
            tag = match tag.intersect(&lr) {
                Some(t) => t,
                None => {
                    // langtag dimension already empty (e.g. xsd:string ⊓ langRange).
                    return Some(StringRange { str_lang: StrLang::Finite(Default::default()), tag: TagClass::Absent });
                }
            };
        } else if facet == format!("{XSD}pattern") {
            // pattern: intersect the string-dim language; its automaton concatenates
            // s_anyLangTag, so it does NOT constrain the langtag dimension.
            match finite_pattern_lang(lexical, MAX_ENUMERATED_VALUES).and_then(|l| l.words) {
                Some(words) => {
                    let set: std::collections::BTreeSet<String> = words.into_iter().collect();
                    let finite = StrLang::Finite(set);
                    str_lang = str_lang.intersect(&finite)?;
                    subtype_unmodeled = false; // a finite pattern pins the string-dim
                }
                // Infinite / unmodeled pattern language ⇒ scope out.
                None => return None,
            }
        } else if facet.strip_prefix(XSD).is_some_and(|f| matches!(f, "minLength" | "maxLength" | "length")) {
            // Length facets put the range in the LENGTH branch, handled elsewhere;
            // mixing length with pattern/langRange is something we do not model
            // here exactly ⇒ scope out.
            return None;
        } else {
            return None;
        }
    }
    if subtype_unmodeled {
        return None;
    }
    Some(StringRange { str_lang, tag })
}

/// Build the combined-alphabet automaton HermiT's `RDFPlainLiteralDatatypeHandler.
/// getAutomatonFor(DatatypeRestriction)` builds for a single string /
/// rdf:PlainLiteral datatype restriction (base datatype automaton, intersected
/// with each pattern / langRange / length facet). The combined alphabet is
/// `string-chars · SEPARATOR · langtag-chars`.
///
/// Returns:
///   * `Some(Some(a))` — the restriction's automaton (possibly accepting an
///     infinite language);
///   * `Some(None)`    — the restriction is MODELLED but its automaton is empty
///     (Java returns `null` / EMPTY_SUBSET): this still contributes emptiness;
///   * `None`          — the datatype / a facet is not modelled exactly ⇒ the
///     caller must scope out (never a false clash).
fn automaton_for_string_restriction(dr: &DatatypeRestriction) -> Option<Option<crate::string_automaton::Automaton>> {
    use crate::string_automaton as sa;
    let uri = dr.datatype_uri();
    let is_plain = uri == format!("{RDF}PlainLiteral");
    let local = uri.strip_prefix(XSD);
    let mut automaton = if is_plain {
        sa::datatype_automaton("", true)?
    } else {
        sa::datatype_automaton(local?, false)?
    };
    let mut min_length: usize = 0;
    let mut max_length: Option<usize> = None;
    for i in 0..dr.number_of_facet_restrictions() {
        let facet = dr.facet_uri(i);
        let lexical = dr.facet_value(i).lexical_form();
        if facet == format!("{XSD}pattern") {
            let pat = sa::pattern_automaton(lexical)?;
            automaton = automaton.intersection(&pat);
        } else if facet == format!("{RDF}langRange") {
            let lr = sa::language_range_automaton(lexical);
            automaton = automaton.intersection(&lr);
        } else if let Some(f) = facet.strip_prefix(XSD) {
            match f {
                "minLength" => {
                    let v: usize = lexical.trim().parse().ok()?;
                    min_length = min_length.max(v);
                }
                "maxLength" => {
                    let v: usize = lexical.trim().parse().ok()?;
                    max_length = Some(max_length.map_or(v, |m| m.min(v)));
                }
                "length" => {
                    let v: usize = lexical.trim().parse().ok()?;
                    min_length = min_length.max(v);
                    max_length = Some(max_length.map_or(v, |m| m.min(v)));
                }
                _ => return None,
            }
        } else {
            return None;
        }
    }
    if let Some(max) = max_length {
        if min_length > max {
            return Some(None);
        }
    }
    if min_length != 0 || max_length.is_some() {
        let len_aut = sa::length_automaton(min_length, max_length, sa::LangMode::Any);
        automaton = automaton.intersection(&len_aut);
    }
    if automaton.is_empty() {
        Some(None)
    } else {
        Some(Some(automaton))
    }
}

/// FIX C (automaton port): whether the conjunction of string / rdf:PlainLiteral
/// ranges carrying pattern / langRange / length facets (over the string subtypes)
/// is provably empty, mirroring the AUTOMATON branch of
/// RDFPlainLiteralDatatypeHandler exactly: intersect every positive restriction's
/// combined-alphabet automaton, `minus` each negated restriction's automaton, and
/// report empty iff the resulting automaton is empty. Scopes out (returns false)
/// for any datatype / facet / regex we do not model — never a false clash.
fn pattern_langrange_automaton_is_empty<D>(ranges: &[(LiteralDataRange, D)]) -> bool {
    use crate::string_automaton::Automaton;
    let mut positives: Vec<Automaton> = Vec::new();
    let mut negatives: Vec<Automaton> = Vec::new();
    let mut saw_positive = false;
    for (r, _) in ranges {
        match r {
            LiteralDataRange::DatatypeRestriction(dr) => match automaton_for_string_restriction(dr) {
                Some(Some(a)) => {
                    positives.push(a);
                    saw_positive = true;
                }
                // Modelled-but-empty positive restriction ⇒ the whole conjunction
                // is empty (a value forced into an empty value space).
                Some(None) => return true,
                None => return false, // unmodelled ⇒ scope out
            },
            LiteralDataRange::AtomicNegationDataRange(n) => match n.get_negated_data_range() {
                crate::model::AtomicDataRange::DatatypeRestriction(dr) => {
                    match automaton_for_string_restriction(dr) {
                        // A negated restriction with an EMPTY automaton removes
                        // nothing (¬∅ = universe); skip it.
                        Some(None) => {}
                        Some(Some(a)) => negatives.push(a),
                        None => return false, // unmodelled negation ⇒ scope out
                    }
                }
                // A negated internal datatype (e.g. ¬rdfs:Literal) is SKIPPED, exactly
                // like a positive internal datatype: Java's DatatypeChecker.DVariable.
                // addDataRange ignores it (DatatypeChecker.java:391-394). It removes
                // nothing from the conjunction, so it must not disable this check.
                crate::model::AtomicDataRange::InternalDatatype(_) => {}
                _ => return false,
            },
            r if is_value_non_constraining_helper(r) => {}
            _ => return false,
        }
    }
    if !saw_positive {
        return false;
    }
    // Conjoin the positives.
    let mut result = positives[0].clone();
    for p in &positives[1..] {
        result = result.intersection(p);
        if result.is_empty() {
            return true;
        }
    }
    // Subtract each negation (result \ neg = result ∩ ¬neg).
    for neg in &negatives {
        result = result.minus(neg);
        if result.is_empty() {
            return true;
        }
    }
    result.is_empty()
}

/// FIX (case 4): the exact value space (cardinality, and the materialized values
/// when small) of a conjunction of string / rdf:PlainLiteral datatype restrictions
/// (with their pattern / langRange / length facets) and negated such restrictions,
/// via the combined-alphabet automaton — mirroring HermiT's
/// `RDFPlainLiteralPatternValueSpaceSubset.getFiniteStrings`/`hasCardinalityAtLeast`.
///
/// Returns `None` (scope out) when any range is not a modelled string restriction
/// or is a value-removing exclusion the automaton cannot represent (a negated
/// oneOf / constant), so this never under-counts. Each accepted word is
/// `string · SEPARATOR · langtag`; an empty langtag denotes an `xsd:string` value,
/// a non-empty one an `rdf:PlainLiteral` (string,lang) value.
fn string_automaton_value_space<D>(ranges: &[(LiteralDataRange, D)]) -> Option<NodeValueSpace> {
    use crate::string_automaton::{Automaton, SEPARATOR};
    let mut positives: Vec<Automaton> = Vec::new();
    let mut negatives: Vec<Automaton> = Vec::new();
    // Forbidden (negated oneOf / negated constant) values, as their combined-alphabet
    // singleton automata: `string · SEPARATOR · langtag`. Java
    // (DatatypeChecker.DVariable) keeps these as `m_forbiddenDataValues` and removes
    // them from the value-space subset; we model that by `minus`-ing each singleton.
    let mut forbidden: Vec<Automaton> = Vec::new();
    // Build the combined-alphabet singleton for one excluded string/langString value.
    // Returns `None` (caller scopes out) for a non-string value or one carrying a
    // code point outside the modelled XML alphabet — subtracting such a word from
    // the value-space automaton could not be represented faithfully. (A non-string
    // value can never be in a string value space, so it removes nothing; but we are
    // conservative and only commit to the exact-difference count when every excluded
    // value is representable, mirroring Java's exact forbidden-value bookkeeping.)
    let singleton_for = |value: &DataValue| -> Option<Automaton> {
        let (string, lang): (&str, String) = match value {
            DataValue::Text(s) => (s.as_str(), String::new()),
            // RDFPlainLiteralDataValue lower-cases the language tag (see Java
            // RDFPlainLiteralPatternValueSpaceSubset.containsDataValue).
            DataValue::LangString { string, lang } => (string.as_str(), lang.to_ascii_lowercase()),
            // A non-string value is not in any string value space.
            _ => return None,
        };
        // Every char must be in the XML string alphabet the automata use; otherwise
        // the singleton (and hence the difference) is not faithfully representable.
        let in_alphabet = |c: char| {
            let cp = c as u32;
            matches!(cp, 0x09 | 0x0A | 0x20..=0x7F | 0xA0..=0xD7FF | 0xE000..=0xFFFD)
        };
        if !string.chars().all(in_alphabet) || !lang.chars().all(in_alphabet) {
            return None;
        }
        let mut a = Automaton::literal(string);
        a = a.concatenate(&Automaton::char(SEPARATOR));
        if !lang.is_empty() {
            a = a.concatenate(&Automaton::literal(&lang));
        }
        Some(a)
    };
    for (r, _) in ranges {
        match r {
            LiteralDataRange::DatatypeRestriction(dr) => match automaton_for_string_restriction(dr) {
                Some(Some(a)) => positives.push(a),
                Some(None) => return Some(NodeValueSpace::Finite { count: 0, values: Some(Vec::new()) }),
                None => return None,
            },
            LiteralDataRange::AtomicNegationDataRange(n) => match n.get_negated_data_range() {
                crate::model::AtomicDataRange::DatatypeRestriction(dr) => {
                    match automaton_for_string_restriction(dr) {
                        Some(None) => {} // ¬∅ removes nothing
                        Some(Some(a)) => negatives.push(a),
                        None => return None,
                    }
                }
                // A negated oneOf / negated constant enumeration: each of its members
                // is a forbidden value. Build a singleton automaton for each and
                // subtract it from the conjunction (Java's m_forbiddenDataValues).
                crate::model::AtomicDataRange::ConstantEnumeration(e) => {
                    for i in 0..e.number_of_constants() {
                        let c = e.constant(i);
                        match parse_value(c) {
                            // A recognised-but-ill-typed forbidden literal denotes
                            // nothing, so it removes nothing — skip it (sound).
                            None if is_ill_typed(c) => {}
                            // An unparseable / unrecognised forbidden value cannot be
                            // represented; scope out rather than risk an over-removal.
                            None => return None,
                            Some(value) => match singleton_for(&value) {
                                Some(a) => forbidden.push(a),
                                // Non-string value: not in the string space, removes
                                // nothing. A value with an out-of-alphabet char is
                                // likewise not in the (XML-alphabet) space, removes
                                // nothing. Both are sound to skip.
                                None => {}
                            },
                        }
                    }
                }
                // A negated internal datatype (e.g. ¬rdfs:Literal) is SKIPPED, exactly
                // like a positive internal datatype: Java's DatatypeChecker.DVariable.
                // addDataRange ignores it (DatatypeChecker.java:391-394). It removes
                // nothing, so it must not turn an otherwise-decidable value space into
                // a scope-out.
                crate::model::AtomicDataRange::InternalDatatype(_) => {}
            },
            r if is_value_non_constraining_helper(r) => {}
            _ => return None,
        }
    }
    if positives.is_empty() {
        return None;
    }
    let mut result = positives[0].clone();
    for p in &positives[1..] {
        result = result.intersection(p);
    }
    for neg in &negatives {
        result = result.minus(neg);
    }
    for f in &forbidden {
        result = result.minus(f);
    }
    // Cardinality first (cheap), then materialize only when small.
    let count = result.cardinality()?; // None ⇒ infinite ⇒ scope out (Infinite handled by caller's fallthrough)
    if count == 0 {
        return Some(NodeValueSpace::Finite { count: 0, values: Some(Vec::new()) });
    }
    if count <= MAX_ENUMERATED_VALUES as u128 {
        if let Some(words) = result.finite_strings(MAX_ENUMERATED_VALUES) {
            let mut out: Vec<DataValue> = Vec::new();
            for w in words {
                let value = match w.char_indices().rev().find(|&(_, c)| c as u32 == SEPARATOR) {
                    Some((idx, _)) => {
                        let string = &w[..idx];
                        let lang = &w[idx + 1..];
                        if lang.is_empty() {
                            DataValue::Text(string.to_string())
                        } else {
                            DataValue::LangString { string: string.to_string(), lang: lang.to_string() }
                        }
                    }
                    // No separator (shouldn't happen for a well-formed combined word);
                    // treat the whole word as a plain string.
                    None => DataValue::Text(w.clone()),
                };
                if !out.iter().any(|v| values_equal(v, &value)) {
                    out.push(value);
                }
            }
            return Some(NodeValueSpace::Finite { count: out.len() as u128, values: Some(out) });
        }
    }
    Some(NodeValueSpace::Finite { count, values: None })
}

/// FIX C: whether the conjunction of string / rdf:PlainLiteral ranges carrying
/// pattern / langRange (and the unconstrained subtype base) facets is provably
/// empty, mirroring the AUTOMATON branch of RDFPlainLiteralDatatypeHandler.
/// Decides the langtag-dimension exactly (TagClass algebra) and the string-dimension
/// exactly for finite patterns / the universe; scopes out (returns false) for
/// anything it cannot decide — never a false clash.
fn pattern_langrange_value_space_is_empty<D>(ranges: &[(LiteralDataRange, D)]) -> bool {
    // First try the faithful automaton port (handles infinite languages, multi-
    // negation cover, string subtypes). If it can decide, trust it; otherwise fall
    // back to the lightweight TagClass/finite-pattern algebra below (which scopes
    // out in the same conservative way).
    if pattern_langrange_automaton_is_empty(ranges) {
        return true;
    }
    pattern_langrange_value_space_is_empty_legacy(ranges)
}

#[allow(clippy::needless_range_loop)]
fn pattern_langrange_value_space_is_empty_legacy<D>(ranges: &[(LiteralDataRange, D)]) -> bool {
    let mut positives: Vec<StringRange> = Vec::new();
    let mut negatives: Vec<StringRange> = Vec::new();
    for (r, _) in ranges {
        match r {
            LiteralDataRange::DatatypeRestriction(dr) => match parse_string_range(dr) {
                Some(sr) => positives.push(sr),
                None => return false,
            },
            LiteralDataRange::AtomicNegationDataRange(n) => {
                match n.get_negated_data_range() {
                    crate::model::AtomicDataRange::DatatypeRestriction(dr) => {
                        match parse_string_range(dr) {
                            Some(sr) => negatives.push(sr),
                            None => return false,
                        }
                    }
                    // ¬(internal datatype) is skipped (Java addDataRange ignores it).
                    crate::model::AtomicDataRange::InternalDatatype(_) => {}
                    _ => return false,
                }
            }
            r if is_value_non_constraining_helper(r) => {}
            _ => return false,
        }
    }
    if positives.is_empty() {
        return false;
    }
    // Conjoin the positives (factorized intersection per dimension).
    let mut str_lang = StrLang::Universe;
    let mut tag = TagClass::Any;
    for p in &positives {
        match str_lang.intersect(&p.str_lang) {
            Some(s) => str_lang = s,
            None => return true, // string-dim empty ⇒ whole product empty
        }
        match tag.intersect(&p.tag) {
            Some(t) => tag = t,
            None => return true, // langtag-dim empty ⇒ whole product empty
        }
    }
    if str_lang.is_empty() {
        return true;
    }
    // Subtract each negation. Removing ¬(A·B) from the survivor rectangle (S·T)
    // leaves {(s,t) : s∈S,t∈T, ¬(s∈A ∧ t∈B)}. A single negation empties the
    // rectangle iff S⊆A ∧ T⊆B. With several negations the survivor is empty iff the
    // rectangle is covered by the union of the (A_i×B_i); we decide the case where
    // SOME negation already covers it (the common, faithful subcase) and otherwise
    // scope out.
    for nrange in &negatives {
        if str_lang.subset_of(&nrange.str_lang) && tag.subset_of(&nrange.tag) {
            return true;
        }
    }
    // We could not prove emptiness (multi-negation cover or unmodeled overlap).
    false
}

/// The base-datatype value-space-class subset test for the non-numeric kinds
/// (string/boolean/datetime/binary/anyURI/…) and as a fast path for the numeric
/// ones: the conjunction is empty when some positive datatype restriction whose
/// *base* datatype is `P` carries a facet-free negated datatype `¬N` with
/// value-space(P) ⊆ value-space(N).
///
/// Crucially, FACETS on the POSITIVE side are ignored — they can only shrink its
/// value space, so `P[facets] ⊆ P ⊆ N` still holds (e.g. `string[minLength 3]`,
/// whose base is `xsd:string`, is subsumed by `¬xsd:string`; `integer[≥0]`, whose
/// base is `xsd:integer`, is subsumed by `¬xsd:decimal`). The negated side is
/// required to be facet-free, so its value space is the full base class and the
/// removal of `P` is total; the faceted-negated numeric case is decided exactly
/// by the numeric lattice in `negation_subsumes`. Value-non-constraining helper
/// ranges (`rdfs:Literal`/`internal:*`) are transparent here too.
fn base_datatype_negation_subsumes<D>(ranges: &[(LiteralDataRange, D)]) -> bool {
    // The facet-free negated atomic datatype classes asserted on the node.
    let negated_classes: Vec<ValueSpaceClass> = ranges
        .iter()
        .filter_map(|(r, _)| match r {
            LiteralDataRange::AtomicNegationDataRange(n) => match n.get_negated_data_range() {
                crate::model::AtomicDataRange::DatatypeRestriction(dr)
                    if dr.number_of_facet_restrictions() == 0 =>
                {
                    value_space_class(dr.datatype_uri())
                }
                _ => None,
            },
            _ => None,
        })
        .collect();
    if negated_classes.is_empty() {
        return false;
    }
    // For each positive datatype restriction, if its BASE value space (facets
    // dropped — they only shrink it) is a subset of some negated datatype's
    // value space, the whole conjunction is empty (every value forced in is
    // excluded).
    ranges.iter().any(|(r, _)| {
        if let LiteralDataRange::DatatypeRestriction(dr) = r {
            if let Some(pos) = value_space_class(dr.datatype_uri()) {
                return negated_classes
                    .iter()
                    .any(|neg| value_space_is_subset(&pos, neg));
            }
        }
        false
    })
}

/// Whether the conjunction of the given (positive) data ranges is provably
/// empty. Sound: returns true only when emptiness is certain.
fn conjunction_is_empty<D>(ranges: &[(LiteralDataRange, D)]) -> bool {
    // A negated datatype that removes the whole of a positive datatype's value
    // space empties the conjunction even when that value space is infinite
    // (e.g. `integer ⊓ ¬integer`). The interval/enumeration logic below only
    // sees the positive ranges, so handle this subsumption case up front.
    if negation_subsumes(ranges) {
        return true;
    }
    // If any oneOf is present, the value must be one of its (parseable) members
    // that also satisfies every other range.
    if let Some((one_of, _)) = ranges
        .iter()
        .find(|(r, _)| matches!(r, LiteralDataRange::ConstantEnumeration(_)))
    {
        let LiteralDataRange::ConstantEnumeration(enumeration) = one_of else {
            unreachable!()
        };
        let mut all_parseable = true;
        for i in 0..enumeration.number_of_constants() {
            let c = enumeration.constant(i);
            match parse_value(c) {
                Some(candidate) => {
                    if ranges.iter().all(|(r, _)| value_in_range(&candidate, r) == Some(true)) {
                        return false; // a feasible candidate exists
                    }
                }
                // Java: recognized-but-ill-typed literal denotes nothing (MalformedLiteralException
                // at clausification) — skip it; it contributes no candidate.
                // Unrecognized datatype may denote anything, so mark not-all-parseable.
                None if is_ill_typed(c) => {}
                None => all_parseable = false,
            }
        }
        return all_parseable; // empty iff every member was parseable/ill-typed and excluded
    }

    // Otherwise, only datatype restrictions / internal datatypes / negations.
    // A value must lie in every restriction's base datatype; numeric, string and
    // boolean kinds are mutually exclusive.
    let mut kinds: std::collections::HashSet<&'static str> = std::collections::HashSet::new();
    let mut lower: Option<Bound> = None;
    let mut upper: Option<Bound> = None;
    // Whether the numeric value space is restricted to the integers. The
    // intersection of an integer base with any other numeric range stays
    // integer-valued, so any integer-based restriction makes the whole
    // conjunction integer-based (OWLRealDatatypeHandler.getIntervalFor builds an
    // INTEGER NumberInterval, whose isIntervalEmpty rounds the bounds inward).
    let mut integer_based = false;
    for (range, _) in ranges {
        if let LiteralDataRange::DatatypeRestriction(r) = range {
            let uri = r.datatype_uri();
            if is_integer_datatype(uri) {
                integer_based = true;
            }
            let kind = if is_integer_datatype(uri)
                || is_decimal_datatype(uri)
                || is_rational_datatype(uri)
                || is_real_datatype(uri)
            {
                "numeric"
            } else if is_xsd_float(uri) {
                // xsd:float, xsd:double and the owl:real family are managed by
                // distinct handlers in HermiT; values of different handlers are
                // disjoint (DatatypeRegistry.isDisjointWith), so they must be
                // separate kinds for the incompatible-base-datatype check below.
                "float"
            } else if is_xsd_double(uri) {
                "double"
            } else if is_string_datatype(uri) {
                "string"
            } else if is_boolean_datatype(uri) {
                "boolean"
            } else if is_datetime_datatype(uri) {
                "datetime"
            } else if is_anyuri_datatype(uri) {
                "anyURI"
            } else if is_hex_binary_datatype(uri) {
                "hexBinary"
            } else if is_base64_datatype(uri) {
                "base64Binary"
            } else {
                continue; // unknown datatype -> cannot decide -> ignore
            };
            kinds.insert(kind);
            // Seed the datatype's implicit value-space bounds (e.g.
            // xsd:nonNegativeInteger is [0, +INF), xsd:unsignedByte is [0, 255])
            // before refining with the explicit facets, matching
            // OWLRealDatatypeHandler.getIntervalFor (which starts from the base
            // interval). Without this, an empty conjunction such as
            // `nonNegativeInteger ⊓ maxInclusive -1` is not detected.
            if let Some((implicit_min, implicit_max)) = integer_datatype_bounds(uri) {
                if let Some(min) = implicit_min {
                    let value = (BigInt::from(min), BigInt::one());
                    if lower
                        .as_ref()
                        .is_none_or(|b| cmp_exact(&value, &b.value).is_gt())
                    {
                        lower = Some(Bound { value, inclusive: true });
                    }
                }
                if let Some(max) = implicit_max {
                    let value = (BigInt::from(max), BigInt::one());
                    if upper
                        .as_ref()
                        .is_none_or(|b| cmp_exact(&value, &b.value).is_lt())
                    {
                        upper = Some(Bound { value, inclusive: true });
                    }
                }
            }
            for i in 0..r.number_of_facet_restrictions() {
                accumulate_numeric_bound(r.facet_uri(i), r.facet_value(i), &mut lower, &mut upper);
            }
        }
    }
    if kinds.len() >= 2 {
        return true; // incompatible base datatypes
    }
    if let (Some(lo), Some(hi)) = (&lower, &upper) {
        if integer_based {
            // NumberInterval.isIntervalEmpty for an INTEGER base range rounds the
            // bounds to the nearest contained integer and tests lower > upper, so
            // intervals empty over the integers but not the reals (e.g.
            // `integer[minExclusive 2, maxExclusive 3]`) are detected.
            let lo_int = nearest_integer_in_bound(&lo.value, true, lo.inclusive);
            let hi_int = nearest_integer_in_bound(&hi.value, false, hi.inclusive);
            if lo_int > hi_int {
                return true; // empty integer interval
            }
        } else {
            let ord = cmp_exact(&lo.value, &hi.value);
            if ord.is_gt() || (ord.is_eq() && (!lo.inclusive || !hi.inclusive)) {
                return true; // empty numeric interval
            }
        }
    }
    // xsd:dateTime / xsd:dateTimeStamp: the ordering facets carve out an
    // interval whose emptiness must be decided explicitly. The four ordering
    // facets are kept as exact instants (BigInt fractions) above are not
    // applicable here (datetime instants are not owl:real values), so build the
    // datetime interval(s) directly and detect an empty intersection, mirroring
    // DateTimeDatatypeHandler.getIntervalsFor + DateTimeInterval.isIntervalEmpty.
    if kinds.contains("datetime") {
        let datetime_restrictions: Vec<&DatatypeRestriction> = ranges
            .iter()
            .filter_map(|(r, _)| match r {
                LiteralDataRange::DatatypeRestriction(r)
                    if is_datetime_datatype(r.datatype_uri()) =>
                {
                    Some(r)
                }
                _ => None,
            })
            .collect();
        if datetime_value_space_is_empty(&datetime_restrictions) {
            return true;
        }
    }
    false
}

/// Maximum timezone correction, in MILLISECONDS: XSD timezone offsets range over
/// ±14:00, so a timezone-less instant maps to a window of width
/// `2 * MAX_TZ_CORRECTION_MILLIS` on the timeline. Mirrors Java's
/// `DateTime.MAX_TIME_ZONE_CORRECTION` (14h, in milliseconds).
const MAX_TZ_CORRECTION_MILLIS: i64 = 14 * 60 * 60 * 1000;

/// A single dateTime interval on the timeline: `[lower, upper]` with each bound
/// inclusive or exclusive. Mirrors Java `DateTimeInterval` (one per interval
/// type — WITH_TIMEZONE / WITHOUT_TIMEZONE). `None` represents an empty
/// interval (Java models this as a `null` interval after `intersectWith`).
///
/// The bounds are EXACT integer milliseconds (mirroring Java `DateTimeInterval`'s
/// `long` bounds). `i64::MIN` / `i64::MAX` serve as the −∞ / +∞ sentinels for an
/// unbounded side (the real instants for years in [-9999, 9999] are far from
/// these extremes, so the sentinels never collide with a genuine instant).
#[derive(Clone, Copy)]
struct DtInterval {
    lower: i64,
    lower_inclusive: bool,
    upper: i64,
    upper_inclusive: bool,
}

impl DtInterval {
    fn all() -> Self {
        DtInterval {
            lower: i64::MIN,
            lower_inclusive: false,
            upper: i64::MAX,
            upper_inclusive: false,
        }
    }
    /// DateTimeInterval.isIntervalEmpty: empty when `lower > upper`, or
    /// `lower == upper` with either bound exclusive.
    fn is_empty(&self) -> bool {
        self.lower > self.upper
            || (self.lower == self.upper && (!self.lower_inclusive || !self.upper_inclusive))
    }
    /// DateTimeInterval.intersectWith: take the more restrictive of each bound;
    /// `None` (empty) on an empty result.
    fn intersect(self, other: DtInterval) -> Option<DtInterval> {
        let (lower, lower_inclusive) = if self.lower > other.lower {
            (self.lower, self.lower_inclusive)
        } else if self.lower < other.lower {
            (other.lower, other.lower_inclusive)
        } else {
            // Equal lower bounds: exclusive is the more restrictive.
            (self.lower, self.lower_inclusive && other.lower_inclusive)
        };
        let (upper, upper_inclusive) = if self.upper < other.upper {
            (self.upper, self.upper_inclusive)
        } else if self.upper > other.upper {
            (other.upper, other.upper_inclusive)
        } else {
            (self.upper, self.upper_inclusive && other.upper_inclusive)
        };
        let result = DtInterval { lower, lower_inclusive, upper, upper_inclusive };
        if result.is_empty() {
            None
        } else {
            Some(result)
        }
    }
}

/// Whether the conjunction of the given dateTime datatype restrictions has an
/// empty value space, mirroring `DateTimeDatatypeHandler.getIntervalsFor`
/// followed by `DateTimeValueSpaceSubset` over the two interval types: HermiT
/// keeps a WITH_TIMEZONE interval (always) and a WITHOUT_TIMEZONE interval
/// (only for `xsd:dateTime`, not `xsd:dateTimeStamp`, which mandates a
/// timezone). Each min/max facet intersects both intervals; a timezone-less
/// instant maps the opposite-type interval's bound by ±MAX_TZ_CORRECTION (made
/// exclusive). The value space is empty iff *both* intervals collapse to empty.
fn datetime_value_space_is_empty(restrictions: &[&DatatypeRestriction]) -> bool {
    if restrictions.is_empty() {
        return false;
    }
    let (with_tz, without_tz) = datetime_value_space(restrictions);
    with_tz.is_none() && without_tz.is_none()
}

/// Complement of a single `DtInterval` for one timezone type: returns the (up to
/// two) half-open intervals that cover the timeline minus `[iv.lower, iv.upper]`.
/// Mirrors the `complementedIntervals` construction in `conjoinWithDRNegation`.
fn complement_dt_interval(iv: Option<DtInterval>) -> Vec<DtInterval> {
    let Some(iv) = iv else {
        // Negated DR's interval for this tz-type was already empty ⇒ complement = all.
        return vec![DtInterval::all()];
    };
    let mut out = Vec::new();
    // Before part: (-INF, lower) with flipped lower inclusivity. `i64::MIN` is the
    // −∞ sentinel, so a lower bound equal to it means the interval is unbounded
    // below and there is no "before" complement part.
    if iv.lower != i64::MIN {
        out.push(DtInterval {
            lower: i64::MIN,
            lower_inclusive: false,
            upper: iv.lower,
            upper_inclusive: !iv.lower_inclusive,
        });
    }
    // After part: (upper, +INF) with flipped upper inclusivity. `i64::MAX` is the
    // +∞ sentinel.
    if iv.upper != i64::MAX {
        out.push(DtInterval {
            lower: iv.upper,
            lower_inclusive: !iv.upper_inclusive,
            upper: i64::MAX,
            upper_inclusive: false,
        });
    }
    out
}

/// Whether a conjunction containing positive and negated dateTime DRs has an
/// empty value space after applying `conjoinWithDRNegation` for each negated DR.
/// Scopes out (returns false) when any value-constraining range is not a
/// datetime DR — never a false clash. Mirrors `length_value_space_is_empty`.
fn datetime_negation_value_space_is_empty<D>(ranges: &[(LiteralDataRange, D)]) -> bool {
    let mut pos_drs: Vec<&DatatypeRestriction> = Vec::new();
    let mut neg_drs: Vec<&DatatypeRestriction> = Vec::new();
    for (r, _) in ranges {
        match r {
            LiteralDataRange::DatatypeRestriction(dr) if is_datetime_datatype(dr.datatype_uri()) => {
                pos_drs.push(dr);
            }
            LiteralDataRange::AtomicNegationDataRange(n) => {
                match n.get_negated_data_range() {
                    crate::model::AtomicDataRange::DatatypeRestriction(dr)
                        if is_datetime_datatype(dr.datatype_uri()) =>
                    {
                        neg_drs.push(dr);
                    }
                    _ => return false, // non-datetime negation: scope out
                }
            }
            r if is_value_non_constraining_helper(r) => {}
            _ => return false, // non-datetime positive range: scope out
        }
    }
    if pos_drs.is_empty() || neg_drs.is_empty() {
        return false;
    }
    // Build the positive space: `(space_wtz, space_notz)` after intersecting all positive DRs.
    let (pos_wtz, pos_notz) = datetime_value_space(&pos_drs);
    let mut space_wtz: Vec<DtInterval> = pos_wtz.into_iter().collect();
    let mut space_notz: Vec<DtInterval> = pos_notz.into_iter().collect();
    // For each negated DR apply conjoinWithDRNegation: replace each surviving interval
    // by its intersection with the complement of the negated DR's interval.
    for neg_dr in &neg_drs {
        let (neg_wtz, neg_notz) = datetime_value_space(std::slice::from_ref(neg_dr));
        let comp_wtz = complement_dt_interval(neg_wtz);
        let comp_notz = complement_dt_interval(neg_notz);
        space_wtz = space_wtz.iter().flat_map(|old| comp_wtz.iter().filter_map(|c| old.intersect(*c))).collect();
        space_notz = space_notz.iter().flat_map(|old| comp_notz.iter().filter_map(|c| old.intersect(*c))).collect();
    }
    space_wtz.is_empty() && space_notz.is_empty()
}

/// Builds the two dateTime intervals (WITH_TIMEZONE, WITHOUT_TIMEZONE) for the
/// given restrictions, each `None` when that interval type collapses to empty.
/// Shared by the emptiness test and the single-instant cardinality computation.
fn datetime_value_space(
    restrictions: &[&DatatypeRestriction],
) -> (Option<DtInterval>, Option<DtInterval>) {
    // INTERVAL_ALL_WITH_TIMEZONE is always present.
    let mut with_tz: Option<DtInterval> = Some(DtInterval::all());
    // INTERVAL_ALL_WITHOUT_TIMEZONE is present only when no restriction is
    // xsd:dateTimeStamp (dateTimeStamp forbids timezone-less values).
    let allows_no_tz = restrictions
        .iter()
        .all(|r| r.datatype_uri().strip_prefix(XSD) != Some("dateTimeStamp"));
    let mut without_tz: Option<DtInterval> = if allows_no_tz {
        Some(DtInterval::all())
    } else {
        None
    };

    for r in restrictions {
        for i in 0..r.number_of_facet_restrictions() {
            let Some(facet) = r.facet_uri(i).strip_prefix(XSD) else {
                continue;
            };
            let inclusive = match facet {
                "minInclusive" | "maxInclusive" => true,
                "minExclusive" | "maxExclusive" => false,
                _ => continue,
            };
            let is_min = matches!(facet, "minInclusive" | "minExclusive");
            // A facet value we cannot parse leaves the intervals unchanged
            // (undecided ⇒ never a false clash).
            let Some(DataValue::DateTime { millis, has_tz, .. }) = parse_value(r.facet_value(i)) else {
                continue;
            };
            // For each interval type, build the half-bounded interval the facet
            // implies and intersect it in. When the facet bound's timezone
            // presence differs from the interval type, widen by the maximum
            // timezone correction and force the bound exclusive (matching Java).
            for (interval, interval_has_tz) in
                [(&mut with_tz, true), (&mut without_tz, false)]
            {
                let Some(current) = *interval else {
                    continue; // already empty for this interval type
                };
                let (bound, bound_inclusive) = if has_tz == interval_has_tz {
                    (millis, inclusive)
                } else if is_min {
                    (millis.saturating_add(MAX_TZ_CORRECTION_MILLIS), false)
                } else {
                    (millis.saturating_sub(MAX_TZ_CORRECTION_MILLIS), false)
                };
                let half = if is_min {
                    DtInterval {
                        lower: bound,
                        lower_inclusive: bound_inclusive,
                        upper: i64::MAX,
                        upper_inclusive: false,
                    }
                } else {
                    DtInterval {
                        lower: i64::MIN,
                        lower_inclusive: false,
                        upper: bound,
                        upper_inclusive: bound_inclusive,
                    }
                };
                *interval = current.intersect(half);
            }
        }
    }
    (with_tz, without_tz)
}

/// The exact number of distinct dateTime literals that map to a single timeline
/// instant `seconds` (UTC-normalized), for the given interval type. Mirrors
/// `DateTimeInterval.subtractSizeFrom` for the singleton (`lower == upper`) case:
///   * WITHOUT_TIMEZONE: one value, plus one more when the instant is a "last day
///     instant" (midnight), since `24:00:00` of the previous day and `00:00:00`
///     of this day denote the same point but are distinct literals;
///   * WITH_TIMEZONE: 840 + 840 + 1 = 1681 base values (timezone offsets
///     hh:mm with 0 ≤ hh < 14, 0 ≤ mm < 60, or 14:00, on each side, minus the
///     doubly-counted 00:00), plus up to two more last-day-instant variants when
///     the instant's seconds are zero.
/// `millis` is the timeline instant as an EXACT integer count of MILLISECONDS on
/// the UNIX epoch (matching `DataValue::DateTime.millis`). Java's
/// `m_timeOnTimeline` is also a `long` in milliseconds, but on a YEAR-1 origin;
/// the conversion below realigns the origin before the sign-sensitive arithmetic.
fn datetime_instant_cardinality(millis: i64, has_timezone: bool) -> u128 {
    // Java works in integer milliseconds on a YEAR-1 origin timeline
    // (DateTime.getTimeOnTimelineRaw, DateTime.java:251-261): the instant of
    // 0001-01-01T00:00:00 is 0, and earlier (BCE) instants are negative. Our
    // `millis` is a UTC-normalized instant on the UNIX epoch (1970-01-01),
    // because `days_from_civil` applies the -719468 offset. The two origins
    // differ by a whole number of days, which does not affect the day/minute
    // modular predicates (isLastDayInstant, secondsAreZero) — but it DOES affect
    // the `m_lowerBound>=0` sign branch and `getMinutesInDay`
    // (DateTimeInterval.java:113-133, DateTime.java:284-286): a date in
    // [year 1, 1970) has a POSITIVE year-1-origin time but a NEGATIVE unix time.
    // So convert to the year-1 origin before any sign-sensitive computation.
    //
    // The unix epoch 1970-01-01 is at year-1-origin day daysToYearStart(1970) =
    // 365*1969 + 1969/400 - 1969/100 + 1969/4 = 719162 days
    // (DateTime.daysToYearStart, DateTime.java:262-265).
    const YEAR1_ORIGIN_OFFSET_DAYS: i64 = 719162;
    let ms_per_minute: i64 = 1000 * 60;
    let ms_per_day: i64 = ms_per_minute * 60 * 24;
    let time_on_timeline: i64 = millis + YEAR1_ORIGIN_OFFSET_DAYS * ms_per_day;
    // DateTime.isLastDayInstant.
    let is_last_day_instant = time_on_timeline.rem_euclid(ms_per_day) == 0;
    // DateTime.secondsAreZero.
    let seconds_are_zero = time_on_timeline.rem_euclid(ms_per_minute) == 0;
    // DateTime.getMinutesInDay: (int)((t / 60000) % 1440) — Java truncating
    // division and `%`, which keep the sign of the dividend.
    let minutes_in_day: i64 = (time_on_timeline / ms_per_minute) % (24 * 60);

    if !has_timezone {
        // WITHOUT_TIMEZONE: one value, +1 for a last-day (midnight) instant.
        let mut n: u128 = 1;
        if is_last_day_instant {
            n += 1;
        }
        n
    } else {
        // WITH_TIMEZONE: 840 + 840 + 1 base values, +extras at last-day instants.
        let mut n: u128 = 840 + 840 + 1;
        if seconds_are_zero {
            if time_on_timeline >= 0 {
                let m = minutes_in_day; // in [0, 1440)
                if (0..=840).contains(&m) {
                    n += 1;
                }
                if (1440 - 840) <= m {
                    n += 1;
                }
            } else {
                let m = minutes_in_day; // in (-1440, 0]
                if (-840..=0).contains(&m) {
                    n += 1;
                }
                if m <= (-1440 + 840) {
                    n += 1;
                }
            }
        }
        n
    }
}

/// Counts the distinct excluded dateTime literals that map to the single
/// timeline instant `instant_seconds` within the given timezone variant
/// (`has_timezone`), so the single-instant cardinality can be reduced exactly.
/// Mirrors HermiT subtracting the negated points from
/// `DateTimeValueSpaceSubset.hasCardinalityAtLeast` (the post-
/// `conjoinWithDRNegation` interval list no longer covers the excluded points).
///
/// Returns `None` when an exclusion cannot be resolved to a finite set of
/// dateTime points at this instant/variant — a negated dateTime *interval* (can
/// remove a sub-range), or an unparseable enumeration member — so the caller
/// falls back to the exclusion-free upper bound (sound-leaning). Each removed
/// value is counted by value-space equality `(millis, last_day, tz_offset)`; distinct
/// excluded literals that collapse to the same model value count once, which can
/// only UNDER-count removals ⇒ the returned cardinality is an upper bound on the
/// distinct values ⇒ never a false clash.
fn count_excluded_datetimes_at_instant<D>(
    ranges: &[(LiteralDataRange, D)],
    instant_millis: i64,
    has_timezone: bool,
) -> Option<u128> {
    let mut removed: Vec<DataValue> = Vec::new();
    let mut consider = |v: DataValue| -> bool {
        // Only a dateTime value at this exact instant with the matching timezone
        // presence removes a value from this variant's single-instant count.
        // De-duplication keys on the full value identity (millis, last_day,
        // timezone offset), mirroring Java `DateTime.equals`: two excluded
        // literals that share an instant but differ in the last-day flag or the
        // offset are distinct values and each remove a point.
        if let DataValue::DateTime { millis, has_tz, last_day, tz_offset } = v {
            if millis == instant_millis && has_tz == has_timezone {
                let value = DataValue::DateTime { millis, has_tz, last_day, tz_offset };
                if !removed.iter().any(|e| values_equal(e, &value)) {
                    removed.push(value);
                }
                return true;
            }
        }
        false
    };
    for (r, _) in ranges {
        match r {
            // The positive dateTime datatype restriction(s) define the interval;
            // they remove nothing here.
            LiteralDataRange::DatatypeRestriction(dr) if is_datetime_datatype(dr.datatype_uri()) => {
            }
            LiteralDataRange::AtomicNegationDataRange(n) => match n.get_negated_data_range() {
                // A negated enumeration removes its (finitely many) members.
                crate::model::AtomicDataRange::ConstantEnumeration(e) => {
                    for i in 0..e.number_of_constants() {
                        match parse_value(e.constant(i)) {
                            // A dateTime member: count it if it hits this instant.
                            Some(v @ DataValue::DateTime { .. }) => {
                                consider(v);
                            }
                            // A non-dateTime member removes nothing from the
                            // dateTime value space.
                            Some(_) => {}
                            // An unparseable member is undecidable ⇒ bail.
                            None => return None,
                        }
                    }
                }
                // A negated dateTime DR removes a (possibly continuous) interval,
                // not a finite point set ⇒ cannot resolve exactly here.
                crate::model::AtomicDataRange::DatatypeRestriction(dr)
                    if is_datetime_datatype(dr.datatype_uri()) =>
                {
                    return None
                }
                // A negated non-dateTime datatype removes nothing from dateTime.
                _ => {}
            },
            // Helper ranges remove nothing.
            r if is_value_non_constraining_helper(r) => {}
            // Anything else (e.g. a positive enumeration) is handled before this
            // branch is reached; be conservative.
            _ => return None,
        }
    }
    Some(removed.len() as u128)
}

fn accumulate_numeric_bound(
    facet_uri: &str,
    facet_value: &Constant,
    lower: &mut Option<Bound>,
    upper: &mut Option<Bound>,
) {
    let Some(facet) = facet_uri.strip_prefix(XSD) else {
        return;
    };
    // Keep the bound as an exact rational so the emptiness test is exact.
    let Some(bound_value) = parse_value(facet_value).and_then(|v| as_exact(&v)) else {
        return;
    };
    match facet {
        "minInclusive" | "minExclusive" => {
            let inclusive = facet == "minInclusive";
            match lower {
                Some(existing) => {
                    let ord = cmp_exact(&bound_value, &existing.value);
                    if ord.is_gt() {
                        *lower = Some(Bound { value: bound_value, inclusive });
                    } else if ord.is_eq() {
                        // Equal bounds: keep the more restrictive bound type
                        // (exclusive wins), as OWLRealDatatypeHandler.getIntervalFor does.
                        existing.inclusive = existing.inclusive && inclusive;
                    }
                }
                None => *lower = Some(Bound { value: bound_value, inclusive }),
            }
        }
        "maxInclusive" | "maxExclusive" => {
            let inclusive = facet == "maxInclusive";
            match upper {
                Some(existing) => {
                    let ord = cmp_exact(&bound_value, &existing.value);
                    if ord.is_lt() {
                        *upper = Some(Bound { value: bound_value, inclusive });
                    } else if ord.is_eq() {
                        existing.inclusive = existing.inclusive && inclusive;
                    }
                }
                None => *upper = Some(Bound { value: bound_value, inclusive }),
            }
        }
        _ => {}
    }
}

/// The cardinality of a node's (conjoined) value space: either infinite/
/// unbounded, or an exact finite count.
#[derive(Clone, Copy, PartialEq)]
enum Cardinality {
    Infinite,
    Finite(u128),
}

/// A data node's value space, mirroring a HermiT `DVariable` after
/// `prepareForSatisfiabilityChecking`: either an infinite value space (a node
/// that can always avoid finitely many distinct neighbours, e.g. a dense
/// real/string/anyURI or an unbounded integer), or a finite one with its
/// *exact* cardinality. The concrete values are materialized only when the
/// cardinality is small enough to enumerate (the survivors of elimination, by
/// construction, always are — their cardinality is below the component size).
#[derive(Clone)]
enum NodeValueSpace {
    Infinite,
    Finite { count: u128, values: Option<Vec<DataValue>> },
}

/// The largest finite value space we materialize as an explicit value list.
/// Survivors of `eliminateTriviallySatisfiableVariables` always have cardinality
/// below their degree+1 (≤ the component size), so any realistic tableau
/// component stays well under this; it is generous enough that the exact
/// pigeonhole/cardinality decision is always available for them.
const MAX_ENUMERATED_VALUES: usize = 4096;

/// Whether two node value spaces are equal in the sense HermiT's
/// `hasSameRestrictions` requires for the symmetric-clique shortcut: same exact
/// cardinality and, when materialized, the same value set (as a value-space
/// multiset of points). Two infinite value spaces are treated as equal (a
/// clique over them is always satisfiable regardless, so the shortcut returns
/// "no clash" either way).
fn node_value_spaces_equal(a: Option<&NodeValueSpace>, b: Option<&NodeValueSpace>) -> bool {
    match (a, b) {
        (Some(NodeValueSpace::Infinite), Some(NodeValueSpace::Infinite)) | (None, None) => true,
        (
            Some(NodeValueSpace::Finite { count: ca, values: va }),
            Some(NodeValueSpace::Finite { count: cb, values: vb }),
        ) => {
            if ca != cb {
                return false;
            }
            match (va, vb) {
                (Some(va), Some(vb)) => {
                    va.len() == vb.len()
                        && va.iter().all(|x| vb.iter().any(|y| values_equal(x, y)))
                        && vb.iter().all(|y| va.iter().any(|x| values_equal(x, y)))
                }
                // Same (huge) cardinality but unmaterialized: treat as equal.
                _ => true,
            }
        }
        _ => false,
    }
}

/// Computes a node's value space (exact cardinality + materialized values when
/// small) from its constant and asserted ranges. This is the analogue of
/// HermiT's `DVariable.prepareForSatisfiabilityChecking` followed by
/// `hasCardinalityAtLeast`/`enumerateDataValues`: the cardinality is exact, so
/// the pigeonhole and assignment decisions are complete, never capped.
fn node_value_space<D>(
    constant: Option<&DataValue>,
    ranges: &[(LiteralDataRange, D)],
) -> NodeValueSpace {
    // A constant node has exactly its value (the per-node pass has already
    // checked it against the ranges).
    if let Some(v) = constant {
        return NodeValueSpace::Finite { count: 1, values: Some(vec![v.clone()]) };
    }
    // A negated datatype that subsumes a positive datatype's value space empties
    // the node even over an infinite base (e.g. `integer ⊓ ¬integer`); the
    // interval/enumeration arms below would otherwise report it Infinite.
    if negation_subsumes(ranges) {
        return NodeValueSpace::Finite { count: 0, values: Some(Vec::new()) };
    }
    let excluded = |candidate: &DataValue| {
        ranges.iter().any(|(r, _)| value_in_range(candidate, r) == Some(false))
    };
    let has_exclusions = || {
        ranges
            .iter()
            .any(|(r, _)| matches!(r, LiteralDataRange::AtomicNegationDataRange(_)))
            || ranges
                .iter()
                .filter(|(r, _)| matches!(r, LiteralDataRange::DatatypeRestriction(_)))
                .count()
                > 1
    };

    // An enumeration bounds the candidates directly; its cardinality is the
    // number of distinct value-space points that survive every other range.
    if let Some(enumeration) = ranges.iter().find_map(|(r, _)| match r {
        LiteralDataRange::ConstantEnumeration(e) => Some(e),
        _ => None,
    }) {
        let mut out: Vec<DataValue> = Vec::new();
        for i in 0..enumeration.number_of_constants() {
            let c = enumeration.constant(i);
            match parse_value(c) {
                Some(candidate) if excluded(&candidate) => {}
                Some(candidate) => {
                    if !out.iter().any(|v| values_equal(v, &candidate)) {
                        out.push(candidate);
                    }
                }
                // Java: recognized-but-ill-typed literal denotes nothing (MalformedLiteralException
                // at clausification) — drop it; it contributes no value to the space.
                None if is_ill_typed(c) => {}
                // A member with an unrecognized datatype may denote anything.
                None => return NodeValueSpace::Infinite,
            }
        }
        return NodeValueSpace::Finite { count: out.len() as u128, values: Some(out) };
    }

    let restrictions: Vec<&DatatypeRestriction> = ranges
        .iter()
        .filter_map(|(r, _)| match r {
            LiteralDataRange::DatatypeRestriction(r) => Some(r),
            _ => None,
        })
        .collect();
    if restrictions.is_empty() {
        return NodeValueSpace::Infinite;
    }

    // Booleans: at most two candidates.
    if restrictions.iter().all(|r| is_boolean_datatype(r.datatype_uri())) {
        let out: Vec<DataValue> = [true, false]
            .into_iter()
            .map(DataValue::Boolean)
            .filter(|c| !excluded(c))
            .collect();
        return NodeValueSpace::Finite { count: out.len() as u128, values: Some(out) };
    }

    // Integers: a bounded interval has an *exact* finite cardinality (its
    // width), computed with BigInt. When the width fits the materialization
    // cap we also enumerate the values; otherwise we still report the exact count
    // so the cardinality decision is complete. (A huge interval combined with
    // value-removing exclusions is conservatively reported as infinite — which is
    // sound, since such an interval still has astronomically many values, far
    // more than any tableau component requires.)
    if restrictions.iter().all(|r| is_integer_datatype(r.datatype_uri())) {
        let mut lower: Option<BigInt> = None;
        let mut upper: Option<BigInt> = None;
        let tighten_lower = |v: BigInt, lower: &mut Option<BigInt>| {
            *lower = Some(match lower.take() {
                Some(c) => c.max(v),
                None => v,
            });
        };
        let tighten_upper = |v: BigInt, upper: &mut Option<BigInt>| {
            *upper = Some(match upper.take() {
                Some(c) => c.min(v),
                None => v,
            });
        };
        let mut undecided_bound = false;
        for r in &restrictions {
            if let Some((implicit_min, implicit_max)) = integer_datatype_bounds(r.datatype_uri()) {
                if let Some(m) = implicit_min {
                    tighten_lower(BigInt::from(m), &mut lower);
                }
                if let Some(m) = implicit_max {
                    tighten_upper(BigInt::from(m), &mut upper);
                }
            }
            for i in 0..r.number_of_facet_restrictions() {
                let Some(facet) = r.facet_uri(i).strip_prefix(XSD) else {
                    continue;
                };
                if !matches!(
                    facet,
                    "minInclusive" | "minExclusive" | "maxInclusive" | "maxExclusive"
                ) {
                    continue;
                }
                // Java's NumberInterval constructor rounds a non-integer bound to
                // the nearest integer inside the bound (getNearestIntegerInBound)
                // for an INTEGER base range. A minInclusive 2.5 becomes effective
                // min 3, a maxInclusive 2.5 becomes effective max 2, etc. Parse the
                // bound as an exact rational and round inward.
                let Some(bound) = parse_value(r.facet_value(i)).as_ref().and_then(as_exact) else {
                    // A facet value that is not an exact numeric (e.g. a string,
                    // or an unparseable literal) cannot be handled here.
                    undecided_bound = true;
                    continue;
                };
                let (lower_dir, inclusive) = match facet {
                    "minInclusive" => (true, true),
                    "minExclusive" => (true, false),
                    "maxInclusive" => (false, true),
                    "maxExclusive" => (false, false),
                    _ => unreachable!(),
                };
                let b = nearest_integer_in_bound(&bound, lower_dir, inclusive);
                if lower_dir {
                    tighten_lower(b, &mut lower);
                } else {
                    tighten_upper(b, &mut upper);
                }
            }
        }
        if undecided_bound {
            return NodeValueSpace::Infinite;
        }
        if let (Some(lo), Some(hi)) = (lower, upper) {
            if hi < lo {
                return NodeValueSpace::Finite { count: 0, values: Some(Vec::new()) };
            }
            let width = &hi - &lo + BigInt::one();
            if width <= BigInt::from(MAX_ENUMERATED_VALUES) {
                let mut out: Vec<DataValue> = Vec::new();
                let mut current = lo;
                while current <= hi {
                    let candidate = DataValue::Integer(current.clone());
                    if !excluded(&candidate) {
                        out.push(candidate);
                    }
                    current += 1;
                }
                return NodeValueSpace::Finite { count: out.len() as u128, values: Some(out) };
            }
            // Too wide to enumerate. If nothing can remove values from it, report
            // the exact width (clamped to u128).
            if !has_exclusions() {
                let count = u128::try_from(&width).unwrap_or(u128::MAX);
                return NodeValueSpace::Finite { count, values: None };
            }
            // A huge interval that ALSO carries value-removing exclusions
            // still has an *exact* finite cardinality. HermiT computes it via
            // NumberInterval/OWLRealValueSpaceSubset; we mirror that here.
            // (a) If every range is numeric, the owl:real lattice gives the exact
            //     cardinality directly (a negated sub-interval is subtracted as a
            //     finite count of integers).
            if let Some(count) = numeric_node_cardinality(ranges) {
                return NodeValueSpace::Finite { count, values: None };
            }
            // (b) Otherwise the exclusions are negated enumerations (finite sets
            //     of points). Count the distinct excluded integers that fall
            //     inside [lo, hi] and subtract: cardinality = width − removed.
            if let Some(removed) = count_excluded_integers_in_range(ranges, &lo, &hi) {
                let width_u = u128::try_from(&width).unwrap_or(u128::MAX);
                return NodeValueSpace::Finite {
                    count: width_u.saturating_sub(removed),
                    values: None,
                };
            }
            // Undecidable exclusion (e.g. an unparseable member): fall back to the
            // sound over-approximation (still astronomically large).
            let count = u128::try_from(&width).unwrap_or(u128::MAX);
            return NodeValueSpace::Finite { count, values: None };
        }
        return NodeValueSpace::Infinite;
    }

    // Numeric value spaces that are not purely integer (xsd:decimal, owl:rational,
    // owl:real, or a mix that includes integer): the space is dense, hence
    // infinite, UNLESS the conjunction pins it to finitely many points -- e.g. a
    // singleton interval `decimal[minInclusive 1, maxInclusive 1]` (cardinality 1)
    // or an integer-line sub-range carved out of a real restriction. HermiT
    // computes the exact cardinality over OWLRealValueSpaceSubset/NumberInterval;
    // mirror that via `numeric_node_cardinality` (None for a dense/unbounded
    // space, which stays Infinite).
    if restrictions
        .iter()
        .all(|r| NumRange::base_of(r.datatype_uri()).is_some())
    {
        return match numeric_node_cardinality(ranges) {
            Some(count) => NodeValueSpace::Finite { count, values: None },
            None => NodeValueSpace::Infinite,
        };
    }

    // xsd:float: the value space is finite and discrete; a facet-bounded
    // interval has an exact representable count.
    // Java: EntireFloatSubset.hasCardinalityAtLeast uses subtractIntervalSizeFrom(-INF,+INF,n)
    // and checks leftover<=1 (+1 for NaN), so the entire space is FINITE, not infinite.
    if restrictions.iter().all(|r| is_xsd_float(r.datatype_uri())) {
        let mut lower_key = f32_order_key(f32::NEG_INFINITY);
        let mut upper_key = f32_order_key(f32::INFINITY);
        let mut has_facets = false;
        for r in &restrictions {
            for i in 0..r.number_of_facet_restrictions() {
                let Some(facet) = r.facet_uri(i).strip_prefix(XSD) else {
                    continue;
                };
                if !matches!(
                    facet,
                    "minInclusive" | "minExclusive" | "maxInclusive" | "maxExclusive"
                ) {
                    continue;
                }
                has_facets = true;
                let Some(DataValue::Float(bits)) = parse_value(r.facet_value(i)) else {
                    return NodeValueSpace::Infinite;
                };
                let bound = f32::from_bits(bits);
                // Faithful to Java's bugged FloatInterval.isNaN (mantissa mask
                // 0x003fffff, not 0x007fffff): the canonical NaN bound 0x7fc00000
                // is NOT recognised as NaN, so getIntervalFor treats it as an
                // ordinary positive value above +INF (order key 0xffc00000). A NaN
                // min* bound therefore drives lower_key above upper_key (empty
                // interval, cardinality 0), while a NaN max* bound leaves upper_key
                // at +INF (the min() keeps +INF). We must NOT skip it (that would be
                // the xsd:double behaviour, whose isNaN mask is correct).
                // Java normalises the bound's zero sign per facet first (so e.g.
                // minInclusive 0.0 admits -0.0). The order key then distinguishes
                // +0.0/-0.0 by their bits and the ±1 step yields the exclusive
                // next/previousFloat (previousFloat(+0.0)==-0.0, nextFloat(-0.0)==+0.0).
                let bound = normalize_zero_for_facet_f32(bound, facet);
                let key = f32_order_key(bound);
                match facet {
                    "minInclusive" => lower_key = lower_key.max(key),
                    "minExclusive" => lower_key = lower_key.max(key.saturating_add(1)),
                    "maxInclusive" => upper_key = upper_key.min(key),
                    "maxExclusive" => upper_key = upper_key.min(key.saturating_sub(1)),
                    _ => {}
                }
            }
        }
        // No !any_bound guard: with no facets lower/upper stay at -INF/+INF and the
        // width below gives the correct finite count (~2^32 non-NaN values), matching
        // Java's EntireFloatSubset which is also finite.
        if upper_key < lower_key {
            return NodeValueSpace::Finite { count: 0, values: Some(Vec::new()) };
        }
        let width = (upper_key - lower_key) as u64 + 1;
        if width <= MAX_ENUMERATED_VALUES as u64 {
            let out: Vec<DataValue> = (lower_key..=upper_key)
                .map(|k| DataValue::Float(f32_from_order_key(k).to_bits()))
                .filter(|c| !excluded(c))
                .collect();
            return NodeValueSpace::Finite { count: out.len() as u128, values: Some(out) };
        }
        // The entire xsd:float value space includes one NaN, so the +1 is present
        // exactly when the value-space subset is still EntireFloatSubset — i.e. when
        // no positive facet and no non-vacuous negated-interval DR has shrunk it to a
        // NoNaN subset. Negated *enumerations* (forbidden values) do NOT remove the
        // NaN; they are subtracted separately (DVariable.m_forbiddenDataValues),
        // matching Java's hasCardinalityAtLeast(number+forbidden.size()).
        let nan = if entire_float_space_keeps_nan(ranges) { 1u128 } else { 0u128 };
        if has_exclusions() {
            // FD-5: a huge-but-finite float interval that also has excluded values
            // still has an EXACT finite cardinality. Java
            // (NoNaNFloatSubset.hasCardinalityAtLeast inflates the requested number
            // by m_forbiddenDataValues.size(), and DVariable.hasCardinalityAtLeast
            // adds the forbidden-value count) => effective cardinality =
            // (interval size via FloatInterval.subtractIntervalSizeFrom) minus the
            // number of excluded values that lie inside the interval, plus the NaN
            // if the subset is still entire (only forbidden enumeration points, no
            // real facet/negated-interval shrink).
            let removed = count_excluded_floats_in_range(ranges, lower_key, upper_key);
            return NodeValueSpace::Finite {
                count: (width as u128).saturating_sub(removed) + nan,
                values: None,
            };
        }
        let _ = has_facets;
        return NodeValueSpace::Finite { count: width as u128 + nan, values: None };
    }

    // xsd:double: finite discrete value space, exact representable count.
    // Java: EntireDoubleSubset.hasCardinalityAtLeast uses subtractIntervalSizeFrom(-INF,+INF,n)
    // and checks leftover<=1 (+1 for NaN), so the entire space is FINITE, not infinite.
    // Mirrors Java DoubleInterval / DoubleValueSpaceSubset.hasCardinalityAtLeast.
    if restrictions.iter().all(|r| is_xsd_double(r.datatype_uri())) {
        let mut lower_key = f64_order_key(f64::NEG_INFINITY);
        let mut upper_key = f64_order_key(f64::INFINITY);
        let mut has_facets = false;
        for r in &restrictions {
            for i in 0..r.number_of_facet_restrictions() {
                let Some(facet) = r.facet_uri(i).strip_prefix(XSD) else {
                    continue;
                };
                if !matches!(
                    facet,
                    "minInclusive" | "minExclusive" | "maxInclusive" | "maxExclusive"
                ) {
                    continue;
                }
                has_facets = true;
                let Some(DataValue::Double(bits)) = parse_value(r.facet_value(i)) else {
                    return NodeValueSpace::Infinite;
                };
                let bound = f64::from_bits(bits);
                // Java: DoubleInterval.isSmallerEqual returns false when either operand is NaN,
                // so the bound-tightening assignment is skipped — the NaN facet is ignored and
                // the interval stays at its current ±INF defaults.
                if bound.is_nan() {
                    continue;
                }
                // Java normalises the bound's zero sign per facet first (so e.g.
                // minInclusive 0.0 admits -0.0). The order key then distinguishes
                // +0.0/-0.0 by their bits and the ±1 step yields the exclusive
                // next/previousDouble (previousDouble(+0.0)==-0.0, nextDouble(-0.0)==+0.0).
                let bound = normalize_zero_for_facet_f64(bound, facet);
                let key = f64_order_key(bound);
                match facet {
                    "minInclusive" => lower_key = lower_key.max(key),
                    "minExclusive" => lower_key = lower_key.max(key.saturating_add(1)),
                    "maxInclusive" => upper_key = upper_key.min(key),
                    "maxExclusive" => upper_key = upper_key.min(key.saturating_sub(1)),
                    _ => {}
                }
            }
        }
        // No !any_bound guard: with no facets lower/upper stay at -INF/+INF and the
        // width below gives the correct finite count (~2^64 non-NaN values), matching
        // Java's EntireDoubleSubset which is also finite.
        if upper_key < lower_key {
            return NodeValueSpace::Finite { count: 0, values: Some(Vec::new()) };
        }
        let width = (upper_key - lower_key) as u128 + 1;
        if width <= MAX_ENUMERATED_VALUES as u128 {
            let out: Vec<DataValue> = (lower_key..=upper_key)
                .map(|k| DataValue::Double(f64_from_order_key(k).to_bits()))
                .filter(|c| !excluded(c))
                .collect();
            return NodeValueSpace::Finite { count: out.len() as u128, values: Some(out) };
        }
        // The entire xsd:double value space includes one NaN; the +1 survives
        // exactly when the value-space subset is still EntireDoubleSubset (no
        // positive facet and no non-vacuous negated-interval DR has shrunk it to a
        // NoNaN subset). Negated *enumerations* (forbidden values) do NOT remove the
        // NaN; they are subtracted separately (DVariable.m_forbiddenDataValues),
        // matching Java's hasCardinalityAtLeast(number+forbidden.size()).
        let nan = if entire_double_space_keeps_nan(ranges) { 1u128 } else { 0u128 };
        if has_exclusions() {
            // FD-5: see the float arm above. Java
            // NoNaNDoubleSubset.hasCardinalityAtLeast / DoubleInterval.subtractIntervalSizeFrom:
            // exact cardinality = (interval size) - (excluded values inside the
            // interval), plus the NaN if the subset is still entire.
            let removed = count_excluded_doubles_in_range(ranges, lower_key, upper_key);
            return NodeValueSpace::Finite {
                count: width.saturating_sub(removed) + nan,
                values: None,
            };
        }
        let _ = has_facets;
        return NodeValueSpace::Finite { count: width + nan, values: None };
    }

    // Strings whose pattern facet denotes a small finite language.
    if restrictions.iter().all(|r| is_string_datatype(r.datatype_uri())) {
        for r in &restrictions {
            for i in 0..r.number_of_facet_restrictions() {
                if r.facet_uri(i).strip_prefix(XSD) != Some("pattern") {
                    continue;
                }
                // STR-3: RDFPlainLiteralPatternValueSpaceSubset.hasCardinalityAtLeast
                // uses getFiniteStrings to decide finiteness/cardinality for ANY
                // regex. `finite_pattern_lang` returns the exact cardinality (and
                // the words when they fit the cap); `None` => infinite language.
                if let Some(lang) =
                    finite_pattern_lang(r.facet_value(i).lexical_form(), MAX_ENUMERATED_VALUES)
                {
                    match lang.words {
                        Some(words) => {
                            let mut out: Vec<DataValue> = Vec::new();
                            for w in words {
                                let candidate = DataValue::Text(w);
                                if !excluded(&candidate)
                                    && !out.iter().any(|v| values_equal(v, &candidate))
                                {
                                    out.push(candidate);
                                }
                            }
                            return NodeValueSpace::Finite {
                                count: out.len() as u128,
                                values: Some(out),
                            };
                        }
                        // Finite but too large to materialize: exact cardinality only.
                        None => {
                            return NodeValueSpace::Finite { count: lang.count, values: None };
                        }
                    }
                }
                // FIX (case 4): `finite_pattern_lang` could not decide finiteness
                // (e.g. a regex its lightweight enumerator does not model). Fall
                // back to the real automaton's `getFiniteStrings`/state-counting:
                // it distinguishes a finite-but-large language (exact cardinality)
                // from a genuinely infinite one — so we never bail to Infinite for a
                // finite pattern. Only used when no value-removing exclusion is
                // present that the automaton cannot represent (handled below).
                if let Some(space) = string_automaton_value_space(ranges) {
                    return space;
                }
            }
        }
        // Length-bounded strings: if every restriction carries only length facets
        // (length_intervals_for returns Some), compute exact cardinality by
        // intersecting the ABSENT intervals and calling size_of — mirroring
        // RDFPlainLiteralLengthValueSpaceSubset.hasCardinalityAtLeast (Java:
        // RDFPlainLiteralLengthInterval.subtractSizeFrom / getNumberOfValuesOfLength).
        // rdf:PlainLiteral PRESENT mode is always infinite; scope out if present.
        let all_length_handled = restrictions.iter().all(|r| length_intervals_for(r).is_some());
        if all_length_handled {
            let mut absent: Option<LengthInterval> = None;
            let mut has_present = false;
            for r in &restrictions {
                let (p, a) = length_intervals_for(r).unwrap();
                if p.is_some() { has_present = true; }
                absent = match (absent, a) {
                    (None, a) => a,
                    (Some(old), Some(new_iv)) => old.intersect(new_iv),
                    (Some(old), None) => Some(old),
                };
            }
            if !has_present {
                match absent {
                    None => return NodeValueSpace::Finite { count: 0, values: Some(Vec::new()) },
                    Some(iv) => {
                        if let Some(count) = iv.size_of() {
                            // values: None — cardinality is exact but we do not
                            // enumerate the Unicode string set; sound for the
                            // pigeonhole test, conservative for assignment search.
                            return NodeValueSpace::Finite { count, values: None };
                        }
                    }
                }
            }
        }
        // FIX (case 4): a string conjunction the length/finite-pattern paths could
        // not bound — try the full automaton (intersection of positive restriction
        // automata, minus negated ones). It reports an exact finite cardinality, a
        // materialized word set when small, or Infinite, faithfully.
        if let Some(space) = string_automaton_value_space(ranges) {
            return space;
        }
        return NodeValueSpace::Infinite;
    }

    // xsd:dateTime / xsd:dateTimeStamp: a MULTI-instant (lower < upper) interval
    // is dense (seconds are real numbers) ⇒ infinite cardinality. But a
    // single-instant (collapsed, lower == upper) interval is actually FINITE:
    // only finitely many distinct literals map to one point on the timeline (the
    // timezone-present-vs-absent corner). HermiT counts these exactly in
    // DateTimeInterval.subtractSizeFrom / DateTimeValueSpaceSubset.
    // hasCardinalityAtLeast; we mirror that so an at-least/min cardinality over a
    // single-instant range is decided, not mis-decided as infinite.
    if restrictions.iter().all(|r| is_datetime_datatype(r.datatype_uri())) {
        let (with_tz, without_tz) = datetime_value_space(&restrictions);
        if with_tz.is_none() && without_tz.is_none() {
            return NodeValueSpace::Finite { count: 0, values: Some(Vec::new()) };
        }
        // If either surviving interval spans more than a single instant, the
        // value space is dense ⇒ infinite (subtractSizeFrom returns 0 there).
        let is_point = |i: &Option<DtInterval>| i.is_none_or(|iv| iv.lower == iv.upper);
        if is_point(&with_tz) && is_point(&without_tz) {
            // Per tz variant: the exclusion-free instant cardinality, minus the
            // number of distinct excluded literals that map to this instant within
            // that variant. Mirrors DateTimeValueSpaceSubset.hasCardinalityAtLeast
            // over the (collapsed) interval(s) after conjoinWithDRNegation has
            // removed the excluded points (DateTimeInterval.subtractSizeFrom).
            // `None` from the excluded-count helper means an exclusion we cannot
            // resolve exactly (e.g. an unparseable member, or a negated *interval*
            // that could remove a sub-range): fall back to the exclusion-free
            // upper bound, which is sound-leaning (can only miss a clash).
            let mut count: u128 = 0;
            for (iv, has_tz) in [(with_tz, true), (without_tz, false)] {
                if let Some(iv) = iv {
                    let base = datetime_instant_cardinality(iv.lower, has_tz);
                    let net = match count_excluded_datetimes_at_instant(ranges, iv.lower, has_tz) {
                        Some(removed) => base.saturating_sub(removed),
                        // Unresolved exclusion ⇒ fall back to the exclusion-free
                        // upper bound for this variant (sound-leaning).
                        None => base,
                    };
                    count = count.saturating_add(net);
                }
            }
            return NodeValueSpace::Finite { count, values: None };
        }
        return NodeValueSpace::Infinite;
    }

    // xsd:hexBinary / xsd:base64Binary: length-bounded intervals have an exact
    // cardinality (BinaryDataLengthInterval.subtractSizeFrom / getNumberOfValuesOfLength).
    // If maxLength is unbounded or either bound >=7, treat as infinite (count overflows long).
    let is_binary = |r: &&DatatypeRestriction| is_hex_binary_datatype(r.datatype_uri()) || is_base64_datatype(r.datatype_uri());
    if restrictions.iter().all(is_binary) {
        // A conjunction that mixes xsd:hexBinary and xsd:base64Binary restrictions
        // is empty: `BinaryDataLengthInterval.intersectWith` returns null across
        // differing `m_binaryDataType`s, so no value lies in both value spaces.
        let any_hex = restrictions.iter().any(|r| is_hex_binary_datatype(r.datatype_uri()));
        let any_base64 = restrictions.iter().any(|r| is_base64_datatype(r.datatype_uri()));
        if any_hex && any_base64 {
            return NodeValueSpace::Finite { count: 0, values: Some(Vec::new()) };
        }
        let mut min_len: u64 = 0;
        let mut max_len: Option<u64> = None;
        for r in &restrictions {
            for i in 0..r.number_of_facet_restrictions() {
                let Ok(b) = r.facet_value(i).lexical_form().trim().parse::<u64>() else { return NodeValueSpace::Infinite; };
                match r.facet_uri(i).strip_prefix(XSD) {
                    Some("minLength") => min_len = min_len.max(b),
                    Some("maxLength") => max_len = Some(max_len.map_or(b, |m| m.min(b))),
                    Some("length") => { min_len = min_len.max(b); max_len = Some(max_len.map_or(b, |m| m.min(b))); }
                    _ => return NodeValueSpace::Infinite,
                }
            }
        }
        let Some(max_len) = max_len else { return NodeValueSpace::Infinite; };
        if min_len > max_len { return NodeValueSpace::Finite { count: 0, values: Some(Vec::new()) }; }
        if min_len >= 7 || max_len >= 7 { return NodeValueSpace::Infinite; }
        let values_up_to = |l: i64| -> u128 {
            if l < 0 { return 0; }
            let mut total: u128 = 1; let mut term: u128 = 1;
            for _ in 1..=l { term *= 256; total += term; } total
        };
        let count = values_up_to(max_len as i64) - values_up_to(min_len as i64 - 1);
        // The value-space subset is typed by its datatype (HEX_BINARY vs
        // BASE_64_BINARY): `BinaryDataLengthInterval.contains` requires the value's
        // `m_binaryDataType` to match. HermiT's `BinaryData.parseBase64Binary` tags
        // parsed base64 literals HEX_BINARY (a quirk), so a base64Binary value space
        // contains none of its own parseable literals and an interval intersection
        // across the two types is empty (`intersectWith` returns null on a type
        // mismatch). We reproduce this by tagging the enumerated members with the
        // positive restrictions' datatype: a mixed hex/base64 conjunction then
        // empties out (every member is excluded by the other-typed restriction), and
        // a base64Binary value space never matches a (HEX_BINARY-tagged) negated
        // enumeration value, so such values are not subtracted.
        let binary_kind: &'static str =
            if restrictions.iter().all(|r| is_base64_datatype(r.datatype_uri())) {
                "base64Binary"
            } else {
                "hexBinary"
            };
        if count <= MAX_ENUMERATED_VALUES as u128 {
            // Enumerate by iterating byte-arrays of each length in [min_len, max_len].
            let mut out: Vec<DataValue> = Vec::new();
            for len in min_len..=max_len {
                // Recursive enumeration of all byte-arrays of exactly `len` bytes.
                let total = 256u64.pow(len as u32);
                for idx in 0..total {
                    let bytes: Vec<u8> = (0..len).rev().map(|pos| ((idx / 256u64.pow(pos as u32)) % 256) as u8).collect();
                    let canonical: String = bytes.iter().map(|b| format!("{:02X}", b)).collect();
                    let candidate = DataValue::Typed { kind: binary_kind, canonical, length: bytes.len() };
                    if !excluded(&candidate) { out.push(candidate); }
                    if out.len() > MAX_ENUMERATED_VALUES { return NodeValueSpace::Finite { count, values: None }; }
                }
            }
            return NodeValueSpace::Finite { count: out.len() as u128, values: Some(out) };
        }
        return NodeValueSpace::Finite { count, values: None };
    }

    // URI-1: xsd:anyURI with a length facet. Java AnyURIValueSpaceSubset.hasCardinalityAtLeast
    // intersects the URI automaton with the length/pattern facets and counts via
    // getFiniteStrings, so a length-bounded anyURI value space is FINITE. We compute
    // an exact finite cardinality over the canonical (ASCII) URI alphabet -- the
    // single-character URIs that `is_valid_any_uri` admits without %-escapes -- and
    // enumerate them when the count fits the cap. The true anyURI value space also
    // contains %-escaped and non-ASCII forms, so this is a (large) lower bound on
    // the cardinality; since any length>=1 already yields ~80 URIs per position
    // (far exceeding any tableau component), the pigeonhole decision is sound (no
    // false clash) and detects the degenerate small cases (notably maxLength 0).
    if restrictions.iter().all(|r| is_anyuri_datatype(r.datatype_uri())) {
        let mut min_len: u64 = 0;
        let mut max_len: Option<u64> = None;
        let mut patterns: Vec<String> = Vec::new();
        for r in &restrictions {
            for i in 0..r.number_of_facet_restrictions() {
                match r.facet_uri(i).strip_prefix(XSD) {
                    // URI-2 (FIX B): collect pattern facets — Java
                    // AnyURIDatatypeHandler.getAutomatonFor intersects the URI
                    // automaton with EACH pattern automaton, so a pattern can make
                    // the (otherwise length-unbounded) language finite.
                    Some("pattern") => patterns.push(r.facet_value(i).lexical_form().to_string()),
                    facet => {
                        let Ok(b) = r.facet_value(i).lexical_form().trim().parse::<u64>() else { return NodeValueSpace::Infinite; };
                        match facet {
                            Some("minLength") => min_len = min_len.max(b),
                            Some("maxLength") => max_len = Some(max_len.map_or(b, |m| m.min(b))),
                            Some("length") => { min_len = min_len.max(b); max_len = Some(max_len.map_or(b, |m| m.min(b))); }
                            _ => return NodeValueSpace::Infinite,
                        }
                    }
                }
            }
        }
        // URI-2 (FIX B): an anyURI restriction carrying pattern facet(s). Java's
        // getAutomatonFor intersects URI ⊓ pattern ⊓ length and counts via
        // getFiniteStrings, so a pattern that bounds the language to finite yields a
        // FINITE value space even with no maxLength. We route it through the same
        // finite-pattern enumerator used for xsd:string patterns, intersected with
        // the URI alphabet (is_valid_any_uri) and the length window.
        if !patterns.is_empty() {
            // Find a pattern whose language is finite; that one bounds the
            // intersection (URI ∩ pattern_i ∩ ... ⊆ pattern_i). If none is finite,
            // the conjunction language is unbounded ⇒ infinite value space.
            let mut universe: Option<Vec<String>> = None;
            for p in &patterns {
                if let Some(words) = enumerate_finite_pattern(p, MAX_ENUMERATED_VALUES) {
                    universe = Some(words);
                    break;
                } else if finite_pattern_lang(p, MAX_ENUMERATED_VALUES).is_none() {
                    // genuinely infinite or unmodeled pattern: keep looking, but if
                    // ALL patterns are like this we cannot bound the language.
                    continue;
                } else {
                    // Finite but too large to materialize: cardinality exact but the
                    // intersection with URI/length still needs the explicit words to
                    // filter; treat as infinite-for-our-purposes (conservative,
                    // never a false clash — we simply do not claim finiteness).
                    return NodeValueSpace::Infinite;
                }
            }
            let Some(universe) = universe else { return NodeValueSpace::Infinite; };
            // Compile the OTHER patterns (the ones we did not enumerate) as anchored
            // regexes so we keep only words matching every pattern facet (the
            // automaton intersection). An uncompilable pattern ⇒ scope out.
            let mut others: Vec<regex::Regex> = Vec::new();
            // We re-match every pattern (cheap, and correct even for the chosen one).
            for p in &patterns {
                match regex::Regex::new(&format!("^(?:{})$", p)) {
                    Ok(re) => others.push(re),
                    Err(_) => return NodeValueSpace::Infinite,
                }
            }
            let mut out: Vec<DataValue> = Vec::new();
            for w in universe {
                let len16 = w.encode_utf16().count() as u64;
                // length window (xsd:minLength/maxLength/length).
                if len16 < min_len { continue; }
                if let Some(max) = max_len { if len16 > max { continue; } }
                // URI alphabet: must be a valid anyURI lexical form.
                if !is_valid_any_uri(&w) { continue; }
                // Every pattern facet must match (automaton intersection).
                if !others.iter().all(|re| re.is_match(&w)) { continue; }
                let candidate = DataValue::Typed {
                    kind: "anyURI",
                    canonical: w.clone(),
                    length: len16 as usize,
                };
                if !excluded(&candidate) && !out.iter().any(|v| values_equal(v, &candidate)) {
                    out.push(candidate);
                }
            }
            return NodeValueSpace::Finite { count: out.len() as u128, values: Some(out) };
        }
        if let Some(max) = max_len {
            if min_len > max { return NodeValueSpace::Finite { count: 0, values: Some(Vec::new()) }; }
            let alphabet: Vec<char> = uri_ascii_alphabet();
            let a = alphabet.len() as u128;
            let mut count: u128 = 0;
            for l in min_len..=max {
                count = count.saturating_add(a.saturating_pow(l.min(64) as u32));
            }
            if count <= MAX_ENUMERATED_VALUES as u128 {
                let mut out: Vec<DataValue> = Vec::new();
                let mut frontier: Vec<String> = vec![String::new()];
                for l in 0..=max {
                    if l >= min_len {
                        for s in &frontier {
                            let candidate = DataValue::Typed {
                                kind: "anyURI",
                                canonical: s.clone(),
                                length: s.chars().count(),
                            };
                            if !excluded(&candidate) {
                                out.push(candidate);
                            }
                        }
                    }
                    if l == max {
                        break;
                    }
                    let mut next = Vec::with_capacity(frontier.len() * alphabet.len());
                    for s in &frontier {
                        for &ch in &alphabet {
                            let mut t = s.clone();
                            t.push(ch);
                            next.push(t);
                        }
                    }
                    frontier = next;
                }
                return NodeValueSpace::Finite { count: out.len() as u128, values: Some(out) };
            }
            return NodeValueSpace::Finite { count, values: None };
        }
    }

    NodeValueSpace::Infinite
}

/// URI-1: the single-character ASCII alphabet that `is_valid_any_uri` admits for a
/// URI (the unreserved/mark and reserved/punctuation characters of RFC 2396, kept
/// in sync with `crate::datatype_value::is_valid_any_uri`). Used to count and
/// enumerate canonical length-bounded anyURI value spaces.
fn uri_ascii_alphabet() -> Vec<char> {
    let mut out: Vec<char> = Vec::new();
    out.extend('A'..='Z');
    out.extend('a'..='z');
    out.extend('0'..='9');
    out.extend([
        '-', '_', '.', '!', '~', '*', '\'', '(', ')',
        ',', ';', ':', '$', '&', '+', '=', '?', '/', '[', ']', '@',
        '#',
    ]);
    out
}

/// A monotone bijection from the non-NaN `f32`s onto a `u32` order key:
/// consecutive keys are consecutive representable floats, with `-0.0` and
/// `+0.0` adjacent but distinct, and all NaN bit patterns mapped strictly
/// outside `[key(-INF), key(+INF)]`.
fn f32_order_key(f: f32) -> u32 {
    let bits = f.to_bits();
    if bits & 0x8000_0000 != 0 {
        !bits
    } else {
        bits | 0x8000_0000
    }
}
/// Normalises the zero sign of a facet bound exactly as
/// `FloatDatatypeHandler.getIntervalFor`/`DoubleDatatypeHandler.getIntervalFor`
/// do before forming an interval: `minInclusive`/`maxExclusive` map `+0.0` to
/// `-0.0`, while `minExclusive`/`maxInclusive` map `-0.0` to `+0.0`. This makes
/// e.g. `minInclusive 0.0` admit both `-0.0` and `+0.0`, and `minExclusive -0.0`
/// exclude both. Non-zero bounds are returned unchanged.
fn normalize_zero_for_facet_f32(bound: f32, facet: &str) -> f32 {
    if bound != 0.0 {
        return bound;
    }
    match facet {
        "minInclusive" | "maxExclusive" => -0.0_f32,
        "minExclusive" | "maxInclusive" => 0.0_f32,
        _ => bound,
    }
}
fn normalize_zero_for_facet_f64(bound: f64, facet: &str) -> f64 {
    if bound != 0.0 {
        return bound;
    }
    match facet {
        "minInclusive" | "maxExclusive" => -0.0_f64,
        "minExclusive" | "maxInclusive" => 0.0_f64,
        _ => bound,
    }
}
fn f32_from_order_key(key: u32) -> f32 {
    if key & 0x8000_0000 != 0 {
        f32::from_bits(key & 0x7FFF_FFFF)
    } else {
        f32::from_bits(!key)
    }
}

/// A monotone bijection from the non-NaN `f64`s onto a `u64` order key:
/// consecutive keys are consecutive representable doubles, with `-0.0` and
/// `+0.0` adjacent but distinct, and all NaN bit patterns mapped strictly
/// outside `[key(-INF), key(+INF)]`.
/// Mirrors Java DoubleInterval / DoubleValueSpaceSubset ordering.
fn f64_order_key(f: f64) -> u64 {
    let bits = f.to_bits();
    if bits & 0x8000_0000_0000_0000 != 0 {
        !bits
    } else {
        bits | 0x8000_0000_0000_0000
    }
}
fn f64_from_order_key(key: u64) -> f64 {
    if key & 0x8000_0000_0000_0000 != 0 {
        f64::from_bits(key & 0x7FFF_FFFF_FFFF_FFFF)
    } else {
        f64::from_bits(!key)
    }
}

/// STR-3: a finite regular language, the way dk.brics `Automaton.getFiniteStrings(n)`
/// reports one — an EXACT cardinality plus, when that cardinality is at most `cap`,
/// the materialized set of words. A pattern denotes a `Lang` iff its language is
/// finite (every unbounded quantifier `*`/`+`/`{m,}` is over the empty/epsilon
/// language); an infinite language is reported as `None`. Mirrors
/// RDFPlainLiteralPatternValueSpaceSubset.hasCardinalityAtLeast, which decides
/// finiteness/cardinality for ANY regular expression.
#[derive(Clone)]
struct Lang {
    count: u128,
    /// `Some` iff `count <= cap`: the explicit words. `None` means finite but too
    /// large to materialize (cardinality is still exact).
    words: Option<Vec<String>>,
}

impl Lang {
    /// The empty language (no words). Cardinality 0.
    fn empty() -> Lang {
        Lang { count: 0, words: Some(Vec::new()) }
    }
    /// The language `{ "" }` (just epsilon).
    fn epsilon() -> Lang {
        Lang { count: 1, words: Some(vec![String::new()]) }
    }
    /// A finite language given by an explicit, already-deduplicated word list.
    fn from_words(words: Vec<String>, cap: usize) -> Lang {
        let count = words.len() as u128;
        if count > cap as u128 {
            Lang { count, words: None }
        } else {
            Lang { count, words: Some(words) }
        }
    }
    /// A language over single characters. `members` is the distinct char set; when
    /// it fits under `cap` the words are materialized, otherwise only the (exact)
    /// count is kept.
    fn from_char_set(members: Vec<char>, cap: usize) -> Lang {
        Lang::from_words(members.into_iter().map(|c| c.to_string()).collect(), cap)
    }
    /// A single-character language of exactly `count` distinct chars, where the
    /// char set is too large to materialize (e.g. `.` over the XML alphabet). The
    /// cardinality is exact; words stay `None`.
    fn char_set_count(count: u128) -> Lang {
        Lang { count, words: None }
    }
    /// Concatenation (language product). The cardinality multiplies; words are the
    /// cross-product, materialized only while under `cap`.
    fn concat(self, other: Lang, cap: usize) -> Lang {
        let count = self.count.saturating_mul(other.count);
        if count == 0 {
            return Lang::empty();
        }
        match (self.words, other.words) {
            (Some(a), Some(b)) if count <= cap as u128 => {
                let mut out = Vec::with_capacity(a.len() * b.len());
                for x in &a {
                    for y in &b {
                        out.push(format!("{x}{y}"));
                    }
                }
                Lang { count, words: Some(out) }
            }
            _ => Lang { count, words: None },
        }
    }
    /// Union. Cardinality is the size of the de-duplicated union; words materialized
    /// while under `cap`.
    fn union(self, other: Lang, cap: usize) -> Lang {
        let total = self.count;
        match (self.words, other.words) {
            (Some(mut a), Some(b)) => {
                for w in b {
                    if !a.contains(&w) {
                        a.push(w);
                    }
                }
                Lang::from_words(a, cap)
            }
            // At least one side is unmaterialized: we cannot dedup exactly, so use
            // the sum as the cardinality. (Both operands of a `|` come from disjoint
            // syntactic alternatives whose languages are almost always disjoint;
            // even if they overlap, an over-count only makes the downstream
            // pigeonhole test more conservative — never a false clash.)
            (_, _) => Lang { count: total.saturating_add(other.count), words: None },
        }
    }
}

/// STR-3: enumerates the finite language of an XSD pattern up to `cap` words,
/// returning the explicit set when finite-and-small. `None` means the language is
/// infinite (an unbounded quantifier over a non-trivial sub-language) or syntax we
/// do not model. Matches dk.brics `RegExp.toAutomaton().getFiniteStrings(n)` as
/// used by RDFPlainLiteralPatternValueSpaceSubset: any regular expression whose
/// language is finite is enumerated; only genuinely infinite ones are rejected.
fn enumerate_finite_pattern(pattern: &str, cap: usize) -> Option<Vec<String>> {
    finite_pattern_lang(pattern, cap).and_then(|l| l.words)
}

/// STR-3: like `enumerate_finite_pattern` but returns the full `Lang` (exact
/// cardinality even when too large to materialize). `None` ⇒ infinite/unmodeled.
fn finite_pattern_lang(pattern: &str, cap: usize) -> Option<Lang> {
    let chars: Vec<char> = pattern.chars().collect();
    let (lang, position) = lang_alternation(&chars, 0, cap)?;
    if position != chars.len() {
        return None;
    }
    Some(lang)
}

fn lang_alternation(chars: &[char], mut position: usize, cap: usize) -> Option<(Lang, usize)> {
    let (first, next) = lang_concat(chars, position, cap)?;
    let mut acc = first;
    position = next;
    while chars.get(position) == Some(&'|') {
        let (branch, next) = lang_concat(chars, position + 1, cap)?;
        acc = acc.union(branch, cap);
        position = next;
    }
    Some((acc, position))
}

fn lang_concat(chars: &[char], mut position: usize, cap: usize) -> Option<(Lang, usize)> {
    let mut acc = Lang::epsilon();
    while let Some(&c) = chars.get(position) {
        if c == '|' || c == ')' {
            break;
        }
        let (atom, next) = lang_atom(chars, position, cap)?;
        let (piece, next) = lang_quantifier(atom, chars, next, cap)?;
        acc = acc.concat(piece, cap);
        position = next;
    }
    Some((acc, position))
}

/// Parses a single atom (group, char class, escape, `.`, or literal) into its
/// `Lang`. STR-3 adds `.`, `\d \D \w \W \s \S`, and negated classes `[^...]`.
fn lang_atom(chars: &[char], position: usize, cap: usize) -> Option<(Lang, usize)> {
    let c = *chars.get(position)?;
    match c {
        '(' => {
            // Skip a non-capturing group prefix `(?:`.
            let body_start = if chars.get(position + 1) == Some(&'?')
                && chars.get(position + 2) == Some(&':')
            {
                position + 3
            } else {
                position + 1
            };
            let (inner, next) = lang_alternation(chars, body_start, cap)?;
            if chars.get(next) != Some(&')') {
                return None;
            }
            Some((inner, next + 1))
        }
        '[' => parse_char_class(chars, position, cap),
        // `.` matches the whole XML character set: huge but finite. Keep only its
        // exact count (it never fits under `cap`).
        '.' => Some((Lang::char_set_count(xml_char_count()), position + 1)),
        '\\' => {
            let escaped = *chars.get(position + 1)?;
            if let Some(members) = class_escape_members(escaped, cap) {
                Some((Lang::from_char_set(members, cap), position + 2))
            } else if escaped.is_ascii_alphanumeric() {
                // An alphanumeric escape that is not a recognized class escape is
                // not something we model.
                None
            } else {
                // Punctuation escape: a literal character.
                Some((Lang::from_words(vec![escaped.to_string()], cap), position + 2))
            }
        }
        '*' | '+' | '{' | '}' | ']' | '^' | '$' => None,
        literal => Some((Lang::from_words(vec![literal.to_string()], cap), position + 1)),
    }
}

/// STR-3: the character members of a single-letter class escape, or `None` if the
/// letter is not a class escape. `\d`=[0-9], `\w`=[A-Za-z0-9_], `\s`=whitespace,
/// and the uppercase variants are the complement within the XML character set.
fn class_escape_members(escaped: char, cap: usize) -> Option<Vec<char>> {
    let digits: Vec<char> = ('0'..='9').collect();
    let word: Vec<char> = ('A'..='Z').chain('a'..='z').chain('0'..='9').chain(['_']).collect();
    let space: Vec<char> = vec![' ', '\t', '\n', '\r'];
    match escaped {
        'd' => Some(digits),
        'w' => Some(word),
        's' => Some(space),
        'D' => Some(complement_chars(&digits, cap)),
        'W' => Some(complement_chars(&word, cap)),
        'S' => Some(complement_chars(&space, cap)),
        _ => None,
    }
}

/// STR-3: the size of the XML character set that dk.brics `.` matches, per
/// RDFPlainLiteralPatternValueSpaceSubset.anyCharAutomaton
/// (`[	\n - -퟿-�]`). Huge but finite, so a
/// bounded-length pattern over `.` is finite with this exact cardinality.
fn xml_char_count() -> u128 {
    XML_CHAR_RANGES.iter().map(|(a, b)| (b - a + 1) as u128).sum()
}

const XML_CHAR_RANGES: &[(u32, u32)] = &[
    (0x09, 0x09),
    (0x0A, 0x0A),
    (0x20, 0x7F),
    (0xA0, 0xD7FF),
    (0xE000, 0xFFFD),
];

/// The complement of `included` within the XML character set (used for `\D \W \S`
/// and negated classes). The count is exact; the char list is materialized in full
/// (the caller's `Lang::from_char_set` keeps only the count when it exceeds `cap`).
fn complement_chars(included: &[char], _cap: usize) -> Vec<char> {
    let excl: std::collections::BTreeSet<u32> = included.iter().map(|&c| c as u32).collect();
    let mut out = Vec::new();
    for (a, b) in XML_CHAR_RANGES {
        for code in *a..=*b {
            if !excl.contains(&code) {
                if let Some(ch) = char::from_u32(code) {
                    out.push(ch);
                }
            }
        }
    }
    out
}

/// Parses a `[...]` character class into its `Lang`. Handles `[abc]`, `[a-c]`,
/// punctuation/class escapes inside the class, and the negated class `[^...]`
/// (STR-3: complement within the XML character set). `position` indexes `[`; the
/// returned position is just past `]`.
fn parse_char_class(chars: &[char], position: usize, cap: usize) -> Option<(Lang, usize)> {
    let mut i = position + 1;
    let negated = chars.get(i) == Some(&'^');
    if negated {
        i += 1;
    }
    let mut members: Vec<char> = Vec::new();
    let mut seen: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    let push = |ch: char, members: &mut Vec<char>, seen: &mut std::collections::BTreeSet<u32>| {
        if seen.insert(ch as u32) {
            members.push(ch);
        }
    };
    while let Some(&c) = chars.get(i) {
        if c == ']' {
            if members.is_empty() && !negated {
                return None;
            }
            let lang = if negated {
                Lang::from_char_set(complement_chars(&members, cap), cap)
            } else {
                Lang::from_char_set(members, cap)
            };
            return Some((lang, i + 1));
        }
        // A class member: a class escape, a punctuation escape, a range, or literal.
        if c == '\\' {
            let escaped = *chars.get(i + 1)?;
            if let Some(class_members) = class_escape_members(escaped, cap) {
                for ch in class_members {
                    push(ch, &mut members, &mut seen);
                }
                i += 2;
                continue;
            }
            if escaped.is_ascii_alphanumeric() {
                return None; // unrecognized alphanumeric escape
            }
            // Punctuation escape: a single literal char, possibly a range start.
            let next = i + 2;
            if chars.get(next) == Some(&'-') && chars.get(next + 1).is_some_and(|&c2| c2 != ']') {
                let end = *chars.get(next + 1)?;
                if (escaped as u32) > (end as u32) {
                    return None;
                }
                for code in (escaped as u32)..=(end as u32) {
                    if let Some(rc) = char::from_u32(code) {
                        push(rc, &mut members, &mut seen);
                    }
                }
                i = next + 2;
            } else {
                push(escaped, &mut members, &mut seen);
                i = next;
            }
            continue;
        }
        let ch = c;
        let next = i + 1;
        if chars.get(next) == Some(&'-') && chars.get(next + 1).is_some_and(|&c2| c2 != ']') {
            let end = *chars.get(next + 1)?;
            if (ch as u32) > (end as u32) {
                return None;
            }
            for code in (ch as u32)..=(end as u32) {
                if let Some(rc) = char::from_u32(code) {
                    push(rc, &mut members, &mut seen);
                }
            }
            i = next + 2;
        } else {
            push(ch, &mut members, &mut seen);
            i = next;
        }
    }
    None // unterminated class
}

/// Applies a trailing quantifier to the preceding atom's `Lang`. `?` is `{0,1}`;
/// `{m}`/`{m,n}` are exact/bounded; `*`, `+`, `{m,}` are unbounded — finite ONLY
/// when the repeated language is empty or just epsilon (then the result is epsilon),
/// otherwise the language is infinite (`None`). With no quantifier the atom stands
/// as-is. STR-3 / RDFPlainLiteralPatternValueSpaceSubset: matches getFiniteStrings,
/// which is finite iff every unbounded star/plus is over a trivial sub-language.
fn lang_quantifier(
    atom: Lang,
    chars: &[char],
    next: usize,
    cap: usize,
) -> Option<(Lang, usize)> {
    // An unbounded repetition is finite only over the empty / epsilon language.
    let unbounded = |atom: &Lang| -> bool {
        atom.count == 0
            || (atom.count == 1
                && atom.words.as_ref().is_some_and(|w| w.len() == 1 && w[0].is_empty()))
    };
    let (min, max, after) = match chars.get(next) {
        Some('?') => (0usize, Some(1usize), next + 1),
        Some('*') => {
            if unbounded(&atom) {
                return Some((Lang::epsilon(), next + 1));
            }
            return None;
        }
        Some('+') => {
            if unbounded(&atom) {
                // (empty)+ = empty; (epsilon)+ = epsilon.
                return Some((atom, next + 1));
            }
            return None;
        }
        Some('{') => {
            let mut j = next + 1;
            let mut min_digits = String::new();
            while let Some(&d) = chars.get(j) {
                if d.is_ascii_digit() {
                    min_digits.push(d);
                    j += 1;
                } else {
                    break;
                }
            }
            if min_digits.is_empty() {
                return None;
            }
            let min: usize = min_digits.parse().ok()?;
            match chars.get(j) {
                Some('}') => (min, Some(min), j + 1),
                Some(',') => {
                    j += 1;
                    let mut max_digits = String::new();
                    while let Some(&d) = chars.get(j) {
                        if d.is_ascii_digit() {
                            max_digits.push(d);
                            j += 1;
                        } else {
                            break;
                        }
                    }
                    if chars.get(j) != Some(&'}') {
                        return None;
                    }
                    if max_digits.is_empty() {
                        // {m,} ⇒ unbounded: finite only over a trivial language.
                        if unbounded(&atom) {
                            let result = if atom.count == 0 && min >= 1 {
                                Lang::empty()
                            } else {
                                Lang::epsilon()
                            };
                            return Some((result, j + 1));
                        }
                        return None;
                    }
                    (min, Some(max_digits.parse().ok()?), j + 1)
                }
                _ => return None,
            }
        }
        // No quantifier.
        _ => return Some((atom, next)),
    };
    let max = max?;
    if max < min {
        return None;
    }
    // Union over k in [min, max] of the k-fold concatenation of `atom`.
    let mut result = Lang::empty();
    let mut kfold = Lang::epsilon();
    for k in 0..=max {
        if k >= min {
            result = result.union(kfold.clone(), cap);
        }
        if k == max {
            break;
        }
        kfold = kfold.concat(atom.clone(), cap);
    }
    Some((result, after))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn finite_pattern(pattern: &str) -> Option<std::collections::BTreeSet<String>> {
        enumerate_finite_pattern(pattern, 1024)
            .map(|words| words.into_iter().collect())
    }
    fn set(words: &[&str]) -> std::collections::BTreeSet<String> {
        words.iter().map(|w| w.to_string()).collect()
    }

    #[test]
    fn finite_pattern_char_classes_and_repetition() {
        // Character classes enumerate their members (incl. ranges).
        assert_eq!(finite_pattern("[ab]"), Some(set(&["a", "b"])));
        assert_eq!(finite_pattern("[a-c]"), Some(set(&["a", "b", "c"])));
        // Bounded repetition is the union of the k-fold concatenations.
        assert_eq!(finite_pattern("[ab]{2}"), Some(set(&["aa", "ab", "ba", "bb"])));
        assert_eq!(finite_pattern("a{1,2}"), Some(set(&["a", "aa"])));
        assert_eq!(finite_pattern("xy?"), Some(set(&["x", "xy"])));
        assert_eq!(finite_pattern("(ab|c)"), Some(set(&["ab", "c"])));
        // STR-3: genuinely-unbounded repetition over a non-trivial language is
        // infinite (None), never a wrong set.
        assert_eq!(finite_pattern("[ab]*"), None);
        assert_eq!(finite_pattern("[ab]+"), None);
        assert_eq!(finite_pattern("a{2,}"), None);
        // STR-3: class escapes are now finite. `\d` = [0-9] is enumerated.
        assert_eq!(finite_pattern("\\d"), Some(set(&["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"])));
        // `\d{2}` = all two-digit strings (100 of them).
        assert_eq!(finite_pattern("\\d{2}").map(|s| s.len()), Some(100));
        // `\w` = [A-Za-z0-9_] has 63 members.
        assert_eq!(finite_pattern("\\w").map(|s| s.len()), Some(63));
        // STR-3: a star over the empty/epsilon language IS finite (epsilon).
        assert_eq!(finite_pattern("()*"), Some(set(&[""])));
        // STR-3: `[^a]` and `.` are finite (huge), so they have an exact
        // cardinality even though they exceed the materialization cap: their
        // `finite_pattern_lang` is Some but its words are None.
        assert!(finite_pattern_lang("[^a]", 1024).is_some());
        assert!(finite_pattern_lang("[^a]", 1024).unwrap().words.is_none());
        assert!(finite_pattern_lang(".", 1024).is_some());
        assert!(finite_pattern_lang(".{3}", 1024).is_some());
        // The XML alphabet `.` has the documented finite cardinality.
        assert_eq!(finite_pattern_lang(".", 1024).unwrap().count, xml_char_count());
    }

    #[test]
    fn str3_digit_pattern_pigeonhole_clash() {
        // A datatype `xsd:string ⊓ pattern "\d"` has a value space of exactly the
        // 10 single-digit strings. 11 pairwise-distinct nodes over it cannot all
        // differ (pigeonhole) ⇒ a clash; 10 fit exactly.
        let digit_string = || {
            LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
                format!("{XSD}string"),
                vec![format!("{XSD}pattern")],
                vec![Constant::create("\\d", format!("{XSD}string"))],
            ))
        };
        let space = || node_value_space(None, &[(digit_string(), ())]);
        assert!(matches!(space(), NodeValueSpace::Finite { count: 10, .. }));
        let eleven: Vec<NodeValueSpace> = (0..11).map(|_| space()).collect();
        assert!(component_is_unsatisfiable(
            &eleven.iter().collect::<Vec<_>>(),
            &clique(11),
            &no_specifics(11),
            &[],
        ));
        let ten: Vec<NodeValueSpace> = (0..10).map(|_| space()).collect();
        assert!(!component_is_unsatisfiable(
            &ten.iter().collect::<Vec<_>>(),
            &clique(10),
            &no_specifics(10),
            &[],
        ));
    }

    /// A string DatatypeRestriction with the given facets; each facet's value is a
    /// raw lexical form (datatype xsd:string), so it works for pattern/length/etc.
    fn string_dr(uri: &str, facets: &[(&str, &str)]) -> LiteralDataRange {
        let (fs, vs): (Vec<String>, Vec<Constant>) = facets
            .iter()
            .map(|(f, v)| {
                let fu = if *f == "langRange" {
                    format!("{RDF}langRange")
                } else {
                    format!("{XSD}{f}")
                };
                (fu, Constant::create(*v, format!("{XSD}string")))
            })
            .unzip();
        LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
            uri.to_string(),
            fs,
            vs,
        ))
    }
    fn neg_string_dr(uri: &str, facets: &[(&str, &str)]) -> LiteralDataRange {
        let LiteralDataRange::DatatypeRestriction(dr) = string_dr(uri, facets) else {
            unreachable!()
        };
        dr.get_negation()
    }
    fn str_conj(ranges: Vec<LiteralDataRange>) -> bool {
        let with_dep: Vec<(LiteralDataRange, ())> = ranges.into_iter().map(|r| (r, ())).collect();
        conjunction_is_empty(&with_dep)
    }

    // ---- AUTOMATON PORT (cases 1-4) -------------------------------------------

    #[test]
    fn case1_infinite_pattern_intersection_emptiness() {
        let string = format!("{XSD}string");
        // Two INFINITE pattern languages whose intersection is empty:
        // `a.*` (starts with 'a') ⊓ `b.*` (starts with 'b') = ∅ ⇒ clash.
        assert!(str_conj(vec![
            string_dr(&string, &[("pattern", "a.*")]),
            string_dr(&string, &[("pattern", "b.*")]),
        ]));
        // Two infinite patterns with a non-empty (infinite) intersection: NOT empty.
        // `a.*` ⊓ `.*b` = strings starting 'a' and ending 'b' (infinite) ⇒ no clash.
        assert!(!str_conj(vec![
            string_dr(&string, &[("pattern", "a.*")]),
            string_dr(&string, &[("pattern", ".*b")]),
        ]));
        // An infinite pattern intersected with a disjoint length window: `a+`
        // (length ≥ 1, all 'a') ⊓ length 0 (the empty string only) = ∅ ⇒ clash.
        assert!(str_conj(vec![
            string_dr(&string, &[("pattern", "a+")]),
            string_dr(&string, &[("length", "0")]),
        ]));
        // `a+` ⊓ length 3 = {"aaa"} (non-empty) ⇒ no clash.
        assert!(!str_conj(vec![
            string_dr(&string, &[("pattern", "a+")]),
            string_dr(&string, &[("length", "3")]),
        ]));
    }

    #[test]
    fn case2_string_subtype_automata_decided() {
        let token = format!("{XSD}token");
        let ncname = format!("{XSD}NCName");
        let string = format!("{XSD}string");
        // `token ⊓ ¬token` = ∅ ⇒ clash (decided exactly via the subtype automaton).
        assert!(str_conj(vec![
            string_dr(&token, &[]),
            neg_string_dr(&token, &[]),
        ]));
        // `NCName ⊓ pattern "a:b"`: an NCName can't contain ':', and the pattern
        // forces a colon ⇒ ∅ ⇒ clash.
        assert!(str_conj(vec![
            string_dr(&ncname, &[]),
            string_dr(&string, &[("pattern", "a:b")]),
        ]));
        // `NCName ⊓ pattern "abc"` = {"abc"} (a valid NCName) ⇒ NOT empty.
        assert!(!str_conj(vec![
            string_dr(&ncname, &[]),
            string_dr(&string, &[("pattern", "abc")]),
        ]));
        // `token ⊓ pattern " a"` (leading space): not a token ⇒ ∅ ⇒ clash.
        assert!(str_conj(vec![
            string_dr(&token, &[]),
            string_dr(&string, &[("pattern", " a")]),
        ]));
    }

    #[test]
    fn case3_multi_negation_cover_emptiness() {
        let string = format!("{XSD}string");
        // A survivor covered only by a UNION of several negations:
        // pattern "[abc]" ⊓ ¬pattern "a" ⊓ ¬pattern "b" ⊓ ¬pattern "c" = ∅ ⇒ clash.
        assert!(str_conj(vec![
            string_dr(&string, &[("pattern", "[abc]")]),
            neg_string_dr(&string, &[("pattern", "a")]),
            neg_string_dr(&string, &[("pattern", "b")]),
            neg_string_dr(&string, &[("pattern", "c")]),
        ]));
        // Removing only two of the three leaves "c": NOT empty.
        assert!(!str_conj(vec![
            string_dr(&string, &[("pattern", "[abc]")]),
            neg_string_dr(&string, &[("pattern", "a")]),
            neg_string_dr(&string, &[("pattern", "b")]),
        ]));
    }

    #[test]
    fn case4_large_finite_pattern_cardinality_not_infinite() {
        let string = format!("{XSD}string");
        // `[0-9]{6}` has 1_000_000 words — far above the materialization cap — yet
        // is FINITE. The value space must carry the EXACT cardinality, never bail to
        // Infinite.
        let big = || string_dr(&string, &[("pattern", "[0-9]{6}")]);
        match node_value_space(None, &[(big(), ())]) {
            NodeValueSpace::Finite { count, values } => {
                assert_eq!(count, 1_000_000);
                assert!(values.is_none()); // too large to materialize
            }
            NodeValueSpace::Infinite => panic!("large finite pattern must not be Infinite"),
        }
        // A finite pattern intersected to a small set is materialized exactly:
        // `[01]{3}` ⊓ pattern "..0" (ends in 0) = {"000","010","100","110"} (4).
        let small = node_value_space(
            None,
            &[
                (string_dr(&string, &[("pattern", "[01]{3}")]), ()),
                (string_dr(&string, &[("pattern", "..0")]), ()),
            ],
        );
        assert!(matches!(small, NodeValueSpace::Finite { count: 4, .. }));
    }

    #[test]
    fn case_soundness_no_false_clash_on_satisfiable() {
        let string = format!("{XSD}string");
        // A genuinely satisfiable conjunction must NOT be reported empty.
        assert!(!str_conj(vec![
            string_dr(&string, &[("pattern", "[a-z]+")]),
            neg_string_dr(&string, &[("pattern", "x.*")]),
        ]));
        // A bare string (no facets) is never empty.
        assert!(!str_conj(vec![string_dr(&string, &[])]));
    }

    #[test]
    fn uri1_bounded_length_anyuri_pigeonhole_clash() {
        // xsd:anyURI with maxLength 1 has a small finite value space (the empty
        // URI plus each single-character URI over the canonical alphabet). A
        // pigeonhole over MORE distinct nodes than the value-space size must clash;
        // exactly the size fits. Use maxLength 0 (only the empty URI, count 1) for a
        // sharp, exact pigeonhole.
        let empty_uri = || {
            LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
                format!("{XSD}anyURI"),
                vec![format!("{XSD}maxLength")],
                vec![Constant::create("0", format!("{XSD}nonNegativeInteger"))],
            ))
        };
        let space = || node_value_space(None, &[(empty_uri(), ())]);
        assert!(matches!(space(), NodeValueSpace::Finite { count: 1, .. }));
        // 2 distinct nodes over a 1-value space => clash; 1 fits.
        let two: Vec<NodeValueSpace> = (0..2).map(|_| space()).collect();
        assert!(component_is_unsatisfiable(
            &two.iter().collect::<Vec<_>>(),
            &clique(2),
            &no_specifics(2),
            &[],
        ));
        // maxLength 1: finite, and strictly larger than 1 (empty + alphabet).
        let len1 = LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
            format!("{XSD}anyURI"),
            vec![format!("{XSD}maxLength")],
            vec![Constant::create("1", format!("{XSD}nonNegativeInteger"))],
        ));
        match node_value_space(None, &[(len1, ())]) {
            NodeValueSpace::Finite { count, .. } => assert!(count > 1),
            NodeValueSpace::Infinite => panic!("length-bounded anyURI must be finite (URI-1)"),
        }
    }

    #[test]
    fn uri2_pattern_bounds_anyuri_to_finite() {
        // FIX B: an anyURI restriction whose xsd:pattern makes the language finite
        // must yield a FINITE value space even with NO length facet (Java
        // AnyURIDatatypeHandler.getAutomatonFor intersects URI ∩ pattern and counts
        // via getFiniteStrings). `urn:(a|b)` denotes exactly {urn:a, urn:b}.
        let pat = |p: &str| {
            LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
                format!("{XSD}anyURI"),
                vec![format!("{XSD}pattern")],
                vec![Constant::create(p, format!("{XSD}string"))],
            ))
        };
        match node_value_space(None, &[(pat("urn:(a|b)"), ())]) {
            NodeValueSpace::Finite { count, values: Some(vals) } => {
                assert_eq!(count, 2, "urn:(a|b) is two URIs");
                assert_eq!(vals.len(), 2);
            }
            _ => panic!("pattern-bounded anyURI must be finite"),
        }
        // A pattern denoting a single URI ⇒ count 1 ⇒ a 2-node pigeonhole clashes.
        let one = || node_value_space(None, &[(pat("urn:only"), ())]);
        assert!(matches!(one(), NodeValueSpace::Finite { count: 1, .. }));
        let two: Vec<NodeValueSpace> = (0..2).map(|_| one()).collect();
        assert!(component_is_unsatisfiable(
            &two.iter().collect::<Vec<_>>(),
            &clique(2),
            &no_specifics(2),
            &[],
        ));
        // An ill-typed word the pattern matches but is NOT a valid URI is filtered
        // out (URI alphabet intersection). `a b` (with a space) matches `.* .*`-ish
        // patterns but is not a valid anyURI. Pattern `a b` → 0 valid URIs.
        match node_value_space(None, &[(pat("a b"), ())]) {
            NodeValueSpace::Finite { count: 0, .. } => {}
            _ => panic!("a-space-b is not a valid URI, expected empty"),
        }
        // A pattern with an unbounded language (no length facet) stays infinite.
        assert!(matches!(
            node_value_space(None, &[(pat("urn:a+"), ())]),
            NodeValueSpace::Infinite
        ));
        // pattern ∩ length window: `urn:[a-z]` with maxLength 4 keeps nothing
        // (each word is length 5), so the value space is empty ⇒ clash-prone.
        let pat_len = LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
            format!("{XSD}anyURI"),
            vec![format!("{XSD}pattern"), format!("{XSD}maxLength")],
            vec![
                Constant::create("urn:[a-z]", format!("{XSD}string")),
                Constant::create("4", format!("{XSD}nonNegativeInteger")),
            ],
        ));
        match node_value_space(None, &[(pat_len, ())]) {
            NodeValueSpace::Finite { count: 0, .. } => {}
            _ => panic!("urn:[a-z] (len 5) under maxLength 4 is empty"),
        }
    }

    #[test]
    fn strc_pattern_langrange_emptiness() {
        use crate::model::{AtomicDataRange, AtomicNegationDataRange};
        // FIX C: string / rdf:PlainLiteral pattern + langRange conjunction emptiness.
        let plain_dr = |facet: &str, val: &str| {
            crate::model::DatatypeRestriction::create(
                format!("{RDF}PlainLiteral"),
                vec![facet.to_string()],
                vec![Constant::create(val, format!("{XSD}string"))],
            )
        };
        let string_dr = |facet: &str, val: &str| {
            crate::model::DatatypeRestriction::create(
                format!("{XSD}string"),
                vec![facet.to_string()],
                vec![Constant::create(val, format!("{XSD}string"))],
            )
        };
        let pos = |dr: crate::model::DatatypeRestriction| {
            LiteralDataRange::DatatypeRestriction(dr)
        };
        let neg = |dr: crate::model::DatatypeRestriction| {
            LiteralDataRange::AtomicNegationDataRange(AtomicNegationDataRange::create(
                AtomicDataRange::DatatypeRestriction(dr),
            ))
        };
        let lr = format!("{RDF}langRange");
        let pat = format!("{XSD}pattern");

        // (1) langRange "en" ⊓ ¬PlainLiteral[langRange "en"] is EMPTY: the positive
        // forces tag=en over any string; the negation removes exactly that
        // (any-string × tag matching en), leaving nothing.
        assert!(conjunction_is_empty(&[
            (pos(plain_dr(&lr, "en")), ()),
            (neg(plain_dr(&lr, "en")), ()),
        ]));

        // (2) Two incompatible langRanges ⊓: en ⊓ fr is empty (disjoint tags).
        assert!(conjunction_is_empty(&[
            (pos(plain_dr(&lr, "en")), ()),
            (pos(plain_dr(&lr, "fr")), ()),
        ]));

        // (3) xsd:string ⊓ langRange "en": xsd:string demands an EMPTY tag, langRange
        // demands a non-empty `en` tag ⇒ empty.
        assert!(conjunction_is_empty(&[(pos(string_dr(&lr, "en")), ())]));

        // (4) Two incompatible finite patterns: {a,b} ⊓ {c} is empty.
        assert!(conjunction_is_empty(&[
            (pos(plain_dr(&pat, "[ab]")), ()),
            (pos(plain_dr(&pat, "c")), ()),
        ]));

        // (5) NOT empty: compatible langRange refinement en ⊓ en-GB survives (tag
        // en-GB). Must NOT be reported empty (no false clash).
        assert!(!conjunction_is_empty(&[
            (pos(plain_dr(&lr, "en")), ()),
            (pos(plain_dr(&lr, "en-GB")), ()),
        ]));

        // (6) NOT empty: langRange "en" ⊓ ¬PlainLiteral[langRange "fr"] keeps en.
        assert!(!conjunction_is_empty(&[
            (pos(plain_dr(&lr, "en")), ()),
            (neg(plain_dr(&lr, "fr")), ()),
        ]));

        // (7) NOT empty: a finite pattern whose words overlap survives.
        assert!(!conjunction_is_empty(&[
            (pos(plain_dr(&pat, "[ab]")), ()),
            (pos(plain_dr(&pat, "[bc]")), ()),
        ]));

        // (8) langRange "*" ⊓ ¬PlainLiteral[langRange "*"] is empty (any non-empty
        // tag minus any non-empty tag).
        assert!(conjunction_is_empty(&[
            (pos(plain_dr(&lr, "*")), ()),
            (neg(plain_dr(&lr, "*")), ()),
        ]));
    }

    #[test]
    fn string_value_space_subtracts_negated_oneof() {
        use crate::model::{AtomicDataRange, AtomicNegationDataRange, ConstantEnumeration};
        let str_const = |s: &str| Constant::create(s, format!("{XSD}string"));
        let pattern = |p: &str| {
            LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
                format!("{XSD}string"),
                vec![format!("{XSD}pattern")],
                vec![str_const(p)],
            ))
        };
        let neg_oneof = |members: Vec<&str>| {
            LiteralDataRange::AtomicNegationDataRange(AtomicNegationDataRange::create(
                AtomicDataRange::ConstantEnumeration(ConstantEnumeration::create(
                    members.into_iter().map(str_const).collect(),
                )),
            ))
        };

        // [ab]{2} is the 4-string language {aa, ab, ba, bb}. Excluding {aa, bb}
        // leaves exactly 2 strings — an exact finite count, not Infinite.
        let sp = string_automaton_value_space(&[
            (pattern("[ab]{2}"), ()),
            (neg_oneof(vec!["aa", "bb"]), ()),
        ])
        .expect("pattern + negated oneOf should be decided");
        match sp {
            NodeValueSpace::Finite { count, .. } => assert_eq!(count, 2),
            _ => panic!("expected Finite count 2"),
        }

        // Excluding a value that is NOT in the language removes nothing: {a, b} minus
        // {"c"} stays at 2.
        let sp = string_automaton_value_space(&[
            (pattern("[ab]"), ()),
            (neg_oneof(vec!["c"]), ()),
        ])
        .expect("decided");
        match sp {
            NodeValueSpace::Finite { count, .. } => assert_eq!(count, 2),
            _ => panic!("expected Finite count 2"),
        }

        // Excluding every member of a finite pattern empties the space (clash-able).
        let sp = string_automaton_value_space(&[
            (pattern("[ab]"), ()),
            (neg_oneof(vec!["a", "b"]), ()),
        ])
        .expect("decided");
        match sp {
            NodeValueSpace::Finite { count: 0, .. } => {}
            _ => panic!("expected empty space"),
        }

        // A `\p{...}`-bounded pattern is finite but the lightweight enumerator
        // (`finite_pattern_lang`) cannot model it, so this exercises the automaton
        // path: \p{Lu} has a fixed finite count; excluding 'A' lowers it by one.
        let full = string_automaton_value_space(&[(pattern("\\p{Lu}"), ())])
            .expect("decided");
        let full_count = match full {
            NodeValueSpace::Finite { count, .. } => count,
            _ => panic!("expected finite Lu space"),
        };
        assert!(full_count > 1);
        let minus_a = string_automaton_value_space(&[
            (pattern("\\p{Lu}"), ()),
            (neg_oneof(vec!["A"]), ()),
        ])
        .expect("decided");
        match minus_a {
            NodeValueSpace::Finite { count, .. } => assert_eq!(count, full_count - 1),
            _ => panic!("expected finite count"),
        }
    }

    #[test]
    fn node_value_space_string_pattern_minus_oneof_exact_count() {
        // End-to-end via node_value_space: a `\p{...}`-bounded pattern (which the
        // finite_pattern_lang enumerator cannot decide) combined with a negated
        // oneOf yields an EXACT finite count instead of Infinite.
        use crate::model::{AtomicDataRange, AtomicNegationDataRange, ConstantEnumeration};
        let str_const = |s: &str| Constant::create(s, format!("{XSD}string"));
        let pat = LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
            format!("{XSD}string"),
            vec![format!("{XSD}pattern")],
            vec![str_const("\\p{Lu}")],
        ));
        let exclude = LiteralDataRange::AtomicNegationDataRange(AtomicNegationDataRange::create(
            AtomicDataRange::ConstantEnumeration(ConstantEnumeration::create(vec![str_const("A")])),
        ));
        let full = match node_value_space(None, &[(pat.clone(), ())]) {
            NodeValueSpace::Finite { count, .. } => count,
            _ => panic!("expected finite Lu space"),
        };
        match node_value_space(None, &[(pat, ()), (exclude, ())]) {
            NodeValueSpace::Finite { count, .. } => assert_eq!(count, full - 1),
            _ => panic!("expected exact finite count"),
        }
    }

    #[test]
    fn chk3_length_string_materialization_assignment() {
        // xsd:string with maxLength 1 over the ASCII alphabet is a finite value
        // space reported with `values: None` (RDFPlainLiteralLengthValueSpaceSubset).
        // CHK-3: decide_component materializes it so the assignment search can run.
        // The value space is large (empty + many 1-char strings), so a small clique
        // is trivially satisfiable -- the point is the materializer yields a
        // non-empty value set, and the (count) is finite.
        let len1_string = LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
            format!("{XSD}string"),
            vec![format!("{XSD}maxLength")],
            vec![Constant::create("1", format!("{XSD}nonNegativeInteger"))],
        ));
        let sp = node_value_space(None, &[(len1_string.clone(), ())]);
        // Finite but unmaterialized at construction.
        assert!(matches!(sp, NodeValueSpace::Finite { values: None, .. }));
        // The CHK-3 materializer produces a non-empty list of distinct Text values.
        let mat = materialize_finite_value_space(&[(len1_string, ())], MAX_ENUMERATED_VALUES)
            .expect("length-string is materializable (CHK-3)");
        assert!(!mat.is_empty());
        assert!(mat.iter().all(|v| matches!(v, DataValue::Text(_))));
    }


    #[test]
    fn fd5_float_interval_with_exclusion_has_exact_cardinality() {
        // A float interval [1.0, 3.0] over a huge range... use a tight interval that
        // is small enough to enumerate to confirm exclusion handling, then a wide
        // one to confirm the FD-5 exact-count path (values: None) subtracts the
        // excluded points.
        use crate::model::{AtomicDataRange, AtomicNegationDataRange, ConstantEnumeration};
        let float = |s: &str| Constant::create(s, format!("{XSD}float"));
        // A wide interval [0.0, 1e30] (huge, > cap) minus the negated enumeration
        // {0.0}: the exact cardinality is (interval size) - 1.
        let wide = LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
            format!("{XSD}float"),
            vec![format!("{XSD}minInclusive"), format!("{XSD}maxInclusive")],
            vec![float("0.0"), float("1e30")],
        ));
        let exclude_zero = LiteralDataRange::AtomicNegationDataRange(AtomicNegationDataRange::create(
            AtomicDataRange::ConstantEnumeration(ConstantEnumeration::create(vec![float("0.0")])),
        ));
        let with_excl = node_value_space(None, &[(wide.clone(), ()), (exclude_zero, ())]);
        let plain = node_value_space(None, &[(wide, ())]);
        // Both are finite (FD-5: no longer Infinite); the excluded one is smaller.
        match (plain, with_excl) {
            (
                NodeValueSpace::Finite { count: c_plain, .. },
                NodeValueSpace::Finite { count: c_excl, .. },
            ) => {
                assert!(c_plain > 0);
                assert_eq!(c_excl, c_plain - 1, "excluding 0.0 removes exactly one value");
            }
            _ => panic!("expected two finite float spaces"),
        }
    }

    // Faithful to Java's bugged FloatInterval.isNaN (mantissa mask 0x003fffff): a
    // NaN bound on xsd:float is NOT recognised as NaN inside getIntervalFor — it is
    // mistaken for a positive value above +INF. A NaN min* facet therefore makes the
    // interval EMPTY, while a NaN max* facet is effectively dropped. (xsd:double's
    // mask is correct, so a NaN double bound is genuinely dropped in both cases.)
    #[test]
    fn float_nan_bound_reproduces_java_isnan_bug() {
        let float = |s: &str| Constant::create(s, format!("{XSD}float"));
        // NaN minInclusive => empty window (lower_key pushed above upper_key).
        let min_nan = crate::model::DatatypeRestriction::create(
            format!("{XSD}float"),
            vec![format!("{XSD}minInclusive")],
            vec![float("NaN")],
        );
        let (lo, hi) = float_restriction_key_window(&min_nan).unwrap();
        assert!(lo > hi, "NaN minInclusive must yield an empty float interval");
        // NaN maxInclusive => the bound is dropped; the window stays the full space.
        let max_nan = crate::model::DatatypeRestriction::create(
            format!("{XSD}float"),
            vec![format!("{XSD}maxInclusive")],
            vec![float("NaN")],
        );
        let (lo, hi) = float_restriction_key_window(&max_nan).unwrap();
        assert_eq!(lo, f32_order_key(f32::NEG_INFINITY));
        assert_eq!(hi, f32_order_key(f32::INFINITY));
        // The value-space cardinality of a NaN minInclusive float restriction is 0
        // (empty), with no NaN (the faceted restriction is a NoNaN subset that is
        // then empty).
        let space = node_value_space(
            None,
            &[(LiteralDataRange::DatatypeRestriction(min_nan), ())],
        );
        assert!(matches!(space, NodeValueSpace::Finite { count: 0, .. }));
        // A finite value never satisfies a NaN minInclusive float facet, but always
        // satisfies a NaN maxInclusive one.
        let v = parse_value(&float("1.0")).unwrap();
        assert!(!value_satisfies_facet(&v, &format!("{XSD}minInclusive"), &float("NaN")));
        assert!(value_satisfies_facet(&v, &format!("{XSD}maxInclusive"), &float("NaN")));
        // For xsd:double (correct mask), a NaN bound is dropped: the value satisfies
        // both a NaN minInclusive and a NaN maxInclusive facet.
        let dbl = |s: &str| Constant::create(s, format!("{XSD}double"));
        let dv = parse_value(&dbl("1.0")).unwrap();
        assert!(value_satisfies_facet(&dv, &format!("{XSD}minInclusive"), &dbl("NaN")));
        assert!(value_satisfies_facet(&dv, &format!("{XSD}maxInclusive"), &dbl("NaN")));
    }

    fn integer(lexical: &str) -> Constant {
        Constant::create(lexical, format!("{XSD}integer"))
    }
    fn decimal(lexical: &str) -> Constant {
        Constant::create(lexical, format!("{XSD}decimal"))
    }

    #[test]
    fn integer_and_decimal_compare_by_value() {
        let one_int = parse_value(&integer("1")).unwrap();
        let one_dec = parse_value(&decimal("1.0")).unwrap();
        // 1^^integer and 1.0^^decimal denote the same value-space point.
        assert!(values_equal(&one_int, &one_dec));
        // Distinct lexical forms of the same integer are equal.
        assert!(values_equal(
            &parse_value(&integer("1")).unwrap(),
            &parse_value(&integer("01")).unwrap()
        ));
        // Different values are not equal.
        assert!(!values_equal(&one_int, &parse_value(&integer("2")).unwrap()));
    }

    #[test]
    fn one_of_membership_uses_value_space() {
        use crate::model::ConstantEnumeration;
        // The enumeration {1.0^^decimal} contains 1^^integer by value.
        let enumeration =
            LiteralDataRange::ConstantEnumeration(ConstantEnumeration::create(vec![decimal("1.0")]));
        let value = parse_value(&integer("1")).unwrap();
        assert_eq!(value_in_range(&value, &enumeration), Some(true));
        let value_two = parse_value(&integer("2")).unwrap();
        assert_eq!(value_in_range(&value_two, &enumeration), Some(false));
    }

    #[test]
    fn ill_typed_literals_are_detected() {
        assert!(is_ill_typed(&integer("abc")));
        assert!(is_ill_typed(&Constant::create("yes", format!("{XSD}boolean"))));
        assert!(!is_ill_typed(&integer("42")));
        // Unknown datatypes are not judged.
        assert!(!is_ill_typed(&Constant::create("abc", "http://example.org/myDatatype")));
        // owl:real has no valid literals; any lexical form is ill-typed
        // (mirrors Java OWLRealDatatypeHandler.parseLiteral throwing MalformedLiteralException).
        assert!(is_ill_typed(&Constant::create("anything", format!("{OWL}real"))));
        assert!(is_ill_typed(&Constant::create("42", format!("{OWL}real"))));
    }

    #[test]
    fn binary_and_anyuri_datatypes() {
        let hex = |l: &str| Constant::create(l, format!("{XSD}hexBinary"));
        let b64 = |l: &str| Constant::create(l, format!("{XSD}base64Binary"));
        let uri = |l: &str| Constant::create(l, format!("{XSD}anyURI"));

        // hexBinary equality ignores case (canonical uppercase); length is octets.
        assert!(values_equal(&parse_value(&hex("0f1a")).unwrap(), &parse_value(&hex("0F1A")).unwrap()));
        assert!(value_satisfies_facet(
            &parse_value(&hex("0F1A")).unwrap(),
            &format!("{XSD}length"),
            &integer("2")
        ));
        // Invalid hex / base64 are ill-typed; anyURI accepts any lexical form.
        assert!(is_ill_typed(&hex("0G")));
        assert!(is_ill_typed(&hex("abc"))); // odd length
        assert!(is_ill_typed(&b64("@@@@")));
        assert!(!is_ill_typed(&b64("QUJD"))); // "ABC"
        assert!(!is_ill_typed(&uri("http://example.org/x")));
        // base64 octet length: "QUJD" decodes to 3 bytes.
        assert!(value_satisfies_facet(
            &parse_value(&b64("QUJD")).unwrap(),
            &format!("{XSD}length"),
            &integer("3")
        ));
        // A hexBinary value is not in the xsd:string value space (disjoint).
        assert!(!value_in_datatype(&parse_value(&hex("0F")).unwrap(), &format!("{XSD}string")));
    }

    #[test]
    fn rdf_plain_literal_lexical_handling() {
        // RDFPlainLiteralDatatypeHandler.parseLiteral requires '@'.
        let plain = |l: &str| Constant::create(l, format!("{RDF}PlainLiteral"));
        // Missing '@' ⇒ MalformedLiteralException ⇒ ill-typed.
        assert!(is_ill_typed(&plain("hello")));
        // "string@" (empty lang) ⇒ bare string value, equal to the xsd:string.
        let bare = parse_value(&plain("hello@")).unwrap();
        assert_eq!(bare, DataValue::Text("hello".to_string()));
        assert!(values_equal(
            &bare,
            &parse_value(&Constant::create("hello", format!("{XSD}string"))).unwrap()
        ));
        // "string@en" ⇒ a distinct language-tagged value, NOT equal to the bare string.
        let tagged = parse_value(&plain("hello@en")).unwrap();
        assert!(!values_equal(&tagged, &bare));
        assert_eq!(
            tagged,
            DataValue::LangString { string: "hello".to_string(), lang: "en".to_string() }
        );
        // The length facet counts only the string part (5), not "hello@en" (8).
        assert!(value_satisfies_facet(&tagged, &format!("{XSD}length"), &integer("5")));
        assert!(!value_satisfies_facet(&tagged, &format!("{XSD}length"), &integer("8")));
        // A language-tagged value is in rdf:PlainLiteral but not xsd:string.
        assert!(value_in_datatype(&tagged, &format!("{RDF}PlainLiteral")));
        assert!(!value_in_datatype(&tagged, &format!("{XSD}string")));
    }

    #[test]
    fn float_double_type_suffix_is_accepted() {
        // Float.parseFloat/Double.parseDouble accept a trailing f/F/d/D.
        let flt = |l: &str| Constant::create(l, format!("{XSD}float"));
        let dbl = |l: &str| Constant::create(l, format!("{XSD}double"));
        for s in ["1.0f", "1.0F", "1.0d", "1.0D"] {
            assert!(!is_ill_typed(&flt(s)), "xsd:float {s} should be well-typed");
        }
        for s in ["1.0f", "1.0F", "1.0d", "1.0D"] {
            assert!(!is_ill_typed(&dbl(s)), "xsd:double {s} should be well-typed");
        }
        // "1.0f"^^xsd:float denotes the same value as "1.0"^^xsd:float.
        assert!(values_equal(
            &parse_value(&flt("1.0f")).unwrap(),
            &parse_value(&flt("1.0")).unwrap()
        ));
        // The special spellings still work and a bare suffix is still ill-typed.
        assert!(!is_ill_typed(&flt("INF")));
        assert!(is_ill_typed(&flt("f")));
        assert!(is_ill_typed(&flt("abc")));
    }

    #[test]
    fn datetimestamp_requires_timezone() {
        // dateTimeStamp REQUIRES a timezone; dateTime does not.
        let dt = |l: &str| Constant::create(l, format!("{XSD}dateTime"));
        let dts = |l: &str| Constant::create(l, format!("{XSD}dateTimeStamp"));
        // dateTime without a timezone is well-typed.
        assert!(!is_ill_typed(&dt("2020-01-01T00:00:00")));
        // dateTimeStamp without a timezone is ill-typed.
        assert!(is_ill_typed(&dts("2020-01-01T00:00:00")));
        // dateTimeStamp WITH a timezone is well-typed.
        assert!(!is_ill_typed(&dts("2020-01-01T00:00:00Z")));
        assert!(!is_ill_typed(&dts("2020-01-01T00:00:00+01:00")));
    }

    #[test]
    fn datetime_hour24_end_of_day_coupling() {
        // DateTime.java:212: hour==24 is legal only as the exact end-of-day instant
        // 24:00:00(.0); non-zero minute or second must be rejected.
        let dt = |l: &str| Constant::create(l, format!("{XSD}dateTime"));
        assert!(!is_ill_typed(&dt("2020-01-01T24:00:00Z")));   // valid end-of-day
        assert!(!is_ill_typed(&dt("2020-01-01T24:00:00.0Z"))); // valid with fractional zero
        assert!(is_ill_typed(&dt("2020-01-01T24:30:00Z")));    // minute != 0 => ill-typed
        assert!(is_ill_typed(&dt("2020-01-01T24:00:01Z")));    // second != 0 => ill-typed
    }

    #[test]
    fn value_space_size_of_finite_ranges() {
        use crate::model::DatatypeRestriction;
        // xsd:boolean has two values.
        assert_eq!(
            value_space_size(&LiteralDataRange::DatatypeRestriction(
                DatatypeRestriction::create(format!("{XSD}boolean"), vec![], vec![])
            )),
            Some(2)
        );
        // integer[>=1, <=3] has three values; xsd:integer (unbounded) has none.
        let restriction = DatatypeRestriction::create(
            format!("{XSD}integer"),
            vec![format!("{XSD}minInclusive"), format!("{XSD}maxInclusive")],
            vec![integer("1"), integer("3")],
        );
        assert_eq!(
            value_space_size(&LiteralDataRange::DatatypeRestriction(restriction)),
            Some(3)
        );
        assert_eq!(
            value_space_size(&LiteralDataRange::DatatypeRestriction(
                DatatypeRestriction::create(format!("{XSD}integer"), vec![], vec![])
            )),
            None
        );
    }

    #[test]
    fn rational_and_string_subtypes() {
        let rational = |l: &str| Constant::create(l, format!("{OWL}rational"));
        // owl:rational "3/4" is the value 0.75, equal by value to 0.75^^decimal.
        assert!(values_equal(
            &parse_value(&rational("3/4")).unwrap(),
            &parse_value(&decimal("0.75")).unwrap()
        ));
        // A numeric value is in the owl:real / owl:rational value spaces.
        assert!(value_in_datatype(&parse_value(&integer("2")).unwrap(), &format!("{OWL}real")));
        assert!(value_in_datatype(
            &parse_value(&rational("3/4")).unwrap(),
            &format!("{OWL}rational")
        ));
        // Malformed rationals are ill-typed.
        assert!(is_ill_typed(&rational("3/0")));
        assert!(is_ill_typed(&rational("abc")));

        // The XSD string subtypes are treated as strings (length facets apply).
        let ncname = Constant::create("foo", format!("{XSD}NCName"));
        let value = parse_value(&ncname).unwrap();
        assert!(value_satisfies_facet(&value, &format!("{XSD}maxLength"), &integer("5")));
        assert!(!value_satisfies_facet(&value, &format!("{XSD}maxLength"), &integer("2")));
    }

    #[test]
    fn most_specific_range_distinguishes_decimal_from_rational() {
        // NumberRange.getMostSpecificRange: BigInteger -> INTEGER,
        // BigDecimal (finite decimal) -> DECIMAL, BigRational (no finite decimal
        // form) -> RATIONAL. We recover the three-way split from the reduced
        // fraction.
        assert_eq!(most_specific_range(&(BigInt::from(4), BigInt::one())), NumRange::Integer);
        // 7/2 = 3.5 has a finite decimal form -> DECIMAL.
        assert_eq!(most_specific_range(&(BigInt::from(7), BigInt::from(2))), NumRange::Decimal);
        // 3/20 = 0.15 (den = 2^2·5) -> DECIMAL.
        assert_eq!(most_specific_range(&(BigInt::from(3), BigInt::from(20))), NumRange::Decimal);
        // 1/3 has no finite decimal form -> RATIONAL (the case the old collapse missed).
        assert_eq!(most_specific_range(&(BigInt::from(1), BigInt::from(3))), NumRange::Rational);
        // 1/6 (den = 2·3) -> RATIONAL.
        assert_eq!(most_specific_range(&(BigInt::from(1), BigInt::from(6))), NumRange::Rational);

        // A faceted xsd:decimal whose only point is a non-decimal rational has an
        // EMPTY value space (1/3 is not in the DECIMAL range), matching Java's
        // isSubsetOf(getMostSpecificRange(1/3)=RATIONAL, DECIMAL)==false in
        // NumberInterval.isIntervalEmpty. The facet value is typed owl:rational.
        let rat = |l: &str| Constant::create(l, format!("{OWL}rational"));
        let dec_singleton = |val: &str| {
            crate::model::DatatypeRestriction::create(
                format!("{XSD}decimal"),
                vec![format!("{XSD}minInclusive"), format!("{XSD}maxInclusive")],
                vec![rat(val), rat(val)],
            )
        };
        assert!(matches!(num_interval_for(&dec_singleton("1/3")), NumIntervalResult::Empty));
        // But the singleton 7/2 (= 3.5, a real decimal) is a non-empty interval.
        assert!(matches!(
            num_interval_for(&dec_singleton("7/2")),
            NumIntervalResult::Interval(_)
        ));
        // owl:rational with the same 1/3 singleton is NON-empty (1/3 is a rational).
        let rat_singleton = crate::model::DatatypeRestriction::create(
            format!("{OWL}rational"),
            vec![format!("{XSD}minInclusive"), format!("{XSD}maxInclusive")],
            vec![rat("1/3"), rat("1/3")],
        );
        assert!(matches!(
            num_interval_for(&rat_singleton),
            NumIntervalResult::Interval(_)
        ));
    }

    #[test]
    fn float_special_values() {
        let double = |l: &str| Constant::create(l, format!("{XSD}double"));
        // NaN parses and is equal to itself (a single value-space point).
        let nan = parse_value(&double("NaN")).unwrap();
        assert!(values_equal(&nan, &parse_value(&double("NaN")).unwrap()));
        // INF / -INF parse to the IEEE infinities.
        assert_eq!(
            parse_value(&double("INF")),
            Some(DataValue::Double(f64::INFINITY.to_bits()))
        );
        assert_eq!(
            parse_value(&double("-INF")),
            Some(DataValue::Double(f64::NEG_INFINITY.to_bits()))
        );
        // +0.0 and -0.0 are *distinct* float/double values (OWL 2 / XSD 1.1),
        // and a float/double is never equal to the same-magnitude decimal.
        assert!(!values_equal(
            &parse_value(&double("+0.0")).unwrap(),
            &parse_value(&double("-0.0")).unwrap()
        ));
        assert!(!values_equal(
            &parse_value(&double("1.0")).unwrap(),
            &parse_value(&Constant::create("1.0", format!("{XSD}decimal"))).unwrap()
        ));
        // HermiT parses doubles with `Double.parseDouble`, so `Infinity`/`NaN`
        // spellings are valid too; but lowercase forms and `+INF` are rejected.
        assert_eq!(
            parse_value(&double("Infinity")),
            Some(DataValue::Double(f64::INFINITY.to_bits()))
        );
        assert!(parse_value(&double("nan")).is_none());
        assert!(parse_value(&double("infinity")).is_none());
        assert!(parse_value(&double("+INF")).is_none());

        // The specials are valid for the float types but ill-typed for decimal.
        assert!(!is_ill_typed(&double("INF")));
        assert!(is_ill_typed(&Constant::create("INF", format!("{XSD}decimal"))));
        assert!(is_ill_typed(&Constant::create("NaN", format!("{XSD}decimal"))));
        // xsd:decimal accepts exponent notation (`new BigDecimal("1e3")`).
        assert!(!is_ill_typed(&Constant::create("1e3", format!("{XSD}decimal"))));
        // A NaN value is not in the xsd:decimal value space.
        assert!(!value_in_datatype(&nan, &format!("{XSD}decimal")));
        assert!(value_in_datatype(&nan, &format!("{XSD}double")));
    }

    #[test]
    fn lexical_validation_matches_hermit() {
        let c = |l: &str, dt: &str| Constant::create(l, format!("{XSD}{dt}"));

        // String subtypes are pattern-validated.
        assert!(is_ill_typed(&c("foo bar", "NCName"))); // space illegal in NCName
        assert!(is_ill_typed(&c("a:b", "NCName"))); // ':' illegal in NCName
        assert!(!is_ill_typed(&c("a:b", "Name"))); // ':' is legal in Name
        assert!(is_ill_typed(&c("1abc", "Name"))); // leading digit illegal
        assert!(is_ill_typed(&c(" x", "token"))); // leading space illegal in token
        assert!(is_ill_typed(&c("a  b", "token"))); // double space illegal in token
        assert!(is_ill_typed(&c("a\tb", "normalizedString"))); // tab illegal
        assert!(is_ill_typed(&c("e n", "language"))); // space illegal in language
        assert!(!is_ill_typed(&c("en-GB", "language")));
        assert!(!is_ill_typed(&c("foo_bar.baz-1", "NCName")));
        assert!(!is_ill_typed(&c("any thing\tgoes", "string"))); // tab (0x09) is a valid XML Char

        // anyURI rejects spaces / illegal characters.
        assert!(is_ill_typed(&c("## not a uri", "anyURI")));
        assert!(is_ill_typed(&c("http://a b", "anyURI")));
        assert!(!is_ill_typed(&c("http://example.org/x#y", "anyURI")));

        // Double special-value spellings follow Double.parseDouble (+ INF/-INF).
        assert!(!is_ill_typed(&c("Infinity", "double")));
        assert!(!is_ill_typed(&c("INF", "double")));
        assert!(is_ill_typed(&c("+INF", "double")));
        assert!(is_ill_typed(&c("infinity", "double")));

        // Boolean is case-insensitive for true/false.
        assert!(!is_ill_typed(&c("TRUE", "boolean")));
        assert!(!is_ill_typed(&c("False", "boolean")));
        assert!(values_equal(
            &parse_value(&c("TRUE", "boolean")).unwrap(),
            &parse_value(&c("true", "boolean")).unwrap()
        ));

        // Decimal accepts exponent notation, kept exact.
        assert!(!is_ill_typed(&c("1E2", "decimal")));
        assert!(values_equal(
            &parse_value(&c("1E2", "decimal")).unwrap(),
            &parse_value(&c("100", "decimal")).unwrap()
        ));

        // xsd:date is not a supported datetime datatype.
        assert!(!is_datetime_datatype(&format!("{XSD}date")));
        assert!(parse_value(&c("2020-01-01", "date")).is_none());

        // owl:rational requires a positive denominator.
        assert!(is_ill_typed(&Constant::create("1/-2", format!("{OWL}rational"))));
        assert!(is_ill_typed(&Constant::create("1/0", format!("{OWL}rational"))));
        assert!(!is_ill_typed(&Constant::create("1/2", format!("{OWL}rational"))));
    }

    #[test]
    fn datetime_value_space() {
        let dt = |l: &str| Constant::create(l, format!("{XSD}dateTime"));
        // Java `DateTime.equals` compares the timezone offset too, so the same
        // instant written with different offsets (`Z` = offset 0 vs `+01:00`) is
        // NOT value-equal -- they are distinct points of the value space.
        assert!(!values_equal(
            &parse_value(&dt("2020-01-01T00:00:00Z")).unwrap(),
            &parse_value(&dt("2020-01-01T01:00:00+01:00")).unwrap()
        ));
        // The same instant with the same offset IS equal (`Z` == `+00:00`, both
        // offset 0, and `01` normalizes to `1`).
        assert!(values_equal(
            &parse_value(&dt("2020-01-01T00:00:00Z")).unwrap(),
            &parse_value(&dt("2020-01-01T00:00:00+00:00")).unwrap()
        ));
        // Different instants are not equal; ordering works.
        let earlier = parse_value(&dt("2019-06-15T12:00:00Z")).unwrap();
        let later = parse_value(&dt("2020-06-15T12:00:00Z")).unwrap();
        assert!(!values_equal(&earlier, &later));
        assert!(value_satisfies_facet(&later, &format!("{XSD}minInclusive"), &dt("2020-01-01T00:00:00Z")));
        assert!(!value_satisfies_facet(&earlier, &format!("{XSD}minInclusive"), &dt("2020-01-01T00:00:00Z")));
        // A malformed datetime is ill-typed (HermiT throws MalformedLiteralException
        // for an unparseable xsd:dateTime literal).
        assert!(parse_value(&dt("2020-13-01T00:00:00Z")).is_none());
        assert!(is_ill_typed(&dt("2020-13-01T00:00:00Z")));
    }

    /// An `xsd:dateTime` (or, with `stamp`, `xsd:dateTimeStamp`) datatype
    /// restriction with the given ordering facets. Each `(facet, lexical)` pair
    /// becomes a facet restriction whose value is a dateTime constant.
    fn datetime_restriction(stamp: bool, facets: &[(&str, &str)]) -> LiteralDataRange {
        let dt_uri = if stamp {
            format!("{XSD}dateTimeStamp")
        } else {
            format!("{XSD}dateTime")
        };
        let facet_uris: Vec<String> = facets.iter().map(|(f, _)| format!("{XSD}{f}")).collect();
        let values: Vec<Constant> = facets
            .iter()
            .map(|(_, l)| Constant::create(*l, dt_uri.clone()))
            .collect();
        LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
            dt_uri, facet_uris, values,
        ))
    }

    #[test]
    fn datetime_empty_interval_is_refuted() {
        // The SOUNDNESS bug: the live emptiness decision treated xsd:dateTime as
        // an opaque kind, so an empty dateTime facet range was never refuted and
        // minExclusive/maxExclusive were ignored. Mirrors Java
        // DateTimeInterval.isIntervalEmpty (lower>upper, or lower==upper with an
        // exclusive bound). Each of these must report the conjunction EMPTY
        // (⇒ Consistent: false end-to-end).

        // Reproducer 1: min > max (inclusive) ⇒ empty.
        assert!(conj(vec![datetime_restriction(
            false,
            &[
                ("minInclusive", "2020-01-01T00:00:00Z"),
                ("maxInclusive", "2010-01-01T00:00:00Z"),
            ],
        )]));

        // Equal bounds, exclusive ⇒ empty point (the exclusive facets are honored).
        assert!(conj(vec![datetime_restriction(
            false,
            &[
                ("minExclusive", "2020-01-01T00:00:00Z"),
                ("maxExclusive", "2020-01-01T00:00:00Z"),
            ],
        )]));
        // A single exclusive bound equal to an inclusive one also empties it.
        assert!(conj(vec![datetime_restriction(
            false,
            &[
                ("minInclusive", "2020-01-01T00:00:00Z"),
                ("maxExclusive", "2020-01-01T00:00:00Z"),
            ],
        )]));

        // Reproducers 3 & 4 use the same kind of empty single-restriction range
        // (min 2099 > max 2000); whether reached via a SubClassOf existential or
        // a DataMinCardinality, the fresh data node's conjunction is empty.
        let range_2099_2000 = || {
            datetime_restriction(
                false,
                &[
                    ("minInclusive", "2099-01-01T00:00:00Z"),
                    ("maxInclusive", "2000-01-01T00:00:00Z"),
                ],
            )
        };
        assert!(conj(vec![range_2099_2000()]));
        // The value-space view (the cross-node/cardinality machinery) agrees:
        // count 0, not Infinite — so a DataMinCardinality over it cannot be met.
        assert!(matches!(
            node_value_space(None, &[(range_2099_2000(), ())]),
            NodeValueSpace::Finite { count: 0, .. }
        ));

        // Reproducer 5: disjoint intersection [2000..2005] ⊓ [2010..2015] ⇒ empty.
        assert!(conj(vec![
            datetime_restriction(
                false,
                &[
                    ("minInclusive", "2000-01-01T00:00:00Z"),
                    ("maxInclusive", "2005-01-01T00:00:00Z"),
                ],
            ),
            datetime_restriction(
                false,
                &[
                    ("minInclusive", "2010-01-01T00:00:00Z"),
                    ("maxInclusive", "2015-01-01T00:00:00Z"),
                ],
            ),
        ]));

        // dateTimeStamp (mandatory timezone) gets the same interval logic.
        assert!(conj(vec![datetime_restriction(
            true,
            &[
                ("minInclusive", "2020-01-01T00:00:00Z"),
                ("maxInclusive", "2010-01-01T00:00:00Z"),
            ],
        )]));
    }

    #[test]
    fn datetime_non_empty_range_stays_satisfiable() {
        // Contrasts that must STAY consistent. A non-empty dateTime range is
        // dense/infinite, so its conjunction is non-empty and it admits any
        // number of distinct values (DateTimeInterval.subtractSizeFrom returns 0
        // — "infinite" — when the bounds are unequal).

        // A well-ordered closed range [2010..2020] is non-empty.
        let in_range = || {
            datetime_restriction(
                false,
                &[
                    ("minInclusive", "2010-01-01T00:00:00Z"),
                    ("maxInclusive", "2020-01-01T00:00:00Z"),
                ],
            )
        };
        assert!(!conj(vec![in_range()]));
        // It is dense ⇒ Infinite cardinality.
        assert!(matches!(
            node_value_space(None, &[(in_range(), ())]),
            NodeValueSpace::Infinite
        ));
        // So ≥5 (indeed any n) pairwise-distinct nodes over the range are
        // satisfiable — an infinite value space never clashes by pigeonhole.
        let spaces: Vec<NodeValueSpace> =
            (0..5).map(|_| node_value_space(None, &[(in_range(), ())])).collect();
        assert!(!component_is_unsatisfiable(&spaces.iter().collect::<Vec<_>>(), &clique(5), &no_specifics(5), &[]));

        // Equal bounds, both inclusive: a single-point (still "non-empty") range.
        assert!(!conj(vec![datetime_restriction(
            false,
            &[
                ("minInclusive", "2020-01-01T00:00:00Z"),
                ("maxInclusive", "2020-01-01T00:00:00Z"),
            ],
        )]));

        // Overlapping ranges intersect to a non-empty range.
        assert!(!conj(vec![
            datetime_restriction(
                false,
                &[("minInclusive", "2000-01-01T00:00:00Z")],
            ),
            datetime_restriction(
                false,
                &[("maxInclusive", "2010-01-01T00:00:00Z")],
            ),
        ]));
    }

    #[test]
    fn big_integer_decimal_rational_not_ill_typed() {
        // A syntactically valid integer/decimal/rational that overflows
        // i128 must NOT be declared ill-typed (HermiT uses BigInteger/
        // BigDecimal/BigRational). A 40-digit integer overflows i128 (max ~38
        // digits).
        let big = "1234567890123456789012345678901234567890"; // 40 digits
        assert!(big.parse::<i128>().is_err(), "precondition: overflows i128");
        let big_int = Constant::create(big, format!("{XSD}integer"));
        assert!(!is_ill_typed(&big_int), "40-digit xsd:integer must be well-typed");
        let value = parse_value(&big_int).unwrap();
        // It is in xsd:integer/owl:real but not in any bounded derived type.
        assert!(value_in_datatype(&value, &format!("{XSD}integer")));
        assert!(value_in_datatype(&value, &format!("{OWL}real")));
        assert!(!value_in_datatype(&value, &format!("{XSD}long")));
        assert!(!value_in_datatype(&value, &format!("{XSD}unsignedLong")));

        // End-to-end shape: a oneOf {bigint} ⊓ xsd:integer conjunction has a
        // feasible candidate, so the conjunction is NOT empty (no clash) — the
        // exact decision check_datatype_constraints performs for a fresh node.
        use crate::model::{ConstantEnumeration, DatatypeRestriction};
        let one_of = LiteralDataRange::ConstantEnumeration(ConstantEnumeration::create(vec![
            big_int.clone(),
        ]));
        let int_dr = LiteralDataRange::DatatypeRestriction(DatatypeRestriction::create(
            format!("{XSD}integer"),
            vec![],
            vec![],
        ));
        assert!(!conjunction_is_empty(&[(one_of, ()), (int_dr, ())]));

        // A huge decimal and a huge rational stay exact and well-typed.
        let big_dec = Constant::create(&format!("{big}.5"), format!("{XSD}decimal"));
        assert!(!is_ill_typed(&big_dec));
        let big_rat = Constant::create(
            &format!("{big}/{big}"),
            format!("{OWL}rational"),
        );
        assert!(!is_ill_typed(&big_rat));
        // bigN/bigN reduces to 1.
        assert!(values_equal(
            &parse_value(&big_rat).unwrap(),
            &parse_value(&integer("1")).unwrap()
        ));
    }

    #[test]
    fn exact_ordering_beyond_2pow53() {
        // A large integer exactly on a tight bound beyond 2^53 must be
        // classified exactly, not via f64 (where it would be indistinguishable
        // from its neighbour). 2^53 = 9007199254740992; 2^53+1 is not f64-exact.
        let bound = "9007199254740993"; // 2^53 + 1, not representable as f64
        let on_bound = parse_value(&integer(bound)).unwrap();
        let below = parse_value(&integer("9007199254740992")).unwrap(); // 2^53
        let max_incl = format!("{XSD}maxInclusive");
        let max_excl = format!("{XSD}maxExclusive");
        let bc = integer(bound);
        // value == bound: satisfies maxInclusive, NOT maxExclusive.
        assert!(value_satisfies_facet(&on_bound, &max_incl, &bc));
        assert!(!value_satisfies_facet(&on_bound, &max_excl, &bc));
        // 2^53 < 2^53+1: satisfies maxExclusive. With lossy f64 both round to
        // 9007199254740992.0 and this exclusive test would wrongly fail.
        assert!(value_satisfies_facet(&below, &max_excl, &bc));
        // Exact decimal on a tight bound: 0.1 (decimal) > 0.1 as nearest f64?
        // 1/3 compared exactly against 0.3333333333333333.
        let third = parse_value(&Constant::create("1/3", format!("{OWL}rational"))).unwrap();
        let approx = Constant::create("0.3333333333333333", format!("{XSD}decimal"));
        // 1/3 > 0.3333333333333333 exactly (the decimal truncates), so it does
        // NOT satisfy maxInclusive 0.3333333333333333.
        assert!(!value_satisfies_facet(&third, &max_incl, &approx));
        assert!(value_satisfies_facet(&third, &format!("{XSD}minExclusive"), &approx));
    }

    #[test]
    fn unsupported_facets_are_rejected() {
        // Each handler has a fixed supported-facet set; an unsupported
        // facet is an UnsupportedFacetException in HermiT, never silently
        // accepted. is_supported_facet mirrors the handlers' supported sets.
        // totalDigits / fractionDigits / whiteSpace: supported by NO handler.
        for f in ["totalDigits", "fractionDigits", "whiteSpace"] {
            assert!(!is_supported_facet(&format!("{XSD}integer"), &format!("{XSD}{f}")));
            assert!(!is_supported_facet(&format!("{XSD}string"), &format!("{XSD}{f}")));
        }
        // length facets: only string/binary/anyURI, NOT numerics/datetime.
        assert!(!is_supported_facet(&format!("{XSD}integer"), &format!("{XSD}length")));
        assert!(!is_supported_facet(&format!("{XSD}dateTime"), &format!("{XSD}minLength")));
        assert!(is_supported_facet(&format!("{XSD}string"), &format!("{XSD}length")));
        assert!(is_supported_facet(&format!("{XSD}hexBinary"), &format!("{XSD}maxLength")));
        assert!(is_supported_facet(&format!("{XSD}anyURI"), &format!("{XSD}length")));
        // ordering facets: only numerics/datetime, NOT strings/binary.
        assert!(is_supported_facet(&format!("{XSD}integer"), &format!("{XSD}minInclusive")));
        assert!(is_supported_facet(&format!("{XSD}dateTime"), &format!("{XSD}maxInclusive")));
        assert!(!is_supported_facet(&format!("{XSD}string"), &format!("{XSD}minInclusive")));
        assert!(!is_supported_facet(&format!("{XSD}hexBinary"), &format!("{XSD}minInclusive")));
        // pattern: string subtypes and anyURI, NOT binary.
        assert!(is_supported_facet(&format!("{XSD}string"), &format!("{XSD}pattern")));
        assert!(is_supported_facet(&format!("{XSD}anyURI"), &format!("{XSD}pattern")));
        assert!(!is_supported_facet(&format!("{XSD}hexBinary"), &format!("{XSD}pattern")));
        // langRange: rdf:PlainLiteral / string only.
        assert!(is_supported_facet(&format!("{RDF}PlainLiteral"), &format!("{RDF}langRange")));
        assert!(!is_supported_facet(&format!("{XSD}integer"), &format!("{RDF}langRange")));
        // boolean / XMLLiteral: no facets at all.
        assert!(!is_supported_facet(&format!("{XSD}boolean"), &format!("{XSD}pattern")));
        assert!(!is_supported_facet(&format!("{RDF}XMLLiteral"), &format!("{XSD}length")));

        // range_has_unsupported_facet (what check_datatype_constraints clashes
        // on) flags a restriction with an unsupported facet.
        use crate::model::DatatypeRestriction;
        let bad = LiteralDataRange::DatatypeRestriction(DatatypeRestriction::create(
            format!("{XSD}integer"),
            vec![format!("{XSD}totalDigits")],
            vec![integer("5")],
        ));
        assert!(range_has_unsupported_facet(&bad));
        let good = LiteralDataRange::DatatypeRestriction(DatatypeRestriction::create(
            format!("{XSD}integer"),
            vec![format!("{XSD}minInclusive")],
            vec![integer("5")],
        ));
        assert!(!range_has_unsupported_facet(&good));
    }

    #[test]
    fn string_length_counts_utf16_code_units() {
        // HermiT counts UTF-16 code units (Java String.length()); an
        // astral-plane char (here U+1F600) counts as 2.
        let s = Constant::create("a\u{1F600}", format!("{XSD}string"));
        let value = parse_value(&s).unwrap();
        // 2 code points, but 3 UTF-16 code units ('a' + surrogate pair).
        assert!(value_satisfies_facet(&value, &format!("{XSD}length"), &integer("3")));
        assert!(!value_satisfies_facet(&value, &format!("{XSD}length"), &integer("2")));
        // anyURI length is also UTF-16 code units.
        let uri = parse_value(&Constant::create(
            "http://x/\u{1F600}",
            format!("{XSD}anyURI"),
        ))
        .unwrap();
        // "http://x/" = 9 + 2 for the emoji = 11 UTF-16 units.
        assert!(value_satisfies_facet(&uri, &format!("{XSD}length"), &integer("11")));
    }

    #[test]
    fn pattern_applies_to_anyuri() {
        // xsd:pattern applies to xsd:anyURI (AnyURIDatatypeHandler), which
        // is a Typed value (the pattern facet applies to Typed values, not only Text).
        let uri = parse_value(&Constant::create(
            "http://example.org/x",
            format!("{XSD}anyURI"),
        ))
        .unwrap();
        let pattern = format!("{XSD}pattern");
        // Matching pattern: satisfied.
        assert!(value_satisfies_facet(
            &uri,
            &pattern,
            &Constant::create("http://.*", format!("{XSD}string"))
        ));
        // Non-matching anchored pattern: NOT satisfied.
        assert!(!value_satisfies_facet(
            &uri,
            &pattern,
            &Constant::create("ftp://.*", format!("{XSD}string"))
        ));
    }

    #[test]
    fn lang_range_and_string_membership() {
        // rdf:langRange (RFC 4647 basic filtering) and xsd:string
        // excluding language-tagged literals.
        let plain = |l: &str| Constant::create(l, format!("{RDF}PlainLiteral"));
        let en = parse_value(&plain("hello@en")).unwrap();
        let en_gb = parse_value(&plain("hello@en-GB")).unwrap();
        let eng = parse_value(&plain("hello@eng")).unwrap();
        let bare = parse_value(&plain("hello@")).unwrap(); // empty tag -> xsd:string value
        let lr = format!("{RDF}langRange");
        let range = |r: &str| Constant::create(r, format!("{XSD}string"));
        // "en" matches en and en-GB (case-insensitively) but not "eng".
        assert!(value_satisfies_facet(&en, &lr, &range("en")));
        assert!(value_satisfies_facet(&en_gb, &lr, &range("en")));
        assert!(value_satisfies_facet(&en_gb, &lr, &range("EN"))); // case-insensitive
        assert!(!value_satisfies_facet(&eng, &lr, &range("en")));
        // "*" matches any non-empty tag, but not a tag-less value.
        assert!(value_satisfies_facet(&en, &lr, &range("*")));
        assert!(!value_satisfies_facet(&bare, &lr, &range("*")));
        // A tag-less value never matches a concrete range.
        assert!(!value_satisfies_facet(&bare, &lr, &range("en")));

        // A language-tagged value is in rdf:PlainLiteral but NOT xsd:string.
        assert!(value_in_datatype(&en, &format!("{RDF}PlainLiteral")));
        assert!(!value_in_datatype(&en, &format!("{XSD}string")));
        // The bare (empty-tag) value IS an xsd:string.
        assert!(value_in_datatype(&bare, &format!("{XSD}string")));
    }

    #[test]
    fn xml_literal_registered_and_well_formedness() {
        // rdf:XMLLiteral is registered as its own disjoint datatype; a
        // malformed XML lexical form is ill-typed, well-formed is accepted, and
        // it admits no facets.
        let xml = |l: &str| Constant::create(l, format!("{RDF}XMLLiteral"));
        assert!(is_supported_datatype(&format!("{RDF}XMLLiteral")));
        // Well-formed fragments parse.
        assert!(!is_ill_typed(&xml("<a>text</a>")));
        assert!(!is_ill_typed(&xml("<a><b/>x</a>")));
        assert!(!is_ill_typed(&xml("plain text")));
        assert!(!is_ill_typed(&xml("<a x=\"1\">y</a>")));
        // Malformed (unbalanced / mismatched / unterminated) are ill-typed.
        assert!(is_ill_typed(&xml("<a>text")));
        assert!(is_ill_typed(&xml("<a></b>")));
        assert!(is_ill_typed(&xml("<a")));
        assert!(is_ill_typed(&xml("a < b")));
        // Its value space is disjoint from xsd:string and others.
        let v = parse_value(&xml("<a/>")).unwrap();
        assert!(value_in_datatype(&v, &format!("{RDF}XMLLiteral")));
        assert!(!value_in_datatype(&v, &format!("{XSD}string")));
        // No facets are supported.
        assert!(!is_supported_facet(&format!("{RDF}XMLLiteral"), &format!("{XSD}length")));
        use crate::model::DatatypeRestriction;
        let faceted = LiteralDataRange::DatatypeRestriction(DatatypeRestriction::create(
            format!("{RDF}XMLLiteral"),
            vec![format!("{XSD}length")],
            vec![integer("1")],
        ));
        assert!(range_has_unsupported_facet(&faceted));
    }

    #[test]
    fn derived_integer_bounds_are_enforced() {
        let nni = |l: &str| Constant::create(l, format!("{XSD}nonNegativeInteger"));
        let ubyte = |l: &str| Constant::create(l, format!("{XSD}unsignedByte"));
        let pos = |l: &str| Constant::create(l, format!("{XSD}positiveInteger"));

        // Out-of-range values of a derived integer type are ill-typed.
        assert!(is_ill_typed(&nni("-1")));
        assert!(is_ill_typed(&ubyte("256")));
        assert!(is_ill_typed(&pos("0")));
        // In-range values are fine and compare by integer value.
        assert!(!is_ill_typed(&nni("0")));
        assert!(!is_ill_typed(&ubyte("255")));
        assert!(values_equal(
            &parse_value(&nni("7")).unwrap(),
            &parse_value(&integer("7")).unwrap()
        ));
    }

    // ----- Cross-node value-assignment decision (complete). -----

    /// A fresh data node constrained to the single datatype restriction `range`.
    fn space_of(range: LiteralDataRange) -> NodeValueSpace {
        node_value_space(None, &[(range, ())])
    }
    fn boolean_space() -> NodeValueSpace {
        space_of(LiteralDataRange::DatatypeRestriction(
            crate::model::DatatypeRestriction::create(format!("{XSD}boolean"), vec![], vec![]),
        ))
    }
    /// A bounded integer range `[lo..hi]` (inclusive).
    fn int_range_space(lo: i64, hi: i64) -> NodeValueSpace {
        space_of(LiteralDataRange::DatatypeRestriction(
            crate::model::DatatypeRestriction::create(
                format!("{XSD}integer"),
                vec![format!("{XSD}minInclusive"), format!("{XSD}maxInclusive")],
                vec![integer(&lo.to_string()), integer(&hi.to_string())],
            ),
        ))
    }
    /// The complete (clique) adjacency over `n` pairwise-distinct nodes.
    fn clique(n: usize) -> Vec<Vec<usize>> {
        (0..n)
            .map(|i| (0..n).filter(|&j| j != i).collect())
            .collect()
    }

    /// A `most_specific` slice of all-`None` of the given length, for tests that
    /// exercise `component_is_unsatisfiable` without datatype-URI-driven
    /// `eliminateTrivialInequalities` edge removal.
    fn no_specifics(n: usize) -> Vec<Option<&'static str>> {
        vec![None; n]
    }

    #[test]
    fn a2_node_value_space_cardinalities_are_exact() {
        // booleans = 2; bounded integer [1..3] = 3; a wide interval [0..1_000_000]
        // has its exact (large) cardinality, not a capped/Unbounded approximation;
        // unbounded xsd:integer is infinite.
        assert!(matches!(boolean_space(), NodeValueSpace::Finite { count: 2, .. }));
        assert!(matches!(int_range_space(1, 3), NodeValueSpace::Finite { count: 3, .. }));
        assert!(matches!(
            int_range_space(0, 1_000_000),
            NodeValueSpace::Finite { count: 1_000_001, values: None }
        ));
        assert!(matches!(
            space_of(LiteralDataRange::DatatypeRestriction(
                crate::model::DatatypeRestriction::create(format!("{XSD}integer"), vec![], vec![])
            )),
            NodeValueSpace::Infinite
        ));
    }

    #[test]
    fn a2_integer_interval_with_non_integer_facet_bound_is_finite() {
        // `xsd:integer ⊓ maxInclusive "2.5" ⊓ minInclusive "0.5"`: Java's
        // NumberInterval constructor rounds the non-integer facet bounds inward
        // (getNearestIntegerInBound): maxInclusive 2.5 -> effective max 2,
        // minInclusive 0.5 -> effective min 1. The value space is {1, 2}, so the
        // cardinality is exactly 2 (a genuine finite space — NOT Infinite).
        let int_with_decimal_facets = |min: &str, max: &str| {
            space_of(LiteralDataRange::DatatypeRestriction(
                crate::model::DatatypeRestriction::create(
                    format!("{XSD}integer"),
                    vec![format!("{XSD}minInclusive"), format!("{XSD}maxInclusive")],
                    vec![decimal(min), decimal(max)],
                ),
            ))
        };
        assert!(matches!(
            int_with_decimal_facets("0.5", "2.5"),
            NodeValueSpace::Finite { count: 2, .. }
        ));
        // maxInclusive 2.5 alone (lower bound from xsd:integer is unbounded below)
        // is still infinite (no finite lower bound), matching Java.
        let int_max_only = space_of(LiteralDataRange::DatatypeRestriction(
            crate::model::DatatypeRestriction::create(
                format!("{XSD}integer"),
                vec![format!("{XSD}maxInclusive")],
                vec![decimal("2.5")],
            ),
        ));
        assert!(matches!(int_max_only, NodeValueSpace::Infinite));
        // minExclusive 0.5, maxExclusive 3.5 -> effective min 1 (0.5 rounds up to 1,
        // exclusive doesn't matter since 0.5 isn't an integer), effective max 3:
        // {1, 2, 3} -> 3. A pigeonhole among 4 such distinct nodes must clash.
        let four: Vec<NodeValueSpace> = (0..4)
            .map(|_| {
                space_of(LiteralDataRange::DatatypeRestriction(
                    crate::model::DatatypeRestriction::create(
                        format!("{XSD}integer"),
                        vec![format!("{XSD}minExclusive"), format!("{XSD}maxExclusive")],
                        vec![decimal("0.5"), decimal("3.5")],
                    ),
                ))
            })
            .collect();
        assert!(matches!(four[0], NodeValueSpace::Finite { count: 3, .. }));
        assert!(component_is_unsatisfiable(
            &four.iter().collect::<Vec<_>>(),
            &clique(4),
            &no_specifics(4),
            &[]
        ));
    }

    #[test]
    fn a2_pigeonhole_clash_over_booleans() {
        // 13 pairwise-distinct xsd:boolean data nodes cannot all differ — the
        // boolean value space has only 2 points (pigeonhole). HermiT's symmetric-
        // clique `hasCardinalityAtLeast(13)` over a value space of size 2 fails,
        // so this is INCONSISTENT. The old port skipped components > 12 nodes and
        // would silently miss it.
        let spaces: Vec<NodeValueSpace> = (0..13).map(|_| boolean_space()).collect();
        let refs: Vec<&NodeValueSpace> = spaces.iter().collect();
        assert!(component_is_unsatisfiable(&refs, &clique(13), &no_specifics(13), &[]));
        // Exactly 2 distinct booleans is satisfiable; 3 already over-fills it.
        let two: Vec<NodeValueSpace> = (0..2).map(|_| boolean_space()).collect();
        assert!(!component_is_unsatisfiable(&two.iter().collect::<Vec<_>>(), &clique(2), &no_specifics(2), &[]));
        let three: Vec<NodeValueSpace> = (0..3).map(|_| boolean_space()).collect();
        assert!(component_is_unsatisfiable(&three.iter().collect::<Vec<_>>(), &clique(3), &no_specifics(3), &[]));
    }

    #[test]
    fn a2_pigeonhole_clash_over_bounded_integer_range() {
        // 4 mutually-distinct nodes each constrained to the integer range [1..3]
        // (value space size 3) is INCONSISTENT (4 > 3); 3 nodes fit exactly.
        let four: Vec<NodeValueSpace> = (0..4).map(|_| int_range_space(1, 3)).collect();
        assert!(component_is_unsatisfiable(&four.iter().collect::<Vec<_>>(), &clique(4), &no_specifics(4), &[]));
        let three: Vec<NodeValueSpace> = (0..3).map(|_| int_range_space(1, 3)).collect();
        assert!(!component_is_unsatisfiable(&three.iter().collect::<Vec<_>>(), &clique(3), &no_specifics(3), &[]));
    }

    #[test]
    fn a2_large_component_is_decided_not_skipped() {
        // 20 mutually-distinct booleans (> the old MAX_COMPONENT_NODES = 12 cap):
        // still decided as a clash. No component is skipped for being large.
        let spaces: Vec<NodeValueSpace> = (0..20).map(|_| boolean_space()).collect();
        assert!(component_is_unsatisfiable(&spaces.iter().collect::<Vec<_>>(), &clique(20), &no_specifics(20), &[]));
    }

    #[test]
    fn a2_infinite_value_spaces_never_clash() {
        // An infinite value space (unbounded integer / dense decimal / string)
        // trivially satisfies any number of distinct nodes — no enumeration, no
        // false clash.
        let unbounded_int = || {
            space_of(LiteralDataRange::DatatypeRestriction(
                crate::model::DatatypeRestriction::create(format!("{XSD}integer"), vec![], vec![]),
            ))
        };
        let spaces: Vec<NodeValueSpace> = (0..100).map(|_| unbounded_int()).collect();
        assert!(!component_is_unsatisfiable(&spaces.iter().collect::<Vec<_>>(), &clique(100), &no_specifics(100), &[]));
    }

    #[test]
    fn a2_mixed_finite_and_infinite_general_case() {
        // A non-clique mixed component: two booleans plus an unbounded integer,
        // all pairwise distinct. The unbounded node is eliminated; the two
        // booleans can still take distinct values (true/false) — satisfiable.
        let spaces = [boolean_space(), boolean_space(), int_range_space(0, 0)];
        // Path graph 0-1, 1-2: not a clique. Node 2 is the fixed value {0}.
        let adjacency = vec![vec![1], vec![0, 2], vec![1]];
        let refs: Vec<&NodeValueSpace> = spaces.iter().collect();
        assert!(!component_is_unsatisfiable(&refs, &adjacency, &no_specifics(refs.len()), &[]));
        // But three nodes ALL fixed to the same singleton value {0}, pairwise
        // distinct, is a clash (3 nodes, 1 value).
        let singletons = [int_range_space(0, 0), int_range_space(0, 0), int_range_space(0, 0)];
        assert!(component_is_unsatisfiable(&singletons.iter().collect::<Vec<_>>(), &clique(3), &no_specifics(3), &[]));
    }

    // ----- Negated-datatype emptiness over infinite value spaces. -----

    /// A facet-free positive datatype restriction over `uri`.
    fn dtype(uri: String) -> LiteralDataRange {
        LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
            uri,
            vec![],
            vec![],
        ))
    }
    /// The negation `¬uri` of a facet-free datatype.
    fn neg_dtype(uri: String) -> LiteralDataRange {
        let LiteralDataRange::DatatypeRestriction(dr) = dtype(uri) else {
            unreachable!()
        };
        dr.get_negation()
    }
    fn conj(ranges: Vec<LiteralDataRange>) -> bool {
        let with_dep: Vec<(LiteralDataRange, ())> = ranges.into_iter().map(|r| (r, ())).collect();
        conjunction_is_empty(&with_dep)
    }

    #[test]
    fn disjoint_numeric_handlers_clash() {
        // xsd:float, xsd:double and the owl:real family are managed by distinct
        // handlers, whose value spaces are pairwise disjoint
        // (DatatypeRegistry.isDisjointWith). A fresh node carrying two such
        // positive restrictions is unsatisfiable.
        assert!(conj(vec![
            dtype(format!("{XSD}float")),
            dtype(format!("{XSD}double")),
        ]));
        assert!(conj(vec![
            dtype(format!("{XSD}float")),
            dtype(format!("{XSD}integer")),
        ]));
        assert!(conj(vec![
            dtype(format!("{XSD}double")),
            dtype(format!("{XSD}decimal")),
        ]));
        // Same handler -> NOT an immediate kind clash (integer ⊆ decimal).
        assert!(!conj(vec![
            dtype(format!("{XSD}integer")),
            dtype(format!("{XSD}decimal")),
        ]));
    }

    #[test]
    fn equal_bound_exclusive_is_empty() {
        // decimal[minInclusive 5][minExclusive 5][maxInclusive 5]: the exclusive
        // lower bound at the same value as the inclusive upper bound carves out an
        // empty interval (OWLRealDatatypeHandler keeps the more restrictive
        // bound type on a tie), regardless of facet order.
        let restriction = crate::model::DatatypeRestriction::create(
            format!("{XSD}decimal"),
            vec![
                format!("{XSD}minInclusive"),
                format!("{XSD}minExclusive"),
                format!("{XSD}maxInclusive"),
            ],
            vec![decimal("5"), decimal("5"), decimal("5")],
        );
        assert!(conj(vec![LiteralDataRange::DatatypeRestriction(restriction)]));
        // The inclusive-only [5,5] interval is NOT empty (it contains 5).
        let ok = crate::model::DatatypeRestriction::create(
            format!("{XSD}decimal"),
            vec![format!("{XSD}minInclusive"), format!("{XSD}maxInclusive")],
            vec![decimal("5"), decimal("5")],
        );
        assert!(!conj(vec![LiteralDataRange::DatatypeRestriction(ok)]));
    }

    #[test]
    fn integer_interval_empty_over_integers() {
        // An interval that is non-empty over the reals but empty over the
        // integers must clash for an integer base datatype: NumberInterval.
        // isIntervalEmpty rounds the bounds inward to the nearest contained
        // integer (OWLRealDatatypeHandler.getIntervalFor builds an INTEGER
        // NumberInterval).
        // xsd:integer[minExclusive 2, maxExclusive 3] -> no integer in (2,3).
        let exclusive_gap = crate::model::DatatypeRestriction::create(
            format!("{XSD}integer"),
            vec![format!("{XSD}minExclusive"), format!("{XSD}maxExclusive")],
            vec![integer("2"), integer("3")],
        );
        assert!(conj(vec![LiteralDataRange::DatatypeRestriction(exclusive_gap)]));
        // xsd:integer[minExclusive 2, maxInclusive 2] -> (2,2] empty.
        let half_open = crate::model::DatatypeRestriction::create(
            format!("{XSD}integer"),
            vec![format!("{XSD}minExclusive"), format!("{XSD}maxInclusive")],
            vec![integer("2"), integer("2")],
        );
        assert!(conj(vec![LiteralDataRange::DatatypeRestriction(half_open)]));
        // xsd:integer[minInclusive 2.5, maxInclusive 2.5] -> no integer at 2.5.
        let fractional = crate::model::DatatypeRestriction::create(
            format!("{XSD}integer"),
            vec![format!("{XSD}minInclusive"), format!("{XSD}maxInclusive")],
            vec![decimal("2.5"), decimal("2.5")],
        );
        assert!(conj(vec![LiteralDataRange::DatatypeRestriction(fractional)]));
        // xsd:integer[minInclusive 2, maxInclusive 3] -> {2,3} non-empty.
        let non_empty = crate::model::DatatypeRestriction::create(
            format!("{XSD}integer"),
            vec![format!("{XSD}minInclusive"), format!("{XSD}maxInclusive")],
            vec![integer("2"), integer("3")],
        );
        assert!(!conj(vec![LiteralDataRange::DatatypeRestriction(non_empty)]));
        // xsd:decimal[minExclusive 2, maxExclusive 3] is NOT integer-based, so it
        // stays non-empty (2.5 is a member).
        let decimal_gap = crate::model::DatatypeRestriction::create(
            format!("{XSD}decimal"),
            vec![format!("{XSD}minExclusive"), format!("{XSD}maxExclusive")],
            vec![integer("2"), integer("3")],
        );
        assert!(!conj(vec![LiteralDataRange::DatatypeRestriction(decimal_gap)]));
    }

    #[test]
    fn integer_intersect_complement_integer_is_empty() {
        // Reproducer 1: DataIntersectionOf(integer, DataComplementOf(integer)) on
        // a fresh data node. integer ⊓ ¬integer removes every value -> empty ->
        // INCONSISTENT: conjunction_is_empty must account for the negation even
        // though the positive integer space is infinite.
        assert!(conj(vec![
            dtype(format!("{XSD}integer")),
            neg_dtype(format!("{XSD}integer")),
        ]));
        // And the value-space view agrees (the cross-node assignment pass): an
        // empty (count 0) space, not Infinite.
        let space = node_value_space(
            None,
            &[
                (dtype(format!("{XSD}integer")), ()),
                (neg_dtype(format!("{XSD}integer")), ()),
            ],
        );
        assert!(matches!(space, NodeValueSpace::Finite { count: 0, .. }));
    }

    #[test]
    fn integer_with_negated_superset_is_empty() {
        // integer ⊆ decimal ⊆ rational ⊆ real, so negating any superset deletes
        // all of integer -> empty. (Reproducer 2's ∃-witness carries integer and
        // ¬integer; the superset cases generalize it.)
        // integer ⊓ ¬decimal (xsd namespace).
        assert!(conj(vec![
            dtype(format!("{XSD}integer")),
            neg_dtype(format!("{XSD}decimal")),
        ]));
        // integer ⊓ ¬rational and integer ⊓ ¬real (both in the owl namespace).
        for sup in ["rational", "real"] {
            assert!(
                conj(vec![
                    dtype(format!("{XSD}integer")),
                    neg_dtype(format!("{OWL}{sup}")),
                ]),
                "integer ⊓ ¬{sup} should be empty"
            );
        }
        // A bounded derived integer type is also a subset: byte ⊓ ¬integer empty.
        assert!(conj(vec![
            dtype(format!("{XSD}byte")),
            neg_dtype(format!("{XSD}integer")),
        ]));
    }

    #[test]
    fn negated_non_superset_stays_consistent() {
        // Contrast: integer ⊓ ¬string is NON-empty (integers that aren't strings)
        // -> CONSISTENT. Distinct base kinds are disjoint, so negating one does
        // not touch the other.
        assert!(!conj(vec![
            dtype(format!("{XSD}integer")),
            neg_dtype(format!("{XSD}string")),
        ]));
        // integer ⊓ ¬decimal is empty (integer ⊆ decimal), but decimal ⊓ ¬integer
        // is NON-empty (non-integer decimals exist) -> must stay consistent.
        assert!(!conj(vec![
            dtype(format!("{XSD}decimal")),
            neg_dtype(format!("{XSD}integer")),
        ]));
        // float and double are disjoint from owl:real and from each other.
        assert!(!conj(vec![
            dtype(format!("{XSD}integer")),
            neg_dtype(format!("{XSD}float")),
        ]));
        assert!(!conj(vec![
            dtype(format!("{XSD}float")),
            neg_dtype(format!("{XSD}double")),
        ]));
        // boolean ⊓ ¬integer non-empty.
        assert!(!conj(vec![
            dtype(format!("{XSD}boolean")),
            neg_dtype(format!("{XSD}integer")),
        ]));
    }

    #[test]
    fn existing_emptiness_contrasts_still_hold() {
        // Contrasting cases that must remain empty:
        // * incompatible base datatypes integer ⊓ string -> empty.
        assert!(conj(vec![
            dtype(format!("{XSD}integer")),
            dtype(format!("{XSD}string")),
        ]));
        // * a directly-empty facet interval integer[≥5, ≤3] -> empty.
        let empty_interval = LiteralDataRange::DatatypeRestriction(
            crate::model::DatatypeRestriction::create(
                format!("{XSD}integer"),
                vec![format!("{XSD}minInclusive"), format!("{XSD}maxInclusive")],
                vec![integer("5"), integer("3")],
            ),
        );
        assert!(conj(vec![empty_interval]));
        // * a single positive integer datatype alone is non-empty.
        assert!(!conj(vec![dtype(format!("{XSD}integer"))]));
        // * integer ⊓ ¬string non-empty (re-checked alongside the interval logic).
        assert!(!conj(vec![
            dtype(format!("{XSD}integer")),
            neg_dtype(format!("{XSD}string")),
        ]));
    }

    /// The value-non-constraining `internal:defdata#N` placeholder the live
    /// `∃p.DataIntersectionOf(...)` path adds onto the witness data node.
    fn defdata_placeholder() -> LiteralDataRange {
        LiteralDataRange::InternalDatatype(crate::model::InternalDatatype::create(
            "internal:defdata#0",
        ))
    }
    /// The universal `rdfs:Literal` top, likewise non-constraining.
    fn rdfs_literal() -> LiteralDataRange {
        LiteralDataRange::InternalDatatype(crate::model::InternalDatatype::rdfs_literal().clone())
    }

    #[test]
    fn helper_ranges_do_not_disable_negation_subsumption() {
        // The exact shapes that reach the live witness node: the real positive +
        // negated ranges PLUS the value-non-constraining helper ranges. The
        // helpers (rdfs:Literal / internal:defdata#) must NOT disable the check.
        let int = format!("{XSD}integer");
        let string = format!("{XSD}string");

        // Reproducer 1 (numeric, FACETED positive + faceted negated, + helper):
        // integer[≥0] ⊓ ¬integer[≥-5] ⊓ internal:defdata#0 -> EMPTY. Every
        // non-negative integer is ≥ -5, so ¬integer[≥-5] removes all of it. The
        // numeric lattice must still fire despite the helper range.
        assert!(conj(vec![
            defdata_placeholder(),
            faceted(&int, &[("minInclusive", "0")]),
            neg_faceted(&int, &[("minInclusive", "-5")]),
        ]));
        // Same with rdfs:Literal instead of the defdata placeholder.
        assert!(conj(vec![
            rdfs_literal(),
            faceted(&int, &[("minInclusive", "0")]),
            neg_faceted(&int, &[("minInclusive", "-5")]),
        ]));

        // Reproducer 2 (string, FACETED positive + facet-free negated, + helper):
        // string[minLength 3] ⊓ ¬string ⊓ internal:defdata#0 -> EMPTY. The
        // faceted positive's BASE is xsd:string, which ⊆ the negated bare string.
        assert!(conj(vec![
            defdata_placeholder(),
            faceted(&string, &[("minLength", "3")]),
            neg_dtype(string.clone()),
        ]));

        // The value-space view (the cross-node assignment pass) agrees: empty.
        for ranges in [
            vec![
                (defdata_placeholder(), ()),
                (faceted(&int, &[("minInclusive", "0")]), ()),
                (neg_faceted(&int, &[("minInclusive", "-5")]), ()),
            ],
            vec![
                (defdata_placeholder(), ()),
                (faceted(&string, &[("minLength", "3")]), ()),
                (neg_dtype(string.clone()), ()),
            ],
        ] {
            assert!(matches!(
                node_value_space(None, &ranges),
                NodeValueSpace::Finite { count: 0, .. }
            ));
        }
    }

    #[test]
    fn faceted_positive_subsumed_by_facetfree_negation_is_empty() {
        // A FACETED positive whose base value space ⊆ a facet-free negated base.
        // string[minLength 3] ⊓ ¬string -> EMPTY (base xsd:string ⊆ xsd:string).
        let string = format!("{XSD}string");
        assert!(conj(vec![
            faceted(&string, &[("minLength", "3")]),
            neg_dtype(string.clone()),
        ]));
        // integer[≥0] ⊓ ¬integer -> EMPTY (base xsd:integer ⊆ xsd:integer).
        let int = format!("{XSD}integer");
        assert!(conj(vec![
            faceted(&int, &[("minInclusive", "0")]),
            neg_dtype(int.clone()),
        ]));
        // integer[≥0] ⊓ ¬decimal -> EMPTY (base xsd:integer ⊆ xsd:decimal).
        assert!(conj(vec![
            faceted(&int, &[("minInclusive", "0")]),
            neg_dtype(format!("{XSD}decimal")),
        ]));
        // Faceted boolean is degenerate, but a faceted-or-bare X ⊓ ¬X over the
        // same base is empty: anyURI[minLength 1] ⊓ ¬anyURI -> EMPTY.
        let anyuri = format!("{XSD}anyURI");
        assert!(conj(vec![
            faceted(&anyuri, &[("minLength", "1")]),
            neg_dtype(anyuri.clone()),
        ]));

        // CONTRAST (must stay CONSISTENT): the faceted positive's base is NOT a
        // subset of the negated base. string[minLength 3] ⊓ ¬integer -> non-empty.
        assert!(!conj(vec![
            faceted(&string, &[("minLength", "3")]),
            neg_dtype(int.clone()),
        ]));
        // decimal[≥0] ⊓ ¬integer -> non-empty (decimal ⊄ integer): 0.5 survives.
        assert!(!conj(vec![
            faceted(&format!("{XSD}decimal"), &[("minInclusive", "0")]),
            neg_dtype(int.clone()),
        ]));
    }

    #[test]
    fn value_space_subset_lattice() {
        use ValueSpaceClass::*;
        // owl:real lattice ordering.
        assert!(value_space_is_subset(&Numeric(0), &Numeric(1))); // integer ⊆ decimal
        assert!(value_space_is_subset(&Numeric(1), &Numeric(3))); // decimal ⊆ real
        assert!(!value_space_is_subset(&Numeric(1), &Numeric(0))); // decimal ⊄ integer
        // Bounded integer windows.
        assert!(value_space_is_subset(
            &IntegerBounded(Some(0), Some(255)),
            &Numeric(0)
        )); // unsignedByte ⊆ integer
        assert!(value_space_is_subset(
            &IntegerBounded(Some(0), Some(127)),
            &IntegerBounded(Some(0), None)
        )); // byte-ish ⊆ nonNegativeInteger
        assert!(!value_space_is_subset(
            &IntegerBounded(Some(0), None),
            &IntegerBounded(Some(0), Some(255))
        )); // nonNegativeInteger ⊄ unsignedByte
        // Disjoint kinds.
        assert!(!value_space_is_subset(&Float, &Numeric(3)));
        assert!(!value_space_is_subset(&Numeric(0), &StringType(1))); // numeric ⊄ xsd:string
        assert!(value_space_is_subset(&StringType(1), &StringType(1))); // xsd:string ⊆ xsd:string
        // String hierarchy: mirrors Java s_datatypeSupersets (RDFPlainLiteralDatatypeHandler:51-69).
        assert!(value_space_is_subset(&StringType(4), &StringType(1))); // Name ⊆ string
        assert!(value_space_is_subset(&StringType(5), &StringType(4))); // NCName ⊆ Name
        assert!(value_space_is_subset(&StringType(6), &StringType(3))); // NMTOKEN ⊆ token
        assert!(!value_space_is_subset(&StringType(1), &StringType(4))); // string ⊄ Name
        assert!(!value_space_is_subset(&StringType(0), &StringType(1))); // PlainLiteral ⊄ string
        assert!(!value_space_is_subset(&StringType(6), &StringType(4))); // NMTOKEN ⊄ Name
    }

    // ----- rdf:XMLLiteral C14N value equality. -----

    #[test]
    fn xml_literal_c14n_equality() {
        let xml = |l: &str| Constant::create(l, format!("{RDF}XMLLiteral"));
        let eq = |a: &str, b: &str| {
            values_equal(&parse_value(&xml(a)).unwrap(), &parse_value(&xml(b)).unwrap())
        };
        // Self-closing vs paired empty element: equal after C14N.
        assert!(eq("<a/>", "<a></a>"));
        // Attribute ordering is canonicalized: equal regardless of source order.
        assert!(eq("<e a=\"1\" b=\"2\"/>", "<e b=\"2\" a=\"1\"></e>"));
        // Attribute quote style (single vs double) is canonicalized.
        assert!(eq("<e a='1'></e>", "<e a=\"1\"></e>"));
        // Intra-tag whitespace is normalized.
        assert!(eq("<e   a=\"1\"  ></e>", "<e a=\"1\"></e>"));
        // Predefined entity vs literal character in text: &amp; == the canonical
        // escaping of '&' (round-trips to the same canonical text).
        assert!(eq("<a>x&amp;y</a>", "<a>x&#38;y</a>"));
        // Genuinely different content is NOT equal.
        assert!(!eq("<a>x</a>", "<a>y</a>"));
        assert!(!eq("<e a=\"1\"/>", "<e a=\"2\"/>"));
    }

    // ----- Completeness: facet-restricted negation subsumption,
    //       huge-interval-with-exclusions cardinality, single-instant dateTime. -

    /// A faceted numeric datatype restriction `uri[facets...]`.
    fn faceted(uri: &str, facets: &[(&str, &str)]) -> LiteralDataRange {
        let facet_uris: Vec<String> = facets.iter().map(|(f, _)| format!("{XSD}{f}")).collect();
        let values: Vec<Constant> =
            facets.iter().map(|(_, l)| Constant::create(*l, uri.to_string())).collect();
        LiteralDataRange::DatatypeRestriction(crate::model::DatatypeRestriction::create(
            uri.to_string(),
            facet_uris,
            values,
        ))
    }
    /// The negation `¬(uri[facets...])` of a faceted datatype restriction.
    fn neg_faceted(uri: &str, facets: &[(&str, &str)]) -> LiteralDataRange {
        let LiteralDataRange::DatatypeRestriction(dr) = faceted(uri, facets) else {
            unreachable!()
        };
        dr.get_negation()
    }

    #[test]
    fn facet_restricted_negation_subsumption_is_empty() {
        // Item 1. `∃p.(integer[≥0] ⊓ ¬integer[≥-5])`: every non-negative integer
        // is ≥ -5, so it is excluded by ¬integer[≥-5] -> the positive value space
        // is a subset of the negated one -> EMPTY -> INCONSISTENT. The positive
        // side is infinite, so the old facet-free-only test missed it.
        let int = format!("{XSD}integer");
        assert!(conj(vec![
            faceted(&int, &[("minInclusive", "0")]),
            neg_faceted(&int, &[("minInclusive", "-5")]),
        ]));
        // The value-space view agrees: empty (count 0), not Infinite.
        assert!(matches!(
            node_value_space(
                None,
                &[
                    (faceted(&int, &[("minInclusive", "0")]), ()),
                    (neg_faceted(&int, &[("minInclusive", "-5")]), ()),
                ],
            ),
            NodeValueSpace::Finite { count: 0, .. }
        ));

        // `integer[1..10] ⊓ ¬integer[0..20]` -> [1..10] ⊆ [0..20] -> EMPTY.
        assert!(conj(vec![
            faceted(&int, &[("minInclusive", "1"), ("maxInclusive", "10")]),
            neg_faceted(&int, &[("minInclusive", "0"), ("maxInclusive", "20")]),
        ]));

        // Negating a wider real range deletes a bounded integer range:
        // `integer[0..10] ⊓ ¬decimal[-1..11]` -> EMPTY (every such integer is a
        // decimal in [-1, 11]).
        assert!(conj(vec![
            faceted(&int, &[("minInclusive", "0"), ("maxInclusive", "10")]),
            neg_faceted(&format!("{XSD}decimal"), &[("minInclusive", "-1"), ("maxInclusive", "11")]),
        ]));

        // CONTRAST (must stay CONSISTENT): the positive range pokes outside the
        // negated one. `integer[≥0] ⊓ ¬integer[1..10]`: 0, 11, 12, ... survive.
        assert!(!conj(vec![
            faceted(&int, &[("minInclusive", "0")]),
            neg_faceted(&int, &[("minInclusive", "1"), ("maxInclusive", "10")]),
        ]));
        // `integer[1..10] ⊓ ¬integer[2..20]`: the value 1 survives -> CONSISTENT.
        assert!(!conj(vec![
            faceted(&int, &[("minInclusive", "1"), ("maxInclusive", "10")]),
            neg_faceted(&int, &[("minInclusive", "2"), ("maxInclusive", "20")]),
        ]));
    }

    #[test]
    fn faceted_negated_string_length_subsumption_is_empty() {
        // Item 1 (faceted-NEGATED, outside the numeric lattice). The positive
        // faceted string range's length value space is a subset of a negated
        // faceted string range's length value space -> EMPTY -> INCONSISTENT.
        // Mirrors RDFPlainLiteralLengthValueSpaceSubset / the length branch of
        // RDFPlainLiteralDatatypeHandler.conjoinWithDR{,Negation}.
        let string = format!("{XSD}string");

        // REPRODUCER A: string[minLength 3] ⊓ ¬string[minLength 1] -> EMPTY.
        // Every string of length >= 3 has length >= 1, so it is removed.
        // (Old facet-free subsumption missed it: the negated side is faceted.)
        assert!(conj(vec![
            faceted(&string, &[("minLength", "3")]),
            neg_faceted(&string, &[("minLength", "1")]),
        ]));
        // REPRODUCER B: string[length 5] ⊓ ¬string[minLength 2] -> EMPTY.
        assert!(conj(vec![
            faceted(&string, &[("length", "5")]),
            neg_faceted(&string, &[("minLength", "2")]),
        ]));
        // string[minLength 4, maxLength 6] ⊓ ¬string[minLength 2, maxLength 8]
        // -> [4..6] ⊆ [2..8] -> EMPTY.
        assert!(conj(vec![
            faceted(&string, &[("minLength", "4"), ("maxLength", "6")]),
            neg_faceted(&string, &[("minLength", "2"), ("maxLength", "8")]),
        ]));

        // The value-space view (the cross-node assignment pass) agrees: empty.
        assert!(matches!(
            node_value_space(
                None,
                &[
                    (faceted(&string, &[("minLength", "3")]), ()),
                    (neg_faceted(&string, &[("minLength", "1")]), ()),
                ],
            ),
            NodeValueSpace::Finite { count: 0, .. }
        ));

        // CONTRAST (must stay CONSISTENT): the positive lengths poke outside the
        // negated window. string[minLength 3] ⊓ ¬string[minLength 5]: lengths 3,4
        // survive -> NON-empty.
        assert!(!conj(vec![
            faceted(&string, &[("minLength", "3")]),
            neg_faceted(&string, &[("minLength", "5")]),
        ]));
        // string[length 5] ⊓ ¬string[maxLength 2]: length 5 is > 2 -> survives.
        assert!(!conj(vec![
            faceted(&string, &[("length", "5")]),
            neg_faceted(&string, &[("maxLength", "2")]),
        ]));
        // string[minLength 2, maxLength 8] ⊓ ¬string[minLength 4, maxLength 6]:
        // lengths 2,3,7,8 survive -> NON-empty (the negated window is interior).
        assert!(!conj(vec![
            faceted(&string, &[("minLength", "2"), ("maxLength", "8")]),
            neg_faceted(&string, &[("minLength", "4"), ("maxLength", "6")]),
        ]));

        // rdf:PlainLiteral keeps BOTH a PRESENT and an ABSENT length interval, so
        // a negated xsd:string (ABSENT only) does NOT empty it: the PRESENT (lang-
        // tagged) values survive -> CONSISTENT.
        let plain = format!("{RDF}PlainLiteral");
        assert!(!conj(vec![
            faceted(&plain, &[("minLength", "3")]),
            neg_faceted(&string, &[("minLength", "1")]),
        ]));
        // But ¬rdf:PlainLiteral[minLength 1] removes both modes of a positive
        // rdf:PlainLiteral[minLength 3] -> EMPTY.
        assert!(conj(vec![
            faceted(&plain, &[("minLength", "3")]),
            neg_faceted(&plain, &[("minLength", "1")]),
        ]));
    }

    #[test]
    fn huge_interval_with_exclusions_has_exact_cardinality() {
        // Item 2. A bounded integer interval too wide to enumerate
        // (> MAX_ENUMERATED_VALUES) that ALSO carries value-removing exclusions
        // still has an EXACT finite cardinality. Reduce a wide interval down to a
        // tiny exact size via a negated sub-interval, then over-fill it.
        let int = format!("{XSD}integer");
        // integer[0 .. 1_000_000] minus ¬integer[3 .. 1_000_000] leaves {0,1,2}:
        // exact cardinality 3 (not "Infinite"). The interval [0..1_000_000] is
        // far wider than the 4096 materialization cap.
        let ranges = [
            (faceted(&int, &[("minInclusive", "0"), ("maxInclusive", "1000000")]), ()),
            (neg_faceted(&int, &[("minInclusive", "3"), ("maxInclusive", "1000000")]), ()),
        ];
        assert!(matches!(
            node_value_space(None, &ranges),
            NodeValueSpace::Finite { count: 3, .. }
        ));
        // Pigeonhole: 4 mutually-distinct such nodes cannot fit in 3 values ->
        // INCONSISTENT; 3 fit exactly.
        let space = || node_value_space(None, &ranges);
        let four: Vec<NodeValueSpace> = (0..4).map(|_| space()).collect();
        assert!(component_is_unsatisfiable(&four.iter().collect::<Vec<_>>(), &clique(4), &no_specifics(4), &[]));
        let three: Vec<NodeValueSpace> = (0..3).map(|_| space()).collect();
        assert!(!component_is_unsatisfiable(&three.iter().collect::<Vec<_>>(), &clique(3), &no_specifics(3), &[]));

        // The same with a negated *enumeration* removing two points from a wide
        // range: integer[0 .. 1_000_000] minus ¬{0, 1_000_000} has exactly
        // 1_000_001 - 2 = 999_999 values (computed, not over-approximated).
        let int_dr = faceted(&int, &[("minInclusive", "0"), ("maxInclusive", "1000000")]);
        let with_neg_enum = node_value_space(
            None,
            &[(int_dr, ()), (neg_faceted_enum_excluding(&["0", "1000000"]), ())],
        );
        assert!(matches!(
            with_neg_enum,
            NodeValueSpace::Finite { count: 999_999, .. }
        ));
    }

    /// A negated integer enumeration `¬{members...}` (each member an xsd:integer).
    fn neg_faceted_enum_excluding(members: &[&str]) -> LiteralDataRange {
        use crate::model::{AtomicDataRange, ConstantEnumeration};
        let e = ConstantEnumeration::create(members.iter().map(|m| integer(m)).collect());
        LiteralDataRange::AtomicNegationDataRange(
            crate::model::AtomicNegationDataRange::create(AtomicDataRange::ConstantEnumeration(e)),
        )
    }

    #[test]
    fn single_instant_datetime_range_is_finite() {
        // Item 3. A collapsed (single-instant) dateTime range is FINITE, not
        // dense: only finitely many distinct literals map to one timeline point.
        // [t .. t] (inclusive, equal bounds) over xsd:dateTime keeps a WITH and a
        // WITHOUT timezone interval, each a single point. The exact cardinality is
        // computed via DateTimeInterval.subtractSizeFrom.
        let point = || {
            datetime_restriction(
                false,
                &[
                    ("minInclusive", "2020-06-15T12:30:00Z"),
                    ("maxInclusive", "2020-06-15T12:30:00Z"),
                ],
            )
        };
        // Not a "noon, not midnight" last-day instant: seconds==0 so the WITH-tz
        // last-day extras may apply; either way the count is finite and modest.
        let space = node_value_space(None, &[(point(), ())]);
        let count = match space {
            NodeValueSpace::Finite { count, .. } => count,
            NodeValueSpace::Infinite => panic!("single-instant dateTime must be finite, not Infinite"),
        };
        assert!(count > 0 && count < 4000, "expected a finite modest count, got {count}");

        // Pigeonhole: a min-cardinality (here modeled as `count+1` mutually
        // distinct nodes over the single-instant range) exceeding the finite size
        // is INCONSISTENT.
        let n = (count as usize) + 1;
        let spaces: Vec<NodeValueSpace> =
            (0..n).map(|_| node_value_space(None, &[(point(), ())])).collect();
        assert!(component_is_unsatisfiable(&spaces.iter().collect::<Vec<_>>(), &clique(n), &no_specifics(n), &[]));
        // Exactly `count` distinct nodes fit.
        let fit: Vec<NodeValueSpace> =
            (0..count as usize).map(|_| node_value_space(None, &[(point(), ())])).collect();
        assert!(!component_is_unsatisfiable(&fit.iter().collect::<Vec<_>>(), &clique(count as usize), &no_specifics(count as usize), &[]));

        // A MULTI-instant range stays dense/infinite (regression guard for the
        // must-stay-consistent direction).
        let span = datetime_restriction(
            false,
            &[
                ("minInclusive", "2020-01-01T00:00:00Z"),
                ("maxInclusive", "2020-12-31T00:00:00Z"),
            ],
        );
        assert!(matches!(
            node_value_space(None, &[(span, ())]),
            NodeValueSpace::Infinite
        ));
    }

    #[test]
    fn single_instant_datetime_cardinality_values() {
        // Exact counts from DateTimeInterval.subtractSizeFrom for the corner
        // cases. A noon instant (seconds==0, not midnight): WITHOUT_TIMEZONE = 1
        // (not last-day), WITH_TIMEZONE = 1681 base + last-day extras when
        // secondsAreZero. 12:30:00 -> minutesInDay = 12*60+30 = 750.
        let noon = datetime_millis("2020-06-15T12:30:00Z");
        assert_eq!(datetime_instant_cardinality(noon, false), 1);
        // minutesInDay = 750: in [0,840] (+1) AND 1440-840=600 <= 750 (+1). So
        // 1681 + 2 = 1683.
        assert_eq!(datetime_instant_cardinality(noon, true), 1683);

        // A midnight instant is a last-day instant: WITHOUT_TIMEZONE = 2.
        let midnight = datetime_millis("2020-06-15T00:00:00Z");
        assert_eq!(datetime_instant_cardinality(midnight, false), 2);
        // minutesInDay = 0 -> in [0,840] (+1) and 0 < 600 so not in [600,1440)
        // (+0) -> 1681 + 1 = 1682.
        assert_eq!(datetime_instant_cardinality(midnight, true), 1682);

        // An instant with non-zero seconds: no WITH-tz last-day extras.
        let odd = datetime_millis("2020-06-15T12:30:30Z");
        assert_eq!(datetime_instant_cardinality(odd, false), 1);
        assert_eq!(datetime_instant_cardinality(odd, true), 1681);
    }

    /// A dateTime constant.
    fn datetime_const(lexical: &str) -> Constant {
        Constant::create(lexical, format!("{XSD}dateTime"))
    }
    /// A negated dateTime enumeration `¬{members...}`.
    fn neg_datetime_enum(members: &[&str]) -> LiteralDataRange {
        use crate::model::{AtomicDataRange, ConstantEnumeration};
        let e = ConstantEnumeration::create(members.iter().map(|m| datetime_const(m)).collect());
        LiteralDataRange::AtomicNegationDataRange(
            crate::model::AtomicNegationDataRange::create(AtomicDataRange::ConstantEnumeration(e)),
        )
    }

    #[test]
    fn single_instant_datetime_with_exclusions_has_exact_cardinality() {
        // Item 2. A collapsed (single-instant) dateTime range that ALSO carries
        // value-removing exclusions has its instant cardinality reduced by the
        // number of distinct excluded literals mapping to that instant (within the
        // timezone-present/absent variants), mirroring DateTimeValueSpaceSubset /
        // DateTimeInterval.subtractSizeFrom over the post-conjoinWithDRNegation
        // intervals.
        //
        // A noon, odd-seconds instant: WITH_TIMEZONE = 1681, WITHOUT_TIMEZONE
        // empty (the tz-present bounds collapse the tz-less interval).
        let point = || {
            datetime_restriction(
                false,
                &[
                    ("minInclusive", "2020-06-15T12:30:30Z"),
                    ("maxInclusive", "2020-06-15T12:30:30Z"),
                ],
            )
        };
        // Sanity: the exclusion-free count is exactly 1681.
        assert!(matches!(
            node_value_space(None, &[(point(), ())]),
            NodeValueSpace::Finite { count: 1681, .. }
        ));

        // Excluding ONE distinct tz-present literal that maps to this instant
        // (a different lexical form, +00:00, of the same UTC instant) drops the
        // count to 1680 (exact, not the 1681 upper bound).
        let with_one_exclusion = node_value_space(
            None,
            &[
                (point(), ()),
                (neg_datetime_enum(&["2020-06-15T12:30:30+00:00"]), ()),
            ],
        );
        assert!(
            matches!(with_one_exclusion, NodeValueSpace::Finite { count: 1680, .. }),
            "expected 1680 after one exclusion, got {:?}",
            match with_one_exclusion {
                NodeValueSpace::Finite { count, .. } => count,
                NodeValueSpace::Infinite => u128::MAX,
            }
        );

        // Excluding TWO distinct tz-present literals at this instant -> 1679.
        // (Different timezone offsets denote distinct values at the same instant;
        // our model conservatively counts distinct (seconds,has_tz) points, so two
        // genuinely-distinct literals at the same instant collapse to one removal —
        // sound-leaning. Here the two members ARE distinct in our model only if
        // they differ in seconds/has_tz; we instead exclude one tz-present and one
        // tz-LESS literal so each removes from a different variant... but
        // WITHOUT_TIMEZONE is empty here, so the tz-less one removes nothing.)
        let with_two = node_value_space(
            None,
            &[
                (point(), ()),
                // The +00:00 form removes the WITH-tz value; the tz-less form maps
                // to the (empty) WITHOUT-tz variant, removing nothing.
                (neg_datetime_enum(&["2020-06-15T12:30:30+00:00", "2020-06-15T12:30:30"]), ()),
            ],
        );
        assert!(matches!(with_two, NodeValueSpace::Finite { count: 1680, .. }));

        // Pigeonhole: with the single exclusion the value space holds exactly 1680
        // distinct values, so 1681 mutually-distinct nodes cannot fit ->
        // INCONSISTENT; 1680 fit. (This is the clash the exclusion-free upper
        // bound of 1681 would have MISSED.)
        let ranges = [
            (point(), ()),
            (neg_datetime_enum(&["2020-06-15T12:30:30+00:00"]), ()),
        ];
        let space = || node_value_space(None, &ranges);
        let over: Vec<NodeValueSpace> = (0..1681).map(|_| space()).collect();
        assert!(component_is_unsatisfiable(&over.iter().collect::<Vec<_>>(), &clique(1681), &no_specifics(1681), &[]));
        let fit: Vec<NodeValueSpace> = (0..1680).map(|_| space()).collect();
        assert!(!component_is_unsatisfiable(&fit.iter().collect::<Vec<_>>(), &clique(1680), &no_specifics(1680), &[]));

        // CONTRAST (must stay sound — no false clash): excluding a literal that
        // does NOT map to this instant removes nothing; the count stays 1681.
        let unrelated = node_value_space(
            None,
            &[
                (point(), ()),
                (neg_datetime_enum(&["2020-06-15T12:30:31Z"]), ()),
            ],
        );
        assert!(matches!(unrelated, NodeValueSpace::Finite { count: 1681, .. }));
    }

    #[test]
    fn single_instant_datetime_exhausting_exclusion_is_empty() {
        // A WITHOUT_TIMEZONE-only single instant with a single value, exhausted by
        // an exclusion, collapses to cardinality 0 (a genuine clash for >=1).
        // Build a tz-LESS single-instant range so only the WITHOUT_TIMEZONE
        // interval survives (an odd-seconds, non-midnight instant -> count 1).
        let tzless_point = datetime_restriction(
            false,
            &[
                ("minInclusive", "2020-06-15T12:30:30"),
                ("maxInclusive", "2020-06-15T12:30:30"),
            ],
        );
        // The tz-less variant has exactly one value (not midnight); the tz-present
        // variant is widened+collapsed to empty by the tz-less bounds.
        assert!(matches!(
            node_value_space(None, &[(tzless_point.clone(), ())]),
            NodeValueSpace::Finite { count: 1, .. }
        ));
        // Excluding that one tz-less literal empties it.
        assert!(matches!(
            node_value_space(
                None,
                &[
                    (tzless_point, ()),
                    (neg_datetime_enum(&["2020-06-15T12:30:30"]), ()),
                ],
            ),
            NodeValueSpace::Finite { count: 0, .. }
        ));
    }

    /// The UTC-normalized instant (exact integer milliseconds) of a dateTime
    /// lexical form.
    fn datetime_millis(lexical: &str) -> i64 {
        match parse_value(&Constant::create(lexical, format!("{XSD}dateTime"))).unwrap() {
            DataValue::DateTime { millis, .. } => millis,
            _ => unreachable!(),
        }
    }
}

/// A finite upper bound on the number of distinct values in a data range's
/// value space, or `None` when it is infinite or cannot be determined. Used to
/// detect unsatisfiable cardinalities over small datatypes (e.g. `≥3 r.boolean`,
/// since `xsd:boolean` has only two values).
pub(crate) fn value_space_size(range: &LiteralDataRange) -> Option<u128> {
    match range {
        LiteralDataRange::ConstantEnumeration(enumeration) => {
            // The number of distinct (value-space) members.
            let mut values: Vec<DataValue> = Vec::new();
            for i in 0..enumeration.number_of_constants() {
                match parse_value(enumeration.constant(i)) {
                    Some(value) => {
                        if !values.iter().any(|v| values_equal(v, &value)) {
                            values.push(value);
                        }
                    }
                    None => return None, // an unparseable member -> cannot decide
                }
            }
            Some(values.len() as u128)
        }
        LiteralDataRange::DatatypeRestriction(restriction) => {
            let uri = restriction.datatype_uri();
            if is_boolean_datatype(uri) && restriction.number_of_facet_restrictions() == 0 {
                Some(2)
            } else if let Some((base_min, base_max)) = integer_datatype_bounds(uri) {
                // A bounded integer interval (from the datatype's implicit bounds
                // tightened by min/max facets) has a finite number of values.
                let (mut low, mut high) = (base_min, base_max);
                for i in 0..restriction.number_of_facet_restrictions() {
                    let value: i128 = restriction.facet_value(i).lexical_form().trim().parse().ok()?;
                    match restriction.facet_uri(i).strip_prefix(XSD)? {
                        "minInclusive" => low = Some(low.map_or(value, |l| l.max(value))),
                        "minExclusive" => {
                            let v = value + 1;
                            low = Some(low.map_or(v, |l| l.max(v)));
                        }
                        "maxInclusive" => high = Some(high.map_or(value, |h| h.min(value))),
                        "maxExclusive" => {
                            let v = value - 1;
                            high = Some(high.map_or(v, |h| h.min(v)));
                        }
                        _ => return None, // a non-range facet -> cannot size
                    }
                }
                match (low, high) {
                    (Some(low), Some(high)) => {
                        Some(if high >= low { (high - low + 1) as u128 } else { 0 })
                    }
                    _ => None, // still unbounded
                }
            } else if is_hex_binary_datatype(uri) || is_base64_datatype(uri) {
                // Mirror BinaryDataLengthInterval.subtractSizeFrom / getNumberOfValuesOfLength.
                // If maxLength is unbounded or either bound >=7, the count exceeds long -> None.
                let mut min_len: u64 = 0;
                let mut max_len: Option<u64> = None;
                for i in 0..restriction.number_of_facet_restrictions() {
                    let b: u64 = restriction.facet_value(i).lexical_form().trim().parse().ok()?;
                    match restriction.facet_uri(i).strip_prefix(XSD)? {
                        "minLength" => min_len = min_len.max(b),
                        "maxLength" => max_len = Some(max_len.map_or(b, |m| m.min(b))),
                        "length" => { min_len = min_len.max(b); max_len = Some(max_len.map_or(b, |m| m.min(b))); }
                        _ => return None,
                    }
                }
                let max_len = max_len?; // unbounded -> None
                if min_len > max_len { return Some(0); } // empty interval
                if min_len >= 7 || max_len >= 7 { return None; } // count overflows long
                // getNumberOfValuesOfLength(L) = 1 + 256 + 256^2 + ... + 256^L
                let values_up_to = |l: i64| -> u128 {
                    if l < 0 { return 0; }
                    let mut total: u128 = 1;
                    let mut term: u128 = 1;
                    for _ in 1..=l { term *= 256; total += term; }
                    total
                };
                let size = values_up_to(max_len as i64) - values_up_to(min_len as i64 - 1);
                Some(size)
            } else if is_string_datatype(uri) && uri != format!("{RDF}PlainLiteral") {
                // Mirror RDFPlainLiteralLengthInterval.subtractSizeFrom for
                // xsd:string (ABSENT mode only; rdf:PlainLiteral has PRESENT
                // mode language-tagged strings which are infinite).
                // Java: max < 4 guard; unbounded max ⇒ None (infinite).
                let mut min_len: u64 = 0;
                let mut max_len: Option<u64> = None;
                for i in 0..restriction.number_of_facet_restrictions() {
                    let b: u64 = restriction.facet_value(i).lexical_form().trim().parse().ok()?;
                    match restriction.facet_uri(i).strip_prefix(XSD)? {
                        "minLength" => min_len = min_len.max(b),
                        "maxLength" => max_len = Some(max_len.map_or(b, |m| m.min(b))),
                        "length" => { min_len = min_len.max(b); max_len = Some(max_len.map_or(b, |m| m.min(b))); }
                        _ => return None, // pattern or other non-length facet
                    }
                }
                let iv = LengthInterval::try_new(LangTagMode::Absent, min_len, max_len)?;
                iv.size_of()
            } else {
                None
            }
        }
        // rdfs:Literal / internal datatypes and negations are (co-)infinite.
        LiteralDataRange::InternalDatatype(_) | LiteralDataRange::AtomicNegationDataRange(_) => None,
    }
}

fn label_as_literal_data_range(label: &TableauObject) -> Option<LiteralDataRange> {
    use crate::model::DLPredicate;
    match label {
        TableauObject::DLPredicate(DLPredicate::DatatypeRestriction(r)) => {
            Some(LiteralDataRange::DatatypeRestriction(r.clone()))
        }
        TableauObject::DLPredicate(DLPredicate::ConstantEnumeration(r)) => {
            Some(LiteralDataRange::ConstantEnumeration(r.clone()))
        }
        TableauObject::DLPredicate(DLPredicate::InternalDatatype(r)) => {
            Some(LiteralDataRange::InternalDatatype(r.clone()))
        }
        TableauObject::DLPredicate(DLPredicate::AtomicNegationDataRange(r)) => {
            Some(LiteralDataRange::AtomicNegationDataRange(r.clone()))
        }
        _ => None,
    }
}

