// The shared lexical->value datatype parser, the single Rust analogue of Java
// HermiT's `DatatypeRegistry.parseLiteral` (and the per-datatype handlers'
// `parseLiteral`). It owns the canonical parsed-value type [`DataValue`], the
// lexical-form parser [`parse_value`], and the
// [`is_supported_datatype`]/[`is_supported_facet`] predicates.
//
// This module is a leaf: it depends only on `std` and the bignum crates, never
// on `model` or `tableau`, so both `crate::model::term` (for
// `Constant::data_value`/`create_checked`) and `crate::tableau::datatype_manager`
// (for the value-space reasoning) can share ONE parser instead of each keeping a
// copy. The variants and lexical semantics are exactly those the datatype
// reasoning relies on (the authoritative, richer version: exact `BigInt`
// numerics, IEEE float specials, `xsd:dateTime` instants, `rdf:XMLLiteral`
// well-formedness/canonicalization, the binary/anyURI value spaces with their
// length facets, and the string subtypes).
#![allow(dead_code)]

use num_bigint::BigInt;
use num_integer::Integer as _;
use num_traits::{One, Signed, Zero};

const XSD: &str = "http://www.w3.org/2001/XMLSchema#";
const OWL: &str = "http://www.w3.org/2002/07/owl#";
const RDF: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";

/// A parsed data value, sufficient for the common OWL 2 datatypes.
#[derive(Clone, Debug, PartialEq)]
pub enum DataValue {
    /// An `owl:real` integer value. Unbounded (`num_bigint::BigInt`), mirroring
    /// HermiT's `Numbers.parseInteger` which yields a `BigInteger` once the value
    /// overflows `long`: a 40-digit `xsd:integer` literal must NOT be
    /// declared ill-typed.
    Integer(BigInt),
    /// A non-integer `owl:real` value (`xsd:decimal` / `owl:rational`), as an
    /// exact reduced fraction (`den > 0`), so that e.g. `1/3^^owl:rational`
    /// and `0.3333333333333333^^xsd:decimal` stay distinct. The components are
    /// unbounded (`BigInt`) so an arbitrarily long decimal/rational literal
    /// is kept exact rather than overflowing (HermiT uses `BigDecimal` /
    /// `BigRational`).
    Decimal { num: BigInt, den: BigInt },
    /// An `xsd:float` value, by its IEEE-754 bits (NaN canonicalized). Per
    /// OWL 2 / XSD 1.1 the float value space is a set of distinct objects
    /// *disjoint* from `owl:real` and `xsd:double`: `+0.0` and `-0.0` are two
    /// different values, NaN is a single value equal to itself, and
    /// `"1.0"^^xsd:float` is *not* the same value as `"1.0"^^xsd:decimal`.
    Float(u32),
    /// An `xsd:double` value, by its IEEE-754 bits (NaN canonicalized).
    Double(u64),
    Boolean(bool),
    Text(String),
    /// An `rdf:PlainLiteral` value with a non-empty language tag, mirroring
    /// HermiT's `RDFPlainLiteralDataValue(string, languageTag)`: a value
    /// *distinct* from the bare `string` (and from any `xsd:string`), so
    /// `"a@en"^^rdf:PlainLiteral` ≠ `"a"^^xsd:string`. The length facet counts
    /// only the `string` part (see `RDFPlainLiteralDatatypeHandler.parseLiteral`).
    LangString { string: String, lang: String },
    /// An instant on the timeline, held as an EXACT integer count of
    /// MILLISECONDS since the Unix epoch (UTC), plus whether the lexical form
    /// carried a timezone (datetimes with and without a timezone are never
    /// comparable, per XSD). This mirrors Java `DateTime.m_timeOnTimeline`, a
    /// `long` in milliseconds: using an integer (rather than `f64` seconds)
    /// keeps the instant exact even at extreme years, where sub-second fractions
    /// would otherwise be lost to floating-point rounding. Mirroring Java
    /// `DateTime.equals`, the value identity is three fields: the instant on the
    /// timeline, the `last_day` flag (true when the lexical hour was exactly 24
    /// at the end-of-day instant, so `...T24:00:00` is a distinct value from the
    /// equal-instant `...T00:00:00` of the next day), and the timezone offset in
    /// minutes (so `...Z` is a distinct value from `...+01:00` even at the same
    /// instant). `tz_offset` is only meaningful when `has_tz`; it is held at `0`
    /// otherwise (mirroring Java's fixed `NO_TIMEZONE` sentinel, which keeps
    /// tz-less values equal).
    DateTime { millis: i64, has_tz: bool, last_day: bool, tz_offset: i32 },
    /// A datatype with its own value space disjoint from the others
    /// (`xsd:anyURI`, `xsd:hexBinary`, `xsd:base64Binary`, `rdf:XMLLiteral`):
    /// compared by canonical form, with a value-space `length` for the length
    /// facets (octets for the binary types, UTF-16 code units for `anyURI`).
    /// `rdf:XMLLiteral` is registered as its own disjoint kind with no
    /// length (it admits no facets).
    Typed { kind: &'static str, canonical: String, length: usize },
}

pub fn is_integer_datatype(uri: &str) -> bool {
    integer_datatype_bounds(uri).is_some()
}

/// Whether `uri` names an OWL 2 datatype the reasoner supports (has a handler for).
/// The analogue of HermiT's `DatatypeRegistry.isDatatypeURI` /
/// `validateDatatypeRestriction` succeeding: a datatype outside this set is
/// unsupported and (unless defined via `DatatypeDefinition` or ignored) makes the
/// ontology rejected, as HermiT throws `UnsupportedDatatypeException`.
pub fn is_supported_datatype(uri: &str) -> bool {
    is_integer_datatype(uri)
        || is_decimal_datatype(uri)
        || is_float_datatype(uri)
        || is_rational_datatype(uri)
        || is_real_datatype(uri)
        || is_boolean_datatype(uri)
        || is_string_datatype(uri)
        || is_datetime_datatype(uri)
        || is_anyuri_datatype(uri)
        || is_hex_binary_datatype(uri)
        || is_base64_datatype(uri)
        || is_xml_literal_datatype(uri)
}

/// `rdf:XMLLiteral`. Java registers `XMLLiteralDatatypeHandler`: its value
/// space is infinite and disjoint from every other datatype, it admits no
/// facets, and a malformed XML lexical form is ill-typed.
pub fn is_xml_literal_datatype(uri: &str) -> bool {
    uri == format!("{RDF}XMLLiteral")
}

/// Whether `facet_uri` is a facet that the handler for `datatype_uri` supports,
/// mirroring each Java handler's `validateDatatypeRestriction` (which throws
/// `UnsupportedFacetException` for any facet outside its fixed supported set).
/// Per the handlers:
///   * owl:real-derived numerics and xsd:dateTime/dateTimeStamp: only the four
///     ordering facets (min/maxInclusive, min/maxExclusive);
///   * binary datatypes: only length/minLength/maxLength;
///   * xsd:anyURI: length facets + xsd:pattern;
///   * rdf:PlainLiteral / xsd:string subtypes: length facets + xsd:pattern +
///     rdf:langRange;
///   * rdf:XMLLiteral and xsd:boolean: no facets at all.
/// `totalDigits`/`fractionDigits`/`whiteSpace` are supported by NO handler.
pub fn is_supported_facet(datatype_uri: &str, facet_uri: &str) -> bool {
    let ordering = |f: &str| {
        matches!(
            f,
            "minInclusive" | "maxInclusive" | "minExclusive" | "maxExclusive"
        )
    };
    let length = |f: &str| matches!(f, "length" | "minLength" | "maxLength");
    if is_integer_datatype(datatype_uri)
        || is_decimal_datatype(datatype_uri)
        || is_float_datatype(datatype_uri)
        || is_rational_datatype(datatype_uri)
        || is_real_datatype(datatype_uri)
        || is_datetime_datatype(datatype_uri)
    {
        // OWLRealDatatypeHandler / FloatDatatypeHandler / DoubleDatatypeHandler /
        // DateTimeDatatypeHandler: only the four ordering facets.
        return facet_uri.strip_prefix(XSD).is_some_and(ordering);
    }
    if is_hex_binary_datatype(datatype_uri) || is_base64_datatype(datatype_uri) {
        // BinaryDataDatatypeHandler: only the length facets.
        return facet_uri.strip_prefix(XSD).is_some_and(length);
    }
    if is_anyuri_datatype(datatype_uri) {
        // AnyURIDatatypeHandler: length facets and xsd:pattern.
        return facet_uri
            .strip_prefix(XSD)
            .is_some_and(|f| length(f) || f == "pattern");
    }
    if is_string_datatype(datatype_uri) {
        // RDFPlainLiteralDatatypeHandler manages xsd:string (+ subtypes) and
        // rdf:PlainLiteral: length facets, xsd:pattern, and rdf:langRange.
        if facet_uri == format!("{RDF}langRange") {
            return true;
        }
        return facet_uri
            .strip_prefix(XSD)
            .is_some_and(|f| length(f) || f == "pattern");
    }
    if is_boolean_datatype(datatype_uri) || is_xml_literal_datatype(datatype_uri) {
        // BooleanDatatypeHandler / XMLLiteralDatatypeHandler: no facets at all.
        return false;
    }
    // Unknown datatype: not judged here (handled by is_supported_datatype).
    true
}
/// The implicit value-space bounds of a derived integer datatype, as
/// `(min, max)` (either side `None` when unbounded). Returns `None` for a
/// non-integer datatype.
pub fn integer_datatype_bounds(uri: &str) -> Option<(Option<i128>, Option<i128>)> {
    let name = uri.strip_prefix(XSD)?;
    let bounds = match name {
        "integer" => (None, None),
        "nonNegativeInteger" => (Some(0), None),
        "positiveInteger" => (Some(1), None),
        "nonPositiveInteger" => (None, Some(0)),
        "negativeInteger" => (None, Some(-1)),
        "long" => (Some(i64::MIN as i128), Some(i64::MAX as i128)),
        "int" => (Some(i32::MIN as i128), Some(i32::MAX as i128)),
        "short" => (Some(i16::MIN as i128), Some(i16::MAX as i128)),
        "byte" => (Some(i8::MIN as i128), Some(i8::MAX as i128)),
        "unsignedLong" => (Some(0), Some(u64::MAX as i128)),
        "unsignedInt" => (Some(0), Some(u32::MAX as i128)),
        "unsignedShort" => (Some(0), Some(u16::MAX as i128)),
        "unsignedByte" => (Some(0), Some(u8::MAX as i128)),
        _ => return None,
    };
    Some(bounds)
}

pub fn is_decimal_datatype(uri: &str) -> bool {
    uri.strip_prefix(XSD) == Some("decimal")
}
/// The IEEE floating-point datatypes, which (unlike `xsd:decimal`) admit the
/// special values `NaN`, `INF` and `-INF`.
pub fn is_float_datatype(uri: &str) -> bool {
    matches!(uri.strip_prefix(XSD), Some("double" | "float"))
}
pub fn is_xsd_float(uri: &str) -> bool {
    uri.strip_prefix(XSD) == Some("float")
}
pub fn is_xsd_double(uri: &str) -> bool {
    uri.strip_prefix(XSD) == Some("double")
}
/// `owl:rational` (lexical `a/b`); a subset of the reals.
pub fn is_rational_datatype(uri: &str) -> bool {
    uri == format!("{OWL}rational")
}
/// `owl:real`, the supertype of all OWL 2 numeric value spaces. It has no
/// literals of its own, so it appears only as a membership target.
pub fn is_real_datatype(uri: &str) -> bool {
    uri == format!("{OWL}real")
}
pub fn is_string_datatype(uri: &str) -> bool {
    matches!(
        uri.strip_prefix(XSD),
        Some(
            "string"
                | "normalizedString"
                | "token"
                | "language"
                | "Name"
                | "NCName"
                | "NMTOKEN"
        )
    ) || uri == format!("{RDF}PlainLiteral")
}
pub fn is_boolean_datatype(uri: &str) -> bool {
    uri == format!("{XSD}boolean")
}
pub fn is_datetime_datatype(uri: &str) -> bool {
    // HermiT registers only xsd:dateTime and xsd:dateTimeStamp; xsd:date (and the
    // other date/time fragments) raise UnsupportedDatatypeException, so they are
    // intentionally NOT recognized here.
    matches!(uri.strip_prefix(XSD), Some("dateTime" | "dateTimeStamp"))
}
pub fn is_anyuri_datatype(uri: &str) -> bool {
    uri.strip_prefix(XSD) == Some("anyURI")
}

/// XML 1.0 (5th ed.) `NameStartChar`, exactly the dk.brics `Datatypes.get("Name2")`/
/// `Datatypes.get("NCName")` start ranges Java HermiT uses (NOT Rust's broader
/// `char::is_alphabetic`, which would over-accept exotic letters/letter-like symbols
/// that the XML grammar excludes). The colon (0x3A) is a NameStartChar only when
/// `allow_colon` (Name accepts it, NCName does not).
pub fn is_name_start_char(c: char, allow_colon: bool) -> bool {
    let u = c as u32;
    (allow_colon && u == 0x3A)
        || matches!(u,
            0x41..=0x5A
            | 0x5F
            | 0x61..=0x7A
            | 0xC0..=0xD6
            | 0xD8..=0xF6
            | 0xF8..=0x2FF
            | 0x370..=0x37D
            | 0x37F..=0x1FFF
            | 0x200C..=0x200D
            | 0x2070..=0x218F
            | 0x2C00..=0x2FEF
            | 0x3001..=0xD7FF
            | 0xF900..=0xFDCF
            | 0xFDF0..=0xFFFD
            | 0x10000..=0xEFFFF)
}
/// XML 1.0 (5th ed.) `NameChar` = `NameStartChar | '-' | '.' | [0-9] | #xB7 |
/// [#x0300-#x036F] | [#x203F-#x2040]`, the dk.brics `Datatypes.get("Name2")`/
/// `NCName` continuation ranges (NOT Rust's broader `is_numeric`/`is_alphabetic`).
pub fn is_name_char(c: char, allow_colon: bool) -> bool {
    let u = c as u32;
    is_name_start_char(c, allow_colon)
        || matches!(u,
            0x2D..=0x2E // '-' '.'
            | 0x30..=0x39 // digits
            | 0xB7
            | 0x300..=0x36F
            | 0x203F..=0x2040)
}
pub fn is_valid_xml_name(s: &str, allow_colon: bool) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(first) if is_name_start_char(first, allow_colon) => {
            chars.all(|c| is_name_char(c, allow_colon))
        }
        _ => false,
    }
}
pub fn is_valid_nmtoken(s: &str) -> bool {
    !s.is_empty() && s.chars().all(|c| is_name_char(c, true))
}
/// Returns `true` iff every character is in the brics `normalizedString` automaton:
/// `[ - -퟿-�]*` (Java ref: normalizedStringAutomaton()).
/// In particular all C0 controls (0x00-0x1F, including tab/LF/CR) and C1 controls
/// (0x80-0x9F) are rejected, as are the non-character code points 0xFFFE-0xFFFF.
pub fn is_valid_normalized_string(s: &str) -> bool {
    s.chars().all(|c| {
        // Java normalizedStringAutomaton: [ - -퟿-�]*
        let u = c as u32;
        (0x0020..=0x007F).contains(&u)
            || (0x00A0..=0xD7FF).contains(&u)
            || (0xE000..=0xFFFD).contains(&u)
    })
}
/// Returns `true` iff `c` is in the brics `tokenAutomaton` word character set
/// `[!-퟿-�]` i.e. `[!-퟿-�]`
/// (RDFPlainLiteralPatternValueSpaceSubset.java:94-96). This set is independent
/// of normalizedString's character set: it INCLUDES the C1 controls 0x80-0x9F
/// (which normalizedString excludes) and excludes only U+0020 and below plus the
/// surrogate/noncharacter ranges.
fn is_token_char(c: char) -> bool {
    let u = c as u32;
    (0x0021..=0xD7FF).contains(&u) || (0xE000..=0xFFFD).contains(&u)
}
/// Returns `true` iff `s` is in the brics `tokenAutomaton`:
/// `([!-퟿-�]+( [!-퟿-�]+)*)?` — either empty, or one or more
/// non-space "words" of token characters separated by single U+0020 spaces.
/// (RDFPlainLiteralPatternValueSpaceSubset.java:94-96.)
pub fn is_valid_token(s: &str) -> bool {
    if s.is_empty() {
        return true;
    }
    if s.starts_with(' ') || s.ends_with(' ') || s.contains("  ") {
        return false;
    }
    s.chars().all(|c| c == ' ' || is_token_char(c))
}
pub fn is_valid_language(s: &str) -> bool {
    let mut parts = s.split('-');
    match parts.next() {
        Some(first)
            if (1..=8).contains(&first.len())
                && first.bytes().all(|b| b.is_ascii_alphabetic()) => {}
        _ => return false,
    }
    parts.all(|p| (1..=8).contains(&p.len()) && p.bytes().all(|b| b.is_ascii_alphanumeric()))
}
/// Validates an rdf:PlainLiteral language subtag against the full BCP47
/// `languageTagAutomaton` (RDFPlainLiteralPatternValueSpaceSubset.java:70-87),
/// which is stricter than the XSD `language` lexical pattern. Structure (each
/// subtag separated by '-'):
///
/// ```text
/// ( ([a-zA-Z]{2,3} ((-[a-zA-Z]{3}){0,3})?) | [a-zA-Z]{4} | [a-zA-Z]{5,8} )  // language
/// (-[a-zA-Z]{4})?                              // script
/// (-([a-zA-Z]{2}|[0-9]{3}))?                   // region
/// (-([a-zA-Z0-9]{5,8}|([0-9][a-z0-9]{3})))*    // variant
/// (-([a-wy-zA-WY-Z0-9](-[a-zA-Z0-9]{2,8})+))*  // extension
/// (-x(-[a-zA-Z0-9]{1,8})+)?                    // privateuse
/// ```
pub fn is_valid_language_bcp47(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    // The automaton has no trailing wildcard; an empty subtag (leading/trailing
    // '-' or "--") makes the whole match fail, mirroring brics.
    let subtags: Vec<&str> = s.split('-').collect();
    if subtags.iter().any(|t| t.is_empty()) {
        return false;
    }
    let is_alpha = |t: &str| t.bytes().all(|b| b.is_ascii_alphabetic());
    let is_digit = |t: &str| t.bytes().all(|b| b.is_ascii_digit());
    let is_alnum = |t: &str| t.bytes().all(|b| b.is_ascii_alphanumeric());

    let mut i = 0usize;
    let n = subtags.len();

    // language: primary subtag.
    let first = subtags[i];
    let flen = first.len();
    if !is_alpha(first) {
        return false;
    }
    if flen == 2 || flen == 3 {
        i += 1;
        // optional extlang: up to three "-[a-zA-Z]{3}" subtags.
        let mut ext = 0;
        while ext < 3 && i < n && subtags[i].len() == 3 && is_alpha(subtags[i]) {
            // An extlang subtag is exactly 3 alpha; but a 3-alpha subtag here
            // could also be a script (4) — no, script is 4. A region of 2 alpha
            // or 3 digit, or variant (5-8 / digit+3) cannot be 3 alpha. So a
            // 3-alpha following the primary is unambiguously extlang.
            i += 1;
            ext += 1;
        }
    } else if flen == 4 {
        i += 1;
    } else if (5..=8).contains(&flen) {
        i += 1;
    } else {
        return false;
    }

    // script: optional "-[a-zA-Z]{4}".
    if i < n && subtags[i].len() == 4 && is_alpha(subtags[i]) {
        i += 1;
    }

    // region: optional "-([a-zA-Z]{2}|[0-9]{3})".
    if i < n
        && ((subtags[i].len() == 2 && is_alpha(subtags[i]))
            || (subtags[i].len() == 3 && is_digit(subtags[i])))
    {
        i += 1;
    }

    // variant: zero or more "-([a-zA-Z0-9]{5,8}|([0-9][a-z0-9]{3}))".
    loop {
        if i >= n {
            break;
        }
        let t = subtags[i];
        let is_variant_long = (5..=8).contains(&t.len()) && is_alnum(t);
        let is_variant_dig4 = t.len() == 4
            && t.as_bytes()[0].is_ascii_digit()
            && t.bytes().all(|b| b.is_ascii_digit() || b.is_ascii_lowercase());
        if is_variant_long || is_variant_dig4 {
            i += 1;
        } else {
            break;
        }
    }

    // extension: zero or more "-([a-wy-zA-WY-Z0-9](-[a-zA-Z0-9]{2,8})+)".
    loop {
        if i >= n {
            break;
        }
        let singleton = subtags[i];
        // singleton: exactly one char in [a-wy-zA-WY-Z0-9] (excludes x/X).
        if singleton.len() != 1 {
            break;
        }
        let c = singleton.as_bytes()[0];
        let is_singleton = (c.is_ascii_alphanumeric()) && c != b'x' && c != b'X';
        if !is_singleton {
            break;
        }
        // Must be followed by one or more "-[a-zA-Z0-9]{2,8}".
        let mut j = i + 1;
        let mut count = 0;
        while j < n && (2..=8).contains(&subtags[j].len()) && is_alnum(subtags[j]) {
            j += 1;
            count += 1;
        }
        if count == 0 {
            return false;
        }
        i = j;
    }

    // privateuse: optional "-x(-[a-zA-Z0-9]{1,8})+".
    if i < n {
        let s0 = subtags[i];
        if s0.len() == 1 && (s0.as_bytes()[0] == b'x' || s0.as_bytes()[0] == b'X') {
            let mut j = i + 1;
            let mut count = 0;
            while j < n && (1..=8).contains(&subtags[j].len()) && is_alnum(subtags[j]) {
                j += 1;
                count += 1;
            }
            if count == 0 {
                return false;
            }
            i = j;
        }
    }

    i == n
}
/// Whether `c` is an XML 1.0 Char: `#x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD]`.
/// Used by `xsd:string` validation (Java ref: s_xsdString = Datatypes.get("string"),
/// which is the brics XML-Char automaton; see also xmlChar() in
/// RDFPlainLiteralPatternValueSpaceSubset.java:88-90).
/// Surrogates (0xD800-0xDFFF) cannot appear in Rust `char`, so no explicit check
/// is needed. Code points above 0xFFFF are allowed (supplementary chars in UTF-16
/// are valid XML Char pairs, and Rust represents them as single scalar values).
fn is_xml_char(c: char) -> bool {
    matches!(c, '\u{9}' | '\u{A}' | '\u{D}')
        || (0x20u32..=0xD7FF).contains(&(c as u32))
        || (0xE000u32..=0xFFFD).contains(&(c as u32))
        || c as u32 > 0xFFFF
}
/// Whether a recognized string subtype's lexical form is valid.
/// `rdf:PlainLiteral` and the bare string (no explicit datatype) accept any character data;
/// `xsd:string` and its subtypes restrict to XML Char and further sub-ranges.
pub fn string_lexical_valid(datatype: &str, lexical: &str) -> bool {
    match datatype.strip_prefix(XSD) {
        // xsd:string: every character must be an XML 1.0 Char (Java: s_xsdString.run()).
        Some("string") => lexical.chars().all(is_xml_char),
        Some("normalizedString") => is_valid_normalized_string(lexical),
        Some("token") => is_valid_token(lexical),
        Some("language") => is_valid_language(lexical),
        Some("Name") => is_valid_xml_name(lexical, true),
        Some("NCName") => is_valid_xml_name(lexical, false),
        Some("NMTOKEN") => is_valid_nmtoken(lexical),
        _ => true,
    }
}
/// Faithful validation for `xsd:anyURI`, matching HermiT's `AnyURIDatatypeHandler.
/// parseLiteral`, which accepts a lexical form iff BOTH gates pass:
///   1. `AnyURIValueSpaceSubset.s_anyURI.run(lexicalForm)` — the dk.brics
///      `Datatypes.get("URI")` grammar automaton (the RFC 2396 *absolute or relative
///      URI-reference* production); and
///   2. `new java.net.URI(lexicalForm)` — the `java.net.URI` RFC 2396 structural
///      parse (scheme / authority(userinfo@host:port) / path / query / fragment, with
///      correct percent-encoding and per-component character sets).
/// We reject what *either* gate rejects: `any_uri_structural` is the `java.net.URI`
/// parse, `any_uri_grammar` is the brics URI-reference grammar; both must accept.
pub fn is_valid_any_uri(s: &str) -> bool {
    any_uri_structural(s) && any_uri_grammar(s)
}

// ---- `java.net.URI` (RFC 2396) structural parse ---------------------------------

/// Does `ch` belong to RFC 2396 `unreserved` = `alphanum | mark`?
fn uri_is_unreserved(ch: char) -> bool {
    ch.is_ascii_alphanumeric()
        || matches!(ch, '-' | '_' | '.' | '!' | '~' | '*' | '\'' | '(' | ')')
}

/// The "other" category `java.net.URI` permits unescaped: any character above
/// `0x80`. The JDK `URI.Parser` defines `other` (in its static char-mask init) as
/// every character `> 0x80` that is neither a space character
/// (`Character.isSpaceChar`) nor an ISO control character (`Character.isISOControl`).
/// Everything else above ASCII (letters, digits, symbols, emoji, CJK, …) is allowed
/// verbatim — so this is much broader than letter-or-digit.
fn uri_is_other(ch: char) -> bool {
    let c = ch as u32;
    c > 0x80 && !char_is_space_char(ch) && !char_is_iso_control(ch)
}

/// Java `Character.isISOControl`: U+0000–U+001F or U+007F–U+009F.
fn char_is_iso_control(ch: char) -> bool {
    let c = ch as u32;
    c <= 0x1F || (0x7F..=0x9F).contains(&c)
}

/// Java `Character.isSpaceChar`: a Unicode space/line/paragraph separator (general
/// categories Zs, Zl, Zp). Enumerated for the code points at or above ASCII space.
fn char_is_space_char(ch: char) -> bool {
    matches!(ch as u32,
        0x20 | 0xA0 | 0x1680
        | 0x2000..=0x200A
        | 0x2028 | 0x2029 | 0x202F | 0x205F | 0x3000)
}

/// RFC 2396 `pchar` extras (besides unreserved/escaped/other): `:@&=+$,`.
fn uri_is_pchar_extra(ch: char) -> bool {
    matches!(ch, ':' | '@' | '&' | '=' | '+' | '$' | ',')
}

/// RFC 2396 `uric` extras for query/fragment (reserved + unreserved): the reserved
/// set is `;/?:@&=+$,[]`.
fn uri_is_uric_extra(ch: char) -> bool {
    matches!(ch, ';' | '/' | '?' | ':' | '@' | '&' | '=' | '+' | '$' | ',' | '[' | ']')
}

/// Scan a percent-escape at `b[i]` (which must be `%`): `%` HEX HEX. Returns the
/// new index past the escape, or `None` if malformed (RFC 2396 §2.4.1).
fn uri_scan_escape(b: &[u8], i: usize) -> Option<usize> {
    if i + 2 < b.len() && b[i + 1].is_ascii_hexdigit() && b[i + 2].is_ascii_hexdigit() {
        Some(i + 3)
    } else {
        None
    }
}

/// Check every char of `s` is allowed by `pred`, an escape, or an "other" char.
fn uri_chars_ok(s: &str, pred: impl Fn(char) -> bool) -> bool {
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if c == b'%' {
            match uri_scan_escape(b, i) {
                Some(n) => { i = n; continue; }
                None => return false,
            }
        }
        if c < 0x80 {
            let ch = c as char;
            if !(uri_is_unreserved(ch) || pred(ch)) {
                return false;
            }
            i += 1;
        } else {
            // Decode the UTF-8 char to test the "other" category.
            let ch = s[i..].chars().next().unwrap();
            if !uri_is_other(ch) {
                return false;
            }
            i += ch.len_utf8();
        }
    }
    true
}

/// A faithful (RFC 2396) `java.net.URI` structural parse. Returns `true` iff
/// `new java.net.URI(s)` would *not* throw `URISyntaxException`.
fn any_uri_structural(s: &str) -> bool {
    // java.net.URI rejects raw ASCII control chars and space everywhere up front.
    if s.chars().any(|c| (c as u32) < 0x20 || c == ' ' || c == 0x7f as char) {
        return false;
    }
    // Split off the fragment at the first '#'. A second '#' is illegal because '#'
    // is not in `uric`, so the fragment (uric*) check below will reject it.
    let (before_frag, fragment) = match s.find('#') {
        Some(p) => (&s[..p], Some(&s[p + 1..])),
        None => (s, None),
    };
    if let Some(frag) = fragment {
        if !uri_chars_ok(frag, uri_is_uric_extra) {
            return false;
        }
    }
    // Detect a scheme: a ':' that comes before any '/', '?' and whose prefix is a
    // valid scheme name (`alpha *(alpha | digit | '+' | '-' | '.')`).
    let hier = if let Some(colon) = before_frag.find(':') {
        let scheme = &before_frag[..colon];
        let before_colon_special = before_frag[..colon]
            .find(['/', '?'])
            .is_none();
        if before_colon_special && uri_is_scheme(scheme) {
            // Absolute URI: scheme ':' (hier-part | opaque-part).
            let ssp = &before_frag[colon + 1..];
            // Opaque part: ssp does NOT start with '/'. java.net.URI treats it as
            // opaque and validates it as uric (no leading '/').
            if !ssp.starts_with('/') {
                return uri_opaque_ok(ssp);
            }
            ssp
        } else {
            before_frag
        }
    } else {
        before_frag
    };
    // hier-part = ( net-path | abs-path | rel-path ) [ '?' query ]
    any_uri_hier_part(hier)
}

/// RFC 2396 scheme = `alpha *( alpha | digit | "+" | "-" | "." )`.
fn uri_is_scheme(s: &str) -> bool {
    let mut it = s.chars();
    match it.next() {
        Some(c) if c.is_ascii_alphabetic() => {}
        _ => return false,
    }
    it.all(|c| c.is_ascii_alphanumeric() || matches!(c, '+' | '-' | '.'))
}

/// RFC 2396 opaque-part = uric-no-slash *uric (validated leniently as uric* here
/// since the leading-slash distinction was already made by the caller).
fn uri_opaque_ok(ssp: &str) -> bool {
    !ssp.is_empty() && uri_chars_ok(ssp, uri_is_uric_extra)
}

/// hier-part: an optional `//authority`, a path, and an optional `?query`.
fn any_uri_hier_part(hier: &str) -> bool {
    let (path_and_authority, query) = match hier.find('?') {
        Some(p) => (&hier[..p], Some(&hier[p + 1..])),
        None => (hier, None),
    };
    if let Some(q) = query {
        if !uri_chars_ok(q, uri_is_uric_extra) {
            return false;
        }
    }
    if let Some(rest) = path_and_authority.strip_prefix("//") {
        // net-path = "//" authority [ abs-path ]
        let (authority, path) = match rest.find(['/', '?']) {
            Some(p) => (&rest[..p], &rest[p..]),
            None => (rest, ""),
        };
        if !any_uri_authority(authority) {
            return false;
        }
        // The abs-path must start with '/' (guaranteed by the split) or be empty.
        any_uri_path(path)
    } else {
        any_uri_path(path_and_authority)
    }
}

/// RFC 2396 path = `*( pchar | ';' | '/' )` (segments with params). We validate the
/// whole path as the union of pchar plus the path separators `/` and `;`.
fn any_uri_path(path: &str) -> bool {
    uri_chars_ok(path, |ch| uri_is_pchar_extra(ch) || matches!(ch, '/' | ';'))
}

/// RFC 2396 authority = `[ userinfo "@" ] host [ ":" port ]`. java.net.URI also
/// accepts a registry-based authority (reg_name). We validate the common
/// server-based form and fall back to reg_name for anything else.
fn any_uri_authority(authority: &str) -> bool {
    if authority.is_empty() {
        // An empty authority ("//") is accepted by java.net.URI.
        return true;
    }
    let (userinfo, hostport) = match authority.rfind('@') {
        Some(p) => (Some(&authority[..p]), &authority[p + 1..]),
        None => (None, authority),
    };
    if let Some(ui) = userinfo {
        // userinfo = *( unreserved | escaped | ";:&=+$," )
        if !uri_chars_ok(ui, |ch| matches!(ch, ';' | ':' | '&' | '=' | '+' | '$' | ',')) {
            return false;
        }
    }
    // host [ ":" port ]: split a trailing :port (but not inside an IPv6 "[...]").
    let (host, port) = if hostport.starts_with('[') {
        match hostport.find(']') {
            Some(rb) => {
                let host = &hostport[..=rb];
                let after = &hostport[rb + 1..];
                if let Some(p) = after.strip_prefix(':') {
                    (host, Some(p))
                } else if after.is_empty() {
                    (host, None)
                } else {
                    return false; // junk after the IPv6 literal
                }
            }
            None => return false, // unterminated IPv6 literal
        }
    } else {
        match hostport.rfind(':') {
            Some(p) => (&hostport[..p], Some(&hostport[p + 1..])),
            None => (hostport, None),
        }
    };
    if let Some(port) = port {
        // port = *digit (java.net.URI also accepts an empty port).
        if !port.chars().all(|c| c.is_ascii_digit()) {
            return false;
        }
    }
    any_uri_host(host)
}

/// RFC 2396 host = IPv4address | IPv6reference | hostname (reg-name-ish). We accept
/// an IPv6 reference `[...]` containing hex/`:`/`.`, and otherwise a reg-name made of
/// unreserved/escaped/"other"/`$,;:&=+`.
fn any_uri_host(host: &str) -> bool {
    if host.is_empty() {
        return true;
    }
    if let Some(inner) = host.strip_prefix('[') {
        let inner = match inner.strip_suffix(']') {
            Some(x) => x,
            None => return false,
        };
        // IPv6 / IPvFuture reference: hexdigits, ':', '.', and (IPvFuture) 'v'/letters.
        return !inner.is_empty()
            && inner.chars().all(|c| c.is_ascii_hexdigit() || matches!(c, ':' | '.' | 'v' | 'V'));
    }
    // reg-name / hostname: unreserved | escaped | other | one of "$,;:&=+".
    uri_chars_ok(host, |ch| matches!(ch, '$' | ',' | ';' | ':' | '&' | '=' | '+'))
}

// ---- dk.brics `Datatypes.get("URI")` grammar gate -------------------------------

/// The brics URI-reference grammar gate (`AnyURIValueSpaceSubset.s_anyURI.run`).
/// The dk.brics `URI` automaton recognizes the RFC 2396 *URI-reference* production:
/// `[ absoluteURI | relativeURI ] [ "#" fragment ]`. In practice the grammar's
/// character-level constraints are a (slightly stricter) superset-check of what the
/// `java.net.URI` parse already enforces, with one extra rule the structural parse
/// does not impose on its own: the alphabet is exactly `unreserved | escaped |
/// reserved | "#"`, so any ASCII char outside that set is rejected, and a `%` not
/// followed by two hex digits is rejected. We implement that alphabet/escape check
/// here; the per-component structure is checked by `any_uri_structural`.
fn any_uri_grammar(s: &str) -> bool {
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if c == b'%' {
            match uri_scan_escape(b, i) {
                Some(n) => { i = n; continue; }
                None => return false,
            }
        }
        if c < 0x80 {
            let ch = c as char;
            // unreserved | reserved | '#'
            let ok = uri_is_unreserved(ch)
                || matches!(ch, ';' | '/' | '?' | ':' | '@' | '&' | '=' | '+' | '$' | ',' | '[' | ']' | '#');
            if !ok {
                return false;
            }
            i += 1;
        } else {
            let ch = s[i..].chars().next().unwrap();
            if !uri_is_other(ch) {
                return false;
            }
            i += ch.len_utf8();
        }
    }
    true
}
/// Parse an `xsd:double`/`xsd:float` special-value lexical form the way
/// `Double.parseDouble`/`Float.parseFloat` do (accept `Infinity`/`-Infinity`/
/// `+Infinity`/`NaN`), plus HermiT's `INF`/`-INF`. Returns `Some(true/false/...)`
/// classification via the closure the caller applies; here it normalizes the
/// special spellings to a canonical token, or `None` to fall through to a numeric
/// parse. Rejects `+INF` and the lowercase spellings, as Java does.
pub fn float_special(t: &str) -> Option<FloatSpecial> {
    match t {
        "INF" | "Infinity" | "+Infinity" => Some(FloatSpecial::PosInf),
        "-INF" | "-Infinity" => Some(FloatSpecial::NegInf),
        "NaN" => Some(FloatSpecial::Nan),
        _ => None,
    }
}
pub enum FloatSpecial {
    PosInf,
    NegInf,
    Nan,
}
/// Strip a single trailing `f`/`F`/`d`/`D` type suffix, the way Java's
/// `Float.parseFloat`/`Double.parseDouble` tolerate one (e.g. `"1.0f"`,
/// `"1.0D"`). Only removed when the remainder is non-empty so a bare `"f"`/`"d"`
/// still fails the subsequent numeric parse, matching Java.
pub fn strip_float_suffix(t: &str) -> &str {
    if t.len() > 1 && matches!(t.as_bytes()[t.len() - 1], b'f' | b'F' | b'd' | b'D') {
        &t[..t.len() - 1]
    } else {
        t
    }
}
pub fn is_hex_binary_datatype(uri: &str) -> bool {
    uri.strip_prefix(XSD) == Some("hexBinary")
}
pub fn is_base64_datatype(uri: &str) -> bool {
    uri.strip_prefix(XSD) == Some("base64Binary")
}

/// Validates an `xsd:hexBinary` lexical form, returning `(canonical_uppercase,
/// octet_count)`. Invalid if it has an odd number of digits or a non-hex char.
pub fn parse_hex_binary(lexical: &str) -> Option<(String, usize)> {
    // BinaryData.parseHexBinary does not trim; whitespace is a non-hex char -> None.
    if lexical.len() % 2 != 0 || !lexical.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    Some((lexical.to_ascii_uppercase(), lexical.len() / 2))
}

/// Canonical base64 encoding of `bytes` (standard alphabet, `=` padding).
pub fn encode_base64(bytes: &[u8]) -> String {
    const T: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let b0 = chunk[0] as u32;
        let b1 = *chunk.get(1).unwrap_or(&0) as u32;
        let b2 = *chunk.get(2).unwrap_or(&0) as u32;
        let n = (b0 << 16) | (b1 << 8) | b2;
        out.push(T[(n >> 18 & 63) as usize] as char);
        out.push(T[(n >> 12 & 63) as usize] as char);
        out.push(if chunk.len() > 1 { T[(n >> 6 & 63) as usize] as char } else { '=' });
        out.push(if chunk.len() > 2 { T[(n & 63) as usize] as char } else { '=' });
    }
    out
}

/// Validates an `xsd:base64Binary` lexical form, returning `(canonical,
/// octet_count)`. Whitespace is ignored; the body must be the base64 alphabet
/// with 0--2 trailing `=` and a total length that is a multiple of four.
///
/// Java's `BinaryData.parseBase64Binary` constructs `new
/// BinaryData(BinaryDataType.HEX_BINARY, data)` (BinaryData.java:parseBase64Binary):
/// a parsed base64 value is tagged HEX_BINARY, so its canonical `toString()` is the
/// hex form of the decoded bytes and it is value-EQUAL to a hexBinary literal with
/// the same bytes (`BinaryData.equals` compares the byte[] and the binaryDataType).
/// The canonical form returned here is therefore the uppercase hex of the decoded
/// bytes, matching `parse_hex_binary`'s canonical, and the parse branch tags the
/// value with kind "hexBinary".
/// `Character.isWhitespace`: the Java whitespace set used by
/// `BinaryData.removeWhitespace` (space separators excluding the non-breaking
/// ones, the line/paragraph separators, and the ASCII control whitespace).
fn is_java_whitespace(c: char) -> bool {
    matches!(c,
        '\u{09}' | '\u{0A}' | '\u{0B}' | '\u{0C}' | '\u{0D}'
        | '\u{1C}' | '\u{1D}' | '\u{1E}' | '\u{1F}'
        | ' ' | '\u{1680}' | '\u{2000}'..='\u{2006}' | '\u{2008}'..='\u{200A}'
        | '\u{2028}' | '\u{2029}' | '\u{205F}' | '\u{3000}')
}

pub fn parse_base64_binary(lexical: &str) -> Option<(String, usize)> {
    // BinaryData.removeWhitespace: trim chars <= U+0020 from both ends, then drop
    // every interior Character.isWhitespace char.
    let trimmed = lexical.trim_matches(|c: char| c <= '\u{20}');
    let cleaned: String = trimmed.chars().filter(|&c| !is_java_whitespace(c)).collect();
    if cleaned.len() % 4 != 0 {
        return None;
    }
    if cleaned.is_empty() {
        return Some((String::new(), 0));
    }
    let pad = cleaned.bytes().rev().take_while(|&b| b == b'=').count();
    if pad > 2 {
        return None;
    }
    let body = &cleaned[..cleaned.len() - pad];
    let sextet = |b: u8| -> Option<u32> {
        match b {
            b'A'..=b'Z' => Some((b - b'A') as u32),
            b'a'..=b'z' => Some((b - b'a' + 26) as u32),
            b'0'..=b'9' => Some((b - b'0' + 52) as u32),
            b'+' => Some(62),
            b'/' => Some(63),
            _ => None,
        }
    };
    let mut bytes: Vec<u8> = Vec::new();
    let (mut acc, mut nbits) = (0u32, 0u32);
    for &b in body.as_bytes() {
        let v = sextet(b)?;
        acc = (acc << 6) | v;
        nbits += 6;
        if nbits >= 8 {
            nbits -= 8;
            bytes.push((acc >> nbits) as u8);
        }
    }
    let len = bytes.len();
    Some((encode_hex_upper(&bytes), len))
}

/// Uppercase hex encoding of `bytes`, matching `BinaryData.toHexBinary`
/// (BinaryData.java). Used as the canonical form for binary values tagged
/// HEX_BINARY (both hexBinary literals and, per Java, parsed base64 literals).
fn encode_hex_upper(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0xF) as usize] as char);
    }
    out
}

/// Maximum number of days in `month` of `year` (proleptic Gregorian).
/// Direct port of `DateTime.java:266-277` `daysInMonth(year, month)`.
fn days_in_month(year: i64, month: i64) -> i64 {
    if month == 2 {
        // DateTime.java:268: leap year iff divisible by 4, except centuries
        // unless also divisible by 400.
        if (year % 4) != 0 || ((year % 100) == 0 && (year % 400) != 0) {
            28
        } else {
            29
        }
    } else if month == 4 || month == 6 || month == 9 || month == 11 {
        30
    } else {
        31
    }
}

/// Days since the Unix epoch for a proleptic-Gregorian date (Howard Hinnant's
/// `days_from_civil`).
pub fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = (if y >= 0 { y } else { y - 399 }) / 400;
    let yoe = y - era * 400; // [0, 399]
    let mp = (m + 9) % 12; // Mar = 0 ... Feb = 11
    let doy = (153 * mp + 2) / 5 + d - 1; // [0, 365]
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy; // [0, 146096]
    era * 146097 + doe - 719468
}

/// Parses an `xsd:dateTime` / `xsd:date` lexical form into
/// `(instant_millis, has_timezone, last_day, tz_offset_minutes)`, where the
/// instant is an EXACT integer count of MILLISECONDS since the Unix epoch,
/// normalized to UTC. This mirrors Java `DateTime.getTimeOnTimelineRaw`, which
/// computes whole seconds and then `seconds*1000 + millisecond` as a `long`.
/// Returns `None` on anything it does not recognize, so a parse failure is
/// always treated as "undecided" (never a false clash). `has_time` distinguishes
/// `dateTime` (with a `T` time part) from `date`.
pub fn parse_datetime(lexical: &str, has_time: bool) -> Option<(i64, bool, bool, i32)> {
    // Java parses every numeric subfield with digit-only regex classes
    // (`[0-9]{...}`), so a leading `+`/`-` inside a subfield makes
    // `matcher.matches()` fail. Rust's `str::parse` would instead accept a
    // leading `+` (and the year sign), so each field is validated to be pure
    // ASCII digits before parsing. (The year carries its own single leading
    // `-`, handled separately below.)
    fn digits_only(field: &str) -> bool {
        !field.is_empty() && field.bytes().all(|b| b.is_ascii_digit())
    }
    let s = lexical.trim();
    let neg_year = s.starts_with('-');
    let mut rest = if neg_year { &s[1..] } else { s };

    let year_end = rest.find('-')?;
    if year_end < 4 {
        return None; // XSD requires at least four year digits
    }
    if !digits_only(&rest[..year_end]) {
        return None;
    }
    let year_abs: i64 = rest[..year_end].parse().ok()?;
    let year = if neg_year { -year_abs } else { year_abs };
    rest = &rest[year_end + 1..];

    if rest.len() < 3 || &rest[2..3] != "-" {
        return None;
    }
    if !digits_only(&rest[..2]) {
        return None;
    }
    let month: i64 = rest[..2].parse().ok()?;
    rest = &rest[3..];
    if rest.len() < 2 {
        return None;
    }
    if !digits_only(&rest[..2]) {
        return None;
    }
    let day: i64 = rest[..2].parse().ok()?;
    rest = &rest[2..];

    // Whole seconds and the millisecond part are kept as exact integers, exactly
    // like Java (which parses seconds and milliseconds separately and combines
    // them as `seconds*1000 + millisecond` in a `long`).
    let (mut hour, mut minute, mut second, mut millisecond) = (0i64, 0i64, 0i64, 0i64);
    if has_time {
        if !rest.starts_with('T') || rest.len() < 9 {
            return None;
        }
        rest = &rest[1..];
        if !digits_only(&rest[..2]) {
            return None;
        }
        hour = rest[..2].parse().ok()?;
        if &rest[2..3] != ":" {
            return None;
        }
        if !digits_only(&rest[3..5]) {
            return None;
        }
        minute = rest[3..5].parse().ok()?;
        if &rest[5..6] != ":" {
            return None;
        }
        rest = &rest[6..];
        // Whole seconds: exactly two digits (Java regex `([0-9]{2})`).
        if rest.len() < 2 || !digits_only(&rest[..2]) { return None; }
        second = rest[..2].parse().ok()?;
        rest = &rest[2..];
        // Optional fraction: '.' followed by 1..=3 digits ONLY (Java `[.]([0-9]{1,3})`).
        // A bare '.' or 4+ digits causes Java's matcher.matches() to return null.
        if let Some(after_dot) = rest.strip_prefix('.') {
            let frac_len = after_dot
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(after_dot.len());
            if frac_len == 0 || frac_len > 3 {
                return None;
            }
            // Java pads to exactly 3 digits and treats as integer milliseconds.
            let mut ms_str = after_dot[..frac_len].to_string();
            while ms_str.len() < 3 { ms_str.push('0'); }
            millisecond = ms_str.parse().ok()?;
            rest = &after_dot[frac_len..];
        }
    }

    if // DateTime.java:209: year must be within [-9999, 9999]
        year < -9999 || year > 9999
        || !(1..=12).contains(&month)
        // DateTime.java:211: day must not exceed the real number of days in that month/year
        || day < 1 || day > days_in_month(year, month)
        || hour > 24
        // DateTime.java:212: hour==24 is only valid as the exact end-of-day instant 24:00:00(.0)
        || (hour == 24 && (minute != 0 || second != 0 || millisecond != 0))
        || minute > 59
        || !(0..60).contains(&second) // Java DateTime.java:214: second>=60 => null (no leap seconds in XSD dateTime)
        || !(0..1000).contains(&millisecond)
    {
        return None;
    }

    let mut has_tz = false;
    // The timezone correction applied to the timeline instant, in MILLISECONDS
    // (Java subtracts `timeZoneOffset*60*1000` from the raw timeline value).
    let mut tz_offset_millis: i64 = 0;
    // The timezone offset in minutes (part of the value identity, mirroring
    // Java `DateTime.m_timeZoneOffset`); only meaningful when `has_tz`.
    let mut tz_offset_minutes: i32 = 0;
    if !rest.is_empty() {
        has_tz = true;
        if rest == "Z" {
            tz_offset_millis = 0;
            tz_offset_minutes = 0;
        } else {
            let (sign, sign_minutes) = match rest.as_bytes()[0] {
                b'+' => (1i64, 1i32),
                b'-' => (-1i64, -1i32),
                _ => return None,
            };
            let tz = &rest[1..];
            if tz.len() != 5 || &tz[2..3] != ":" {
                return None;
            }
            if !digits_only(&tz[..2]) || !digits_only(&tz[3..5]) {
                return None;
            }
            let th: u32 = tz[..2].parse().ok()?;
            let tm: u32 = tz[3..5].parse().ok()?;
            // DateTime.java:227-228: tz hour must be 0..=14; if 14, minutes must be 0; minutes must be 0..=59.
            if th > 14 || (th == 14 && tm != 0) || tm >= 60 {
                return None;
            }
            // Java DateTime.parse: timeZoneOffset = sign*(hour*60+minute) (minutes);
            // the timeline correction subtracts timeZoneOffset*60*1000 ms.
            tz_offset_minutes = sign_minutes * (th as i32 * 60 + tm as i32);
            tz_offset_millis = sign * (th as i64 * 3600 + tm as i64 * 60) * 1000;
        }
    }

    // DateTime.java:66: m_lastDayInstant is true exactly when the lexical hour was
    // 24 (at the validated end-of-day instant, minute/second/millisecond all 0).
    let last_day = hour == 24;

    // Exact integer milliseconds since the Unix epoch (UTC). Java computes whole
    // seconds first and then `*1000 + millisecond`; we mirror that exactly.
    let seconds = days_from_civil(year, month, day) * 86400
        + hour * 3600
        + minute * 60
        + second;
    let millis = seconds * 1000 + millisecond - tz_offset_millis;
    Some((millis, has_tz, last_day, tz_offset_minutes))
}

/// Parses `lexical_form` against `datatype_uri`, returning the parsed value or
/// `None` for a malformed / ill-typed literal (the analogue of Java
/// `DatatypeRegistry.parseLiteral` throwing `MalformedLiteralException`). An
/// unrecognized/opaque datatype yields `None` (it has no handler); callers that
/// must not fail on opaque datatypes test [`is_supported_datatype`] first.
pub fn parse_value(lexical_form: &str, datatype_uri: &str) -> Option<DataValue> {
    let lexical = lexical_form;
    let datatype = datatype_uri;
    if let Some((min, max)) = integer_datatype_bounds(datatype) {
        // Reject values outside the derived integer type's implicit value space
        // (e.g. -1 is not an xsd:nonNegativeInteger, 300 not an xsd:unsignedByte).
        // HermiT's Numbers.parseInteger falls back to BigInteger, so a
        // syntactically valid integer that overflows i128 must NOT be ill-typed.
        // `BigInt::parse` accepts only an optional sign + ASCII digits, matching
        // `new BigInteger(string)` (no '+' before Java 7? Java's BigInteger does
        // accept a leading '+'); we accept a leading '+' too. Numbers.parseInteger
        // does NOT trim, so surrounding whitespace makes the literal ill-typed.
        let parsed = parse_big_integer(lexical)?;
        if min.is_some_and(|m| parsed < BigInt::from(m))
            || max.is_some_and(|m| parsed > BigInt::from(m))
        {
            return None;
        }
        Some(DataValue::Integer(parsed))
    } else if is_decimal_datatype(datatype) {
        // xsd:decimal is kept exact. HermiT parses with `new BigDecimal(...)`, which
        // also accepts scientific (exponent) notation, e.g. "1E2". Numbers.parseDecimal
        // does NOT trim, so surrounding whitespace makes the literal ill-typed.
        let t = lexical;
        // Split off an optional exponent (e/E followed by a signed integer).
        let (mantissa, exp): (&str, i32) = match t.split_once(['e', 'E']) {
            Some((m, e)) => (m, e.parse::<i32>().ok()?),
            None => (t, 0),
        };
        if !mantissa
            .bytes()
            .all(|b| b.is_ascii_digit() || b == b'+' || b == b'-' || b == b'.')
        {
            return None;
        }
        let (negative, mantissa) = match mantissa.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, mantissa.strip_prefix('+').unwrap_or(mantissa)),
        };
        let (int_part, frac_part) = match mantissa.split_once('.') {
            Some((i, f)) => (i, f),
            None => (mantissa, ""),
        };
        if (int_part.is_empty() && frac_part.is_empty())
            || !int_part.bytes().all(|b| b.is_ascii_digit())
            || !frac_part.bytes().all(|b| b.is_ascii_digit())
        {
            return None;
        }
        // Build numerator/denominator as BigInt so an arbitrarily long
        // decimal literal stays exact (HermiT uses BigDecimal). The combined
        // digit string `int_part ++ frac_part` is the unscaled value; the
        // denominator is 10^(frac digits).
        let digits: String = format!("{int_part}{frac_part}");
        let mut num: BigInt = if digits.is_empty() {
            BigInt::zero()
        } else {
            digits.parse().ok()?
        };
        let ten = BigInt::from(10);
        let mut den: BigInt = BigInt::one();
        for _ in 0..frac_part.len() {
            den *= &ten;
        }
        // Apply the exponent exactly: positive scales the numerator, negative the
        // denominator (10^|exp|).
        for _ in 0..exp.max(0) {
            num *= &ten;
        }
        for _ in 0..(-exp).max(0) {
            den *= &ten;
        }
        if negative {
            num = -num;
        }
        Some(make_rational(num, den))
    } else if is_xsd_float(datatype) {
        // xsd:float admits the special values (canonical spellings). Values are
        // the IEEE bits: ±0 stay distinct, an out-of-range lexical rounds to
        // ±INF (XSD lexical mapping), NaN is canonicalized to one bit pattern.
        // FloatDatatypeHandler.parseLiteral: Float.parseFloat (which trims and
        // accepts "Infinity"/"NaN") is tried first; only on failure is the lexical
        // form matched EXACTLY (untrimmed) against "INF"/"-INF". So " INF " is
        // ill-typed while " Infinity " is not.
        let v: f32 = if lexical == "INF" {
            f32::INFINITY
        } else if lexical == "-INF" {
            f32::NEG_INFINITY
        } else {
            let t = lexical.trim();
            match t {
                "Infinity" | "+Infinity" => f32::INFINITY,
                "-Infinity" => f32::NEG_INFINITY,
                "NaN" => f32::NAN,
                // Java's Float.parseFloat accepts a trailing 'f'/'F'/'d'/'D' type
                // suffix (e.g. "1.0f"), so strip a single one before parsing.
                // It rounds an overflowing finite numeral to ±Infinity without
                // throwing; a real overflow numeral always has a digit, while
                // lenient spellings like "inf" do not.
                _ => match strip_float_suffix(t).parse::<f32>() {
                    Ok(v) if !v.is_nan() && (v.is_finite() || t.bytes().any(|b| b.is_ascii_digit())) => v,
                    _ => return None,
                },
            }
        };
        Some(DataValue::Float(if v.is_nan() { f32::NAN.to_bits() } else { v.to_bits() }))
    } else if is_xsd_double(datatype) {
        // As for xsd:float: Double.parseDouble (trims, accepts "Infinity"/"NaN")
        // is tried first; "INF"/"-INF" are matched only as an exact, untrimmed
        // fallback.
        let v: f64 = if lexical == "INF" {
            f64::INFINITY
        } else if lexical == "-INF" {
            f64::NEG_INFINITY
        } else {
            let t = lexical.trim();
            match t {
                "Infinity" | "+Infinity" => f64::INFINITY,
                "-Infinity" => f64::NEG_INFINITY,
                "NaN" => f64::NAN,
                // Java's Double.parseDouble accepts a trailing 'f'/'F'/'d'/'D'
                // type suffix (e.g. "1.0d"); strip a single one before parsing.
                // It rounds an overflowing finite numeral to ±Infinity without
                // throwing; a real overflow numeral always has a digit.
                _ => match strip_float_suffix(t).parse::<f64>() {
                    Ok(v) if !v.is_nan() && (v.is_finite() || t.bytes().any(|b| b.is_ascii_digit())) => v,
                    _ => return None,
                },
            }
        };
        Some(DataValue::Double(if v.is_nan() { f64::NAN.to_bits() } else { v.to_bits() }))
    } else if is_boolean_datatype(datatype) {
        // HermiT accepts "true"/"false" case-insensitively, but "1"/"0" exactly.
        let t = lexical.trim();
        if t.eq_ignore_ascii_case("true") || t == "1" {
            Some(DataValue::Boolean(true))
        } else if t.eq_ignore_ascii_case("false") || t == "0" {
            Some(DataValue::Boolean(false))
        } else {
            None
        }
    } else if is_rational_datatype(datatype) {
        // owl:rational lexical form is "numerator/denominator" over integers.
        // Numbers.parseRational parses both sides with BigInteger, so an
        // overflowing numerator/denominator stays exact. It does NOT trim; the only
        // leniency is stripping a single leading `+` on the whole string (so on the
        // numerator), so any surrounding whitespace makes the literal ill-typed.
        let t = lexical.strip_prefix('+').unwrap_or(lexical);
        let (num, den) = t.split_once('/')?;
        let num = parse_big_integer(num)?;
        let den = parse_big_integer(den)?;
        // HermiT requires a strictly positive denominator.
        if den <= BigInt::zero() {
            return None;
        }
        Some(make_rational(num, den))
    } else if is_datetime_datatype(datatype) {
        // Mirror DateTimeDatatypeHandler.parseLiteral: xsd:dateTimeStamp REQUIRES
        // a timezone offset (unlike xsd:dateTime), so a timezone-less
        // dateTimeStamp lexical form is malformed ⇒ ill-typed.
        let (millis, has_tz, last_day, tz_offset) = parse_datetime(lexical, true)?;
        if datatype.strip_prefix(XSD) == Some("dateTimeStamp") && !has_tz {
            return None;
        }
        Some(DataValue::DateTime { millis, has_tz, last_day, tz_offset })
    } else if is_anyuri_datatype(datatype) {
        if !is_valid_any_uri(lexical) {
            return None;
        }
        Some(DataValue::Typed {
            kind: "anyURI",
            canonical: lexical.to_string(),
            // HermiT counts UTF-16 code units (Java String.length()), not
            // Unicode code points, so an astral-plane character counts as 2.
            length: lexical.encode_utf16().count(),
        })
    } else if is_hex_binary_datatype(datatype) {
        parse_hex_binary(lexical).map(|(canonical, length)| DataValue::Typed {
            kind: "hexBinary",
            canonical,
            length,
        })
    } else if is_base64_datatype(datatype) {
        // Java BinaryData.parseBase64Binary tags the parsed value HEX_BINARY,
        // so a base64 literal is value-equal to a hexBinary literal with the same
        // decoded bytes and is NOT a member of the base64Binary value space
        // (BinaryDataLengthInterval.contains requires matching binaryDataType).
        parse_base64_binary(lexical).map(|(canonical, length)| DataValue::Typed {
            kind: "hexBinary",
            canonical,
            length,
        })
    } else if is_xml_literal_datatype(datatype) {
        // XMLLiteralDatatypeHandler.parseLiteral calls XMLLiteral.parse,
        // which throws (⇒ MalformedLiteralException ⇒ ill-typed) on a lexical
        // form that is not well-formed XML, and otherwise stores the EXCLUSIVE
        // XML-canonicalized form (Canonicalizer20010315ExclWithComments). Two
        // XMLLiteral constants are equal iff their canonical strings match. We
        // do not pull in a full C14N library; instead `canonicalize_xml_literal`
        // applies the canonicalization steps that decide value equality of
        // lexically-distinct-but-equal literals (attribute ordering and quoting,
        // self-closing vs paired empty tags, intra-tag whitespace, and
        // character/entity-reference expansion in text). See its doc-comment for
        // the residual gap vs full C14N.
        if !is_well_formed_xml(lexical) {
            return None;
        }
        Some(DataValue::Typed {
            kind: "XMLLiteral",
            canonical: canonicalize_xml_literal(lexical),
            length: 0,
        })
    } else if datatype == format!("{RDF}PlainLiteral") {
        // Mirror RDFPlainLiteralDatatypeHandler.parseLiteral: the lexical form of
        // an rdf:PlainLiteral MUST contain '@' (lastIndexOf('@')==-1 ⇒
        // MalformedLiteralException ⇒ ill-typed). It is split into "string@lang";
        // an empty language tag yields the bare string value (== xsd:string), a
        // non-empty one yields a distinct (string,lang) value.
        let last_at = lexical.rfind('@')?;
        let string = &lexical[..last_at];
        let lang = &lexical[last_at + 1..];
        // RDFPlainLiteralDatatypeHandler gates the string part through
        // s_xsdString (the XML Char automaton); a string containing a non-XML
        // character is ill-typed (MalformedLiteralException).
        if !string.chars().all(is_xml_char) {
            return None;
        }
        if lang.is_empty() {
            Some(DataValue::Text(string.to_string()))
        } else {
            // Mirror RDFPlainLiteralLengthInterval.contains(RDFPlainLiteralDataValue):95 —
            // s_languageTag.run(languageTag) rejects any tag that does not match the
            // full BCP47 languageTagAutomaton; return None (≡ MalformedLiteralException).
            if !is_valid_language_bcp47(lang) {
                return None;
            }
            Some(DataValue::LangString {
                string: string.to_string(),
                lang: lang.to_string(),
            })
        }
    } else if is_string_datatype(datatype) {
        // The string subtypes (normalizedString/token/Name/NCName/NMTOKEN/language)
        // constrain the lexical form; xsd:string accepts all.
        if !string_lexical_valid(datatype, lexical) {
            return None;
        }
        Some(DataValue::Text(lexical.to_string()))
    } else {
        None
    }
}

/// Builds the canonical (reduced, positive-denominator) rational `num/den`,
/// as an `Integer` when the denominator reduces to 1. Mirrors
/// `Numbers.parseRational` (reduce by gcd, normalize the sign onto the
/// numerator). Operates on `BigInt` so it never overflows.
pub fn make_rational(num: BigInt, den: BigInt) -> DataValue {
    let sign = if den.is_negative() {
        -BigInt::one()
    } else {
        BigInt::one()
    };
    let mut g = num.gcd(&den);
    if g.is_zero() {
        g = BigInt::one();
    }
    let num = &sign * &num / &g;
    let den = &sign * &den / &g;
    if den.is_one() {
        DataValue::Integer(num)
    } else {
        DataValue::Decimal { num, den }
    }
}

/// Parses a base-10 integer the way `new java.math.BigInteger(string)` does:
/// an optional leading `+`/`-` followed by one or more ASCII digits, with no
/// other characters. (`BigInt`'s own `FromStr` accepts the same grammar.)
pub fn parse_big_integer(s: &str) -> Option<BigInt> {
    if s.is_empty() {
        return None;
    }
    let digits = s.strip_prefix(['+', '-']).unwrap_or(s);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    s.parse::<BigInt>().ok()
}

/// A lightweight well-formedness check for an `rdf:XMLLiteral` lexical form.
/// HermiT delegates to `XMLLiteral.parse` (a full XML parser); we verify
/// the common well-formedness constraints without pulling in an XML
/// dependency: every `<...>` tag is closed, start/end tags nest and balance,
/// attribute quotes balance, and `<`/`&` only appear as part of markup/entity
/// references. This rejects the malformed forms HermiT rejects (unbalanced or
/// mismatched tags) while accepting well-formed fragments. Empty content is a
/// well-formed XML literal (a document with no elements is allowed here, as
/// HermiT treats the empty string as a valid XMLLiteral fragment).
pub fn is_well_formed_xml(s: &str) -> bool {
    // FIX D: a well-formed XML document/fragment contains only XML 1.0 Char
    // (Java's parser rejects any other code point — e.g. a raw NUL or a C0 control
    // other than tab/LF/CR — with a fatal error ⇒ MalformedLiteralException). We
    // reject such content up front so the Rust does not accept malformed XML Java
    // rejects. (Characters inside markup are a subset of this and are revalidated
    // structurally below.)
    if !s.chars().all(is_xml_char) {
        return false;
    }
    let bytes = s.as_bytes();
    let mut stack: Vec<String> = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'<' => {
                // Comment / CDATA / processing instruction / declaration.
                if s[i..].starts_with("<!--") {
                    match s[i + 4..].find("-->") {
                        Some(rel) => i += 4 + rel + 3,
                        None => return false,
                    }
                    continue;
                }
                if s[i..].starts_with("<![CDATA[") {
                    match s[i + 9..].find("]]>") {
                        Some(rel) => i += 9 + rel + 3,
                        None => return false,
                    }
                    continue;
                }
                if i + 1 < bytes.len() && (bytes[i + 1] == b'?' || bytes[i + 1] == b'!') {
                    match s[i..].find('>') {
                        Some(rel) => i += rel + 1,
                        None => return false,
                    }
                    continue;
                }
                // Find the matching '>' (skipping quoted attribute values).
                let mut j = i + 1;
                let mut quote: Option<u8> = None;
                while j < bytes.len() {
                    let c = bytes[j];
                    match quote {
                        Some(q) if c == q => quote = None,
                        Some(_) => {}
                        None if c == b'"' || c == b'\'' => quote = Some(c),
                        None if c == b'>' => break,
                        None if c == b'<' => return false, // '<' not allowed inside a tag
                        None => {}
                    }
                    j += 1;
                }
                if j >= bytes.len() || quote.is_some() {
                    return false; // unterminated tag
                }
                let inner = s[i + 1..j].trim();
                if let Some(name) = inner.strip_prefix('/') {
                    // End tag: must match the top of the stack.
                    let name = name.trim();
                    match stack.pop() {
                        Some(open) if open == name => {}
                        _ => return false,
                    }
                } else if let Some(name) = inner.strip_suffix('/') {
                    // Self-closing tag: well-formed, nothing pushed.
                    if xml_tag_name(name.trim()).is_none() {
                        return false;
                    }
                } else {
                    match xml_tag_name(inner) {
                        Some(name) => stack.push(name),
                        None => return false,
                    }
                }
                i = j + 1;
            }
            b'&' => {
                // XMLLiteral.parse uses a full XML parser; without a DTD only the
                // five predefined entities and numeric character references are
                // valid -- any other &name; causes a parse error (⇒
                // MalformedLiteralException in Java). Reject unknown entities.
                match s[i..].find(';') {
                    Some(rel) if rel > 1 => {
                        let name = &s[i + 1..i + rel];
                        let valid = matches!(name, "amp" | "lt" | "gt" | "quot" | "apos")
                            || name.starts_with('#');
                        if !valid {
                            return false;
                        }
                        i += rel + 1;
                    }
                    _ => return false,
                }
            }
            _ => i += 1,
        }
    }
    stack.is_empty()
}

/// Extracts and validates the element name from a start-tag body (the text
/// between `<` and `>`), returning the name when the first token is a valid XML
/// name. Returns `None` for an empty or invalid name.
pub fn xml_tag_name(inner: &str) -> Option<String> {
    let name: String = inner
        .chars()
        .take_while(|c| !c.is_whitespace())
        .collect();
    if name.is_empty() || !is_valid_xml_name(&name, true) {
        return None;
    }
    // A real XML parser (Java's XMLLiteral.parse) rejects a start tag with a
    // repeated attribute name (the "Unique Att Spec" well-formedness constraint)
    // or an attribute whose name is not a valid XML Name, making the literal
    // ill-typed; reject those here too. Only clearly-parsable attribute syntax is
    // judged -- ambiguous syntax is left to the lenient scanner.
    if !attributes_well_formed(inner) {
        return None;
    }
    Some(name)
}

/// Whether a start-tag body (`name attr="v" ...`) has well-formed attributes:
/// no repeated attribute name (XML "Unique Att Spec") and every parsed attribute
/// name is a valid XML Name (`xmlns`/`xmlns:*`/`name`/`pfx:name`). Conservative: it
/// parses `name="value"` / `name='value'` pairs and only judges cleanly-parsable
/// syntax; if the attribute syntax cannot be parsed it stops (returns `true`,
/// "no problem found"), so no well-formed literal is rejected.
fn attributes_well_formed(inner: &str) -> bool {
    let bytes = inner.as_bytes();
    let n = bytes.len();
    let mut i = 0;
    // Skip the element name (the leading non-whitespace token).
    while i < n && !bytes[i].is_ascii_whitespace() {
        i += 1;
    }
    let mut seen: Vec<&str> = Vec::new();
    loop {
        while i < n && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= n {
            break;
        }
        let name_start = i;
        while i < n && bytes[i] != b'=' && !bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        let name = &inner[name_start..i];
        while i < n && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= n || bytes[i] != b'=' {
            break; // not a name="value" attribute; stop (stay lenient)
        }
        i += 1;
        while i < n && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= n || (bytes[i] != b'"' && bytes[i] != b'\'') {
            break;
        }
        let quote = bytes[i];
        i += 1;
        while i < n && bytes[i] != quote {
            i += 1;
        }
        if i >= n {
            break; // unterminated value
        }
        i += 1; // closing quote
        if !name.is_empty() {
            // The attribute name must be a valid (possibly prefixed) XML Name.
            if !is_valid_xml_name(name, true) {
                return false;
            }
            if seen.contains(&name) {
                return false; // duplicate attribute name
            }
            seen.push(name);
        }
    }
    true
}

/// A best-effort exclusive-XML-canonicalization of an `rdf:XMLLiteral` lexical
/// form, sufficient to make two literals that are lexically distinct but
/// identical under C14N compare *equal*. HermiT stores the output of Apache
/// Axiom's `Canonicalizer20010315ExclWithComments`; we reproduce the
/// canonicalization rules that decide value equality of the common
/// distinct-but-equal forms:
///   * start tags: attributes are sorted (namespace declarations — `xmlns`,
///     `xmlns:*` — first, then the rest by name), each rendered as
///     `name="value"` with the value double-quoted, intra-tag whitespace
///     collapsed to a single separating space, and no whitespace before `>`;
///   * empty elements are written as a start/end pair: `<e/>` ⇒ `<e></e>`;
///   * character references and the predefined entities in text and attribute
///     values are expanded to their characters, then re-escaped canonically
///     (`&` ⇒ `&amp;`, `<` ⇒ `&lt;`, `>` ⇒ `&gt;` in text; plus `"` ⇒ `&quot;`
///     in attribute values);
///   * comments are preserved (the *WithComments* variant);
///   * CDATA sections are replaced by their (escaped) character content.
///
/// FIX D: this is a tree-based canonicalizer (a recursive descent over the parsed
/// element structure) implementing the parts of exclusive C14N (with comments)
/// that decide rdf:XMLLiteral value equality:
///   * namespace minimization — at each element, only the namespace declarations
///     that are *visibly utilized* (the element's own prefix and its non-namespace
///     attributes' prefixes) and *not already rendered in the same scope with the
///     same value* are emitted (the exclusive-C14N rendered-namespace rule), so two
///     fragments that declare the same namespace at different levels / redundantly
///     canonicalize equal;
///   * attribute ordering — namespace declarations first, sorted by prefix
///     (`xmlns` before `xmlns:*`), then ordinary attributes sorted by
///     (namespace-URI, local-name) per the C14N document order;
///   * empty elements are written as a start/end pair (`<e/>` ⇒ `<e></e>`);
///   * attribute-value normalization — references expanded, then re-escaped for the
///     attribute context (`&` `<` `"` and the whitespace `	`/`\n`/`\r`);
///   * full numeric character reference expansion, including supplementary (astral)
///     code points (`char::from_u32` decodes the whole Unicode range);
///   * comments preserved (the *WithComments* variant); CDATA replaced by its
///     escaped character content.
///
/// Residual gap vs Apache Axiom's byte-exact output (documented; it only ever makes
/// two genuinely-equal literals *fail* to unify, never the reverse, so it stays
/// sound for the equality test): DTD-driven attribute-type normalization (CDATA vs
/// tokenized) and DTD default attributes are not applied, and namespace-prefix
/// *rewriting* (renaming prefixes) is not performed — prefixes are preserved, which
/// matches C14N (C14N never renames prefixes; it only minimizes declarations).
pub fn canonicalize_xml_literal(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = String::with_capacity(s.len());
    let mut pos = 0;
    // The namespace scope: a stack of (prefix -> uri) frames. The wrapper element in
    // Java carries no namespaces, so we start with one empty in-scope frame.
    let mut scope: Vec<std::collections::BTreeMap<String, String>> = vec![Default::default()];
    canonicalize_nodes(&chars, &mut pos, &mut out, &mut scope, None);
    out
}

/// Recursively canonicalize a run of sibling nodes until either end-of-input or the
/// end tag named `closing` (when `Some`). `pos` advances past consumed input.
fn canonicalize_nodes(
    chars: &[char],
    pos: &mut usize,
    out: &mut String,
    scope: &mut Vec<std::collections::BTreeMap<String, String>>,
    closing: Option<&str>,
) {
    while *pos < chars.len() {
        if chars[*pos] == '<' {
            // Comment / CDATA / PI / declaration.
            if starts_with(chars, *pos, "<!--") {
                if let Some(end) = find_seq(chars, *pos + 4, "-->") {
                    out.extend(&chars[*pos..end + 3]);
                    *pos = end + 3;
                } else {
                    out.extend(&chars[*pos..]);
                    *pos = chars.len();
                }
                continue;
            }
            if starts_with(chars, *pos, "<![CDATA[") {
                if let Some(end) = find_seq(chars, *pos + 9, "]]>") {
                    let content: String = chars[*pos + 9..end].iter().collect();
                    out.push_str(&escape_xml_text(&content));
                    *pos = end + 3;
                } else {
                    *pos = chars.len();
                }
                continue;
            }
            if *pos + 1 < chars.len() && (chars[*pos + 1] == '?' || chars[*pos + 1] == '!') {
                if let Some(end) = char_find(chars, *pos, '>') {
                    out.extend(&chars[*pos..=end]);
                    *pos = end + 1;
                } else {
                    out.extend(&chars[*pos..]);
                    *pos = chars.len();
                }
                continue;
            }
            // A tag: locate the matching '>' skipping quoted attribute values.
            let mut j = *pos + 1;
            let mut quote: Option<char> = None;
            while j < chars.len() {
                let c = chars[j];
                match quote {
                    Some(q) if c == q => quote = None,
                    Some(_) => {}
                    None if c == '"' || c == '\'' => quote = Some(c),
                    None if c == '>' => break,
                    None => {}
                }
                j += 1;
            }
            if j >= chars.len() {
                // Unterminated (well-formedness already rejected this case in
                // parsing); copy verbatim and stop.
                out.extend(&chars[*pos..]);
                *pos = chars.len();
                return;
            }
            let inner: String = chars[*pos + 1..j].iter().collect();
            let inner = inner.trim().to_string();
            if let Some(rest) = inner.strip_prefix('/') {
                // End tag: it must close the current element; return to the caller.
                let _ = rest.trim();
                *pos = j + 1;
                return;
            }
            let self_closing = inner.ends_with('/');
            let body = if self_closing { inner[..inner.len() - 1].trim() } else { inner.as_str() };
            *pos = j + 1;
            canonicalize_element(chars, pos, out, scope, body, self_closing);
        } else {
            // Character data up to the next '<'.
            let start = *pos;
            while *pos < chars.len() && chars[*pos] != '<' {
                *pos += 1;
            }
            let text: String = chars[start..*pos].iter().collect();
            out.push_str(&escape_xml_text(&expand_xml_refs(&text)));
        }
    }
    let _ = closing;
}

/// Canonicalize one element given its start-tag body (`name attr=...`). Emits the
/// start tag with minimized namespaces and ordered attributes, recurses into the
/// content (unless self-closing), and emits the matching end tag.
fn canonicalize_element(
    chars: &[char],
    pos: &mut usize,
    out: &mut String,
    scope: &mut Vec<std::collections::BTreeMap<String, String>>,
    body: &str,
    self_closing: bool,
) {
    let (name, raw_attrs) = parse_tag_body(body);
    // Partition raw attributes into namespace declarations and ordinary attributes.
    let mut decls: Vec<(String, String)> = Vec::new(); // (prefix, uri); prefix "" = default
    let mut attrs: Vec<(String, String)> = Vec::new(); // (qname, value)
    for (aname, avalue) in &raw_attrs {
        let value = escape_xml_attr(&expand_xml_refs(avalue));
        if aname == "xmlns" {
            decls.push((String::new(), expand_xml_refs(avalue)));
        } else if let Some(pfx) = aname.strip_prefix("xmlns:") {
            decls.push((pfx.to_string(), expand_xml_refs(avalue)));
        } else {
            attrs.push((aname.clone(), value));
        }
    }
    // Push a new scope frame reflecting these declarations.
    let mut frame = scope.last().cloned().unwrap_or_default();
    for (pfx, uri) in &decls {
        frame.insert(pfx.clone(), uri.clone());
    }
    // The set of prefixes visibly utilized by this element: its own prefix plus the
    // prefixes of its ordinary attributes. (Exclusive C14N also honours an
    // InclusiveNamespaces PrefixList; we have none here.)
    let mut utilized: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    utilized.insert(prefix_of(&name));
    for (qn, _) in &attrs {
        let p = prefix_of(qn);
        if !p.is_empty() {
            utilized.insert(p);
        }
    }
    // Rendered (output) namespace context = the most recent ancestor-emitted set.
    // We track it as the previous frame's *rendered* map via the scope stack: a
    // declaration is emitted iff the prefix is utilized AND not already in the
    // parent's in-scope context with the same URI (exclusive C14N).
    let parent = scope.last().cloned().unwrap_or_default();
    let mut emitted_decls: Vec<(String, String)> = Vec::new();
    for pfx in &utilized {
        let uri = frame.get(pfx).cloned().unwrap_or_default();
        if uri.is_empty() && pfx.is_empty() {
            // The default namespace is undeclared (no xmlns="..."): emit nothing.
            continue;
        }
        match parent.get(pfx) {
            Some(prev) if prev == &uri => {} // already in scope with same value
            _ => emitted_decls.push((pfx.clone(), uri.clone())),
        }
    }
    // Order: namespace declarations first (default ns, then by prefix), then
    // ordinary attributes by (namespace-URI, local-name).
    emitted_decls.sort_by(|a, b| a.0.cmp(&b.0));
    attrs.sort_by(|a, b| {
        let auri = frame.get(&prefix_of(&a.0)).cloned().unwrap_or_default();
        let buri = frame.get(&prefix_of(&b.0)).cloned().unwrap_or_default();
        auri.cmp(&buri).then_with(|| local_of(&a.0).cmp(local_of(&b.0)))
    });
    out.push('<');
    out.push_str(&name);
    for (pfx, uri) in &emitted_decls {
        if pfx.is_empty() {
            out.push_str(" xmlns=\"");
        } else {
            out.push_str(" xmlns:");
            out.push_str(pfx);
            out.push_str("=\"");
        }
        out.push_str(&escape_xml_attr(uri));
        out.push('"');
    }
    for (qn, value) in &attrs {
        out.push(' ');
        out.push_str(qn);
        out.push_str("=\"");
        out.push_str(value);
        out.push('"');
    }
    out.push('>');
    if !self_closing {
        scope.push(frame);
        canonicalize_nodes(chars, pos, out, scope, Some(&name));
        scope.pop();
    }
    out.push_str("</");
    out.push_str(&name);
    out.push('>');
}

/// The namespace prefix of a QName (`""` when unprefixed).
fn prefix_of(qname: &str) -> String {
    match qname.find(':') {
        Some(c) => qname[..c].to_string(),
        None => String::new(),
    }
}
/// The local part of a QName.
fn local_of(qname: &str) -> &str {
    match qname.find(':') {
        Some(c) => &qname[c + 1..],
        None => qname,
    }
}

fn starts_with(chars: &[char], at: usize, needle: &str) -> bool {
    let n: Vec<char> = needle.chars().collect();
    at + n.len() <= chars.len() && chars[at..at + n.len()] == n[..]
}
fn find_seq(chars: &[char], from: usize, needle: &str) -> Option<usize> {
    let n: Vec<char> = needle.chars().collect();
    if n.is_empty() || from > chars.len() {
        return None;
    }
    let mut i = from;
    while i + n.len() <= chars.len() {
        if chars[i..i + n.len()] == n[..] {
            return Some(i);
        }
        i += 1;
    }
    None
}
fn char_find(chars: &[char], from: usize, target: char) -> Option<usize> {
    (from..chars.len()).find(|&i| chars[i] == target)
}

/// Parse a start-tag body into its element QName and ordered (name, raw-value)
/// attribute pairs (raw value = the unexpanded text between the quotes).
fn parse_tag_body(body: &str) -> (String, Vec<(String, String)>) {
    let body = body.trim();
    let chars: Vec<char> = body.chars().collect();
    let mut p = 0;
    while p < chars.len() && !chars[p].is_whitespace() {
        p += 1;
    }
    let name: String = chars[..p].iter().collect();
    let mut attrs: Vec<(String, String)> = Vec::new();
    while p < chars.len() {
        while p < chars.len() && chars[p].is_whitespace() {
            p += 1;
        }
        if p >= chars.len() {
            break;
        }
        let astart = p;
        while p < chars.len() && chars[p] != '=' && !chars[p].is_whitespace() {
            p += 1;
        }
        let aname: String = chars[astart..p].iter().collect();
        while p < chars.len() && chars[p].is_whitespace() {
            p += 1;
        }
        let mut avalue = String::new();
        if p < chars.len() && chars[p] == '=' {
            p += 1;
            while p < chars.len() && chars[p].is_whitespace() {
                p += 1;
            }
            if p < chars.len() && (chars[p] == '"' || chars[p] == '\'') {
                let q = chars[p];
                p += 1;
                let vstart = p;
                while p < chars.len() && chars[p] != q {
                    p += 1;
                }
                avalue = chars[vstart..p].iter().collect();
                if p < chars.len() {
                    p += 1;
                }
            }
        }
        if !aname.is_empty() {
            attrs.push((aname, avalue));
        }
    }
    (name, attrs)
}

/// Expands the predefined entities and numeric character references in a text /
/// attribute fragment to their character values (BMP/ASCII numeric refs).
pub fn expand_xml_refs(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'&' {
            if let Some(rel) = s[i..].find(';') {
                let entity = &s[i + 1..i + rel];
                let replaced = match entity {
                    "amp" => Some('&'),
                    "lt" => Some('<'),
                    "gt" => Some('>'),
                    "quot" => Some('"'),
                    "apos" => Some('\''),
                    _ => entity
                        .strip_prefix('#')
                        .and_then(|num| {
                            if let Some(hex) = num.strip_prefix(['x', 'X']) {
                                u32::from_str_radix(hex, 16).ok()
                            } else {
                                num.parse::<u32>().ok()
                            }
                        })
                        .and_then(char::from_u32),
                };
                if let Some(c) = replaced {
                    out.push(c);
                    i += rel + 1;
                    continue;
                }
            }
        }
        out.push(s[i..].chars().next().unwrap());
        i += s[i..].chars().next().unwrap().len_utf8();
    }
    out
}

/// Canonical escaping for element text content.
pub fn escape_xml_text(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '\r' => out.push_str("&#xD;"),
            _ => out.push(c),
        }
    }
    out
}

/// Canonical escaping for a (double-quoted) attribute value.
pub fn escape_xml_attr(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '"' => out.push_str("&quot;"),
            '\t' => out.push_str("&#x9;"),
            '\n' => out.push_str("&#xA;"),
            '\r' => out.push_str("&#xD;"),
            _ => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod rescan_tests {
    use super::{
        canonicalize_xml_literal, is_valid_any_uri, is_well_formed_xml, parse_base64_binary,
        parse_datetime,
    };

    // FIX D: equal-but-differently-serialized XMLLiterals must canonicalize equal,
    // and malformed forms must be rejected by the stricter well-formedness check.
    #[test]
    fn xml_literal_canonicalization_and_wellformedness() {
        let c = canonicalize_xml_literal;
        // Self-closing vs paired empty element canonicalize equal.
        assert_eq!(c("<a/>"), c("<a></a>"));
        // Attribute order is canonicalized (sorted), so different orders match.
        assert_eq!(c("<e b=\"2\" a=\"1\"/>"), c("<e a=\"1\" b=\"2\"></e>"));
        // Character/entity references expand to the same canonical text.
        assert_eq!(c("<a>&#65;&#x42;</a>"), c("<a>AB</a>"));
        // Supplementary (astral) numeric refs expand (U+1F600).
        assert_eq!(c("<a>&#128512;</a>"), c("<a>\u{1F600}</a>"));
        assert_eq!(c("<a>&#x1F600;</a>"), c("<a>\u{1F600}</a>"));
        // Namespace minimization: a redundant re-declaration of the SAME namespace
        // on a child is dropped, so the two forms canonicalize equal.
        assert_eq!(
            c("<a xmlns:p=\"u\"><p:b xmlns:p=\"u\"/></a>"),
            c("<a xmlns:p=\"u\"><p:b/></a>"),
        );
        // But a namespace actually used must be present (no false equality with a
        // form that never declares it).
        assert_ne!(c("<p:b xmlns:p=\"u\"/>"), c("<p:b xmlns:p=\"v\"/>"));

        // Stricter well-formedness: non-XML-Char content is rejected.
        assert!(!is_well_formed_xml("<a>\u{0}</a>")); // NUL is not an XML Char
        assert!(!is_well_formed_xml("\u{1}")); // bare C0 control
        // Invalid attribute name is rejected.
        assert!(!is_well_formed_xml("<a 1bad=\"x\"/>"));
        // A valid prefixed attribute / element name is accepted.
        assert!(is_well_formed_xml("<p:a p:b=\"x\"/>"));
        // Well-formed baselines still accepted.
        assert!(is_well_formed_xml("<a>text</a>"));
        assert!(is_well_formed_xml("<a><b/>x</a>"));
    }

    // A real XML parser rejects a start tag with a repeated attribute name
    // (XML's "Unique Att Spec"), so such an rdf:XMLLiteral is ill-typed; the
    // lenient scanner must reject it too, while still accepting distinct
    // attributes and the unquoted-but-valid cases it cannot fully parse.
    #[test]
    fn xml_literal_rejects_duplicate_attributes() {
        assert!(!is_well_formed_xml("<a x=\"1\" x=\"2\"/>"));
        assert!(!is_well_formed_xml("<a x=\"1\" x=\"2\"></a>"));
        // Distinct attribute names are fine.
        assert!(is_well_formed_xml("<a x=\"1\" y=\"2\"/>"));
        assert!(is_well_formed_xml("<a x=\"1\"></a>"));
        // Single-quoted values are handled too.
        assert!(!is_well_formed_xml("<a x='1' x='2'/>"));
    }

    // Java parses dateTime subfields with digit-only regex classes, so a
    // leading `+` inside any subfield makes `matcher.matches()` fail (an
    // ill-typed literal). Rust's `str::parse` would otherwise accept `+`, which
    // could suppress a clash Java raises. Each numeric subfield must be rejected
    // when it carries a `+` (the year keeps only its own single leading `-`).
    #[test]
    fn datetime_rejects_plus_prefixed_subfields() {
        // Well-typed baselines still parse.
        assert!(parse_datetime("2020-01-01T00:00:00Z", true).is_some());
        assert!(parse_datetime("-0044-03-15T12:00:00", true).is_some());
        assert!(parse_datetime("2020-01-01T00:00:00+05:30", true).is_some());
        // `+`-prefixed subfields are ill-typed in Java and must be rejected.
        assert!(parse_datetime("+2020-01-01T00:00:00Z", true).is_none()); // year
        assert!(parse_datetime("2020-+1-01T00:00:00Z", true).is_none()); // month
        assert!(parse_datetime("2020-01-+1T00:00:00Z", true).is_none()); // day
        assert!(parse_datetime("2020-01-01T+5:00:00Z", true).is_none()); // hour
        assert!(parse_datetime("2020-01-01T00:+5:00Z", true).is_none()); // minute
        assert!(parse_datetime("2020-01-01T00:00:+5Z", true).is_none()); // second
        assert!(parse_datetime("2020-01-01T00:00:00+0a:30", true).is_none()); // tz
    }

    // A parsed base64 value is tagged HEX_BINARY (matching Java
    // `BinaryData.parseBase64Binary`), so its canonical form is the uppercase hex
    // of the decoded bytes and forms decoding to the same bytes compare equal.
    #[test]
    fn base64_equality_is_by_decoded_bytes() {
        let (c1, n1) = parse_base64_binary("QQ==").unwrap(); // decodes to 0x41
        let (c2, n2) = parse_base64_binary("QR==").unwrap(); // non-canonical, also 0x41
        assert_eq!(c1, c2, "forms decoding to the same bytes must be equal");
        assert_eq!(c1, "41");
        assert_eq!((n1, n2), (1, 1));
        // Whitespace is ignored; the canonical form is the hex of the bytes.
        let (c3, n3) = parse_base64_binary(" QU JD ").unwrap(); // "ABC" = 0x41,0x42,0x43
        assert_eq!(c3, "414243");
        assert_eq!(n3, 3);
        // Malformed: wrong length / bad alphabet rejected.
        assert!(parse_base64_binary("QQ=").is_none());
        assert!(parse_base64_binary("@@@@").is_none());
    }

    // Faithful to `new java.net.URI(...)` (RFC 2396): malformed percent-escapes are rejected.
    #[test]
    fn any_uri_validation_matches_java_net_uri() {
        // Valid forms HermiT accepts.
        assert!(is_valid_any_uri("http://example.org/a"));
        assert!(is_valid_any_uri("urn:hermit:x"));
        assert!(is_valid_any_uri("http://example.org/a%20b")); // well-formed %XX
        assert!(is_valid_any_uri("../relative/path?q=1#frag"));
        assert!(is_valid_any_uri("http://example.org/\u{00e9}")); // non-ASCII "other"
        // Invalid forms HermiT rejects.
        assert!(!is_valid_any_uri("## not a uri")); // space
        assert!(!is_valid_any_uri("http://e.org/%zz")); // bad escape
        assert!(!is_valid_any_uri("http://e.org/%2")); // truncated escape
        assert!(!is_valid_any_uri("a<b")); // illegal char
        assert!(!is_valid_any_uri("a|b")); // illegal char
        assert!(!is_valid_any_uri("a\u{0007}b")); // control char
    }

    // Structural (RFC 2396 / java.net.URI) cases beyond the character-class check:
    // malformed authority / host structure is rejected, while well-structured
    // absolute and relative URI-references are accepted.
    #[test]
    fn any_uri_structural_authority_and_paths() {
        // Valid absolute URIs with authority.
        assert!(is_valid_any_uri("http://user:pass@host.example.com:8080/p/a/t/h?q=1#f"));
        assert!(is_valid_any_uri("http://[::1]:80/")); // IPv6 host
        assert!(is_valid_any_uri("http://192.168.0.1/")); // IPv4 host
        assert!(is_valid_any_uri("ftp://host/")); // empty path after authority
        assert!(is_valid_any_uri("mailto:user@example.com")); // opaque part
        assert!(is_valid_any_uri("urn:isbn:0451450523")); // opaque part
        // Valid relative references.
        assert!(is_valid_any_uri("a/b/c"));
        assert!(is_valid_any_uri("/abs/path"));
        assert!(is_valid_any_uri("?query-only"));
        assert!(is_valid_any_uri("#frag-only"));
        assert!(is_valid_any_uri("")); // the empty reference is a valid URI-reference
        // Bad authority: unterminated IPv6 literal.
        assert!(!is_valid_any_uri("http://[::1/"));
        // Bad authority: non-digit port.
        assert!(!is_valid_any_uri("http://host:8a/"));
        // Junk after IPv6 literal.
        assert!(!is_valid_any_uri("http://[::1]x/"));
        // A second '#' is illegal (only one fragment).
        assert!(!is_valid_any_uri("a#b#c"));
        // Illegal characters anywhere.
        assert!(!is_valid_any_uri("http://host/ a")); // space in path
        assert!(!is_valid_any_uri("http://host/\"q\"")); // quote
        assert!(!is_valid_any_uri("http://host/{x}")); // braces
        assert!(!is_valid_any_uri("http://host/a^b")); // caret
        assert!(!is_valid_any_uri("http://host/a\\b")); // backslash
    }
}
