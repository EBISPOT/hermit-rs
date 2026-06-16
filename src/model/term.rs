// Ports of org.semanticweb.HermiT.model.{Term,Variable,Individual,Constant}.

use crate::prefixes::Prefixes;
use crate::{impl_display_prefixes, interned};

// ---------------------------------------------------------------------------
// Variable
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct VariableData {
    name: String,
}

interned!(pub Variable => VariableData);

impl Variable {
    pub fn create(name: impl Into<String>) -> Variable {
        Variable::intern(VariableData { name: name.into() })
    }
    pub fn name(&self) -> &str {
        &self.0.name
    }
    pub fn to_string_prefixes(&self, _prefixes: &Prefixes) -> String {
        self.0.name.clone()
    }
}

// ---------------------------------------------------------------------------
// Individual
// ---------------------------------------------------------------------------

const ANONYMOUS_INDIVIDUAL_PREFIX: &str = "internal:anonymous#";

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct IndividualData {
    uri: String,
}

interned!(pub Individual => IndividualData);

impl Individual {
    /// Returns an Individual with the given identifier. Calling this multiple
    /// times with the same identifier returns the same (interned) object. It is
    /// the caller's responsibility to normalize the given URI.
    pub fn create(uri: impl Into<String>) -> Individual {
        Individual::intern(IndividualData { uri: uri.into() })
    }
    pub fn create_anonymous(id: &str) -> Individual {
        Individual::create(Self::anonymous_uri(id))
    }
    pub fn anonymous_uri(id: &str) -> String {
        format!("{ANONYMOUS_INDIVIDUAL_PREFIX}{id}")
    }
    pub fn iri(&self) -> &str {
        &self.0.uri
    }
    pub fn is_anonymous(&self) -> bool {
        self.0.uri.starts_with(ANONYMOUS_INDIVIDUAL_PREFIX)
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        prefixes.abbreviate_iri(&self.0.uri)
    }
}

// Ordering by IRI, mirroring DLOntology.IndividualComparator.
impl PartialOrd for Individual {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Individual {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        crate::model::java_string_cmp(self.iri(), other.iri())
    }
}

// ---------------------------------------------------------------------------
// Constant
// ---------------------------------------------------------------------------
//
// In Java, `Constant.create(lexicalForm, datatypeURI)` parses the lexical form
// against the datatype registry (`DatatypeRegistry.parseLiteral`), stores the
// resulting `m_dataValue`, and *throws* `MalformedLiteralException` for an
// invalid lexical form; `getDataValue()` then returns the parsed value.
//
// The lexical->value parser is the shared leaf module `crate::datatype_value`
// (the single Rust analogue of `DatatypeRegistry.parseLiteral`), so `Constant`
// and the value-space reasoning in `crate::tableau::datatype_manager` use ONE
// parser. `data_value()` / `create_checked` below call into it directly;
// `model` keeps depending only on that leaf module, not on `tableau`.
//
// Crucially, HermiT interns constants on the lexical form and datatype URI ONLY
// (the parsed value is excluded from `equal`/`getHashCode`), so the interning
// key here is `(lexical_form, datatype_uri)` and the parsed value -- available
// on demand via `data_value()` -- never participates in identity.

const ANONYMOUS_CONSTANTS_DATATYPE: &str = "internal:anonymous-constants";

/// The shared parsed-constant value type (Java's `Object m_dataValue` produced
/// by `DatatypeRegistry.parseLiteral`), re-exported from the canonical
/// [`crate::datatype_value`] module so `Constant::data_value` and the datatype
/// reasoning share one type.
pub use crate::datatype_value::{parse_value as parse_data_value, DataValue};

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct ConstantData {
    lexical_form: String,
    datatype_uri: String,
}

interned!(pub Constant => ConstantData);

impl Constant {
    /// Interns a constant from a lexical form and datatype URI, WITHOUT parsing
    /// or validating the lexical form (always succeeds). This is the infallible
    /// constructor used pervasively across the port (clausification, internal
    /// constants like `internal:anonymous-constants`, tests). For the
    /// validating, throw-on-malformed analogue of Java's `Constant.create`, use
    /// [`Constant::create_checked`].
    pub fn create(lexical_form: impl Into<String>, datatype_uri: impl Into<String>) -> Constant {
        Constant::intern(ConstantData {
            lexical_form: lexical_form.into(),
            datatype_uri: datatype_uri.into(),
        })
    }
    /// The faithful analogue of Java `Constant.create(lexicalForm, datatypeURI)`:
    /// it parses the lexical form against the datatype (mirroring
    /// `DatatypeRegistry.parseLiteral`) and returns `Err` -- the
    /// `MalformedLiteralException` equivalent -- for an invalid lexical form,
    /// otherwise interns and returns the constant. The interning key is still
    /// `(lexical_form, datatype_uri)` only, so a checked and an unchecked
    /// constant with the same lexical+datatype are the same interned object.
    pub fn create_checked(
        lexical_form: impl Into<String>,
        datatype_uri: impl Into<String>,
    ) -> Result<Constant, String> {
        let lexical_form = lexical_form.into();
        let datatype_uri = datatype_uri.into();
        // A recognized datatype with an invalid lexical form is malformed (the
        // `MalformedLiteralException` analogue). An unsupported/opaque datatype
        // has no handler, so HermiT stores the lexical form verbatim and never
        // fails -- mirrored here by accepting it when the parser declines.
        if parse_data_value(&lexical_form, &datatype_uri).is_some()
            || !crate::datatype_value::is_supported_datatype(&datatype_uri)
        {
            Ok(Constant::create(lexical_form, datatype_uri))
        } else {
            Err(format!(
                "MalformedLiteralException: \"{lexical_form}\" is not a well-formed value of datatype <{datatype_uri}>"
            ))
        }
    }
    pub fn create_anonymous(id: &str) -> Constant {
        Constant::create(id, ANONYMOUS_CONSTANTS_DATATYPE)
    }
    pub fn lexical_form(&self) -> &str {
        &self.0.lexical_form
    }
    pub fn datatype_uri(&self) -> &str {
        &self.0.datatype_uri
    }
    /// The parsed data value of this constant, mirroring Java
    /// `Constant.getDataValue()`. HermiT stores the value `parseLiteral` produced
    /// at construction; here it is parsed on demand from the stored lexical form
    /// against the datatype (the parsed value is deliberately not part of the
    /// interning key, exactly as in Java). Returns `None` for a malformed /
    /// ill-typed literal -- what `parseLiteral` would have thrown on -- matching
    /// the `parse_value` semantics in `crate::tableau::datatype_manager`.
    pub fn data_value(&self) -> Option<DataValue> {
        parse_data_value(&self.0.lexical_form, &self.0.datatype_uri)
    }
    pub fn is_anonymous(&self) -> bool {
        self.0.datatype_uri == ANONYMOUS_CONSTANTS_DATATYPE
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        let mut buffer = String::new();
        buffer.push('"');
        for c in self.0.lexical_form.chars() {
            match c {
                '"' => buffer.push_str("\\\""),
                '\\' => buffer.push_str("\\\\"),
                _ => buffer.push(c),
            }
        }
        buffer.push_str("\"^^");
        buffer.push_str(&prefixes.abbreviate_iri(&self.0.datatype_uri));
        buffer
    }
}

// ---------------------------------------------------------------------------
// Term (abstract supertype)
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Variable(Variable),
    Individual(Individual),
    Constant(Constant),
}

impl Term {
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        match self {
            Term::Variable(v) => v.to_string_prefixes(prefixes),
            Term::Individual(i) => i.to_string_prefixes(prefixes),
            Term::Constant(c) => c.to_string_prefixes(prefixes),
        }
    }
    pub fn as_variable(&self) -> Option<&Variable> {
        match self {
            Term::Variable(v) => Some(v),
            _ => None,
        }
    }
    pub fn as_individual(&self) -> Option<&Individual> {
        match self {
            Term::Individual(i) => Some(i),
            _ => None,
        }
    }
    pub fn as_constant(&self) -> Option<&Constant> {
        match self {
            Term::Constant(c) => Some(c),
            _ => None,
        }
    }
}

impl From<Variable> for Term {
    fn from(v: Variable) -> Term {
        Term::Variable(v)
    }
}
impl From<Individual> for Term {
    fn from(i: Individual) -> Term {
        Term::Individual(i)
    }
}
impl From<Constant> for Term {
    fn from(c: Constant) -> Term {
        Term::Constant(c)
    }
}

impl_display_prefixes!(Variable, Individual, Constant, Term);

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    const XSD_INTEGER: &str = "http://www.w3.org/2001/XMLSchema#integer";
    const XSD_ANYURI: &str = "http://www.w3.org/2001/XMLSchema#anyURI";
    const XSD_DECIMAL: &str = "http://www.w3.org/2001/XMLSchema#decimal";
    const XSD_BOOLEAN: &str = "http://www.w3.org/2001/XMLSchema#boolean";

    // data_value() returns the parsed value for a valid literal, mirroring
    // Java Constant.getDataValue().
    #[test]
    fn data_value_parses_valid_literal() {
        let c = Constant::create("5", XSD_INTEGER);
        assert_eq!(c.data_value(), Some(DataValue::Integer(BigInt::from(5))));

        // "1.0"^^xsd:decimal reduces to an integer value (1/1) per make_rational.
        let d = Constant::create("1.0", XSD_DECIMAL);
        assert_eq!(d.data_value(), Some(DataValue::Integer(BigInt::from(1))));

        let b = Constant::create("true", XSD_BOOLEAN);
        assert_eq!(b.data_value(), Some(DataValue::Boolean(true)));

        let u = Constant::create("http://example.org/x", XSD_ANYURI);
        assert_eq!(
            u.data_value(),
            Some(DataValue::Typed {
                kind: "anyURI",
                canonical: "http://example.org/x".to_string(),
                length: "http://example.org/x".encode_utf16().count(),
            })
        );
    }

    // data_value() returns None for a malformed literal, like parseLiteral throwing.
    #[test]
    fn data_value_none_for_malformed() {
        assert_eq!(Constant::create("abc", XSD_INTEGER).data_value(), None);
        assert_eq!(Constant::create("## not a uri", XSD_ANYURI).data_value(), None);
    }

    // An unsupported/opaque datatype has no handler, so the shared parser
    // declines (`data_value() == None`) -- but `create_checked` must still NOT
    // fail (HermiT stores the lexical form verbatim for an opaque datatype).
    #[test]
    fn opaque_datatype_never_fails_create_checked() {
        let dt = "http://example.org/myDatatype";
        let c = Constant::create("anything", dt);
        assert_eq!(c.data_value(), None);
        assert!(Constant::create_checked("anything", dt).is_ok());
    }

    // create_checked returns Err (MalformedLiteral equivalent) for an invalid form.
    #[test]
    fn create_checked_err_for_malformed() {
        assert!(Constant::create_checked("abc", XSD_INTEGER).is_err());
        assert!(Constant::create_checked("## not a uri", XSD_ANYURI).is_err());
        let msg = Constant::create_checked("abc", XSD_INTEGER).unwrap_err();
        assert!(msg.contains("MalformedLiteralException"));
    }

    // create_checked succeeds and interns for a valid literal.
    #[test]
    fn create_checked_ok_for_valid() {
        let c = Constant::create_checked("5", XSD_INTEGER).expect("valid literal");
        assert_eq!(c.lexical_form(), "5");
        assert_eq!(c.data_value(), Some(DataValue::Integer(BigInt::from(5))));
    }

    // The interning key is (lexical, datatype) ONLY: a checked and an unchecked
    // constant with the same lexical+datatype are the same interned object,
    // regardless of the parsed value.
    #[test]
    fn interning_key_unaffected_by_parsed_value() {
        let a = Constant::create("5", XSD_INTEGER);
        let b = Constant::create_checked("5", XSD_INTEGER).unwrap();
        assert!(a.ptr_eq(&b));

        let c = Constant::create("5", XSD_INTEGER);
        assert!(a.ptr_eq(&c));
    }

    // The existing infallible create still works for anonymous/internal constants,
    // even with lexical forms that would never parse against a real datatype.
    #[test]
    fn infallible_create_still_works() {
        let anon = Constant::create_anonymous("c1");
        assert!(anon.is_anonymous());
        assert_eq!(anon.lexical_form(), "c1");

        // Internal constants whose datatype is not a recognized XSD datatype are
        // accepted by create; the opaque datatype has no parsed value but never
        // fails the checked constructor either.
        let internal = Constant::create("whatever", ANONYMOUS_CONSTANTS_DATATYPE);
        assert_eq!(internal.data_value(), None);
        assert!(
            Constant::create_checked("whatever", ANONYMOUS_CONSTANTS_DATATYPE).is_ok()
        );
    }
}
