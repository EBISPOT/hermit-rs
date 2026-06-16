// Port of org.semanticweb.HermiT.structural.OWLClausification.
//
// Turns a normalized `OWLAxioms` into a `model::DLOntology`: a set of DL clauses
// plus positive/negative ABox facts and the derived vocabulary. The OWL-API
// clausifier visitors become recursive `match`es over horned-owl expressions,
// producing the interned `model` atoms and clauses.
//
// The full OWL 2 DL clausification is ported: concept/role/data inclusions,
// keys, facts, complex object-property inclusions (preprocessed by the
// `ObjectPropertyInclusionManager` into concept inclusions before this point),
// and SWRL rules (`clausify_rule`, the port of `NormalizedRuleClausifier`). By
// this point `OWLNormalization.RuleNormalizer` has fully normalized every rule
// (all arguments are variables; class atoms use only named classes), so the
// clausifier just maps atoms to DL atoms, collects abstract (object) variables,
// and guards them with `internal:named` for DL-safety. The data-property
// subject is DL-safety-restricted but the object (a data value) is not.

use std::collections::{BTreeSet, HashSet};

use horned_owl::model::DataProperty;
use horned_owl::vocab::Facet;

use super::{
    ClassExpr as CE, DataRangeExpr as DR, Individ as OwlIndividual, Lit as Literal,
    ObjectPropExpr as OPE,
};

use crate::model::{
    AnnotatedEquality, AtLeastConcept, AtLeastDataRange, Atom, AtomicConcept, AtomicRole, Constant,
    ConstantEnumeration, DLClause, DLOntology, DLPredicate, DatatypeRestriction, Individual,
    InternalDatatype, LiteralConcept, LiteralDataRange, NodeIDsAscendingOrEqual, Role, Term,
    Variable,
};
use crate::prefixes::Prefixes;

use super::expressivity::OWLAxiomsExpressivity;
use super::owl_axioms::{Fact, HasKeyAxiom, OWLAxioms};
use super::A;

const XSD_STRING: &str = "http://www.w3.org/2001/XMLSchema#string";
const RDF_PLAIN_LITERAL: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";

/// Faithful analogue of Java `OWLClausification.getConstant` /
/// `DataRangeConverter.visit(OWLLiteral)` (and the identical
/// `ReducedABoxOnlyClausification.getConstant`): build an interned constant from
/// a lexical form and datatype URI, mirroring `Constant.create ->
/// DatatypeRegistry.parseLiteral`.
///
/// `parseLiteral` throws in two distinct ways, which HermiT treats differently:
///   * `UnsupportedDatatypeException` — the datatype has no handler (it is not in
///     the OWL 2 datatype map). `getConstant` *catches* this: under
///     `ignoreUnsupportedDatatypes` it substitutes an anonymous constant
///     (`Constant.createAnonymous`, datatype `internal:anonymous-constants`);
///     otherwise it rethrows and the ontology is rejected.
///   * `MalformedLiteralException` — the datatype *is* supported but the lexical
///     form is invalid. `getConstant` does NOT catch this, so a malformed literal
///     of a supported datatype always rejects the ontology, regardless of the
///     ignore flag.
///
/// CRITICAL: every `internal:*` datatype (e.g. `internal:anonymous-constants`,
/// used by the data-property entailment reductions, and `internal:unknown-datatype#…`)
/// is treated as always-valid and stored verbatim. In Java these are registered /
/// handled datatypes, never `UnsupportedDatatypeException`s; rejecting them would
/// break the reductions in `reasoner.rs` (see `tests/breadth_tests.rs::p01d_*`).
pub(crate) fn build_validated_constant(
    lexical_form: String,
    datatype_uri: String,
    ignore_unsupported_datatypes: bool,
) -> Result<Constant, String> {
    // internal:* datatypes are always valid (Java has registered handlers for
    // internal:anonymous-constants and internal:unknown-datatype#…); store the
    // lexical form verbatim and never reject or anonymize.
    if datatype_uri.starts_with("internal:") {
        return Ok(Constant::create(lexical_form, datatype_uri));
    }
    if !crate::datatype_value::is_supported_datatype(&datatype_uri) {
        // UnsupportedDatatypeException analogue.
        if ignore_unsupported_datatypes {
            return Ok(Constant::create_anonymous(&lexical_form));
        }
        return Err(format!(
            "Unsupported datatype '{datatype_uri}': literals can only use the datatypes \
             of the OWL 2 datatype map. (HermiT rejects such ontologies unless unsupported \
             datatypes are ignored.)"
        ));
    }
    // Supported datatype: a malformed LEXICAL form is the MalformedLiteralException
    // analogue, which is fatal regardless of ignore_unsupported_datatypes.
    //
    // IMPORTANT: parseLiteral validates only the *lexical* form, NOT value-space
    // membership of a *derived* datatype. Java `Numbers.parseInteger` is purely
    // syntactic, so e.g. "-1"^^xsd:nonNegativeInteger does NOT throw at clausification
    // (it parses fine; the tableau's datatype reasoner later detects the value-space
    // clash and reports the ontology *inconsistent*). So we validate an integer-family
    // lexical against the UNBOUNDED xsd:integer to ignore the derived bounds, and only
    // reject genuinely malformed lexical forms. (`Constant::create_checked` would also
    // apply the derived bounds, which would wrongly reject this case.)
    const XSD_INTEGER: &str = "http://www.w3.org/2001/XMLSchema#integer";
    let lexical_well_formed = if crate::datatype_value::integer_datatype_bounds(&datatype_uri)
        .is_some()
    {
        crate::datatype_value::parse_value(&lexical_form, XSD_INTEGER).is_some()
    } else {
        crate::datatype_value::parse_value(&lexical_form, &datatype_uri).is_some()
    };
    if lexical_well_formed {
        Ok(Constant::create(lexical_form, datatype_uri))
    } else {
        Err(format!(
            "MalformedLiteralException: \"{lexical_form}\" is not a well-formed value of datatype \
             <{datatype_uri}>"
        ))
    }
}

/// Minimal stand-in for `org.semanticweb.HermiT.Configuration` carrying only the
/// flags consulted during clausification.
#[derive(Clone, Debug, Default)]
pub struct Configuration {
    pub ignore_unsupported_datatypes: bool,
}

fn var(name: &str) -> Variable {
    Variable::create(name)
}
fn x() -> Term {
    Term::Variable(var("X"))
}

// ---------------------------------------------------------------------------
// Static helpers (the OWLClausification.getXxx static methods).
// ---------------------------------------------------------------------------

fn get_literal_concept(description: &CE) -> LiteralConcept {
    match description {
        CE::Class(c) => LiteralConcept::AtomicConcept(AtomicConcept::create(c.0.to_string())),
        CE::ObjectComplementOf(internal) => match &**internal {
            CE::Class(c) => AtomicConcept::create(c.0.to_string()).get_negation(),
            _ => panic!("Internal error: invalid normal form."),
        },
        _ => panic!("Internal error: invalid normal form."),
    }
}

fn get_role(ope: &OPE) -> Role {
    match ope {
        OPE::ObjectProperty(p) => Role::AtomicRole(AtomicRole::create(p.0.to_string())),
        OPE::InverseObjectProperty(p) => AtomicRole::create(p.0.to_string()).get_inverse(),
    }
}

fn get_atomic_role_data(dp: &DataProperty<A>) -> AtomicRole {
    AtomicRole::create(dp.0.to_string())
}

fn get_role_atom_object(ope: &OPE, first: Term, second: Term) -> Atom {
    // Port of `OWLClausification.getRoleAtom(OWLObjectPropertyExpression,...)`.
    // For an inverse role HermiT builds the atom on the *named* property with the
    // arguments swapped (`Atom.create(role, second, first)`), rather than going
    // through `Role.getInverse()`. This matters for `owl:topObjectProperty` (and
    // `owl:bottomObjectProperty`): their `getInverse()` collapses to the role
    // itself, so routing through `get_role().get_role_assertion()` would drop the
    // argument swap and yield a *forward* `top(first,second)` instead of the
    // intended reverse edge `top(second,first)`. That collapse silently discarded
    // the reverse (mirror-automaton) transitions emitted for `∀top.C`, so
    // universal restrictions over `owl:topObjectProperty` never propagated.
    match ope {
        OPE::ObjectProperty(p) => Atom::create(
            DLPredicate::AtomicRole(AtomicRole::create(p.0.to_string())),
            vec![first, second],
        ),
        OPE::InverseObjectProperty(p) => Atom::create(
            DLPredicate::AtomicRole(AtomicRole::create(p.0.to_string())),
            vec![second, first],
        ),
    }
}

fn get_role_atom_data(dp: &DataProperty<A>, first: Term, second: Term) -> Atom {
    Atom::create(
        DLPredicate::AtomicRole(get_atomic_role_data(dp)),
        vec![first, second],
    )
}

fn get_individual(individual: &OwlIndividual) -> Individual {
    match individual {
        OwlIndividual::Anonymous(a) => Individual::create_anonymous(&a.0.to_string()),
        OwlIndividual::Named(n) => Individual::create(n.0.to_string()),
    }
}

/// Collects the IRIs of the named individuals occurring in an ABox fact.
/// Maps an XSD constraining facet to its IRI.
fn facet_iri(facet: &Facet) -> &'static str {
    use horned_owl::vocab::Facet::*;
    match facet {
        Length => "http://www.w3.org/2001/XMLSchema#length",
        MinLength => "http://www.w3.org/2001/XMLSchema#minLength",
        MaxLength => "http://www.w3.org/2001/XMLSchema#maxLength",
        Pattern => "http://www.w3.org/2001/XMLSchema#pattern",
        MinInclusive => "http://www.w3.org/2001/XMLSchema#minInclusive",
        MinExclusive => "http://www.w3.org/2001/XMLSchema#minExclusive",
        MaxInclusive => "http://www.w3.org/2001/XMLSchema#maxInclusive",
        MaxExclusive => "http://www.w3.org/2001/XMLSchema#maxExclusive",
        TotalDigits => "http://www.w3.org/2001/XMLSchema#totalDigits",
        FractionDigits => "http://www.w3.org/2001/XMLSchema#fractionDigits",
        // rdf:langRange lives in the RDF namespace (HermiT registers it as
        // RDF_NS+"langRange" in RDFPlainLiteralDatatypeHandler; the datatype manager
        // matches `{RDF}langRange`). Emitting owl#langRange here left it unrecognised.
        LangRange => "http://www.w3.org/1999/02/22-rdf-syntax-ns#langRange",
    }
}

fn as_internal_datatype_negation(literal_range: &LiteralDataRange) -> Option<InternalDatatype> {
    match literal_range.get_negation() {
        LiteralDataRange::InternalDatatype(d) => Some(d),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// DataRangeConverter
// ---------------------------------------------------------------------------

pub struct DataRangeConverter<'a> {
    // Consulted by datatype validation; mirrors HermiT's Configuration.ignoreUnsupportedDatatypes.
    ignore_unsupported_datatypes: bool,
    defined_datatype_iris: &'a HashSet<String>,
    all_unknown_datatype_restrictions: HashSet<DatatypeRestriction>,
    /// The first unsupported datatype IRI encountered (when not ignoring), so
    /// `clausify` can reject the ontology as HermiT does (UnsupportedDatatypeException).
    unsupported_datatype: Option<String>,
    /// The first `(datatype, facet)` pair where the facet is not supported by that
    /// datatype, so `clausify` can reject the ontology as HermiT does
    /// (`UnsupportedFacetException`).
    unsupported_facet: Option<(String, String)>,
    /// The first literal-validation error (a malformed literal of a supported
    /// datatype, or an unsupported datatype while not ignoring) encountered while
    /// converting a literal inside a data range (DataOneOf / facet value). This is
    /// the `convert_data_range`-side equivalent of the rethrown
    /// `MalformedLiteralException` / `UnsupportedDatatypeException`; `clausify`
    /// checks it and rejects the ontology, mirroring Java.
    literal_error: Option<String>,
}

impl<'a> DataRangeConverter<'a> {
    fn new(ignore_unsupported_datatypes: bool, defined_datatype_iris: &'a HashSet<String>) -> Self {
        DataRangeConverter {
            ignore_unsupported_datatypes,
            defined_datatype_iris,
            all_unknown_datatype_restrictions: HashSet::new(),
            literal_error: None,
            unsupported_datatype: None,
            unsupported_facet: None,
        }
    }

    /// Port of `DatatypeRegistry.validateDatatypeRestriction` for an unfaceted
    /// datatype: a URI that is neither a supported OWL 2 datatype, nor internal,
    /// nor defined via `DatatypeDefinition` is unsupported. With
    /// `ignore_unsupported_datatypes` it joins the unknown-restriction set
    /// (treated as a fresh value space); otherwise the ontology is rejected.
    fn validate_datatype(&mut self, datatype_uri: &str, restriction: &DatatypeRestriction) {
        if datatype_uri.starts_with("internal:unknown-datatype#") {
            self.all_unknown_datatype_restrictions.insert(restriction.clone());
        } else if !crate::tableau::datatype_manager::is_supported_datatype(datatype_uri) {
            if self.ignore_unsupported_datatypes {
                self.all_unknown_datatype_restrictions.insert(restriction.clone());
            } else if self.unsupported_datatype.is_none() {
                self.unsupported_datatype = Some(datatype_uri.to_string());
            }
        }
    }

    fn convert_data_range(&mut self, data_range: &DR) -> LiteralDataRange {
        match data_range {
            DR::Datatype(datatype) => {
                let datatype_uri = datatype.0.to_string();
                if InternalDatatype::rdfs_literal().iri() == datatype_uri {
                    return LiteralDataRange::InternalDatatype(InternalDatatype::rdfs_literal().clone());
                }
                if datatype_uri.starts_with("internal:defdata#")
                    || self.defined_datatype_iris.contains(&datatype_uri)
                {
                    return LiteralDataRange::InternalDatatype(InternalDatatype::create(datatype_uri));
                }
                let restriction = DatatypeRestriction::create(datatype_uri.clone(), vec![], vec![]);
                self.validate_datatype(&datatype_uri, &restriction);
                LiteralDataRange::DatatypeRestriction(restriction)
            }
            DR::DataComplementOf(inner) => self.convert_data_range(inner).get_negation(),
            DR::DataOneOf(values) => {
                let mut constants: HashSet<Constant> = HashSet::new();
                for literal in values {
                    constants.insert(self.convert_literal_recording(literal));
                }
                LiteralDataRange::ConstantEnumeration(ConstantEnumeration::create(
                    constants.into_iter().collect(),
                ))
            }
            DR::DatatypeRestriction(datatype, facets) => {
                let datatype_uri = datatype.0.to_string();
                if InternalDatatype::rdfs_literal().iri() == datatype_uri {
                    if !facets.is_empty() {
                        panic!("rdfs:Literal does not support any facets.");
                    }
                    return LiteralDataRange::InternalDatatype(
                        InternalDatatype::rdfs_literal().clone(),
                    );
                }
                let mut facet_uris = Vec::with_capacity(facets.len());
                let mut facet_values = Vec::with_capacity(facets.len());
                for facet in facets {
                    let facet_uri = facet_iri(&facet.f).to_string();
                    // HermiT's `DatatypeRegistry.validateDatatypeRestriction` throws
                    // `UnsupportedFacetException` for a facet the datatype handler does
                    // not support (e.g. `fractionDigits`, or `length` on a numeric).
                    // Java visit(OWLDatatypeRestriction) does NOT exempt defined datatypes
                    // (OWLClausification.java:820 — unconditional validateDatatypeRestriction).
                    if crate::tableau::datatype_manager::is_supported_datatype(&datatype_uri)
                        && !crate::tableau::datatype_manager::is_supported_facet(
                            &datatype_uri,
                            &facet_uri,
                        )
                        && self.unsupported_facet.is_none()
                    {
                        self.unsupported_facet = Some((datatype_uri.clone(), facet_uri.clone()));
                    }
                    // Java's validateDatatypeRestriction also validates the FACET
                    // VALUE's type/range (throws UnsupportedFacetException for bad values).
                    // Mirror each handler family here, at clausification time.
                    // No defined_datatype_iris exemption — Java checks unconditionally.
                    if self.unsupported_facet.is_none()
                        && crate::tableau::datatype_manager::is_supported_datatype(&datatype_uri)
                    {
                        // Extract the lexical form and datatype URI from the facet literal.
                        let (fv_lexical, fv_dtype) = match &facet.l {
                            Literal::Simple { literal } => {
                                (literal.as_str(), XSD_STRING)
                            }
                            Literal::Language { literal, .. } => {
                                (literal.as_str(), RDF_PLAIN_LITERAL)
                            }
                            Literal::Datatype { literal, datatype_iri } => {
                                (literal.as_str(), datatype_iri.as_ref())
                            }
                        };
                        use crate::datatype_value::{
                            is_decimal_datatype, is_datetime_datatype, is_integer_datatype,
                            is_rational_datatype, is_real_datatype, DataValue,
                        };
                        let xsd = "http://www.w3.org/2001/XMLSchema#";
                        let rdf_ns = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
                        let facet_local = facet_uri.strip_prefix(xsd);
                        let bad_facet_value = match facet_local {
                            // length/minLength/maxLength: value must be a non-negative
                            // integer strictly less than Integer.MAX_VALUE (Java int max).
                            // (AnyURIDatatypeHandler, BinaryDataDatatypeHandler,
                            //  RDFPlainLiteralDatatypeHandler all share this rule.)
                            Some("length" | "minLength" | "maxLength") => {
                                match fv_lexical.trim().parse::<i64>() {
                                    Ok(v) => v < 0 || v >= i32::MAX as i64,
                                    Err(_) => true,
                                }
                            }
                            // Ordering facets on the owl:real/decimal/integer/rational
                            // family: value must parse as an exact number (Integer or
                            // Decimal). OWLRealDatatypeHandler checks `instanceof Number`
                            // and `Numbers.isValidNumber`.
                            Some(
                                "minInclusive" | "maxInclusive"
                                | "minExclusive" | "maxExclusive",
                            ) if is_integer_datatype(&datatype_uri)
                                || is_decimal_datatype(&datatype_uri)
                                || is_rational_datatype(&datatype_uri)
                                || is_real_datatype(&datatype_uri) =>
                            {
                                !matches!(
                                    crate::datatype_value::parse_value(fv_lexical, fv_dtype),
                                    Some(DataValue::Integer(_) | DataValue::Decimal { .. })
                                )
                            }
                            // Ordering facets on xsd:dateTime/dateTimeStamp: value must
                            // parse as a dateTime. DateTimeDatatypeHandler checks
                            // `instanceof DateTime`.
                            Some(
                                "minInclusive" | "maxInclusive"
                                | "minExclusive" | "maxExclusive",
                            ) if is_datetime_datatype(&datatype_uri) => {
                                !matches!(
                                    crate::datatype_value::parse_value(fv_lexical, fv_dtype),
                                    Some(DataValue::DateTime { .. })
                                )
                            }
                            // xsd:pattern: value must be a string AND a valid regex.
                            // AnyURIDatatypeHandler / RDFPlainLiteralDatatypeHandler
                            // check `instanceof String` and `isValidPattern`.
                            Some("pattern") => {
                                if !matches!(
                                    crate::datatype_value::parse_value(fv_lexical, fv_dtype),
                                    Some(DataValue::Text(_))
                                ) {
                                    true // non-string facet value
                                } else {
                                    regex::Regex::new(
                                        &format!("^(?:{})$", fv_lexical)
                                    ).is_err()
                                }
                            }
                            // rdf:langRange: value must be a string.
                            // RDFPlainLiteralDatatypeHandler checks `instanceof String`.
                            _ if facet_uri == format!("{rdf_ns}langRange") => {
                                !matches!(
                                    crate::datatype_value::parse_value(fv_lexical, fv_dtype),
                                    Some(DataValue::Text(_))
                                )
                            }
                            _ => false,
                        };
                        if bad_facet_value {
                            self.unsupported_facet =
                                Some((datatype_uri.clone(), facet_uri.clone()));
                        }
                    }
                    facet_uris.push(facet_uri);
                    facet_values.push(self.convert_literal_recording(&facet.l));
                }
                let restriction =
                    DatatypeRestriction::create(datatype_uri.clone(), facet_uris, facet_values);
                // Java visit(OWLDatatypeRestriction) calls validateDatatypeRestriction
                // unconditionally — no exemption for defined datatypes
                // (OWLClausification.java:820). It also throws UnsupportedDatatypeException
                // without any ignore_unsupported_datatypes escape, so we force-reject here
                // rather than routing through the ignore-aware validate_datatype helper.
                if !datatype_uri.starts_with("internal:unknown-datatype#")
                    && !crate::tableau::datatype_manager::is_supported_datatype(&datatype_uri)
                    && self.unsupported_datatype.is_none()
                {
                    self.unsupported_datatype = Some(datatype_uri.clone());
                }
                LiteralDataRange::DatatypeRestriction(restriction)
            }
            DR::DataIntersectionOf(_) | DR::DataUnionOf(_) => {
                panic!("Internal error: invalid normal form.")
            }
        }
    }

    /// Faithful analogue of Java `DataRangeConverter.visit(OWLLiteral)`: parse and
    /// validate the literal against its datatype (`Constant.create ->
    /// DatatypeRegistry.parseLiteral`), returning `Err` for a malformed literal of
    /// a supported datatype or for an unsupported datatype (unless
    /// `ignore_unsupported_datatypes`, which substitutes an anonymous constant).
    /// See [`build_validated_constant`].
    fn convert_literal(&self, literal: &Literal) -> Result<Constant, String> {
        // Determine the lexical form and datatype URI HermiT interns on. For
        // rdf:PlainLiteral the lexical is canonicalized to "string@lang"; a typed
        // rdf:PlainLiteral with NO language tag canonicalizes to "lexical@" with a
        // trailing '@' (Java OWLClausification.getConstant: !hasLang -> literal+"@").
        let (lexical, datatype_uri) = match literal {
            Literal::Simple { literal } => (literal.clone(), XSD_STRING.to_string()),
            Literal::Language { literal, lang } => {
                (format!("{literal}@{lang}"), RDF_PLAIN_LITERAL.to_string())
            }
            Literal::Datatype { literal, datatype_iri } => {
                let datatype_uri = datatype_iri.to_string();
                if datatype_uri == RDF_PLAIN_LITERAL {
                    (format!("{literal}@"), datatype_uri)
                } else {
                    (literal.clone(), datatype_uri)
                }
            }
        };
        build_validated_constant(lexical, datatype_uri, self.ignore_unsupported_datatypes)
    }

    /// `convert_literal` for a literal occurring inside a data range (DataOneOf /
    /// facet value), where `convert_data_range` is infallible: on a validation
    /// error, record the first one into `literal_error` (so `clausify` rejects the
    /// ontology, as Java rethrows) and fall back to an unchecked constant so the
    /// data structure stays well-formed until clausify aborts.
    fn convert_literal_recording(&mut self, literal: &Literal) -> Constant {
        match self.convert_literal(literal) {
            Ok(constant) => constant,
            Err(message) => {
                if self.literal_error.is_none() {
                    self.literal_error = Some(message);
                }
                // Best-effort placeholder; clausify will reject before use.
                match literal {
                    Literal::Simple { literal } => Constant::create(literal.clone(), XSD_STRING),
                    Literal::Language { literal, lang } => {
                        Constant::create(format!("{literal}@{lang}"), RDF_PLAIN_LITERAL)
                    }
                    Literal::Datatype { literal, datatype_iri } => {
                        Constant::create(literal.clone(), datatype_iri.to_string())
                    }
                }
            }
        }
    }
}

fn ldr_predicate(ldr: &LiteralDataRange) -> DLPredicate {
    match ldr {
        LiteralDataRange::DatatypeRestriction(d) => DLPredicate::DatatypeRestriction(d.clone()),
        LiteralDataRange::ConstantEnumeration(d) => DLPredicate::ConstantEnumeration(d.clone()),
        LiteralDataRange::InternalDatatype(d) => DLPredicate::InternalDatatype(d.clone()),
        LiteralDataRange::AtomicNegationDataRange(d) => DLPredicate::AtomicNegationDataRange(d.clone()),
    }
}

// ---------------------------------------------------------------------------
// NormalizedAxiomClausifier
// ---------------------------------------------------------------------------

#[derive(Default)]
struct AxiomClausifier {
    head_atoms: Vec<Atom>,
    body_atoms: Vec<Atom>,
    y_index: u32,
    z_index: u32,
}

impl AxiomClausifier {
    fn get_dl_clause(&mut self) -> DLClause {
        let clause = DLClause::create(
            std::mem::take(&mut self.head_atoms),
            std::mem::take(&mut self.body_atoms),
        );
        self.y_index = 0;
        self.z_index = 0;
        clause
    }
    fn ensure_y_not_zero(&mut self) {
        if self.y_index == 0 {
            self.y_index += 1;
        }
    }
    fn next_y(&mut self) -> Variable {
        let result = if self.y_index == 0 {
            var("Y")
        } else {
            var(&format!("Y{}", self.y_index))
        };
        self.y_index += 1;
        result
    }
    fn next_z(&mut self) -> Variable {
        let result = if self.z_index == 0 {
            var("Z")
        } else {
            var(&format!("Z{}", self.z_index))
        };
        self.z_index += 1;
        result
    }
    fn get_concept_for_nominal(
        &mut self,
        individual: &OwlIndividual,
        positive_facts: &mut HashSet<Atom>,
    ) -> AtomicConcept {
        let result = match individual {
            OwlIndividual::Anonymous(a) => {
                AtomicConcept::create(format!("internal:anon#{}", a.0))
            }
            OwlIndividual::Named(n) => {
                AtomicConcept::create(format!("internal:nom#{}", n.0.to_string()))
            }
        };
        positive_facts.insert(Atom::create(
            DLPredicate::AtomicConcept(result.clone()),
            vec![Term::Individual(get_individual(individual))],
        ));
        result
    }

    /// Clausifies a normalized SWRL rule into a DL clause (the port of
    /// `OWLClausification.NormalizedRuleClausifier.clausify(rule, restrictToNamed)`).
    ///
    /// By this point `OWLNormalization.RuleNormalizer` has fully normalized the
    /// rule: every argument is a variable and every class-atom predicate is a
    /// named class. The head atoms form a *disjunction* (`DisjunctiveRule`), so
    /// this mirror maps atoms to DL atoms, collects the abstract (object)
    /// variables, and -- when `restrict_to_named` -- guards each abstract variable
    /// with `internal:named` for DL-safety, then emits a single DLClause whose
    /// (possibly multi-atom, disjunctive) head matches Java exactly. We pass
    /// `restrict_to_named = true`: HermiT's `processRules` only relaxes this for
    /// description-graph object properties, which this port does not support.
    fn clausify_rule(
        &mut self,
        rule: &super::owl_axioms::DisjunctiveRule,
        converter: &mut DataRangeConverter,
    ) -> Result<DLClause, String> {
        let restrict_to_named = true;
        let mut body_atoms: Vec<Atom> = Vec::new();
        let mut head_atoms: Vec<Atom> = Vec::new();
        let mut abstract_variables: Vec<Variable> = Vec::new();

        for atom in &rule.body {
            let converted = self.convert_rule_atom(atom, &mut abstract_variables, converter)?;
            body_atoms.push(converted);
        }
        for atom in &rule.head {
            let converted = self.convert_rule_atom(atom, &mut abstract_variables, converter)?;
            head_atoms.push(converted);
        }
        if restrict_to_named {
            // DL-safety: every abstract variable ranges over named individuals
            // (NormalizedRuleClausifier.clausify, the `restrictToNamed` block).
            for variable in &abstract_variables {
                body_atoms.push(Atom::create(
                    DLPredicate::AtomicConcept(AtomicConcept::internal_named().clone()),
                    vec![Term::Variable(variable.clone())],
                ));
            }
        }

        // The rule head is a disjunction: emit a single DLClause carrying all
        // head atoms (matching NormalizedRuleClausifier.clausify, which never
        // splits the head). An empty head yields a clash clause.
        Ok(DLClause::create(head_atoms, body_atoms))
    }

    /// Converts a single normalized SWRL atom to a `model::Atom`, recording the
    /// abstract (object) variables. Port of the per-atom
    /// `NormalizedRuleClausifier.visit(...)` methods. All arguments are assumed
    /// to be variables (RuleNormalizer guarantees this); `toVariable` panics on
    /// the Java side if not, so we error here.
    fn convert_rule_atom(
        &mut self,
        atom: &super::SwrlAtom,
        abstract_variables: &mut Vec<Variable>,
        converter: &mut DataRangeConverter,
    ) -> Result<Atom, String> {
        use horned_owl::model::{Atom as SwrlAtom, DArgument, IArgument};

        // toVariable(SWRLIArgument): all arguments must be variables after
        // normalization.
        fn to_variable_i(arg: &IArgument<A>) -> Result<Variable, String> {
            match arg {
                IArgument::Variable(v) => Ok(Variable::create(v.0.to_string())),
                IArgument::Individual(_) => Err(
                    "Internal error: all arguments in a SWRL rule should have been normalized to \
                     variables."
                        .into(),
                ),
            }
        }
        fn to_variable_d(arg: &DArgument<A>) -> Result<Variable, String> {
            match arg {
                DArgument::Variable(v) => Ok(Variable::create(v.0.to_string())),
                DArgument::Literal(_) => Err(
                    "Internal error: all arguments in a SWRL rule should have been normalized to \
                     variables."
                        .into(),
                ),
            }
        }

        match atom {
            // visit(SWRLClassAtom): predicate is a named class; arg is abstract.
            SwrlAtom::ClassAtom { pred, arg } => match pred {
                CE::Class(class) => {
                    let variable = to_variable_i(arg)?;
                    if !abstract_variables.contains(&variable) {
                        abstract_variables.push(variable.clone());
                    }
                    Ok(Atom::create(
                        DLPredicate::AtomicConcept(AtomicConcept::create(class.0.to_string())),
                        vec![Term::Variable(variable)],
                    ))
                }
                _ => Err("Internal error: SWRL rule class atoms should be normalized to contain \
                          only named classes, but this class atom has a complex concept."
                    .into()),
            },
            // visit(SWRLObjectPropertyAtom): both variables are abstract.
            SwrlAtom::ObjectPropertyAtom { pred, args } => {
                let v1 = to_variable_i(&args.0)?;
                let v2 = to_variable_i(&args.1)?;
                if !abstract_variables.contains(&v1) {
                    abstract_variables.push(v1.clone());
                }
                if !abstract_variables.contains(&v2) {
                    abstract_variables.push(v2.clone());
                }
                Ok(get_role_atom_object(
                    pred,
                    Term::Variable(v1),
                    Term::Variable(v2),
                ))
            }
            // visit(SWRLDataPropertyAtom): ONLY the subject (variable1) is
            // an abstract variable; the object (variable2) ranges over data
            // values and must NOT be restricted to named individuals.
            SwrlAtom::DataPropertyAtom { pred, args } => {
                let v1 = to_variable_d(&args.0)?;
                let v2 = to_variable_d(&args.1)?;
                if !abstract_variables.contains(&v1) {
                    abstract_variables.push(v1.clone());
                }
                Ok(get_role_atom_data(
                    pred,
                    Term::Variable(v1),
                    Term::Variable(v2),
                ))
            }
            // visit(SWRLDataRangeAtom): the variable is a data value, not added
            // to the abstract variables.
            SwrlAtom::DataRangeAtom { pred, arg } => {
                let variable = to_variable_d(arg)?;
                let literal_range = converter.convert_data_range(pred);
                Ok(Atom::create(
                    ldr_predicate(&literal_range),
                    vec![Term::Variable(variable)],
                ))
            }
            // visit(SWRLSameIndividualAtom): Equality. Not added to abstract
            // variables (matching NormalizedRuleClausifier).
            SwrlAtom::SameIndividualAtom(a1, a2) => {
                let v1 = to_variable_i(a1)?;
                let v2 = to_variable_i(a2)?;
                Ok(Atom::create(
                    DLPredicate::Equality,
                    vec![Term::Variable(v1), Term::Variable(v2)],
                ))
            }
            // visit(SWRLDifferentIndividualsAtom): Inequality.
            SwrlAtom::DifferentIndividualsAtom(a1, a2) => {
                let v1 = to_variable_i(a1)?;
                let v2 = to_variable_i(a2)?;
                Ok(Atom::create(
                    DLPredicate::Inequality,
                    vec![Term::Variable(v1), Term::Variable(v2)],
                ))
            }
            SwrlAtom::BuiltInAtom { .. } => Err(
                "Rules with SWRL built-in atoms are not yet supported.".into(),
            ),
        }
    }

    fn clausify(
        &mut self,
        object: &CE,
        positive_facts: &mut HashSet<Atom>,
        converter: &mut DataRangeConverter,
    ) {
        match object {
            CE::Class(c) => {
                self.head_atoms.push(Atom::create(
                    DLPredicate::AtomicConcept(AtomicConcept::create(c.0.to_string())),
                    vec![x()],
                ));
            }
            CE::ObjectIntersectionOf(_) | CE::ObjectUnionOf(_) => {
                panic!("Internal error: invalid normal form.")
            }
            CE::ObjectComplementOf(description) => match &**description {
                CE::ObjectHasSelf(ope) => {
                    self.body_atoms.push(get_role_atom_object(ope, x(), x()));
                }
                CE::ObjectOneOf(individuals) if individuals.len() == 1 => {
                    let concept = self.get_concept_for_nominal(&individuals[0], positive_facts);
                    self.body_atoms
                        .push(Atom::create(DLPredicate::AtomicConcept(concept), vec![x()]));
                }
                CE::Class(c) => {
                    self.body_atoms.push(Atom::create(
                        DLPredicate::AtomicConcept(AtomicConcept::create(c.0.to_string())),
                        vec![x()],
                    ));
                }
                _ => panic!("Internal error: invalid normal form."),
            },
            CE::ObjectOneOf(individuals) => {
                for individual in individuals {
                    let z = self.next_z();
                    let concept = self.get_concept_for_nominal(individual, positive_facts);
                    self.head_atoms.push(Atom::create(
                        DLPredicate::Equality,
                        vec![x(), Term::Variable(z.clone())],
                    ));
                    self.body_atoms.push(Atom::create(
                        DLPredicate::AtomicConcept(concept),
                        vec![Term::Variable(z)],
                    ));
                }
            }
            CE::ObjectSomeValuesFrom { ope, bce } => {
                if let CE::ObjectOneOf(individuals) = &**bce {
                    for individual in individuals {
                        let z = self.next_z();
                        let concept = self.get_concept_for_nominal(individual, positive_facts);
                        self.body_atoms.push(Atom::create(
                            DLPredicate::AtomicConcept(concept),
                            vec![Term::Variable(z.clone())],
                        ));
                        self.head_atoms
                            .push(get_role_atom_object(ope, x(), Term::Variable(z)));
                    }
                } else {
                    let to_concept = get_literal_concept(bce);
                    let on_role = get_role(ope);
                    let at_least = AtLeastConcept::create(1, on_role, to_concept);
                    if !at_least.is_always_false() {
                        self.head_atoms.push(Atom::create(
                            DLPredicate::AtLeastConcept(at_least),
                            vec![x()],
                        ));
                    }
                }
            }
            CE::ObjectAllValuesFrom { ope, bce } => {
                let y = self.next_y();
                self.body_atoms
                    .push(get_role_atom_object(ope, x(), Term::Variable(y.clone())));
                match &**bce {
                    CE::Class(c) => {
                        let concept = AtomicConcept::create(c.0.to_string());
                        if !concept.is_always_false() {
                            self.head_atoms.push(Atom::create(
                                DLPredicate::AtomicConcept(concept),
                                vec![Term::Variable(y)],
                            ));
                        }
                    }
                    CE::ObjectOneOf(individuals) => {
                        for individual in individuals {
                            let z_ind = self.next_z();
                            let concept =
                                self.get_concept_for_nominal(individual, positive_facts);
                            self.body_atoms.push(Atom::create(
                                DLPredicate::AtomicConcept(concept),
                                vec![Term::Variable(z_ind.clone())],
                            ));
                            self.head_atoms.push(Atom::create(
                                DLPredicate::Equality,
                                vec![Term::Variable(y.clone()), Term::Variable(z_ind)],
                            ));
                        }
                    }
                    CE::ObjectComplementOf(operand) => match &**operand {
                        CE::Class(c) => {
                            let concept = AtomicConcept::create(c.0.to_string());
                            if !concept.is_always_true() {
                                self.body_atoms.push(Atom::create(
                                    DLPredicate::AtomicConcept(concept),
                                    vec![Term::Variable(y)],
                                ));
                            }
                        }
                        CE::ObjectOneOf(individuals) if individuals.len() == 1 => {
                            let concept =
                                self.get_concept_for_nominal(&individuals[0], positive_facts);
                            self.body_atoms.push(Atom::create(
                                DLPredicate::AtomicConcept(concept),
                                vec![Term::Variable(y)],
                            ));
                        }
                        _ => panic!("Internal error: invalid normal form."),
                    },
                    _ => panic!("Internal error: invalid normal form."),
                }
            }
            CE::ObjectHasValue { .. } => panic!("Internal error: invalid normal form."),
            CE::ObjectHasSelf(ope) => {
                self.head_atoms.push(get_role_atom_object(ope, x(), x()));
            }
            CE::ObjectMinCardinality { n, ope, bce } => {
                let to_concept = get_literal_concept(bce);
                let on_role = get_role(ope);
                let at_least = AtLeastConcept::create(*n as i32, on_role, to_concept);
                if !at_least.is_always_false() {
                    self.head_atoms.push(Atom::create(
                        DLPredicate::AtLeastConcept(at_least),
                        vec![x()],
                    ));
                }
            }
            CE::ObjectMaxCardinality { n, ope, bce } => {
                self.ensure_y_not_zero();
                let (is_positive, atomic_concept) = match &**bce {
                    CE::Class(c) => {
                        let concept = AtomicConcept::create(c.0.to_string());
                        (true, if concept.is_always_true() { None } else { Some(concept) })
                    }
                    CE::ObjectComplementOf(internal) => match &**internal {
                        CE::Class(c) => {
                            let concept = AtomicConcept::create(c.0.to_string());
                            (false, if concept.is_always_false() { None } else { Some(concept) })
                        }
                        _ => panic!("Internal error: Invalid ontology normal form."),
                    },
                    _ => panic!("Internal error: Invalid ontology normal form."),
                };
                let on_role = get_role(ope);
                let to_concept = get_literal_concept(bce);
                let annotated_equality =
                    AnnotatedEquality::create(*n as i32, on_role, to_concept);
                let count = (*n as usize) + 1;
                let mut y_vars: Vec<Variable> = Vec::with_capacity(count);
                for _ in 0..count {
                    let yv = self.next_y();
                    self.body_atoms
                        .push(get_role_atom_object(ope, x(), Term::Variable(yv.clone())));
                    if let Some(concept) = &atomic_concept {
                        let atom = Atom::create(
                            DLPredicate::AtomicConcept(concept.clone()),
                            vec![Term::Variable(yv.clone())],
                        );
                        if is_positive {
                            self.body_atoms.push(atom);
                        } else {
                            self.head_atoms.push(atom);
                        }
                    }
                    y_vars.push(yv);
                }
                if y_vars.len() > 2 {
                    for i in 0..y_vars.len() - 1 {
                        self.body_atoms.push(Atom::create(
                            DLPredicate::NodeIdLessEqualThan,
                            vec![
                                Term::Variable(y_vars[i].clone()),
                                Term::Variable(y_vars[i + 1].clone()),
                            ],
                        ));
                    }
                    let args: Vec<Term> =
                        y_vars.iter().cloned().map(Term::Variable).collect();
                    self.body_atoms.push(Atom::create(
                        DLPredicate::NodeIDsAscendingOrEqual(NodeIDsAscendingOrEqual::create(
                            y_vars.len(),
                        )),
                        args,
                    ));
                }
                for i in 0..y_vars.len() {
                    for j in (i + 1)..y_vars.len() {
                        self.head_atoms.push(Atom::create(
                            DLPredicate::AnnotatedEquality(annotated_equality.clone()),
                            vec![
                                Term::Variable(y_vars[i].clone()),
                                Term::Variable(y_vars[j].clone()),
                                x(),
                            ],
                        ));
                    }
                }
            }
            CE::ObjectExactCardinality { .. } => {
                panic!("Internal error: invalid normal form.")
            }
            CE::DataSomeValuesFrom { dp, dr } => {
                if !is_bottom_data_property(dp) {
                    let atomic_role = get_atomic_role_data(dp);
                    let literal_range = converter.convert_data_range(dr);
                    let at_least =
                        AtLeastDataRange::create(1, Role::AtomicRole(atomic_role), literal_range);
                    if !at_least.is_always_false() {
                        self.head_atoms.push(Atom::create(
                            DLPredicate::AtLeastDataRange(at_least),
                            vec![x()],
                        ));
                    }
                }
            }
            CE::DataAllValuesFrom { dp, dr } => {
                let literal_range = converter.convert_data_range(dr);
                if is_top_data_property(dp) && literal_range.is_always_false() {
                    return;
                }
                let y = self.next_y();
                self.body_atoms
                    .push(get_role_atom_data(dp, x(), Term::Variable(y.clone())));
                if literal_range.is_negated_internal_datatype() {
                    if let Some(negated_range) = as_internal_datatype_negation(&literal_range) {
                        if !negated_range.is_always_true() {
                            self.body_atoms.push(Atom::create(
                                DLPredicate::InternalDatatype(negated_range),
                                vec![Term::Variable(y)],
                            ));
                        }
                    }
                } else if !literal_range.is_always_false() {
                    self.head_atoms.push(Atom::create(
                        ldr_predicate(&literal_range),
                        vec![Term::Variable(y)],
                    ));
                }
            }
            CE::DataHasValue { .. } => panic!("Internal error: Invalid normal form."),
            CE::DataMinCardinality { n, dp, dr } => {
                if !is_bottom_data_property(dp) || *n == 0 {
                    let atomic_role = get_atomic_role_data(dp);
                    let literal_range = converter.convert_data_range(dr);
                    let at_least = AtLeastDataRange::create(
                        *n as i32,
                        Role::AtomicRole(atomic_role),
                        literal_range,
                    );
                    if !at_least.is_always_false() {
                        self.head_atoms.push(Atom::create(
                            DLPredicate::AtLeastDataRange(at_least),
                            vec![x()],
                        ));
                    }
                }
            }
            CE::DataMaxCardinality { n, dp, dr } => {
                let negated_data_range = converter.convert_data_range(dr).get_negation();
                self.ensure_y_not_zero();
                let count = (*n as usize) + 1;
                let mut y_vars: Vec<Variable> = Vec::with_capacity(count);
                for _ in 0..count {
                    let yv = self.next_y();
                    self.body_atoms
                        .push(get_role_atom_data(dp, x(), Term::Variable(yv.clone())));
                    if negated_data_range.is_negated_internal_datatype() {
                        if let Some(negated) = as_internal_datatype_negation(&negated_data_range) {
                            if !negated.is_always_true() {
                                self.body_atoms.push(Atom::create(
                                    DLPredicate::InternalDatatype(negated),
                                    vec![Term::Variable(yv.clone())],
                                ));
                            }
                        }
                    } else if !negated_data_range.is_always_false() {
                        self.head_atoms.push(Atom::create(
                            ldr_predicate(&negated_data_range),
                            vec![Term::Variable(yv.clone())],
                        ));
                    }
                    y_vars.push(yv);
                }
                for i in 0..y_vars.len() {
                    for j in (i + 1)..y_vars.len() {
                        self.head_atoms.push(Atom::create(
                            DLPredicate::Equality,
                            vec![
                                Term::Variable(y_vars[i].clone()),
                                Term::Variable(y_vars[j].clone()),
                            ],
                        ));
                    }
                }
            }
            CE::DataExactCardinality { .. } => {
                panic!("Internal error: invalid normal form.")
            }
        }
    }
}

fn is_bottom_data_property(dp: &DataProperty<A>) -> bool {
    dp.0.to_string() == AtomicRole::bottom_data_role().iri()
}
fn is_top_data_property(dp: &DataProperty<A>) -> bool {
    dp.0.to_string() == AtomicRole::top_data_role().iri()
}

fn y() -> Term {
    Term::Variable(var("Y"))
}

// ---------------------------------------------------------------------------
// NormalizedDataRangeAxiomClausifier
// ---------------------------------------------------------------------------

#[derive(Default)]
struct DataRangeClausifier {
    head_atoms: Vec<Atom>,
    body_atoms: Vec<Atom>,
    y_index: u32,
}

impl DataRangeClausifier {
    fn get_dl_clause(&mut self) -> DLClause {
        let clause = DLClause::create(
            std::mem::take(&mut self.head_atoms),
            std::mem::take(&mut self.body_atoms),
        );
        self.y_index = 0;
        clause
    }

    fn clausify(
        &mut self,
        object: &DR,
        converter: &mut DataRangeConverter,
        defined_datatype_iris: &HashSet<String>,
    ) {
        match object {
            DR::Datatype(_) | DR::DataOneOf(_) | DR::DatatypeRestriction(..) => {
                let literal_range = converter.convert_data_range(object);
                self.head_atoms
                    .push(Atom::create(ldr_predicate(&literal_range), vec![x()]));
            }
            DR::DataComplementOf(inner) => {
                if let DR::Datatype(dt) = &**inner {
                    let iri = dt.0.to_string();
                    if Prefixes::is_internal_iri(&iri) || defined_datatype_iris.contains(&iri) {
                        self.body_atoms.push(Atom::create(
                            DLPredicate::InternalDatatype(InternalDatatype::create(iri)),
                            vec![x()],
                        ));
                        return;
                    }
                }
                let literal_range = converter.convert_data_range(object);
                if literal_range.is_negated_internal_datatype() {
                    if let Some(negated) = as_internal_datatype_negation(&literal_range) {
                        if !negated.is_always_true() {
                            self.body_atoms.push(Atom::create(
                                DLPredicate::InternalDatatype(negated),
                                vec![x()],
                            ));
                        }
                    }
                } else if !literal_range.is_always_false() {
                    self.head_atoms
                        .push(Atom::create(ldr_predicate(&literal_range), vec![x()]));
                }
            }
            DR::DataIntersectionOf(_) | DR::DataUnionOf(_) => {
                panic!("Internal error: invalid normal form.")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// FactClausifier
// ---------------------------------------------------------------------------

fn clausify_fact(
    fact: &Fact,
    converter: &mut DataRangeConverter,
    positive_facts: &mut HashSet<Atom>,
    negative_facts: &mut HashSet<Atom>,
) -> Result<(), String> {
    match fact {
        Fact::SameIndividual(individuals) => {
            for i in 0..individuals.len().saturating_sub(1) {
                positive_facts.insert(Atom::create(
                    DLPredicate::Equality,
                    vec![
                        Term::Individual(get_individual(&individuals[i])),
                        Term::Individual(get_individual(&individuals[i + 1])),
                    ],
                ));
            }
        }
        Fact::DifferentIndividuals(individuals) => {
            for i in 0..individuals.len() {
                for j in (i + 1)..individuals.len() {
                    positive_facts.insert(Atom::create(
                        DLPredicate::Inequality,
                        vec![
                            Term::Individual(get_individual(&individuals[i])),
                            Term::Individual(get_individual(&individuals[j])),
                        ],
                    ));
                }
            }
        }
        Fact::ClassAssertion { class_expression, individual } => {
            let ind = || Term::Individual(get_individual(individual));
            match class_expression {
                CE::Class(c) => {
                    positive_facts.insert(Atom::create(
                        DLPredicate::AtomicConcept(AtomicConcept::create(c.0.to_string())),
                        vec![ind()],
                    ));
                }
                CE::ObjectComplementOf(operand) => match &**operand {
                    CE::Class(c) => {
                        negative_facts.insert(Atom::create(
                            DLPredicate::AtomicConcept(AtomicConcept::create(c.0.to_string())),
                            vec![ind()],
                        ));
                    }
                    CE::ObjectHasSelf(ope) => {
                        negative_facts.insert(get_role_atom_object(ope, ind(), ind()));
                    }
                    _ => panic!("Internal error: invalid normal form."),
                },
                CE::ObjectHasSelf(ope) => {
                    positive_facts.insert(get_role_atom_object(ope, ind(), ind()));
                }
                _ => panic!("Internal error: invalid normal form."),
            }
        }
        Fact::ObjectPropertyAssertion { ope, from, to } => {
            positive_facts.insert(get_role_atom_object(
                ope,
                Term::Individual(get_individual(from)),
                Term::Individual(get_individual(to)),
            ));
        }
        Fact::NegativeObjectPropertyAssertion { ope, from, to } => {
            negative_facts.insert(get_role_atom_object(
                ope,
                Term::Individual(get_individual(from)),
                Term::Individual(get_individual(to)),
            ));
        }
        Fact::DataPropertyAssertion { dp, from, to } => {
            let target = converter.convert_literal(to)?;
            positive_facts.insert(get_role_atom_data(
                dp,
                Term::Individual(get_individual(from)),
                Term::Constant(target),
            ));
        }
        Fact::NegativeDataPropertyAssertion { dp, from, to } => {
            let target = converter.convert_literal(to)?;
            negative_facts.insert(get_role_atom_data(
                dp,
                Term::Individual(get_individual(from)),
                Term::Constant(target),
            ));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// OWLClausification (the clausify entry point)
// ---------------------------------------------------------------------------

pub struct OWLClausification {
    configuration: Configuration,
}

impl OWLClausification {
    pub fn new(configuration: Configuration) -> OWLClausification {
        OWLClausification { configuration }
    }

    pub fn clausify(
        &self,
        ontology_iri: &str,
        axioms: &OWLAxioms,
        axioms_expressivity: &OWLAxiomsExpressivity,
    ) -> Result<DLOntology, String> {
        // Complex object-property inclusions (role chains / transitivity) are
        // not clausified directly: the `ObjectPropertyInclusionManager` rewrites
        // them into concept inclusions over automaton-state concepts before this
        // point. Only the simple inclusions are emitted as role-inclusion clauses
        // below.
        // Insertion-ordered, mirroring Java's `LinkedHashSet<DLClause>`: this keeps
        // rule compilation and hyperresolution firing order deterministic.
        let mut dl_clauses: indexmap::IndexSet<DLClause> = indexmap::IndexSet::new();
        let mut positive_facts: HashSet<Atom> = HashSet::new();
        let mut negative_facts: HashSet<Atom> = HashSet::new();

        for inclusion in &axioms.simple_object_property_inclusions {
            let sub = get_role_atom_object(&inclusion[0], x(), y());
            let sup = get_role_atom_object(&inclusion[1], x(), y());
            dl_clauses.insert(DLClause::create(vec![sup], vec![sub]));
        }
        for inclusion in &axioms.data_property_inclusions {
            let sub = get_role_atom_data(&inclusion[0], x(), y());
            let sup = get_role_atom_data(&inclusion[1], x(), y());
            dl_clauses.insert(DLClause::create(vec![sup], vec![sub]));
        }
        for ope in &axioms.asymmetric_object_properties {
            let role_atom = get_role_atom_object(ope, x(), y());
            let inverse_role_atom = get_role_atom_object(ope, y(), x());
            dl_clauses.insert(DLClause::create(vec![], vec![role_atom, inverse_role_atom]));
        }
        for ope in &axioms.reflexive_object_properties {
            let role_atom = get_role_atom_object(ope, x(), x());
            let body = Atom::create(
                DLPredicate::AtomicConcept(AtomicConcept::thing().clone()),
                vec![x()],
            );
            dl_clauses.insert(DLClause::create(vec![role_atom], vec![body]));
        }
        for ope in &axioms.irreflexive_object_properties {
            let role_atom = get_role_atom_object(ope, x(), x());
            dl_clauses.insert(DLClause::create(vec![], vec![role_atom]));
        }
        for properties in &axioms.disjoint_object_properties {
            for i in 0..properties.len() {
                for j in (i + 1)..properties.len() {
                    let atom_i = get_role_atom_object(&properties[i], x(), y());
                    let atom_j = get_role_atom_object(&properties[j], x(), y());
                    dl_clauses.insert(DLClause::create(vec![], vec![atom_i, atom_j]));
                }
            }
        }
        if axioms
            .data_properties
            .iter()
            .any(|dp| dp.0.to_string() == AtomicRole::bottom_data_role().iri())
        {
            let body = Atom::create(
                DLPredicate::AtomicRole(AtomicRole::bottom_data_role().clone()),
                vec![x(), y()],
            );
            dl_clauses.insert(DLClause::create(vec![], vec![body]));
        }
        for properties in &axioms.disjoint_data_properties {
            for i in 0..properties.len() {
                for j in (i + 1)..properties.len() {
                    let atom_i = get_role_atom_data(&properties[i], x(), y());
                    let atom_j = get_role_atom_data(&properties[j], x(), Term::Variable(var("Z")));
                    let atom_ij = Atom::create(
                        DLPredicate::Inequality,
                        vec![y(), Term::Variable(var("Z"))],
                    );
                    dl_clauses.insert(DLClause::create(vec![atom_ij], vec![atom_i, atom_j]));
                }
            }
        }

        let mut converter = DataRangeConverter::new(
            self.configuration.ignore_unsupported_datatypes,
            &axioms.defined_datatype_iris,
        );

        let mut clausifier = AxiomClausifier::default();
        for inclusion in &axioms.concept_inclusions {
            for description in inclusion {
                clausifier.clausify(description, &mut positive_facts, &mut converter);
            }
            let clause = clausifier.get_dl_clause();
            dl_clauses.insert(clause.get_safe_version(DLPredicate::AtomicConcept(
                AtomicConcept::thing().clone(),
            )));
        }

        let mut data_range_clausifier = DataRangeClausifier::default();
        for inclusion in &axioms.data_range_inclusions {
            for description in inclusion {
                data_range_clausifier.clausify(
                    description,
                    &mut converter,
                    &axioms.defined_datatype_iris,
                );
            }
            let clause = data_range_clausifier.get_dl_clause();
            dl_clauses.insert(clause.get_safe_version(DLPredicate::InternalDatatype(
                InternalDatatype::rdfs_literal().clone(),
            )));
        }

        for has_key in &axioms.has_keys {
            dl_clauses.insert(clausify_key(has_key));
        }

        // Java's `m_facts` and `m_rules` are `HashSet`s, so equal entries never
        // produce duplicate clauses. The Rust container keeps insertion order in
        // a `Vec`; deduplicate here (preserving order) to match Java.
        let mut seen_facts: HashSet<&crate::structural::owl_axioms::Fact> = HashSet::new();
        let mut unique_facts: Vec<&crate::structural::owl_axioms::Fact> = Vec::new();
        for fact in &axioms.facts {
            if seen_facts.insert(fact) {
                unique_facts.push(fact);
            }
        }
        let mut seen_rules: HashSet<&crate::structural::owl_axioms::DisjunctiveRule> =
            HashSet::new();
        let mut unique_rules: Vec<&crate::structural::owl_axioms::DisjunctiveRule> = Vec::new();
        for rule in &axioms.rules {
            if seen_rules.insert(rule) {
                unique_rules.push(rule);
            }
        }

        for fact in unique_facts.iter().copied() {
            clausify_fact(fact, &mut converter, &mut positive_facts, &mut negative_facts)?;
        }

        // SWRL rules (already fully normalized by OWLNormalization.RuleNormalizer).
        for rule in unique_rules.iter().copied() {
            let clause = clausifier.clausify_rule(rule, &mut converter)?;
            dl_clauses.insert(clause);
        }

        // Vocabulary.
        let mut atomic_concepts: BTreeSet<AtomicConcept> = BTreeSet::new();
        for owl_class in &axioms.classes {
            atomic_concepts.insert(AtomicConcept::create(owl_class.0.to_string()));
        }
        let mut individuals: BTreeSet<Individual> = BTreeSet::new();
        let tag_named = !axioms.has_keys.is_empty() || !axioms.rules.is_empty();
        // The named-individual vocabulary is built solely from `m_namedIndividuals`
        // (the ontology signature plus fresh SWRL-rule individuals), matching
        // `OWLClausification.java:243-251`. Individuals introduced only into
        // generated facts (e.g. OPIM `internal:nom#` nominal representatives) are
        // NOT part of this vocabulary and are not tagged with internal:named.
        let mut named_iris: BTreeSet<String> = BTreeSet::new();
        for owl_individual in &axioms.named_individuals {
            named_iris.insert(owl_individual.0.to_string());
        }
        for iri in &named_iris {
            let individual = Individual::create(iri.clone());
            individuals.insert(individual.clone());
            if tag_named {
                positive_facts.insert(Atom::create(
                    DLPredicate::AtomicConcept(AtomicConcept::internal_named().clone()),
                    vec![Term::Individual(individual)],
                ));
            }
        }
        let mut atomic_object_roles: BTreeSet<AtomicRole> = BTreeSet::new();
        for object_property in &axioms.object_properties {
            atomic_object_roles.insert(AtomicRole::create(object_property.0.to_string()));
        }
        let mut complex_object_roles: HashSet<Role> = HashSet::new();
        for ope in &axioms.complex_object_property_expressions {
            complex_object_roles.insert(get_role(ope));
        }
        let mut atomic_data_roles: BTreeSet<AtomicRole> = BTreeSet::new();
        for data_property in &axioms.data_properties {
            atomic_data_roles.insert(AtomicRole::create(data_property.0.to_string()));
        }

        // Reject an ontology using an unsupported datatype, as HermiT throws
        // UnsupportedDatatypeException by default (unless ignore_unsupported_datatypes).
        if let Some(datatype) = &converter.unsupported_datatype {
            return Err(format!(
                "Unsupported datatype '{datatype}': it is not a recognized OWL 2 datatype and is \
                 not defined by a DatatypeDefinition. (HermiT rejects such ontologies unless \
                 unsupported datatypes are ignored.)"
            ));
        }
        // Reject an unsupported facet, as HermiT throws UnsupportedFacetException.
        if let Some((datatype, facet)) = &converter.unsupported_facet {
            return Err(format!(
                "Unsupported facet '{facet}' on datatype '{datatype}': HermiT's datatype \
                 registry does not support this facet for this datatype."
            ));
        }
        // Reject a literal (inside a data range) with a malformed lexical form of a
        // supported datatype, or an unsupported datatype, as HermiT rethrows
        // MalformedLiteralException / UnsupportedDatatypeException from parseLiteral.
        if let Some(message) = converter.literal_error.take() {
            return Err(message);
        }
        let all_unknown_datatype_restrictions =
            std::mem::take(&mut converter.all_unknown_datatype_restrictions);
        let defined_datatype_iris: HashSet<String> = axioms.defined_datatype_iris.clone();

        Ok(DLOntology::new(
            ontology_iri,
            dl_clauses,
            positive_facts,
            negative_facts,
            Some(atomic_concepts),
            Some(atomic_object_roles),
            Some(complex_object_roles),
            Some(atomic_data_roles),
            Some(all_unknown_datatype_restrictions),
            Some(defined_datatype_iris),
            Some(individuals),
            axioms_expressivity.has_inverse_roles,
            axioms_expressivity.has_at_most_restrictions,
            axioms_expressivity.has_nominals,
            axioms_expressivity.has_datatypes,
        ))
    }
}

fn clausify_key(object: &HasKeyAxiom) -> DLClause {
    use horned_owl::model::PropertyExpression as PE;
    let mut head_atoms: Vec<Atom> = Vec::new();
    let mut body_atoms: Vec<Atom> = Vec::new();
    let x1 = || Term::Variable(var("X1"));
    let x2 = || Term::Variable(var("X2"));
    head_atoms.push(Atom::create(DLPredicate::Equality, vec![x1(), x2()]));
    body_atoms.push(Atom::create(
        DLPredicate::AtomicConcept(AtomicConcept::internal_named().clone()),
        vec![x1()],
    ));
    body_atoms.push(Atom::create(
        DLPredicate::AtomicConcept(AtomicConcept::internal_named().clone()),
        vec![x2()],
    ));
    match &object.class_expression {
        CE::Class(c) => {
            if !c.is_thing() {
                body_atoms.push(Atom::create(
                    DLPredicate::AtomicConcept(AtomicConcept::create(c.0.to_string())),
                    vec![x1()],
                ));
                body_atoms.push(Atom::create(
                    DLPredicate::AtomicConcept(AtomicConcept::create(c.0.to_string())),
                    vec![x2()],
                ));
            }
        }
        CE::ObjectComplementOf(internal) => match &**internal {
            CE::Class(c) => {
                head_atoms.push(Atom::create(
                    DLPredicate::AtomicConcept(AtomicConcept::create(c.0.to_string())),
                    vec![x1()],
                ));
                head_atoms.push(Atom::create(
                    DLPredicate::AtomicConcept(AtomicConcept::create(c.0.to_string())),
                    vec![x2()],
                ));
            }
            _ => panic!("Internal error: invalid normal form."),
        },
        _ => panic!("Internal error: invalid normal form."),
    }
    let mut y_index = 1;
    for pe in &object.property_expressions {
        if let PE::ObjectPropertyExpression(ope) = pe {
            let y = Term::Variable(var(&format!("Y{y_index}")));
            y_index += 1;
            body_atoms.push(get_role_atom_object(ope, x1(), y.clone()));
            body_atoms.push(get_role_atom_object(ope, x2(), y.clone()));
            body_atoms.push(Atom::create(
                DLPredicate::AtomicConcept(AtomicConcept::internal_named().clone()),
                vec![y],
            ));
        }
    }
    for pe in &object.property_expressions {
        if let PE::DataProperty(dp) = pe {
            let y = Term::Variable(var(&format!("Y{y_index}")));
            y_index += 1;
            body_atoms.push(get_role_atom_data(dp, x1(), y.clone()));
            let y2 = Term::Variable(var(&format!("Y{y_index}")));
            y_index += 1;
            body_atoms.push(get_role_atom_data(dp, x2(), y2.clone()));
            head_atoms.push(Atom::create(DLPredicate::Inequality, vec![y, y2]));
        }
    }
    DLClause::create(head_atoms, body_atoms)
}

#[cfg(test)]
mod tests {
    //! End-to-end regression tests for the SWRL rule pipeline: DataProperty subject
    //! DL-safety, and RuleNormalizer / Rule2FactConverter behaviour.
    use horned_owl::model::{
        Atom as SwrlAtom, Build, Class, Component, DArgument, DataProperty, DisjointClasses,
        IArgument, Individual, Literal, MutableOntology, NamedIndividual, ObjectProperty,
        ObjectPropertyExpression, Rule,
    };
    use horned_owl::ontology::set::SetOntology;

    use crate::reasoner::is_ontology_consistent;
    use crate::structural::{ClassExpr as CE, A};

    fn build() -> Build<A> {
        Build::new_arc()
    }
    fn class(b: &Build<A>, iri: &str) -> Class<A> {
        b.class(iri)
    }
    fn dprop(b: &Build<A>, iri: &str) -> DataProperty<A> {
        b.data_property(iri)
    }
    fn ind(b: &Build<A>, iri: &str) -> Individual<A> {
        Individual::Named(b.named_individual(iri))
    }
    fn named(b: &Build<A>, iri: &str) -> NamedIndividual<A> {
        b.named_individual(iri)
    }
    fn ivar(b: &Build<A>, name: &str) -> IArgument<A> {
        IArgument::Variable(b.variable(name))
    }
    fn dvar(b: &Build<A>, name: &str) -> DArgument<A> {
        DArgument::Variable(b.variable(name))
    }

    /// In `dp(?x,?y) -> C(?x)`, only the subject `?x` is restricted to
    /// named individuals. If the object `?y` were also guarded with
    /// `internal:named`, the data-value binding could never satisfy it and the
    /// rule would never fire -- so the disjointness clash below would be missed
    /// and the ontology would be wrongly reported consistent.
    #[test]
    fn data_property_subject_is_dl_safe_object_is_not() {
        let b = build();
        let c = class(&b, "http://ex/C");
        let d = class(&b, "http://ex/D");
        let dp = dprop(&b, "http://ex/dp");
        let a = ind(&b, "http://ex/a");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareDataProperty(horned_owl::model::DeclareDataProperty(dp.clone())));
        // dp(a, "5")
        o.insert(Component::DataPropertyAssertion(horned_owl::model::DataPropertyAssertion {
            dp: dp.clone(),
            from: a.clone(),
            to: Literal::Simple { literal: "5".to_string() },
        }));
        // D(a)
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: c_expr(&d),
            i: a.clone(),
        }));
        // DisjointClasses(C, D)
        o.insert(Component::DisjointClasses(DisjointClasses(vec![c_expr(&c), c_expr(&d)])));
        // Rule: dp(?x,?y) -> C(?x)
        o.insert(Component::Rule(Rule {
            body: vec![SwrlAtom::DataPropertyAtom {
                pred: dp.clone(),
                args: (dvar(&b, "urn:x"), dvar(&b, "urn:y")),
            }],
            head: vec![SwrlAtom::ClassAtom { pred: c_expr(&c), arg: ivar(&b, "urn:x") }],
        }));

        // The rule fires (dp(a,_) with a named) deriving C(a); C and D are
        // disjoint and D(a) holds, so the ontology is INCONSISTENT.
        let consistent = is_ontology_consistent(&o).expect("pipeline should accept the rule");
        assert!(!consistent, "F-1: data-property rule must fire and clash on disjointness");
    }

    /// A rule whose body uses an individual constant and a SameIndividual
    /// atom. RuleNormalizer must: (a) ground `a` to a fresh variable bound by an
    /// ObjectOneOf body atom, and (b) treat `SameIndividual(?x, a)` in the body
    /// as variable unification (NOT a body Equality atom). The resulting rule
    /// `C(a)` should make the ontology inconsistent given `not C(a)`.
    #[test]
    fn individual_constant_and_body_same_individual() {
        let b = build();
        let c = class(&b, "http://ex/C");
        let p = ObjectProperty::from(b.object_property("http://ex/p"));
        let a = ind(&b, "http://ex/a");
        let e = ind(&b, "http://ex/e");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareObjectProperty(horned_owl::model::DeclareObjectProperty(
            p.clone(),
        )));
        // p(e, a)
        o.insert(Component::ObjectPropertyAssertion(horned_owl::model::ObjectPropertyAssertion {
            ope: ObjectPropertyExpression::ObjectProperty(p.clone()),
            from: e.clone(),
            to: a.clone(),
        }));
        // not C(a)  (ObjectComplementOf(C) assertion on a)
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::ObjectComplementOf(Box::new(c_expr(&c))),
            i: a.clone(),
        }));
        // Rule: p(?z, a) ^ sameAs(?z, ?z') ^ p(?z', ?w) -> C(?w)
        // The SameIndividual body atom unifies ?z and ?z'. With p(e,a) we get
        // ?z=?z'=e, ?w=a, deriving C(a) -- contradicting not C(a).
        o.insert(Component::Rule(Rule {
            body: vec![
                SwrlAtom::ObjectPropertyAtom {
                    pred: ObjectPropertyExpression::ObjectProperty(p.clone()),
                    args: (ivar(&b, "urn:z"), IArgument::Individual(a.clone())),
                },
                SwrlAtom::SameIndividualAtom(ivar(&b, "urn:z"), ivar(&b, "urn:z2")),
                SwrlAtom::ObjectPropertyAtom {
                    pred: ObjectPropertyExpression::ObjectProperty(p.clone()),
                    args: (ivar(&b, "urn:z2"), ivar(&b, "urn:w")),
                },
            ],
            head: vec![SwrlAtom::ClassAtom { pred: c_expr(&c), arg: ivar(&b, "urn:w") }],
        }));

        let consistent = is_ontology_consistent(&o).expect("pipeline should accept the rule");
        assert!(
            !consistent,
            "F-2: individual constant grounding + body SameIndividual unification must derive C(a)"
        );
    }

    /// A rule body data-property atom with a literal object. HermiT accepts
    /// this (RuleNormalizer turns it into a DataHasValue class atom). Here
    /// `dp(?x,"7") -> C(?x)` plus `dp(a,"7")` and `not C(a)` must be inconsistent.
    #[test]
    fn data_property_literal_object_in_body() {
        let b = build();
        let c = class(&b, "http://ex/C");
        let dp = dprop(&b, "http://ex/dp");
        let a = ind(&b, "http://ex/a");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::DeclareDataProperty(horned_owl::model::DeclareDataProperty(dp.clone())));
        o.insert(Component::DataPropertyAssertion(horned_owl::model::DataPropertyAssertion {
            dp: dp.clone(),
            from: a.clone(),
            to: Literal::Simple { literal: "7".to_string() },
        }));
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::ObjectComplementOf(Box::new(c_expr(&c))),
            i: a.clone(),
        }));
        // Rule: dp(?x, "7") -> C(?x)
        o.insert(Component::Rule(Rule {
            body: vec![SwrlAtom::DataPropertyAtom {
                pred: dp.clone(),
                args: (dvar(&b, "urn:x"), DArgument::Literal(Literal::Simple {
                    literal: "7".to_string(),
                })),
            }],
            head: vec![SwrlAtom::ClassAtom { pred: c_expr(&c), arg: ivar(&b, "urn:x") }],
        }));

        let consistent = is_ontology_consistent(&o)
            .expect("pipeline should accept a rule with a literal data-property object");
        assert!(!consistent, "F-2: literal-object data-property body atom must fire the rule");
    }

    /// An empty-body rule is converted to a fact by Rule2FactConverter.
    /// `() -> C(a)` plus `not C(a)` is inconsistent (the head class assertion is
    /// added as an ABox fact, not a clause guarded by named variables).
    #[test]
    fn empty_body_rule_becomes_fact() {
        let b = build();
        let c = class(&b, "http://ex/C");
        let a = named(&b, "http://ex/a");

        let mut o: SetOntology<A> = SetOntology::new();
        o.insert(Component::ClassAssertion(horned_owl::model::ClassAssertion {
            ce: CE::ObjectComplementOf(Box::new(c_expr(&c))),
            i: Individual::Named(a.clone()),
        }));
        // () -> C(a)
        o.insert(Component::Rule(Rule {
            body: vec![],
            head: vec![SwrlAtom::ClassAtom {
                pred: c_expr(&c),
                arg: IArgument::Individual(Individual::Named(a.clone())),
            }],
        }));

        let consistent = is_ontology_consistent(&o).expect("empty-body rule should become a fact");
        assert!(!consistent, "F-2: empty-body rule must assert C(a) as a fact");
    }

    fn c_expr(c: &Class<A>) -> CE {
        CE::Class(c.clone())
    }

    // ---- Literal validation at clausification ----

    const XSD_INTEGER: &str = "http://www.w3.org/2001/XMLSchema#integer";
    const XSD_NON_NEGATIVE_INTEGER: &str = "http://www.w3.org/2001/XMLSchema#nonNegativeInteger";

    // A malformed lexical form of a SUPPORTED datatype is the MalformedLiteralException
    // analogue: rejected regardless of ignore_unsupported_datatypes.
    #[test]
    fn build_validated_constant_rejects_malformed_supported_literal() {
        assert!(super::build_validated_constant("abc".into(), XSD_INTEGER.into(), false).is_err());
        assert!(super::build_validated_constant("abc".into(), XSD_INTEGER.into(), true).is_err());
    }

    // A SYNTACTICALLY valid integer outside a derived type's value space is NOT a
    // MalformedLiteralException (parseLiteral is purely syntactic); it parses, and
    // the value-space clash is left for the tableau. So clausification accepts it.
    #[test]
    fn build_validated_constant_accepts_out_of_range_derived_integer() {
        let c = super::build_validated_constant("-1".into(), XSD_NON_NEGATIVE_INTEGER.into(), false)
            .expect("a value-space violation is not a malformed literal");
        assert_eq!(c.lexical_form(), "-1");
        assert_eq!(c.datatype_uri(), XSD_NON_NEGATIVE_INTEGER);
    }

    // An unsupported, non-internal datatype is the UnsupportedDatatypeException
    // analogue: rejected by default, anonymized under ignore_unsupported_datatypes.
    #[test]
    fn build_validated_constant_handles_unsupported_datatype() {
        let custom = "http://example.org/MyType";
        assert!(super::build_validated_constant("v".into(), custom.into(), false).is_err());
        let anon = super::build_validated_constant("v".into(), custom.into(), true)
            .expect("ignore_unsupported_datatypes substitutes an anonymous constant");
        assert!(anon.is_anonymous());
    }

    // CRITICAL: internal:* datatypes are always valid and stored verbatim (never
    // rejected or anonymized) -- this guards the data-property entailment reductions.
    #[test]
    fn build_validated_constant_exempts_internal_datatypes() {
        let c = super::build_validated_constant("c1".into(), "internal:anonymous-constants".into(), false)
            .expect("internal:* datatypes are always valid");
        assert_eq!(c.lexical_form(), "c1");
        assert_eq!(c.datatype_uri(), "internal:anonymous-constants");
        // Also under ignore: still verbatim, not re-anonymized to a different lexical.
        let c2 = super::build_validated_constant("x".into(), "internal:unknown-datatype#0".into(), true)
            .expect("internal:* datatypes are always valid");
        assert_eq!(c2.datatype_uri(), "internal:unknown-datatype#0");
    }

    // A typed rdf:PlainLiteral with NO language tag canonicalizes its lexical
    // form to "lexical@" (trailing '@'), matching Java OWLClausification.getConstant.
    #[test]
    fn convert_literal_canonicalizes_typed_plain_literal_without_lang() {
        let defined = std::collections::HashSet::new();
        let converter = super::DataRangeConverter::new(false, &defined);
        let literal = Literal::Datatype {
            literal: "abc".to_string(),
            datatype_iri: build().iri(super::RDF_PLAIN_LITERAL),
        };
        let c = converter.convert_literal(&literal).expect("valid rdf:PlainLiteral");
        assert_eq!(c.lexical_form(), "abc@");
        assert_eq!(c.datatype_uri(), super::RDF_PLAIN_LITERAL);
        // It equals the language-tagged-with-empty-tag / xsd:string-value form: an
        // empty language tag yields the bare string value.
        let lang = Literal::Language { literal: "abc".to_string(), lang: String::new() };
        assert_eq!(converter.convert_literal(&lang).unwrap().lexical_form(), "abc@");
    }
}
