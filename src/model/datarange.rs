// Ports of org.semanticweb.HermiT.model.{DataRange,LiteralDataRange,AtomicDataRange,
// DatatypeRestriction,ConstantEnumeration,InternalDatatype,AtomicNegationDataRange}.

use std::hash::{Hash, Hasher};
use std::sync::OnceLock;

use crate::model::term::Constant;
use crate::prefixes::Prefixes;
use crate::{impl_display_prefixes, interned};

/// Hashes a single value to a `u64`, used to build the order-independent
/// (sum-of-element-hashes) hashing that HermiT uses for the set-valued ranges.
fn hash_one<T: Hash>(value: &T) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut h);
    h.finish()
}

// ---------------------------------------------------------------------------
// DatatypeRestriction
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub struct DatatypeRestrictionData {
    datatype_uri: String,
    facet_uris: Vec<String>,
    facet_values: Vec<Constant>,
}

// Equality and hashing are order-independent over the facet restrictions, as in
// HermiT's InterningManager for DatatypeRestriction.
impl PartialEq for DatatypeRestrictionData {
    fn eq(&self, other: &Self) -> bool {
        if self.datatype_uri != other.datatype_uri
            || self.facet_uris.len() != other.facet_uris.len()
        {
            return false;
        }
        for i in 0..self.facet_uris.len() {
            if !contains_facet(other, &self.facet_uris[i], &self.facet_values[i]) {
                return false;
            }
        }
        true
    }
}
impl Eq for DatatypeRestrictionData {}
impl Hash for DatatypeRestrictionData {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut sum = hash_one(&self.datatype_uri);
        for i in 0..self.facet_uris.len() {
            sum = sum
                .wrapping_add(hash_one(&self.facet_uris[i]))
                .wrapping_add(hash_one(&self.facet_values[i]));
        }
        state.write_u64(sum);
    }
}

fn contains_facet(data: &DatatypeRestrictionData, facet_uri: &str, facet_value: &Constant) -> bool {
    for j in 0..data.facet_uris.len() {
        if data.facet_uris[j] == facet_uri && &data.facet_values[j] == facet_value {
            return true;
        }
    }
    false
}

interned!(pub DatatypeRestriction => DatatypeRestrictionData);

impl DatatypeRestriction {
    pub fn create(
        datatype_uri: impl Into<String>,
        facet_uris: Vec<String>,
        facet_values: Vec<Constant>,
    ) -> DatatypeRestriction {
        DatatypeRestriction::intern(DatatypeRestrictionData {
            datatype_uri: datatype_uri.into(),
            facet_uris,
            facet_values,
        })
    }
    pub fn datatype_uri(&self) -> &str {
        &self.0.datatype_uri
    }
    pub fn number_of_facet_restrictions(&self) -> usize {
        self.0.facet_uris.len()
    }
    pub fn facet_uri(&self, index: usize) -> &str {
        &self.0.facet_uris[index]
    }
    pub fn facet_value(&self, index: usize) -> &Constant {
        &self.0.facet_values[index]
    }
    pub fn get_negation(&self) -> LiteralDataRange {
        LiteralDataRange::AtomicNegationDataRange(AtomicNegationDataRange::create(
            AtomicDataRange::DatatypeRestriction(self.clone()),
        ))
    }
    pub fn arity(&self) -> usize {
        1
    }
    pub fn is_always_true(&self) -> bool {
        false
    }
    pub fn is_always_false(&self) -> bool {
        false
    }
    pub fn is_internal_datatype(&self) -> bool {
        false
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        let mut buffer = prefixes.abbreviate_iri(&self.0.datatype_uri);
        if !self.0.facet_uris.is_empty() {
            buffer.push('[');
            for index in 0..self.0.facet_uris.len() {
                if index > 0 {
                    buffer.push(',');
                }
                buffer.push_str(&prefixes.abbreviate_iri(&self.0.facet_uris[index]));
                buffer.push('=');
                buffer.push_str(&self.0.facet_values[index].to_string_prefixes(prefixes));
            }
            buffer.push(']');
        }
        buffer
    }
}

// ---------------------------------------------------------------------------
// ConstantEnumeration
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub struct ConstantEnumerationData {
    constants: Vec<Constant>,
}

impl PartialEq for ConstantEnumerationData {
    fn eq(&self, other: &Self) -> bool {
        if self.constants.len() != other.constants.len() {
            return false;
        }
        self.constants.iter().all(|c| other.constants.contains(c))
    }
}
impl Eq for ConstantEnumerationData {}
impl Hash for ConstantEnumerationData {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut sum: u64 = 0;
        for c in &self.constants {
            sum = sum.wrapping_add(hash_one(c));
        }
        state.write_u64(sum);
    }
}

interned!(pub ConstantEnumeration => ConstantEnumerationData);

impl ConstantEnumeration {
    pub fn create(constants: Vec<Constant>) -> ConstantEnumeration {
        ConstantEnumeration::intern(ConstantEnumerationData { constants })
    }
    pub fn number_of_constants(&self) -> usize {
        self.0.constants.len()
    }
    pub fn constant(&self, index: usize) -> &Constant {
        &self.0.constants[index]
    }
    pub fn get_negation(&self) -> LiteralDataRange {
        LiteralDataRange::AtomicNegationDataRange(AtomicNegationDataRange::create(
            AtomicDataRange::ConstantEnumeration(self.clone()),
        ))
    }
    pub fn arity(&self) -> usize {
        1
    }
    pub fn is_always_true(&self) -> bool {
        false
    }
    pub fn is_always_false(&self) -> bool {
        self.0.constants.is_empty()
    }
    pub fn is_internal_datatype(&self) -> bool {
        false
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        let mut buffer = String::from("{ ");
        for (index, constant) in self.0.constants.iter().enumerate() {
            if index > 0 {
                buffer.push(' ');
            }
            buffer.push_str(&constant.to_string_prefixes(prefixes));
        }
        buffer.push_str(" }");
        buffer
    }
}

// ---------------------------------------------------------------------------
// InternalDatatype
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct InternalDatatypeData {
    iri: String,
}

interned!(pub InternalDatatype => InternalDatatypeData);

impl InternalDatatype {
    pub fn create(iri: impl Into<String>) -> InternalDatatype {
        InternalDatatype::intern(InternalDatatypeData { iri: iri.into() })
    }
    pub fn iri(&self) -> &str {
        &self.0.iri
    }
    pub fn arity(&self) -> usize {
        1
    }
    pub fn get_negation(&self) -> LiteralDataRange {
        LiteralDataRange::AtomicNegationDataRange(AtomicNegationDataRange::create(
            AtomicDataRange::InternalDatatype(self.clone()),
        ))
    }
    pub fn is_always_true(&self) -> bool {
        self == InternalDatatype::rdfs_literal()
    }
    pub fn is_always_false(&self) -> bool {
        false
    }
    pub fn is_internal_datatype(&self) -> bool {
        true
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        prefixes.abbreviate_iri(&self.0.iri)
    }

    pub fn rdfs_literal() -> &'static InternalDatatype {
        static D: OnceLock<InternalDatatype> = OnceLock::new();
        D.get_or_init(|| InternalDatatype::create("http://www.w3.org/2000/01/rdf-schema#Literal"))
    }
}

// ---------------------------------------------------------------------------
// AtomicNegationDataRange
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct AtomicNegationDataRangeData {
    negated_data_range: AtomicDataRange,
}

interned!(pub AtomicNegationDataRange => AtomicNegationDataRangeData);

impl AtomicNegationDataRange {
    pub fn create(negated_data_range: AtomicDataRange) -> AtomicNegationDataRange {
        AtomicNegationDataRange::intern(AtomicNegationDataRangeData { negated_data_range })
    }
    pub fn get_negated_data_range(&self) -> &AtomicDataRange {
        &self.0.negated_data_range
    }
    pub fn get_negation(&self) -> LiteralDataRange {
        self.0.negated_data_range.clone().into()
    }
    pub fn arity(&self) -> usize {
        1
    }
    pub fn is_always_true(&self) -> bool {
        self.0.negated_data_range.is_always_false()
    }
    pub fn is_always_false(&self) -> bool {
        self.0.negated_data_range.is_always_true()
    }
    pub fn is_internal_datatype(&self) -> bool {
        false
    }
    pub fn is_negated_internal_datatype(&self) -> bool {
        self.0.negated_data_range.is_internal_datatype()
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        format!("not({})", self.0.negated_data_range.to_string_prefixes(prefixes))
    }
}

// ---------------------------------------------------------------------------
// AtomicDataRange (abstract): datatype, datatype restriction, internal
// datatype, or enumeration of constants
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum AtomicDataRange {
    DatatypeRestriction(DatatypeRestriction),
    ConstantEnumeration(ConstantEnumeration),
    InternalDatatype(InternalDatatype),
}

impl AtomicDataRange {
    pub fn get_negation(&self) -> LiteralDataRange {
        match self {
            AtomicDataRange::DatatypeRestriction(r) => r.get_negation(),
            AtomicDataRange::ConstantEnumeration(r) => r.get_negation(),
            AtomicDataRange::InternalDatatype(r) => r.get_negation(),
        }
    }
    pub fn is_always_true(&self) -> bool {
        match self {
            AtomicDataRange::DatatypeRestriction(r) => r.is_always_true(),
            AtomicDataRange::ConstantEnumeration(r) => r.is_always_true(),
            AtomicDataRange::InternalDatatype(r) => r.is_always_true(),
        }
    }
    pub fn is_always_false(&self) -> bool {
        match self {
            AtomicDataRange::DatatypeRestriction(r) => r.is_always_false(),
            AtomicDataRange::ConstantEnumeration(r) => r.is_always_false(),
            AtomicDataRange::InternalDatatype(r) => r.is_always_false(),
        }
    }
    pub fn is_internal_datatype(&self) -> bool {
        match self {
            AtomicDataRange::DatatypeRestriction(r) => r.is_internal_datatype(),
            AtomicDataRange::ConstantEnumeration(r) => r.is_internal_datatype(),
            AtomicDataRange::InternalDatatype(r) => r.is_internal_datatype(),
        }
    }
    pub fn arity(&self) -> usize {
        1
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        match self {
            AtomicDataRange::DatatypeRestriction(r) => r.to_string_prefixes(prefixes),
            AtomicDataRange::ConstantEnumeration(r) => r.to_string_prefixes(prefixes),
            AtomicDataRange::InternalDatatype(r) => r.to_string_prefixes(prefixes),
        }
    }
}

impl From<AtomicDataRange> for LiteralDataRange {
    fn from(r: AtomicDataRange) -> LiteralDataRange {
        match r {
            AtomicDataRange::DatatypeRestriction(r) => LiteralDataRange::DatatypeRestriction(r),
            AtomicDataRange::ConstantEnumeration(r) => LiteralDataRange::ConstantEnumeration(r),
            AtomicDataRange::InternalDatatype(r) => LiteralDataRange::InternalDatatype(r),
        }
    }
}

// ---------------------------------------------------------------------------
// LiteralDataRange (abstract): an atomic data range or a negation thereof
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum LiteralDataRange {
    DatatypeRestriction(DatatypeRestriction),
    ConstantEnumeration(ConstantEnumeration),
    InternalDatatype(InternalDatatype),
    AtomicNegationDataRange(AtomicNegationDataRange),
}

impl LiteralDataRange {
    pub fn get_negation(&self) -> LiteralDataRange {
        match self {
            LiteralDataRange::DatatypeRestriction(r) => r.get_negation(),
            LiteralDataRange::ConstantEnumeration(r) => r.get_negation(),
            LiteralDataRange::InternalDatatype(r) => r.get_negation(),
            LiteralDataRange::AtomicNegationDataRange(r) => r.get_negation(),
        }
    }
    pub fn is_always_true(&self) -> bool {
        match self {
            LiteralDataRange::DatatypeRestriction(r) => r.is_always_true(),
            LiteralDataRange::ConstantEnumeration(r) => r.is_always_true(),
            LiteralDataRange::InternalDatatype(r) => r.is_always_true(),
            LiteralDataRange::AtomicNegationDataRange(r) => r.is_always_true(),
        }
    }
    pub fn is_always_false(&self) -> bool {
        match self {
            LiteralDataRange::DatatypeRestriction(r) => r.is_always_false(),
            LiteralDataRange::ConstantEnumeration(r) => r.is_always_false(),
            LiteralDataRange::InternalDatatype(r) => r.is_always_false(),
            LiteralDataRange::AtomicNegationDataRange(r) => r.is_always_false(),
        }
    }
    pub fn is_internal_datatype(&self) -> bool {
        match self {
            LiteralDataRange::DatatypeRestriction(r) => r.is_internal_datatype(),
            LiteralDataRange::ConstantEnumeration(r) => r.is_internal_datatype(),
            LiteralDataRange::InternalDatatype(r) => r.is_internal_datatype(),
            LiteralDataRange::AtomicNegationDataRange(r) => r.is_internal_datatype(),
        }
    }
    pub fn is_negated_internal_datatype(&self) -> bool {
        match self {
            LiteralDataRange::AtomicNegationDataRange(r) => r.is_negated_internal_datatype(),
            _ => false,
        }
    }
    pub fn arity(&self) -> usize {
        1
    }
    pub fn to_string_prefixes(&self, prefixes: &Prefixes) -> String {
        match self {
            LiteralDataRange::DatatypeRestriction(r) => r.to_string_prefixes(prefixes),
            LiteralDataRange::ConstantEnumeration(r) => r.to_string_prefixes(prefixes),
            LiteralDataRange::InternalDatatype(r) => r.to_string_prefixes(prefixes),
            LiteralDataRange::AtomicNegationDataRange(r) => r.to_string_prefixes(prefixes),
        }
    }
}

impl_display_prefixes!(
    DatatypeRestriction,
    ConstantEnumeration,
    InternalDatatype,
    AtomicNegationDataRange,
    AtomicDataRange,
    LiteralDataRange,
);
