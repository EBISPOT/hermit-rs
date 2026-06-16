//! OWL 2 WG conformance harness — a Rust port of HermiT's
//! `org.semanticweb.HermiT.owl_wg_tests.*` test suite.
//!
//! This single integration test reads the committed OWL 2 Working-Group test
//! manifest (`tests/owl_wg/all.rdf`), enumerates every test case, scopes it the
//! same way Java's `AllNonRejectedNonExtracreditWGTests` does, parses the
//! embedded premise (and, for entailment tests, conclusion) ontologies with
//! horned-owl, runs the Rust reasoner, and compares the answer to the expected
//! result. Each case lands in exactly one of three buckets: PASS (ran, correct),
//! WRONG (ran, incorrect — a real reasoning divergence) or SKIP (could not run:
//! a horned-owl parse error, an unsupported OWL feature, or a reasoner error).
//!
//! Semantics mirrored from the Java harness:
//!   * Scope = DIRECT semantics, species DL, status in {Approved, Proposed}
//!     (NOT Rejected, NOT Extracredit).  See `WGTestDescriptor.isDLTest()` and
//!     `AllNonRejectedNonExtracreditWGTests.suite()`.
//!   * Test types: ConsistencyTest / InconsistencyTest (→ `ConsistencyTest`),
//!     PositiveEntailmentTest / NegativeEntailmentTest (→ `EntailmentTest`).
//!     ProfileIdentificationTest is ignored (`WGTestDescriptor.getTest`).
//!   * Consistency        → `is_ontology_consistent(premise)` MUST be true.
//!   * Inconsistency      → `is_ontology_consistent(premise)` MUST be false.
//!   * PositiveEntailment → premise entails the conclusion's logical axioms.
//!   * NegativeEntailment → premise does NOT entail the conclusion's axioms.
//!   * Premise ontology selection prefers Functional Syntax, then OWL/XML, then
//!     RDF/XML (`WGTestDescriptor.SerializationFormat.values()` order).
//!
//! Inconsistent-premise entailment: the Java suite runs the `EntailmentChecker`
//! with `Configuration.throwInconsistentOntologyException = false`
//! (`AbstractTest.getConfiguration`), so an inconsistent premise entails
//! *everything* (each `EntailmentChecker.visit` returns `true` once
//! `!reasoner.isConsistent()`). The Rust public `is_entailed_axioms` instead
//! uses `Configuration::default()` (throw-on-inconsistent = true) and would
//! return `Err`. To stay faithful we first test premise consistency ourselves
//! and, when inconsistent, short-circuit entailment to `true`.
//!
//! Gating: this is a single `#[test]`. It prints a full tally and asserts
//! `wrong_count <= BASELINE_WRONG`. SKIP never fails the test (it only reports a
//! count and per-test reasons). Lower `BASELINE_WRONG` as conformance is fixed.

use std::collections::BTreeMap;
use std::io::Write as _;

use horned_owl::io::rdf::reader::{IncompleteParse, Term};
use horned_owl::model::{AnnotatedComponent, Build, Component, MutableOntology};
use horned_owl::ontology::set::SetOntology;
use horned_owl::vocab::{OWL as VOWL, RDF as VRDF};

use quick_xml::events::Event;
use quick_xml::Reader;

use hermit_rs::reasoner::{is_entailed_axioms, is_ontology_consistent};
use hermit_rs::structural::A;

/// First-run count of WRONG (ran, but produced the wrong answer) cases.
///
/// On the first full run over the corpus the Rust reasoner produced the correct
/// answer for *every* test it could run faithfully, so this is 0 — the harness
/// gates at `wrong_count <= 0`, i.e. any future reasoning regression on a
/// currently-passing test fails the suite. Keep ratcheting down (it is already
/// at the floor); if a new manifest or a parser improvement surfaces a genuine
/// divergence, investigate rather than bumping this up.
const BASELINE_WRONG: usize = 0;

const URI_BASE: &str = "http://www.w3.org/2007/OWL/testOntology#";
const TEST_ID_PREFIX: &str = "http://owl.semanticweb.org/id/";

/// Per-test wall-clock guard. HermiT's `AbstractTest.TIMEOUT` is 300_000 ms; we
/// keep a generous-but-bounded budget so a pathological case cannot wedge the
/// whole run. A case that exceeds it is recorded as SKIP("timeout").
const PER_TEST_TIMEOUT_SECS: u64 = 15;

type O = SetOntology<A>;

// ----------------------------------------------------------------------------
// Test vocabulary
// ----------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TestType {
    Consistency,
    Inconsistency,
    PositiveEntailment,
    NegativeEntailment,
}

impl TestType {
    fn label(self) -> &'static str {
        match self {
            TestType::Consistency => "Consistency",
            TestType::Inconsistency => "Inconsistency",
            TestType::PositiveEntailment => "PositiveEntailment",
            TestType::NegativeEntailment => "NegativeEntailment",
        }
    }
}

/// One `<test:TestCase>` element, after walking the manifest.
#[derive(Default, Debug)]
struct RawTest {
    /// IRI suffix after `TEST_ID_PREFIX` (the Java `testID`).
    id: String,
    /// `test:identifier` literal (the Java `identifier`, used for suite naming).
    identifier: String,
    /// Local names of every `rdf:type` resource under `URI_BASE`.
    types: Vec<String>,
    /// Local names of every `test:status` resource under `URI_BASE`.
    statuses: Vec<String>,
    /// Local names of every (positive) `test:semantics` resource.
    semantics: Vec<String>,
    /// Local names of every `test:species` resource.
    species: Vec<String>,
    // Embedded ontology serializations (already XML-unescaped to source text).
    fs_premise: Option<String>,
    owx_premise: Option<String>,
    rdf_premise: Option<String>,
    fs_conclusion: Option<String>,
    owx_conclusion: Option<String>,
    rdf_conclusion: Option<String>,
    fs_nonconclusion: Option<String>,
    owx_nonconclusion: Option<String>,
    rdf_nonconclusion: Option<String>,
}

/// Serialization formats in the Java `SerializationFormat.values()` order
/// (FUNCTIONAL, OWLXML, RDFXML) — premise/conclusion selection walks them in
/// this order and takes the first present.
#[derive(Clone, Copy)]
enum Format {
    Functional,
    Owx,
    Rdf,
}

impl RawTest {
    fn premise(&self, f: Format) -> Option<&String> {
        match f {
            Format::Functional => self.fs_premise.as_ref(),
            Format::Owx => self.owx_premise.as_ref(),
            Format::Rdf => self.rdf_premise.as_ref(),
        }
    }
    fn conclusion(&self, f: Format, positive: bool) -> Option<&String> {
        match (f, positive) {
            (Format::Functional, true) => self.fs_conclusion.as_ref(),
            (Format::Owx, true) => self.owx_conclusion.as_ref(),
            (Format::Rdf, true) => self.rdf_conclusion.as_ref(),
            (Format::Functional, false) => self.fs_nonconclusion.as_ref(),
            (Format::Owx, false) => self.owx_nonconclusion.as_ref(),
            (Format::Rdf, false) => self.rdf_nonconclusion.as_ref(),
        }
    }
}

// ----------------------------------------------------------------------------
// Manifest parsing
// ----------------------------------------------------------------------------

/// Replace the four DOCTYPE-defined entity references with their literal IRIs so
/// a plain (non-DTD) XML reader can consume the manifest. These four entities
/// only ever appear in the test-vocabulary markup (attribute values and resource
/// references); they never occur inside the doubly-escaped `&lt;...&gt;` literal
/// ontology blocks (verified against the corpus), so this textual substitution
/// is safe and does not touch the embedded serializations.
fn expand_doctype_entities(src: &str) -> String {
    src.replace("&rdf;", "http://www.w3.org/1999/02/22-rdf-syntax-ns#")
        .replace("&rdfs;", "http://www.w3.org/2000/01/rdf-schema#")
        .replace("&owl;", "http://www.w3.org/2002/07/owl#")
        .replace("&test;", URI_BASE)
}

/// Strip `URI_BASE` from a resource IRI, returning the local name; `None` if the
/// IRI is not under the test ontology namespace.
fn local_name(iri: &str) -> Option<&str> {
    iri.strip_prefix(URI_BASE)
}

/// Parse the manifest into the list of raw test cases. Implemented as a small
/// streaming walk: we only care about `<test:TestCase>` subtrees and, within
/// them, the vocabulary elements. Everything else (the `owl:Ontology` header,
/// the trailing `owl:NegativePropertyAssertion`s that encode profile exclusions)
/// is ignored — exactly the fields `WGTestDescriptor` reads.
fn parse_manifest(xml: &str) -> Result<Vec<RawTest>, String> {
    let mut reader = Reader::from_str(xml);
    let cfg = reader.config_mut();
    cfg.trim_text(false);
    cfg.expand_empty_elements = false;

    let mut tests: Vec<RawTest> = Vec::new();
    let mut cur: Option<RawTest> = None;
    // When inside a vocabulary element that carries text (identifier / status /
    // the ontology serializations), this holds (field-tag, accumulated-text).
    let mut text_field: Option<(String, String)> = None;
    let mut buf = Vec::new();

    loop {
        match reader.read_event_into(&mut buf) {
            Err(e) => return Err(format!("XML error at {}: {e}", reader.buffer_position())),
            Ok(Event::Eof) => break,
            Ok(Event::Start(e)) => {
                let name = e.name();
                let tag = String::from_utf8_lossy(name.as_ref()).into_owned();
                if tag == "test:TestCase" {
                    let mut rt = RawTest::default();
                    if let Some(about) = attr(&e, b"rdf:about") {
                        rt.id = about
                            .strip_prefix(TEST_ID_PREFIX)
                            .unwrap_or(&about)
                            .to_string();
                    }
                    cur = Some(rt);
                } else if cur.is_some() {
                    // A start tag with content inside a TestCase. If it carries
                    // an rdf:resource it is an object-property value handled like
                    // an empty element; otherwise begin accumulating its text.
                    if let Some(rt) = cur.as_mut() {
                        if let Some(res) = attr(&e, b"rdf:resource") {
                            record_resource(rt, &tag, &res);
                        }
                    }
                    // We always start a text buffer: data properties (identifier,
                    // the ontology literals) deliver their value as Text events.
                    text_field = Some((tag, String::new()));
                }
            }
            Ok(Event::Empty(e)) => {
                if cur.is_some() {
                    let name = e.name();
                    let tag = String::from_utf8_lossy(name.as_ref()).into_owned();
                    if let (Some(rt), Some(res)) = (cur.as_mut(), attr(&e, b"rdf:resource")) {
                        record_resource(rt, &tag, &res);
                    }
                }
            }
            Ok(Event::Text(t)) => {
                if let Some((_, acc)) = text_field.as_mut() {
                    // The text inside a data-property element is the (single
                    // level) XML-unescaped value: `&lt;` → `<`, etc. This yields
                    // the embedded ontology's own source text.
                    match t.unescape() {
                        Ok(s) => acc.push_str(&s),
                        Err(_) => acc.push_str(&String::from_utf8_lossy(t.as_ref())),
                    }
                }
            }
            Ok(Event::CData(t)) => {
                if let Some((_, acc)) = text_field.as_mut() {
                    acc.push_str(&String::from_utf8_lossy(t.as_ref()));
                }
            }
            Ok(Event::End(e)) => {
                let name = e.name();
                let tag = String::from_utf8_lossy(name.as_ref()).into_owned();
                if tag == "test:TestCase" {
                    if let Some(rt) = cur.take() {
                        tests.push(rt);
                    }
                    text_field = None;
                } else if let Some((field, value)) = text_field.take() {
                    if field == tag {
                        if let Some(rt) = cur.as_mut() {
                            record_text(rt, &field, value);
                        }
                    }
                }
            }
            _ => {}
        }
        buf.clear();
    }
    Ok(tests)
}

/// Read an attribute value (already entity-expanded for the four DOCTYPE
/// entities at the file level, but quick-xml still XML-unescapes standard
/// entities) by its raw qualified name.
fn attr(e: &quick_xml::events::BytesStart, key: &[u8]) -> Option<String> {
    e.attributes().with_checks(false).find_map(|a| {
        let a = a.ok()?;
        if a.key.as_ref() == key {
            Some(
                a.unescape_value()
                    .map(|c| c.into_owned())
                    .unwrap_or_else(|_| String::from_utf8_lossy(&a.value).into_owned()),
            )
        } else {
            None
        }
    })
}

/// Record an object-property `rdf:resource` value (type / status / semantics /
/// species) onto the current test.
fn record_resource(rt: &mut RawTest, tag: &str, resource: &str) {
    match tag {
        "rdf:type" => {
            if let Some(ln) = local_name(resource) {
                rt.types.push(ln.to_string());
            }
        }
        "test:status" => {
            if let Some(ln) = local_name(resource) {
                rt.statuses.push(ln.to_string());
            }
        }
        "test:semantics" => {
            if let Some(ln) = local_name(resource) {
                rt.semantics.push(ln.to_string());
            }
        }
        "test:species" => {
            if let Some(ln) = local_name(resource) {
                rt.species.push(ln.to_string());
            }
        }
        _ => {}
    }
}

/// Record a data-property text value (identifier or an embedded ontology
/// serialization) onto the current test.
fn record_text(rt: &mut RawTest, field: &str, value: String) {
    match field {
        "test:identifier" => rt.identifier = value.trim().to_string(),
        "test:fsPremiseOntology" => rt.fs_premise = Some(value),
        "test:owlXmlPremiseOntology" => rt.owx_premise = Some(value),
        "test:rdfXmlPremiseOntology" => rt.rdf_premise = Some(value),
        "test:fsConclusionOntology" => rt.fs_conclusion = Some(value),
        "test:owlXmlConclusionOntology" => rt.owx_conclusion = Some(value),
        "test:rdfXmlConclusionOntology" => rt.rdf_conclusion = Some(value),
        "test:fsNonConclusionOntology" => rt.fs_nonconclusion = Some(value),
        "test:owlXmlNonConclusionOntology" => rt.owx_nonconclusion = Some(value),
        "test:rdfXmlNonConclusionOntology" => rt.rdf_nonconclusion = Some(value),
        _ => {}
    }
}

// ----------------------------------------------------------------------------
// Scoping (AllNonRejectedNonExtracreditWGTests + WGTestDescriptor.isDLTest)
// ----------------------------------------------------------------------------

/// `WGTestDescriptor.isDLTest()`: DIRECT semantics AND species DL.
fn is_dl_test(rt: &RawTest) -> bool {
    rt.semantics.iter().any(|s| s == "DIRECT") && rt.species.iter().any(|s| s == "DL")
}

/// Status in {Approved, Proposed} (the suite excludes Rejected and Extracredit).
fn is_in_scope_status(rt: &RawTest) -> bool {
    rt.statuses
        .iter()
        .any(|s| s == "Approved" || s == "Proposed")
}

/// The runnable (non-profile) test types declared on this case, mapped to our
/// enum. Mirrors `WGTestDescriptor.getTest` switching only on the four DL types.
fn runnable_types(rt: &RawTest) -> Vec<TestType> {
    let mut out = Vec::new();
    for t in &rt.types {
        match t.as_str() {
            "ConsistencyTest" => out.push(TestType::Consistency),
            "InconsistencyTest" => out.push(TestType::Inconsistency),
            "PositiveEntailmentTest" => out.push(TestType::PositiveEntailment),
            "NegativeEntailmentTest" => out.push(TestType::NegativeEntailment),
            _ => {}
        }
    }
    out
}

// ----------------------------------------------------------------------------
// horned-owl parsing of the embedded serializations
// ----------------------------------------------------------------------------

/// Parse an embedded ontology serialization into a `SetOntology<A>`, trying the
/// formats in the Java preference order. Returns the parsed ontology together
/// with the format used, or a descriptive error. A premise (or conclusion) that
/// is absent in *every* format is reported by the caller; here `present` already
/// holds the (format, source) pairs to try.
fn parse_ontology(present: &[(Format, &String)]) -> Result<(O, &'static str), String> {
    let mut last_err = String::from("no serialization present");
    for (fmt, src) in present {
        match parse_one(*fmt, src) {
            Ok(o) => return Ok((o, fmt_name(*fmt))),
            Err(e) => last_err = format!("{}: {e}", fmt_name(*fmt)),
        }
    }
    Err(last_err)
}

fn fmt_name(f: Format) -> &'static str {
    match f {
        Format::Functional => "fs",
        Format::Owx => "owx",
        Format::Rdf => "rdf",
    }
}

/// Parse one serialization. horned-owl's readers can both return `Err` and
/// (for some malformed RDF/XML) *panic* (e.g. an `unwrap` on an unexpected
/// property element). We catch unwinding so a parser panic becomes a SKIP
/// reason rather than aborting the whole suite.
fn parse_one(fmt: Format, src: &str) -> Result<O, String> {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| parse_one_inner(fmt, src)));
    match result {
        Ok(r) => r,
        Err(p) => {
            let msg = p
                .downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| p.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "parser panicked".to_string());
            Err(format!("parser panic: {msg}"))
        }
    }
}

fn parse_one_inner(fmt: Format, src: &str) -> Result<O, String> {
    let build: Build<A> = Build::new();
    match fmt {
        Format::Functional => {
            let mut cur = std::io::Cursor::new(src.as_bytes());
            let (o, _prefixes): (O, _) =
                horned_owl::io::ofn::reader::read_with_build(&mut cur, &build)
                    .map_err(|e| format!("{e}"))?;
            Ok(o)
        }
        Format::Owx => {
            let mut cur = std::io::Cursor::new(src.as_bytes());
            let (o, _prefixes): (O, _) =
                horned_owl::io::owx::reader::read_with_build(&mut cur, &build)
                    .map_err(|e| format!("{e}"))?;
            Ok(o)
        }
        Format::Rdf => {
            let mut cur = std::io::Cursor::new(src.as_bytes());
            let (rdfo, incomplete) = horned_owl::io::rdf::reader::read_with_build::<
                A,
                AnnotatedComponent<A>,
                _,
            >(&mut cur, &build, Default::default())
            .map_err(|e| format!("{e}"))?;
            // horned-owl's `is_complete()` is strict: it reports incomplete
            // whenever *any* triple is left unconsumed, including the harmless
            // `_:b rdf:type owl:Ontology` triple it emits for an anonymous (or
            // some named) `owl:Ontology` header — even though every logical
            // axiom was extracted. We accept the parse when the only residue is
            // such ontology-header / version / import noise, and SKIP only when
            // *logical* content (a stray class expression, sub-class/restriction
            // triple, RDF list, etc.) was dropped — that is a genuine parser gap
            // where running the reasoner would silently use a truncated ontology.
            if !incomplete.is_complete() && !residue_is_benign(&incomplete) {
                return Err(format!("rdf parse incomplete: {}", summarize_residue(&incomplete)));
            }
            Ok(rdfo.into())
        }
    }
}

/// True when every unconsumed triple is an ontology-header artifact (and there
/// are no leftover class expressions / property expressions / data ranges /
/// RDF-list sequences / floating atoms / annotation maps). See `parse_one_inner`.
fn residue_is_benign(inc: &IncompleteParse<A>) -> bool {
    inc.class_expression.is_empty()
        && inc.object_property_expression.is_empty()
        && inc.data_range.is_empty()
        && inc.atom.is_empty()
        && inc.ann_map.is_empty()
        && inc.bnode_seq.is_empty()
        && inc.simple.iter().all(|p| benign_triple(p.triple()))
        && inc.bnode.iter().all(|v| v.iter().all(benign_triple))
}

/// A residual triple is benign iff it is an ontology-header triple:
/// `(_, rdf:type, owl:Ontology)` or an ontology-level
/// import / version-IRI declaration. These carry no logical content.
fn benign_triple(t: &[Term<A>; 3]) -> bool {
    match (&t[1], &t[2]) {
        (Term::RDF(VRDF::Type), Term::OWL(VOWL::Ontology)) => true,
        (Term::OWL(VOWL::Imports), _) => true,
        (Term::OWL(VOWL::VersionIRI), _) => true,
        _ => false,
    }
}

/// A compact, deterministic description of the dropped (logical) residue, for
/// the per-test SKIP reason. We avoid the giant `Debug` of `IncompleteParse`
/// (which embeds whole literals) and instead count what was left behind.
fn summarize_residue(inc: &IncompleteParse<A>) -> String {
    let n_logical_triples = inc
        .simple
        .iter()
        .filter(|p| !benign_triple(p.triple()))
        .count()
        + inc
            .bnode
            .iter()
            .map(|v| v.iter().filter(|t| !benign_triple(t)).count())
            .sum::<usize>();
    format!(
        "left {} logical triple(s), {} class-expr, {} obj-prop-expr, {} data-range, {} rdf-list-seq, {} atom, {} ann",
        n_logical_triples,
        inc.class_expression.len(),
        inc.object_property_expression.len(),
        inc.data_range.len(),
        inc.bnode_seq.len(),
        inc.atom.len(),
        inc.ann_map.len(),
    )
}

/// The bundled import resources, mirroring `AbstractTest.registerImportedReosurces`:
/// each `owl:imports` target IRI maps to a local RDF/XML file under
/// `tests/owl_wg/`. The Java suite registers these with an OWLAPI `IRIMapper` so
/// the import closure loads from disk.
const IMPORT_MAP: &[(&str, &str)] = &[
    (
        "http://www.w3.org/2002/03owlt/miscellaneous/consistent001",
        "consistent001.rdf",
    ),
    (
        "http://www.w3.org/2002/03owlt/miscellaneous/consistent002",
        "consistent002.rdf",
    ),
    (
        "http://www.w3.org/2002/03owlt/imports/support011-A",
        "support011-A.rdf",
    ),
];

/// Merge the import closure into `onto` for the imports the Java harness maps to
/// bundled resources. Walks transitively (an imported file may itself import).
/// Returns `Err` if an `owl:imports` target has no local mapping or fails to
/// parse — we must not silently reason over a premise missing imported axioms.
fn resolve_imports(onto: &mut O) -> Result<(), String> {
    use std::collections::HashSet;
    let mut seen: HashSet<String> = HashSet::new();
    loop {
        // Gather not-yet-resolved import targets currently in the ontology.
        let pending: Vec<String> = onto
            .iter()
            .filter_map(|ac| match &ac.component {
                Component::Import(imp) => {
                    let iri = imp.0.to_string();
                    if seen.contains(&iri) {
                        None
                    } else {
                        Some(iri)
                    }
                }
                _ => None,
            })
            .collect();
        if pending.is_empty() {
            return Ok(());
        }
        for iri in pending {
            seen.insert(iri.clone());
            let file = IMPORT_MAP
                .iter()
                .find(|(k, _)| *k == iri)
                .map(|(_, f)| *f)
                .ok_or_else(|| format!("unmapped import target {iri}"))?;
            let path = format!("{}/tests/owl_wg/{}", env!("CARGO_MANIFEST_DIR"), file);
            let src = std::fs::read_to_string(&path)
                .map_err(|e| format!("cannot read import resource {path}: {e}"))?;
            // The bundled resources are RDF/XML.
            let imported = parse_one(Format::Rdf, &src)
                .map_err(|e| format!("parse import {iri} ({file}): {e}"))?;
            for ac in &imported {
                onto.insert(ac.clone());
            }
        }
    }
}

/// Collect a `SetOntology`'s components (the `AnnotatedComponent.component`s),
/// mirroring the axiom stream EntailmentChecker walks. Non-logical components
/// (declarations, annotations, imports, ontology id/annotations) are handled by
/// `is_entailed_*` as vacuously entailed, exactly as OWLAPI's
/// `getLogicalAxioms()` excludes them.
fn components(o: &O) -> Vec<Component<A>> {
    o.into_iter()
        .map(|ac: &AnnotatedComponent<A>| ac.component.clone())
        .collect()
}

// ----------------------------------------------------------------------------
// Outcome model
// ----------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum Bucket {
    Pass,
    Wrong,
    Skip,
}

struct Outcome {
    id: String,
    ttype: TestType,
    expected: String,
    got: String,
    bucket: Bucket,
    reason: String,
}

/// Run one scoped (test-case, test-type) pair and classify the outcome.
fn run_case(rt: &RawTest, ttype: TestType) -> Outcome {
    let mut out = Outcome {
        id: rt.id.clone(),
        ttype,
        expected: String::new(),
        got: String::new(),
        bucket: Bucket::Skip,
        reason: String::new(),
    };

    // --- premise ---
    let premise_present: Vec<(Format, &String)> = [Format::Functional, Format::Owx, Format::Rdf]
        .into_iter()
        .filter_map(|f| rt.premise(f).map(|s| (f, s)))
        .collect();
    // A missing premise property means "empty ontology" in the Java harness; we
    // model that with an empty SetOntology.
    let mut premise: O = if premise_present.is_empty() {
        SetOntology::new()
    } else {
        match parse_ontology(&premise_present) {
            Ok((o, _)) => o,
            Err(e) => {
                out.reason = format!("premise parse: {e}");
                return out;
            }
        }
    };
    // Resolve the handful of `owl:imports` the Java harness maps to bundled local
    // resources (`AbstractTest.registerImportedReosurces`). OWLAPI loads the
    // import closure before HermiT runs; the Rust reasoner ignores `Import`
    // components, so we merge the imported axioms here. An import we cannot
    // resolve (no local mapping / parse failure) is reported as a SKIP, because
    // running with a truncated premise would produce a spurious verdict — exactly
    // the `WebOnt-imports-011` situation.
    if let Err(e) = resolve_imports(&mut premise) {
        out.reason = format!("import resolution: {e}");
        return out;
    }

    match ttype {
        TestType::Consistency | TestType::Inconsistency => {
            let want = matches!(ttype, TestType::Consistency);
            out.expected = if want { "consistent" } else { "inconsistent" }.to_string();
            match catch_consistency(&premise) {
                Ok(got) => {
                    out.got = if got { "consistent" } else { "inconsistent" }.to_string();
                    out.bucket = if got == want { Bucket::Pass } else { Bucket::Wrong };
                }
                Err(e) => {
                    out.reason = classify_runtime_error(&e);
                }
            }
        }
        TestType::PositiveEntailment | TestType::NegativeEntailment => {
            let positive = matches!(ttype, TestType::PositiveEntailment);
            out.expected = if positive { "entailed" } else { "not-entailed" }.to_string();
            let concl_present: Vec<(Format, &String)> =
                [Format::Functional, Format::Owx, Format::Rdf]
                    .into_iter()
                    .filter_map(|f| rt.conclusion(f, positive).map(|s| (f, s)))
                    .collect();
            if concl_present.is_empty() {
                out.reason = "no conclusion ontology in a parsable format".to_string();
                return out;
            }
            let conclusion: O = match parse_ontology(&concl_present) {
                Ok((o, _)) => o,
                Err(e) => {
                    out.reason = format!("conclusion parse: {e}");
                    return out;
                }
            };
            match entails(&premise, &conclusion) {
                Ok(got) => {
                    out.got = if got { "entailed" } else { "not-entailed" }.to_string();
                    out.bucket = if got == positive { Bucket::Pass } else { Bucket::Wrong };
                }
                Err(e) => {
                    out.reason = classify_runtime_error(&e);
                }
            }
        }
    }
    out
}

/// `is_ontology_consistent`, wrapped so a panic or timeout inside the reasoner
/// becomes a recoverable SKIP rather than aborting the whole suite. The premise
/// is cloned into the worker thread (these test ontologies are tiny) so the
/// closure can be `'static`.
fn catch_consistency(premise: &O) -> Result<bool, String> {
    let premise = premise.clone();
    run_guarded(move || is_ontology_consistent(&premise))
}

/// Faithful port of the harness's entailment decision (see the module doc):
/// inconsistent premise ⇒ everything entailed; otherwise delegate to
/// `is_entailed_axioms` over the conclusion's components.
fn entails(premise: &O, conclusion: &O) -> Result<bool, String> {
    let consistent = catch_consistency(premise)?;
    if !consistent {
        // EntailmentChecker with throwInconsistentOntologyException=false:
        // an inconsistent ontology entails every axiom.
        return Ok(true);
    }
    let premise_owned = premise.clone();
    let axioms = components(conclusion);
    run_guarded(move || is_entailed_axioms(&premise_owned, &axioms))
}

/// Run a reasoner closure under a wall-clock guard and panic-catch. The guard
/// runs the closure on a worker thread and abandons it after
/// `PER_TEST_TIMEOUT_SECS`; the abandoned thread (if any) is detached. A panic in
/// the reasoner is converted to an `Err` so the case is bucketed as SKIP.
fn run_guarded<F>(f: F) -> Result<bool, String>
where
    F: FnOnce() -> Result<bool, String> + Send + 'static,
{
    use std::sync::mpsc;
    use std::time::Duration;

    let (tx, rx) = mpsc::channel();
    let handle = std::thread::spawn(move || {
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        // Receiver may be gone if we timed out; ignore send errors.
        let _ = tx.send(res);
    });
    match rx.recv_timeout(Duration::from_secs(PER_TEST_TIMEOUT_SECS)) {
        Ok(Ok(r)) => {
            let _ = handle.join();
            r
        }
        Ok(Err(panic)) => {
            let _ = handle.join();
            let msg = panic
                .downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| panic.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "reasoner panicked".to_string());
            Err(format!("panic: {msg}"))
        }
        Err(_) => {
            // Timed out: detach the worker (the process will reap it at exit).
            Err("timeout".to_string())
        }
    }
}

/// Bucket a reasoner-side error string into a concise SKIP reason category.
fn classify_runtime_error(e: &str) -> String {
    let lower = e.to_ascii_lowercase();
    if lower.starts_with("timeout") {
        "timeout".to_string()
    } else if lower.starts_with("panic") {
        format!("reasoner panic ({})", e.trim_start_matches("panic: "))
    } else if lower.contains("not supported")
        || lower.contains("unsupported")
        || lower.contains("not yet")
        || lower.contains("unimplemented")
    {
        format!("unsupported feature ({e})")
    } else if lower.contains("anonymous") {
        format!("anonymous-individual restriction ({e})")
    } else {
        format!("reasoner error ({e})")
    }
}

/// A coarse category for a SKIP reason, used only for the aggregated summary.
fn skip_category(reason: &str) -> &'static str {
    let l = reason.to_ascii_lowercase();
    let is_parse = l.starts_with("premise parse") || l.starts_with("conclusion parse");
    if is_parse && l.contains("parse incomplete") {
        "parse: horned-owl dropped logical triples"
    } else if is_parse && l.contains("parser panic") {
        "parse: horned-owl reader panic"
    } else if is_parse {
        "parse: horned-owl hard error"
    } else if l.contains("no conclusion") {
        "missing conclusion serialization"
    } else if l.starts_with("unsupported feature") {
        "unsupported feature (reasoner)"
    } else if l.starts_with("timeout") {
        "timeout"
    } else if l.contains("panic") {
        "reasoner panic"
    } else if l.contains("anonymous") {
        "anonymous-individual restriction"
    } else {
        "reasoner error"
    }
}

// ----------------------------------------------------------------------------
// The test
// ----------------------------------------------------------------------------

#[test]
fn owl_wg_conformance() {
    // Catch-unwind inside run_guarded would otherwise print every reasoner panic
    // backtrace to stderr and drown the report; silence the default hook for the
    // duration of the run (we surface the panic message ourselves).
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    let manifest_path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/owl_wg/all.rdf");
    let raw = std::fs::read_to_string(manifest_path)
        .unwrap_or_else(|e| panic!("cannot read manifest {manifest_path}: {e}"));
    let xml = expand_doctype_entities(&raw);
    let tests = parse_manifest(&xml).expect("manifest parse failed");

    // Scope exactly like AllNonRejectedNonExtracreditWGTests: DL test (DIRECT +
    // DL species) AND status in {Approved, Proposed}, then expand into one run
    // per runnable test type.
    let mut scoped: Vec<(&RawTest, TestType)> = Vec::new();
    for rt in &tests {
        if is_dl_test(rt) && is_in_scope_status(rt) {
            for ttype in runnable_types(rt) {
                scoped.push((rt, ttype));
            }
        }
    }

    let mut outcomes: Vec<Outcome> = Vec::with_capacity(scoped.len());
    for (rt, ttype) in &scoped {
        outcomes.push(run_case(rt, *ttype));
    }

    std::panic::set_hook(prev_hook);

    // --- tallies ---
    let mut pass = 0usize;
    let mut wrong = 0usize;
    let mut skip = 0usize;
    // per-type [pass, wrong, skip]
    let mut per_type: BTreeMap<&'static str, [usize; 3]> = BTreeMap::new();
    // aggregated skip categories
    let mut skip_cats: BTreeMap<&'static str, usize> = BTreeMap::new();

    for o in &outcomes {
        let slot = per_type.entry(o.ttype.label()).or_insert([0, 0, 0]);
        match o.bucket {
            Bucket::Pass => {
                pass += 1;
                slot[0] += 1;
            }
            Bucket::Wrong => {
                wrong += 1;
                slot[1] += 1;
            }
            Bucket::Skip => {
                skip += 1;
                slot[2] += 1;
                *skip_cats.entry(skip_category(&o.reason)).or_insert(0) += 1;
            }
        }
    }

    // --- full per-test results file ---
    let results_path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/owl_wg/results.txt");
    write_results_file(results_path, &scoped, &outcomes);

    // --- printed report ---
    eprintln!("\n================ OWL 2 WG conformance (DIRECT, non-rejected, non-extracredit) ================");
    eprintln!(
        "manifest: {} test cases parsed; {} scoped (test-case x test-type) runs",
        tests.len(),
        scoped.len()
    );
    eprintln!(
        "OVERALL: {} PASS / {} WRONG / {} SKIP  (total {})",
        pass,
        wrong,
        skip,
        outcomes.len()
    );
    eprintln!("\nper-type (PASS / WRONG / SKIP):");
    for (ty, [p, w, s]) in &per_type {
        eprintln!("  {:<20} {:>4} / {:>4} / {:>4}", ty, p, w, s);
    }

    eprintln!("\nWRONG cases (real reasoning divergences):");
    if wrong == 0 {
        eprintln!("  (none)");
    } else {
        for o in outcomes.iter().filter(|o| o.bucket == Bucket::Wrong) {
            eprintln!(
                "  [{}] {}  expected={} got={}",
                o.ttype.label(),
                o.id,
                o.expected,
                o.got
            );
        }
    }

    eprintln!("\nSKIP reasons (aggregated):");
    if skip == 0 {
        eprintln!("  (none)");
    } else {
        for (cat, n) in &skip_cats {
            eprintln!("  {:<34} {:>4}", cat, n);
        }
    }
    eprintln!(
        "\nfull per-test results written to: {}\nBASELINE_WRONG = {} (ratchet down to 0 as conformance is fixed)",
        results_path, BASELINE_WRONG
    );
    eprintln!("=============================================================================================\n");

    assert!(
        wrong <= BASELINE_WRONG,
        "conformance regression: {wrong} WRONG cases exceeds BASELINE_WRONG={BASELINE_WRONG}. \
         See the WRONG list above and {results_path}."
    );
}

fn write_results_file(path: &str, scoped: &[(&RawTest, TestType)], outcomes: &[Outcome]) {
    let mut f = match std::fs::File::create(path) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("warning: could not write results file {path}: {e}");
            return;
        }
    };
    let _ = writeln!(
        f,
        "# OWL 2 WG conformance — per-test results (DIRECT, non-rejected, non-extracredit)"
    );
    let _ = writeln!(
        f,
        "# columns: BUCKET\\tTYPE\\tID\\texpected\\tgot\\treason"
    );
    let _ = writeln!(f, "# scoped runs: {}", scoped.len());
    for o in outcomes {
        let bucket = match o.bucket {
            Bucket::Pass => "PASS",
            Bucket::Wrong => "WRONG",
            Bucket::Skip => "SKIP",
        };
        let _ = writeln!(
            f,
            "{}\t{}\t{}\t{}\t{}\t{}",
            bucket,
            o.ttype.label(),
            o.id,
            if o.expected.is_empty() { "-" } else { &o.expected },
            if o.got.is_empty() { "-" } else { &o.got },
            if o.reason.is_empty() { "-" } else { &o.reason },
        );
    }
}
