# Role-automaton construction

`structural::object_property_inclusion_manager` (`ObjectPropertyInclusionManager`)
builds, for every non-simple object property `R`, a finite automaton whose language
is the set of role chains entailed to be sub-roles of `R`. This is the standard
regular-RIA encoding HermiT uses to clausify `∀R.C` restrictions: transitivity and
role chains are pushed onto the universal restrictions rather than materialising
role edges.

## The construction

The role box is read as a grammar. `w ⊑ R` holds exactly when `R` derives the word
`w` from the told inclusions closed under inverse, where `S1...Sn ⊑ R` also gives
`Inv(Sn)...Inv(S1) ⊑ Inv(R)`. `∀R.C` propagates along walks, so a word such as
`R Inv(R) R` counts as a walk even where a model folds it back. `RoleBox` builds one
automaton per class of equivalent roles, following Horrocks, Kutz and Sattler
("The Even More Irresistible SROIQ", KR 2006):

* The skeleton is `initial -R-> final`, plus one path per chain inclusion into the
  class. A class member at the start of a chain starts the path at `final`, and one
  at the end ends the path at `initial`. `R ∘ R ⊑ R` becomes an ε edge from `final`
  to `initial`.
* A non-simple sub-property `S ⊑ R` gets an `initial -S-> final` edge. A simple one
  gets none, because the tableau's role-inclusion clauses already apply the simple
  hierarchy to every edge.
* Each edge labelled by a non-simple role of another class, which is smaller in the
  regular order, is replaced by that role's complete automaton. The automaton of
  `Inv(R)` is the mirror of `R`'s.

The properties are built in `prop_sort_key` order, so the output is deterministic.
HermiT's structural regularity checks (`buildPropertyOrdering`,
`checkForRegularity`) are kept and reject the same role boxes. Those checks do not
close over inverses or equivalences, so they accept a few role boxes whose classes
depend on each other and whose languages need not be regular. There the dependency
is cut and the role is kept as a plain label. The automata stay sound, and, as in
HermiT, completeness is not guaranteed.

### Deliberate deviations from Java HermiT

HermiT's `connectAllAutomata` enriches automata in place while it iterates
`HashMap`s. The automaton a property ends up with therefore depends on iteration
order, and so on IRI spelling through Java's content-based hashing. Forcing
HermiT's iterations into a different deterministic order changes its clause output
on an EFO STAR module. The port used to model that order, with corrections for the
incompleteness of #5 and #8, and it was still unsound:

* `buildInversePropertiesMap` records `SubObjectPropertyOf(R ObjectInverseOf(S))`
  as if `R` and `S` were declared inverses, and enriches `R` with the mirror of
  `S`. With `TransitiveObjectProperty(S)`, `∀R.C` then propagates along
  `Inv(S)`-chains, which is `Inv(S) ⊑ R`. Only `Inv(R) ⊑ S` follows. This showed up
  in class reasoning, `isSubObjectPropertyExpressionOf` and the property classifier
  (`tests/inverse_transitive_automaton_tests.rs`).
* A brute-force comparison over random small role boxes found many more unsound
  and incomplete automata. The comparison is the `language_tests` module next to
  the construction, and it now passes.

The construction above replaces HermiT's. It does not reproduce HermiT's clause
output for role boxes with complex properties. It does reproduce the entailments
that follow from the role box, which HermiT misses on some IRI spellings.

Minimal case this guarantees (now derived on every IRI spelling):

```
a ⊑ u,  a ∘ b ⊑ a,  Transitive(b),  InverseObjectProperties(u, ui)
C ≡ ∃u.Z,  M ⊑ ∃a.Y1,  Y1 ⊑ ∃b.Y2,  Y2 ⊑ ∃b.Z      ⊢   M ⊑ C
```

This is exactly the EFO pattern behind `MONDO_* ⊑ EFO_0000524` ("head and neck
disorder", `EFO_0000524 ≡ ∃EFO_0000784.UBERON_0000033`): `RO_0004027 ⊑ EFO_0000784`,
the chain `RO_0004027 ∘ BFO_0000050 ⊑ RO_0004027`, `BFO_0000050` (part-of)
transitive, and disorders defined via `∃RO_0004027.<anatomy>`. Such a disorder is a
head disorder exactly when its anatomical location is part-of head, e.g.
`UBERON_0001711` (eyelid) `→ UBERON_0000019 → UBERON_0004088 → UBERON_0000033`
(head). These subsumptions are **valid entailments** (ELK, JFact and Whelk all
derive them) and are derived on every IRI spelling.

## Cross-checking completeness: use renamed IRIs, not ROBOT directly

Because HermiT's construction is order-sensitive, ROBOT/HermiT is **not** a
reliable completeness oracle on these ontologies: it misses the `MONDO_* ⊑
EFO_0000524` entailments on the real OBO IRIs, but **derives them once the IRIs are
renamed to opaque strings** with the logical axioms left byte-identical — its answer
depends on IRI spelling via HashMap bucketing. ROBOT remains useful for *soundness*
(it asserts nothing this crate contradicts); for *completeness*, cross-check against
ROBOT on an **IRI-renamed** copy of the ontology, or against a hand-checked
entailment. Each EFO `MONDO_* ⊑ EFO_0000524` was confirmed by walking the part-of +
subclass graph to head/neck.

## Issue #8 regressions

`tests/issue8_role_automata.rs` checks the reported eight-axiom RO fragment,
16 axiom orderings, 32 property renamings, absence of the invented participation
relationship, and the valid inverse/transitive chain entailments. It also checks
that `reasoner::explain` returns a minimal inconsistency justification.

The explanation entry point accepts an inconsistent ontology directly. To obtain
an inconsistency justification, pass `SubClassOf(owl:Thing owl:Nothing)` to
`explain` without first calling the default `is_entailed` entry point. The latter
retains Java's default policy of rejecting queries on inconsistent inputs;
`IncrementalReasoner` exposes the configurable consistency policy.

## Validation

* EFO STAR modules classify **deterministically** (identical across runs) and derive
  the valid inverse+chain subsumptions.
* The full `cargo test` suite passes: lib (312), `owl_wg_conformance`,
  `classification_tests`, `reasoner_tests`, `structural_tests`,
  `owlreasoner_api_tests`, `blocking_strategy_tests`, `tableau_tests`.

## Tooling

`scripts/classification_diff.py` is a transitive-closure soundness/completeness diff
between a `hermit -c` classification and a reference reasoner, with correct OWL
functional-syntax parsing (it strips `Annotation(...)` wrappers and expands
`Prefix(...)`). Its reference reasoner (ROBOT/HermiT) is order-sensitive per the
note above, so treat "rust-only" pairs as candidates to verify (re-run ROBOT on the
IRI-renamed ontology), not as confirmed unsoundness.
