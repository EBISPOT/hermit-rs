# Role-automaton construction: determinism and inverse/chain completeness

`structural::object_property_inclusion_manager` (`ObjectPropertyInclusionManager`)
builds, for every complex object property `R`, a finite automaton whose language is
the set of role chains implied to be sub-roles of `R` — the standard regular-RIA
encoding HermiT uses to clausify `∀R.C` restrictions (transitivity and role chains
are pushed onto the universal restrictions rather than materialising role edges).

The construction enriches automata **in place** while iterating
`HashMap`/`HashSet`-keyed collections: `increase_automaton_with_inverse` splices
(the mirror of) a property's inverse automaton via `automata_connector`, which
performs a disjoint union of states. Because splicing adds states, the automaton a
property ends up with depends on the iteration order and on which related automata
have already been enriched. Two consequences of that order-sensitivity are handled
explicitly; both are covered by the construction as it now stands.

## 1. Deterministic, order-independent output

Rust's `std::collections::HashMap` reseeds `RandomState` per process, so an
unordered iteration produced a *different* automaton on every run — classifying EFO
gave non-deterministic class hierarchies (a property could come out under-enriched
⇒ incomplete, or over-enriched ⇒ unsound, run to run).

This is a property of the algorithm, not just the port: HermiT's own construction
is equally order-sensitive — it is reproducible only because Java's hashing is
content-based and unseeded. Forcing Java HermiT's `propertiesToStartRecursion` and
sub-property iterations into a different deterministic (sorted) order changes its
clause output too (e.g. on an EFO STAR module it goes from its default result to a
different one), confirming the fragility is in the algorithm.

**How it is handled:** every order-sensitive collection in the construction is
iterated in a fixed canonical order, `prop_sort_key` (named properties before their
inverses, then by IRI). The output is fully deterministic across runs and, on small
EFO modules, byte-identical to Java HermiT's `--dump-clauses` (modulo
internal-concept renaming).

## 2. Forward sub-chains survive inverse + chain hierarchies (completeness)

Sub-property edges are recorded only forward in the dependency graph: `a ⊑ R` is
stored, but its mirror `Inv(a) ⊑ Inv(R)` is not. So when a property `R` has both a
chain-bearing complex sub-property (`a ⊑ R` with `a ∘ b ⊑ a`) **and** a declared
inverse (`InverseObjectProperties(R, Ri)`), the recursion may only ever be entered
on the inverse representations (`Inv(R)` / `Ri`), whose sub-property successors omit
`Inv(a)`. `R` would then be produced by the mirror-fill pass as
`mirror(automaton(Inv(R)))`, which lacks `R`'s sub-chains — silently dropping
`a ∘ b*` from `R`'s automaton, so `∀R.C` under-propagates and valid subsumptions are
missed (which way it broke depended on iteration order).

**How it is handled** — two order-independent rules in
`object_property_inclusion_manager.rs`:

1. The automaton recursion is seeded with **every** property in the dependency
   graph, not only the sinks, so a forward, sub-chain-bearing property `R` is always
   built directly from its own sub-chains. Builds are memoised, so the extra seeds
   are no-ops once a property is done.
2. The `R = mirror(complete(Inv(R)))` shortcut is only taken when `R` has **no**
   forward sub-properties of its own; otherwise `R` is built from its sub-chains
   (the mirror would drop them).

Minimal case this guarantees (now derived; it was missed before):

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
(head). These subsumptions are **valid entailments** and are derived.

## Cross-checking completeness: use renamed IRIs, not ROBOT directly

Because HermiT's construction is order-sensitive (point 1), ROBOT/HermiT is **not** a
reliable completeness oracle on these ontologies: it misses the `MONDO_* ⊑
EFO_0000524` entailments on the real OBO IRIs, but **derives them once the IRIs are
renamed to opaque strings** with the logical axioms left byte-identical — its answer
depends on IRI spelling via HashMap bucketing. ROBOT remains useful for *soundness*
(it asserts nothing this crate contradicts); for *completeness*, cross-check against
ROBOT on an **IRI-renamed** copy of the ontology, or against a hand-checked
entailment. Each EFO `MONDO_* ⊑ EFO_0000524` was confirmed by walking the part-of +
subclass graph to head/neck.

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
