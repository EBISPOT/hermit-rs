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
iterated in a fixed order — `java_map_order_key` (Java's `HashMap` bucket order over
the OWLAPI hash codes, to keep the automaton *shape* close to Java's) for the seed
and map walks, `prop_sort_key` (named properties before their inverses, then by
IRI) for the sub-property splices. The output is fully deterministic across runs and, on small
EFO modules, byte-identical to Java HermiT's `--dump-clauses` (modulo
internal-concept renaming).

## 2. Forward sub-chains survive inverse + chain hierarchies (completeness)

Sub-property edges are recorded only forward in the dependency graph: `a ⊑ R` is
stored, but its mirror `Inv(a) ⊑ Inv(R)` is not. A declared inverse
`InverseObjectProperties(R, Ri)` adds the edges `R → Inv(Ri)` and `Ri → Inv(R)`, so
`Inv(R)` and `Inv(Ri)` become sinks of the graph and therefore recursion seeds.
When `R` also has a chain-bearing complex sub-property (`a ⊑ R` with `a ∘ b ⊑ a`),
Java's `buildCompleteAutomataForProperties` behaves differently depending on which
seed it walks first:

* `Inv(Ri)` first: its sub-property `R` is built directly from `a`, keeps `a ∘ b*`,
  and `finalizeConstruction` stores `Inv(R)` as the mirror. Correct.
* `Inv(R)` first: Java splices only `Inv(R)`'s **own** sub-properties (`Ri`); the
  sub-properties of `Inv(Inv(R)) = R` are consulted only to decide that `Inv(R)` is
  not a leaf. `finalizeConstruction` then stores `R` as the plain mirror of that
  automaton, so `a ∘ b*` is silently dropped, `∀R.C` under-propagates and valid
  subsumptions are missed.

The walk order is `java.util.HashSet` bucket order over the property IRIs, so
Java's answer changes under renaming (12 of the 24 spellings of the four-property
pattern in EBISPOT/hermit-rs#5 fail in Java) and is non-monotonic: deleting the
inverse axiom, which the derivation does not use, makes every spelling succeed.

**How it is handled:** when a non-leaf property `R` is built,
`build_complete_automaton_inner` splices the mirrored complete automaton of every
`t ⊑ Inv(R)` into `R` alongside `R`'s own sub-properties. `t ⊑ Inv(R)` makes every
`t`-chain `x → y` an `R`-edge `y → x`, so `mirror(L(t)) ⊆ L(R)` and the splice is
sound. With both sides present in whichever automaton is built first, the mirror
written by `finalizeConstruction` is complete too, and the result no longer depends
on the seed order. Both sub-property sets are iterated in `prop_sort_key` order.

The one `t ⊑ Inv(R)` left out is `R`'s *declared* inverse (`InverseObjectProperties(R, t)`
puts both `R → Inv(t)` and `t → Inv(R)` in the graph). Those pairs are reconciled by
the final inverse-map pass of `create_automata`, which enriches each side with the
mirror of the other's complete automaton; splicing them during construction as well
doubled every branch of both automata (the port does not minimise automata, so the
duplicates became clauses) and made EFO classification measurably slower.

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
derive them) and are derived.

This is a deliberate departure from Java HermiT. An exact reproduction of Java's
answers was not on the table anyway: the seed order is modelled with
`java_map_order_key`, and on the 24 spellings of the issue's pattern the current
model disagrees with ROBOT/HermiT on 6 of them, so "bug-for-bug" would have meant
a *different* set of missed entailments, not Java's.

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
