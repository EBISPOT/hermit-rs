# Role-automaton reproducers

Minimal OWL functional-syntax ontologies for the inverse + chain role-automaton
completeness behaviour described in `ROLE_AUTOMATON_CONSTRUCTION.md`. Each is a
self-contained EFO STAR-module fragment small enough to read and to run by hand:

```
hermit -c tests/data/role_automaton/<file>.ofn
```

They are exercised by `tests/role_automaton_completeness_tests.rs`, which also
generates the 24 property-IRI renamings of the issue's four-property pattern.

## The pattern

Property `u` has a chain-bearing sub-property (`a ⊑ u`, `a ∘ b ⊑ a`) **and** a
declared inverse (`InverseObjectProperties(u, ui)`). With `C ≡ ∃u.Z` and
`M ⊑ ∃a.∃b.…∃b.Z`, the role chain lifts the part-of (`b`) steps onto `a ⊑ u`, so:

```
M ⊑ C        (entailed)
```

The entailment does not use the inverse axiom at all. Java HermiT nevertheless
misses it on some spellings of the property IRIs and derives it on others: the
inverse declaration puts `Inv(u)` and `Inv(ui)` into the sub-property dependency
graph as recursion seeds, `connectAllAutomata` walks those seeds in
`java.util.HashSet` order, and if `Inv(u)` is built before `u` then `u` is stored
as the plain mirror of `Inv(u)`, which never saw `u`'s own sub-chain `a ∘ b*`.
Deleting the inverse axiom makes Java derive the subsumption on every spelling.
hermit-rs builds each property's automaton from the sub-properties of both `R` and
`Inv(R)`, so its answer is the same on every spelling (EBISPOT/hermit-rs#5).

## `inverse_chain_completeness.ofn`

The minimal case: `a ⊑ u`, `a ∘ b ⊑ a`, `b` transitive, `InverseObjectProperties(u, ui)`.
Java derives `M ⊑ C` here, and so do we.

## `efo_pattern.ofn`

The same pattern with the real EFO/OBO IRIs it was found on:
`EFO_0000524 ≡ ∃EFO_0000784.UBERON_0000033` (head), `RO_0004027 ⊑ EFO_0000784`,
`RO_0004027 ∘ BFO_0000050 ⊑ RO_0004027`, `BFO_0000050` (part-of) transitive, and
`MONDO_0004785 ⊑ ∃RO_0004027.UBERON_0001711` (eyelid) with eyelid part-of head via
`UBERON_0000019 → UBERON_0004088 → UBERON_0000033`. Java HermiT (ROBOT 1.9.x,
HermiT 1.4.5.519) does **not** derive `MONDO_0004785 ⊑ EFO_0000524` on these IRIs;
hermit-rs does.

## `efo_pattern_renamed.ofn`

`efo_pattern.ofn` with the IRIs renamed to opaque short names and the logical
axioms left identical. Java derives `M ⊑ C` on this file but not on
`efo_pattern.ofn`. hermit-rs derives it on both.
