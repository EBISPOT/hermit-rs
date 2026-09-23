# Java parity handoff

The implementation work is paused at the user's request to conserve credits.
Continue on `rust`; the remaining work is recorded in the issues below.

## Completed and released

[`v2026-sep-22.1`](https://github.com/EBISPOT/hermit-rs/releases/tag/v2026-sep-22.1)
points to `880e7d1c036f5e6b4125b92ce2a9d008f4656f94`.
[Linux CI passed](https://github.com/EBISPOT/hermit-rs/actions/runs/35756467659),
as did the local serial release tests and focused tuple-identity regressions.

- Issue #8: preserve inverse role-chain automaton paths. Regressions cover the
  supplied minimal ontology, axiom order, property renaming, valid entailments,
  and explanations. The full RO input was not supplied for independent checking.
- Import all 598 declared Java test methods, including inherited configurations,
  with an inventory check and original source/fixture provenance.
- Isolate test workers, bound allocations, and kill/reap timed-out processes.
- Fix tuple predicate identity collisions that silently discarded constraints
  on Linux. Keep allocated identities distinct; do not use XOR-based hash keys
  as exact tuple equality.

## Required approach

The user explicitly said: **do not reproduce Java bugs**. Preserve the original
Java fixture/source, establish the corrected behavior independently, document the
evidence, and explicitly state any deliberate deviation from Java faithfulness
in the commit message. The empty-URI cardinality case below is a confirmed example.
Record a corrected replay expectation in [corrections.json](corrections.json),
beside the unchanged trace; see [README.md](README.md).

Run one local build/test/export job at a time. Use `CARGO_BUILD_JOBS=1`,
`OWLMAKE_CLASSIFY_THREADS=1`, and serial test execution. Retain the 512 MiB worker
allocation budget and existing deadlines; do not start a Lima/Docker VM. The user
previously exhausted RAM through a Lima virtual machine.

The default gate accepts only the exact recorded failures and rejects changed
failures or unexpected passes. **A green gate does not mean full Java parity.**
Use `HERMIT_JAVA_STRICT=1` for the actual assertions. Remove resolved exceptions
from `expected-failures.json` and update `RESULTS.md`; do not convert failures into
skips. Keep native test generators in sync with their generated ports.

[Regeneration and test commands](README.md), [measured results](RESULTS.md),
[complete inventory](inventory.json), and [failure baseline](expected-failures.json)
provide the starting point. Java is pinned to
`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`.

## Suggested starting points

The property classifiers now reduce object roles to proxy concepts
`C_R = exists R.M` with a fresh inhabited marker `M`, and data roles to
`C_P = exists P.U` with a fresh unknown datatype `U`, and classify the proxies
with the concept classifier (#22). Their hierarchy looks up
`ObjectInverseOf(owl:topObjectProperty)` and
`ObjectInverseOf(owl:bottomObjectProperty)` as the built-in properties (#26).

The role automata keep a HermiT flaw that no imported case covers:
`buildInversePropertiesMap` records `SubObjectPropertyOf(R ObjectInverseOf(S))`
as if `R` and `S` were inverses, so when `S` is not simple, `forall R.C` also
propagates along `Inv(S)`. With `TransitiveObjectProperty(S)`, `R <= Inv(S)` then
yields `Inv(S) <= R` in class reasoning, `isSubObjectPropertyExpressionOf` and
the property classifiers alike, as in Java.

Two more gaps that no imported case covers, found while fixing #26. The
`DisjointObjectProperties` entailment tests role atoms on the ontology's
tableau, where `owl:bottomObjectProperty` is axiomatized only when the ontology
mentions it; otherwise `DisjointObjectProperties(owl:bottomObjectProperty :r)`
is not entailed, as in Java, although the empty role is disjoint from every
role. And `isFunctional`/`isInverseFunctional` test `owl:Thing <= max 1 P`,
which rejects a non-simple `P` (a transitive property or
`owl:topObjectProperty`) that Java's role atoms answer.

Several datatype failures share missing subtraction of negative ranges or
excluded values during cardinality counting/enumeration. Keep emptiness,
cardinality, and inequality assignment consistent.

Nineteen failing assertions also failed in the pinned Java checkout. These require
investigation of obsolete controls or fixtures, not blindly changing Rust to
match them. The two `BlockingValidatorTest` fixtures are repaired (#32, #33;
see `corrected/` and [RESULTS.md](RESULTS.md)). Issues #35 to #50 are
resolved by a semantic clause comparison (see [RESULTS.md](RESULTS.md)); one
structural control remains (#51). Original Java error traces are retained in the case fixtures and
`upstream-failures.json`.

## Imported Java failures

43 issues cover all 63 failing executable cases. Duplicate inherited failures
are grouped; every issue lists its exact cases, reproduction command, findings,
and acceptance criteria. At the release baseline, 912 imported cases pass and
two overrides are empty in the original Java source.

| Issue | Work | Cases |
| --- | --- | ---: |
| [#9](https://github.com/EBISPOT/hermit-rs/issues/9) | Correct the Java empty-URI cardinality expectation (**resolved**; see [corrections.json](corrections.json)) | 1 |
| [#10](https://github.com/EBISPOT/hermit-rs/issues/10) | Respect excluded URI values in finite pattern/length intersections (**resolved**) | 1 |
| [#11](https://github.com/EBISPOT/hermit-rs/issues/11) | Respect URI exclusions after complementing a length restriction (**resolved** with #10) | 1 |
| [#12](https://github.com/EBISPOT/hermit-rs/issues/12) | Count finite binary ranges after subtracting length restrictions (**resolved**) | 1 |
| [#13](https://github.com/EBISPOT/hermit-rs/issues/13) | Keep individual-reuse classification of Dolce within the worker memory budget (**resolved** with #22) | 1 |
| [#14](https://github.com/EBISPOT/hermit-rs/issues/14) | Count dateTime boundary values after subtracting an open interval (**resolved**) | 1 |
| [#15](https://github.com/EBISPOT/hermit-rs/issues/15) | Enumerate finite mixed numeric ranges for inequality assignment (**resolved**) | 1 |
| [#16](https://github.com/EBISPOT/hermit-rs/issues/16) | Subtract enumerated exclusions from mixed numeric value spaces (**resolved** with #15) | 1 |
| [#17](https://github.com/EBISPOT/hermit-rs/issues/17) | Detect an empty plain-literal range after excluding its sole value (**resolved**) | 1 |
| [#18](https://github.com/EBISPOT/hermit-rs/issues/18) | Infer data-property subsumption forced by singleton values (**resolved** with #22) | 3 |
| [#19](https://github.com/EBISPOT/hermit-rs/issues/19) | Return only the most specific direct individual types (**resolved**) | 3 |
| [#20](https://github.com/EBISPOT/hermit-rs/issues/20) | Correct property hierarchy axioms emitted by printHierarchies (**resolved** with #22) | 3 |
| [#21](https://github.com/EBISPOT/hermit-rs/issues/21) | Avoid declaring built-in bottom classes in collapsed hierarchies (**resolved**) | 3 |
| [#22](https://github.com/EBISPOT/hermit-rs/issues/22) | Infer role subsumption implied by chains and existential restrictions (**resolved**) | 3 |
| [#23](https://github.com/EBISPOT/hermit-rs/issues/23) | Infer role subsumption forced by nominals and transitivity (**resolved** with #22) | 3 |
| [#24](https://github.com/EBISPOT/hermit-rs/issues/24) | Classify role subsumption with chains, transitivity and symmetry (**resolved** with #22) | 3 |
| [#25](https://github.com/EBISPOT/hermit-rs/issues/25) | Recognize equivalent data properties forced to a common singleton range (**resolved** with #22) | 3 |
| [#26](https://github.com/EBISPOT/hermit-rs/issues/26) | Normalize inverse built-in roles in property hierarchy queries (**resolved**) | 3 |
| [#27](https://github.com/EBISPOT/hermit-rs/issues/27) | Recognize object properties equivalent to the universal role (**resolved** with #22) | 3 |
| [#28](https://github.com/EBISPOT/hermit-rs/issues/28) | Reject the first unsatisfiable Widmann case under core blocking (**resolved**) | 1 |
| [#29](https://github.com/EBISPOT/hermit-rs/issues/29) | Reject the second unsatisfiable Widmann case under core blocking (**resolved** with #28) | 1 |
| [#30](https://github.com/EBISPOT/hermit-rs/issues/30) | Reject the third unsatisfiable Widmann case under core blocking (**resolved** with #28) | 1 |
| [#31](https://github.com/EBISPOT/hermit-rs/issues/31) | Reject intersections of XMLLiteral and disjoint datatype spaces (**resolved**) | 1 |
| [#32](https://github.com/EBISPOT/hermit-rs/issues/32) | Repair the obsolete annotated-equality blocking-validator fixture (**resolved**; see `corrected/`) | 1 |
| [#33](https://github.com/EBISPOT/hermit-rs/issues/33) | Repair the obsolete one-invalid-block validator fixture and check its assertions (**resolved** with #32) | 1 |
| [#34](https://github.com/EBISPOT/hermit-rs/issues/34) | Apply description-graph rules to anonymous graph vertices (**resolved**) | 1 |
| [#35](https://github.com/EBISPOT/hermit-rs/issues/35) | Compare datatype clausification semantically: testDataComplementOf3 (**resolved**) | 1 |
| [#36](https://github.com/EBISPOT/hermit-rs/issues/36) | Compare datatype clausification semantically: testDataComplementOf4 (**resolved** with #35) | 1 |
| [#37](https://github.com/EBISPOT/hermit-rs/issues/37) | Compare datatype clausification semantically: testDataPropertiesDataComplementOf1 (**resolved** with #35) | 1 |
| [#38](https://github.com/EBISPOT/hermit-rs/issues/38) | Compare datatype clausification semantically: testDataPropertiesDataComplementOf2 (**resolved** with #35) | 1 |
| [#39](https://github.com/EBISPOT/hermit-rs/issues/39) | Compare datatype clausification semantically: testDataPropertiesDataOneOf1 (**resolved** with #35) | 1 |
| [#40](https://github.com/EBISPOT/hermit-rs/issues/40) | Compare datatype clausification semantically: testDataPropertiesDataOneOf2 (**resolved** with #35) | 1 |
| [#41](https://github.com/EBISPOT/hermit-rs/issues/41) | Compare datatype clausification semantically: testDataPropertiesDataOneOf3 (**resolved** with #35) | 1 |
| [#42](https://github.com/EBISPOT/hermit-rs/issues/42) | Compare datatype clausification semantically: testDataPropertiesDataOneOf4 (**resolved** with #35) | 1 |
| [#43](https://github.com/EBISPOT/hermit-rs/issues/43) | Compare datatype clausification semantically: testDataPropertiesHasValue1 (**resolved** with #35) | 1 |
| [#44](https://github.com/EBISPOT/hermit-rs/issues/44) | Compare datatype clausification semantically: testDataPropertiesHasValue2 (**resolved** with #35) | 1 |
| [#45](https://github.com/EBISPOT/hermit-rs/issues/45) | Modernize the transitive-role clausification control without weakening semantics (**resolved**; compared by automaton language) | 1 |
| [#46](https://github.com/EBISPOT/hermit-rs/issues/46) | Compare clausification auxiliaries modulo consistent renaming (**resolved** with #35) | 1 |
| [#47](https://github.com/EBISPOT/hermit-rs/issues/47) | Restore the nominal clausification control: testNominals1 (**resolved** with #45) | 1 |
| [#48](https://github.com/EBISPOT/hermit-rs/issues/48) | Restore the nominal clausification control: testNominals2 (**resolved** with #45) | 1 |
| [#49](https://github.com/EBISPOT/hermit-rs/issues/49) | Restore the nominal clausification control: testNominals3 (**resolved** with #45) | 1 |
| [#50](https://github.com/EBISPOT/hermit-rs/issues/50) | Restore the nominal clausification control: testNominals4 (**resolved** with #45) | 1 |
| [#51](https://github.com/EBISPOT/hermit-rs/issues/51) | Correct the upstream key-normalization expectation that drops a data property | 1 |

## OWL WG conformance

The separate suite has 212 passes and 147 explicit skips across 359 scoped cases.
These three issues cover the 143 RDF parsing skips and both checks for each of
the two timed-out reasoning cases. They are separate from the 63 Java failures.

- [#52: Expand RDF parser coverage for 143 skipped OWL WG cases](https://github.com/EBISPOT/hermit-rs/issues/52)
- [#53: Resolve the OWL WG description-logic 208 reasoning timeout](https://github.com/EBISPOT/hermit-rs/issues/53)
- [#54: Resolve the OWL WG description-logic 209 reasoning timeout](https://github.com/EBISPOT/hermit-rs/issues/54)
