# Java test parity

Remaining work is indexed in [HANDOFF.md](HANDOFF.md), with a GitHub issue for every outstanding item.


These tests are ported from the `java` branch of EBISPOT/hermit-rs at
`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`. The original Java test sources and
resources are preserved under `upstream/`, under the repository's LGPL license.

`inventory.json` accounts for all 598 declared test methods. This includes the
two parameterized OWL WG entry points, which are exercised by
`tests/owl_wg_conformance.rs`, and two empty overrides that Java disables.
Inherited reasoner tests are also recorded under their concrete suite names so
individual-reuse and core-blocking configurations are exercised independently.

There are two forms of executable port:

* `cases/` contains query traces recorded while the original Java assertions run.
  `java_parity` replays each operation against Rust and compares the complete
  result, including equivalence groups and exceptions. Ontology snapshots are
  deduplicated in `ontologies/`. Classification and precomputation calls are
  replayed before subsequent queries. No JVM or network is needed to run tests.
* `native-cases.json` identifies direct Rust ports for private tableau operations,
  datatype value sets, indices, and key clausification. These retain the original
  assertion scenarios. Clause comparison permits consistent variable renaming;
  normalization comparison treats OWL set-valued operands as unordered.
  Replayed clausification controls are compared semantically by
  `tests/support/clause_compare.rs`. Literals are compared by data value,
  enumerations and clause atoms as sets, each clause's variables up to a
  bijective renaming, fresh auxiliary predicates up to one consistent renaming,
  and transitive-role automaton states by the language they accept. Everything
  else must match exactly. The default prefix is the original fixture's
  ontology IRI, as in Java.

A trace is not evidence that Rust passes it. `expected-failures.json` lists the
remaining discrepancies explicitly. Every case still executes: normal CI checks
that passing cases stay passing and that each recorded discrepancy fails at the
same assertion. Changed failures and unexpected passes fail the gate. Cases
labelled `XFAIL` are **not Rust conformance passes**. Use `HERMIT_JAVA_STRICT=1`
to make every mismatch fail normally and obtain the actual parity count.
See [RESULTS.md](RESULTS.md) for the measured results and remaining discrepancies.

`corrections.json` records Java expectations that contradict the OWL 2 or XSD
specifications. Each entry names the recorded operation, or several under
`operations`, and keeps Java's value beside the corrected one (for a list, the
Java elements to `remove`), with the specification evidence, the Java cause
and independent regression tests. Traces stay as exported: the replay runner,
and the native datatype port that reads the same traces, substitute the
corrected value, in strict mode too, only while the trace still records that
Java value. A corrected value `{"invalid": error}` records that the
ontology must be rejected: the reasoner's creation becomes an `invalid`
operation and its queries are dropped. The inventory check validates every entry.

Missing operations, empty recordings, unexpected exceptions, timeouts, and
allocation failures are failures, with the same explicit exception policy. `upstream-failures.json` separately preserves assertions that already fail
in the pinned Java checkout; the original Java aggregate suite excludes the
structural tests and `BlockingValidatorTest`. `corrected/` holds repaired copies
of obsolete upstream fixtures, each with a header explaining the repair; the
native port reads the corrected `BlockingValidatorTest` (issues #32 and #33).

Run the inventory check and tests:

```sh
python3 scripts/java-tests/check_inventory.py
HERMIT_JAVA_STRICT=1 CARGO_BUILD_JOBS=1 OWLMAKE_CLASSIFY_THREADS=1 cargo test --release --test java_parity -- --test-threads=1
HERMIT_JAVA_STRICT=1 CARGO_BUILD_JOBS=1 OWLMAKE_CLASSIFY_THREADS=1 cargo test --release --lib java_ -- --test-threads=1
CARGO_BUILD_JOBS=1 cargo test --test java_collections --test rdf_parse_completeness
CARGO_BUILD_JOBS=1 OWLMAKE_CLASSIFY_THREADS=1 cargo test --release --test owl_wg_conformance -- --test-threads=1
```

Each replay case and each potentially expensive native test runs in a separate
process with a 120-second deadline and a 512 MiB allocation budget. Timed-out
children are killed and reaped. The WG runner uses a 15-second per-case deadline
and checks every scoped outcome against `tests/owl_wg/expected.tsv`; a newly
skipped case, missing identity, wrong answer, or stale skip exception fails.

To regenerate traces, first build the pinned Java checkout's main classes and
its dependency classpath, then run:

```sh
python3 scripts/java-tests/export.py /path/to/java-checkout tests/java reasoner.ReasonerTest
```

Additional class names or `class#method` selections can be supplied. The exporter
uses a 256 MiB Java heap and records the original JUnit assertion failures. The
NI and blocking-validator translations can be regenerated with `port_ni.py`
and `port_blocking.py`. Preserve the pin and rerun the inventory check when
changing the imported suite.
