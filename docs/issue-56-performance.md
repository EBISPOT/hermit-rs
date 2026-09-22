# Issue #56: property read-off and classification

The benchmark uses [cohort-ontology at `91e16d8`](https://github.com/EBISPOT/cohort-ontology/tree/91e16d84ad737f7f1b4677703ef6e0699caf288f),
merging `coho-edit.owl` and the 12 local import/component files in its catalog.
It has 52 classes, 111 object properties and 331 named individuals. After removing
ontology IDs, import directives and ontology annotations, the merged input has
4,022 axioms, matching the Java OWLAPI loader. Earlier Rust profiling retained
eight ontology annotations (4,030 components); the logical input is the same.

Measurements below were taken on macOS ARM64 on 2026-09-22, using release builds
and one classification worker. Parsing is excluded from the reasoner timings.
These are individual observations, not statistical benchmark estimates.

| Operation | Observed result |
| --- | --- |
| Previous index, as reported in [#56](https://github.com/EBISPOT/hermit-rs/issues/56) | Still unfinished when stopped at 136 seconds |
| New shared index construction | 1.222 seconds |
| New index plus querying/exporting every property | 1.227 seconds; 3,633 named-individual pairs |
| New index in a separate memory-monitored run | 1.142 seconds; 316.8 MiB maximum sampled RSS |
| Rust classification before this change, one worker | 15.591 seconds |
| Rust classification after this change, one worker | 12.547 seconds |
| Java classification, one active processor | 22.706 seconds |

Memory was sampled every 250 ms, so it is not an exact peak. The earlier issue's
timings used a different invocation and should not be treated as a controlled
speedup comparison. The pair count includes asserted and imported consequences;
it is the complete index sweep, not owlmake's filtered assertion export.

## What caused the cost

The original ontology compiles to 22,819 DL clauses, including 22,625 normalized
concept inclusions after role-automaton rewriting. Its initial saturation took
about half a second including preprocessing. There are 73 complex named roles
(146 expressions including inverses). Generating markers for all 331 individuals
therefore multiplies a large automaton program by thousands of irrelevant pairs.

The index now reuses the permanent automata and compiled clause programs, creates
only marker deltas, and batches them at individual boundaries. Conservative role
liveness removes impossible transition labels from fresh marker automata. The
initial model identifies named sources that could start a relevant path. The
original constraints and entailment checks remain unrestricted. See
[the query documentation](object-property-instances.md) for the algorithm and
regression coverage.

Classification has a separate cost: repeated model construction, plus copying,
converting and hashing internal automaton concepts during model read-off. A
sampling profile exposed that extra work in `ConceptStreamingPool::recv` and
classification's label processing. Java filters labels to the classes being
classified while reading the extension tables. Rust now discards internal
auxiliary concepts at that stage too. Repeated saturation remains necessary in
this implementation; classification still takes roughly 12.5 seconds in the
serial measurement above. The timing difference also includes run/order variance.

## Correctness and Java comparison

Java was pinned to `37ec30aced32ac81ebecc5e33fad255ddefcb4c3`. Its unfiltered
property index did not finish within a 90-second local limit with `-Xmx1536m`
and `-XX:ActiveProcessorCount=1`. That bounded run is not a general claim about
Java performance with other resource limits.

Instead, 54 cohort queries were checked independently with Java's tableau:
the first, middle and last sorted positive pair for each nonempty role (removing
duplicates), absent-pair controls, and five empty-role controls. All 54 agreed
with Rust. Each query `r(a,b)` was checked by adding
`ClassAssertion(ObjectAllValuesFrom(r ObjectComplementOf(ObjectOneOf(b))) a)`
and testing inconsistency, using the permanent role automata. This avoids relying
on either implementation's property-instance index. It is a sample, not an
exhaustive cross-check of all 3,633 pairs.

The regression suite also compares every named pair in small ontologies with
full-ontology entailment checks, covering inverses, equality, anonymous paths,
existentially generated edges, self restrictions, reflexivity and disjunctions.

There is one intentional deviation from Java faithfulness: Java's
`InstanceManager` marks property initialization complete at `length - 1`, which
can skip the final individual. With 73 transitive roles and 70 individuals in a
ring on one role, Java returned 4,831 pairs instead of the entailed 4,900. Rust's
final-batch regression requires all 4,900 forward and inverse pairs.

## Reproduce the Rust measurements

Check out the pinned cohort revision separately, then run from hermit-rs:

```sh
CARGO_BUILD_JOBS=1 cargo build --release --example profile_reasoner
python3 - /path/to/cohort-ontology/src/ontology instances > pairs.tsv <<'PY'
import os
from pathlib import Path
import subprocess
import sys
import xml.etree.ElementTree as ET

root = Path(sys.argv[1])
files = [root / "coho-edit.owl"]
files += [root / entry.attrib["uri"]
          for entry in ET.parse(root / "catalog-v001.xml").iter()
          if entry.tag.endswith("}uri")]
subprocess.run(
    ["target/release/examples/profile_reasoner", sys.argv[2], *map(str, files)],
    env=dict(os.environ, OWLMAKE_CLASSIFY_THREADS="1"), check=True,
)
PY
```

Replace `instances` with `classify` to profile classification. Timings and counts
are written to stderr; instance pairs are tab-separated on stdout. The example
reads Functional Syntax regardless of filename extension. It does not resolve
imports itself: all files in the closure must be supplied explicitly. Run one
benchmark at a time to keep memory use bounded.
