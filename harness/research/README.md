# Research library catalog

`catalog.json` is the small discovery surface for reusable research code and
supported `es` workflows. Query it before writing a new Python evaluator or
one-off workflow:

```text
es lib search "recursive bounds"
es lib show research.recursive-bounds
es lib list [--kind primitive|workflow]
```

Search and list deliberately return only an ID, kind, title, summary, and
(for search) a deterministic lexical score. `lib show` is the drilldown for
the curated API signature, short example, precise semantics, and source
reference. None of these commands imports or executes a catalogued source.

## Catalog convention

The document has `schema_version: 1` and an `entries` list. Each entry has:

- `id`: stable lowercase dotted or hyphenated identifier;
- `kind`: `primitive` for reusable Python code or `workflow` for a supported
  `es` command surface;
- `title` and `summary`: compact discovery text;
- `keywords`: plain lexical aliases used for ranking;
- `api`: the callable signature, or the public `es` command for workflows;
- `example`: a short invocation, not a source excerpt;
- `semantics`: the input domain and interpretation needed to reuse it safely;
- `source.path` and `source.symbols`: a project-relative Python file and its
  statically declared functions/classes.

Keep entries narrow enough that one result answers one reuse question. Add
keywords users are likely to search, including singular/plural or established
project terminology when useful. Workflow entries should advertise `es`
commands as their API; their internal Python source is only an integrity and
navigation reference.

Prefer `harness.research` primitives over the legacy scripts they retain or
wrap. Legacy entries remain discoverable for capabilities not yet promoted,
and their semantics must say explicitly that Python enumeration is distinct
from a kernel-compiled Lean result.

Every catalog load resolves sources inside the project, parses them with the
standard-library AST parser, and checks every named symbol. A missing file,
renamed symbol, malformed entry, or invalid source fails the command with the
entry ID and stale reference. Update the catalog in the same change that
renames or removes a listed symbol.

`research.singleton-cuts` retains the singleton enumeration reused by the R13
normal-form and exchange probes. Its example uses the compiled evaluator;
run it through `es job run` as required by AGENTS.md. Both parts must contain
a child. Zero values are retained, and the complementary maxima sum to k-1.
The frozen diagnostic fixture is `examples/singleton-cuts-v1.json`; it gives
no Lean proof of a normal form.

`research.cup-cap-chains`, `research.lazy-strong-gons`, `decomposable.label-sets`
and `decomposable.band-partitions` (modules `chains.py`, `decomposable_sets.py`,
`band_partitions.py`) retain the chain, strong-set, label-tree and BDL
band-partition helpers that the 3 Oct runs copied between directories
(`bl.py`, `dec.py`, `sig.py`, `lightgon.py`); those run files are unchanged.
All three modules share one convention: `cup[(i, j, k)]` is True for a cup,
and sets of at most 2 points are both cups and caps. `strong_number` and
`find_gon` assume a one-change colouring. Exact class enumeration stays in
`decomposable.coloring-enumeration` and is reached through
`decomposable_masks`. The frozen fixture `examples/band-partitions-v1.json`
holds the audit's exhaustive per-n BDL, P, PF and P' counts. The tests
reproduce them for n <= 7. Runnable examples: `examples/band_partitions_demo.py`
and `examples/strong_gons_demo.py`. The SAT helpers need python-sat, which
the `es` venv lacks, so their tests skip there. Everything here is diagnostic
evidence, not Lean proof.

`research.endpoint-slot-profiles` provides pure child endpoint refinement,
run-to-slot expansion and marker-barrier restriction. It keeps every finite
child slot and treats each removed slot as an opposite endpoint constraint;
it does not contract runs or evaluate the unrestricted maximum. Public inputs
are validated: square nonnegative integer upper-triangular matrices, distinct
retained indices, legal capacity split and boolean barriers. The refinement
formula has an extension-path hand derivation; its independent legacy-signature
fixtures establish finite regression agreement, not a Lean equivalence theorem.
Original R24 sources and the full160-state fixture remain under
`runs/r24-sol-20261003/`; the checked-in fixture retains16 diagnostic states.

Run the small example from the repository root:

```text
es job run --why "endpoint profile example" --out runs/endpoint-profiles-demo.json \
  --mem 2G -- bash -c 'PYTHONPATH=. python3 \
  harness/research/examples/endpoint_profiles_demo.py > runs/endpoint-profiles-demo.json'
```

`decomposable.root-cuts` enumerates valid lower parts of an ordered triple
coloring root through a vertex implication graph. Its SCC order has width at
most two, so all roots are unions of one or two principal reachability sets.
Every component transversal is strong. Its interior cup representatives
collapse to one component, and its interior cap representatives do likewise;
hence there are at most four components and four roots for ANY complete
coloring. The retained four-point diamond attains four roots.
It accepts complete Boolean colorings, including those that fail one-change:
a root cut alone does not certify hereditary decomposability. The retained
source is the R25 root-graph investigation; tests compare every arbitrary
coloring through five points against the direct mixed-triple rule and check
every component transversal by the defining strong quadruples, including
non-one-change inputs. Run the
solver-free example `examples/root_cuts_demo.py` through a guarded `es` job.

`research.triple-metrics` retains the R25 solver-free exact finite evaluator.
It checks every triple of a monochromatic chain and every defining quadruple
of a strong set, including arbitrary colorings that fail one-change. It
supports repeated subset metrics and ALL maximum-chain endpoint extrema;
empty maxima are zero with empty endpoint sets. Construction and lazy strong
evaluation enumerate subsets, so this is exponential small-instance code,
not the consecutive-turn dynamic program or a decomposition/Lean certificate.
Input is copied and strictly validated using the same contract as root cuts.
The self-contained `examples/triple-metrics-v1.json` preserves the non-one-
change trap and R25 n8/n11/n13 witnesses. Run `examples/triple_metrics_demo.py`
through `es job run`; the primitive owns no execution or storage workflow.
