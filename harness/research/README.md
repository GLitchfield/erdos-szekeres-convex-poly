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
