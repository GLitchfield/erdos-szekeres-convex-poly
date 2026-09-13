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
