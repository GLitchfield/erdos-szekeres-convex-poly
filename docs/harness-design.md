# `es` harness — detailed design

Version 1, 3 September 2026. This document is the implementation contract for the
blueprint harness of the `erdos-szekeres-convex-poly` Lean project. It is written
for a fresh Claude Code session that has this repository checked out and nothing
else in context. Read sections 1–3 before touching anything; section 12 is the
build order; section 13 is the acceptance checklist to report against.

Companion documents in `docs/`: `research-plan-2026-09-03.md` (the workstreams the
seed nodes come from) and `review-2026-09-03.md` (why the project needs this).

Proposed automation extension: [Automation plan, 12 September 2026](automation-plan-2026-09-12.md)
defines the staged workflow, completion-delivery, proof/probe, and usage-accounting work.
It is a proposal; it does not describe features already implemented.

---

## 1. Background a fresh session needs

**The project.** A Lean 4 + mathlib formal research repository attacking the exact
Erdős–Szekeres conjecture `ES(n) = 2^(n-2)+1`. Public statement in
`ErdosSzekeres/Basic.lean` (`ErdosSzekeresConjecture`, `ForcesConvexPolygon`,
`HasSharpnessExample`). Sweep/orientation model in `Sweep.lean`, `StrongPolygon.lean`,
`Decomposable.lean`. Toolchain pinned in `lean-toolchain` (v4.29.1 at time of writing).

**The current build.** One Lake package, one `lean_lib` rooted at `ErdosSzekeres.lean`,
which imports ~250 hand-written modules. About 11,000 *generated* modules (names
matching `*CNFChunk*`, `*CNFRaw*`, `*CNFMid*`, `*CheckpointSegment*`, `*SemanticSegment*`,
`*SupportSegment*`, `*ClauseChunk*`, `*CNFGenerated`, `*CheckpointData/*`) hold SAT/LRAT
certificate material produced by `scripts/generate_*.py` and checked through mathlib's
`FromLRAT` plus a project command `lrat_checkpoint_reify` (`LRATCheckpoint.lean`).
`make test` greps `ErdosSzekeres/` for `sorry|admit` and fails on any hit. A full
rebuild takes on the order of an hour; a guarded single-thread build has been timing
out at 1,800 s inside generated modules, so recent hand-written work has only been
checked by the language server.

**The problem the harness solves.** Project state (what is proved, what is open, what
depends on what) currently lives in ~4 MB of prose (`docs/wayfinder/map.md`,
`frontier-portfolio.md`, 129 tickets). Agents must read it to know the state and
drift from it. The harness replaces that with state *derived from Lean*: a node is
open iff its compiled proof depends on `sorryAx`. Modeled on the DAG-of-statements
approach used for the Fermat's Last Theorem formalization (Prove2Me), kept
repository-local.

**What is out of scope.** Choosing which nodes exist, judging mechanisms, adversarial
review of statements. Those stay with the humans (Gavin, with Sol/Fable reviews).

---

## 2. Principles (non-negotiable)

1. **Lean is the source of truth.** Status, dependencies, axioms, and statement
   identity are read from the compiled environment on every `extract`. The harness
   never records "proved" on an agent's say-so. If the SQLite cache and Lean
   disagree, Lean wins and the cache is rebuilt.
2. **Git holds everything authoritative that is small and reviewable:** the
   statement lock, the axiom allowlist, retired-node notes, the generated status
   file (committed so diffs show frontier changes). SQLite holds only what git
   handles badly: claims, the extractor cache, jobs, attempts.
3. **Statements are reviewed; proofs are not.** A statement is approved once, on
   creation or restatement (CODEOWNERS). Proofs of existing nodes merge on green.
4. **Conjecture nodes need a passed falsifier before they can be claimed.**
5. **Every session starts from the frontier**, injected by a `SessionStart` hook.
6. **Generic tool, project-specific config.** Nothing in `tools/es/` may name an
   ES-specific module, theorem, or path; all of that comes from `harness/config.toml`.
   The harness will be extracted into its own repository once its command surface
   is stable (target: two weeks), so build it as if it already were.

---

## 3. Target repository layout

```
erdos-szekeres-convex-poly/
├── lakefile.toml                      # one package, three lean_lib targets + one lean_exe (see §4)
├── lean-toolchain
├── ErdosSzekeres.lean                 # root of ESCore (unchanged role)
├── ErdosSzekeres/                     # hand-written modules (ESCore)
│   └── Certificates/                  # ALL generated modules move here (ESCertificates)
├── ESBlueprint.lean                   # root of ESBlueprint: imports every node module
├── ESBlueprint/                       # one module per node: ESBlueprint/<WS>/<NodeName>.lean
├── harness/
│   ├── config.toml                    # project-specific configuration (§6)
│   ├── statements.lock                # node → approved type hash (§7.3)
│   ├── allowlist.json                 # axiom allowlist (§7.4)
│   ├── destinations.txt               # ESCore theorems included in the audit (one name per line)
│   ├── certificate_consumers.txt      # ESCore modules allowed to import ESCertificates
│   ├── restatements.md                # append-only log written by `es node restate`
│   ├── retired.md                     # append-only log of refuted/retired nodes
│   ├── falsifiers/                    # falsifier scripts referenced by @falsifier tags
│   ├── dataset/                       # Workstream D extremal-structure dataset (inputs to falsifiers)
│   ├── falsify/                       # generated: <node>.json falsifier results
│   ├── nodes.json                     # generated by `es extract`
│   ├── index.json                     # generated by `es extract`
│   └── status.md                      # generated by `es extract`; committed
├── tools/es/                          # the harness (Python package, own pyproject.toml)
│   ├── pyproject.toml
│   ├── es/                            # package: cli, mcp_server, config, lean, model, store, commands/
│   ├── lean/Extract.lean.tmpl         # extractor template, materialized into ESBlueprint/Extract.lean
│   └── tests/
├── .mcp.json                          # registers the MCP server for Claude Code
├── .claude/settings.json              # hooks (§10)
├── .github/workflows/ci.yml           # §10
├── CODEOWNERS
└── CLAUDE.md                          # short rules (§10); AGENTS.md is rewritten to match in M6
```

`docs/wayfinder/` stays as history. Nothing new is written there after M6.

---

## 4. Lake restructuring

Keep a single Lake package (no cross-package version churn) with three library
targets and one executable. Layering is enforced by `es layers`, not by Lake.

```toml
# lakefile.toml (sketch — adapt to the existing file; keep mathlib/hammer requires as they are)
name = "erdos-szekeres-convex-poly"
defaultTargets = ["ESCore"]

[[lean_lib]]
name = "ESCertificates"
roots = ["ErdosSzekeres.Certificates"]
globs = ["ErdosSzekeres.Certificates.*"]    # every module under ErdosSzekeres/Certificates/

[[lean_lib]]
name = "ESCore"
roots = ["ErdosSzekeres"]                    # builds the root module and its imports

[[lean_lib]]
name = "ESBlueprint"
roots = ["ESBlueprint"]

[[lean_exe]]
name = "es-extract"
root = "ESBlueprint.Extract"                 # materialized from tools/es/lean/Extract.lean.tmpl
```

**Moving the generated modules.** Every generated module moves from
`ErdosSzekeres/<Name>.lean` to `ErdosSzekeres/Certificates/<Name>.lean`, so its module
name becomes `ErdosSzekeres.Certificates.<Name>`. This is a mechanical change with two
parts: (a) update every `scripts/generate_*.py` to emit into the new directory and
new module name; (b) rewrite imports in the hand-written consumer modules
(`ES5Certificate`, `E3State*Certificate`, `HalfPure*`, `PredecessorHalfFin13`,
`Mixed567*`, `DiagonalCupBlocksK9*`, `ExtremeExchangeK9*`, `Pascal556*`,
`SynchronizedFiveFan*`, `LRATCheckpoint*`). The exact list of consumer modules is
whatever imports a generated module today; produce it with a script, do not guess.
Which modules are "generated" is defined by `harness/config.toml`'s
`certificates.generated_patterns`, and the same list drives the move. Declarations
inside generated files keep their `namespace ErdosSzekeres` so theorem names do not
change; only module names change.

**Build time.** The point of the split is caching: `ESCertificates` oleans are built
once and restored from cache (CI) or simply kept (`.lake/build`, never cleaned by the
harness). Do not run builds with a single thread as the old guard did; use Lake's
defaults, and put a wall-clock budget on `ESCore` (config `build.core_budget_min`,
default 10) as a regression guard against anything that forces a certificate rebuild.

**Memory guard.** Every Lean invocation runs in a transient user cgroup with a
`MemoryMax` from config, and is *refused* (nothing runs, exit 3) unless cap + 6 GiB
is available. A refusal is reported as `es.errors.Refused`, a `LeanError` that
`es node add` treats differently from an elaboration failure: the freshly written
module and its root import are kept, no lock entry is written, and repeating the
identical `es node add` later completes the registration (a re-run whose rendered
module matches the file on disk is accepted; different content is still "already
exists"). When only the full extract is refused, `es node add` falls back to a
*targeted* extract over the new module's import closure alone (cap
`extract.targeted_memory_max`, default 12G; attempted only if the closure holds at most
`extract.targeted_max_olean_gib` of project oleans, default 4): enough to hash the
statement and write the lock entry. The duplicate check is then limited to that closure
and `nodes.json`/`status.md` are not rewritten; the next full `es extract` does both.
`ES_EXTRACT_MEMORY_MAX=<cap>` overrides `extract.memory_max` for one invocation; every
fresh extractor run logs an `extract` event with its measured `peak_mib`. Note that the
cgroup counts the page cache of mmap'd oleans, so a capped full extract (the root imports
every certificate) thrashes at the cap rather than failing: run it when the machine is free.

**`sorry` policy.** The existing grep in `make test` must be narrowed to
`ErdosSzekeres/` so that `ESBlueprint/` may contain `sorry`. Lean's own `sorry`
warning is fine in `ESBlueprint`; CI treats it as expected there and as an error in
`ESCore`.

---

## 5. Nodes

### 5.1 One node = one module

A node is a module `ESBlueprint/<WS>/<NodeName>.lean` containing exactly one *main*
declaration plus any private helpers. `ESBlueprint.lean` imports all node modules
(maintained by `es node add`). Node names are the fully qualified Lean name of the
main declaration (e.g. `ErdosSzekeres.fin15_endpoint`); the module path is derived
from the workstream letter and a CamelCase form of the short name.

### 5.2 Docstring tags

The main declaration's docstring is its natural-language description followed by
tags, one per line, `@tag value`:

| Tag | Required | Meaning |
| --- | --- | --- |
| `@node` | yes | marks the main declaration of the module |
| `@ws` | yes | workstream letter `A`–`G` (validated against config) |
| `@kind` | yes | `formalization` (known mathematics), `conjecture` (needs a passed falsifier before claim), `refutation` (statement of the form `¬P`; proof is a compiled counterexample) |
| `@depends` | no | comma-separated Lean names the proof is *expected* to use; replaced by actual dependencies once a proof exists; divergence is reported, not an error |
| `@consumer` | yes unless `@dangling-ok` | the existing theorem (in ESCore or ESBlueprint) that consumes this node |
| `@dangling-ok` | no | explicit opt-out of `@consumer`, with a reason after it |
| `@falsifier` | required for `conjecture` | path under `harness/falsifiers/` |
| `@measure` | no | free text: the decreasing measure for induction-shaped nodes |
| `@target` | no | ESCore module the closed node should be moved under (default from config: `ErdosSzekeres.Closed.<WS>`) |

Example:

```lean
import ErdosSzekeres

namespace ErdosSzekeres

/-- Every 15-vertex one-change coloring without a strong six-set has an eight-point
support without a strong five-set. With `strongSixCardinalityCeiling` this closes
`predecessorHalfSubsetAt_six`.
@node
@ws A
@kind formalization
@depends ErdosSzekeres.predecessorHalfFin15_or_exactMaximumObstruction
@consumer ErdosSzekeres.predecessorHalfSubsetAtSixMiddle_of_fin15Endpoint
@falsifier fin15_endpoint.py
-/
theorem fin15_endpoint (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ∃ support : Finset (Fin 15), support.card = 8 ∧
      ¬ContainsStrongPolygonSet chi support 5 := by
  sorry

end ErdosSzekeres
```

### 5.3 Lifecycle

`proposed` → `open` → `claimed` → `closed` → `merged`, with side exits `refuted` and
`retired`.

- `proposed`: module exists; for `conjecture` kind the falsifier has not passed.
- `open`: sorry-free is false; ready when every declared dependency is closed/merged
  or already a theorem in ESCore; for conjectures, falsifier result is `pass`.
- `claimed`: a live row in `claims` (12 h expiry, configurable).
- `closed`: extractor reports no `sorryAx` and all axioms allowlisted for this node.
- `merged`: `es close` moved the module under ESCore and re-ran extract.
- `refuted`: falsifier exit 2, or a compiled counterexample; node becomes a
  `refutation` node or is deleted with a paragraph in `harness/retired.md`.
- `retired`: human decision, same log.

Status is *computed* by `es extract`; only `claimed`, `refuted`, `retired` involve
harness-owned records.

---

## 6. Configuration: `harness/config.toml`

```toml
[project]
id = "erdos-szekeres"                  # keys ~/.es/<id>/es.db
blueprint_namespace = "ESBlueprint"    # module prefix of node modules
blueprint_root = "ESBlueprint.lean"
core_namespace = "ErdosSzekeres"
closed_target_default = "ErdosSzekeres.Closed"
workstreams = ["A", "B", "C", "D", "E", "F", "G"]

[layers]                               # order matters: earlier may not import later
order = ["ESCertificates", "ESCore", "ESBlueprint"]
ESCertificates = ["ErdosSzekeres.Certificates"]
ESCore = ["ErdosSzekeres"]
ESBlueprint = ["ESBlueprint"]
certificate_consumers_file = "harness/certificate_consumers.txt"

[certificates]
generated_patterns = ["*CNFChunk*", "*CNFRaw*", "*CNFMid*", "*CheckpointSegment*",
  "*SemanticSegment*", "*SupportSegment*", "*ClauseChunk*", "*CNFGenerated", "*CheckpointData/*"]

[audit]
standard_axioms = ["propext", "Classical.choice", "Quot.sound"]
destinations_file = "harness/destinations.txt"
allowlist_file = "harness/allowlist.json"

[build]
core_budget_min = 10
lake = "lake"                          # command; allows `elan run` wrappers

[claims]
ttl_hours = 12

[falsify]
dataset_dir = "harness/dataset"
results_dir = "harness/falsify"
timeout_min = 60

[jobs]
max_parallel_builds = 1
max_parallel_falsifiers = 2
```

`harness/destinations.txt` initially: `ErdosSzekeres.erdosSzekeresFormulaAt_three`,
`_four`, `_five`, `ErdosSzekeres.classical_lower_sharpness`,
`ErdosSzekeres.decomposableExactUpperAt_six`, `ErdosSzekeres.tothValtr_upper`,
`ErdosSzekeres.suk_explicit_upper`, `ErdosSzekeres.hmpt_explicit_upper`,
`ErdosSzekeres.exists_predecessorHalfSubsetAtSix_of_card_le_fourteen`,
`ErdosSzekeres.decomposableStateUpper_488`. Add every closed node automatically.

---

## 7. The Lean extractor

### 7.1 Contract

`lake exe es-extract --out harness/nodes.json --index harness/index.json`
(built from `ESBlueprint/Extract.lean`, materialized from the template with the
config's module list). It imports `ESBlueprint` (hence all of ESCore) and writes:

**`nodes.json`**
```json
{
  "generated_at": "2026-09-05T14:02:11Z",
  "git_sha": "…", "toolchain": "leanprover/lean4:v4.29.1",
  "nodes": [{
    "name": "ErdosSzekeres.fin15_endpoint",
    "module": "ESBlueprint.A.Fin15Endpoint",
    "ws": "A", "kind": "formalization",
    "description": "Every 15-vertex …",
    "tags": {"depends": ["…"], "consumer": "…", "falsifier": "fin15_endpoint.py"},
    "type_pp": "∀ (chi : TripleColoring 15), OneChangeOn chi Finset.univ → …",
    "type_hash": "a1b2c3…",              // hash of the type Expr (see 7.2)
    "sorry": true,
    "axioms": ["propext", "Classical.choice", "Quot.sound", "sorryAx"],
    "deps_actual": [],                    // blueprint/destination names used by the proof term
    "helpers": ["ErdosSzekeres.fin15_endpoint.aux1"],
    "status": "open"                      // open | closed (before allowlist check) — final status computed in Python
  }],
  "destinations": [{ "name": "…", "axioms": [...], "type_hash": "…" }]
}
```

**`index.json`**: one record per theorem/def in the core namespace: `name`, `module`,
`docstring`, `type_pp`, `type_hash`. Used by `es search` and duplicate detection.

### 7.2 Implementation sketch (adapt to the pinned toolchain's API)

```lean
import Lean
import ESBlueprint            -- pulls in ESCore transitively
open Lean Meta

structure NodeOut where
  name : Name; module : Name; doc : Option String; typePP : String; typeHash : UInt64
  sorry : Bool; axioms : List Name; deps : List Name
  deriving ToJson

def isUnderPrefix (env : Environment) (n : Name) (prefixes : List Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => prefixes.any fun p => p.isPrefixOf (env.header.moduleNames[idx.toNat]!)
  | none => false

def collect (env : Environment) (prefixes : List Name) (destinations : List Name) : MetaM (List NodeOut) := do
  let mut out := []
  for (n, ci) in env.constants.toList do
    if ci.isUnsafe then continue
    let inBlueprint := isUnderPrefix env n prefixes
    unless inBlueprint || destinations.contains n do continue
    let (_, st) := ((CollectAxioms.collect n).run env |>.run {})
    let axioms := st.axioms.toList
    let typePP ← toString <$> ppExpr ci.type
    let deps := match ci.value? with
      | some v => (v.getUsedConstants.toList.filter fun d => isUnderPrefix env d prefixes || destinations.contains d)
      | none => []
    out := { name := n, module := (env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!),
             doc := ← findDocString? env n, typePP, typeHash := ci.type.hash,
             sorry := axioms.contains ``sorryAx, axioms, deps } :: out
  return out

def main (args : List String) : IO Unit := do
  -- parse --out/--index/--prefix/--destinations from args (config is passed on the command line by Python)
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ESBlueprint }] {} 0
  let (nodes, _) ← (collect env prefixes destinations).toIO {fileName := "es", fileMap := default} {env}
  -- write JSON …
```

Notes for the implementer: `CollectAxioms.collect` lives in `Lean.Util.CollectAxioms`
(the same machinery as `#print axioms`); `Expr.getUsedConstants` in `Lean.Util.FoldConsts`;
`findDocString?` in `Lean.DocString`. `Expr.hash` is a structural hash and is the
statement identity used by the lock; store `type_pp` alongside so humans can read
diffs. Universe-polymorphic statements: hash `ci.type` as stored (universe params are
part of the constant, not the type Expr), and include `ci.levelParams` in the hash
input to be safe. The tag parser lives in Python; the extractor only ships raw
docstrings. Docstrings on `private` helpers are ignored.

### 7.3 Statement lock — `harness/statements.lock`

```json
{ "ErdosSzekeres.fin15_endpoint": { "type_hash": "a1b2c3…", "type_pp": "…",
    "approved_by": "gavin", "approved_at": "2026-09-05", "kind": "formalization", "ws": "A" } }
```

`es extract --check` fails if any blueprint node's current `type_hash` differs from
the lock, or a node is missing from the lock, unless a matching entry exists in
`harness/restatements.md` written by `es node restate` (which rewrites the lock).
Closed-and-merged nodes keep their lock entry (their statement is now ESCore API).

### 7.4 Axiom allowlist — `harness/allowlist.json`

```json
[
  { "axiom": "EmptyHexagon.cnf_unsat_17", "reaches": ["ErdosSzekeres.forces_six", "ErdosSzekeres.strongSixCardinalityCeiling", "ErdosSzekeres.erdosSzekeresFormulaAt_six"],
    "justification": "Unsatisfiability of the 17-point convex-hexagon CNF from EmptyHexagonLean (ITP 2024), checked by cake_lpr; to be replaced by an LRAT replay (node A.es6_replay).",
    "added_by": "gavin", "added_at": "2026-09-08" },
  { "axiom": "Lean.ofReduceBool", "reaches": ["ErdosSzekeres.fin4_permutation_reorder_table"],
    "justification": "native_decide finite table; computational evidence only, no downstream users.", "added_by": "gavin", "added_at": "2026-09-05" }
]
```

`es audit` passes iff for every audited declaration, `axioms − standard` is covered by
entries whose `reaches` contains the declaration (or `"*"`). CODEOWNERS protects this file.

---

## 8. Data model and storage

### 8.1 Authoritative files (git)

`config.toml`, `statements.lock`, `allowlist.json`, `destinations.txt`,
`certificate_consumers.txt`, `restatements.md`, `retired.md`, `status.md` (generated
but committed), `falsify/*.json` (generated, committed: falsifier results are evidence).

### 8.2 SQLite — `<es_home>/<project.id>/es.db`

`es_home` is `ES_HOME` if set, else `[project] es_home` in `config.toml` (relative to the
root), else `~/.es`. This project keeps it at `.es/` inside the checkout (gitignored) because
sandboxed agents (Codex in workspace-write mode) may write only the checkout and `/tmp`;
`~/.es/erdos-szekeres` is a symlink to it so a second checkout sharing `~/.es` sees the same
state. The database is never committed.

```sql
CREATE TABLE claims (node TEXT PRIMARY KEY, agent TEXT NOT NULL, claimed_at REAL NOT NULL, expires_at REAL NOT NULL, note TEXT);
CREATE TABLE extract_cache (tree_hash TEXT PRIMARY KEY, nodes_json TEXT NOT NULL, index_json TEXT NOT NULL, created_at REAL NOT NULL);
CREATE TABLE jobs (id TEXT PRIMARY KEY, kind TEXT NOT NULL, node TEXT, argv TEXT NOT NULL, cwd TEXT NOT NULL,
                   status TEXT NOT NULL,           -- queued | running | done | failed | killed
                   exit_code INTEGER, created_at REAL NOT NULL, started_at REAL, finished_at REAL,
                   log_path TEXT, budget_min INTEGER, agent TEXT, pid INTEGER, result_json TEXT,
                   why TEXT, memory_max TEXT, outputs TEXT, peak_mib INTEGER, seconds REAL);  -- kind = run (§8.4)
CREATE TABLE attempts (id INTEGER PRIMARY KEY, node TEXT NOT NULL, agent TEXT, started_at REAL, ended_at REAL,
                       outcome TEXT, note TEXT);   -- closed | partial | blocked | abandoned | refuted | expired
CREATE TABLE events (id INTEGER PRIMARY KEY, at REAL NOT NULL, kind TEXT NOT NULL, node TEXT, agent TEXT, detail TEXT);
CREATE INDEX jobs_status ON jobs(status);
```

`tree_hash` = the committed tree ids of the state directories (`git rev-parse HEAD:<dir>`
for `ESBlueprint/**`, `ErdosSzekeres/**`, …) plus a hash of uncommitted changes under them,
so the cache is valid per working-tree state of those directories and a commit that only
touches notes, scripts or data does not force the extractor (36 GiB) to run again.

### 8.2.1 Build-storage maintenance

Filesystem maintenance and guarded writers use the same exact storage reservations. A
`worktree:<resolved-root>` key excludes builds and maintenance in that checkout; additional
namespaces such as `artifact-cache:<resolved-root>` protect shared stores. A multi-root
operation acquires every key in one SQLite transaction and commits before touching files.
It counts as one operation toward `max_parallel_builds`. An enclosing running job may add a
supplemental key without counting itself twice, and that lease inherits the job's cgroup so
scope reconciliation can release it only after confirmed termination. A standalone process
killed outside a guarded job can leave a conservative lease that needs explicit
reconciliation.

Lake 4.29.1 writes large, untracked `*.setup.json` snapshots under `.lake/build/ir` before
real compilation. Cached builds and `lake setup-file` do not require those persisted files;
the next real compile recreates the relevant snapshot. The cleanup command is dry-run by
default:

```bash
es storage prune-setup --out runs/setup-audit
# Inspect the manifest, then run a separately receipted application.
es storage prune-setup --apply --out runs/setup-prune
```

The command accepts only the configured relative IR root under a real, nonsymlink checkout
path. It records device, inode, mode, size, timestamps, link count and allocated blocks,
fsyncs the manifest, revalidates the complete set, and unlinks through directory file
descriptors with no symlink following. Receipts distinguish logical bytes removed from
allocated blocks whose final hard link was removed and record partial effects if an unlink
fails. Missing roots are an empty operation; changed files, replaced ancestors, malformed
manifests and active Lean compilers cause refusal. Plugin and dynlib entries inside a setup
snapshot are references; cleanup never touches their shared-library files. A pinned 4.29.1
module/plugin smoke verified cached builds, `lake setup-file`, pre-failure regeneration and a
successful rebuild after pruning; its receipt is under
`runs/storage-optimization-20260917/plugin-smoke/`.

`[build.setup_metadata_cleanup] enabled = true` adds the same deletion after a successful,
fully acknowledged `lake build`, before its reservation is released. The hook selects only
modules named by Lake's `Built` records. It never runs for extractors, arbitrary guarded
commands, failed builds or uncertain termination. Production configuration remains opt-in;
the standalone command and each build receipt expose the manifest and receipt paths.

### 8.3 Agent identity

`ES_AGENT` env var; default `<user>@<host>:<parent-pid>`. Claude Code sessions should
set `ES_AGENT` in the SessionStart hook to something stable for the session
(e.g. `claude-code:<session-id>` if available, else the hook's parent pid).

### 8.4 Audit trail (2026-09-07)

Several agents work in one checkout and one database, so everything an agent does that
another agent could duplicate, wait for, or be starved by is recorded where the harness
can show it, and the harness checks it rather than asking for prose:

- **Intent on claims.** `es claim --why` is mandatory (`[claims] require_why`); the text is
  the claim's `note` and appears in the `claimed by / last attempt` column of `es status`.
  `es release --outcome closed|partial|blocked|abandoned|refuted` needs `--note` for the
  three unfinished outcomes; the note lands on the attempt. An unclaimed open node whose
  last attempt ended within 14 days shows `(expired|partial|blocked|abandoned <date> <agent>: <note>)`
  so the next agent knows whether to continue or restart.
- **One door for compute.** `es job run --why … --out … [--node] [--mem] [--budget] [--cpu] -- <command>`
  is the only sanctioned way to run anything longer than a minute. The job row keeps the
  command, purpose, node, cap, output paths, agent, and after the run the measured peak
  (cgroup `memory.peak`), seconds and exit status; `es status` lists live jobs; the
  pre-bash hook blocks `systemd-run`/`nohup` that do not go through `es`. Submission is
  refused when the caps of live jobs plus the new one exceed `[jobs] memory_budget`, when
  fewer than cap + `run_margin_gib` GiB are available, or when an output path is not under
  `[jobs] output_roots` (results must be findable, not in a scratch directory). A submitter
  that cannot create a guarded scope (a sandbox without the systemd user bus, e.g. Codex)
  gets the job *queued*; `es worker`, started once from an unsandboxed shell, runs queued
  jobs one at a time; `es job requeue <id>` puts a failed job back. Synchronous
  `es check`/`es falsify`/`es build` runs are not job rows and are not counted against the
  budget; they are short and run under their own caps.
- **Report completion.** Submitting a background job does not complete the agent's task.
  Keep its reporting turn open and use `es job wait <id> --timeout 55` (also MCP `job_wait`).
  Waiting is read-only, releases the database between observations, and returns a compact
  `terminal` flag; a wait-window timeout neither cancels the job nor means it is finished.
  A terminal job includes its exit code and output/log paths. Inspect these and report success,
  failure, or a review gate without a user status request. The command's own exit zero means
  the read succeeded, just as for `job status`; it does not mean the job or proof succeeded.
  Native research runs now register an ordinary-code observer in `es worker`, with a separate
  exact-thread callback challenge. Only a verified binding and an available worker allow the
  coordinator to yield unattended; otherwise the reporting turn stays open. A saved checkpoint
  is for resumption after interruption, not an automatic notification mechanism. See
  `docs/automation-implementation.md` for commands, rollout status, and recovery limits.
- **A journal.** `es log "<text>" [--node]` writes a free-text event; `es journal --since 24h
  [--agent] [--node] [--kind]` merges claims, releases, expiries, jobs (submitted/finished
  with peak and seconds), falsifier runs, extracts, log entries and git commits into one
  timeline. It is what an agent reads after `es status`. Agents record every substantive
  mathematical finding, including failed attempts that leave the plan unchanged, with the
  exact assumptions, failure reason, and a job, receipt, or durable artifact reference.
  Before a pause or handoff they link a research account under `runs/` from the journal;
  the generated `es run handoff` bundle lists operations and usage but cannot supply the
  mathematical interpretation. Read the relevant older journal history and latest
  research handoff before choosing another attempt.
- **Loud staleness.** `es status` and `es ready` compare `statements.lock` with `nodes.json`
  and print `index is stale: N node(s) … run es extract` when nodes were added since the
  last full extract (the index showed 3 nodes while the lock held 13 for a day before this).

### 8.5 Incremental index (2026-09-28)

A node's extractor record (statement, `sorry`, axioms, dependencies, tags) depends only on the
sources in its import closure, the extractor and the extract configuration. Re-deriving the whole
index from the whole compiled environment on every commit loaded every module, including 9,857
certificate modules, into one 28–30 GiB process for a one-lemma change. It also meant a fresh
worktree needed hours of cache restores before its first commit.

- **Fingerprints.** Every full `es extract` writes `fingerprints` into `nodes.json`
  (`tools/es/es/fingerprint.py`):
  - `core` hashes, via git trees plus uncommitted changes, everything outside the blueprint
    node modules: the core and certificate libraries, destinations, toolchain files, the
    extractor template and the extract-relevant config sections;
  - `blueprint` maps each blueprint module reachable from the root to a digest of the blueprint
    sources in its import closure. Only blueprint imports are followed; `es layers` forbids core
    modules from importing the blueprint.
- **`es extract --incremental`** re-extracts only the modules whose fingerprints changed, in one
  closure-sized extractor run under the targeted cap. It carries every other record over and
  recomputes statuses, readiness, lock, duplicate and tag problems from the merged records. The
  result equals a full extraction up to the volatile lines; the environment module count is
  estimated and is volatile. It refuses (`NeedsFullExtract`) when `core` changed or the index
  has no fingerprints.
- **`es check --targeted` and `es node add --targeted`** now update `nodes.json` and `status.md`
  this way. The merge reuses their targeted extraction from the cache (same tree hash and
  import set), so it costs no second extractor run. `node add` gains a duplicate check over
  every node, not just the new node's import closure.
- **`es extract --check`**, which the commit hook runs:
  - When all fingerprints match, it re-renders the index from the recorded records plus the
    current lock, allowlist, falsifier results and claims, and compares. No Lean runs.
  - When only blueprint modules changed, it names them and asks for `--incremental` instead of
    starting a whole-blueprint build.
  - Core changes (or an index without fingerprints) still take the full path.
  - The nightly full extraction remains the backstop.
  - The commit hook runs `es extract --check --changed`. A change that touches no extract state
    directory, index file, lock, allowlist or falsifier result cannot make the index stale or
    current, so it passes at once; tooling and docs commits no longer need a whole-blueprint
    build. Without `--changed`, `--check` still answers "is the index current?".
- **Cache fix.** A targeted extraction (`no_cache=True`) used to empty the whole extract cache,
  evicting the full-environment entries that `cache_put` was written to protect. It now only
  skips the lookup.
- **Guard fixes.**
  - Guarded scopes run with `OOMPolicy=continue`, so an OOM-killed compiler no longer makes
    systemd stop the whole scope before the wrapper records the peak and the kill. Those jobs
    used to report `rc=-15`, peak 0, 0 OOM kills. When stats are still missing, the journal is
    consulted (`scope_oom_kills`).
  - Queued `es build` jobs reserve the largest cap the build may request (`build_reservation`,
    the final step), instead of the per-module cap their final step then exceeded ("requested
    30G exceeds job reservation 20G").

Adoption: the first full `es extract` with this code writes the fingerprints. Until then every
path falls back to its previous behaviour.

---

## 9. Commands

All commands: `es <cmd> [args] [--json]`. Exit code 0 success, 1 check failed,
2 usage/config error, 3 Lean/Lake failure. Human output is a table; `--json` emits
the same data structured. Every command is also an MCP tool (§10.1) with the same
name and a JSON schema mirroring its arguments.

| Command | Arguments | Behaviour | Fails when |
| --- | --- | --- | --- |
| `es extract` | `--check`, `--no-cache` | Runs the extractor (via cache keyed on tree hash), parses tags, computes status, writes `nodes.json`, `index.json`, `status.md`. `--check`: also verifies the committed `status.md`/`index.json` are up to date and the lock matches. | extractor fails; `--check` finds stale files, lock mismatch, missing required tags, unknown workstream, duplicate type hashes among blueprint nodes, node with no consumer and no `@dangling-ok` |
| `es status` | `--brief`, `--ws X` | Frontier grouped by workstream: name, kind, status, ready?, claimed by, days open, falsifier state; then burn-down (nodes closed per ISO week, attempts per week). `--brief` is ≤ 25 lines for the SessionStart hook. | — |
| `es ready` | `--ws X`, `--kind K` | Open nodes whose declared deps are closed/merged or exist in ESCore, unclaimed, and (for conjectures) falsifier `pass`. | — |
| `es node show <name>` | | Everything known: statement, tags, declared vs actual deps, consumer and whether it compiles, lock entry, claim, falsifier result, last job. | unknown node |
| `es node add` | `--name`, `--ws`, `--kind`, `--type "<Lean type>"`, `--description`, `--depends a,b`, `--consumer c` or `--dangling-ok "reason"`, `--falsifier f`, `--approved-by who` | Runs `es search` on description and type and refuses exact type-hash duplicates (needs a quick elaboration: writes the module, runs `lake build ESBlueprint.<Mod>`, then `es extract` on it); writes `ESBlueprint/<WS>/<Name>.lean` from a template with `sorry`; adds the import to `ESBlueprint.lean`; adds the lock entry (approval is the human running this or the CODEOWNERS review of the PR). | duplicate; statement fails to elaborate; missing required tags |
| `es node restate <name>` | `--type`, `--approved-by`, `--reason` | Rewrites the statement in place, updates the lock, appends to `restatements.md`. The only sanctioned way to change a statement. | node claimed by someone else; elaboration fails |
| `es node retire <name>` | `--reason`, `--as-refutation` | Deletes the module (or rewrites as `¬`-node), removes from `ESBlueprint.lean`, appends to `retired.md`, records an attempt outcome. | — |
| `es claim <name>` / `es release <name>` | `--why` (claim, required), `--outcome` + `--note` (release), `--agent` | Insert/delete claim; expired claims are purged on every command and recorded as `expired` attempts. Claiming a `proposed` conjecture is refused until `es falsify` passed. | already claimed by another live agent; not ready (override with `--force`, logged) |
| `es search <query>` | `--type-hash H`, `--limit N`, `--ns` | Full-text (SQLite FTS5 over `index.json` + `nodes.json`: names, docstrings, `type_pp`). Returns name, module, one-line docstring, score. | — |
| `es check <name>` | `--async`, `--budget MIN` | Builds only the node's module (`lake build ESBlueprint.<Mod>`), runs a targeted extract, reports sorry-free / axioms / build time; records an attempt. `--async` submits a job. | build fails; budget exceeded |
| `es falsify <name>` | `--async`, `--dataset PATH` | Runs the node's falsifier with `dataset_dir` on argv; exit 0 = pass, 2 = counterexample (falsifier must write `harness/falsify/<node>.json` with the witness), other = error. Records result. | falsifier missing; error exit |
| `es close <name>` | `--dry-run` | Preconditions: sorry-free, axioms allowlisted, claim held by caller or none. Actions: `git mv` the module to the `@target` location, rewrite `import` lines across the repo, keep lock entry, add name to `destinations.txt`, run `es extract`, run `lake build` of the `@consumer` module, print the suggested follow-up node ("instantiate consumer"). Records attempt `closed`. | any precondition; consumer fails to build after the move |
| `es audit` | `--changed` (only declarations whose modules changed vs `origin/main`) | Axiom audit over blueprint nodes + `destinations.txt` against the allowlist. | uncovered axiom |
| `es layers` | | Parses `import` lines of every module in the three layers; checks the order in config and the certificate-consumer allowlist; checks nothing imports `ESBlueprint` from ESCore; checks `ESBlueprint.lean` imports every node module. | violation |
| `es build <target>` | `core\|blueprint\|certs\|node <name>`, `--budget MIN`, `--async` | Wraps `lake build` with wall-clock budget and a summary line (modules built, seconds). | build fails; budget exceeded |
| `es job run -- <command>` | `--why`, `--out` (required), `--node`, `--mem`, `--budget`, `--cpu`, `--queue` | Runs any command as a recorded job in the guarded scope (§8.4): purpose, cap, outputs, agent, peak and seconds in the job table; enforces the memory budget. | budget or availability exceeded; output outside `runs/`/`data/` |
| `es job list\|status\|log\|cancel` | `<id>` | Job table access (list shows cap, peak, agent, why). `es worker` runs the loop (foreground; run under tmux/systemd-user); `es job exec <id>` is the internal runner. | — |
| `es job wait <id>` | `--timeout` (0–60 seconds; default 55) | Read-only bounded wait; returns `terminal`/`timed_out`, and exit code plus output paths on completion. Repeat while pending, then inspect and report. | unknown job; invalid timeout |
| `es log <text>` | `--node` | Free-text journal entry under the agent id. | — |
| `es journal` | `--since 24h`, `--agent`, `--node`, `--kind`, `--limit`, `--no-commits` | Timeline of claims, releases, jobs, falsifier runs, extracts, log entries and commits. | — |
| `es note` | `--since DATE` | Weekly note from status diffs and the attempts table: nodes opened/closed/refuted/retired, attempts, allowlist and lock changes, job time spent. Writes `docs/notes/<ISO-week>.md` with a `## Judgment` section left empty for the human. | — |
| `es doctor` | | Checks toolchain, `lake` presence, config validity, DB schema, that `.lake/build` has certificate oleans, cache health. | any check fails |

### 9.1 Ready computation

```
ready(n) := status(n) == open
         ∧ no live claim
         ∧ ∀ d ∈ deps_declared(n): d ∈ ESCore ∨ status(d) ∈ {closed, merged}
         ∧ (kind(n) == conjecture → falsify_result(n) == pass)
```
Dependencies that are themselves open blueprint nodes make `n` *blocked*; `es status`
lists the blocker.

### 9.2 Duplicate detection

Two declarations are duplicates when their `type_hash` is equal. `es node add` refuses
exact duplicates; `es extract --check` reports exact duplicates among blueprint nodes
as an error and exact duplicates between a blueprint node and an ESCore theorem as an
error (the node should be retired: the theorem exists). Near-duplicates are surfaced
by `es search` only.

---

## 10. Integrations

### 10.1 MCP server (`tools/es/es/mcp_server.py`)

Uses the official `mcp` Python SDK (`FastMCP`) over stdio. One tool per command
above, named identically, with typed arguments; long commands (`check`, `falsify`,
`build`) return a job id immediately and `job_status`/`job_log` tools poll. Tools
return the `--json` payload. Register in `.mcp.json`:

```json
{ "mcpServers": { "es": { "command": "python", "args": ["-m", "es.mcp_server"], "cwd": "tools/es",
                          "env": { "ES_PROJECT_ROOT": "${workspaceFolder}" } } } }
```

(Use whatever variable expansion Claude Code supports for the repo root; otherwise
`es` discovers the root by walking up to `harness/config.toml`.)

### 10.2 Claude Code hooks (`.claude/settings.json`)

```json
{
  "hooks": {
    "SessionStart": [{ "hooks": [{ "type": "command", "command": "tools/es/hooks/session_start.sh" }] }],
    "PreToolUse": [{ "matcher": "Bash", "hooks": [{ "type": "command", "command": "tools/es/hooks/pre_bash.sh" }] }]
  }
}
```

`session_start.sh`: exports `ES_AGENT`, runs `es status --brief` and prints it (Claude
Code injects hook stdout as context). `pre_bash.sh`: reads the tool input JSON from
stdin; if the command contains `git commit` or `git push`, runs `es layers && es extract --check && es audit --changed`
and exits non-zero (blocking the tool call) on failure; if it launches `systemd-run` or
`nohup` outside an `es` command, it is blocked with a pointer to `es job run` (§8.4).

### 10.3 CLAUDE.md and AGENTS.md

`CLAUDE.md` holds the working rules; `AGENTS.md` (read by Codex and other tools) carries the
identical rule list under a short project header, and `tools/es/tests/test_audit_trail.py`
fails when the two lists differ. The rules, as of 2026-09-07: state from `es status` (run
`es extract` when it says the index is stale); `es ready`, `es claim --why`, `es release
--outcome --note`; every command longer than a minute through `es job run`; `es log` before a
decision that changes the plan; statements only via `es node add`/`restate`; `es search`
before writing a lemma; one node per branch; no unallowlisted axioms; generated certificate
modules only from the generators; `es note` for the weekly note; builds through `es build`/
`es check`; git metadata in `.git-data`. The current rules also require recording all
research findings and failed approaches as they arise, linking durable evidence from
`es log`, and writing a mathematical handoff before a pause or run close.

### 10.4 CI (`.github/workflows/ci.yml`)

Jobs, in order, all required by branch protection on `main`:

1. `harness-tests`: `pytest tools/es/tests` (no Lean).
2. `layers`: `es layers`.
3. `lean`: restore mathlib cache (`lake exe cache get`), restore `.lake/build` for
   `ESCertificates` keyed on `hashFiles('lean-toolchain','lake-manifest.json','ErdosSzekeres/Certificates/**')`,
   `es build certs` (no-op on cache hit), `es build core --budget 10`, `es build blueprint`,
   `es extract --check`, `es audit`.
4. `pr-shape` (pull requests only): the diff touches at most one `ESBlueprint/**` module's
   proof, and `statements.lock` only via a `restatements.md` entry in the same PR.

Merge queue enabled so proof PRs land serially. `CODEOWNERS`:

```
ESBlueprint/**            @GLitchfield
harness/statements.lock   @GLitchfield
harness/allowlist.json    @GLitchfield
harness/destinations.txt  @GLitchfield
```

PR template fields: Node; `es search` query and result; `es check` output; for
conjecture nodes `es falsify` output.

---

## 11. Seed nodes

Draft statements for `es node add` at M2. Exact API names must be checked against
the repository before adding (the names below follow the current sources); where a
statement's precise form is uncertain it is marked TODO and the node is created as
`proposed` until the human approves the exact type.

**A — exact six**

```lean
/-- @node @ws A @kind formalization @consumer ErdosSzekeres.ErdosSzekeresConjecture -/
theorem forcesConvexPolygon_of_sweepExactUpperAt (k : ℕ) (hk : 3 ≤ k)
    (h : SweepExactUpperAt k) : ForcesConvexPolygon k (2 ^ (k - 2) + 1) := by sorry
-- route: exists_sweptPresentation, apply h to P.configuration.tripleColoring, then
-- SweptPresentation.containsConvexSubset_iff_exists_isStrongPolygonOn.

/-- @node @ws A @kind formalization @consumer ErdosSzekeres.forcesConvexPolygon_of_sweepExactUpperAt -/
theorem sweepExactUpperAt_of_predecessorHalfSubset_all (k : ℕ) (hk : 3 ≤ k)
    (h : ∀ j, 4 ≤ j → j ≤ k → PredecessorHalfSubsetAt j) : SweepExactUpperAt k := by sorry
-- route: Nat.le_induction from sweepExactUpperAt_three and sweepExactUpperAt_of_predecessorHalfSubset.

/-- @node @ws A @kind formalization @dangling-ok destination theorem -/
theorem forces_six : ForcesConvexPolygon 6 17 := by sorry
-- route (fast): bridge to EmptyHexagonLean.gon_6_theorem under allowlisted axiom;
-- route (policy): regenerate their CNF, LRAT replay through lrat_checkpoint_reify.

/-- @node @ws A @kind formalization @depends ErdosSzekeres.forces_six
    @consumer ErdosSzekeres.predecessorHalfSubsetAt_six_of_cardinalityCeiling_of_middle -/
theorem strongSixCardinalityCeiling : StrongSixCardinalityCeiling := by sorry
-- route: a SweptConfiguration's point set is a general-position Finset of card n;
-- forces_six gives a convex 6-subset; the strong-polygon bridge gives a strong 6-set.

/-- @node @ws A @kind formalization @depends ErdosSzekeres.predecessorHalfFin15_or_exactMaximumObstruction
    @consumer ErdosSzekeres.predecessorHalfSubsetAtSixMiddle_of_fin15Endpoint @falsifier fin15_endpoint.py -/
theorem fin15_endpoint (chi : TripleColoring 15) (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ∃ support : Finset (Fin 15), support.card = 8 ∧ ¬ContainsStrongPolygonSet chi support 5 := by sorry

/-- @node @ws A @kind formalization @depends ErdosSzekeres.strongSixCardinalityCeiling, ErdosSzekeres.fin15_endpoint
    @consumer ErdosSzekeres.sweepExactUpperAt_of_predecessorHalfSubset_all -/
theorem predecessorHalfSubsetAt_six : PredecessorHalfSubsetAt 6 := by sorry

/-- @node @ws A @kind formalization @depends ErdosSzekeres.forces_six @dangling-ok destination theorem -/
theorem erdosSzekeresFormulaAt_six : ErdosSzekeresFormulaAt 6 := by sorry
-- ⟨forces_six, classical_lower_sharpness 6 (by norm_num)⟩
```

**B — decomposable theorem**

```lean
/-- @node @ws B @kind formalization @dangling-ok uniform theorem; consumer is E3FiniteReduction's DecomposableExactUpperAt
    @measure a + u (published induction) -/
theorem decomposableStateUpper_all (a u k : ℕ) (ha : 1 ≤ a) (hu : 1 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
    DecomposableStateUpper a u k := by sorry
-- TODO check the degenerate a = 1 / u = 1 cases against containsCupSet_one before locking.

/-- @node @ws B @kind conjecture @falsifier external_endpoint_state.py @consumer ErdosSzekeres.decomposableStateUpper_all -/
-- TODO statement: the per-vertex external cap/cup extension-rank state is a recursive congruence with a k-only bound.
-- Created as `proposed`; the falsifier runs the all-root census on the k = 6 eight-vertex roots first.
```

**C — Erdős–Tuza–Valtr, cap parameter 5**

```lean
/-- @node @ws C @kind conjecture @falsifier etv_cap5_small_n.py @dangling-ok equivalent-ladder theorem -/
theorem etv_cap_five (n : ℕ) (hn : 5 ≤ n) {m : ℕ} (χ : TripleColoring m) (hreal : IsSweepRealizable χ)
    (hcard : decomposableThreshold 5 n n < m) :
    ContainsCapSet χ Finset.univ 5 ∨ ContainsCupSet χ Finset.univ n ∨ ContainsStrongPolygonSet χ Finset.univ n := by sorry
```

**E — predecessor-half conjecture**

```lean
/-- @node @ws E @kind conjecture @falsifier predecessor_half_constructions.py
    @consumer ErdosSzekeres.sweepExactUpperAt_of_predecessorHalfSubset_all -/
theorem predecessorHalfSubsetAt_all (k : ℕ) (hk : 4 ≤ k) : PredecessorHalfSubsetAt k := by sorry
```

**D/F — extremal sets decomposable in some direction** — TODO: needs a definition of
"sweep after rotation by θ" on `Finset (Point 2)`; create as `proposed` with the
falsifier `direction_census.py` (the 77 pentagon-free 8-point order types) and lock the
Lean statement only after the falsifier passes.

---

## 12. Build order (milestones)

**M1 — layout and layering (2–3 days).** Move generated modules under
`ErdosSzekeres/Certificates/`, update generators and consumer imports, restructure
`lakefile.toml`, narrow the `sorry` grep, write `es layers`, `es build`, `es doctor`,
and the CI `lean` job with certificate caching. Nothing else changes.

**M2 — extractor and frontier (2–3 days).** `Extract.lean.tmpl`, `es extract`
(cache, tag parsing, status, `status.md`), `es status`, `es ready`, `es node add/show/restate/retire`,
`statements.lock`, `ESBlueprint` with the Workstream A seed nodes.

**M3 — trust and closure (1–2 days).** `es audit` + allowlist, `es close`, `destinations.txt`,
attempts table.

**M4 — agents (2 days).** `es search` (FTS5), `es claim/release`, MCP server, `.mcp.json`,
hooks, `CLAUDE.md`, PR template, CODEOWNERS, branch protection, `pr-shape` CI job,
`es note`. Also the §17 changes marked M4 (`docs/automation.md`, `docs/reproducibility.md`,
`docs/adversarial-review.md`, README build section).

**M5 — falsifiers (2–3 days, parallel with D scripts).** `es falsify`, job runner and
`es worker`, `harness/dataset/` layout, conjecture seed nodes for B, C, E.

**M6 — retirement (1 day).** Apply every §17 row marked M6: rewrite `AGENTS.md`,
retire the orchestration documents and templates, archive the wayfinder, rewrite the
README's state narrative, and remove the orchestration/scheduler/generator/genome checks
from `make test` and systemd.

Extraction of `tools/es/` into its own repository happens after M6 once a week passes
with no change to the command surface.

---

## 13. Acceptance checklist (report each as done / partial / not started)

1. `lake build ESCore` completes from a warm `.lake/build` within `core_budget_min` on the WSL box and in CI.
2. `es layers` passes on `main`; introducing an `ESCore → ESCertificates` import outside the allowlist makes it fail.
3. `es extract` lists every `ESBlueprint` node with correct `sorry`/axioms; a node given a real proof flips to `closed` with no edit to any harness file.
4. `es extract --check` fails when a statement is edited by hand and passes after `es node restate`.
5. `es node add` refuses a statement whose type hash equals an existing ESCore theorem.
6. `es audit` fails on a new axiom and passes once allowlisted with a `reaches` entry.
7. `es close` on a proved node moves it, rewrites imports, rebuilds the consumer, and `es status` no longer lists it.
8. `es ready` hides a conjecture node until `es falsify` records `pass`; a falsifier exit 2 marks it `refuted` and writes the witness file.
9. Two Claude Code sessions in different worktrees see each other's claims; an expired claim disappears.
10. `es search "strong five-free support"` returns the Fin13 window transport theorem in the top results.
11. A fresh Claude Code session shows the frontier from the SessionStart hook without reading any doc.
12. A `git commit` that violates layering or the lock is blocked by the pre-bash hook.
13. `es note` produces a weekly note whose numbers match `attempts` and `status.md` diffs.
14. `pytest tools/es/tests` passes without a Lean toolchain (extractor mocked), and the CI `lean` job passes with it.

---

## 14. Test plan

- Unit (no Lean): tag parser (all tags, malformed tags, missing required), ready
  computation, duplicate detection, lock diffing, allowlist coverage, layer parser on a
  synthetic module tree, `es close` import rewriting on a temp git repo, claims expiry,
  job state machine, note generation from fixture tables.
- Integration (Lean, CI `lean` job): `es extract` on the real repo; a fixture node
  `ESBlueprint/Test/Trivial.lean` with a trivially provable statement that is proved
  in a test branch to exercise the open→closed flip and `es close`.
- Falsifier contract test: a falsifier that always exits 2 with a witness, and one
  that exits 0.

---

## 15. Decisions left open (answer before M2)

1. Should closed nodes be **moved** into `ErdosSzekeres/Closed/<WS>/` (this design) or
   left in place with ESBlueprint promoted to a layer ESCore may import? Moving keeps
   the layering simple; leaving them avoids import rewriting.
2. CLI framework: stdlib `argparse` (zero dependencies for the core; `mcp` only as an
   extra) is the default in this design; `typer` is fine if preferred.
3. Whether `docs/wayfinder/tickets` are moved to `docs/history/` at M6 or left where
   they are with a banner.
4. The name `es` for the CLI; rename freely, but keep tool names identical between CLI and MCP.

---

## 16. What this harness does not do

It does not choose nodes, judge whether a candidate mechanism deserves one, or replace
adversarial review of statements. It does not prevent wasted proof attempts; it measures
them. It is not a hosted service; an HTTP transport for the same handlers can be added
if a second machine or a cloud session needs access, and Prove2Me could replace §9–10
if it turns out to host private projects, but §7 (extractor) and §7.3–7.4 (lock,
allowlist) are needed either way.

---

## 17. Operational documentation changes

The harness replaces a prose-based operating model. Every document that encodes the
old model must be rewritten, retired, or turned into generated output; otherwise agents
that read it will keep following it. Disposition of each file, with the milestone in
which it changes. "Retire" means move to `docs/history/<original path>` with a one-line
banner at the top saying it is historical and superseded by `docs/harness-design.md`;
nothing is deleted from git history.

| File | Disposition | Replacement / new content | When |
| --- | --- | --- | --- |
| `AGENTS.md` (42 KB) | **Rewrite** to ≤ 60 lines | Identical rules to `CLAUDE.md` (§10.3) plus: how to run `es`, the three-layer layout, the trust policy summary (standard axioms; allowlist; `sorry` only in `ESBlueprint`; `native_decide` is evidence, never a kernel proof), and a pointer to `docs/harness-design.md`. Drop: frontier execution cycle, six-field accounting prose, failure-genome memory, skeptical proof-distance accounting, rolling pipeline, theorem-entry memo, semantic-readiness receipt, packet/hash requirements, agent occupancy targets. The six-field accounting survives only as the `es note` template. | M6 |
| `CLAUDE.md` | **Create** | §10.3 verbatim. `AGENTS.md` must not contradict it. | M4 |
| `README.md` "Current state" (≈1,100 lines of narrative) | **Rewrite** | Replace the narrative with: a ten-line statement of the destination and the model; a link to `harness/status.md` (generated frontier); a table of destination theorems with their Lean names, generated from `destinations.txt`; the trust surface (allowlist contents). Keep the Build section, updated for the three targets and `es doctor`. The old narrative moves to `docs/history/README-state-2026-09.md`. | M6 |
| `docs/wayfinder/map.md`, `frontier-portfolio.md`, `tickets/*`, `wayfinder/README.md` | **Retire** (archive) | `harness/status.md` (frontier), `harness/nodes.json`, `docs/notes/<week>.md` (from `es note`). The load-bearing dependency ledger's *content* is re-expressed as seed nodes (§11); the ledger table itself is not maintained. `scripts/wayfinder_status.py` and `scripts/check_wayfinder_thread_lifecycle.py` are deleted from `make test`. | M6 |
| `docs/wayfinder/proof-distance-assessment-2026-08-14.md` | **Keep**, move to `docs/history/` | Still the rationale; referenced from the review. | M6 |
| `docs/agents/README.md`, `docs/agents/profiles/*.md`, `manifest.toml`, `schemas/*.json`, `issue-tracker.md`, `time-estimates.csv`, `time-estimation.md`, `research-campaign.md`, `continuous-idea-generator.md`, `research-scheduler.md` | **Retire** | Roles collapse to: human (statements, allowlist, judgment), proof agents (any Claude Code/Codex session running `es`), reviewers (Sol/Fable on frozen statements only, see `adversarial-review.md`). No profiles, packets, schemas, or time estimates; the `attempts` table replaces time-estimate calibration. `scripts/check_agent_orchestration.py`, `check_agent_slate.py`, `check_research_campaign.py`, `check_research_scheduler_*.py`, `research_scheduler.py`, `continuous_idea_generator.py`, `freeze_agent_context.py`, `build_*_packet.py`, `time_estimate_report.py` and their tests leave `make test` and are moved to `scripts/history/` (or deleted; decision for the human). systemd user units for the generator and scheduler are disabled and their unit files removed. | M6 |
| `docs/adversarial-review.md` | **Rewrite** (keep the tool) | Scope becomes: bounded Sol/Fable review is run (a) on a node's statement before `es node add` when the node is `conjecture` kind or is a destination-level formalization, (b) on `es node retire` of a conjecture, (c) on allowlist additions. It is not run on slate selection, proof PRs, or process changes. Output is attached to the PR, not to a ticket. `scripts/adversarial_review.py` is kept; its packet/hash framing is simplified to "review this statement / this retirement". | M4 |
| `docs/automation.md` | **Rewrite** | Proof-search workflow section stays (hammer policy). Trust policy section becomes the allowlist policy of §7.4 plus the `sorry`-in-`ESBlueprint` rule, the certificate layout (`ErdosSzekeres/Certificates/`), and how `es audit` runs in CI. | M4 |
| `docs/reproducibility.md` | **Rewrite** | Evidence tiers restated for the harness: kernel theorem (closed node) > allowlisted external certificate > `native_decide` / falsifier `pass` (computational evidence) > solver output without checked proof. Falsifier results in `harness/falsify/*.json` are the canonical record of computational evidence; the dataset in `harness/dataset/` is versioned. Independent-replay requirement kept for any falsifier result that retires a node. | M4 |
| `docs/research_log.md`, `docs/experiments/*` | **Keep** | Experiments remain the home for designed computations; new entries are written for falsifier runs that change a node's state (cite the node name and the `harness/falsify/<node>.json` hash). `docs/experiments/README.md` gets two lines saying so. The `templates/experiment-note.md` template is kept. | M6 |
| `docs/formalization_plan.md` (172 KB) | **Retire** (archive) | Its live content is the seed-node list (§11) and, over time, `harness/status.md`. | M6 |
| `docs/literature_review.md`, `docs/bibliography.md` | **Keep** | Add the EmptyHexagonLean `gon_6_theorem` correction and the Balko–Valtr tier note from the review. | M4 |
| `docs/template_improvements.md` | **Retire** | — | M6 |
| `templates/agent-task-packet.json`, `agent-result.json`, `agent-execution-slate.json`, `research-development-brief.json`, `research-development-receipt.json`, `research-seed-batch.json`, `decision-ticket.md`, `review-question.md` | **Retire** | `es node add` arguments and the PR template are the only intake formats. `review-question.md` may be kept as the input format for `adversarial_review.py` if that script still needs it. | M6 |
| `Makefile` | **Rewrite** the `test`/`lean` targets | `make test` = `es layers && es extract --check && es audit && pytest tools/es/tests` plus the existing Python unit tests that are still relevant (generators, checkers). `make lean` = `es build core` (default threads, budget from config). The `py_compile` list is trimmed to scripts that remain. Remove the `LEAN_BUILD_THREADS=1` guard path. | M1 (targets), M6 (trim) |
| `.codex/rules/adversarial-review.rules` | **Rewrite** | Same scope as `docs/adversarial-review.md`. | M4 |
| `data/derived/README.md`, `data/reference/README.md` | **Keep** | Add: falsifier datasets live in `harness/dataset/`, results in `harness/falsify/`. | M5 |

Two rules for the rewrite: (1) no operational document may describe a state that
`es status` also describes — the frontier has exactly one home; (2) every retired
document keeps its git history and gets the banner, so an agent that stumbles on it
learns it is superseded rather than obeying it.
# Automation implementation

The [automation operating guide](automation-implementation.md) documents the current
durable operations, proof finalization, reusable probes, context artifacts and usage
comparison commands. It distinguishes tested behavior from client-delivery, publication
and incremental-index rollout gates. The compiled Lean environment remains authoritative.
