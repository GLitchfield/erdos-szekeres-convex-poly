# `es` harness — implementation notes (4 September 2026)

Companion to `docs/harness-design.md` (the contract). This records what was built,
where the implementation deviates from the design and why, and the state of the
acceptance checklist (§13) at the end of the first build session.

## What exists

- `tools/es/` — the harness: `es` package (config, module scan, layers, guarded
  builds, extractor runner, node model, SQLite store, commands, MCP server),
  `lean/Extract.lean.tmpl`, `templates/node.lean.tmpl`, `hooks/`, `tests/` (pytest),
  `bin/es` and `bin/es-mcp` launchers, a `.venv` (uv) with pytest and mcp 2.x.
- `harness/` — `config.toml`, `destinations.txt`, `allowlist.json`, `statements.lock`,
  `certificate_consumers.txt`, `certificate_inputs.txt`, `restatements.md`,
  `retired.md`, `falsifiers/` (contract fixtures + `predecessor_half_constructions.py`),
  `dataset/`, `falsify/`, and the generated `nodes.json`, `index.json`, `status.md`.
- `ESBlueprint.lean` + `ESBlueprint/` (node modules; `Extract.lean` is materialized
  there and git-ignored).
- `lakefile.toml` with `ESCore` (roots `ErdosSzekeres`) and `ESBlueprint`.
- `CLAUDE.md`, `.mcp.json`, `.claude/settings.json` (SessionStart + PreToolUse hooks),
  `CODEOWNERS`, `.github/workflows/ci.yml`, `.github/pull_request_template.md`,
  Makefile targets `lean` (via `es build core`) and `harness-test`.

## Deviations from the design

1. **Certificate modules were not moved** to `ErdosSzekeres/Certificates/`.
   Renaming a module rewrites every import line that names it (8,449 files) and
   therefore changes the trace of every certificate module: all 125 GB of
   `.olean.private` proof terms would be rebuilt (the Fin15 chain alone took 6.2 h on
   2026-09-04; the design's "about an hour" is wrong for this repository). The
   layer is logical instead: `[certificates] generated_patterns` + a header marker in
   `harness/config.toml` classify 9,857 generated modules; `es layers` enforces the
   boundary. `es certs relocate` plans (and with `--apply` performs) the physical move
   for when the rebuild is authorized. Consequently there is no `ESCertificates`
   Lake target yet; `es build certs` builds `ESCore`.
2. **Two allowlists at the certificate boundary.** Certificates import core
   definitions (encodings, presentations, `LRATCheckpoint`), so the design's one-way
   order does not hold. `certificate_consumers.txt` (core modules that may import
   certificates, 50 today) and `certificate_inputs.txt` (core modules certificates
   may import, 33 today) are derived from the import graph by
   `es layers --write-allowlists`.
3. **Extractor is a script, not a `lean_exe`.** A native executable would compile
   the 10,000-module import closure to C; `lake env lean --run ESBlueprint/Extract.lean`
   interprets `main` against the existing oleans.
4. **Axioms come from a module-order taint propagation, not `CollectAxioms`.**
   `#print axioms` walks proof terms depth-first and thrashes on the certificate
   families (measured on 2026-09-04: 16 TB read in 3.5 h without finishing). The
   extractor reads each module's constants once in import order and propagates a
   bitmask of *non-standard* axioms; standard axioms are reported for every proved
   constant. Results are cached per module in `~/.es/<id>/taint/` keyed on the olean
   hash, so only changed modules are rescanned. `importAll := true` must not be used
   (it forces a 30+ GB environment); a plain import exposes every proof term.
5. **Statement identity** is `mixHash (Expr.hash type) (hash levelParams)`; stable
   within a toolchain, not across toolchain bumps (all lock entries would then need
   `es node restate`, or a future `es lock refresh`).
6. **CI Lean job needs a self-hosted runner** (`es-lean` label); hosted runners
   cannot hold 130 GB of build products or 15 GiB compiles. The job is gated on a
   repository variable until such a runner exists.
7. **Builds are memory-guarded** (systemd transient scope, `MemoryMax` from config)
   with default Lean threads. Lake 5 has no `-j`; a full `ESCore` rebuild with 22
   parallel compilers hit the 20 GB cap on 2026-09-04, so `es build` first builds
   Lake's out-of-date list one module per invocation (repeating until Lake reports
   nothing stale) and only then runs the full target.
8. **`proposed`** also covers nodes missing from `statements.lock` (approval = lock
   entry), not only conjectures without a passed falsifier. **`unallowlisted`** is an
   extra status for sorry-free nodes reaching an axiom without an allowlist entry.
9. `status.md` contains only Lean- and git-derived content (deterministic across
   machines); claims and the burn-down live in `es status` (local database).

## State of the build on 2026-09-04 (found by the harness)

- **The core root does not build.** `ErdosSzekeres.lean` imports both
  `ES6Certificate` (added 2026-09-04) and `E3State466Certificate`; their encodings
  both declare `ErdosSzekeres.StrongSixValues` (`ES6AnchoredEncoding.lean:17`,
  `E3State466Encoding.lean:113`), so importing the root fails with "environment
  already contains 'ErdosSzekeres.StrongSixValues'". One of the two has to be renamed
  (the E3State466 one is generated by `scripts/generate_e3_state466_lean.py`, so the
  cheaper fix is probably renaming in `ES6AnchoredEncoding` + `ES6Anchored*` consumers,
  which costs an ES6 family rebuild; renaming the E3State466 one costs that family's
  rebuild). Until then `[extract] imports` lists the destination modules on the ES6
  side; `decomposableExactUpperAt_six` and `decomposableStateUpper_488` (E3 side)
  are reported as missing destinations.
- **A 318-module rebuild is pending.** Uncommitted hand-written edits from the
  previous session (`StructuralChargingCupBlocks45`, `StrongPredecessorFractionalDual`,
  ... eight modules) sit upstream of the Mixed567, ExtremeExchangeK9, DiagonalCupBlocksK9
  and Pascal556 certificate families; Lake wants 318 modules rebuilt (263 generated).
  `es build core` handles this one module per guarded invocation, but it is a
  multi-hour job and was not started without a go-ahead. Twenty-four of those modules
  currently have no olean at all (their rebuild was in flight when the first,
  fully parallel attempt hit the 20 GB memory cap).
- The first taint scan of the ES6 + Fin15 closures (8,425 modules, 2.0 M constants)
  took 42 min; with the cache warm a full extraction takes about a minute.
  `predecessorHalfSubsetAt_six`, `forces_six`, `erdosSzekeresFormulaAt_six` and the
  other ES6-side destinations depend on no non-standard axiom; the scan also found
  the `native_decide` auxiliary axiom under `fin4_permutation_reorder_table`.

- **Seed nodes.** Of the §11 seeds, `forces_six`, `strongSixCardinalityCeiling`,
  `predecessorHalfSubsetAt_six`, `erdosSzekeresFormulaAt_six` and the Fin15 endpoint
  were already theorems in ESCore on 2026-09-04 (they are destinations instead).
  Added: `forcesConvexPolygon_of_sweepExactUpperAt` (A), `sweepExactUpperAt_of_predecessorHalfSubset_all`
  (A), `predecessorHalfSubsetAt_all` (E, conjecture, falsifier
  `harness/falsifiers/predecessor_half_constructions.py`). Not added:
  `decomposableStateUpper_all` (B) — its import of `E3FiniteReduction` puts the
  E3State466 encoding in the same environment as the ES(6) certificate, i.e. the
  `StrongSixValues` clash; add it once one definition is renamed. The C (`etv_cap_five`)
  and B2/D/F conjecture nodes wait for their falsifiers (milestone M5). Lock entries
  carry `approved_by = "fable (provisional; Gavin to confirm via CODEOWNERS review)"`.

## Acceptance checklist (§13)

| # | Item | State | Evidence (2026-09-04) |
| --- | --- | --- | --- |
| 1 | `lake build ESCore` from warm cache within budget | **blocked** | the root does not build (`StrongSixValues` clash) and 318 modules are stale; the eight hand-written stale modules built serially in 3–53 s each under the guard |
| 2 | `es layers` passes; an unlisted ESCore→certificate import fails | done | passes on the tree (9,857 / 364 / 4 modules); unit test `test_core_importing_certificate_outside_allowlist_fails` |
| 3 | `es extract` lists nodes with correct sorry/axioms; a proof flips a node to closed | done | smoke node: open → `es check` → closed, standard axioms only, no harness file edited |
| 4 | `--check` fails on a hand-edited statement, passes after `es node restate` | done | "statement changed by hand (lock b948…, now 506a…)"; restate rewrote the lock and appended to `restatements.md` |
| 5 | `es node add` refuses a duplicate of an existing theorem | done | `forces_six_dup` refused: "duplicates core theorem ErdosSzekeres.forces_six" |
| 6 | `es audit` fails on a new axiom, passes once allowlisted | done | `native_decide` produced `…_native.native_decide.ax_1_1`, audit failed; allowlist entries accept globs (`*._native.native_decide.*`) because Lean 4.29 names these axioms per declaration (unit-tested) |
| 7 | `es close` moves the module, rewrites imports, rebuilds the consumer, node leaves `es status` | done | moved to `ErdosSzekeres/Closed/G/…`, two import rewrites, root import appended, destination added, status no longer lists it |
| 8 | `es ready` hides a conjecture until `es falsify` passes; exit 2 marks it refuted with a witness | done | contract fixtures; also the real E node went proposed → ready after `predecessor_half_constructions.py` passed |
| 9 | two sessions see each other's claims; expired claims disappear | done | two `ES_AGENT`s: second claim refused, status shows the claimant; expiry unit-tested |
| 10 | `es search "strong five-free support"` returns the Fin13 window transport theorem | partial | that phrase ranks the base-six lemmas first; `es search "Fin13 window"` / `"window transport"` return `predecessorFreeSevenSubsetAtSixFinThirteenWindow_of_oneChange` at the top (its docstring does not contain the phrase) |
| 11 | a fresh session gets the frontier from the SessionStart hook | done | `tools/es/hooks/session_start.sh` prints `es status --brief` (hooks registered in `.claude/settings.json`) |
| 12 | a commit that violates layering or the lock is blocked by the pre-bash hook | done | `pre_bash.sh` runs `es layers && es extract --check && es audit --changed` and exits 2 on failure |
| 13 | `es note` writes a weekly note matching `attempts` and status diffs | done | `docs/notes/2026-W36.md` written from the events/attempts tables |
| 14 | `pytest tools/es/tests` passes without Lean; CI `lean` job passes with it | partial | 35 tests pass (extractor mocked by fixtures); the `lean` job is written but gated on a self-hosted runner |

Milestones: M1 done except the physical certificate move (deferred, see deviations);
M2 done (extractor, frontier, node commands, lock, seed nodes A/E); M3 done (audit,
allowlist, close, attempts); M4 done (search, claims, MCP, hooks, CLAUDE.md, PR
template, CODEOWNERS, pr-shape job, note; branch protection is a GitHub setting);
M5 partial (`es falsify`, jobs, worker, dataset layout, one real falsifier; B/C
conjecture seeds pending falsifiers and the clash fix); M6 not started (banners only).
