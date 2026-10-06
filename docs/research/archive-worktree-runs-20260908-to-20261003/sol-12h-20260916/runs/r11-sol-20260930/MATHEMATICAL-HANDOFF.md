# R11 mathematical handoff

Both authorized reductions are closed and committed, in the requested order and on separate
branches. Agent `codex:01a0f2ee-e8b3-78d0-8d67-59fe27405b5b`, configured gpt-6.1-sol at xhigh;
no delegation. Research window `window-60c40fd28a2d49f9` ended with two accepted results.
Final review window `window-fceddeeee2e54f21` is separate.

## Exact accepted results

1. `ErdosSzekeres.ctx_bound_additive_single_run_alternating_of_part_contraction_and_deletion`
   on `node/CtxBoundAdditiveSingleRunAlternatingOfPartContractionAndDeletion`.
   Proof commit `254357db32a5e3b3d3364c4e1f6be87df005d546`; `es node commit` job
   `20260930-113931-e29ebb`, rc=0. Locked type `1024dcf9ff295899`.
   Scratch `20260930-113255-b00ef1`: rc=0,19.1s,peak643MiB.
   Targeted registered check `20260930-113654-9334ed`: rc=0,113.6s,peak2362MiB,
   `sorry=false`, `lock_ok=true`, precisely `propext`, `Classical.choice`, `Quot.sound`,
   no nonstandard/uncovered axioms or missing outputs. Incremental targeted extraction only.
2. `ErdosSzekeres.ctx_bound_additive_single_run_of_part_contraction_and_alternating`
   on `node/CtxBoundAdditiveSingleRunOfPartContractionAndAlternating`.
   Proof commit `e1d3ec8053c5d025c789826f267593c3b4621281`; `es node commit` job
   `20260930-114958-1f699e`, rc=0. Locked type `bb363755215dc459`.
   Scratch `20260930-114612-1d89c5`: rc=0,13.0s,peak600MiB.
   Targeted registered check `20260930-114717-d79169`: rc=0,100.5s,peak2349MiB,
   `sorry=false`, `lock_ok=true`, the same three standard axioms, no nonstandard/uncovered
   axioms or missing outputs. Incremental targeted extraction only.
   Per the updated brief, registered exactly immutable `R6P-TYPE.txt` first:
   job `20260930-114142-a8bf92`, rc=0,160.9s,peak2290MiB; registration commit
   `aabf60cc4e17d50150f3d1eef1ce48017231a7d8`, job `20260930-114517-7e40bf`.

Both proof commits contain only their own node module and generated `harness/nodes.json`
and `harness/status.md`. R6p registration additionally contains its root import and new lock
entry. `AUDIT.final.json` verifies both branch heads, committed-source/scratch equality,
exact registered signature/docstring bytes, unchanged locks across proof commits,
terminal proof receipts and clean tracked tree. R6p registration adds only its approved
statement; every older lock entry is identical to the base. No proof source changed afterward.

## Proof argument and reusable observations

Copy the closed R9 and R6 bodies, retaining their induction and word bookkeeping. Both
reconstruct the parent word as `L ++ replicate n child ++ R`, with no children in `L ++ R`.
Boolean keep labels paint the exact part word through `hPartPaint`. Each body's sole old
`hcontract` call already acts on `τ.part (keepOf L.length labels) s m`. Apply `hpart` directly:

```lean
have hrun : τ.numRuns ≤ 1 :=
  hRunCount τ L.length _ (hPositions τ L R _ hout hw)
```

Pass `τ`, its existing well-formedness proof, `hrun`, the original keep/side/coupling bounds,
and the exact doubled-child word equality. No general C1 hypothesis is synthesized. The
existing literal shortened-parent representation already handles separator deletion in R9
and repeated kept-label deletion in R6. No new representation lemma is needed; the obsolete
local `hSpan` proofs are removed.

- R9: use `hdel` to delete a false separator from an isolated alternating part while another
  separator remains. The shortened parent is well formed by `hWF` and still a literal child
  block. Contract the doubled true tooth with `hpart`. Shortening by two preserves the parent
  base through closed base contraction. Both orientations reduce to the shorter alternating
  partition; lengths two/three use closed prefix/suffix and singleton-ended sandwich bounds.
- R6: compress equal neighboring Boolean labels. True labels use `hpart`; false labels use
  closed external-letter contraction. Shortening preserves the parent base. If no repeated
  labels exist, the list is the exact parity partition supplied by `halternating`.
  Membership-based `part_congr` handles arbitrary keep lists, including duplicates.
  Nonempty keep gives a true label; the strict keep-length bound and nodup child positions
  force a false label. No additional nodup hypothesis is introduced.

Source checkpoints in the accepted `R9p.module.lean` / `R6p.module.lean` snapshots:

| Fact | R9p line | R6p line |
| --- | --- | --- |
| Single-run child interval | 28 | 31 |
| Well-formedness transport | 154 | 157 |
| Child-block positions and run count | 192 / 231 | 195 / 234 |
| Painted-part contraction with hpart | 511 | 481 |
| Strong induction | 635 | 516 |

These are local facts in the compiling registered reductions, not standalone helper nodes.
The trial has no remaining mathematical obligation. Outside it, the explicit assumptions
remain: C1p contraction on parts, deletion monotonicity for isolated children, and alternating
additivity. R9p proves C1p + deletion implies alternating; R6p proves C1p + alternating implies
arbitrary single-run additivity. Neither proves those hypotheses, root contraction,
unconditional additivity, or the happy-ending conjecture.

## Failures and infrastructure limits

No mathematical proof attempt failed: both first scratch compiles passed.

- Direct checkout met read-only `.git-data/index.lock`. Guarded worker switches
  `20260930-113018-81ceb5` and `20260930-114026-bc5dff` passed. Their original receipts
  report declared output paths missing because `--out` does not redirect stdout.
  Retained those receipts; copied existing logs to `checkout-r9p`/`checkout-r6p` after
  completion. Branch/commit checks independently verify the switches.
- CamelCase module names were invalid node lookup/claim names; exact declaration names
  worked. R6p's first lookup/claim found no node because coordinator registration failed
  on a missing line break in a `let`. The updated brief authorized exact corrected-type
  registration. `R6P-TYPE.txt` was never edited.
- Sandbox-side check `20260930-113424-cb098c` reserved20G because guarded dependency
  preflight could not reach the bus. Withdrew it while queued, rc=130; no compiler ran.
  The identical targeted check passed on the worker under6G. No coverage was dropped.
- R6p retains one unnecessarySimpa warning. Imported pre-existing open
  `CtxBoundAttainedByEndCut` also replays a warning, but is absent from the target's
  transitive axioms: its registered theorem has no `sorryAx`.
- Read-only final audit initially expected generic `result.rc` in commit receipts, which
  instead use `result.ok/sha/branch/files` plus `job.exit_code`. Logged the schema error,
  repaired inspection and reran the full audit successfully.
- Final artifact patch rejected a delete/add pair on one handoff path before editing.
  Logged it and used a single replacement; proof source/receipts were unaffected.

Every finding/follow-up was logged. No self-chosen compile kill budget was used; jobs finished
before review checkpoints. No review-due computation was ignored. `es release` automatically
preserves cited handoff evidence in primary `runs/`; shared state and that harness copy are
the only primary writes. No manual primary source/branch edits, merge, push, full extract,
other statement edit or additional trial occurred.

## Evidence, review and safe next action

For each `r9p`/`r6p`, retain `CHECK.*.json`, `NODE.*.closed.json`,
`RECEIPT.scratch-*.json`, `RECEIPT.check-*.json`, `RECEIPT.commit-*.json`,
`R9p`/`R6p` `.stub.lean`, `.body.lean`, `.module.lean`, `.lean`, `SHA256.*.txt`,
`LOG.scratch-*.txt`; also R6p registration receipts, `AUDIT.final.json`, `JOURNAL.sol.json`,
research-window handoff and usage snapshots. Original proof-capture fixtures snapshot the
registered stubs; the kernel evidence is the scratch/targeted receipts, not those fixtures.

Reviewed source assembly assertions/parser reuse, hpart hypotheses, induction decreases,
both orientations, duplicate keeps, every inline job command, receipts and commit scopes.
Reused harness `whole_span`, job/check/commit commands and existing local mathematical facts.
No tracked scripts/shared algorithms changed. One-off source assembly and receipt inspection
need no promotion. Extraction of duplicated local List/Bool facts is deferred to later
library review, outside this trial's scope. Review was performed by this configured Sol
under the explicit model/no-delegation constraint; coordinator review remains external.

Safest next action: review both commits and targeted receipts, then decide integration and
how to discharge explicit C1p/deletion assumptions, including the independent R10 bridge.
No R11 compiler jobs remain. Release claims, publish `PROGRESS.md` and `REPORT.sol.md`, then
stop this trial. The native goal is not marked complete before its fixed
`2026-09-30T23:28:59.179712Z` instant; coordinator early finish is requested by the brief.
