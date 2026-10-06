# R8 Sol report

**Result: CLOSED**, verified 2026-09-30 13:19 UTC.
The exact registered node
`ErdosSzekeres.ctx_bound_ext_letter_deletion_mono_of_isolated_children`
is proved with standard axioms only. Statement/docstring unchanged;
type hash `41d377ff917bd9a1`, lock matches.
Commit **`bf243a393c9a220ffc1ea0d4e5f387fd0c52d70a`**, made with
`es node commit` job `20260930-092220-63abf4` (rc=0). Tracked working tree clean.
Claim released with outcome closed; all R8 compiler/check/commit jobs terminal.
The harness automatically mirrored the release handoff to the primary checkout;
no primary source edit, merge or push was performed.

## Change and proof

Changed only the requested node module and the harness's generated node/status records.
No other statement changed. The proof prunes the deleted occurrence to an inert level
while retaining an actual witness, then proves inert deletion monotonicity by induction
on source fuel. Mapped indexed histories give identical bases; mapped blocks give cuts.
For a merge to one target run, isolation forces exactly two consecutive children and
the closed prefix/suffix additivity theorem supplies both cut orientations.
The intermediate inert context is not assumed WellFormed; the deleted context is.

## Verification

Exact targeted command (inside explicit 5G guarded job `20260930-091640-28f1ec`):

```text
/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916 check ErdosSzekeres.ctx_bound_ext_letter_deletion_mono_of_isolated_children --targeted --force --full
```

Result rc=0, `sorry=False`, `status=closed`, axioms exactly `propext`,
`Classical.choice`, `Quot.sound`; no uncovered/nonstandard axioms. Build 14s, total
guarded audit 180.8s, sampled peak 2383 MiB, no OOM/budget exceed. One module was
re-extracted incrementally. No full extraction or whole-project build was run.
Receipts: `TARGETED-CHECK.json`, `NODE-CLOSED.json`, and shared harness log
`job-20260930-091640-28f1ec.log`. Closure artifact
`3338b093cde6c847b8934c9c889262d281fb2c48a0de50cae27c4508007beeca`.
Commit receipt `COMMIT-JOB.json`; final captured source fixture
`8b29c702a5cce327954a43b84afe9b8939bdc66bead43b3e66422ef4a687e6ea`.
`git diff --check` passed; exact docstring/signature comparison to `Node.original.lean`
passed. No `sorry`, `axiom` or `native_decide` appears in the node module.

Guarded scratch jobs (all 4G, no deadline wrappers):

| Job | Result | Scope |
| --- | --- | --- |
| `20260930-090606-227b90` | failed rc1 | Initial range/filter bookkeeping |
| `20260930-090701-0adef9` | passed rc0 | Position/history/fold transport |
| `20260930-090825-f93ba0` | passed rc0 | Bases, blocks, isolated runs |
| `20260930-091011-5b4118` | passed rc0 | Exact two-child merge and cuts |
| `20260930-091128-f0d031` | passed rc0 | Inert deletion fuel induction |
| `20260930-091341-108093` | failed rc1 | Full proof packaging elaboration |
| `20260930-091430-8e8366` | passed rc0 | Complete scratch proof, 12.42s, no warnings |

Generic async check `20260930-091532-856030` reserved 20G and remained queued;
cancelled before execution (no compile/log), then rerouted unchanged through the 5G
targeted audit above. At its progress checkpoint the build/extractor had completed;
review left it running. Failures, reroute and every finding were journaled.

## Review, scope and next action

Solo review used the configured gpt-6.1-sol at xhigh; no delegation or other model.
Research window `window-65885abecb2d4f22` ended with one checked result; separate review
window `window-f8a58ff3ec1b4424`. Reused `es` automation and existing Lean proof patterns;
no new Python/workflow script or algorithm was introduced. All run snippets were reviewed.
No script promotion is applicable. Future extraction of shared Lean transport/interval
helpers is deferred because this authorization closes exactly one node.

Open risks: the repository's proof of the full Erdős–Szekeres conjecture remains
incomplete; this theorem establishes only the requested reusable deletion step.
Fixed declared dependency metadata differs
from generated direct dependencies (local proof constants, prune/cut wrappers); the
axiom audit passes. Dependency-module lint/sorry warnings were replayed by Lake but
do not taint this theorem. `es status` burn-down formatting has an unrelated known error;
scoped status works. No mathematical obligation remains for this node.

Safest next action: review this node commit and supply the closed theorem to the R9/C3
reduction when its independent trial is ready. Do not start another R8 trial, merge or push.
Detailed proof/failed-attempt evidence is in `MATHEMATICAL-HANDOFF.md`.

Native timing contract: research admission deadline `2026-09-30T23:03:18.554193Z`,
consolidation `22:33:18.554193Z`. The node closed early; the native goal remains active
until the permitted completion instant. No further research trial is authorized.
At the 22:33 UTC consolidation gate, inspect the same commit, current node status,
receipts and these handoffs; repeat compilation only if changed state creates a reason.
At/after 23:03:18.554193 UTC, perform the requirement audit and mark the native goal
complete only if these verified results still hold.
