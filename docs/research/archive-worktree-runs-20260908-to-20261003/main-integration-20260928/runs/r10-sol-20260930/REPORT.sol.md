# R10 Sol report

Closed and committed at 2026-09-30 15:59 UTC:
`b58edc4cc368f92dbbf26a3aa0f3cbdfdbcbe745`, on
`node/CtxBoundPartRunContractionOfOneLevelRoot`. The worktree is clean.

The proof derives contraction in arbitrary parts of well-formed single-run
contexts from the explicit root hypothesis `hroot`. It normalizes both the
part and its contraction, identifies ancestor capacities by ordered
child-deletion transport and the closed constant-run-limit theorem, removes
inert exterior history by exact fuel induction, and invokes `hroot` on the
remaining one-level word. The registered statement and docstring are unchanged.

Checks:

- `20260930-113454-900ba6`: inert endpoint transport, rc 0.
- `20260930-114039-49c421`: local helper assembly, rc 0 (diagnostic only).
- `20260930-114807-1296db`: full exact-statement candidate, rc 0,
  19.9 s, 682 MiB, all outputs present.
- `git diff --check`: clean.
- `20260930-115042-a5d00c`: targeted check cancelled while unstarted,
  because its 20G fallback reservation could not fit; no proof result.
- `20260930-115406-87ab9e`: identical targeted `es check` in a 6G worker
  reservation, rc 0, 114.9 s, 2353 MiB, all outputs present. It reports
  `closed`, `sorry=false`, only `propext`, `Classical.choice`, `Quot.sound`,
  and unchanged type hash `15a30a4e651354ba`. Receipt:
  `1de650ee0589affa54d452e27dea92de8232cb6e90707dc829ef09e76276b046`
  (`TARGETED-CHECK.json`). Module build: 22.49 s; targeted incremental
  extraction only.
- `20260930-115816-9fe979`: `es node commit`, rc 0; exactly the node module
  and generated node/status records committed, no uncommitted tracked files.

No merge, push, full extraction, delegation, or other statement edits.
No workflow script, custom axiom, `native_decide`, or new `sorry` was added.
Failed compiler attempts and exact evidence paths are in
`MATHEMATICAL-HANDOFF.md` and the shared journal.

R10's mathematical obligation is complete. `hroot` remains an explicit
premise; the root contraction conjecture is not proved by this bridge.
The safest next action is coordinator review/integration of this single
node commit. No second trial is authorized. Mathematical details, failed
attempts, reuse/deferred promotion, and review records are in the handoff.
The coordinator verified the receipt and module and ended research early at
2026-09-30T16:00:47.382560Z; the user made that instant the research deadline.
This finalization turn revalidated the existing receipts and workspace;
it launched no new research or checks. PROGRESS.md records closure/commit.

Research window `window-873fe0c3430041b4` ended with one accepted result;
review `window-214a569e709d45d5` and maintenance
`window-d9dddfc11b634533` ended separately. An implicit usage sync refused
to reassign an already attributed response; explicit reconciliation keeps
the original research-window assignment. Token attribution cannot split
that single long response between review/maintenance windows. No savings
claim is made. Factual operation/usage bundle: `HARNESS-HANDOFF.json`.
Claim released `closed`; no pending R10 jobs or tracked changes remain.
The harness automatically preserved the mathematical handoff in the primary
checkout's run artifacts on release; primary source files were not edited.
