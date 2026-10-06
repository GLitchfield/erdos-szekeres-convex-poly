# R12 mathematical handoff

Finalized 2026-09-30 after the coordinator's early cutoff at
2026-09-30T17:12:27.157887Z. All three authorized proof replacements are checked, committed
and reviewed, in order, on separate node branches. No further R12 mathematical development
is needed. Only existing evidence and reporting were handled after the cutoff; no compiler
or research job was started. The finalization hard stop is 2026-09-30T17:42:27.157887Z.

## Accepted results and exact receipts

1. `ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end`
   - Branch `node/CtxBoundAdditiveSandwichOneSingletonEnd`.
   - Commit `4eecb22ec60c0cf616f17d12b72c0c7d310b4d93`; commit job
     `20260930-123429-98a2eb`, rc 0.
   - Targeted check `20260930-121912-c6b2de`, rc 0, 107 s total; module build 9.01 s,
     peak 575 MiB. Receipt `20a853de9fcfa0f777b7d0ada87a7ad9b1f907e032a4e0d034d1d72ef8b0b531`
     in `SANDWICH-CHECK.json`.
   - Unchanged type `f0546849c2ec6e87`, lock matches; only blocking node
     `ErdosSzekeres.ctx_bound_additive_single_run`.

2. `ErdosSzekeres.ctx_bound_additive_three_blocks`
   - Branch `node/CtxBoundAdditiveThreeBlocks`.
   - Commit `65293c48b3b4fbff3e8b7309d1c635c702533360`; commit job
     `20260930-124403-d3cb09`, rc 0.
   - Targeted check `20260930-124150-17bbf1`, rc 0; module build 8.36 s, peak 573 MiB.
     Receipt `1303dd0b96f8ef88ddd116d14cf3e04524a69ec28c2a1978fedc8c35eb56763f`
     in `THREE-BLOCKS-CHECK.json`.
   - Unchanged type `45248c571dd09384`, lock matches; only blocking node
     `ErdosSzekeres.ctx_bound_additive_single_run`.

3. `ErdosSzekeres.ctx_bound_uniform_separator_contraction`
   - Branch `node/CtxBoundUniformSeparatorContraction`.
   - Commit `c589080a24bd4bfe355b63b2139b198a80ae1e3d`; commit job
     `20260930-130254-8e2dd5`, rc 0.
   - Targeted check `20260930-130025-3ac084`, rc 0; module build 9.56 s, peak 636 MiB.
     Receipt `2729678704849df6eb1848277e9c028cf6cc8df9c799e6a2b2d0c1ec12a94caa`
     in `UNIFORM-CHECK.json`.
   - Unchanged type `4b3e67b06d755b0e`, lock matches; only blocking node
     `ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root`.
     The other substantive dependency is the closed
     `ctx_bound_part_run_contraction_of_one_level_root` bridge.

Every check was targeted and updated the index incrementally. Every receipt reports
`sorry=true` with exactly `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.
The proof bodies contain no direct `sorry`, axiom, or `native_decide`. These are closure
modulo the named dependencies, not unconditional sorry-free theorems.

Every commit changes exactly its own node module and generated `harness/nodes.json` /
`harness/status.md`, relative to its actual parent. First two parents are
`f55e3b9245ab20056598d7dfce8b8d88abd2a0b0`; third parent is
`857827d680fd52f622704d436fd7d1383bd7182c`: coordinator main advanced before the third
branch was created. Inherited C3/falsifier changes relative to the initial base are not R12 edits.
A blanket same-parent assertion in one audit log was corrected immediately after inspection.
All branches were created from then-current main, as instructed; no merge or push occurred.

## Mathematics

The first two proofs use keep = the two outer intervals. Every child run start must be the
interval's first position, since each later child has a child predecessor. Nodup/cardinality
therefore gives at most one run. Interval membership proves keep inclusion and positivity
gives nonempty/proper keep. Sorted-list membership identifies the filtered complement exactly
with the middle interval. Apply `ctx_bound_additive_single_run` for both orientations.
The first proof does not use its singleton-end hypothesis.

For uniform contraction, retain the original parameters, lower exterior external levels by
one, replace the entire run/separator/run span by an uninterrupted child block, and use
`maxima.tail`. The exterior hypothesis (levels at least two) gives positive ancestor levels.
Original well-formedness bounds those levels by the tail length and proves one side per level,
including the ancestor side selector. This works for every replacement child-block length.

The positive separator ensures the original maxima list is nonempty. Its head M satisfies
1 <= M <= k-2. For every Bool list bs, a painted family with the original exterior and
children at true entries is exactly a part of the corresponding ancestor, with keep pulled
from the true entries and new maximum M. Shifting the lowered exterior back restores the
original word; M :: maxima.tail restores the original maxima.

For any pre/post lists, apply the closed bridge to C1r to contract
pre ++ true :: true :: post to pre ++ true :: post. Rebuild the ancestor for each word size,
so every step is genuinely a part of a single-run context. Separate natural-number inductions
shorten the left run and then the right run. Unit run lengths are the base cases. No extra
positive internal-capacity assumption or general C1 hypothesis is used.

The exact open dependencies are the original single-run additivity theorem for the first two
nodes and C1r for the third. C1r remains a conjecture for bare-root one-level words over children
and one side of level-one external letters, parameters 1 <= a,u <= k, 3 <= k, and 1 <= M <= k-2.
R12 does not prove those dependencies and does not authorize another trial.

## Scratch and failed attempts

- Sandwich initial scratch `20260930-121221-273cd5`: interval start was supplied as range step.
  Fixed to step 1; exact scratch `20260930-121305-2d8ee3` and installed-file
  `20260930-121738-dae0a3` passed.
- Initial sandwich targeted wrapper `20260930-121347-4284c4`: refused before Lean, 20G
  fallback above 6G outer cap. Import prebuild `20260930-121444-39f9c6` refused twice before
  Lean due to occupied project reservation. A later successful read-only dependency probe
  sized the async check to 4G; stale imports were not established.
- Reconciliation `20260930-121619-0086bc` released nothing. Host process/tree diagnostics
  `20260930-121738-b81e52`, `20260930-121919-d8a168` confirmed the coordinator's C1r
  falsifier `20260930-120418-655daa` was live. It later completed rc 0; no job was killed.
- First branch-create job `20260930-121120-90cda0` succeeded but its declared output was
  missing at termination. Original receipt subsequently preserved at `branch-sandwich`;
  this does not retroactively change the original receipt.
- One compile submission named an output outside runs/data and was refused before launch.
  Corrected installed-source job is listed above.
- Three-block exact scratch `20260930-123642-55c4ab` passed. Initial targeted
  `20260930-123814-17c7c9` failed because proof copying split at the first local := by and
  truncated the body. One repair patch refused because that marker was itself absent.
  Full-body copying fixed it; installed-file `20260930-124007-d9fc6b` passed before retry.
  Failed receipt remains `THREE-BLOCKS-CHECK.failed.json`.
- Uniform ancestor `20260930-124728-144f67`: record field-layout parse error; retry
  `20260930-124825-c8074f`: substitution removed witness binders still referenced.
  Repaired; `20260930-124907-e07e8c` passed.
- Uniform representation `20260930-125251-b8ad85`: underspecified context arguments with
  early rfl inferred identical records. Explicit context terms fixed it;
  `20260930-125347-6f8cec` passed.
- Bridge step `20260930-125504-912ef0` passed. These helper files conclude True and are
  diagnostic local-helper evidence, not registered theorem receipts.
- Full exact-statement `UniformCandidate.lean`, `20260930-125715-7c7e85`, and original
  header/qualified `UniformInstalledCandidate.lean`, `20260930-125832-1777fe`, passed
  without warnings. Installed source/candidate SHA-256
  `6d36dd12710e2f80c0dc23216bcc04d6bda8eea9b81207cd9a310bca4ce355a1`;
  the targeted check covers the final one-line style wrap.

No failed mathematical conjecture or unresolved missing lemma arose. Compiler errors were
syntactic, binder/inference, or copying issues and are preserved in the shared job logs.

## Review, usage and resumption

Configured model throughout: gpt-6.1-sol, xhigh, no delegation. Initial first claim/jobs used
`codex:01a0f314-2bec-7b02-a6f2-f0c9f6c320ad`; future jobs use the native host identity
`codex:agent-run-8dea069568ec49c9`. Both refer to this same thread/trial; all IDs are preserved.
Research window `window-2ea7c559b25346e8` ended with three checked conditional results.
Mathematical review `window-bdf38ddd957a458d` ended; maintenance review
`window-bca2009b63054f19` records the ad hoc code and command review.
The authoritative host all-in window is `window-79fe6421c2214ff4`;
`FINAL-USAGE-SYNC.json` and refreshed `HARNESS-HANDOFF.json` record the finalization snapshot.
Usage snapshots may lag active reporting; the host can reconcile the last response after exit.
No savings comparison or final-cost claim is made.

Reviewed all new scratch code, changed tracked proof modules and inline job commands.
No Python/workflow script or certificate regeneration was introduced. Reused R6/R11 local
membership, run-count and painted-word transports and harness jobs/check/commit/artifact
automation. Lowering/part-family helpers may be reusable, but promotion is deferred because
this trial permits only three existing proof bodies, and there is no authorized standalone node
or generic workflow contract to add. Original artifacts remain intact.

No research/check/commit job remains pending. The final worktree is clean on the third branch.
All three claims were released partial because their dependencies remain open.
Handoffs are attached immutably to release
logs; runs-path release notes are avoided because the harness would auto-copy them into the
primary checkout, which this trial forbids. No primary source/run file was edited or copied.

The coordinator independently verified the three compositions and expected single_run / C1r
blockers and ended research early at the timestamp above, superseding the original deadline.
Final source audit compared each theorem's statement and docstring to its actual commit parent:
all unchanged, with no direct sorry/native_decide/axiom in the proof bodies. Saved check and
commit receipts support all claims. Native host `20260930-120936-23367c` is the process serving
this finalization turn; its eventual exit is not a pending research check.

`FINAL-REVIEW.json` references immutable sanitized review artifact
`045257db5da64e019a0fbe93f47e55be937a0842589bdbbf5cd5898054a0cdad`, inspected in bounded
chunks. It reports no active claims or pending jobs for the native host identity, and assigns
no theorem credit. Its three validation entries include the failed initial three-block check
and the two later successful checks; the successful sandwich check is omitted because it
used the initial identity. That check's saved receipt and current job status were separately
verified. Its baseline-to-worktree code inventory contains inherited coordinator changes;
R12's exact scope remains the three commit diffs relative to their actual parents.
The artifact reader's default 4096-byte truncation and rejected overlarge limit were logged;
complete evidence was then read using supported bounded chunks. No evidence was lost.

Mathematical work and final reporting are complete for R12. Do not restart any compiler or
trial. Safest next action: coordinator performs its authorized integration and host
finalization. The native goal can be marked complete for the three requested conditional
compositions; the named dependencies remain open. Late usage reconciliation remains host
lifecycle bookkeeping.
