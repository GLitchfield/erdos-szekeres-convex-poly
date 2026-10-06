# R12 Sol report

Finalized 2026-09-30 after the coordinator's research cutoff at
2026-09-30T17:12:27.157887Z. All three requested existing-node proof replacements are
compiled, committed and reviewed, in order, on separate branches. Statements and docstrings
are unchanged. This finalization turn performed only receipt/source inspection and reporting;
no new research or compiler work followed the cutoff.

| Node suffix | Commit | Targeted check job | Remaining blocking node |
| --- | --- | --- | --- |
| ctx_bound_additive_sandwich_one_singleton_end | 4eecb22ec60c0cf616f17d12b72c0c7d310b4d93 | 20260930-121912-c6b2de | ctx_bound_additive_single_run |
| ctx_bound_additive_three_blocks | 65293c48b3b4fbff3e8b7309d1c635c702533360 | 20260930-124150-17bbf1 | ctx_bound_additive_single_run |
| ctx_bound_uniform_separator_contraction | c589080a24bd4bfe355b63b2139b198a80ae1e3d | 20260930-130025-3ac084 | ctx_bound_child_run_contraction_one_level_root |

All targeted jobs and commit jobs exited 0. Commit jobs are
`20260930-123429-98a2eb`, `20260930-124403-d3cb09`, `20260930-130254-8e2dd5`.
Exact receipts are `SANDWICH-CHECK.json`, `THREE-BLOCKS-CHECK.json`, `UNIFORM-CHECK.json`
in this directory. They report matching type locks (`f0546849c2ec6e87`,
`45248c571dd09384`, `4b3e67b06d755b0e`), targeted incremental extraction, and axioms
exactly `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.
The proof bodies contain no direct sorry; each sorry is inherited only through the listed
dependency. These are conditional closures, not proofs of single-run additivity or C1r.
Module builds took 9.01 / 8.36 / 9.56 seconds and peaked at 575 / 573 / 636 MiB.

The additivity proofs keep the two outer intervals, prove their complement is the middle
interval, show the original child interval has at most one run, and apply single-run additivity.
The first proof also works without its singleton-end restriction.

Uniform contraction lowers older exterior levels and uses tail maxima to reconstruct a
well-formed single-run ancestor. Every painted intermediate word is an exact part of a newly
sized ancestor with the original head maximum restored. The closed bridge applied to C1r
contracts each adjacent child pair; two inductions shorten the left and right runs to one.
The original parameters, maxima and separator multiplicity are preserved.

Every branch was created from then-current main. First two bases are `f55e3b92`; the third
base is `857827d6`, because coordinator main advanced before its creation. Each node commit
changes only its own module plus generated nodes/status relative to that parent. Inherited
C3/falsifier changes relative to the initial base are not R12 edits. Final worktree is clean on
`node/CtxBoundUniformSeparatorContraction`. No merge, push, primary source/run edit,
statement edit, full extract, delegation, new axiom/native_decide/sorry, or additional trial.

The initial build admission wait was caused by a live coordinator C1r falsifier; it later
finished, and no job was killed or cancelled. A three-block installation truncation and
uniform parser/binder/context-inference errors were corrected and preserved. No mathematical
route failed or missing lemma remains. Exact failure IDs and scratch evidence are in the
mathematical handoff; helper diagnostics concluding True grant no registered theorem credit.

Model: gpt-6.1-sol at xhigh throughout. Host window `window-79fe6421c2214ff4` includes
setup, failed attempts, recovery and review. Research and separate mathematical/maintenance
review windows are recorded in the handoff. `FINAL-USAGE-SYNC.json` records the refreshed
reconciled snapshot; an active request and the final response may still arrive later. No
savings or final usage claim is made. The host can reconcile late usage after this turn exits.

The coordinator independently verified all three compositions, their proof bodies, axioms
and intended blockers, then ended the research window early. This cutoff supersedes the
original 22:09 deadline; the single finalization turn has hard stop
2026-09-30T17:42:27.157887Z. `FINAL-REVIEW.json` references immutable review artifact
`045257db5da64e019a0fbe93f47e55be937a0842589bdbbf5cd5898054a0cdad`:
no active claims or pending research jobs. Its inventory alone grants no theorem credit;
the three saved targeted receipts and commit/source audit support this report. Its exact-agent
inventory omits the first check under the initial identity; that check was separately re-read
and is terminal rc 0. The inventory also includes inherited coordinator changes.

Safest next action: coordinator performs its authorized integration and host finalization.
The remaining root/single-run conjectures are outside this trial. The requested conditional
proof replacements and final report are complete; native goal completion is supported.

Detailed handoff:
`runs/r12-sol-20260930/MATHEMATICAL-HANDOFF.md` under
`/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/main-integration-20260928`.
No further R12 research, compiler check or trial is pending. Host exit/late usage reconciliation
is lifecycle bookkeeping, not an outstanding mathematical obligation.
