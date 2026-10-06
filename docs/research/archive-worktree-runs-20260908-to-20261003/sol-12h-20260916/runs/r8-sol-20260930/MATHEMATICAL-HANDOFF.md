# R8 mathematical handoff — node closed

Agent `codex:agent-run-ea2920bdae864f85`, gpt-6.1-sol at xhigh, no delegation.
Thread `01a0f269-88d8-7053-906d-e9fc42afa312`; worktree/branch are those in RESEARCH-BRIEF.md.
Baseline `73675e50874881119df95f689c907e729400f008`.
Proof commit `bf243a393c9a220ffc1ea0d4e5f387fd0c52d70a`, created through
`es node commit` job `20260930-092220-63abf4` (rc=0). Tracked working tree clean.

## Exact obligation

Prove the registered theorem
`ErdosSzekeres.ctx_bound_ext_letter_deletion_mono_of_isolated_children`:
for WellFormed σ with no adjacent child positions, and
σ.word = left ++ [ext lev side] ++ right with ext lev side also in left ++ right,
σ.bound ≤ ({σ with word := left ++ right}).bound. Signature/docstring were preserved.

## Current proof and evidence

Complete scratch proof `Transport.lean` and `Transport.accepted05.lean` passed guarded
job `20260930-091430-8e8366`, rc=0, 12.42s, max RSS 3932864 KiB, no warnings.
The proof is now in `ESBlueprint/B/CtxBoundExtLetterDeletionMonoOfIsolatedChildren.lean`.
Targeted audit `20260930-091640-28f1ec` passed rc=0: `sorry=False`, `status=closed`,
axioms exactly `propext`, `Classical.choice`, `Quot.sound`, no uncovered/nonstandard axioms.
Type hash `41d377ff917bd9a1`, lock matches. New module build 14s; whole guarded check
180.8s, sampled peak 2383 MiB, no OOM/budget exceed. One node module re-extracted
incrementally; no full extraction. One exact registered theorem is closed.
Receipts `TARGETED-CHECK.json`, `NODE-CLOSED.json`, `COMMIT-JOB.json`.
Node closure artifact `3338b093cde6c847b8934c9c889262d281fb2c48a0de50cae27c4508007beeca`.
Final source fixture `8b29c702a5cce327954a43b84afe9b8939bdc66bead43b3e66422ef4a687e6ea`
freezes the checked source/dependencies; capture is not itself an acceptance receipt.

The proof has only local helper lemmas (no new registered statements):

1. `up p i = if i < p then i else i+1` embeds the deleted word's positions into the original.
   Filtered ranges, child positions and indexed external positions commute with this map.
   Indexed histories and sides agree when the inserted level exceeds maxima.length.
2. Left/right fold count transport yields base equality. Blocks and complementary keep
   lists commute with the map. Isolated source child positions have one run per child.
3. Any new target adjacency must straddle the deleted position. A target with ≤1 run is
   an interval (reused local proof pattern from the closed R6 reduction). If the source
   has ≥2 runs and target has ≤1, the target has exactly two consecutive children.
   Its only proper blocks are the singleton prefix and suffix. Closed
   `ctx_bound_additive_prefix_suffix` controls both orientations, all admissible couplings.
4. Induction on source fuel proves `boundFuel f big ≤ small.bound` for every f. It carries
   target WellFormed and source isolation. Parts preserve target WellFormed, source
   isolation and inertness (inserted level and maxima depth both increase by one).
   Target multi-run cuts use `ctx_bound_cut_le`; merged targets use step 3. Comparing to
   the target full bound avoids extra equal-fuel bookkeeping and proves the exact goal.
5. The deleted context is WellFormed: all remaining occurrence tags still agree at each
   indexed level. The other identical ext occurrence supplies a retained witness to
   `ctx_single_level_occurrence_prune_bound_mono`, with keep = all positions except p.
   The prune map changes exactly p to `ext (maxima.length+1) side`. Combine prune
   monotonicity with step 4. The intermediate inert context intentionally is not WellFormed.

Module line map: order/range/history at 20/25/77, folds/base at 116/156, blocks/rest at
229/239, isolation/adjacency at 262/287, single-run interval at 300, merge shape/cuts at
395/418, fuel induction at 445, uniform side/deleted context at 533/558/586, occurrence
prune at 617/622/629, final inert bound composition at 673.

## Failed approaches and infrastructure

No failed mathematical conjecture or counterexample. Two scratch compiler failures:
`20260930-090606-227b90`: range identity tactic misuse, semicolon scoping and unexpanded
Function.comp after filter_map; fixed by explicit map congruence/rewrites.
`20260930-091341-108093`: match predicate needed simplification and retained-letter
equalities had reversed orientation; fixed without changing the proof route.
Failed snapshots `Transport.attempt01.lean`, `Transport.attempt05.lean` preserve diagnostics.
All intermediate successes have acceptedNN snapshots and corresponding shared job logs.

`es status` fails in burn_down because a journal detail is a string; scoped commands and
`es status --brief --full` work. No harness changes were made.
`es check --async --targeted` reserved generic 20G and remained queued under shared caps;
job `20260930-091532-856030` was cancelled before execution (no log/compile). Follow-up
job `20260930-091640-28f1ec` guards the same synchronous targeted check at 5G. It is not
a stopped computation or a mathematical failure. Checkpoint review left it running.

## Review and remaining actions

Targeted receipt and postcommit node status inspected: exact theorem closed, standard
axioms only, approved type unchanged. Exact docstring/signature diff versus
`Node.original.lean` and `git diff --check` passed. Commit touches exactly the node module,
`harness/nodes.json`, `harness/status.md`; generated node diff concerns only this node
plus aggregate extraction/status metadata. No other statement changed.

Solo mathematical/code review in `window-f8a58ff3ec1b4424` follows research window
`window-65885abecb2d4f22` (one accepted theorem). Only configured Sol model used, with no
delegation. New/changed ad hoc Lean files and recorded inline commands reviewed. Reused
existing es automation and local patterns from external contraction/R6 interval proof.
No new Python/workflow glue or executable algorithm was introduced; no script promotion
applies. Shared Lean transport/interval helper extraction deferred under one-node scope.
No independent Astra review was performed because this trial prohibits other models/agents.

No mathematical obligation remains for this node. Full conjecture, C1 and independent
R9/C3 work remain outside this trial. Safest next action is review of this proof commit
and later use of the closed theorem in that reduction. Do not merge, push, run a full
extract, edit another statement or begin another trial. No custom axiom/native_decide/
sorry was added. Fixed dependency annotations differ from direct generated proof-helper
dependencies; this is diagnostic metadata, and the theorem's transitive axiom audit passes.
Pre-edit fixture `3af69c983fb8177baf625a0a7ef9f604978d77f1f1c5e1d4ef2015eb230b40ac`
is a freeze record of the original source, not a proof receipt.

Research deadline 2026-09-30T23:03:18.554193Z; consolidation starts
22:33:18.554193Z. The native goal must not be marked complete before the research deadline.
Both audit and commit jobs are terminal and their receipts are preserved. On resumption
read es status, this node's journal, this handoff and REPORT.sol.md; verify commit/status
before admitting any work. The timing gate is the remaining native-goal requirement;
do not mark complete before the deadline. The node claim was released with outcome closed;
the harness also mirrored release evidence to the primary checkout automatically.
