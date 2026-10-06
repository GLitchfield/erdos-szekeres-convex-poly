# Twelve-hour Sol/xhigh research brief

User authorization: prepare and run this one twelve-hour trial, make reviewed local commits,
and finish its review. Sol (`gpt-5.6-sol`, `xhigh`) owns research, Lean proofs, compiler repair,
and routine job follow-up. Astra coordinates the mathematics and performs final mathematical
and library review. Do not start another trial, push, or publish. Follow AGENTS.md.

## Recovered baseline and scope

Work only in `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`.
Reviewed mathematical source is `433d1b33`. Preparation commit `52e48fa2` cherry-picks
the worker observer, verified callbacks, and final review bundle from primary `5ea7c6ad`.
No Lean source changed in that cherry-pick. The original primary and September 13 worktrees
are preserved; the primary has unrelated ESBlueprint and dataset edits.

The baseline compiled frontier is **251 closed, 12 open, one refuted**, with zero stale
entries or problems. The parent is ready:
`ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end`.
Read `previous-mathematical-handoff.md`, `parent-context.json`, and the actual declarations.
Refresh current state with `es status` and `es ready`; extract first if stale. Claim the
parent before research and claim each newly registered node before proof work. The initial
branch reserves the proposed component theorem name; use one node per branch and preserve
checked progress in local commits as in the prior run. New statements use `es node add`;
revisions use `es node restate`. Never edit statement text by hand.

Run artifacts, probes, proof receipts, checkpoints, and the Sol report belong in
`runs/sol-12h-20260916/` within this research checkout. The native host uses its `host/`
subdirectory. Preserve the host's supplied `ES_AGENT`, `ES_WINDOW_ID`, model, effort,
thread, and frozen timing. The host research window is the authoritative Sol window;
do not create a second overlapping research window.

### Initial cache preparation overlaps source analysis

The mathematical sources and pinned dependencies are verified identical to the reviewed
baseline, the compiled source-hash index is fresh, and integrated harness tests pass
(206 passed, one skipped). An independent physical copy of the 135G Lean artifact cache
is still finishing under the separate Sol bootstrap helper. Its current guarded copy job
is `20260916-125101-e0cb90`; setup artifacts are in `runs/setup-20260916/`.
The helper owns transfer completion and a targeted compiler check of the existing final
residual classifier; it will write `runs/setup-20260916/READY.md` or `BLOCKED.md` with
terminal receipts. Do not duplicate its jobs, register statements, edit tracked Lean
sources, or compile against the partial cache before readiness. Start with substantive
reading of exact declarations, searches, mathematical analysis and proof-body planning
in run artifacts while this disk transfer finishes. Claim the chosen parent before that
research. Use bounded job waits when needed, not repeated status-only turns. After the
helper's readiness receipt, continue the full proof workflow. If its copy fails or the
helper report is absent after a terminal copy, inspect the evidence before recovering;
never treat a directory or partial output as a completed compiler check.

This initial source analysis is research; the separate bootstrap helper and its jobs
remain setup costs. The twelve-hour host deadline will not be extended for cache I/O.

## Mathematical objective and exact boundary

Primary success is a **compiling, audited theorem eliminating a documented remaining case**.
Useful reusable component bounds count as supporting infrastructure; theorem count alone
does not measure obstruction removal. A uniform two-marker theorem is the stronger target;
connecting it to parent sandwich additivity is the stretch target.

The prior run closed every actual two-marker endpoint cut at `k = 6`, lower-width internal
cuts, younger-surround cuts, between-marker intervals, and older-exterior intervals.
Its current classifier is
`ctx_two_marker_internal_complement_cut_six_top_width_middle_residual_classification`
in `ESBlueprint/B/CtxTwoMarkerInternalComplementCutSixTopWidthMiddleResidualClassification.lean`.
At opposite global five, the unresolved families are:

* The kept opposite interval surrounds the older marker, with complement maximum `m = 2` or `3`.
* The kept opposite interval lies exterior to the younger marker, away from the older marker.

Use actual declaration signatures, including positive external labels, distinct chosen
and opposite sides `s,t`, levels `N < M`, witnesses `x,y`, chosen global at most five,
empty opposite indexed history, exactly the two actual chosen positions, nonempty kept
children, excluded children `l,r` enclosing every kept child, and the relevant positional
condition. `N`/`x` are the younger marker and `M`/`y` the older marker in this convention.
Keep arbitrary original maxima, unused indexed levels, inactive children and positive
unindexed barriers where the existing statement permits them. Do not silently add global
well-formedness, word-size, active-child, or finite-search assumptions.

For legal `k = 6` corollaries, explicitly retain `σ.k = 6`, `1 ≤ m`, `1 ≤ n`,
`m + n = σ.k - 1`, opposite global at most five, and child-convexity when required by
the classifier. Distinguish hypotheses of the unconditional component theorem from those
of legal-coupling corollaries. Preserve independent fuel quantification **and** full bound
conclusions, so later recursive consumers can use the result.

## Ordered proposed directions

1. Expose the component estimates already proved inside
   `ctx_two_marker_younger_exterior_internal_complement_cut_potential_bound`, with exactly
   its hypotheses. Let `w := oppositeGlobal - 1`, `rest := σ.childPositions.filter (· ∉ keep)`,
   `α := σ.part rest s m`, `β := σ.part keep t n`. The intended reusable conclusion is
   `((∀ f, boundFuel f α ≤ (w+1).choose 2 + 1) ∧ α.bound ≤ (w+1).choose 2 + 1) ∧`
   `((∀ g, boundFuel g β ≤ w-2) ∧ β.bound ≤ w-2)`.
   At opposite global five this is `11 + 2 = 13`, one above twelve.
   Search first. Reuse the exported
   `ctx_three_ordered_markers_triangular_plus_one_bound`,
   `ctx_active_separating_marker_retained_boundary_rank_union_bound`, and
   `ctx_part_positive_letters`. The relevant existing proof tail starts around line 438
   and ends around line 618 in
   `ESBlueprint/B/CtxTwoMarkerYoungerExteriorInternalComplementCutPotentialBound.lean`.
   Avoid reproducing its old local helper proofs when the exported declarations suffice.

2. Test and formalize the proposed extreme-maximum reductions for the younger-exterior
   family. Legal coupling with `m=1` forces `n=4`; the proposed unit bound on β combines
   with eleven on α. With `m=4`, the proposed unit bound on α combines with two on β.
   The key existing theorem is `ctx_bound_le_one_of_large_sibling_maximum`; establish its
   actual indexed-level and maximum hypotheses after `part`, rather than reasoning from
   informal names. Compare the already checked older-surround extreme theorem in
   `CtxTwoMarkerOlderSurroundingInternalComplementCutSixBoundOfExtremeMaximum.lean`.
   These proposals are **not established results**. Log any failed implication, discovered
   counterexample, missing hypothesis, or change of direction before changing the plan.

3. If those reductions hold, compose the classifier to isolate precisely
   `oppositeGlobal = 5 ∧ (m=2 ∨ m=3) ∧ (older-surround ∨ younger-exterior)`.
   Then attack the middle maxima in both positional families. Prefer genuine sharpenings
   or case elimination to another restatement. Inspect the actual recursive coupling and
   active rank budgets; a finite negative probe is not a universal theorem.

4. If the residual closes, assemble the uniform two-marker bound and trace its exact
   consumers back to the parent additivity obstruction. Do not claim the parent or the
   Erdős–Szekeres conjecture solved merely because a supporting two-marker theorem compiles.

## Execution, trust, and reuse

Before each lemma run `es search` and preserve its result in the result ledger/review notes.
Prefer `es proof capture/check/prove`, `es node finish --policy review`, and `es context`.
If the reusable finalization workflow does not fit a newly introduced node, document the
equivalent targeted check, full extraction, statement integrity, layer check and axiom audit
receipts before accepting or committing it. Use only the standard permitted axioms; no
new axioms, `sorry`, or `native_decide` outside the allowed blueprint mechanism. A closed
accepted theorem must be sorry-free. Generated certificate modules remain generator-owned.

Every potentially minute-long command goes through `es job run` with purpose, node, cap,
and declared outputs under runs/data. Builds use `es build`/`es check`. A normal full
extraction reserves 28G alongside the 2G host in the shared 30G budget. Do not reserve a
small enclosing job and then request a larger nested build. Inspect terminal receipts and
outputs, including failures; follow queued jobs with bounded waits rather than finishing
the goal at submission. Unknown execution requires reconciliation, never blind replay.

Before new Python/workflow glue: `es lib search`, `es lib show`, then source inspection if
the catalog has no fitting contract. Reuse the registered recursive evaluator and probe
run/replay contracts with explicit semantics. Keep mathematical candidates separate from
execution, budgets, artifact handling and reporting. Keep a small code inventory recording
what was reused, introduced or deferred; Astra reviews run scripts, changed tracked scripts
and inline job commands after research. No speculative library generalization is required.

Log substantive decisions using `es log --node ...`. Maintain `checkpoint.md` and
`verified-results.json` with full declaration names, exact removed cases, statement scope,
search receipts, check/extract/audit receipts, commits, failures and still-open cases.
Stage only reviewed files explicitly. Direct Git commands need
`git -c gc.auto=0 -c maintenance.auto=false --git-dir=.git-data --work-tree=.`.

## Deadlines, monitoring, and final handoff

This is one twelve-hour allocation. Native host timing is frozen at pickup; use the
remaining time for substantive research, validation and a clear handoff. Prepare final
validation before admission closes. Preserve the host's existing bounded finalization
policy: one final report/finalization turn if necessary, hard stop thirty minutes after
the research deadline. Never reset quota, user pause, cancellation, uncertain submission,
or a frozen deadline. The configured one capacity-only retry preserves the same run.

The worker observes routine jobs with ordinary code; Astra does not poll compiler repair.
Only a substantive blocker or infrastructure failure should need coordinator intervention.
The exact coordinator callback must have been verified before this host is admitted.

At research end: inspect all pending jobs, finish authorized validation within the existing
policy, release every claim accurately (parent partial unless actually proved), preserve
an honest final frontier and local status, and write `REPORT.sol.md`. Include accepted
results with actual receipts, mathematical obstruction removed, remaining hypotheses/cases,
commits, failed attempts, direct jobs, usage window/source, late finalization usage and code
inventory. Run `es run review runs/sol-12h-20260916/host --artifact-root runs/sol-12h-20260916`
when the host state is available. The final authoritative bundle and Astra review occur
after terminal host state. Do not spend a new research window reviewing yourself as Astra.

Savings claims remain observational: include setup, failed work, research, recovery,
monitoring, final review, maintenance, and late usage without counting reasoning twice.
