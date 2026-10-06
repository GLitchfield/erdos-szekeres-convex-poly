# Certified counterexample to remaining-budget-loss selection

2026-10-02 18:03 UTC, codex:01a0fc94-0467-7b90-823c-bce1e6fe6128.
Node ctx_k6_remaining_budget_cost_counterexample, independent branch
node/CtxK6RemainingBudgetCostCounterexample, basee3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8.
Registration20261002-135149-8bc692, unchanged locked type7be8179010ca9dad.
Pinned commitc0094d67eaf0247835dcb62b4720328896c815ba, commit job
20261002-140323-8af144 DONE. Claim released CLOSED after separate review
window-afcf9684c3d84ca5; see BUDGET-LOSS.CODE-REVIEW.md.

The literal context is SSS1L3L2LS at(5,5,6), maxima111. Upper3 peels at the
middle child1 and last child6 both have leaf bound2. The end remainder[0,1,2]
lower2 preserves every ordered cup/cap limit and has bound4. The middle
remainder[0,2,6] lower2 loses cup(0,0) but has bound>=6. Every legal side/coupling
at child6 gives sum<=7. Thus choosing a child by minimum pointwise remaining
budget loss can prefer an inferior end child, even with identical leaf gain.
This refutes that precise surrogate, not every possible undefined cost notion.

The37-line proof kernel-checks limits, leaf values, the single-run end remainder
and all8 end-child choices. For the middle remainder, cut child6 lower3: leaf4
plus rho. Rho keeps[0,2] upper2 and has bound>=2 from its child0 lower1 cut
worth1+1. Two ctx_bound_cut_le applications give middle remainder>=6. No full
parent or middle maximum is evaluated. The body passed its first complete check,
with no compiler/registration failure or restatement.

Original-source check20261002-135814-128f53 CLOSED, compiler3.401433s,
guarded outer42.3s/2351MiB under4G. Inner peak0 is unavailable nested measurement.
Receipt2dd0090dbe57f57267bf19742af8237b234cfe0dc227eb628513887a1a909677;
original-check-full.json and final-verification.json are fully parsed. No sorry,
standard axioms, matching type/lock, no blocked/uncovered dependencies,
byte-exact assembly, all378 inherited lock objects unchanged/exactly one new,
audit/layers pass. Source SHAa879205f5ff821c73f18cb86bb73c31c160acdfaa02f9b7461f2e1ef40584f09.
Current fixtureb20fee4385c4593b4d42cbb168337b8d72b5548b4ae916e325ea41316e2b44be;
initial capture5818a63cbfd14ef2866e4caf6c724922022a6c809480d45b05540ed1374cc305
was superseded after adding only heartbeat/recursion metadata, before proof assembly.

Searches minimum remaining limit loss selection /k6 residual cut tree bound six
remaining endpoint budgets found no duplicate. Reused the existing cut-dominance
theorem, the accepted k6 lower-bound technique and shared fixture/assembly,
artifact and guarded job APIs. No new Python mathematics or workflow script.

The same literal context is separately certified WellFormed/Satisfies under
constant-right coloring by commit8e2f72ce9b0ae129609f051661313b7bee767dcf,
receipt37353e1f739a6742ee72aa641913fdcf267f1bdadc569e67d87be88a4f097f51.
This is logical composition of independent receipts; no compiled conjunction
or actual external-history realization is asserted here. Exact parent bound8,
middle remainder6 and unique middle attainer remain diagnostic. The certified
middle lower bound and end upper bound suffice for the cost refutation.

The explanation is residual run geometry. End peeling retains a contiguous early
run with cup2/cap4 and capacity4. Middle peeling separates early components while
retaining spanning cup2, permitting their joint capacity2 plus last capacity4.
Pointwise budget loss does not measure that change. Diagnostic profiles also
show zero longest-extension/join changes for the end cut: the new level1 marker
lies beyond older right markers and cannot thread them. These walk-count
equalities are outside the locked statement. Selected evidence in
BUDGET-LOSS.selected-diagnostic.json, source job20261002-093908-bcbe7b.

There is no general feasible singleton-selection proof idea yet. Raw full PEEL
is certified false; its witness is separately certified infeasible. This result
does not commission a sibling-penalty narrowing. Preserve all ignored artifacts
with the pinned branch; independent coordinator review is pending. Native goal
remains active until its fixed deadline.
