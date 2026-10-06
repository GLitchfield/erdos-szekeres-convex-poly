# Sol/xhigh research trial — September 18, 2026

The user authorizes this one twelve-hour trial, reviewed local commits, and final Astra
review. Sol (`gpt-5.6-sol`, `xhigh`) performs mathematics, Lean proofs, compiler repair,
and routine job follow-up. Astra coordinates mathematical scope and reviews final proof
receipts and code. Follow AGENTS.md. Do not start a second trial or publish remotely.

## Absolute paths and preserved baseline

- Research checkout: `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`
- Research artifacts: `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916/runs/sol-12h-20260918`
- This brief: `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916/runs/sol-12h-20260918/RESEARCH-BRIEF.md`
- Native host: `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916/runs/sol-12h-20260918/host`
- Sol report: `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916/runs/sol-12h-20260918/REPORT.sol.md`
- Astra setup, review and final reports: `/home/gavin/git/erdos-szekeres-convex-poly/runs/sol-12h-20260918`
- Reviewed clean baseline: `70c20c037f9ec031346e81508a0eb6f5ef223fc8`.
- Primary harness: `harness/automation-20260912`, `36a960df`; primary lacks some latest mathematics.

Reuse this checkout and its existing compiled files. Preserve prior commits and receipts.
Do not alter the primary checkout's unrelated `ESBlueprint.lean` and
`harness/dataset/ctx_end_cut_normal_form/`. No mathematical changes occurred during setup.
Baseline status is 283 closed, 12 open, one refuted, zero stale entries/problems, eleven ready
nodes. Refresh `es status` and `es ready`; if stale, perform guarded extraction before choosing.
Claim `ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end` before research. Use fresh
`node/<Name>` branches for individual new nodes; claim each before proof work. New statements
use `es node add`, revisions use `es node restate`; never hand-edit statement text.

## Required handoff and authoritative evidence

Read the parent checkout's `runs/sol-12h-20260916/REPORT.md`, `MATHEMATICAL-REVIEW.md`,
`LIBRARY-REVIEW.md`, and `runs/storage-optimization-20260917/REPORT.md` and `DEPLOYMENT.md`.
Read `docs/automation-implementation.md`, `docs/artifact-cache.md`, and this checkout's
`runs/sol-12h-20260916/{REPORT.sol.md,mathematical-analysis.md,checkpoint.md,verified-results.json}`.
The checkpoint contains historical intermediate obstructions that later closed. Astra's
review corrects the original narrative: finite probes did not Lean-refute a theorem; the
first full extraction timed out and was not established to be OOM; the retired stale node
originated within that trial. Compiled declarations and actual proof receipts govern.
`RESIDUAL-PREFLIGHT.sol.md` is read-only setup assistance, not an additional accepted theorem.

## Target and already solved cases

Continue toward `ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end`.
Primary success is an audited compiling Lean theorem that eliminates a documented remaining
case. Prefer a genuine stronger estimate to more classifications or theorem count.

The prior trial closed **all actual two-marker internal-complement cuts at k=6**, including
the former younger-exterior `11+2` obstruction, now `10+2<=12`. It assembled
`ctx_two_marker_internal_complement_cut_six_bound` and
`ctx_two_marker_opposite_kept_block_cut_six_bound`. Do not repeat those proofs as research.

The chosen-kept extreme has `k=6`, `m=4`, and, under legal positive coupling `m+n=k-1`,
`n=1`. Large old chosen maxima, low-only/high-only support, and canonical pair overlap at
most one are already handled. Overlap exactly two is excluded geometrically. The remaining
mixed low/high companion support has overlap at least three.

## Exact interface and mathematical priorities

Start with these source declarations and their proofs:

- `ESBlueprint/B/CtxExtremeCutSixPairIntersectionThreeResidualClassification.lean`
- `ESBlueprint/B/CtxActualMarkerOppositeRankIntervalEndpointExclusion.lean`
- `ESBlueprint/B/CtxTwoActualMarkerCompanionMaximumBound.lean`

Write down the actual context before proposing a lemma:

`rest := σ.childPositions.filter (· ∉ keep)`;
`A := σ.part keep s m`; `B := σ.part rest t n`, with `s ≠ t`.

The classifier takes positive external labels, levels `N < M`, actual chosen marker witnesses
`x,y`, chosen/opposite globals at most five, exactly the two chosen positions, a kept child
`p ∈ A.childPositions`, `m+2=σ.k`, `σ.k=6`, and a companion child `high` with chosen point
capacity at least three. Its conclusion is the independent-fuel and full cut bound twelve,
or canonical low/high ordered-rank-pair intersection cardinality at least three. **It does
not itself assume legal positive coupling or n=1.** Add and derive the relevant legal-cut
facts explicitly at the consumer; do not attribute missing premises to the classifier.

Retain the facts used in its proof: `p ∈ B.extPositions 1`, `B.sideAt 1=t`,
`1 ∈ B.levels`, `B.maximumAt 1=n` from `part_maximumAt_one`, `B.k=σ.k`, and transported
chosen markers at `N+1,M+1`. In the legal extreme derive `n=1` before abstracting B.
The synthetic marker may have multiple physical positions: preserve all actual keep/cut
transport facts. Do not quietly replace its external-position set by a singleton.

Canonical groups split B's children by chosen point capacity `<=2` versus `>2`. Pruning
replaces unkept children by a positive unindexed barrier. Each group's pair set is the union
over active children of nondecreasing pairs from its opposite rank interval. Preserve the
original-history/pruning transport, activity, unused indexed levels, arbitrary word length,
and any permitted inactive children. No finite size or extra well-formedness assumptions.

The endpoint theorem applies to an actual marker on the rank axis: every child strictly
to its right has available ranks at least two; every child to its left has ranks r with
`r+2<=global`. It does not use the maximum-one fact and does not prove the companion bound.

Ordered priorities:

1. Reconstruct the precise remaining branch and actual companion under legal cut coupling.
   Identify exactly which hypotheses each reused theorem needs. Keep independent fuels.
2. Investigate a **coupled recursion estimate** retaining the synthetic opposite level-one
   marker and maximum one. Use its endpoint losses within the low/high recursion to recover
   missing slack. Desired result: `(∀ g, boundFuel g B <= 11) ∧ B.bound <= 11`, paired with
   A's already established unit bound to obtain twelve. This direction is a conjectural
   research proposal, not an established implication.
3. Close a documented remaining case with an audited compiling theorem. If a uniform coupled
   estimate fails, log why before changing approach; select a useful precise unsolved subcase
   without dropping essential actual-companion information.
4. If successful, assemble the remaining two-marker bounds and inspect exact consumers toward
   the parent obstruction. Do not claim parent additivity or the conjecture from supporting
   bounds alone.

Known limitation: the prior bare-signature probe found value twelve after forgetting the
synthetic marker. These are diagnostic examples, not Lean-certified refutations. Even with
the actual marker, extremal diagnostic examples have group pair sizes 6+6 or 6+9. Neither
endpoint exclusion plus separate group bounds nor `bound <= 10 + intersectionCard` already
gives eleven. Avoid spending the run reproving that inadequate composition.

## Proof acceptance, reuse and resource discipline

Before every lemma run `es search` and preserve the result in the ledger/review notes.
Prefer `es proof capture/check/prove`, `es node finish --policy review`, and `es context`.
If using targeted `es check` plus full extraction, retain equivalent statement-integrity,
layer, sorry, axiom, source-hash and commit receipts. Accepted results must be sorry-free
with only permitted standard axioms. No new axiom, native_decide or unallowlisted sorry;
generated certificates remain generator-owned. Review each exact staged diff before a local
commit; preserve one node per branch and cite search evidence in review/PR descriptions.

Every command that may exceed one minute uses `es job run` with purpose, outputs under
runs/data, node and memory cap, or the existing guarded asynchronous operation. Builds use
`es build`/`es check`; never bare `lake build`. Follow jobs to terminal state with bounded
waits and inspect outputs. Unknown execution is not permission to replay.

Keep normal native-host resource configuration: host 2G, shared job budget 30G, usual
targeted-check/build cap 20G, full extraction 28G. Match each enclosing reservation to every
nested stage. Generic `es build` has a configured final stage of 30G and requires a 30G
wrapper; a 20G wrapper is refused before compilation. Such a 30G job cannot coexist with
the 2G host under the shared budget. Use the appropriate targeted-check and extraction
workflows during research; do not alter caps or disable guards to force admission. Report
a genuine unavailable stage so Astra can run it after the host is terminal if required.

Keep setup-metadata cleanup and native immutable artifact-cache integration enabled.
Do not copy entire caches, share mutable build directories, delete proof bodies, or run
`lake cache clean` against the shared store. Use documented reservations/storage commands.
This checkout already has the reviewed materialized artifacts and mappings; a new checkout
would require separate restoration and physical-space verification before admission.
Measure filesystem free bytes/allocated physical blocks, not a sum of hardlinked apparent
directory sizes. Preserve disk-before.txt for final growth assessment.

Before Python or workflow glue: `es lib search`, `es lib show` relevant APIs, then source
search if no fit. Reuse the prior reviewed
`runs/sol-12h-20260916/probe_two_marker_overlap_reused.py` and existing context-extension,
recursive-bounds and enumeration primitives where their contracts fit. Preserve explicit
semantics and original artifacts. Finite search remains diagnostic absent a Lean bridge.
Keep new candidates small and separate from execution, budgets and reporting. Record code
reuse/new code/deferred generalization; Astra reviews scripts and inline commands afterward.

## Timing, ownership and handoff

The host supplies the frozen native thread, research window and deadlines. Use its registered
ES_AGENT/ES_WINDOW_ID and record the actual CODEX_THREAD_ID; do not invent a different
identity or open an overlapping research window. Ordinary worker code monitors; routine
compiler repairs and job waits remain Sol's responsibility. The configured bounded capacity
retry preserves the same thread and deadlines. Never reset user pause, quota or uncertain
submission, and never launch a second host to recover an uncertain first one.

Log decisions with `es log --node ...` before changing the plan. Maintain checkpoint.md,
mathematical-analysis.md, verified-results.json, and code-inventory.md. The result ledger
must include full theorem name, exact hypotheses and removed case, source/type identity,
targeted/full receipts, commit, search evidence, failed attempts and remaining cases.

Consolidate at the host's frozen boundary; stop admitting research at its deadline. Preserve
the existing single bounded finalization turn and hard stop. Release all claims accurately.
Write REPORT.sol.md with outcome, exact proof receipts/commits, remaining obstruction,
failures, job state, physical disk change and library reuse. Run
`es run review runs/sol-12h-20260918/host --artifact-root runs/sol-12h-20260918` and reference
its immutable bundle. Inventory/exit success earns no theorem credit. Sync usage through
finalization; explicitly disclose active-response lag. Astra then performs final mathematical
and library review in separate windows and reports automatically on the terminal callback.
