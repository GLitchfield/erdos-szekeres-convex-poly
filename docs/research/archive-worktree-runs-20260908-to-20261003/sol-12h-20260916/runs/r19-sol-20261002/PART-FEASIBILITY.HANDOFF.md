# Arbitrary-part feasibility obstruction

2026-10-02, codex:01a0fc94-0467-7b90-823c-bce1e6fe6128,
research window-dd9b0cbfa73f418c. New branch
node/CtxSatisfiesArbitraryPartCounterexample starts independently at
e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8, branchjob20261002-172031-876925 DONE.
Previous fifteen pins and all R18 branches preserved. Registration through
es node add, job20261002-172112-317d5d, DONE89.9s/2304MiB4G, type9bd7f9a32a302abf.
Post-lock claim succeeded; it is now released CLOSED. Finset.Sort and Order.Interval.Fin imports
were added before capture096e99efbabe9380cc5959ec44cdc1842de2f893fa82aae3b2c8342ccd4c57ae.
Proof body is assembled byte-exactly from that fixture, with unchanged signature.
Corrected original check20261002-172857-7ed08e is CLOSED, compiler3.833904s,
outer41.1s/2354MiB under4G. Receipt
739ee383947782d1c2d2ebb2bb7f19e20f6f804fd1d5834ccf1a2ac4e252ce81, matching
registered type/PP/lock, standard axioms only/no sorry/blocked/uncovered,
exact fixture assembly, all378 inherited locks unchanged/one new; audit/layers
pass and status fresh/no problems. PART-FEASIBILITY.final-verification.json
contains full source/body hashes and measured enclosing peak; inner0 is unavailable.
Pinned6b5dce7e7d26dc99172f89b72e9b4bebcefd51fc, commitjob20261002-173309-4cea1f
DONE, parent exactlye3baseline, clean tree/exactly five node/import/lock/index/status
files. No further compiler check is justified. Separate self-review
window-b1703224a25d450e is complete, research window ended accepted1, and
PART-FEASIBILITY.release.json records the CLOSED release and eleven copied
evidence files. Independent coordinator review remains pending.
No merge/push/delegation.

Exact target in PART-FEASIBILITY.signature.lean.txt: parent literal(5,5,6),
SSS1L3L2LS/maxima111 is WellFormed, four-child/two-run, and Satisfies for the
constant-right Fin4/univ coloring. Coupling3 is legal. Its p0 upper3 leaf and
lower(k-1-3)=lower2 remainder are both WellFormed. Remainder children[1,2,6]
have cupLimit1,2=1, hence no coloring/ambient finite set satisfies it.
The universal remainder clause prevents a trivial cardinality-mismatch reading.

Proof idea: parent caps are bounded by4, cups by2 under constant-right coloring,
and all ordered parent cup limits are at least2/cap limits4. Sixteen finite
endpoint checks and ordinal ranks prove its Satisfies constraint. Core
WellFormed.part passes WellFormed to both legal parts. The remainder's first
two ambient vertices form a vacuous cup of cardinality2, whose sorted ranks
are0 and1. Their positions1,2 have cup limit1, contradiction. No recursive
bound evaluation is required. Prior accepted finite Satisfies and two-point
rank proof patterns can be reused without importing another independent branch.

Existing diagnostic PART-FEASIBILITY.diagnostic.json, sourcejob
20261002-093908-bcbe7b/PEEL.cost-profiles.json, records this cut leaf2/rest5/sum7
and remainder first-pair lower chain3/join4. Both pure and strong limits are1.
Those capacity and chain/join values remain diagnostic here; the receipt
certifies parent feasibility and universal remainder infeasibility. Parent actual history
and exact bound8 have separate existing receipts; this theorem does not compile
a combined history/bound conjunction or claim that the chosen cut is optimal.
The end cut is nonoptimal by the existing exact-k6 theorem.

This removes a specific proof-assumption uncertainty: Satisfies at a parent
does not automatically pass to an arbitrary formal cut, whereas the closed
actual-split transfer theorem has stronger hypotheses. Feasible singleton
attainment remains open, with no paying-child invariant. This is not a narrowed
selector or another stalled sibling-penalty trial. The raw PEEL statement remains
Lean-refuted. No independent conclusion about the happy-ending conjecture.

es status was fresh/no problems; es ready read. New searches
PART-FEASIBILITY.search.json/helper-search.json found no exact match. Catalog,
Core WellFormed.part and earlier finite proof sources were read. No new
mathematical evaluator or workflow driver is needed. Reporting-adapter stage
was separately reviewed before this trial. Latest accounted usage is
32 completed windows/1004376 outputs; completed arbitrary-part reconciliation
job20261002-174736-f47624 is DONE, zero deltas, with research49041 and
self-review4343 outputs. Review stayed below observational10000. Active final
synthesis and unassigned/unlinked work are excluded; no savings claimed.
Deadline unchanged2026-10-03T00:25:54.693298Z, consolidation23:55:54.693298Z.

First check20261002-172632-0ac8b3 failed compiler3.797609s, outer14.3s/648MiB4G,
without OOM/guard/budget failure. Final omega lacked concrete endpoints because
dsimp unfolded the local remainder alias before simp could match hposI/hposJ.
Only that final goal failed; body-v1/check-v1 preserve evidence and full compiler
log is check-20261002-172636-ctx_satisfies_arbitrary_part_counterexample.log.
The repair simplifies pair min/max first, folds gamma explicitly with change,
then rewrites endpoint equalities and the cup limit. No mathematical assumption
or statement changed, and no partial-stage theorem credit is claimed.
