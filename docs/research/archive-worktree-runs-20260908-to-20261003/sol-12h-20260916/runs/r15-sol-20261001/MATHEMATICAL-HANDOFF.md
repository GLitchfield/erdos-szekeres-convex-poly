# R15 mathematical handoff — consolidated 2026-10-01 12:13Z

**Done(narrowing)=YES. Done(full)=NO. Stuck(full): the paired recursive lower comparison after a whole maximal-segment flip is unproved.** This is the same single authorized R15, Sol at xhigh without delegation. Research admission ends 2026-10-01T12:43:31.668169Z; finalization deadline13:13:31.668169Z. The native goal must not be marked achieved.

The 26 useful corrected CLOSED results, exact types, separate node branches/commits, check jobs, receipt/file hashes, canonical checked source archives and import/declaration dependency DAG are in [ACCEPTED-RESULTS.md](ACCEPTED-RESULTS.md) and [ACCEPTED-RESULTS.json](ACCEPTED-RESULTS.json). Every entry is sorry-free with only propext, Classical.choice and Quot.sound, a locked type and no proof blockers. Checks are targeted; conditional entry2 has incremental=false, the other25 have incremental=true. The original unused singleton conditional is excluded from this corrected count.

## Exact open obligation

For WellFormed σ with at least two physical child runs, a nonempty proper keep list of source children whose canonical keep and complement are both noninterval, and legal d/orientation o, prove there are child-order lists L,S,R with σ.childPositions=L++S++R, nonempty homogeneous S, opposite membership at both adjacent ends when present, and legal e/orientation b, such that

    value(keep,d,o) <= value(canonical(keep XOR S),e,b).

Here value(K,e,false) is the lower-e part bound plus complementary upper-(k-1-e) part bound; true reverses the axes. ANY segment length, end or interior, is allowed. Both the coupling and orientation may change. Exact type/signature: [SEGMENT-FLIP.signature.txt](SEGMENT-FLIP.signature.txt), hash dbd0e335b115583d.

Latest partial source/commit: node/CtxBoundMaximalSegmentFlipExchange,
e03d9bc70c29527dec456d5d3621ad5af95f37d1; archive
[SEGMENT-FLIP.k3-narrowed-candidate-v1.txt](SEGMENT-FLIP.k3-narrowed-candidate-v1.txt),
SHA26a72246d25c7c6e96675f11c52170add5b02469fc5779b0f6e7e3821911f66c.
Its single remaining sorry is the positive original-value branch with k>=4.
Zero values are discharged by accepted1; k=3 positive values contradict accepted8.
Check20261001-031633-4d778b, original artifact
7b21cd16a1be7d33c7a12bb15ce137a58ff076daec0e1f643b7a8f07f0ac7f70,
fully reread213050B: locked type, sorryAx, targeted=true/incremental=false,
build3.840707302093506s; enclosing189.1s2599MiB. This is OPEN, with no full theorem credit.
The reserialized [CHECK.flip-k3-v1.full.json](CHECK.flip-k3-v1.full.json)
FILE-SHAd003a0e354973f3484c3f8f473abba23954d115fdcef570c327ea1dc8f755891
is distinct from the original artifact ID.

Original multi_run composition remains OPEN through FLIP:
commit1e9dcc8d96960b209f57e0575e95dc596c8f160a, typeb9572285e41a575b,
check20260930-230449-e505e1, [CHECK.composition.json](CHECK.composition.json)
FILE-SHA14b7fd09396533d9d53fc1e5d749756dbb00fedb62d3d80e9e41802a77f17f8a.
It preserves its original statement and explicitly depends on corrected conditional2 and open FLIP.

## Accepted route and latest reusable reductions

Conditional2, commit2051ea71a65e8c8486d23b351dbd021929275044, proves multi_run from positive ANY-length FLIP by strong induction on maximal membership-segment count. A whole end/interior flip removes one/two transitions; at most three segments leaves an interval side, handled by the checked interval-cut bound. FLIP is an explicit hypothesis, without importing the open FLIP theorem. The coordinator's01:15 correction from singleton to arbitrary-length segments is essential.

Accepted3 characterizes a multi-run upper bound by ALL proper interval cuts, both orientations and every legal coupling. Accepted21 supplies attainment by such a cut whenever the full bound is positive. Neither provides paired uncrossing after arbitrary source-membership flips.

Accepted5/6 handle saturated histories at k-2; accepted9/10/11 handle near-saturation at k-3; accepted12 bounds both κ4 proper partition values by three; accepted14/18/19 expose bracketing and outer-marker annihilation. Their exact raw-context hypotheses are in the registry/source, including actual omitted-child witnesses where required.

Latest24: positive proper part implies every indexed source maximum on its selected axis is <=k-3. It requires positive actual external labels, k>=3 and an actual omitted child; arbitrary keep/new maximum, no global/WF/run/coupling premise. Commitfc33578a09d63832a3d1d6a00345d2b910eb561a, check073315-7ecc5b. Full account [POSITIVE-PART-UNSATURATED.HANDOFF.md](POSITIVE-PART-UNSATURATED.HANDOFF.md).

Latest25: if one indexed old maximum and the fresh maximum are both >=k-3, ANY-axis proper part has every fuel/full bound<=2. Same-axis uses10; opposite-axis has actual fresh level1 plus shifted old near-saturation and uses11. No k lower bound, WF/run/global/coupling premise. Commitafb36431268c2e326f2f443846205346b3c0f85e, check074813-96b1dc, typea7a22e44827d4efb. [OLD-FRESH-TWO.HANDOFF.md](OLD-FRESH-TWO.HANDOFF.md).

Latest26: κ4 legal proper paired value>2, in either orientation, forces EVERY declared source maximum=1, assuming positive actual labels and positive declared source maxima. For each indexed N,25 bounds each proper component<=2; sum>2 forces both positive, then24 on N's axis forces maximum<=1. Empty source history gives a vacuous conclusion. No converse, finite history limit or flip witness. Commit4e59d48e8654f46ae5b30cbf087f43d652096297, check075853-7af218, typeb8c097958adbdaaa. [K4-CRITICAL-UNIT.HANDOFF.md](K4-CRITICAL-UNIT.HANDOFF.md).

Unit maximum values do not mean a uniform one-level root: arbitrarily many indexed levels and mixed axes remain. WellFormed bounds a marker's level index by history length, while its declared maximum value is bounded by k-2. Closed20 already has four mixed-axis levels with unit maxima atκ4. R14/R16 one-level selectors need a separately proved bridge before applying here.

Accepted10's normalization (reused by25) truncates maxima and clamps a global while proving the word unchanged. Older external letters beyond the retained indexed history therefore remain physical run barriers. Do not erase or contract them to a uniform root without a comparison theorem, even when their old maximum values were one.

For integration, use the union of declared and source-import edges. In particular3 must precede generated witness4 and singleton counter22 even though their declared-node tags are empty; helper-only direct dependency lists do not eliminate imported dependencies. The latest chain is9->10, (10,11)->25,5->24,(24,25)->26. Closed commits are isolated from main, with exact overlays excluded and removed. No merge/push occurred.

## Failed mathematical shortcuts, with evidence

- Singleton-only FLIP is structurally false when all maximal membership segments have length>1. The stronger κ4 counter22 has WF globals4/4/k4, word1U,S,S,S,S,1U,S,S/max1 and keep[1,2,6]. Original value3; the only singleton maximal-segment flips (children6/7) have value<=2 for every legal coupling/orientation. It does not refute ANY-length FLIP. Dedicated [K4-SINGLETON-COUNTER.HANDOFF.md](K4-SINGLETON-COUNTER.HANDOFF.md).
- End-only whole-segment choice fails in kernel-certified16 (globals4/3/k4, oldvalue2, every end flip<=1). Interior segments must remain available. [CHECK.k4-end-counter-v1.full.json](CHECK.k4-end-counter-v1.full.json).
- Positive point capacities do not imply a positive recursive full bound (closed13). Even ALL unit sibling maxima and ALL surviving cup/cap capacities1 can have bound0 (closed20). This blocks a converse to26 and pointwise positivity shortcuts.
- A clear fresh saturated SINGLETON has exact bound1 under15's hypotheses. Dropping singleton fails in17, despite source opposite point capacities positive. Fresh-unit clear-history positivity also fails diagnostically: fresh-unit-clear-timing.json has11 zero-full-bound misses among47 point-positive parts/124 tests. The first run's occupancy assertion failed before evaluation; correction stayed within the intended occupied-level scope.
- Adding a fresh unit interior child can destroy positive full bound: probe_k4_interior_addition.py, job051856-340439,44 tests/two losses. This source already has selected-axis history; it is distinct from the clear-axis probe.
- Adding an inactive child can lower full bound1->0 while old actual-child capacities remain unchanged (closed23). Exact [INACTIVE-INSERTION.HANDOFF.md](INACTIVE-INSERTION.HANDOFF.md). It does NOT refute the compiled zero-capacity marker-inclusion theorem: the precise target-child/marker inclusion premises differ; in the reverse labeling observed0<=1 is consistent.
- Raw near-saturated source bound<=2 is false: κ4 source569 has bound3, diagnostic k4-near-source-raw-bound.json/job063020-bd479d. The proper omitted-child condition in10/25 is essential.
- Fixed-coordinate compensation fails at κ6 (11/243 diagnostic cases); retain paired sum, free orientation and legal reoptimized coupling. Fixed-leaf lifting fails in R14's read-only journal example. Neither a same-leaf lift nor point-capacity monotonicity is a substitute for a whole-pair theorem.
- No counterexample to the corrected ANY-length full FLIP was found. Finite nonfailure is not a proof.

## Completed finite coverage and explicit open coverage

All evaluators are finite diagnostics, without a C-to-Lean equivalence theorem. Shared compiled evaluator semantics retain zero-capacity children, all declared indexed levels (including unused), default sides, copied globals and truncated Nat subtraction. The fresh maximum is prepended and old labels shift; part globals do NOT become d+1/k-d. Signed64 overflow raises. Cache saturation is unmeasured; no unsupported cache/worker cause is inferred.

- Broad any-length profile:148 rows515 canonical classes, zero270/positive245,1021 working segments; guarded20260930-220342-09ec9e. Frozen falsifier.segment-v4.py SHAb761f2c3747c7b0301969fec3106e415164d07e095cf6c0d131d3c3177488d2f.
- κ4 five-child fixed576-row family:2880 classes,621 positive; end-only missed one. Finite source family only.
- κ4 six-child fixed576-row family:9216 classes,1827 positive/7389 zero, all passed. Job055028-bb1ff0; k4-six-all-sample.json SHA
bc08bed66b4cc9618106da7349d48b0bd2d83c64433605a05bf9935577214eaa.
- Selected-old-coupling κ4 six replay:1827 positive/8063 flips,6940 working, zero misses; job062335-b50373, fixed-k4-six-sample.json SHA
469a3342a263ff7b905766eabc20945edfc01b8361a7291008e07e5e73887993.
It tests the saved winning old coupling, not every old coupling.
- κ7 six-child fixed24-row sample:384 classes,368 positive16 zero, all passed; job060912-b89a0a DONE3056.7s400MiB. k7-six-all-24-sample.json SHA
c6a9f87df0bf690c39f5da5650944e0873464a023ef3b10b9c82be42e0e9e811.
Full192-row κ7 family was NEVER launched; higher κ/history/child coverage remains open.
- κ4 seven-child fixed16-row stress:672 classes640 positive32 zero, all passed. Four complete guarded shards071623-defe3c/e69a5a/d56a2f/30d0e6, longest379.6s; review preserved scope. Combined k4-seven-stress.combined.json SHA
6bde9363f7711b93783a06f39f1f09b75ce9186a0c0dce25ea68a185e93adb71.
End-only missed18, singleton-only8, interior-only0 IN THIS SAMPLE. No universal interior selector.
- Structural audits072437-23a344 (seven combined) and070348-2a00b7/072011-6cf497 (κ7 archive-path replay) check complete fixed coverage, maximal segments, XOR/legal coupling and reported arithmetic only. Right values may be sufficient threshold witnesses, not exact maxima. No independent recursive evaluator or kernel proof is added.

## Compiler/infrastructure and code-review record

22's monolithic ordinary-decide candidate failed967.1s with24GiB/two OOM kills, job063529-35124b; no proof credit. Reused the existing build_dag/project/lifetime emitter, producing996 facts/914 contexts/maxlive96 and removing64 IO pairs. Clean22 checked182.2s3372MiB; exact C-selected facts are verified by Lean. Accepted eight-child4 similarly uses the existing projected/lifetime DAG and a cleaned Std-only source; failed earlier variants remain historical artifacts without credit.

24's first8G check072759-e0d71c refused a nested20G stage before Lean (build0/seconds0). Unchanged source succeeded under24G job073315-7ecc5b. No memory config change. Registration25/26 reviewed at5-minute checkpoints and completed without narrowing/kill. 26's check waited for terminal R16 compiler then fresh full running/starting scans. A truncated admission scan was fetched after submission instead of before once; immediate full audit showed no compiler and the defect was logged.

Latest static receipt audit080318-855ec6 completed26/26,0.2s29MiB, algorithm0.09270401600224432s; [AUDIT.accepted-receipts.full.json](AUDIT.accepted-receipts.full.json) SHA
0be532fcafd5777cad158de5493ba92d90f09a3d935df1e09a743942d6c4cd6b.
Every accepted archive also matches its committed source byte-for-byte. This is static archived metadata/identity verification, not recompilation/new theorem credit. Failed pilot080222-f6cee4 omitted-wrapper schema error/output missing, repaired pilot080307-2e3e29 succeeded; exact sources preserved.

Separate Sol self-reviews: CODE-REVIEW.1111.md,1121.md,1142.md,1202.md (including schema repair), and CODE-REVIEW.final.md. No Astra/delegation claim. Reused shared evaluator and existing DAG/projection/emitter algorithms. Fixed mathematical wrappers and fixed-run receipt inventory remain local; stable import/serialization/lifetime contracts and fixtures are needed before promotion, with no promotion solely to grow the catalog. Host review claim/job/usage arrays are unavailable under its different researcher identity; explicit own statuses/receipts are authoritative. No all-in savings claim. FINAL-RELEASE-AUDIT.json independently confirms all26closed releases and fullFLIPpartial.

Isolated26-branch es status reported6 extraction/index problems at12:07; exact causes uninspected. After returning the unchanged FLIP branch, current index is explicitly stale: locked FLIP and inherited R14 conditional are unindexed. Full project extraction/merge/build was not authorized and is not claimed green. No new work is being chosen, no R14 index repair. An older FLIP incremental attempt was refused by an unrelated broad closure; it remains targeted-only. Direct proof receipts establish listed exact compiled nodes, not the whole checkout. FACTUAL-HANDOFF.final-maintenance.json preserves available window usage; its zero explicitly linked resource jobs excludes unlinked work rather than proving absence.

## Safest next action and handoff state

Use26 to focus the κ4 value-three case on unit source maxima, while retaining arbitrary source-marker order, unused indexed levels, copied globals and inactive children. Derive a FULL proper-part bound-two characterization and paired whole-segment lower comparison; unit point capacities/old history alone are insufficient. κ4 positive values1/2 and κ>=5 also remain open. Coupling/orientation may change, and both end and interior segments of any length must remain admissible.

Terminal review clarifies an unresolved support route: extracting a bound-two recursive witness and flipping another membership segment would still require a valid recursive tree/whole-run lift. Arbitrary inactive-child addition is false23 and pointwise positivity is insufficient13/20; no support selector or contraction is proved. Boundary lemma18 annihilates a further proper recursive part and must not be used as a direct zero statement for its current raw source context or singleton. This is a diagnosis for a later authorized attempt, not a new theorem or finite evaluation.

Before another authorized attempt: es status, relevant node-filtered journal including this handoff, es ready/claim, exact dependency overlays from the registry, and fresh complete compiler scans. Do not start another trial or extend R15's deadline. Full FLIP claim released partial12:16 after guarded branch-return081553-05e0e0 and linking this handoff; final HEAD e03d9bc70c29527dec456d5d3621ad5af95f37d1 is clean. The parent was already released partial. All26 useful closed claims are released closed and no own claim remains; all own computations/checks/audits terminal and inspected. Host observers/R16 jobs are outside R15 follow-up.

Earlier chronological reports are preserved as PROGRESS.pre-consolidation-1213.md, REPORT.sol.pre-consolidation-1213.md and MATHEMATICAL-HANDOFF.pre-consolidation-1213.md. They are historical; this handoff and the exact registry supersede pending statuses and receipt-ID/file-hash ambiguities there.

Deadline outcome: the external host paused the native goal at the fixed research deadline, confirmed by get_goal at2026-10-01 12:43:39 UTC (FINAL-NATIVE-GOAL.json). R15 is incomplete; no further research was admitted. Post-deadline separate full running/starting/queued scans confirm no own job pending (FINAL-JOB-INVENTORY.json); foreign host/R16 work remains outside this handoff. Worktree clean, all26 useful claims closed/released and fullFLIP/parent partial. Finalization only.

Final reporting usage window-cbafaca212224e2b ended accepted0, with no theorem added during finalization. FACTUAL-HANDOFF.deadline.json and USAGE.deadline-sync.json preserve the available snapshot and its observational target overrun; late reporting/resource linkage limits remain explicit in REPORT.sol.md. Goal status paused is host-controlled, not a claim of mathematical completion.
