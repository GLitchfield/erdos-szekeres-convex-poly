# R19 progress

Updated 2026-10-02 20:05 UTC. Agent
`codex:01a0fc94-0467-7b90-823c-bce1e6fe6128`. Fixed research deadline
2026-10-03T00:25:54.693298Z; consolidation starts2026-10-02T23:55:54.693298Z.
Only Sol/xhigh, no delegation, merge or push. Every independent node branch
starts at `e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8`; R18 branches preserved.

## Accepted mathematics

All three original priorities are achieved, with PEEL resolved by refutation.
The native goal remains active until its fixed deadline; remaining work verifies
the scope and structural explanation and improves the handoff.

* `decomposableThreshold_split_attained`: `d=a-2` is legal and attains the split
  sum for3<=a,u<=k. Pascal proves the classical regime; in the active regime its
  singleton binomial window complements the suffix. Boundaries k+2/k+3 included.
  Check20261002-083132-7de94e, receipt161f6e6f3b4a97c22b413a26cd4e35801bff88de80ac6d422ab08836262fdf70,
  commit991b783989fd7515b23409ec3202bd9b860210e3.
* `decomposableThreshold_split_le`: every legal coupling gives at most the
  parent threshold, by certified disjoint prefix/suffix allocation.
  Check20261002-084819-794720, receipt1866ab58618b533de5d93e823b22854e8155325c7c1a746878f8899f5eccc4f6,
  commite29026398ad8cafe3ce1c93dd80a85dda8978c4b.
* `ctx_bound_eq_flank_swap`: both actual flanks and physical orientations,
  arbitrary older letters. Different sides keep their maxima; equal sides keep
  M=max(m1,1+m2) via(M,M-1), with required legality. Opposite directional steps
  commute; strong join contributions become alpha+M; descendant transport and
  fuel induction give full bound equality.
  Check20261002-092340-20d151, receipt882f635458f3cf58aef80fc3acbf82181564022088875761b02342a0811a0343,
  commite05ed9a3a90443aff49d04047dda17f97ba4627b.
* `ctx_bound_singleton_attainment_counterexample`: the exact universal negation
  of full PEEL. At(4,4,5), word3U4LSS1L2USS, maxima1111, children[2,3,6,7], the
  bound is>=2 but all24 singleton-cut sums are1. The lower bound uses certified
  interval-cut dominance on[2,3]|[6,7], worth1+1; finite sums and WellFormed are
  kernel-checked. Full bound=2 is diagnostic only.
  Check20261002-101239-d357fa, receipt9159d9e9c8b436a7edd362410be34693c221562de3d85dcfca000cbb2c7ee3f5,
  commit119a082b4ee8a668e565027b226f5bc4cacddb66.
* `ctx_satisfies_pair_limits`: every ordered pair of distinct child positions
  in a satisfied coloring context has both limits>=2, without WellFormed or
  global assumptions. Ordered finite-set enumeration identifies each rank;
  apply Satisfies to the vacuous cup/cap two-point subset.
  Check20261002-105442-376a39, receipt7835038cff4025744af5b60c676263d34ca8192bea6b0505951f369c424668d4,
  commitc37f3751de15f776209110fdf31048fa3d8b2319.

* `ctx_singleton_attainment_counterexample_not_satisfiable`: the exact full-PEEL
  witness cannot satisfy any coloring context. Its first pair has cup limit1,
  whereas their ambient two-point cup requires limit>=2. This certifies the
  scope boundary between the raw-context refutation and actual coloring histories.
  Check20261002-110525-546700, receipt67023967022a9fc6d5a0e81d1747f55825db39858ae6efc200ea84f48cc5c62f,
  commit1e8e5c90b897d653c1e875ee39bee22f172ce64e.

Every accepted theorem has an original-source CLOSED check, no sorry, standard
axioms only, matching unchanged type/lock, passing changed-node audit and layers.
All378 inherited lock entries remain unchanged on each independent branch.
* `ctx_oldest_singleton_flank_normalize`: truncate a genuine singleton last
  indexed flank and replace its axis G by min(G-1,k-m). All child limits and
  fuel/full bounds are equal, for positive labels and m>=1, both orientations
  and axes. Last-level walks add one selected extension; the only new strong
  contribution is oldPure+m. Part transport preserves the invariant.
  Check20261002-112036-dd5454, receipt62f7fe5143ebd50e933b2099cff7d0dc537303c5fdb6a214da89449c0a43ab06,
  commite51c80334b2da5be84b6630d5f1491129462b742.

* `ctx_satisfies_of_limits_le`: with equal child positions, nondecreasing k
  and cup/cap endpoint limits, Satisfies transfers without WellFormed. Existing
  pos_mem_childPositions realizes min/max endpoints, so old constraints apply.
  Check20261002-113919-10c1db, receiptaa6bed352f35e52c8d15a53eaab989d9c4003ed689ada7ef2ba96cd23bab1a40,
  commita2f5f1388b4109415e8b8a703dd2a8ea30d43dc7.

* `ctx_k6_satisfied_end_cut_counterexample`: SSS1L3L2LS at(5,5,6), maxima111,
  is WellFormed and Satisfies the constant-right coloring on four children.
  An explicit cut tree certifies bound>=8; all16 global first/last cuts are
  kernel-checked<=7. End-only selection fails even under Satisfies. Exact bound8,
  the other run-end p2 and actual external-history realization remain separate.
  Check20261002-122611-18dca1, receipt37353e1f739a6742ee72aa641913fdcf267f1bdadc569e67d87be88a4f097f51,
  commit8e2f72ce9b0ae129609f051661313b7bee767dcf.

* `ctx_bound_eq_unindexed_padding`: exterior markers above indexed depth are
  invisible to every fuel/full bound, and child positions and all limits translate
  by prefix length. No WellFormed or legality assumptions. Indexed walks transport
  by a constant order embedding; recursive parts bump both depth and padding labels.
  Check20261002-130548-84659e, receipt357fd8bbee50ebc29aae9752951405f645a99922023acd2759510879e0e1ff17,
  commit940641e30236f2dbf0b0f229cacbfe05872f8f5a.

* `ctx_satisfies_of_ordinal_limits_le`: equal child counts and nondecreasing
  corresponding ordinal limits/k transfer Satisfies despite renumbered word
  positions, with no WF premise. Ambient subset ranks identify the endpoints.
  Check20261002-133225-571382, receipt098887d523a6ecee23d7a9e6b91161b641405999a7582d3d24550edeb2e264cb,
  commit3ef1651152fa03db37ef45215344ea5c986f256d.

* `ctx_k6_remaining_budget_cost_counterexample`: end upper3 preserves every
  remaining ordered limit with leaf2/rest4, while middle upper3 has leaf2,
  positive cup loss and rest>=6. Every end-child side/coupling sum<=7. Pointwise
  remaining-budget-loss minimization can prefer an inferior child; run geometry
  changes recursive capacity even when leaf gain is identical.
  Check20261002-135814-128f53, receipt2dd0090dbe57f57267bf19742af8237b234cfe0dc227eb628513887a1a909677,
  commitc0094d67eaf0247835dcb62b4720328896c815ba.

* `ctx_k6_unique_middle_singleton_attainment`: same literal has full bound8,
  middle upper3 attains as2+6, every other child has sum<=7 on either side/all
  couplings, including p2. Closed all-cut upper plus complement symmetry and
  explicit lower tree explain the two residual unit runs plus final capacity4.
  Side/coupling uniqueness and sharp actual cardinality8 are outside scope.
  Check20261002-145508-8b2f02, receiptf2d86d2b78a2888f86ed602b7adc5c32e04d850e5616102b720b5348c4a89c38,
  commit1cd0281b18dddb1177d47d876c1e6b87f15fc741.

All thirteen accepted claims are released CLOSED. Per-node *.HANDOFF.md files are authoritative
for exact scope, searches, compiler failures, proof receipts and review evidence.

## Current verification

Actual-history node ctx_k6_actual_history_witness is registered and claimed on
node/CtxK6ActualHistoryWitness, independent base e3c87197. Registration
20261002-152751-e1af40 passed103.6s/2305MiB, locked type80c84048681897f7,
fixture5012c7d1eb106f951d85adba4ef2ed8380de541e8558a31d0803d9b0d155ff0e.
The explicit seven-vertex tree has singleton ancestors at positions4,5,3,
actual sibling maxima1 and root avoidance. Finite crossing/profile certificates
plus three applications of closed deep-below Satisfies transfer are the proof
idea. Pilot20261002-153422-dc918a failed before mathematical evaluation because
the fixture body omitted leading by; recorded before repair. Repaired finite
pilot20261002-153500-86fdd9 failed Decidable synthesis. Further diagnostics
isolated combined instance size166 above default128; local512 removes it.
Direct implication evaluation then hit measured4G OOM in20261002-154202-52abea.
Cardinality-first disjunction checks avoid needless evaluations on small sets
without dropping coverage. Optimized pilot20261002-154436-ae1185 passed,
compiler4.582335s/outer49.1s/2355MiB. Crossing351ms, root-profile763ms.
Original checks154618-34ea0c and154722-fecddc refused before compiler (nested
cap and occupied cache). Isolatedv1 failed on root rewrite, nonreducing positionsOf
and unmatched sibling maximum; sorted ordinal interpretation fixes them.
Corrected isolated op-3ab73e56b0e14388/job20261002-155957-e8611a accepted full
proof9.095906s/2100MiB, matching type/standard axioms. Final source removes
four stdout blocks; original check20261002-160456-155bf5 is pending4G/review5min,
replacing an oversized unstarted20G reservation without dropping coverage.
No original CLOSED receipt or pinned history theorem yet. Failed bodies/checks and corrected diagnoses
are recorded in the shared journal. Actual child4 does not establish sharp8.

Exterior-padding verification is complete, with separate review
window-061a596dfee14451. UNINDEXED-PADDING.HANDOFF.md records the exact raw-context
scope, failures and receipt. Combining it with oldest-flank normalization erases
the retained raw prefix3U4L from the PEEL witness to SS1L2USS at(3,3,5), maxima11;
this is a logical composition, not a separately compiled corollary. Existing
Satisfies transport requires identical child positions. The next precise
obligation was ordinal child-limit transport across renumbered positions; it is
now accepted. Research window-001510fde88a48ee and separate review
window-afe2dfc298944d7d are complete. RANK-TRANSPORT.HANDOFF.md records the exact
scope, receipt and launcher recovery. One sandbox async check lost its runner
and produced no compiler receipt; exact host observation/reconciliation marked
only that job FAILED without killing a process or changing any foreign job.
Worker-backed synchronous check passed; use that path here going forward.

Budget-loss verification is accepted, with37-line proof passing its first check,
compiler3.401433s/outer42.3s/2351MiB under4G. Separate review
window-afcf9684c3d84ca5 is complete. BUDGET-LOSS.HANDOFF.md states exact scope,
receipt and explanation. Exact parent8, exact middle remainder6 and uniqueness
of the middle child are now accepted in the separate exact-k6 node; there is no general feasible-selection
proof idea, because pointwise budget loss misses residual run geometry/capacity.

Next verification targets those exact k6 facts. Reuse the closed interval-cut
upper certificate and existing fuel stability. There are72 upper-cut cases and
24 nonmiddle singleton cases. First time two representative three-child kernel
evaluations, then estimate the full pass before launch. Node ctx_k6_unique_middle_singleton_attainment is registered/claimed on
node/CtxK6UniqueMiddleSingletonAttainment, type537308258d6e92aa, fixture
71156669dc05ec501c3729a2c1a04fb1dd1b13e16a12810c2d57e575fee67bfb.
Pilot20261002-143028-dc4d1e failed on IO annotation; repaired pilot
20261002-143142-f8a97b completed, middle remainder6 in66.558s and first
remainder5 in37.055s, outer143.6s/10594MiB under20G. Pilot sorry gives no
theorem credit. Structural checks20261002-143522-92993f and redundant
20261002-143648-e284fe passed with local sorry certificates; parser/submission
error was recorded before retry. Full instrumented proof20261002-143754-a63746
completed CLOSED, compiler922.374s, outer960.2s/14987MiB under20G. Receipt
e0e76c9ea74ddab9d2e0193ebf069a1468b8e131ad7f2733b41db17509faa0e6,
no sorry/extra axiom, matching lock/type. It certifies parent8, middle2+6
attainment and all other child cuts<=7. Temporary FS writes were removed.
Original-source check20261002-145508-8b2f02 passed CLOSED1138.081594s,
outer1185.6s/15121MiB under20G, receiptf2d86d2b78a2888f86ed602b7adc5c32e04d850e5616102b720b5348c4a89c38.
No sorry/extra axiom/blocked/uncovered, unchanged type/pp, byte-exact source,
all378 inherited locks unchanged/one new, audit/layers pass. Pinned
1cd0281b18dddb1177d47d876c1e6b87f15fc741, guarded commit20261002-151648-df2ac7 DONE.
Claim released CLOSED. Research window-e77d2d7f9d0d4354 ended accepted1;
separate self-review window-ad0ba0b085064f6f ended accepted0. Exact HANDOFF/
CODE-REVIEW carry scope and failures; all owned jobs terminal. Complementary
cuts reduce numerical repetitions to56, covering72 upper and24 nonmiddle cases.
No singleton-penalty narrowing or duplicate evaluator is commissioned.

Actual-history diagnostic20261002-144048-b98707 checks one explicit
seven-vertex tree with external levels at positions3/4/5 equal1/3/2 and
constant-right core[0,1,2,6]. All six explicit deep-below splits are valid,
full maxima(cap,cup,strong)=(4,4,5), so root avoids5/5/6.
K6-HISTORY.probe.json uses shared classifiers; no Lean credit yet. V2
20261002-145007-c722e6 additionally verifies proper nonempty partitions and
three shared root parts yielding the literal word/maxima. V1 artifacts remain.
Actual child cardinality4 does not prove capacity8 attainable cardinality.
Interleaving is allowed by HasDeepBelowSplit. Certifying this candidate in
Lean can remove the external-history scope uncertainty after exact bound
verification, without proposing a general PEEL narrowing.

Exact oldest singleton-flank normalization is now accepted. Exact statement and
mechanism are in OLDEST-FLANK.signature.lean.txt / OLDEST-FLANK.PROOF-PLAN.md.
The selected flank contributes exactly one chain extension and oldPure+m to
its strong join, so its axis parameter becomes min(global-1,k-m). Existing
boundary normalization is one-way; equality needs a genuine singleton last
level, maximum>=1 and all children/younger same-axis markers on the other side.
Other-axis markers and unindexed older positive labels can remain unrestricted.
This certifies the effective-parameter mechanism of the raw PEEL lift. The
normalized state keeps an unindexed marker and need not be WellFormed.
No new singleton selection theorem is proposed for the refuted raw-context domain.

K6 verification is complete: final check223.023s, guarded outer259.2s/8613MiB
under20G, typee482c53a7d35a688/lock unchanged, standard axioms/no sorry,
audit/layers pass. Three4GiB failures were localized to end-remainder evaluation;
the configured20G outer scope resolved them. Inner peak0 is unavailable nested
measurement. Temporary filesystem instrumentation is absent from pinned source.
Separate review window-f8ba8e9bb2e7489f is complete; its HANDOFF/CODE-REVIEW files
record precise scope, diagnostics and failures. Further work must answer an unresolved structural question,
not revive raw PEEL or commission a sibling-penalty narrowing.

The counterexample does not refute the happy-ending conjecture or the one-level
root exchange target. Its exact witness is now certified not Satisfies; whether
singleton attainment holds on actual coloring histories remains open.
The inherited end-cut-of-four-le statement is also ruled
out mathematically by the same raw witness, but was not edited and has no new
compiled corollary here.

## Failed routes and evidence limits

PEEL was registered unchanged with falsifier on node/CtxBoundAttainedBySingletonCut,
commit528caa7e560a86e8e77661d4a21e54d29f3454e4; its sorry is a blueprint placeholder.
Exact-dataset falsifier20261002-100340-9841d8 returned COUNTEREXAMPLE/inner rc2.
The depth<=3 generated scan20261002-093527-a2bca0 was scientifically superseded by
this depth4 witness and stopped through exact-identity recovery20261002-100139-bd1337.
Its terminal ERROR/-15 and partial coverage are not a pass. Unvisited coverage
remains open; PEEL.HANDOFF.md gives details and the non-run cancellation gap.

PEEL.MECHANISM.md explains the k6 middle-of-run examples. In SSS1L3L2LS at
(5,5,6), only the middle p1/upper/c3 cut attains8 as2+6. It retains a spanning
cup limit2 between residual runs, instead of a contiguous cup-limit1 run.
An end child with zero remaining-limit loss still gives rest4, while the middle
with some limit losses gives rest6. Raw limit-loss minimization is false.
Another example attains only through a zero-valued leaf. These observations are
diagnostic, not a valid universal selection principle. No stalled sibling-penalty
narrowing was commissioned.

PAIR-LIMITS checks first found the missing List.GetD import, then its explicit
argument contract. After compilation, the core pair-lemma import caused a28.4GiB
extraction closure refused by the4GiB guard. Local no-triple cardinality removed
the import; the guard and theorem stayed unchanged. All failures are journaled.

## Accounting and handoff

Initial window window-cc1a814a160145d6 ended with four accepted results. Separate
first-pass review window window-fcc41d920d8743c8 is complete. Pair-limit verification
window window-8eae99f6acd74cda ended with its accepted theorem; separate review
window window-882dc47915a3436d is complete. Witness-verification/review windows
window-7c764839f3134e8a / window-ff33769a9e324de5 are complete. Current normalization
window-04ff3046ae1d43aa and its separate review window-8645e8ca57fb4df3 are complete.
Transport/review windows window-1ee843e766a844cd / window-a1c945a4457b4523 are complete.
K6 verification/review windows window-6da4f1b237b94e57 /window-f8ba8e9bb2e7489f
are complete. Padding windows window-d44241a82a8146fc /window-061a596dfee14451
are complete. Ordinal windows window-001510fde88a48ee /window-afe2dfc298944d7d
and budget-cost windows window-33dfcce0c9504e9d /window-afcf9684c3d84ca5 are
complete. Reviews are Sol self-review under the fixed
no-delegation contract; independent coordinator review remains pending.

FIRST-PASS.CODE-REVIEW.md and PAIR-LIMITS.CODE-REVIEW.md record reuse/promotion
choices. Shared evaluators, parts, singleton cuts, proof assembly, guarded jobs
and immutable artifacts were reused. One-off mathematics on the refuted route
was not promoted; the exact cancellation recovery is not a general helper.

Usage sync and automated review found the host/session identity association gap:
our explicit ES_AGENT differs from host researcher_agent, and some responses are
already assigned to our explicit windows. Host-filtered zero jobs/receipts does
not mean no work. Direct journal, immutable receipts and deduplicated session
usage are authoritative; do not rewrite host descriptors or double-count.
Late usage reconciliation20261002-122158-f34224 covered the first ten ended
windows. Follow-up20261002-131856-404de8 covered completed k6/padding windows,
with zero cumulative deltas. Fourteen nonoverlapping completed windows have
deduplicated output total479025; LATE-USAGE.completed-windows-14.json is exact.
First review15363 and padding review11794 exceed their observational10k targets.
The latter job's declared jobs.json output was absent; its eight actual reports
were independently parsed and verified in LATE-USAGE.k6-padding.verified.json.
Ordinal/budget-cost reconciliation20261002-141857-d82c61 verified all four
actual reports with zero cumulative deltas. Eighteen completed nonoverlapping
windows have deduplicated output total552498, recorded in
LATE-USAGE.completed-windows-18.json. No matched-work savings are claimed.
Exact-k6 research/review late usage and final reporting reconciliation remain due. Preserve the ignored artifact root
runs/r19-sol-20261002/ alongside pinned branches. MATHEMATICAL-HANDOFF.md and
per-node handoffs carry the research account. No deadline or usage limit is reset.
