# Exact seven-vertex history certificate

Agent codex:01a0fc94-0467-7b90-823c-bce1e6fe6128, 2026-10-02 20:19 UTC.
Branch node/CtxK6ActualHistoryWitness starts independently at
e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8. No merge or push.

The accepted obligation is ctx_k6_actual_history_witness, locked type
80c84048681897f7. Registration20261002-152751-e1af40 passed103.6s/2305MiB.
Fixture5012c7d1eb106f951d85adba4ef2ed8380de541e8558a31d0803d9b0d155ff0e.
Research window-919a78fd58a7486a ended with accepted1. Separate self-review
window-93d73fe61830469a ended accepted0 after inspecting final proof, receipts, command journal and
diagnostic artifacts; K6-HISTORY.CODE-REVIEW.md records the review and maintenance
decision. Claim released CLOSED; K6-HISTORY.release.json confirms both handoff
and code-review evidence were copied to the shared primary checkout.
Corrected full proof is accepted in isolated check op-3ab73e56b0e14388,
job20261002-155957-e8611a, stage receipt959ef5c36fd773c046a8c5f26a235f443d21ece92dcab4d99a6611d32c6b6f6a.
It took9.095906s/2100MiB under4G, expected type and standard axioms only.
Final source removes four stdout diagnostic blocks. Original-source check
20261002-160456-155bf5 is CLOSED (compiler6.601233s, outer55.5s/2353MiB under4G),
receiptd882dc65055b3a1af3920b833c3e518df688494e481c51e80b25075ff88f965d.
Expected type/pp and lock, standard axioms only, no sorry/blocked/uncovered,
byte-exact fixture assembly, all378 inherited lock objects unchanged/one new,
changed audit and layers pass. Final source232d37afc9f8445f7d41037f955b1bc3e56390601bb99113c8c4ce1674a2d944,
body33e2003243e3575b45c61e20de363b79397090b33d6de93fefdb45d6a88343de.
Pinned d3b81e384ff288237fbef7fa380c985dd0ded1ca; guarded commit
20261002-161126-1ae1b0 DONE, parent exactly e3c87197, clean worktree.
All owned jobs are terminal. Exactly five node/import/index/lock/status files
changed. No new evaluator or execution script was introduced; existing shared
classifiers, context parts, proof assembly and context-transfer lemmas were
reused. No promotion is warranted for the fixed mathematical candidate or its
one-node sorted-position interpretation. Independent coordinator review is
pending; the separate review here is Sol self-review under no delegation.

The explicit coloring on Fin7 assigns levels[0,0,0,1,3,2,0]. An increasing
triple is left exactly when its largest level is positive and its middle
vertex has smaller level; all-level0 triples are right. The largest external
level selects the rootmost crossing ancestor. Six finite split certificates
construct the decomposable tree. Existing IsDecomposable.isSweepRealizable
supplies planar general-position realization of the coloring.

The ancestor lower sets are {0,1,2,3,5,6}, {0,1,2,3,6}, {0,1,2,6}, with upper
singletons {4}, {5}, {3}. Actual sibling cap maxima are1. Finite subset checks
certify every cap/cup cardinal<=4 and every strong-set cardinal<=5 at the root.
Three applications of the already closed ctx_satisfies_of_deepBelowSplit,
with literal positionsOf keep lists and WellFormed.part, give Satisfies for
the final four-child context SSS1L3L2LS/maxima111 at(5,5,6). Three root parts
equal that context by definitional reduction.

This removes the actual external-history uncertainty of the cost/end example.
It does not construct an eight-point child, prove capacity8 sharp, establish
general feasible PEEL, or certify IsGeometricallyDeepBelow for this same
coordinate split tree. The exact bound8 and unique middle-child attainment
are separately accepted at commit1cd0281b18dddb1177d47d876c1e6b87f15fc741,
receiptf2d86d2b78a2888f86ed602b7adc5c32e04d850e5616102b720b5348c4a89c38.
Combining independent accepted statements has no separate compiled conjunction.
There is no general feasible-selection invariant or proof idea yet.

The finite pilot20261002-154436-ae1185 passed (compiler4.582335s,
outer49.1s/2355MiB under4G); crossing351ms, root profile763ms. Its sorry tail
gives no theorem credit. K6-HISTORY.pilot-v6.check.full.json retains the node
and guard payload. The final candidate is K6-HISTORY.full.body.lean.txt.

Failed attempts and their meaning:

* 20261002-153422-dc918a: missing leading by in fixture body; compiler3.325s,
  no mathematical evaluation. pilot-v1 body/check preserved.
* 20261002-153500-86fdd9, 20261002-153655-c5bc19,
  20261002-153851-3e25d1: root finite Decidable synthesis failed in3.6–4s,
  despite explicit indices and normalized projections. Guesses about implicit
  binders and proof dependence were insufficient and were corrected in journal.
* 20261002-154022-ac8881: diagnostic isolated the actual size cap. Finset
  Fintype and simple forall decisions work; combined instance size166 exceeds
  default128. Trace check-20261002-154026-ctx_k6_actual_history_witness.log
  records rejection. Local synthInstance.maxSize512 fixes it; diagnostic body
  and check are preserved. No root result from this failed diagnostic.
* 20261002-154202-52abea: direct implication evaluation OOM at4096MiB,
  one kill, compiler16.890s/exit137, outer29.6s. No root result or reliable
  buffered stage timing. Cardinality-first disjunctions preserve all128 sets
  while avoiding chain evaluation on99 sets<=4 and120 sets<=5. Recover original
  implications from these finite alternatives. The optimized pilot passes.
* Two assembly assertions failed before mutation/submission because a marker
  for hd01 also matched hd012. An initial guessed newline diagnosis was wrong;
  exact marker correction is recorded. No missing compiler attempt is claimed.
* Successful pilot payload is flat build_seconds, not nested build. Inspection
  KeyError had no side effects; keys were inspected before proceeding.
* 20261002-154618-34ea0c: full check refused before compiler admission,
  requested nested20G above enclosing4G, rc125/seconds0, outer10.5s/83MiB.
  Declared compiler log does not exist; inspection FileNotFoundError was
  explained by refusal.
* 20261002-154722-fecddc: got admitted during cancellation race, already
  failed before compiler with occupied artifact-cache storage reservation;
  rc125/seconds0, outer10.2s/82MiB. Cancel reports terminal acknowledgment;
  no compiler coverage or foreign state was dropped. Declared log is absent.
* Isolatedv1 op-180d1609cbe745f9/job20261002-155127-5fa9b1 failed256.890s/
  537MiB, receiptb71ba3d1017eccbb5d09ddbaad637221a4518ac84bedb128ec45e1749b94b3af,
  diagnostic48a54427a965abf3b58bd1313dd67ab96eb04e5f8a0260ac7e726a5b53447f42.
  Root rewrite lost replicate form; three positionsOf decisions did not reduce;
  sibling maximum simp did not match, and subsequent unification exhausted
  4m heartbeats. Ordinal-map/sorted membership proof and explicit actual-upper
  maxima rewrite fix these. Exact failed body and candidate source are retained.
  A progress review raced terminal completion and was rejected; no next5 review
  was recorded. Journal corrects the initially inaccurate following wording.
* 20261002-160237-e3eae9: final20G check remained queued. Foreign28G extraction
  plus three2G hosts left6G shared capacity. Exact cache reservation was empty;
  the complete proof had already passed4G. Replaced only that unstarted job with
  measured4G check20261002-160456-155bf5, same finalized source and coverage.
  Cancellation was for memory allocation, not a chosen time deadline or result.

Accepted isolatedv2 source55ce20bd62f8cefb27c8ac0da113f317e05b0edbed9b1cc4f6beb4ded7984735,
bodycaa1e06eb7f8755c4dbede1a18e7984848f582d91197722ae24754ebdc20e769,
fixture128743e781301de92a639c9192988995d08c5ffea0c447ac6a64e0b2bcae7524.
K6-HISTORY.isolated-v2.terminal.json retains audit/dependency validation.
Final original source differs only by removal of stdout blocks and has its own
CLOSED receipt above. Sorted positionsOf interpretation uses existing
positionsOf_pairwise_lt, mem_positionsOf, List.Perm sorted uniqueness;
only the ordinal map and literal set/list properties require finite evaluation.

Searches: K6-HISTORY.search.json (no exact history theorem), singleton-search,
helpers-search, satisfies-part-search. The latter finds the closed transfer
theorem reused three times. Library/source reuse: decomposable coloring/split
classifiers and research.context-part for the diagnostic, Mathlib computable
Finset Fintype for the kernel table, existing chainMax_le_iff/one_le_chainMax,
WellFormed.part, and geometric decomposable realization. No duplicate engine.

Separate usage reconciliation20261002-154202-33eb3c passed1.5s/26MiB after
two recorded infrastructure failures (wrong positional window syntax; absent
worker CODEX_THREAD_ID). It exports the exact existing thread, not a new one.
LATE-USAGE.completed-windows-20.json records671178 output tokens in20 completed
windows, zero reconciliation deltas. Active/unassigned work and incomplete
resource associations remain excluded; no all-in matched savings claimed.
