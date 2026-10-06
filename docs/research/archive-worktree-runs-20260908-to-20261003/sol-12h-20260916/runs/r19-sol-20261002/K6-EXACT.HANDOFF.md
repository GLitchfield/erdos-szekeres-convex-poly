# Exact k6 middle-singleton certificate

Updated2026-10-02 19:19 UTC. Agent codex:01a0fc94-0467-7b90-823c-bce1e6fe6128.
Branch node/CtxK6UniqueMiddleSingletonAttainment, independently based at
 e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8. No merge/push or delegation.

## Exact obligation and present status

Node ErdosSzekeres.ctx_k6_unique_middle_singleton_attainment, registered
20261002-141936-563c0a, locked type537308258d6e92aa, fixture
71156669dc05ec501c3729a2c1a04fb1dd1b13e16a12810c2d57e575fee67bfb.
K6-EXACT.signature.lean.txt is exact. For the fixed(5,5,6) context
SSS1L3L2LS, maxima111, prove bound8, p1/upper3 leaf plus lower2 remainder
attains8, that remainder is6, and every p!=1 child at every legal coupling
has both sums<=7. This includes run end p2. It does not assert uniqueness
of side/coupling, all interval attainers, global feasible PEEL, or sharp actual
cardinality8. WellFormed/Satisfies are separately certified on the same literal
by ctx_k6_satisfied_end_cut_counterexample; no combined receipt is claimed.

Full instrumented proof passed CLOSED in job20261002-143754-a63746,
compiler922.374348s, guarded outer960.2s/14987MiB under20G. Immutable receipt
 e0e76c9ea74ddab9d2e0193ebf069a1468b8e131ad7f2733b41db17509faa0e6.
No sorry, only propext/Classical.choice/Quot.sound, no blocked/uncovered
axioms, matching lock/type. Temporary filesystem progress writes were removed.
Original-source check20261002-145508-8b2f02 passed CLOSED1138.081594s,
outer1185.6s/15121MiB under20G, receipt
f2d86d2b78a2888f86ed602b7adc5c32e04d850e5616102b720b5348c4a89c38.
No sorry/extra axiom/blocked/uncovered dependency, unchanged type/pp; source
byte matches fixture and full body, SHA
85befe04af505206c056987148a83f3a17e3d25730f1eba446c5c7ed18f42309.
Audit/layers pass. Pinned commit1cd0281b18dddb1177d47d876c1e6b87f15fc741,
guarded commit20261002-151648-df2ac7 DONE; parent is exactly the fixed base,
five node files, clean tree. Research window-e77d2d7f9d0d4354 ended accepted1.
Separate self-review window-ad0ba0b085064f6f; K6-EXACT.CODE-REVIEW.md is exact.
Claim released CLOSED after review; all owned computation/commit jobs terminal.

## Why the theorem is true and proof structure

The middle peel separates its two neighbors into unit runs. Their spanning
cup limit2 permits total capacity2, while the old final run contributes4.
A neighbor peel merges those survivors into one cup-limit1 run, worth1;
the residual then has capacity5. Removing the last child removes the final
run and leaves capacity4 despite no loss of any remaining endpoint budget.
The middle leaf is2, so2+6=8. This is a run-geometry effect, beyond a count of
budget losses. No valid general feasible selection invariant is established.

Reuse closed ctx_bound_le_iff_all_interval_cuts_le for the parent upper bound.
Nine proper blocks give72 cuts. Four singleton certificates (8 sums each)
and three balanced certificates (8 each) give56 distinct numeric comparisons;
complement symmetry supplies the two three-child blocks, and the same singleton
certificates establish all24 nonmiddle cases. Seven local certificates avoid
repeating parent recursion. The p1 certificate plus leaf2 bounds its remainder
by6; an explicit lower tree gives6 as4+2, with the last2 as1+1. Cut dominance
then supplies parent>=8, antisymmetry gives equality, and finite child dispatch
proves uniqueness. Existing fuel stability is reused through the closed upper
certificate, not duplicated. The imported open end-cut theorem is unused;
target axiom/dependency checks certify no dependency on its sorry.

## Measurements, failures and preserved evidence

Pilot20261002-143028-dc4d1e failed2.794587s before numeric outcomes: progress
block inferred BaseIO, while stdout writing needs IO. Explicit IO Unit fixed it.
Failed body/check preserved in K6-EXACT.pilot-v1.*. Repaired pilot
20261002-143142-f8a97b checked middle6 in66.558s and first-rest5 in37.055s,
compiler106.491s/outer143.6s/10594MiB under20G. Its Blueprint sorry tail gives
no theorem credit. Structural-only checks20261002-143522-92993f and redundant
20261002-143648-e284fe passed with local numeric sorries, also no credit.
An artifact parser expected a dict from es.artifacts.read, which returns bytes;
that assembly failed before mutation, so the second structural job was unchanged
v1. json.loads repaired parsing. Redundancy/failure were explicitly journaled.
A later prose edit had a multiline-quote syntax error; no files changed, then
apply_patch corrected the handoff. Unsupported job show and a stale local exec
session poll had no job/source mutation. These are operational errors, not
mathematical failures. No failed or missing result is credited.

The instrumented pass wrote K6-EXACT.progress-0..7.txt. Seven group times were
229.344,425.321,248.090,0.262,5.225,5.072,5.161s. At10min review the pilot cost
ratio correctly explained the expensive middle group; job review left full
coverage unchanged, with6–10min estimated remaining. No self-chosen kill
budget/deadline. All declared outputs were present. Nested inner peak0 is
unavailable measurement; the guarded outer peak is authoritative.

K6-EXACT.lock-verification.json checks all378 inherited objects unchanged
as parsed JSON, exactly one new lock. K6-EXACT.final-verification.json records
the final receipt, assembly hashes and guarded measurements. Source/body/fixture APIs are shared es.proofs;
no ad hoc mathematical evaluator was written for this proof.

## Separate actual-history diagnostic and next safe action

Probe20261002-144048-b98707 and refined20261002-145007-c722e6 use shared
classifiers on one seven-vertex history, not a class enumeration. Core
[0,1,2,6] is constant-right; singleton upper ancestors at positions3/5/4 have
nearest-to-root levels1/2/3. Six explicit proper deep-below splits pass;
full maximum(cap,cup,strong)=(4,4,5), one-change true, root avoidance5/5/6.
Three shared root parts produce the literal context/maxima. K6-HISTORY.probe.json
is diagnostic, not Lean credit; v1 code/output preserved. Actual child cardinality
is4 and does not prove sharpness of capacity8. K6-HISTORY.PLAN.md gives the
finite future theorem and source/library contracts. Existing geometric coloring
realization does not assert the stronger coordinate deep-below predicate for
the same tree.

This node is released and review ended. A new independent branch may register
the finite actual-history
certificate. Search found the closed ctx_satisfies_of_deepBelowSplit; reuse it
to transport root constraints through the three actual singleton ancestors.
Native R19 goal stays active until fixed deadline2026-10-03T00:25:54.693298Z.
Consolidation starts2026-10-02T23:55:54.693298Z; neither deadline is reset.
