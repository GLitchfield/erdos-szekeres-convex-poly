# R13 mathematical handoff (checkpoint, 2026-09-30 23:13Z)

New research attempts stopped under the brief's two-failure rule. First,
minimum-active chosen-axis selection failed (175945-5d3b66). Second,
fixed-position lifting through a cut failed (191222-5c7678). At(3,4,5),
lower root[S,1L,S,S,1L,S],max[1],outer block[0,2,3],lower coupling1,
the part[S,2L,S,S,2L,1L],max[1,1],has an inner singletonp2 lowerc2
with cut sum2. Outer rest is a singletonp5 with bound1. Total3 exceeds
every root singleton atp2 (best2 atupperc3); singletonp5 upperc3 attains3.
All360 legal inner rows across24 eligible outer cuts completed;20 failures.
`fixed-leaf-lifting-fixture.json`/receipt are diagnostic, not Lean-certified.
This refutes retaining an inductively selected leaf while lifting. It does
not refute N or C1r. No expanded fixed-leaf family will run.

Finish the already registered exact-limit helper and the two authorized
running diagnostic probes, then review/report only. Do not start a new trial.

C1r is unchanged and open. The requested Done criterion is not met.
Exact remaining obligation: prove that every value in the multi-run root
recurrence is dominated after adjacent child deletion. The registered
singleton exchange X compares explicit one-child thresholds plus complement
parts, but a reduction from arbitrary interval cuts to those singleton cuts
has not been proved. A conditional that also assumes such a reduction would
not constitute C1r-from-X alone.

Accepted compiling nodes, each on its own branch from main41cc0e4b:

- `ctx_singleton_part_bound_eq_threshold`, hash47f67af285e3e6f,
  commit6d49410067fbc677ae64cc252d4774698985c353,
  targeted check20260930-165717-642558. Arbitrary raw singleton part equals
  explicit T(capLimit+1,cupLimit+1,k), including zero/unit capacities.
  `SINGLETON-HELPER.md` gives the proof and receipts.
- `ctx_num_runs_child_letter_contraction`, hash87d38cf7fc07a108,
  commit5bfb2e085e2999b10be2bf31fedfd645eb1fb152,
  isolated accepted proof op-6fc2a6974e26450b/job20260930-172809-41e2ac,
  targeted check20260930-173003-dade47. Arbitrary raw adjacent child deletion
  preserves run count. `NUMRUNS-HELPER.md` gives position-map proof/receipts.

Both nodes use only propext, Classical.choice and Quot.sound; their claims
were released closed. No full extraction, merge or push was performed.

Third accepted node: `ctx_bound_zero_of_unit_global_axis`,
hash3f2964484062c828,commitdd4291f419eef48178c2c75d9e839b6de18defa3,
isolated proofop-240299ed72764811/job20260930-174832-d8e6f8,
targeted check20260930-175052-dd087d. Every fuel/full bound is0 when either
global parameter is<=1,arbitrary raw contexts. Only standard axioms,
claim released closed. `ZERO-HELPER.md` gives receipts and review.

Registered partial narrowing: `ctx_one_level_root_singleton_base_exchange`,
hasha68960f119792789, commiteb65ce22ba759254ff4db4a06a159c5e70bd6f78,
targeted check20260930-171804-8bfcc5. Its proof remains sorry. The targeted
falsifier20260930-171455-ff2d9f passed3984roots/4648pairs/106912cuts and
168592explicit-T audits. `X-HANDOFF.md` states the full exchange. It allows
orientation and coupling reoptimization and covers every singleton p,
including p unrelated to the contracted adjacent pair. Claim released partial.

Compiling scratch only, no registered credit: `Core.lean` proves the raw
zero-global-axis bound and the all-cut upper recurrence (pass20260930-162839-1e7956).
`RootBranches.lean` proves single-run contraction using the closed geometry
and base contraction, and proves uniform one-level roots WellFormed when
a,u>=2 (pass20260930-174047-d3781e). First WF compile173939-6cd1df failed
only let-context simplification; source preserved inRootBranches.attempt1.lean.

`RootReverse.lean` compiles the actual reverse C1r inequality for the full
parameter range (pass20260930-180743-dfade0,464MiB). It uses the zero-axis
node,explicit root WF,and closed child expansion. A record-layout parse
error is preserved atRootReverse.attempt1.lean/job180637-be8293. The missing
direction is big.bound<=short.bound at numRuns>=2.

`SingletonReductionInterface.lean` compiles an honest conditional N+X=>
upper inequality for arbitrary raw contexts (pass20260930-181726-8f796c).
N explicitly assumes singleton attainment; X sends each old singleton to
a valid new singleton. This is not C1r-from-X alone. Early attempts failed
dependent-match elaboration; match(generalizing:=false) fixes it.

`SmallSingletonNormalForm.lean` compiles N for raw contexts with k>=3,
numRuns>=2 and at most3children (pass20260930-181942-f219cc). It takes a
maximum recurrence witness and classifies every proper2/3-child interval
block as a singleton or its complement; fuel stability gives exact equality.
It does not invoke the refuted end-cut theorem. This is now the fourth closed
node, `ctx_bound_attained_by_singleton_cut_of_le_three_children`,
hashbb154cfb31cbe29b, commit59809ac4e015f79f8acd2b58ccf07bd60d7257f1,
isolated proofop-3e4ead331249487c/job20260930-182808-3a9b3f,
targeted check20260930-183003-64cb4c. Only standard axioms, no sorry,
claim released closed. `SMALL-N-HELPER.md` supplies exact receipts.
Current branch node/CtxBoundAttainedBySingletonCutOfLeThreeChildren frommain.

`ChildPositionTransport.lean` proves the exact q membership used by X
for arbitrary raw words (pass20260930-183606-427b62). Its first
compile182232-940a60 failed only two reassociation goals in word lengths;
omega repairs passed. Scratch only, no registered credit.

`RootConditionalInterface.lean` compiles the actual full C1r equality from
BOTH N and X (185428-a5469d); this is not the requested narrowing Done.
`RootConditionalSmall.lean` compiles C1r from X with<=3children, using the
accepted small-N theorem to discharge N (185653-ed8b9e,7.2s/519MiB).
Both are scratch only. Failed wrappers and sigma.k normalization attempts
are preserved as attempt files and logged, not treated as math failures.

`OneLevelLimits.lean` compiles raw exact one-indexed-level capacities:
join on selected side=max(chain,m),opposite chain/join0,chosen capacity
min(global-1-chain,k-1-m),opposite capacity=otherglobal-1. Globals<=k,
maxima=[m],sideAt1=s,arbitrary endpoints/noWF/nochild-membership needed.
Scratch190039-f57429 passed5.8s/531MiB. Node
ctx_single_level_limits_exact registered190926-53b050,hash27c5ffa48b789810,
branch node/CtxSingleLevelLimitsExact frommain; claim active,body/capture
prepared,not yet checked/committed. It is not yet accepted theorem credit.

Diagnostic evidence, never a Lean proof: exhaustive bounded root singleton
attainment passed5400k5,10368k6,17640k7 contexts with<=4children; endpoint-only
versions failed4/6/8 respectively. Localized X passed the all-k5 family
5400roots/7800pairs/201600cuts, with2608recouplings. Every result and probe
semantics is under this directory; the evaluator uses zero-child-capacity
semantics `context-bound-zero-children-c-v1` and checked signed64-bit arithmetic.

Active jobs to check before any resumed attempt:

- 20260930-170246-ccbdbe: general singleton attainment at(5,5,6),
  exact5children,<=2externals,<=2indexed levels including unused levels,
  all maxima and uniform per-level sides. Output
  `general-singleton-five-k6.json`;2688/3889 at5618s,zero failures.
  Cap1G,persistent2M memo,next review22:47Z (check again if due).

Completed20260930-180439-d550b7 root singleton benchmark:680/680 at
(6,6,7),allm1..5,both sides/ends,2..5runs,len1/2,<=5children,
2246.73s,zero singleton or endpoint failures. Output
`singleton-k7-five-scale.json`. Do not launch49globalpairs at this measured
cost without a cheaper route.

Completed three-level N samples at(5,5,6): balanced shape
[S,S,E,E,E,S,S],job20260930-183035-f9cc1b,3072rows117.63s;
isolated shape[S,E,S,E,S,E,S],job20260930-183722-34c55a,
3072rows189.22s. All8 uniform per-level side patterns,all6 orders,
all64 maxima choices1..4; zero failures. Outputs
`balanced-three-level-singleton-all.json` and
`isolated-three-level-singleton-all.json`. These are only two placements,
not all three-level contexts. Diagnostic, not Lean-certified.

Both use ten-minute progress reviews without a chosen kill deadline. Native
host job20260930-160249-642cc3 remains active; do not cancel it.

Failed approaches already ruled out by prior evidence: same-cut/same-coupling
contraction is false in descendants (P7); C1r itself has non-separating cuts
that require orientation/coupling changes (P11). General end-cut normal form
is refuted and must not be used. P11 k7 non-separating rescue tables include
larger blocks, not only singleton blocks. Finite singleton evidence does not
remove that obligation. No new axiom or native_decide was introduced.

Safest next action: finish both authorized diagnostic jobs and inspect their
full terminal outputs; use the closed geometry and base lemmas for boundary
branches, then develop an actual root-only value reduction without assuming
the refuted descendant or end-cut laws. Research deadline08:02:53Z,
consolidation07:32:53Z, final reporting08:32:53Z on2026-10-01.

Additional diagnostic failed route: minimum active chosen-axis capacity does
not select an attaining singleton. At(a,u,k,m)=(3,4,5,1),lower word
[S,1L,S,S,1L,S],sourcebound3,mincup1 atp2/3,bestselected singleton2,
bestunrestricted3 atp5. Job20260930-175945-5d3b66 completed192cases,
0.784s,onefailure. `min-active-singleton-smoke.json`/receipt preserve it.
No larger retry of this false selector was launched. Unrestricted N is
not refuted by the witness and has only finite positive evidence beyond3.

Completed k6 X sweep20260930-164738-c3329d:10368roots14976pairs,
516096cuts737280explicit-T audits,zero failures,3551.9s.10084rescues
included5568side-only,3816shift-1,284shift+1,416shift-2. Complete output
`exchange-k6-all5.json`/`RECEIPT.exchange-k6-all5.json` is diagnostic only.
