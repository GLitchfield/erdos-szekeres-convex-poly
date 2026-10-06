# R13 progress

Started 2026-09-30T20:03Z. Researcher: `codex:agent-run-65158fed3cd841d2`.
Configured model/effort: `gpt-6.1-sol`, `xhigh`. No delegation.

Target: `ctx_bound_child_run_contraction_one_level_root` (C1r).
Done criterion is **not met**. Four reusable helpers are proved and committed;
C1r and the requested conditional from a single narrower X are still open.

**Research stopped at 2026-09-30 23:13Z under the brief's two-failure rule.**
Two routes failed at the singleton-reduction obligation: the minimum-active
capacity selector, and fixed-position lifting of an attaining singleton
through an outer cut. The latter fails even when root side and coupling may
change: a legal inner value2 plus outer rest1 gives3, while every root cut
at that same p has value<=2. Root singleton at another p attains3.
Evidence: job20260930-191222-5c7678, fixed-leaf-lifting-fixture.json.
N and C1r themselves remain unrefuted. No larger fixed-leaf retry will run.

Completion work only remains: install/check/commit the already registered
exact one-indexed-level capacities helper, inspect the two running probes,
review artifacts and reconcile usage/handoff. Running probes:
20260930-170246-ccbdbe and20260930-184927-794b43. Node registration
20260930-190926-53b050 completed; exact-limit scratch check
20260930-190039-f57429 passed. This pending fifth helper is not yet counted.

Initial worktree HEAD: `e00928048c9a0dc2d6a9ecc9dc9c08db6bab8783`.
Required branch baseline main: `41cc0e4b58206008bde4af9b510b56b35dd3aa69`.
Initial harness state: `status-initial.json`, `stale=[]`, `problems=[]`.
Research usage window: `window-2facfcf307994c0f`.

The first claim was refused because this worktree lacked a passing falsifier
receipt. Guarded targeted falsifier `20260930-160559-931c71` finished rc=0:
1200 k=5 + 2304 k=6 contexts, zero violations, 1113.1 s. Receipt
`RECEIPT.falsify-c1r.json`, diagnostic result `FALSIFIER.c1r.pass.json`.
The second claim was also refused: the claim command reads the cached
`nodes.json` status, which the targeted falsifier deliberately does not refresh.
Main has a passing cached record. Guarded checkout `20260930-162909-f27997`
created `node/CtxOneLevelRootSingletonBaseExchange` from `main` at `41cc0e4b`.
The C1r claim then succeeded for `codex:agent-run-65158fed3cd841d2`.
No harness patch or full extraction was needed.

Current route: inspect the one-level root recurrence and P11 moved-cut rescue;
seek a value exchange against an explicit single-child threshold. The P7
counterexample rules out assuming contraction in arbitrary descendants.
P11 k=7 also contains shifts of magnitude three and non-separating rescues.
General end-cut normal form is harness-refuted and will not be assumed.
The first bounded diagnostic tests singleton cuts in one-level roots, to
identify a reduction that could actually derive C1r from a base/part exchange.

Completed evidence:

- `20260930-160845-134563`: singleton normal-form smoke, 96 contexts,
  0 failures, 0.16 s. Output `singleton-smoke.json`.
- `20260930-160951-c033f2`: singleton normal-form scaling at (5,5,6),
  352 contexts with <=5 children, 0 failures, 216.98 s.
  Output `singleton-scale-k6.json`.
- `20260930-160952-da74b5`: guarded Lean interface audit, rc=0.
  All seven reused helper declarations printed only standard axioms.
  Receipt `RECEIPT.interfaces.json`, source `Interfaces.lean`.

- `20260930-161514-5418ea`: k=5 all a/u, 5400 <=4-child contexts,
  zero singleton failures, four end-only failures, 40.89 s.
- `20260930-161514-907ce7`: k=6 all a/u, 10368 <=4-child contexts,
  zero singleton failures, six end-only failures, 205.31 s.

These normal-form checks are finite diagnostics. No reduction theorem has
been proved. Interior singleton cuts are necessary in this parameter domain.
`Core.lean` develops the raw zero-parameter case and the defining all-cut
upper bound. First compile `20260930-162238-4e39ad` failed because `rw` inferred
the parent context instead of the part; explicit part contexts repair it.
The successful recurrence example alone does not close the exchange gap.
`20260930-162839-1e7956` now compiles both scratch glue examples (rc=0).

Current candidate, not yet registered: every singleton cut's explicit
`T(capLimit+1,cupLimit+1,k)` plus complement-part value is dominated by the
same mapped singleton in the contracted root at a reoptimized orientation
and coupling. `probe_singleton_exchange.py` checks all adjacent duplicate
positions and audits each explicit threshold against the compiled leaf.
Sufficiency for arbitrary interval cuts remains an exact open obligation.

The explicit singleton-part identity now compiles in `ExplicitSingleton.lean`,
job `20260930-164345-e12daf` (receipt `RECEIPT.explicit-singleton-pass.json`).
This identifies the exchange leaf with explicit T even at zero/unit limits.
The first scratch compile failed only at list/part-field elaboration; its
source and receipt are preserved.

- `20260930-163512-92d63d`: localized exchange, exhaustive k5 bounded family,
  5400 roots, 7800 adjacent-pair cases, 201600 cuts and 288000 leaf audits.
  Zero violations; 2608 required reoptimization. Output
  `exchange-k5-all5.json`, 596.3 s, diagnostic only.
- `20260930-163513-578615`: exchange scaling at (5,5,6),
  288 roots, 416 pairs, 14336 cuts, zero violations, 103.6 s.
- Running `20260930-163513-cfa6ad`: exhaustive k7 singleton-attainment
  check with <=4 children; checkpoint 12312/17640, zero singleton failures,
  eight endpoint-only failures; left running on track.
- The general-context singleton-normal-form smoke first failed before
  evaluation (`20260930-164546-baf63b`, absent worker `python` executable).
  Rerun uses python3 and the inspected list API; no mathematical result yet.

Registered helper: `ctx_singleton_part_bound_eq_threshold`, closed targeted
check `20260930-165717-642558`, `sorry=false`, standard axioms only, statement
hash `47f67af285e3e6f`. Commit `6d49410067fbc677ae64cc252d4774698985c353`,
branch `node/CtxSingletonPartBoundEqThreshold`, commit job
`20260930-165924-d1ee9e`. Helper claim released closed. Evidence and focused
handoff: `RECEIPT.singleton-helper-check.json`, `SINGLETON-HELPER.md`.
Ignored --include artifacts did not enter the commit; they remain under runs.

The k7 singleton-attainment probe finished: 17640 contexts, zero singleton
failures, eight endpoint-only failures, 687.3 s. General singleton attainment
also passed 1495 contexts at(3,4,5) and 2617 at(5,5,6), with four children,
at most two external letters and two indexed levels, including unused levels.
These are diagnostics, not a normal-form theorem.

Running exchange job `20260930-164738-c3329d`: full k6 <=5-child family,
14976 pair cases. Checkpoint 3604 cases in 712 s; about37min remain,
no failures reported. Running general five-child scaling job
`20260930-165808-8b70ea`: last96 depth-two cases, progress32/96 in48s,
no failures reported. Native research remains active.

Localized X now registered: `ctx_one_level_root_singleton_base_exchange`,
hash `a68960f119792789`, module `CtxOneLevelRootSingletonBaseExchange.lean`.
Its targeted falsifier `20260930-171455-ff2d9f` passed in29.5s:3984 roots,
4648 pairs,106912 cuts,168592 explicit-T audits,zero violations. Evidence
`FALSIFIER.X.pass.json`; exact partial-narrowing handoff `X-HANDOFF.md`.
Targeted module check is pending. The proof is still sorry; a conditional
from X alone has not been derived, so this does not meet Done.

`NumRunsTransport.lean` compiles, job `20260930-171623-382c2c`: adjacent
child contraction preserves run count for arbitrary raw contexts. This
opens the single-run base branch independently of the multi-run gap.
General five-child singleton-attainment job `20260930-170246-ccbdbe` has
3889 contexts; checkpoint384/3889 in684s,zero failures,about104min left.
The exact domain remains unchanged at1G with10min checkpoints.

X's targeted check `20260930-171804-8bfcc5` finished rc0. X is committed
as `eb65ce22ba759254ff4db4a06a159c5e70bd6f78` via job
`20260930-172130-c4e358`; its claim was released partial. Its proof remains
sorry/open. Done is still **not met**. C1r's statement and proof are unchanged.

Research deadline: `2026-10-01T08:02:53.423594Z`.
Consolidation starts: `2026-10-01T07:32:53.423594Z`.
Host job: `20260930-160249-642cc3`.

At21:39Z numRuns helper is closed and committed:
`5bfb2e085e2999b10be2bf31fedfd645eb1fb152`, branch
`node/CtxNumRunsChildLetterContraction`, commit job20260930-173304-1a85a7.
Actual isolated proof acceptance op-6fc2a6974e26450b/job20260930-172809-41e2ac
was followed by targeted check20260930-173003-dade47, standard axioms only,
sorry=false, hash87d38cf7fc07a108. Focused handoff NUMRUNS-HELPER.md;
claim released closed. C1r remains unchanged/open.

Active probes: exchange20260930-164738-c3329d is12756/14976 pair cases,
zero failures, estimated9min left. General singleton attainment
20260930-170246-ccbdbe is1120/3889,zero failures,estimated85min left.
Both checkpoint decisions preserve their complete original domains.

RootBranches.lean compiles after explicit-let repair (job20260930-174047-d3781e).
It proves single-run contraction for arbitrary raw contexts and one-level
uniform-root well-formedness at a,u>=2 as anonymous scratch results.
First compile20260930-173939-6cd1df failed only two context simplification
matches, preserved/logged. These scratch lemmas earn no registered credit yet.

Full k6 X diagnostic20260930-164738-c3329d finished rc0 in3551.9s:
10368roots14976pairs516096cuts737280explicit-T audits,zero violations.
10084rescues:5568side-only,3816shift-1,284shift+1,416shift-2.
Complete exchange-k6-all5.json and RECEIPT.exchange-k6-all5.json.
General singleton-attainment job20260930-170246-ccbdbe remains running.
Raw zero-axis node registration20260930-174521-a8e0b3 is pending on fresh
node/CtxBoundZeroOfUnitGlobalAxis frommain41cc0e4b; this is a reusable
boundary helper, not completion of C1r.

At21:54Z raw zero-axis helper is closed and committed:
ctx_bound_zero_of_unit_global_axis,hash3f2964484062c828,
commitdd4291f419eef48178c2c75d9e839b6de18defa3 on
node/CtxBoundZeroOfUnitGlobalAxis. Isolated accepted proof
op-240299ed72764811/job20260930-174832-d8e6f8, targeted check
20260930-175052-dd087d,commit job20260930-175305-aa3cbc. Standard axioms
only,sorryfalse,locktrue;claimreleasedclosed. ZERO-HELPER.md and full
NODE.zero.full.json record evidence. Done remains not met.

Extremal singleton reduction attempt1 failed diagnostically:
job20260930-175945-5d3b66 completed192 k5(a3,u4) cases in0.784s and
found [S,1L,S,S,1L,S],m1,bound3. Minimum-active lower capacities occur
atp2/3 but their best singleton cuts are2; outerp5 yields3. Evidence
min-active-singleton-smoke.json/RECEIPT.min-active-singleton-smoke.json.
The exact general singleton reduction remains open; no larger sweep of
this false minimum-capacity candidate is justified.

Actual reverse C1r inequality compiles for every target parameter, including
a/u=1: RootReverse.lean/job20260930-180743-dfade0 rc0,464MiB. It uses the
closed zero-axis node plus explicit one-level WF and closed expansion.
First submission was refused at shared28+4>30G; measured2G cap admitted.
First compile180637-be8293 failed record-layout parsing, preserved/logged;
second passed. Scratch only, no new node credit. Missing upper direction is
big.bound<=short.bound when numRuns>=2.

SmallSingletonNormalForm.lean compiles,job20260930-181942-f219cc:
raw sigma,k>=3,numRuns>=2,childcount<=3 has an exactly attaining singleton
cut at an admissible coupling, either orientation. No WF/end-cut premise.
Registration is queued4G on fresh node/CtxBoundAttainedBySingletonCutOfLeThreeChildren
frommain. Shared reservations28G leave insufficient headroom for the
measured~2.3G registration pipeline. It is not a closed registered node yet.

SingletonReductionInterface.lean passesjob20260930-181726-8f796c after
explicit match(generalizing:=false): explicit N plus X imply the upper
inequality. This is scratch only and does not count as C1r-from-X alone.

Small-arity N registered successfully:20260930-182142-a9709e rc0,
peak2282MiB,complete-index duplicate check,targeted extraction only.
Claim active;proof capture pending/available atCAPTURE.small-N.json.
The compiling body is SmallSingletonNormalForm.body.lean. Next verify
whole parent through es proof check,then target-check and commit.

At22:36Z fourth reusable helper is closed and committed:
ctx_bound_attained_by_singleton_cut_of_le_three_children,
hashbb154cfb31cbe29b,commit59809ac4e015f79f8acd2b58ccf07bd60d7257f1,
branch node/CtxBoundAttainedBySingletonCutOfLeThreeChildren frommain.
Accepted proofop-3e4ead331249487c/job20260930-182808-3a9b3f;
targeted check20260930-183003-64cb4c,commit20260930-183453-a1e76d.
Standard axioms,sorryfalse,locktrue;claimreleasedclosed.
SMALL-N-HELPER.md/NODE.small-N.full.json carry receipts.
Done remains not met: singleton attainment for4+children unproved,
C1r and conditional C1r-from-X alone still open.
# Checkpoint 2026-09-30 22:49Z

FOUR closed helpers committed; Done is still not met. The small-N node is
59809ac4e015f79f8acd2b58ccf07bd60d7257f1 with targeted check
20260930-183003-64cb4c. ChildPositionTransport.lean passed guarded job
20260930-183606-427b62 (scratch only).

Completed diagnostic probes: 20260930-183722-34c55a (3072 isolated
three-level rows,189.22s) and20260930-180439-d550b7 (680 five-child k7
roots,2246.73s),zero failures. New all-placement probe20260930-184927-794b43 records every one of
31 multi-run four-child/three-marker placements, all8 side patterns,
6 level orders and64 maxima;95232 rows. Smoke128 passed in1.772s,
job20260930-184809-f5b32c. Estimated full cost61-98min,10min reviews.
