# R13 mathematical handoff — stopped; authorized jobs completed

Final mathematical account, finalized 2026-10-01. Configured researcher
codex:agent-run-65158fed3cd841d2, gpt-6.1-sol,xhigh, no delegation.
**Done is not met. C1r remains open and unchanged.** New research attempts
stopped at23:13Z under the brief's two-failed-attempt rule. Complete only
already authorized work; all proof/probe/library jobs are now terminal.
The coordinator reviewed this STUCK outcome and ended research at
2026-10-01T00:00:34.307053Z, with finalization hard stop
2026-10-01T00:30:34.307053Z. No new research, checks or trial were started
in finalization. The native goal remains paused; mathematical Done is unmet.

## Exact open obligation for this route

Let sigma be the C1r root: globals1<=a,u<=k, k>=3, maxima=[m] with
1<=m<=k-2, word=left++[S,S]++right, all other letters S or ext1side.
Let P=sigma.childPositions. The missing root singleton reduction N is:

For numRuns(sigma)>=2, there exist p in P, orientation s and coupling
1<=c<=k-2 such that

    sigma.bound <=
      T(capLimit(sigma.part [p] s c,p,p)+1,
        cupLimit(sigma.part [p] s c,p,p)+1,k)
      + (sigma.part (P.filter (q != p)) opposite(s) (k-1-c)).bound.

The reverse cut inequality is already available, so this is an attainment
statement. It is proved here only when |P|<=3. Root N with arbitrary child
count is unproved and unrefuted. General raw-context N is an even stronger
unproved candidate; finite probes do not substitute for either theorem.

The registered singleton-base/complement-part exchange X dominates each
old singleton value by the same mapped singleton in the shortened root at
some new orientation/coupling. Its explicit thresholds avoid an all-cut or
whole-root-bound hypothesis. X has positive falsifier evidence but remains
sorry. To meet narrowing Done with this X, first discharge the root N gap,
then register/prove C1r-from-X alone and compose C1r's module. The scratch
full conditional assumes BOTH N and X and therefore does not meet Done.

## Accepted reusable theorems and commits

Every node branch was created independently from required main
41cc0e4b58206008bde4af9b510b56b35dd3aa69. All five receipts below say
sorry=false and only propext, Classical.choice, Quot.sound. Claims released
closed. Coordinator integration is recorded on main 7d9c2fed: the first
four helpers are closed there and X is open, verified read-only against
its generated status. The accepted fifth helper 95559e09 awaits integration.

| Node | Commit | Type hash | Targeted check job |
| --- | --- | --- | --- |
| ctx_singleton_part_bound_eq_threshold | 6d49410067fbc677ae64cc252d4774698985c353 | 47f67af285e3e6f | 20260930-165717-642558 |
| ctx_num_runs_child_letter_contraction | 5bfb2e085e2999b10be2bf31fedfd645eb1fb152 | 87d38cf7fc07a108 | 20260930-173003-dade47 |
| ctx_bound_zero_of_unit_global_axis | dd4291f419eef48178c2c75d9e839b6de18defa3 | 3f2964484062c828 | 20260930-175052-dd087d |
| ctx_bound_attained_by_singleton_cut_of_le_three_children | 59809ac4e015f79f8acd2b58ccf07bd60d7257f1 | bb154cfb31cbe29b | 20260930-183003-64cb4c |
| ctx_single_level_limits_exact | 95559e090ff7044040348aec1c00ac7094fbd6af | 27c5ffa48b789810 | 20260930-194307-536ecb |

The first identifies an arbitrary raw singleton part's bound with the exact
T term, including zero/unit capacities. The second preserves raw run count
under adjacent child deletion by an explicit position map. The third proves
boundFuel=0 for EVERY fuel, and bound=0, when a<=1 or u<=1 in raw contexts.
The fourth proves exact attainment by a singleton/complement cut for raw
contexts with k>=3,numRuns>=2,|P|<=3; p may be interior. It classifies proper
intervals of two/three children and uses stable fuel to extract an attaining
maximum. It never invokes the refuted general end-cut assertion.

Focused accounts and actual receipts: SINGLETON-HELPER.md,
NUMRUNS-HELPER.md, ZERO-HELPER.md, SMALL-N-HELPER.md. Isolated accepted
operations for the latter three are op-6fc2a6974e26450b,
op-240299ed72764811 and op-3e4ead331249487c; corresponding jobs
172809-41e2ac,174832-d8e6f8,182808-3a9b3f on20260930.

## Fifth accepted helper

ctx_single_level_limits_exact, hash27c5ffa48b789810, current branch
node/CtxSingleLevelLimitsExact. For raw sigma,maxima=[m],a/u<=k,
sideAt1=s and arbitrary p,q, joinExt(s)=max(chainExt(s),m), opposite
chain/join are0, selected limit=min(global-1-chainExt(s),k-1-m),
opposite limit=otherglobal-1. No WF or child-membership premise.

Scratch190039-f57429 passed; targeted registration190926-53b050 passed.
Captured fixture3b30692e0ef2e617d34fa03f496fa1dcb3daa9c0d2234a932d3a21d16fec493b,
bodyd6be72f2432767d1bc5ed28a06ae573189e1089e23132ab1499f2f9eb7b2337c.
Isolated check op-489128753867417b/job20260930-192528-c4309b accepted at3G,
standard axioms only,12.04s/2101MiB. Installed source hash81e034f2 matches
the retained candidate byte-for-byte, with only the captured body changed.
Original-source targeted check194307-536ecb confirmed sorry=false,
lock_ok=true and unchanged type hash (build5.13s/649MiB). Commit
95559e090ff7044040348aec1c00ac7094fbd6af,job194452-0516c6; claim closed.
The identical4G request was verified unstarted and cancelled to lower its
reservation; no compiler result or coverage was lost.
ONELEVEL-HELPER.md gives the exact accepted receipts and source.

## Registered partial exchange

ctx_one_level_root_singleton_base_exchange, hasha68960f119792789,
commiteb65ce22ba759254ff4db4a06a159c5e70bd6f78,
branch node/CtxOneLevelRootSingletonBaseExchange. Sorry remains;
claim released partial. X-HANDOFF.md gives exact statement and evidence.
Targeted module check171804-8bfcc5 is a compiling conjecture, not a proof.
Falsifier171455-ff2d9f passed3984roots/4648pairs/106912cuts and
168592explicit-T audits. Broader diagnostic X sweeps passed:

- k5:5400roots/7800pairs/201600cuts/288000audits,
  job163512-92d63d,596.3s,exchange-k5-all5.json.
- k6:10368roots/14976pairs/516096cuts/737280audits,
  job164738-c3329d,3551.9s,exchange-k6-all5.json. Of10084 rescues,
  5568 changed side only,3816 shifted coupling-1,284 shifted+1,416 shifted-2.

These checks use finite families of at most five children; they prove
neither X nor the reduction from arbitrary interval cuts.

## Compiling scratch observations, no registered credit

RootReverse.lean/job180743-dfade0 proves actual reverse C1r for the full
parameter range. For unit axes it uses the closed zero lemma; otherwise
explicit uniform-root WF and closed expansion apply. RootBranches.lean /
174047-d3781e handles the single-run contraction branch. The unresolved
inequality is big.bound<=short.bound at numRuns>=2.

ChildPositionTransport.lean/job183606-427b62 proves valid mapped q for every
child p: q=p if p<=left.length, otherwise p-1. This includes the deleted
copy mapping to the retained child. SingletonReductionInterface.lean /
181726-8f796c proves the honest raw N+X=>upper-bound interface.
RootConditionalInterface.lean/job185428-a5469d compiles full C1r from
explicit N AND X; RootConditionalSmall.lean/job185653-ed8b9e compiles
C1r-from-X for <=3 children. These scratch files import the separately
accepted helper oleans cached in this worktree. The original scratch checks
preceded coordinator integration; they are not new registered declarations or a clean
combined-branch check. Failed parsing/elaboration wrappers are retained as
attempt files and recorded in the journal, not counted as math failures.

OneLevelLimits.lean and the four accepted helper scratch/body files retain
reusable proofs. Interfaces.lean checks the reused declarations' standard
axioms. Compiler receipts are under this directory; process exit alone
never grants a registered theorem credit.

## Failed routes and stopping evidence

1. Minimum active chosen-axis capacity fails to select an attaining
   singleton. At(3,4,5),max[1],lower word[S,1L,S,S,1L,S],bound3,
   minimumcup1 occurs atp2/3 but their best singleton value is2; p5 upperc3
   attains3. Job20260930-175945-5d3b66 completed192rows; exact witness and
   receipt are min-active-singleton-smoke.json and its RECEIPT file.
2. Fixed-position lifting through a cut fails even with free root
   orientation/coupling. Same root, outer block[0,2,3],lowerc1 yields
   part[S,2L,S,S,2L,1L],max[1,1]. Its inner singletonp2 lowerc2 has value2;
   outer rest singletonp5 has bound1. Their total3 exceeds every root cut
   atp2 (best2,upperc3), while a DIFFERENT root positionp5 attains3.
   Job20260930-191222-5c7678 completed1root/24eligible outer cuts/360legal
   inner rows with20failures. fixed-leaf-lifting-fixture.json and receipt
   retain all witnesses. This refutes keeping an inductively chosen leaf
   position, not N or C1r. No larger retry will run.

Earlier known negative facts remain binding: unrestricted adjacent
contraction fails; contraction is not closed under parts(P7); same-cut /
same-coupling transport fails(P11); general end-cut normal form is refuted.
No induction may assume any of these false laws. If a future trial is
explicitly authorized, a lifting invariant must allow position as well as
orientation/coupling to reoptimize, and prove the required closure under
actual part histories rather than infer it from root diagnostics.

The asymmetric stress word[1U,S,S,1U,2L,S,S,2L] at(4,4,5),max[1,1]
was NOT a counterexample to N: bound2,best singleton2. Job190636-34c407 /
asymmetric-singleton-witness.json shows the two-run cut1+1 and all24
singleton choices. A nearer old marker can prevent the hypothesized new
outward extension. The incorrect hand prediction is logged and withdrawn.

## Completed diagnostics and remaining job

All arithmetic uses context-bound-zero-children-c-v1 semantics and checked
signed64-bit compiled evaluation. It is diagnostic, not Lean-certified.
The root generators use run lengths1or2 and optional SINGLE markers at
each end; their maximum run counts and global grids are in each output's
saved args. The <=4/5-child counts below do not mean every possible run
length distribution or arbitrary repeated physical markers was tested.

- One-level root N,<=4children:5400k5,10368k6,17640k7 contexts passed;
  endpoint-only versions failed4/6/8. All a/u ranges in saved args.
- Root N at(6,6,7),<=5children:680rows passed in2246.73s,
  job180439-d550b7,singleton-k7-five-scale.json. Do not silently generalize
  this single global pair to all49 global pairs.
- General N at(5,5,6):3888 exact5-child multi-run contexts,<=2markers and
  <=2indexed levels including unused,plusone4-child end-cut fixture;
  job170246-ccbdbe passed3889rows in8236.3s,
  general-singleton-five-k6.json and terminal receipt.
- Three-level balanced / isolated four-child samples passed3072rows each,
  jobs183035-f9cc1b and183722-34c55a,117.63s/189.22s. Only those two shapes.
- Maximum active chosen-axis selector passed5400k5 and10368k6 root rows
  with<=4children, jobs185550-bbee3c and185653-6b55b3. This is a stronger
  unproved candidate; no next trial or k7 expansion is authorized here.

Completed diagnostic20260930-184927-794b43 covers ALL31multi-run placements
of four children and three occupied levels at(5,5,6),all8side patterns,
6orders,64maxima:95232rows. The actual terminal output has complete=true,
checked=total=95232,zero failures; all31distinct placements and exactly
3072rows per checkpoint were verified. Output3935.32s; guarded receipt
3935.7s/334MiB/rc0. Evidence: three-level-singleton-all-placements.json and
RECEIPT.three-level-singleton-all-placements.json. Ten-minute progress
reviews preserved its scope. No new research route was launched after
stopping. All our authorized jobs are terminal. Native host160249-642cc3
and coordinator jobs are not ours to cancel.

## Maintenance, accounting and safest action

CODE-REVIEW.md records Sol's review of ad hoc files, inline job commands,
the tracked X falsifier and inherited-baseline differences. Repeated pure
singleton-cut enumeration was promoted to harness/research/singleton_cuts.py
using the existing part primitive, with catalog semantics/example and frozen
fixture. Ten guarded tests passed192820-7a8919; the exact catalog example
passed192847-4fa726. System-python missing-pytest failure is preserved.
Library changes are committed8fd0a9b8efa3325f492cfb952f810ed9b1b200a4,
guarded job193614-ca9a52. It contains exactly six reviewed library files,
no additional node. False/one-off math stays in artifacts.
The coordinator accepted the five closed helper receipts and registered X
in host/FINISH-REQUEST.json. This acceptance is distinct from the Sol code
self-review; no delegation or other model was used in this run.

Research window2facfcf307994c0f ended with four accepted receipts; review /
maintenance windowfdb41dcc21e94ff4 ended with one accepted helper result.
USAGE.finalization-sync.json has
an all-thread reconciled recorded snapshot, including setup/failures, with
active/later-request caveats. Two local window reports preserve the explicit
split; some setup/transition requests remain outside those window counts.
The host review's import was refused because of existing explicit request
assignments; its zero usage means unavailable accounting, not zero cost.
No matched-baseline savings claim. FACTUAL-HANDOFF.research.json and
FACTUAL-HANDOFF.review.json preserve recorded operations and usage; the
mathematical account above supplies the proof/failure interpretation.

Safest next action: coordinator integration of accepted 95559e09. The
coordinator has prepared R14 for N_root and registration of the explicit
N_root + X conditional; that follow-up is outside this finalization turn.
The fixed-position lifting law remains refuted. This run has stopped; no
new trial is being started.
C1r claim was released partial with this account; RELEASE.c1r.json is the
receipt. Report STUCK; Done remains unmet.
All five helper claims are closed. Preserve the native goal as paused and
incomplete because the original mathematical Done criterion was not met.
No existing statement edits, full extraction,
merge/push, primary-checkout source edits, axioms/native_decide or new trial.
