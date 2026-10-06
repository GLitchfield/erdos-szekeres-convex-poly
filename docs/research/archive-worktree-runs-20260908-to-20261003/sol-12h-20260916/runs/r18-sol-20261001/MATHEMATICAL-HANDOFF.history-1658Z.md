# R18 mathematical checkpoint — active, not a final result

**Latest at16:31Z:** NF registration committed
1223439dd88c35d6c0c6d07b931b6cf528a4b3da (commit121740-3688ff DONE rc0), remains
OPEN. Current independent conditional branch starts at guidance-only current
mainf112ce1d346d150c0c5f9eb85392f0fb4bba5042 (branch122253-07cc63 DONE rc0).
Metadata repair replayed376/19 with all inherited statement types unchanged;
LOCK-REPAIR.root-nf.json preserves first branch provenance. Conditional
registration122417-9ed2ef RUNNING8G, tighter temporary LOCAL cap restored before
commit. Module build successful3325jobs with expected sorry; five-minute review
estimated3-5min remaining, no timeout. SQLite lock cleared16:17Z; pending findings
logged. --include runs artifacts are ignored by runs/*, so NF commit has only the
five node/import/lock/falsifier/result files. Durable artifacts remain local.

Full erasure classification115602-22d1a0 finished complete rc2,88.4s,
3960roots/254160cuts. Zero component upper failures;9720candidate-sum failures
ALL in no-end class(63540cuts). One-end127080cuts/both-end63540cuts have zero
failures; zero actual-pair failures throughout. Transport remains unproved.

**Current proof idea and structural lesson:** use a JOINT extension-profile/cut-tree
invariant with coupling/orientation reoptimization. One old level threads at most
one marker on each endpoint side, so extra children/runs supply no new ROOT
extension count. This alone does not control fresh-level histories. Separate
old-history erasure discards a paired Pascal deficit, the common upper obstacle.
NF's<=3child normal side reduces its own recursion to bounded depth, but source
cut transport remains open. Counts of helper nodes/commits are bookkeeping.

Fixed mechanism probe122825-18f2b7 DONE rc0,0.0067s:
a=u5,k6,m1,source[S,S,1U,S,S],contracted[S,S,1U,S],NF[S,1U,S] allbound13.
Same singleton[1]/upper4 cut gives(1,12)->(1,9). Complement is the exact known
general-C1 failure[S,1L,2U,S,S]->[S,1L,2U,S],maxima[1,1]. This failure is therefore
REACHABLE from a legal one-level-root cut; an individually contraction-stable
class closed under all such cuts is impossible. Contracted singleton[1]/lower4
rescues(1,12); NFsingleton[0]/lower3 gives(3,10). Parent13/reachability/compensation
here are diagnostic; the general-C1 component failure is already Lean-certified.
Evidence reachable-contraction-failure.json/.STATUS.json. REACHABLE-PART.signature/
body.txt prepares a finite certificate but is UNREGISTERED/UNCHECKED. Pause
scalar transport variants; this is a structural mechanism test, not another trial.

ROOT-NF.strong-induction-v2.body.txt now exposes exact paired upper goals via
the closed all-interval-cuts certificate, proves proper part child counts<n, and
retains FULL P(j) for all j<n, changed legal globals/maxima. Unit/empty branches,
single-run base and lower inequality are separated. Four explicit holes remain,
no compilation receipt yet. Requested actual guarded compiler attempt is still
pending after the conditional proof. Full ROOT-NF/C1r remain open.

**Superseding checkpoint at2026-10-01T16:12Z:** the registration/falsifier/check
states below are historical. Registration113638-c3a27f DONE rc0, exact type
e0cedb9ee88cc591; falsifier114749-eba325 DONE rc0/pass29520cases,zero violations;
check115504-d79ec9 DONE rc0, targeted=true,lock_ok=true,sorry=true,standard axioms
plus expected sorryAx. Immutable detail bc5b52889c7c0b1d4b4cb67623c79283814324d90cec0935af7adcf0e863417b
is copied to check-root-nf.DONE.RECEIPT.json. ROOT-NF remains OPEN. No commit
yet. See ROOT-NF.registration.md for current receipts. Database-lock failures
at16:07Z are preserved in INFRASTRUCTURE-PENDING-20261001T1607Z.md; es log retries
also failed. No database/worker mutation was attempted. Temporary8G cap restored.

The third candidate's extension to0/1/2old ends, absorbingG into min(G-e,k-m),
FAILS paired sharpness. Pilot115324-8f3b9b rc2 at a=u4/k6/m1:4endpoint patterns,
288cuts,zero component failures,36candidate-sum failures,zero actual failures.
Only NO-END stratum fails. Source S L S L S L S,keep[0]/upper3 gives
actual(2,3),candidate(3,3),NF5: coarse erasure loses a one-sided Pascal deficit.
Evidence cut-deletion-allends-timing.json/.STATUS.json. Full classification job
115602-22d1a0 submitted2G; no log/output yet, terminal state uncertain due lock.
Keep0-end coverage open. Two consecutive transport proposals have failed at the
same paired upper obligation; actual strong-induction body is still UNCHECKED,
so the requested formal attempt must precede a Stuck(full) report.

NO-END-ERASURE.signature.txt/body.txt propose a tiny kernel obstruction:
a=u4,k6,m1,word S L S has bound5; its upper3 first-child part2 and lower2
last-child part3 attain5, whereas erased singleton candidates give3+3=6.
This is not registered/proved and does not refute ROOT-NF. It uses ordinary
decide+kernel, never native_decide. Search found no matching declaration.

Endpoint-invisibility pilot115040-03f806:48contexts0.22s,run counts1..4,
k5/7,a=u=k,m1,both sides. Both ends give all bounds26/4;0/1end give31/7.
This agrees with COORDINATOR-NOTE.md but proves no general invariance.
T(7,5,7)=26, not16; an apparent tension was an incorrect threshold comparison
and was explicitly corrected in the shared log.

Next remains: save terminal check status/log and commit NF registration; create
conditional branch FROM MAIN, replay inherited lock repair, register/prove/check/
commit conditional C1r; return NF branch and guard-compile the strong induction.
The <=3children helper is singleton-cut attainment, NOT a proved NF base.
The lower inequality NFbound<=sourcebound remains open as well as both paired
upper inequalities. No R18 accepted theorem or commit yet.

Single authorized Sol/xhigh trial. Done(narrowing)=NO; Done(full)=NO.
Research deadline2026-10-02T02:45:22.637741Z, consolidation02:15:22.637741Z.
No merge, push, delegation, primary source changes, full extract or existing statement edits.

## Exact target and current branch

Target C1r: ctx_bound_child_run_contraction_one_level_root, legal3<=k,
1<=a,u<=k,1<=m<=k-2, all letters child or ext1side. Contracting an adjacent
child pair should preserve bound. Parent is claimed under
codex:agent-run-cd0185da75604d4f (forced because its existing N_root/X dependencies
remain open). Those parallel nodes are untouched.

ROOT-NF candidate retains each end-marker's presence, uses one child per run,
and clamps run count at3 if a=2 or u=2, otherwise2. Exact signature is in
registration job20261001-105328-1501d7. The axis-two change is explicitly authorized
in the brief. Zero-child words are allowed by the Lean signature and have zero
bound; diagnostic C evaluation excludes them because its API requires a child.

Independent branch node/CtxOneLevelRootBoundNormalForm is based on
main b231fee6ae19ad8623809d48131cdb535234ab01, created by
job20261001-104610-520d32 DONE rc0. No R18 theorem is accepted or committed yet.
ROOT-NF registration20261001-113638-c3a27f is DONE rc0 (476.9s2306MiB), lock
e0cedb9ee88cc591. Targeted falsifier20261001-114749-eba325 is queued4G.
The conjecture remains sorry; its claim is gated on falsifier pass. Temporary local8G
build cap was restored to the original config. Earlier failed storage/memory receipts
are preserved under register-root-nf/, including the exact terminal successful receipt.

## Current induction upper transport findings (diagnostic only)

First candidate: each two-level source cut component is dominated by a matching NF
singleton-cut component, allowing arbitrary NF coupling/orientation/component exchange.
False: a=u=k=7,m=1, L S L S L S L S L, interior upper4 part pair(4,22);
source/NF bounds26, no NF pair dominates both. Pilot20261001-110404-a965df.
Full grid20261001-113221-5d305b:3960 roots/254160 cuts,12992 component failures,
zero actual paired-sum or NF-equality failures. component-bridge-grid.json has witnesses.

Interior-only exact normalization: if old markers and omitted source children both
bracket all retained children, absorb old-side global G into min(G-2,k-m), truncate
maxima[c,m] to[c], and relabel every nonchild ext1 freshSide. Grid20261001-113438-3fca40
checks990 roots/21180 interior parts, zero failures. This is not proved and does not
handle outer complements. Evidence interior-normalization-grid.json.

Second paired upper route applied absorption to all interval parts and complements,
deleted the two exterior old letters, and relabelled remaining old letters as fresh.
False: grid20261001-114206-b197f9 (990 roots/63540 cuts) has336 component failures.
a3/u4/k4/m1, lower L S S L S L S L, keep[2]/lower2 gives actual(0,1), proposed(0,0),
NFbound1. Adding fresh markers creates3 runs after the old global becomes2, losing
the original complement's unit bound. cut-normalization-grid.json preserves witnesses.
No actual paired sum exceeded NF, so this does not refute ROOT-NF.

Third candidate deletes ALL physical older markers after the same global absorption,
retaining actual fresh markers and child order. Same full grid20261001-114501-b24249
passes all990 roots/63540 cuts: zero component, candidate-pair or actual-pair failures.
Evidence cut-deletion-grid.json and STATUS.json;21.1s126MiB. This is a plausible
inert-barrier transport obligation, not a theorem. R16's arbitrary inert-barrier
larger-axis upper obstruction may remain relevant. Exact candidate implementations
are in probe_interior_normalization.py and probe_cut_normalization.py; executed
prior variants are preserved under timing-v1/relabel-v1 names.

The main missing upper inequalities remain, for every proper interval block B and
1<=d<=k-2, bound(part B lower d)+bound(part rest upper(k-1-d))<=bound(NF sigma),
and the swapped orientation. A full smaller-root ROOT-NF IH cannot apply to two-level
parts until a transport is proved. ROOT-NF.strong-induction-v1.body.txt is still unchecked.

## Accepted facts and evidence

Existing ctx_num_runs_child_letter_contraction is CLOSED, locked87d38cf7fc07a108,
standard axioms. Together with unchanged head?/getLast? after contraction it
should make the normal words identical. Draft conditional body
C1R-FROM-NF.body.txt has no compiler/proof receipt yet.

Timing job20261001-104924-5eb924 DONE rc0, root-nf-timing.json:
four fixed roots agree with the proposed NF; k4 fourchildren0.0116s,
k5 fourchildren0.0181s, axis-two0.0163s, k6 fivechildren0.4138s.
Semantics context-bound-zero-children-c-v1; diagnostic, no Lean credit.
Falsifier harness/falsifiers/ctx_one_level_root_normal_form.py reuses the shared
compiled evaluator. Default family29520contexts: k3/4, alllegalglobals/maxima,
bothsides,1..4children, endmultiplicities0..2, separators1..2. Not run yet.

Read-only R16 evidence: CLOSED global-end singleton counterexample
aad0cd4939df89e219189c4372b9e629a5f2950e, raw a2/u3/k4/m1 and SSLSS,
sourcebound1/global-end cuts0/inner extreme run-end cut1. Lower comparisons must
allow inner extreme run ends. This does not refute ROOT-NF, N_ends or N_root.

## Exact induction obstruction and attempts still required

For a one-level rootσ and smaller-child ROOT-NF hypotheses, every proper
interval blockB and legalcouplingd must satisfy both paired inequalities

    bound(σ.part B lower d) + bound(σ.part rest upper(k-1-d)) <= bound(NFσ),
    bound(σ.part B upper(k-1-d)) + bound(σ.part rest lower d) <= bound(NFσ).

The closed all-interval-cuts characterization makes these the upper obligation.
Proper parts have fewer children but TWO indexed external levels. A part lying
inside one ancestor run can use ctx_single_run_descendant_bound_normalize and
then the one-level IH. Parts spanning multiple ancestor runs do not satisfy that
normalizer's contiguous-child premise; applying the one-level IH directly would
be invalid. A weaker paired comparison or valid two-level domination is needed.
No two completed R18 attempts at this obligation yet; do not report Stuck(full)
merely from this structural observation.

R16 HANDOFF.larger-axis-upper-stuck.md separately records failed relaxations:
at A5/G7/k7, rank triples56 exceed requiredT26; scalar normalized charges30/27
exceedT26 although actual cuts are<=26. These are diagnostic failures of charge
estimates, not target refutations and not R18 attempts. Its isolated-child
external deletion lemma requires WellFormed, isolated children and a retained
same-level marker; arbitrary inert-barrier deletion/run merging is not available.

## Infrastructure recovery and pending work

Main inherited malformed statements.lock. Nineteen metadata records were
restored from their exact original accepted R15 commits, all376 inherited
type_hash/type_pp fields asserted unchanged. LOCK-REPAIR.json,
repair_inherited_lock.py, statements.lock.inherited-corrupt and
statements.lock.repaired preserve recovery. Initial two-record repair detected
another malformed record before any lock write; recovery then inventoried all.
This is metadata repair only, not Lean statement edits/new approval.

Registration20261001-105019-bc8776 (20G) was cancelled only while unstarted,
terminalkilledrc130, to replace its reservation with8G for identical scope.
Replacement20261001-105328-1501d7 is QUEUED; continue exact job waits.
Fresh shared admission diagnostic40G/max2/no budget problem, no resourceleases;
outsideworkerPID4531 startedSep30. Cause of queue delays is not established.
Resource reconcile released nothing; no worker/service/primary changes attempted.
R16/R17 jobs also queued/running and remain outside this run's control.

Next: inspect registration output; targeted falsify/check and es node commit
ROOT-NF; independent main branch for the conditional reduction, targeted check
and es node commit. Then conduct and log the strong-induction comparison
attempts. Preserve exact sources, failures and any two-level witness family.
No callback is verified; submission is not completion and the reporting turn
must remain open while its authorized jobs are pending.
