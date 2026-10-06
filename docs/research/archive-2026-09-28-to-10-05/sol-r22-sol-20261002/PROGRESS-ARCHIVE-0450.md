# R22 progress

Updated 2026-10-03T04:50Z. Agent `codex:agent-run-c94853b9754648ba`;
thread `01a0fefb-d883-7cc1-8d31-dc8f00948974`;
usage window `window-27233773101944d1`.

Research deadline: 2026-10-03T11:38:33.055867Z. Consolidation begins at
2026-10-03T11:08:33.055867Z. No delegation, merge, push, or cherry-pick.
Baseline `6e4d0e66274e9d3dd1ccdbacf9fd747deb5e1d14` is preserved.

## Current authoritative state

Both exact requested lower gates are ACCEPTED and committed. The diagonal
full check `20261003-002634-6a5ff2` confirms hash87bbef437ea7141f,
CLOSED, no sorry and standard axioms only (1284.1s, peak5670MiB).
Commit `5d4fa26d8a20192c90624b23ed8a9cef90af8dd1`; capture fixture
`7ac8e061d29029089b5b7affd65d074b1d2527edf7510f17aeff910d85acf26f`.
See `DIAGONAL-GATE-HANDOFF.md` for the accepted proof and receipts.
Optional upper dual gates and final separate review remain; research
continues until the fixed deadline. No mathematical obstruction remains
for either requested lower gate. Earlier progress below is historical
and superseded by this paragraph.

## Historical progress

Exact diagonal gate SOURCE compiles first try without placeholders in
**20261003-002559-692f37**. Full original-source check
**20261003-002634-6a5ff2** is live,28G,review20min, estimated25-35min;
receipt `diag-gate-full-check.json`. Keep following until terminal and
inspect exact locked hash87bbef437ea7141f/axioms before theorem credit.
Current branch `node/SingletonLowerPascalTailGateFiveDiagOfSixLeOfInputs`,
claim active. Own original scaffold preserved at
`research/r22-diagonal-scaffold-20261003`; R21 branches intact.
Proof reservoirG+1 contradicts accepted rootG with exact explicit inputs.
After acceptance: capture/commit/release, optional upper dual gates,
separate final mathematical/code review and usage maintenance.

Full diagonal root boundG=choose(k-1,2)+choose(k-3,2)+1 is ACCEPTED by
original-source **20261003-002306-951371**, exact hashca9484d7726e5e53,
no sorry, standard axioms only, audit25decls clean. Receipt
`diag-root-original-source-receipt.json`; fixture
fba350d418a52a4a3f83afb5a08d86a93289c06420ac136bb4f63414ceb71a2b.
Commit **2bce9cc2f6b0b99005852f82285bf7ce35f56940**, job20261003-002458-d553be.
All root orientations and k6 residual case are certified.
Next is the exact diagonal gate wrapper: reservoirG+1 contradicts rootG.
The gate itself remains open pending proof and full original-source check.

Diagonal R2 prefix/suffix bound is ACCEPTED by original-source check
**20261003-001609-4350b7**, exact hashf04035ea5e0888c4, no sorry,
standard axioms only, audit24decls clean; receipt
`r2diag-original-source-receipt.json`. Fixture
ae034b2e79968d06de570327adaf3ee78a4f3c416b4d864057713cbe8295dfc7.
Commit **d73bb74dc4068b0163c2e17ce82f54ca9f136123**, job20261003-001758-222c5d.
Next is the full diagonal deep-root bound, using
predecessor child bound plus accepted R1/R2 and fixed-k explicit inputs.
The exact diagonal gate remains open.

Adjacent-pair three-cup extremal deficit3k-6 is ACCEPTED by original-source
check **20261003-000935-deaead**, exact hashcb2c65ddc64176bc, no sorry,
standard axioms only, audit23decls clean. Receipt
`deficit-original-source-receipt.json`. Fixture
9dfafc8ae5441b56cd6c33d4b81f389697b5a9c2101ba398a6d6857a01c91c46.
Commit **63858d9e73769ac2de02a7e5312ad7b94c642c24**, job20261003-001158-321cf8.
Next R2 prefix/suffix bound groups lower child by its
position in the two original blocks. The diagonal root and gate remain open.

R1 decomposable three-cup bound3k-8 is ACCEPTED by original-source check
**20261003-000353-78b053**, locked hash126eea55ed06ad2b, no sorry,
standard axioms only, audit22decls clean. Receipts `r1-check-job.json`,
`r1-original-source-receipt.json`. Fixture
6766a2b6e9dbb194137d3b0acb1fe492e7811d7ac19096aeddfa97266befb8e5.
Commit **edd0792efd9360a3045dbc99d3e4dd0f36f77b7a**, job
20261003-000601-7191c3. Current branch
`node/ThreeCupBlocksCardLeOfDecomposableNoCapFourNoStrongOfPairBound`.
Next is extremal adjacent-pair deficit3k-6: violating it forces cup sizes
k-1,k-3,k-1, whose boundary turns should force a strong k-polygon.
The diagonal target still needs this, R2, its root bound and wrapper.

The exact predecessor gate is accepted and committed as
`0281d8bbf6ec782323840a4c2643153a648124fb` (commit job
`20261002-231745-d44e7a`), and its claim was released closed.
Full original-source check `20261002-223942-093363` accepted the unchanged
locked type hash `d717e6e0c539a549`, no sorry, standard axioms only; changed
audit passed. Proof capture `20261002-231408-260326` saved fixture
`e86015cb7af73eca2deba396c8f52527ee0c0efd73d5904efbc2d4f2cf0cc4e4`.
Reservoir H+1 contradicts the certified genuine deep-root bound H.

Current branch is `node/DeepSplitTwoEndpointExtensions`.
Full diagonal registration job **20261002-231841-9c4a9c** completed rc0,
1488.1s,peak5647MiB. Exact locked type hash **87bbef437ea7141f**;
OPEN/ready, no theorem credit. Scaffold commit
**89ff2f9db358e708a6120ab146ae016026f977ca**, commitjob
**20261002-234358-f3743a**. The20min review retained full coverage.
Receipts `diag-registration.json` and `diag-registration-job.json`.
Next work is the thin Z-prime helper and structural diagonal toolkit.
Z-prime is ACCEPTED by original-source check **20261002-234842-f12d34**,
locked hash596228c998f557ed,CLOSED,no sorry, standard axioms only, audit
clean. Its126-line source compiled first try. Receipt
`zprime-original-source-receipt.json`; commit
**7dfceae54b23364066f9cf5894e7a7812c0dbb42**, released closed. Fixture
68fd8f4b97ba6c5ef2c3dd35152394d0e15b414d9087d702b1b00da5d26e3431.
The maximum-prefix transfer forces any new4cap to yield an mCup or5cap;
the m2 base follows because every two-point set is a cup.
Simultaneous endpoint extensions are ACCEPTED by original-source check
**20261002-235448-9f5cae**, exact hash c0597e18a9e9b81e, no sorry,
standard axioms only; receipt `endpoint-original-source-receipt.json`.
Committed **710a3245135450e7fe2274abe9809dd29fa7b292**. Next is the
decomposable three-cup bound 3k-8 using chosen lower points and supplied
uniform two-cup count; the diagonal gate remains open.
The signature has uniform R20 cupblock and exact R21 Baek bounds as inputs.
No diagonal theorem is accepted yet. Its proof idea groups child roots by
lower points lying in the cup prefix, the four-cap-free suffix, or both.
Concrete cap witnesses then give the cup deficit needed by the classic
triangular/square bounds. The remaining obstruction is checking the
decomposable three-cup and prefix/suffix bounds and their extremal deficit;
all planned cases remain in `DIAGONAL-PROOF-PLAN.md`.

The following sections preserve earlier research history and are superseded
by this current state where they describe old pending work.

## Historical target and proof idea

First prove `singletonLowerPascalTailGate_five_pred_of_six_le`, following
`AUDITED-PROOF-5k1k.md`. Its reservoir is
`choose (k-1) 2 + choose (k-3) 2 + 1`.
The root split couples the maximum lower cup and maximum upper cap through
a strong polygon. Cap extension forces the upper child to be one, two, or
three cups, or a cup followed by a four-cap-free set. The classic Z bound
controls the lower child. Two sharp cases need more structure: the marker
lemma for a singleton upper child, and the R2 row-defect lemma for N2e.
The R2 obligation is now certified: triangular equality fills the two top
cup-start rows, whose free edges force a common-endpoint strong polygon;
maximum-prefix transfer gives the full two-block bound. Marker WE, its count,
and arbitrary-set reflection are accepted and committed. The full nonempty
deep-root bound is accepted by original-source check20261002-223031-d2569c,
hashcc7ef1f85cc93f23, no sorry, standard axioms only. Its concrete cap coupling,
endpoint gains, and one reversal certify every audited root case. Root commit
`00b7765074fc4ac92787c64c29b0d0bb5c393b81`, released closed. The exact gate
wrapper compiles in guarded job20261002-223458-865799, peak804MiB; full
original-source check20261002-223942-093363 accepted with explicit28G cap:
exact hashd717e6e0c539a549, closed, no sorry, standard axioms only, audit pass.
Full job1930s peak5630MiB; independent #check/#print axioms230948-97c159 agrees.
Capturejob20261002-231408-260326 running; commit/release next.
Earlier asynccheck223527-b81836 failed in reservation/fallback sizing, so
the unchanged source was rerun with full extraction support. The diagonal proof
remains open; the gate reservoir is exactly one point larger than this bound.

At the full check's20-minute checkpoint, the exact extractor was100%CPU
and RSS~14.7GiB, nearly flat and below28G. No item counter is emitted;
remaining time is estimated3-10min from the prior~23min full registration.
Both progress reviews were recorded; the full check subsequently completed.
DIAGONAL-PROOF-PLAN.md saves the structural regrouping and all residual cases.

Then prove the diagonal five gate with the exact R20 cupblock and R21 Baek
statements as explicit hypotheses; derive the dual gates if time permits.

## Evidence and current state

- Read AGENTS.md, the reviewed RESEARCH-BRIEF.md, and both audited proofs in full.
- Worktree initially clean on `research/r22-gate5-20261002`; R21 branches intact.
- Initial `es status --brief --full`: 404 closed, 25 open, 2 refuted; no stale warning.
- The exact predecessor gate is now registered and ready; it remains open.
- `es search` found finite reservoir identities and the existing four-diagonal
  arithmetic. Direct source search subsequently found `reverseColor` and its
  transports in StructuralChargingTransport; no generic one-change cup layer
  theorem has been found.
- Exact R20 and R21 signatures read from the authorized integration worktree.
- Threshold identity is Lean-certified, with standard axioms and no sorry:
  `decomposableThreshold_five_pred_of_six_le`. Original-source receipt:
  `threshold-original-source-receipt.json`, job `20261002-200926-c93a70`.
  The three-entry window reflects to indices 3,2,1 and two Pascal identities
  leave exactly the audited two triangular terms after subtracting the tail.
  This removes the reservoir arithmetic obligation, not the geometric gate.
  Committed as `3fd98a53102fb29be7a0aa9371a8ff360341584e`. Ignored runs
  artifacts were omitted by node commit despite --include; they remain durable
  workspace evidence, and the release preserved the handoff immutably.
  Open scaffold checkpoint:
  `0fc5f65658103bf09c620a7b4e2c1ae78b55e1a1`.
- General chain principle `isMonochromaticSet_of_oneChange_consecutive` is
  Lean-certified by original-source check `20261002-201424-e60b93`, no sorry,
  standard axioms only; receipt `chain-original-source-receipt.json`.
  Outer-span induction fixes two outer colours, so one-change fixes the inner
  turn. This supplies the audited basic chain fact for arbitrary one-change sets.
  Minimum insertion and the longest-cup-start layer invariant come next.
  Chain commit `5f6ef102f051df86df505b01dddfe74713b8ec12`.
  Chain source fixture `4dd81f81dd66550aae6af30fe37d3d138535c01e6090b1145aa89e085616badd`.

## Pending work

Finish the classic Z, marker and R2 toolkit, then the full root analysis. All
Lean/compiler work uses guarded jobs. Threshold arithmetic and audited Lemma1
are already certified.

- Branch creation job `20261002-194017-3e657e`: done, rc 0;
  current branch `node/SingletonLowerPascalTailGateFivePredOfSixLe`.
- Targeted registration job `20261002-194037-ed7bdc`: failed, rc 3;
  the exact statement elaborated, but its 28.4 GiB import closure exceeds the
  4.0 GiB targeted extraction ceiling. Scaffold remains, no lock yet.
- Full registration job `20261002-194139-818f71`: done rc0, 23 minutes,
  peak5618MiB. Reviews at 23:51Z and 00:02Z left healthy CPU-bound extraction
  running. The final statement lock is written; no theorem credit.
- Scaffold commit job `20261002-200548-a5929e`: done rc0, sha above.
- Branch job `20261002-200613-cbf4bd`: done rc0, creates
  `node/DecomposableThresholdFivePredOfSixLe` for the arithmetic helper.
- Arithmetic registration `20261002-200641-5e7a12`: done rc0 in2m.
- Original-source arithmetic check `20261002-200926-c93a70`: done rc0,
  build4.1s, peak574MiB, statement lock matches; incremental index updated.
- Minimum insertion registration `20261002-201658-0ce60a` on
  `node/MonochromaticSetInsertMinOfOneChange`: completed rc0 in3m.
  Its review raced completion; final outputs were inspected.
- Minimum insertion check `20261002-202056-2a21cf`: done rc0,
  hash `e71a2eb6309d502d`, no sorry, standard axioms only. It certifies the
  new consecutive triple x,a,b, then uses the generic chain principle.
  Commit job `20261002-202233-7e2be6` done rc0;
  commit `b99e7c6a27f98b4e2898fde52a1409d05bf3313c`.
- Layer registration `20261002-202311-6ec7b1` done rc0 in2m on
  `node/ExistsCupStartLayersOfOneChangeNoCapFour`. Claimed; full proof draft
  first check `20261002-202634-880072` failed: equality versus order in the
  singleton witness; pinned API is card_insert_of_notMem; empty-row target
  needed an explicit change. These were corrected, retry checking as
  `20261002-202802-6baa6f`, which succeeded: hash `c6db8e8bf151a0ab`, no
  sorry, standard axioms only, build3.98s peak581MiB. Full original-source
  receipt `layers-original-source-receipt.json`, artifact
  `6bc3595a14001f53aa2abae3cea94f3513c10525a995355857b45320382d568e`.
  Audit passes. The structural part of audited Lemma1 is certified; the
  triangular fibre sum is next. Both full gates remain open.
  Layer commit `ff5d00e0a9d98496d624bcd2d60f18fe640c3ab0`.
- Triangular count registration `20261002-203138-ec5e51` done rc0 on
  `node/CardLeChooseOfOneChangeNoCapFourNoCup`. Checks `20261002-203455-7136d6`
  and `20261002-203808-9bfdea` failed on the cup restriction namespace and
  the literal binomial index normal form. Corrected both; check
  `20261002-203942-a9faee` succeeded: hash `5bd4ab7b285da66a`, no sorry,
  standard axioms only, closed layer dependency. Build4.01s peak564MiB.
  Receipt `triangle-original-source-receipt.json`, axiom audit passes.
  Audited Lemma1 count is certified for arbitrary one-change sets.
  Commit `ed1ab1e938b732ad9cbbcb206262902ab5f10491`; source fixture
  `905bc2f156f3cdc7fa3cd19c222d747b13a708fed2dd4efb207e0c7f5c0253be`.
- Maximum insertion registration `20261002-204238-4b43dd` done rc0 in2m on
  `node/MonochromaticSetInsertMaxOfOneChange`, cap4G peak2311MiB.
  Its mirrored chain proof is certified by `20261002-204618-c8d838`:
  hash `ebd3b03f70e15ea8`, no sorry, standard axioms only, exact lock match.
  Receipt `max-insertion-original-source-receipt.json`; fixture
  `04a564c9fa235471611871cac80d728958eccc148c49ad8cc722bce5ce3b49b1`.
  Commit `f3a4ee2ed813d7f976da4aaafbc1bb6d88a603ff`; claim released closed.
- Classic Z node registration `20261002-205130-53d52d` completed rc0 under4G,
  peak2318MiB, exact hash `f31fe859cac77f54`. Current branch
  `node/CardLeSquareOfOneChangeGapNoCapFiveNoCup`; claimed through08:54EDT.
  First check `20261002-205519-35f5ff` failed on two reversed subset
  compositions, corrected after full log inspection. Check
  `20261002-205626-776dc7` certified the exact theorem with no sorry and only
  standard axioms, build6.185s peak596MiB. Receipt
  `z-original-source-receipt.json`; audited Lemma2 is accepted.
  Commit `a3b09728c66eb7833e9275d159030a4066048226`; fixture
  `ffb1896efd6e36fde57a2dbf9fda908f1ba713d8109482c3845146a831a6c295`.
- Two-cup count and extension registration `20261002-205836-d94aaa` is live,
  cap4G, on its own node branch. This formalizes all of audited Lemma3.
  Registration and original-source check `20261002-210208-7c5bde` now accepted:
  hash `dac186281844e9ad`, no sorry, only standard axioms, exact lock match.
  Build5.017s peak583MiB; receipt `two-cup-original-source-receipt.json`.
  Both boundary turns cannot be caps; an extending cup turn supplies the
  one-point saving and forces the opposite extension from a full u-1 block.
  Commit `5ce54df044c0160b48ba20da7d5fe08251ec65fe`; fixture
  `6b0a7a9fa4f2fe7651b1da648d34f9f0917e667475cee74054265a956cfe2ab0`.
- Three-cup registration `20261002-210446-af4b64` live, cap4G, on
  `node/ThreeCupBlocksCardLeOfOneChangeNoCapFourNoCup`. This targets audited
  Lemma4; both exceptional outer cases use the accepted two-cup contracts
  and maximum insertion to glue the middle cup's extreme extensions.
  Registered exact hash `e64ec02518bfa43a`; first check
  `20261002-210827-ffb1e7` failed on one missing explicit finset argument.
  Corrected; original-source retry `20261002-210928-06ce7e` accepted, no sorry,
  standard axioms only, lock match and audit pass; build4.678s peak617MiB.
  Receipt `three-cup-original-source-receipt.json`; audited Lemma4 certified.
  Commit `854bc9a693c76064f71503d900a191d31d0ed393`; fixture
  `8ad212aadef63702422fc82de960376bcacd3f0031f210a637df45effae9e7f5`.
- Cap-three equivalence registration `20261002-211150-f6ea14` live, cap4G,
  on `node/IsCupSetIffNotContainsCapSetThree`. This elementary bridge turns
  WE into a cup and converts cap-rank at most two into cupness in the root cases.
  Registration exact hash `87c897e89483d3ac`; claim through09:13EDT.
  Checks `20261002-211412-8abe71` and `20261002-211531-28571d` failed on Fin3
  witness construction. The actual chain API was re-read; a unique increasing
  triple argument replaces finite-case enumeration. Third check
  `20261002-211644-f4a3ba` accepted with no sorry, standard axioms only,
  exact lock match and audit pass. Build5.284s peak611MiB; receipt
  `cap-three-original-source-receipt.json`. The increasing triple invariant
  avoids numeric finite-case normalization. No one-change assumption needed.
  Commit `57ef543bdbf508e8bee75b2fda88f78b595cc70d`; fixture
  `a2e6a2ef7d3e50b16e05f3a220d46c28f0f37d0ae1d576dcf45b9cc00dc1b8d7`.
- Common-endpoint cup/cap union bridge registered as
  `20261002-211904-fc26d5`, exact hash `375bee3caa99c512`, claimed09:21UTC.
  Original-source full proof checks as `20261002-212236-2c909e`, cap4G.
  It seeks both strong union and exact two-endpoint intersection; no credit yet.
  First two checks `20261002-212236-2c909e` and `20261002-212400-47e0a2`
  failed on layout syntax, corrected without mathematical changes. Third
  check `20261002-212520-09e65f` accepted with no sorry, standard axioms,
  exact lock match, incremental extraction and audit pass; build10.648s peak591MiB.
  Receipt `common-endpoint-original-source-receipt.json`. Both strong union
  and two-endpoint intersection are now certified. Next the sharp R2 prefix-row deficit,
  then the independent marker WE obligation and the root analysis.
  Bridge commit `99f267eb7e6e56a8cd21b60dbfe2e338a862cca3`; fixture
  `aced0f514aaad0491c6fcdf925960a8f88e0b9042ce67d1c6f1a59790251af81`.
- Sharp ordered-prefix R2 row deficit registration `20261002-212811-4856c9`
  completed, exact hash `939b6726111fb00e`, claimed through09:30EDT on
  `node/CardLtChooseOfOrderedCupPrefixNoCapFiveNoCupNoStrong`.
  Diagnostic stage1 build `20261002-213217-ddc58d` passed (default cap30G).
  Stage2 default build `20261002-213723-f11ba6` was cancelled before starting
  because its reservation conflicted with a coordinator 28G job; the same
  source compiled through guarded 4G job `20261002-213806-60be09`, peak520MiB.
  Stage3 `20261002-213927-4efe05` passed, peak540MiB. Main sorry remains;
  no theorem credit. Triangular equality, the equal-row free-edge argument,
  first-point and last-point ordering, and all boundary cap turns now compile.
  The final two common-endpoint strong-set cases remain next.
  Final sharp proof check `20261002-214148-c53cc9` failed only on a removed
  witness name in one span-bound branch. Corrected original-source check
  `20261002-214344-43e174` accepted: no sorry, standard axioms only, exact
  hash939b6726111fb00e, lock match, audit pass; build7.8372s peak669MiB.
  Receipt `sharp-r2-original-source-receipt.json`, source fixture
  `1567809f8c64fde19467f16757891eac65bea86cf4abcc53daf67a36a3b562aa`.
  Commit `9ad68fa5187f5ffb808a9508ec549364d73553ab`; released closed.
- Full R2 wrapper registered by `20261002-214623-7b33ba`, exact hash
  `917aaf2dd72226f1`, claimed through09:48EDT on its own node branch.
  Full proof is filled; original-source check `20261002-215002-8fec9c` live.
  It transfers a full prefix maximum to the suffix and eliminates a new
  four-cap by the cup/five-cap joining-turn dichotomy. No wrapper credit yet.
  Wrapper check accepted: no sorry, standard axioms, lock match, audit pass;
  build4.3283s peak618MiB, receipt `r2-wrapper-original-source-receipt.json`.
  Commit `952a08289a37981529522c8fc5f0014f4d2dc27c`; released closed.
- Marker WE registration `20261002-215241-b916ea` live, cap4G. It keeps the
  missing cap gap q distinct from the straddled cup marker h. Endpoint-family
  three-caps force opposing crossing four-caps; one-change then contradicts
  saturated-cup straddling. The shorter S4iii proof appends two points to a
  cup with its last point deleted, already giving m+1 points.
  WE accepted first full proof by `20261002-215945-d7ec0d`: hashff022500197d4701,
  no sorry, standard axioms, lock match, audit pass; build7.9475s peak689MiB.
  Receipt `marker-we-original-source-receipt.json`, fixture
  `e623eeff61d72ade16f1f0bf827ac695f0d9a7a13d1ba8f352203dd64623053d`,
  commit `5032fb505a6d24d09893fffe3f556c99a2e7fb1b`; released closed.
- Marker count registered by `20261002-220251-1109a7`, hashbdd23fc3926df984,
  claimed through10:05EDT. Complete endpoint families and deletion-square
  proof filled. First check20261002-220609-79e82e failed in final arithmetic
  rewriting only; corrected check20261002-220733-46c796 live. No count credit yet.
  Corrected check accepted: no sorry, standard axioms, lock match, audit pass;
  build4.1772s peak574MiB. Receipt `marker-count-original-source-receipt.json`,
  fixture `7a04ebad6c1c9652902bbf04859724a3e8faa16d3360ae7719369df80ec4b645`,
  commit `2659861326db48a56037a6b248395c55bad2b1f3`; released closed.
- Arbitrary-set reflection registration `20261002-220954-3f0989` live, cap4G,
  on `node/ReverseColorSetInvariants`. It will preserve one-change, cup/cap/strong
  sets and containment, deep splits with the same labels, and decomposability.
  The order involution makes mirrored root cases instances of one argument.
  The rank contract includes attained longest-cup-start
  witnesses, maximality, and cup layers of cardinality at most their index.

Diagnostics `20261002-195609-49714f` and `20261002-195649-323e53` both
completed with rc 0. The latter shows the active Lean extractor at 99.9% CPU
and 14m19s CPU time, with the guarded scope around 5.6 GB memory. This is
CPU-bound declaration processing, not a detected memory stall or deadlock.
The uninstrumented processing phase eventually completed. Evidence:
registration-process.txt and registration-subtree.txt in this directory.

The unchanged registered gate scaffold is saved. Arithmetic and the shared
chain/layer toolkit are certified on separate helper branches. Thin-import
helpers avoid re-extracting the large gate closure. The full gate remains
open; the geometric bound toolkit will support both priorities. Authorized
read-only R20 inspection found the intended general chain argument as its
local H1. Expose it here using outer-span induction for either colour.

SEARCHES.md records pre-proof searches. Available usage was synced to the
host research window at 23:49Z (49 responses imported; a reconciled snapshot).

Host job: `20261002-193828-be3769` (the native goal host, not a proof check).
