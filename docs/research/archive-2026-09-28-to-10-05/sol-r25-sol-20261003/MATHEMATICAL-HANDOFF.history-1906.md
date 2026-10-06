# R25 mathematical handoff (live checkpoint)

Status: active, 2026-10-03 18:58 UTC (host clock). No complete BDL proof, no new Lean theorem,
no new compiled proof receipt and no commit. Preserve this goal and its fixed deadline.

## Exact obligation

BDL for all decomposable colorings without a strong k-set. At a root A<<B,
with s=k-1, p=cup(A), t=cap(B), the unresolved ordinary BDL case is
`cap(X)=t` and `p=s-t`, with B having at least three intrinsic bands.
Every maximum t-cap of B strictly surrounds A. It suffices to supply B's
bottom band on one side of A, but preservation of that positional IH is unproved.

The exact sufficient missing lemma is **BRL+**, `BDL-OBSTRUCTION.md` section 33:
given a valid BDL partition of decomposable Y with positive bottom index
s-beta>=1, at least three intrinsic bands and open maximum-cap core `(L*,R*)`,
there is a valid partition in the same
range with its bottom band wholly at or before L*, or wholly at or after R*.
Only one orientation is required. Conditional BRL+ => BDL is proved on paper by
size induction and duality. BRL+ is unproved. The current direction is exchange
between existing partitions, with cup conflicts and termination still unresolved.
Locality has now failed: simultaneous, global changes are necessary for an exchange
from arbitrary supplied partitions. A direct positional induction has since closed
additional uniform root geometries; see sections16,18-20 and the update below.

## Accepted reasoning and receipts

- Audited paper Lemma DS: main checkout
  `runs/claude-audit-667-20261003/AUDITED-PROOF-667.md`, section6.1.
- `BDL-OBSTRUCTION.md` writes the complete ordinary/non-tight/endpoint/positioned
  tight root reduction and its dual. This is a paper reduction, not a complete proof.
- The first-maximum-cap endpoint split proves BDL and separate P choices for any
  one-change coloring with exactly two intrinsic bands. This removes another
  subcase of R uniformly, rather than proving a special numerical instance.
- Uniform conditional positional steps, paper sections16,19,20: cap gain2 uses
  two separated bands; gain1 with an interior lower anchor forces an open upper
  cap core and absorbs the lower remainder into its positioned bottom; retained
  cap gain0 with at most one lower exterior inserts only interior points in the
  next band. Such points cannot be endpoints of a parent maximum cap, so that
  band's cap number drops. Matching child orientation is required for the
  one-exterior gain0 case; with all lower points interior either choice suffices.
- Paper induction map section18: larger pure lower cap maxima propagate childP
  under strict cup gain or non-tight dual absorption. Tight dual absorption needs
  simultaneous bottom-cap/top-cup choices on a child with >=3 bands. Candidate
  Q supplies this if proved; Q has no preservation proof. Remaining split exterior
  anchors and orientation demands must not be silently treated as solved.
- Separately retained common-endpoint Lean lemma: branch
  `node/ContainsCupSetSuccOrContainsCapSetSuccOfOneChangeCommonEndpoint`, commit
  `7806d5c4`. Classical per-band upper: R23 branch
  `node/CardLeChooseOfOneChangeNoCapNoCup`, commit `bad5a94e`.
  Neither branch has been modified/imported into this R25 branch.

## Failed route / reusable observations

Requiring cap-core and cup-core positioning simultaneously is false,
already at a five-point four-cup plus nested upper singleton (cup4,cap3,strong5,
k6). The singleton lies inside both cores and has no allowed band. Actual sibling
cut constraints must be weaker and must record choice tradeoffs.

The universal endpoint split only controls two bands. Requiring a bottom band
to hit every maximum cap would impose the coordinator's already-refuted peel.
BDL can permit maximum chains using several different bands.

The core low-two-band cup hypothesis is refuted: the k7,n27 cap-gate model
was independently reduced to n23, still with cup5,cap5,strong6, a nonempty cap
core and ordinary BDL satisfiable. No partition meets the extra union bound.
The original root has beta=t+1,p=j0+1, precisely the transition where an extra
mixed-cup endpoint survives. The n23 witness is deletion-minimal under the fixed
hypotheses and k, not globally minimal. See section 10 and the retained labels.

Simultaneous low-two cup / high-two cap control is refuted at n7,k5. The
seven-point coloring in section 9.1 cannot be partitioned into one cap and one
cup, which those two conditions would require. Its short paper contradiction
and all 128 independently checked bipartitions support this statement. Both
separate controls remain satisfiable on all 76 joint failures through n7.
These failures show why adjacent-band counts do not control mixed chains and
why choosing a different partition matters; neither is a BDL refutation.

New paper obstructions (BDL-OBSTRUCTION.md sections12-15): a fixed child partition
cannot always extend through R, even with A distributed over all parent bands;
the six-point failure has a one-point child repair. Restricted cap peeling is
false even with an open core, and even when the bottom is essential: the old
n11 witness has a short cap-transversal contradiction. The core interior can
have large cups (uniform nested-upper-pair family), so no local chain budget
comes from its position. A four-point fully occupied partition admits no
one-point valid moves, but a swap aligns its bottom.

Independent exact BRL replay on the n23/n27 CH2 failures and the n11 peel failure
finds both core orientations and both endpoint restrictions. Yet a supplied
n27 partition has neither orientation if original higher-band points keep
their bands; a deletion-minimal n18 witness retains that failure while full
BRL witnesses exist. Low-pair points were allowed to escape into higher bands,
so this is stronger than failure of a lowest-two-bands-only repair. A general
proof must therefore allow coupled exchanges across all bands or construct
a different partition directly. No such global construction has been found.

## Diagnostic evidence

New obstruction sections22-23: scalar Adm_DS is false even for physical
ancestor contexts in its stated >=2-band domain. Vcup3/cap4,strong4 at k6
has intrinsicspan[1,2]. Three nested lower singleton tags allatbottom1
satisfyD1/D2/D3/globalstrong, yet block every free point on both sides;
allVtop violates its four-cap. `adm-ds-failure-certificate.json`, job
`20261003-125213-31de43`,0.00113s, all32assignments/allquadstrong/ordinaryBDL.
General family for every b>=4 (k=b+2) has the same tags, Vcup3/capb,
globalstrongb+1 and no completion; every <=b-1 free-point subset does fit.
Thus bounded tuple feasibility cannot replace chain-extension compatibility.
Representative b5/b6 independent checks `20261003-125625-bdbf25`,0.00684s,
`adm-ds-family-certificate.json`. This refutes Adm_DS, not BDL/BRL/M.
All three ancestors are literal tight R lower-singleton merges, so retaining
their band commitments while descending can produce the obstruction. One
must allow recoloring ancestors or preserve actual matching chain constraints.
Section25 now rules out restricting scalar Adm_DS to>=3 bands. Eight-point V
cup4/cap4/strong5 has a gap with bothsidecap2 and cannot omit its bottom1 at k6.
The short paper contradiction is organized by the cup top band's intersection
with middlepair{3,4}; two outer3cups then force a4cup or4cap in the middleband.
Literal three lower ancestors inserted in that gap give n11 physical context
cup4/cap4/strong5 with all scalar hypotheses and no fixed-tag completion.
Independent all256assignments/allquadstrong/ordinaryBDL certificate
`20261003-132110-e6062c`,0.009505s, raised-floor-failure-certificate.json.
BRL sides/firstlast endpoints are independently retained by replay
`20261003-132332-91146b`,0.017s, allfourchoices onbothinputs. Cupcores are empty;
Q is unaffected by these failures.
Larger RF2 exactprofile `20261003-131933-b7ed1c` also fails atn26,cup6/cap5/strong6
in18.716s/285MiB. No n27 query is needed or commissioned. The eight-point finder
stopped at its first decisive conflict after115.693s; n8 finitecoverage incomplete.
Global endpoint-frontier attempts also fail: pure3cup for actual-lowest-leaf rule,
and four-point {3}<<cup012 for inherited-limit rule. Both pairs reachband1 and
merge into forbidden3chains. Stop this route; sections24-25 explain compatibility.

Section26 gives a general paper closed form for singleton LOWER ancestors all
in one emptyfreegap. If r is their x-orderdepthpermutation, actualcap is
max(betaV,dLeft+LDS(r),dRight+LIS(r),bitonicPeak(r)). Puretags have no valleys;
mixedcaps use one freezone with ordereddepths. Retainingbeta bounds #ancestors
by (beta-dLeft)(beta-dRight), via the classical injectiveLIS/LDS rankpair.
Cup remains freealpha>=3; retainedcap givesstrongmax(freeStrong,beta+1).
For exacttwo-unitdeficits,4taginsertionsmaximum; fourthinside(a,d)collapsescore.
Independent formulaaudit `20261003-133101-9b8202`,6.157s/81MiB, all308cases
(permutations0..5 onV8/V26) agrees. This explainscontextdepth budgets, notBDL.

Section27 constructs ordinaryBDL on the3tagcontext from either childposition
by lifting oneancestor intoband2; actualaudit `20261003-133553-c4f23a`,0.632s,
passesbothV8/V26. Its bottomcrossesparentcapcore, soBRLpreservationstillfails.
Boundaryrequests alternate: insertiond needsrightchildchoice, latera needsleft.

Section28 proves conditionalBDL => Qcountdeficit byaddingclassicalblocks in
emptycap-/cup-core gaps, preservingalpha,beta,strong. Actualaudit
`20261003-134514-056c1b`,0.933s, coversbothprofilesk6n12->14,k7n28->30,
k8samebases->38 with5pointblocks. SuppliedQpartitions extendintoextremecells.
This explainscapacity, notQchoice: anybalancedk7n29bothcoremodelwouldinflate
to31pointswithsamealpha/beta5,strong<=6, violatingordinaryBDLcapacity30.
The two capacityqueries were therefore retired (see operation update below),
with no numerical verdict. Firstinflationadapter `134338-c7f298` failedJSON
stringkeyembedding, v1retained; correctedpilot `134408-d2cdca`0.0148s passed.

Three preliminary jobs failed integer/fixedwidthlabel API contracts:
`20261003-124925-ace3fa`, `20261003-125034-520ae0`, `20261003-125119-8081e4`.
v1-v3 sources and invalidstring artifact remain; no output from these is credited.

- `mechanism-n6.json`: job `20261003-105504-05c55d`, rc0, 0.928s, 11MiB.
- `mechanism-n7.json`: job `20261003-105642-ed2e66`, rc0, 23.034s, 12MiB.
  44,334 admitted roots, all exact paper constructions valid; P supplied by SAT
  in child applications. Thus this does not prove induction preservation.
- `core-prefix-n6.json`: job `20261003-110243-0c2824`, rc0, 626 applicable instances.
- `core-prefix-n7.json`: job `20261003-110400-f7fa1c`, rc0, 11,005 applicable instances.
  Both the prefix cup condition alone and with bottom inside first cap endpoints pass.
- `core-prefix-gate-pilot.json`: job `20261003-110448-db6180`, rc0, 0.226s, 19MiB;
  25 unique cap-gate n11 inputs at alpha=beta4,k6, both candidate forms pass.
- Checkers reuse shared enumeration, coordinator chain clauses and audited profile SAT.
  SAT partitions are independently checked by all-triple subset maxima (small inputs)
  or audited edge DP (larger labeled inputs). UNSAT is diagnostic, not DRAT/Lean certified.
- Original mechanism source is preserved as `check_bdl_mechanism.v1.py`.
- `core-prefix-n8.json`: `20261003-110638-cfc089`, rc0, 756.096s, 29MiB;
  228,823 applicable core-bearing cases passed the subsequently refuted rule.
- `core-prefix-gate-k7-n27-pilot.json`: `20261003-111007-d56ff1`, rc0,
  233.583s, 401MiB; fifth accepted model refutes that rule, first model cost ~218s.
- `prefix-obstruction-independent.json`: `20261003-111711-a726d5`, rc0,
  4.640s, 23MiB; independent edge DP, all-triple clauses and strong-set DS recurrence,
  50 deletion trials. Ordinary BDL SAT, extra condition UNSAT on the retained n23.
- `pair-compatibility-n7.json`: `20261003-111141-fd7360`, rc0, 6.872s;
  10,110 applicable instances, 76 joint failures and both separate rules SAT.
- `pair-obstruction-independent.json`: `20261003-111711-59390b`, rc0;
  independent decomposition and exhaustive 128-bipartition certificate.
- `20261003-110639-ea05c9` failed on assuming profile cap bounds imply an actual
  nonempty core; failing model was not retained. Corrected actual-core filter
  `20261003-110756-ea0ac4` completed 25 accepted n18 models with 3 discarded.
- `20261003-111238-dc0656` failed on an F30 core assertion before writing results.
  Corrected replay `20261003-111414-96de32` checked five U29 inputs (pass) and
  excluded five F30 inputs (empty core). Both original adapters remain as v1 sources;
  do not read failed runs as negative evidence for a mathematical statement.
- Fixed-child E pilot: `20261003-113113-80fbcc`, rc0,0.022s;
  independent all729 parent assignments and all-quad strong check:
  `20261003-113338-7a1bdb`, rc0,0.004s, `fixed-extension-independent.json`.
  First independent replay `20261003-113241-ff67a0` failed syntax before execution;
  its source snapshot remains `recheck_fixed_extension.v1.py`.
- Actual cores of old peel failures: `20261003-114042-ee7521`, rc0,0.004s.
  `core-peel-failure-certificate.json`: `20261003-114201-0e4ed9`, rc0,0.007s;
  all205 cap candidates, all40 max caps, both positioned partitions and strong5.
- Exact BRL/endpoint hard-input replay: `20261003-114847-38c372`, rc0,1.681s,
  `brl-hard-input-replay.json`. It does not prove the general lemma.
- Reduced frozen-upper obstruction: `20261003-115000-04e158`, rc0,2.903s,
  `frozen-realignment-reduced.json`, n18,k7,cup5,cap5,strong6,core(6,10),45 trials.
  Deletion-minimal at fixed k under valid supplied bands and actual hypotheses;
  full P witnesses retained, both fixed-upper orientations UNSAT diagnostically.
- Constructive capgain2/Q pilot `20261003-115741-ea8db7`,0.610s; n7
  `20261003-115832-ec2692`,15.275s,Q10,110 instances allfour side pairs pass.
- Actual gain0/gain1/gain2 operations through n7: `20261003-120911-02d706`,
 3.157s, `positional-exterior-n7.json`. Child P is supplied by SAT where the
  paper lemma assumes it. This does not prove general P or Q.
- Hostile Q source replay `20261003-120111-100bbe`,1.429s, and positional
  assertions/exclusion reasons `20261003-120241-3a7766`,1.320s:
  frozen n18 supports allfour pairs;638 unique oldFF failures outsideQ,
 24 duplicates; source hashes retained. No large eligible corpus was supplied.

## Operations to inspect first on resume

Host `20261003-104816-63f404`; native thread
`01a1023c-c35d-7cd0-8ab1-3018afeb70aa`; researcher
`codex:agent-run-78d7135402e34729`; usage window `window-b668d2eb270d4a73`.
Claim `ErdosSzekeres.decomposableStateUpper_all`; research branch
`research/r25-bdl-20261003`, baseline `d63b3fb8`. The old context route stays open.
Actual positional n8 `20261003-121409-49dc22` is terminal rc0,136.400s,28MiB:
gain2 29148, anchored gain1 4487, matching gain0 13899 valid each orientation.
Q-only n8 `20261003-121835-a458a4` is terminal rc0,531.820s,28MiB:212,990
eligible instances through n8, allfour pairs SAT. Counts are diagnostic only.
Capacity pilot `20261003-123046-7241ae` is terminal rc0,0.122s: both k6,n12
profiles yield actual alpha=beta4,strong5 and open cores with joint witnesses.
Boundary k6,n13 job `20261003-123127-49274c` is terminal rc0,0.096s: both
profiles UNSAT, diagnostic only. Upper-only k7,n20 `20261003-123247-6ddd3b`
gives ineligible actual cap4 models, correctly excluded. Exact-maximum pilot
`20261003-123435-c1d817` gives eligible alpha=beta5,strong6,open-core models
and allfour Qwitnesses in1.396s. Do not assert existence using lr_vars:
its implication is one-way. New adapter selects an all-triple monochromatic
subset with at least the required length; global upper bounds make it exact.
Exact saturation job `20261003-123526-b2881a` finished18.602s/442MiB: both
profiles have actual cup=cap5,strong6,open cores atn28 and Qwitnesses. Pending
k7,n29 exact-capacity boundary job `20261003-123638-8b81d1`: first3min review
found common-cut still solving after0.453s encoding;0of2profiles complete.
Unknown UNSAT ETA; subsequent18min review kept fullqueryrunning duringfixedcut
calibration. Latest17:23 review:47min,0/2profiles complete; nextreview17:38UTC.
Fixedcut14 n28 pilot
`20261003-125625-bc71b8` finished10.029s (solve8.560s/19564conflicts), automatic
10000-conflict progress chunks resume correctly untilterminal. Pending n29cut14
pilot `20261003-125750-914085` measuresUNSATcost and givescumulativestats:
at1527s225chunks/2,250,186conflicts, no verdict. Nextreview17:38UTC.
Two attempts hit UNSAT search exhaustion; no more SAT shards commissioned.
Global whole-set endpoint peeling pilots `20261003-130912-3089c7` and
`20261003-131008-fb6edf` refute both deterministic frontier rules; no more variants.
All other commoncuts9..13 and separatedprofiles stay open untilfullcoverage.
**Operation update17:47:** both n29queries `20261003-123638-8b81d1` and
`20261003-125750-914085` were cancelled after section28 changed their mathematical
purpose. Workeracknowledged killedrc-15; fullquery0profiles complete after~70min,
cut14last2935s/351chunks/3,510,309conflicts. Outputs terminal=false withnoverdict
remainpreserved; noSAT/UNSATcredit. Memorypeaknotrecordedforcancelledscopes.
All n29commoncuts andseparatedprofile existence remainopen asBDLfalsification
questions. No childcomputation pending; host/nativegoalactive. Q itself remains
unproved/unrefuted, and a counttest cannotdistinguishit fromordinaryBDLtruth.
Positioned bottom/top cells have cap/cup limits lowered by one. For balanced
alpha=beta=k-2 this loses two vertices of classical capacity; n13 at k6 would
refute Q if both cores can stay open. This is a structural compatibility test,
not an attempt to claim progress from another small numerical confirmation.
The host and native goal remain active. Inspect exact status on resumption.
No queued submission counts as completion.

Keep PROGRESS.md and this handoff current. Do not register or formalize BDL until
its full paper proof is complete and logged. Consolidation starts at
`2026-10-04T02:18:19.108264Z`, research ends at `02:48:19.108264Z`.


## Active checkpoint 18:10 UTC

The general proof idea remains conditional BRL realignment plus DS size induction.
No terminating exchange or complete contextual invariant is known. Paper sections
29-31 add a maximal-counter closed-core reduction and exact weighted LOWER-ancestor
profiles. The latter explains the difference between scalar chain budgets and
compatible band assignments; it yields a fixed-bottom failure at every bottom
index p>=1 (two bands), alongside the existing genuine three-band RF2 obstruction.

Guarded audit20261003-140344-57b55a completed0.095829s/12MiB;
block-depth-formula.json checks six nonsingleton depth orders and independently
certifies p2,beta6,n14,strong8, all256 fixed-bottom failures and ordinary BDL.
EP+ first-endpoint cup bound was immediately rejected by the existing section13
cap-transversal contradiction; queued140522-e9ac94 was canceled without execution,
rc130, no coverage/result. No child job remains pending; the R25 host and native
goal remain active with the original deadline. No Lean theorem or receipt is new.

Current unresolved structural question: construct a compatible array of free-cell
left/right cap deficits across bands, or a global BRL realignment. Ordered context
profiles compute how those deficits are consumed, but do not guarantee such an
array exists. Coordinator PSL-sep explores related one-colour profile induction;
do not duplicate blind context tests. End-of-run code review/maintenance still due.


## Active checkpoint 18:22 UTC: BRL+ and a global-label alternative

The original proof route now needs only BRL+ (paper section33): positive bottom
s-beta>=1, >=3 intrinsic bands, supplied BDL partition and open maximum-cap core.
BRL+ => all-parameter BDL is proved conditionally by DS size induction; every
BRL+ profile is realizable as a difficult retained-cap child. Realignment remains
unproved. No Lean theorem, receipt, statement registration or commit.

A global common-window compression of classical endpoint-rank staircase words
is refuted on six points, with an independent direct-chain/quad/tree certificate:
common-window-failure-certificate.json, jobs141242-4edb49 and141339-9272b3.
The weaker WM matching asks for distinct representatives among each point's
length(s-1) windows. This would prove the Theorem8 count directly but does not
give BDL band bounds. Its exact missing general lemma is Hall expansion on
every subset of the actual whole-set word family. There is no proof of that
expansion or a compositional invariant; September rank-state collisions prevent
assuming child word states suffice.

WM passes all11900 applicable states through n7 (142026-034cda,2.688s), plus
five previously certified near-capacity models including both k7 n28 profiles
(141749-cf69f3,0.0912s). These are mechanism diagnostics, not theorem credit.
Pending guarded n8 job20261003-142217-7cc776, estimated95s,2G,review2min,
checkpoints every250 colorings. Inspect and report it first on resume. Native
R25 goal/host remains active; original deadlines unchanged. End-of-run code
review and maintenance remains due, including reused generic matching code.


## Active checkpoint 18:58 UTC: certified failures and root interpretation

BRL+ (paper section33) is unproved and unrefuted. The current proof idea is the
conditional DS size induction plus global bottom realignment. No compatible
exchange invariant or termination proof is known. No new Lean theorem/receipt,
registered statement, tracked source change or commit. Earlier pending-job notes
are chronological only; every R25 child job listed below is now terminal.

WM is refuted by the exactly saturated n8,cup=cap=strong4 example (section35).
Points1..7 have just six possible length3 classical windows. Independent
all-monochromatic-subset ranks, tree, all-quad strong and ordinary BDL replay:
142541-d10a75,0.006795s/10MiB, window-matching-failure-certificate.json.
Stop common/flexible classical-window variants after these two failures.

The exact suffix-conditioned pair-rank formulas (section37) explain the existing
compiled matrix collision: child cap pair(5,8) has the same unconditioned rank,
but after first-point cut1 its rank is3/2 and the parent rank becomes4/3.
Audit143035-b92ab3,0.010131s/10MiB, checks240 cut/pair/color entries on each
witness; tail-pair-root-audit.json. This is a closed n-dependent state, without
an exact k-only count proof.

Uniform endpoint and root facts are paper sections36,38-40. A first-endpoint set
can retain the full strong number with positive bottom and an open cap core.
Audit143726-1d9578,0.004460s/10MiB, endpoint-paper-facts.json. Root cuts are
successor-closed vertex sets; their SCC order has width<=2 even for arbitrary
complete triple colorings. All roots are unions of at most two principal
reachability sets. Pure algorithm fixtures144848-d62ee3,0.044589s/6MiB,
root-graph-primitive-fixtures.json, compare every arbitrary coloring through n5.

NC changing-roots shortcut is false: an n8 set has exactly two roots, both hard
R or dual R, although ordinary BDL exists. Audit144249-133f80,0.002053s/11MiB,
root-choice-audit.json. SourceDef cap-deficit normal form is uniformly false:
for beta>=4, a beta-cap below an outer pair, with a lower singleton in its core,
has a source SCC containing the full beta-cap and exactly one valid hard root.
Independent beta4 audit145623-f3fc50,0.000484s/10MiB,
one-sided-root-obstruction.json. Earlier145555-208afa failed on coincident
upper-pair leaf addresses, produced no result; v1 preserved. Stop fitted root
normal-form variants. Polynomial root enumeration is reusable, not a BDL proof.

Next: independently review the complete conditional BDL root reduction and its
exact hypotheses; review/promote reusable root enumeration in a separate usage
window. Only configured Sol is allowed, so no independent Astra/model review is
claimed. The native goal/host retain the original 02:18 consolidation and02:48
research deadlines; no early completion. Count-probe n29 coverage remains open.
