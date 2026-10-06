# R18 mathematical handoff — active checkpoint

Single authorized Sol gpt-6.1-sol xhigh trial. Part1 complete; ROOT-NF and full
C1r remain open. This checkpoint supersedes historical status entries in
MATHEMATICAL-HANDOFF.history-1658Z.md. No merge/push/delegation/new trial.

Exact target: ctx_bound_child_run_contraction_one_level_root (C1r), legal
3<=k,1<=a,u<=k,1<=m<=k-2, every word letter child or ext1side. Contracting an
adjacent child pair should preserve the recursive context bound.

ROOT-NF fixes global parameters/maxima, retains each end marker's PRESENCE,
uses one child per run, and clamps run count at3 if a=2 or u=2, otherwise2.
Unused indexed maxima remain present. Type hash e0cedb9ee88cc591.

Proof idea and why NF should help:
one old level contributes at most one extension on either endpoint side;
multiplicity does not enlarge the root's direct extension capacity. A normal
word has at most three children, hence bounded recursion. Fresh cut levels
create additional extension paths, so direct endpoint invariance does not prove
recursive saturation. A joint cut-tree/profile invariant must retain the
one-sided Pascal deficit and allow orientation/coupling reoptimization.

Accepted compiling theorem:
ctx_bound_child_run_contraction_one_level_root_of_normal_form,
type fee0a07f9cb0f06, assumes the full ROOT-NF equality for every uniform word
at fixed legal globals/maxima. Closed ctx_num_runs_child_letter_contraction
and unchanged head?/getLast? make the normal words identical.
Branch node/CtxBoundChildRunContractionOneLevelRootOfNormalForm from main
f112ce1d346d150c0c5f9eb85392f0fb4bba5042.
Commit6cc98c1f9dff6d7577cbe424b9756b62a4810149.
Isolated proof job123546-843746 accepted, fixture
3eb196df89e76a83cb10470d2c4906fdb136ead704860a85ca711c4d05abcbdb.
Required targeted check123704-d45ee0 closed,sorry=false,lock_ok=true;
Immutable receipt:
3d7b5f4195ff1e1be384247419ebf66a5a4b7458c63929310201010883e351a9.
Only propext/Quot.sound/Classical.choice. Claim released CLOSED.
C1R-FROM-NF.HANDOFF.md and targeted-check.DONE.RECEIPT.json are authoritative.
Initial proof123406-c2c688 failed record layout; archived/logged, corrected by
tuple constructors without changing statement. No dependency on open NF.

Open ROOT-NF registration:
branch node/CtxOneLevelRootBoundNormalForm from b231fee6ae19ad8623809d48131cdb535234ab01,
commit1223439dd88c35d6c0c6d07b931b6cf528a4b3da.
Registration113638-c3a27f; falsifier114749-eba325 PASS29520/29520 cases;
targeted check115504-d79ec9 expected sorryAx, exact locked type.
Receiptbc5b52889c7c0b1d4b4cb67623c79283814324d90cec0935af7adcf0e863417b.
Falsifier source hash6d3176a4eee019882af95d0ee28de79935a109bea48a11b1358e9f0870fc5185.
Default scope k3/4,all legal globals/maxima,both sides,1..4children, all run
compositions,end multiplicity0/1/2,separator multiplicity1/2.
Zero-child Lean roots have bound0 but C evaluator excludes empty child sets.
No theorem credit from registration or diagnostics.

Actual induction attempt:
ROOT-NF.strong-induction-v2.body.txt uses strong induction on child count with
FULL P(j) for all legal globals/maxima and all j<n. Parts have fewer children,
but have TWO indexed levels, so the root IH cannot be applied to parts directly.
Proper block/rest count decreases are explicit. Raw unit-axis and empty
branches are attempted; single-run equality and lower comparison are separate.
Four explicit holes remain.
Guarded check125255-1249c2 failed parser/namespace errors before mathematical
goals,4.73s556MiB,no budget/OOM. Source/log/receipt under induction-v2.FAILED.*.
Repaired dot layout and Ctx.numRuns_le_length only; type unchanged.
v3 check125444-c8882d failed redundant dsimp,4.77s568MiB.
v4 check130258-3d9d9b reached mathematical traces but failed finite empty-word
indices0/1 and another expression-dot newline,3.44s558MiB. All errors logged.
v5 module compiles successfully with expected four deliberate holes;
unit/empty branches and both strict child-count decreases elaborate.
130509-eaf110 targeted audit DONE rc0,lock_ok=true,typee0cedb9ee88cc591,
expected sorryAx,3.53s575MiB. Immutable receipt
73d81fabca3bb5043788291eb4d2ede4c434a65fda5826087d45e85966754ee1.
ROOT-NF.induction-v5.lean and SUCCESS.compile.log preserve source/trace.
Partial induction COMMITTED e5d95acfad66fe8130afeca86ee94e62283eb226
via131254-fba174,one NF module only. Four open holes, no theorem credit.

Exact unresolved upper obligation for every proper interval blockB and legal
1<=d<=k-2, both
  bound(part B lower d)+bound(part rest upper(k-1-d))<=bound(NF sigma),
  bound(part B upper(k-1-d))+bound(part rest lower d)<=bound(NF sigma).
Closed ctx_bound_le_iff_all_interval_cuts_le exposes these; a full smaller-root
IH needs a sound joint transport across two-level parts.
Lower NF<=source also OPEN. <=3children helper is singleton-cut attainment,
NOT a proved NF base/equality. Single-run descendant normalization requires
children/new markers inside ONE ancestor run and cannot handle multi-run parts.

Failed upper routes (diagnostic, not target refutations):
1. Allow free NF singleton coupling/orientation/component swap and ask component
   domination. Pilot110404-a965df at a=u=k7,m1,L S L S L S L S L:
   source/NF26, interior cut(4,22), NF pairs(16,10),(6,20),(1,25); no domination.
   Full113221-5d305b:3960roots254160cuts,12992 component failures,zero paired
   or NF-equality failures. component-bridge-grid.json.
2. Interior exact normalization passes113438-3fca40:990roots21180parts.
   Only when old markers and omitted children BOTH bracket retained children:
   cap old chosenG at min(G-2,k-m), maxima[c,m]->[c], relabel all nonchildren as
   ext1freshSide. Outer complements unhandled; not a theorem.
3. Absorb old endpoints, trim exterior old letters, relabel internal old markers
   fresh.114206-b197f9:990roots63540cuts,336 component failures.
   a3/u4/k4/m1, L S S L S L S L,keep[2]/lower2:
   actual(0,1),candidate(0,0),NF1. Relabelling creates3 fresh runs on axis2.
   cut-normalization-grid.json; no actual paired failures.
4. Absorb and DELETE all old letters, keeping actual fresh order.
   Both-end grid114501-b24249:990roots63540cuts,zero component/candidate/actual
   failures. Inert-barrier transport unproved.
5. Extend deletion to0/1/2 endpresence with cap min(G-e,k-m).
   Pilot115324-8f3b9b:a=u4/k6/m1,no-end S L S L S L S,keep[0]/upper3:
   actual(2,3),candidate(3,3),NF5. Coarse erasure loses one-sided Pascal deficit.
   Full115602-22d1a0:3960roots254160cuts,zero component failures,
   9720 candidate-sum failures ALL no-end;zero actual sum failures.
   One-end127080cuts/both-end63540cuts pass. All scopes complete; none dropped.
   cut-deletion-allends-grid.json. No-end erasure finite certificate drafted,
   UNREGISTERED/UNCHECKED.

Structural mechanism established diagnostically:
122825-18f2b7, a=u5,k6,m1,root[S,S,1U,S,S],
contracted[S,S,1U,S],NF[S,1U,S],all13.
Same singleton[1]/upper4:(1,12)->(1,9).
Complement [S,1L,2U,S,S]->[S,1L,2U,S],maxima[1,1] is the exact existing
Lean-certified general-C1 counterexample. Hence that failure is REACHABLE as a
part of a legal one-level-root cut. A class of individually contraction-stable
parts closed under all root cuts cannot cover the induction.
Reoptimizing contracted singleton[1]/lower4 rescues(1,12);
NFsingleton[0]/lower3 gives(3,10).
Reachability/parent13/rescue remain diagnostic pending prepared
REACHABLE-PART.signature.txt/body.txt finite certificate. Shared existing
CtxBoundAdjacentLetterContractionCounterexample certifies only the part failure.

Axis-two interpretation, unproved:
opposite globalO=2 gives Boolean bound<=1 using clear-unit-axis potential.
A proper opposite-side part has a fresh physical marker and point capacity0;
a reusable raw part-zero proof should follow from sum-point-base bound.
Only one selected-side path can survive. Single-run root positive iffG>=e+2.
For r>=2 predict positive iff m<=k-3 and G>=e+3+[e=0,r>=3].
Extra thread at no-end>=3runs explains clamp3. Need prove path-minimum invariant,
not merely compare fitted values.
Pilot124520-469ec6 passes128cases0.1886s.
Full124627-f7b5d4 DONE rc0,814.8s/86MiB:50400 legalcontexts k3..7,opposite2,chosen2..k,
m1..k-2,both sides,children1..4,all compositions/end/separator multiplicities.
All50400/50400 complete,0failures; scaling reviewed, no scope dropped.
probe_axis_two_threading.py uses frozen exact NF falsifier root_nf_reference.py.
C diagnostics are not Lean certification.

Infrastructure/recovery:
main inherited19 malformed lock metadata records. Restored exact original R15
committed entries, assert inherited type_hash/type_pp unchanged (376entries).
LOCK-REPAIR.root-nf.json and LOCK-REPAIR.json document branch provenance.
Temporary local8G registration cap restored; shared guard unchanged.
16:07-16:17Z SQLite locked reads/writes; no DB/service mutation. Pending findings
logged after recovery. Admission delay cause unestablished. Initial unstarted
reservations cancelled/replaced only; exact histories in historical handoff.
No full extract: unrelated28.5GiB closure exceeds targeted4GiB ceiling.
Run artifacts ignored by runs/*, so node commits do not include local receipts;
all durable run evidence remains here. No verified callback.

Two-child normal-side formula (UNPROVED): G=chosen global,O=opposite global,
e=endpresence sum, C=min(G-2-[e=2],k-1-m),D=min(G-2-e,k-2-m), natural subtraction.
NF(two children)=max_{1<=d<=k-2}
  baseOf(min(D,k-1-d),O-1,k)+baseOf(C,min(O-2,d),k).
Same-axis fresh singleton threads e+1 markers and old join m+1;
opposite fresh singleton retains old chain1+its outer-end flag. Orientation
selects the lesser outer-end flag. This retains the paired C/D deficit.
Pilot130546-a8e558:256 cases0fail0.00423s.
Grid130659-09192b:18048/18048 legal k3..10 cases,both sides/all endpresence,
0fail0.3223s,job0.5s9MiB. probe_normal_two_formula.py reuses shared C evaluator
and retained enumerate_decomposable_colorings.py::threshold, explicit baseOf.
Normal-side exact symbolic formula is a possible Lean helper; it does not
prove any source paired upper transport.

Existing closed boundary tools newly inspected: ctx_bound_le_one_of_large_sibling_maximum
(indexed max>=k-2 gives all-fuel/full<=1); ctx_bound_le_two_of_small_global_axis_with_indexed_marker
(chosen global<=3 plus actual indexed marker gives<=2). Reuse, do not duplicate.
Fresh-axis2 proper-part zero is prepared in AXIS-TWO-PART-ZERO.* and remains
UNREGISTERED/UNCHECKED. It would discard one branch, not prove path-minimum.

New accepted R18 component:
ctx_part_bound_zero_of_unit_global_axis_and_removed_child,type59d3fffe846cf5be.
Commit298a3661e45f15e7dadc728ee4f9e67b3c949fe7 on its main-based node branch;
registration131505-64042f,isolated132235-01b6f9 accepted,final132328-d90057 CLOSED.
Only standard axioms,lock_ok=true,sorry=false; finalreceipt
1097e9da1c118e5b4d2d2354d580477be12312299c67ea4da64b270baab1547c.
AXIS-TWO-PART-ZERO.HANDOFF.md is concise authoritative component handoff.
Fresh omitted child forces selected chain>=1 and selected global<=2 gives point
limit0; sum-point-base bound gives full0. Arbitrary raw globals/k/maxima/keeps,
positive actual labels. This eliminates the opposite branch of axis-two cuts,
not the surviving path minimum. Claim CLOSED.

Next priority is direct raw single-run NF equality, not finite cut bookkeeping.
Current branch node/CtxOneLevelSingleRunBoundNormalForm from mainf112ce1d,
guarded branch133232-9e78bf DONE. Strict lock recovery376/19 unchangedtypes.
133422-264aca registration RUNNING8G with temporary local tighter cap;
restore config.pre-single-run-registration.toml on terminal before proof/check.
SINGLE-RUN-NF.signature.txt and complete body-v1.txt/no sorry are UNCHECKED.
Proof reuses checked hInterval to fill a contiguous child span, identifies marker
filter nonemptiness with head/getLast flags, preserves sideAt1 including unused
defaultlower, then one-level fold/capacity/base equality. No raw parameter
legality assumptions needed. This would close the single-run induction hole.
Normal-side C/D cut certificate remains deferred/unregistered, no scope dropped.

Wider frozen ROOT-NF diagnostic133422-a41c9d RUNNING2G:157680 k5/6 contexts,
all legal globals/maxima,children1..4,all compositions,endmultiplicity0/1/2,
separators1/2. At25920/157680 in103.8s,zero violations. Pilot133232-1876bf
passed17550 k5<=3child cases in1.304s51MiB. Count-only extrapolation invalid;
child4 is dearer, estimate5-30min and review5. Exact unchanged frozen falsifier.
Earlier3960-root component grid scope is k4/5/6,globals3..k,allm,onlyfive4child
shapes,endpresence0/1,separator1; k7 was a separate high-axis timing witness.
Pending own jobs133422-264aca and133422-a41c9d must be followed to terminal.
C1r claim active; NF released PARTIAL for this helper work, conditional CLOSED.
Own research window
window-bff1ef2d0f4547b3. Review code/library separately before run end.
Research deadline2026-10-02T02:45:22.637741Z; consolidation02:15:22.637741Z,
finalization03:15:22.637741Z. Do not mark goal complete early.
