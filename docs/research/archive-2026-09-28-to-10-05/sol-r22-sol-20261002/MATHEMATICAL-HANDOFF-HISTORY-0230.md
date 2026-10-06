# R22 mathematical handoff (living document)

Updated 2026-10-03T02:15Z. Research is active, not finished.

Current first action on resumption: finish reflection capture/commit/release,
then register the full predecessor root cardinal bound. Reflection check
20261002-221407-728240 accepted first draft: hash493d24070fe3ae02, no sorry,
standard axioms, lock match and audit pass; build3.3251s peak602MiB. Receipt
`reflection-original-source-receipt.json`, artifact
`3f9fea4ef432d825023ce010e06ee82a1f6011c23042f4701bd11c1e788fb924`.
All nine arbitrary-set equivalences are certified. Reflection registration
20261002-220954-3f0989 complete, hash493d24070fe3ae02, claim10:11EDT.
Staged diagnostics20261002-221220-cddba3 (peak455MiB) and
20261002-221312-7c31a2 (peak462MiB) passed with final placeholder retained,
verifying all forward invariants. Full no-placeholder equivalences are filled
using one generic involutive predicate transport. No reflection theorem credit yet.
Marker-count capture/commit/release
complete, commit `2659861326db48a56037a6b248395c55bad2b1f3`, fixture
`7a04ebad6c1c9652902bbf04859724a3e8faa16d3360ae7719369df80ec4b645`.
Original-source check20261002-220733-46c796 accepted:
hashbdd23fc3926df984, no sorry, standard axioms, lock match and audit pass;
build4.1772s peak574MiB. Receipt `marker-count-original-source-receipt.json`,
artifact `9071ad14867a7218e3a74c5c8221e62352dff71a0a0510bf845d80efcbf457ec`.
The complete-family deletion plus square bound certifies audited Lemma5 count.
Registration
20261002-220251-1109a7 complete, hashbdd23fc3926df984, claimed through10:05EDT.
Full proof is filled. First check20261002-220609-79e82e failed only in the
final arithmetic identity because a reverse rewrite also changed a nested
subtraction. Replaced with ring then forward rewrite; full failure
`marker-count-first-compiler-failure.json`, build4.0280s peak603MiB.
No marker-count theorem credit yet. Next arbitrary-set reflection, then
the exact decomposable root bound and original gate.
WE commit/release complete,
commit `5032fb505a6d24d09893fffe3f556c99a2e7fb1b`.
WE original-source check20261002-215945-d7ec0d accepted on
first final draft, no sorry, standard axioms only, lock match and audit pass;
build7.9475s peak689MiB. Receipt `marker-we-original-source-receipt.json`,
artifact `e645249c8a9e98d78859c6a316ab6f7344a77b403e54b8a54ee26254f3661060`,
fixture `e623eeff61d72ade16f1f0bf827ac695f0d9a7a13d1ba8f352203dd64623053d`.
Both the S4iii two-point shortcut and all final turn cases are certified.
Marker WE registration20261002-215241-b916ea complete,
exact hashff022500197d4701, claimed through09:55EDT. Full proof is filled.
Diagnostics stage1 `20261002-215604-e520ef` peak499MiB, stage2
`20261002-215738-0511be` peak523MiB, stage3 `20261002-215811-4b80d4`
peak534MiB all passed with the final placeholder retained. They verify
endpoint extraction, S1, crossing four-caps, S4 and both X lemmas. Final
three-case contradiction is now written; no marker theorem credit yet.
The deprecated push_neg warning was removed using push Not syntax.
Wrapper capture/commit/release complete,
commit `952a08289a37981529522c8fc5f0014f4d2dc27c`, fixture
`12a3ddd52c551d0cb7f8da1fc188bf58c985a203b8c155c22f7df10c47413de8`.
Wrapper original-source check20261002-215002-8fec9c
accepted first draft: hash917aaf2dd72226f1, no sorry, standard axioms only,
lock match, audit pass; build4.3283s peak618MiB. Receipt
`r2-wrapper-original-source-receipt.json`, artifact
`5ada49f9d8f8820e3355f598854b29b24fcabbe0c8b7d811b214d0ce0b3d9d20`.
The three prefix-length cases and maximum transfer certify full audited R2.
Sharp R2 commit/release complete:
`9ad68fa5187f5ffb808a9508ec549364d73553ab`, fixture
`1567809f8c64fde19467f16757891eac65bea86cf4abcc53daf67a36a3b562aa`.
Sharp R2 original-source check
`20261002-214344-43e174` accepted: exact hash939b6726111fb00e, no sorry,
standard axioms only, lock match, build7.8372s peak669MiB; receipt
`sharp-r2-original-source-receipt.json` and artifact
`5f7b5937fa0fd3d99b9e8ad4dbf6193229f775d672e19f7905e8a46852e93cd6`.
Both common-endpoint contradiction cases are certified. Its first full
check failed only because `rcases ... with rfl` removed witness name z from
one span-bound branch. Corrected using z<g1<=gl; durable failure
`sharp-r2-first-compiler-failure.json`, full build12.0567s peak697MiB.
Earlier staged diagnostics `20261002-213217-ddc58d`,
`20261002-213806-60be09` (peak520MiB), and `20261002-213927-4efe05`
(peak540MiB) all passed with the final Blueprint placeholder retained.
Default build `20261002-213723-f11ba6` was cancelled while queued because
its30G reservation conflicted with a coordinator28G reservation; the same
source was checked by guarded4G job `20261002-213806-60be09`, no dropped
coverage. The exact sharp helper remains uncredited until its final receipt.

## Exact obligations

1. `singletonLowerPascalTailGate_five_pred_of_six_le {k : ℕ}
   (hk : 6 ≤ k) : SingletonLowerPascalTailGate 5 (k - 1) k`.
2. The diagonal five gate with the uniform R20 cupblock theorem and exact R21
   Baek bound as explicit hypotheses, on baseline `6e4d0e66`.
3. Optional colour-dual upper gates.

## Accepted results and receipts

Accepted: `decomposableThreshold_five_pred_of_six_le`, exact type hash
`fbf5bbaf1dea45ac`; check `20261002-200926-c93a70`, sorry=false and only
propext/Classical.choice/Quot.sound. Receipt:
`threshold-original-source-receipt.json`. Expanding the three-entry window
proves the audited reservoir arithmetic. No geometric bound follows yet.
Commit: `3fd98a53102fb29be7a0aa9371a8ff360341584e`. The runs receipt and
search record are durable local evidence; node commit omitted ignored paths
despite --include. Release preserved this handoff as immutable harness artifact
`99cf6cb991c753b5391f90da098ea9ce2d106869661d4d0ab4a3e9d5fd3ed876`.
Threshold source fixture:
`10f971b44cde5b47d1667678101ade3a2573a53b71844e584118bdb4ae9b6ad9`.

Accepted: `isMonochromaticSet_of_oneChange_consecutive`, hash
`f2f0b04ce9926768`; original-source check `20261002-201424-e60b93`,
sorry=false and the same three standard axioms only. Receipt:
`chain-original-source-receipt.json`. Outer-span induction fixes the outer
four-point colours; one-change then propagates the desired colour. This
certifies the general chain principle needed for cup/cap extension, without
assuming realizability. Next establish minimum insertion and cup-start rows.
Chain commit `5f6ef102f051df86df505b01dddfe74713b8ec12`; source fixture
`4dd81f81dd66550aae6af30fe37d3d138535c01e6090b1145aa89e085616badd`.

Accepted: `monochromaticSet_insert_min_of_oneChange`, hash `e71a2eb6309d502d`;
original-source check `20261002-202056-2a21cf`, no sorry, three standard axioms
only, closed chain dependency. Receipt `min-insertion-original-source-receipt.json`.
The only new consecutive triple is the new point followed by the first pair.
Commit `b99e7c6a27f98b4e2898fde52a1409d05bf3313c`; source fixture
`8d04d5d0f6f84f4b92788fe584a81e9b6bf3ec474df3b3f9aac82cca1f55e958`.

Accepted: `exists_cupStartLayers_of_oneChange_no_capFour`, hash
`c6db8e8bf151a0ab`. Original-source check `20261002-202802-6baa6f`;
full receipt artifact `6bc3595a14001f53aa2abae3cea94f3513c10525a995355857b45320382d568e`
and `layers-original-source-receipt.json`: no sorry, three standard axioms,
closed insertion dependency; build3.98s peak581MiB. Finite supremum attains a
longest cup starting at every point. Equal-rank cap triples force a four-cap
using the first edge of a longest cup at the third point; hence rows are cups.
The row's minimum starts that entire cup, giving its sharp cardinality bound.
This certifies the structural part of audited Lemma1, ready for a fibre sum.
Layer commit `ff5d00e0a9d98496d624bcd2d60f18fe640c3ab0`; source fixture
`de74cb9be3b7926f2a749d901d6d28fe7778a67bc33c624161e7ede1b284cb57`.

Accepted: `card_le_choose_of_oneChange_no_capFour_no_cup`, hash
`5bd4ab7b285da66a`; original-source check `20261002-203942-a9faee`, no sorry,
three standard axioms only, closed layer dependency, build4.01s peak564MiB.
Receipt `triangle-original-source-receipt.json`. Attained ranks below v
partition s into cup fibers of size at most their rank; the triangular sum
is choose v2. This certifies the count in audited Lemma1 for arbitrary
one-change sets, without realizability. Next maximum insertion and Lemma2 Z.
Count commit `ed1ab1e938b732ad9cbbcb206262902ab5f10491`; source fixture
`905bc2f156f3cdc7fa3cd19c222d747b13a708fed2dd4efb207e0c7f5c0253be`.

Accepted: `monochromaticSet_insert_max_of_oneChange`, hash `ebd3b03f70e15ea8`;
original-source check `20261002-204618-c8d838`, no sorry, standard axioms only,
exact lock match, closed chain dependency, build6.20s peak564MiB. Receipt
`max-insertion-original-source-receipt.json`; fixture
`04a564c9fa235471611871cac80d728958eccc148c49ad8cc722bce5ce3b49b1`.
The sole new consecutive triple is the old last pair followed by the new point.
Commit `f3a4ee2ed813d7f976da4aaafbc1bb6d88a603ff`.

Accepted: `card_le_square_of_oneChange_gap_no_capFive_no_cup`, hash
`f31fe859cac77f54`. Original-source check `20261002-205626-776dc7`, no sorry,
standard axioms only, exact lock match and axiom audit pass; build6.185s
peak596MiB. Receipt `z-original-source-receipt.json`, artifact
`f30d2295f22a869096473ff2f9daf3632781dd730a523e7feff2c4796eaf45e1`.
The four-cap first points lie left of the missing gap and cannot contain a
(v-1)-cup: either joining turn creates a forbidden v-cup or five-cap. Their
complement has no four-cap. The two triangular bounds sum to (v-1)^2.
This certifies audited Lemma2 without realizability or decomposability.
Commit `a3b09728c66eb7833e9275d159030a4066048226`; fixture
`ffb1896efd6e36fde57a2dbf9fda908f1ba713d8109482c3845146a831a6c295`.

Accepted: `twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup`,
hash `dac186281844e9ad`; original-source check `20261002-210208-7c5bde` passed
on its first draft. No sorry, standard axioms only, lock match, axiom audit
pass; build5.017s peak583MiB. Receipt `two-cup-original-source-receipt.json`,
artifact `abb6146048e90308997ff1febe21559a6bf13e428e2a370e55a4318999666c88`.
It certifies all three audited Lemma3 parts: count<=2u-3, boundary extension
dichotomy, and the opposite extension forced by a full u-1 block. Two cap
boundary turns make a four-cap; the cup turn permits insertion. Empty and
one-point cases are handled explicitly.
Commit `5ce54df044c0160b48ba20da7d5fe08251ec65fe`; fixture
`6b0a7a9fa4f2fe7651b1da648d34f9f0917e667475cee74054265a956cfe2ab0`.

Accepted: `threeCupBlocks_card_le_of_oneChange_no_capFour_no_cup`, exact hash
`e64ec02518bfa43a`. Original-source check `20261002-210928-06ce7e`, no sorry,
standard axioms only, lock matches, closed two-cup and maximum-insertion
dependencies, audit pass; build4.678s peak617MiB. Receipt
`three-cup-original-source-receipt.json`, artifact
`070ca8137bc89c103116d7fddc09bdba31157c816b399bb6b7c99f8bd124883f`.
Full middle block saves two using separated cup extensions. Outer-full
exceptional cases force an impossible two-block count or a u-cup glued
through Q by maximum insertion. This certifies audited Lemma4.
Commit `854bc9a693c76064f71503d900a191d31d0ed393`; fixture
`8ad212aadef63702422fc82de960376bcacd3f0031f210a637df45effae9e7f5`.

Accepted: `isCupSet_iff_not_containsCapSet_three`, exact hash
`87c897e89483d3ac`; original-source check `20261002-211644-f4a3ba`, no sorry,
standard axioms only, lock match, incremental extraction and audit pass;
build5.284s peak611MiB. Receipt `cap-three-original-source-receipt.json`.
The unique increasing triple in Fin3 has indices012; a cap-coloured triple
supplies a three-cap witness, and any three-cap conflicts with ambient cupness.
No one-change hypothesis is needed. This certifies the no-three-cap part of F1.
Commit `57ef543bdbf508e8bee75b2fda88f78b595cc70d`; fixture
`a2e6a2ef7d3e50b16e05f3a220d46c28f0f37d0ae1d576dcf45b9cc00dc1b8d7`.

Accepted: `isStrongPolygonSet_union_of_cup_cap_common_extremes`, exact hash
`375bee3caa99c512`; original-source check `20261002-212520-09e65f`, no sorry,
only standard axioms, lock matches, incremental extraction and audit pass;
build10.648s peak591MiB. Receipt `common-endpoint-original-source-receipt.json`.
A cup and cap sharing distinct extrema have intersection exactly those two
points. Anchor colours at l,x,r assign every interior point its membership
colour; boundary one-change and adjacent-change rules force every triple
from its middle. Hence the union obeys the strong law. This certifies the
audited F2 bridge required for the exact R2 strong(m+1)-set assembly.
Commit `99f267eb7e6e56a8cd21b60dbfe2e338a862cca3`; fixture
`aced0f514aaad0491c6fcdf925960a8f88e0b9042ce67d1c6f1a59790251af81`.

The target is registered and ready,
with unchanged sorry. Its open scaffold checkpoint is
`0fc5f65658103bf09c620a7b4e2c1ae78b55e1a1` (job `20261002-200548-a5929e`).

The already accepted baseline tools include root split exposure, cup/cap
extension, split cup-cap strongness, the one-change law, and the gap-side
no-cap reduction. `reverseColor` and its univ containment transports exist
in StructuralChargingTransport.

## Proof idea and remaining obstacles

The audited predecessor proof controls the lower root child by the classic Z
bound after coupling its largest cup with an upper-child cap. Endpoint cap
extension constrains the upper child to cup blocks. Sharp exceptional cases
are the marker WE lemma (singleton upper child) and the R2 row-defect Lemma C
(cup followed by a four-cap-free set). The threshold arithmetic, generic chain,
minimum insertion, cup-start layer invariant and triangular count are certified.
Maximum insertion, classic Z, two-cup and three-cup lemmas are certified;
next R2 defect, marker WE and
the eleven-case root analysis. Both supplied audits
are paper evidence, not Lean receipts.

The diagonal proof reuses the predecessor theorem at the same k, and adds
the decomposable three-cup and R2 lemmas. It must retain these exact inputs:

```
hblocks : ∀ k, 5 ≤ k → DiagonalCupBlocksForce4kk k
hbaek : ∀ {n k : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)},
  3 ≤ k → OneChangeOn χ s → ¬ContainsCapSet χ s 4 →
  ¬ContainsStrongPolygonSet χ s k → s.card ≤ 1 + Nat.choose (k - 1) 2
```

## Failed attempts and infrastructure

Common-endpoint checks `20261002-212236-2c909e` and
`20261002-212400-47e0a2` failed on proof layout: multiline by/using
applications inside an And constructor, then newline immediately after dot
field notation. Both replaced by explicit constructor branches and namespace
rule applications. Evidence `common-endpoint-first-compiler-failure.json`
(8.8389s,596MiB) and `common-endpoint-second-compiler-failure.json`
(8.1866s,573MiB). Mathematical middle-colour invariant unchanged.

Cap-three checks `20261002-211412-8abe71` and `20261002-211531-28571d`
failed. First fin_cases/try omega left five unordered numeric Fin3 branches.
A mistaken API diagnosis led to an invalid conversion through f.lt_iff_lt;
reading Sweep.lean:235 corrected it: source index inequalities are already
the chain hypothesis. Current proof uses the unique increasing Fin3 triple
invariant i=0,j=1,k=2, by Fin.ext/omega before substitution. Pending third
check. Failures `cap-three-first-compiler-failure.json` (4.178s,600MiB) and
`cap-three-second-compiler-failure.json` (4.2768s,606MiB). The wrong image-order
explanation and inaccurate statistics were explicitly corrected in es log.

Three-cup first check `20261002-210827-ffb1e7` failed only on the missing
explicit finset argument to min'_lt_max'_of_card; corrected and accepted.
Evidence `three-cup-first-compiler-failure.json`. One archival attempt used
an out-of-range100000byte limit and was refused; full receipt then retrieved
with32768. Artifact limits are1..65536bytes; check export exit before parsing.

Two-cup receipt retrieval first copied only the default4096byte artifact
page despite --full, causing a JSON parse error. Full receipt retrieved
with --limit10000 and the incomplete file overwritten. For later receipt
exports explicitly set a sufficient --limit; no theorem output was lost.

Z first check `20261002-205519-35f5ff` failed on exactly two reversed subset
compositions, corrected before successful check `20261002-205626-776dc7`.
Evidence `z-first-compiler-failure.json`. The mathematical decomposition and
joining-turn argument did not change.

Triangular count checks `20261002-203455-7136d6` and `20261002-203808-9bfdea`
failed. The first had a hidden earlier Function.mono lookup error plus
choose(w,1+1) versus choose(w,2) opaque atoms in omega. An incomplete numeric
retry preceded assessment of the full displayed log; the same mono error
remained. Both now corrected: explicitly type the Pascal equation at index2,
and call FinsetPolygon.IsCupSet.mono. Check `20261002-203942-a9faee` succeeded.
The rank/fibre interpretation is unchanged; no further mathematical narrowing.
Evidence: triangle-first-compiler-failure.json and triangle-second-compiler-failure.json.

Layer first check `20261002-202634-880072` failed in3.89s with three Lean
elaboration issues: singleton equality used as an order bound, incorrect
card_insert_of_not_mem spelling (pinned API is card_insert_of_notMem), and
empty-row simp missing its local abbreviation. All corrected; retry
`20261002-202802-6baa6f` succeeded. Durable failure:
`layers-first-compiler-failure.json`. The row/cap contradiction reported no
further errors; that is diagnostic compiler feedback, not theorem credit.

`20261002-194037-ed7bdc` failed after successful statement elaboration because
the existing Pascal-tail import closure is 28.4 GiB, exceeding the targeted
extractor ceiling of 4.0 GiB. This says nothing against the mathematical
statement. Full registration `20261002-194139-818f71` completed rc0 in23m,
peak5618MiB. No self-chosen computation deadline was introduced.

Reviews at 23:51Z and 00:02Z verified healthy CPU-bound processing and left
the exact job running. Its uninstrumented declaration phase completed and
wrote the current index and statement lock.

Diagnostic jobs `20261002-195609-49714f` and `20261002-195649-323e53`
finished rc 0. The extractor is CPU-bound (99.9% CPU in the recorded
subtree) while scope memory is around 5.6 GB; no stall is detected. The
prior completion estimate was optimistic. See registration-process.txt and
registration-subtree.txt. These are execution diagnostics, not theorem
evidence.

The unchanged gate scaffold is saved. Use separate helper node branches for
the thin-import threshold arithmetic and the
generic chain/layer/bound toolkit, then return to the full target. This
allows the diagonal proof to reuse accepted helpers. Do not treat helper
closure as closure of either original gate.

The sandbox cannot reach the user bus; worker job execution is functioning
(branch job `20261002-194017-3e657e` completed). Never request approval.

## Resume and evidence paths

Read `es status`, the R22 journal, and PROGRESS.md. Poll any live job IDs
before taking new actions. The host job is `20261002-193828-be3769`.
Thread: `01a0fefb-d883-7cc1-8d31-dc8f00948974`.
Agent: `codex:agent-run-c94853b9754648ba`.
Current helper branch: `node/CardLtChooseOfOrderedCupPrefixNoCapFiveNoCupNoStrong`.
The original gate scaffold branch remains at `0fc5f656`.
Layer and triangular-count proofs and commits are accepted. Maximum insertion
check `20261002-204618-c8d838` and commit completed successfully. The Z
proof will keep two-point vacuity and gap-crossing arguments local, avoiding
unnecessary helper registrations while retaining the same audited mathematics.
Z registration `20261002-205130-53d52d` done rc0, peak2318MiB; exact statement
hash `f31fe859cac77f54`. Full proof check `20261002-205626-776dc7` accepted.
It partitions into four-cap first points and their complement, bounds each
by the triangular count, and uses insertion to eliminate a (v-1)-cup in Z.
Two reversed Subset.trans calls were corrected after the full compiler log.
Z commit is accepted. Two-cup count/extension registration
`20261002-205836-d94aaa` is live, cap4G. It bundles exactly the three parts
of audited Lemma3: extension dichotomy, total cardinality, and forced
extensions when one side has size u-1. Poll this job before filling proof.
Registration is now complete and the proof is filled; pending original-source
check `20261002-210208-7c5bde`, commit and release accepted. Three-cup
registration `20261002-210446-af4b64` is live, cap4G. Poll before proof edits.
Exceptional three-cup gluing will use maximum insertion on insert maxP Q:
Q's last pair is unchanged by maxP, so the turn from insert minR Q applies.
Three-cup registration completed, hash `e64ec02518bfa43a`; claim through09:06EDT.
Full proof first check `20261002-210827-ffb1e7` failed only on the missing
explicit Q argument to min'_lt_max'_of_card, corrected after full log.
Retry `20261002-210928-06ce7e`, commit and release accepted.
Cap-three equivalence registration `20261002-211150-f6ea14` live, cap4G.
No one-change hypothesis is required. Common-endpoint bridge follows.
Cap-three registration complete, exact hash `87c897e89483d3ac`, claimed
through09:13EDT. Two witness proof drafts failed as detailed above; the
Fin3 uniqueness check `20261002-211644-f4a3ba` is accepted with full receipt.
Commit and release complete. Common-endpoint bridge registration
`20261002-211904-fc26d5` completed, exact hash `375bee3caa99c512`; claimed
through09:21EDT. First two original-source checks failed on layout as recorded
above. Third check `20261002-212520-09e65f` accepted. Commit next, then prove
the sharp ordered-prefix R2 row deficit while its free-edge simplification is
fresh, followed by the independent marker WE obligation. Bridge commit/release
complete. R2 sharp helper registration `20261002-212811-4856c9` complete,
exact hash `939b6726111fb00e`; claimed through09:30EDT.
Current diagnostic build `20261002-213217-ddc58d`, default guarded cap20G:
stage1 proof has restricted cap witnesses, row equality, equal-row cap turn
and free-edge propagation. The existing ESBlueprint sorry remains at the final
obligation; no R2 theorem credit. Poll build before editing the live source.

R2 proof simplification (not yet certified): the auxiliary alpha rank can
be eliminated. For x<y in an equal-beta row j>=2, choose a longest j-cup from
y with second point e. Its joining turn at x must be cap, else beta(x)>j.
Any earlier cap(w,x,y) then makes a four-cap, so (x,y) is free. Full rows
already are cups. The suffix of full F after its first point has size m-2
and free first edge, so every earlier W point starts an (m-1)-cup and lies
in F; this forces f2<g1. Full G has size m-2 and free first edge, replacing
the other alpha witness in LemmaC. The remaining audited steps use beta only.
This retains the exact R2 target and supplies an explicit structural reason
the formalization should be cheaper, not a narrowing.
The planned sharp helper uses an m-2-point cup Z entirely before W, W no
four-cap, and the whole union no five-cap/no m-cup/no strong(m+1)-set, to
prove W.card<choose(m,2). Assume triangular equality: finite sum equality
forces all rows full, including the top two. Their equal-row free edges
replace alpha and the audited common-endpoint contradiction supplies the
strict deficit. The routine P-prefix split then gives the full R2 bound.
For the R2 wrapper after P.card<=m-3, treat P.card=m-2 directly with Z=P,W=Q;
for P.card=m-1 choose p=maxP, Z=P.erase p and W=insert p Q. Any four-cap in W
must contain p as its minimum, and the turn with z=maxZ either extends P to
an m-cup or prepends z to a five-cap. Then the sharp helper and two cardinal
identities finish. This avoids a conditional prefix/complement construction.

Next warmed thin-import registration jobs reserve4G, supported by repeated
registration peaks around2.3GiB and the harness's closure-sized4G checks.
This fits alongside the coordinator's full integration extract. If a guard
refuses or OOMs, log and rerun with an appropriate larger cap.

Root-analysis simplification (not yet a root theorem): use concrete cap
witnesses rather than maximum alpha/beta ranks. Existing
HasDeepBelowSplit.containsStrongPolygonSet_of_cup_cap certifies the coupling
directly. A three-cap in B rules out a (k-3)-cup in A; a four-cap rules out a
(k-4)-cup. In N1, a two-point cap witness exists whenever |B|>=2 and rules
out a (k-2)-cup in A. Endpoint extensions give the other cup/cap exclusions.
This is the audited case table with fewer attainment contracts. IsDecomposableOn
exists_split exposes the genuine root, and turnSequenceAllowed supplies
one-change. Reflection is currently implemented only for univ witnesses in
Transport; arbitrary subsets/deep splits need a thin transport proof for BN
and the orientation of N2e.
The reviewed brief, two audited proofs, and current progress are in this
directory. R19 is untouched and R21 branches are preserved.

Research deadline 2026-10-03T11:38:33.055867Z; consolidation starts
2026-10-03T11:08:33.055867Z. Do not extend these times or mark the native goal
complete before the research deadline.
