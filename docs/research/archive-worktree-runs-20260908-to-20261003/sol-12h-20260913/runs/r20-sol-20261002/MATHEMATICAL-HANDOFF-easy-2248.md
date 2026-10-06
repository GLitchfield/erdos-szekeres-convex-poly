# R20 mathematical handoff

Checkpoint: 2026-10-02 22:48 UTC. Native goal ACTIVE; no user pause.
Research deadline 2026-10-03 04:57:32.670035 UTC; consolidation starts
04:27:32.670035 UTC; finalization must end by05:27:32.670035 UTC.
Agent `codex:agent-run-67caffbfbf804ebf`, configured gpt-6.1-sol/xhigh, no delegation.
Worktree `runs/worktrees/sol-12h-20260913`; baseline
`6e4d0e66274e9d3dd1ccdbacf9fd747deb5e1d14`. R19 was not modified.
Earlier detailed chronology, including failures and corrected reports, is preserved
in `MATHEMATICAL-HANDOFF-history-2134.md` and `PROGRESS.md`.

## Established mathematics and proof ideas

The uniform two-cup-block theorem and singleton Pascal-tail gate compile for every
k≥5. An ordered union of two cups with OneChange, no four-cap and no strong k-set
has cardinality≤2k−4. A strong set of at least five points avoiding the second left
point and penultimate right point can grow. Deleting those two points lowers the
forbidden strong size and permits induction; the manual 3|4 theorem supplies the
base k=5. Consecutive-turn propagation, strong-set cup/apex shape and shielded
insertions prove growth. The size-four exception is real, so this argument does
not lower the base to k=4. The gate uses the existing bridge: absent a parent
four-cap, both gap sides are cups and the reservoir of size2k−3 is impossible.

For a strong set with extrema l<r, classify each interior x by χ(l,x,r).
Cap-colored interiors B together with l,r form a cap; the complement is a cup.
No(j+1)-cap bounds B.card≤j−2. Middle determinacy proves this without OneChange.
Conversely, under OneChange, a cup and cap sharing their extreme endpoints have
strong union, with arbitrary cap interiors. Anchored colors make each mixed
triple depend only on its middle point. Standalone cup insertion moves formalize
shielding by two selected vertices, then iterate it for two-point growth.

Exact ending and starting cup ranks exist on every finite support without any
color assumption: choose a maximum-cardinality endpoint cup in its finite family.
Under OneChange and no4cap, each rank-j fiber is a cup of size≤j. For a hypothetical
cap triple x<y<z of equal ending ranks, the predecessor w of a longest cup at x
either gives a cup extension to y (contradicting its rank), or a four-cap wxyz.
Starting ranks mirror this through a successor. More generally, no(k+1)-cap
implies no k-cap in every ending-rank fiber, k≥2: take the first two cap vertices,
force the predecessor turn, and prepend it to get a forbidden larger cap.

Two cross-gap facts are accepted. An ending-rank layer on the left, united with
any later cup, avoids4cap under the registered no4cap-left/no5cap-union contract.
A four-cap would begin with two equal-rank left points, whose predecessor extends
it to5. The no4cap-left hypothesis is retained in the registered statement; proof
inspection suggests it is unnecessary for this conclusion, but no stronger
statement is credited here.

The rank-free extension alternative supplies the reason for cross-gap cups.
For a cap turn a<b<c, an ending cup C at a and starting cup D at c, both size≥2,
must permit b to extend at least one cup under OneChange/no5cap. Failure on both
sides forces predecessor/successor cap turns and then a five-cap. Cross-gap A
uses exact local ranks and global upper cup profiles to forbid both insertions
at a hypothetical mixed cap triple. Therefore its restricted layer union is a cup.

The ordinary binomial cup-cap alternative now holds under OneChange alone on
the finite support, without geometric realizability. CupCap.cup_cap already
supplies sorted consecutive chains at the binomial threshold. Restrict the
coloring and OneChange to a chain image; accepted H1 propagates each consecutive
color to all triples. The image has exactly the chain length, giving the cap
or cup of any prescribed size at least two. This unifies existing fixed-size
abstract recipes and reuses the recurrence; it does not supply polygon savings.

The documented easy a5 regimes are now accepted uniformly. If both sides lack
a c-cup, their triangular capacities sum to c(c-1). If either lacks a(c-1)-cup,
the other side's cup bound c gives choose(c-1,2)+choose(c+1,2)=c*c-c+1.
Thus the exact budget follows without gap order, no5cap or polygon avoidance.
Only both(c-1)-cups with at least one c-cup need coupled polygon savings.

## Accepted targets and exact original checks

Each mathematical branch is `node/<suffix>` from the baseline, with exactly one
new global statement in `ESBlueprint/B/<suffix>.lean`; no sibling merges.
Each listed original-source check is terminal rc0, CLOSED/sorry=false, locked
type unchanged, only standard axioms, fresh incremental/full index, no blockers,
and clean audit/layers. Receipt counts are bookkeeping, not the proof explanation.

| Theorem / branch suffix | Pinned mathematical commit | Original check | Type lock |
|---|---|---|---|
| `diagonalCupBlocksForce4kk_of_five_le` / DiagonalCupBlocksForce4kkOfFiveLe | c89df0e8605272ad2484600507ce342c8cf5f421 | 20261002-133903-34a3cd | 7b9515ee94a1f04b |
| `singletonLowerPascalTailGate_four_diagonal_of_five_le` / SingletonLowerPascalTailGateFourDiagonalOfFiveLe | 82a570723fc014cbd192dee18fa19e8f7a1a15dc | 20261002-140250-5b9883 | 5ef1de5a24229d34 |
| `strongPolygonSet_capMiddle_partition_of_no_cap_succ` / StrongPolygonSetCapMiddlePartitionOfNoCapSucc | 96d751150ddbc6881b183ba1fd9ef2735c46fa2c | 20261002-142724-7d87f7 | 875d3f763cb1a39a |
| `cupLayer_of_no_capFour` / CupLayerOfNoCapFour | e6df7d76733f7c9328e09c8cc0673f3383a46e61 | 20261002-145546-60d9cc | 732a647456a876b8 |
| `isCupSet_insert_of_two_left_vertices` / IsCupSetInsertOfTwoLeftVertices | 2d993f82ddb2e375bc9f8cec4e67ed676f053879 | 20261002-150329-e8a6e0 | c005da92ee73f667 |
| `isCupSet_insert_of_two_right_vertices` / IsCupSetInsertOfTwoRightVertices | b982195a6ec50d8f54d936ef28a5c87cdb7ec536 | 20261002-150906-d6ab01 | 1f0b9577a357c8a2 |
| `isCupSet_insert_two_left_and_card` / IsCupSetInsertTwoLeftAndCard | 8acb61b2af6c99eda48c11a14a9e1bc82ec7c287 | 20261002-151606-c31d96 | d62a250e6f1ffb0e |
| `isCupSet_insert_two_right_and_card` / IsCupSetInsertTwoRightAndCard | 5070599d3dc3d0a0029906fb204f9dead193a8e9 | 20261002-152242-418f37 | 6375458bcedfe290 |
| `isStrongPolygonSet_cup_union_cap_of_common_extremes` / IsStrongPolygonSetCupUnionCapOfCommonExtremes | ddd9dea56692bc7d94deeb20717ee3bbdd2844bf | 20261002-153032-82183a | c07e8cd85ed7d9af |
| `allTripleColors_eq_of_consecutive` / AllTripleColorsEqOfConsecutive | ff1e7d84a69faff21a66dfa47b103d137f268037 | 20261002-160052-94ea97 | f2f0b04ce9926768 |
| `existsEndingAndStartingCupRankProfiles` / ExistsEndingAndStartingCupRankProfiles | 79ab12867b418bedf3b8019a870bf62d164bcb62 | 20261002-160958-802e30 | 3b42bbf38ce81b7c |
| `startingCupLayer_of_no_capFour` / StartingCupLayerOfNoCapFour | 05f67bac8263d5ecee4f420fa25bd4621dcbf1a3 | 20261002-162242-46dc96 | d3a8de630d0f75e8 |
| `notContainsCapFour_endingCupLayer_union_laterCup` / NotContainsCapFourEndingCupLayerUnionLaterCup | 540d45ecce1821f24f9b5202b6943ca1551069fe | 20261002-164346-dd2bc2 | 74e49008b8f60c59 |
| `notContainsCapSet_endingCupRankLayer_of_no_cap_succ` / NotContainsCapSetEndingCupRankLayerOfNoCapSucc | 9ded8a3c582936b5530042e4c42bc08854d481fc | 20261002-165014-106554 | 1c666a869b5bd8c5 |
| `isCupSet_insert_or_insert_of_no_capFive` / IsCupSetInsertOrInsertOfNoCapFive | 4b1ac83c00c3bbe6987fa44df326a545b069c004 | 20261002-165556-4089f9 | 14e3c3517accb78f |
| `isCupSet_crossGapRankRestrictedUnion` / IsCupSetCrossGapRankRestrictedUnion | f3c45abfb7b6a9bfa68a2dcd8d8183e5ba9d72de | 20261002-170749-92dc59 | 8b7d14044ef6dedb |
| `orderedTwoSideSquareBound_of_no_cup_succ` / OrderedTwoSideSquareBoundOfNoCupSucc | d41189941a183a72aae1c854c31260c7e9576bbe | 20261002-174035-15e650 | aec659557232639f |
| `existsCupExtension_of_side_three_caps` / ExistsCupExtensionOfSideThreeCaps | 637fef9fd1ec3b029df1e7e47b05de9deab8521d | 20261002-175130-634ddc | 66fe1d2e96dd9a6a |
| `strongPolygonSet_two_capMiddles_of_side_three_caps` / StrongPolygonSetTwoCapMiddlesOfSideThreeCaps | ee6831eaafd3ed949c88abce114e3a17c84aecda | 20261002-180330-a00a02 | 65e61fa9648a47ea |
| `containsCapSet_or_containsCupSet_of_oneChange_choose_lt` / ContainsCapSetOrContainsCupSetOfOneChangeChooseLt | c0e40e21409204f3a26850254e5ef9cf97db375e | 20261002-183138-a9c2fa | d4e0aff1d0b4a971 |
| `twoCapFreeSides_card_add_le_of_short_cups` / TwoCapFreeSidesCardAddLeOfShortCups | 16d1abcf68f9b4e52ef2bf23d18db33b80913d49 | 20261002-184525-7511f5 | af4b26c8c8ac5e22 |

The uniform original check used13471MiB/908.5s; gate5681MiB/990s.
Later thin checks usedabout2.4GiB/38–63s. No OOM or missing outputs on these
accepted original checks. `CHECK-*.json` and `PROOF-*-RESULT.json` preserve the
full evidence; the chronological account gives every registration/commit job.

Eighteen candidate receipts also have independent isolated audits and now exact
commit byte comparisons in `PIN-IDENTITY-*.json`. Gate, shape and ending L1 have
original-source checks and are not mislabeled as independent candidate audits.
For final A: receipt
`007f25493ea09b677b072c305415b6044bc1d7d94f89d38a992266ca0717b934`,
fixture `a8ce1b493179f2fa730469146422bc0d03f1e615e297323beb886dbbbd1240d4`,
body `34ab9490003a25b882052b78fcd0258ae441265eff8c361680e0c2f5f9a28daf`,
source `863f2d375248dffec4d5fa513a45a62c3b0031fc9e2472bc7db639bbd4c1b890`.
Isolated job20261002-170711-59d4f3/op-3d660aeef22f47c5; actual successful
commitjob20261002-170857-802d4f. `CROSS-GAP-A.accepted.lean.txt` is exact pinned
source. Its first whitespace variant compiled but commitjob20261002-170543-6c2510
FAILED. The premature baseline-as-pin report was explicitly corrected; baseline
6e4d0e66 is never an A proof commit. Old variant receipts/files remain preserved.

## Exact open obligation and next attempt

The coupled a=5 cut E and polygon-dependent lower-layer deficiency remain open.
There is no complete proof idea for choosing a gap-compatible removed two-cup
block that meets maximum strong sets within the exact size budget.
For c=K−1, the accepted rank count gives only the ordinary bound c²; the desired
c²−c+1 requires another c−1 savings linked to strong-polygon avoidance.
Proving or refuting those savings requires a structural interpretation, not
fitted rank signatures. No narrowing is presented as a result.

The ordinary square target is now accepted: ordered L<R, OneChange/no5cap on L∪R, no4cap on each side,
no(c+1)-cup globally, c≥2 ⇒ (L∪R).card≤c*c.
Proof idea: exact local ranks exist; every cup has size≤c by taking a (c+1)-subset
otherwise. Each lower rank-r fiber has size≤r by L1. Cross-gap A at i=j=c with
constant global upper profiles c makes the two top fibers one cup, with combined
size≤c. Sum the remaining fibers:
2*sum(r=0..c−1,r)+c=c².
Search `SEARCH-TWO-SIDE-SQUARE.json` is empty; Mathlib supplies
Finset.card_eq_sum_card_fiberwise and Finset.sum_range_id_mul_two.
First isolated check20261002-173958-f980af/op-c559cd3a77c444d3 accepted8.336s/2103MiB;
receipt c0a989993c2570ab258566a54bdc2943d3511b2599a5da7cb95f0fa61472997f,
fixture c44b246634f51cb68a5b6c285561c69b245fc3940edb4ea550533e94c1b3a486,
body c3269fb9a4ca752d7a15c41a5574976030b709b2fd57e3d9b0245f1bf06a4401,
source19e153610fb93a578fa184505fac7376c76b9fb7ae0a06c004556e8541c595a2.
Original20261002-174035-15e650 passed44.2s/2371MiB/noOOM/missing;
commitjob20261002-174215-e6c51e DONE/rc0, exact Git bytes verified by the
promoted API loaded from its hash-verified archive (no sibling merge).
Evidence PROOF-TWO-SIDE-SQUARE-RESULT.json, CHECK-TWO-SIDE-SQUARE-ORIGINAL.json,
TWO-SIDE-SQUARE.accepted.lean.txt and PIN-IDENTITY-TWO-SIDE-SQUARE.json.
An untested triangular sharpness construction is only a hypothesis, not a result.

The cup-killing extension fact (L3) is now accepted in an explicit endpoint-witness
contract: a cup C of size≥3 whose left points end side3cap turns and whose right
points start side3cap turns extends by one ambient point, with exact cardinality.
Only ordered sides, OneChange and no4cap each side are needed; no globalno5cap.
Its ordered enumeration supplies first/second and penultimate/last vertices.
A supporting3cap forces the extending cup turn or a forbidden side4cap. This
certifies cup hitting outside E0, not E0's tight size budget; E0 may contain a
cross-gap4cap. The structural consequence is now separately accepted for k≥4:
with no5cap/no k-cup, a strong k-set supported this way has exactly2 canonical
cap-colored interiors, a (k−2)-cup and4-cap sharing extrema. General shape gives
at most2; at most1 leaves a cup portion≥k−1≥3, which L3 extends to a forbidden
k-cup. The minimum4 is exactly the growth threshold, not a fitted extension.
No4cap on each side forces the resulting4cap to cross the gap, but selecting a
tight compatible E to meet those polygons remains open.

## Reuse, failed routes and limits

Both coordinator a5 note sets were read in full; canonical second layers,
pointwise signatures, endpoint/hook hitting and local exchanges have diagnostic
counterexamples there, not new R20 Lean refutations. Read those exact semantics
before adopting any such route. Paths in the primary checkout:
`runs/claude-twoside-a5-20261002/NOTES.md` and
`runs/claude-twoside-a5b-20261002/NOTES.md`.

Deep-below root strong classification already exists at
HasDeepBelowSplit.isStrongPolygonSet_iff_inter_cup_cap in
ErdosSzekeres/Decomposable.lean:1301, plus its cup/cap union and existence helpers.
Reuse it; its handling of interleaved children is essential. Decomposable children
need not be contiguous in sweep order. Conditional ordered-root estimates do not
cover all roots and are not credited as the target theorem. Empty harness search
is not exhaustive: source search found these untagged helpers.

Meaningful compiler failures and infrastructure problems are logged before repairs:
implicit ambient arguments at the gate; redundant tactics after simp; folded
ambient let in B membership; mistaken Turn constructor rename in the general
layer proof; unknown Mathlib @depends name at rank registration; false dependency
cache-current due to another worktree writer; closure admission/full extractor
limits; no-pytest interpreter and queued-worker PYTHONPATH at maintenance.
No failed or cancelled job is counted as theorem evidence. Source artifacts and
original diagnostics remain in this run directory and the shared job journal.

## Review and maintenance

Generic type/value dependency tracer promotion:
commit7242b3e927bb256e61134285b6ca694fc87abf00 (follows H3, separate from its proof).
Archive `PROMOTED-DEPENDENCY-AUDIT/`; 17 tests in20261002-154318-4ae882,
Nat smoke20261002-154347-ffad00, project demo20261002-154522-2a7466.
It follows actual constant ownership and opaque/inductive families. Source/olean/
trace hashes are observational; they do not attest source-to-olean correspondence.
The extractor's configured standard-axiom set is conservative; isolated audits
use actual Lean.collectAxioms. Different subsets of standard axioms are expected.

Generic read-only `es proof identity` promotion:
commitba9b1946f0c9cd9dd3d0584c40d170b52026e2e1 (follows A, separate from its proof).
Commitjob20261002-173245-2010a5 DONE/rc0. Archive
`PROMOTED-PINNED-SOURCE-IDENTITY/`; testjob20261002-172518-594691,
32 passed in3.11s/57MiB. Live actual A identity passed; actual baseline rejection
returned exit2. It reconstructs immutable candidate bytes and compares raw Git
blob bytes at a full SHA; compiler_rechecked=false/theorem_credit=not_inferred.
Earlier commitjob20261002-173218-8cb2fa failed before mutations because the queued
worker did not inherit PYTHONPATH; missing declared output explicitly recorded.
Diagnostic `COMMIT-PINNED-SOURCE-MAINTENANCE-01-IMPORT-FAILURE.json`.
Both promotions were self-reviewed by configured Sol; independent coordinator
review remains pending. No delegation or independent Astra review occurred.

Structural review inventory `STRUCTURAL-REVIEW-EVIDENCE.json` was read, including
80 recorded inline commands and18 validation jobs. Its3320 generated cache C
payloads are immutable cache artifacts, not ad hoc evaluators. Direct assembly
commands were also manually reviewed; local proof replay follows one-node packaging.
Successful inventory/process exit grants no mathematical credit.

## Operation and usage resumption

Current branch node/TwoCapFreeSidesCardAddLeOfShortCups, HEAD mathematical
commit16d1abcf68f9b4e52ef2bf23d18db33b80913d49, exact baseline parent6e4d0e66.
Worktree clean; temporary private artifact cache root restored before pinning.
Binomial claim CLOSED/released atc0e40e21409204f3a26850254e5ef9cf97db375e, handoff
MATHEMATICAL-HANDOFF-binomial-2234.md preserved. New branchjob20261002-183844-8509f7
DONE/rc0. A5-EASY is CLOSED with original/isolated receipts and exact pin identity;
claim release follows this checkpoint. No pending R20 compiler/research jobs.
Normal-form claim CLOSED/released with immutable handoff
88cf309094f0259852a30abdc63ea66e5d84bf30bf86b246e0e24e3c680a9049. Cup-killing claim
CLOSED/released; release handoff189c76ac1d4b8b45fc6ac09ed4f150b41789067083acb0d8ff0612583eec6367.
Square claim
CLOSED/released; release handoff artifact
2669c8adc33866aff4e45bc94e3c7df9c9a6ea3e6c6c7c4116b19aaa76ffd3e5
preserves the new account where the primary checkout's older handoff conflicted.
All R20 compiler/research jobs terminal at last review; native outer host
20261002-125731-43d19d remains running and is not a compiler.
Callbacks unverified; keep reporting turn open for authorized queued/running jobs.

Windows: research window-1dbf3b5a506149ca ended with9 accepted; maintenance
window-9cc69ab671434f81 ended with0; structural research window-7b4248f877f74097
ended with7; maintenance window-271bfcbd3c1b4810 ended with0 after source identity
promotion/review. Current square research window-fba7fa080ef94955 has one accepted
target and ended before the next maintenance review/trial. Counts do not measure understanding.
Latest structural review usage had569 responses, input72,727,540,
cached71,119,744, output545,630, reasoning284,930; later usage is pending.
See USAGE-STRUCTURAL-REPORT.json/STRUCTURAL-REVIEW-EVIDENCE.json; reconcile late
responses before final report. No matched-work saving is claimed.

On resumption: inspect status, latest node-filtered journal, this handoff and
any pending job IDs first. Preserve accepted branch commits before returning to
baseline for one new node. Thin 4GiB guarded checks worked atabout2.4GiB; a temporary
worktree-private artifact root avoids false cache-current but must be restored
before mathematical pinning. Use actual submitted job IDs; inspect terminal and
job_exit_code before dependent actions. All compiler/long jobs remain guarded es.

L3 acceptance details: first isolated20261002-175057-fd9a8b/op-a9e87671ea9e418e
passed8.141s/2099MiB, receipt9410046cfaaae91c0786295975bad9e0301555ec5b921c4c790ea2ea5b2cfaf6,
fixturee06880373134f3a864076b9ba70db607d2596a3145af44f1fb2248ef9d6de978,
bodyfcc42293a8146e0ae156d145ea51b3184a03224b8ee62b4183fc78c142d240db,
source29fa6be0261550d446e025c16159e79017ac6303e9b9b67fd71050e7d4120efe.
Original20261002-175130-634ddc passed54.4s/2373MiB/noOOM/missing,
CLOSED/sorryfalse/lock66fe1d2e96dd9a6a/no blockers/nonstandard axioms/incremental fresh,
audit449/layers clean. Commitjob20261002-175336-64c7b2 DONE/rc0, exact source
identity verified through the hash-verified archived promoted API. Existing
baseline lock entries unchanged, exact baseline parent. Artifacts
PROOF-CUP-KILLING-RESULT.json, CHECK-CUP-KILLING-ORIGINAL.json,
CUP-KILLING.accepted.lean.txt, PIN-IDENTITY-CUP-KILLING.json.
Research window-b115d3fe317c4dde ended with one accepted target before
maintenance self-review/next trial. No R20 compiler jobs pending; outer
native host remains live. Coupled E and polygon-dependent deficiency remain open.

Normal-form acceptance: first isolated20261002-180243-eff8e9/op-9468abbda9134f92
passed8.021s/2103MiB, receipt834484053cc3764d6a37ca15039c9d4dd9376a870889b0f052f0e48f0a79b67b,
fixture36f977b7af6205f744f5a9e2bbd8ae314de117b84dcfe764eabcb073f4a3c5af,
bodyfcbbc3c810acb4b9293334c65ee8f278c7457eb731811822e8749d381ca3aa1f,
source5bdd769704c4d9fa4a32f8f7146945e0018a96e535c4a42ac82676c668d89425.
Original20261002-180330-a00a02 passed50.0s/2370MiB/noOOM/missing,
CLOSED/sorryfalse/lock65e61fa9648a47ea/no blockers/nonstandard axioms/incremental fresh,
audit449/layers clean. Commitjob20261002-180650-452077 DONE/rc0, exact source/Git
identity matched through the hash-verified archived promoted API.
Artifacts PROOF-STRONG-NORMAL-FORM-RESULT.json, CHECK-STRONG-NORMAL-FORM-ORIGINAL.json,
STRONG-NORMAL-FORM.accepted.lean.txt, PIN-IDENTITY-STRONG-NORMAL-FORM.json.
All19 mathematical branches in ALL-MATH-PINS-SEMANTIC-LOCK-AUDIT.json have exact
baseline parents, one new source/lock and no changes to existing locks. Current
research window-c5b9eff4c0fa4e1a ended with one accepted target; the claim is CLOSED
and released, immutable handoff88cf309094f0259852a30abdc63ea66e5d84bf30bf86b246e0e24e3c680a9049.
Maintenance window-42c24b61efe6499b records self-review and the
observational combined dependency/loading audit. Sample job20261002-182017-3ca86e
DONE/rc0,16s/2195MiB,5306 constants, no disallowed dependencies. Remaining job
20261002-182051-0eadcd DONE/rc0,274.1s/2594MiB/noOOM/missing. All19 compiled
modules load together; #check/#print axioms pass. Their closures contain no
generated/certificate/unsafe/nonstandard-axiom dependencies. Eighteen absent
branch source files remain explicit unknown current-source owners. Separate
pinned-source/olean/trace hashes are observations, not source-to-olean attestations.
Original-source checks remain acceptance. Artifacts ALL-PINNED-DEPENDENCIES/;
one-off inventory driver self-reviewed, shared tracer API reused unchanged.
Maintenance window ended0; binomial researchwindow-20839b89fec44352 ended1.
Separate self-reviewwindow-1aaa91d9541f4222 ended0; new active easy-regime
researchwindow-d55d2321da084e58. Binomial dependency/loading audit
20261002-183615-5d5a92 DONE/rc0,21.6s/2191MiB,noOOM/missing; new closure5290
constants, std only/no disallowed dependencies, and all20 modules load together.
BINOMIAL-DEPENDENCY-AUDIT/receipt.json hashes remain observations.
All compiler work remains guarded, no callback assumed.

Source search found CupCap.cup_cap already proves the generic consecutive-chain
binomial alternative for arbitrary coloring. Existing full cup/cap set bridges
require IsSweepRealizable. A possible new abstract bridge should reuse that
recurrence and accepted OneChange consecutive-turn propagation, rather than
duplicate Pascal induction. Search SEARCH-ABSTRACT-BINOMIAL.json has no matching
indexed abstract result. Fixed-size abstract bridges also exist, and are
acknowledged. New target ABSTRACT-BINOMIAL.type.txt generalizes them: OneChange
on s, a,u>=2, choose(a+u-4,a-2)<s.card implies an a-cap or u-cup. Restrict
OneChange to the sorted chain image and propagate consecutive colors using H1.
Current branch node/ContainsCapSetOrContainsCupSetOfOneChangeChooseLt from the
baseline (guarded branchjob20261002-182633-1acb97 DONE/rc0). Registration
20261002-182655-ceb712 DONE/rc0,103.6s/2317MiB/noOOM/missing. Canonical node
ErdosSzekeres.containsCapSet_or_containsCupSet_of_oneChange_choose_lt is claimed.
First isolated20261002-182950-6c4492 failed two intermediate-Fin index bounds;
diagnostic42c8064daa8860a2633cd9d7e43a233b6e6f712f700055f0a0b6c78fefb6bc59,
body-01/result-01 preserved. Explicit OrderedTriple inequalities repaired them.
Revised isolated20261002-183040-14f45f/op-f0def5180c0c4fa9 accepted7.440s/2100MiB,
receipt d14aedf0b774a7cffc5e4f5b1160e772e90e12bcd7d2ef54edb78e3eac9bda58,
fixture347da1aa56bca61bdca6c30aa745b665e1c561cd6bed73c32ba07533fefa2d40,
body9065a511a5578d10411ae0cd61775d2d6ae63ca669985e51485d90f9303b05e7,
source313416f7e208a01bc9bd33b0aa03996006bd06637bd44e69ec718fa82fa98c12,
typed4e0aff1d0b4a971. Original forcedcheck20261002-183138-a9c2fa DONE/rc0,
48.7s/2367MiB/noOOM/missing,CLOSED/sorryfalse/lock/std/no blockers/incremental
fresh,audit449/layers clean. Commitjob20261002-183259-ee235c DONE/rc0;
actual pinc0e40e21409204f3a26850254e5ef9cf97db375e matches accepted bytes via
hash-verified promoted source-identity API (PIN-IDENTITY-ABSTRACT-BINOMIAL.json).
All20 pins retain baseline parents, one new source/lock and unchanged existing
locks (ALL-MATH-PINS-SEMANTIC-LOCK-AUDIT.json; previous19 inventory preserved).
Reused fixture/validate/assembled
APIs after inspecting node finish's fixed20G/full28G reservations; no new workflow.
Private artifact cache root restored before pinning. The uniform abstract
binomial alternative is accepted; coupled E size/deficiency remain open.

Accepted A5-EASY.type.txt formalizes documented easy cases uniformly: c>=3,
OneChange/no4cap each side/no(c+1)-cup globally, and either both sides lack a
c-cup or one lacks a(c-1)-cup, imply totalcard<=c*c-c+1. Ordinary no4cap/no
q-cup capacity choose(q,2) gives total2choose(c,2)=c(c-1) when both are short,
or choose(c-1,2)+choose(c+1,2)=c*c-c+1 when one is shorter by two levels.
The explanation identifies why only both(c-1)-cups with at least one c-cup
need polygon-dependent savings; original E remains open. Empty indexed searches
SEARCH-A5-EASY-REGIME.json/SEARCH-A5-SHORT-SIDE.json and source search support
the duplicate check. No order/no5cap/polygon assumption is needed for these
easy cases. Reuse the accepted binomial body locally; no new evaluator.

A5 easy-regime acceptance: registration20261002-183910-f4dd90 DONE/rc0,
103.4s/2311MiB/noOOM/missing. First isolated20261002-184426-7cec9a/
op-e401130d5a4549cb accepted12.601s/2099MiB, receipt
3856f11149e609aed13b79378bb810af428697a45475018ee54bae748aad4d5f,
fixture7baa84e0d0a7a0b378dcefa77f4961b85540c771f70d87c5d86c0bfc7c4d1454,
body4ac38c0e6c9210031353fe95f221181597f4fcd7de7cdc75ff4064e4d3de1dbd,
source629a02fc590bd9694b65dd8c6db94f4bfef4ab71fea5a513aca6f090837b4aad.
Original20261002-184525-7511f5 passed55.7s/2374MiB/noOOM/missing,
CLOSED/sorryfalse/lockaf4b26c8c8ac5e22/std/no blockers/incremental fresh,
audit449/layers clean. Commitjob20261002-184706-ea4f6d DONE/rc0; actualpin
16d1abcf68f9b4e52ef2bf23d18db33b80913d49 matches candidate bytes through the
hash-verified promoted identity API (PIN-IDENTITY-A5-EASY.json).
All21 pins retain one-node source/lock scope and baseline parents; previous20
semantic inventory preserved. Source A5-EASY.accepted.lean.txt, body142 lines,
main40 lines; no failed compiler attempt. Activewindow-d55d2321da084e58 has one
accepted target; end before separate self-review/next trial.

Structural deduction, not yet a separately certified corollary: no4cap and
no(c+1)-cup on one support already exclude a strong(c+2)-set there. Shape at
j=3 leaves at most one cap-colored interior, hence a cup of at least c+1.
Thus in the a5 setup individual-side noStrong(c+2) is redundant; the polygon
hypothesis has content only for crossing sets. Do not infer lower-layer
deficiency from applying that redundant side hypothesis. More generally,
no(j+1)-cap/no u-cup should exclude strong(u+j-2), j,u>=2, by the same partition
cardinality. Search SEARCH-STRONG-CUP-CAP-ALTERNATIVE.json is empty; no uniform
source duplicate found. This explains the obstruction and supplies a direct
proof idea if the general reusable corollary is registered next. Full E remains open.
