# R20 mathematical handoff

Checkpoint: 2026-10-02 19:53 UTC. Native goal remains active. Research deadline
2026-10-03 04:57:32.670035 UTC; consolidation starts 04:27:32.670035 UTC.
Agent `codex:agent-run-67caffbfbf804ebf`, configured Sol at xhigh, no delegation.
Worktree `runs/worktrees/sol-12h-20260913`; baseline
`6e4d0e66274e9d3dd1ccdbacf9fd747deb5e1d14`. R19 was not modified.
Earlier chronological account is preserved in `MATHEMATICAL-HANDOFF-history-1953.md`.

## What is established and why

The uniform two-cup-block theorem and its singleton Pascal-tail gate compile for
all k≥5. The proof bounds the size of an ordered union of two cups with OneChange,
no four-cap and no strong k-set by 2k−4. A strong set avoiding the second left point
and penultimate right point can grow if it has at least five vertices. Deleting
those two points therefore lowers the forbidden strong size and permits induction.
The base is the existing manual 3|4 cup-block theorem. Consecutive-turn propagation,
the cup-plus-cap-apex shape and shielded insertions supply the growth proof. The
size-four growth exception is real; the argument does not lower the base to k=4.

The gate applies the existing diagonal-gate bridge: the absence of a parent four-cap
makes both gap sides cups, and the remaining diagonal reservoir has size 2k−3.
The uniform theorem contradicts the forbidden cup/cap/strong alternatives.

The general shape theorem identifies a strong set's cap-colored interior points
through its extreme endpoints. Those points plus the endpoints form a cap, and
the remaining points form a cup. No (j+1)-cap bounds the number of cap-colored
interiors by j−2. Middle determinacy alone proves this; OneChange is unnecessary.
The converse is also accepted under OneChange: any cup and cap sharing both extreme
endpoints have a strong union, with arbitrarily many cap interiors. Anchored pair
colors force every mixed triple to depend only on its middle vertex.

The ending-cup layer theorem uses an attained longest cup ending at x. A cap
x<y<z in one rank fiber either extends that cup to y, contradicting equal ranks,
or forms a four-cap with its penultimate vertex. The fiber is therefore a cup;
its maximum endpoint bounds its size by its rank. Standalone insertion moves use
two selected vertices on one side to shield a new extreme point through OneChange.
Applying shielding twice gives an exact two-point cardinality increase.

## Accepted theorem receipts and commits

Every row is an independent one-node branch from the baseline. Each original-source
check reports CLOSED, sorry=false, the locked type, standard axioms only, a fresh
incrementally maintained full index, and clean layers/audit. No sibling was merged.

| Registered theorem / branch suffix | Pinned commit | Original-source check | Locked type |
|---|---|---|---|
| `diagonalCupBlocksForce4kk_of_five_le` / `DiagonalCupBlocksForce4kkOfFiveLe` | `c89df0e8605272ad2484600507ce342c8cf5f421` | `20261002-133903-34a3cd` | `7b9515ee94a1f04b` |
| `singletonLowerPascalTailGate_four_diagonal_of_five_le` / `SingletonLowerPascalTailGateFourDiagonalOfFiveLe` | `82a570723fc014cbd192dee18fa19e8f7a1a15dc` | `20261002-140250-5b9883` | `5ef1de5a24229d34` |
| `strongPolygonSet_capMiddle_partition_of_no_cap_succ` / `StrongPolygonSetCapMiddlePartitionOfNoCapSucc` | `96d751150ddbc6881b183ba1fd9ef2735c46fa2c` | `20261002-142724-7d87f7` | `875d3f763cb1a39a` |
| `cupLayer_of_no_capFour` / `CupLayerOfNoCapFour` | `e6df7d76733f7c9328e09c8cc0673f3383a46e61` | `20261002-145546-60d9cc` | `732a647456a876b8` |
| `isCupSet_insert_of_two_left_vertices` / `IsCupSetInsertOfTwoLeftVertices` | `2d993f82ddb2e375bc9f8cec4e67ed676f053879` | `20261002-150329-e8a6e0` | `c005da92ee73f667` |
| `isCupSet_insert_of_two_right_vertices` / `IsCupSetInsertOfTwoRightVertices` | `b982195a6ec50d8f54d936ef28a5c87cdb7ec536` | `20261002-150906-d6ab01` | `1f0b9577a357c8a2` |
| `isCupSet_insert_two_left_and_card` / `IsCupSetInsertTwoLeftAndCard` | `8acb61b2af6c99eda48c11a14a9e1bc82ec7c287` | `20261002-151606-c31d96` | `d62a250e6f1ffb0e` |
| `isCupSet_insert_two_right_and_card` / `IsCupSetInsertTwoRightAndCard` | `5070599d3dc3d0a0029906fb204f9dead193a8e9` | `20261002-152242-418f37` | `6375458bcedfe290` |
| `isStrongPolygonSet_cup_union_cap_of_common_extremes` / `IsStrongPolygonSetCupUnionCapOfCommonExtremes` | `ddd9dea56692bc7d94deeb20717ee3bbdd2844bf` | `20261002-153032-82183a` | `c07e8cd85ed7d9af` |

Node files are `ESBlueprint/B/<branch suffix>.lean`; branch names begin `node/`.
The first full check took908.5s/13471MiB; gate990s/5681MiB. Thin original-source
checks took37.6–62.6s/about2.4GiB. All terminal rc0 with no OOM or missing outputs.
Exact body/fixture receipts for the uniform and standalone insertion/H3 theorems
are in `PROOF-*.json`; original-source results in `CHECK-*.json`. See `PROGRESS.md`
for each commit job and isolated receipt. The gate repeats the uniform induction
locally so its baseline branch is self-contained; integration can replace that
repetition with the imported uniform theorem.

Uniform exact identity is pinned in `UNIFORM-IDENTITY-VERIFICATION.json`: source,
body and type agree with the captured receipt and unchanged baseline statements.
Observational type/value dependency audits cover the uniform theorem (6030 constants,
job`20261002-141330-ba1b81`), gate(6468,`20261002-141800-9a57e9`) and L1
(4527,`20261002-145812-e7dddb`). Their `*-CERTIFICATE-DEPENDENCY-AUDIT.json` files
record no generated/certificate/unknown project modules or unsafe constants, with
standard axioms only. These audits support dependency claims; they do not themselves
accept proofs or attest source-to-olean correspondence.

## Open obligation and useful next facts

The coupled a=5 cut E remains open, and there is no full proof idea for it here.
A tight gap-compatible removed two-cup block must meet maximum strong sets with the
exact size budget. Canonical layers, pointwise signatures, literal second layers,
endpoint hitting, hooks and local exchanges fail on diagnostic instances in the
coordinator's two a5 note sets. Those diagnostics are not Lean-certified by R20.
No fitted profile inequality is promoted to mathematical progress.

Two hand-proved cross-gap observations have a structural explanation worth formalizing:
with exact left ending ranks and right starting ranks, equal-rank pairs force cap
turns with a longest cup's predecessor/successor. A forbidden mixed cap then extends
to a five-cap. This proves a bounded-global-rank cross-gap cup and rules out a
four-cap in the union of one left and one right layer. These observations may
explain top-layer deficiency, but neither chooses E nor supplies the missing
lower-layer polygon deficiency. Record the exact proof idea before registering them.
First provide the mirrored starting-layer lemma and existence of exact rank profiles.

Additional accepted reusable theorem:
`allTripleColors_eq_of_consecutive`, branch`node/AllTripleColorsEqOfConsecutive`,
commit`ff1e7d84a69faff21a66dfa47b103d137f268037`, lock`f2f0b04ce9926768`.
Original check`20261002-160052-94ea97`:rc0/48.1s/2369MiB/noOOM/missing,
CLOSED/sorryfalse/fresh index/clean audit and layers. Isolated receipt
`69246cb83927ec2493a1ef6bf8ad13e235419986232a4df6e0067e11399454d5`,
job`20261002-160005-fa08df`, uses the exact accepted local outer-span argument.
Endpoint rank existence is now accepted at commit
`79ab12867b418bedf3b8019a870bf62d164bcb62`, exact original-source check
`20261002-160958-802e30`, lock`3b42bbf38ce81b7c`; details below.
Starting-layer mirror is accepted/pinned at
`05f67bac8263d5ecee4f420fa25bd4621dcbf1a3`, check`20261002-162242-46dc96`,
lock`d3a8de630d0f75e8`; exact receipts and mathematical explanation below.
The layer/later-cup no-four-cap node is accepted and pinned at
`540d45ecce1821f24f9b5202b6943ca1551069fe`, original check
`20261002-164346-dd2bc2`, lock`74e49008b8f60c59`; its claim is being released.
The exact registered contract still assumes no4cap on the left side. Next is the
general cap-layer reduction recorded below.
Coupled a5 cut remains open.

## Failures, repairs and infrastructure

Meaningful compiler failures are preserved and journaled before repair. Explicit
eight-case OneChange analysis avoids unrestricted simp_all heartbeat exhaustion;
eta expansion exposes opaque OrderedTriple coordinates; explicit membership
witnesses avoid opaque local aliases. Gate introduction fixes implicit ambient
instantiation. `Finset.card_insert_of_notMem` is the correct spelling; its rewrites
may close a card goal without a following omega. UTF8 proof spans use byte offsets,
with shared `es.proofs` fixture/validation/assembly APIs.

A serial root build hit its synchronous guard; background job`20261002-133827-ebe4aa`
completed without certificate regeneration. Thin checks initially needed a 20GiB
reservation because an unrelated shared cache writer lease made dependencies look
uncurrent, despite existing objects. A temporary worktree-private artifact cache
root fixed that classification while preserving memory guards, baseline core and
extractor fingerprints. It is restored before every mathematical commit. Current
registration uses that temporary root again; restore before pinning. Never patch
index fingerprints or treat a successful process exit as theorem credit.

Only guarded es builds/checks/jobs are used. No deadline wrappers or native_decide,
new mathematical axioms, or sorry outside the blueprint were introduced. Pending
jobs/claims are tracked in the shared harness. The native host is
`20261002-125731-43d19d`; it is not a compiler job. Callback readiness is unverified,
so this reporting turn remains open while authorized jobs run or queue.

## Separate maintenance review

Research window`window-1dbf3b5a506149ca` ended after the accepted primary proofs;
usage snapshot`USAGE-PRIMARY.json` includes setup and failed attempts, with late
usage to reconcile. Maintenance window`window-9cc69ab671434f81` ended separately.
Reusable observational dependency traversal and owner-aware classification were
promoted as catalog`research.lean-proof-dependencies`, commit
`7242b3e927bb256e61134285b6ca694fc87abf00`, guarded commit
job`20261002-154857-93bed3`. It follows the H3 proof commit and can be reviewed
separately. Exact promotion is archived in `PROMOTED-DEPENDENCY-AUDIT/`; original
run inspector/traces remain intact. Self-review used Sol under the no-delegation
instruction; independent coordinator review is pending.

The API reuses ConstantInfo traversal, scan_modules/layer prefixes and streaming
sha256_file. It records actual declaration ownership separately from the import
entry, retains unknown modules and obstructions, refuses legacy ownerless identity
receipts, and grants no acceptance/freshness flags. Guarded regression job
`20261002-154318-4ae882`:17 passed. Nat smoke`20261002-154347-ffad00`:unchanged
43 constants, owner`Init.Data.Nat.Basic` despite import`Init`. Guarded project
example`20261002-154522-2a7466`:rc0/14.1s/2191MiB/noOOM/missing,71 constants,
no certificate/generated/unknown project modules, unsafe or nonstandard axioms.
Example receipts are in `MAINTENANCE-PROJECT-DEMO/`.

New research window`window-7b4248f877f74097` covers further structural tools.
Before another trial, review any new ad hoc run code and log reuse/promotion/deferment.
On resumption, first check status, agent/node journal, and all pending job IDs above.
The safest integration step is coordinator review of independent branches, importing
the uniform theorem in the gate, then guarded compilation/extraction of the combined
sources. No merged integration has been claimed in this worktree.

Original-source extractor standard-axiom lists are conservative: record() adds
all configured standard axioms to the computed nonstandard closure. The isolated
AuditCandidate uses Lean.collectAxioms for the actual list. H1's different lists
(three vs two standard axioms) therefore reflect reporting semantics, not a source
mismatch or extra unapproved axiom. Exact used-axiom claims require the latter or
an observational full dependency traversal.


2026-10-02 20:12 UTC: `existsEndingAndStartingCupRankProfiles` accepted/pinned at
`79ab12867b418bedf3b8019a870bf62d164bcb62`, commit job`20261002-161235-37434a`.
Registration`20261002-160446-a8c61a` passed101.7s/2308MiB. Its Mathlib @depends tag
was wrongly project-qualified; the initial claim refusal and premature draft
preparation were explicitly logged. Forced claim was limited to this known
closed Mathlib dependency, and only the false docstring tag was removed; no
statement/index/lock was manually changed. New fixture
`0a0c1c5d526fcad2c52e568d365f371cd0417bcce5b585e2bb3443a534864702`
preserves the corrected source. First isolated compiler attempt
`20261002-160857-875240`,op`op-84b9a1cf3a664f95`, passed6.987s/2099MiB;
receipt`333521daa5e3b8454b2e1bdf01ce12b82c0da39ba305c3086b8b94b87080eee3`,
body`c8130cbf1650ebb32ba8920cced51e51b0bd5fa6bdd8188b5d2420550a0a8edd`,
source`62e6ef006680253fac61bfd2e660e111d7ec5c3d4bc41b2fd96f0a5676eb81b6`.
Original check`20261002-160958-802e30` passed48.6s/2369MiB/noOOM/missing,
CLOSED/sorryfalse/lock`3b42bbf38ce81b7c`, empty blockers and fresh full index.
Audit449/layers clean, temporary cache restored. Exact source preserved in
`RANK-PROFILES.accepted.lean.txt`. Endpoint-constrained finite maxima prove both
profiles for arbitrary coloring/support, without OneChange or cap restrictions.

Next reusable starting-layer mirror: with OneChange and no four-cap, take a bad
fiber triple x<y<z and an attained longest cup starting at z. Its next point w>z
exists because y,z give a two-cup starting at y and equal ranks imply rank≥2.
If y,z,w is a cup, prepend y to the attained cup, contradicting the equal rank at y.
Otherwise x,y,z,w is a four-cap. Thus the fiber is a cup; its minimum endpoint
bounds its size by the rank. Direct mirror of accepted L1 avoids introducing a
new Fin.rev coloring transport API. Search SEARCH-STARTING-LAYER.json found no
duplicate. This is a reusable semantic layer fact, not a proposed a5 cut.


Refined cross-gap B proof idea, before registration: under OneChange on L∪R,
no5cap there, no4cap in L, exact ending ranks on L, and any cup R ordered
strictly later than all of L, each ending-rank fiber A=L_i has no4cap in A∪R.
L1 makes A a cup. A four-cap in A∪R must then have exactly two A vertices
x<x' followed by two R vertices y<y'. Take a longest ending cup at x, with
penultimate w<x. The turn w,x,x' must be a cap, or that cup extends to x',
contradicting the equal ranks. Thus w,x,x',y,y' is a consecutive five-cap,
which OneChange promotes to a full five-cap, contradiction. Any later cup
works: the right starting-rank hypothesis of the hand-notes B is unnecessary.
This stronger form has a witness proof, not a fitted profile rule. It makes a
layer/later-cup union eligible for the accepted uniform diagonal bound, but does
not select the globally coupled cut E. Search SEARCH-LAYER-LATER-CUP.json found
no duplicate. Exact rank semantics and ambient no5cap/no4cap-side hypotheses
must remain visible in the registered statement.


2026-10-02 20:26 UTC: starting-layer mirror accepted/pinned at
`05f67bac8263d5ecee4f420fa25bd4621dcbf1a3`, commitjob`20261002-162510-b31bb6`.
Registration`20261002-161529-a18820`:rc0/102.7s/2316MiB. First isolated check
`20261002-162013-7dfa52`,op`op-69c0db530725434e`:7.637s/2102MiB,receipt
`9f0cb25cf5cde564ca38e8084ce09f641d4ba12bc56e6614f30f51fa80734b24`,
fixture`f95915fde074d24475bfa6ec6ce782585ea11f07bd8626111783926b069a56a5`,
body`de1f178ba80975665f02cd6ca566275f7dbe8a86188f18ccb9d4ab6f54caa708`,
source`b15ee58f0a9e77c36996dc049b01d3f88122d8a8a8aee905335d869aaffd5f21`.
Original`20261002-162242-46dc96`:rc0/47.3s/2374MiB/noOOM/missing,
CLOSED/sorryfalse/lock`d3a8de630d0f75e8`,fresh incremental full index,
empty blockers/nonstandard axioms,audit449/layers clean,private cache restored.
Exact source `STARTING-LAYER.accepted.lean.txt` supplies the mirrored attained
starting-cup layer/cardbound interface. The successor/prepend-or-four-cap invariant
is now Lean-certified, but the stronger flat-rank-pair law is only a recorded
proof inspection until separately exported. Next is the recorded stronger B
layer-plus-arbitrary-later-cup cap-freeness theorem; coupled a5 cut remains open.


Current checkpoint 2026-10-02 20:28 UTC: B branch
`node/NotContainsCapFourEndingCupLayerUnionLaterCup` created by
`20261002-162714-91c3f2` (DONE). Registration
`20261002-162742-075519` uses4GiB/review2min and is pending;
`LAYER-LATER-CUP.type.txt` records exact end-rank, no4cap-left, no5cap-union,
OneChange and ordered arbitrary-right-cup hypotheses. No claim or proof credit yet.
On resume, check that registration first, then claim before proof work. Temporary
private artifact-cache root is active and must be restored before commit.


2026-10-02 20:35 UTC: deeper invariant found before B compiler attempt.
For the cap-freeness conclusion, no4cap-left is unnecessary: a sorted four-cap
in A∪R has at most2 right-cup vertices, so its first2 lie in the ending-rank
fiber, and the predecessor extends it to5. Layer-cup status is unnecessary.
The supported es node restate requires two full-library extractions; retain and
close the already registered B contract, whose no4cap-left is present in the
intended application, and next export the broader general invariant with a
new registered statement. Do not edit the current type manually.

General cap-layer proof idea: under OneChange and no(a+1)-cap, each exact ending
rank fiber avoids an a-cap for a≥2. A cap's first two points have equal ranks.
A longest cup ending at the first has a predecessor w; its turn with those two
points must be a cap (otherwise extend the cup and violate the second rank).
Prepending w to the cap, through the abstract consecutive-turn invariant,
gives an (a+1)-cap. Starting ranks mirror this via a successor. This is not yet
Lean-certified beyond the registered no4cap-left B instance; it explains L1
as cap-arity reduction rather than a fitted fiber phenomenon. It could also
supply the classical binomial cup-cap recurrence by rank layers: each layer
has one smaller cap threshold and cup length bounded by its rank. These
ordinary cap/cup constraints still do not supply polygon-dependent lower-layer
deficiency or choose E. Keep the coupled a5 target open.


2026-10-02 20:45 UTC: B registration completed (106.4s/2310MiB), claim acquired. First isolated compiler job20261002-163755-073dae failed only at the new predecessor image-membership step: simp did not unfold the ambient let s. Diagnostic d38ea561211943e664f99c64d8ae35d005a1842fceeb8786716fe73f8ffa9192 and body01 preserved. Repair unfolded s, leaving the statement unchanged. Isolated retry20261002-164308-bd8a71/op-6c624768db0a41f8 accepted in11.857s/2106MiB, receipt72894241590e6f1bb0280344293eacf611535578632b1d440c77879d56285ff7; fixture24fc38b564b6ba9e4dd469fb1585110e914e289ed98a694dd33053f005a62869, body9d3586f75c2f4f1d70680d21cb72d717c63c0b7e00b15b17590d5a08482f5363, source52e3c50d876863b64d86464c42416d0485b79fd24654d70d9d02f99fb2166596. Exact bytes assembled via shared proof fixture APIs; original-module check20261002-164346-dd2bc2 pending. Claim active; private cache root must be restored before commit. No theorem credit until original extraction succeeds. This proves the predecessor/forbidden-five-cap argument once original checking finishes; it does not address polygon-dependent deficiency.


2026-10-02 20:46 UTC: B original source and extraction accepted: job20261002-164346-dd2bc2 DONE/rc0/54.9s/2361MiB/noOOM/missing, CLOSED/sorryfalse/lock74e49008b8f60c59, incremental index fresh, audit449/layers clean. Private cache root restored. Pinned commit 540d45ecce1821f24f9b5202b6943ca1551069fe, commitjob20261002-164511-e84f72 DONE; exact source LAYER-LATER-CUP.accepted.lean.txt. The no4cap-left hypothesis remains in the registered type. The cap-extension interpretation is Lean-certified for this contract; the coupled a5 cut remains open. Next is the recorded general cap-layer reduction with k≥2 and exact ending profiles, using min/next-min of a hypothetical cap and a forced longest-cup predecessor. No enumeration or fitted conjecture is planned.


Current operation checkpoint 2026-10-02 20:48 UTC: active branch node/NotContainsCapSetEndingCupRankLayerOfNoCapSucc from baseline6e4d0e66274e9d3dd1ccdbacf9fd747deb5e1d14. Registration job20261002-164618-e0ffcf is running; next check its terminal result, then claim ErdosSzekeres.notContainsCapSet_endingCupRankLayer_of_no_cap_succ before any proof body. Exact type CAP-LAYER.type.txt, empty search SEARCH-CAP-LAYER-REDUCTION.json, reused API LIB-PROOF-CAP-LAYER.json. No proof credit or current claim for this node yet. Private artifact-cache root active, restore before commit. Prior B node CLOSED/released, release handoff artifact4d18adb6f2ce77b6d51e716a7264d7baf75debaf42bfaddb04d239e0c5881041. General proof needs only min/second-min of a hypothetical cap, forced predecessor from equal ending ranks, and monochromatic cap prepend. Coupled a5 cut remains open.


2026-10-02 20:49 UTC: general ending-rank cap-layer node registered and claimed successfully; fixture7f10759c35f7759031f14566ad7fd1598644e2d6dac2e1792eb56ea9acc47235. The170-line candidate reuses endpoint cup append and the color-dual cap prepend proofs, then chooses min/second-min of the hypothetical cap. First compiler20261002-164900-359a92 failed only because a broad support rename accidentally changed Turn case label left to s. Diagnostic3946d953be5dfad2ecbb7157f353c9d71a6490e7bc409191191e791097fd7235, PROOF-CAP-LAYER-01.json and body01 preserved/logged before repair. Label repaired; unchanged statement/fixture retry20261002-164933-976692/op-81aead93df8a42fb running. No original source change or theorem credit yet. Active claim ErdosSzekeres.notContainsCapSet_endingCupRankLayer_of_no_cap_succ; private cache root remains active. This proof interprets equal ranks via endpoint extension, not via data fitting.


2026-10-02 20:51 UTC: general ending-layer reduction isolated retry20261002-164933-976692/op-81aead93df8a42fb accepted7.286s/2106MiB, receipt d4fb5495b3a46764fd2f21013f6338d502d5766d798ba9c659bca9272eacb36e, body301b0bab687f6a6931f871e59a6c7e406480d017dacd1d9ee17f4e96b6946a1a, sourceb655522c538d414f64686ea32f7735f026fafc113a21d91c8b0e4e932eb343e6, type lock1c666a869b5bd8c5. Exact bytes assembled; original check20261002-165014-106554 pending. Current claim still active.

Next cross-gap proof idea (not yet Lean-certified): under OneChange/no5cap, if a<b<c is a cap turn, an ending cup C at a and a starting cup D at c, both card≥2, must permit insertion of b into at least one cup. Refusal on the left forces cap(w,a,b) for C's predecessor w; refusal on the right forces cap(b,c,z) for D's successor z. Together with cap(a,b,c), OneChange gives a five-cap. This rank-free extension alternative explains the restricted layer-union A fact: local/global rank upper bounds exclude both insertions for each possible mixed cap triple. Formalize the alternative first rather than introduce a rank-heavy statement without its invariant. No proof of selecting E or of polygon-dependent lower-layer deficiency follows yet. Searches SEARCH-TWO-CUP-NONEXTENSIONS.json and SEARCH-CROSS-GAP-A.json preserve duplicate checks.


2026-10-02 20:51 UTC: general cap-layer theorem accepted and pinned at9ded8a3c582936b5530042e4c42bc08854d481fc, commitjob20261002-165138-4156fa DONE. Original check20261002-165014-106554 DONE/rc0/52.1s/2369MiB/noOOM/missing, CLOSED/sorryfalse/lock1c666a869b5bd8c5, no blockers/nonstandard axioms, audit449/layers clean. Cache root restored; exact source CAP-LAYER.accepted.lean.txt. The theorem uniformly proves no(k+1)-cap⇒no k-cap in every exact ending-rank layer, k≥2, without the no4cap-side hypothesis. Equal first two ranks force the predecessor turn; cap prepend excludes the hypothetical cap. This is accepted structural progress, not a proof of the a5 coupled cut. Next is the previously recorded rank-free two-cup extension alternative; no new ad hoc algorithm needed.


Operation checkpoint20:54UTC: current branch node/IsCupSetInsertOrInsertOfNoCapFive, registration20261002-165239-a9890f running with4GiB/review2min. Type TWO-CUP.type.txt states the cap-turn extension alternative with exact endpoints, two outer cups of card≥2, ambient OneChange/no5cap; no rank assumptions. No claim or proof body yet. Prior cap-layer node CLOSED/released at9ded8a3c582936b5530042e4c42bc08854d481fc; release handoff artifactf1b720b85761d03acf2a90df4cac2bbf17011e264ac6a458e896e1c949c0d93f. Temporary private-cache root active and must be restored before pinning. Two-cup branch job20261002-165223-36fbaa terminal; a mistyped observer job ID was refused and logged, with no execution effect.


2026-10-02 20:58 UTC: rank-free two-cup extension alternative accepted/pinned at4b1ac83c00c3bbe6987fa44df326a545b069c004, commitjob20261002-165813-627264 DONE. Original20261002-165556-4089f9 DONE/rc0/52.8s/2364MiB/noOOM/missing, CLOSED/sorryfalse/lock14e3c3517accb78f, no blockers/nonstandard axioms, audit449/layers clean; cache root restored. First isolated20261002-165520-4b443b/op-5ebf6e74318848f9:7.471s/2102MiB, receipt892b0c933fed2cb828aafb2805617a3c068980f4d641f213b380ef10e6b79a6f, fixture301dcc734028456ce91ae0ad141d994ee8a5b8797165336b632312451ff5d263, body0c1953f21c0700a585597019984516516c63598aaaadcaca34e914fceaf1d454, source8ea14e5fccd0c39e9a1ab72a387852ad89b511796d216d99449b704d1423ab19. Exact source TWO-CUP.accepted.lean.txt. Both failed insertions force predecessor/successor cap turns and a forbidden5-cap, so at least one outer cup extends to the middle point of a cap turn. Next cross-gap A uses local/global rank upper bounds to forbid both insertions. No proof of selecting E or lower-layer polygon deficiency.


2026-10-02 20:59 UTC: next exact A contract is CROSS-GAP-A.type.txt: OneChange/no5cap on ordered L∪R, no4cap on each side; exact local ending profile on L and starting profile on R; global ending/starting cup upper profiles (attainment globally not required). For i,j≥2, the union of ending-i left points with global-start≤j and starting-j right points with global-end≤i is a cup. Pure triples use L1; for each mixed triple choose an attained cup at its first/last point. A cap turn forces an insertion by the accepted extension alternative, but local equal ranks or global bounds at the middle point exclude both possibilities. Search SEARCH-CROSS-GAP-A.json empty. This supplies a structural explanation and formalizes the hand A fact; it does not establish the polygon-dependent lower-layer deficiency. Current branch is being created; no claim or proof body for A yet.


Operation checkpoint21:01UTC: active branch node/IsCupSetCrossGapRankRestrictedUnion; registration20261002-165949-beaa4f running with4GiB/review2min. No claim or proof body until terminal registration. Exact CROSS-GAP-A.type.txt includes i,j≥2, local ending/starting attained/maximal cup ranks, and global ending/starting upper profiles. Pure triples use the accepted two L1 directions; mixed cap turns force one insertion, which its local or global rank bound forbids. Both type and proof idea were recorded before registration. Prior two-cup node CLOSED/released at4b1ac83c00c3bbe6987fa44df326a545b069c004; release artifactd28279caba6be30b8d5bd7b5cddb8f7fa4c3dbadd3255ab015040ac1336d14a0. Private cache root active, restore before pinning. Registration waits must use actual returned IDs in a separate call; prior incorrect observer IDs were refused/logged without execution effect.


2026-10-02 21:06 UTC: A original checking accepted, but commitjob20261002-170543-6c2510 FAILED due to trailing whitespace; no A commit exists. HEAD6e4d0e66274e9d3dd1ccdbacf9fd747deb5e1d14 is the baseline, not a proof commit. This corrects the earlier premature pinned/DONE report. Original20261002-170405-a4676a DONE/rc0/43.7s/2367MiB/noOOM/missing; CLOSED/sorryfalse/lock8b7d14044ef6dedb, empty blockers/nonstandard axioms, audit449/layers clean; cache root restored. First isolated20261002-170255-106d6f/op-216b448b31e84e17:7.835s/2105MiB, receipt86a74650e0c564fef74399292d7e14109d20fae1d4285fbf94ddef7e1d74919f; fixture32b767ebc88dc1c240925ea3a9ea651a67b6f17134878c5b66a9c476efc9ab73, bodyf6df9b7250309281914a28b7007b5b5c5f214a320b7a520dd8ca174344391ba6, source9d6f1824aea263089860fee14e338f3281ae46b0ef1cb1f3d0b0e8dde95ed38c. Exact source CROSS-GAP-A.accepted.lean.txt, mathematical application body CROSS-GAP-A.main.lean.txt. Equal local endpoint ranks or global upper cup profiles exclude each insertion at a mixed cap turn; the no5cap extension alternative makes it a cup. This formalizes the hand A fact uniformly for i,j≥2. It also explains the next prospective ordinary bound: top c-layers unite into a cup of size≤c; lower layers each have capacity j, so total≤c². Desired c²−c+1 for c=K−1 still requires c−1 polygon-dependent savings. No proof of E.


2026-10-02 21:09 UTC: corrected final A acceptance: commit f3c45abfb7b6a9bfa68a2dcd8d8183e5ba9d72de, commitjob20261002-170857-802d4f terminal DONE/rc0; clean worktree and pinned file bytes verified against git. Exact final source863f2d375248dffec4d5fa513a45a62c3b0031fc9e2472bc7db639bbd4c1b890, body34ab9490003a25b882052b78fcd0258ae441265eff8c361680e0c2f5f9a28daf, fixturea8ce1b493179f2fa730469146422bc0d03f1e615e297323beb886dbbbd1240d4. Isolated20261002-170711-59d4f3/op-3d660aeef22f47c5:8.647s/2107MiB, receipt007f25493ea09b677b072c305415b6044bc1d7d94f89d38a992266ca0717b934. Original final20261002-170749-92dc59:rc0/42.8s/2371MiB/noOOM/missing, CLOSED/sorryfalse/lock8b7d14044ef6dedb, incremental fresh, empty blockers/nonstandard axioms. Original audit449/layer checks reused because the only intervening change removed whitespace on one blank line; no mathematical syntax changed. Cache root restored. Earlier compile receipts describe the unpinned whitespace variant, preserved as accepted-01-unpinned; first commit job20261002-170543-6c2510 FAILED, and its premature pinned report was corrected/logged explicitly. Final source CROSS-GAP-A.accepted.lean.txt now matches the actual proof commit. Cross-gap A is now closed; polygon deficiency and E remain open.
