# R20 mathematical handoff (live checkpoint)

Updated 2026-10-02 19:32 UTC. This is an interim account, not the final report. Research
deadline 2026-10-03T04:57:32.670035Z; consolidation starts 04:27:32.670035Z. Researcher
`codex:agent-run-67caffbfbf804ebf`; no delegation, merge, push, or R19 modifications.

## Exact obligation and current evidence

`diagonalCupBlocksForce4kk_of_five_le {k : ℕ} (hk : 5 ≤ k) : DiagonalCupBlocksForce4kk k`
is registered and claimed, type lock `7b9515ee94a1f04b`, on branch
`node/DiagonalCupBlocksForce4kkOfFiveLe`, from baseline
`6e4d0e66274e9d3dd1ccdbacf9fd747deb5e1d14`.

The original module `ESBlueprint/B/DiagonalCupBlocksForce4kkOfFiveLe.lean` now compiles
without any sorry, native_decide, or new axiom: build `20261002-132244-93d40c` DONE rc0,
13s compiler and 6s final build stage. The independent isolated audit accepted the entire
parent with exactly the standard axioms `propext`, `Quot.sound`, and `Classical.choice`:
receipt `2b5071d2df886b644d452b8bc716cf3ac73db93d01092c5a9903b939b820a5a0` in
`UNIFORM-PROOF-RECEIPT.json`. Byte identity, type lock, body hash, and unchanged baseline
lock values are checked in `UNIFORM-IDENTITY-VERIFICATION.json`.
Full original-source check `20261002-133903-34a3cd` is DONE rc0, 908.5s, peak 13471 MiB.
`CHECK-UNIFORM-ORIGINAL.json` reports **CLOSED**, `sorry=false`, standard axioms only,
`lock_ok=true`; full status is fresh and problem-free. `es audit` passed 449 records,
and `es layers` found no violations. Pinned commit
`c89df0e8605272ad2484600507ce342c8cf5f421`, job `20261002-135617-abf673`; claim released
CLOSED, with this handoff preserved by the harness in the primary checkout.

The singleton lower Pascal-tail gate for all k ≥ 5 is now CLOSED and pinned at
`82a570723fc014cbd192dee18fa19e8f7a1a15dc`, commit job `20261002-142049-0a7a45`.
Full original-source check `20261002-140250-5b9883` passed (990.0s,peak5681MiB):
`CHECK-GATE-ORIGINAL.json`,sorry=false,lock`5ef1de5a24229d34`,standard axioms only.
Audit449 records passed, layers clean, full status fresh, source/config clean.
Dependency trace `20261002-141800-9a57e9` passed (7.3s,peak2526MiB), no generated/certificate
or unsafe constants; exact source/olean hashes in `GATE-CERTIFICATE-DEPENDENCY-AUDIT.json`.
It replays the exact accepted uniform proof as a local fact, then the existing gate
consumer. Baseline branch `node/SingletonLowerPascalTailGateFourDiagonalOfFiveLe` was
created by `20261002-135725-ce21d1`; registration `20261002-135755-288083` passed.
Temporary config is restored. Earlier stub check `20261002-140014-f8bdd8` was cancelled
after the default python shim blocked prerequisite body assembly; worker acknowledged
termination, output `CHECK-GATE-STUB-CANCELLED.txt`. Recovery used system Python3 and
shared `es.proofs.whole_span`, asserting the frozen body hash before writing.
First body check `20261002-140108-3db947` failed only at final implicit gate application;
`intro n χ q upper` repairs it, preserving the accepted uniform proof. Failure is logged
and preserved in `CHECK-GATE-01.json`.
General shape `strongPolygonSet_capMiddle_partition_of_no_cap_succ` is registered/claimed
on `node/StrongPolygonSetCapMiddlePartitionOfNoCapSucc`, baseline branch creation
`20261002-142202-e4c67a`, name alignment `20261002-142613-9be446`, registration
`20261002-142331-026251` passed with incremental index update and no config change.
Its proof is accepted: **original-source check `20261002-142724-7d87f7` passed** (37.6s,
2359MiB peak), `CHECK-SHAPE-ORIGINAL.json`: CLOSED,sorry=false,lock`875d3f763cb1a39a`,
standard axioms; full index fresh,audit449/layers clean. Pinned commit
`96d751150ddbc6881b183ba1fd9ef2735c46fa2c`, commit job `20261002-142923-2b3f38`.
First check
`20261002-142640-b8193a` failed only on redundant omega after simp solved a cardinality
identity; `CHECK-SHAPE-01.json` preserves it and the journal records the repair.
L1 `cupLayer_of_no_capFour` is registered/claimed on `node/CupLayerOfNoCapFour`, baseline
branch `20261002-143241-acd196`, registration `20261002-143309-6c98f9` passed. Its exact
rank profile hypotheses are attained ending cups plus maximality for all ending cups.
Complete proof body submitted: **check `20261002-144348-9f7819` failed admission** (6G,thin targeted
incremental), output `CHECK-LAYER-ORIGINAL.json`. First check `20261002-143744-d29f7b`
failed only at two leading-dot field applications; named sequence terms repaired them.
`CHECK-LAYER-01.json` preserves the failure, logged before repair. The20G corrected retry
`20261002-143900-22e707` never started, was cancelled with acknowledged termination,
and was replaced by the identical6G check using measured~2.3GiB thin peaks. Shared status
confirmed R19's20G job plus two2G hosts blocked the20G reservation. The6G attempt failed
before Lean with rc125: dependencies_built=false requested the conservative20G child.
Diagnostic `20261002-144822-672566` found all oleans present but a shared artifact-cache
writer reservation occupied by R19. No check is live. Temporarily isolate this worktree's
cache root under this run, preserving guards and unchanged core/extractor fingerprints;
rerun dependency currency then the identical proof, and restore config before pinning.
Evidence `DIAG-LAYER-DEPS.json`, `CHECK-LAYER-02-ADMISSION.json`. No coverage dropped.
Recovery diagnostic `20261002-145515-f967eb` confirmed current dependencies.
**Check `20261002-145546-60d9cc` passed**,62.6s,2374MiB,noOOM; receipt
`36ab2c8ad5e69de0807106dd854cb8d2b8e695ec8c2d778369e81e3637616504`:
CLOSED,sorry=false,lock`732a647456a876b8`,standard axioms. Full index fresh,
audit449/layers clean; cache policy restored. Pinned commit
`e6df7d76733f7c9328e09c8cc0673f3383a46e61`, commit job `20261002-145855-e0a82c`.
Observational dependency audit `20261002-145812-e7dddb` passed8.8s,2176MiB:
4527 reachable type/value constants, no generated/certificate/unknown project modules
or unsafe constants, standard axioms. `LAYER-CERTIFICATE-DEPENDENCY-AUDIT.json`
pins source/olean/trace hashes. Standalone insertion
M1 left insertion is registered/claimed on `node/IsCupSetInsertOfTwoLeftVertices`,
branch `20261002-145949-8981cd`,registration `20261002-150027-f9c6cd`. Exact frozen
H1/insertLeft replay accepted by isolated check `20261002-150252-5aab30`
(8.356s,2101MiB),receipt`851f9616df290f3c405b3f4f6b697051fb80a2c695f5ab17ba868e27ffb3b53a`,
type`c005da92ee73f667`,standard axioms. **Original check `20261002-150329-e8a6e0`
passed**,47.7s,2364MiB,noOOM,CLOSED,sorryfalse,lockOK,std axioms. Full indexfresh,
audit449/layers clean,temporary cache policy restored. Pinned commit
`2d993f82ddb2e375bc9f8cec4e67ed676f053879`,commit job`20261002-150514-abe971`.
M1 right mirror registered/claimed on `node/IsCupSetInsertOfTwoRightVertices`,
baseline branch`20261002-150554-a4584f`,registration`20261002-150606-56a9eb`.
Isolated check`20261002-150840-174b47` accepted6.989s,2102MiB,receipt
`079645d649bb97acae721ea059bef3b3015766ad16e3abef62208a99419b4b8c`,
type`1f0b9577a357c8a2`,standard axioms. Original check`20261002-150906-d6ab01`
**passed**,47.1s,2366MiB,noOOM,CLOSED,sorryfalse,lockOK,std axioms. Full indexfresh,
audit449/layers clean,temporary cache restored. Pinned commit
`b982195a6ec50d8f54d936ef28a5c87cdb7ec536`,commit job`20261002-151036-f6a892`.
Double moves remain unregistered;
apply shielding twice and include exact card increase by2 when both new points are absent.
M2 left registered/claimed on `node/IsCupSetInsertTwoLeftAndCard`,baseline branch
`20261002-151111-b9282f`,registration`20261002-151130-6295ce` passed104.7s,2310MiB.
Failures `PROOF-MOVE-DOUBLE-LEFT-01/02.json` are spelling and redundant-tactic issues
in the cardinality step, preserved/logged before repair. Corrected isolated check
`20261002-151533-fe8b0a` accepted6.331s,2100MiB,receipt
`5802b652a35312e5e2b718a995ce34fbfcf42a542b71c4b6be7aefef6470ef15`,
type`d62a250e6f1ffb0e`,standard axioms. Original check`20261002-151606-c31d96`
**passed**,46.5s,2369MiB,noOOM,CLOSED,sorryfalse,lockOK,std axioms. Full indexfresh,
audit449/layers clean,temporary cache restored. Pinned commit
`8acb61b2af6c99eda48c11a14a9e1bc82ec7c287`,commit job`20261002-151735-b076cd`.
M2 suffix is registered/claimed on `node/IsCupSetInsertTwoRightAndCard`,baseline branch
`20261002-151818-5ccfeb`,registration`20261002-151832-b9a551` passed. Isolated check
`20261002-152156-45c180` accepted5.551s,2100MiB,receipt
`6004c54069467e9dcea27490e174d6a48789de908f2370c999665a262de126af`,
type`6375458bcedfe290`,standard axioms. Original check`20261002-152242-418f37`
**passed**,44.7s,2372MiB,noOOM,CLOSED,sorryfalse,lockOK,std axioms. Full indexfresh,
audit449/layers clean,private cache restored. Pinned commit
`5070599d3dc3d0a0029906fb204f9dead193a8e9`,commit job`20261002-152442-181ba4`.

## Why the uniform theorem is true

Additional H3 invariant now registered/claimed as
`isStrongPolygonSet_cup_union_cap_of_common_extremes` on
`node/IsStrongPolygonSetCupUnionCapOfCommonExtremes`,baseline branch
`20261002-152522-29bb7c`,registration`20261002-152547-3512f4` passed97.6s,2312MiB.
Cup C and cap D share both extreme endpoints, OneChange holds on their union; no
cap-cardinality restriction. Interior endpoint-anchored colors determine every mixed
triple by a neighboring color switch; equal labels identify one pure hull. Isolated
check`20261002-152922-db1055` passed first try7.434s,2099MiB,receipt
`045ab4399fa5f4c6a581942c874b99a08633b2e85ed5e0c21420670165fa52c1`,
type`c07e8cd85ed7d9af`,standard axioms. Original check`20261002-153032-82183a`
**passed**,45.8s,2367MiB,noOOM,CLOSED,sorryfalse,lockOK,std axioms. Full indexfresh,
audit449/layers clean,private cache restored. Pinned commit
`ddd9dea56692bc7d94deeb20717ee3bbdd2844bf`,commit job`20261002-153215-9853f9`.
This is an accepted multi-apex reconstruction tool, not an a5 cut.

The strengthened card bound is `|left|+|right| ≤ 2*k-4` for arbitrary disjoint ordered cup
sides whose union satisfies OneChangeOn, avoids a 4-cap and avoids a strong k-set.

H1 proves that equal consecutive turns propagate to every triple, for either color, by
strong induction on the outer index span. An intervening point supplies a smaller first
and last triple; OneChange makes equal outer turns force the two spanning turns.

H2 uses middle determinacy of a strong set. Every interior middle can be compared with the
two extreme endpoints. If two interior middles were cap-colored, those middles together
with the endpoints would give a 4-cap. Thus the set is a cup or a cup with one apex erased.
H3 proves the converse by pinning mixed-triple colors: changing middle entries in an allowed
four-turn sequence pins both outer entries. A cup plus an apex with a cap through its two
endpoints is therefore middle-determined and strong.

The insertion rule is more uniform than the paper's two named moves: any left-cup point
with two selected left-cup points above it can be inserted into a cup. The two selected
points shield every new consecutive triple from crossing the gap. Apply it twice for the
double prepend. The right version uses two selected points below the new point.

Claim D is proved locally for second-left point p after p0 and penultimate-right point q
before q0. Every strong S of size at least five avoiding p,q extends to size |S|+1. If S
is a cup, one side has at least three selected points and takes its deleted point. For a
cup plus apex, a side with at least two cup points forces the corresponding extreme
endpoint: otherwise double prepend/append gives a larger cup. A side with at least three
cup points then takes the deleted point while preserving the apex cap. What remains has
exactly two cup points per side and one apex. Either the first or last new cross turn is
a cup and gives a five-cup core, or both are caps and yield a forbidden 4-cap. Source
compilation of Claim D is recorded by `20261002-132033-ab3346`.

The card induction uses the existing k=5 theorem. In a hypothetical oversized block each
side has fewer than k points (otherwise that side alone supplies a strong k-set), and
both sides are large enough to select p,q. Delete those points. Claim D rules out a strong
(k−1)-set in the remainder; all other hypotheses are hereditary. Induction bounds the
remainder by `2*(k−1)-4`, and restoring two points gives `2*k-4`. The prescribed adjacent
block sizes total `2*k-3`, completing the original uniform target.

No decomposability or generated-certificate theorem is part of this mathematical argument.
The existing k=5 base is the hand-built cup-block theorem. Actual transitive proof dependencies
are now supported by observational trace `20261002-141330-ba1b81`: 6030 reachable
type/value constants, no generated or ESCertificates modules under the unchanged harness
catalog, no unsafe constants, only standard axioms. Evidence is in
`UNIFORM-CERTIFICATE-DEPENDENCY-AUDIT.json`; this trace is not new theorem credit.

The gate derivation does use its existing decomposable singleton-root hypotheses:
avoiding a parent 4-cap makes each ordered gap side avoid a 3-cap, hence be a cup.
Their diagonal Pascal reservoir has total size `2*k-3`. The uniform block theorem
contradicts the gate's three avoidance assumptions. At a=5 the sides merely avoid
4-caps and may have many cup layers; this is why the same direct induction does not
automatically settle that family.

## Verification jobs and infrastructure

- Host job `20261002-125731-43d19d` is the live native-goal host.
- Original uniform dependency trace `20261002-141330-ba1b81` is DONE (6G,11.8s,2508MiB),
  `TRACE-DEPS-UNIFORM.json`/`.log`. Script `TraceProofDependencies.lean` is an observational
  runtime inspector, using the extractor's ConstantInfo type/value dependency API.
  It adds no project mathematical statement. Small Init/Nat.add_comm test passed in
  `20261002-141228-197454`:43 constants,405ms runtime,611MiB whole-job peak.
  Original olean SHA256 `d4d7c8e615ebcf74c9e5c35fabf3fc082c06e8a7a78323378b48b37bd314060f`.
  Classification with existing `es.modules.scan_modules` passed: no generated/certificate
  or unknown ErdosSzekeres modules, no unsafe constants; source catalogs unchanged.
  Review this generic runtime inspector separately before finalizing the research run.
- Serial root materialization `20261002-132649-e50025` hit the synchronous build guard.
  Background recovery `20261002-133827-ebe4aa` completed in 9s from the immutable cache,
  without regeneration. A cache count or successful process exit earns no theorem credit.
- Isolated proof audit `op-ae2b922e3fc947cf`, job `20261002-132715-7f609b` (12G), is DONE.
  Fixture `b2fcef784528e943778afd620983db87396689d21099938c91fc93dcc5d0f755`; exact body
  `3b87e1173243301273650ad6156d08891ad101d3be2aea36839408aeb4f4f261`. Accepted in 12.09s,
  peak 2444 MiB. Full original-source check `20261002-133903-34a3cd` is DONE under its
  28G guard, output `CHECK-UNIFORM-ORIGINAL.json`. It became terminal at the first review;
  the raced review refusal and correction are recorded. No full coverage was dropped.
- The node's import closure is 28.4 GiB. Targeted extraction rejects anything above 4 GiB;
  a temporary closure-admission adjustment enabled registration under the unchanged 12G
  extraction cap. It was restored. Full registration initially failed because the whole
  core root olean was absent. Raising the targeted setting invalidates the baseline core
  fingerprint, so full root materialization and full extraction are the safe final route.
- All temporary config settings are restored, including baseline `memory_max_final=30G`.
  Do not patch the index or fingerprints.

## Failed approaches and reusable repairs

No mathematical conjecture failed in this formalization so far. Meaningful compiler failures
and infrastructure failures are all in `es journal` and their outputs under this directory.
Unrestricted simp_all on the local color-switch helper spent the heartbeat budget simplifying
the whole context; explicit eight-case analysis fixed it. Coordinate equality alone did not
rewrite an opaque OrderedTriple; explicit eta expansion fixed the three mixed cases.
The `not_imp` name needed qualification. Opaque local cup aliases required explicit
`mem_insert_of_mem` witnesses instead of simp. A first proof-body assembly used UTF-8 byte
offsets as character offsets, failed its pre-write assertion, and made no source edit;
subsequent assembly sliced bytes using the shared `es.proofs.whole_span` API.

The paper's deletion lemma is false at size four, so no argument here lowers the base to
k=4. This is a genuine known obstruction; see `CUPBLOCK-PROOF.md`.

## Next cases

There is presently no uniform a=5 proof idea to formalize. Both diagnostic note sets explain the
missing ingredient: a jointly chosen tight gap-compatible removed two-cup block, with the
exact size budget. Local point statistics and canonical layers do not choose it. Do not
commission new narrowing without an explanation of why it should be easier.

The general strong-set shape is reusable: a cap through the endpoints and all cap-colored
middles has size `2 + number of those middles`. Under no (j+1)-cap, that number is at most
j−2. The cup layer proof uses a longest ending cup at x: a cap x<y<z in the same layer would
either extend that cup to y or create a 4-cap with its penultimate point. These are genuine
proof ideas for tools, not a proof of the missing a=5 split.

## Safest resumption

Read harness status, the relevant node journal, PROGRESS.md, and this account. Both primary
theorem and gate are pinned and their original-source checks terminal. The next obligation
is L1 (canonical cap-middle partition is already pinned), then standalone moves.
All node branches start from `6e4d0e66`, without sibling merges. The gate's local induction
keeps it self-contained; after integration it can call the uniform theorem directly.
L1 exact check and dependency audit are accepted, pinned at `e6df7d7673`.
All requested M1/M2 tools and general H3 are accepted/pinned. Review additional
reusable layer tools, with explicit proof ideas before registration; a5 cut remains open.
Rank fibers alone do not
solve the coupled a=5 cut. Revalidate new jobs before retrying or reporting.
Revalidate every newly recorded job
before retrying, and review the runtime dependency inspector in a separate maintenance window.


Maintenance checkpoint 2026-10-02 19:50 UTC: primary research window
`window-1dbf3b5a506149ca` ended with the accepted results above; the native goal
remains active until its research deadline. Separate maintenance window
`window-9cc69ab671434f81` reviewed the observational dependency inspector and
repeated classifiers. Generic traversal and owner-aware identity receipts are
promoted to `tools/es/lean/TraceProofDependencies.lean` and
`tools/es/es/proof_dependencies.py`, catalog `research.lean-proof-dependencies`,
with a guarded runnable example and regression fixtures. The original inspector
and traces remain unchanged under this run. Source and olean hashes are observations,
not an attestation that one was built from the other, and grant no theorem credit.
Sol self-review obeys the developer no-delegation restriction; independent
coordinator review is still pending.

Tests `20261002-154318-4ae882`: 17 passed. Nat smoke
`20261002-154347-ffad00`: unchanged 43-constant closure, correctly owns
`Nat.add_comm` in `Init.Data.Nat.Basic` although `Init` was imported.
Project example `20261002-154522-2a7466`: DONE rc0, 14.1s, peak2191MiB,
no OOM/missing outputs. `MAINTENANCE-PROJECT-DEMO/receipt.json` pins the
71-constant `TurnSequenceAllowed.all_eq_of_outer_eq` closure and actual owner;
no generated/certificate/unknown project modules, nonstandard axioms, or unsafe
constants. Initial admission refused the 6GiB job because reservations were 38/40GiB;
queuing unchanged cap succeeded. No other run was modified.


Maintenance pinned at `7242b3e927bb256e61134285b6ca694fc87abf00`, job
`20261002-154857-93bed3` DONE rc0. This separate commit follows the H3 proof commit
and can be reviewed/cherry-picked separately. Maintenance window ended; new
research window `window-7b4248f877f74097` begins structural layer tools.

Next reusable obligation: under OneChange on a finite support, equality to one
fixed color on all triples consecutive in that support implies equality on every
triple. Induct on the outer index span; an interior point in either gap supplies
two smaller triples, whose equal outer turns force the whole quadruple constant.
This exact H1 argument is already accepted locally in the uniform proof; expose
it as a standalone theorem to support cap/cup chain extension in later layer
arguments. Search found no abstract finite-support duplicate: existing Chains
results use sweep realizability or fixed small cardinality. No coupled a5 cut
is asserted. Registration input `CONSECUTIVE.type.txt`, replay body
`CONSECUTIVE.body.lean.txt`, searches `SEARCH-CONSECUTIVE.json`.
