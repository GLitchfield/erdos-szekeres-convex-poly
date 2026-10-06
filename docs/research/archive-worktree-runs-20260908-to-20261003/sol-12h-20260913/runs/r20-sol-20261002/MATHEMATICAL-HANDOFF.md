# R20 final mathematical handoff

Finalization checkpoint: 2026-10-02 23:41 UTC. Research ended early by Gavin and
the coordinator at **2026-10-02T23:34:36.971478Z**. The native goal is COMPLETE
on the supported requested deliverables; no further research is authorized. Finalization hard
stop is **2026-10-03T00:04:36.971478Z**, replacing the original timing contract.
Agent: `codex:agent-run-67caffbfbf804ebf`, configured gpt-6.1-sol/xhigh, no delegation.
Worktree: `runs/worktrees/sol-12h-20260913`; baseline:
`6e4d0e66274e9d3dd1ccdbacf9fd747deb5e1d14`. R19 was not modified.

The coordinator reports priority one closed, certified and reviewed. Exact
existing receipts and pinned source hashes were inspected again in finalization;
`FINAL-DELIVERY-EVIDENCE.json` records this read-only verification. The supplied
review reference resolves to
`4bbf154b6bba7c7dc701198f911ba271db32df5d803848761cffb29579e0d952`;
the full immutable inventory is preserved as `COORDINATOR-REVIEW-4bbf154b6bb.json`.
That inventory alone grants no theorem credit. No new research/check/commit was
launched after receiving the early-finish steering. The already-started optional
witness check was allowed to finish, as requested.

Earlier detailed chronology and failures remain in `PROGRESS.md`,
`MATHEMATICAL-HANDOFF-history-2331.md` and the older history/snapshots.
`INTEGRATION-GUIDE.md` explains independent branches and proof reuse.

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

General shape now gives a certified size exclusion: for j,u>=2, no(j+1)-cap
and no u-cup exclude a strong(u+j-2)-set, with no OneChange needed. Its cap
interiors number at most j-2, leaving a cup of size at least u. In particular,
each no4cap/no(c+1)-cup side already avoids strong(c+2). More generally at the
first active boundary a+u=k+4, a>=4,u>=2, the gap-side cap/cup bounds already
exclude strong k on each individual side. The parent polygon hypothesis has
content only for crossing sets, explaining why side-only counting stops.

At an arbitrary deep-below root, maximum crossing polygons form a Cartesian
product of lower cups and upper caps. The exact deletion criterion is now
accepted: if lower cups have size≤u and upper caps size≤a, deleting E removes
strong(u+a)-sets iff both residual children avoid them and either the residual
lower has no u-cup or residual upper has no a-cap. A crossing polygon partitions
into a cup and cap with bounded cardinalities summing to u+a, so both bounds are
attained. Conversely any surviving maximum pair forms a strong(u+a)-set.
All natural u,a are allowed, including zero; OneChange and child contiguity are
unneeded. Applying this to both colors of a cut gives the balanced hitting
condition. It does not construct the gap-compatible two-cup block or bound its size.

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
| `notContainsStrongPolygonSet_of_no_capSucc_no_cup` / NotContainsStrongPolygonSetOfNoCapSuccNoCup | 63630a8ff944fa91ee6ff71b42b4164c4e295d9d | 20261002-185308-b1999d | 4f6d1fea8323ea84 |
| `deepBelow_noStrong_after_delete_iff_child_and_rankDrop` / DeepBelowNoStrongAfterDeleteIffChildAndRankDrop | 75d0d5b1c34d6cc3b72f2a2347f41c88d00eb5b2 | 20261002-191226-3793b9 | 331d54a2d747be06 |

The uniform original check used13471MiB/908.5s; gate5681MiB/990s.
Later thin checks usedabout2.4GiB/38–63s. No OOM or missing outputs on these
accepted original checks. `CHECK-*.json` and `PROOF-*-RESULT.json` preserve the
full evidence; the chronological account gives every registration/commit job.

Twenty candidate receipts also have independent isolated audits and now exact
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

## Exact remaining obligation and mathematical limit

The coupled a=5 cut E and polygon-dependent lower-layer deficiency remain open
in R20. There is no complete proof idea for selecting a gap-compatible removed
two-cup block that meets maximum strong sets within the exact size budget.
For c=K−1, the rank argument gives c²; the target c²−c+1 needs c−1 savings
from crossing polygon avoidance. The easy short-side regimes are certified.
The hard regime has (c−1)-cups on both sides and at least one c-cup. Side-only
polygon exclusions are redundant there, so they cannot provide the savings.
This is the obstruction; no narrowing or diagnostic fit is credited as its proof.
This statement concerns R20's route, not the status of other research runs.

Failed routes are preserved with their exact semantics. Coordinator a5 notes
refute canonical second layers, pointwise signatures, endpoint/hook hitting and
local exchanges diagnostically; R20 did not certify those refutations. Reuse
`runs/claude-twoside-a5-20261002/NOTES.md` and
`runs/claude-twoside-a5b-20261002/NOTES.md` in the primary checkout.
Deep-below children may interleave. Existing
`HasDeepBelowSplit.isStrongPolygonSet_iff_inter_cup_cap` handles them;
contiguous-child assumptions do not cover the general root.

Meaningful compiler/infrastructure failures were logged before repair:
ambient implicit-argument inference; redundant omega steps; OrderedTriple Fin
bounds; mistaken constructor/member names; shared artifact-cache false-current
state; nested memory-cap refusal; accidental broad118GiB import closure; worker
PYTHONPATH absence; one whitespace-rejected commit and its corrected premature
pin report. Exact failed bodies, result files, diagnostics and job IDs remain in
the chronology/journal. No uncertain result is promoted into proof evidence.

## Optional size-four exception at the stop

Current branch is `node/ExistsTwoCupBlockDeletionCounterexampleAtFour`, HEAD
the baseline. Its source, blueprint import and generated harness metadata remain
uncommitted. The coordinator says this documentation-only node is unnecessary,
so it is excluded from the delivered pins and will not be committed/integrated
during finalization. The temporary artifact-cache override was restored exactly
to HEAD; `harness/config.toml` is unchanged.

The registered exact existential type has lock87337c6475ab9e1e. Its six-point
table has right codes014,023,024,025,034,123,124,125,134,135; cups012 and345,
OneChange/no4cap/noStrong5, and a strong0235 avoiding deletion14. The surviving
polygon is cup035 plus apex2. The first diagnostic probe wrongly demanded a
pure four-cup, found no witness among908 patterns and produced no witness file;
it establishes no universal pure-cup theorem. The corrected shared-pattern probe
`20261002-192237-469e36` supplied the documented strong-set witness.

Registration `20261002-192431-98fc38` passed104.8s/2314MiB. First proof check
`20261002-193111-319819` failed for a missing computable allowed-word Decidable
instance; the failed body/result are preserved. A local computable instance
fixed it. Isolated check `20261002-193320-1de692` /
`op-9dfa6a0723f24226` accepted9.148s/2102MiB, only standard axioms,
receipt7074b39251de0e0f746564b04c97033aaa3d255aa2a00ee43cce0cd9658c49de.
Fixtureaae661752e58b08161919176b51e855a0416f2b4ab7c50e5849b3d0e70f1570d;
bodya91be1e9c96f281b1cb4f6c1177f17922c078d2d6a337a5060c583b13c48326e;
source12c90edf1a1a97a273f2ec64eb5d0e9851c797aebac9c00c3c946815b4f3a14d.
Existing original check `20261002-193516-180bee` completed52.7s/2364MiB,
rc0/noOOM/missing, CLOSED/sorryfalse/type/std/lock, targeted fresh index.
`RESULT-DELETION-EXCEPTION-02.json`,
`CHECK-DELETION-EXCEPTION-ORIGINAL.json` and
`DELETION-EXCEPTION.accepted.lean.txt` preserve evidence. No native_decide,
new axiom, generated certificate or global evaluator was added.

## Review, maintenance and final operational state

The current proof and probe commands were self-reviewed in the separate
finalization window. Local turn checking proves its equivalence for arbitrary
selected triples; OneChange checks every increasing quadruple; finite cap/strong
checks range over every subset of the prescribed cardinality. The generic
strong checker is reused. The probe reused shared signotope enumeration rather
than creating a new generator. No recurring algorithm needs promotion here;
the witness table is one-off mathematics and remains with its artifacts.

Two prior workflow promotions are separate review units:
`7242b3e927bb256e61134285b6ca694fc87abf00` for observational dependency tracing
and `ba9b1946f0c9cd9dd3d0584c40d170b52026e2e1` for exact pinned-source identity.
Their tests passed and original artifacts remain in PROMOTED-* directories.
Independent coordinator review of these promotions and optional later helper
pins is not inferred from the priority-one review. No independent Astra review
or delegation was performed under this run's model restriction.

All23 pinned modules loaded together in guarded
`20261002-191637-234410`; no generated/certificate/unsafe/nonstandard-axiom
dependencies were observed. Absent sibling source owners remain explicit in
the traces. Hash observations and combined loading are not source-to-olean
attestations; individual original checks are acceptance evidence.

Exception research window `window-a1b632f326b847a8` ended with zero delivered
targets. Finalization/maintenance window `window-d75628b9a0134796` also ended0.
Usage is synchronized, including failed work and setup, with an explicit
active-response/late-reporting caveat. No matched-work savings claim is made.
Factual operation/usage bundle: `EARLY-FINALIZATION-OPERATION-HANDOFF.json`.

Final read-only inventory `FINAL-REVIEW-INVENTORY.json`, immutable artifact
9f242132277c81348574a4391c87caca21503b54304a6a52a97cefdca0607d32,
confirms zero pending/unknown jobs and active claims. Of its13328 artifact
scripts,13315 are private Lake cache payloads, seven are preserved promoted
helper files and six are the previously reviewed tracer, audit driver and
combined-loading files. Last benchmark/probe/registration/check inline commands
were read and their exact semantics/failures reviewed. The inventory grants no
theorem credit. Usage snapshot has922 recorded responses,939942 output tokens
and455988 reasoning output tokens; active/final response usage may still lag.
The native goal completion receipt records3,386,075 tokens and23,824 elapsed
seconds (6h37m), frozen at the pause; finalization usage is recorded separately.

All R20 child jobs are terminal and no jobs are queued. The native outer host
`20261002-125731-43d19d` remains live to receive this final report. The optional
witness claim has been released. The requested outcome was partial, but the
harness normalized it to closed from the compiled environment; the source is
still uncommitted and excluded from delivered pins. FINAL-WITNESS-RELEASE.json
records this distinction. The shared primary handoff already differed, so the
harness preserved this exact handoff as immutable release-evidence artifact
9241cb74cd5e254565a4bf8c07f9f6d8fc52d62581e161a335897b84be6c74fc
instead of overwriting it. A final named snapshot is preserved locally.
No merge or push was performed.
Safest next action: integrate the two reviewed priority-one pins using the
repository node workflow, resolve generated metadata, then select useful helper
exports for independent review. Do not bulk-apply the independent metadata diffs
or infer an a≥5 proof from them.
