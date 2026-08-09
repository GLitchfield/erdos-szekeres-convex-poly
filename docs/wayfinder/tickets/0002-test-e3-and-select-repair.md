---
title: Test E3 and select a repair strategy
type: research
mode: AFK
status: open
claim: codex-e3-adversarial-2026-08-01
blocked_by: none
---

## Question

Is `DecomposableExactUpperAt k` true for the repository's abstract recursive
deep-below model for every `k ≥ 3`, and, if so, which strengthened invariant
has the best bounded evidence for repairing the failed published induction?
If it is false, what is the smallest counterexample, and is that counterexample
sweep-realizable by an actual planar point configuration?

## Decision criteria

- Treat the truth and falsity directions symmetrically.  A search that only
  reproduces expected extremal examples cannot select the proof route.
- Use the exact repository definitions of `HasDeepBelowSplit`,
  `IsDecomposableOn`, cup, cap, and strong polygon.  Record separately whether
  a generated abstract coloring satisfies the signotope law and whether it is
  known to be realizable by straight-line planar points.
- First perform an exact exhaustive enumeration at the largest feasible small
  size, deduplicating colorings rather than merely sampling decomposition
  trees.  The producer and independent checker must not import one another.
- The default computation budget is 30 minutes, 8 CPU cores, 16 GiB RAM, and
  5 GiB under `runs/`.  Deterministic shards, seeds, conventions, and coverage
  counts are required.
- A counterexample branch advances only with a compact coloring/decomposition
  certificate independently checked against every defining predicate.  It
  refutes the repository's E3 statement only if sweep realizability is also
  certified; otherwise it redirects the abstraction boundary.
- A proof branch advances only when a candidate invariant survives exhaustive
  small cases, explains the `(4,5,5,1,3)` boundary regression, has an explicit
  inductive transition, and yields a nontrivial compiling Lean lemma.  Pattern
  agreement or reviewer consensus is not enough.
- Classify an inconclusive search by its exact coverage bound.  Do not infer
  the all-`k` theorem from a finite negative search.
- Before selecting the route, obtain a bounded blind and reciprocal Sol/Fable
  review of the evidence packet, then independently dispose of every material
  objection.

## Candidate strategies under review

1. **Endpoint-profile injection.** Refine the scalar cup/cap maxima by left and
   right endpoint-extension states, and inject vertices or recursive blocks
   into the `2^(k-2)` binary profiles.
2. **Rank-downset compression.** Start from the classical injective map from a
   sweep vertex to its cup/cap predecessor downset.  Search for the additional
   pairwise restriction imposed by recursive deep-below structure and absence
   of a strong `k`-gon.
3. **Context-carrying induction.** Repair the three-parameter recurrence by
   carrying an external cup/cap supplied by ancestor blocks.  A saturated
   off-diagonal child must pay for the binomial term that currently overflows.
4. **Minimal-counterexample descent.** Assume a smallest E3 counterexample,
   choose its root split, and use the exact crossing characterization plus
   saturation/straddling lemmas to contradict minimality or expose a smaller
   rooted counterexample.
5. **Falsification.** Enumerate recursive colorings and optimize/SAT-search for
   more than `2^(k-2)` vertices with no strong `k`-gon, then separately test
   signotope and straight-line realizability constraints.

## Resolution

Open.  The published scalar induction cannot be used: Lean checks a boundary
instance where the claimed two contributions are eight and the outer threshold
is seven.  Local endpoint transitions compile, but no global profile count has
yet been proved.  This ticket deliberately reopens the theorem's truth value
instead of assuming that an endpoint repair must exist.

The first falsification round is complete through eight leaves.  Independent
implementations agree on 186,888 distinct eight-leaf colorings, none of which
contradicts the proposed five-vertex base lemma.  All recursively decomposable
colorings are now proved in Lean to satisfy the signotope law, and the existing
nine-point LRAT certificate consequently proves
`decomposableExactUpperAt_five`.  The all-`k` statement remains open; the
reciprocal Sol/Fable route review and the general anchor-context transition are
still pending.

Both off-diagonal `k = 6` states are now closed in Lean.  Generated semantic
bridges connect kernel-checked LRAT proofs to
`exists_cap_four_or_cup_six_or_strong_six` on twelve vertices and
`exists_cap_five_or_cup_six_or_strong_six` on sixteen vertices.  Restriction
promotes them to the hereditary invariants `decomposableStateUpper_466` and
`decomposableStateUpper_566`.  The audited dual-state reduction then proves
`decomposableExactUpperAt_six : DecomposableExactUpperAt 6`.

The large sixteen-vertex proof is represented by 256 kernel-checked
checkpoints rather than one monolithic Lean declaration.  Its committed
segments contain the complete 496,453,316-byte trimmed LRAT trace and compose
to a proof of the empty clause.  This settles the finite `k = 6` milestone but
not the ticket's all-`k` question; selecting and proving a uniform strengthened
invariant remains open.

The semantic side is also complete and independently checked.  Its 155,064
canonical clauses are covered by 769 semantic chunks, 4,096 raw aggregation
modules, and 1,024 midpoint modules.  Short named midpoint propositions form a
compact root, and Lean accepts a single `rfl` bridge identifying that tree with
the checkpoint's full clause proposition.  The independent checker in
`scripts/check_e3_state566_aggregation.py` reparses the DIMACS source and
verifies every range, proposition, import, alias, hypothesis, elimination
leaf, and root association without importing either generator.

A bounded reciprocal Sol/Fable review of the pre-redesign aggregation packet
had SHA-256
`1c50d5ec1789727a630e1f34579968d11389cc2af3d26cb9e8ee3dd300f9247a`.
Both reviewers returned `partially_supported` at medium confidence and asked
for the independent whole-data checker, the named-proposition proof shape, a
successful root build, and an axiom audit.  All four checks are now complete.
Lean reports only `propext`, `Classical.choice`, and `Quot.sound` for
`decomposableExactUpperAt_six`; no project axiom or `sorryAx` occurs.  This
disposes of the material aggregation objections but does not answer the open
uniform all-`k` question.

A fresh post-six reciprocal review now selects one narrower next obligation,
not a uniform route.  Against packet SHA-256
`09beb042e541117ef77f30f73353e91f5c0dae50968753eb216f2b347584ca55`,
both final reviewers converged at `partially_supported`, medium confidence, on
formalizing the hereditary diagnostic
`decomposableStateUpper_455 : DecomposableStateUpper 4 5 5`.  They agree that
the proposed context state is still undefined, minimal-counterexample descent
is circular without such a rooted state, and a global endpoint injection lacks
both completeness and injectivity.

The review's finite gate has been independently discharged.  The canonical
eight-vertex `(4,5,5)` signotope instance has 56 variables and 1,134 clauses
(CNF SHA-256
`56ea4a13b8f976fbb266ef58e8a8c7074de38e08a201fda0477b59642abc49c1`).
CaDiCaL 1.7.3 returned UNSAT with a 39,037-byte LRAT trace (SHA-256
`5401621fc275e55a42077cecd293b5b303969da341bd6a0dc25973eaf5287861`),
and a temporary Lean `FromLRAT` probe kernel-checked it in 4.4 seconds.

The selected theorem is now complete. The CNF and LRAT data are committed,
eight generated semantic chunks connect all clauses to the repository
predicates, and an independent checker reconstructs the aggregation directly
from DIMACS without importing either generator. Lean proves
`decomposableStateUpper_455 : DecomposableStateUpper 4 5 5` and its dual
`decomposableStateUpper_545`; both have only `propext`, `Classical.choice`, and
`Quot.sound` in their axiom audit. This certifies that the `8 > 7` regression
is a proof-method defect, but it remains explicitly diagnostic rather than the
missing uniform transition.

The all-root directional context-profile replay is complete through eight
leaves. Two independent implementations agree on 243,102 compatible roots,
1,896,168 anchor/four-chain records, 4,343,048 restriction comparisons, and
all canonical hashes. Same-gap and cross-anchor summaries have open
composition collisions. The complete all-gap word has no open `k = 5`
collision in the covered range, but the generalization fails at the next
nonvacuous probe: a targeted `k = 6`, `n = 9` singleton-root search finds
2,055 collision observations among 85,797 open parents. A compact certificate
contains two explicit decomposition trees with equal child words and unequal
parent profiles, and a separate checker reconstructs every defining
predicate. Candidate B's maxima-only state is rejected. The live redirect is
to a correlation-preserving rank/downset state or a bounded transition
congruence that separates this pair; neither route is selected until bounded
Sol/Fable review is disposed and its first transition is stated precisely.
The fixed-ambient definition layer has begun in Lean:
`ContainsCupSetAtGap.mono` and `ContainsCapSetAtGap.mono` compile and preserve
the same directional chain witness under subset enlargement.  The maxima
aggregation and collision theorem remain pending.

The first clean advisory review attempt used packet SHA-256
`5ba9b4a4b2ad34b02486a2593dfc03d0ac5383007e46c77951d60cb4928ab6d2`
at revision `48cb924`. Sol returned `partially_supported`, agreed with rejecting
maxima-only candidate B, and recommended a concrete singleton-root
rank/downset falsification gate before a replacement Lean transition. Fable
was unavailable because its provider returned repeated HTTP 429 session-limit
responses; reciprocal critiques did not run. This is not reviewer consensus,
and the replacement route remains unselected.

The requested rank/downset falsification gate is now complete at the first
nonvacuous singleton-root target `k = 6`, `n = 9`. A deterministic producer
and an independently written full replay agree on all 186,888 decomposable
upper-child colorings and 85,797 open parents. The ordered child downset word
has 9,535 collision observations, and even the complete child pair-rank matrix
has 481: in each case equal child state produces unequal parent state. Raw
parent downsets remain vertex-injective in every covered parent, but the exact
34-vertex compatibility graph has a maximum clique of size 27, exceeding the
target `2^(6-2) = 16`. Thus deterministic rank-state composition and the
pairwise incompatibility counting shortcut are both rejected. Higher-order
rank restrictions and realizability-sensitive transitions remain logically
open; at this stage the witnesses had decomposition trees but no planar
realization certificate. No replacement uniform route is selected pending bounded
Sol/Fable review of this gate.

The first Sol audit returned `partially_supported` and agreed with all three
bounded rejections. It correctly identified two provenance/semantic gaps in
the first packet: the certificate called its pre-generation commit simply
`revision`, and both full implementations used the same rank recurrence. The
certificate now calls that value `generation_base_revision`, binds the exact
producer source by SHA-256, and the checker verifies it. A new direct-chain
oracle exhaustively checks every triple coloring through five vertices at
clips one through five against the dynamic ranks and downsets, with zero
differences. The audit's remaining scope warnings agree with the ticket:
abstract decomposability is not planar realizability, and the observed
injectivity does not prove or refute the global counting theorem. A clean
post-disposition review remains pending before selecting the next Lean package.

The clean corrected packet at revision `bbafd69` has SHA-256
`b52e93af2a71e4cb1da99de9429a52ff752a86d3871a1a2a3343994384042d8a`.
The combined provider stage exhausted its 30-minute limit without an answer;
a standalone 15-minute Fable retry likewise produced zero bytes and left no
live process. This is recorded as provider unavailability, not consensus. It
does not reopen the independently replayed finite facts, but it prevents a
claim of completed Sol/Fable review.

The smallest assumption-safe Lean package recommended by the successful Sol
audit now compiles as `ErdosSzekeres.RankProfile`. It specifies pair-rank
thresholds using actual `CupCap.IsTurnChain` witnesses and defines clipped
vertex downsets in the fixed ambient order. Its monotonicity, threshold,
rank-one, and lower-closure theorems require only an arbitrary triple coloring
and audit to `propext` and `Quot.sound`. This removes the shared Python
semantic obstruction without selecting a uniform route. The next formal gate
is a kernel-checked bounded theorem exhibiting the `k = 6`, `n = 9` pair-rank
non-congruence; realizability was left as a separate question, now closed by
the next paragraph.

That bounded theorem is now complete in
`ErdosSzekeres.RankProfileCollision`. A structural decomposition-tree coloring
avoids treating the witnesses as opaque truth tables. Lean proves both trees
are well formed and decomposable, checks the singleton root, proves absence of
a strong six-set through an executable checker equivalent to
`IsStrongPolygonSet`, and verifies equal complete child states but unequal
parent states. Exact rational coordinates with `x_i=i` realize both colorings,
with minimum absolute orientation determinant one. The combined theorem uses
only `propext`, `Classical.choice`, and `Quot.sound`. Thus the complete
pair-rank matrix is not a transition congruence even in the straight-line
realizable subclass. Higher-order predecessor correlation remains the live
rank-based direction, but no uniform state has yet been selected.

The realizability boundary is now closed for the full recursive class, not
only for the collision witnesses. `ErdosSzekeres.DecomposableRealization`
proves a fixed-abscissa merge theorem for arbitrarily interleaved
`HasDeepBelowSplit` parts: one finite vertical-shift parameter preserves
both child colorings and enforces every crossing orientation. Induction gives
`IsDecomposable.isSweepRealizable`, with strict general position and no
external oracle. Therefore a realizability-sensitive repair cannot distinguish
any abstract decomposable parent; the next rank-based candidate must instead
retain genuinely higher-order predecessor correlation and pass a `k`-only
state-count gate. The conclusion realizes the coloring; preservation of the
same tree as coordinate-level `IsGeometricallyDeepBelow` witnesses is a
strictly stronger statement and is not claimed.

A bounded blind provider review of this bridge used packet SHA-256
`98e8213b03d9aa12146c2690d7fad234d8e4a76da0cb65089df46fabd87fe706`.
Claude Fable 5 and Codex Sol both returned `partially_supported`, at medium and
high confidence respectively. Both supported the displayed theorem, manually
rechecked the six crossing signs, and agreed with treating it as a negative
model-boundary result. Their qualification was that the packet omitted the
existing determinant/general-position helpers and build evidence; `make test`
subsequently built 9,630 Lean jobs and passed all workflow checks, while the
axiom audit found only `propext`, `Classical.choice`, and `Quot.sound`. The
reviewers also required the now-explicit `IsGeometricallyDeepBelow` scope
qualification and agreed that no higher-order route is selected until its
finite carrier, transition, and `k`-only count are stated.

The first higher-order candidate was the depth-bounded pair turn-language
spectrum, which forgets pair endpoints after retaining every consecutive turn
word. A bounded provider review at revision `2d07250` returned
`partially_supported` from both Claude Fable 5 and Codex Sol. Both reviewers
identified the missing `k = 6`, depth-four gate and endpoint incidence as the
cheapest falsification targets. The targeted replay then found an open
seven-vertex collision: equal lower spectra through depth four produce unequal
parent spectra after adjoining vertex `6`. Full singleton replay at depth
three also found 35,858 open collisions outside the originally tested extreme
root positions. The plain spectrum is therefore rejected by its own stop rule.

This negative result and its semantic explanation now compile in Lean.
`TurnLanguage.lean` defines chronological pair languages from actual
increasing chains, proves a kernel-reducible predecessor recurrence correct,
and shows that a constant new turn composes exactly through incoming languages
at the terminal endpoint. `TurnLanguageCollision.lean` proves both witness
trees decomposable and open, checks equal lower spectra and unequal parent
spectra, and isolates `right,right,left` at pair `(5,6)`. The incoming-star
spectrum separates this collision and the older pair-rank witness in
exploratory gates, but remains unselected: an arbitrary interleaved root needs
prefix-indexed star information unless a new theorem shows that global open
star types determine every relevant prefix. The next bounded decision is that
prefix-control test, with failure redirecting away from deterministic quotient
refinement rather than adding another color-refinement round.

That prefix-control gate is complete through eight vertices at
`(k,d)=(6,4)`. A deterministic recurrence producer and an independent
direct-chain checker agree on 153,648 open root observations and 122,156
fixed-root inputs, with zero collisions in root-relevant prefix queries,
ordered child-star sequences, or parent incoming-star spectra. Lean proves
cut causality and depth truncation for pair languages and incoming stars. A
six-vertex positive theorem confirms that the quotient can identify distinct
open decomposable colorings while preserving the covered transition data.
These are finite facts and semantic infrastructure, not a uniform theorem or
a state-count bound.

The closest negative control is now also kernel-checked. Two open decomposable
eight-vertex colorings have equal global depth-three incoming-star spectra but
different prefix spectra at gap seven; depth four separates them. Thus no
parameter-free spectrum argument can recover prefixes. The first Sol audit of
the new gate returned `partially_supported` at high confidence and recommends
testing conditional parent-transition sufficiency before attempting
strong-six-open prefix recovery. A clean Fable retry is still pending, so the
incoming-star route remains unselected.

The conditional transition attempt first isolated and proved its crossing
case. `IncomingStarTransition.lean` shows that every crossing pair language is
the forced split turn appended to its first endpoint's parent incoming star,
and proves the corresponding pair-language congruence. The remaining
same-child case is now refuted rather than merely difficult.

`IncomingStarTransitionCollision.lean` kernel-checks a fixed-root
nine-vertex collision. Its smallest pair has equal complete upper-child pair
languages, equal child spectra, and every equal root-relevant prefix, but the
parent pair `(7,8)` gains different words and the parent spectra differ. A
second structural pair proves the same failure with both parents recursively
decomposable. Both of those parents contain a strong six-set. Consequently
neither the split algebra nor decomposability/signotope structure makes the
incoming-star state a transition congruence. Strong-six-openness is the only
untested escape, but adding it to the sufficiency theorem collapses the
planned separation and leaves no plausible route to a `2^(k-2)` state count.
The deterministic quotient route is stopped by its declared incidence-
refinement rule. The next bounded route decision is minimal-counterexample
descent versus structural charging.

That route decision is now complete. A clean blind Sol/Fable review at
revision `b90dd3f` used packet SHA-256
`97f73c43b09f0c591ad43e6a7bed3f034b906c3196b6a7cc375cbf9a1a51c47a`.
Both reviewers returned `supported` and selected structural charging. The next
theorem is the certificate-free upper-child gap trichotomy: seven decomposable
upper vertices and an external singleton anchor force a five-cup, four-cap,
strong five-set, or a three-cap for which the anchor is a sweep endpoint. The
endpoint case extends across the root to a parent four-cap. Success requires a
compiling proof without LRAT or coloring-space enumeration and a mechanical
derivation of the singleton-root `(4,5,5)` bound. Failure of either condition
stops this target.

The first structural core now compiles in
`ErdosSzekeres.StructuralChargingCore`. For normalized vertices `0 < ... < 6`,
a cup on `{0,1,2}`, a cup on `{3,4,5,6}`, and the one-change law force a
four-cap, five-cup, or strong five-set. The proof has seven named turn branches
and no generated certificate or coloring-space enumeration. The remaining
ticket item was the order-embedding transport to arbitrary `3+4` blocks and
its mirrored `4+3` case. `ErdosSzekeres.StructuralChargingTransport` now proves
both, closes `CupBlocks34Force455`, and derives the certificate-free
singleton-root `(4,5,5)` cardinal bound seven. The next gate is whether the
exposed gap-side witness mechanism scales to the first `k=6` boundary.

That first boundary calculation now compiles in
`ErdosSzekeres.StructuralChargingBoundary`. Absence of an endpoint four-cap
makes both sides of the singleton anchor four-cap-free. Applying the existing
`(4,6,6)` theorem to each side independently proves only the coarse parent
bound `1 + 11 + 11 = 23`, while the diagonal `k = 6` threshold is 16. The
seven-vertex deficit is therefore specifically a missing cross-gap coupling,
not a missing unary side bound. The next proposal must pass a bounded coupled
gate before any uniform recurrence is claimed.

The separated-cap, common-cut, endpoint-port, and explicit-tree allocation
round is now complete. Lean proves local capacity two, summed lower incidence,
and unique lowest separating-node allocation inside a fixed tree. Exact
enumeration through eight vertices refutes both the immediate crossing-cap
outcome and its disjoint repair, while 1,295,559 ordered crossing-cap chains
show the coefficient-two bound is sharp.

A blind Sol/Fable review of the proposed weighted overflow-token route
completed at packet SHA-256
`1a879cf0be9c3bceec4d9ec5e514b4f73a0a9650bfb85435b93e9c79a08899ae`.
Both reviewers returned `not_supported` with high confidence: the semantic
owner and resource identity of an overflow unit are undefined. Their suggested
follow-ups were stale. The singleton `(4,5,5)` boundary is already closed
locally by `singleton_root_card_le_seven`, and the recorded kernel-checked
nine-vertex collision already stops deterministic incoming-star refinement.

A corrected audit used question SHA-256
`116946c9457e8592da499dadaed8cd028562e85ee109429c49b06c90be2ceb80`.
Sol returned `partially_supported` with high confidence: no finite
classification is yet well-posed because the combinatorial family counted by
the child summands has not been defined. The next single work item is semantic
specification recovery: define `ChildContribution` using the coloring, a fixed
tree and address, child state, side, and a concrete resource; establish that
its finite family has the advertised child-summand cardinality; and formulate
restriction/composition and stable ancestor-identity obligations. A later
bounded census may test extraction and reuse only after those meanings are
independent of the desired conclusion. The corrected Fable run hit an external
session quota without returning a valid review, so no corrected consensus is
claimed. The Sol review is advisory route evidence, not a proof.

The missing source semantics have since been recovered and kernel-checked.
`PublishedInductionSemantics.lean` defines the maximal child parameter,
constructs its actual retained vertex subset, and proves the exact
complement-plus-core inequality. It proves for every `2 ≤ a ≤ k` that
auxiliary index one forces the whole nonempty child to be a singleton. The
specific `(4,5,5,1,3)` branch then composes with
`singleton_root_card_le_seven`, yielding the sharp parent bound seven without
a finite certificate. This disposes of the corrected Sol audit's semantic
blocker rather than inventing a token type. The next single route-selection
item is a bounded classification of the remaining positive auxiliary indices
below the active Pascal-window endpoint, followed by a fresh Sol/Fable review
of one exact structural transition contract.

That bounded classification is now complete through `k = 20`, with a
deterministic certificate and an independently implemented replay. Among
7,752 feasible scalar failures, removing the index-one singleton cases leaves
6,120 states; every one has one saturated auxiliary parameter and the other
strictly below the dual active-window endpoint. The first state is
`(4,6,6,3,2)`, with complementary child sizes `(2,10)` or `(3,9)` and scalar
defect five. Lean now proves those exact arithmetic and cardinality facts, the
general semantic bridge saying that complementary child sizes force the two
adjacent thresholds to exceed the outer threshold, and the all-parameter
saturation classification. Its proof allocates nonsaturated child thresholds
to disjoint prefix and suffix regions of the outer Pascal row. The geometric
transition remains open. A fresh Sol/Fable review must now freeze a uniform
saturated-boundary contract and test it first at this smallest state; no
consensus is claimed while Fable's provider quota remains unavailable.

The first cross-split resource at that state is also kernel-checked and
certificate-free. `first_saturated_boundary_has_covering_upper_three_cap`
uses the ordinary `(3,6)` cup--cap theorem to extract an upper three-cap; if
the parent avoids four-caps, the deep-below endpoint transition forces that
single cap interval to cover every lower-child vertex. The underlying theorem
is uniform in the cap size and arbitrary, potentially interleaved lower
children. This does not yet close the saturated branch: the review must specify
how the covering-cap resource is consumed or transported in the induction.

A preliminary high-confidence Sol audit (`partially_supported`, packet
SHA-256 `5ea929b9570f6240368833758b05f82e215814abc783ceb03e42a73b9142a88a`)
supports the saturation proof but identified two verification gaps that are
now disposed: the independent checker directly replays the greatest-index
definition at every feasible interval endpoint, and Lean explicitly proves
the two saturation alternatives mutually exclusive. Its remaining concern is
the real route question: no definition yet links a covering cap to retained
core/remainder demand, irreversible consumption, or nonreuse at comparable
tree addresses. Fable returned no review because its provider quota remained
exhausted, so this is not Sol/Fable consensus and no transport contract is yet
selected.

The first saturated gate has since closed by a simpler certificate-free
argument. `upper_card_le_eight_of_nonempty_lower_open_466` proves that an open
`(4,6,6)` parent with nonempty lower child and decomposable upper child has at
most eight upper vertices. It chooses one lower vertex, proves its two upper
gap sides are cups (an endpoint upper three-cap would extend to a parent
four-cap), and invokes the symbolic `4+5/5+4` cup-block theorem. Therefore the
feasible `(2,10)` and `(3,9)` child pairs are impossible without state-466 or
state-566 certificate consequences. The parameterized theorem
`gap_sides_avoid_cap_of_no_parent_succ_cap` identifies the candidate uniform
kernel for the next review: both gap sides are `r`-cap-free when the parent
avoids an `(r+1)`-cap. The cup--cap duality layer is now independent of the
finite-state modules, and `lower_card_le_eight_of_nonempty_upper_open_646`
eliminates the reversed `(10,2)` and `(9,3)` child pairs as well. A missing
Fable response remains a recorded review gap, not a blocker for further Lean
lemmas or bounded counterexample work.

The next `k = 7` arithmetic layer has now been replayed and partially closed.
The certificate-free theorem
`upper_card_lt_twice_cup_parameter_of_nonempty_lower_open_four` eliminates
the `(4,7,7,3,2)` child pairs `(2,15)` and `(3,14)`, and duality eliminates
their reversals. The sharper `2*(u-1)` count also eliminates the 13-vertex
alternative at `(4,7,7,3,3)`. For upper sizes 11 and 12, the exact
`5+6/6+5` cup-block contract, reversal, transport, quantitative payoff, and
actual application shell compile. The normalized proof has been reduced to
two explicit residual leaves, `CupBlocks56ResidualA` and
`CupBlocks56ResidualC`. Residual A now compiles in full through explicit cup,
cap, and strong-seven witnesses; only residual C remains open. External UNSAT
evidence supports the complete normalized proposition but is not a proof.
Sol's transport-shell objection has been discharged and its seven-chain/fan
proposal implemented; Fable returned no answer because of provider quota.

The residual frontier has since closed completely in Lean. Residual C uses
forced bridge turns, an explicit seven-cup branch, and a two-six-cup
strong-seven branch. The normalized eleven-vertex theorem, both arbitrary
block orientations, the upper-child bound ten, every `(4,7,7,3,3)` child
pair, and all color-dual pairs now compile without importing a SAT
certificate.

The active state is `(5,6,7,4,2)`. A bounded blind review at packet SHA-256
`39ac2acb7aae73c84889f20e0006569b42e630166a1253665ec2d9a2509fa9bc`
returned `partially_supported` from both Sol and Fable: the proposed
two-four-cap-free-sides bound is a sufficient application contract, but its
truth was unsupported. That exact dependency now compiles as
`TwoCapFreeSidesBound567`, together with its conditional upper bound 21,
elimination of child pairs `(2,24)`, `(3,23)`, `(4,22)`, and color-dual shell.
The first conceptual reduction also compiles: the ordinary `(4,6)` cup--cap
recurrence is promoted from consecutive chains using `OneChangeOn`, bounding
each side by 15. Any counterexample to 21 therefore has both side sizes in
the residual interval `[7,15]`, formalized as `TwoCapFreeSidesCore567`.
Lean also proves that such a residual pair contains four-cups on both sides
and a five-cup on at least one side. The completed `4+5/5+4` theorem turns
those witnesses into either a four-cap meeting both sides or a strong six-set.
The one-vertex extension layer now compiles as explicit cap and strong failure
certificates. A cap failure localizes to a consecutive triple; five-cups force
right bridge colors to the opposite side, with a proved nesting law. Strong
polygons now have the kernel-checked equivalent formulation that every triple
color is determined by its middle vertex.

A second bounded Sol/Fable packet at SHA-256
`d7611ab3099cfc0088afed4463db4628c3f93067ffea722002350e9bdf6f1a69`
returned `partially_supported` from both reviewers. Small independently
validated SAT models refute the unconditional identical witness-profile
collision proposed as the first counting lemma. A new eager encoding based on
the middle-determinacy equivalence nevertheless resolves the previously open
22-point cuts: cut 10 is UNSAT in 277.550 seconds and cut 11 in 289.393
seconds, each with one blocker for every seven-subset. Together with the
earlier cuts and the validated sharp 21-point model, the full abstract local
contract now has bounded computational support. These UNSAT runs have no
checked proof certificate and imply no Lean theorem.

The live proof target remains a conceptual proof of the 21 bound, now using a
global count over five-cup bridges, consecutive cap failures, middle-color
disagreements, and triples among outside vertices. The predeclared fallback
preserves decomposability or root-relative cross-gap data.

The sharp cap-charge selector has now failed its bounded gate. On each of the
validated 21-point cuts 6, 10, and 11, no crossing four-cap admits even the
permissive matching of outside vertices to nine capacity-two realized
signatures: the best ranks are 15, 13, and 14. Independent replay validates
the ambient assignments, maximum matchings, and Hall-deficient sets. The
selector's desired `2*9-1=17` capacity is also logically circular at total 22,
where a selected four-cap has 18 outside vertices.

A bounded Sol/Fable review at evidence-packet SHA-256
`52f4db63c5a7c2bd0c748a090ed8b6fba056b14cf0dff2335a6c5e468f5fb0f7`
rejects that route and supports separating the strong-six and no-strong-six
cases. `StructuralChargingWitnessBranches.lean` implements the reviewed
replacement. Hereditary transport of the kernel-checked 16-vertex `(5,6,6)`
certificate closes the no-strong-six branch outright, with bound 15. At the
sharp boundary it also proves that every six-point deletion leaves a strong
six-set, giving every designated strong six a disjoint partner and mutual
middle-extension failures.

The sole remaining strong-six work is now split more finely. Unless the cut
is exactly `11+11`, one cap-free side has at least 12 vertices. The checked
`(4,6,6)` state forces an internal strong six there, and order forces every
opposite-side middle failure into the corresponding endpoint role. The new
`StructuralChargingStrongSixSignature.lean` theorem proves that cap-four and
cup-six avoidance leave exactly one right-colored internal middle position,
so only four polygon signatures survive. The other branch is the fixed
`11+11` obstruction. Deterministic SAT countercontrols refute bare two-five-cup,
strong-six-plus-four-cup, and strong-six-plus-cap-free-seven block theorems;
the full large-side and balanced-side structure is essential. These are route
controls, not completed results.

Endpoint-failure normalization now compiles as well. A right-side failure
relative to a left internal strong six either disagrees with one of the four
internal middle reference colors or varies inside the final-middle fan. If
two fan entries differ, the one-change law forces the earlier fan color and
the bridge between their polygon endpoints to equal the later endpoint's
polygon-middle color. Lean now indexes the internal cases by `Fin 4`, adds the
final fan as a fifth constructor, and proves that every forced endpoint
failure realizes one of these five classes.

The direct quantitative follow-up is false. The deterministic endpoint-class
analyzer, run on independently replayed sharp 21-point models at cuts 6, 10,
and 11, finds a class realized by all ten opposite vertices at cut 10 and a
class realized by all eleven at cut 11. Some cut-11 strong sixes require
uniform assignment capacity four across the five labels. The route may still
use the proved fan transition, but it must couple successive opposite vertices
to unused large-side vertices rather than bound label repetitions alone.

The exact `11+11` exception is now refined by the same checked 12-vertex
state. For every vertex on either side, adjoining it to the opposite side
produces a four-cap through that vertex or a strong six. If that strong six
does not use the adjoined vertex, it is internal and the endpoint branch
applies. Consequently the only balanced leaf left after endpoint redirection
has a through-cap or through-strong-six witness for each of all 22 vertices.
Lean proves that the endpoint branch plus this through-witness branch implies
`TwoCapFreeSidesBound567`. It now also removes the adjoined vertex from each
witness: a through-cap is exactly a three-subset residue and a through-strong
six is exactly a five-subset residue of the opposite side. The final reduction
accepts this incidence-normalized residue branch directly.

The first residue-coupling layer now compiles. Two vertices sharing a cap
three-residue have a monotone pair profile, hence one of the four exact words
`LLL`, `LLR`, `LRR`, `RRR`. Two strong-six extensions over a common
five-residue glue to a strong seven if their pair profile is constant and all
base-middle extension colors agree. The latter agreement is automatic away
from the first base vertex. A first-middle discrepancy forces a constant pair
profile, so no-strong-seven leaves an exact dichotomy between pair variation
without first disagreement and constant profile with first disagreement.
Ordered-cut and mirror specializations expose these laws to the balanced
branch. An all-right cap profile now explicitly completes a cap five.

These transition laws do not supply a repetition bound. Independently checked
SAT controls retain a full eleven-vertex cap-free, no-internal-strong-six side
and find both shared cap and shared strong residues with two and three external
vertices while avoiding `(5,6,7)`. Minimal controls allow ten vertices on one
fixed cap residue and all eleven on one fixed strong residue. The next
balanced target must therefore couple distinct overlapping residues. Lean now
proves the first such incidence fact: among any three five-residues inside an
eleven-set, two share at least two vertices. The pending bridge must force at
least three strong-residue witnesses from the 22-point strong-six packing and
then resolve the shared-pair agreement case.

The packing-to-residue bridge is now isolated exactly. Every strong six left
after a prescribed six-vertex deletion crosses the balanced cut in one of the
five splits `1+5`, `2+4`, `3+3`, `4+2`, or `5+1`. The extreme splits are
equivalent to strong-five residue carriers. If all three middle splits are
excluded, any six purported carriers can be deleted at once; packing then
produces a fresh extreme carrier. Lean therefore proves at least seven total
carriers, at least four on one side, and three ordered strong-five residues
whose bases contain an overlapping pair. Thus the missing packing bridge is
no longer a vague multiplicity question. Its exact remaining premise is a
middle-split obstruction: each `2+4`, `3+3`, or `4+2` crossing strong six must
force a target outcome or yield an extreme replacement. Only after that
premise is discharged does the shared-pair agreement case become active.

The symmetric `3+3` follow-up has now been audited and reduced. A bounded
Sol/Fable review at evidence-packet SHA-256
`3b1bc9f5737ee6c33e3566dce112466e2c1da93be961a0d13339a668e44ef53d`
agreed that deletion-preserving extreme replacement has a quantifier gap.
Lean settles the reviewers' disagreement about the local middle word: under
cap-five and cup-six avoidance it has weight one or two, since three right
positions form a cap five through the strong-six endpoints. A deterministic
12-point SAT model, independently replayed, refutes the claim that two
disjoint `3+3` crossing strong sixes force a target outcome. The surviving
compiling transition deletes the first polygon and retains a disjoint partner,
mutual middle obstruction in all twelve directed extensions, the partner's
five-way crossing split, and weight-one-or-two words on both polygons. The
crossing normalization is now also compiled: each directed failure has three
side-aware states, with the extreme role's comparison core forced entirely
onto the probe's side of the cut. The next target must combine these localized
cores with the bounded middle words and crossing split types.

That combination is now a compiling local state. Raw roles normalize to
indexed middle anomalies, boundary fans, internal fans, or fresh-middle fans.
The nominal class type has 19 elements. Arbitrary anomaly endpoints either
canonicalize or create a same-index fan, and one-change turns canonical,
boundary-fan, internal-fan, and fresh-middle-fan classes into explicit bridge
equalities. Replay on the checked `3+3` model rules out a capacity-one count on
these indexed labels. All 19 classes now supply one common four-vertex bridge
certificate, and deletion packing supplies all twelve directed certificates.
Interior certificates anchor to the color of their three-polygon frame, so
two probes on one frame have equal outer-pair colors. Exhaustive five-vertex
checking refutes every stronger bare-certificate conclusion involving a
triple through both probes and refutes a forced strong five. The attempted
three-probe repair is also false. Independently replayed SAT models can avoid
a shared frame in either or both directions. More decisively, a model with
shared frames in both directions has no extreme `1+5` or `5+1` strong six.
The independent checker directly validates the local one-change, cap, cup,
strong-seven, mutual-obstruction, and `3+3` split assumptions. This remains
computational route-selection evidence rather than a Lean theorem. Local
bridge-certificate refinement is retired as the main route. The bounded review
selected global packing conditionally, but its broad form is false on fully
packed sharp models and a proof-core shrink of the no-internal `7+8` state
still needs 704 deletion clauses. Stronger geometry does not remove the local
countermodel: explicit rational coordinates now give the compiling theorem
`middleSplitRealizationColor_isSweepRealizable`. The remaining SAT properties
are not promoted to Lean. Both modest repairs are retired, so the pre-vetted
fallback is a new uniform E3 invariant with an all-root falsification gate.

The first residual-state oracle under that fallback is complete. Two
independent implementations exhaust all 186,888 decomposable eight-vertex
colorings and all 18 singleton root contexts at `k=6`. The 5,917 immediate
property-relative all-gap observations refine to 7,159 residual classes. The
oracle separates the committed all-gap profile collision by an interior
rooted cup-extension response, but it does not separate the complete pair-rank
collision. The full residual word is therefore retained only as a discovery
oracle. A bounded blind Sol/Fable review at packet SHA-256
`4058cc55c5850b4630e70a9b413a8773bdbc0251ba00f87cbab7138e5ea7d304`
returned `partially_supported` at high confidence from both reviewers. Both
reject selecting an invariant before defining the critical-cut container,
domination quotient, retained endpoint incidence, and `k`-only bound. The
selected work item is only the bounded specification gate: test critical-cut
convexity, then exact singleton observation and self-composition congruence,
with a two-vertex interleaved-root gate required afterward. The candidate
route itself remains unselected.

The bounded specification gate is now complete, with a necessary correction
to the reviewed sketch. The unlabelled critical-cut set is generally the union
of two rays and is not convex. Lean makes the endpoint side explicit, proves
the two ray-closure laws and their disjointness for an external singleton,
recovers the exact existing cup/cap singleton-extension iff, and supplies a
concrete counterexample to unsplit convexity. The corrected structured carrier
stores maximum cup and cap length at each exact total endpoint span. Two
independent implementations exhaust all 186,888 decomposable children and all
3,363,984 singleton extensions at `k=6`: the footprint reconstructs every
direct observation, its singleton transition has no collision, and it
separates both the all-gap and consecutive pair-rank regressions. This passes
the singleton semantic and self-composition gates, but the raw 46,699-class,
ambient-quadratic carrier has no `k`-only count. The candidate route therefore
remains unselected. The next formal target is the uniform span-rank singleton
transition, followed by the required two-vertex interleaved-root test and a
dominance quotient with a proved `k`-only weight.

That semantic and interleaved-root follow-up is now complete. Lean defines
exact sweep spans and cup/cap span-rank thresholds and proves the full
singleton decomposition: endpoint comparisons, left/right rank updates,
erase/recover iff laws, the size-three opposite-color branch, and terminal
strong-`k` creation from a child strong set or `(k-1)` chain. Independently
implemented programs then exhaust all 10,596 decomposable seven-vertex
children under all 72 two-vertex root contexts at `k=6`. All 762,912 parent
transitions, including 720,528 in 68 interleaved contexts, have equal outputs
for equal child footprints. This closes the smallest feasible two-root gate,
not the uniform route. The footprint remains indexed by ambient endpoint
pairs. The next bounded contract is to define a dominance quotient, its exact
incidence-preserving equality, and a `k`-only weight, then replay both committed
collisions and the existing singleton/two-root tables. Any ambient-cardinality
dependence or transition collision rejects the quotient.

The first formal subobligation of that contract now compiles in
`SpanDominance.lean`. Rank thresholds are antitone, and four sidewise theorems
prove that, at a fixed far endpoint, a span with no smaller rank and a near
endpoint farther toward the singleton supplies every extension supplied by
the dominated endpoint/rank pair. Thus directional Pareto pruning is
semantically sound for both cup and cap singleton transitions. This is not yet
the promised quotient: the retained frontiers remain indexed by ambient far
endpoints, and no theorem yet preserves shared-endpoint incidence after
identification or bounds the carrier solely in terms of `k`. The next bounded
item is to define that concrete incidence carrier and falsify it against the
committed collisions and existing transition tables before attempting its
`k`-only counting theorem.

That concrete gate is now complete and rejects the first quotient. The
candidate stores clipped global exact-rank histograms, the proved directional
frontier tags, and the clipped multiset of coarse endpoint-incidence types. Its
carrier is finite in `k`; at the eight-vertex boundary it merges 80 of 46,699
raw footprint classes, separates both regressions, and has zero collisions in
all singleton contexts. The small two-root gate also passes, although the
candidate is injective on its seven-vertex raw states. The reserved raw
`8+2 -> 10` census then covers all 16,819,920 parents and has zero raw
footprint collisions or observation mismatches, independently replayed.

The quotient fails that same large gate: 320 cross-fiber transition
collisions are reproduced independently from only 14,400 representative
parents. The first swaps exact ranks three and four between `(0,7)` and
`(1,7)` and is distinguished after roots occupy `[1,2]`. Every failure touches
the first or last internal gap. Exploratory exact-boundary repairs reduce the
failures, but any tested clipped boundary rank count strong enough to remove
them is injective on all 46,699 raw classes. The quotient is retired. A fresh
bounded route review must now decide whether to make the root cut an explicit
finite interface, prove or refute finite-depth boundary stabilization, or use
the raw footprint only as local machinery in a structural count.

The fresh review was completed at packet SHA-256
`593e6f8cc88c4c7d7c26175f5d1a864472af90f80e179aa0c83ab783d5cc8aa6`.
Fable and Sol both selected a final Rooted Interface Definition Contract gate
and required redirection to structural counting on a collision or injectivity.
The frozen candidate stores exact recursive left/right side footprints and a
finite multiset of crossing exact-rank ports whose distances from the cut are
clipped at depth `d`. A complete eight-vertex class census shows that depth
three is noninjective at every cut, including 1,710 merged fibers at the
middle cut. It nevertheless fails the rooted `8+2 -> 10` transition: lower
roots `[0,5]`, with the second root distinguished, give equal child signatures
and unequal open parent signatures. The independent checker reconstructs the
witness from coloring bits. Depth four is injective on all 46,699 raw classes
at that same cut and therefore fails the review's nonvacuity condition.

The obvious ordered-frontier repair also lacks its required counting theorem.
Lean's `twoSidedExtensionDominates_diagonal_iff` exhibits an equal-rank
antichain of every finite size, so the existing dominance relation cannot
bound the number of retained ordered ports solely in terms of `k`. This does
not refute a stronger structural use of endpoint incidence; it stops the
global finite-interface route selected by the review.

The pre-vetted structural redirect has passed its first local gate. Lean's
`publishedSpanPascalDemand` is the adjacent coefficient
`choose (k-2) (rank-1)`; compiling theorems bound both color-dual one-step
threshold jumps by it. `LowestSeparatedSpanAllocation` now packages the
unique lowest-node allocation of distinct endpoints and proves they occupy
opposite children there.

The independently replayed `k=6` census covers every recursively
deep-below coloring on every labeled support through eight vertices and every
compatible root: 376,764 roots and 631,474 open exact-rank frontier groups.
No frontier exceeds its Pascal demand. Rank five saturates capacity one;
ranks three and four have observed maxima five and three against capacities
six and four. This is bounded evidence, not the general theorem.

Lean now freezes exact span ranks, allocated frontiers, their endpoint
antichain and common-order properties, and the four equivalences between an
exact crossing rank and the corresponding exact predecessor ray rank in a
child. Under a no-strong-`k` hypothesis it also proves the crossing-pair
cup/cap rank sum is at most `k + 1`. `AllocatedExactRankSlotting` states the
remaining local injection precisely, and
`allocatedExactRankFrontier_card_le_spanPascalDemand_of_slotting` proves that
it yields the desired capacity.

The independently replayed census also refutes the simplest proposed
construction. Projecting to left endpoints fails in 1,208 color/rank groups,
as does projecting to right endpoints; 996 rank-three groups fail both. Thus
the slotting must use child-ray incidence rather than raw endpoint cup--cap.

The first incidence-sensitive construction survives the bounded gate. At
each endpoint it records the past and future same/opposite rank pairs as lower
ideals of the truncated `(rank-1) × (k-rank-1)` Pascal rectangle. A span may
use any ideal in the past/future lattice interval at either endpoint. All
631,474 exact-rank frontier groups admit distinct representatives from these
two-interval unions. By contrast, either endpoint alone fails 494 groups
across both colors and ranks, and using only the fixed past/future labels fails
376 rank-three groups. The producer uses cell masks and augmenting paths; the
independent replay uses row-height ideals and backtracking matching.

`StructuralChargingTransitionHall.lean` now proves the lower-ideal and
boundary-path encoding into the exact adjacent Pascal layer, defines the
concrete past/future rank ideals and full all-subfamily Hall condition, and
proves that Hall supplies `AllocatedExactRankSlotting` and therefore the local
capacity inequality. These are completed Lean reductions. The bounded census
does not prove the geometry-specific Hall premise.

That premise, including its proposed two-span expansion base case, is now
formally refuted for the endpoint profiles as defined. The kernel-checked
counterexample has `n=12`, `k=7`, and rank three. Its recursively decomposable
coloring has a deep root split and no strong seven-point cap or cup, but the
distinct allocated spans `(4,6)` and `(5,7)` have all four endpoint profiles
equal to the full `2 x 3` lower ideal. Both candidate sets are therefore the
same singleton. Lean proves failure of rigid-label injectivity, pair
expansion, and the full Hall condition. The generic surviving API proves that
an interval candidate is a singleton exactly when its two endpoint ideals
agree, characterizes pair expansion by injectivity of these rigid labels, and
shows that Hall implies pair expansion. The example does not refute the
frontier cardinal bound: this two-span frontier is below Pascal capacity ten.

A zero-round blind Sol/Fable review at revision
`b7f794018df9006efe48c518040a5995f774e291` used evidence-packet SHA-256
`cf05f9eb2123531ab4e7dea44f1aa65d5ae79d5f50e87096ac382e5c4870bc89`.
Its advisory report SHA-256 is
`009b7c59d0a674f046b094dbef115475bd372f4d49eb98cc9d79d977a1b26416`.
Both reviewers rated the proposed repair only partially supported. The next
bounded contract is to define the rotate-complement involution on rectangular
lower ideals and its induced reversal of the *same untagged* allocated Pascal
slots, prove the involution/encoding laws in Lean, and place the
orientation-dependent permutation inside the Hall candidate system. An
orientation coproduct or doubled carrier is forbidden because it would
silently double capacity.

That complete gate now passes. Lean proves rotate-complement is an involution,
that boundary encoding intertwines it with reversal of the same untagged
Pascal slots, and that reflected Hall still implies the original local demand
bound. It also proves that the frozen rigid pair is separated as singleton
full and empty ideals. The producer checks the whole frozen `n=12` root
frontier and all 631,474 existing `k=6` frontier groups with cell masks and
augmenting paths. The independent checker reproduces the same result with
row-height ideals and backtracking. Neither implementation finds a Hall
failure, same-orientation rigid pair, reflection-fixed opposite pair, or
triple-rigid collision. The compact manifest SHA-256 is
`f65c400c9b99f944eb755f5ea3d38e47adf94f9a25737e56401fec1af263c267`.
This is bounded computational evidence, not reflected Hall for arbitrary
parameters.

The structural bridge authorized by the review now compiles. Lean proves that
an exact parent span at its unique lowest separating node exposes the forced
one of four predecessor/successor child rays. It selects the endpoint profile
incident to that ray and proves that its deterministic orientation reflection
belongs to the span's reflected candidate family. Thus orientation cannot be
selected post hoc to avoid a collision. This is not an injectivity or Hall
theorem: the active target is consecutive-block expansion and then
all-subfamily Hall. Failure of block expansion retires the current per-span
endpoint-candidate repair and redirects to the Innovation Scout's
skew-Bollobás set-pair encoding of actual ray events. The original
`allocatedSpanPascalDemand_le_window` remains the subsequent global injection
theorem.

The consecutive-block gate is now resolved negatively for both natural
single-endpoint strengthenings. `StructuralChargingTransitionHallBlocks.lean`
defines endpoint blocks, proves the left/right frontier orders agree, proves
every block intrinsically consecutive, and shows every nonempty intrinsic
consecutive subfamily is a block. The single active profile is not injective:
an independently replayed `k=6` five-span block selects `0,f,0,f,0`. Retaining
the whole endpoint interval incident to the active ray also fails. In the
frozen `n=12`, `k=7` cap/rank-three group, adjacent spans `(2,5)` and `(4,6)`
both have the reflected active singleton `{3f}`; hence their two-span block has
candidate-union cardinality one. Independent cell-mask and row-height
implementations reproduce the exact defect, and Lean proves the exact-rank
frontier membership, adjacency, candidate equalities, and
`activeBlockExpansion_fails`. The full reflected two-endpoint family is not
refuted by either witness. The predeclared redirect is therefore active: the
next bounded contract must encode actual child-ray events as a skew Bollobás
set-pair system, preserve the coefficient
`choose (k-2) (rank-1)` without tags, and pass the frozen root before Lean
promotion.

Laplace's read-only audit confirms the claim boundary and proposes the first
noncircular contract. An actual-ray event is a normalized direction, concrete
child chain, and marked chain vertex. Each span must locally construct a
present incident set of size `rank-1` and an actual nonincident set of size
`k-rank-1`; every earlier/later pair in a block must have nonempty
`earlier.present ∩ later.absent`. Self-disjointness is then definitional, and
the skew-Bollobas coefficient is exactly `choose (k-2) (rank-1)`. The cheapest
falsifier is the frozen adjacent pair: first test whether the full actual-ray
incidence support of `(2,5)` has any event absent from that of `(4,6)`. An empty
difference stops the event route before any selection search. This remains a
proposal until the event semantics and bounded gate are implemented.

The exact proposed event semantics is now implemented and refuted on the
frozen root. The adjacent support-difference gate passes: `(2,5)` has the
left-ray chain `(3,5)`, and its two marked events are absent at `(4,6)`. Across
the full frontier, however, the first four unique present sets are pairwise
disjoint because direction and complete chain identity are part of the key.
All are nonincident at the fifth span `(6,10)`, so a later absent set must use
at least four events, exceeding its exact capacity `7-3-1 = 3`. Independent
tuple and chain-mask implementations reproduce this certificate. This retires
the marked-chain key, not all actual-ray encodings. A new Innovation Scout
packet compares a semantic event quotient, incidence-matrix accounting, and
direct use of both reflected endpoint intervals before the next route is
selected.

The preferred semantic quotient has now failed its independently replayed
frozen gate. Its 24 directed keys retain ordinal chain role and clipped
complementary ray depth computed inside the active child. The adjacent spans
`(2,5)` and `(4,6)` both have coarse present/support keys `(past,0,0)` and
`(past,1,2)`. Fiberwise absence at the later span therefore excludes the whole
earlier present set, so no absent selection can satisfy skew cross-incidence.
The direction-forgetting diagnostic has the same collision. This retires the
two concrete event encodings.

A bounded comparison packet at SHA-256
`097dd1be3b15cc54a41d4157a5ac196ef8660e4860e43483ae84870a27559788`
then compared exact reflected endpoint-incidence row rank with two-lane
meet/join uncrossing. Sol returned `partially_supported` at high confidence
and selected exact rational rank as the sharper first falsifier; its result
SHA-256 is
`053b0a0b8b76d2ef762ede1421acae22c1cb63f7207d3df3a0c1fab050bc30c4`.
Fable returned a zero-token `ENOTIMP` provider connection error, so no Fable
judgment, reciprocal review, or Sol/Fable consensus is claimed. This provider
failure did not justify route promotion; it left the already frozen bounded
falsifier available to run.

That matrix gate is decisive. For each span and untagged ideal, the row entry
counts membership in the two orientation-reflected endpoint intervals, giving
a fixed coefficient in `{0,1,2}`. The cap/rank-three matrix has exact rank five
on six rows, with primitive circuit

    2 row(0,4) - row(4,6) - 2 row(6,10) = 0.

The cup/rank-four matrix has exact rank three on four rows, with primitive
coefficients `(2,1,-1,-2)`. Rational row reduction over cell-mask ideals and
integer-minor/cofactor replay over row-height ideals agree. Both underlying
candidate systems still pass reflected Hall. This retires only the fixed
endpoint-multiplicity independence mechanism.

The first exact two-lane local rule is now frozen as well. Assigning meet to
the earlier span and join to the later span is false at the adjacent full/empty
pair `(4,6)`, `(5,7)`. Allowing either assignment when it preserves the two
untagged candidate unions passes all 738 frozen adjacent ideal pairs in two
independent representations. This is not yet an augmentation theorem. The
generic implication is now formally refuted:
`StructuralChargingTransitionHallUncrossing.lean` constructs three identical
two-element transition-interval families, proves flexible meet/join and every
two-family expansion test, and proves that no injective representative exists.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

The first candidate strict measure was rejected before execution. Its
discrete-convex boundary energy had no deterministic hole proxy or local
envelope; linear cardinality energy is invariant under meet/join, convex
cardinality energy increases on incomparable ideals, and a local replacement
can collide with a third representative. The stable-ownership replacement has
an exact move: the hole takes a boundary-priority candidate and passes the hole
to that ideal's unique owner.

That rule passes the complete 5,208-state cap/rank-three frozen gate. Exactly
3,612 states fill directly. Every one of the 1,596 blocked states has hole
index 2 or 3, the singleton full/empty families. One ownership transfer moves
the hole to index 0, 1, 4, or 5, whose family has 10, 7, 9, or 10 candidates;
with only five occupied ideals it is immediately fillable. Independent
cell-mask and row-height programs reproduce the one-step termination and the
absence of cycles. Lean now proves the generic completion, ownership-transfer,
cardinality-exit, well-founded descent-to-SDR, and block-cardinality lemmas.
The bounded route review then sharpened this observation into a
singleton-or-block-large owner profile. Fable selected the profile-only gate;
Sol initially selected the full remaining state census, then revised to the
same profile gate after reciprocal critique. Fable's reciprocal call hit its
usage limit, so no complete reciprocal consensus is claimed. The corresponding
Lean one-transfer theorem and Hall corollary now compile.

The profile is not uniform. The frozen cup/rank-three group has block size
seven and family sizes `[10,9,6,6,3,6,8]`, violating H1 at four spans. The
reviewed targeted fallback enumerates its 78,236 one-hole states. Exactly 72
states reach 36 terminal-free two-cycles under the unchanged boundary priority.
The first alternates the hole between `(3,7)` and `(6,8)` by stealing ideal
`0` back and forth. Independent cell-mask and row-height implementations agree.
The active target is therefore an exact local cycle breaker—another ownership
priority or collision-free meet/join escape—frozen and tested first on all 36
cycles. No graph-distance measure is promoted.

The priority-free two-step augmentation passes that cycle-breaking gate and a
stronger coverage check. Among all 85,920 one-hole states in the four frozen
frontier groups, 81,032 fill directly and every one of the 4,888 blocked states
has an occupied hole candidate whose unique owner has a fresh candidate.
Restricting independently to all 62 nonempty consecutive subblocks gives
134,236 states; 128,259 fill directly and all 5,977 blocked states have the
same two-step exit. Cell-mask and row-height implementations independently
reconstruct and replay both results. Lean proves that the explicit certificate
completes the representative system and implies the block Hall inequality
using only the two local updates.

A zero-round blind route review at clean revision
`89277094588987ce86f5dbe2d61e5cb8aab7685c` used packet SHA-256
`2ff3e016f4c17f174aec9f3b1427a7e2d8a0ec2005562bc3a370fe7522fdcebf`.
Sol returned high-confidence `partially_supported` and selected the universal
direct-or-two-step disjunction as the next exact target. Its result SHA-256 is
`1540002485803a54b804114718aa90c35f4b53a4039f0005085132845c57a0aa`.
The missing geometry is a no-closed-saturated-star or overlap-to-slack
principle: in a blocked genuine reflected state, at least one owner reached
from the hole family has a candidate outside the original used set. The
two-span abstract system with identical singleton families shows this is false
for arbitrary candidate systems. Fable returned no mathematical answer because
its Fable 5 provider quota was exhausted; no Sol/Fable consensus is claimed.
The selected work target is to prove the structural escape from genuine
reflected endpoint data without Hall, an existing full matching, or finite
enumeration.

That obstruction has now been normalized in Lean. A
`HasClosedSaturatedOwnerStar` state has every hole candidate currently owned
and every candidate of each actual reached owner already used; Lean proves
this is equivalent to the conjunction of being blocked and having no two-step
exit. The word "actual" is material. A reviewed counterexample shows that a
membership-feasible but fictitious owner can have a large family even when the
owner selected by the partial injection has no fresh candidate. The canonical
`reachedOwners` and `ownerStar` definitions therefore follow the partial
injection. Lean proves that a block-large canonical star forces a two-step exit
and hence an SDR.

For a state-free structural premise, Lean defines
`FiniteCandidateFeasibleOwnerStarExpansion`: for every hole and every
injective membership-feasible assignment of its candidates to other spans,
the union of the hole family and the assigned owners' families has at least the
block cardinality. This stronger profile implies the canonical actual-owner
bound for every blocked one-hole state. Its reflected wrapper, together with a
separately supplied one-hole state for every nonempty consecutive block,
implies the desired reflected block expansion. The separate theorem that
reflection preserves nonempty candidate families rules out the empty-family
base obstruction but does not construct those one-hole states.

Experiment 0041 tests the state-free premise, not merely states produced by one
ownership rule. Independent cell-mask production and row-height replay cover
all 247 injective membership-feasible owner maps on all 62 frozen consecutive
blocks. Every owner-star union is block-large; the minimum slack is `+1`. The
manifest SHA-256 is
`ac49dbc95b02951a3bc3482963473c412d1a3684a421fe3f1abed720422a4fe0`.
This bounded pass does not prove the arbitrary reflected theorem. The active
mathematical target is to derive feasible-owner-star expansion from the
ordered reflected boundary slots, with telescoping slack as the leading
mechanism. After that, a uniform induction must supply the one-hole states.
These are explicit separate obligations, and neither may assume Hall, an SDR,
or enumeration.

Reflection normalization is now explicit in Lean. Rotate-complement is
antitone on rectangular ideals, exchanges meet and join, and carries membership
in a transition interval exactly to membership in the interval between the
reflected endpoints. This removes an algebraic ambiguity but supplies no
cross-span expansion by itself.

The adversarial fallback strengthens owner-star expansion in a different
direction. `FiniteCandidateFeasibleOwnerHasBlockLargeFamily` requires every
injective membership-feasible owner map to reach at least one individual owner
whose candidate family has cardinality at least the block. Lean proves that
the selected owner family lies in the owner star, hence this stronger profile
implies `FiniteCandidateFeasibleOwnerStarExpansion`. The genuine reflected
wrapper and its implication to block expansion, conditional on the separate
one-hole-state premise, also compile.

Experiment 0042 independently tests that stronger profile on the same 62
blocks and 247 maps. Cell-mask production and row-height replay agree; the
minimum maximum-owner-family slack is `+1`. The certificate retains raw left
and right endpoint intervals, their past/future ideals and boundary slots, and
the reflection bit. Its manifest SHA-256 is
`b3f75fb27142b11023db09ab8ed28ba9bed67ab4b23da10fca3d169f5a644ac9`.
This remains bounded evidence at one root, and two color/rank groups are
vacuous.

A zero-round route audit at clean revision
`326dc216fd7b840a96d7071c1396a074f86974be` used packet SHA-256
`5bbdafccfb2158d0a475aefe546ec219c42023fc600922282b12691667980d61`.
Sol returned medium-confidence `partially_supported` and selected the
deterministic reflected frontier-gap rule only as a falsification target. Its
structured result SHA-256 is
`40bf8a82148f1434e9d0fdaabed9291e5f6976c3a354ae4ce1507b7bc8002d4a`.
Fable returned zero tokens because its Fable 5 usage limit was exhausted, so
no Sol/Fable consensus or reciprocal review is claimed.

Experiment 0043 implements Sol's exact cheapest gate: process unmapped block
positions in order, choose the nearest mapped owner, use its endpoint lane
facing the gap, and greedily take the first normalized boundary-slot ideal
outside the hole family and prior charges. The rule fails on the tight cap
`+1` witness before a broader scan. Hole `{3f}` maps to owner `(2,5)`; after
one left-lane charge, the second gap faces that owner's right lane, which is
exactly `{3f}`, so no fresh charge exists. Independent implementations agree.
The failure manifest SHA-256 is
`cd376724314ee6ea44849e86922f12c4ea003fcfa102a6cbad16dc978c9441d6`.

This retires only the nearest-owner facing-lane rule, not arbitrary gap
witnesses. Sol's pre-vetted fallback is now active: prove the arbitrary genuine
block-large reached-owner profile from exact-rank two-lane endpoint incidence.
Generic lattice intervals, consecutive order, and reflection are insufficient,
so the missing lemma must expose a genuine rank-witness reason that at least
one owner family dominates the containing block. The one-hole-state induction
remains a separate open premise.

Experiment 0044 tests the active profile on the complete decomposable `k = 6`
census through eight vertices. A bottleneck matching reduction replaces owner-
map enumeration: profile failure is exactly an injection of the hole family
into compatible owners whose families are all smaller than the block. Lean
proves this logical equivalence. Cell-mask production and independent row-
height replay agree on all 631,474 groups, 1,126,134 consecutive blocks, and
1,438,464 holes. There are 3,792 nonvacuous holes, all with bottleneck slack at
least `+1`; no profile failure occurs. This remains bounded evidence, not the
arbitrary theorem.

The gate also extracts a minimum small-owner deficiency. Every nonvacuous hole
has a singleton deficient anchor with deficiency one, and in every case some
such singleton is one of the hole's four normalized past/future endpoint
extremes. Thus one genuine endpoint extreme has no compatible block-small
owner. Lean now defines the normalized extreme family, proves it lies inside
the reflected candidate family, and proves that this forced-extreme contract
implies the active block-large reached-owner profile. The open geometry target
has therefore narrowed to proving that one of those four extremes is forced
for an arbitrary exact-rank consecutive block.

Experiment 0046 falsifies that last singleton strengthening on the frozen
`k = 7` root. Of 29 nonvacuous holes, four cup/rank-three holes force no
endpoint extreme. In the first full seven-span block, hole `(2,5)` has endpoint
labels `9`, `3f`, and `1b`, each supported by at least one block-small owner.
Nevertheless the two-ideal anchor `{f,1f}` has only one block-small neighbor.
Across the frozen root, 26 minimum anchors have size one and three have size
two, always with deficiency one. The active local target is consequently the
compiled `AllocatedReflectedEndpointRankTransitionSmallOwnerDeficiency`, not
the refuted forced-extreme strengthening.

Experiment 0047 exhaustively classifies every minimum deficient anchor in that
frozen root. Although two holes also admit a skipped chain pair, every hole has
some minimum anchor that is a complete saturated lattice interval contained in
one normalized endpoint lane. Lean proves the abstract explanation for the
unit deficiency: an inclusion-minimal deficient anchor is nonempty, has one
more anchor than neighbor, and retains the same neighbor set after any member
is deleted. It also characterizes singleton and two-anchor minima exactly.

Experiment 0048 tests the sharpened existential shape over all 376,764
decomposable `k = 7` roots through eight vertices. Independent cell-mask and
row-height implementations agree on 947,452 frontier groups, 2,422,116 holes,
and all 3,056 nonvacuous cases, with no block-large profile failure. A
normalized endpoint singleton works in 1,876 holes; the remaining 1,180 select
a two-ideal cover pair. Every selected minimum anchor is a complete chain
interval in one normalized endpoint lane. Lean packages that observation as
`AllocatedReflectedEndpointRankTransitionLaneChainMinimalDeficiency` and proves
it implies the active small-owner-deficiency contract. The consequential open
geometry lemma is now to construct this shaped anchor for an arbitrary genuine
exact-rank consecutive block. This bounded census is evidence for that lemma,
not its proof.

Experiment 0049 performs the first parameter extension, `k = 8` through eight
vertices. Cell-mask production and row-height replay agree on all 992,028
frontier groups, 1,953,566 blocks, and 2,606,420 holes. There are 2,096
nonvacuous holes, no profile failure, and minimum bottleneck slack `+3`. Every
minimum deficient anchor is a singleton. The singleton-or-cover-pair
strengthening therefore survives, but this support range does not test the
first path with more than one adjacent gap.

The innovation, adversarial, and architecture audits converged on an explicit
owner-labelled lane path rather than an unsupported all-`k` size-two claim.
Lean now proves the generic finite path-incidence inequality and packages it as
`FiniteCandidateLanePathCertificate.minimalDeficientAnchor`: `m + 1` anchors
and `m` injectively labelled adjacent-gap owners give an inclusion-minimal
deficient anchor when those owners exhaust its block-small neighborhood. The
theorem `laneChainMinimalDeficiency` adds strict order, a complete Pascal
interval, and one-lane containment. The reflected contract
`AllocatedReflectedEndpointRankTransitionLanePathCertificates` implies the
previous lane-chain contract and therefore all existing downstream
small-owner and block-large reductions.

The central open bridge is now the construction of those certificates from
`IsDecomposableOn` for both children, `HasDeepBelowSplit`, and the absence of a
strong `k`-set. It must derive the neighbor-exhaustion clause from exact-ray
geometry; assuming deficiency, Hall, or an SDR would be circular. Ranks one
and two must be discharged separately because the available active-ray normal
form starts at rank three.

An adversarial audit then found an evidence mismatch: Experiment 0048 checked
the lane shape only on the 3,056 nonvacuous holes, whereas the reflected Lean
path contract quantifies over all 2,422,116 holes. Experiment 0050 removes that
bounded gap. Independent cell-mask production and row-height replay agree on
947,452 frontier groups, 1,830,286 blocks, and all 2,422,116 holes. Every hole
has a lane-path certificate. The length distribution is 2,418,432 empty paths,
3,170 one-gap paths, and 514 genuine two-gap paths. The first deterministic
certificate has an inexact neighborhood trace in precisely those 514 cases,
but an explicit search finds an alternative exact singleton-neighborhood trace
for every one of them. The manifest SHA-256 is
`acf09031049232967e8ad4b7f45ad6b8319c0543773f1c2419cde1ca4a438362` and
the independent checked-prefix digest is
`0b7f9c79c190c40766f21c72aef75e82499e0351842e204d7084e5fa118a6f26`.

Lean now constructs a path certificate from local singleton neighborhoods in
`finiteCandidateLanePathCertificate_of_localNeighborhoods`, specializes this
to exact adjacent-gap traces in
`finiteCandidateLanePathCertificate_of_singletonNeighborhoodTrace`, and proves
that the reflected exact-trace contract implies the existing reflected path
contract. Separately, `HasSweepSpan.two_le_card` proves that a genuine endpoint
span contains at least its two distinct endpoints, so exact rank one is
impossible and the rank-one path obligation is discharged without geometry.
The next theorem contract is therefore exact singleton-neighborhood trace
construction at rank two, followed by the rank-at-least-three active-ray
bridge. This remains a boundedly supported target, not an arbitrary-rank proof.

A bounded route review froze evidence packet SHA-256
`fbc83f02526a8be8dcfd15e90ffeb323f8164427a07cca03ceaf574019fcffe2`.
Sol rated the proposed route `partially_supported` with high confidence and
selected falsification of the first multi-gap cases before further abstraction;
Experiment 0050 performs that gate and strengthens the surviving target to the
exact trace. Fable returned zero tokens with a provider usage-limit error, so
no Fable judgment, reciprocal review, or Sol/Fable consensus is claimed.

That rank-two target is now formally retired. A source audit found that the
Experiment 0050 group generator explicitly filtered to `rank >= 3`; its
successful 2,422,116-hole census never exercised rank two. Dedicated
Experiment 0051 finds a rank-two lane-path failure at support size five and a
reflected-Hall failure at size six. Its complete independently replayed census
through size eight checks 732,172 rank-two groups and finds 20,254 Hall
failures plus 2,896 direct Pascal-capacity violations.

Lean promotes the decisive part beyond computational evidence.
`mem_allocatedExactRankSpans_two_iff_no_active_interior` proves the exact
active-child normal form, and
`mem_allocatedExactRankFrontier_two_iff_adjacent_crossing` identifies the
frontier with adjacent child changes in sweep order. The explicit
`StructuralChargingRankTwoCounterexample` is recursively decomposable, has a
deep-below alternating root, and has no strong seven-set. Its six cap/rank-two
spans exceed `publishedSpanPascalDemand 7 2 = 5`; Lean consequently proves
`no_rank_two_slotting`. Thus neither a different Hall proof nor more elaborate
lane paths can establish the old individual-span capacity statement at rank
two. The next route decision must instead group/quotient rank-two transitions
or replace the per-rank allocation with a coupled recurrence. The
rank-at-least-three active-ray subroute remains available as a component, not
as a complete local theorem.

A bounded replacement review then considered summing local rank-two
adjacencies at their unique lowest separating nodes and bounding the result by
the global gap count `support.card - 1`. Sol regarded the route as only
partially supported; Fable returned zero tokens because its provider quota was
exhausted, so no consensus is claimed. The proposal is false independently of
that incomplete review. Lean checks the minimal interleaved tree with root
split `{0,2}|{1}`: the root contributes `(0,1),(1,2)` and the `{0,2}` child
contributes `(0,2)`, for three distinct locally adjacent endpoint pairs but
only two global gaps. Unique lowest-node ownership prevents duplicate endpoint
pairs; it does not make adjacency in a node support global. The next contract
must survive this three-vertex obstruction and the seven-vertex alternating
`6 > 5` obstruction before implementation.

Experiment 0052 identifies such a surviving direction. In an alternating-run
decomposition of the root membership word, every transition after the first
is canonically paired with a hidden child gap. A hidden lower gap supports a
cap span of ambient rank at least three; a hidden upper gap supports a cup
span. The producer and independent direct-child-gap checker agree on all
366,086 open `k = 7` roots through support size eight: 392,562 promotions and
1,913,894 adjusted color/rank groups produce no capacity or endpoint-candidate
failure. Lean proves the numerical run identity and both hidden-gap color
bridges.

This evidence selects a theorem-design direction but does not close the
ticket. Promoted gaps are noncrossing at the parent and therefore do not fit
the existing allocated crossing frontier. The next exact contract must define
an ambient promoted carrier, prove its canonical matching to the appropriate
rank-two transitions, and then justify rank-ideal candidates for noncrossing
spans. A color-coupled arithmetic bridge to the published two-child recurrence
is still required before capacity or the outer window can be claimed.

The first of those contracts now compiles. `AmbientPromotedGap` stores the
color-compatible hidden source and its exact parent-support rank at least
three; every source gap has such a promotion. The endpoint-rank construction
has been generalized to arbitrary ambient spans, and each promoted object has
a nonempty ideal family and nonempty encoded Pascal-slot family without a
crossing, Hall, or capacity hypothesis. The canonical run-gap contract now
also compiles: hidden sources are equivalent to the noninitial parent
crossings, and all hidden sources plus one unit are equivalent to all parent
crossings. Fixed-color removal leaves the opposite-color hidden-source count
plus one at rank two. The finite `AdjustedHigherRankDemand` then combines the
old crossing frontier and exact-rank promoted sources. Lean proves common
exact-rank semantics, a same-color corner in both incident endpoint profiles,
and the conditional theorem that adjusted Hall yields the published Pascal
capacity. The next exact contract is adjusted Hall expansion, followed by a
rank-two residual bound and the two-color recurrence composition. The bounded
Sol review rates the direction `partially_supported`; Fable supplied no
judgment because its usage limit returned zero tokens.

That theorem target is now formally retired. Experiment 0053 tests the first
unenumerated alternating root at ten vertices. The explicit reverse-comb
children form an open recursively decomposable `k = 7` context. Lean proves
that seven crossing cap spans and four promoted hidden lower gaps all have
exact ambient rank three. Hence `AdjustedHigherRankDemand` has at least eleven
members while `publishedSpanPascalDemand 7 3 = 10`; the exact adjusted Hall
contract is false and the proposed slotting type is empty.

The same independently replayed certificate executes the nearest reviewed
aggregate. Its adjusted group cardinalities across both colors and all ranks
are `5,11,5,11,3,1`, totaling 36. One untagged nonempty Pascal window has 31
slots. A separate color-tagged window would obscure this failure only by
doubling the resource and losing the target exponent. Thus raw additive
cross-rank/color aggregation is also stopped. The canonical hidden-gap
genealogy, color bridges, and exact ambient promotions remain proved and may
be reused, but they are constraints or alternative representations rather
than independent demands.

The bounded review packet SHA-256 is
`dbda4bbe1a4f89dadcdd587631a02f3c5deec9bf077821df8d9c4917b6f668a9`.
Sol returned `partially_supported` with medium confidence and agreed that the
fixed-rank Hall contract is decisively false; Fable returned zero tokens at
its provider limit, so no consensus is claimed. The next single bounded task
was the ten-point exclusive-choice conservation gate. It treated each hidden
source and canonical entering transition as one charge with alternative
representations, merged the initial obligations with the empty sentinel, and
retained the higher-rank crossing demands. That exact 27-charge graph also
fails: its maximum matching has size 20, and an explicit 20-demand subfamily
has only 13 candidate slots. The deficiency contains all fourteen cap/cup
rank-three crossing obligations, so rank-two/promotion choices alone do not
repair cross-color competition. Structural endpoint slotting is demoted from
the main route.

The ensuing bounded route review froze packet SHA-256
`9d017fc6059f3c4caaf6ec59b8bf4739eb76928904589163363c587127b7321c`.
Sol returned `partially_supported` with high confidence and selected the
common-span cross-color quotient as the sharpest next falsifier. Fable again
returned zero tokens at its provider usage limit, so no Fable judgment or
consensus is claimed. Experiment 0054 now closes that falsifier. Merging the
seven identical-endpoint cap/cup rank-three pairs and intersecting their
candidate families repairs the finite graph: all 20 resulting charges have a
perfect matching. But the required semantic payoff is false. Lean proves the
seven spans are genuine frontiers in both colors; their cup rays use the lower
child and their cap rays use the disjoint upper child, so no nonempty retained
subset belongs to both published cores. Independently, the proposed shared
coefficient inequality specializes to `32 <= 22` at `k = 7`, rank three.

Common endpoints alone are therefore retired as a proof-reuse rule, not merely
left without a proof. A stronger nonadditive invariant is not refuted.
Containment-minimal pruning remains parked because span containment has no
proved semantic payment relation. The next exact design contract is a
branch-indexed tree-global conserved charge: it must name an actual retained
owner, prove address nonreuse, and survive both the compiled three-vertex
local/global-gap counterexample and the ten-point obstruction before a new
Hall or recurrence theorem is selected.

Experiment 0055 completes that conservation contract without claiming a
recurrence. Gap-or-sentinel tokens are equivalent to actual support vertices;
their child-to-parent merge preserves owners and agrees with the hidden-gap
genealogy. The fold over an explicit decomposition tree proves leaf-owner and
Boolean-address nonreuse. The three-point overcount is repaired by transport,
and the ten-point split remains exactly ten owner tokens. Lean separately
proves unique selection of the saturated published branch and its actual
retained core.

The bounded review packet SHA-256 was
`fbdd71e0ca938691364140abbf35412390107762248744033d25690758808b12`.
Sol returned `partially_supported` at high confidence and proposed testing
whether a live hidden-gap owner belongs to the unique saturated child. Fable
returned zero tokens at its usage limit, so no two-reviewer consensus is
claimed. Lean now refutes that proposed membership at the first
`(4,6,6,3,2)`, `2+10` scalar boundary. The conserved right endpoint stays in
the lower child while the unique saturated branch is upper.

The corrected branch-local object is the canonical entering-crossing pivot,
not the immutable endpoint owner. Lean proves that these pivots lie in the
selected opposite child and are injective over hidden sources. A single
published slice can retain all pivots conditional on the exact core-capacity
inequality. Pure source-child counting does not establish it: the feasible
`(4,8,8,3,4)`, `10+13` scalar state permits nine source adjacencies against an
eight-vertex selected upper core.

Experiment 0056 closes this first geometric gate in Lean. The minimum lower
vertex lies strictly left of every canonical hidden-lower pivot. Any upper
three-cap among those pivots would extend through that common endpoint to a
parent four-cap, so no parent four-cap makes the full pivot seed a cup. No
parent `u`-cup therefore gives fewer than `u` hidden-lower sources. The
color-dual theorem bounds hidden upper sources under no parent four-cup. This
matches every published index-three core exactly and, at the normalized
`(4,8,8)`, `10+13` split, gives at most seven pivots for an eight-vertex core.
Lean constructs one published upper slice retaining all of them; the
no-strong-eight hypothesis is unnecessary.

The next theorem-design gate is the higher-index cone bridge. For `a > 4`,
the anchor should force `(a-1)`-cap avoidance on the pivot seed, but the proof
must still convert inherited decomposable/one-change structure into the
general cup--cap cardinal bound and identify that binomial with the selected
published threshold. No Hall or Boolean-code theorem is selected before that
gate passes.

Experiment 0045 rejects the first lane-level bridge proposed after that pass.
On the tight cap witness, singleton hole `{3f}` maps to owner `(2,5)`, whose
candidate family has size seven. Its left lane changes by four grid cells and
its right lane by zero, so maximum single-lane spread plus one is `5 < 6`, the
block size. Independent cell-mask and boundary-slot calculations agree. The
active proof must therefore retain lattice branching, combine both lanes, or
derive a strict deficiency in the incidence graph of block-small owners.

Experiment 0061 resolves the first root-local boundary without reviving the
tree-global ledger.  Exact visible/hidden accounting shows that the proposed
residual payment is false at `(4,8,8)`, `10+13`: the central cut permits at most
one hidden lower adjacency and forces at least eight visible ones.  Two
nonpivot cap extrema give a valid but insufficient reserve.  The same cut
partitions the thirteen upper vertices into ordered cup blocks of sizes six
and seven.  A direct symbolic Lean proof of `CupBlocks67Force488`, including
reversal and arbitrary-set transport, proves that those blocks force a
four-cap, eight-cup, or strong eight-set.  Lean consequently proves
`upper.card ≤ 12`, excludes `10+13`, and records the residual exact-root window
`11 ≤ lower.card`, `upper.card ≤ 12`.

Experiment 0062 closes that residual window without the strict predecessor
pool.  Four smaller normalized cup-block gates are independently SAT-refuted.
The successful proof instead divides the positive upper sizes into `8..12`,
`2..7`, and `1`.  Elementary cup--cap thresholds give crossing witnesses
`(5,3)`, `(6,2)`, and `(7,1)` respectively, so every branch contains a strong
eight-set.  Lean proves `criticalRootImpossible_488` and lifts it to the
unconditional hereditary theorem `decomposableStateUpper_488`.  A frozen
read-only review independently reproduced the build, axiom audit, and branch
arithmetic.  This ticket remains open because one off-diagonal decomposable
state is not the uniform E3 transition.  The next bottom-up state is
`(5,7,8)`.  Exact published-index arithmetic removes lower sizes `11..40` but
leaves the small-lower family `1..10` against upper sizes `41..32` as well as
the extreme `41+1` split.  The two tails are not color-dual within this state.
Restriction gives a singleton-lower `1+32` gate. Its two upper sweep sides are
four-cap-free, have sizes `11..21`, and contain five-cups. The extracted
`5+q+5` local force statement is false: Experiment 0063 supplies both an
independently checked SAT witness and a Lean proof from an explicit recursive
decomposition tree. This does not refute the full `1+32` tail. The next
lower-tail contract must retain the unused side reservoirs; the
upper-singleton extreme remains a separate obligation before the `(5,8,8)`
higher-cone consumer. Lean now proves the first reservoir layer: every
23-vertex upper restriction contains a four-cap by `(4,8,8)`, all such caps
straddle the singleton root, and three pairwise-disjoint caps can be selected.
An independently checked 13-vertex signotope model refutes using only those
three selected caps. The active theorem-design gate must use the full cap
density together with decomposition-tree ownership.

A bounded Sol/Fable review rejected the first tree-transversal target. Lean
now proves the exact obstruction: every cap transversal has cardinality at
least ten, while the universal nine-transversal gate is equivalent to the
full singleton-lower gate. Since every upper four-cap straddles the singleton
root, no two can be weakly ordered, so the existing ordered-family port bound
does not aggregate this reservoir.

Threshold-frontier extraction now compiles, as did the proposed strict-span
minimum consumer. The corresponding universal recurrence is false. An exact
Lean construction on 32 support vertices proves four-cap density in every
23-subset and a common omitted cut for every four-cap, then refutes strict
descent by finite minimum span. The same file proves that the construction has
a seven-cup, so it does not satisfy the actual open-state hypotheses.

The corrected positive reduction is terminal and tree-local rather than a
new universal descent axiom. Lean chooses a terminal four-cap, proves its open
endpoint window has at most 21 vertices under inherited seven-cup avoidance,
and obtains at least nine genuine vertices strictly before or after the cap.
All nine carry one of the two endpoint bridge failures. At the cap's unique
lowest separating node, its child profile is `1+3` or `2+2`; strong-eight
avoidance forbids respectively a lower five-cup or lower six-cup. The strict
predecessor `(5,5,8)` bounds the lower child by 20 in the `1+3` branch. The
`2+2` child word is forced to be lower--upper--upper--lower, so endpoint
bridges of tails still in that node are automatic. A kernel-checked
nine-vertex recursive counterexample refutes the exact five-internal-tail
force gate. Lean now partitions the nine tails into five internal tails or
five external tails and assigns every external tail a concrete first-exit
node with the whole cap below and the tail above.

Experiment 0065 carries the global density into this residual. Lower-sibling
supports along one path are pairwise disjoint and ordered, and a four-cap
fully covered by singleton bucket fibers is impossible. Every residual cap
disjoint from the terminal cap meets the outer-tail set; any such transversal
has size at least six by deleting it together with the fixed cap and applying
the `32/23` density theorem. Lean chooses a minimum transversal, gives every
selected tail a private residual cap, proves those caps are injectively
indexed, and routes every owner internally or to a lower first exit. The
actual state-578 theorem now returns this complete package.

Two natural numerical conclusions are false. A 17-vertex target-free Lean
model with a terminal cap and nine tails has a secondary cap using only one
tail. A separate target-free recursively decomposable nine-vertex model has
six distinct private caps all sharing one three-vertex core; it does not have
the terminal or `32/23` hypotheses and therefore isolates the failed packing
inference. The surviving structural theorem says that any four-cap not wholly
in a lower deep-split child has both middle sweep vertices in the upper child
and lower vertices only at its endpoints. A post-result bounded Sol/Fable review
(evidence packet SHA-256
`9b98a3e1aa0151eb04dd5684d6fae7872c4b9b58bb4c795e8c81bf3a9c01be52`)
selects the whole-cap path trace as primary and a density-aware shared-core
gate as the only reserve. Its exact first interface compiled: when a private
cap owner has a lower first exit, the cap has either an uncovered non-owner
vertex or a two-vertex lower-sibling-bucket collision.

Experiment 0066 resolves that bounded milestone. Lean classifies every
uncovered non-owner as internal or true-exiting and defines the shallowest
escape of the whole cap. A shallowest false step forces the cap's two middle
vertices into one sibling bucket. Thus every external private cap either
first peels at a true step or has the desired collision, and the actual state
returns three owners with this residual. An eight-vertex terminal,
decomposable, target-free Lean counterexample realizes the collision-free true
peel followed by a false owner exit. This triggers the recorded formal expiry
of independent cap-by-cap tracing. The one density-aware reserve proves that
every set of at most five vertices misses some residual cap, but does not
control overlap among the six chosen private caps. Following the pre-vetted
fallback order, the active overflow is the `41+1` branch. It now reduces to an
exact 32-vertex color-dual `(7,5,8)` lower gate, whose every decomposable
23-subset contains a four-cup. Reviewer agreement is advisory; the positive
and negative mathematical claims above are separate compiling Lean theorems.

Experiment 0067 converts that density into a global witness supply. Assuming
the strict `(4,5,8)` predecessor, Lean extracts three disjoint four-cups and,
from the residual sizes `20`, `16`, and `12`, three further disjoint
four-caps. Pairwise lowest joint splits and their endpoint patterns compile,
as does a six-witness common-split defense. A kernel-checked eight-vertex
reverse-separated pair expires synchronization by address equality alone.
Regenerating a cap inside the 12 cup vertices leaves one exact alternative:
it misses a selected cup or meets the three cups in profile `2+1+1`. A
target-free signotope realizes the latter but is not decomposable; 50,000
bounded decomposable samples found no witness. The batch is Outcome 2, a
reusable structural advance, not closure of the singleton tail. The active
contract must use recursive decomposability essentially to eliminate both
regeneration branches or derive a named child-capacity violation.

## Evidence

- [Terminal-tail capacity and private caps](../../experiments/0065-state-578-terminal-tail-capacity.md)
- [Lean terminal-tail capacity](../../../ErdosSzekeres/StructuralChargingNextState578Capacity.lean)
- [Lean two-tail multiplicity counterexample](../../../ErdosSzekeres/StructuralChargingNextState578CapacityCounterexample.lean)
- [Lean private-cap consumers](../../../ErdosSzekeres/StructuralChargingNextState578PrivateCaps.lean)
- [Lean shared-core private-cap counterexample](../../../ErdosSzekeres/StructuralChargingNextState578PrivateCapsCounterexample.lean)
- [Whole-private-cap traces and route expiry](../../experiments/0066-state-578-private-cap-traces.md)
- [Lean whole-private-cap traces](../../../ErdosSzekeres/StructuralChargingNextState578PrivateCapTrace.lean)
- [Lean true-peel/later-false-owner counterexample](../../../ErdosSzekeres/StructuralChargingNextState578PrivateCapTraceCounterexample.lean)
- [Dual packing and regeneration](../../experiments/0067-state-578-dual-packing.md)
- [Lean dual packing](../../../ErdosSzekeres/StructuralChargingNextState578DualPacking.lean)
- [Lean reverse-separated pair](../../../ErdosSzekeres/StructuralChargingNextState578DualPackingCounterexample.lean)
- [`ErdosSzekeres.Decomposable`](../../../ErdosSzekeres/Decomposable.lean)
- [`ErdosSzekeres.E3FiniteReduction`](../../../ErdosSzekeres/E3FiniteReduction.lean)
- [Lean span-dominance pruning](../../../ErdosSzekeres/SpanDominance.lean)
- [Dominance-quotient gate and refutation](../../experiments/0027-span-dominance-quotient-gate.md)
- [Small dominance-quotient manifest](../../../data/derived/e3-span-dominance-quotient-k6-n9.json)
- [Large raw two-root manifest](../../../data/derived/e3-two-root-span-k6-n10.json)
- [Large dominance-quotient refutation](../../../data/derived/e3-span-dominance-quotient-k6-n10.json)
- [Rooted-interface gate and route redirect](../../experiments/0028-rooted-span-interface-gate.md)
- [Rooted-interface refutation manifest](../../../data/derived/e3-rooted-span-interface-k6-n10.json)
- [Allocated span Pascal-demand gate](../../experiments/0029-allocated-span-pascal-demand.md)
- [Allocated span Pascal-demand manifest](../../../data/derived/e3-allocated-span-pascal-demand-k6-n8.json)
- [Lean Pascal demand and lowest-node span allocation](../../../ErdosSzekeres/StructuralChargingPascalDemand.lean)
- [Lean exact span frontier and slotting reduction](../../../ErdosSzekeres/StructuralChargingSpanFrontier.lean)
- [Lean endpoint-transition Hall reduction](../../../ErdosSzekeres/StructuralChargingTransitionHall.lean)
- [Lean endpoint-transition Hall counterexample data](../../../ErdosSzekeres/StructuralChargingTransitionHallCollisionData.lean)
- [Lean endpoint-transition Hall counterexample](../../../ErdosSzekeres/StructuralChargingTransitionHallCollision.lean)
- [Reflected transition-Hall gate](../../experiments/0030-reflected-transition-hall-gate.md)
- [Reflected transition-Hall manifest](../../../data/derived/e3-reflected-transition-hall-k6-n8.json)
- [Lean reflected transition-Hall machinery](../../../ErdosSzekeres/StructuralChargingTransitionHallReflection.lean)
- [Lean reflected separation of the frozen pair](../../../ErdosSzekeres/StructuralChargingTransitionHallReflectionCollision.lean)
- [Lean child-ray/reflected-candidate bridge](../../../ErdosSzekeres/StructuralChargingTransitionHallRayBridge.lean)
- [Consecutive-block Hall gate](../../experiments/0031-consecutive-block-hall-gate.md)
- [Lean consecutive-block and active-interval reductions](../../../ErdosSzekeres/StructuralChargingTransitionHallBlocks.lean)
- [Lean active-interval block counterexample](../../../ErdosSzekeres/StructuralChargingTransitionHallReflectionCollision.lean)
- [Active-representative counterexample manifest](../../../data/derived/e3-active-reflected-representative-counterexample-k6-n8.json)
- [Active-interval block counterexample manifest](../../../data/derived/e3-active-reflected-transition-hall-k6-n8.json)
- [Actual child-ray event-pair gate](../../experiments/0032-actual-ray-event-pair-gate.md)
- [Actual child-ray event-pair manifest](../../../data/derived/e3-actual-ray-event-pair-frozen-n12-k7.json)
- [Coarse ray-event incidence-matrix gate](../../experiments/0033-coarse-ray-event-matrix-gate.md)
- [Coarse ray-event matrix manifest](../../../data/derived/e3-coarse-ray-event-matrix-frozen-n12-k7.json)
- [Reflected endpoint-incidence matrix gate](../../experiments/0034-reflected-endpoint-incidence-matrix.md)
- [Reflected endpoint-incidence matrix manifest](../../../data/derived/e3-reflected-endpoint-incidence-matrix-frozen-n12-k7.json)
- [Two-lane adjacent uncrossing gate](../../experiments/0035-two-lane-adjacent-uncrossing.md)
- [Two-lane adjacent uncrossing manifest](../../../data/derived/e3-two-lane-adjacent-uncrossing-frozen-n12-k7.json)
- [Lean limit of pairwise uncrossing](../../../ErdosSzekeres/StructuralChargingTransitionHallUncrossing.lean)
- [Stable-ownership one-hole descent gate](../../experiments/0036-stable-ownership-hole-descent.md)
- [Stable-ownership one-hole descent manifest](../../../data/derived/e3-stable-ownership-hole-descent-frozen-n12-k7.json)
- [Lean one-hole descent machinery](../../../ErdosSzekeres/StructuralChargingTransitionHallHoleDescent.lean)
- [Singleton-or-block-large profile gate](../../experiments/0037-singleton-large-owner-profile.md)
- [Singleton-or-block-large profile manifest](../../../data/derived/e3-singleton-large-owner-profile-frozen-n12-k7.json)
- [Cup/rank-three ownership-cycle gate](../../experiments/0038-stable-ownership-cup-rank3-cycle.md)
- [Cup/rank-three ownership-cycle manifest](../../../data/derived/e3-stable-ownership-cup-rank3-cycle-frozen-n12-k7.json)
- [Two-step ownership-augmentation gate](../../experiments/0039-two-step-ownership-augmentation.md)
- [Two-step ownership-augmentation manifest](../../../data/derived/e3-two-step-ownership-augmentation-frozen-n12-k7.json)
- [Consecutive-block two-step augmentation gate](../../experiments/0040-consecutive-block-two-step-augmentation.md)
- [Consecutive-block two-step augmentation manifest](../../../data/derived/e3-consecutive-block-two-step-augmentation-frozen-n12-k7.json)
- [Owner-star expansion gate](../../experiments/0041-owner-star-expansion.md)
- [Owner-star expansion manifest](../../../data/derived/e3-owner-star-expansion-frozen-n12-k7.json)
- [Block-large reached-owner gate](../../experiments/0042-block-large-reached-owner.md)
- [Block-large reached-owner manifest](../../../data/derived/e3-block-large-reached-owner-frozen-n12-k7.json)
- [Facing-lane gap-witness refutation](../../experiments/0043-reflected-facing-lane-gap-witness.md)
- [All-root block-large reached-owner gate](../../experiments/0044-all-root-block-large-reached-owner.md)
- [All-root block-large reached-owner manifest](../../../data/derived/e3-block-large-reached-owner-all-roots-k6-n8.json)
- [Maximum single-lane spread refutation](../../experiments/0045-max-lane-spread-owner-counterexample.md)
- [Forced endpoint-extreme refutation](../../experiments/0046-forced-endpoint-extreme-counterexample.md)
- [Frozen minimum-anchor classification](../../experiments/0047-frozen-small-owner-anchor-structure.md)
- [All-root `k = 7` block-large and anchor-shape gate](../../experiments/0048-all-root-k7-block-large-and-anchor-shape.md)
- [Frozen minimum-anchor manifest](../../../data/derived/e3-frozen-small-owner-anchor-structure-n12-k7.json)
- [All-root `k = 7` block-large manifest](../../../data/derived/e3-block-large-reached-owner-all-roots-k7-n8.json)
- [All-root `k = 8` block-large and anchor-shape gate](../../experiments/0049-all-root-k8-block-large-and-anchor-shape.md)
- [All-root `k = 8` block-large manifest](../../../data/derived/e3-block-large-reached-owner-all-roots-k8-n8.json)
- [All-hole `k = 7` lane-path certificate gate](../../experiments/0050-all-hole-k7-lane-path-certificates.md)
- [All-hole `k = 7` lane-path manifest](../../../data/derived/e3-lane-path-certificates-all-roots-k7-n8.json)
- [Rank-two frontier obstruction](../../experiments/0051-rank-two-frontier-obstruction.md)
- [Rank-two lane-path counterexample manifest](../../../data/derived/e3-rank-two-lane-path-counterexample-k7-n5.json)
- [Complete rank-two Hall/capacity manifest](../../../data/derived/e3-rank-two-reflected-endpoint-hall-k7-n8.json)
- [Lean rank-two normal form](../../../ErdosSzekeres/StructuralChargingSpanFrontier.lean)
- [Lean rank-two capacity counterexample](../../../ErdosSzekeres/StructuralChargingRankTwoCounterexample.lean)
- [Rank-two gap-promotion gate](../../experiments/0052-rank-two-gap-promotion.md)
- [Rank-two gap-promotion manifest](../../../data/derived/e3-rank-two-gap-promotion-k7-n8.json)
- [Lean hidden-gap promotion bridge](../../../ErdosSzekeres/StructuralChargingRankTwoGenealogy.lean)
- [Adjusted-promotion counterexample](../../experiments/0053-adjusted-promotion-counterexample.md)
- [Adjusted-promotion counterexample manifest](../../../data/derived/e3-adjusted-promotion-counterexample-k7-n10.json)
- [Lean adjusted-promotion counterexample](../../../ErdosSzekeres/StructuralChargingAdjustedCounterexample.lean)
- [Cross-color common-span gate](../../experiments/0054-cross-color-common-span-gate.md)
- [Cross-color common-span manifest](../../../data/derived/e3-cross-color-common-span-gate-k7-n10.json)
- [Lean cross-color reuse counterexample](../../../ErdosSzekeres/StructuralChargingCrossColorReuseCounterexample.lean)
- [Conserved gap-token and pivot gate](../../experiments/0055-conserved-gap-token-carrier.md)
- [Lean gap-token conservation](../../../ErdosSzekeres/StructuralChargingGapTokenConservation.lean)
- [Lean tree-global token nonreuse](../../../ErdosSzekeres/StructuralChargingTreeTokenConservation.lean)
- [Lean selected-owner counterexample](../../../ErdosSzekeres/StructuralChargingSelectedBranchOwnerCounterexample.lean)
- [Lean selected-branch pivot repair](../../../ErdosSzekeres/StructuralChargingSelectedBranchPivot.lean)
- [Pivot-cone capacity gate](../../experiments/0056-pivot-cone-capacity.md)
- [Lean pivot-overflow closure](../../../ErdosSzekeres/StructuralChargingPivotOverflow.lean)
- [Central-cut and ordered `6+7` gate](../../experiments/0061-central-cut-cup-blocks67.md)
- [Lean symbolic `6+7` proof](../../../ErdosSzekeres/StructuralChargingCupBlocks67Symbolic.lean)
- [Residual `(4,8,8)` closure](../../experiments/0062-residual-488-cup-cap-staircase.md)
- [Lean residual closure](../../../ErdosSzekeres/StructuralChargingResidualWindow488.lean)
- [Facing-lane gap-witness manifest](../../../data/derived/e3-reflected-facing-lane-gap-witness-frozen-n12-k7.json)
- [Formalization plan](../../formalization_plan.md)
- [Literature review](../../literature_review.md)
- [Profile-search prototype](../../../scripts/decomposable_profile_search.py)
- [Exact coloring producer](../../../scripts/enumerate_decomposable_colorings.py)
- [Independent enumeration checker](../../../scripts/check_decomposable_enumeration.py)
- [Exact enumeration design and results](../../experiments/0002-e3-adversarial-design.md)
- [Post-six route review and disposition](../../experiments/0003-e3-post-six-route-review.md)
- [All-root context replay and collision redirect](../../experiments/0004-e3-all-root-context-profile.md)
- [Compact `k=6`, `n=9` collision certificate](../../../data/derived/e3-context-k6-n9-singleton-collision.json)
- [Independent collision checker](../../../scripts/check_decomposable_context_collision.py)
- [Rank/downset gate and interpretation](../../experiments/0005-e3-rank-downset-gate.md)
- [Compact rank/downset certificate](../../../data/derived/e3-rank-k6-n9-singleton.json)
- [Independent rank/downset checker](../../../scripts/check_decomposable_rank_profiles.py)
- [Lean consecutive-rank/downset specification](../../../ErdosSzekeres/RankProfile.lean)
- [Lean realizable pair-rank collision](../../../ErdosSzekeres/RankProfileCollision.lean)
- [Lean realization of every decomposable coloring](../../../ErdosSzekeres/DecomposableRealization.lean)
- [Realization bridge review and disposition](../../experiments/0006-decomposable-realization-review.md)
- [Turn-language spectrum rejection and Lean package](../../experiments/0007-turn-word-spectrum-design.md)
- [Lean turn-language semantics](../../../ErdosSzekeres/TurnLanguage.lean)
- [Lean open spectrum collision](../../../ErdosSzekeres/TurnLanguageCollision.lean)
- [Incoming-star prefix gate](../../experiments/0008-incoming-star-prefix-gate.md)
- [Exact incoming-star manifest](../../../data/derived/e3-incoming-star-prefix-k6-n8.json)
- [Independent incoming-star checker](../../../scripts/check_incoming_star_prefixes.py)
- [Lean incoming-star positive regression](../../../ErdosSzekeres/IncomingStarPositive.lean)
- [Lean depth-three prefix collision](../../../ErdosSzekeres/IncomingStarPrefixCollision.lean)
- [Lean crossing-pair transition](../../../ErdosSzekeres/IncomingStarTransition.lean)
- [Lean incoming-star transition collision](../../../ErdosSzekeres/IncomingStarTransitionCollision.lean)
- [Structural charging reduction](../../experiments/0009-structural-charging-gap.md)
- [Middle-determinacy extension charge](../../experiments/0015-middle-determinacy-extension-charge.md)
- [Strong-six branch reduction](../../experiments/0016-strong-six-branch-reduction.md)
- [Endpoint anomaly-class analyzer](../../../scripts/analyze_endpoint_anomaly_classes.py)
- [Balanced residue transitions](../../experiments/0017-balanced-residue-transitions.md)
- [Packed crossing splits](../../experiments/0018-packed-crossing-splits.md)
- [Middle crossing split state](../../experiments/0019-middle-crossing-split-state.md)
- [Finite middle-failure classes](../../experiments/0020-middle-failure-classes.md)
- [Common middle-failure bridge certificates](../../experiments/0021-middle-bridge-certificates.md)
- [Middle-bridge route counterexample](../../experiments/0022-middle-bridge-route-counterexample.md)
- [Middle-failure class analyzer](../../../scripts/analyze_middle_split_failure_classes.py)
- [Two-probe bridge compatibility analyzer](../../../scripts/analyze_two_probe_bridge_compatibility.py)
- [Middle-bridge route SAT generator](../../../scripts/check_middle_split_bridge_routes.py)
- [Independent middle-bridge route checker](../../../scripts/verify_middle_split_bridge_route_model.py)
- [Middle-split pair falsifier](../../../scripts/check_middle_split_pair.py)
- [Independent middle-split pair checker](../../../scripts/verify_middle_split_pair_model.py)
- [Repeated-residue falsifier](../../../scripts/check_repeated_residue_fibers.py)
- [Independent repeated-residue checker](../../../scripts/verify_repeated_residue_model.py)
- [Lean structural charging machinery](../../../ErdosSzekeres/StructuralCharging.lean)
- [Lean normalized seven-vertex core](../../../ErdosSzekeres/StructuralChargingCore.lean)
- [Lean arbitrary-set transport and closure](../../../ErdosSzekeres/StructuralChargingTransport.lean)
- [First `k=6` structural boundary](../../experiments/0010-structural-charging-k6-boundary.md)
- [Lean endpoint charge and coarse bound](../../../ErdosSzekeres/StructuralChargingBoundary.lean)
- [Separated-cap descent, port census, and overflow-route disposition](../../experiments/0011-separated-cap-descent.md)
- [Lean endpoint-port capacity](../../../ErdosSzekeres/StructuralChargingPortCapacity.lean)
- [Lean explicit-tree allocation and local coupling](../../../ErdosSzekeres/StructuralChargingTreeAllocation.lean)
- [Published child-slice semantics and first remaining boundary](../../../ErdosSzekeres/PublishedInductionSemantics.lean)
- [Published off-window classification](../../experiments/0012-published-offwindow-classification.md)
- [Independent off-window replay](../../../scripts/check_published_offwindow.py)
- [First saturated-boundary closure](../../experiments/0013-first-saturated-boundary-closure.md)
- [Lean sourced resource and gap-side closure](../../../ErdosSzekeres/StructuralChargingSaturatedResource.lean)
- [Certificate-free cup--cap duality](../../../ErdosSzekeres/Duality.lean)
- [First `k=7` cup-block frontier](../../experiments/0014-k7-cup-block-frontier.md)
- [Lean normalized `5+6` reduction](../../../ErdosSzekeres/StructuralChargingCupBlocks56.lean)
- [Independent rational-realization checker](../../../scripts/check_rank_profile_realization.py)
- [Singleton residual oracle](../../experiments/0024-singleton-residual-oracle.md)
- [Singleton residual manifest](../../../data/derived/e3-singleton-residual-k6-n9.json)
- [Independent singleton residual checker](../../../scripts/check_singleton_residuals.py)
- [Endpoint-span rank footprint gate](../../experiments/0025-span-rank-footprint-gate.md)
- [Lean side-labelled critical-cut semantics](../../../ErdosSzekeres/RootedChainFootprint.lean)
- [Endpoint-span rank manifest](../../../data/derived/e3-span-rank-footprint-k6-n9.json)
- [Independent endpoint-span rank checker](../../../scripts/check_span_rank_footprints.py)
- [Uniform singleton transition and two-root gate](../../experiments/0026-two-root-span-footprint-gate.md)
- [Two-root endpoint-span manifest](../../../data/derived/e3-two-root-span-k6-n9.json)
- [Independent two-root endpoint-span checker](../../../scripts/check_two_root_span_footprints.py)
