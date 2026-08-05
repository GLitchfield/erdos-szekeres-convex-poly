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
bridge-certificate refinement is retired as the main route. The next bounded
review must choose between global multi-deletion packing correlations and
stronger geometric realizability.

## Evidence

- [`ErdosSzekeres.Decomposable`](../../../ErdosSzekeres/Decomposable.lean)
- [`ErdosSzekeres.E3FiniteReduction`](../../../ErdosSzekeres/E3FiniteReduction.lean)
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
