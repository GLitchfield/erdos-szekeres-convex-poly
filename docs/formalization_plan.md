# Sweep-orientation formalization plan

Last updated: 2026-08-03.

## Leading mathematical interface

The model-selection ticket remains open while the alternative APIs receive the
same bounded comparison. The following two-layer interface is the working
candidate justified by the first compiling pilot, not yet a canonical choice.

The candidate uses two connected layers.

1. **Geometric statement layer.** Finite point sets in `ℝ²`, general position,
   convex position, forcing, and sharpness remain the public statement of the
   exact Erdős--Szekeres formula.
2. **Ordered combinatorial layer.** A generic sweep orders the points. Every
   increasing triple receives the color `left` or `right` from the sign of its
   determinant. Cups, caps, polygon chains, decompositions, and recurrences are
   proved on this finite coloring only after the required geometric bridge has
   been proved in Lean.

The first layer prevents an abstract coloring theorem from being mistaken for
a planar theorem. The second exposes the finite combinatorics in the user's
original angle-graph approach.

## Fixed convention

Normalize the sweep direction to increasing first coordinate. For `i < j < k`,

```text
χ(i,j,k) = left
  iff det(v_j - v_i, v_k - v_i) > 0
  iff slope(v_i,v_j) < slope(v_j,v_k).
```

General position excludes determinant zero. Reversing orientation conventions
would merely exchange `left` and `right`, but the convention above is canonical
inside this repository.

## Lemma ladder

The status labels below distinguish compiled infrastructure, known mathematics
still to formalize, and genuinely new research.

### Layer A: sweep and orientation foundations

| ID | Lemma or definition | Status | Purpose |
| --- | --- | --- | --- |
| A1 | `orientation` and planar `InGeneralPosition` | Compiles | Coordinate determinant and no-collinear-triple statement |
| A2 | `SweptConfiguration` with strictly increasing first coordinate | Compiles | Finite point configuration indexed in sweep order |
| A3 | `point_injective` | Compiles | The sweep labels distinct points |
| A4 | `turn`, `OrderedTriple`, and `tripleColoring` | Compiles | Two-coloring of the ordered complete 3-uniform hypergraph |
| A5 | determinant equals positive sweep differences times the consecutive-slope difference | Compiles | Algebraic bridge from orientation to the user's angles |
| A6 | left iff slopes increase; right iff slopes decrease | Compiles | Verifies the exact left/right convention |
| A7 | `exists_injective_sweepCoordinate` | Compiles | Choose a shear parameter outside the finite forbidden set |
| A8 | `shear_neg_shear` and `orientation_shear` | Compiles | Normalize the sweep by an invertible determinant-one map |
| A9 | `SweptPresentation` and `exists_sweptPresentation` | Compiles | Sort and equivalently enumerate the public `Finset` as a `SweptConfiguration` |

The presentation additionally proves that its induced left/right color is
exactly the orientation sign of the corresponding original, unsheared triple.
Thus the coordinate-order premise of Layers B--E is now discharged for every
finite public input satisfying `InGeneralPosition`.

### Layer B: realizable triple colorings

| ID | Lemma or definition | Status | Purpose |
| --- | --- | --- | --- |
| B1 | `OrderedTriple.map`, `TripleColoring.restrict`, `SweptConfiguration.restrict` | Compiles | State induced subconfigurations cleanly |
| B2 | `IsMonochromaticChain`, `IsCup`, and `IsCap` | Compiles | Common finite definition of cups and caps |
| B2a | `IsSweepRealizable` and its canonical witness | Compiles | Keep realizability available in combinatorial theorem signatures |
| B3 | `isCup_iff_isConsecutiveCup`, `isCap_iff_isConsecutiveCap` | Compiles | Matches classical recurrence-friendly definitions |
| B4 | every swept coloring satisfies the necessary four-index consistency law | Known; pending | Record realizability information rather than allowing arbitrary colorings |
| B5 | reflection exchanges cups and caps and preserves convexity | Known; pending | Symmetry control and proof reuse |

We will not assert that B4 characterizes realizability. Rank-three sign data can
be nonrealizable, and overly broad ordered-hypergraph generalizations are known
to fail. Any theorem not valid for arbitrary `TripleColoring`s must take a
`SweptConfiguration`, an `IsSweepRealizable` witness, or a separately proved
sufficient consistency hypothesis.

B1 also proves that restriction preserves sweep realizability. Combined with
`IsStrongPolygonOn`, the theorem
`SweptPresentation.containsConvexSubset_iff_exists_isStrongPolygonOn` now
identifies the public `ContainsConvexSubset` predicate exactly with an
increasing restriction that satisfies the strong-polygon law.

B3 uses a four-point orientation propagation identity and strong induction on
the outer index span. It is available both for a concrete
`SweptConfiguration` and for an abstract coloring with an `IsSweepRealizable`
witness; no corresponding claim is made for arbitrary triple colorings.

### Layer C: recognize convex position from signs

| ID | Lemma or definition | Status | Purpose |
| --- | --- | --- | --- |
| C1 | `mem_convexHull_triangle_iff_insideTriangleBySigns` | Compiles | Characterize triangle membership by four nonzero orientation signs |
| C2 | `inConvexPosition_four_iff_no_mem_triangle` | Compiles | A four-point set is convex iff no point lies in the other triangle |
| C3 | `inConvexPosition_four_iff_orientation_signs` | Compiles | Give a purely sign-based four-point convexity certificate |
| C4 | `inConvexPosition_iff_four_subsets` | Compiles | Lift the local certificate to arbitrary size using Carathéodory's theorem |
| C5 | `IsStrongPolygon`, `SweptPresentation.inConvexPosition_iff_isStrongPolygon` | Compiles | Exact four-index combinatorial form of the geometric target polygon |

C1--C5 establish the full combinatorial/geometric safety bridge. The C3 certificate is
stated for arbitrary point order; cyclicity and sign reversal reduce it to the
four colors of increasing triples in sweep order. C4 uses Carathéodory's
theorem and general position to show that every convex-hull obstruction is
witnessed inside a four-point subset. C5 proves that a sweep-ordered set is
convex exactly when every increasing four-tuple has one of the patterns
`++++`, `++--`, `--++`, or `----`; equivalently, its two middle vertices form
compatible upper/lower hull chains. The theorem is transported through the
generic determinant-one shear to the original public point set, while B1
extends the bridge to selected subsets.

### Layer D: classical controls

| ID | Lemma or definition | Status | Purpose |
| --- | --- | --- | --- |
| D1 | cup--cap recurrence engine on ordered vertices | Compiles | Pincer induction, partition, and chain-splicing pigeonhole engine |
| D2 | exact cup--cap number `binom(a+b-4,a-2)+1` | Compiles, including planar sharpness | Reproduce the 1935 theorem in the chosen API |
| D3 | classical binomial upper bound for `ES(n)` | Compiles | End-to-end positive control of all bridges |
| D4 | recursive `2^(n-2)` lower-bound construction | Compiles as `classical_lower_sharpness` | Formal sharpness for all `n` |
| D5 | exact cases `n = 3,4,5` | Compiles, including a kernel-checked LRAT proof of the nine-point case | Small controls; `n=6` is a separate certificate project |

### Layer E: the modern structural frontier

| ID | Lemma or definition | Status | Purpose |
| --- | --- | --- | --- |
| E1 | composition/decomposition of sweep colorings | Arbitrary deep-below partitions, recursive decomposability, hereditary nonempty subsets, binary deep composition, and the coordinate-to-color bridge compile | Express the published recursive class, including interleaved sweep orders |
| E2 | polygon-size recurrence under composition | Pascal-row aggregate recurrence, both directions of the crossing cup/cap characterization, and the two-endpoint crossing-chain bounds compile | Control decomposable configurations |
| E3 | exact formula for decomposable point sets | The exact upper formula compiles at `k = 5` and `k = 6`; the latter uses hereditary kernel-checked `(4,6,6)` and `(5,6,6)` state bounds. The uniform endpoint-profile counting induction remains pending | Reproduce the strongest directly relevant structural theorem |
| E4 | a minimal counterexample to the exact formula is indecomposable | The exact counterexample predicate and conditional consequence `IsExactFormulaCounterexample.not_isDecomposable` compile; uniform discharge still awaits all-`k` E3 | Isolate the genuine obstruction without hiding its dependency |

### Layer F: new research required

The remaining destination needs a new theorem controlling indecomposable
realizable colorings. Plausible forms include a nontrivial decomposition after
deleting few vertices, a sharper rank recurrence using the four-point laws, or
an implication through the Erdős--Tuza--Valtr parameter lattice. None is
currently claimed.

The Layer E definitions deliberately distinguish the older contiguous-cut
API `HasDeepSplit` from the published arbitrary deep-below partition.  The
theorem `HasDeepSplit.toHasDeepBelowSplit` embeds the former into the latter,
while `IsGeometricallyDeepBelow.toHasDeepBelowSplit` proves the general
crossing-color law from determinant orientations.  Thus Horton-style
interleaving is not silently excluded from E1.

The first attempted transcription of the 2026 E3 induction exposed a boundary
case that must be resolved before the published upper theorem can be claimed.
The proof selects auxiliary values `u'` and `a'` and, when
`a' + u' <= k - 1`, absorbs two next binomial terms into disjoint intervals.
At `(a,u,k,u',a') = (4,5,5,1,3)`, however, the first advertised interval is
empty while its next binomial term is `choose 3 0 = 1`.  The resulting bound is
eight, not the outer threshold seven.  Lean checks this closed calculation as
`published_induction_boundary_regression`.  This does not refute the diagonal
theorem, but it does rule out completing E3 by copying that induction step
unchanged; a strengthened invariant or a separate boundary argument is
required.

The complete journal proof has now been checked as well as the omitted
conference proof.  Its final displayed absorption makes exactly the same
endpoint assumption: it rewrites a classical cup--cap contribution as a
Pascal interval even when the advertised interval is empty.  The theorem
`decomposableBinomialWindow_diagonal_pair_le` verifies separately that the
outer `(k,k,k)` split has the necessary lower endpoint automatically.
Therefore the obstruction first appears in an off-diagonal child state
generated by the induction; a diagonal-only arithmetic patch is insufficient.

The boundary classification is now sharper than the single numerical
regression.  In the interior, `decomposableBinomialWindow_pair_le` proves that
the two auxiliary windows are disjoint subintervals of the outer Pascal-row
window.  Failure occurs when an auxiliary chain lies below that window and
its classical cup--cap contribution sits just outside it.  The geometry does
constrain this overflow: `cup_inter_upper_card_le_two` and
`cap_inter_lower_card_le_two` prove that a crossing cup or cap can use at most
the two opposite-side sweep endpoints; the pointwise lemmas
`upper_mem_cup_isSweepEndpoint` and `lower_mem_cap_isSweepEndpoint` identify
those vertices as actual extremes of the entire chain.  Meanwhile,
`isStrongPolygonSet_iff_inter_cup_cap` gives the exact crossing-polygon
characterization.  The corrected E3 invariant therefore has to retain these
endpoint states; cardinality alone is insufficient.

The next endpoint layer is now exact rather than merely necessary.  The
directional predicates `IsLeftSweepEndpoint` and `IsRightSweepEndpoint` split
the old endpoint flag into two disjoint states for a point outside a nonempty
chain.  The theorems `insert_upper_isCupSet_iff_isSweepEndpoint` and
`insert_lower_isCapSet_iff_isSweepEndpoint` prove that adjoining a vertex
across a deep-below split preserves the relevant chain if and only if it is in
one of those two states.  Their cardinal corollaries implement the resulting
`r -> r+1` transitions.  Negating the transition gives the complementary
saturation rule: if the larger cup or cap is forbidden, every opposite-block
vertex is strictly straddled by the smaller chain.  What remains is to
aggregate these binary endpoint/straddling states over the recursive
decomposition without double-counting the boundary term exposed above.

An adversarial truth-or-counterexample pass has added two independent checks
on this direction.  Exact enumeration through eight labeled leaves covers
17,297,280 ordered decomposition trees and 186,888 distinct eight-leaf
colorings; an independent replay agrees on the complete coloring hash and all
cup, cap, strong, and signotope profiles.  Every recursive coloring in the
completed range is a signotope, and every one of the 2,862 eight-leaf
colorings with no strong five-set has both a four-cup and a four-cap.  Lean now
proves the all-size structural statement as
`IsDecomposableOn.turnSequenceAllowed`: the recursive crossing law alone
implies the rank-three one-change axiom, without realizability.  Applying the
existing kernel-checked nine-point LRAT certificate then gives
`IsDecomposable.containsStrongPolygonSet_five_of_nine_le` and closes the full
abstract decomposable base case as `decomposableExactUpperAt_five`.

This validates the signotope reduction and the five-vertex base, but not the
general formula.  The remaining E3 research obligation is still an all-`k`
counting invariant that charges stacked singleton-anchor straddling contexts;
finite agreement through eight leaves cannot supply that induction.

The first two proposed off-diagonal falsification states are now closed at the
semantic level.  Theorems
`exists_cap_four_or_cup_six_or_strong_six` and
`IsDecomposable.exists_cap_four_or_cup_six_or_strong_six` are backed by a
kernel-checked 20,163-clause LRAT certificate and prove the twelve-vertex
`(4,6,6)` alternative.  The theorem `decomposableStateUpper_466` now lifts
that exact-size result to every decomposable subset above the threshold eleven,
which is the hereditary form required by an induction.  A checkpointed
1,667,699-addition LRAT proof and generated semantic bridge likewise prove
`exists_cap_five_or_cup_six_or_strong_six`; restriction lifts it to
`decomposableStateUpper_566`.  The dual-state transport and audited finite
reduction then yield
`decomposableExactUpperAt_six : DecomposableExactUpperAt 6`.

This closes the decomposable upper formula at six vertices, but it is a finite
milestone rather than the missing uniform induction.  The all-`k` endpoint
profile or context-carrying argument remains the E3 research obligation.

The large `(5,6,6)` semantic bridge now has an independently checked bounded
proof architecture.  Its 155,064 clauses are covered by 769 semantic chunks,
4,096 raw aggregation modules, and 1,024 midpoint modules.  Named midpoint
propositions keep the final elimination tree small, while a single compiling
`rfl` theorem identifies that tree with the canonical checkpoint proposition.
An independent Python checker imports neither generator and reconstructs the
whole hierarchy directly from the canonical DIMACS input.  The final Lean
audit reports only `propext`, `Classical.choice`, and `Quot.sound` for
`decomposableExactUpperAt_six`, with no `sorryAx` or project axiom.

The post-six Sol/Fable review did not support defining the uniform endpoint
profile immediately. Both reviewers instead selected the precise hereditary
boundary diagnostic `DecomposableStateUpper 4 5 5`, whose threshold is seven.
That diagnostic now compiles as `decomposableStateUpper_455`, together with
its color dual `decomposableStateUpper_545`. Its eight-vertex signotope CNF has
56 variables and 1,134 clauses; Lean kernel-checks the 39,037-byte LRAT trace,
and eight generated semantic chunks connect every clause to the project
predicates. This establishes that the published `8 > 7` regression is a
proof-method failure, but it does not supply the missing inductive transition.
The all-root directional context-profile gate is complete.  Independent
programs agree through eight leaves on every compatible root, 1,896,168
anchor/four-chain records, and all restriction and local endpoint checks.
Same-gap and cross-anchor maxima summaries collide on open branches.  The
complete all-gap word has no open `k = 5` collision through eight leaves, but
a compact targeted certificate at `k = 6`, `n = 9` gives two decomposable
parents with identical child all-gap words, no strong six-set, and different
parent profiles.  Thus maxima-only candidate B is not a valid uniform
composition state.  The next formal result should define the fixed-ambient
profile aggregation and kernel-check this explicit incompleteness witness,
building on the compiling fixed-ambient directional-witness monotonicity
lemmas in `ContextProfile.lean`, while the
research route redirects to a correlation-preserving rank/downset state or a
bounded transition congruence that separates the witness.

The first rank/downset redirect has now passed through its own exact negative
gate. At the `k = 6`, `n = 9` singleton root, independent programs enumerate
all 186,888 decomposable upper-child colorings and 85,797 open parents. Equal
ordered child downset words can produce unequal parent words, and even equal
complete child pair-rank matrices can produce unequal parent matrices. The 34
observed parent downsets remain vertex-injective, but their exact empirical
compatibility graph has a 27-clique, ruling out any 16-state bound based only
on pairwise incompatibility of those raw values. The bounded pair-rank
collision is now also a compiling Lean theorem for two explicit rational
planar configurations. A surviving rank strategy must retain higher-order
predecessor correlations, use a different label, or exploit geometric data
strictly richer than realizability itself; none is yet selected as the
uniform E3 route.

The abstract-versus-planar boundary for recursive decomposability is now
closed uniformly in `ErdosSzekeres/DecomposableRealization.lean`.  Lean proves
a fixed-abscissa merge theorem for arbitrary interleaved `HasDeepBelowSplit`
parts by choosing one finite bound on the required vertical shift.  Induction
on `IsDecomposableOn` then constructs strict orientation signs on the whole set,
and `IsDecomposable.isSweepRealizable` packages those points as a
`SweptConfiguration` in general position.  Consequently a state-transition
collision within the abstract decomposable class cannot be removed by adding
mere straight-line realizability.  This is a model bridge, not the missing
`2^(k-2)` count; the next uniform work still requires a concretely specified
`k`-bounded higher-order state or a different structural invariant.  The
bridge realizes the coloring and does not claim that its coordinates witness
the same tree under the stronger `IsGeometricallyDeepBelow` predicate.

The corresponding specification layer now compiles in
`ErdosSzekeres/RankProfile.lean`. `HasPairRankAtLeast` is stated directly by an
actual `CupCap.IsTurnChain` ending at the ordered pair, and
`InVertexDownset` uses one incoming pair to witness both clipped coordinates.
Theorems prove monotonicity under enlargement of the fixed ambient subset,
antitonicity in the requested rank threshold, the rank-one base case, and
lower-rectangle closure. These facts hold for an arbitrary triple coloring;
decomposability or sweep realizability belongs only in later transition or
witness theorems. `RankProfileCollision.lean` completes the bounded `k = 6`,
`n = 9` target with a kernel-checked realizable non-congruence witness. The
next higher-order gate has now produced both reusable machinery and a sharper
negative theorem. `TurnLanguage.lean` defines complete bounded consecutive
turn languages, proves its executable predecessor recurrence equivalent to
increasing-chain semantics, and isolates the constant-turn terminal-star
update. `TurnLanguageCollision.lean` kernel-checks two open decomposable
seven-vertex parents whose lower endpoint-forgetting spectra agree through
depth four but whose parent spectra differ. The word `right,right,left` can
reach `(5,6)` only when its prefix occurs at an edge ending specifically at
vertex `5`; a decoy occurrence at another endpoint cannot compose. Thus more
word depth and openness do not repair the quotient. The smallest surviving
bounded candidate is the incoming-star spectrum, which groups language values
by terminal endpoint before forgetting vertex identities. Before selection as
a uniform E3 route, it must pass an independently checked all-root transition
gate and a prefix-control test for arbitrarily interleaved deep splits; failure
of that test redirects away from deterministic quotient refinement.

The structural-charging interval layer now compiles in
`ErdosSzekeres/StructuralChargingIntervals.lean`. Finite interval Helly turns
failure of a common cap-witness cut into two weakly separated witnesses, whose
intersection has at most one vertex. Two four-caps therefore reserve seven
ambient vertices. A deterministic eight-point countercontrol shows this is
sharp and that separation alone forces no target outcome. The normalized
`4+5` cup-block statement now compiles by a nine-witness symbolic proof;
reversal and sorted restriction transport close both arbitrary orientations.
The resulting unconditional cup-block charge is eight. The separated-cap
exterior bound remains open, and its compiling conditional consequence would
recover the diagonal bound 16.

The stronger root-local contract now compiles outright in
`ErdosSzekeres/StructuralChargingSingletonRoot.lean`. The endpoint-straddling
law proves that two weakly separated upper four-caps at a singleton deep-below
root force a parent five-cap. Consequently the separated-cap charge holds, and
its compiling cardinal consequence reaches 16 without the state-566
certificate. More importantly, an open singleton-root parent cannot enter the
separated-witness branch: every upper four-cap straddles the root, so the
remaining structural work is the common-cut branch. A certificate-free proof
must recursively expose its first separating decomposition node and recover
the coupled Pascal contribution there. The first uniform lemma now compiles:
for arbitrary positive `a`, absence of a parent `(a+1)`-cap makes the
singleton root's sweep index a common cut for every upper `a`-cap. Thus the
next proof obligation begins at the decomposition-tree descent, not at interval
Helly or root-cut existence. `StructuralChargingFirstSplit.lean` now supplies
the honest existential descent interface: a witness set with at least two
vertices is separated by some recursive split contained in the original
decomposable set. It does not encode a canonical or minimal-depth node.

The first force-outcome proposal at such a split is false. A deterministic
complete census through eight vertices finds 185 violating root/cap-pairs at
seven vertices and 13,266 at eight vertices. Requiring the two caps to be
disjoint still leaves 74 eight-vertex violations. The smallest shared-boundary
and disjoint witnesses are independently replayed with explicit decomposition
trees. Consequently the next structural invariant must count the one or two
lower-child endpoint ports used by each crossing cap; another binary
force-outcome case split has no support.

`StructuralChargingPortCapacity.lean` now proves this local invariant for an
arbitrary finite weakly ordered family. A common vertex of two family members
is forced to be the earlier member's right sweep endpoint and the later
member's left sweep endpoint. Three uses would make the middle member have at
most one vertex, so each lower-child vertex has capacity two. Double counting
then gives
`∑ i, ((caps i) ∩ lower).card ≤ 2 * lower.card`.

The remaining obstruction is no longer local endpoint geometry. The
existential split theorem forgets the occurrence of a split in a decomposition
tree, so it cannot yet assign each witness or Pascal overflow to a unique node.
The next layer must reify decomposition trees and prove a minimal-separating
node allocation, or prove a choice-independent no-double-charge theorem.

`StructuralChargingTreeAllocation.lean` completes the reified-tree option. It
bridges ordinary decomposability to a data-carrying tree, looks up nodes by
Boolean paths, computes the lowest separating address, proves that the
address resolves to a genuine separating split, and proves uniqueness within
the chosen tree. The next contract must define the `k = 6` Pascal overflow
assigned to such an address and connect its demand to the compiling local
two-port capacity theorem.

The allocation-to-capacity coupling now compiles as well. Every cap assigned
to one address crosses the resolved split, and an ordered family of four-caps
at that address has at most `2 * node.lower.card` members. This statement is
sharp on the seven-vertex counterexample and is only a cap-witness count. It
does not bound the Pascal window, extract the ordered `4+5` cup blocks, or
prevent a vertex from supplying ports at several ancestor addresses. A sound
future charging layer may require weighted tokens, but it cannot define them
before recovering the semantic family counted by the published child
summands.

A bounded blind Sol/Fable review at packet SHA-256
`1a879cf0be9c3bceec4d9ec5e514b4f73a0a9650bfb85435b93e9c79a08899ae`
rejects selecting that token route in its current form. Its proposed follow-up
items were subsequently disposed: the singleton `(4,5,5)` boundary is already
closed by `singleton_root_card_le_seven`, while deterministic incoming-star
refinement is stopped by the recorded nine-vertex collision.

A corrected audit with question SHA-256
`116946c9457e8592da499dadaed8cd028562e85ee109429c49b06c90be2ceb80`
finds that the proposed one-unit classification is itself undefined. Sol's
high-confidence `partially_supported` result identifies the smallest
non-circular work item as specification recovery: define a decidable semantic
`ChildContribution` relation from a coloring, fixed explicit tree, node
address, child state, and concrete resource; prove that the finite resource
family has the cardinality of the relevant published child summand; and prove
restriction/composition and stable ancestor-identity properties. Membership
must not mention overflow, the desired bound, or successful extraction. Only
then is a bounded extraction/reuse census well-posed. The corrected Fable run
generated no valid review because it hit an external session quota, so there
was no corrected Sol/Fable consensus. This was route evidence, not a proof.

Direct recovery of the missing source semantics has now superseded the audit's
information gap. `PublishedInductionSemantics.lean` defines the published
maximal child index, constructs the actual retained vertex subset of size
`decomposableThreshold a index k + 1`, and proves the exact complement-plus-core
inequality at the next threshold. It also proves uniformly that auxiliary
index one forces the entire nonempty child to be a singleton whenever
`2 ≤ a ≤ k`. Therefore the `(4,5,5,1,3)` source branch is transported into
`singleton_root_card_le_seven` by
`published_455_index_one_boundary_card_le_seven`; the precise caveat noted by
the corrected Sol audit is closed with only `propext`, `Classical.choice`, and
`Quot.sound`. This does not repair all off-diagonal states: the next bounded
route-selection problem is to classify positive indices strictly below
`k - a + 1` (and the dual range) after removing index one, then state the
smallest non-scalar transition that covers those remaining cases.

The bounded classification in
`docs/experiments/0012-published-offwindow-classification.md` now sharpens that
problem. Independent implementations agree through `k = 20` on 7,752 feasible
scalar failures and 3,670,056 child-cardinality splits. Once index-one branches
are removed, every remaining state has `a' = a - 1` with
`u' < k - a + 1`, or its color dual. The first case is
`(a,u,k,a',u') = (4,6,6,3,2)`, where the children have cardinalities `(2,10)`
or `(3,9)`. The saturation statement is no longer only computational:
`published_feasible_auxiliary_saturation` proves it for all admissible
parameters by allocating nonsaturated child thresholds to disjoint outer-row
prefix and suffix intervals. The bounded census still supplies the first
structural gate. A fresh route review must freeze a certificate-free uniform
saturated-boundary contract and test it at this two/three-anchor state; using
the existing state-466 certificate as the gate would be circular.

The first structural bridge at that gate now compiles independently of the
certificate. The upper child has more than five vertices, so the ordinary
`(3,6)` cup--cap theorem supplies a three-cap unless a forbidden parent
six-cup already exists. If the parent has no four-cap, the deep-below endpoint
transition forces that cap's sweep interval to contain every lower-child
vertex. `first_saturated_boundary_has_covering_upper_three_cap` packages this
resource. It is not yet the saturated transition: the next theorem must state
how this common covering cap is consumed or transported through recursive
decomposition.

That first transition is now closed by a simpler structural argument in
`StructuralChargingSaturatedResource.lean`. Around any lower-child vertex,
absence of a parent four-cap makes both upper gap sides three-cap-free, hence
cups. Upper-child decomposability supplies the one-change law, and the
certificate-free `4+5/5+4` cup-block theorem bounds their union by eight.
Thus `upper_card_le_eight_of_nonempty_lower_open_466` eliminates both feasible
child pairs `(2,10)` and `(3,9)`. The parameterized surviving kernel says that
absence of a parent `(r+1)`-cap makes both gap sides `r`-cap-free. Generalizing
the cup-block bound to these higher cap-free side states is the next proposed
uniform transition, pending corrected reciprocal route review. The elementary
duality facts have been separated into `Duality.lean`; the derived theorem
`lower_card_le_eight_of_nonempty_upper_open_646` also rules out the reversed
child pairs `(10,2)` and `(9,3)` without a certificate dependency.

The next `k = 7` pass now distinguishes two layers. The uniform elementary
two-gap bound closes `(4,7,7,3,2)` and its color dual, and its sharper
`2*(u-1)` form separately excludes the 13-vertex child at
`(4,7,7,3,3)`. For the remaining sizes 11 and 12,
`StructuralChargingCupBlocks56.lean` freezes the normalized `5+6/6+5`
contract and proves its complete transport and application shell. A new
seven-chain lemma, five immediate fan cups, a bridge seven-cup, and three cap
leaves reduce the normalized target to `CupBlocks56ResidualA` and
`CupBlocks56ResidualC`. Both residuals now compile. Residual C uses the
one-change law to force turns `459`, `346`, and `467`; a left `4510` gives an
explicit seven-cup, while a right `4510` combines a tail six-cup, a skip
six-cup, and a forced right fan into the strong seven-set
`{4,5,6,7,8,9,10}`. Consequently the normalized theorem and arbitrary
`5+6/6+5` transport close all `(4,7,7,3,3)` child pairs and their duals. The
bounded SAT traces were used only for proof discovery.

The active state is now `(5,6,7,4,2)`. The exact proposed local dependency is
`TwoCapFreeSidesBound567`: two ordered sides, each four-cap-free, have total
cardinality at most 21 when their union obeys `OneChangeOn` and avoids a
five-cap, six-cup, and strong seven-set. Lean now proves the elementary first
layer: the ordinary `(4,6)` cup--cap recurrence plus `OneChangeOn` bounds each
side by 15, so every counterexample has both side cardinalities in `[7,15]`.
The `(4,4)` and `(4,5)` recurrences then supply a four-cup on each side and a
five-cup on at least one side. Applying the completed `4+5/5+4` theorem proves
that the residual window contains either a four-cap meeting both sides or a
strong six-set. Lean now extracts a local nonextension certificate for every
unused vertex. Four-cap failure can be localized to a consecutive triple;
five-cups force nested right-bridge colors; and a strong set is proved
equivalent to middle determinacy of all its triple colors.
Lean also proves the complete conditional application and color-dual shells,
eliminating `(2,24)`, `(3,23)`, and `(4,22)` if the residual local bound is
supplied. Bounded SAT falsification found a validated 21-point witness.
The middle-determinacy encoding now also finds cuts 10 and 11 UNSAT, completing
all 22-point cuts computationally. Separate small SAT models refute a naive
identical witness-profile collision, so the remaining proof must count global
middle-color and outside-vertex correlations. This is sharp computational
evidence, not a proof or a reason to freeze the premise as a theorem.

The proposed nine-signature cap selector has since been retired. Hall-deficient
certificates on validated sharp 21-point models refute even its permissive
capacity-two matching relaxation, and its 17-slot conclusion is circular at a
22-point counterexample. The checked `(5,6,6)` state instead closes the whole
no-strong-six branch at ambient size 15. At size 22 it makes the strong-six
family avoid every prescribed six-set. The checked `(4,6,6)` state then gives
an internal strong six on one side unless the cut is exactly `11+11`; all
opposite-side vertices have a forced middle failure. Lean classifies each
failure into one of 19 indexed classes and maps every class to a common
four-vertex bridge certificate. Deletion packing supplies twelve such
certificates. An interior certificate anchors the probe to a three-vertex
polygon frame, and Lean proves equality for two probes anchored to the same
frame. Exhaustive five-vertex checking shows that this equality does not
extend to a triple containing both probes and does not force a strong five.
The three-probe repair is false as well: an independently replayed local SAT
model has shared frames in both directions but no extreme `1+5` or `5+1`
strong six. This is route-selection evidence rather than a Lean theorem. The
local certificate state therefore cannot by itself create the residue carrier
needed by packing. The next reviewed route must use correlations among
several global packing deletions or restore stronger geometric realizability
information.
That review selected packing conditionally, but the bounded gates did not
produce a theorem-sized core. All three sharp 21-point models satisfy full
packing while thousands of deletions have only middle crossing witnesses;
after excluding internal strong sixes, a `7+8` full-packing state is UNSAT,
but even a proof-core shrink retains 704 packing deletions across every split.
The modest multi-deletion extremization route is therefore retired. The
geometry fallback is also closed for this local obstruction: explicit rational
coordinates realize the decisive no-extreme coloring, and Lean proves
`middleSplitRealizationColor_isSweepRealizable`. The full SAT avoidance bundle
has not been promoted to Lean. The pre-vetted terminal fallback is to design a
new uniform E3 invariant, subject to the existing transition falsification
gates rather than another local refinement of this balanced leaf.
Normalized `5+5`, `6+4`, and `6+7` block shortcuts also have validated SAT
countermodels and must not be used. The balanced `11+11` leaf retains its
hereditary interface: unless an internal strong six redirects to this branch,
each vertex activates a four-cap or strong-six witness through itself on the
opposite side.

The proof is complete only when that new structural input and Layers A--E
combine into the already-defined `ErdosSzekeresConjecture` with no placeholders.

The first invariant-design oracle is now complete at the `k = 6`, `8 -> 9`
singleton boundary. Property-relative anchored profiles have 5,917 values on
the 186,888 child colorings; closure under all 18 singleton contexts produces
7,159 residual classes. The known all-gap collision is separated by an
interior rooted cup-extension response, while the complete pair-rank collision
remains equivalent. This is bounded evidence, not a Lean result. The next
formal contract must replace the ambient-length response word by a finite
critical rooted-chain footprint and prove its semantic transition before any
counting claim is attempted.
The bounded route review rejects freezing that footprint from prose alone.
The next contract is specification-first: test whether each critical cut set
is convex, define the domination quotient and retained endpoint incidence,
then demand singleton observation and self-composition congruence. Only a
surviving carrier earns the uniform singleton-extension iff lemma in Lean.

That first specification gate is now resolved, with one correction. The
unlabelled successful-cut set is not convex: it is the union of a left and a
right endpoint ray. `RootedChainFootprint.lean` proves the side-labelled ray
closure, external disjointness, exact extension iff, and an explicit unsplit
counterexample. Retaining exact total endpoints yields the span-rank footprint.
Two independent implementations exhaust all 186,888 children and 3,363,984
singleton extensions at `k = 6`, finding zero observation-readout mismatches
and zero transition collisions and separating both prior regressions. This
surviving carrier is still ambient-quadratic and has 46,699 child classes, so
it is a semantic transition candidate rather than the desired finite count.
The next formal obligation is its uniform singleton transition, followed by
the two-vertex interleaved-root falsification gate and a dominance quotient
with a proved `k`-only weight.

The uniform singleton obligation and the first interleaved-root gate now
close. Lean defines exact sweep spans and cup/cap span-rank thresholds, proves
their endpoint comparisons and rank updates, gives erase/recover iff laws,
bounds the opposite-color singleton contribution by three, and characterizes
terminal strong-`k` creation by a child strong set or `(k-1)` chain. The
independently replayed `k = 6`, `7+2 -> 9` gate covers all 762,912 two-root
parents and all 720,528 interleaved transitions with zero footprint
collisions. No theorem removes ambient endpoint identities, so this does not
yet provide a finite carrier depending only on `k`. The active design target
is now the dominance quotient and its transition-preserving, `k`-only weight;
the 16,819,920-parent `8+2 -> 10` census is reserved as a falsifier for a
concrete quotient rather than run as unstructured depth.

The dominance and rooted-interface gates are now complete. Lean proves the
four sound one-sided dominance rules, but the first finite `k`-only quotient
has 320 independently replayed collisions at the reserved `8+2 -> 10` gate.
A reviewed cut-relative repair retains exact recursive side states and clips
crossing-port distances. Depth three is noninjective but fails a rooted
transition; depth four is already injective on all 46,699 raw classes at the
decisive middle cut. Lean's
`twoSidedExtensionDominates_diagonal_iff` additionally proves that the exact
two-sided dominance frontier can have arbitrarily large equal-rank
antichains. The uniform finite-state route is therefore stopped. The next E3
contract uses the raw footprint only locally. Its first bounded gate now
passes: Lean defines the exact-rank Pascal demand, proves both uniform
one-step threshold bounds, and constructs the unique lowest-node endpoint
allocation. Independent programs check every compatible root through eight
vertices at `k = 6`; all 631,474 open exact-rank frontiers fit their adjacent
coefficient. Lean now also defines those exact spans and their
inclusion-minimal frontier, proves its endpoint antichain and ordering laws,
and identifies every exact crossing rank with an exact predecessor ray rank
in either child. Under no strong `k`-set, opposite cup/cap ranks at a crossing
pair sum to at most `k + 1`. The bounded gate refutes the tempting shortcut of
applying cup--cap directly to either endpoint projection: each projection fails
in 1,208 group instances, with 996 rank-three groups failing both.
`AllocatedExactRankSlotting` is therefore the precise remaining local
contract. Lean proves that any such injection into the `(rank - 1)`-subsets of
`Fin (k - 2)` gives the desired Pascal bound. The first ray-incidence
construction now survives the exact gate: encode past/future rank pairs at
both endpoints as lower ideals of the truncated Pascal rectangle and allow
each span either endpoint's lattice interval. All 631,474 frontier groups have
distinct representatives; one-endpoint and fixed-label controls fail. Lean
proves the ideal boundary encoding into the exact Pascal layer and that the
full all-subfamily Hall condition constructs the slotting. The unreflected
geometry-specific Hall premise is formally false: a kernel-checked `n=12`,
`k=7` coloring has two opposite-orientation rigid spans with the same full
ideal. The reviewed rotate-complement repair now passes its bounded gate.
Lean proves reflection is an involution, induces reversal on the unchanged
Pascal-slot carrier, preserves the Hall-to-capacity reduction, and separates
the frozen pair as full versus empty. Independent implementations find no
reflected Hall failure on the complete frozen root frontier or any of the
631,474 existing `k=6` groups. Lean now derives the orientation normalization
from actual predecessor/successor child rays at the unique lowest separating
node and proves that the incident endpoint profile belongs to the reflected
candidate family. This is an incidence bridge, not an injectivity theorem.
Lean now also defines closed endpoint blocks of the ordered frontier, proves
their left/right order equivalence and their equivalence with nonempty
intrinsically consecutive subfamilies, and freezes reflected block expansion.
The deterministic active-profile shortcut is computationally false on a
five-span `k=6` block. Keeping the whole active endpoint interval is still too
strong: in the frozen `n=12`, `k=7` root, adjacent spans `(2,5)` and `(4,6)`
both have singleton reflected active interval `{3f}`, so their two-span block
has union size one. Lean kernel-checks the exact ranks, frontier membership,
adjacency, singleton active candidate sets, and the resulting failure of active
block expansion; independent cell-mask and row-height replays agree. This does
not refute the full reflected two-endpoint block target, but it retires proofs
that discard the inactive endpoint. The predeclared next design target is
therefore a skew-Bollobas set-pair encoding of actual child-ray events.
After a local block theorem and general Hall come the global slot injection
and the final `allocatedSpanPascalDemand_le_window` return to the published
child-slice induction.

The first actual-event contract has now failed its frozen gate.  It keys an
event by normalized ray direction, the complete child witness chain, and one
marked chain vertex.  The adjacent active-interval collision does have a
nonempty actual-event support difference, but the full six-span frontier is
decisive: the first four unique present sets are pairwise disjoint, and the
fifth span can place at most `k-rank-1 = 3` events in its absent set.  Two
independent implementations certify the resulting `4 > 3` obstruction.  This
is computational route-selection evidence, not a Lean theorem and not a
refutation of every ray-event quotient.  The pending decision compares a
semantic coarsening of events, incidence-matrix accounting, and direct use of
both reflected endpoint intervals.

The preferred semantic coarsening is now independently refuted as well. Its
24 keys retain normalized direction, ordinal chain role, and clipped
complementary one-sided rank inside the active child. On the frozen adjacent
pair `(2,5)`, `(4,6)`, both spans have exactly the keys `(past,0,0)` and
`(past,1,2)`. Because absence is correctly defined fiberwise, neither key can
belong to the later absent set; the required skew intersection is impossible
under every tie-breaking rule. Forgetting direction preserves the collision,
while restoring chain identity returns toward the fine-key capacity failure.
The route review selected exact reflected endpoint-row independence only as
the sharper falsifier. Sol returned `partially_supported` at high confidence;
Fable returned a zero-token provider connection error, so there was no model
consensus. The exact frozen matrices refute independence: the cap/rank-three
matrix has rank five on six rows with circuit coefficients `(2,-1,-2)` on
spans `(0,4)`, `(4,6)`, `(6,10)`, and the cup/rank-four matrix has rank three
on four rows with coefficients `(2,1,-1,-2)`. Reflected Hall still passes,
showing that this linearization was strictly stronger than the needed claim.

The two-lane alternative now has one precise positive local gate. The rigid
rule assigning meet to the earlier span and join to the later span fails at
the full/empty adjacent pair `(4,6)`, `(5,7)`. Allowing whichever of the two
assignments preserves both untagged candidate unions succeeds for all 738
frozen adjacent ideal pairs in two independent representations. This does not
give Hall. Lean now proves the abstract failure directly: three identical
two-element transition intervals satisfy flexible uncrossing and every
two-family expansion test but admit no system of distinct representatives.
The first proposed boundary-energy invariant fails adversarial audit: its
canonical hole proxy and local envelope were not executable, linear
cardinality energy is invariant under meet/join, convex cardinality energy
moves in the wrong direction on incomparable ideals, and third-representative
collisions are uncontrolled. The replacement stable-ownership gate is exact
and positive. Among all 5,208 one-hole states of the frozen cap/rank-three
frontier, every one of the 1,596 blocked states has its hole at one of the two
singleton candidate families. Taking that singleton from its unique owner
moves the hole to a family of size 7, 9, or 10, which must be fillable because
only five ideals remain occupied. Independent implementations show termination
after at most one transfer and no directed cycles.

`StructuralChargingTransitionHallHoleDescent.lean` now proves the generic
completion lemma, the cardinality exit, preservation of membership and
injectivity under ownership transfer, and the implication from any
well-founded strict hole progress relation to an SDR and block Hall inequality.
The open structural target is no longer an unspecified energy: prove that an
arbitrary reflected frontier block either has a large-family hole or admits a
locally certified ownership/uncrossing move from a small family to a larger
one. The frozen candidate cardinalities are still computational evidence until
their structural analogue is proved in Lean.

The reviewed singleton-or-block-large theorem now compiles, but its uniform
profile gate fails. The four frozen family-size profiles are
`[10,7,1,1,9,10]`, `[6,6]`, `[10,9,6,6,3,6,8]`, and `[10,9,9,10]`; the
seven-span cup/rank-three group has four intermediate-size families. A targeted
78,236-state census then refutes the unchanged ascending boundary priority:
72 states reach 36 two-cycles. The first alternates the hole between `(3,7)`
and `(6,8)` by stealing ideal `0` back and forth.

The cycles do not obstruct a priority-free length-two augmenting certificate.
Across the four full frozen groups, all 4,888 blocked states have an occupied
hole candidate whose owner has a candidate unused by the original partial
representative system. The property remains true for all 5,977 blocked states
on all 62 nonempty consecutive subblocks. Cell-mask production and row-height
replay agree. Lean defines `HasTwoStepAugmentingExit` and proves constructively
that it gives an SDR and block Hall inequality.

The universal direct-or-two-step disjunction now has an exact compiling normal
form. `HasClosedSaturatedOwnerStar` says that every hole candidate is owned and
that every candidate of every actual reached owner is already used. Lean proves
that this is equivalent to being blocked with no two-step exit. It also proves
that a block-large canonical owner star forces an exit and that the stronger
state-free `FiniteCandidateFeasibleOwnerStarExpansion` profile forces the
canonical star to be block-large. This distinction is essential: an arbitrary
membership-feasible owner need not be the actual owner in a partial injection.
The reflected wrapper now separates the remaining obligations precisely:
feasible-owner-star expansion plus a one-hole state for every nonempty block
implies consecutive-block expansion. Reflection itself preserves candidate
nonemptiness, ruling out the empty-family obstruction.

Experiment 0041 independently reconstructs all 247 injective membership-
feasible owner maps across the 62 frozen consecutive blocks. Every resulting
owner-star union is block-large, with minimum slack `+1`. This is bounded
evidence for the stronger state-free profile, not a proof for arbitrary
reflected frontiers. Reflection normalization has now moved one algebraic edge
into Lean: rotate-complement reverses ideal inclusion, exchanges meet and join,
and preserves transition-interval membership after reflecting both endpoints.

The first boundary-slot route review produced two concrete descendants. The
stronger `FiniteCandidateFeasibleOwnerHasBlockLargeFamily` profile requires
every feasible owner map to reach one individual owner family as large as the
block. Lean proves that this profile implies feasible-owner-star expansion and
packages the implication for genuine reflected blocks. Experiment 0042
independently passes the stronger profile on all 247 frozen maps with minimum
slack `+1`, retaining the underlying endpoint lanes, boundary slots, and
reflection bits.

A zero-round Sol audit at clean revision `326dc21` returned
`partially_supported` and selected a deterministic nearest-owner, facing-lane
gap charge as the cheapest falsifier; Fable returned no answer because its
usage limit was exhausted, so no consensus is claimed. Experiment 0043 stops
that rule on the tight cap witness: after one left-lane charge, the second gap
faces a right lane equal to the singleton hole family `{3f}`. This refutes only
that deterministic rule. The active fallback is now the arbitrary genuine
block-large reached-owner profile. Its missing proof must use exact-rank
two-endpoint incidence rather than generic interval convexity. The separate
one-hole-state premise must still be constructed uniformly, normally by
induction over smaller consecutive blocks. Neither obligation may invoke Hall,
a completed SDR, or finite enumeration.

Experiment 0044 widens the bounded evidence to every decomposable `k = 6` root
through eight vertices. A matching threshold computes the exact minimum, over
feasible owner maps, of the maximum reached-owner family size. Independent
cell-mask and row-height implementations pass all 631,474 frontier groups and
all 3,792 nonvacuous holes with minimum slack `+1`. Lean now proves the matching
logic abstractly: block-large reached ownership is equivalent to the absence
of a feasible injective map into only block-small owners. In fact, every
nonvacuous bounded hole has a singleton deficient anchor chosen from its four
normalized endpoint extremes. Lean defines those extremes, proves they belong
to the reflected candidate family, and proves that the resulting forced-
extreme contract implies block-large reached ownership.

Experiment 0046 shows that this singleton strengthening is not the arbitrary
geometry lemma. Four nonvacuous frozen `k = 7` cup holes force no endpoint
extreme at all. In the first, anchor `{f,1f}` has one block-small neighbor and
therefore gives the required strict deficiency. Of the 29 nonvacuous frozen
holes, 26 have a singleton minimum anchor and three require two ideals; every
deficiency is one. Lean now packages the surviving exact target as
`AllocatedReflectedEndpointRankTransitionSmallOwnerDeficiency` and proves it
implies block-large reached ownership.

Experiments 0047 and 0048 sharpen the surviving target without restoring the
false singleton claim. The frozen exhaustive classification finds, for every
hole, some minimum deficient anchor that is a saturated lattice-chain interval
inside one normalized endpoint lane. The complete all-root `k = 7`, `n <= 8`
gate confirms the same property for the deterministically selected minimum
anchor in all 3,056 nonvacuous holes. Of these, 1,180 genuinely require a pair
of adjacent ideals. Lean proves that every inclusion-minimal deficient anchor
has deficiency exactly one and an unchanged neighborhood after deleting any
member; it also characterizes singleton and pair minima. The new
`AllocatedReflectedEndpointRankTransitionLaneChainMinimalDeficiency` contract
records the observed geometry and implies the active small-owner-deficiency
contract. The next theorem must construct this lane-chain anchor uniformly
from exact-rank reflected endpoint incidence. The one-hole-state induction is
still a separate downstream premise.

Experiment 0049 moves the bounded parameter to `k = 8` through eight
vertices. Independent implementations agree on 992,028 frontier groups and
2,096 nonvacuous holes. The block-large profile again passes, now with minimum
slack `+3`, but every minimum deficient anchor is a singleton. Thus the gate
supports the constructor while leaving the first genuinely longer chain
untested.

The scalable Lean reduction is now explicit. A
`FiniteCandidateLanePathCertificate` consists of `m + 1` ordered anchors,
`m` distinct small owners containing consecutive anchor pairs, and an
exhaustion of all small owners meeting the path. Lean proves, by injecting any
proper vertex subset into its incident path edges, that the full path is an
inclusion-minimal deficient anchor. Adding strict ideal order, exact Pascal-
interval image, and containment in one reflected endpoint lane supplies the
lane-chain contract. The open geometry lemma is no longer merely “find a
deficient subset”: it must construct this owner-labelled path from recursively
decomposable children, a genuine deep-below split, and the no-strong-`k`
hypothesis. Ranks one and two require separate base cases because the existing
active-ray normal form begins at rank three.

Experiment 0050 closes that mismatch only in the rank-at-least-three range.
The earlier anchor-shape statistics covered only 3,056 holes with a feasible
owner map, whereas the Lean path contract quantifies over every hole. Its
independent implementations searched 2,422,116 bounded `k = 7` holes and found
2,418,432 length-zero paths, 3,170 one-gap paths, and 514 two-gap paths, with an
exact singleton-neighborhood trace for each included hole. A post-audit found
that the shared group generator explicitly retained only `rank >= 3`; these
counts say nothing about rank two.

Lean now exposes that sharpened landing point. The local-neighborhood
constructor needs only distinct common owners on consecutive anchor gaps and
pointwise containment of every singleton small-owner neighborhood in the
listed owners. The exact-trace constructor specializes this to equality with
the incident path-edge owners. The reflected
`LaneSingletonNeighborhoodTraces` contract implies the existing path
contract, with no deficiency, Hall, or SDR premise. Separately, Lean proves
that every exact endpoint-span rank is at least two, so rank one has an empty
frontier and its path obligation is vacuous.

Experiment 0051 retires the former rank-two base target. A dedicated stopped
gate finds a genuine rank-two lane-path failure at support size five; a full
independent census through size eight finds 20,254 reflected-Hall failures and
2,896 direct violations of `choose (k - 2) 1`. Lean proves why: exact rank-two
frontiers are precisely adjacent changes in the split-membership word. An
explicit open decomposable seven-vertex context has six adjacent cap spans but
only five proposed Pascal slots, and Lean proves that no
`AllocatedExactRankSlotting` exists. The rank-at-least-three exact-trace route
remains a possible component, but the all-rank recurrence now requires a new
rank-two quotient/grouping or a globally coupled accounting invariant. The
next contract must be chosen and falsified at that architectural level before
more trace machinery is promoted.

The first such architectural proposal does not survive its minimal gate.
Charging each local rank-two adjacency at its unique lowest separating node
does assign every endpoint pair exactly once, but local adjacency need not be
global adjacency. Lean checks the interleaved three-vertex tree with root
split `{0,2}|{1}`: its root contributes `(0,1),(1,2)` and its lower child
contributes `(0,2)`, so local mass is three while `support.card - 1 = 2`.
The true injection into all unordered endpoint pairs is only quadratic, and
the seven-vertex alternating obstruction consists entirely of global gaps
anyway. Lowest-node ownership therefore remains infrastructure but is not the
replacement recurrence.

The next bounded gate finds a concrete cross-rank replacement direction.
Experiment 0052 matches every crossing transition after the first with the
hidden child gap created by the intervening opposite-child run. For caps it
promotes only hidden lower gaps; for cups it promotes only hidden upper gaps,
placing each at its exact ambient span rank. Independent implementations check
all 366,086 open decomposable `k = 7` roots through size eight and find no
capacity or endpoint-ideal matching failure among 1,913,894 adjusted groups.
Lean proves the binary run-count identity and both rank-at-least-three color
bridges. This changes the immediate target from inventing a quotient to
formalizing the new ambient-support carrier and its canonical matching. That
matching is now complete: for nonempty disjoint children, Lean constructs an
equivalence between all hidden child gaps plus one unit and all parent
crossing transitions.

There is a strict interface boundary: promoted gaps have both endpoints in
one child, so they are noncrossing at the parent and are not existing
`allocatedExactRankFrontier` members. Before any Hall result is reused, Lean
must prove a rank-ideal semantics theorem for these promoted spans. Before the
outer recurrence is claimed, a color-aware arithmetic theorem must show that
the adjusted carrier actually replaces the relevant published rank-two jump.

The reviewed interface package is now substantially complete.
`AmbientPromotedGap`
records the compatible hidden source, an exact rank at least three in the
parent support, and no false crossing field. Every source gap lifts to this
carrier. Its generalized endpoint-rank candidates and encoded Pascal-slot
candidates are compiling and nonempty without Hall or capacity. The canonical
bijection identifies hidden sources with all noninitial crossings and proves
the exact `hidden + 1 = crossing` cardinal identity on the explicit carriers.
For a fixed color, the residual rank-two carrier has cardinality equal to the
opposite-color hidden carrier plus one. Fixed-rank promoted sources combine
with the crossing frontier in `AdjustedHigherRankDemand`; exact promoted spans
place the same-color corner in both incident endpoint profiles, and adjusted
Hall expansion would imply the published Pascal capacity.

Experiment 0053 proves that this additive target is false. An explicit open
decomposable ten-point root has eleven cap/rank-three adjusted obligations
against ten slots. Lean proves the strict inequality, negates adjusted Hall,
and shows the slotting type is empty. Across both colors and all ranks the raw
adjusted total is 36 against 31 nonempty slots in the one untagged Pascal
window, so simple aggregation is not the replacement recurrence. The next
bounded gate was an exclusive-choice conservation model on this witness: a
hidden gap and its canonical transition became one charge with alternative
representations. It fails as well. The 27-charge endpoint-candidate graph has
maximum matching 20 and a 20-demand/13-neighbor Hall witness. Structural
slotting is demoted from the main route. The next route-selection review must
compare semantic proof reuse across colors and containments with a conserved
tree-global charge; no replacement theorem contract is active yet.

The first geometric refinement does not survive its frozen gate. Experiment
0045 shows that the tight cap owner has a seven-element family but maximum
single-lane cell spread plus one only `5 < 6`. The missing bridge must exploit
branching inside a Pascal lattice interval, the union of both endpoint lanes,
or a strict small-owner neighborhood deficiency. A proof based only on the
length of one lane interval is retired.

## External Lean baseline

Jineon Baek's `jcpaik/erdos-tuza-valtr` repository was inspected read-only at
commit `a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f` (retrieved 2026-08-01). It is
Apache-2.0 licensed and pins Lean `v4.13.0-rc3`, while this project pins Lean
and mathlib `v4.29.1`. After stabilizing the geometry bridge, D1 adapted and
substantially rewrote the upstream cup--cap recurrence proof structure for this
project's `Turn`, list-chain, realizability, and public convex-subset APIs. The
source file carries a modification notice; `NOTICE` records the pinned source,
and `LICENSE-APACHE-2.0` reproduces the upstream license.

`ErdosSzekeres/CupCap.lean` now proves the recurrence threshold
`choose (a+b) a + 1`, upgrades its consecutive chains to all-triples cups or
caps only for actual swept configurations, and transports monochromatic chains
through `IsStrongPolygonOn` to geometric convex subsets. Consequently the
public theorem `classical_binomial_upper` proves
`ForcesConvexPolygon n (choose (2*n-4) (n-2) + 1)` for every `n ≥ 3`.
`ErdosSzekeres/Extremal.lean` supplies the matching construction. It realizes
Pascal's recurrence by genuine planar deep compositions, proves exact
preservation of both component colorings, and establishes global crossing
bounds for cups and caps. The theorem `exact_cupCap` now packages the forcing
threshold and a planar configuration at the preceding cardinality avoiding
both requested chains.

`ErdosSzekeres/SmallCases.lean` proves `ErdosSzekeresFormulaAt 3` and
`ErdosSzekeresFormulaAt 4`. The four-point upper theorem is not obtained from
the much weaker binomial bound: it proves the one-change signotope law from
real orientation inequalities and checks the five overlapping four-tuples of
a five-point sweep. Explicit two- and four-point planar configurations supply
the first two sharpness halves. `ErdosSzekeres/ES5Certificate.lean` proves
`ErdosSzekeresFormulaAt 5`. Its upper half enumerates the 84 increasing triples
on nine vertices, imposes all 1,008 forbidden one-change assignments, and
forbids the eight strong patterns on each of the 126 five-subsets. Lean checks
the resulting 2,016-clause UNSAT claim from the committed LRAT trace, and a
generated semantic proof connects every clause to `TurnSequenceAllowed` or
`IsStrongPolygonOn`; the external SAT solver is therefore outside the trusted
base. The general lower theorem supplies the matching eight-point sharpness
witness.

`ErdosSzekeres/Composition.lean` provides the first construction-facing API. A
`HasDeepSplit` records the two mixed-triple rules of a left block placed deep
below a right block. Compiling lemmas show that a cup crossing the split cannot
use two right vertices, a cap cannot use two left vertices, and a strong
polygon crossing the split restricts to a cup on its left side and a cap on
its right side. The file also discharges the realizability obligation: finite
upper bounds choose horizontal and vertical translation parameters, the two
mixed orientation inequalities are proved algebraically, arbitrary-index
general position is recovered from ordered triples, and
`exists_deepComposition` returns an actual planar configuration. The selected
vertices on either side of a split are now enumerated as canonical initial and
final subchains, so component chain bounds transfer through composition. The
recursive family `exists_cupCapExtremal` has exactly `choose (p+q) p` planar
points and the claimed cap/cup bounds. For a strong polygon crossing one split,
the entire left part is now proved to be a cup, the entire right part a cap,
and their cardinalities are bounded by the corresponding component
invariants. The key local bookkeeping lemma also compiles: under two nested
left-associated splits, a strong polygon using vertices on both sides cannot
take two vertices from the intermediate block.

`ErdosSzekeres/Extremal.lean` packages the full construction as left-associated
Pascal-row prefixes. Prefix `t` has cup bound `t`, while every strong polygon
has at most `d+1` vertices. Appending block `t` follows from the binary crossing
theorem and that block's cap bound `d-t+1`. The full row has size `2^d` by
`Nat.sum_range_choose`, and `classical_lower_sharpness` transports the result
to `HasSharpnessExample n (2^(n-2)+1)` for every `n ≥ 3`.
