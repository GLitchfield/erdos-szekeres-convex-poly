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
coefficient. The next theorem is
`allocatedExactRankFrontier_card_le_spanPascalDemand` for arbitrary open
decomposable nodes. It must be proved in Lean before building the global
slot injection and the final `allocatedSpanPascalDemand_le_window` return to
the published child-slice induction.

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
