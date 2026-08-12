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

The first few-deletion proposal has now been decisively falsified in Lean.
`PrimeTwoDeletionCounterexample.lean` realizes a seven-point integer
configuration whose coloring is decomposition-prime and strong-six-free but
whose every one- or two-vertex deletion is non-prime. The exact replacement
interface is `TargetReflectingDecomposableNormalizationAt`: if a target-free
sweep-realizable coloring can be normalized on the same ground set to a
decomposable realizable coloring while reflecting any target back, the
decomposable exact theorem proves the unrestricted upper bound. A target-free
realizable single-triple mutation normalization is the surviving proposal for
constructing this interface. Its generic mutation-path consumer and one exact
geometric positive-control edge into the decomposable class now compile;
bounded connectivity remains computational evidence only.

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

The later entering-pivot correction now has a uniform cone bridge.
`StructuralChargingHigherCone.lean` proves that no parent `(a+1)`-cap makes
the complete hidden-lower pivot seed avoid an `a`-cap, with the color-dual
cup statement.  A nonempty seed inherits decomposability from its opposite
child, so a strictly smaller `DecomposableStateUpper a u k` hypothesis bounds
the seed by `decomposableThreshold a u k` and constructs an actual published
slice retaining every pivot.  This is the needed refinement over ordinary
cup--cap counting: at `(5,8,8)` the respective bounds are 28 and 22, while the
selected core has 23 vertices.

`StructuralChargingSaturatedPredecessor.lean` discharges the local
well-founded-shell obligation. The saturated-branch validity equations imply
strict selected-index descent and strict decrease of `a + u`. On each branch
they rewrite outer cap or cup avoidance into the exact successor hypothesis of
the higher cone and select a pivot-containing published core from only the
corresponding strict predecessor state. A combined theorem uses the unique
saturated branch and a single strong-induction hypothesis over `a + u`; it
never assumes the outer state. Core reselection preserves the deterministic
published index and cardinality, not core identity.

`StructuralChargingRootTransition.lean` sharpens the remaining obligation.
For every positive threshold, `DecomposableStateUpper a u k` is equivalent to
one root-local transition: if the two children of a deep decomposable split
already satisfy the outer threshold and the parent avoids the target cap, cup,
and strong polygon, then their union satisfies that threshold. Structural
induction lifts this transition without adding payments from different call
frames. Any larger root split also contains a restricted decomposable split of
exactly threshold plus one vertices with both children nonempty, so this exact
boundary loses no generality.

The saturated-predecessor dispatcher now returns a selected root core together
with both simultaneous pivot retention and the induced bound from root hidden
sources into that core. That count alone is insufficient: Lean checks that the
`(4,8,8)` boundary data `10+13=23`, an eight-source bound, and an eight-vertex
predecessor core satisfy every displayed scalar inequality. A new set-level
counterexample also gives a root hidden gap and a hidden gap in its nested
upper support with the same canonical entering pivot. It does not construct a
coloring or a `DecompositionTree`, but it refutes any direct inference from
fixed-split pivot injectivity to untagged injectivity over arbitrary nested
split data.

The root-local audit has now advanced beyond that scalar obstruction.
`StructuralChargingVisibleAdjacency.lean` and
`StructuralChargingResidualBudget.lean` prove that hidden-pivot payment is
equivalent to a visible-adjacency bound.  At the `10+13` boundary,
`StructuralChargingCentralCut488.lean` proves the opposite: the central cut
allows at most one hidden lower adjacency and forces at least eight visible
ones, so the three-vertex lower residual cannot be paid.  A valid two-extrema
reserve in `StructuralChargingCapExtremaReserve.lean` improves only to a
six-pivot bound and is also insufficient.

The same cut supplies the successful replacement.  It partitions the thirteen
upper vertices into two ordered cup blocks of sizes six and seven.
`StructuralChargingCupBlocks67Symbolic.lean` proves directly, from the
one-change law, that ordered `6+7` or `7+6` cup blocks force a four-cap, an
eight-cup, or a strong eight-set.  The proof uses consecutive-chain extension,
two explicit strong-eight configurations, and five terminal cup cases; it is
not an external SAT oracle.  Arbitrary-set transport yields
`upper.card ≤ 12` at every open `(4,8,8)` root with nonempty lower child, hence
rules out `10+13`.  At exact total size 23, Lean records the remaining oriented
window `11 ≤ lower.card` and `upper.card ≤ 12`.

`StructuralChargingResidualWindow488.lean` now eliminates the full window.
For upper sizes `8..12`, `2..7`, and `1`, ordinary cup--cap thresholds provide
crossing cup/cap pairs `(5,3)`, `(6,2)`, and `(7,1)`.  Each pair has total size
eight and therefore glues across the root to a forbidden strong eight-set.
The resulting `criticalRootImpossible_488` and
`decomposableStateUpper_488` theorems are unconditional; they do not assume
the strict predecessor pool, sweep realizability, or color duality.  An
independent frozen-file review reproduced the proof gate and axiom audit.

The next transition obligation remains root-local but advances one level in
the fixed-`k=8` predecessor order.  The `(5,8,8)` higher-cone consumer needs
the sum-twelve predecessor layer; `(5,7,8)`, threshold 41, is the smallest new
structural state.  Exact index arithmetic closes lower-child sizes `11..40`.
It leaves two oriented tails: lower sizes `1..10` with upper sizes `41..32`,
and the extreme `41+1` split.  These are not color-dual within the same state.
Restricting the first family to one lower and thirty-two upper vertices gives
the first bounded structural gate. Lean further splits those upper vertices
into two four-cap-free sweep sides of sizes `11..21`, each containing a
five-cup. The constant-size `5+q+5` conclusion is nevertheless false:
`StructuralChargingNextState578Counterexample.lean` proves a recursively
decomposable 11-vertex counterexample. The next lower-tail statement must keep
the unused side reservoirs and their recursive ownership rather than only two
selected cups. The first such statement now compiles: `(4,8,8)` makes every
23-vertex upper restriction contain a four-cap; all upper four-caps straddle
the root, and three can be selected disjointly. A 13-vertex SAT model shows
that the selected triple alone is insufficient, so the open step is a
density-plus-tree-ownership theorem. The nine-transversal shortcut is now
proved equivalent to the full singleton-lower gate. Threshold-frontier
extraction compiles, but an exact Lean `32/23` decomposable common-cut model
refutes avoidance-free strict span descent; the model contains a seven-cup and
therefore is not an open-state counterexample. The surviving reduction selects
a terminal cap. Its open span is four-cap-free and seven-cup-free, hence has
cardinality at most 21; after removing the cap endpoints at least nine outer
tail vertices remain, all in the two endpoint bridge classes. The cap's unique
lowest separating node has child profile `1+3` with no lower five-cup or
`2+2` with no lower six-cup. The strict `(5,5,8)` predecessor bounds the first
lower child by 20. In the second branch, Lean proves the sorted cap word is
lower--upper--upper--lower and hence that internal endpoint bridges are forced
by the split law. The exact five-internal-tail force statement is false by a
kernel-checked nine-vertex recursive counterexample. The repaired invariant
partitions the nine tails: five remain internal, or five are external and each
has a concrete first-exit tree address with the cap in the lower child and the
tail in the upper child.

The one permitted whole-cap trace layer is now resolved. Lean defines the
shallowest set escape along a terminal path and proves that a false-directed
first escape of a four-cap puts its two sweep-middle vertices in one
lower-sibling bucket. Hence every private cap with a later false-exiting owner
either first peels at a true step or has a two-vertex bucket collision. The
actual state-578 package supplies three owners with this residual. A separate
eight-vertex recursively decomposable Lean construction is terminal and
target-free, realizes the true-peel/later-false-owner branch, and has no bucket
collision. Independent single-cap tracing is therefore formally expired as a
closure route. The density-only reserve proves that every set of at most five
vertices misses some residual cap, but does not control overlap among the six
chosen private caps. Following the recorded fallback order, the active branch
is now the `41+1` extreme. It reduces by restriction and color duality to an
exact 32-vertex singleton-lower `(7,5,8)` gate; every decomposable 23-subset of
that reservoir contains a four-cup. Conditional on the strict `(4,5,8)`
predecessor, Lean now turns this into three disjoint four-cups and three
further disjoint four-caps. Pairwise lowest joint splits, dual endpoint laws,
and a six-witness common-split defense compile, but a target-free reverse
separation counterexample expires address equality as a closure mechanism.
Regenerating a cap inside the 12 cup vertices gives the exact next residual:
the cap misses one cup or has intersection profile `2+1+1`. A target-free
signotope realizes the latter without being recursively decomposable, while a
bounded 50,000-tree decomposable sample found no witness. The next missing
bridge must therefore use recursive decomposability essentially to eliminate
both regeneration branches or derive a named child-capacity violation.

A bounded goal-driven lemma-forge preflight runs separately from that main
route.  It rejected four-point localization as already compiled, parked
insertion-signature and universal binary-fingerprint proposals after their
consumer audits, and retained only planar rooted-triangle circuit elimination
for a sharper statement and minimal-counterexample consumer.  This is proposal
evidence only; no circuit-elimination result is yet claimed.

The complete blocker-family matrix now has its first genuinely color-sensitive
consumer. `StructuralChargingNextState578BlockerConsumer.lean` proves that
opposite strict extensions from the common minimum put a four-cup below and a
four-cap above the same deep split, hence force a strong eight-set. The mixed
rectangle is eliminated, leaving one-sided `24+8` localization or a universal
minimum column. Exact-small decomposable models refute the projected versions
of both remaining consumers but do not retain the full 32-vertex
private-star/density package. This is Outcome 2; state `(5,7,8)` remains open.

A route-level audit confirms that state 578 is a conditional fixed-`k=8`
milestone, not a uniform E3 theorem. Seven symmetry-unique active `k=8` states
remain after it, and uniform E3 would still only reduce the unrestricted
conjecture to the indecomposable Layer-F obstruction. The new generic module
`DecomposableStateDuality.lean` kernel-checks symmetry of the threshold,
hereditary state, root transition, and critical-root obstruction, removing
duplicated off-diagonal obligations without claiming a new state. A bounded
endpoint-indexed predecessor-fiber shelling is retained only as a proposed
direct-diagonal falsification experiment; it is not selected as the main
route before its specification and noncircularity gates pass.

## 2026-08-10 geometric-tail and independent-route outcomes

The geometric Pascal interface now compiles. Exact retained-child tail gates
feed the generic critical-root reducer, and one ordered predicate,
`PascalTailTwoSideBound`, supplies the singleton lower gate and its color dual.
The first three positive controls `(4,5,5)`, `(4,6,6)`, and `(4,8,8)` close
without finite certificates. The first open uniform instance is `(5,6,7)`:
Lean proves it equivalent to the existing `TwoCapFreeSidesBound567`. Thus the
uniform route has an exact earlier obstruction, rather than state 578 being
its first truth test.

The independent Layer-F rooted-circuit lead is stopped. A kernel-checked
seven-point rational configuration refutes the first strengthening with a
plausible deletion-chain consumer: two rooted triangles cannot in general be
eliminated while preserving both untouched anchors. One-anchor convex-hull
substitution remains plausible but has no bounded-fiber recurrence consumer.

The fixed state-578 branch obtains Outcome 2. Four singleton-owned deletion
rows and the six-column one-sided matrix force one entire row to remain at the
common-minimum address. That four-cup misses two distinct foreign cap blocks.
The resulting plateau/two-foreign-cap theorem compiles, but address-only
models show that another color-sensitive consumer is still required. Ticket
0010 owns that continuation; `DecomposableStateUpper 5 7 8` remains open.

The next state-578 global audit does not obtain another ticket outcome, but it
isolates a terminal consumer. A cover of the complete residual four-cup family
by one at-most-seven carrier per full spine would combine local
three-boundaries into the forbidden global density boundary. Conversely,
Lean proves that every single residual seed has an escaping cup outside its
seven-carrier and that carrier replacement cannot be monotone inclusion
growth. The missing theorem is therefore global and color-sensitive: it must
cover or rank the complete residual family, not choose another selected row.

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

## 2026-08-10 route integration: certificates, Layer F, and state 578

The first new diagonal certificate target is now complete. Both normalized
`k=9` dense CNFs kernel-check directly after dependency trimming, generated
Lean proofs derive every retained clause from the exact cup-block hypotheses,
and order-embedding transport from `Fin 15` to arbitrary `7+8` and `8+7`
blocks proves `diagonalCupBlocksForce4kk_nine`. The much larger state-567 cut-7
proof can be checkpointed, but its semantic bridge is harder and it closes
only one cut; it remains second priority. The diagonal route now needs a
uniform successor consumer rather than another proof of the `k=9` base.

Layer F now has a corrected load-bearing API. The original unthresholded
normalization contracts are false because of `Fin 0`; their exact-threshold
versions compile. A one-to-three mutation rank decrease implies target-free
normalization by well-founded induction and hence promotes the decomposable
exact upper theorem. `PrimeCoreCount` is a concrete noncircular candidate,
with zero proved equivalent to decomposability on nonempty ground sets.
Support congruence now proves that a single mutation changes prime-core status
only on supports containing its three vertices, and exact rank accounting
compiles in every cardinality stratum. The primary candidate is the
highest-cardinality-first `StratifiedPrimeCoreRank`; its zero law compiles and
bounded mutation censuses pass its first falsification gates. No general
decrease theorem is claimed. The next hard target is a three-step
highest-stratum decrease above threshold or a realizable target-free closed
component that refutes it.

A separate unrestricted bridge now has a compiling exact recurrence.
`StrongPredecessorBicoloringAt k` partitions a strong-`k`-free realizable
coloring into two strong-`(k-1)`-free classes; together with the predecessor
upper theorem this bounds each class by `2^(k-3)` and their union by
`2^(k-2)`. The `k=3` base and recurrence consumer compile. Independent
abstract encodings pass the balanced eight-vertex `k=5` gate, while the
unbounded bicoloring theorem remains open.

The current state-578 route is suspended. The terminal seven-carrier-cover and
seed-escape interfaces remain available, but seed selection, carrier size, and
address depth all admit explicit cycles at the evidence levels recorded in
Experiment 0094. Reopen only for a complete-residual-family theorem using the
exact 32-point coloring laws essentially and producing the cover, a strict
predecessor, or a genuine descent. This suspension is not a proof or
refutation of state `(5,7,8)`.

## 2026-08-11 parallel-route integration

The predecessor route now exposes the weakest presently known sufficient
contract. `PredecessorHalfSubsetAt k` asks only for one
strong-`(k-1)`-free support containing at least half the vertices. Lean proves
the hierarchy

```text
StrongPredecessorBicoloringAt k
  -> FractionalPredecessorCoverAt k
  -> PredecessorHalfSubsetAt k
  -> (SweepExactUpperAt (k-1) -> SweepExactUpperAt k).
```

The direct bicoloring and fractional recurrence consumers remain as
independent proofs. A local four-index lemma also gives a uniform finite base:
for `k>=5`, every strong-`k`-free coloring on at most `2*k-3` vertices has an
integral predecessor bicoloring. This theorem does not use realizability. At
`k=6` it proves the range through nine vertices; independent exact CNF/LRAT
checks find no integral/fractional/half separator through 11, but the last two
sizes remain computational evidence.

The maximum-support one-hole exchange proposed as a producer is stopped. With
a disjoint predecessor polygon, deleting at most two support vertices while
inserting the other three polygon vertices strictly enlarges the support, so
success would contradict maximum cardinality. An independently checked
integer-coordinate eight-point configuration proves the premise is
nonvacuous at the computational-evidence level. The predecessor hierarchy
therefore remains a live proof architecture, but its next producer must not be
this monotone maximum-support exchange.

The state-567 branch also advanced without closing. The full-premise
mutually-middle-obstructed pair is now a compiling interface for the packed
internal obligation. Exact cardinality and a second use of deletion packing
give a ten-point residual plus a universal four-residual escape family. A
compiling trichotomy separates escapes meeting zero, one, or two carriers.
Those three occupancy impossibilities and the five balanced terminal classes
are the remaining structural leaves. Pair-only contradictions are rejected by
the exact 12-point control.

The `k=9` extreme-exchange mathematical extraction remains computationally
supported, but two proposed Lean conjunction-projection architectures each
exceeded the ten-minute single-clause gate below the memory ceiling. Further
work must split the 120 middle-color consequences and final finite cases into
smaller semantic modules; more projection variants are not an active repair.

## 2026-08-11 fourteen-thread forward plan

This section is the detailed execution memory for the fourteen-thread
portfolio in the Wayfinder map.  Threads 1--6 are the initial execution front;
7--14 are staged reserve, revival, discovery, and research-system tracks.  The
plans are intentionally branched: a failed candidate is
supposed to return a precise counterexample or expiry decision instead of
turning into an unbounded repair loop.  Computational evidence is never a
completed result; every promoted mathematical milestone below is a named Lean
theorem passing the repository proof gate without `sorry`, `admit`, unsafe
axioms, or an unverified oracle.

### Thread 1: predecessor half-subset producer

**Destination.**  Prove `PredecessorHalfSubsetAt k` for every relevant `k`.
Together with the already compiling predecessor recurrence and the `k=3`
base, this supplies the unrestricted exact upper bound without requiring every
realizable coloring to be recursively decomposable.

**Stage 1.1: separate the three producer strengths at the first new boundary.**

- Freeze exact `k=6`, `n=12` contracts for integral predecessor bicoloring,
  fractional predecessor cover of total weight at most two, and one
  predecessor-free support of at least half the vertices.
- Search the abstract rank-three/signotope model first under the default
  bounded-computation policy.  Classify a model into the first applicable
  outcome: integral, fractional-only, half-only, or half failure.
- Any failure must be independently checked.  Before it refutes the geometric
  theorem, obtain an exact rational/integer realization or a proved bridge to
  one.  An abstract-only model is a relaxed-model falsifier, not a planar
  counterexample.
- If half fails in an exact realizable model, expire this whole route and
  Lean-certify the smallest counterexample.  If only integral or fractional
  strength fails, demote that stronger producer and continue with the weakest
  surviving contract.  If all three survive, treat the result only as bounded
  evidence and proceed structurally.

**Stage 1.2: maximum-support witness infrastructure without circular size
assumptions.**

- For a maximum-cardinality strong-`(k-1)`-free support `S`, prove the cheap
  exterior-anchor lemma: every `v ∉ S` participates in a strong
  `(k-1)`-witness `insert v A` with `A ⊆ S` and `A.card = k-2`.
- Define the exterior-to-support eligibility relation from orientation or
  middle-incidence data.  The definition must not contain injectivity, Hall's
  condition, or the desired half-cardinality inequality.
- Test the relation on the exact rational one-hole-exchange counterexample and
  on the `k=6` boundary catalog.  The stopped exchange `(S \ D) ∪ (P \ {p})`
  with `|D| ≤ 2` is forbidden as a proposed repair: its successful conclusion
  contradicts maximum cardinality for formal cardinal reasons.
- Prove either a Hall-neighborhood inequality for all exterior subsets, an
  injective charge as a consequence of a separately stated collision lemma,
  or an exact fractional dual inequality.  Compiling an interface that simply
  assumes an injection is bookkeeping, not mathematical progress.

**Stage 1.3: producer and recurrence.**

- Package the surviving charge/dual theorem into
  `PredecessorHalfSubsetAt k`.
- Compose it with `sweepExactUpperAt_of_predecessorHalfSubset`, then prove the
  all-`k` upper result by induction from the compiling base.
- Transport through the existing swept-configuration/convex-position bridge
  and combine with `classical_lower_sharpness` to obtain the exact formula.

**Expiry rule.**  After two independently motivated eligibility or charging
relations either inherit the exact rational controls or fail without exposing
a new orientation-sensitive collision law, run a route review before proposing
a third.  Do not weaken the destination by silently assuming the desired
cardinality bound.

### Thread 2: state-567 ten-residual occupancy leaves

**Destination.**  Prove
`PackedInternalMutuallyMiddleObstructedPairImpossibleAtTwentyTwo567`, hence the
packed-internal state-567 obligation, while visibly using exact total 22,
internality, and repeated global deletion packing.

**Stage 2.1: normalize every escape to concrete set data.**

- Add a small unpacking theorem for `PackedInternalPairFourResidualEscape`:
  for each carrier vertices `a,b` and each four-set `block` in the ten-point
  residual, choose a concrete strong six `third` contained in the prescribed
  deletion and record its carrier intersections.
- Compile generic finite-set lemmas for the residual cardinalities.  In the
  residual-only case, prove that `third` equals the six vertices of
  `residual \ block`; this is the sharp place where total 22 is spent.
- Run the fixed 12- and 21-point controls against every proposed branch
  antecedent.  A proof kernel inherited by either control is rejected before
  deeper Lean work.

**Stage 2.2: residual-only branch.**

- Probe at least two distinct residual four-blocks rather than selecting one
  arbitrary third witness.  Translate the resulting complement sixes into
  overlapping strong-six constraints.
- Use internality of the first carrier and the appropriate side's cap-four
  exclusion to convert those overlap constraints into a forbidden ambient
  cap, cup, or strong seven-set.
- If a full-premise exact model survives, record and Lean-certify it and stop
  this branch.  Otherwise freeze the smallest surviving contradiction theorem
  and compile it.

**Stage 2.3: one-carrier branch.**

- Split by which carrier is met and normalize the intersection cardinality and
  sweep-middle profile.  Use reversal/color duality only through a compiling
  transport theorem.
- Compare two or more universal escape probes so that global packing is used
  beyond construction of the original pair.  Apply the twelve directed middle
  failures and the internal side cap-four exclusion at the first common
  profile.
- Promote the terminal contradiction only after it fails the relaxed and
  sharp-control models.

**Stage 2.4: two-carrier branch and assembly.**

- Use the six vertices of `third`, its intersections with both disjoint
  carriers, and the ten residual vertices to enumerate the feasible occupancy
  profiles without brute-force enumeration of ambient colorings.
- Seek a pigeonhole profile forcing one of the recorded middle failures or an
  ambient strong seven.  Any residual finite classification must expose a
  small, reviewable signature and a certificate bridge if computation is used.
- Combine the three compiled occupancy leaves with the existing trichotomy,
  then invoke the existing explicit-pair consumer to close the packed-internal
  obligation.

**Expiry rule.**  Pair-only contradiction lemmas are permanently stopped.  A
valid continuation must compare multiple universal escape probes or derive a
genuinely universal consequence of all 210 residual four-blocks.

### Thread 3: uniform Pascal-tail lift

**Destination.**  Turn the state-567 structural mechanism into a parameterized
theorem strong enough to prove `PascalTailTwoSideBound a u k`, then feed the
existing critical-root reducers and the decomposable induction.

**Stage 3.1: extract the parameterized kernel.**

- Audit every use of the state-567 constants: side total 22, two carrier sizes
  six, residual size ten, and four-vertex deletion blocks.  Rewrite each as a
  binomial/Pascal expression or mark it explicitly as special to `(5,6,7)`.
- Define a generic two-carrier residual-escape structure indexed by `a,u,k`,
  with cardinalities and avoidance predicates separated from the terminal
  color argument.
- Generalize the finite-set residual cardinality and the zero/one/two-carrier
  occupancy trichotomy first.  These are reusable regardless of whether the
  terminal color lemma generalizes.

**Stage 3.2: prove one genuinely uniform leaf.**

- Select the state-567 occupancy leaf whose contradiction uses the fewest
  special equalities.  State a parameterized inequality contract and verify
  that its `(5,6,7)` specialization proves the concrete leaf rather than
  assuming it.
- Test the statement at the immediately adjacent feasible Pascal states and
  their color duals.  A bounded countermodel narrows the parameter range; it
  must not be patched with a conclusion equivalent to the desired recurrence.
- Compile the parameterized leaf and its specialization before attempting all
  occupancy classes.

**Stage 3.3: lift through the existing recurrence interfaces.**

- Generalize the remaining occupancy/balanced leaves that survive Stage 3.2.
- Prove `PascalTailTwoSideBound a u k` over the largest honest parameter range.
- Use `singletonLowerPascalTailGate_of_twoSideBound` and the generic critical
  root reducers to discharge the corresponding decomposition-tree states.
- Prove the uniform `DecomposableStateUpper`/`DecomposableExactUpperAt`
  induction and combine it with either Thread 1 or a completed Layer-F bridge
  for the unrestricted upper theorem.

**Expiry rule.**  If a state-567 terminal proof depends essentially on an
equality with no stable adjacent-state analogue, retain it as a finite theorem.
Do not name a one-state wrapper “uniform”; return to a different Pascal-tail
invariant.

### Thread 4: Layer-F highest-stratum mutation descent

**Destination.**  Prove or refute the frozen three-step target-free realizable
drop in `StratifiedPrimeCoreRank`.  A proof supplies well-founded normalization
to recursively decomposable colorings; a counterexample prevents further work
on a false unrestricted bridge.

**Stage 4.1: decisive realizable falsification.**

- Freeze `ThreeStepTopPrimeStratumDropsAboveAt` with the exact threshold,
  target-free intermediate states, realizability at every endpoint, and no
  monotonicity requirement on intermediate ranks.
- Extend the bounded exact-rational mutation graph controls only within a
  predeclared limit.  Search specifically for a target-free closed component
  or a vertex with no three-step decrease in its highest affected positive
  stratum.
- An abstract signotope obstruction remains diagnostic until rationally
  realized.  A below-threshold obstruction cannot refute the threshold
  consumer unless the theorem quantifies there.

**Stage 4.2: local mutation accounting.**

- Use the compiling locality theorem to characterize all prime supports whose
  status can change under one flipped triple.
- Prove structural inequalities comparing created and destroyed supports at
  the highest changed stratum.  Permit temporary lower-stratum increases and
  rank plateaus because exact seven-point controls require three-step macros.
- Seek a geometric circuit-flip choice rule that forces the endpoint loss and
  preserves target avoidance along a path of length at most three.

**Stage 4.3: normalization consumer.**

- Compile the three-step drop theorem, apply the existing well-founded
  consumer, and obtain target-free normalization above the exact threshold.
- Once Thread 3 supplies the uniform decomposable upper theorem, compose the
  two and transport to the planar statement.

**Expiry rule.**  A rationally realizable target-free closed component or
highest-stratum local minimum satisfying the theorem's threshold closes this
candidate.  Layer F remains a sidecar until the decomposable theorem is
uniform; it must not consume all capacity merely because it is conceptually
general.

### Thread 5: state-567 balanced five-class branch

**Destination.**  Prove `PackedElevenElevenForcesInternalStrongSix567`, the
balanced companion to Thread 2.

**Stage 5.1: compile the exhaustive shell.**

- Freeze the common `11+11` context once: ordered disjoint sides, side cap-four
  exclusions, `OneChangeOn`, ambient `(5,6,7)` target avoidance, and global
  deletion packing.
- Prove the mechanical five-way exhaustion from the existing packing/residue
  infrastructure: crossing `2+4`, `3+3`, or `4+2`, otherwise three residues
  with pair overlap in the left-right or right-left orientation.
- Keep the five terminal contradiction Props separate so each can be tested
  and compiled independently.

**Stage 5.2: terminal classes.**

- Attack `2+4` first and derive `4+2` only through a verified reversal/color
  dual bridge; otherwise prove both orientations separately.
- Treat `3+3` as its own central class.  Exact small controls already show
  that generic crossing `3+3` pairs do not force a target, so the proof must
  spend exact `11+11` capacity or repeated packing.
- Attack the two residue-overlap classes as a dual pair.  Compare all three
  residues, not one selected pair, and make the pair-overlap pigeonhole step
  explicit.
- Before Lean promotion, falsify each terminal signature against the 12- and
  21-point controls and any exact balanced controls already recorded.

**Stage 5.3: state-567 closure.**

- Assemble the five terminal lemmas into
  `PackedElevenElevenForcesInternalStrongSix567`.
- Combine this with Thread 2's packed-internal theorem through the existing
  exact reducer to prove `TwoCapFreeSidesBound567` and then the `(5,6,7)`
  Pascal-tail gate.

**Expiry rule.**  Reject any terminal contradiction whose proof does not use
exact balanced size, side cap exclusions, or repeated packing.  Such a theorem
is inherited by known exact-small controls.

### Thread 6: finite `k=9` extreme-exchange Lean bridge

**Destination.**  Kernel-check both normalized 17-vertex extreme-exchange
extraction formulas while preserving the frozen CNF/LRAT and semantic theorem
contracts, then use the finite proof to identify a uniform successor lemma.

**Stage 6.1: bounded semantic engineering.**

- Keep all variable maps, CNF clauses, LRAT traces, and final theorem
  signatures byte-stable.  Regeneration must recheck their recorded hashes.
- Replace the timed-out clause-local proof with three layers: small modules of
  middle-color equalities, a reusable strong-ten pattern reconstruction, and a
  final finite contradiction.  Group middle facts conservatively (initially
  8--16 per module) so each file has a short independent gate.
- First compile the smallest 9+8 clause under a ten-minute, single-job,
  16-GiB cap.  If it succeeds, compile a noncontiguous clause and then all
  seven.  If one small middle-fact module itself exceeds the cap, profile that
  exact module and redesign once; do not return to direct or depth-four
  conjunction projection.
- Assemble the semantic chunks, normalized 8+9 and 9+8 theorems, and final
  extraction theorem.  Run the forbidden-token and axiom audits plus targeted
  and repository proof gates before integration.

**Stage 6.2: mathematical extraction.**

- Classify which semantic clause families actually occur in the compact
  certificate.  Translate the recurring pattern into an extreme-core
  extraction statement that does not assume `DiagonalCupBlocksForce4kk
  (k+1)` or an equivalent ambient conclusion.
- Combine the extracted opposite extreme cup extensions with the compiling
  `OneChange` cup-gluing lemma.
- Test the proposed successor statement at the next finite quotient before
  formalizing an all-`k` induction.  SAT refutes the proposal; UNSAT is only
  bounded support until certified and semantically bridged.
- If the successor compiles, combine it with the existing diagonal base and
  Thread 3's Pascal-tail interfaces.

**Expiry rule.**  Once the exact `k=9` extraction compiles, stop adding isolated
finite cases.  Continued certificate work is justified only by a named
uniform consumer.  Two projection architectures have already failed their
bounded elaboration gates and are not eligible for another retry.

### Thread 7: integral predecessor Property-B producer

**Destination.**  Prove `StrongPredecessorBicoloringAt k`, the strongest
currently formalized predecessor producer.  Its two color classes then feed
the compiling exact recurrence directly.

**Stage 7.1: finish or deliberately park the finite semantic control.**

- Preserve the exact Fin-8 Property-B CNF and certificate semantics.  The
  bare LRAT contradiction, encoding layer, and at least one semantic chunk
  compile; the monolithic generated final bridge does not have a verified
  bounded build.
- Try one bounded checkpointed semantic architecture that partitions by clause
  origin: signotope constraints, strong-five definitions/avoidance, and the
  balanced two-color obstruction.  Each chunk must compile independently and
  the final theorem must use only those checked chunks.
- Do not repeat dense-core minimization: removing 16 of 1,211 clauses enlarged
  the fresh certificate and did not address elaboration.  If checkpointing
  still exceeds the declared cap, park the finite promotion and retain the
  independently replayed computational evidence.

**Stage 7.2: expose structural hypergraph properties.**

- For a strong-`k`-free realizable coloring, define the hypergraph of strong
  `(k-1)` subsets.  Prove its hereditary, deletion, and local four-index
  consequences without assuming a bicoloring.
- Identify a property stronger than arbitrary hypergraph Property B but forced
  by rank-three orientation structure: candidate forms include an ordered
  interval property, bounded edge-intersection pattern, or a signed circuit
  constraint.
- Falsify each candidate against exact rational controls and the equality
  construction before using it in a coloring theorem.

**Stage 7.3: all-`k` bicoloring.**

- Prove that the structural property admits a two-coloring splitting every
  predecessor edge, or reduce it to a separately proved ordered-hypergraph
  theorem.
- Package the coloring as `StrongPredecessorBicoloringAt k` and use its
  compiling recurrence consumer.

**Expiry rule.**  Integral Property B is stronger than needed.  If Thread 1
or 8 proves the half/fractional producer first, demote this route to a useful
structural corollary.  A realizable non-bicolorable predecessor hypergraph
stops it without affecting those weaker routes.

### Thread 8: fractional predecessor-cover producer

**Destination.**  Prove `FractionalPredecessorCoverAt k`.  The exact rational
double-counting recurrence and the implication to `PredecessorHalfSubsetAt k`
already compile, so this route can succeed even if integral Property B fails.

**Stage 8.1: freeze primal and dual formulations.**

- State the finite rational LP exactly: nonnegative weights on
  strong-`(k-1)`-free supports, pointwise coverage at least one, total weight at
  most two.
- Prove a finite rational duality bridge in the needed form, or use a
  certificate-bearing finite LP theorem already trusted by mathlib.  External
  optimization output may suggest weights but cannot close the Lean theorem.
- Derive the dual target: every nonnegative vertex weighting has a
  predecessor-free support carrying at least half the total mass.

**Stage 8.2: weighted geometric charging.**

- Test weighted maximum-support, random-cut, sweep-interval, and deletion
  averaging arguments.  The proof must use rank-three/realizability structure;
  relaxed hypergraphs have exact fractional-versus-integral separators.
- Start at `k=6` and use the integral-through-11 computation as a positive
  control, not as a proof.  Search `n=12` for the first exact fractional/half
  separator as part of Thread 1's common bounded gate.
- When a weighted inequality survives, compile it first as a finite-sum lemma
  for an arbitrary rational weight function, then derive the cover.

**Stage 8.3: recurrence and comparison.**

- Produce `FractionalPredecessorCoverAt k`, invoke the compiling direct
  fractional recurrence, and compare its hypotheses with Thread 1's half
  producer.  Retain whichever statement has the simpler all-`k` proof.

**Expiry rule.**  An exact realizable model with fractional cover number
greater than two stops the route and also refutes the half producer only if its
maximum predecessor-free support has size less than half.  Keep those two
conclusions separate.

### Thread 9: diagonal extreme-exchange successor

**Destination.**  Prove a noncircular successor from the diagonal cup-block
theorem at `k` to the theorem at `k+1`, using extreme exchange rather than the
stopped all-double-deletions gluing statement.

**Stage 9.1: exact extraction contract.**

- Retain two ordered cup blocks of sizes `(k-1)+k` and choose the far extreme
  `q` and the opposite `k-1` core.
- Under no four-cap and no strong `(k+1)`, conclude that some vertex of the
  smaller block extends that core to a cup.  Do not assume absence of a
  `(k+1)`-cup if that would make the extraction equivalent to the desired next
  diagonal theorem.
- Verify noncircularity formally by showing the theorem's premises are supplied
  by `DiagonalCupBlocksForce4kk k` on genuine deletions, while its conclusion
  is strictly local.

**Stage 9.2: finite gate and Lean promotion.**

- Thread 6 supplies the `k=9` finite truth test.  After its semantic bridge
  compiles, inspect which local configurations close both orientations.
- State the smallest symbolic exchange lemma explaining those configurations,
  falsify it at `k=10` under a bounded quotient, and compile it if it survives.
- Combine opposite-core extensions through the existing `OneChange` cup
  gluing theorem.

**Stage 9.3: successor induction.**

- Prove the successor theorem for all `k` in its honest parameter range, then
  derive the diagonal family from the compiling bases.
- Feed the diagonal theorem into the Pascal-tail/critical-root machinery and
  record exactly which off-diagonal leaves remain.

**Expiry rule.**  The prior gluing statement `G(k)` with every double deletion
is equivalent, under `D(k)`, to `D(k+1)` and is permanently stopped.  Any new
contract that recreates this equivalence before doing local extraction is
rejected as circular.

### Thread 10: state-567 finite-certificate fallback

**Destination.**  Kernel-check one exact state-567 packed obligation as a
bounded fallback and as a source of structural proof patterns, without
mistaking one finite state for the uniform theorem.

**Stage 10.1: select the smallest semantic leaf.**

- Compare the existing cut-7 trace, the five balanced terminal classes, and
  the three residual occupancy branches by variable count, semantic-clause
  complexity, and downstream leverage.
- Freeze exactly one leaf whose conclusion plugs into a compiling reducer.
  Keep the full semantic hypotheses; do not certify a weakened CNF with no
  proved transport back to Lean.

**Stage 10.2: deterministic certificate pipeline.**

- Generate a bounded CNF, solver certificate, independent replay, corrupted
  controls, and semantic clause map.  The source-to-clause bridge is part of
  the deliverable.
- If the monolithic LRAT import exceeds memory, checkpoint additions while
  recording exact live-clause interfaces.  Each checkpoint theorem must be
  small enough for the standard proof gate.
- Compile the leaf, then the existing state-567 consumer.  Record standard
  axioms and scan for forbidden placeholders.

**Stage 10.3: mine rather than proliferate.**

- Group retained clauses by mathematical origin and extract the smallest
  repeated witness pattern.  Offer that pattern to Threads 2, 3, and 5 as a
  symbolic lemma candidate.
- Do not launch certificates for the remaining cuts unless the first one
  either closes the full state or reveals a reusable uniform consumer.

**Expiry rule.**  A certificate with no semantic bridge is computational
evidence only.  Once one exact leaf compiles, priority returns to structural
uniformization.

### Thread 11: inverse stepping-up/decomposition extraction

**Destination.**  Find a noncircular inverse to the lower-bound composition:
a target-free configuration above the critical size should expose smaller
predecessor-free pieces, a half-size predecessor-free support, or a usable
deep split.

**Stage 11.1: formulate exact alternatives.**

- Study the equality construction under sweep order and identify the
  partitions, extreme vertices, or deletion chains that witness its recursive
  structure.
- Freeze three distinct candidates: a near-halving two-piece partition, a
  single half-size predecessor-free subset, and a deletion step lowering the
  target parameter.  State each in the weakest model where the intended
  consumer is valid.
- Prove that none of the candidates merely restates `SweepExactUpperAt k` or
  smuggles in the critical cardinal bound.

**Stage 11.2: decisive small gates.**

- Test the candidates on exact small realizable catalogs and on the known
  recursively decomposable equality family.  Require a rational realization
  for negative geometric claims.
- For a survivor, identify the orientation/circuit mechanism producing the
  split or deletion and compile the local lemma before the global cardinal
  theorem.

**Stage 11.3: connect to live consumers.**

- A half-subset conclusion feeds Thread 1; a two-piece conclusion feeds the
  bicoloring/fractional routes; a deep split feeds Thread 3; a mutation/deletion
  normalization feeds Thread 4.
- Promote only a candidate with one of these exact compiled consumers.

**Expiry rule.**  After the three frozen alternatives have decisive exact
controls, do not invent additional inverse statements without a new geometric
mechanism.  A theorem true only for the recursively constructed lower-bound
family is not an unrestricted bridge.

### Thread 12: state-578 strict-gate revival

**Destination.**  Reopen state `(5,7,8)` only if a new invariant uses the full
32-point, six-cap, 24-deletion-row, complete-residual-family, exact-color
package and produces a terminal consumer.

**Stage 12.1: admission test.**

- Write a lemma card for a static residual-exterior core, global carrier cover,
  or acyclic rank.  The hypotheses must quantify over the full residual family
  and use decomposition colors/density essentially.
- Replay the relaxed 32-point two-cycle, exact-small decomposable carrier
  cycles, plateau/two-foreign-cap controls, and universal seed-escape theorem.
  Any candidate inherited by them is rejected without implementation.
- Demand one exact conclusion: a residual boundary of size at most three, a
  strict predecessor state, or a well-founded descent.  Another selected row
  or local address classification does not pass admission.

**Stage 12.2: bounded implementation if admitted.**

- Compile the smallest full-family synchronization lemma and reconnect it to
  the terminal carrier-cover or density-boundary consumer already present.
- If a finite truth test is necessary, retain all six columns/full residual
  family and independently check the certificate.  Incidence-only models are
  useful falsifiers but cannot settle the exact coloring statement.

**Expiry rule.**  Until Stage 12.1 passes, allocate no builder or long search.
State 578 is a fixed-`k=8` milestone, not the uniform proof, and may not again
become the sole focus.

### Thread 13: goal-driven intermediary lemma forge

**Destination.**  Generate independent, reusable lemmas that remove a named
obstruction or reveal that a live route is false, without creating a second
roadmap.

**Stage 13.1: portfolio checkpoint.**

- At each major approval/integration boundary, identify the one or two missing
  invariants shared by active routes and ask whether an outside mechanism could
  help.  Keep at most three simultaneous forge cards.
- Each card records an exact Lean-shaped statement, model tier, compiled
  dependencies, named downstream consumer, dual/hereditary forms, behavior on
  the equality construction, bounded falsifier, and expiry condition.

**Stage 13.2: lifecycle.**

- Follow `seed -> normalize -> falsify -> formalize -> consumer audit`.
  Reject duplicates, unreachable hypotheses, circular statements, and lemmas
  whose only application assumes the target recurrence.
- Maintain different failure modes: for example one weighted predecessor
  lemma, one residual-escape compression lemma, and one planar circuit lemma,
  rather than three variants of the same address count.
- Promote only a compiling theorem with a verified consumer.  Park a true but
  inert theorem; retain a counterexample for a false one.

**Candidate queue.**  Two-anchor rooted-circuit elimination and the middle-word
selector remain negative controls.  One-anchor Carathéodory survives only as
inert geometric infrastructure, while neighborhood weighting, signed local
transitions, and the first collective exterior Borda-rank invariant fail exact
rational Fin-8 controls.  Multi-probe residual escape has graduated from the
forge: the 30-probe incidence theorem compiles and its witness-reuse/collision
consumer is active state-567 work.  Do not add another exterior-rank candidate
until it first passes the recorded Fin-8 and duplicated-neighborhood controls.

**Expiry rule.**  Forge work is capped and secondary.  It never displaces all
direct work on Threads 1--3 and agent consensus never upgrades evidence.

### Thread 14: formal-research system and template feedback

**Destination.**  Improve the rate at which conjectures are correctly stated,
falsified, formalized, and integrated.  This thread contributes to progress by
reducing wasted proof search and evidence mistakes, but it produces no
mathematical completion by itself.

**Stage 14.1: planning and timing.**

- Turn the existing estimate ledger into a deterministic summary grouped by
  task type, reporting forecast midpoint versus actual active wall time and
  separating stop budget from predicted duration.
- Give every planned work item a stable, theorem-specific outcome contract
  before execution. Completion reports must identify which declared outcome
  occurred, its evidence level, and the next branch implied by that result;
  never replace this with a generic activity or progress report.
- Package the measured workflow as a reusable planning/timekeeping skill and
  forward-test it on short Lean work, bounded searches, and multi-route blocks.
- For multi-hour plans, compute the approval inventory before execution and
  trigger foreseeable platform prompts at the beginning.

**Stage 14.2: orchestration and evidence integrity.**

- Harden immutable task-packet/result validation, workspace-fingerprint
  handling under concurrent branches, ownership boundaries, and finish-gate
  reporting.  Avoid unnecessary whole-workspace freezes for disjoint read-only
  research when exact input hashes suffice.
- Add a portfolio dashboard that distinguishes theorem completion, bounded
  evidence, refutation, parked proposals, and elapsed critical path.
- Preserve serialized top-level integration, full proof gates, scoped commits,
  and pushes.

**Stage 14.3: tools, skills, and template promotion.**

- Build the planned catalog of free mathematical software with problem class,
  trust boundary, license, resource profile, reproducibility notes, and an
  optional skill entry point for each reproduced tool.
- Extract the project-neutral orchestration, innovation-sidecar, certificate
  chunking, and calibrated-timekeeping improvements into
  `docs/template_improvements.md`.  Changes to the neighboring
  `open-math-research-template` require a separate reviewed and authorized
  project.

**Expiry rule.**  Process work is scheduled only when it removes a measured
bottleneck or prevents a demonstrated evidence failure.  It is never reported
as progress on the exact formula and should remain a minority of total active
capacity.

### 2026-08-11 portfolio checkpoint

- **Thread 1:** no integral/fractional/half separator exists in the checked
  abstract rank-three model through `k=6,n=12`; this is computational evidence.
  Exact rational controls retire maximum-support exchange, neighborhood-only
  charging, signed local transitions, and the first exterior Borda-rank
  invariant.  Sol/Fable ranks the pure deep-split producer first. That producer
  survives all 19,870 strong-five-free rank-three Fin8 signotopes in two
  independent complete encodings, and the compact UNSAT core has now been
  promoted to the compiling theorem
  `halfPureDeepSplitAtFiveFinEight_of_oneChange`. This proves the exact bounded
  OneChange/no-strong-five implication, not its uniform arbitrary-size
  generalization. The thresholded `HalfPureSingletonFanProducerAboveAt`
  interface and its noncircular consumer into `PredecessorHalfSubsetAt` now
  compile. At `k=5,n=9` this producer is vacuous: the compiling theorem
  `containsStrongFiveFinNine_of_oneChange` reuses the existing ES5 certificate
  to rule out its target-free premise. At the first informative `k=6,n=10`
  boundary, two independent complete encodings make the fan negation UNSAT
  while target-free controls remain SAT. This is nonvacuous computational
  evidence; the exact bounded fan theorem is the next Lean certificate target.
  A fourth local charge is forbidden; `n=13` receives preflight only.
- **Threads 2--3:** generic deletion packing and the state-567 specialization
  compile. Exact incidence counting supplies at least 30 bad residual probes
  and a carrier-touching escape for every probe. Choice-free fiber counting
  and the residual-triple cover now compile and force either a same-occupancy
  distinct-witness collision or a carrier-only strong six. The latter has a
  compiling `1+5` through `5+1` overlap normalization. A light collision now
  compiles to exact one- or two-vertex replacement data and a four-repair
  triangular avoidance network. A relaxed Fin12 carrier-rectangle system is
  computationally UNSAT but not kernel-checked. The exact omission-rectangle
  interface now compiles: the finite carrier-only family covers every anchor
  pair, and distinct witnesses have edge-disjoint rectangles. The generic
  division-free seed-cover theorem now compiles as well: if `(C*M)*B` is below
  `choose R (B-1)`, then there is a same-class collision or a witness fiber
  larger than `M`; its exact state-567 specialization is `112 < 120` and gives
  the 15-probe leaf without assuming it. This is a genuine parameterized
  counting lemma but not a uniform Pascal recurrence, because the smaller
  diagonal states do not instantiate two disjoint carriers. The carrier-only
  terminal has also been reduced in Lean to exactly two omission-area profiles:
  four `3×3` rectangles or four area-5 plus two area-8 rectangles. The balanced
  four-grid extraction compiles. A proposed local color closure from the six
  strong pair-unions is false: an independently checked interleaved Fin12
  witness has exact integer coordinates and is nondecomposable. Hence
  realizability does not repair the lemma. The selected repair retains the
  balanced four-grid and `PackedInternalPairFourResidualEscape` together: the
  counterexample has residual cardinality zero and cannot inherit the latter.
  The first mechanical landing should package the grid with the existing two
  carrier-touching residual escapes; the next consumer must then use that
  packed-22/residual-ten provenance or decomposability essentially.
- **Thread 5:** the balanced five-way shell, universal clean `2+4` escape
  family, and nine-middle-word normalization compile.  The five named terminal
  contracts remain open.
- **Threads 4 and 11:** repeated uniform spectator lifting is stopped by an
  exact rational second-spectator target, while its generic local obstruction
  compiles.  Pure deep-split predecessor-freeness and its half-subset consumer
  compile; a global producer remains under bounded falsification. For Layer F,
  `AtMostThree.hasAtMostThreePrimeCoreCarrierCover` and its symmetric-difference
  corollary now compile: every endpoint prime-core change along an at-most-three
  mutation macro lies on a support containing one of at most three changed
  triples. This is locality infrastructure, not existence of a rank-dropping
  macro.
- **Threads 6 and 9:** `extremeExchangeK9FinSeventeen` now compiles end to end,
  including all seven former strong-ten blockers.  It is retained as a finite
  successor base.  Its explicit clause reconstruction exposes no honest
  all-parameter propagation theorem, so uniform certificate mining is stopped.
- **Threads 13--14:** the one-anchor circuit route is suspended as true but
  inert infrastructure.  The timing ledger now has a deterministic validator
  and category summary; current medians, not raw task-list sums, must calibrate
  future plans.

### Post-structural-round live matrix

This matrix supersedes stale stage descriptions without deleting their
historical rationale.  Every next item has a declared outcome contract; a
completion report must name the outcome and evidence level.

| Thread | Current state | Next exact gate | Declared outcomes |
| --- | --- | --- | --- |
| 1. Half-subset | Fin8 theorem and generic singleton-fan consumer compile; Fin9 is vacuous; Fin10 is nonvacuously UNSAT in two independently checked encodings | Promote `halfPureSingletonFanAtSixFinTen_of_oneChange`, then classify reusable semantic leaves | `T1-O1` finite theorem compiles and structural mining begins; `T1-O2` certificate bridge is operationally parked with computation retained; `T1-O3` semantic mismatch or counterexample repairs/expires the fan |
| 2. State-567 residual | Probe reuse, carrier-only normalization, rectangles, and the two-profile dichotomy compile; grid-only color closure is realizably false | Package balanced grid plus two residual escapes; separately freeze the mixed profile; run the fixed-carrier-plus-ten-residual falsifier | `T2-O1` a full-context terminal closes one profile; `T2-O2` exact SAT witness refutes/repairs it; `T2-O3` only packaging lands and the color terminal remains open |
| 3. Uniform Pascal | Generic seed-cover and collision/large-fiber counting compile, but only the state-567 two-carrier parameters instantiate | Test a variable/one-carrier residual kernel on adjacent Pascal states before formalization | `T3-O1` a genuine parameter theorem closes a concrete leaf and adjacent controls; `T3-O2` the count remains state-567-only; `T3-O3` an adjacent countermodel expires the proposed kernel |
| 4. Layer F | Three-change prime-core path locality compiles; rank-dropping macro existence is open | Search the exact realizable target-free mutation graph at the theorem threshold, then state the highest-stratum loss lemma | `T4-O1` a three-step drop theorem compiles; `T4-O2` a realizable closed component stops the route; `T4-O3` only below-threshold evidence lands |
| 5. Balanced state 567 | Five-way shell and universal clean `2+4` normalization compile; five terminal color leaves remain | Attack one terminal while visibly using exact `11+11` and repeated packing | `T5-O1` one or more terminal leaves compile; `T5-O2` an exact full-context model refutes a leaf; `T5-O3` only a sharper reduction lands |
| 6. Finite extreme exchange | `extremeExchangeK9FinSeventeen` compiles end to end | No independent work; transfer the finite base to Thread 9 | `T6-O1` a uniform pattern is stated under Thread 9; `T6-O2` no honest pattern exists and the lane is archived; `T6-O3` regression repair only |
| 7. Integral Property B | Recurrence consumer and small-cardinality base compile; Fin8 semantic promotion remains partial and integral behavior survives checked `k=6,n≤12` controls | One bounded checkpointed Fin8 bridge or one new ordered-hypergraph property, not both | `T7-O1` bounded theorem or structural property compiles; `T7-O2` engineering gate parks the certificate; `T7-O3` realizable non-bicolorable model stops integral but not weaker routes |
| 8. Fractional cover | Fractional-to-half and direct recurrence consumers compile; no separator from integral/half appears through checked `k=6,n≤12` | Propose one weighted geometric inequality that passes rational and relaxed-hypergraph controls | `T8-O1` weighted lemma produces total weight at most two; `T8-O2` exact separator demotes/stops the route; `T8-O3` candidate fails controls and no Lean work follows |
| 9. Diagonal successor | Exact diagonal `k=9` and extreme-exchange finite theorems compile; clause mining exposed no uniform law | Freeze a symbolic core-extraction candidate and falsify it at `k=10` | `T9-O1` noncircular successor compiles; `T9-O2` bounded counterexample stops the candidate; `T9-O3` no statement survives and the finite result remains a base only |
| 10. State-567 certificate | Exact 22-point searches support the packed leaves, but no state-567 semantic certificate is kernel-checked | Activate only if structural Threads 2/5 stall; choose the smallest profile-aware leaf | `T10-O1` one leaf compiles and feeds the reducer; `T10-O2` resource/bridge cap parks it; `T10-O3` certificate mining yields a symbolic lemma returned to Threads 2/3/5 |
| 11. Inverse extraction | Singleton-fan work graduated to Thread 1; one-anchor circuit is true but inert; deletion/two-piece proposals are stopped or unmotivated | Park until a new geometric mechanism gives a noncircular consumer | `T11-O1` a new mechanism produces an exact half/two-piece/deletion theorem; `T11-O2` decisive realizable control stops it; `T11-O3` remains parked |
| 12. State 578 | Suspended; infrastructure retained | Admit only a full-residual, exact-color+density invariant that defeats every recorded cycle and constructs a boundary/predecessor/descent | `T12-O1` revival gate passes; `T12-O2` candidate is inherited by controls and rejected; `T12-O3` no admissible candidate, so no resources |
| 13. Lemma forge | Residual probe counting graduated; exterior-rank and circuit candidates are negative/inert controls | Screen at most three cards: mixed profile, decomposability retention, variable-carrier Pascal repair | `T13-O1` a card graduates with compiling consumer; `T13-O2` a bounded falsifier retires it; `T13-O3` true but inert statement is parked |
| 14. Research system | Packet discipline, outcome reporting, certificate chunking, and timing ledger operate; old estimates remain badly high | Build empirical category/size bands and a portfolio dashboard; preserve approval preflight | `T14-O1` calibration coverage materially improves; `T14-O2` instrumentation lands without better forecasts; `T14-O3` process work is parked because it does not remove a measured bottleneck |

### Newly surfaced work and route ownership

The latest results create five named subthreads but no fifteenth main route:

1. `T1.A` promotes the nonvacuous Fin10 fan certificate and mines it for the
   arbitrary-size producer.
2. `T2.A` combines the balanced four-grid with universal ten-residual escape.
3. `T2.B` treats the mixed four-area-5/two-area-8 profile, which is logically
   necessary even if the balanced profile closes.
4. `T2.C` determines whether decomposability can be retained through the
   packed reducer before using it to exclude the exact planar grid witness.
5. `T3.A` tests one-carrier or unequal-carrier residual counting at adjacent
   Pascal states, repairing the precise scope failure of the current generic
   theorem.

The next four-slot mathematical wave should allocate one slot to `T1.A`, two
to `T2.A/T2.B`, and one to `T3.A`.  `T2.C` is a short read-only dependency
audit that should precede any decomposable-grid proof.  Threads 4--5 remain the
first reserves; 6 and 11 are merged/parked, and 12 stays suspended.

Empirical active-time bands for that wave are deliberately shorter than the
old forecasts: 5--20 minutes for a mechanical Lean package, 10--35 minutes
for a bounded falsifier or dependency audit, and 45--150 minutes for the Fin10
semantic certificate promotion.  Stop budgets remain separate: 30 minutes,
8 cores, 16 GiB, and 5 GiB for exploratory computation unless a packet states
otherwise.  These bands will be scored against actual active time; they are
not promises that four sequential tasks sum to a multi-hour critical path.

### Approved-next-wave candidate: four-lane deep execution plan

This block is ready for user approval but is not self-authorizing.  It uses
four parallel slots with disjoint source/run ownership and a serialized root
integration lane.  Forecasts are active work, not stop budgets.  The closest
calibration points are the 27-minute Fin8 half-pure certificate promotion,
the 60/63-minute extreme/k9 certificate promotions, the 5--13-minute recent
state-567 Lean packages, and the 6--15-minute recent bounded audits.

#### Approval and resource inventory

- No provider/Sol/Fable call is planned: these tasks implement or falsify the
  already reviewed portfolio and do not select a new main route.
- No network access, software installation, destructive cleanup, external
  repository mutation, or resource-limit increase is planned.
- Local Python, existing solver artifacts, targeted Lean checks, `make test`,
  scoped `git add`/commit, and push are already normal project operations.  A
  future approval of this plan authorizes their in-scope use but does not
  bypass any platform prompt.
- Each exploratory solver/checker command keeps the default ceiling of 30
  minutes, 8 cores, 16 GiB RAM, and 5 GiB under ignored `runs/`.  A packet-owned
  process may be terminated at its declared cap.  Any need to exceed a ceiling
  pauses only that lane and requires a new narrow approval.
- A route-changing result may trigger a later bounded review with the exact
  authorized prefix `python3 scripts/adversarial_review.py run`; that call is
  not part of this block and will not be made preemptively.

#### Lane A — `T1.A`: Fin10 singleton-fan certificate promotion

**Frozen target.**  Prove the exact theorem
`halfPureSingletonFanAtSixFinTen_of_oneChange` from the existing 1,086-variable,
17,930-clause CNF and independently replayed 6,502-addition LRAT.  Preserve all
2,560 side/pivot pairs, including the 2,550 noncovering pairs.

**Primary stages.**

1. Freeze the theorem signature, CNF/LRAT hashes, semantic map, owned generated
   modules, and per-module resource caps.  Adapt the compiling Fin8 certificate
   architecture rather than inventing a monolithic proof.
2. Generate and independently audit compact Lean atoms for OneChange, strong
   four/five/six definitions, pure-side failure, deep-split branches, and the
   5,120 fan-negation clauses.  Separate local semantic chunks from the LRAT
   replay tree.
3. Chunk the 6,502 additions with explicit live-clause interfaces.  Compile
   the encoding, representative semantic chunks, every LRAT checkpoint, the
   normalized `Fin 10` theorem, and then its public exact signature.
4. Regenerate byte-identically; reject corrupted map/proof controls; run
   forbidden-token and axiom audits.  Record compilation peak memory and the
   slowest module instead of extrapolating from source size.
5. If the theorem compiles, classify its retained semantic leaves into local
   uniform laws versus finite witness-selection/RUP structure.  Freeze at most
   one all-`n` producer candidate and give it a bounded `n=11` falsifier before
   any uniform Lean proof.

**Forecast.**  45--120 active minutes through the bounded theorem, plus
15--45 minutes for post-proof structural mining.  Individual compile commands
retain the 30-minute cap; one checkpoint redesign is allowed, not an unbounded
sequence of chunk layouts.

**Outcomes.**

- `HP610L-O1`: the exact Fin10 theorem compiles; report the uniform/nonuniform
  leaf split and next producer candidate.
- `HP610L-O2`: encoding/LRAT layers compile but one bounded semantic family
  exceeds the cap; retain precise partial evidence and the smallest blocker.
- `HP610L-O3`: the Lean semantic reconstruction disagrees with the frozen
  computational model; invalidate the computation until repaired.
- `HP610L-O4`: operational stop before a trustworthy theorem, with no
  mathematical inference.

#### Lane B — `T2.A`: balanced grid plus universal ten-residual escape

**Frozen target.**  Package the balanced omission-grid branch with the exact
two carrier-touching residual escapes, then test the full proposed terminal
`PackedBalancedGridResidualEscapeImpossible567`.  The contract must retain
the ten-point residual, OneChange, ambient cap-five/cup-six/strong-seven
avoidance, and universal four-block escape.

**Primary stages.**

1. Compile a mechanical `PackedBalancedGridTwoEscapeSystem567` theorem from
   `fourGrid_of_balanced_area_profile` and
   `packedInternalPair_has_two_carrierTouchingEscapes`.  This is packaging, not
   closure, and must preserve the common carriers/ambient state.
2. Freeze the terminal Prop and its exact consumer into the no-collision branch
   of `PackedInternalMutuallyMiddleObstructedPairImpossibleAtTwentyTwo567`.
   Audit every use of total 22, residual ten, internality, and repeated packing.
3. Build the cheapest decisive falsifier: keep the exact realizable 12-carrier
   grid coloring fixed, append ten labeled residual vertices, and encode the
   remaining colors with OneChange/target avoidance and universal residual
   escape.  Use a direct semantic checker independent of the producer.
4. If SAT, classify decomposability and exact realizability only when those
   properties decide a stated repair.  If UNSAT, mine the smallest
   full-context color/escape conflict; do not promote solver output directly.
5. Formalize a surviving conflict lemma and reconnect it through the existing
   state-567 consumers.  Stop after the balanced profile is closed or exactly
   refuted; the mixed profile remains Lane C's responsibility.

**Forecast.**  5--20 minutes for the mechanical Lean package, 15--45 minutes
for the exact falsifier/checker, and 20--75 minutes for one surviving terminal
proof or counterexample classification: 40--140 active minutes total.

**Outcomes.**

- `S567B-O1`: a full-context balanced terminal compiles and removes the
  balanced no-collision profile.
- `S567B-O2`: an independently checked exact model refutes the terminal and
  identifies which added premise is still missing.
- `S567B-O3`: packaging compiles and the fixed falsifier is UNSAT, but only
  computational support/one sharper proposal lands.
- `S567B-O4`: bounded operational stop without a route claim.

#### Lane C — `T2.B`: mixed omission-profile terminal

**Frozen target.**  Resolve the surviving profile with four area-5 rectangles
and two area-8 rectangles.  Area 5 means `1×5` or `5×1`; area 8 means `2×4` or
`4×2`.  Closing the balanced profile alone is not state-567 progress unless
this profile also has an exact disposition.

**Primary stages.**

1. Define `IsMixedCarrierOnlyOmissionProfile567` directly from the compiling
   rectangle system and the `(4,2,0,6)` count.  Derive the exact orientation,
   row-degree, column-degree, and omitted-block alternatives without colors.
2. Independently enumerate the finite six-rectangle tilings of the `6×6`
   anchor product and replay them with a different representation.  Freeze the
   smallest complete structural classification as a Lean-shaped theorem.
3. Compile the color-free classification if it materially narrows the mixed
   branch.  Then state `PackedMixedOmissionProfileResidualEscapeImpossible567`
   with the same full ambient/residual premises as Lane B.
4. Reuse only the solver harness architecture, not the semantic encoding, from
   Lane B to test the mixed layouts.  A SAT witness must be directly checked;
   UNSAT is bounded support until a semantic Lean bridge exists.
5. Formalize the first surviving color/residual conflict, or integrate the
   smallest countermodel and expire the terminal.  If both Lane B and Lane C
   close, compile the no-collision contradiction and hand the remaining
   same-occupancy collision branch to the existing four-repair network.

**Forecast.**  10--30 minutes for structural enumeration/classification,
10--30 minutes for a compiling extraction, and 20--80 minutes for the
full-context gate/terminal: 40--140 active minutes total.

**Outcomes.**

- `S567M-O1`: the mixed full-context terminal compiles and removes the second
  no-collision profile.
- `S567M-O2`: an independently checked mixed-profile model refutes the proposed
  terminal and becomes the next repair control.
- `S567M-O3`: an exact structural classification compiles, but the color
  terminal remains open.
- `S567M-O4`: bounded operational stop without mathematical inference.

#### Lane D — `T3.A`: variable-carrier Pascal repair

**Frozen question.**  Can the generic residual seed-cover/fiber count be fed
by a one-carrier, unequal-carrier, or fractional witness-class producer at
adjacent Pascal states whose reservoirs are too small for two disjoint
predecessor carriers?

**Primary stages.**

1. Produce a parameter table for the exact controls `(4,5,5)`, `(4,6,6)`,
   `(4,8,8)`, and `(5,6,7)`: reservoir size, possible carrier sizes, residual
   size, deletion-block size, seed count, fiber cap, and the inequality needed
   by `badResidualBlocks_collision_or_largeFiber`.
2. Freeze exactly three noncircular producers before controls:
   a single-carrier/private-witness system, an unequal two-carrier system, and
   a fractional class-bound system.  None may assume the target Pascal bound,
   injectivity, or the desired large fiber.
3. Test all three on the compiled small states, equality construction, and the
   exact state-567 positive control.  Use a finite-set/incidence falsifier
   first; require exact color/decomposition evidence only for survivors.
4. For the strongest survivor, compile a generic producer-to-count theorem
   whose `(5,6,7)` specialization recovers existing state-567 infrastructure
   and whose adjacent specialization is genuinely nonvacuous.
5. Attempt one connection to `PascalTailTwoSideBound`.  If the geometric/color
   terminal is still missing, freeze that precise interface and stop rather
   than calling the count a uniform recurrence.

**Forecast.**  10--30 minutes for the parameter/candidate audit, 15--45 minutes
for bounded controls, and 15--60 minutes for one generic Lean consumer:
40--135 active minutes total.

**Outcomes.**

- `PTVC-O1`: a variable-carrier parameter theorem compiles and has a genuine
  adjacent-state specialization.
- `PTVC-O2`: exactly one candidate survives controls and yields a precise open
  geometric terminal, but no Pascal-tail theorem yet.
- `PTVC-O3`: all three producers are refuted or reduce to the target bound;
  expire this repair and retain the state-567 count as finite infrastructure.
- `PTVC-O4`: operational stop before decisive controls.

#### Contingent second wave and overall duration

- After `HP610L-O1`, spend one bounded block on uniform leaf mining and only
  then decide whether an `n=11` fan gate tests a named candidate.
- After `S567B-O1` and `S567M-O1`, compile the no-collision contradiction and
  switch Thread 2 to the same-occupancy collision/four-repair terminal.  If
  either is refuted, the returned model controls the repair instead.
- After `PTVC-O1/O2`, formalize only the surviving producer/terminal; after
  `PTVC-O3`, return the slot to Layer F or the balanced state-567 branch.
- The first wave contains roughly 165--515 cumulative active agent-minutes.
  With four slots, the empirical elapsed forecast is 45--150 minutes.  The
  contingent second wave adds 45--180 elapsed minutes only when an outcome
  creates a named follow-on.  Thus 2--5 hours of useful parallel runway is
  available, but the plan does not pad fast refutations to manufacture wall
  time.

### Portfolio scheduling and evidence gates

- Keep at least one active item from Threads 1--3 whenever mathematical work
  is scheduled.  Threads 4--11 are hedges, not replacements for every direct
  route; Thread 12 is dormant; Threads 13--14 are bounded support work.
- Resolve candidate statements with the cheapest exact falsifier before large
  Lean scripts.  Promote only the strongest statement that survives.
- Integrate shared files, run project gates, commit, and push serially from the
  top-level orchestrator.  Specialist proposals and computations remain
  untrusted until independently checked and incorporated into a compiling
  theorem.
- State 578 remains suspended.  It may re-enter only through the ticket-0010
  revival condition recorded in the Wayfinder map.
