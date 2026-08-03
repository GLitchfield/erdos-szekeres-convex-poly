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
on pairwise incompatibility of those raw values. This is an abstract
decomposable-coloring result, not a realizability certificate. A surviving
rank strategy must retain higher-order predecessor correlations, use a
different label, or exploit a precisely stated geometric constraint; none is
yet selected as the uniform E3 route.

The proof is complete only when that new structural input and Layers A--E
combine into the already-defined `ErdosSzekeresConjecture` with no placeholders.

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
