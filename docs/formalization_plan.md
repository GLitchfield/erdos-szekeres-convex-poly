# Sweep-orientation formalization plan

Last updated: 2026-08-01.

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
| D2 | exact cup--cap number `binom(a+b-4,a-2)+1` | Upper half compiles; sharpness pending | Reproduce the 1935 theorem in the chosen API |
| D3 | classical binomial upper bound for `ES(n)` | Compiles | End-to-end positive control of all bridges |
| D4 | recursive `2^(n-2)` lower-bound construction | Known; pending | Formal sharpness for all `n` |
| D5 | exact cases `n = 3,4,5` | Known; pending | Small controls; `n=6` is a separate certificate project |

### Layer E: the modern structural frontier

| ID | Lemma or definition | Status | Purpose |
| --- | --- | --- | --- |
| E1 | composition/decomposition of sweep colorings | Known; pending | Express the recursive extremal construction |
| E2 | polygon-size recurrence under composition | Known; pending | Control decomposable configurations |
| E3 | exact formula for decomposable point sets | Published 2026; pending | Reproduce the strongest directly relevant structural theorem |
| E4 | a minimal counterexample to the exact formula is indecomposable | Consequence of E3; pending | Isolate the genuine obstruction |

### Layer F: new research required

The remaining destination needs a new theorem controlling indecomposable
realizable colorings. Plausible forms include a nontrivial decomposition after
deleting few vertices, a sharper rank recurrence using the four-point laws, or
an implication through the Erdős--Tuza--Valtr parameter lattice. None is
currently claimed.

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
The matching cup--cap construction is still required before D2 can be called
exact.
