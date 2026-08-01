# Sweep-orientation formalization plan

Last updated: 2026-08-01.

## Chosen mathematical interface

The project will use two connected layers.

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
| A7 | a generic sweep direction exists for every finite point set | Known; pending | Avoid equal projection coordinates |
| A8 | an orientation-preserving affine coordinate change normalizes an arbitrary generic sweep to A2 | Known; pending | Removes the current coordinate normalization assumption |
| A9 | sorting and indexing give an equivalence between a geometric `Finset` and `SweptConfiguration` | Known; pending | Connects the public theorem to the ordered layer |

### Layer B: realizable triple colorings

| ID | Lemma or definition | Status | Purpose |
| --- | --- | --- | --- |
| B1 | restriction and increasing relabeling of `TripleColoring` | Pending | State induced subconfigurations cleanly |
| B2 | `IsMonochromaticChain`, `IsCup`, and `IsCap` | Compiles | Common finite definition of cups and caps |
| B3 | all-triples and consecutive-triples definitions of a cup/cap are equivalent for a sweep coloring | Known; pending | Matches classical recurrence-friendly definitions |
| B4 | every swept coloring satisfies the necessary four-index consistency law | Known; pending | Record realizability information rather than allowing arbitrary colorings |
| B5 | reflection exchanges cups and caps and preserves convexity | Known; pending | Symmetry control and proof reuse |

We will not assert that B4 characterizes realizability. Rank-three sign data can
be nonrealizable, and overly broad ordered-hypergraph generalizations are known
to fail.

### Layer C: recognize convex position from signs

| ID | Lemma or definition | Status | Purpose |
| --- | --- | --- | --- |
| C1 | orientation-sign characterization of a point inside a triangle | Known; pending | Reduce four-point convexity to triple signs |
| C2 | a four-point subset is convex iff no point lies in the triangle of the other three | Known; pending | Small local convexity certificate |
| C3 | explicit Boolean criterion for a convex ordered quadruple from its four triple colors | Known; pending | Make convexity purely combinatorial |
| C4 | a finite planar set is in convex position iff all four-point subsets are convex | Known; pending | Lift the local certificate to arbitrary size |
| C5 | define a strong polygon as compatible upper/lower monochromatic chains and prove it equivalent to geometric convex position | Known; pending | Exact combinatorial form of the target polygon |

C3--C5 are the crucial safety bridge. Until they compile, a theorem about
`TripleColoring` is not reported as a theorem about planar convex polygons.

### Layer D: classical controls

| ID | Lemma or definition | Status | Purpose |
| --- | --- | --- | --- |
| D1 | cup--cap rank assignment for each sweep vertex | Known; pending | Pigeonhole/recurrence engine |
| D2 | exact cup--cap number `binom(a+b-4,a-2)+1` | Known; pending | Reproduce the 1935 theorem in the chosen API |
| D3 | classical binomial upper bound for `ES(n)` | Known; pending | End-to-end positive control of all bridges |
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
and mathlib `v4.29.1`. No source has been copied. We will first stabilize our
geometry bridge, then port small combinatorial APIs with attribution only when
that is cheaper and clearer than reimplementation.
