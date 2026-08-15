---
title: Classify geometric right-extension fibers
type: research
mode: AFK
status: closed
claim: codex-geometric-extension-fibers-2026-08-15
blocked_by: none
---

## Question

For a realizable ordered triple coloring `χ`, what restrictions does geometry
place on the colors of all triples containing one new rightmost point?  Can
those restrictions be represented by an invariant that is smaller than the
new child's full straight-line realizability obligation and useful to a named
upper-bound consumer?

This question has three different fibers which must not be conflated:

1. abstract links satisfying the new `OneChangeOn` constraints;
2. links realized by adding a point to one fixed coordinate realization; and
3. the union of the fixed fibers over every realization of the parent
   coloring.

The finite atlas may sample the third object, but finite coordinate cohorts do
not exhaust it without a separate theorem.

## Decision criteria

The work had one proof-producing slot and three information-gathering slots.
It could count as forward proof movement only if a compiling theorem closed or
strictly reduced `D-HALF`, `D-DECOMP`, `D-NORMALIZE`, or the state-567
terminal.  An exact representation of a fixed arrangement, a source-backed
abstract-extension normal form, or another finite equality was not enough.

The seven-point outcome remained embargoed unless a frozen invariant first
showed nonsymmetric compression through six and named a load-bearing consumer.

## Formal contracts

`TripleColoringExtensionFiber.lean` defines:

```lean
AbstractRightExtensionLinkFiber χ
AbstractRightExtensionFiber χ
FixedGeometricRightExtensionFiber P
GeometricRightExtensionFiber χ
PredicateFilteredRightExtensionFiber fiber predicate
```

The central exact theorem is:

```lean
theorem mem_geometricRightExtensionFiber_iff
    (χ : TripleColoring n) (ψ : TripleColoring (n + 1)) :
    ψ ∈ GeometricRightExtensionFiber χ ↔
      IsSweepRealizable ψ ∧
        ψ.restrict (finInitialOrderEmbedding n) = χ
```

The module also proves that the parent restriction and labeled old-pair link
determine the child, and that every fixed geometric extension is an abstract
compatible extension.

## Resolution

### Formal layer: `EXTFIBER-LAND`

The exact module compiles directly and through its targeted Lake build.  Its
public declaration audit uses only `propext`, `Classical.choice`, and
`Quot.sound`.  This closes the representation-interface card, but the theorem
is an exact restatement of child realizability over a fixed parent restriction;
it does not reduce a destination dependency.

### Source/localization layer: `LOCALIZATION-NO-CANDIDATE`

The bounded source audit distinguished three attractive mechanisms:

- Las Vergnas type-III coline-cycle localizations;
- crossing-poset lower sets for signotope extensions; and
- fixed-realization half-plane feasibility and Helly certificates.

The first two characterize abstract oriented-matroid or pseudoline extensions,
not straight-line realizability.  The third is exact for one common coordinate
realization, but taking a union over the parent realization space does not
permit different small subfamilies to use different witnesses.  Connectivity
or lexicographic reachability is also too coarse: rank-three abstract
extension spaces already have the relevant connectedness.  No noncircular
exact characterization of `GeometricRightExtensionFiber` survived.

### Fixed-coordinate atlas: `ATLAS-56-LAND`

Independent exact-rational producer and checker implementations agree through
child size six:

| Child size | Parents | Abstract edges | Frozen realizations | Fixed cells | Sensitive parents |
| --- | ---: | ---: | ---: | ---: | ---: |
| 4 | 2 | 8 | 91 | 364 | 0 |
| 5 | 8 | 62 | 112 | 825 | 4 |
| 6 | 62 | 908 | 124 | 1,550 | 43 |

All 327 cell-adjacency graphs are connected.  A labeled boundary-relative
wiring representation exactly replays all 2,739 cells: it stores canonical
pair-line labels, their bottom-to-top order just right of the parent, and
strictly ordered crossing slices; every equal-abscissa collection is reversed
as one atomic family of disjoint concurrent blocks.  This last condition
prevents nonexistent intermediate cells at concurrence.

This wiring is an exact encoding of each checked fixed arrangement.  It is not
a compression theorem and not an invariant of the abstract parent coloring.
The sampled fixed-fiber union misses 78 abstract links across 44 of the 62
five-point parents, but absence from the samples is not nonrealizability
evidence.  The checker rejects coordinate, line-label, sign-mask, omitted-cell,
false-adjacency, and false-wiring corruptions.

### Target-free and two-step consumers: `TFCOUPLING-NO-CANDIDATE`

For a first link `λ`, second link `μ`, and colors
`σ(i) = χ(i,x,y)`, a set `S ∪ {x,y}` is strong exactly when the last-link
strong-support condition holds, `λ = μ` on all pairs of `S`, and `σ` is
constant on `S`.  OneChange makes the two pair links permutation orders and
the `σ` classes common consecutive blocks.  Those properties are abstract
OneChange consequences rather than extra geometry.

The tested fixed target-free fibers are often disconnected at child size five
and only sometimes gated.  More importantly, an exact target-free Fin9
realization has one seven-vertex `σ` class containing five strong-five sets.
Thus a majority-class consumer is false.  The remaining separation-set hitting
formulation still requires the original global support/purity selector and
does not strictly reduce it.

## Evidence

- Compiling fiber module SHA-256:
  `d66a33d1491c06a9ed19c5aa88f08e05edda2a4ca8df9f1e44862070f32495c1`.
- Validated Lean result SHA-256:
  `51981ffd661afb32963f55ad17827c44a2f0e1a40e7d797c36aae752c2ad980c`.
- Validated source-audit result SHA-256:
  `f9238435750839adfbace97e7dbfe618d454027ade1236c6131b69c580acef68`.
- Atlas certificate/check-report SHA-256:
  `f58ce6173b1051455fe245561e5e63b90523e83991cd55fae2e803564d0b569d`
  and
  `6090dffccf11c4880de5656511d95fec7dcfee79c93ba38d192e126c81b876a1`.
- Validated atlas result SHA-256:
  `3314cdd5d4607787520d6b1ddcb24b881accd0316c92cc5b99cd0eabe968ee42`.
- Validated target-free result SHA-256:
  `567efa0aff5a7e4362b7f58945b8521be67d7444bbbf3b048b5cadbcca73b638`.
- The bounded Sol/Fable review used evidence-packet SHA-256
  `9d3f111c91431bca00a185421675c526714fb68921b7529e257be77d63a1a882`;
  both reviewers advised treating the block as bounded falsification rather
  than a proof route.  Provider review is advisory, not mathematical evidence.

## Proof-distance accounting

- **Net proof movement:** neutral.
- **Evidence:** one compiling interface theorem, checked bounded computation,
  and a source audit.
- **Difficulty displaced:** none demonstrably smaller.  The open obligation is
  still to characterize or exploit the union over the realization space, or
  to produce a target-free support from it without reintroducing the original
  selector.
- **Counterfactual test:** knowing the result earlier would have prevented
  fixed-representative, bare-swap, abstract-localization, topology, and
  majority-class detours.  It would not have reduced the remaining proof work
  enough to count as proof progress.
- **Planning consequence:** retain the Lean API and atlas as gated
  infrastructure; suspend geometric-fiber localization/topology and direct
  majority consumers; do not open `n = 7` from this mechanism.
- **Load-bearing ledger:** no destination edge changed.

## Revival gate

Revive this child only with a frozen invariant which:

1. is strictly smaller than labeled atomic-slice wiring or full child
   realizability;
2. shows nonsymmetric compression on the admitted through-six atlas;
3. has a compiling or Lean-shaped consumer that strictly reduces a named
   `D-HALF`, `D-NORMALIZE`, or state-567 obligation; and
4. has a preregistered false-positive/false-negative test before any
   seven-point outcome is opened.

Do not revive it merely by enumerating more coordinate representatives,
formalizing an abstract lower-set presentation, or rephrasing realizability as
a coherent adjoint/allowable-lift premise.
