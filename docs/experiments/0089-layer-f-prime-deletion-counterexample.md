# Experiment 0089: Layer-F prime-deletion counterexample

Date: 2026-08-10

Status: Compiling counterexample; deletion route stopped

## Question

Does every sweep-realizable, target-free decomposition-prime support with more
than six vertices retain a decomposition-prime restriction after deleting one
or two vertices?

## Compiling result

No. `PrimeTwoDeletionCounterexample.lean` defines the seven integer points

```text
(0,0), (1,0), (2,-6), (3,-54), (4,-74), (5,-30), (6,-21)
```

and kernel-checks all of the following:

- their sweep coordinates are strictly increasing and every ordered
  orientation determinant is nonzero;
- their induced coloring is decomposition-prime on the full support;
- the coloring contains no strong six-set; and
- deleting any one or any two vertices leaves a non-prime restriction.

The theorem `not_primeTwoDeletionOrTargetAtSix` therefore refutes the exact
one-or-two-deletion contract, rather than only an abstract signotope variant.
The finite checks reduce inside the Lean kernel through proved Boolean
reflection lemmas; no external SAT result or native-code oracle occurs in the
theorem.

## Surviving Layer-F interface

`DecompositionPrimeNormalization.lean` states the actual load-bearing
normalization contract and proves that a target-reflecting normalization from
arbitrary sweep-realizable colorings to decomposable ones promotes
`DecomposableExactUpperAt k` to the unrestricted sweep upper bound.

The deletion counterexample redirects the proposed construction of that
normalization. The surviving bounded proposal is target-free realizable
single-triple mutation. `DecompositionPrimeNormalization.lean` defines the
mutation-path contract and proves it implies target-reflecting normalization.
`PrimeMutationPositiveControl.lean` kernel-checks one genuine planar edge:
moving point zero flips exactly triple `(0,5,6)` and reaches a
sweep-realizable, strong-six-free decomposable coloring. Exact computation on
seven-vertex signotopes additionally reports that every target-free coloring
reaches a decomposable one within three changes. The single edge is a
completed positive control; the connectivity claim and general normalization
remain proposal evidence.

`DecompositionPrimeUncrossing.lean` records the safe fallback: four nonempty
corners of two deep-below splits force a strong four-set. An exact rational
six-point control shows that crossing alone does not force a strong six-set,
so any larger uncrossing theorem needs an explicit cup/cap capacity premise.

## Route disposition

- Prime one-or-two deletion: **STOP**, by a Lean-kernel counterexample.
- Target-reflecting normalization consumer: **GO**, compiling and reusable.
- Realizable target-free mutation normalization: **GO as a proposal**, with a
  compiling exact-small positive control but no general theorem.
- Crossing-split route to strong six: **STOP** without new capacity data;
  retain the compiling strong-four lemma.

This closes a proposed route, not the unrestricted happy-ending theorem.

## Evidence

- `ErdosSzekeres/PrimeTwoDeletionCounterexample.lean`
- `ErdosSzekeres/DecompositionPrimeNormalization.lean`
- `ErdosSzekeres/DecompositionPrimeUncrossing.lean`
- `ErdosSzekeres/PrimeMutationPositiveControl.lean`
- deterministic and independently replayed ignored certificates under
  `runs/agents/20260810-next-four-hour-block/layerf/`
- partial bounded provider review under
  `runs/reviews/20260810-three-thread-four-hour-block/run1/`
