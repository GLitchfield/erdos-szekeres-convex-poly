# Experiment 0093: threshold-scoped Layer-F mutation rank

Date: 2026-08-10

Status: Compiling interface correction and rank infrastructure

## Question

Is the existing mutation-normalization contract sound as stated, and what is
the smallest noncircular descent interface that would promote the decomposable
upper theorem to every sweep-realizable coloring?

## Compiling correction

The unthresholded contracts are false for every positive target size. They
quantify over `Fin 0`: the empty coloring is sweep-realizable and target-free,
but recursive decomposability requires a nonempty support. Lean now proves

```lean
not_targetFreeMutationNormalizesAt_of_pos
not_targetReflectingDecomposableNormalizationAt_of_pos
```

and introduces the exact-threshold replacement
`TargetFreeMutationNormalizesAboveAt`. The theorem
`sweepExactUpperAt_of_mutationNormalizationAbove` proves that this corrected
contract, together with `DecomposableExactUpperAt k`, yields the unrestricted
sweep upper bound.

The new three-step interface allows a natural-number rank to decrease after
one, two, or three target-free realizable mutations; its intermediate values
need not decrease. Well-founded induction compiles the resulting
normalization. This is an implication theorem, not a proof that such a rank
descends.

## Prime-core rank

`DecompositionPrimeMutationRank.lean` defines `PrimeCoreCount χ`, the number
of restrictions of `χ` that are deletion-minimal indecomposable prime cores.
On every nonempty ground set Lean proves

```lean
PrimeCoreCount χ = 0 ↔ IsDecomposable χ
```

so this is a concrete, noncircular candidate rank. Proposal-level seven-point
diagnostics indicate that one- and two-mutation descent are false for this and
a related restriction-defect rank; three mutations are the first surviving
macro length. Those diagnostics are not independently certified and no
general descent theorem is claimed.

## Literature boundary

Roudneff and Sturmfels prove connectivity by representability-preserving
mutations for general-position arrangements. That unrestricted connectivity
does not imply connectivity of the induced subgraph obtained after deleting
every coloring containing the forbidden strong polygon. Target-free descent
or a target-free component obstruction remains the Layer-F mathematical
problem.

## Route disposition

`MODIFY_TO_THRESHOLD_SCOPED_THREE_STEP_DESCENT`.

The corrected consumer and prime-core zero characterization are completed Lean
results. The next hard theorem is a strict three-step descent for a concrete
rank above the exact threshold, or a sweep-realizable target-free mutation
component with no decomposable vertex that refutes this route.

## Evidence

- `ErdosSzekeres/DecompositionPrimeNormalization.lean`
- `ErdosSzekeres/DecompositionPrimeMutationRank.lean`
- `ErdosSzekeres/PrimeMutationPositiveControl.lean`
- J.-P. Roudneff and B. Sturmfels, “Simplicial cells in arrangements and
  mutations of oriented matroids,” *Geometriae Dedicata* 27 (1988), 153--170,
  DOI `10.1007/BF00151346`.
- bounded route review packet SHA-256
  `b7948090fde046765ddadb2cefa186f2c453294edab5a8ceae61b8fbaaba6311`
