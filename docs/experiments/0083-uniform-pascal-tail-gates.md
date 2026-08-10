# Experiment 0083: uniform geometric Pascal-tail gates

Date: 2026-08-10

Status: generic consumer proved; first open instance identified exactly

## Question

Can the binomial-width arithmetic tails from Experiment 0081 be consumed by
one geometric statement, rather than by a new argument for every state?

## Compiling result

`StructuralChargingPascalTailGates.lean` defines the honest retained-child
left and right obligations, without assuming that a positive tail is a
singleton. It proves that strict predecessor states plus those two obligations
eliminate every active critical root.

The stronger singleton reduction is then derived from one ordered local
predicate, `PascalTailTwoSideBound`. Around a singleton root, absence of the
parent cap makes the two ordered gap sides predecessor-cap-free; a bound on
their combined size closes the exact Pascal reservoir. Color duality supplies
the upper gate, so the all-parameter theorem
`criticalRootImpossible_of_predecessors_pascal_twoSide_bounds` needs the same
consumer in the two color orientations.

Three positive controls compile without finite certificates:
`singletonLowerPascalTailGate_455`, `_466`, and `_488`. The next boundary is
not state 578. Lean proves `pascalTailTwoSideBound_567_iff`, identifying the
`(5,6,7)` instance exactly with the repository's already isolated
`TwoCapFreeSidesBound567`; its lower and upper reservoirs are 22 and 25.

## Outcome

The geometric interface is a genuine uniform reduction, but not the uniform
E3 proof. The remaining theorem family is `PascalTailTwoSideBound`; its first
open member is the known state-567 two-cap-free-sides obstruction. This
consolidates the all-parameter route and gives it an earlier, cheaper truth
test than state 578.

All named theorems compile. Their axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`.

A frozen pre-implementation Sol/Fable review ranked this branch first but
recommended MODIFY: retain the whole small-child gate as the canonical
obligation and treat singleton gates as sufficient attack lemmas. The Lean
file follows that distinction. The review was advisory and preceded the
compiling result.

## Evidence

- `ErdosSzekeres/StructuralChargingPascalTailGates.lean`
- `ErdosSzekeres/StructuralChargingPascalTails.lean`
- `ErdosSzekeres/StructuralChargingCapFreeSides.lean`
- `runs/reviews/20260810-three-route-deep-block/run1/REPORT.md`
  (ignored advisory output)
