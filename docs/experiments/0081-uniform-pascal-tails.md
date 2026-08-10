# Experiment 0081: uniform Pascal-tail reduction

Date: 2026-08-10

Status: arithmetic and integration shell proved in Lean; geometric tail gates
remain open

## Question

Can the published induction's state-specific scalar failures be replaced by
one all-parameter staircase theorem, and does state `(5,7,8)` arise as an
exact instance?

## Bounded audit

An independent replay through `k = 20` checked 968 active states and 14,532
feasible index intervals.  It found no violation of the pattern

```text
published index sum <= k - 1
iff lowerCard <= choose(k-3,a-2) or upperCard <= choose(k-3,u-2).
```

Outside the two tails, the index sum was exactly `k`.  This finite audit was
proposal evidence only and did not establish the theorem.

## Compiling result

`StructuralChargingPascalTails.lean` proves the needed implication uniformly:
the existing unique saturation theorem puts one actual child in the left or
right binomial tail.  It also proves both tail widths lie inside the active
outer threshold, defines the two exact singleton-reservoir gates, and proves
that strict predecessor states plus those gates imply the full exact
critical-root obstruction.

`StructuralChargingPascalTails578.lean` proves that the two generic reservoirs
at `(5,7,8)` are exactly 32 and 41.  Its generic critical-root theorem is
therefore definitionally the existing state-578 two-gate reduction.

## Outcome

The uniform arithmetic route succeeds.  Repeated state-specific
`interval_cases` proofs are no longer needed for the active middle window.
The unresolved work is now stated cleanly as two parameterized geometric
singleton-tail gate families.  Their binomial widths grow with the
parameters, so this is a uniform reduction rather than a proof of all E3
states.

## Evidence

- `ErdosSzekeres/StructuralChargingPascalTails.lean`
- `ErdosSzekeres/StructuralChargingPascalTails578.lean`
- `ErdosSzekeres/PublishedInductionSemantics.lean`
- `ErdosSzekeres/StructuralChargingConservedBranch.lean`
