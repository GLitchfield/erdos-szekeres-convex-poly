# Experiment 0086: diagonal Pascal cup-block interface

Date: 2026-08-10

Status: Compiling reduction; first new case isolated

## Question

Do the certificate-free `(4,k,k)` singleton-tail proofs share one exact
all-parameter interface, and does that interface clarify the relation between
the open state-567 branch and the uniform E3 program?

## Compiling result

`StructuralChargingPascalCupBlocks.lean` defines
`DiagonalCupBlocksForce4kk k`: two ordered cup blocks of sizes `(k-2,k-1)` in
either order force a four-cap, a `k`-cup, or a strong `k`-set. Lean proves:

- `lowerPascalTailReservoir 4 k k = 2*k-3` for every `k ≥ 5`;
- the cup-block contract bounds any target-free ordered pair by `2*k-4`;
- the contract implies `PascalTailTwoSideBound 4 k k` and hence
  `SingletonLowerPascalTailGate 4 k k`; and
- the existing `3+4`, `4+5`, `5+6`, and `6+7` theorems instantiate the
  contract for every `5 ≤ k ≤ 8`.

This also supplies the previously omitted compiling positive control
`singletonLowerPascalTailGate_477`. The first genuinely new diagonal instance
is `k=9`, with ordered cup blocks `7+8` or `8+7`.

The state-567 specialist found that the historical residue refinements already
meet their expiry condition. `StructuralChargingWitnessBranchesPacked.lean`
therefore retains the exact 22-point cardinality and deletion packing in two
new contracts and proves that those two contracts imply
`TwoCapFreeSidesBound567`. This reducer compiles; the two contracts remain
open mathematical obligations.

## Interpretation

This is progress on the uniform interface, not a proof of the all-`k`
cup-block contract and not a proof of state 567. The diagonal `a=4` family is
also not a replacement for the open `a=5` state-567 obstruction. It supplies a
clean scalable falsification target and proves that four previously separate
finite developments are instances of one theorem shape.

The frozen Sol/Fable review ranked state 567 above the other two streams but
did not verify exact Lean signatures. The later read-only specialist audit
recommended the exact packed reducer and independently identified `k=9` as
the first new diagonal case. Advisory agreement is not proof evidence.

## Evidence

- `ErdosSzekeres/StructuralChargingPascalCupBlocks.lean`
- `ErdosSzekeres/StructuralChargingWitnessBranchesPacked.lean`
- `docs/wayfinder/tickets/0002-test-e3-and-select-repair.md`
- ignored provider report
  `runs/reviews/20260810-next-three-streams/run1/REPORT.md`
