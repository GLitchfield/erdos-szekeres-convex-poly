import ErdosSzekeres.StructuralChargingPascalCupBlocks
import ESBlueprint.B.SingletonLowerPascalTailGateFiveDiagOfSixLeOfInputs

namespace ErdosSzekeres

/-- Colour duality transfers the accepted diagonal five lower singleton Pascal-tail gate to the upper gate at (k,5,k), with the exact same uniform R20 cupblock and R21 Baek hypotheses.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem singletonUpperPascalTailGate_diag_five_of_six_le_of_inputs (hblocks : ∀ k, 5 ≤ k → DiagonalCupBlocksForce4kk k) (hbaek : ∀ {n k : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}, 3 ≤ k → OneChangeOn χ s → ¬ContainsCapSet χ s 4 → ¬ContainsStrongPolygonSet χ s k → s.card ≤ 1 + Nat.choose (k - 1) 2) {k : ℕ} (hk : 6 ≤ k) : SingletonUpperPascalTailGate k 5 k := by
  exact (singletonUpperPascalTailGate_iff_lower_dual
    (a := k) (u := 5) (k := k)
    (by omega) (by omega) (by omega) (by omega)).2
      (singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs hblocks hbaek hk)

end ErdosSzekeres
