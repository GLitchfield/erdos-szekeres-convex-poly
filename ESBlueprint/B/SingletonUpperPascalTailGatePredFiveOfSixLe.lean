import ErdosSzekeres.StructuralChargingPascalTailGates
import ESBlueprint.B.SingletonLowerPascalTailGateFivePredOfSixLe

namespace ErdosSzekeres

/-- For every k at least six, colour duality transfers the accepted lower singleton Pascal-tail gate at (5,k-1,k) to the upper gate at (k-1,5,k).
@node
@ws B
@kind formalization
@depends ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem singletonUpperPascalTailGate_pred_five_of_six_le {k : ℕ} (hk : 6 ≤ k) : SingletonUpperPascalTailGate (k - 1) 5 k := by
  exact (singletonUpperPascalTailGate_iff_lower_dual
    (a := k - 1) (u := 5) (k := k)
    (by omega) (by omega) (by omega) (by omega)).2
      (singletonLowerPascalTailGate_five_pred_of_six_le hk)

end ErdosSzekeres
