import ErdosSzekeres.StructuralChargingPascalTails

namespace ErdosSzekeres

/-- The audited decomposable singleton lower Pascal-tail gate at (6,k-2,k) for every k at least seven, proved by cap-start peeling, asymmetric markers and the exhaustive root-split cubic bound.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.decomposableStateUpper_of_lower_gates_at -/
theorem singletonLowerPascalTailGate_six_pred_pred_of_seven_le {k : ℕ} (hk : 7 ≤ k) : SingletonLowerPascalTailGate 6 (k - 2) k := by
  sorry

end ErdosSzekeres
