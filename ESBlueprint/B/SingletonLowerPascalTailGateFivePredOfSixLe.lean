import ErdosSzekeres.StructuralChargingPascalTails

namespace ErdosSzekeres

/-- For every k at least six, the audited decomposable two-side five-cap bound closes the lower singleton Pascal-tail gate at (5,k-1,k), using the classic Z bound, marker lemma, and cup-plus-four-cap-free row defect.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem singletonLowerPascalTailGate_five_pred_of_six_le {k : ℕ} (hk : 6 ≤ k) : SingletonLowerPascalTailGate 5 (k - 1) k := by
  sorry

end ErdosSzekeres
