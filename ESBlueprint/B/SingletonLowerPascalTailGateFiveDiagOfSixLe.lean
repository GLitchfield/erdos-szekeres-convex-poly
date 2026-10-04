import ESBlueprint.B.SingletonLowerPascalTailGateFiveDiagOfSixLeOfInputs
import ESBlueprint.B.DiagonalCupBlocksForce4kkOfFiveLe
import ESBlueprint.C.CardLeChooseOfOneChangeNoCapFourNoStrong

namespace ErdosSzekeres

/-- The decomposable (5,k,k) singleton lower Pascal-tail gate for every k >= 6, unconditionally: R22 gate singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs with its two inputs supplied by the uniform two-cup-block lemma (R20) and the Baek single-set bound (R21).
@node
@ws B
@kind formalization
@depends ErdosSzekeres.singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs, ErdosSzekeres.diagonalCupBlocksForce4kk_of_five_le, ErdosSzekeres.card_le_choose_of_oneChange_no_capFour_no_strong
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem singletonLowerPascalTailGate_five_diag_of_six_le {k : ℕ} (hk : 6 ≤ k) : SingletonLowerPascalTailGate 5 k k := by
  exact @singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs
    (fun k hk ↦ @diagonalCupBlocksForce4kk_of_five_le k hk)
    (@card_le_choose_of_oneChange_no_capFour_no_strong) k hk

end ErdosSzekeres
