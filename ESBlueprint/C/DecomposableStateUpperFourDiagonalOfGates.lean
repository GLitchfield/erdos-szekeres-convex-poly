import ErdosSzekeres.StructuralChargingPascalTails
import ESBlueprint.C.CardLeChooseOfOneChangeNoCapFourNoStrong

namespace ErdosSzekeres

/-- The uniform four-diagonal decomposable state follows from the whole-set one-change cardinal bound. The lower-gate hypothesis is retained in the approved R21 signature.
@node
@ws C
@kind formalization
@depends ErdosSzekeres.card_le_choose_of_oneChange_no_capFour_no_strong
@dangling-ok Approved R21 uniform (4,k,k) result; the coordinator instantiates this interface with separately reviewed singleton lower gates. -/
theorem decomposableStateUpper_four_diagonal_of_gates (hgate : ∀ k, 5 ≤ k → SingletonLowerPascalTailGate 4 k k) : ∀ k, 5 ≤ k → DecomposableStateUpper 4 k k := by
  classical
  intro k hk n χ s hdecomp hlarge
  by_cases hcap : ContainsCapSet χ s 4
  · exact Or.inl hcap
  by_cases hstrong : ContainsStrongPolygonSet χ s k
  · exact Or.inr (Or.inr hstrong)
  have hbound := card_le_choose_of_oneChange_no_capFour_no_strong
    (by omega : 3 ≤ k) hdecomp.turnSequenceAllowed hcap hstrong
  have hthreshold : decomposableThreshold 4 k k = 1 + Nat.choose (k - 1) 2 := by
    rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
    unfold decomposableBinomialWindow
    have hinterval : Finset.Icc (k - 4) (k - 2) = {k - 4, k - 3, k - 2} := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hinterval, Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp; omega), Finset.sum_singleton]
    have hsymTwo : Nat.choose (k - 2) (k - 4) = Nat.choose (k - 2) 2 := by
      rw [show k - 4 = (k - 2) - 2 by omega]
      exact Nat.choose_symm (by omega)
    have hsymOne : Nat.choose (k - 2) (k - 3) = k - 2 := by
      rw [show k - 3 = (k - 2) - 1 by omega,
        Nat.choose_symm (by omega), Nat.choose_one_right]
    have hpascal : Nat.choose (k - 1) 2 =
        (k - 2) + Nat.choose (k - 2) 2 := by
      rw [show k - 1 = (k - 2) + 1 by omega, Nat.choose_succ_succ']
      simp
    rw [hsymTwo, hsymOne, Nat.choose_self]
    omega
  rw [hthreshold] at hlarge
  omega


end ErdosSzekeres
