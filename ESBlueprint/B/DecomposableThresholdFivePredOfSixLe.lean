import ErdosSzekeres.Decomposable

namespace ErdosSzekeres

/-- The five predecessor Pascal window expands into the cap tail and the two triangular terms used by the audited singleton gate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem decomposableThreshold_five_pred_of_six_le {k : ℕ} (hk : 6 ≤ k) : decomposableThreshold 5 (k - 1) k = Nat.choose (k - 3) 3 + Nat.choose (k - 1) 2 + Nat.choose (k - 3) 2 := by
  rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
  unfold decomposableBinomialWindow
  have harg : k - 1 - 2 = k - 3 := by omega
  rw [harg]
  have hsum : (∑ j ∈ Finset.Icc (k - 5) (k - 3), Nat.choose (k - 2) j) =
      Nat.choose (k - 2) 3 + Nat.choose (k - 2) 2 + (k - 2) := by
    have htop : k - 3 = k - 5 + 1 + 1 := by omega
    rw [htop, Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega)]
    simp only [Finset.Icc_self, Finset.sum_singleton]
    rw [Nat.choose_symm_of_eq_add (by omega : k - 2 = (k - 5) + 3),
      Nat.choose_symm_of_eq_add (by omega : k - 2 = (k - 5 + 1) + 2),
      Nat.choose_symm_of_eq_add (by omega : k - 2 = (k - 5 + 1 + 1) + 1)]
    simp only [Nat.choose_one_right]
  rw [hsum]
  have hp3 : Nat.choose (k - 2) 3 = Nat.choose (k - 3) 2 + Nat.choose (k - 3) 3 := by
    simpa only [show k - 3 + 1 = k - 2 by omega] using Nat.choose_succ_succ' (k - 3) 2
  have hp2 : Nat.choose (k - 1) 2 = (k - 2) + Nat.choose (k - 2) 2 := by
    simpa only [Nat.choose_one_right, show k - 2 + 1 = k - 1 by omega] using
      Nat.choose_succ_succ' (k - 2) 1
  omega

end ErdosSzekeres
