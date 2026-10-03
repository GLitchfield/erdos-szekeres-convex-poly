import ErdosSzekeres.Decomposable

namespace ErdosSzekeres

/-- At every k at least seven the six predecessor-predecessor Pascal window equals its lower tail plus the audited two-side cubic bound, with all three window terms untruncated.
@node
@ws B
@kind formalization
@dangling-ok R23 six singleton gate reservoir arithmetic -/
theorem decomposableThreshold_six_pred_pred_of_seven_le {k : ℕ} (hk : 7 ≤ k) : decomposableThreshold 6 (k - 2) k = Nat.choose (k - 3) 4 + Nat.choose (k - 1) 3 + Nat.choose (k - 3) 3 := by
  rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
  unfold decomposableBinomialWindow
  have harg : k - 2 - 2 = k - 4 := by omega
  rw [harg]
  have hsum : (∑ j ∈ Finset.Icc (k - 6) (k - 4), Nat.choose (k - 2) j) =
      Nat.choose (k - 2) 4 + Nat.choose (k - 2) 3 + Nat.choose (k - 2) 2 := by
    have htop : k - 4 = k - 6 + 1 + 1 := by omega
    rw [htop, Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega)]
    simp only [Finset.Icc_self, Finset.sum_singleton]
    rw [Nat.choose_symm_of_eq_add (by omega : k - 2 = (k - 6) + 4),
      Nat.choose_symm_of_eq_add (by omega : k - 2 = (k - 6 + 1) + 3),
      Nat.choose_symm_of_eq_add (by omega : k - 2 = (k - 6 + 1 + 1) + 2)]
  rw [hsum]
  have hp4 : Nat.choose (k - 2) 4 =
      Nat.choose (k - 3) 3 + Nat.choose (k - 3) 4 := by
    simpa only [show k - 3 + 1 = k - 2 by omega] using Nat.choose_succ_succ' (k - 3) 3
  have hp3 : Nat.choose (k - 1) 3 =
      Nat.choose (k - 2) 2 + Nat.choose (k - 2) 3 := by
    simpa only [show k - 2 + 1 = k - 1 by omega] using Nat.choose_succ_succ' (k - 2) 2
  omega

end ErdosSzekeres
