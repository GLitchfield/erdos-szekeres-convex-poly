import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Exact capacity-aware Pascal decomposition of the three-parameter threshold for legal globals: decreasing the cap parameter by one leaves a second term whose cup parameter is capped at min(u-1,k-a+2). Covers both the inactive binomial regime and the active binomial-window regime, including their boundary. Supplies the arithmetic identity for constructing an exposed-end singleton cut from marked-root point potentials.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem decomposableThreshold_capacity_pascal_left (a u k : ℕ) (ha : 3 ≤ a) (hak : a ≤ k) (hu : 2 ≤ u) (huk : u ≤ k) :
  decomposableThreshold a u k = decomposableThreshold (a - 1) u k +
    decomposableThreshold a (min (u - 1) (k - a + 2)) k := by
  classical
  have hSplit (lo hi : ℕ) (h : lo ≤ hi) (f : ℕ → ℕ) :
      (∑ j ∈ Finset.Icc lo hi, f j) =
        f lo + ∑ j ∈ Finset.Icc (lo + 1) hi, f j := by
    have hI : Finset.Icc lo hi = insert lo (Finset.Icc (lo + 1) hi) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hI, Finset.sum_insert (by simp [Finset.mem_Icc])]
  have hBoundary (x y : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
      (hxk : x ≤ k) (hyk : y ≤ k) (hxy : x + y = k + 3) :
      decomposableThreshold x y k = decomposableBinomialWindow x y k := by
    rw [decomposableThreshold_eq_choose hx hy (by omega)]
    have htop : x + y - 4 = k - 1 := by omega
    have hsym : Nat.choose (k - 1) (x - 2) =
        Nat.choose (k - 1) (k - x + 1) :=
      Nat.choose_symm_of_eq_add (by omega)
    have hrow : k - 1 = (k - 2) + 1 := by omega
    have hcol : k - x + 1 = (k - x) + 1 := by omega
    have hhi : y - 2 = (k - x) + 1 := by omega
    rw [htop, hsym, hrow, hcol, Nat.choose_succ_succ']
    unfold decomposableBinomialWindow
    rw [hSplit (k - x) (y - 2) (by omega), hhi]
    simp
  by_cases hu2 : u = 2
  · subst u
    have hmin : min (2 - 1) (k - a + 2) = 1 := by omega
    rw [hmin, decomposableThreshold_one_right]
    rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    simp
  · have hu3 : 3 ≤ u := by omega
    by_cases hbase : a + u ≤ k + 3
    · have hmin : min (u - 1) (k - a + 2) = u - 1 := by omega
      rw [hmin, decomposableThreshold_eq_choose (by omega) hu hbase,
        decomposableThreshold_eq_choose (by omega) hu (by omega),
        decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
      have htop : a + u - 4 = (a + u - 5) + 1 := by omega
      have hidx : a - 2 = (a - 3) + 1 := by omega
      rw [htop, hidx, Nat.choose_succ_succ']
      congr 1 <;> congr 1 <;> omega
    · have hactive : k + 4 ≤ a + u := by omega
      have hmin : min (u - 1) (k - a + 2) = k - a + 2 := by omega
      have hLeaf : decomposableThreshold (a - 1) u k =
          decomposableBinomialWindow (a - 1) u k := by
        by_cases hmore : k + 4 ≤ (a - 1) + u
        · exact decomposableThreshold_eq_window (by omega) hu hmore
        · exact hBoundary (a - 1) u (by omega) hu (by omega) huk (by omega)
      have hSecond : decomposableThreshold a (k - a + 2) k =
          Nat.choose (k - 2) (k - a) := by
        rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
        have htop : a + (k - a + 2) - 4 = k - 2 := by omega
        rw [htop]
        exact Nat.choose_symm_of_eq_add (by omega)
      rw [hmin, decomposableThreshold_eq_window (by omega) hu hactive,
        hLeaf, hSecond]
      unfold decomposableBinomialWindow
      have hlo : k - (a - 1) = (k - a) + 1 := by omega
      rw [hlo, hSplit (k - a) (u - 2) (by omega)]
      omega

end ErdosSzekeres
