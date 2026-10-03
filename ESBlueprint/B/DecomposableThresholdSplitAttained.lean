import ErdosSzekeres.Decomposable

namespace ErdosSzekeres

/-- The decomposable threshold is attained by splitting into adjacent singletons at the explicit coupling d=a-2, in both the classical and active Pascal-window regimes. Together with the universal split upper bound this proves exact splitting. @node
@node
@ws B
@kind formalization
@dangling-ok R19 splitting tool for all-context singleton attainment PEEL; companion upper inequality will establish the max identity -/
theorem decomposableThreshold_split_attained (a u k : ℕ) (ha : 3 ≤ a) (hu : 3 ≤ u) (hak : a ≤ k) (huk : u ≤ k) : ∃ d : ℕ, 1 ≤ d ∧ d ≤ k - 2 ∧ d = a - 2 ∧ decomposableThreshold a (min (u - 1) (k - d)) k + decomposableThreshold (min (a - 1) (d + 1)) u k = decomposableThreshold a u k := by
  classical
  have hWindow : ∀ x y k : ℕ, 2 ≤ x → 2 ≤ y → x ≤ k → y ≤ k →
      k + 2 ≤ x + y →
      decomposableThreshold x y k = decomposableBinomialWindow x y k := by
    intro x y k hx hy hxk hyk hsum
    by_cases hdeep : k + 4 ≤ x + y
    · exact decomposableThreshold_eq_window hx hy hdeep
    by_cases heq : x + y = k + 2
    · have hI : Finset.Icc (k - x) (y - 2) = {k - x} := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_singleton]
        omega
      rw [decomposableThreshold_eq_choose hx hy (by omega)]
      unfold decomposableBinomialWindow
      rw [hI, Finset.sum_singleton, show x + y - 4 = k - 2 by omega]
      exact Nat.choose_symm_of_eq_add (by omega)
    · have hI : Finset.Icc (k - x) (y - 2) = {k - x, k - x + 1} := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [decomposableThreshold_eq_choose hx hy (by omega)]
      unfold decomposableBinomialWindow
      rw [hI, Finset.sum_pair (show k - x ≠ k - x + 1 by omega),
        show x + y - 4 = k - 1 by omega]
      have hpas := Nat.choose_succ_succ' (k - 2) (k - x)
      rw [show k - 2 + 1 = k - 1 by omega] at hpas
      rw [← hpas]
      exact Nat.choose_symm_of_eq_add (by omega)
  refine ⟨a - 2, by omega, by omega, rfl, ?_⟩
  rw [Nat.min_eq_left (show a - 1 ≤ (a - 2) + 1 by omega)]
  by_cases hclass : a + u ≤ k + 3
  · rw [Nat.min_eq_left (show u - 1 ≤ k - (a - 2) by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) hclass]
    rw [show a + (u - 1) - 4 = a + u - 5 by omega,
      show a - 1 + u - 4 = a + u - 5 by omega,
      show a + u - 4 = (a + u - 5) + 1 by omega,
      show a - 2 = (a - 3) + 1 by omega,
      show a - 1 - 2 = a - 3 by omega, Nat.choose_succ_succ]
    simp only [Nat.succ_eq_add_one]
    omega
  · rw [Nat.min_eq_right (show k - (a - 2) ≤ u - 1 by omega),
      hWindow a (k - (a - 2)) k (by omega) (by omega) hak (by omega) (by omega),
      hWindow (a - 1) u k (by omega) (by omega) (by omega) huk (by omega),
      decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
    have hI : Finset.Icc (k - a) (k - (a - 2) - 2) = {k - a} := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_singleton]
      omega
    have hOuter : Finset.Icc (k - a) (u - 2) =
        insert (k - a) (Finset.Icc (k - (a - 1)) (u - 2)) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hNot : k - a ∉ Finset.Icc (k - (a - 1)) (u - 2) := by
      simp only [Finset.mem_Icc]
      omega
    unfold decomposableBinomialWindow
    rw [hI, hOuter, Finset.sum_singleton, Finset.sum_insert hNot]


end ErdosSzekeres
