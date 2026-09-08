import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

open Ctx Ctx.Context

set_option maxHeartbeats 2000000

/-- Ordered unit transfer for context base values: with equal initial cup limit c, moving one extra cup unit from a leaf with cap limit p to a leaf with cap limit P at least p cannot decrease their sum. Includes zero limits and the transition from the classical binomial regime to the active Pascal window. This is an explicit compensation rule for the strip-exchange workstream; its cap-order hypothesis must be established at application sites.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_attained_by_end_cut -/
theorem ctx_base_unit_transfer (c p P k : ℕ) (hp : p ≤ P) (hP : P ≤ k - 1) (hc : c + 1 ≤ k - 1) :
  Ctx.Context.baseOf (c + 1) p k + Ctx.Context.baseOf c P k ≤
    Ctx.Context.baseOf c p k + Ctx.Context.baseOf (c + 1) P k := by
  -- At the interface the Pascal window has two terms, whose sum is the classical value.
  have hWindow : ∀ a u k : ℕ, 2 ≤ a → 2 ≤ u → a ≤ k → k + 3 ≤ a + u →
      decomposableThreshold a u k = decomposableBinomialWindow a u k := by
    intro a u k ha hu hak hactive
    by_cases hdeep : k + 4 ≤ a + u
    · exact decomposableThreshold_eq_window ha hu hdeep
    · have heq : a + u = k + 3 := by omega
      have hu3 : 3 ≤ u := by omega
      have hrow : a + u - 4 = k - 1 := by omega
      have hI : Finset.Icc (k - a) (u - 2) = {u - 3, u - 2} := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [decomposableThreshold_eq_choose ha hu (by omega)]
      unfold decomposableBinomialWindow
      rw [hI, Finset.sum_pair (show u - 3 ≠ u - 2 by omega), hrow]
      have hpascal := Nat.choose_succ_succ' (k - 2) (u - 3)
      have hkrow : k - 2 + 1 = k - 1 := by omega
      have hucol : u - 3 + 1 = u - 2 := by omega
      rw [hkrow, hucol] at hpascal
      rw [← hpascal]
      exact Nat.choose_symm_of_eq_add (by omega)
  have hWindowStep : ∀ a u k : ℕ, 2 ≤ u → k - a ≤ u - 1 →
      decomposableBinomialWindow a (u + 1) k =
        decomposableBinomialWindow a u k + Nat.choose (k - 2) (u - 1) := by
    intro a u k hu hlo
    have hI : Finset.Icc (k - a) (u + 1 - 2) =
        insert (u - 1) (Finset.Icc (k - a) (u - 2)) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : u - 1 ∉ Finset.Icc (k - a) (u - 2) := by
      simp only [Finset.mem_Icc]
      omega
    unfold decomposableBinomialWindow
    rw [hI, Finset.sum_insert hnot]
    omega
  -- An increment in the cup parameter is one coefficient in a capped Pascal row.
  have hIncrement : ∀ a u k : ℕ, 2 ≤ a → 2 ≤ u → a ≤ k → u + 1 ≤ k →
      decomposableThreshold a (u + 1) k = decomposableThreshold a u k +
        Nat.choose (min (a + u - 4) (k - 2)) (u - 1) := by
    intro a u k ha hu hak huk
    by_cases hclass : a + u ≤ k + 2
    · rw [decomposableThreshold_eq_choose ha (by omega) (by omega),
        decomposableThreshold_eq_choose ha hu (by omega),
        Nat.min_eq_left (show a + u - 4 ≤ k - 2 by omega)]
      have hsym₀ : Nat.choose (a + u - 4) (a - 2) = Nat.choose (a + u - 4) (u - 2) :=
        Nat.choose_symm_of_eq_add (by omega)
      have hsym₁ : Nat.choose (a + (u + 1) - 4) (a - 2) =
          Nat.choose (a + (u + 1) - 4) (u - 1) := Nat.choose_symm_of_eq_add (by omega)
      rw [hsym₀, hsym₁]
      have hrow : a + (u + 1) - 4 = (a + u - 4) + 1 := by omega
      have hcol : u - 1 = (u - 2) + 1 := by omega
      rw [hrow, hcol, Nat.choose_succ_succ']
    · rw [hWindow a (u + 1) k ha (by omega) hak (by omega),
        hWindow a u k ha hu hak (by omega),
        Nat.min_eq_right (show k - 2 ≤ a + u - 4 by omega),
        hWindowStep a u k hu (by omega)]
  have hConvert : ∀ x y k : ℕ, 1 ≤ x → 1 ≤ y → x ≤ k - 1 → y ≤ k - 1 →
      baseOf x y k = decomposableThreshold (y + 1) (x + 1) k := by
    intro x y k hx hy hxk hyk
    unfold baseOf
    rw [if_neg (by omega)]
    by_cases h : x = 1 ∨ y = 1
    · rw [if_pos h]
      rcases h with rfl | rfl
      · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
        have he : y + 1 + (1 + 1) - 4 = y + 1 - 2 := by omega
        rw [he, Nat.choose_self]
      · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
        simp
    · rw [if_neg h]
  by_cases hp0 : p = 0
  · have hz : ∀ x, baseOf x 0 k = 0 := by intro x; simp [baseOf]
    rw [hp0, hz, hz, Nat.zero_add, Nat.zero_add]
    exact baseOf_mono (by omega) le_rfl
  have hp1 : 1 ≤ p := by omega
  have hP1 : 1 ≤ P := by omega
  by_cases hc0 : c = 0
  · simp [hc0, baseOf, Nat.ne_of_gt hp1, Nat.ne_of_gt hP1]
  have hc1 : 1 ≤ c := by omega
  rw [hConvert (c + 1) p k (by omega) hp1 (by omega) (by omega),
    hConvert c P k hc1 hP1 (by omega) hP,
    hConvert c p k hc1 hp1 (by omega) (by omega),
    hConvert (c + 1) P k (by omega) hP1 (by omega) hP]
  rw [hIncrement (p + 1) (c + 1) k (by omega) (by omega) (by omega) (by omega),
    hIncrement (P + 1) (c + 1) k (by omega) (by omega) (by omega) (by omega)]
  have hdelta : Nat.choose (min (p + 1 + (c + 1) - 4) (k - 2)) (c + 1 - 1) ≤
      Nat.choose (min (P + 1 + (c + 1) - 4) (k - 2)) (c + 1 - 1) :=
    Nat.choose_le_choose _ (by omega)
  omega

end ErdosSzekeres
