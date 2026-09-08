import ErdosSzekeres.PublishedInductionSemantics
import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A reusable Pascal combination rule for context bases. Two leaves fit below a parent when the left cup and right cap each leave one unit of parent capacity and their cross-sum is at most k-1. Covers zero limits and both classical and active Pascal-window regimes. Iterating this rule supplies the finite capacity allocations in the four-position sandwich proof.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_112 -/
theorem ctx_base_pascal_combine (cl pl cr pr C P k : ℕ)
  (hC : C ≤ k - 1) (hP : P ≤ k - 1)
  (hlC : cl + 1 ≤ C) (hlP : pl ≤ P)
  (hrC : cr ≤ C) (hrP : pr + 1 ≤ P) (hsum : cl + pr ≤ k - 1) :
  Ctx.Context.baseOf cl pl k + Ctx.Context.baseOf cr pr k ≤ Ctx.Context.baseOf C P k := by
  have hbaseSplit : ∀ cl pl k d : ℕ, cl ≤ k - 1 → pl ≤ k - 1 →
      1 ≤ d → d ≤ k - 2 →
      baseOf (min (cl - 1) (k - 1 - d)) pl k +
          baseOf cl (min (pl - 1) d) k ≤ baseOf cl pl k := by
    intro cl pl k d hc hp hd hdk
    by_cases hc0 : cl = 0
    · simp [hc0, baseOf]
    by_cases hp0 : pl = 0
    · simp [hp0, baseOf]
    by_cases hc1 : cl = 1
    · simpa [hc1, baseOf] using
        (baseOf_mono (k := k) (cl := cl) (cl' := cl) (Nat.le_refl cl)
          (Nat.min_le_left (pl - 1) d |>.trans (Nat.sub_le pl 1)))
    by_cases hp1 : pl = 1
    · simpa [hp1, baseOf] using
        (baseOf_mono (k := k)
          (Nat.min_le_left (cl - 1) (k - 1 - d) |>.trans (Nat.sub_le cl 1))
          (pl := pl) (pl' := pl) (Nat.le_refl pl))
    have hce : 2 ≤ cl := by omega
    have hpe : 2 ≤ pl := by omega
    have hmc : 1 ≤ min (cl - 1) (k - 1 - d) := by omega
    have hmp : 1 ≤ min (pl - 1) d := by omega
    have hconvert : ∀ x y : ℕ, 1 ≤ x → 1 ≤ y → x ≤ k - 1 → y ≤ k - 1 →
        baseOf x y k = decomposableThreshold (y + 1) (x + 1) k := by
      intro x y hx hy hxk hyk
      unfold baseOf
      rw [if_neg (by omega)]
      by_cases h : x = 1 ∨ y = 1
      · rw [if_pos h]
        rcases h with rfl | rfl
        · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
          have hrow : y + 1 + (1 + 1) - 4 = y + 1 - 2 := by omega
          rw [hrow, Nat.choose_self]
        · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
          simp
      · rw [if_neg h]
    rw [hconvert _ _ hmc (by omega) (by omega) hp,
      hconvert _ _ (by omega) hmp hc (by omega),
      hconvert _ _ (by omega) (by omega) hc hp]
    by_cases hsmall : (pl + 1) + (cl + 1) ≤ k + 3
    · calc
        decomposableThreshold (pl + 1) (min (cl - 1) (k - 1 - d) + 1) k +
            decomposableThreshold (min (pl - 1) d + 1) (cl + 1) k ≤
            decomposableThreshold (pl + 1) cl k +
              decomposableThreshold pl (cl + 1) k :=
          Nat.add_le_add
            (decomposableThreshold_mono (by omega) (by omega) (by omega) (by omega))
            (decomposableThreshold_mono (by omega) (by omega) (by omega) (by omega))
        _ = decomposableThreshold (pl + 1) (cl + 1) k := by
          rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega),
            decomposableThreshold_eq_choose (by omega) (by omega) (by omega),
            decomposableThreshold_eq_choose (by omega) (by omega) hsmall]
          have hrow₁ : pl + 1 + cl - 4 = pl + cl - 3 := by omega
          have hrow₂ : pl + (cl + 1) - 4 = pl + cl - 3 := by omega
          have hrow : pl + 1 + (cl + 1) - 4 = (pl + cl - 3) + 1 := by omega
          have hcol : pl + 1 - 2 = (pl - 2) + 1 := by omega
          rw [hrow₁, hrow₂, hrow, hcol, Nat.choose_succ_succ]
          simp only [Nat.succ_eq_add_one]
          omega
    · exact published_nonsaturated_next_threshold_pair_le
        (by omega) (by omega) (by omega) (by omega) hmp hmc
        (by omega) (by omega) (by omega) (by omega)
  by_cases hzL : cl = 0 ∨ pl = 0
  · have hzero : baseOf cl pl k = 0 := by simp [baseOf, hzL]
    rw [hzero, Nat.zero_add]
    exact baseOf_mono hrC (by omega)
  by_cases hzR : cr = 0 ∨ pr = 0
  · have hzero : baseOf cr pr k = 0 := by simp [baseOf, hzR]
    rw [hzero, Nat.add_zero]
    exact baseOf_mono (by omega) hlP
  have hd1 : 1 ≤ pr := by omega
  have hdk : pr ≤ k - 2 := by omega
  have hs := hbaseSplit C P k pr hC hP hd1 hdk
  have hleft : baseOf cl pl k ≤ baseOf (min (C - 1) (k - 1 - pr)) P k :=
    baseOf_mono (by omega) hlP
  have hright : baseOf cr pr k ≤ baseOf C (min (P - 1) pr) k :=
    baseOf_mono hrC (by omega)
  exact (Nat.add_le_add hleft hright).trans hs

end ErdosSzekeres
