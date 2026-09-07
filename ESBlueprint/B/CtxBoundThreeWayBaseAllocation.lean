import ESBlueprint.B.CtxBoundAdditivePrefixSuffix

namespace ErdosSzekeres

open Ctx Ctx.Context

set_option maxHeartbeats 1600000

/-- Two three-term threshold allocations for a sandwich with singleton outer children. Nested two-part allocations, with an adjusted intermediate coupling, bound both orientations for arbitrary natural limits and all admissible couplings. Includes zero limits and endpoint couplings. This is the reusable arithmetic component; the context extension inequalities remain a separate obligation.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_bound_three_way_base_allocation (cl pl k d e : ℕ) (hc : cl ≤ k - 1) (hp : pl ≤ k - 1)
  (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2) :
  let B := Ctx.Context.baseOf
  (B (min (min (cl - 1) (k - 1 - e)) (k - 2 - d)) pl k +
    B (min (cl - 1) (k - 1 - d)) (min (pl - 1) e) k +
    B cl (min (pl - 2) d) k ≤ B cl pl k) ∧
  (B cl (min (min (pl - 1) e) (d - 1)) k +
    B (min (cl - 1) (k - 1 - e)) (min (pl - 1) d) k +
    B (min (cl - 2) (k - 1 - d)) pl k ≤ B cl pl k) := by
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
  -- Requires the existing local hbaseSplit from CtxBoundAdditivePrefixSuffix.
  have hthreeBase : ∀ cl pl k d e : ℕ, cl ≤ k - 1 → pl ≤ k - 1 →
      1 ≤ d → d ≤ k - 2 → 1 ≤ e → e ≤ k - 2 →
      baseOf (min (min (cl - 1) (k - 1 - e)) (k - 2 - d)) pl k +
          baseOf (min (cl - 1) (k - 1 - d)) (min (pl - 1) e) k +
          baseOf cl (min (pl - 2) d) k ≤ baseOf cl pl k := by
    intro cl pl k d e hc hp hd hdk he hek
    by_cases htop : d = k - 2
    · have hzero : baseOf (min (min (cl - 1) (k - 1 - e)) (k - 2 - d)) pl k = 0 := by
        simp [htop, baseOf]
      rw [hzero, Nat.zero_add]
      have hB : baseOf (min (cl - 1) (k - 1 - d)) (min (pl - 1) e) k ≤
          baseOf (min (cl - 1) (k - 1 - d)) pl k :=
        baseOf_mono (Nat.le_refl _) (by omega)
      have hC : baseOf cl (min (pl - 2) d) k ≤ baseOf cl (min (pl - 1) d) k :=
        baseOf_mono (Nat.le_refl _) (by omega)
      exact (Nat.add_le_add hB hC).trans (hbaseSplit cl pl k d hc hp hd hdk)
    · let E := max e (d + 1)
      let P := min (pl - 1) E
      have hEe : e ≤ E := Nat.le_max_left _ _
      have hEd : d + 1 ≤ E := Nat.le_max_right _ _
      have hEk : E ≤ k - 2 := by dsimp [E]; omega
      have hP : P ≤ k - 1 := by dsimp [P]; omega
      have hA : baseOf (min (min (cl - 1) (k - 1 - e)) (k - 2 - d)) pl k ≤
          baseOf (min (cl - 1) (k - 1 - E)) pl k :=
        baseOf_mono (by dsimp [E]; omega) (Nat.le_refl _)
      have hB : baseOf (min (cl - 1) (k - 1 - d)) (min (pl - 1) e) k ≤
          baseOf (min (cl - 1) (k - 1 - d)) P k :=
        baseOf_mono (Nat.le_refl _) (by dsimp [P]; omega)
      have hC : baseOf cl (min (pl - 2) d) k ≤
          baseOf cl (min (P - 1) d) k :=
        baseOf_mono (Nat.le_refl _) (by dsimp [P]; omega)
      have hinner := hbaseSplit cl P k d hc hP hd hdk
      have houter := hbaseSplit cl pl k E hc hp (by omega) hEk
      calc
        _ ≤ baseOf (min (cl - 1) (k - 1 - E)) pl k +
            (baseOf (min (cl - 1) (k - 1 - d)) P k +
              baseOf cl (min (P - 1) d) k) := by
          simpa only [Nat.add_assoc] using Nat.add_le_add (Nat.add_le_add hA hB) hC
        _ ≤ baseOf (min (cl - 1) (k - 1 - E)) pl k + baseOf cl P k :=
          Nat.add_le_add_left hinner _
        _ ≤ baseOf cl pl k := houter
  -- Direct dual argument; no threshold-symmetry import required.
  have hthreeBaseDual : ∀ cl pl k d e : ℕ, cl ≤ k - 1 → pl ≤ k - 1 →
      1 ≤ d → d ≤ k - 2 → 1 ≤ e → e ≤ k - 2 →
      baseOf cl (min (min (pl - 1) e) (d - 1)) k +
          baseOf (min (cl - 1) (k - 1 - e)) (min (pl - 1) d) k +
          baseOf (min (cl - 2) (k - 1 - d)) pl k ≤ baseOf cl pl k := by
    intro cl pl k d e hc hp hd hdk he hek
    by_cases hbot : d = 1
    · have hzero : baseOf cl (min (min (pl - 1) e) (d - 1)) k = 0 := by
        simp [hbot, baseOf]
      rw [hzero, Nat.zero_add]
      have hB : baseOf (min (cl - 1) (k - 1 - e)) (min (pl - 1) d) k ≤
          baseOf cl (min (pl - 1) d) k :=
        baseOf_mono (by omega) (Nat.le_refl _)
      have hC : baseOf (min (cl - 2) (k - 1 - d)) pl k ≤
          baseOf (min (cl - 1) (k - 1 - d)) pl k :=
        baseOf_mono (by omega) (Nat.le_refl _)
      have hsum := (Nat.add_le_add hC hB).trans (hbaseSplit cl pl k d hc hp hd hdk)
      omega
    · let E := min e (d - 1)
      let P := min (cl - 1) (k - 1 - E)
      have hEe : E ≤ e := Nat.min_le_left _ _
      have hEd : E ≤ d - 1 := Nat.min_le_right _ _
      have hE1 : 1 ≤ E := by dsimp [E]; omega
      have hEk : E ≤ k - 2 := by omega
      have hP : P ≤ k - 1 := by dsimp [P]; omega
      have hA : baseOf cl (min (min (pl - 1) e) (d - 1)) k ≤
          baseOf cl (min (pl - 1) E) k :=
        baseOf_mono (Nat.le_refl _) (by dsimp [E]; omega)
      have hB : baseOf (min (cl - 1) (k - 1 - e)) (min (pl - 1) d) k ≤
          baseOf P (min (pl - 1) d) k :=
        baseOf_mono (by dsimp [P]; omega) (Nat.le_refl _)
      have hC : baseOf (min (cl - 2) (k - 1 - d)) pl k ≤
          baseOf (min (P - 1) (k - 1 - d)) pl k :=
        baseOf_mono (by dsimp [P]; omega) (Nat.le_refl _)
      have hinner := hbaseSplit P pl k d hP hp hd hdk
      have houter := hbaseSplit cl pl k E hc hp hE1 hEk
      have hCB := (Nat.add_le_add hC hB).trans hinner
      have hsum := (Nat.add_le_add hCB hA).trans houter
      omega
  exact ⟨hthreeBase cl pl k d e hc hp hd hdk he hek,
    hthreeBaseDual cl pl k d e hc hp hd hdk he hek⟩

end ErdosSzekeres
