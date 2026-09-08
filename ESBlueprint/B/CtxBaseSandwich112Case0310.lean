import ESBlueprint.B.CtxBasePascalCombine

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000

/-- Four-leaf Pascal allocation for the lower outer (1,1,2) sandwich: isolate outer position 3, with second cut upper and last cut lower. Uniform in parent capacities, k, and all admissible couplings, including zero capacities. The explicit four leaf profiles are combined by the checked Pascal rule; this is the numeric component of the corresponding finite cut case.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_112 -/
theorem ctx_base_sandwich_112_case_0310 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      Ctx.Context.baseOf C (min (P - 2) d) k +
        Ctx.Context.baseOf (min (C - 1) (k - 1 - d)) (min (P - 1) e) k +
        Ctx.Context.baseOf (min (C - 2) (min (k - 1 - f) (min (k - 1 - e - 1) (k - 1 - d - 2)))) P k +
        Ctx.Context.baseOf (min (C - 2) (min (k - 1 - e) (k - 1 - d - 1))) (min (P - 1) f) k ≤ Ctx.Context.baseOf C P k := by
  have hcombine := ctx_base_pascal_combine
  clear * - C P k d e f hC hP hd hdk he hek hf hfk hcombine
  let c0 := C
  let p0 := (min (P - 2) d)
  let c1 := (min (C - 1) (k - 1 - d))
  let p1 := (min (P - 1) e)
  let c2 := (min (C - 2) (min (k - 1 - f) (min (k - 1 - e - 1) (k - 1 - d - 2))))
  let p2 := P
  let c3 := (min (C - 2) (min (k - 1 - e) (k - 1 - d - 1)))
  let p3 := (min (P - 1) f)
  change baseOf c0 p0 k + baseOf c1 p1 k + baseOf c2 p2 k + baseOf c3 p3 k ≤ _
  have hc0b : c0 ≤ C := Nat.le_refl _
  have hp0b : p0 ≤ (P - 2) ∧ p0 ≤ d := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.le_refl _)⟩
  have hc1b : c1 ≤ (C - 1) ∧ c1 ≤ (k - 1 - d) := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.le_refl _)⟩
  have hp1b : p1 ≤ (P - 1) ∧ p1 ≤ e := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.le_refl _)⟩
  have hc2b : c2 ≤ (C - 2) ∧ c2 ≤ (k - 1 - f) ∧ c2 ≤ (k - 1 - e - 1) ∧ c2 ≤ (k - 1 - d - 2) := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.min_le_left _ _), (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.min_le_left _ _)), (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.le_refl _)))⟩
  have hp2b : p2 ≤ P := Nat.le_refl _
  have hc3b : c3 ≤ (C - 2) ∧ c3 ≤ (k - 1 - e) ∧ c3 ≤ (k - 1 - d - 1) := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.min_le_left _ _), (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.le_refl _))⟩
  have hp3b : p3 ≤ (P - 1) ∧ p3 ≤ f := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.le_refl _)⟩
  clear_value c0 p0 c1 p1 c2 p2 c3 p3
  by_cases hs0 : C ≤ 1
  · have hz : c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by omega
    obtain ⟨hz0, hz1, hz2⟩ := hz
    have hzero (x : ℕ) : baseOf 0 x k = 0 := by simp [baseOf]
    rw [hz0, hz1, hz2]
    simp only [hzero, Nat.zero_add, Nat.add_zero]
    exact baseOf_mono (by omega) (by omega)
  by_cases hs1 : P ≤ 1
  · have hz : p0 = 0 ∧ p1 = 0 ∧ p3 = 0 := by omega
    obtain ⟨hz0, hz1, hz2⟩ := hz
    have hzero (x : ℕ) : baseOf x 0 k = 0 := by simp [baseOf]
    rw [hz0, hz1, hz2]
    simp only [hzero, Nat.zero_add, Nat.add_zero]
    exact baseOf_mono (by omega) (by omega)
  have hgood : (c2 + p3 ≤ k - 1) ∧ (c1 + p0 ≤ k - 1) ∧ ((max (c2 + 1) c3) + (max p1 (p0 + 1)) ≤ k - 1) ∧ ((max ((max (c2 + 1) c3) + 1) (max (c1 + 1) c0)) ≤ C) ∧ ((max (max p2 (p3 + 1)) ((max p1 (p0 + 1)) + 1)) ≤ P) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]) <;> omega
  obtain ⟨hg0, hg1, hg2, hg3, hg4⟩ := hgood
  have h0 := hcombine c2 p2 c3 p3 (max (c2 + 1) c3) (max p2 (p3 + 1)) k
    (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega) (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) hg0
  have h1 := hcombine c1 p1 c0 p0 (max (c1 + 1) c0) (max p1 (p0 + 1)) k
    (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega) (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) hg1
  have h2 := hcombine (max (c2 + 1) c3) (max p2 (p3 + 1)) (max (c1 + 1) c0) (max p1 (p0 + 1)) (max ((max (c2 + 1) c3) + 1) (max (c1 + 1) c0)) (max (max p2 (p3 + 1)) ((max p1 (p0 + 1)) + 1)) k
    (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega) (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) hg2
  have hroot : baseOf (max ((max (c2 + 1) c3) + 1) (max (c1 + 1) c0)) (max (max p2 (p3 + 1)) ((max p1 (p0 + 1)) + 1)) k ≤ baseOf C P k := baseOf_mono hg3 hg4
  clear * - h0 h1 h2 hroot
  omega

end ErdosSzekeres
