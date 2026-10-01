import ESBlueprint.B.CtxPartBoundLeTwoOfSameSideNearSaturatedSiblingMaximum
import ESBlueprint.B.CtxBoundLeTwoOfBothSidesNearSaturatedSiblingMaxima

namespace ErdosSzekeres

/-- Every proper recursive part is at most two when one indexed old sibling maximum and the fresh sibling maximum are both at least k-3. Positive actual external labels and an actual omitted source child suffice for either selected axis, arbitrary raw contexts, unused indexed levels and keep lists. Generalizes the checked local κ4 estimate by combining same-side near-saturation with opposite-axis near-saturation in the child part. Includes every fuel bound; asserts no positive lower bound or maximal-segment exchange witness.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_bound_le_two_of_same_side_near_saturated_sibling_maximum, ErdosSzekeres.ctx_bound_le_two_of_both_sides_near_saturated_sibling_maxima
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_part_bound_le_two_of_near_saturated_old_and_fresh_maxima (σ : Ctx.Context) (hpositive : ∀ x j v, σ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j) (N : ℕ) (hN : N ∈ σ.levels) (hmaximum : σ.k - 3 ≤ σ.maximumAt N) (keep : List ℕ) (v : Ctx.Side) (m r : ℕ) (hfresh : σ.k - 3 ≤ m) (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep) : (∀ fuel, Ctx.Context.boundFuel fuel (σ.part keep v m) ≤ 2) ∧ (σ.part keep v m).bound ≤ 2 := by
  classical
  let s := σ.sideAt N
  have hNOn : N ∈ σ.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hN, by simp [s]⟩
  have hNpos : 1 ≤ N := (Ctx.Context.one_le_of_mem_levelsOn hNOn).1
  by_cases hv : v = s
  · subst v
    exact ctx_part_bound_le_two_of_same_side_near_saturated_sibling_maximum
      σ hpositive s N hNOn hmaximum keep m r hr hremoved
  · let ρ := σ.part keep v m
    have hPos : ∀ x j w, ρ.letterAt x = Ctx.Letter.ext j w → 1 ≤ j :=
      ctx_part_positive_letters σ keep v m
    have hOne : 1 ∈ ρ.levels := by
      rw [Ctx.Context.part_levels]
      simp
    have hrnew : r ∈ ρ.extPositions 1 := by
      rw [Ctx.Context.part_extPositions_one hpositive keep v m]
      exact List.mem_filter.mpr ⟨hr, by simpa using hremoved⟩
    have hFreshSide : ρ.sideAt 1 = v :=
      Ctx.Context.part_sideAt_one_of_mem hpositive keep v m hrnew
    have hFreshOn : 1 ∈ ρ.levelsOn v 0 :=
      List.mem_filter.mpr ⟨hOne, by simp [hFreshSide]⟩
    have hFreshMax : ρ.maximumAt 1 = m :=
      Ctx.Context.part_maximumAt_one σ keep v m
    have hFreshNear : ρ.k - 3 ≤ ρ.maximumAt 1 := by
      rw [hFreshMax]
      change σ.k - 3 ≤ m
      exact hfresh
    have hOldLevel : N + 1 ∈ ρ.levels := by
      rw [Ctx.Context.part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
    have hOldSide : ρ.sideAt (N + 1) = s :=
      Ctx.Context.part_sideAt_succ σ keep v m hNpos
    have hOldOn : N + 1 ∈ ρ.levelsOn s 0 :=
      List.mem_filter.mpr ⟨hOldLevel, by simp [hOldSide]⟩
    have hOldMax : ρ.maximumAt (N + 1) = σ.maximumAt N :=
      Ctx.Context.part_maximumAt_succ σ keep v m hNpos
    have hOldNear : ρ.k - 3 ≤ ρ.maximumAt (N + 1) := by
      rw [hOldMax]
      exact hmaximum
    cases hs : s <;> cases v
    · exact (hv hs.symm).elim
    · have hOldOn' : N + 1 ∈ ρ.levelsOn .lower 0 := by
        simpa only [hs] using hOldOn
      exact ctx_bound_le_two_of_both_sides_near_saturated_sibling_maxima
        ρ hPos (N + 1) 1 hOldOn' hFreshOn hOldNear hFreshNear
    · have hOldOn' : N + 1 ∈ ρ.levelsOn .upper 0 := by
        simpa only [hs] using hOldOn
      exact ctx_bound_le_two_of_both_sides_near_saturated_sibling_maxima
        ρ hPos 1 (N + 1) hFreshOn hOldOn' hFreshNear hOldNear
    · exact (hv hs.symm).elim

end ErdosSzekeres
