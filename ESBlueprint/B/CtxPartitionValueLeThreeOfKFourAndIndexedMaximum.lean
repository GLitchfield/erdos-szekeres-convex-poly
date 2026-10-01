import ESBlueprint.B.CtxPartBoundLeTwoOfSameSideNearSaturatedSiblingMaximum
import ESBlueprint.B.CtxBoundLeTwoOfBothSidesNearSaturatedSiblingMaxima
import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum

namespace ErdosSzekeres

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- At k=4 both orientations of every nonempty proper child partition have value at most three when the raw positive context has one indexed sibling maximum at least one. Kept and omitted source-child witnesses express properness; keep lists may contain duplicates. Every proper part is at most two by same-side near-saturation or opposite-axis near-saturation, and legal coupling gives new maxima one and two, so the maximum-two part is at most one. No well-formedness, run-count, interleaving, global-width or history-length premise. Supplies the unbounded k=4 upper estimate for maximal-segment exchange; no flip lower witness is asserted.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_bound_le_two_of_same_side_near_saturated_sibling_maximum, ErdosSzekeres.ctx_bound_le_two_of_both_sides_near_saturated_sibling_maxima, ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_partition_value_le_three_of_k_four_and_indexed_maximum (σ : Ctx.Context)
  (hpositive : ∀ x j v, σ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j)
  (hk : σ.k = 4) (N : ℕ) (hN : N ∈ σ.levels)
  (hmaximum : 1 ≤ σ.maximumAt N)
  (keep : List ℕ) (p r : ℕ)
  (hp : p ∈ σ.childPositions) (hkept : p ∈ keep)
  (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep)
  (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) :
  (σ.part keep Ctx.Side.lower d).bound +
    (σ.part (σ.childPositions.filter (· ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ 3 ∧
  (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound +
    (σ.part (σ.childPositions.filter (· ∉ keep)) Ctx.Side.lower d).bound ≤ 3 := by
  classical
  let s := σ.sideAt N
  have hNOn : N ∈ σ.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hN, by simp [s]⟩
  have hNpos : 1 ≤ N := (Ctx.Context.one_le_of_mem_levelsOn hNOn).1
  have hNear : σ.k - 3 ≤ σ.maximumAt N := by omega
  have hTwo (K : List ℕ) (v : Ctx.Side) (m q : ℕ)
      (hm : 1 ≤ m) (hq : q ∈ σ.childPositions) (hqremoved : q ∉ K) :
      (σ.part K v m).bound ≤ 2 := by
    by_cases hv : v = s
    · subst v
      exact (ctx_part_bound_le_two_of_same_side_near_saturated_sibling_maximum
        σ hpositive s N hNOn hNear K m q hq hqremoved).2
    · let ρ := σ.part K v m
      have hPos : ∀ x j w, ρ.letterAt x = Ctx.Letter.ext j w → 1 ≤ j :=
        ctx_part_positive_letters σ K v m
      have hOne : 1 ∈ ρ.levels := by
        rw [Ctx.Context.part_levels]
        simp
      have hqnew : q ∈ ρ.extPositions 1 := by
        rw [Ctx.Context.part_extPositions_one hpositive K v m]
        exact List.mem_filter.mpr ⟨hq, by simpa using hqremoved⟩
      have hFreshSide : ρ.sideAt 1 = v :=
        Ctx.Context.part_sideAt_one_of_mem hpositive K v m hqnew
      have hFreshOn : 1 ∈ ρ.levelsOn v 0 :=
        List.mem_filter.mpr ⟨hOne, by simp [hFreshSide]⟩
      have hFreshMax : ρ.maximumAt 1 = m :=
        Ctx.Context.part_maximumAt_one σ K v m
      have hFreshNear : ρ.k - 3 ≤ ρ.maximumAt 1 := by
        rw [hFreshMax]
        change σ.k - 3 ≤ m
        omega
      have hOldLevel : N + 1 ∈ ρ.levels := by
        rw [Ctx.Context.part_levels]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
      have hOldSide : ρ.sideAt (N + 1) = s :=
        Ctx.Context.part_sideAt_succ σ K v m hNpos
      have hOldOn : N + 1 ∈ ρ.levelsOn s 0 :=
        List.mem_filter.mpr ⟨hOldLevel, by simp [hOldSide]⟩
      have hOldMax : ρ.maximumAt (N + 1) = σ.maximumAt N :=
        Ctx.Context.part_maximumAt_succ σ K v m hNpos
      have hOldNear : ρ.k - 3 ≤ ρ.maximumAt (N + 1) := by
        rw [hOldMax]
        exact hNear
      cases hs : s <;> cases v
      · exact (hv hs.symm).elim
      · have hOldOn' : N + 1 ∈ ρ.levelsOn .lower 0 := by
          simpa only [hs] using hOldOn
        exact (ctx_bound_le_two_of_both_sides_near_saturated_sibling_maxima
          ρ hPos (N + 1) 1 hOldOn' hFreshOn hOldNear hFreshNear).2
      · have hOldOn' : N + 1 ∈ ρ.levelsOn .upper 0 := by
          simpa only [hs] using hOldOn
        exact (ctx_bound_le_two_of_both_sides_near_saturated_sibling_maxima
          ρ hPos 1 (N + 1) hFreshOn hOldOn' hFreshNear hOldNear).2
      · exact (hv hs.symm).elim
  have hOne (K : List ℕ) (v : Ctx.Side) :
      (σ.part K v 2).bound ≤ 1 := by
    let ρ := σ.part K v 2
    have hPos : ∀ x j w, ρ.letterAt x = Ctx.Letter.ext j w → 1 ≤ j :=
      ctx_part_positive_letters σ K v 2
    have hLevel : 1 ∈ ρ.levels := by
      rw [Ctx.Context.part_levels]
      simp
    have hMaximum : ρ.k - 2 ≤ ρ.maximumAt 1 := by
      rw [Ctx.Context.part_maximumAt_one σ K v 2]
      change σ.k - 2 ≤ 2
      omega
    exact (ctx_bound_le_one_of_large_sibling_maximum ρ hPos 1 hLevel hMaximum).2
  let rest := σ.childPositions.filter (· ∉ keep)
  have hpnotrest : p ∉ rest := by simp [rest, hkept]
  change (σ.part keep Ctx.Side.lower d).bound +
      (σ.part rest Ctx.Side.upper (σ.k - 1 - d)).bound ≤ 3 ∧
    (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound +
      (σ.part rest Ctx.Side.lower d).bound ≤ 3
  have hdCases : d = 1 ∨ d = 2 := by omega
  rcases hdCases with hdOne | hdTwo
  · subst d
    have hOther : σ.k - 1 - 1 = 2 := by omega
    rw [hOther]
    have hKL := hTwo keep .lower 1 r (by omega) hr hremoved
    have hRL := hTwo rest .lower 1 p (by omega) hp hpnotrest
    have hKU := hOne keep .upper
    have hRU := hOne rest .upper
    exact ⟨Nat.add_le_add hKL hRU, Nat.add_le_add hKU hRL⟩
  · subst d
    have hOther : σ.k - 1 - 2 = 1 := by omega
    rw [hOther]
    have hKU := hTwo keep .upper 1 r (by omega) hr hremoved
    have hRU := hTwo rest .upper 1 p (by omega) hp hpnotrest
    have hKL := hOne keep .lower
    have hRL := hOne rest .lower
    exact ⟨Nat.add_le_add hKL hRU, Nat.add_le_add hKU hRL⟩

end ErdosSzekeres
