import ESBlueprint.B.CtxBoundLeTwoOfSmallGlobalAxisWithIndexedMarker
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize
import ESBlueprint.B.CtxPartPositiveLetters

namespace ErdosSzekeres

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A proper recursive part on the side of an indexed sibling maximum at least k-3 has every fuel approximation and full context bound at most two. A removed source child gives an actual fresh indexed level-one marker, which survives upper normalization at the shifted old maximum. Positive actual external labels suffice for arbitrary raw contexts, keep lists, histories and new maximum m, with no well-formedness, run-count or legal-coupling hypothesis. This is the near-saturation companion to the k-2 zero theorem.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_two_of_small_global_axis_with_indexed_marker, ErdosSzekeres.ctx_sibling_maximum_upper_normalize, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_part_bound_le_two_of_same_side_near_saturated_sibling_maximum (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s : Ctx.Side) (N : ℕ) (hN : N ∈ σ.levelsOn s 0)
  (hmaximum : σ.k - 3 ≤ σ.maximumAt N)
  (keep : List ℕ) (m r : ℕ)
  (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep) :
  (∀ fuel, Ctx.Context.boundFuel fuel (σ.part keep s m) ≤ 2) ∧
    (σ.part keep s m).bound ≤ 2 := by
  classical
  let ρ := σ.part keep s m
  have hNpos : 1 ≤ N := (Ctx.Context.one_le_of_mem_levelsOn hN).1
  have hNmem : N ∈ σ.levels := (List.mem_filter.mp hN).1
  have hNside : σ.sideAt N = s := by simpa using (List.mem_filter.mp hN).2
  have hOldMem : N + 1 ∈ ρ.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hNmem, rfl⟩)
  have hOldSide : ρ.sideAt (N + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ keep s m hNpos).trans hNside
  have hOldMax : ρ.maximumAt (N + 1) = σ.maximumAt N :=
    Ctx.Context.part_maximumAt_succ σ keep s m hNpos
  have hM : ρ.k - 3 ≤ ρ.maximumAt (N + 1) := by
    simpa only [hOldMax] using hmaximum
  have hrnew : r ∈ ρ.extPositions 1 := by
    rw [Ctx.Context.part_extPositions_one hpositive keep s m]
    exact List.mem_filter.mpr ⟨hr, by simpa using hremoved⟩
  have hFreshSide : ρ.sideAt 1 = s :=
    Ctx.Context.part_sideAt_one_of_mem hpositive keep s m hrnew
  let τ : Ctx.Context := match ρ.sideAt (N + 1) with
    | .lower =>
        { ρ with u := min ρ.u (ρ.k - ρ.maximumAt (N + 1)), maxima := ρ.maxima.take (N + 1 - 1) }
    | .upper =>
        { ρ with a := min ρ.a (ρ.k - ρ.maximumAt (N + 1)), maxima := ρ.maxima.take (N + 1 - 1) }
  have hτWord : τ.word = ρ.word := by
    cases hs : ρ.sideAt (N + 1) <;> simp only [τ, hs]
  have hτMaxima : τ.maxima = ρ.maxima.take N := by
    cases hs : ρ.sideAt (N + 1) <;> simp only [τ, hs, Nat.add_sub_cancel]
  have hτLetter (p : ℕ) : τ.letterAt p = ρ.letterAt p := by
    simp only [Ctx.Context.letterAt, hτWord]
  have hτExt (j : ℕ) : τ.extPositions j = ρ.extPositions j := by
    simp only [Ctx.Context.extPositions, hτWord, hτLetter]
  have hτSide (j : ℕ) : τ.sideAt j = ρ.sideAt j := by
    simp only [Ctx.Context.sideAt, hτExt, hτLetter]
  have hτPositive : ∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    rw [hτLetter] at hp
    exact ctx_part_positive_letters σ keep s m p j v hp
  have hτSmall : (match s with | .lower => τ.u | .upper => τ.a) ≤ 3 := by
    cases s <;> simp only [τ, hOldSide]
    all_goals
      exact (Nat.min_le_right _ _).trans (by omega)
  have hτLength : 1 ≤ τ.maxima.length := by
    rw [hτMaxima, List.length_take]
    change 1 ≤ min N (m :: σ.maxima).length
    simp only [List.length_cons]
    omega
  have hτOne : 1 ∈ τ.levels := by
    unfold Ctx.Context.levels
    exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩
  have hτOneSide : τ.sideAt 1 = s := (hτSide 1).trans hFreshSide
  have hτOneOn : 1 ∈ τ.levelsOn s 0 := by
    exact List.mem_filter.mpr ⟨hτOne, by simp [hτOneSide]⟩
  have hτMarker : r ∈ τ.extPositions 1 := by rw [hτExt]; exact hrnew
  have hnorm := ctx_sibling_maximum_upper_normalize ρ (N + 1) hOldMem
  have hFuelNorm : ∀ fuel, Ctx.Context.boundFuel fuel ρ ≤
      Ctx.Context.boundFuel fuel τ := by
    simpa only [τ] using hnorm.2.1
  have hBoundNorm : ρ.bound ≤ τ.bound := by
    simpa only [τ] using hnorm.2.2
  have htwo := ctx_bound_le_two_of_small_global_axis_with_indexed_marker
    τ hτPositive s hτSmall 1 r hτOneOn hτMarker
  exact ⟨fun fuel => (hFuelNorm fuel).trans (htwo.1 fuel),
    hBoundNorm.trans htwo.2⟩

end ErdosSzekeres
