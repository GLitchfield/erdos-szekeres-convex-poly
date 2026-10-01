import ESBlueprint.B.CtxSingletonPartBoundEqThreshold
import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum
import ESBlueprint.B.CtxPartPositiveLetters

namespace ErdosSzekeres

/-- Exact value one for a singleton part whose fresh axis has no old indexed markers and global parameter at least four, with k at least four and new sibling maximum k-2. A distinct omitted source child ensures the fresh level-one side; a positive source point capacity on the opposite axis is preserved by the existing exact part transport. The fresh chosen chain is at most two, so chosen point capacity equals one. Arbitrary opposite-axis history, word patterns, unindexed positive markers, raw globals and length; no WF or source run-count premise. Supplies a restricted lower witness for k=4 maximal-segment exchange.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_singleton_part_bound_eq_threshold, ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_singleton_part_bound_one_of_fresh_saturated_axis_and_positive_opposite_point (σ : Ctx.Context) (hpositive : ∀ x j v, σ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (hk : 4 ≤ σ.k) (hglobal : 4 ≤ (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)) (hempty : σ.levelsOn s 0 = []) (p r : ℕ) (hp : p ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hrne : r ≠ p) (hpoint : 0 < (match t with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p)) : (σ.part [p] s (σ.k - 2)).bound = 1 := by
  classical
  let τ := σ.part [p] s (σ.k - 2)
  have hrnot : r ∉ [p] := by simpa using hrne
  have hrnew : r ∈ τ.extPositions 1 := by
    rw [Ctx.Context.part_extPositions_one hpositive [p] s (σ.k - 2)]
    exact List.mem_filter.mpr ⟨hr, by simpa using hrnot⟩
  have hFresh : τ.sideAt 1 = s :=
    Ctx.Context.part_sideAt_one_of_mem hpositive [p] s (σ.k - 2) hrnew
  have hLevels : τ.levelsOn s 0 = [1] := by
    rw [Ctx.Context.part_levelsOn_self_zero hFresh, hempty]
    rfl
  have hLeft : τ.leftExt s 0 p ≤ 1 := by
    cases h : ((τ.extPositions 1).filter (· < p)).getLast? <;>
      simp [Ctx.Context.leftExt_eq, hLevels, Ctx.Context.leftStep, h]
  have hRight : τ.rightExt s 0 p ≤ 1 := by
    cases h : ((τ.extPositions 1).filter (p < ·)).head? <;>
      simp [Ctx.Context.rightExt_eq, hLevels, Ctx.Context.rightStep, h]
  have hChain : τ.chainExt s p p ≤ 2 := by
    simp only [Ctx.Context.chainExt]
    omega
  have hMaximum : τ.maximumAt 1 = σ.k - 2 :=
    Ctx.Context.part_maximumAt_one σ [p] s (σ.k - 2)
  have hJoin : τ.joinExt s p p = σ.k - 2 := by
    have hj : τ.joinExt s p p = max (τ.chainExt s p p) (σ.k - 2) := by
      simp [Ctx.Context.joinExt, hLevels, Ctx.Context.leftExt_one,
        Ctx.Context.rightExt_one, hMaximum]
    rw [hj]
    apply max_eq_right
    omega
  have hGlobals : τ.a = σ.a ∧ τ.u = σ.u ∧ τ.k = σ.k := ⟨rfl, rfl, rfl⟩
  have hSelected : (match s with
      | Ctx.Side.lower => τ.cupLimit p p
      | Ctx.Side.upper => τ.capLimit p p) = 1 := by
    cases s <;> simp only [Ctx.Context.cupLimit, Ctx.Context.capLimit,
      hGlobals.1, hGlobals.2.1, hGlobals.2.2, hJoin]
    all_goals simp only at hglobal; omega
  have hFreshNe : τ.sideAt 1 ≠ t := by rw [hFresh]; exact hne
  have hOther : (match t with
      | Ctx.Side.lower => τ.cupLimit p p
      | Ctx.Side.upper => τ.capLimit p p) =
      (match t with
      | Ctx.Side.lower => σ.cupLimit p p
      | Ctx.Side.upper => σ.capLimit p p) := by
    cases t <;> simp only [Ctx.Context.cupLimit, Ctx.Context.capLimit,
      hGlobals.1, hGlobals.2.1, hGlobals.2.2]
    all_goals rw [Ctx.Context.chainExt_part_other hFreshNe,
      Ctx.Context.joinExt_part_other hFreshNe]
  have hOtherPos : 0 < (match t with
      | Ctx.Side.lower => τ.cupLimit p p
      | Ctx.Side.upper => τ.capLimit p p) := by
    cases t <;> rw [hOther] <;> exact hpoint
  have hPoint : 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := by
    cases s <;> cases t
    · exact (hne rfl).elim
    · change τ.cupLimit p p = 1 at hSelected
      exact ⟨by omega, hOtherPos⟩
    · change τ.capLimit p p = 1 at hSelected
      exact ⟨hOtherPos, by omega⟩
    · exact (hne rfl).elim
  have hLower : 1 ≤ τ.bound := by
    change 1 ≤ (σ.part [p] s (σ.k - 2)).bound
    rw [ctx_singleton_part_bound_eq_threshold σ p hp s (σ.k - 2)]
    exact one_le_decomposableThreshold (by change 2 ≤ τ.capLimit p p + 1; omega)
      (by change 2 ≤ τ.cupLimit p p + 1; omega)
  have hOne : 1 ∈ τ.levels := by
    rw [Ctx.Context.part_levels]
    simp
  have hPos : ∀ x j v, τ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j :=
    ctx_part_positive_letters σ [p] s (σ.k - 2)
  have hUpper : τ.bound ≤ 1 :=
    (ctx_bound_le_one_of_large_sibling_maximum τ hPos 1 hOne
      (by rw [hMaximum, hGlobals.2.2])).2
  exact Nat.le_antisymm hUpper hLower

end ErdosSzekeres
