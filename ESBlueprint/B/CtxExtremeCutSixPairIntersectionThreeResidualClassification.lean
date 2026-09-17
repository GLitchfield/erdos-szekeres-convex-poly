import ESBlueprint.B.CtxExtremeCutSixTwoPairCollisionResidualClassification
import ESBlueprint.B.CtxTwoMarkerTwoPairCollisionIntersectionThree

set_option maxHeartbeats 12000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- For the actual extreme chosen-kept cut at k six, either every independent-fuel and full cut sum is at most twelve, or the companion canonical low/high ordered-rank-pair intersection has cardinality at least three. The impossible cardinality-two residual is removed by exact two-marker collision amplification.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_extreme_cut_six_two_pair_collision_residual_classification, ErdosSzekeres.ctx_two_marker_two_pair_collision_intersection_three
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_extreme_cut_six_pair_intersection_three_residual_classification (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (keep : List ℕ) (m n p high : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hm : m + 2 = σ.k) (hk : σ.k = 6) (hhighmem : high ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit high high | Ctx.Side.upper => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit high high)) : let A : Ctx.Context := σ.part keep s m; let B : Ctx.Context := σ.part (σ.childPositions.filter (· ∉ keep)) t n; let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => B.cupLimit q q | Ctx.Side.upper => B.capLimit q q; let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1; let support : ℕ → List ℕ := fun c => B.childPositions.filter (fun q => color q = c); let group : ℕ → Ctx.Context := fun c => ({ B with word := (List.range B.word.length).map (fun q => match B.letterAt q with | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global : ℕ := match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a; let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q); let interval : ℕ → ℕ → Finset ℕ := fun c q => Finset.Icc ((group c).leftExt t 0 q + 1) (global - 1 - (group c).rightExt t 0 q); let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun q => (((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2))); ((∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 12) ∧ A.bound + B.bound ≤ 12) ∨ 3 ≤ ((pairs 0) ∩ (pairs 1)).card := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let A : Ctx.Context := σ.part keep s m
  let B : Ctx.Context := σ.part rest t n
  dsimp only
  change high ∈ B.childPositions at hhighmem
  have hpa : p ∈ σ.childPositions ∧ p ∈ keep := by
    simpa only [Ctx.Context.part_childPositions, List.mem_filter,
      decide_eq_true_eq] using hp
  have hpB : p ∈ B.extPositions 1 := by
    change p ∈ (σ.part rest t n).extPositions 1
    rw [Ctx.Context.part_extPositions_one hpositive]
    exact List.mem_filter.mpr ⟨hpa.1, by simp [rest, hpa.2]⟩
  have hBsideOne : B.sideAt 1 = t :=
    Ctx.Context.part_sideAt_one_of_mem hpositive rest t n hpB
  have hNpos := Ctx.Context.one_le_of_mem_levels hN
  have hMpos := Ctx.Context.one_le_of_mem_levels hM
  have hNB : N + 1 ∈ B.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hMB : M + 1 ∈ B.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hNsB : B.sideAt (N + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest t n hNpos).trans hNs
  have hMsB : B.sideAt (M + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest t n hMpos).trans hMs
  have hxB : x ∈ B.extPositions (N + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ rest t n hNpos]
    exact hx
  have hyB : y ∈ B.extPositions (M + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ rest t n hMpos]
    exact hy
  have hChosenB : ∀ j ∈ B.levelsOn s 0, ∀ z ∈ B.extPositions j,
      z = x ∨ z = y := by
    have hs : B.sideAt 1 ≠ s := by
      rw [hBsideOne]
      exact Ne.symm hne
    intro j hj z hz
    rw [Ctx.Context.part_levelsOn_other_zero hs] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [Ctx.Context.part_extPositions_succ σ rest t n
      (Ctx.Context.one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hz
    exact hchosen i hi z hz
  have hPosB := ctx_part_positive_letters σ rest t n
  have hGlobalB : (match s with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := by
    cases s <;> exact hchosenGlobal
  have hClass := ctx_extreme_cut_six_two_pair_collision_residual_classification
    σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy
      hchosenGlobal hopposite hchosen keep m n p high hp hm hk hhighmem hhigh
  rcases hClass with hcut | ⟨z, hz, w, hw, hzw⟩
  · exact Or.inl hcut
  · right
    cases t with
    | lower =>
      have hThree := ctx_two_marker_two_pair_collision_intersection_three
        (σ.part (σ.childPositions.filter (· ∉ keep)) Ctx.Side.lower n) hPosB
          s Ctx.Side.lower (N + 1) (M + 1) x y hNB hMB (by omega)
            hNsB hMsB hxB hyB (by cases s <;> exact hGlobalB) hChosenB
      dsimp only at hz hw hThree
      exact hThree z hz w hw hzw
    | upper =>
      have hThree := ctx_two_marker_two_pair_collision_intersection_three
        (σ.part (σ.childPositions.filter (· ∉ keep)) Ctx.Side.upper n) hPosB
          s Ctx.Side.upper (N + 1) (M + 1) x y hNB hMB (by omega)
            hNsB hMsB hxB hyB (by cases s <;> exact hGlobalB) hChosenB
      dsimp only at hz hw hThree
      exact hThree z hz w hw hzw

end ErdosSzekeres
