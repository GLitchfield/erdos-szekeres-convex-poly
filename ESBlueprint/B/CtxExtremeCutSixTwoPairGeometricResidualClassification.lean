import ESBlueprint.B.CtxExtremeCutSixTwoPairCollisionResidualClassification
import ESBlueprint.B.CtxTwoMarkerPairCollisionSourceSeparated

set_option maxHeartbeats 24000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- For the actual extreme chosen-kept cut at k six, either every independently fueled and full cut sum is at most twelve, or the companion has two distinct shared low/high ordered-rank pairs and each collision is realized by active source children of capacities at most two and at least three that straddle the older marker, with both coordinates in both original-history intervals. This turns the remaining cut obstruction into explicit two-collision geometry.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_extreme_cut_six_two_pair_collision_residual_classification, ErdosSzekeres.ctx_two_marker_pair_collision_source_separated
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_extreme_cut_six_two_pair_geometric_residual_classification (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (keep : List ℕ) (m n p high : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hm : m + 2 = σ.k) (hk : σ.k = 6) (hhighmem : high ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit high high | Ctx.Side.upper => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit high high)) : let A : Ctx.Context := σ.part keep s m; let B : Ctx.Context := σ.part (σ.childPositions.filter (· ∉ keep)) t n; let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => B.cupLimit q q | Ctx.Side.upper => B.capLimit q q; let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1; let support : ℕ → List ℕ := fun c => B.childPositions.filter (fun q => color q = c); let group : ℕ → Ctx.Context := fun c => ({ B with word := (List.range B.word.length).map (fun q => match B.letterAt q with | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global : ℕ := match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a; let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q); let interval : ℕ → ℕ → Finset ℕ := fun c q => Finset.Icc ((group c).leftExt t 0 q + 1) (global - 1 - (group c).rightExt t 0 q); let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun q => (((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2))); let sourceInterval : ℕ → Finset ℕ := fun q => Finset.Icc (B.leftExt t 0 q + 1) (global - 1 - B.rightExt t 0 q); let geometry : (ℕ × ℕ) → Prop := fun z => ∃ low high, low ∈ B.childPositions ∧ 0 < B.cupLimit low low ∧ 0 < B.capLimit low low ∧ capacity low ≤ 2 ∧ high ∈ B.childPositions ∧ 0 < B.cupLimit high high ∧ 0 < B.capLimit high high ∧ 3 ≤ capacity high ∧ z.1 ≤ z.2 ∧ z.1 ∈ sourceInterval low ∧ z.2 ∈ sourceInterval low ∧ z.1 ∈ sourceInterval high ∧ z.2 ∈ sourceInterval high ∧ ((x < y ∧ low < y ∧ y < high) ∨ (y < x ∧ high < y ∧ y < low)); ((∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 12) ∧ A.bound + B.bound ≤ 12) ∨ ∃ z ∈ (pairs 0) ∩ (pairs 1), ∃ w ∈ (pairs 0) ∩ (pairs 1), z ≠ w ∧ geometry z ∧ geometry w := by
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
      have hGeom := ctx_two_marker_pair_collision_source_separated
        (σ.part (σ.childPositions.filter (· ∉ keep)) Ctx.Side.lower n) hPosB
          s Ctx.Side.lower (N + 1) (M + 1) x y hNB hMB (by omega)
            hNsB hMsB hxB hyB (by cases s <;> exact hGlobalB) hChosenB
      dsimp only at hz hw hGeom
      exact ⟨z, hz, w, hw, hzw, hGeom z hz, hGeom w hw⟩
    | upper =>
      have hGeom := ctx_two_marker_pair_collision_source_separated
        (σ.part (σ.childPositions.filter (· ∉ keep)) Ctx.Side.upper n) hPosB
          s Ctx.Side.upper (N + 1) (M + 1) x y hNB hMB (by omega)
            hNsB hMsB hxB hyB (by cases s <;> exact hGlobalB) hChosenB
      dsimp only at hz hw hGeom
      exact ⟨z, hz, w, hw, hzw, hGeom z hz, hGeom w hw⟩

end ErdosSzekeres
