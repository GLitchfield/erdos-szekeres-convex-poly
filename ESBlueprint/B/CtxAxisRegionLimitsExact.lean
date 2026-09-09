import ESBlueprint.B.CtxNonunitStraddlingUniqueAxisLevel

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Exact equality of all chosen-axis endpoint extensions and point limits at positions having the same order relation to every actual indexed marker on that axis. Covers every history cutoff, pure chain extension, sibling-join extension and the selected cup or cap limit. Opposite-axis letters, inactive or unused levels, maxima and global parameters are arbitrary; neither positivity nor child membership is required. Greedy folds agree until their first common marker, after which their states coincide. Allows the two exterior nonunit witnesses in the remaining collision-saving case to determine capacities throughout their respective chosen-axis regions, even when opposite-axis markers separate children into different runs.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_axis_region_limits_exact (σ : Ctx.Context) (s : Ctx.Side) (p q : ℕ)
  (hregion : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j,
    (z < p ↔ z < q) ∧ (p < z ↔ q < z)) :
  (∀ top, σ.leftExt s top p = σ.leftExt s top q ∧
    σ.rightExt s top p = σ.rightExt s top q) ∧
    σ.chainExt s p p = σ.chainExt s q q ∧
    σ.joinExt s p p = σ.joinExt s q q ∧
    (match s with
      | Ctx.Side.lower => σ.cupLimit p p = σ.cupLimit q q
      | Ctx.Side.upper => σ.capLimit p p = σ.capLimit q q) := by
  classical
  have hFilterLeft (j : ℕ) (hj : j ∈ σ.levelsOn s 0) :
      (σ.extPositions j).filter (· < p) = (σ.extPositions j).filter (· < q) := by
    apply List.filter_congr
    intro z hz
    by_cases hp : z < p
    · have hq := (hregion j hj z hz).1.mp hp
      simp [hp, hq]
    · have hq : ¬ z < q := fun h => hp ((hregion j hj z hz).1.mpr h)
      simp [hp, hq]
  have hFilterRight (j : ℕ) (hj : j ∈ σ.levelsOn s 0) :
      (σ.extPositions j).filter (p < ·) = (σ.extPositions j).filter (q < ·) := by
    apply List.filter_congr
    intro z hz
    by_cases hp : p < z
    · have hq := (hregion j hj z hz).2.mp hp
      simp [hp, hq]
    · have hq : ¬ q < z := fun h => hp ((hregion j hj z hz).2.mpr h)
      simp [hp, hq]
  have hFoldLeft : ∀ (ls : List ℕ) (c : ℕ), (∀ j ∈ ls, j ∈ σ.levelsOn s 0) →
      (ls.foldl (leftStep σ) (p, c)).2 = (ls.foldl (leftStep σ) (q, c)).2 := by
    intro ls
    induction ls with
    | nil => intro c _; rfl
    | cons j ls ih =>
      intro c hls
      have heq := hFilterLeft j (hls j (by simp))
      have htail : ∀ k ∈ ls, k ∈ σ.levelsOn s 0 := fun k hk => hls k (by simp [hk])
      cases he : ((σ.extPositions j).filter (· < p)).getLast? with
      | none =>
        simpa only [List.foldl_cons, leftStep, ← heq, he] using ih c htail
      | some z => simp only [List.foldl_cons, leftStep, ← heq, he]
  have hFoldRight : ∀ (ls : List ℕ) (c : ℕ), (∀ j ∈ ls, j ∈ σ.levelsOn s 0) →
      (ls.foldl (rightStep σ) (p, c)).2 = (ls.foldl (rightStep σ) (q, c)).2 := by
    intro ls
    induction ls with
    | nil => intro c _; rfl
    | cons j ls ih =>
      intro c hls
      have heq := hFilterRight j (hls j (by simp))
      have htail : ∀ k ∈ ls, k ∈ σ.levelsOn s 0 := fun k hk => hls k (by simp [hk])
      cases he : ((σ.extPositions j).filter (p < ·)).head? with
      | none =>
        simpa only [List.foldl_cons, rightStep, ← heq, he] using ih c htail
      | some z => simp only [List.foldl_cons, rightStep, ← heq, he]
  have hOnSubset (top : ℕ) : σ.levelsOn s top ⊆ σ.levelsOn s 0 := by
    intro j hj
    have hh := List.mem_filter.mp hj
    have hjS : σ.sideAt j = s := (of_decide_eq_true hh.2).1
    exact List.mem_filter.mpr ⟨hh.1, by simp [hjS]⟩
  have hExt (top : ℕ) : σ.leftExt s top p = σ.leftExt s top q ∧
      σ.rightExt s top p = σ.rightExt s top q := by
    constructor
    · rw [leftExt_eq, leftExt_eq]
      congr 2
      apply List.map_congr_left
      intro ls hls
      exact hFoldLeft ls 0 (fun j hj => hOnSubset top ((List.mem_sublists.mp hls).subset hj))
    · rw [rightExt_eq, rightExt_eq]
      congr 2
      apply List.map_congr_left
      intro ls hls
      exact hFoldRight ls 0 (fun j hj => hOnSubset top ((List.mem_sublists.mp hls).subset hj))
  have hChain : σ.chainExt s p p = σ.chainExt s q q := by
    simp only [chainExt, (hExt 0).1, (hExt 0).2]
  have hJoin : σ.joinExt s p p = σ.joinExt s q q := by
    unfold joinExt
    rw [hChain]
    congr 1
    congr 2
    apply List.map_congr_left
    intro j _
    rw [(hExt j).1, (hExt j).2]
  refine ⟨hExt, hChain, hJoin, ?_⟩
  cases s <;> simp only [cupLimit, capLimit] <;> rw [hChain, hJoin]

end ErdosSzekeres
