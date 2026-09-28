import ESBlueprint.B.CtxSeparatingMarkerRetainedBoundaryRankUnionBound
import ESBlueprint.B.CtxBoundLeInactivePruneCapacityThree
import ESBlueprint.B.CtxPartPruningHistoryTransport

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Prune inactive children from a capacity-three context, apply the all-active separating-marker retained-boundary rank-union theorem to the transported context, and pull the exact opposite-rank-set bound back to the source. This reusable wrapper retains arbitrary inactive children, maxima, opposite history, marker direction, and fuels.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_separating_marker_retained_boundary_rank_union_bound, ErdosSzekeres.ctx_bound_le_inactive_prune_capacity_three, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_active_separating_marker_retained_boundary_rank_union_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N) (rightward : Bool) (hchildren : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p → if rightward then p < x else x < p) (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j, if rightward then p < x else x < p) (holder : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, N < j → ∀ p ∈ σ.extPositions j, if rightward then x < p else p < x) (I y : ℕ) (hI : I ∈ σ.levels) (hNI : N < I) (hIs : σ.sideAt I = σ.sideAt N) (hy : y ∈ σ.extPositions I) (hretained : ∀ j ∈ σ.levelsOn (σ.sideAt N) I, j ≠ N → ∀ p ∈ σ.extPositions j, if rightward then p < y else y < p) (t : Ctx.Side) (hne : σ.sideAt N ≠ t) (hglobal : (match (generalizing := false) σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) : let budget := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1; let active := σ.childPositions.toFinset.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p); let ranks := active.biUnion (fun p => Finset.Icc (σ.leftExt t 0 p + 1) (budget - σ.rightExt t 0 p)); (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ ranks.card) ∧ σ.bound ≤ ranks.card := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let ranks (ρ : Context) := (active ρ).biUnion
    (fun p => Finset.Icc (ρ.leftExt t 0 p + 1) (G ρ t - 1 - ρ.rightExt t 0 p))
  let keep := σ.childPositions.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let τ : Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Letter.child => if p ∈ keep then Letter.child else Letter.ext (σ.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  change (∀ fuel, boundFuel fuel σ ≤ (ranks σ).card) ∧ σ.bound ≤ (ranks σ).card
  have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hNOn : N ∈ σ.levelsOn (σ.sideAt N) 0 := List.mem_filter.mpr ⟨hN, by simp⟩
  have hSmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3 := by
    intro p hp
    by_cases ha : 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p
    · have hc := hchildren p hp ha
      have he : 1 ≤ σ.leftExt (σ.sideAt N) 0 p ∨ 1 ≤ σ.rightExt (σ.sideAt N) 0 p := by
        cases rightward with
        | false => exact Or.inl (hOneLeft σ (σ.sideAt N) N p x hNOn hx hc)
        | true => exact Or.inr (hOneRight σ (σ.sideAt N) N p x hNOn hx hc)
      cases hs : σ.sideAt N <;>
        simp only [hs, cupLimit, capLimit, chainExt] at hglobal he ⊢ <;> omega
    · omega
  have ht := ctx_part_pruning_history_transport σ hpositive keep Side.lower 0
  have hPos : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := ht.1
  have hChild : τ.childPositions = σ.childPositions.filter (· ∈ keep) := ht.2.1
  have hHist : ∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧
      τ.sideAt j = σ.sideAt j := ht.2.2.1
  have hLevels : ∀ v top, τ.levelsOn v top = σ.levelsOn v top := ht.2.2.2.1
  have hPure : ∀ v top p, τ.leftExt v top p = σ.leftExt v top p ∧
      τ.rightExt v top p = σ.rightExt v top p := ht.2.2.2.2.1
  have hLimits : ∀ p q, τ.cupLimit p q = σ.cupLimit p q ∧
      τ.capLimit p q = σ.capLimit p q := ht.2.2.2.2.2.1
  have hMem (p : ℕ) : p ∈ τ.childPositions ↔ p ∈ σ.childPositions ∧
      0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p := by
    rw [hChild]
    simp only [keep, List.mem_filter, decide_eq_true_eq]
    tauto
  have hAllActive : ∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := by
    intro p hp
    rw [(hLimits p p).1, (hLimits p p).2]
    exact ((hMem p).mp hp).2
  have hChildren : ∀ p ∈ τ.childPositions, if rightward then p < x else x < p := by
    intro p hp
    obtain ⟨hc, ha⟩ := (hMem p).mp hp
    exact hchildren p hc ha
  have hYoung : ∀ j ∈ τ.levelsOn (τ.sideAt N) N, ∀ p ∈ τ.extPositions j,
      if rightward then p < x else x < p := by
    intro j hj p hp
    rw [(hHist N hN).2, hLevels] at hj
    rw [(hHist j (List.mem_filter.mp hj).1).1] at hp
    exact hyounger j hj p hp
  have hOld : ∀ j ∈ τ.levelsOn (τ.sideAt N) 0, N < j → ∀ p ∈ τ.extPositions j,
      if rightward then x < p else p < x := by
    intro j hj hNj p hp
    rw [(hHist N hN).2, hLevels] at hj
    rw [(hHist j (List.mem_filter.mp hj).1).1] at hp
    exact holder j hj hNj p hp
  have hRetained : ∀ j ∈ τ.levelsOn (τ.sideAt N) I, j ≠ N → ∀ p ∈ τ.extPositions j,
      if rightward then p < y else y < p := by
    intro j hj hjN p hp
    rw [(hHist N hN).2, hLevels] at hj
    rw [(hHist j (List.mem_filter.mp hj).1).1] at hp
    exact hretained j hj hjN p hp
  have hX : x ∈ τ.extPositions N := by rw [(hHist N hN).1]; exact hx
  have hY : y ∈ τ.extPositions I := by rw [(hHist I hI).1]; exact hy
  have hISide : τ.sideAt I = τ.sideAt N := by rw [(hHist I hI).2, (hHist N hN).2, hIs]
  have hGlobal : G τ (τ.sideAt N) ≤ 5 := by
    rw [(hHist N hN).2]
    exact hglobal
  have hOpp : τ.sideAt N ≠ t := by rw [(hHist N hN).2]; exact hne
  have hd := ctx_separating_marker_retained_boundary_rank_union_bound τ hPos N x hN hX
    rightward hChildren hYoung hOld I y hI hNI hISide hY hRetained hAllActive t hOpp hGlobal
  change (∀ fuel, boundFuel fuel τ ≤ (ranks τ).card) ∧
    τ.bound ≤ (ranks τ).card at hd
  have hActive : active τ = active σ := by
    ext p
    simp only [active, Finset.mem_filter, List.mem_toFinset, hMem,
      (hLimits p p).1, (hLimits p p).2]
    tauto
  have hRanks : ranks τ = ranks σ := by
    simp only [ranks, hActive, (hPure t 0 _).1, (hPure t 0 _).2]
    rfl
  rw [hRanks] at hd
  have hm := ctx_bound_le_inactive_prune_capacity_three σ hpositive hSmall
  change (∀ fuel, boundFuel fuel σ ≤ τ.bound) ∧ σ.bound ≤ τ.bound at hm
  exact ⟨fun fuel => (hm.1 fuel).trans hd.2, hm.2.trans hd.2⟩

end ErdosSzekeres
