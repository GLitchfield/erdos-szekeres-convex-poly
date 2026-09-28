import ESBlueprint.B.CtxUniformRankExteriorBound

import ESBlueprint.B.CtxBoundMonoOfZeroCapacityMarkerInclusion

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Active-only strict doubled-rank bound for positive-label contexts with chosen global at most four and an actual indexed chosen marker. Chosen capacity at least two and uniform opposite pure extension traces are required only at children whose two point capacities are positive. Every fuel approximation and the full recursive bound are at most twice the resulting common rank-interval cardinality minus one. Inactive children may occur anywhere with arbitrary traces and capacities; older histories, maxima, unbounded exterior sizes and empty active support are allowed. Original-history pruning preserves all indexed data and point capacities, while the actual chosen marker bounds the surviving chosen capacities by two. The checked zero-capacity marker comparison transports the original bound to this pruned context, where the full uniform-source theorem applies. Removes inactive-source restrictions from the uniform-rank capacity-three estimate toward the singleton-end sandwich obstruction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_active_uniform_rank_exterior_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4)
  (L R : ℕ)
  (hnonunit : ∀ r ∈ σ.childPositions, 0 < σ.cupLimit r r → 0 < σ.capLimit r r →
    2 ≤ (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.cupLimit r r | Ctx.Side.upper => σ.capLimit r r) s)
  (htraces : ∀ r ∈ σ.childPositions, 0 < σ.cupLimit r r → 0 < σ.capLimit r r →
    σ.leftExt t 0 r = L ∧ σ.rightExt t 0 r = R) :
  let global := fun (ρ : Ctx.Context) (v : Ctx.Side) =>
    match v with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let sourceRanks := Finset.Icc (L + 1) (global σ t - 1 - R)
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2 * sourceRanks.card - 1) ∧
    σ.bound ≤ 2 * sourceRanks.card - 1 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let C (ρ : Context) (v : Side) (r : ℕ) := match v with
    | Side.lower => ρ.cupLimit r r | Side.upper => ρ.capLimit r r
  let active (ρ : Context) : Finset ℕ := ρ.childPositions.toFinset.filter
    (fun r => 0 < ρ.cupLimit r r ∧ 0 < ρ.capLimit r r)
  let marks (ρ : Context) : Finset ℕ :=
    (ρ.levelsOn s 0).toFinset.biUnion (fun j => (ρ.extPositions j).toFinset)
  let Good (ρ : Context) : Prop := ∃ N x : ℕ,
    N ∈ ρ.levels ∧ ρ.sideAt N = s ∧ x ∈ ρ.extPositions N
  let S := Finset.Icc (L + 1) (G σ t - 1 - R)
  let Budget := 2 * S.card - 1
  change (∀ fuel, boundFuel fuel σ ≤ Budget) ∧ σ.bound ≤ Budget
  have hMark (ρ : Context) (x : ℕ) :
      x ∈ marks ρ ↔ ∃ l ∈ ρ.levelsOn s 0, x ∈ ρ.extPositions l := by
    simp [marks]
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by
    simp [active]
  have hNoMark (ρ : Context) (p : ℕ) (hp : p ∈ ρ.childPositions) : p ∉ marks ρ := by
    intro hm
    obtain ⟨l, _, hx⟩ := (hMark ρ p).mp hm
    have hc := (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hx).2
    simp only [decide_eq_true_eq] at hc he
    simp [hc] at he
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
  have hChosenTwo (ρ : Context) (hg : G ρ s ≤ 4) (hgood : Good ρ)
      (p : ℕ) (hp : p ∈ ρ.childPositions) : C ρ s p ≤ 2 := by
    obtain ⟨N, x, hN, hNs, hx⟩ := hgood
    have hNOn : N ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
    have hxMark : x ∈ marks ρ := (hMark ρ x).mpr ⟨N, hNOn, hx⟩
    have hxp : x ≠ p := by intro he; exact hNoMark ρ p hp (he ▸ hxMark)
    have hchain : 1 ≤ ρ.leftExt s 0 p + ρ.rightExt s 0 p := by
      rcases lt_or_gt_of_ne hxp with hl | hr
      · have hh := hOneLeft ρ s N p x hNOn hx hl
        omega
      · have hh := hOneRight ρ s N p x hNOn hx hr
        omega
    cases s <;> simp only [C, G, cupLimit, capLimit, chainExt] at hg hchain ⊢ <;> omega
  let live := σ.childPositions.filter (fun r => 0 < σ.cupLimit r r ∧ 0 < σ.capLimit r r)
  let τ : Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Letter.child => if p ∈ live then Letter.child else Letter.ext (σ.maxima.length + 1) s
      | Letter.ext j v => Letter.ext j v) }
  have hpr := ctx_part_pruning_history_transport σ hpositive live s 0
  change (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
    τ.childPositions = σ.childPositions.filter (· ∈ live) ∧
    (∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧ τ.sideAt j = σ.sideAt j) ∧
    (∀ v top, τ.levelsOn v top = σ.levelsOn v top) ∧
    (∀ v top a, τ.leftExt v top a = σ.leftExt v top a ∧
      τ.rightExt v top a = σ.rightExt v top a) ∧
    (∀ a b, τ.cupLimit a b = σ.cupLimit a b ∧ τ.capLimit a b = σ.capLimit a b) ∧
    active τ = (active σ).filter (· ∈ live) ∧
    (∀ fuel, boundFuel fuel (σ.part live s 0) ≤ boundFuel fuel τ) ∧
    (σ.part live s 0).bound ≤ τ.bound at hpr
  obtain ⟨hτPos, hτChild, hτHist, hτLevels, hτExt, hτLimits, hτActive, hτFuel, hτBound⟩ := hpr
  have hChild (r : ℕ) : r ∈ τ.childPositions ↔
      r ∈ σ.childPositions ∧ 0 < σ.cupLimit r r ∧ 0 < σ.capLimit r r := by
    rw [hτChild]
    simp [live]
  have hC (r : ℕ) : C τ s r = C σ s r := by
    cases s
    · exact (hτLimits r r).1
    · exact (hτLimits r r).2
  have hHistory : ∀ j ∈ σ.levels, τ.sideAt j = σ.sideAt j ∧
      τ.extPositions j ⊆ σ.extPositions j ∧ τ.maximumAt j ≤ σ.maximumAt j := by
    intro j hj
    refine ⟨(hτHist j hj).2, ?_, le_rfl⟩
    intro r hr
    simpa only [(hτHist j hj).1] using hr
  have hLength : σ.word.length = τ.word.length := by simp [τ]
  have hSmallτ : ∀ r ∈ τ.childPositions, min (τ.cupLimit r r) (τ.capLimit r r) ≤ 2 := by
    intro r hr
    have hh := hChosenTwo σ hglobal ⟨N, x, hN, hNs, hx⟩ r ((hChild r).mp hr).1
    rw [(hτLimits r r).1, (hτLimits r r).2]
    cases s
    · exact (Nat.min_le_left _ _).trans hh
    · exact (Nat.min_le_right _ _).trans hh
  have hDead : ∀ r ∈ σ.childPositions, r ∉ τ.childPositions →
      σ.cupLimit r r = 0 ∨ σ.capLimit r r = 0 := by
    intro r hr hn
    rw [hChild] at hn
    by_contra hh
    exact hn ⟨hr, by omega, by omega⟩
  have hComparison := ctx_bound_mono_of_zero_capacity_marker_inclusion σ τ hpositive hτPos
    le_rfl le_rfl rfl hLength rfl hHistory (fun r hr => ((hChild r).mp hr).1)
    hDead hSmallτ
  have hτSource : ∀ r ∈ τ.childPositions,
      0 < τ.cupLimit r r ∧ 0 < τ.capLimit r r ∧ 2 ≤ C τ s r := by
    intro r hr
    have hh := (hChild r).mp hr
    refine ⟨?_, ?_, ?_⟩
    · rw [(hτLimits r r).1]; exact hh.2.1
    · rw [(hτLimits r r).2]; exact hh.2.2
    · rw [hC]; exact hnonunit r hh.1 hh.2.1 hh.2.2
  have hτTraces : ∀ r ∈ τ.childPositions, τ.leftExt t 0 r = L ∧ τ.rightExt t 0 r = R := by
    intro r hr
    have hh := (hChild r).mp hr
    rw [(hτExt t 0 r).1, (hτExt t 0 r).2]
    exact htraces r hh.1 hh.2.1 hh.2.2
  have hτSide : τ.sideAt N = s := (hτHist N hN).2.trans hNs
  have hxτ : x ∈ τ.extPositions N := by simpa only [(hτHist N hN).1] using hx
  have hb := (ctx_uniform_rank_exterior_bound τ hτPos s t hne N x hN hτSide hxτ
    hglobal L R hτSource hτTraces).2
  change τ.bound ≤ Budget at hb
  exact ⟨fun fuel => (hComparison.1 fuel).trans hb, hComparison.2.trans hb⟩

end ErdosSzekeres
