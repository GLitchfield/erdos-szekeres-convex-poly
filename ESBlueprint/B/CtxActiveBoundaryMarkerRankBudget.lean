import ESBlueprint.B.CtxBoundaryMarkerRankBudgetAllHistory

import ESBlueprint.B.CtxBoundMonoOfZeroCapacityMarkerInclusion

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

/-- An active-only full-history boundary rank budget. The selected indexed marker and every younger same-axis marker satisfy the same boundary geometry as before, while child-side geometry and uniform opposite-axis extension losses are required only at children with both point capacities positive. The selected normalization premise implies small point capacities, so the checked zero-capacity marker comparison removes inactive children without lowering the bound; all indexed histories and extension counts are preserved. Bounds every fuel approximation and the full original bound, covering both axes, both directions, repeated markers, arbitrary older histories and empty active support. Removes inactive wrong-side children from the geometric obstruction in the singleton-end sandwich estimates.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_active_boundary_marker_rank_budget (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N)
  (rightward : Bool)
  (hchildren : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p → if rightward then p < x else x < p)
  (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
    if rightward then p < x else x < p)
  (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
  (hsmall : min ((match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
    (σ.k - σ.maximumAt N) ≤ 3)
  (A B : ℕ)
  (hLeft : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p → A ≤ σ.leftExt t 0 p)
  (hRight : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p → B ≤ σ.rightExt t 0 p) :
  let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - A - B
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ budget) ∧ σ.bound ≤ budget := by
  classical
  dsimp only
  let prune (ρ : Context) (keep : List ℕ) (v : Side) : Context := { ρ with
    word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
      | Letter.child => if p ∈ keep then Letter.child else Letter.ext (ρ.maxima.length + 1) v
      | Letter.ext j s => Letter.ext j s) }
  have hPLen (ρ : Context) (keep : List ℕ) (v : Side) :
      (prune ρ keep v).word.length = ρ.word.length := by simp [prune]
  have hPLetter (ρ : Context) (keep : List ℕ) (v : Side) (p : ℕ) (hp : p < ρ.word.length) :
      (prune ρ keep v).letterAt p = (match ρ.letterAt p with
      | Letter.child => if p ∈ keep then Letter.child else Letter.ext (ρ.maxima.length + 1) v
      | Letter.ext j s => Letter.ext j s) := by
    simp only [prune, letterAt, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some]
  have hPChild (ρ : Context) (keep : List ℕ) (v : Side) :
      (prune ρ keep v).childPositions = ρ.childPositions.filter (· ∈ keep) := by
    simp only [childPositions, hPLen, List.filter_filter]
    apply List.filter_congr
    intro p hp
    rw [hPLetter ρ keep v p (List.mem_range.mp hp)]
    cases ρ.letterAt p <;> simp
  have hPPos (ρ : Context) (keep : List ℕ) (v : Side)
      (hpos : ∀ p j s, ρ.letterAt p = Letter.ext j s → 1 ≤ j) :
      ∀ p j s, (prune ρ keep v).letterAt p = Letter.ext j s → 1 ≤ j := by
    intro p j s hp
    have hpl : p < ρ.word.length := by
      by_contra h
      have he := letterAt_of_length_le (prune ρ keep v)
        (show (prune ρ keep v).word.length ≤ p by rw [hPLen]; omega)
      rw [he] at hp
      cases hp
    rw [hPLetter ρ keep v p hpl] at hp
    cases he : ρ.letterAt p with
    | child =>
      by_cases hpk : p ∈ keep
      · simp [he, hpk] at hp
      · simp only [he, if_neg hpk, Letter.ext.injEq] at hp
        omega
    | ext i w =>
      have hi := hpos p i w he
      simp only [he, Letter.ext.injEq] at hp
      omega
  have hPExt (ρ : Context) (keep : List ℕ) (v : Side) (j : ℕ) (hj : j ∈ ρ.levels) :
      (prune ρ keep v).extPositions j = ρ.extPositions j := by
    have hjD : j ≤ ρ.maxima.length := by
      simp only [levels, List.mem_map, List.mem_range] at hj
      obtain ⟨i, hi, rfl⟩ := hj; omega
    simp only [extPositions, hPLen]
    apply List.filter_congr
    intro p hp
    rw [hPLetter ρ keep v p (List.mem_range.mp hp)]
    cases ρ.letterAt p with
    | child => split_ifs <;> simp [show ρ.maxima.length + 1 ≠ j by omega]
    | ext i w => rfl
  have hPSide (ρ : Context) (keep : List ℕ) (v : Side) (j : ℕ) (hj : j ∈ ρ.levels) :
      (prune ρ keep v).sideAt j = ρ.sideAt j := by
    simp only [sideAt, hPExt ρ keep v j hj]
    cases hh : (ρ.extPositions j).head? with
    | none => rfl
    | some p =>
      have hp := List.mem_of_mem_head? hh
      have hpl := List.mem_range.mp (List.mem_filter.mp hp).1
      dsimp only
      rw [hPLetter ρ keep v p hpl]
      cases he : ρ.letterAt p with
      | child => simp [extPositions, he] at hp
      | ext i s => rfl
  have hPExtensions (ρ : Context) (keep : List ℕ) (v s : Side) (top x : ℕ) :
      (prune ρ keep v).leftExt s top x = ρ.leftExt s top x ∧
      (prune ρ keep v).rightExt s top x = ρ.rightExt s top x := by
    have hlevels (s : Side) (top : ℕ) :
        (prune ρ keep v).levelsOn s top = ρ.levelsOn s top := by
      change ρ.levels.filter _ = ρ.levels.filter _
      apply List.filter_congr
      intro j hj
      rw [hPSide ρ keep v j hj]
    have hfold : ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ ρ.levels) → ∀ z,
        ls.foldl (leftStep (prune ρ keep v)) z = ls.foldl (leftStep ρ) z ∧
        ls.foldl (rightStep (prune ρ keep v)) z = ls.foldl (rightStep ρ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; exact ⟨rfl, rfl⟩
      | cons j ls ih =>
        intro hj z
        have ht := ih (fun i hi => hj i (by simp [hi]))
        simp only [List.foldl_cons, leftStep, rightStep, hPExt ρ keep v j (hj j (by simp))]
        exact ⟨(ht _).1, (ht _).2⟩
    have hext (s : Side) (top x : ℕ) :
        (prune ρ keep v).leftExt s top x = ρ.leftExt s top x ∧
        (prune ρ keep v).rightExt s top x = ρ.rightExt s top x := by
      simp only [leftExt_eq, rightExt_eq, hlevels]
      constructor <;> congr 2 <;> apply List.map_congr_left <;> intro ls hls
      · exact congrArg Prod.snd (hfold ls
          (fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) _).1
      · exact congrArg Prod.snd (hfold ls
          (fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) _).2
    exact hext s top x
  have hPLimits (ρ : Context) (keep : List ℕ) (v : Side) (p q : ℕ) :
      (prune ρ keep v).cupLimit p q = ρ.cupLimit p q ∧
      (prune ρ keep v).capLimit p q = ρ.capLimit p q := by
    have hlevels (s : Side) (top : ℕ) :
        (prune ρ keep v).levelsOn s top = ρ.levelsOn s top := by
      change ρ.levels.filter _ = ρ.levels.filter _
      apply List.filter_congr
      intro j hj
      rw [hPSide ρ keep v j hj]
    have hext := hPExtensions ρ keep v
    have hchain (s : Side) : (prune ρ keep v).chainExt s p q = ρ.chainExt s p q := by
      simp only [chainExt, (hext s 0 p).1, (hext s 0 q).2]
    have hjoin (s : Side) : (prune ρ keep v).joinExt s p q = ρ.joinExt s p q := by
      simp only [joinExt, hchain, hlevels]
      congr 3
      apply List.map_congr_left
      intro j _
      simp only [(hext s j p).1, (hext s j q).2]
      rfl
    simp only [cupLimit, capLimit, hchain, hjoin]
    exact ⟨rfl, rfl⟩
  let s := σ.sideAt N
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [s]⟩
  have hOneLeft (p : ℕ) (hxp : x < p) : 1 ≤ σ.leftExt s 0 p := by
    have hm : x ∈ (σ.extPositions N).filter (· < p) := by simp [hx, hxp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
      (fun ls => (ls.foldl (leftStep σ) (p, 0)).2))
      (List.mem_map.mpr ⟨[N], List.mem_sublists.mpr (List.singleton_sublist.mpr hNOn), rfl⟩)
    change _ ≤ σ.leftExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (p : ℕ) (hpx : p < x) : 1 ≤ σ.rightExt s 0 p := by
    have hm : x ∈ (σ.extPositions N).filter (p < ·) := by simp [hx, hpx]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
      (fun ls => (ls.foldl (rightStep σ) (p, 0)).2))
      (List.mem_map.mpr ⟨[N], List.mem_sublists.mpr (List.singleton_sublist.mpr hNOn), rfl⟩)
    change _ ≤ σ.rightExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hChain (p : ℕ) (hp : p ∈ σ.childPositions) : 1 ≤ σ.chainExt s p p := by
    have hlet : σ.letterAt p = Letter.child := of_decide_eq_true (List.mem_filter.mp hp).2
    have hpx : p ≠ x := by
      intro heq
      subst p
      simp [extPositions, hlet] at hx
    rcases lt_or_gt_of_ne hpx with hpx | hxp
    · have hr := hOneRight p hpx
      simp only [chainExt]
      omega
    · have hl := hOneLeft p hxp
      simp only [chainExt]
      omega
  have hJoin (p : ℕ) : σ.maximumAt N ≤ σ.joinExt s p p := by
    have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).map
      (fun j => σ.leftExt s j p + σ.rightExt s j p + σ.maximumAt j))
      (List.mem_map.mpr ⟨N, hNOn, rfl⟩)
    unfold joinExt
    omega
  have hSmall (p : ℕ) (hp : p ∈ σ.childPositions) :
      min (σ.cupLimit p p) (σ.capLimit p p) ≤ 2 := by
    have hc := hChain p hp
    have hj := hJoin p
    change min ((match s with | Side.lower => σ.u | Side.upper => σ.a) - 1)
      (σ.k - σ.maximumAt N) ≤ 3 at hsmall
    cases hs : s <;> simp only [hs] at hc hj hsmall
    · simp only [cupLimit, capLimit]
      omega
    · simp only [cupLimit, capLimit]
      omega
  let active := σ.childPositions.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let τ := prune σ active Side.lower
  have hτpositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j :=
    hPPos σ active Side.lower hpositive
  have hChild (p : ℕ) : p ∈ τ.childPositions ↔
      p ∈ σ.childPositions ∧ 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p := by
    simp [τ, hPChild, active]
  have hSide : τ.sideAt N = σ.sideAt N := hPSide σ active Side.lower N hN
  have hNτ : N ∈ τ.levels := hN
  have hxτ : x ∈ τ.extPositions N := by
    simpa only [τ, hPExt σ active Side.lower N hN] using hx
  have hLevels (v : Side) (top : ℕ) : τ.levelsOn v top = σ.levelsOn v top := by
    change σ.levels.filter _ = σ.levels.filter _
    apply List.filter_congr
    intro j hj
    rw [hPSide σ active Side.lower j hj]
  have hHistory : ∀ j ∈ σ.levels, τ.sideAt j = σ.sideAt j ∧
      τ.extPositions j ⊆ σ.extPositions j ∧ τ.maximumAt j ≤ σ.maximumAt j := by
    intro j hj
    refine ⟨hPSide σ active Side.lower j hj, ?_, le_rfl⟩
    intro p hp
    simpa only [τ, hPExt σ active Side.lower j hj] using hp
  have hSmallτ : ∀ p ∈ τ.childPositions, min (τ.cupLimit p p) (τ.capLimit p p) ≤ 2 := by
    intro p hp
    have h := hSmall p ((hChild p).mp hp).1
    change min ((prune σ active Side.lower).cupLimit p p)
      ((prune σ active Side.lower).capLimit p p) ≤ 2
    rw [(hPLimits σ active Side.lower p p).1, (hPLimits σ active Side.lower p p).2]
    exact h
  have hDead : ∀ p ∈ σ.childPositions, p ∉ τ.childPositions →
      σ.cupLimit p p = 0 ∨ σ.capLimit p p = 0 := by
    intro p hp hn
    rw [hChild] at hn
    by_contra h
    exact hn ⟨hp, by omega, by omega⟩
  have hComparison := ctx_bound_mono_of_zero_capacity_marker_inclusion σ τ hpositive hτpositive
    le_rfl le_rfl rfl (hPLen σ active Side.lower).symm rfl hHistory
    (fun p hp => ((hChild p).mp hp).1) hDead hSmallτ
  have hChildrenτ : ∀ p ∈ τ.childPositions, if rightward then p < x else x < p := by
    intro p hp
    have hh := (hChild p).mp hp
    exact hchildren p hh.1 hh.2
  have hYoungerτ : ∀ j ∈ τ.levelsOn (τ.sideAt N) N, ∀ p ∈ τ.extPositions j,
      if rightward then p < x else x < p := by
    intro j hj p hp
    rw [hSide, hLevels] at hj
    have hjσ := (List.mem_filter.mp hj).1
    have hpσ : p ∈ σ.extPositions j := by
      simpa only [τ, hPExt σ active Side.lower j hjσ] using hp
    exact hyounger j hj p hpσ
  have hNormτ : min ((match τ.sideAt N with | Side.lower => τ.u | Side.upper => τ.a) - 1)
      (τ.k - τ.maximumAt N) ≤ 3 := by
    simpa only [hSide] using hsmall
  have hLeftτ : ∀ p ∈ τ.childPositions, A ≤ τ.leftExt t 0 p := by
    intro p hp
    have hh := (hChild p).mp hp
    change A ≤ (prune σ active Side.lower).leftExt t 0 p
    rw [(hPExtensions σ active Side.lower t 0 p).1]
    exact hLeft p hh.1 hh.2
  have hRightτ : ∀ p ∈ τ.childPositions, B ≤ τ.rightExt t 0 p := by
    intro p hp
    have hh := (hChild p).mp hp
    change B ≤ (prune σ active Side.lower).rightExt t 0 p
    rw [(hPExtensions σ active Side.lower t 0 p).2]
    exact hRight p hh.1 hh.2
  have ht : τ.sideAt N ≠ t := by rw [hSide]; exact hne
  have hb := (ctx_boundary_marker_rank_budget_all_history τ hτpositive N x hNτ hxτ
    rightward hChildrenτ hYoungerτ t ht hNormτ A B hLeftτ hRightτ).2
  exact ⟨fun fuel => (hComparison.1 fuel).trans hb, hComparison.2.trans hb⟩

end ErdosSzekeres
