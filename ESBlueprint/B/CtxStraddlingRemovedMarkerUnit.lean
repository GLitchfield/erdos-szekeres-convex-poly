import ESBlueprint.B.CtxBoundLeOneOfClearUnitAxis

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Two removed children on opposite sides of an indexed old marker force unit point capacities in the same-axis kept part when that axis global parameter is at most four. The unit conclusion allows arbitrary kept sets. If the kept children are convex in child order and share a clear interval on the old marker axis, every fuel approximation and the full bound are at most one. Positive external labels suffice, with arbitrary new maxima, unused levels, empty kept sets and both axes. Supplies the unit contribution when the opposite part spans the old gap in the singleton-end sandwich obstruction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_straddling_removed_marker_unit (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N)
  (keep : List ℕ) (newMax y z : ℕ)
  (hy : y ∈ σ.childPositions) (hz : z ∈ σ.childPositions)
  (hyremoved : y ∉ keep) (hzremoved : z ∉ keep)
  (hyx : y < x) (hxz : x < z)
  (hglobal : (match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) :
  let ρ := σ.part keep (σ.sideAt N) newMax
  (∀ p ∈ ρ.childPositions,
    (match σ.sideAt N with | Ctx.Side.lower => ρ.cupLimit p p | Ctx.Side.upper => ρ.capLimit p p) ≤ 1) ∧
  ((∀ p ∈ σ.childPositions, p ∈ keep → ∀ q ∈ σ.childPositions, q ∈ keep →
      ∀ r ∈ σ.childPositions, min p q ≤ r → r ≤ max p q → r ∈ keep) →
    (∀ p ∈ σ.childPositions, p ∈ keep → ∀ q ∈ σ.childPositions, q ∈ keep →
      ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, ∀ w ∈ σ.extPositions j,
        w < min p q ∨ max p q < w) →
    (∀ fuel, Ctx.Context.boundFuel fuel ρ ≤ 1) ∧ ρ.bound ≤ 1) := by
  classical
  let s := σ.sideAt N
  let τ := σ.part keep s newMax
  have hN1 : 1 ≤ N := one_le_of_mem_levels hN
  have hChild (p : ℕ) : p ∈ τ.childPositions ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [τ, part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hPositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    have hpl : p < σ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (σ.part keep s newMax)
        (show (σ.part keep s newMax).word.length ≤ p by rw [part_word_length]; omega)
      rw [hn] at hp
      cases hp
    cases he : σ.letterAt p with
    | child =>
      rw [part_letterAt_of_child σ keep s newMax hpl he] at hp
      split at hp
      · cases hp
      · cases hp
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ keep s newMax hpl he] at hp
      cases hp
      omega
  have hRemoved (q : ℕ) (hq : q ∈ σ.childPositions) (hnot : q ∉ keep) :
      q ∈ τ.extPositions 1 := by
    simp only [τ, part_extPositions_one hpositive, List.mem_filter, decide_eq_true_eq]
    exact ⟨hq, hnot⟩
  have hyNew := hRemoved y hy hyremoved
  have hzNew := hRemoved z hz hzremoved
  have hSide : τ.sideAt 1 = s := part_sideAt_one_of_mem hpositive keep s newMax hyNew
  have hLevels : τ.levelsOn s 0 = 1 :: (σ.levelsOn s 0).map (· + 1) :=
    part_levelsOn_self_zero hSide
  have hNOn : N ∈ σ.levelsOn s 0 := by
    exact List.mem_filter.mpr ⟨hN, by simp [s]⟩
  have hOne : 1 ∈ τ.levelsOn s 0 := by rw [hLevels]; simp
  have hTwo : [1, N + 1].Sublist (τ.levelsOn s 0) := by
    rw [hLevels]
    exact (List.singleton_sublist.mpr (List.mem_map.mpr ⟨N, hNOn, rfl⟩)).cons_cons 1
  have hxNew : x ∈ τ.extPositions (N + 1) := by
    simpa only [τ, part_extPositions_succ σ keep s newMax hN1] using hx
  have hSort (ρ : Context) (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp le_of_lt
  have hOneLeft (p q : ℕ) (hq : q ∈ τ.extPositions 1) (hqp : q < p) :
      1 ≤ τ.leftExt s 0 p := by
    have hm : q ∈ (τ.extPositions 1).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
      (fun ls => (ls.foldl (leftStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr (List.singleton_sublist.mpr hOne), rfl⟩)
    change _ ≤ τ.leftExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (p q : ℕ) (hq : q ∈ τ.extPositions 1) (hpq : p < q) :
      1 ≤ τ.rightExt s 0 p := by
    have hm : q ∈ (τ.extPositions 1).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
      (fun ls => (ls.foldl (rightStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr (List.singleton_sublist.mpr hOne), rfl⟩)
    change _ ≤ τ.rightExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hTwoLeft (p : ℕ) (hzp : z < p) : 2 ≤ τ.leftExt s 0 p := by
    have hm : z ∈ (τ.extPositions 1).filter (· < p) := by simp [hzNew, hzp]
    have hnonempty := List.ne_nil_of_mem hm
    let w := ((τ.extPositions 1).filter (· < p)).getLast hnonempty
    have hw : ((τ.extPositions 1).filter (· < p)).getLast? = some w :=
      List.getLast?_eq_some_getLast hnonempty
    have hzw : z ≤ w := ((hSort τ 1).filter _).rel_getLast hm
    have hmOld : x ∈ (τ.extPositions (N + 1)).filter (· < w) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hxNew, by omega⟩
    have hOldNonempty := List.ne_nil_of_mem hmOld
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
      (fun ls => (ls.foldl (leftStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨[1, N + 1], List.mem_sublists.mpr hTwo, rfl⟩)
    change _ ≤ τ.leftExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep, hw,
      List.getLast?_eq_some_getLast hOldNonempty] using hv
  have hTwoRight (p : ℕ) (hpy : p < y) : 2 ≤ τ.rightExt s 0 p := by
    have hm : y ∈ (τ.extPositions 1).filter (p < ·) := by simp [hyNew, hpy]
    have hnonempty := List.ne_nil_of_mem hm
    let w := ((τ.extPositions 1).filter (p < ·)).head hnonempty
    have hw : ((τ.extPositions 1).filter (p < ·)).head? = some w :=
      List.head?_eq_some_head hnonempty
    have hwy : w ≤ y := ((hSort τ 1).filter _).rel_head hm
    have hmOld : x ∈ (τ.extPositions (N + 1)).filter (w < ·) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hxNew, by omega⟩
    have hOldNonempty := List.ne_nil_of_mem hmOld
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
      (fun ls => (ls.foldl (rightStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨[1, N + 1], List.mem_sublists.mpr hTwo, rfl⟩)
    change _ ≤ τ.rightExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep, hw,
      List.head?_eq_some_head hOldNonempty] using hv
  have hChain (p : ℕ) (hp : p ∈ τ.childPositions) : 2 ≤ τ.chainExt s p p := by
    have hpkeep := ((hChild p).mp hp).2
    have hpy : p ≠ y := by intro h; subst p; exact hyremoved hpkeep
    have hpz : p ≠ z := by intro h; subst p; exact hzremoved hpkeep
    by_cases hleft : p < y
    · have := hTwoRight p hleft
      simp only [chainExt]
      omega
    · by_cases hright : z < p
      · have := hTwoLeft p hright
        simp only [chainExt]
        omega
      · have hL := hOneLeft p y hyNew (by omega)
        have hR := hOneRight p z hzNew (by omega)
        simp only [chainExt]
        omega
  have hGlobal : (match s with | Side.lower => τ.u | Side.upper => τ.a) ≤ 4 := by
    simpa only [τ, part, s] using hglobal
  have hUnit : ∀ p ∈ τ.childPositions,
      (match s with | Side.lower => τ.cupLimit p p | Side.upper => τ.capLimit p p) ≤ 1 := by
    intro p hp
    have hc := hChain p hp
    cases hs : s <;> simp only [hs] at hGlobal hc ⊢
    · simp only [cupLimit]
      omega
    · simp only [capLimit]
      omega
  refine ⟨hUnit, ?_⟩
  intro hconvex hclear
  apply ctx_bound_le_one_of_clear_unit_axis τ hPositive s hUnit
  intro p hp q hq j hj w hw
  obtain ⟨hpOrig, hpKeep⟩ := (hChild p).mp hp
  obtain ⟨hqOrig, hqKeep⟩ := (hChild q).mp hq
  rw [hLevels] at hj
  rcases List.mem_cons.mp hj with hjone | hjold
  · subst j
    have hRemovedW : w ∈ σ.childPositions ∧ w ∉ keep := by
      simpa only [τ, part_extPositions_one hpositive, List.mem_filter, decide_eq_true_eq] using hw
    by_contra hout
    exact hRemovedW.2 (hconvex p hpOrig hpKeep q hqOrig hqKeep w hRemovedW.1 (by omega) (by omega))
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hjold
    have hi1 : 1 ≤ i := one_le_of_mem_levels (List.mem_filter.mp hi).1
    have hwOld : w ∈ σ.extPositions i := by
      simpa only [τ, part_extPositions_succ σ keep s newMax hi1] using hw
    exact hclear p hpOrig hpKeep q hqOrig hqKeep i hi w hwOld

end ErdosSzekeres
