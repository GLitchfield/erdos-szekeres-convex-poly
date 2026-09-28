import ESBlueprint.B.CtxBoundaryMarkerRankBudget

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- An opposite-side recursive part kept entirely on one side of an indexed older marker has a linear rank budget, with one unit deducted for a certified removed child on each side of every kept child. The older marker and all younger markers on its side satisfy the boundary geometry; the normalized marker-side global parameter is at most three. Covers arbitrary kept lists, new maxima, both directions and axes, zero losses and empty kept sets. Converts the quantitative boundary rank theorem into the concrete one-sided cut estimate needed for the unbounded sandwich obstruction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_one_sided_part_boundary_budget (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N)
  (keep : List ℕ) (t : Ctx.Side) (hne : σ.sideAt N ≠ t) (newMax : ℕ)
  (rightward : Bool)
  (hchildren : ∀ p ∈ σ.childPositions, p ∈ keep → if rightward then p < x else x < p)
  (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
    if rightward then p < x else x < p)
  (hsmall : min ((match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
    (σ.k - σ.maximumAt N) ≤ 3)
  (A B : ℕ) (hA : A ≤ 1) (hB : B ≤ 1)
  (hLeft : 0 < A → ∀ p ∈ σ.childPositions, p ∈ keep →
    ∃ q ∈ σ.childPositions, q ∉ keep ∧ q < p)
  (hRight : 0 < B → ∀ p ∈ σ.childPositions, p ∈ keep →
    ∃ q ∈ σ.childPositions, q ∉ keep ∧ p < q) :
  let ρ := σ.part keep t newMax
  let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - A - B
  (∀ fuel, Ctx.Context.boundFuel fuel ρ ≤ budget) ∧ ρ.bound ≤ budget := by
  classical
  let τ := σ.part keep t newMax
  have hN1 : 1 ≤ N := one_le_of_mem_levels hN
  have hIndex : N + 1 ∈ τ.levels := by
    simp only [τ, part_levels, List.mem_cons, List.mem_map]
    exact Or.inr ⟨N, hN, rfl⟩
  have hMarker : x ∈ τ.extPositions (N + 1) := by
    simpa only [τ, part_extPositions_succ σ keep t newMax hN1] using hx
  have hSideN : τ.sideAt (N + 1) = σ.sideAt N := part_sideAt_succ σ keep t newMax hN1
  have hMaximum : τ.maximumAt (N + 1) = σ.maximumAt N := part_maximumAt_succ σ keep t newMax hN1
  have hGlobalA : τ.a = σ.a := rfl
  have hGlobalU : τ.u = σ.u := rfl
  have hGlobalK : τ.k = σ.k := rfl
  have hChild (p : ℕ) : p ∈ τ.childPositions ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [τ, part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hPositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    have hpl : p < σ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (σ.part keep t newMax)
        (show (σ.part keep t newMax).word.length ≤ p by rw [part_word_length]; omega)
      rw [hn] at hp
      cases hp
    cases he : σ.letterAt p with
    | child =>
      rw [part_letterAt_of_child σ keep t newMax hpl he] at hp
      split at hp
      · cases hp
      · cases hp
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ keep t newMax hpl he] at hp
      cases hp
      omega
  have hTauChildren : ∀ p ∈ τ.childPositions, if rightward then p < x else x < p := by
    intro p hp
    exact hchildren p ((hChild p).mp hp).1 ((hChild p).mp hp).2
  have hTauYounger : ∀ j ∈ τ.levelsOn (τ.sideAt (N + 1)) (N + 1),
      ∀ p ∈ τ.extPositions j, if rightward then p < x else x < p := by
    intro j hj p hp
    have hmem : j ∈ τ.levels := (List.mem_filter.mp hj).1
    have hprops : τ.sideAt j = τ.sideAt (N + 1) ∧ (N + 1 = 0 ∨ j < N + 1) :=
      of_decide_eq_true (List.mem_filter.mp hj).2
    have hlevels : j ∈ 1 :: σ.levels.map (· + 1) := by simpa only [τ, part_levels] using hmem
    rcases List.mem_cons.mp hlevels with hjone | hjold
    · subst j
      have hnew : τ.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t newMax hp
      have hEq : σ.sideAt N = t := by rw [hSideN, hnew] at hprops; exact hprops.1.symm
      exact False.elim (hne hEq)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hjold
      have hi1 : 1 ≤ i := one_le_of_mem_levels hi
      have hside : σ.sideAt i = σ.sideAt N := by
        simpa only [τ, part_sideAt_succ σ keep t newMax hi1,
          part_sideAt_succ σ keep t newMax hN1] using hprops.1
      have hiN : i < N := by omega
      have hiOn : i ∈ σ.levelsOn (σ.sideAt N) N := by
        exact List.mem_filter.mpr ⟨hi, by simpa only [decide_eq_true_eq] using And.intro hside (Or.inr hiN)⟩
      have hpOld : p ∈ σ.extPositions i := by
        simpa only [τ, part_extPositions_succ σ keep t newMax hi1] using hp
      exact hyounger i hiOn p hpOld
  have hSmall : min ((match τ.sideAt (N + 1) with | Side.lower => τ.u | Side.upper => τ.a) - 1)
      (τ.k - τ.maximumAt (N + 1)) ≤ 3 := by
    simpa only [hSideN, hMaximum, hGlobalA, hGlobalU, hGlobalK] using hsmall
  have hOneLeft (ρ : Context) (v : Side) (top j p y : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hy : y ∈ ρ.extPositions j) (hyp : y < p) :
      1 ≤ ρ.leftExt v top p := by
    have hm : y ∈ (ρ.extPositions j).filter (· < p) := by simp [hy, hyp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (top j p y : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hy : y ∈ ρ.extPositions j) (hpy : p < y) :
      1 ≤ ρ.rightExt v top p := by
    have hm : y ∈ (ρ.extPositions j).filter (p < ·) := by simp [hy, hpy]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hRemoved (q : ℕ) (hq : q ∈ σ.childPositions) (hnot : q ∉ keep) :
      q ∈ τ.extPositions 1 := by
    simp only [τ, part_extPositions_one hpositive, List.mem_filter, decide_eq_true_eq]
    exact ⟨hq, hnot⟩
  have hNewLevel (q : ℕ) (hq : q ∈ τ.extPositions 1) : 1 ∈ τ.levelsOn t (N + 1) := by
    have hnew := part_sideAt_one_of_mem hpositive keep t newMax hq
    have hlevel : 1 ∈ τ.levels := by simp only [τ, part_levels, List.mem_cons, true_or]
    exact List.mem_filter.mpr ⟨hlevel, by
      simp only [decide_eq_true_eq]
      exact ⟨hnew, Or.inr (by omega)⟩⟩
  have hTauLeft : ∀ p ∈ τ.childPositions, A ≤ τ.leftExt t (N + 1) p := by
    intro p hp
    by_cases hzero : A = 0
    · simp only [hzero, Nat.zero_le]
    · obtain ⟨q, hq, hnot, hqp⟩ := hLeft (by omega) p ((hChild p).mp hp).1 ((hChild p).mp hp).2
      have hqNew := hRemoved q hq hnot
      exact hA.trans (hOneLeft τ t (N + 1) 1 p q (hNewLevel q hqNew) hqNew hqp)
  have hTauRight : ∀ p ∈ τ.childPositions, B ≤ τ.rightExt t (N + 1) p := by
    intro p hp
    by_cases hzero : B = 0
    · simp only [hzero, Nat.zero_le]
    · obtain ⟨q, hq, hnot, hpq⟩ := hRight (by omega) p ((hChild p).mp hp).1 ((hChild p).mp hp).2
      have hqNew := hRemoved q hq hnot
      exact hB.trans (hOneRight τ t (N + 1) 1 p q (hNewLevel q hqNew) hqNew hpq)
  have hOpposite : τ.sideAt (N + 1) ≠ t := by simpa only [hSideN] using hne
  have hResult := ctx_boundary_marker_rank_budget τ hPositive (N + 1) x hIndex hMarker
    rightward hTauChildren hTauYounger t hOpposite hSmall A B hTauLeft hTauRight
  cases t <;> simpa only [τ, part] using hResult

end ErdosSzekeres
