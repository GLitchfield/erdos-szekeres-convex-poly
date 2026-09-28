import ESBlueprint.B.CtxMixedCapacityChildrenMarkerSeparatedGlobalFive
import ESBlueprint.B.CtxPartPositiveLetters

namespace ErdosSzekeres

/-- In a younger-exterior chosen complement, the transported older marker separates every chosen-capacity-three child from every chosen-capacity-at-most-two child. This makes the high and low supports simultaneously boundary-ready despite the arbitrary convex level-one marker block.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_mixed_capacity_children_marker_separated_global_five, ErdosSzekeres.ctx_capacity_three_children_exterior_of_two_levels_global_five, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_younger_exterior_complement_mixed_capacities_separated_by_older_marker (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s : Ctx.Side) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (keep : List ℕ) (q₀ m : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (houtside : (x < y ∧ ∀ p ∈ keep, p < x) ∨ (y < x ∧ ∀ p ∈ keep, x < p)) : let rest := σ.childPositions.filter (· ∉ keep); let α := σ.part rest s m; ∀ p ∈ α.childPositions, ∀ q ∈ α.childPositions, 3 ≤ (match s with | Ctx.Side.lower => α.cupLimit p p | Ctx.Side.upper => α.capLimit p p) → (match s with | Ctx.Side.lower => α.cupLimit q q | Ctx.Side.upper => α.capLimit q q) ≤ 2 → (x < y ∧ q < y ∧ y < p) ∨ (y < x ∧ p < y ∧ y < q) := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  change ∀ p ∈ α.childPositions, ∀ q ∈ α.childPositions,
    3 ≤ (match s with
      | Ctx.Side.lower => α.cupLimit p p
      | Ctx.Side.upper => α.capLimit p p) →
    (match s with
      | Ctx.Side.lower => α.cupLimit q q
      | Ctx.Side.upper => α.capLimit q q) ≤ 2 →
    (x < y ∧ q < y ∧ y < p) ∨ (y < x ∧ p < y ∧ y < q)
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ rest := by
    simp only [α, Ctx.Context.part_childPositions, rest, List.mem_filter,
      decide_eq_true_eq]
    tauto
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔
      p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [Ctx.Context.part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hQα : q₀ ∈ α.extPositions 1 :=
    (hExtα q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
  have hSideα : α.sideAt 1 = s :=
    Ctx.Context.part_sideAt_one_of_mem hpositive rest s m hQα
  have hOneα : 1 ∈ α.levels := by
    simp only [α, Ctx.Context.part_levels]
    simp
  have hNpos := Ctx.Context.one_le_of_mem_levels hN
  have hMpos := Ctx.Context.one_le_of_mem_levels hM
  have hNα : N + 1 ∈ α.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hMα : M + 1 ∈ α.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hNsα : α.sideAt (N + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest s m hNpos).trans hNs
  have hMsα : α.sideAt (M + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest s m hMpos).trans hMs
  have hXα : x ∈ α.extPositions (N + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ rest s m hNpos]
    exact hx
  have hYα : y ∈ α.extPositions (M + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ rest s m hMpos]
    exact hy
  have hGlobalα : (match s with
      | Ctx.Side.lower => α.u | Ctx.Side.upper => α.a) ≤ 5 := by
    cases s <;> exact hglobal
  have hAtLevel (j i z : ℕ) (hz : z ∈ σ.extPositions j)
      (hz' : z ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hz).2
    have hi := (List.mem_filter.mp hz').2
    cases hletter : σ.letterAt z <;> simp [hletter] at hj hi
    omega
  have hActual : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j,
      (j = N ∧ z = x) ∨ (j = M ∧ z = y) := by
    intro j hj z hz
    rcases hchosen j hj z hz with hzx | hzy
    · exact Or.inl ⟨hAtLevel j N x (by simpa only [hzx] using hz) hx, hzx⟩
    · exact Or.inr ⟨hAtLevel j M y (by simpa only [hzy] using hz) hy, hzy⟩
  have hAlphaActual : ∀ j ∈ α.levelsOn s 0, ∀ z ∈ α.extPositions j,
      (j = 1 ∧ z ∈ keep) ∨ (j = N + 1 ∧ z = x) ∨
        (j = M + 1 ∧ z = y) := by
    intro j hj z hz
    rw [Ctx.Context.part_levelsOn_self_zero hSideα] at hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact Or.inl ⟨rfl, ((hExtα z).mp hz).2⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      rw [Ctx.Context.part_extPositions_succ σ rest s m
        (Ctx.Context.one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hz
      rcases hActual i hi z hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  intro p hp q hq hhigh hlow
  have hSep := ctx_mixed_capacity_children_marker_separated_global_five
    α s 1 (N + 1) q₀ x p q hOneα hNα (by omega) hSideα hNsα hQα hXα
      hGlobalα hp hq hhigh hlow
  have hHigh := ctx_capacity_three_children_exterior_of_two_levels_global_five
    α s 1 (N + 1) q₀ x hOneα hNα (by omega) hSideα hNsα hQα hXα hGlobalα
  rcases houtside with ⟨hxy, hkeepLeft⟩ | ⟨hyx, hkeepRight⟩
  · rcases hHigh with hHigh | hHigh
    · obtain ⟨j, hj, z, hz, hbetween⟩ := hSep
      have hzp := hHigh.2 p hp hhigh j hj z hz
      have hqz : q < z := by
        rcases hbetween with ⟨hpz, _⟩ | ⟨hqz, _⟩
        · omega
        · exact hqz
      have hyP := hHigh.2 p hp hhigh (M + 1)
        (List.mem_filter.mpr ⟨hMα, by simp [hMsα]⟩) y hYα
      refine Or.inl ⟨hxy, ?_, hyP⟩
      rcases hAlphaActual j hj z hz with ⟨_, hzKeep⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact lt_trans hqz (lt_trans (hkeepLeft z hzKeep) hxy)
      · exact lt_trans hqz hxy
      · exact hqz
    · have hq₀x := hkeepLeft q₀ hq₀
      omega
  · rcases hHigh with hHigh | hHigh
    · have hxq₀ := hkeepRight q₀ hq₀
      omega
    · obtain ⟨j, hj, z, hz, hbetween⟩ := hSep
      have hpz := hHigh.2 p hp hhigh j hj z hz
      have hzq : z < q := by
        rcases hbetween with ⟨_, hzq⟩ | ⟨hqz, _⟩
        · exact hzq
        · omega
      have hpY := hHigh.2 p hp hhigh (M + 1)
        (List.mem_filter.mpr ⟨hMα, by simp [hMsα]⟩) y hYα
      refine Or.inr ⟨hyx, hpY, ?_⟩
      rcases hAlphaActual j hj z hz with ⟨_, hzKeep⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact lt_trans (lt_trans hyx (hkeepRight z hzKeep)) hzq
      · exact lt_trans hyx hzq
      · exact hzq

end ErdosSzekeres
