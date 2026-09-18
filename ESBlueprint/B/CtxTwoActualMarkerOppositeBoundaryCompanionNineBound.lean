import ESBlueprint.B.CtxTwoMarkerTriangularLinearRankBudget
import ESBlueprint.B.CtxPartPositiveLetters

namespace ErdosSzekeres

/-- If the actual level-one opposite-axis marker created by a chosen-kept cut lies to one side of every companion child and has maximum one, transport the two actual chosen markers into the companion and spend the marker endpoint as one uniform rank loss in the checked triangular-linear potential. Every fuel approximation and the full companion are at most nine. Multiple synthetic level-one positions, arbitrary additional source history, kept lists, inactive children, and independent fuel remain allowed.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_triangular_linear_rank_budget, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem CtxTwoActualMarkerOppositeBoundaryCompanionNineBound (σ : Ctx.Context) (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (keep : List ℕ) (m n p : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hn : n = 1) (hboundary : let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; (∀ q ∈ B.childPositions, q < p) ∨ (∀ q ∈ B.childPositions, p < q)) : let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; (∀ fuel, Ctx.Context.boundFuel fuel B ≤ 9) ∧ B.bound ≤ 9 := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let B := σ.part rest t n
  change (∀ fuel, Ctx.Context.boundFuel fuel B ≤ 9) ∧ B.bound ≤ 9
  change (∀ q ∈ B.childPositions, q < p) ∨
    (∀ q ∈ B.childPositions, p < q) at hboundary
  have hpa : p ∈ σ.childPositions ∧ p ∈ keep := by
    simpa only [Ctx.Context.part_childPositions, List.mem_filter,
      decide_eq_true_eq] using hp
  have hpB : p ∈ B.extPositions 1 := by
    change p ∈ (σ.part rest t n).extPositions 1
    rw [Ctx.Context.part_extPositions_one hpositive]
    exact List.mem_filter.mpr ⟨hpa.1, by simp [rest, hpa.2]⟩
  have hBlevelOne : 1 ∈ B.levels := by
    simp [B, Ctx.Context.part_levels]
  have hBsideOne : B.sideAt 1 = t :=
    Ctx.Context.part_sideAt_one_of_mem hpositive rest t n hpB
  have hBmaximumOne : B.maximumAt 1 = 1 := by
    rw [Ctx.Context.part_maximumAt_one, hn]
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
  have hChosenGlobalB : (match s with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := by
    cases s <;> exact hchosenGlobal
  have hOppositeB : (match t with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := by
    cases t <;> exact hopposite
  have hOneOn : 1 ∈ B.levelsOn t (N + 1) := by
    apply List.mem_filter.mpr
    refine ⟨hBlevelOne, ?_⟩
    simp [hBsideOne]
    omega
  have hOneLeft (q : ℕ) (hq : q ∈ B.childPositions) (hpq : p < q) :
      1 ≤ B.leftExt t (N + 1) q := by
    have hm : p ∈ (B.extPositions 1).filter (· < q) := by
      simp [hpB, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := (B.levelsOn t (N + 1)).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.leftStep B) (q, 0)).2))
      (List.mem_map.mpr ⟨[1],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hOneOn), rfl⟩)
    change _ ≤ B.leftExt t (N + 1) q at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (q : ℕ) (hq : q ∈ B.childPositions) (hqp : q < p) :
      1 ≤ B.rightExt t (N + 1) q := by
    have hm : p ∈ (B.extPositions 1).filter (q < ·) := by
      simp [hpB, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := (B.levelsOn t (N + 1)).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.rightStep B) (q, 0)).2))
      (List.mem_map.mpr ⟨[1],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hOneOn), rfl⟩)
    change _ ≤ B.rightExt t (N + 1) q at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
      List.head?_eq_some_head hnonempty] using hv
  let G := match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a
  have hG : G ≤ 5 := hOppositeB
  have finish (A R : ℕ) (hA : A = 0 ∧ R = 1 ∨ A = 1 ∧ R = 0)
      (hh : (∀ fuel, Ctx.Context.boundFuel fuel B ≤
          ((G - 1 - A - R + 1).choose 2 + (G - 1 - A - R))) ∧
        B.bound ≤ ((G - 1 - A - R + 1).choose 2 + (G - 1 - A - R))) :
      (∀ fuel, Ctx.Context.boundFuel fuel B ≤ 9) ∧ B.bound ≤ 9 := by
    let v := G - 1 - A - R
    have hv : v ≤ 3 := by
      rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp only [v] <;> omega
    have hNine : (v + 1).choose 2 + v ≤ 9 := by
      interval_cases v <;> norm_num [Nat.choose]
    change (∀ fuel, Ctx.Context.boundFuel fuel B ≤ (v + 1).choose 2 + v) ∧
      B.bound ≤ (v + 1).choose 2 + v at hh
    exact ⟨fun fuel => (hh.1 fuel).trans hNine, hh.2.trans hNine⟩
  rcases hboundary with hleft | hright
  · have hh := ctx_two_marker_triangular_linear_rank_budget B hPosB s t hne
      (N + 1) (M + 1) x y hNB hMB (by omega) hNsB hMsB hxB hyB
      hChosenGlobalB hChosenB 0 1 (fun q hq => Nat.zero_le _)
      (fun q hq => hOneRight q hq (hleft q hq))
    change (∀ fuel, Ctx.Context.boundFuel fuel B ≤
        ((G - 1 - 0 - 1 + 1).choose 2 + (G - 1 - 0 - 1))) ∧
      B.bound ≤ ((G - 1 - 0 - 1 + 1).choose 2 + (G - 1 - 0 - 1)) at hh
    exact finish 0 1 (Or.inl ⟨rfl, rfl⟩) hh
  · have hh := ctx_two_marker_triangular_linear_rank_budget B hPosB s t hne
      (N + 1) (M + 1) x y hNB hMB (by omega) hNsB hMsB hxB hyB
      hChosenGlobalB hChosenB 1 0 (fun q hq => hOneLeft q hq (hright q hq))
      (fun q hq => Nat.zero_le _)
    change (∀ fuel, Ctx.Context.boundFuel fuel B ≤
        ((G - 1 - 1 - 0 + 1).choose 2 + (G - 1 - 1 - 0))) ∧
      B.bound ≤ ((G - 1 - 1 - 0 + 1).choose 2 + (G - 1 - 1 - 0)) at hh
    exact finish 1 0 (Or.inr ⟨rfl, rfl⟩) hh

end ErdosSzekeres
