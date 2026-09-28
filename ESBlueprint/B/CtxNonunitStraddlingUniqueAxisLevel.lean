import ESBlueprint.B.CtxNonunitChildrenExteriorOfTwoLevels

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Nonunit children straddling an actual chosen-axis marker force all actual indexed markers on that axis to use that same level and to lie strictly between the two children, when the chosen global parameter is at most four. Other indexed levels may be unused, opposite-axis history and maxima are arbitrary, and no positivity or opposite-activity premise is required. Uses the two-level exterior orientation theorem to exclude a second actual chosen level and greedy one-step extensions to trap every chosen marker between the witnesses. Reduces the remaining exterior rank-pair collision saving to a single actual chosen-axis level, without erasing or simplifying opposite-axis history.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonunit_straddling_unique_axis_level (σ : Ctx.Context) (s : Ctx.Side) (N x p q : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hp : p ∈ σ.childPositions) (hq : q ∈ σ.childPositions)
  (hpnonunit : 2 ≤ (match s with
    | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p))
  (hqnonunit : 2 ≤ (match s with
    | Ctx.Side.lower => σ.cupLimit q q | Ctx.Side.upper => σ.capLimit q q))
  (hpx : p < x) (hxq : x < q)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) :
  ∀ j ∈ σ.levelsOn s 0, ∀ y ∈ σ.extPositions j, j = N ∧ p < y ∧ y < q := by
  classical
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
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hChildNe (r j z : ℕ) (hr : r ∈ σ.childPositions) (hz : z ∈ σ.extPositions j) :
      r ≠ z := by
    have hc := of_decide_eq_true (List.mem_filter.mp hr).2
    have he := (List.mem_filter.mp hz).2
    intro h
    subst z
    simp [hc] at he
  have hpchain : σ.chainExt s p p ≤ 1 := by
    cases s <;> simp only [cupLimit, capLimit] at hpnonunit hglobal ⊢ <;> omega
  have hqchain : σ.chainExt s q q ≤ 1 := by
    cases s <;> simp only [cupLimit, capLimit] at hqnonunit hglobal ⊢ <;> omega
  have hExcludeTwo (A B a b : ℕ) (hA : A ∈ σ.levels) (hB : B ∈ σ.levels)
      (hAB : A < B) (hAs : σ.sideAt A = s) (hBs : σ.sideAt B = s)
      (ha : a ∈ σ.extPositions A) (hb : b ∈ σ.extPositions B) : False := by
    have hh := ctx_nonunit_children_exterior_of_two_levels σ s A B a b
      hA hB hAB hAs hBs ha hb hglobal
    rcases hh with hh | hh
    · have hc := hh.2 p hp hpnonunit N hNOn x hx
      omega
    · have hc := hh.2 q hq hqnonunit N hNOn x hx
      omega
  intro j hj y hy
  have hjL := (List.mem_filter.mp hj).1
  have hjSide : σ.sideAt j = s := (of_decide_eq_true (List.mem_filter.mp hj).2).1
  have hjN : j = N := by
    rcases lt_trichotomy j N with hlt | he | hgt
    · exact False.elim (hExcludeTwo j N y x hjL hN hlt hjSide hNs hy hx)
    · exact he
    · exact False.elim (hExcludeTwo N j x y hN hjL hgt hNs hjSide hx hy)
  have hpy : p < y := by
    have hne := hChildNe p j y hp hy
    by_contra h
    have hyp : y < p := by omega
    have hl := hOneLeft σ s j p y hj hy hyp
    have hr := hOneRight σ s N p x hNOn hx hpx
    simp only [chainExt] at hpchain
    omega
  have hyq : y < q := by
    have hne := hChildNe q j y hq hy
    by_contra h
    have hqy : q < y := by omega
    have hl := hOneLeft σ s N q x hNOn hx hxq
    have hr := hOneRight σ s j q y hj hy hqy
    simp only [chainExt] at hqchain
    omega
  exact ⟨hjN, hpy, hyq⟩

end ErdosSzekeres
