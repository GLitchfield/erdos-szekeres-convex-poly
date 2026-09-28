import ESBlueprint.B.CtxSurroundedYoungerMarkerComplementWidthPlusOneBound
import ESBlueprint.B.CtxBoundaryRetainedDoubledRankBudget
import ESBlueprint.B.CtxPartPositiveLetters

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- If an opposite kept endpoint surrounds the younger of two actual chosen markers but does not surround the older marker, then the chosen complement is at most opposite width plus one and the kept companion is at most twice the residual width minus one. Opposite global at most five makes their independent-fuel and full-bound sum at most ten. Positive labels, arbitrary maxima and k, both endpoint orientations, inactive children, and all histories remain explicit; no coupling hypothesis is needed.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_surrounded_younger_marker_complement_width_plus_one_bound, ErdosSzekeres.ctx_boundary_retained_doubled_rank_budget, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_younger_only_surrounding_endpoint_cut_ten_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (a b l m n : ℕ) (ha : a ∈ keep) (hb : b ∈ keep) (hsurround : a < x ∧ x < b) (hNoOldSurround : ¬ ∃ c ∈ keep, ∃ d ∈ keep, c < y ∧ y < d) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hlnot : l ∉ keep) (endpoint : Bool) (hendpoint : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → if endpoint then q < p else p < q) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 10) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 10 := by
  classical
  let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  let β := σ.part keep t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ 10) ∧
    α.bound + β.bound ≤ 10
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ rest := by
    simp only [α, part_childPositions, rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hChildβ (p : ℕ) : p ∈ β.childPositions ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [β, part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ rest := by
    rw [part_extPositions_one hpositive]
  have hAα : a ∈ α.extPositions 1 := (hExtα a).mpr ⟨hkeep a ha, ha⟩
  have hLβ : l ∈ β.extPositions 1 := (hExtβ l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
  have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive rest s m hAα
  have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t n hLβ
  have hPosα := ctx_part_positive_letters σ rest s m
  have hPosβ := ctx_part_positive_letters σ keep t n
  have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
  have hNpos := one_le_of_mem_levels hN
  have hNα : N + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNβ : N + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNsα : α.sideAt (N + 1) = s := (part_sideAt_succ σ rest s m hNpos).trans hNs
  have hNsβ : β.sideAt (N + 1) = s := (part_sideAt_succ σ keep t n hNpos).trans hNs
  have hXα : x ∈ α.extPositions (N + 1) := by rw [part_extPositions_succ σ rest s m hNpos]; exact hx
  have hXβ : x ∈ β.extPositions (N + 1) := by rw [part_extPositions_succ σ keep t n hNpos]; exact hx
  have hw : 2 ≤ w := hwidth
  have hMpos := one_le_of_mem_levels hM
  have hMα : M + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hMβ : M + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hMsα : α.sideAt (M + 1) = s := (part_sideAt_succ σ rest s m hMpos).trans hMs
  have hMsβ : β.sideAt (M + 1) = s := (part_sideAt_succ σ keep t n hMpos).trans hMs
  have hYα : y ∈ α.extPositions (M + 1) := by rw [part_extPositions_succ σ rest s m hMpos]; exact hy
  have hYβ : y ∈ β.extPositions (M + 1) := by rw [part_extPositions_succ σ keep t n hMpos]; exact hy
  have hAtLevel (j i p : ℕ) (hp : p ∈ σ.extPositions j) (hp' : p ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hp).2
    have hi := (List.mem_filter.mp hp').2
    cases hletter : σ.letterAt p <;> simp [hletter] at hj hi
    omega
  have hActual : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j,
      (j = N ∧ p = x) ∨ (j = M ∧ p = y) := by
    intro j hj p hp
    rcases hchosen j hj p hp with hpx | hpy
    · exact Or.inl ⟨hAtLevel j N x (by simpa only [hpx] using hp) hx, hpx⟩
    · exact Or.inr ⟨hAtLevel j M y (by simpa only [hpy] using hp) hy, hpy⟩
  have hBetaActual : ∀ j ∈ β.levelsOn s 0, ∀ p ∈ β.extPositions j,
      (j = N + 1 ∧ p = x) ∨ (j = M + 1 ∧ p = y) := by
    have hs : β.sideAt 1 ≠ s := by rw [hSideβ]; exact Ne.symm hne
    intro j hj p hp
    rw [part_levelsOn_other_zero hs] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [part_extPositions_succ σ keep t n (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
    rcases hActual i hi p hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hBetaBelow (top j : ℕ) (hj : j ∈ β.levelsOn s top) :
      j ∈ β.levelsOn s 0 ∧ (top = 0 ∨ j < top) := by
    have hh := List.mem_filter.mp hj
    have hp := of_decide_eq_true hh.2
    exact ⟨List.mem_filter.mpr ⟨hh.1, by simp [hp.1]⟩, hp.2⟩
  have hAlphaActual : ∀ j ∈ α.levelsOn s 0, ∀ p ∈ α.extPositions j,
      (j = 1 ∧ p ∈ keep) ∨ (j = N + 1 ∧ p = x) ∨ (j = M + 1 ∧ p = y) := by
    intro j hj p hp
    rw [part_levelsOn_self_zero hSideα] at hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact Or.inl ⟨rfl, ((hExtα p).mp hp).2⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      rw [part_extPositions_succ σ rest s m (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
      rcases hActual i hi p hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  have hAlphaBelow (top j : ℕ) (hj : j ∈ α.levelsOn s top) :
      j ∈ α.levelsOn s 0 ∧ (top = 0 ∨ j < top) := by
    have hh := List.mem_filter.mp hj
    have hp := of_decide_eq_true hh.2
    exact ⟨List.mem_filter.mpr ⟨hh.1, by simp [hp.1]⟩, hp.2⟩
  have hBα : b ∈ α.extPositions 1 := (hExtα b).mpr ⟨hkeep b hb, hb⟩
  have hEndα : ∀ p ∈ α.childPositions, if endpoint then p < a else b < p := by
    intro p hp
    have hh := (hRest p).mp ((hChildα p).mp hp)
    cases hd : endpoint
    · simpa [hd] using hendpoint b hb p hh.1 hh.2
    · simpa [hd] using hendpoint a ha p hh.1 hh.2
  have hOutside : ∀ p ∈ α.childPositions, p < a ∨ b < p := by
    intro p hp
    have hh := hEndα p hp
    cases endpoint
    · exact Or.inr hh
    · exact Or.inl hh
  have hBeforeN : ∀ j ∈ α.levelsOn s (N + 1), ∀ p ∈ α.extPositions j, j = 1 := by
    intro j hj p hp
    have hj' := hAlphaBelow (N + 1) j hj
    rcases hAlphaActual j hj'.1 p hp with ⟨hj1, _⟩ | ⟨hjN, _⟩ | ⟨hjM, _⟩
    · exact hj1
    · omega
    · omega
  have hBeforeM : ∀ j ∈ α.levelsOn s (M + 1), ∀ p ∈ α.extPositions j,
      j = 1 ∨ (j = N + 1 ∧ p = x) := by
    intro j hj p hp
    have hj' := hAlphaBelow (M + 1) j hj
    rcases hAlphaActual j hj'.1 p hp with ⟨hj1, _⟩ | ⟨hjN, hpx⟩ | ⟨hjM, _⟩
    · exact Or.inl hj1
    · exact Or.inr ⟨hjN, hpx⟩
    · omega
  have hOneLeft (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls ↦ (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls ↦ (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hOneβ : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
  have hLossLeft (top : ℕ) (htop : 1 < top) (he : endpoint = true) :
      ∀ p ∈ β.childPositions, 1 ≤ β.leftExt t top p := by
    intro p hp
    have hOn : 1 ∈ β.levelsOn t top := List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ, htop]⟩
    have hlp : l < p := by simpa [he] using hendpoint p ((hChildβ p).mp hp).2 l hl hlnot
    exact hOneLeft β t top 1 p l hOn hLβ hlp
  have hLossRight (top : ℕ) (htop : 1 < top) (he : endpoint = false) :
      ∀ p ∈ β.childPositions, 1 ≤ β.rightExt t top p := by
    intro p hp
    have hOn : 1 ∈ β.levelsOn t top := List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ, htop]⟩
    have hpl : p < l := by simpa [he] using hendpoint p ((hChildβ p).mp hp).2 l hl hlnot
    exact hOneRight β t top 1 p l hOn hLβ hpl
  have hax : a < x := hsurround.1
  have hxb : x < b := hsurround.2
  have hNoY (p : ℕ) (hp : p ∈ keep) : p ≠ y := by
    have hc := of_decide_eq_true (List.mem_filter.mp (hkeep p hp)).2
    have he := (List.mem_filter.mp hy).2
    intro h
    subst p
    simp [hc] at he
  have hOldSide : ((∀ p ∈ keep, p < y) ∧ x < y) ∨
      ((∀ p ∈ keep, y < p) ∧ y < x) := by
    by_cases hay : a < y
    · have hAll : ∀ p ∈ keep, p < y := by
        intro p hp
        have hn := hNoY p hp
        by_contra hh
        exact hNoOldSurround ⟨a, ha, p, hp, hay, by omega⟩
      exact Or.inl ⟨hAll, lt_trans hxb (hAll b hb)⟩
    · have hya : y < a := by have := hNoY a ha; omega
      have hAll : ∀ p ∈ keep, y < p := by
        intro p hp
        have hn := hNoY p hp
        by_contra hh
        exact hNoOldSurround ⟨p, hp, a, ha, by omega, hya⟩
      exact Or.inr ⟨hAll, lt_trans hya hax⟩
  have hDoubled (direction : Bool)
      (hChildren : ∀ p ∈ keep, if direction then p < y else y < p)
      (hYounger : if direction then x < y else y < x) :
      (∀ fuel, boundFuel fuel β ≤ 2 * (w - 1) - 1) ∧ β.bound ≤ 2 * (w - 1) - 1 := by
    have hYoungβ : ∀ j ∈ β.levelsOn (β.sideAt (M + 1)) (M + 1),
        ∀ p ∈ β.extPositions j, if direction then p < y else y < p := by
      rw [hMsβ]
      intro j hj p hp
      have hh := hBetaBelow (M + 1) j hj
      rcases hBetaActual j hh.1 p hp with ⟨_, hpx⟩ | ⟨hjM, _⟩
      · simpa only [hpx] using hYounger
      · omega
    cases he : endpoint
    · have hh := ctx_boundary_retained_doubled_rank_budget β hPosβ
        (M + 1) (N + 1) y x hMβ hNβ (by omega) hYβ hXβ (by rw [hNsβ,hMsβ])
        direction (fun p hp => hChildren p ((hChildβ p).mp hp).2) hYoungβ
        t (by rw [hMsβ]; exact hne) (by rw [hMsβ]; exact hglobal)
        0 1 (by intros; omega) (hLossRight (M + 1) (by omega) he)
      simpa only [Nat.sub_zero] using hh
    · have hh := ctx_boundary_retained_doubled_rank_budget β hPosβ
        (M + 1) (N + 1) y x hMβ hNβ (by omega) hYβ hXβ (by rw [hNsβ,hMsβ])
        direction (fun p hp => hChildren p ((hChildβ p).mp hp).2) hYoungβ
        t (by rw [hMsβ]; exact hne) (by rw [hMsβ]; exact hglobal)
        1 0 (hLossLeft (M + 1) (by omega) he) (by intros; omega)
      simpa only [Nat.sub_zero] using hh
  have hOpp : (∀ fuel, boundFuel fuel β ≤ 2 * (w - 1) - 1) ∧ β.bound ≤ 2 * (w - 1) - 1 := by
    rcases hOldSide with ⟨hAll, hxy⟩ | ⟨hAll, hyx⟩
    · exact hDoubled true hAll hxy
    · exact hDoubled false hAll hyx
  have hOwn := ctx_surrounded_younger_marker_complement_width_plus_one_bound α hPosα s t hne
    1 (N + 1) (M + 1) a b x y hOneα hNα hMα (by omega) (by omega)
    hSideα hNsα hMsα hAα hBα hXα hYα hax hxb hOutside hBeforeN hglobal
  have hwUpper : w ≤ 4 := by
    dsimp only [w]
    cases t <;> simp only at hopposite ⊢ <;> omega
  have hBudget : (w + 1) + (2 * (w - 1) - 1) ≤ 10 := by omega
  exact ⟨fun f g => (Nat.add_le_add (hOwn.1 f) (hOpp.1 g)).trans hBudget,
    (Nat.add_le_add hOwn.2 hOpp.2).trans hBudget⟩

end ErdosSzekeres
