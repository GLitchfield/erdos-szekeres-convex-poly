import ESBlueprint.B.CtxYoungestMiddleMarkerDoubledWidthBound

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- When a nonempty opposite kept block lies strictly between the two actual chosen-axis markers, both independent-fuel and full internal-complement cut sums are at most ten at chosen and opposite globals at most five. The chosen complement costs at most twice the opposite width by the youngest-middle-marker theorem, while two retained boundary witnesses reduce the kept part to width minus two; width at most four closes the arithmetic. Empty opposite indexed history, arbitrary maxima, inactive children, and cut parameters remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_youngest_middle_marker_doubled_width_bound, ErdosSzekeres.ctx_nested_boundary_markers_rank_budget
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_between_internal_complement_cut_ten_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hclear : σ.levelsOn t 0 = []) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (q₀ l r m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hlnot : l ∉ keep) (hrnot : r ∉ keep) (hinside : ∀ p ∈ keep, l < p ∧ p < r) (hbetween : (∀ p ∈ keep, x < p ∧ p < y) ∨ (∀ p ∈ keep, y < p ∧ p < x)) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 10) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 10 := by
  classical
  let w := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  let β := σ.part keep t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ 10) ∧ α.bound + β.bound ≤ 10
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
  have hQα : q₀ ∈ α.extPositions 1 := (hExtα q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
  have hLβ : l ∈ β.extPositions 1 := (hExtβ l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
  have hRβ : r ∈ β.extPositions 1 := (hExtβ r).mpr ((hRest r).mpr ⟨hr, hrnot⟩)
  have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive rest s m hQα
  have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t n hLβ
  have hPositivePart (ks : List ℕ) (v : Side) (q : ℕ) :
      ∀ p j z, (σ.part ks v q).letterAt p = Letter.ext j z → 1 ≤ j := by
    intro p j z hp
    have hpl : p < σ.word.length := by
      by_contra h
      have hh := letterAt_of_length_le (σ.part ks v q)
        (show (σ.part ks v q).word.length ≤ p by rw [part_word_length]; omega)
      rw [hh] at hp
      cases hp
    cases he : σ.letterAt p with
    | child =>
      rw [part_letterAt_of_child σ ks v q hpl he] at hp
      split at hp
      · cases hp
      · cases hp; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ ks v q hpl he] at hp
      cases hp; omega
  have hPosα := hPositivePart rest s m
  have hPosβ := hPositivePart keep t n
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
  have hXα : x ∈ α.extPositions (N + 1) := by
    rw [part_extPositions_succ σ rest s m hNpos]
    exact hx
  have hXβ : x ∈ β.extPositions (N + 1) := by
    rw [part_extPositions_succ σ keep t n hNpos]
    exact hx
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
  have hYα : y ∈ α.extPositions (M + 1) := by
    rw [part_extPositions_succ σ rest s m hMpos]
    exact hy
  have hYβ : y ∈ β.extPositions (M + 1) := by
    rw [part_extPositions_succ σ keep t n hMpos]
    exact hy
  have hAtLevel (j i p : ℕ) (hp : p ∈ σ.extPositions j)
      (hp' : p ∈ σ.extPositions i) : j = i := by
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
    rw [part_extPositions_succ σ keep t n
      (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
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
      rw [part_extPositions_succ σ rest s m
        (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
      rcases hActual i hi p hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  have hAlphaBelow (top j : ℕ) (hj : j ∈ α.levelsOn s top) :
      j ∈ α.levelsOn s 0 ∧ (top = 0 ∨ j < top) := by
    have hh := List.mem_filter.mp hj
    have hp := of_decide_eq_true hh.2
    exact ⟨List.mem_filter.mpr ⟨hh.1, by simp [hp.1]⟩, hp.2⟩
  obtain ⟨direction, hBoundary, hOrder⟩ : ∃ direction : Bool,
      (∀ p ∈ keep, (if direction then x < p else p < x) ∧
        (if direction then p < y else y < p)) ∧
      (if direction then x < y else y < x) := by
    rcases hbetween with hh | hh
    · have hq := hh q₀ hq₀
      exact ⟨true, hh, by change x < y; omega⟩
    · have hq := hh q₀ hq₀
      exact ⟨false, (by intro p hp; exact ⟨(hh p hp).2, (hh p hp).1⟩),
        by change y < x; omega⟩
  have hBeforeN : ∀ j ∈ α.levelsOn s (N + 1), ∀ p ∈ α.extPositions j,
      if direction then x < p else p < x := by
    intro j hj p hp
    have hj' := hAlphaBelow (N + 1) j hj
    rcases hAlphaActual j hj'.1 p hp with ⟨_, hpk⟩ | ⟨hjN, _⟩ | ⟨hjM, _⟩
    · exact (hBoundary p hpk).1
    · omega
    · omega
  have hBeforeM : ∀ j ∈ α.levelsOn s (M + 1), ∀ p ∈ α.extPositions j,
      if direction then p < y else y < p := by
    intro j hj p hp
    have hj' := hAlphaBelow (M + 1) j hj
    rcases hAlphaActual j hj'.1 p hp with ⟨_, hpk⟩ | ⟨_, rfl⟩ | ⟨hjM, _⟩
    · exact (hBoundary p hpk).2
    · exact hOrder
    · omega
  have hOwn : (∀ fuel, boundFuel fuel α ≤ 2 * w) ∧ α.bound ≤ 2 * w :=
    ctx_youngest_middle_marker_doubled_width_bound α hPosα s t hne
      1 (N + 1) (M + 1) q₀ x y hOneα hNα hMα (by omega) (by omega)
      hSideα hNsα hMsα hQα hXα hYα hglobal
      (by simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true])
      direction hBeforeN hBeforeM
  have hOuter : ∀ p ∈ β.childPositions, if direction then p < y else y < p := by
    intro p hp
    exact (hBoundary p ((hChildβ p).mp hp).2).2
  have hInner : ∀ p ∈ β.childPositions, if !direction then p < x else x < p := by
    intro p hp
    have hh := (hBoundary p ((hChildβ p).mp hp).2).1
    cases direction <;> simpa using hh
  have hOuterYoung : ∀ j ∈ β.levelsOn (β.sideAt (M + 1)) (M + 1),
      ∀ p ∈ β.extPositions j, if direction then p < y else y < p := by
    intro j hj p hp
    rw [hMsβ] at hj
    have hj' := hBetaBelow (M + 1) j hj
    rcases hBetaActual j hj'.1 p hp with ⟨_, rfl⟩ | ⟨hjM, _⟩
    · exact hOrder
    · omega
  have hInnerYoung : ∀ j ∈ β.levelsOn (β.sideAt (N + 1)) (N + 1),
      ∀ p ∈ β.extPositions j, if !direction then p < x else x < p := by
    intro j hj p hp
    rw [hNsβ] at hj
    have hj' := hBetaBelow (N + 1) j hj
    rcases hBetaActual j hj'.1 p hp with ⟨hjN, _⟩ | ⟨hjM, _⟩ <;> omega
  have hOneLeftTop (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRightTop (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hOneβ : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
  have hOneOn : 1 ∈ β.levelsOn t (N + 1) :=
    List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ]; omega⟩
  have hLeft : ∀ p ∈ β.childPositions, 1 ≤ β.leftExt t (N + 1) p := by
    intro p hp
    exact hOneLeftTop β t (N + 1) 1 p l hOneOn hLβ
      (hinside p ((hChildβ p).mp hp).2).1
  have hRight : ∀ p ∈ β.childPositions, 1 ≤ β.rightExt t (N + 1) p := by
    intro p hp
    exact hOneRightTop β t (N + 1) 1 p r hOneOn hRβ
      (hinside p ((hChildβ p).mp hp).2).2
  have hGlobalβ : (match β.sideAt (M + 1) with
      | Side.lower => β.u | Side.upper => β.a) ≤ 5 := by
    rw [hMsβ]
    exact hglobal
  have hOther : (∀ fuel, boundFuel fuel β ≤ w - 2) ∧ β.bound ≤ w - 2 := by
    have hh := ctx_nested_boundary_markers_rank_budget β hPosβ
      (M + 1) (N + 1) y x hMβ hNβ (by omega) hYβ hXβ
      (by rw [hNsβ, hMsβ]) direction (!direction)
      hOuter hOuterYoung hInner hInnerYoung t (by rw [hMsβ]; exact hne)
      hGlobalβ 1 1 hLeft hRight
    change (∀ fuel, boundFuel fuel β ≤ w - 1 - 1) ∧ β.bound ≤ w - 1 - 1 at hh
    have he : w - 1 - 1 = w - 2 := by omega
    simpa only [he] using hh
  have hwUpper : w ≤ 4 := by
    dsimp only [w]
    cases t <;> simp only at hopposite ⊢ <;> omega
  have hBudget : 2 * w + (w - 2) ≤ 10 := by omega
  exact ⟨fun f g => (Nat.add_le_add (hOwn.1 f) (hOther.1 g)).trans hBudget,
    (Nat.add_le_add hOwn.2 hOther.2).trans hBudget⟩

end ErdosSzekeres
