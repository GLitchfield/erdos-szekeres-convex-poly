import ESBlueprint.B.CtxActiveSeparatingMarkerRetainedBoundaryRankUnionBound
import ESBlueprint.B.CtxThreeOrderedMarkersTriangularPlusOneBound
import ESBlueprint.B.CtxPartPositiveLetters

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Expose the two independent component estimates underlying the younger-exterior internal-complement potential: the chosen complement has the triangular-plus-one charge, while the internally retained opposite block loses two ranks. The hypotheses exactly match the existing combined theorem; arbitrary maxima, inactive children, positive barriers, and independent fuels remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_three_ordered_markers_triangular_plus_one_bound, ErdosSzekeres.ctx_active_separating_marker_retained_boundary_rank_union_bound, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_younger_exterior_internal_complement_cut_component_bounds (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hclear : σ.levelsOn t 0 = []) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (q₀ l r m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hlnot : l ∉ keep) (hrnot : r ∉ keep) (hinside : ∀ p ∈ keep, l < p ∧ p < r) (houtside : (x < y ∧ ∀ p ∈ keep, p < x) ∨ (y < x ∧ ∀ p ∈ keep, x < p)) : let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1; let rest := σ.childPositions.filter (· ∉ keep); (((∀ f, Ctx.Context.boundFuel f (σ.part rest s m) ≤ (w + 1).choose 2 + 1) ∧ (σ.part rest s m).bound ≤ (w + 1).choose 2 + 1) ∧ ((∀ g, Ctx.Context.boundFuel g (σ.part keep t n) ≤ w - 2) ∧ (σ.part keep t n).bound ≤ w - 2)) := by
  classical
  let w := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  let β := σ.part keep t n
  change ((∀ f, boundFuel f α ≤ (w + 1).choose 2 + 1) ∧
      α.bound ≤ (w + 1).choose 2 + 1) ∧
    ((∀ g, boundFuel g β ≤ w - 2) ∧ β.bound ≤ w - 2)
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
  have hXα : x ∈ α.extPositions (N + 1) := by
    rw [part_extPositions_succ σ rest s m hNpos]
    exact hx
  have hXβ : x ∈ β.extPositions (N + 1) := by
    rw [part_extPositions_succ σ keep t n hNpos]
    exact hx
  have hLevelsβ : β.levelsOn t 0 = [1] := by
    rw [part_levelsOn_self_zero hSideβ, hclear]
    rfl
  have hw : 2 ≤ w := hwidth
  let activeβ := β.childPositions.toFinset.filter
    (fun p => 0 < β.cupLimit p p ∧ 0 < β.capLimit p p)
  let Iβ (p : ℕ) := Finset.Icc (β.leftExt t 0 p + 1) (w - β.rightExt t 0 p)
  let ranksβ := activeβ.biUnion Iβ
  let J := Finset.Icc 2 (w - 1)
  have hIntervalβ (p : ℕ) (hp : p ∈ β.childPositions) : Iβ p = J := by
    have hpk := ((hChildβ p).mp hp).2
    have hpl := (hinside p hpk).1
    have hpr := (hinside p hpk).2
    have hMemL : l ∈ (β.extPositions 1).filter (· < p) := by simp [hLβ, hpl]
    have hMemR : r ∈ (β.extPositions 1).filter (p < ·) := by simp [hRβ, hpr]
    have hNEL := List.ne_nil_of_mem hMemL
    have hNER := List.ne_nil_of_mem hMemR
    have hLeft : β.leftExt t 0 p = 1 := by
      unfold leftExt
      rw [hLevelsβ]
      change ([0, (match ((β.extPositions 1).filter (· < p)).getLast? with
        | some q => (q, 1) | none => (p, 0)).2].max?).getD 0 = 1
      rw [List.getLast?_eq_some_getLast hNEL]
      rfl
    have hRight : β.rightExt t 0 p = 1 := by
      unfold rightExt
      rw [hLevelsβ]
      change ([0, (match ((β.extPositions 1).filter (p < ·)).head? with
        | some q => (q, 1) | none => (p, 0)).2].max?).getD 0 = 1
      rw [List.head?_eq_some_head hNER]
      rfl
    simp only [Iβ, J, hLeft, hRight]
  have hJCard : J.card = w - 2 := by simp only [J, Nat.card_Icc]; omega
  have hRanksβSub : ranksβ ⊆ J := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    rw [hIntervalβ p (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)] at hz
    exact hz
  have hRanksβCard : ranksβ.card ≤ w - 2 := by
    rw [← hJCard]
    exact Finset.card_le_card hRanksβSub
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
  have hOrderα : (q₀ < x ∧ x < y) ∨ (y < x ∧ x < q₀) := by
    rcases houtside with ⟨hxy, hout⟩ | ⟨hyx, hout⟩
    · exact Or.inl ⟨hout q₀ hq₀, hxy⟩
    · exact Or.inr ⟨hyx, hout q₀ hq₀⟩
  have hOwn : (∀ fuel, boundFuel fuel α ≤ (w + 1).choose 2 + 1) ∧
      α.bound ≤ (w + 1).choose 2 + 1 :=
    ctx_three_ordered_markers_triangular_plus_one_bound α hPosα s t hne
      1 (N + 1) (M + 1) q₀ x y hOneα hNα hMα (by omega) (by omega)
      hSideα hNsα hMsα hQα hXα hYα hglobal
      (by simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true]) hOrderα
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
  obtain ⟨direction, hBoundary, hOlderPosition⟩ : ∃ direction : Bool,
      (∀ p ∈ β.childPositions, if direction then p < x else x < p) ∧
      (if direction then x < y else y < x) := by
    rcases houtside with ⟨hxy, hout⟩ | ⟨hyx, hout⟩
    · exact ⟨true, fun p hp => hout p ((hChildβ p).mp hp).2, hxy⟩
    · exact ⟨false, fun p hp => hout p ((hChildβ p).mp hp).2, hyx⟩
  have hYounger : ∀ j ∈ β.levelsOn (β.sideAt (N + 1)) (N + 1),
      ∀ p ∈ β.extPositions j, if direction then p < x else x < p := by
    intro j hj p hp
    rw [hNsβ] at hj
    have hj' := hBetaBelow (N + 1) j hj
    rcases hBetaActual j hj'.1 p hp with ⟨hjN, _⟩ | ⟨hjM, _⟩ <;> omega
  have hOlder : ∀ j ∈ β.levelsOn (β.sideAt (N + 1)) 0, N + 1 < j →
      ∀ p ∈ β.extPositions j, if direction then x < p else p < x := by
    intro j hj hlt p hp
    rw [hNsβ] at hj
    rcases hBetaActual j hj p hp with ⟨hjN, _⟩ | ⟨_, rfl⟩
    · omega
    · exact hOlderPosition
  have hRetained : ∀ j ∈ β.levelsOn (β.sideAt (N + 1)) (M + 1), j ≠ N + 1 →
      ∀ p ∈ β.extPositions j, if direction then p < y else y < p := by
    intro j hj hjN p hp
    rw [hNsβ] at hj
    have hj' := hBetaBelow (M + 1) j hj
    rcases hBetaActual j hj'.1 p hp with ⟨hjN', _⟩ | ⟨hjM, _⟩ <;> omega
  have hGlobalβ :
      (match β.sideAt (N + 1) with | Side.lower => β.u | Side.upper => β.a) ≤ 5 := by
    rw [hNsβ]
    exact hglobal
  have hOther : (∀ fuel, boundFuel fuel β ≤ w - 2) ∧ β.bound ≤ w - 2 := by
    have hh := ctx_active_separating_marker_retained_boundary_rank_union_bound β hPosβ
      (N + 1) x hNβ hXβ direction (by intro p hp hact; exact hBoundary p hp)
      hYounger hOlder (M + 1) y hMβ (by omega) (by rw [hMsβ, hNsβ]) hYβ hRetained
      t (by rw [hNsβ]; exact hne) hGlobalβ
    change (∀ fuel, boundFuel fuel β ≤ ranksβ.card) ∧ β.bound ≤ ranksβ.card at hh
    exact ⟨fun fuel => (hh.1 fuel).trans hRanksβCard, hh.2.trans hRanksβCard⟩
  exact ⟨hOwn, hOther⟩

end ErdosSzekeres
