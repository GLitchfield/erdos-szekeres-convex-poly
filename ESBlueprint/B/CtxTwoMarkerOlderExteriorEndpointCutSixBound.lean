import ESBlueprint.B.CtxBoundLeOppositeWidthOfSiblingMaximumGeKMinusThree
import ESBlueprint.B.CtxTwoActualMarkerCompanionMaximumBound
import ESBlueprint.B.CtxBoundaryMarkerFullRankBudget
import ESBlueprint.B.CtxBoundaryMarkerUpperNormalize
import ESBlueprint.B.CtxSmallGlobalAxisSaturatedTriangleBound

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At k=6, the positive legal coupling sharpens the older-exterior endpoint cut from the coarse two-marker budget thirteen to twelve in the clear-opposite-history source used by the actual reduction. The four chosen maxima are paid respectively by nonmonotone-linear plus sibling-one, saturated-nonmonotone plus full-history boundary rank, sibling k-minus-three normalization plus the sharp two-marker companion, and sibling-one plus boundary normalization with the global-four saturated triangle. Arbitrary chosen history, old maxima, inactive children, endpoint length and fuel approximations remain explicit. Exact search found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_nonmonotone_triple_linear_potential, ErdosSzekeres.ctx_nonmonotone_triple_saturated_potential_arbitrary_opposite_history, ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum, ErdosSzekeres.ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three, ErdosSzekeres.ctx_two_actual_marker_companion_maximum_bound, ErdosSzekeres.ctx_boundary_marker_full_rank_budget, ErdosSzekeres.ctx_boundary_marker_upper_normalize, ErdosSzekeres.ctx_small_global_axis_saturated_triangle_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_older_exterior_endpoint_cut_six_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (hclear : σ.levelsOn t 0 = []) (keep : List ℕ) (q₀ l m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hlnot : l ∉ keep) (horder : ((∀ p ∈ keep, y < p) ∧ x < y ∧ ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → q < p) ∨ ((∀ p ∈ keep, p < y) ∧ y < x ∧ ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → p < q)) (hk : σ.k = 6) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12 := by
  classical
  let G (ρ : Ctx.Context) (v : Ctx.Side) := match v with
    | Ctx.Side.lower => ρ.u
    | Ctx.Side.upper => ρ.a
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  let β := σ.part keep t n
  change (∀ f g, Ctx.Context.boundFuel f α + Ctx.Context.boundFuel g β ≤ 12) ∧
    α.bound + β.bound ≤ 12
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ rest := by
    simp only [α, Ctx.Context.part_childPositions, rest, List.mem_filter,
      decide_eq_true_eq]
    tauto
  have hChildβ (p : ℕ) : p ∈ β.childPositions ↔
      p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [β, Ctx.Context.part_childPositions, List.mem_filter,
      decide_eq_true_eq]
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔
      p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [Ctx.Context.part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ rest := by
    rw [Ctx.Context.part_extPositions_one hpositive]
  have hQα : q₀ ∈ α.extPositions 1 :=
    (hExtα q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
  have hLβ : l ∈ β.extPositions 1 :=
    (hExtβ l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
  have hSideα : α.sideAt 1 = s :=
    Ctx.Context.part_sideAt_one_of_mem hpositive rest s m hQα
  have hSideβ : β.sideAt 1 = t :=
    Ctx.Context.part_sideAt_one_of_mem hpositive keep t n hLβ
  have hPosα := ctx_part_positive_letters σ rest s m
  have hPosβ := ctx_part_positive_letters σ keep t n
  have hOneα : 1 ∈ α.levels := by
    simp only [α, Ctx.Context.part_levels, List.mem_cons, true_or]
  have hOneβ : 1 ∈ β.levels := by
    simp only [β, Ctx.Context.part_levels, List.mem_cons, true_or]
  have hNpos := Ctx.Context.one_le_of_mem_levels hN
  have hMpos := Ctx.Context.one_le_of_mem_levels hM
  have hNα : N + 1 ∈ α.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hMα : M + 1 ∈ α.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hMβ : M + 1 ∈ β.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hNsα : α.sideAt (N + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest s m hNpos).trans hNs
  have hMsα : α.sideAt (M + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest s m hMpos).trans hMs
  have hMsβ : β.sideAt (M + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ keep t n hMpos).trans hMs
  have hXα : x ∈ α.extPositions (N + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ rest s m hNpos]
    exact hx
  have hYα : y ∈ α.extPositions (M + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ rest s m hMpos]
    exact hy
  have hYβ : y ∈ β.extPositions (M + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ keep t n hMpos]
    exact hy
  have hGlobalα : G α s ≤ 5 := by
    cases s <;> exact hglobal
  have hAxisα (v : Ctx.Side) : G α v = G σ v := by
    cases v <;> rfl
  have hAxisβ (v : Ctx.Side) : G β v = G σ v := by
    cases v <;> rfl
  have hKα : α.k = σ.k := rfl
  have hKβ : β.k = σ.k := rfl
  have hSLeFive : G σ s ≤ 5 := by
    cases s <;> exact hglobal
  have hTLeFive : G σ t ≤ 5 := by
    cases t <;> exact hopposite
  have hTWidth : 2 ≤ G σ t - 1 := by
    cases t <;> exact hwidth
  have hFiveK : 5 ≤ σ.k := by omega
  have hFiveNext : 5 ≤ σ.k - 1 := by omega
  have hOppositeα : G α t ≤ α.k := by
    rw [hAxisα, hKα]
    exact hTLeFive.trans hFiveK
  have hNextα : G α t ≤ α.k - 1 := by
    rw [hAxisα, hKα]
    exact hTLeFive.trans hFiveNext
  have hkα : 5 ≤ α.k := by
    change 5 ≤ σ.k
    omega
  obtain ⟨direction, hTriple, hBoundaryβ, hYSideβ⟩ : ∃ direction : Bool,
      ((q₀ < x ∧ y < x) ∨ (x < q₀ ∧ x < y)) ∧
      (∀ p ∈ β.childPositions, if direction then p < l else l < p) ∧
      (∀ p ∈ β.childPositions, if direction then p < y else y < p) := by
    rcases horder with ⟨hYKeep, hxy, hEnd⟩ | ⟨hKeepY, hyx, hEnd⟩
    · refine ⟨false, Or.inr ⟨lt_trans hxy (hYKeep q₀ hq₀), hxy⟩, ?_, ?_⟩
      · intro p hp
        have hp' := (hChildβ p).mp hp
        simpa using hEnd p hp'.2 l hl hlnot
      · intro p hp
        simpa using hYKeep p ((hChildβ p).mp hp).2
    · refine ⟨true, Or.inl ⟨lt_trans (hKeepY q₀ hq₀) hyx, hyx⟩, ?_, ?_⟩
      · intro p hp
        have hp' := (hChildβ p).mp hp
        simpa using hEnd p hp'.2 l hl hlnot
      · intro p hp
        simpa using hKeepY p ((hChildβ p).mp hp).2
  have hYoungerβ : ∀ j ∈ β.levelsOn (β.sideAt 1) 1,
      ∀ p ∈ β.extPositions j, if direction then p < l else l < p := by
    simp only [Ctx.Context.levelsOn_one, List.not_mem_nil, false_implies, implies_true]
  have hYOnβ : M + 1 ∈ β.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hMβ, by simp [hMsβ]⟩
  have hOneLeft (p : ℕ) (hp : y < p) : 1 ≤ β.leftExt s 0 p := by
    have hm : y ∈ (β.extPositions (M + 1)).filter (· < p) := by
      simp [hYβ, hp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := (β.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.leftStep β) (p, 0)).2))
      (List.mem_map.mpr ⟨[M + 1],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hYOnβ), rfl⟩)
    change _ ≤ β.leftExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (p : ℕ) (hp : p < y) : 1 ≤ β.rightExt s 0 p := by
    have hm : y ∈ (β.extPositions (M + 1)).filter (p < ·) := by
      simp [hYβ, hp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := (β.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.rightStep β) (p, 0)).2))
      (List.mem_map.mpr ⟨[M + 1],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hYOnβ), rfl⟩)
    change _ ≤ β.rightExt s 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hAlphaLinear : (∀ fuel, Ctx.Context.boundFuel fuel α ≤ 10) ∧
      α.bound ≤ 10 := by
    have hh := ctx_nonmonotone_triple_linear_potential α hPosα s t hne
      1 (N + 1) (M + 1) q₀ x y hOneα hNα hMα (by omega) (by omega)
      hSideα hNsα hMsα hQα hXα hYα hTriple hGlobalα
      (by
        have hw : 1 ≤ G α t - 1 := by
          rw [hAxisα]
          omega
        cases t <;> exact hw)
    have hcap : 3 * (G α t - 1) - 2 ≤ 10 := by
      rw [hAxisα]
      omega
    exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
  have hAlphaNine (hmLarge : 2 ≤ m) :
      (∀ fuel, Ctx.Context.boundFuel fuel α ≤ 9) ∧ α.bound ≤ 9 := by
    have hMaximumα : α.k - 4 ≤ α.maximumAt 1 := by
      rw [Ctx.Context.part_maximumAt_one]
      change σ.k - 4 ≤ m
      omega
    have hh := ctx_nonmonotone_triple_saturated_potential_arbitrary_opposite_history
      α hPosα s t hne 1 (N + 1) (M + 1) q₀ x y hOneα hNα hMα
      (by omega) (by omega) hSideα hNsα hMsα hQα hXα hYα hTriple
      hGlobalα (by cases t <;> exact hOppositeα) hkα 1 hOneα hSideα hMaximumα
    have hnine : 3 * α.k - 9 ≤ 9 := by
      change 3 * σ.k - 9 ≤ 9
      omega
    have hn := hh.2.2 (by cases t <;> exact hNextα)
    exact ⟨fun fuel => (hn.1 fuel).trans hnine, hn.2.trans hnine⟩
  have hTerminalβ : ∀ j ∈ β.levelsOn (β.sideAt 1) 0, j ≤ 1 := by
    intro j hj
    rw [hSideβ, Ctx.Context.part_levelsOn_self_zero hSideβ, hclear] at hj
    have hj1 : j = 1 := by simpa using hj
    omega
  have hBetaThree (hnThree : n = 3) :
      (∀ fuel, Ctx.Context.boundFuel fuel β ≤ 3) ∧ β.bound ≤ 3 := by
    have hMaximumβ : β.maximumAt 1 = n := Ctx.Context.part_maximumAt_one σ keep t n
    have hSmall : min (G β (β.sideAt 1) - 1) (β.k - β.maximumAt 1) ≤ 3 := by
      rw [hSideβ, hMaximumβ]
      refine (Nat.min_le_right _ _).trans ?_
      rw [hKβ, hnThree, hk]
    cases hd : direction
    · have hh := ctx_boundary_marker_full_rank_budget β hPosβ 1 l hOneβ hLβ
        false (by simpa only [hd] using hBoundaryβ) (by simpa only [hd] using hYoungerβ)
        hTerminalβ s (by rw [hSideβ]; exact Ne.symm hne) (by simpa only [G] using hSmall)
        1 0 (fun p hp => hOneLeft p (by simpa only [hd] using hYSideβ p hp))
        (by intros; omega)
      have hcap : G β s - 1 - 1 - 0 ≤ 3 := by
        rw [hAxisβ]
        omega
      exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
    · have hh := ctx_boundary_marker_full_rank_budget β hPosβ 1 l hOneβ hLβ
        true (by simpa only [hd] using hBoundaryβ) (by simpa only [hd] using hYoungerβ)
        hTerminalβ s (by rw [hSideβ]; exact Ne.symm hne) (by simpa only [G] using hSmall)
        0 1 (by intros; omega)
        (fun p hp => hOneRight p (by simpa only [hd] using hYSideβ p hp))
      have hcap : G β s - 1 - 0 - 1 ≤ 3 := by
        rw [hAxisβ]
        omega
      exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
  have hAlphaFour (hmThree : m = 3) :
      (∀ fuel, Ctx.Context.boundFuel fuel α ≤ 4) ∧ α.bound ≤ 4 := by
    have hMaximumα : α.k - 3 ≤ α.maximumAt 1 := by
      rw [Ctx.Context.part_maximumAt_one]
      change σ.k - 3 ≤ m
      omega
    have hh := ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three
      α hPosα s t hne 1 hOneα hSideα hMaximumα
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · have hcap : α.a - 1 ≤ 4 := by
        change σ.a - 1 ≤ 4
        simpa only [G] using (show G σ Ctx.Side.upper - 1 ≤ 4 by omega)
      exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
    · have hcap : α.u - 1 ≤ 4 := by
        change σ.u - 1 ≤ 4
        simpa only [G] using (show G σ Ctx.Side.lower - 1 ≤ 4 by omega)
      exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
    · exact False.elim (hne rfl)
  have hDouble (v : Ctx.Side) (c : ℕ) :
      σ.part (σ.childPositions.filter (· ∉ rest)) v c = σ.part keep v c := by
    apply part_congr
    intro p hp
    simp only [rest, List.mem_filter, decide_eq_true_eq, hp, true_and, not_not]
  have hCompanion := ctx_two_actual_marker_companion_maximum_bound σ hpositive s t hne
    N M x y hN hM hNM hNs hMs hx hy hglobal rest m n l q₀
    ((hChildα l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)) (hkeep q₀ hq₀)
    (by simp only [rest, List.mem_filter, decide_eq_true_eq, hkeep q₀ hq₀,
      true_and, not_true_eq_false, not_false_eq_true, hq₀])
  rw [hDouble t n] at hCompanion
  have hBetaEight (hnTwo : n = 2) :
      (∀ fuel, Ctx.Context.boundFuel fuel β ≤ 8) ∧ β.bound ≤ 8 := by
    have hbudget : σ.k - n - 1 = 3 := by omega
    change (∀ fuel, Ctx.Context.boundFuel fuel (σ.part keep t n) ≤ 8) ∧
      (σ.part keep t n).bound ≤ 8
    simpa only [hbudget] using hCompanion
  have hBetaEleven : (∀ fuel, Ctx.Context.boundFuel fuel β ≤ 11) ∧
      β.bound ≤ 11 := by
    let τ : Ctx.Context := match β.sideAt 1 with
      | Ctx.Side.lower =>
          { β with u := min (β.u - 1) (β.k - β.maximumAt 1), maxima := β.maxima.take 0 }
      | Ctx.Side.upper =>
          { β with a := min (β.a - 1) (β.k - β.maximumAt 1), maxima := β.maxima.take 0 }
    have hNorm := ctx_boundary_marker_upper_normalize β hPosβ 1 l hOneβ hLβ
      direction hBoundaryβ hYoungerβ
    have hFuelNorm : ∀ fuel, Ctx.Context.boundFuel fuel β ≤
        Ctx.Context.boundFuel fuel τ := by
      simpa only [τ, Nat.sub_self] using hNorm.2.1
    have hBoundNorm : β.bound ≤ τ.bound := by
      simpa only [τ, Nat.sub_self] using hNorm.2.2
    have hτWord : τ.word = β.word := by
      cases hs : β.sideAt 1 <;> simp only [τ, hs]
    have hτLetter (p : ℕ) : τ.letterAt p = β.letterAt p := by
      simp only [Ctx.Context.letterAt, hτWord]
    have hτPositive : ∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j := by
      intro p j v hp
      rw [hτLetter] at hp
      exact hPosβ p j v hp
    have hτK : τ.k = σ.k := by
      cases h : β.sideAt 1 <;> simpa only [τ, h] using hKβ
    have hChosenβ : G β t ≤ 5 := by
      rw [hAxisβ]
      exact hopposite
    have hτSmall : G τ t ≤ 4 := by
      cases t with
      | lower =>
          simp only [G, τ, hSideβ]
          exact (Nat.min_le_left _ _).trans (by
            simp only [G] at hChosenβ
            omega)
      | upper =>
          simp only [G, τ, hSideβ]
          exact (Nat.min_le_left _ _).trans (by
            simp only [G] at hChosenβ
            omega)
    have hτOther : G τ s = G β s := by
      cases t <;> cases s
      · exact False.elim (hne rfl)
      · simp only [G, τ, hSideβ]
      · simp only [G, τ, hSideβ]
      · exact False.elim (hne rfl)
    have hτOpposite : G τ s ≤ τ.k := by
      rw [hτOther, hAxisβ, hτK]
      exact hSLeFive.trans hFiveK
    have hSat := ctx_small_global_axis_saturated_triangle_bound τ hτPositive
      t s (Ne.symm hne) (by cases t <;> exact hτSmall)
      (by cases s <;> exact hτOpposite) (by rw [hτK]; omega)
    have hcap : (τ.k - 2).choose 2 + (τ.k - 1) ≤ 11 := by
      rw [hτK, hk]
      decide
    exact ⟨fun fuel => (hFuelNorm fuel).trans ((hSat.1 fuel).trans hcap),
      hBoundNorm.trans (hSat.2.1.trans hcap)⟩
  have hmUpper : m ≤ 4 := by omega
  by_cases hmOne : m = 1
  · have hnFour : n = 4 := by omega
    have hMaximumβ : β.k - 2 ≤ β.maximumAt 1 := by
      rw [Ctx.Context.part_maximumAt_one]
      change σ.k - 2 ≤ n
      omega
    have hBetaOne := ctx_bound_le_one_of_large_sibling_maximum β hPosβ 1 hOneβ hMaximumβ
    exact ⟨fun f g => (Nat.add_le_add (hAlphaLinear.1 f) (hBetaOne.1 g)).trans (by omega),
      (Nat.add_le_add hAlphaLinear.2 hBetaOne.2).trans (by omega)⟩
  by_cases hmFour : m = 4
  · have hMaximumα : α.k - 2 ≤ α.maximumAt 1 := by
      rw [Ctx.Context.part_maximumAt_one]
      change σ.k - 2 ≤ m
      omega
    have hAlphaOne := ctx_bound_le_one_of_large_sibling_maximum α hPosα 1 hOneα hMaximumα
    exact ⟨fun f g => (Nat.add_le_add (hAlphaOne.1 f) (hBetaEleven.1 g)).trans (by omega),
      (Nat.add_le_add hAlphaOne.2 hBetaEleven.2).trans (by omega)⟩
  by_cases hmTwo : m = 2
  · have hnThree : n = 3 := by omega
    have hA := hAlphaNine (by omega)
    have hB := hBetaThree hnThree
    exact ⟨fun f g => (Nat.add_le_add (hA.1 f) (hB.1 g)).trans (by omega),
      (Nat.add_le_add hA.2 hB.2).trans (by omega)⟩
  · have hmThree : m = 3 := by omega
    have hnTwo : n = 2 := by omega
    have hA := hAlphaFour hmThree
    have hB := hBetaEight hnTwo
    exact ⟨fun f g => (Nat.add_le_add (hA.1 f) (hB.1 g)).trans (by omega),
      (Nat.add_le_add hA.2 hB.2).trans (by omega)⟩

end ErdosSzekeres
