import ESBlueprint.B.CtxSurroundedOlderMarkerEndpointComplementWidthBound
import ESBlueprint.B.CtxTwoMarkerTriangularLinearRankBudget
import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum
import ESBlueprint.B.CtxBoundLeOppositeWidthOfSiblingMaximumGeKMinusThree
import ESBlueprint.B.CtxTwoActualMarkerCompanionMaximumBound
import ESBlueprint.B.CtxPartPositiveLetters

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At k=6, an endpoint cut whose kept side surrounds the older of two actual chosen markers satisfies the exact coupled budget twelve. The chosen complement costs at most the opposite width; the four legal new maxima are paired with a saturated sibling-one bound, normalized width bound, sharp two-marker companion bound, or the coarse endpoint rank budget. Positive labels, both globals at most five, arbitrary opposite history, inactive children, endpoint orientation, and independent fuels remain explicit. Exact search found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_surrounded_older_marker_endpoint_complement_width_bound, ErdosSzekeres.ctx_two_marker_triangular_linear_rank_budget, ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum, ErdosSzekeres.ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three, ErdosSzekeres.ctx_two_actual_marker_companion_maximum_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_older_surrounding_endpoint_cut_six_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (a b l m n : ℕ) (ha : a ∈ keep) (hb : b ∈ keep) (hsurround : a < y ∧ y < b) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hlnot : l ∉ keep) (endpoint : Bool) (hendpoint : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → if endpoint then q < p else p < q) (hk : σ.k = 6) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12 := by
  classical
  let w := (match (generalizing := false) t with
    | Side.lower => σ.u
    | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  let β := σ.part keep t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ 12) ∧
    α.bound + β.bound ≤ 12
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ rest := by
    simp only [α, part_childPositions, rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔
      p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hChildβ (p : ℕ) : p ∈ β.childPositions ↔
      p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [β, part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ rest := by
    rw [part_extPositions_one hpositive]
  have hAα : a ∈ α.extPositions 1 := (hExtα a).mpr ⟨hkeep a ha, ha⟩
  have hBα : b ∈ α.extPositions 1 := (hExtα b).mpr ⟨hkeep b hb, hb⟩
  have hLβ : l ∈ β.extPositions 1 :=
    (hExtβ l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
  have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive rest s m hAα
  have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t n hLβ
  have hPosα := ctx_part_positive_letters σ rest s m
  have hPosβ := ctx_part_positive_letters σ keep t n
  have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
  have hOneβ : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
  have hNpos := one_le_of_mem_levels hN
  have hMpos := one_le_of_mem_levels hM
  have hNα : N + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hMα : M + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hNβ : N + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hMβ : M + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hNsα : α.sideAt (N + 1) = s := (part_sideAt_succ σ rest s m hNpos).trans hNs
  have hMsα : α.sideAt (M + 1) = s := (part_sideAt_succ σ rest s m hMpos).trans hMs
  have hNsβ : β.sideAt (N + 1) = s := (part_sideAt_succ σ keep t n hNpos).trans hNs
  have hMsβ : β.sideAt (M + 1) = s := (part_sideAt_succ σ keep t n hMpos).trans hMs
  have hXα : x ∈ α.extPositions (N + 1) := by
    rw [part_extPositions_succ σ rest s m hNpos]
    exact hx
  have hYα : y ∈ α.extPositions (M + 1) := by
    rw [part_extPositions_succ σ rest s m hMpos]
    exact hy
  have hXβ : x ∈ β.extPositions (N + 1) := by
    rw [part_extPositions_succ σ keep t n hNpos]
    exact hx
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
  have hBeforeN : ∀ j ∈ α.levelsOn s (N + 1),
      ∀ p ∈ α.extPositions j, j = 1 := by
    intro j hj p hp
    have hj' := hAlphaBelow (N + 1) j hj
    rcases hAlphaActual j hj'.1 p hp with ⟨hj1, _⟩ | ⟨hjN, _⟩ | ⟨hjM, _⟩
    · exact hj1
    · omega
    · omega
  have hBeforeM : ∀ j ∈ α.levelsOn s (M + 1),
      ∀ p ∈ α.extPositions j, j = 1 ∨ (j = N + 1 ∧ p = x) := by
    intro j hj p hp
    have hj' := hAlphaBelow (M + 1) j hj
    rcases hAlphaActual j hj'.1 p hp with ⟨hj1, _⟩ | ⟨hjN, hpx⟩ | ⟨hjM, _⟩
    · exact Or.inl hj1
    · exact Or.inr ⟨hjN, hpx⟩
    · omega
  have hEndα : ∀ p ∈ α.childPositions,
      if endpoint then p < a else b < p := by
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
  have hOwn := ctx_surrounded_older_marker_endpoint_complement_width_bound
    α hPosα s t hne 1 (N + 1) (M + 1) a b x y hOneα hNα hMα
    (by omega) (by omega) hSideα hNsα hMsα hAα hBα hXα hYα
    hsurround.1 hsurround.2 hOutside hBeforeN hBeforeM
    (by cases s <;> exact hglobal) endpoint hEndα
  have hw : 2 ≤ w := hwidth
  have hwUpper : w ≤ 4 := by
    dsimp only [w]
    cases t <;> simp only at hopposite ⊢ <;> omega
  have hOwnFour : (∀ fuel, boundFuel fuel α ≤ 4) ∧ α.bound ≤ 4 :=
    ⟨fun fuel => (hOwn.1 fuel).trans hwUpper, hOwn.2.trans hwUpper⟩
  have hOneLeft (ρ : Context) (v : Side) (top j p q : ℕ)
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
  have hOneRight (ρ : Context) (v : Side) (top j p q : ℕ)
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
  have hLossLeft (top : ℕ) (htop : 1 < top) (he : endpoint = true) :
      ∀ p ∈ β.childPositions, 1 ≤ β.leftExt t top p := by
    intro p hp
    have hOn : 1 ∈ β.levelsOn t top :=
      List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ, htop]⟩
    have hlp : l < p := by
      simpa [he] using hendpoint p ((hChildβ p).mp hp).2 l hl hlnot
    exact hOneLeft β t top 1 p l hOn hLβ hlp
  have hLossRight (top : ℕ) (htop : 1 < top) (he : endpoint = false) :
      ∀ p ∈ β.childPositions, 1 ≤ β.rightExt t top p := by
    intro p hp
    have hOn : 1 ∈ β.levelsOn t top :=
      List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ, htop]⟩
    have hpl : p < l := by
      simpa [he] using hendpoint p ((hChildβ p).mp hp).2 l hl hlnot
    exact hOneRight β t top 1 p l hOn hLβ hpl
  have hCoarse : (∀ fuel, boundFuel fuel β ≤ w.choose 2 + (w - 1)) ∧
      β.bound ≤ w.choose 2 + (w - 1) := by
    have hChosenβ : ∀ j ∈ β.levelsOn s 0, ∀ p ∈ β.extPositions j,
        p = x ∨ p = y := by
      intro j hj p hp
      rcases hBetaActual j hj p hp with ⟨_, hpx⟩ | ⟨_, hpy⟩
      · exact Or.inl hpx
      · exact Or.inr hpy
    have hew : w - 1 + 1 = w := by omega
    cases he : endpoint
    · have hh := ctx_two_marker_triangular_linear_rank_budget β hPosβ s t hne
        (N + 1) (M + 1) x y hNβ hMβ (by omega) hNsβ hMsβ hXβ hYβ
        hglobal hChosenβ 0 1 (by intros; omega) (hLossRight (N + 1) (by omega) he)
      change (∀ fuel, boundFuel fuel β ≤ (w - 0 - 1 + 1).choose 2 + (w - 0 - 1)) ∧
        β.bound ≤ (w - 0 - 1 + 1).choose 2 + (w - 0 - 1) at hh
      simpa only [Nat.sub_zero, hew] using hh
    · have hh := ctx_two_marker_triangular_linear_rank_budget β hPosβ s t hne
        (N + 1) (M + 1) x y hNβ hMβ (by omega) hNsβ hMsβ hXβ hYβ
        hglobal hChosenβ 1 0 (hLossLeft (N + 1) (by omega) he) (by intros; omega)
      change (∀ fuel, boundFuel fuel β ≤ (w - 1 - 0 + 1).choose 2 + (w - 1 - 0)) ∧
        β.bound ≤ (w - 1 - 0 + 1).choose 2 + (w - 1 - 0) at hh
      simpa only [Nat.sub_zero, hew] using hh
  have hChooseSix : w.choose 2 ≤ 6 :=
    (Nat.choose_le_choose 2 hwUpper).trans (by decide)
  have hCoarseNine : (∀ fuel, boundFuel fuel β ≤ 9) ∧ β.bound ≤ 9 :=
    ⟨fun fuel => (hCoarse.1 fuel).trans (by omega), hCoarse.2.trans (by omega)⟩
  have hDouble (v : Side) (c : ℕ) :
      σ.part (σ.childPositions.filter (· ∉ rest)) v c = σ.part keep v c := by
    apply part_congr
    intro p hp
    simp only [rest, List.mem_filter, decide_eq_true_eq, hp, true_and, not_not]
  have hCompanion := ctx_two_actual_marker_companion_maximum_bound σ hpositive s t hne
    N M x y hN hM hNM hNs hMs hx hy hglobal rest m n l a
    ((hChildα l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)) (hkeep a ha)
    (by simp only [rest, List.mem_filter, decide_eq_true_eq, hkeep a ha,
      true_and, not_true_eq_false, not_false_eq_true, ha])
  rw [hDouble t n] at hCompanion
  have hBetaEight (hnTwo : n = 2) :
      (∀ fuel, boundFuel fuel β ≤ 8) ∧ β.bound ≤ 8 := by
    have hbudget : σ.k - n - 1 = 3 := by omega
    change (∀ fuel, boundFuel fuel (σ.part keep t n) ≤ 8) ∧
      (σ.part keep t n).bound ≤ 8
    simpa only [hbudget] using hCompanion
  have hmUpper : m ≤ 4 := by omega
  by_cases hmOne : m = 1
  · have hnFour : n = 4 := by omega
    have hMaximumβ : β.k - 2 ≤ β.maximumAt 1 := by
      rw [part_maximumAt_one]
      change σ.k - 2 ≤ n
      omega
    have hBetaOne := ctx_bound_le_one_of_large_sibling_maximum
      β hPosβ 1 hOneβ hMaximumβ
    exact ⟨fun f g => (Nat.add_le_add (hOwnFour.1 f) (hBetaOne.1 g)).trans (by omega),
      (Nat.add_le_add hOwnFour.2 hBetaOne.2).trans (by omega)⟩
  by_cases hmFour : m = 4
  · have hMaximumα : α.k - 2 ≤ α.maximumAt 1 := by
      rw [part_maximumAt_one]
      change σ.k - 2 ≤ m
      omega
    have hAlphaOne := ctx_bound_le_one_of_large_sibling_maximum
      α hPosα 1 hOneα hMaximumα
    exact ⟨fun f g => (Nat.add_le_add (hAlphaOne.1 f) (hCoarseNine.1 g)).trans (by omega),
      (Nat.add_le_add hAlphaOne.2 hCoarseNine.2).trans (by omega)⟩
  by_cases hmTwo : m = 2
  · have hnThree : n = 3 := by omega
    have hMaximumβ : β.k - 3 ≤ β.maximumAt 1 := by
      rw [part_maximumAt_one]
      change σ.k - 3 ≤ n
      omega
    have hBetaWidth := ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three
      β hPosβ t s (Ne.symm hne) 1 hOneβ hSideβ hMaximumβ
    have hBetaFour : (∀ fuel, boundFuel fuel β ≤ 4) ∧ β.bound ≤ 4 := by
      cases t <;> cases s
      · exact False.elim (hne rfl)
      · have hcap : β.a - 1 ≤ 4 := by
          change σ.a - 1 ≤ 4
          simp only at hglobal
          omega
        exact ⟨fun fuel => (hBetaWidth.1 fuel).trans hcap,
          hBetaWidth.2.trans hcap⟩
      · have hcap : β.u - 1 ≤ 4 := by
          change σ.u - 1 ≤ 4
          simp only at hglobal
          omega
        exact ⟨fun fuel => (hBetaWidth.1 fuel).trans hcap,
          hBetaWidth.2.trans hcap⟩
      · exact False.elim (hne rfl)
    exact ⟨fun f g => (Nat.add_le_add (hOwnFour.1 f) (hBetaFour.1 g)).trans (by omega),
      (Nat.add_le_add hOwnFour.2 hBetaFour.2).trans (by omega)⟩
  · have hmThree : m = 3 := by omega
    have hnTwo : n = 2 := by omega
    have hBeta := hBetaEight hnTwo
    exact ⟨fun f g => (Nat.add_le_add (hOwnFour.1 f) (hBeta.1 g)).trans (by omega),
      (Nat.add_le_add hOwnFour.2 hBeta.2).trans (by omega)⟩

end ErdosSzekeres
