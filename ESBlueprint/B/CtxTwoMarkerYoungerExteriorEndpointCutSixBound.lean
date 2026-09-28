import ESBlueprint.B.CtxTwoMarkerOlderExteriorEndpointCutSixBound
import ESBlueprint.B.CtxActiveBoundaryMarkerRankPairUnionBound

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At k=6, a younger-exterior endpoint cut with clear opposite history satisfies the exact coupled budget twelve. The two small chosen maxima use the boundary rank-pair charge ten plus two ordered full-history ranks in the companion; the two large maxima use sibling normalization with the sharp companion and the unit-plus-normalized-triangle endpoint. Arbitrary old maxima, inactive children, endpoint length and fuels remain explicit. Exact search found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_active_boundary_marker_rank_pair_union_bound, ErdosSzekeres.ctx_boundary_marker_full_rank_budget, ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum, ErdosSzekeres.ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three, ErdosSzekeres.ctx_two_actual_marker_companion_maximum_bound, ErdosSzekeres.ctx_boundary_marker_upper_normalize, ErdosSzekeres.ctx_small_global_axis_saturated_triangle_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_younger_exterior_endpoint_cut_six_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (hclear : σ.levelsOn t 0 = []) (keep : List ℕ) (q₀ l m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hlnot : l ∉ keep) (horder : ((∀ p ∈ keep, p < x) ∧ x < y ∧ ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → p < q) ∨ ((∀ p ∈ keep, x < p) ∧ y < x ∧ ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → q < p)) (hk : σ.k = 6) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12 := by
  classical
  ·
    let G (ρ : Ctx.Context) (v : Ctx.Side) := match v with
      | Ctx.Side.lower => ρ.u
      | Ctx.Side.upper => ρ.a
    let w := G σ t - 1
    let rest := σ.childPositions.filter (· ∉ keep)
    let α := σ.part rest s m
    let β := σ.part keep t n
    change (∀ f g, boundFuel f α + boundFuel g β ≤ 12) ∧ α.bound + β.bound ≤ 12
    have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
      simp only [rest, List.mem_filter, decide_eq_true_eq]
    have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ rest := by
      simp only [α, part_childPositions, rest, List.mem_filter, decide_eq_true_eq]
      tauto
    have hChildβ (p : ℕ) : p ∈ β.childPositions ↔
        p ∈ σ.childPositions ∧ p ∈ keep := by
      simp only [β, part_childPositions, List.mem_filter, decide_eq_true_eq]
    have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔
        p ∈ σ.childPositions ∧ p ∈ keep := by
      rw [part_extPositions_one hpositive]
      simp only [rest, List.mem_filter, decide_eq_true_eq]
      tauto
    have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ rest := by
      rw [part_extPositions_one hpositive]
    have hQα : q₀ ∈ α.extPositions 1 :=
      (hExtα q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
    have hLβ : l ∈ β.extPositions 1 :=
      (hExtβ l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
    have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive rest s m hQα
    have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t n hLβ
    have hPosα := ctx_part_positive_letters σ rest s m
    have hPosβ := ctx_part_positive_letters σ keep t n
    have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
    have hOneβ : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
    have hNpos := one_le_of_mem_levels hN
    have hMpos := one_le_of_mem_levels hM
    have hNβ : N + 1 ∈ β.levels := by
      rw [part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
    have hMβ : M + 1 ∈ β.levels := by
      rw [part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
    have hNsβ : β.sideAt (N + 1) = s :=
      (part_sideAt_succ σ keep t n hNpos).trans hNs
    have hMsβ : β.sideAt (M + 1) = s :=
      (part_sideAt_succ σ keep t n hMpos).trans hMs
    have hXβ : x ∈ β.extPositions (N + 1) := by
      rw [part_extPositions_succ σ keep t n hNpos]
      exact hx
    have hYβ : y ∈ β.extPositions (M + 1) := by
      rw [part_extPositions_succ σ keep t n hMpos]
      exact hy
    have hAxisα (v : Ctx.Side) : G α v = G σ v := by cases v <;> rfl
    have hAxisβ (v : Ctx.Side) : G β v = G σ v := by cases v <;> rfl
    have hKβ : β.k = σ.k := rfl
    have hSLeFive : G σ s ≤ 5 := by cases s <;> exact hglobal
    have hTLeFive : G σ t ≤ 5 := by cases t <;> exact hopposite
    obtain ⟨direction, hOutside, hOldOrder, hEnd⟩ : ∃ direction : Bool,
        (∀ p ∈ keep, if direction then p < x else x < p) ∧
        (if direction then x < y else y < x) ∧
        (∀ p ∈ keep, ∀ q ∈ rest, if direction then p < q else q < p) := by
      rcases horder with ⟨hOut, hXY, hEnd⟩ | ⟨hOut, hYX, hEnd⟩
      · exact ⟨true, hOut, hXY,
          fun p hp q hq => hEnd p hp q ((hRest q).mp hq).1 ((hRest q).mp hq).2⟩
      · exact ⟨false, hOut, hYX,
          fun p hp q hq => hEnd p hp q ((hRest q).mp hq).1 ((hRest q).mp hq).2⟩
    let active := α.childPositions.toFinset.filter
      (fun p => 0 < α.cupLimit p p ∧ 0 < α.capLimit p p)
    let I (p : ℕ) := Finset.Icc (α.leftExt t 0 p + 1) (w - α.rightExt t 0 p)
    let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
    let pairs := active.biUnion (fun p => Q (I p))
    have hCardPairs (T : Finset ℕ) : (Q T).card = (T.card + 1).choose 2 := by
      rw [← Finset.card_sym2]
      apply Finset.card_bij (fun z _ => Sym2.mk z.1 z.2)
      · intro z hz
        exact Finset.mk_mem_sym2_iff.mpr
          (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
      · intro p hp q hq he
        have hpl := (Finset.mem_filter.mp hp).2
        have hql := (Finset.mem_filter.mp hq).2
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext h1 h2
        · apply Prod.ext <;> omega
      · intro z hz
        induction z using Sym2.ind with
        | h a b =>
            obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hz
            by_cases hab : a ≤ b
            · exact ⟨(a, b), Finset.mem_filter.mpr
                ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
            · exact ⟨(b, a), Finset.mem_filter.mpr
                ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩, Sym2.eq_swap⟩
    have hAlphaTen : (∀ fuel, boundFuel fuel α ≤ 10) ∧ α.bound ≤ 10 := by
      have hSmallG : min ((match α.sideAt 1 with
          | Side.lower => α.u | Side.upper => α.a) - 1)
          (α.k - α.maximumAt 1) ≤ 4 := by
        rw [hSideα]
        apply (Nat.min_le_left _ _).trans
        have hs : G α s - 1 ≤ 4 := by
          rw [hAxisα]
          omega
        cases s <;> exact hs
      have hh := ctx_active_boundary_marker_rank_pair_union_bound α hPosα 1 q₀
        hOneα hQα (!direction)
        (by
          intro p hp _
          have he := hEnd q₀ hq₀ p ((hChildα p).mp hp)
          cases direction <;> simpa using he)
        (by simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true])
        t (by rw [hSideα]; exact hne) hSmallG
      change (∀ fuel, boundFuel fuel α ≤ pairs.card) ∧ α.bound ≤ pairs.card at hh
      have hSub : pairs ⊆ Q (Finset.Icc 1 w) := by
        intro z hz
        obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
        have hz' := Finset.mem_filter.mp hz
        obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hz'.1
        have hza' := Finset.mem_Icc.mp hza
        have hzb' := Finset.mem_Icc.mp hzb
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
            Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, hz'.2⟩
      have hcard : (Q (Finset.Icc 1 w)).card = (w + 1).choose 2 := by
        rw [hCardPairs]
        have hc : (Finset.Icc 1 w).card = w := by
          simp only [Nat.card_Icc]
          omega
        rw [hc]
      have hPairBound := (Finset.card_le_card hSub).trans_eq hcard
      have hTen : (w + 1).choose 2 ≤ 10 := by
        have hw5 : w + 1 ≤ 5 := by dsimp only [w]; omega
        exact (Nat.choose_le_choose 2 hw5).trans (by decide)
      exact ⟨fun fuel => (hh.1 fuel).trans (hPairBound.trans hTen),
        hh.2.trans (hPairBound.trans hTen)⟩
    have hNOnβ : N + 1 ∈ β.levelsOn s 0 :=
      List.mem_filter.mpr ⟨hNβ, by simp [hNsβ]⟩
    have hMOnβ : M + 1 ∈ β.levelsOn s 0 :=
      List.mem_filter.mpr ⟨hMβ, by simp [hMsβ]⟩
    have hSortedβ : (β.levelsOn s 0).Pairwise (· < ·) := by
      unfold levelsOn levels
      exact (List.pairwise_lt_range.map (fun i => i + 1)
        (fun i j h => Nat.add_lt_add_right h 1)).filter _
    have hTwoLevels : [N + 1, M + 1].Sublist (β.levelsOn s 0) := by
      have hs : [N + 1, M + 1].Pairwise (· < ·) := by simp; omega
      have hsub : [N + 1, M + 1] ⊆ β.levelsOn s 0 := by
        intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hNOnβ
        · exact hMOnβ
      have he : (β.levelsOn s 0).filter (· ∈ [N + 1, M + 1]) =
          [N + 1, M + 1] := by
        apply (hSortedβ.filter _).eq_of_mem_iff hs
        intro j
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨And.right, fun hj => ⟨hsub hj, hj⟩⟩
      rw [← he]
      exact List.filter_sublist
    have hTwoRight (p : ℕ) (hpx : p < x) (hxy : x < y) :
        2 ≤ β.rightExt s 0 p := by
      have hmX : x ∈ (β.extPositions (N + 1)).filter (p < ·) := by simp [hXβ, hpx]
      have hneX := List.ne_nil_of_mem hmX
      let u := ((β.extPositions (N + 1)).filter (p < ·)).head hneX
      have hu : ((β.extPositions (N + 1)).filter (p < ·)).head? = some u :=
        List.head?_eq_some_head hneX
      have hux : u ≤ x :=
        ((List.pairwise_lt_range.filter _).imp le_of_lt).filter (p < ·) |>.rel_head hmX
      have hmY : y ∈ (β.extPositions (M + 1)).filter (u < ·) := by
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨hYβ, by omega⟩
      have hneY := List.ne_nil_of_mem hmY
      have hv := le_getD_max?_of_mem
        (L := (β.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (rightStep β) (p, 0)).2))
        (List.mem_map.mpr ⟨[N + 1, M + 1], List.mem_sublists.mpr hTwoLevels, rfl⟩)
      change _ ≤ β.rightExt s 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, rightStep, hu,
        List.head?_eq_some_head hneY] using hv
    have hTwoLeft (p : ℕ) (hyx : y < x) (hxp : x < p) :
        2 ≤ β.leftExt s 0 p := by
      have hmX : x ∈ (β.extPositions (N + 1)).filter (· < p) := by simp [hXβ, hxp]
      have hneX := List.ne_nil_of_mem hmX
      let u := ((β.extPositions (N + 1)).filter (· < p)).getLast hneX
      have hu : ((β.extPositions (N + 1)).filter (· < p)).getLast? = some u :=
        List.getLast?_eq_some_getLast hneX
      have hxu : x ≤ u :=
        ((List.pairwise_lt_range.filter _).imp le_of_lt).filter (· < p) |>.rel_getLast hmX
      have hmY : y ∈ (β.extPositions (M + 1)).filter (· < u) := by
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨hYβ, by omega⟩
      have hneY := List.ne_nil_of_mem hmY
      have hv := le_getD_max?_of_mem
        (L := (β.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (leftStep β) (p, 0)).2))
        (List.mem_map.mpr ⟨[N + 1, M + 1], List.mem_sublists.mpr hTwoLevels, rfl⟩)
      change _ ≤ β.leftExt s 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, leftStep, hu,
        List.getLast?_eq_some_getLast hneY] using hv
    have hTerminalβ : ∀ j ∈ β.levelsOn (β.sideAt 1) 0, j ≤ 1 := by
      intro j hj
      rw [hSideβ, part_levelsOn_self_zero hSideβ, hclear] at hj
      have hj1 : j = 1 := by simpa using hj
      omega
    have hBoundaryβ : ∀ p ∈ β.childPositions,
        if direction then p < l else l < p := by
      intro p hp
      have hp' := (hChildβ p).mp hp
      have he := hEnd p hp'.2 l ((hRest l).mpr ⟨hl, hlnot⟩)
      cases direction <;> simpa using he
    have hYoungerβ : ∀ j ∈ β.levelsOn (β.sideAt 1) 1,
        ∀ p ∈ β.extPositions j, if direction then p < l else l < p := by
      simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true]
    have hBetaTwo (hnLarge : 3 ≤ n) :
        (∀ fuel, boundFuel fuel β ≤ 2) ∧ β.bound ≤ 2 := by
      have hMaximumβ : β.maximumAt 1 = n := part_maximumAt_one σ keep t n
      have hSmall : min ((match β.sideAt 1 with
          | Side.lower => β.u | Side.upper => β.a) - 1)
          (β.k - β.maximumAt 1) ≤ 3 := by
        rw [hMaximumβ]
        exact (Nat.min_le_right _ _).trans (by rw [hKβ, hk]; omega)
      cases hd : direction
      · have hh := ctx_boundary_marker_full_rank_budget β hPosβ 1 l hOneβ hLβ
          false (by simpa only [hd] using hBoundaryβ)
          (by simpa only [hd] using hYoungerβ) hTerminalβ s
          (by rw [hSideβ]; exact Ne.symm hne) hSmall 2 0
          (fun p hp => hTwoLeft p (by simpa only [hd] using hOldOrder)
            (by simpa only [hd] using hOutside p ((hChildβ p).mp hp).2))
          (by intros; omega)
        have hcap : G β s - 1 - 2 - 0 ≤ 2 := by rw [hAxisβ]; omega
        exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
      · have hh := ctx_boundary_marker_full_rank_budget β hPosβ 1 l hOneβ hLβ
          true (by simpa only [hd] using hBoundaryβ)
          (by simpa only [hd] using hYoungerβ) hTerminalβ s
          (by rw [hSideβ]; exact Ne.symm hne) hSmall 0 2
          (by intros; omega)
          (fun p hp => hTwoRight p
            (by simpa only [hd] using hOutside p ((hChildβ p).mp hp).2)
            (by simpa only [hd] using hOldOrder))
        have hcap : G β s - 1 - 0 - 2 ≤ 2 := by rw [hAxisβ]; omega
        exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
    have hAlphaFour (hmThree : m = 3) :
        (∀ fuel, boundFuel fuel α ≤ 4) ∧ α.bound ≤ 4 := by
      have hMaximumα : α.k - 3 ≤ α.maximumAt 1 := by
        rw [part_maximumAt_one]
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
    have hCompanion := ctx_two_actual_marker_companion_maximum_bound σ hpositive
      s t hne N M x y hN hM hNM hNs hMs hx hy hglobal rest m n l q₀
      ((hChildα l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)) (hkeep q₀ hq₀)
      (by simp only [rest, List.mem_filter, decide_eq_true_eq, hkeep q₀ hq₀,
        true_and, not_true_eq_false, not_false_eq_true, hq₀])
    rw [hDouble t n] at hCompanion
    have hBetaEight (hnTwo : n = 2) :
        (∀ fuel, boundFuel fuel β ≤ 8) ∧ β.bound ≤ 8 := by
      have hbudget : σ.k - n - 1 = 3 := by omega
      change (∀ fuel, boundFuel fuel (σ.part keep t n) ≤ 8) ∧
        (σ.part keep t n).bound ≤ 8
      simpa only [hbudget] using hCompanion
    have hBetaEleven : (∀ fuel, boundFuel fuel β ≤ 11) ∧ β.bound ≤ 11 := by
      let τ : Ctx.Context := match β.sideAt 1 with
        | Side.lower =>
            { β with u := min (β.u - 1) (β.k - β.maximumAt 1), maxima := β.maxima.take 0 }
        | Side.upper =>
            { β with a := min (β.a - 1) (β.k - β.maximumAt 1), maxima := β.maxima.take 0 }
      have hNorm := ctx_boundary_marker_upper_normalize β hPosβ 1 l hOneβ hLβ
        direction hBoundaryβ hYoungerβ
      have hFuelNorm : ∀ fuel, boundFuel fuel β ≤ boundFuel fuel τ := by
        simpa only [τ, Nat.sub_self] using hNorm.2.1
      have hBoundNorm : β.bound ≤ τ.bound := by
        simpa only [τ, Nat.sub_self] using hNorm.2.2
      have hτWord : τ.word = β.word := by
        cases hs : β.sideAt 1 <;> simp only [τ, hs]
      have hτLetter (p : ℕ) : τ.letterAt p = β.letterAt p := by
        simp only [letterAt, hτWord]
      have hτPositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
        intro p j v hp
        rw [hτLetter] at hp
        exact hPosβ p j v hp
      have hτK : τ.k = σ.k := by
        cases hs : β.sideAt 1 <;> simpa only [τ, hs] using hKβ
      have hChosenβ : G β t ≤ 5 := by rw [hAxisβ]; exact hTLeFive
      have hτSmall : G τ t ≤ 4 := by
        cases t with
        | lower =>
            simp only [G, τ, hSideβ]
            exact (Nat.min_le_left _ _).trans (by simp only [G] at hChosenβ; omega)
        | upper =>
            simp only [G, τ, hSideβ]
            exact (Nat.min_le_left _ _).trans (by simp only [G] at hChosenβ; omega)
      have hτOther : G τ s = G β s := by
        cases t <;> cases s
        · exact False.elim (hne rfl)
        · simp only [G, τ, hSideβ]
        · simp only [G, τ, hSideβ]
        · exact False.elim (hne rfl)
      have hτOpposite : G τ s ≤ τ.k := by
        rw [hτOther, hAxisβ, hτK]
        exact hSLeFive.trans (by omega)
      have hSat := ctx_small_global_axis_saturated_triangle_bound τ hτPositive
        t s (Ne.symm hne) (by cases t <;> exact hτSmall)
        (by cases s <;> exact hτOpposite) (by rw [hτK]; omega)
      have hcap : (τ.k - 2).choose 2 + (τ.k - 1) ≤ 11 := by
        rw [hτK, hk]
        decide
      exact ⟨fun fuel => (hFuelNorm fuel).trans ((hSat.1 fuel).trans hcap),
        hBoundNorm.trans (hSat.2.1.trans hcap)⟩
    have hmUpper : m ≤ 4 := by omega
    by_cases hmSmall : m ≤ 2
    · have hnLarge : 3 ≤ n := by omega
      exact ⟨fun f g => (Nat.add_le_add (hAlphaTen.1 f) ((hBetaTwo hnLarge).1 g)).trans
          (by omega),
        (Nat.add_le_add hAlphaTen.2 (hBetaTwo hnLarge).2).trans (by omega)⟩
    by_cases hmFour : m = 4
    · have hMaximumα : α.k - 2 ≤ α.maximumAt 1 := by
        rw [part_maximumAt_one]
        change σ.k - 2 ≤ m
        omega
      have hAlphaOne := ctx_bound_le_one_of_large_sibling_maximum α hPosα 1
        hOneα hMaximumα
      exact ⟨fun f g => (Nat.add_le_add (hAlphaOne.1 f) (hBetaEleven.1 g)).trans
          (by omega),
        (Nat.add_le_add hAlphaOne.2 hBetaEleven.2).trans (by omega)⟩
    · have hmThree : m = 3 := by omega
      have hnTwo : n = 2 := by omega
      have hA := hAlphaFour hmThree
      have hB := hBetaEight hnTwo
      exact ⟨fun f g => (Nat.add_le_add (hA.1 f) (hB.1 g)).trans (by omega),
        (Nat.add_le_add hA.2 hB.2).trans (by omega)⟩

end ErdosSzekeres
