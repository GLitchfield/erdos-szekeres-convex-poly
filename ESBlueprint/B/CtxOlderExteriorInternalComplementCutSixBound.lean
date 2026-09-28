import ESBlueprint.B.CtxOlderExteriorInternalComplementCutPotentialBound
import ESBlueprint.B.CtxNonmonotoneTripleSaturatedPotentialArbitraryOppositeHistory
import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At k six, the positive legal coupling sharpens the older-exterior internal complement cut from thirteen to twelve. The boundary pair part costs at most three; maxima one and four force a sibling-bound-one part, while middle maxima make the nonmonotone part satisfy the checked next-band bound nine. This removes the exact one-unit loss in the residual two-marker companion induction. Exact es searches found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_older_exterior_internal_complement_cut_potential_bound, ErdosSzekeres.ctx_nonmonotone_triple_saturated_potential_arbitrary_opposite_history, ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_older_exterior_internal_complement_cut_six_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = []) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (q₀ l r m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hlnot : l ∉ keep) (hrnot : r ∉ keep) (hinside : ∀ p ∈ keep, l < p ∧ p < r) (hexterior : (x < y ∧ ∀ p ∈ keep, y < p) ∨ (y < x ∧ ∀ p ∈ keep, p < y)) (hk : σ.k = 6) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12 := by
  classical
  have hFiveK : 5 ≤ σ.k := by
    simpa only [hk] using (show 5 ≤ 6 by decide)
  have hFivePred : 5 ≤ σ.k - 1 := by
    simpa only [hk] using (show 5 ≤ 6 - 1 by decide)
  let w := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hQα : q₀ ∈ α.extPositions 1 := (hExtα q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
  have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive rest s m hQα
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
      · cases hp
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ ks v q hpl he] at hp
      cases hp
      omega
  have hPosα := hPositivePart rest s m
  have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
  have hNpos := one_le_of_mem_levels hN
  have hMpos := one_le_of_mem_levels hM
  have hNα : N + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hMα : M + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hNsα : α.sideAt (N + 1) = s :=
    (part_sideAt_succ σ rest s m hNpos).trans hNs
  have hMsα : α.sideAt (M + 1) = s :=
    (part_sideAt_succ σ rest s m hMpos).trans hMs
  have hXα : x ∈ α.extPositions (N + 1) := by
    rw [part_extPositions_succ σ rest s m hNpos]
    exact hx
  have hYα : y ∈ α.extPositions (M + 1) := by
    rw [part_extPositions_succ σ rest s m hMpos]
    exact hy
  have hGeometry : (q₀ < y ∧ y < x) ∨ (x < y ∧ y < q₀) := by
    rcases hexterior with ⟨hxy, hout⟩ | ⟨hyx, hout⟩
    · exact Or.inr ⟨hxy, hout q₀ hq₀⟩
    · exact Or.inl ⟨hout q₀ hq₀, hyx⟩
  have hTripleGeometry : (q₀ < x ∧ y < x) ∨ (x < q₀ ∧ x < y) := by
    rcases hGeometry with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨lt_trans h1 h2, h2⟩
    · exact Or.inr ⟨lt_trans h1 h2, h1⟩
  have hGlobalα : (match s with | Side.lower => α.u | Side.upper => α.a) ≤ 5 := by
    change (match s with | Side.lower => σ.u | Side.upper => σ.a) ≤ 5
    exact hglobal
  have hkα : 5 ≤ α.k := by
    change 5 ≤ σ.k
    exact hFiveK
  have hSaturatedNext (hLargeα : α.k - 4 ≤ α.maximumAt 1) :
      (∀ fuel, boundFuel fuel α ≤ 3 * α.k - 9) ∧ α.bound ≤ 3 * α.k - 9 := by
    cases t with
    | lower =>
      have hOpp : α.u ≤ α.k := by
        change σ.u ≤ σ.k
        exact hopposite.trans hFiveK
      have hNext : α.u ≤ α.k - 1 := by
        change σ.u ≤ σ.k - 1
        exact hopposite.trans hFivePred
      have hSat := ctx_nonmonotone_triple_saturated_potential_arbitrary_opposite_history
        α hPosα s Side.lower hne 1 (N + 1) (M + 1) q₀ x y hOneα hNα hMα
        (Nat.lt_succ_iff.mpr hNpos) (Nat.add_lt_add_right hNM 1)
        hSideα hNsα hMsα hQα hXα hYα hTripleGeometry
        hGlobalα hOpp hkα 1 hOneα hSideα hLargeα
      exact hSat.2.2 hNext
    | upper =>
      have hOpp : α.a ≤ α.k := by
        change σ.a ≤ σ.k
        exact hopposite.trans hFiveK
      have hNext : α.a ≤ α.k - 1 := by
        change σ.a ≤ σ.k - 1
        exact hopposite.trans hFivePred
      have hSat := ctx_nonmonotone_triple_saturated_potential_arbitrary_opposite_history
        α hPosα s Side.upper hne 1 (N + 1) (M + 1) q₀ x y hOneα hNα hMα
        (Nat.lt_succ_iff.mpr hNpos) (Nat.add_lt_add_right hNM 1)
        hSideα hNsα hMsα hQα hXα hYα hTripleGeometry
        hGlobalα hOpp hkα 1 hOneα hSideα hLargeα
      exact hSat.2.2 hNext
  let β := σ.part keep t n
  have hChildβ (p : ℕ) : p ∈ β.childPositions ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [β, part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ rest := by
    rw [part_extPositions_one hpositive]
  have hLβ : l ∈ β.extPositions 1 := (hExtβ l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
  have hRβ : r ∈ β.extPositions 1 := (hExtβ r).mpr ((hRest r).mpr ⟨hr, hrnot⟩)
  have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t n hLβ
  have hPosβ := hPositivePart keep t n
  have hOneβ : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
  have hNβ : N + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNsβ : β.sideAt (N + 1) = s :=
    (part_sideAt_succ σ keep t n hNpos).trans hNs
  have hXβ : x ∈ β.extPositions (N + 1) := by
    rw [part_extPositions_succ σ keep t n hNpos]
    exact hx
  have hw : 2 ≤ w := hwidth
  let activeβ := β.childPositions.toFinset.filter
    (fun p => 0 < β.cupLimit p p ∧ 0 < β.capLimit p p)
  let Iβ (p : ℕ) := Finset.Icc (β.leftExt t 0 p + 1) (w - β.rightExt t 0 p)
  let J := Finset.Icc 2 (w - 1)
  have hOneLeft (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v top p := by
    have hmem : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hmem
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls ↦ (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr
        ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v top p := by
    have hmem : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hmem
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls ↦ (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr
        ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hOppOn : 1 ∈ β.levelsOn t 0 :=
    List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ]⟩
  have hIntervalβ (p : ℕ) (hp : p ∈ β.childPositions) : Iβ p ⊆ J := by
    intro z hz
    have hpk := ((hChildβ p).mp hp).2
    have hL := hOneLeft β t 0 1 p l hOppOn hLβ (hinside p hpk).1
    have hR := hOneRight β t 0 1 p r hOppOn hRβ (hinside p hpk).2
    have hh := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hJCard : J.card = w - 2 := by
    simp only [J, Nat.card_Icc]
    omega
  obtain ⟨direction, hBoundary⟩ : ∃ direction : Bool,
      ∀ p ∈ β.childPositions, if direction then p < x else x < p := by
    rcases hexterior with ⟨hxy, hout⟩ | ⟨hyx, hout⟩
    · exact ⟨false, fun p hp => by
        change x < p
        exact lt_trans hxy (hout p ((hChildβ p).mp hp).2)⟩
    · exact ⟨true, fun p hp => by
        change p < x
        exact lt_trans (hout p ((hChildβ p).mp hp).2) hyx⟩
  have hYounger : ∀ j ∈ β.levelsOn (β.sideAt (N + 1)) (N + 1),
      ∀ p ∈ β.extPositions j, if direction then p < x else x < p := by
    rw [hNsβ]
    have hs : β.sideAt 1 ≠ s := by
      rw [hSideβ]
      exact Ne.symm hne
    intro j hj p hp
    rw [part_levelsOn_other_succ hs hNpos] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [part_extPositions_succ σ keep t n (one_le_of_mem_levelsOn hi).1,
      hyoung i hi] at hp
    exact False.elim (List.not_mem_nil hp)
  let Q (S : Finset ℕ) := (S.product S).filter (fun z ↦ z.1 ≤ z.2)
  let pairsβ := activeβ.biUnion (fun p => Q (Iβ p))
  have hCardPairs (T : Finset ℕ) : (Q T).card = (T.card + 1).choose 2 := by
    rw [← Finset.card_sym2]
    apply Finset.card_bij (fun z _ ↦ Sym2.mk z.1 z.2)
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
  have hSmallβ : min ((match (generalizing := false) β.sideAt (N + 1) with
      | Side.lower => β.u | Side.upper => β.a) - 1)
      (β.k - β.maximumAt (N + 1)) ≤ 4 := by
    rw [hNsβ]
    apply (Nat.min_le_left _ _).trans
    have hg : (match (generalizing := false) s with
      | Side.lower => β.u | Side.upper => β.a) ≤ 5 := hglobal
    omega
  have hOther : (∀ fuel, boundFuel fuel β ≤ (w - 1).choose 2) ∧
      β.bound ≤ (w - 1).choose 2 := by
    have hh := ctx_active_boundary_marker_rank_pair_union_bound β hPosβ
      (N + 1) x hNβ hXβ direction (fun p hp _ => hBoundary p hp) hYounger t
      (by rw [hNsβ]; exact hne) hSmallβ
    have hb : (∀ fuel, boundFuel fuel β ≤ pairsβ.card) ∧ β.bound ≤ pairsβ.card := by
      change (∀ fuel, boundFuel fuel β ≤ pairsβ.card) ∧ β.bound ≤ pairsβ.card at hh
      exact hh
    have hsub : pairsβ ⊆ Q J := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hs := hIntervalβ p (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
      have hz' := Finset.mem_filter.mp hz
      have hpair := Finset.mem_product.mp hz'.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hs hpair.1, hs hpair.2⟩, hz'.2⟩
    have hc : (Q J).card = (w - 1).choose 2 := by
      rw [hCardPairs, hJCard, show w - 2 + 1 = w - 1 by omega]
    have hCount := (Finset.card_le_card hsub).trans_eq hc
    exact ⟨fun fuel => (hb.1 fuel).trans hCount, hb.2.trans hCount⟩
  have hwUpper : w ≤ 4 := by
    dsimp only [w]
    omega
  have hPairCard : (w - 1).choose 2 ≤ 3 := by
    have hh : w - 1 ≤ 3 := by omega
    exact (Nat.choose_le_choose 2 hh).trans (by norm_num)
  have hOtherThree : (∀ fuel, boundFuel fuel β ≤ 3) ∧ β.bound ≤ 3 :=
    ⟨fun fuel => (hOther.1 fuel).trans hPairCard, hOther.2.trans hPairCard⟩
  have hOwn := ctx_nonmonotone_triple_linear_potential α hPosα s t hne
    1 (N + 1) (M + 1) q₀ x y hOneα hNα hMα (by omega) (by omega)
    hSideα hNsα hMsα hQα hXα hYα hTripleGeometry hglobal
    (by change 1 ≤ w; omega)
  change (∀ fuel, boundFuel fuel α ≤ 3 * w - 2) ∧
    α.bound ≤ 3 * w - 2 at hOwn
  have hOwnTen : (∀ fuel, boundFuel fuel α ≤ 10) ∧ α.bound ≤ 10 := by
    have hten : 3 * w - 2 ≤ 10 := by omega
    exact ⟨fun fuel => (hOwn.1 fuel).trans hten, hOwn.2.trans hten⟩
  have hmUpper : m ≤ 4 := by omega
  change (∀ f g, boundFuel f α + boundFuel g β ≤ 12) ∧ α.bound + β.bound ≤ 12
  by_cases hmOne : m = 1
  · have hMaximumβ : β.maximumAt 1 = n := part_maximumAt_one σ keep t n
    have hLargeβ : β.k - 2 ≤ β.maximumAt 1 := by
      rw [hMaximumβ]
      change σ.k - 2 ≤ n
      omega
    have hβOne := ctx_bound_le_one_of_large_sibling_maximum β hPosβ 1 hOneβ hLargeβ
    exact ⟨fun f g => (Nat.add_le_add (hOwnTen.1 f) (hβOne.1 g)).trans (by omega),
      (Nat.add_le_add hOwnTen.2 hβOne.2).trans (by omega)⟩
  by_cases hmFour : m = 4
  · have hMaximumα : α.maximumAt 1 = m := part_maximumAt_one σ rest s m
    have hLargeα : α.k - 2 ≤ α.maximumAt 1 := by
      rw [hMaximumα]
      change σ.k - 2 ≤ m
      omega
    have hαOne := ctx_bound_le_one_of_large_sibling_maximum α hPosα 1 hOneα hLargeα
    exact ⟨fun f g => (Nat.add_le_add (hαOne.1 f) (hOtherThree.1 g)).trans (by omega),
      (Nat.add_le_add hαOne.2 hOtherThree.2).trans (by omega)⟩
  have hmMiddle : 2 ≤ m ∧ m ≤ 3 := by omega
  have hMaximumα : α.maximumAt 1 = m := part_maximumAt_one σ rest s m
  have hLargeα : α.k - 4 ≤ α.maximumAt 1 := by
    rw [hMaximumα]
    change σ.k - 4 ≤ m
    omega
  have hSatNext := hSaturatedNext hLargeα
  have hOwnNine : (∀ fuel, boundFuel fuel α ≤ 9) ∧ α.bound ≤ 9 := by
    have hnine : 3 * α.k - 9 ≤ 9 := by
      change 3 * σ.k - 9 ≤ 9
      omega
    exact ⟨fun fuel => (hSatNext.1 fuel).trans hnine, hSatNext.2.trans hnine⟩
  exact ⟨fun f g => (Nat.add_le_add (hOwnNine.1 f) (hOtherThree.1 g)).trans (by omega),
    (Nat.add_le_add hOwnNine.2 hOtherThree.2).trans (by omega)⟩

end ErdosSzekeres
