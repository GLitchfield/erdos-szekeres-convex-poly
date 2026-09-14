import ESBlueprint.B.CtxCapacityThreePruningExteriorOfTwoLevelsGlobalFive
import ESBlueprint.B.CtxActiveBoundaryMarkerRankPairUnionBound

namespace ErdosSzekeres

/-- If two actual levels occur on an axis of global at most five, no younger level on that axis has an actual occurrence, and every active child has chosen-axis capacity at least three, then the two-level exterior geometry makes the younger marker an active boundary. The exact active boundary ordered-rank-pair union is contained in the full opposite rank triangle, so every fuel approximation and the full bound are at most choose(opposite global,2). At opposite global five this is ten and closes the pure capacity-three part of the six-extreme companion obstruction; mixed capacity-two/capacity-three support remains. Exact searches in runs/sol-12h/search-all-active-capacity-three-two-marker-triangle.json found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_capacity_three_children_exterior_of_two_levels_global_five, ErdosSzekeres.ctx_active_boundary_marker_rank_pair_union_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_all_active_capacity_three_two_marker_triangle_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = []) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hhigh : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p → 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p)) : let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ global.choose 2) ∧ σ.bound ≤ global.choose 2 := by
  classical
  let G (v : Ctx.Side) := match v with
    | Ctx.Side.lower => σ.u
    | Ctx.Side.upper => σ.a
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let I (p : ℕ) := Finset.Icc (σ.leftExt t 0 p + 1)
    (G t - 1 - σ.rightExt t 0 p)
  let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
  let ranks := active.biUnion (fun p => Q (I p))
  let T := Finset.Icc 1 (G t - 1)
  let triangle := Q T
  change (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (G t).choose 2) ∧
    σ.bound ≤ (G t).choose 2
  have hNOn : N ∈ σ.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hsmall : min
      ((match σ.sideAt N with
        | Ctx.Side.lower => σ.u
        | Ctx.Side.upper => σ.a) - 1)
      (σ.k - σ.maximumAt N) ≤ 4 := by
    apply (Nat.min_le_left _ _).trans
    rw [hNs]
    cases s <;> simp only at hglobal ⊢ <;> omega
  have hboundary :
      (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ ranks.card) ∧
        σ.bound ≤ ranks.card := by
    rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
        σ s N M x y hN hM hNM hNs hMs hx hy hglobal with hl | hr
    · have hb := ctx_active_boundary_marker_rank_pair_union_bound σ hpositive
          N x hN hx false
          (fun p hp ha => by
            have hout := hl.2 p hp (hhigh p hp ha.1 ha.2) N hNOn x hx
            simpa using hout)
          (fun j hj p hp => by
            have hj' : j ∈ σ.levelsOn s N := by simpa only [hNs] using hj
            rw [hyoung j hj'] at hp
            exact False.elim (List.not_mem_nil hp))
          t (by simpa only [hNs] using hne) hsmall
      simpa only [ranks, active, Q, I, G] using hb
    · have hb := ctx_active_boundary_marker_rank_pair_union_bound σ hpositive
          N x hN hx true
          (fun p hp ha => by
            have hout := hr.2 p hp (hhigh p hp ha.1 ha.2) N hNOn x hx
            simpa using hout)
          (fun j hj p hp => by
            have hj' : j ∈ σ.levelsOn s N := by simpa only [hNs] using hj
            rw [hyoung j hj'] at hp
            exact False.elim (List.not_mem_nil hp))
          t (by simpa only [hNs] using hne) hsmall
      simpa only [ranks, active, Q, I, G] using hb
  have hInside (p : ℕ) : I p ⊆ T := by
    intro z hz
    have hh := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hSub : ranks ⊆ triangle := by
    intro z hz
    obtain ⟨p, _, hz⟩ := Finset.mem_biUnion.mp hz
    have hh := Finset.mem_filter.mp hz
    have hp := Finset.mem_product.mp hh.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hInside p hp.1, hInside p hp.2⟩, hh.2⟩
  have hCardPairs (S : Finset ℕ) :
      ((S.product S).filter (fun z => z.1 ≤ z.2)).card =
        (S.card + 1).choose 2 := by
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
          · exact ⟨(a, b),
              Finset.mem_filter.mpr
                ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
          · exact ⟨(b, a),
              Finset.mem_filter.mpr
                ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩,
              Sym2.eq_swap⟩
  have hTriangle : triangle.card = (G t).choose 2 := by
    change (Q T).card = (G t).choose 2
    rw [show (Q T).card = (T.card + 1).choose 2 by
      exact hCardPairs T]
    by_cases hz : G t = 0
    · norm_num [T, hz]
    · have hc : T.card + 1 = G t := by
        simp only [T, Nat.card_Icc]
        omega
      rw [hc]
  have hCount : ranks.card ≤ (G t).choose 2 :=
    (Finset.card_le_card hSub).trans_eq hTriangle
  exact ⟨fun fuel => (hboundary.1 fuel).trans hCount,
    hboundary.2.trans hCount⟩


end ErdosSzekeres
