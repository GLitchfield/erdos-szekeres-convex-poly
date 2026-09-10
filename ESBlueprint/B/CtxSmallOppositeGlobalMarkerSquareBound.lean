import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential
import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank
import ESBlueprint.B.CtxSmallGlobalAxisRankPairPotential

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- The marker square estimate for opposite global at most four and chosen global at most five, using any actual chosen marker. Bounds every fuel and the full recursive context by the square of the opposite global minus one. Allows arbitrary maxima, older histories, inactive children, and positive unindexed markers. Covers opposite widths zero through three without a youngest-marker or bare-history assumption, supplying the small-width base of the remaining bare-marker square problem.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_small_opposite_global_marker_square_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ w ^ 2) ∧ σ.bound ≤ w ^ 2 := by
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
  let G (v : Side) := match v with | Side.lower => σ.u | Side.upper => σ.a
  let w := G t - 1
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let I (p : ℕ) := Finset.Icc (σ.leftExt s 0 p + 1) (G s - 1 - σ.rightExt s 0 p)
  let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
  let potential := active.biUnion (fun p => Q (I p))
  change (∀ fuel, boundFuel fuel σ ≤ w ^ 2) ∧ σ.bound ≤ w ^ 2
  have hGs : G s ≤ 5 := hglobal
  have hGt : G t ≤ 4 := hopposite
  have hw : w ≤ 3 := by dsimp only [w]; omega
  have hp := ctx_small_global_axis_rank_pair_potential σ hpositive t s (Ne.symm hne) hopposite
  change (∀ fuel, boundFuel fuel σ ≤ potential.card) ∧ σ.bound ≤ potential.card at hp
  have hActive (p : ℕ) (h : p ∈ active) :
      p ∈ σ.childPositions ∧ 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p := by
    simpa only [active, Finset.mem_filter, List.mem_toFinset, and_assoc] using h
  by_cases hw0 : w = 0
  · have hEmpty : active = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p h
      have ha := hActive p h
      have hz : G t ≤ 1 := by dsimp only [w] at hw0; omega
      cases t <;> simp only [G, cupLimit, capLimit] at hz ha <;> omega
    have hPot : potential = ∅ := by simp only [potential, hEmpty, Finset.biUnion_empty]
    simpa only [hPot, Finset.card_empty, hw0, Nat.zero_pow (by decide : 0 < 2)] using hp
  by_cases hw1 : w = 1
  · have hRank : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
        σ.leftExt t 0 p + 1 = 1 ∧
          1 + σ.rightExt t 0 p = (match (generalizing := false) t with | Side.lower => σ.u - 1 | Side.upper => σ.a - 1) := by
      intro p hp hcup hcap
      dsimp only [w] at hw1
      cases t <;> simp only [G, cupLimit, capLimit, chainExt] at hw1 hcup hcap ⊢ <;> omega
    have hh := ctx_bound_le_one_of_common_singleton_rank σ hpositive t 1 hRank
    simpa only [hw1, one_pow] using And.intro hh.1 hh.2.1
  by_cases hw2 : w = 2
  · have hThree : G t ≤ 3 := by dsimp only [w] at hw2; omega
    have hh := ctx_small_global_axis_rank_region_potential σ hpositive t s (Ne.symm hne) hThree
    have hBudget : (match s with | Side.lower => σ.u - 1 | Side.upper => σ.a - 1) ≤ 4 := by
      cases s <;> simp only [G] at hGs ⊢ <;> omega
    have hFull : σ.bound ≤ 4 := hh.2.1.trans (hh.2.2.1.trans hBudget)
    have hFuel : ∀ fuel, boundFuel fuel σ ≤ 4 :=
      fun fuel => (hh.1 fuel).trans (hh.2.2.1.trans hBudget)
    simpa only [hw2, show (2 : ℕ) ^ 2 = 4 by decide] using And.intro hFuel hFull
  have hw3 : w = 3 := by omega
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hNe (p : ℕ) (hc : p ∈ σ.childPositions) : p ≠ x := by
    intro he
    subst p
    have hlet : σ.letterAt x = Letter.child := of_decide_eq_true (List.mem_filter.mp hc).2
    simp [extPositions, hlet] at hx
  let L : Finset ℕ := Finset.Icc 1 3
  let R : Finset ℕ := Finset.Icc 2 4
  have hSub : potential ⊆ Q L ∪ Q R := by
    intro z hz
    obtain ⟨p, hpA, hz⟩ := Finset.mem_biUnion.mp hz
    have hc := (hActive p hpA).1
    obtain ⟨hz, hzOrder⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz
    have h1 := Finset.mem_Icc.mp hz1
    have h2 := Finset.mem_Icc.mp hz2
    rcases lt_or_gt_of_ne (hNe p hc) with hpx | hxp
    · have hr := hOneRight σ s N p x hNOn hx hpx
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hzOrder⟩
      · apply Finset.mem_Icc.mpr
        omega
      · apply Finset.mem_Icc.mpr
        omega
    · have hl := hOneLeft σ s N p x hNOn hx hxp
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hzOrder⟩
      · apply Finset.mem_Icc.mpr
        omega
      · apply Finset.mem_Icc.mpr
        omega
  have hCard : (Q L ∪ Q R).card = 9 := by decide
  have hBound : potential.card ≤ 9 := by
    rw [← hCard]
    exact Finset.card_le_card hSub
  have hFull : σ.bound ≤ 9 := hp.2.trans hBound
  have hFuel : ∀ fuel, boundFuel fuel σ ≤ 9 := fun fuel => (hp.1 fuel).trans hBound
  simpa only [hw3, show (3 : ℕ) ^ 2 = 9 by decide] using And.intro hFuel hFull

end ErdosSzekeres
