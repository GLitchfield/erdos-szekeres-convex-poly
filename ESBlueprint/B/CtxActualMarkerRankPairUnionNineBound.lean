import ESBlueprint.B.CtxActualMarkerOppositeRankIntervalEndpointExclusion

namespace ErdosSzekeres

/-- An actual indexed marker on an axis of global at most five clips every active pure-rank interval away from one extreme endpoint, so the union of all ordered rank-pair triangles has cardinal at most nine.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_actual_marker_opposite_rank_interval_endpoint_exclusion
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_actual_marker_rank_pair_union_nine_bound (σ : Ctx.Context) (t : Ctx.Side) (N x : ℕ) (hN : N ∈ σ.levels) (hNt : σ.sideAt N = t) (hx : x ∈ σ.extPositions N) (hglobal : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) : let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; let active := σ.childPositions.toFinset.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p); let interval := fun p => Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p); let pairs := active.biUnion (fun p => ((interval p).product (interval p)).filter (fun z => z.1 ≤ z.2)); pairs.card ≤ 9 := by
  classical
  let G := match (generalizing := false) t with
    | Ctx.Side.lower => σ.u
    | Ctx.Side.upper => σ.a
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let I (p : ℕ) := Finset.Icc (σ.leftExt t 0 p + 1)
    (G - 1 - σ.rightExt t 0 p)
  let Q (S : Finset ℕ) :=
    (S.product S).filter (fun z => z.1 ≤ z.2)
  let pairs := active.biUnion (fun p => Q (I p))
  let L := Finset.Icc 1 3
  let R := Finset.Icc 2 4
  change pairs.card ≤ 9
  have hSub : pairs ⊆ Q L ∪ Q R := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    have hpData : p ∈ σ.childPositions ∧
        0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p := by
      simpa only [active, Finset.mem_filter, List.mem_toFinset, and_assoc] using hp
    have hclip := ctx_actual_marker_opposite_rank_interval_endpoint_exclusion
      σ t N x p hN hNt hx hpData.1
    have hclip' : (x < p ∧ ∀ r ∈ I p, 2 ≤ r) ∨
        (p < x ∧ ∀ r ∈ I p, r + 2 ≤ G) := by
      cases t <;> simpa only [I, G] using hclip
    obtain ⟨hzProd, hzOrder⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzLeft, hzRight⟩ := Finset.mem_product.mp hzProd
    have hLeftRange := Finset.mem_Icc.mp hzLeft
    have hRightRange := Finset.mem_Icc.mp hzRight
    rcases hclip' with hright | hleft
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hzOrder⟩
      · apply Finset.mem_Icc.mpr
        exact ⟨hright.2 z.1 hzLeft, by omega⟩
      · apply Finset.mem_Icc.mpr
        exact ⟨hright.2 z.2 hzRight, by omega⟩
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hzOrder⟩
      · apply Finset.mem_Icc.mpr
        exact ⟨by omega, by have := hleft.2 z.1 hzLeft; omega⟩
      · apply Finset.mem_Icc.mpr
        exact ⟨by omega, by have := hleft.2 z.2 hzRight; omega⟩
  have hCard : (Q L ∪ Q R).card = 9 := by decide
  rw [← hCard]
  exact Finset.card_le_card hSub

end ErdosSzekeres
