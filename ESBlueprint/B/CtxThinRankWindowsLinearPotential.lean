import ESBlueprint.B.CtxThinRankRectangleContextCoverPotential

namespace ErdosSzekeres

/-- Bound every fuel approximation and the full context bound by (W-1)*(V-1)+1 when active chosen pure intervals have width at most two and the chosen and opposite rank intervals lie in fixed windows of widths W and V. Both windows may be translated. Positive physical labels and distinct axes suffice; history depth, sibling maxima, inactive children, global capacities and window widths are otherwise unrestricted. Packages the finite rank-union cardinality step of the rectangle cover potential for reuse in actual-marker and saturation comparisons, eliminating repeated one-cluster counting arguments. This is a reusable bound, not a proof of the unrestricted singleton-end parent. Search evidence: runs/sol-trial-20260913/search-window.json.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_thin_rank_windows_linear_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (L K W V : ℕ)
  (hthin : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤
      σ.leftExt s 0 p + 2)
  (hchosen : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    L ≤ σ.leftExt s 0 p + 1 ∧
      (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p < L + W)
  (hopposite : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    K ≤ σ.leftExt t 0 p + 1 ∧
      (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt t 0 p < K + V) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (W - 1) * (V - 1) + 1) ∧
    σ.bound ≤ (W - 1) * (V - 1) + 1 := by
  let active :=
    σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks := fun (v : Ctx.Side) p =>
    Finset.Icc (σ.leftExt v 0 p + 1)
      ((match v with
        | Ctx.Side.lower => σ.u
        | Ctx.Side.upper => σ.a) - 1 - σ.rightExt v 0 p)
  let cost := fun (I : Finset ℕ) =>
    if I = ∅ then 0
    else
      ((I.biUnion (ranks s)).card - 1) *
          ((I.biUnion (ranks t)).card - 1) + 1
  have hcover : ∀ p ∈ active, ∃ I ∈ [active], p ∈ I := by
    intro p hp
    exact ⟨active, by simp, hp⟩
  have hsub : ∀ I ∈ [active], I ⊆ active := by
    intro I hI
    simp only [List.mem_singleton] at hI
    subst I
    exact fun _ hx => hx
  have hbase :
      (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ cost active) ∧
        σ.bound ≤ cost active := by
    simpa [active, ranks, cost] using
      (ctx_thin_rank_rectangle_context_cover_potential
        σ hpositive s t hne hthin [active] hcover hsub)
  have hs_subset :
      active.biUnion (ranks s) ⊆ Finset.Ico L (L + W) := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨p, hp, hxp⟩
    have hpdata :
        p ∈ σ.childPositions ∧
          (0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p) := by
      simpa [active] using hp
    have hc :=
      hchosen p hpdata.1 hpdata.2.1 hpdata.2.2
    dsimp only [ranks] at hxp
    have hr := Finset.mem_Icc.mp hxp
    apply Finset.mem_Ico.mpr
    constructor
    · exact le_trans hc.1 hr.1
    · cases s <;> exact lt_of_le_of_lt hr.2 hc.2
  have ht_subset :
      active.biUnion (ranks t) ⊆ Finset.Ico K (K + V) := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨p, hp, hxp⟩
    have hpdata :
        p ∈ σ.childPositions ∧
          (0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p) := by
      simpa [active] using hp
    have hc :=
      hopposite p hpdata.1 hpdata.2.1 hpdata.2.2
    dsimp only [ranks] at hxp
    have hr := Finset.mem_Icc.mp hxp
    apply Finset.mem_Ico.mpr
    constructor
    · exact le_trans hc.1 hr.1
    · cases t <;> exact lt_of_le_of_lt hr.2 hc.2
  have hs_card : (active.biUnion (ranks s)).card ≤ W := by
    calc
      (active.biUnion (ranks s)).card
          ≤ (Finset.Ico L (L + W)).card :=
        Finset.card_le_card hs_subset
      _ = W := by simp
  have ht_card : (active.biUnion (ranks t)).card ≤ V := by
    calc
      (active.biUnion (ranks t)).card
          ≤ (Finset.Ico K (K + V)).card :=
        Finset.card_le_card ht_subset
      _ = V := by simp
  have hcost : cost active ≤ (W - 1) * (V - 1) + 1 := by
    by_cases ha : active = ∅
    · simp [cost, ha]
    ·
      have hs_sub :
          (active.biUnion (ranks s)).card - 1 ≤ W - 1 :=
        Nat.sub_le_sub_right hs_card 1
      have ht_sub :
          (active.biUnion (ranks t)).card - 1 ≤ V - 1 :=
        Nat.sub_le_sub_right ht_card 1
      have hmul :
          ((active.biUnion (ranks s)).card - 1) *
              ((active.biUnion (ranks t)).card - 1)
            ≤ (W - 1) * (V - 1) :=
        Nat.mul_le_mul hs_sub ht_sub
      have hadd := Nat.add_le_add_right hmul 1
      simpa [cost, ha] using hadd
  exact
    ⟨fun fuel => le_trans (hbase.1 fuel) hcost,
      le_trans hbase.2 hcost⟩


end ErdosSzekeres
