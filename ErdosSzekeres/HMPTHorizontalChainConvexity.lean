module

public import ErdosSzekeres.HMPTHorizontalProfileProducer

@[expose] public section

/-!
# Convexity of the local HMPT horizontal chains

The literal inner and outer triple predicates determine a uniform orientation
sign along the strict horizontal order.  The four-point criterion then makes
each stored horizontal subchain convex without retaining either outer anchor.
-/

namespace ErdosSzekeres

noncomputable section

private theorem orientation_reverse_l4 (a b c : Point 2) :
    orientation c b a = -orientation a b c := by
  simp only [orientation]
  ring

private theorem inConvexPosition_four_of_all_orientation_pos_l4
    (a b c d : Point 2)
    (habc : 0 < orientation a b c)
    (habd : 0 < orientation a b d)
    (hacd : 0 < orientation a c d)
    (hbcd : 0 < orientation b c d) :
    InConvexPosition {a, b, c, d} := by
  have h := inConvexPosition_four_of_all_orientation_neg a d c b
    (by rw [orientation_swap_last]; linarith)
    (by rw [orientation_swap_last]; linarith)
    (by rw [orientation_swap_last]; linarith)
    (by rw [orientation_reverse_l4]; linarith)
  rw [show ({a, d, c, b} : Finset (Point 2)) = {a, b, c, d} by
    ext x
    simp [or_comm, or_left_comm]] at h
  exact h

/-- A wrapper which isolates the local strict horizontal order from the
ambient pointwise order on coordinate functions. -/
private structure HMPTOrderedSelectedPointL4
    {s : Finset (Point 2)} (selected : Finset (↥s)) where
  val : ↥selected
  deriving Fintype

private def hmptOrderedSelectedPointEquivL4
    {s : Finset (Point 2)} (selected : Finset (↥s)) :
    HMPTOrderedSelectedPointL4 selected ≃ ↥selected where
  toFun p := p.val
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl

private def hmptOrderedSelectedPointEmbeddingL4
    {s : Finset (Point 2)} (selected : Finset (↥s)) :
    HMPTOrderedSelectedPointL4 selected ↪ Point 2 where
  toFun p := p.val.1.1
  inj' := by
    intro p q hpq
    apply (hmptOrderedSelectedPointEquivL4 selected).injective
    exact Subtype.ext (Subtype.ext hpq)

namespace SukRegionGeometry

variable {outerLeft rightAnchor leftAnchor outerRight : Point 2}
  {s : Finset (Point 2)}

private theorem horizontalLT_trans_l4
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1)
    (hqr : HMPTSpikeHorizontalLT outerLeft outerRight q.1 r.1) :
    HMPTSpikeHorizontalLT outerLeft outerRight p.1 r.1 := by
  have hpair := h.toHMPTSpikeOrderPair
  rcases hpair.horizontal_trans p q r (Or.inr hpq) (Or.inr hqr) with hpr | hpr
  · exfalso
    apply hqr.1
    have hrq : HMPTSpikeHorizontalLE outerLeft outerRight r.1 q.1 := by
      rw [← hpr]
      exact Or.inr hpq
    have hqrEq := hpair.horizontal_antisymm q r (Or.inr hqr) hrq
    exact congrArg Subtype.val hqrEq
  · exact hpr

private theorem selected_horizontalLT_isStrictTotal_l4
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (verticalProfile : HMPTVerticalProfile
      outerLeft rightAnchor leftAnchor outerRight s)
    (selected : Finset (↥s))
    (hselected : selected ⊆ verticalProfile.horizontalChain) :
    IsStrictTotalOrder (HMPTOrderedSelectedPointL4 selected)
      (fun p q ↦ HMPTSpikeHorizontalLT
        outerLeft outerRight p.val.1.1 q.val.1.1) where
  irrefl p hp := hp.1 rfl
  trans p q r hpq hqr :=
    h.horizontalLT_trans_l4 p.val.1 q.val.1 r.val.1 hpq hqr
  trichotomous p q hpq hqp := by
    by_contra hpqNe
    have hpqVal : p.val.1 ≠ q.val.1 := by
      intro heq
      apply hpqNe
      apply (hmptOrderedSelectedPointEquivL4 selected).injective
      exact Subtype.ext heq
    rcases verticalProfile.horizontalMaximum.1
        (hselected p.val.property) (hselected q.val.property) hpqVal with
      hpqLE | hqpLE
    · rcases hpqLE with heq | hlt
      · exact hpqVal (Subtype.ext heq)
      · exact hpq hlt
    · rcases hqpLE with heq | hlt
      · exact hpqVal (Subtype.ext heq.symm)
      · exact hqp hlt

private theorem horizontalChain_convex_of_ordered_four_l4
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (verticalProfile : HMPTVerticalProfile
      outerLeft rightAnchor leftAnchor outerRight s)
    (selected : Finset (↥s))
    (hselected : selected ⊆ verticalProfile.horizontalChain)
    (hfour : ∀ p q r t : ↥selected,
      HMPTSpikeHorizontalLT outerLeft outerRight p.1.1 q.1.1 →
      HMPTSpikeHorizontalLT outerLeft outerRight q.1.1 r.1.1 →
      HMPTSpikeHorizontalLT outerLeft outerRight r.1.1 t.1.1 →
        InConvexPosition {p.1.1, q.1.1, r.1.1, t.1.1}) :
    InConvexPosition (hmptChainPoints selected) := by
  classical
  have hgp : InGeneralPosition (hmptChainPoints selected) := by
    apply h.generalPosition.mono
    intro p hp
    have hps : p ∈ s := hmptChainPoints_subset selected hp
    simp [hps]
  apply (inConvexPosition_iff_four_subsets
    (hmptChainPoints selected) hgp).2
  intro u hu hucard
  let horizontalLT : HMPTOrderedSelectedPointL4 selected →
      HMPTOrderedSelectedPointL4 selected → Prop :=
    fun p q ↦ HMPTSpikeHorizontalLT
      outerLeft outerRight p.val.1.1 q.val.1.1
  letI : DecidableRel horizontalLT := Classical.decRel _
  letI : IsStrictTotalOrder
      (HMPTOrderedSelectedPointL4 selected) horizontalLT :=
    h.selected_horizontalLT_isStrictTotal_l4 verticalProfile selected hselected
  letI : LinearOrder (HMPTOrderedSelectedPointL4 selected) :=
    linearOrderOfSTO horizontalLT
  let g : HMPTOrderedSelectedPointL4 selected ↪ Point 2 :=
    hmptOrderedSelectedPointEmbeddingL4 selected
  have himage : Finset.univ.image g = hmptChainPoints selected := by
    ext p
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      hmptChainPoints, Finset.mem_map]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.val.1, q.val.property, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨⟨q, hq⟩⟩, rfl⟩
  have huimage : u ⊆ Finset.univ.image g := by
    rw [himage]
    exact hu
  obtain ⟨w, hw⟩ := Finset.subset_univ_image_iff.mp huimage
  have hwcard : w.card = 4 := by
    calc
      w.card = (w.image g).card :=
        (Finset.card_image_of_injective w g.injective).symm
      _ = u.card := congrArg Finset.card hw
      _ = 4 := hucard
  let e := w.orderEmbOfFin hwcard
  have h01 : HMPTSpikeHorizontalLT outerLeft outerRight
      (e 0).val.1.1 (e 1).val.1.1 := by
    exact e.strictMono (by decide)
  have h12 : HMPTSpikeHorizontalLT outerLeft outerRight
      (e 1).val.1.1 (e 2).val.1.1 := by
    exact e.strictMono (by decide)
  have h23 : HMPTSpikeHorizontalLT outerLeft outerRight
      (e 2).val.1.1 (e 3).val.1.1 := by
    exact e.strictMono (by decide)
  have heimage : Finset.univ.image e = w := by
    dsimp [e]
    exact Finset.image_orderEmbOfFin_univ w hwcard
  have hpoints : ({g (e 0), g (e 1), g (e 2), g (e 3)} :
      Finset (Point 2)) = u := by
    have hfin4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by
      decide
    calc
      ({g (e 0), g (e 1), g (e 2), g (e 3)} : Finset (Point 2)) =
          Finset.univ.image (g ∘ e) := by
        rw [hfin4]
        simp
      _ = (Finset.univ.image e).image g := by
        rw [Finset.image_image]
      _ = w.image g := congrArg (fun v ↦ v.image g) heimage
      _ = u := hw
  rw [← hpoints]
  exact hfour (e 0).val (e 1).val (e 2).val (e 3).val h01 h12 h23

private theorem ordered_inner_triple_orientation_neg_l4
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    {selected : Finset (↥s)}
    (hliteral : ∀ triple : Finset (↥s), triple ⊆ selected →
      triple.card = 3 →
        InConvexPosition
          (insert outerLeft (insert outerRight (hmptChainPoints triple))))
    (p q r : ↥selected)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p.1.1 q.1.1)
    (hqr : HMPTSpikeHorizontalLT outerLeft outerRight q.1.1 r.1.1) :
    orientation p.1.1 q.1.1 r.1.1 < 0 := by
  let triple : Finset (↥s) := {p.1, q.1, r.1}
  have hpr := h.horizontalLT_trans_l4 p.1 q.1 r.1 hpq hqr
  have htripleSubset : triple ⊆ selected := by
    intro x hx
    simp only [triple, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact p.property
    · exact q.property
    · exact r.property
  have htripleCard : triple.card = 3 := by
    have hpq' : p.1 ≠ q.1 := fun heq ↦ hpq.1 (congrArg Subtype.val heq)
    have hpr' : p.1 ≠ r.1 := fun heq ↦ hpr.1 (congrArg Subtype.val heq)
    have hqr' : q.1 ≠ r.1 := fun heq ↦ hqr.1 (congrArg Subtype.val heq)
    simp [triple, hpq', hpr', hqr']
  have hconvex : InConvexPosition
      {outerLeft, outerRight, p.1.1, q.1.1, r.1.1} := by
    simpa [triple, hmptChainPoints] using
      hliteral triple htripleSubset htripleCard
  have hright := (h.hmptHorizontalTripleGeometry.semantics
    p.1 q.1 r.1 hpq hqr).1.mpr hconvex
  simpa [hmptHorizontalTripleColor] using hright

private theorem ordered_outer_triple_orientation_pos_l4
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    {selected : Finset (↥s)}
    (hliteral : ∀ triple : Finset (↥s), triple ⊆ selected →
      triple.card = 3 →
        ¬InConvexPosition
          (insert outerLeft (insert outerRight (hmptChainPoints triple))))
    (p q r : ↥selected)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p.1.1 q.1.1)
    (hqr : HMPTSpikeHorizontalLT outerLeft outerRight q.1.1 r.1.1) :
    0 < orientation p.1.1 q.1.1 r.1.1 := by
  let triple : Finset (↥s) := {p.1, q.1, r.1}
  have hpr := h.horizontalLT_trans_l4 p.1 q.1 r.1 hpq hqr
  have htripleSubset : triple ⊆ selected := by
    intro x hx
    simp only [triple, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact p.property
    · exact q.property
    · exact r.property
  have htripleCard : triple.card = 3 := by
    have hpq' : p.1 ≠ q.1 := fun heq ↦ hpq.1 (congrArg Subtype.val heq)
    have hpr' : p.1 ≠ r.1 := fun heq ↦ hpr.1 (congrArg Subtype.val heq)
    have hqr' : q.1 ≠ r.1 := fun heq ↦ hqr.1 (congrArg Subtype.val heq)
    simp [triple, hpq', hpr', hqr']
  have hnotConvex : ¬InConvexPosition
      {outerLeft, outerRight, p.1.1, q.1.1, r.1.1} := by
    simpa [triple, hmptChainPoints] using
      hliteral triple htripleSubset htripleCard
  have hleft := (h.hmptHorizontalTripleGeometry.semantics
    p.1 q.1 r.1 hpq hqr).2.mpr hnotConvex
  have hnotNeg : ¬orientation p.1.1 q.1.1 r.1.1 < 0 := by
    intro hneg
    have hright : hmptHorizontalTripleColor p.1 q.1 r.1 = Turn.right := by
      simp [hmptHorizontalTripleColor, hneg]
    simp [hleft] at hright
  have hne : orientation p.1.1 q.1.1 r.1.1 ≠ 0 :=
    h.generalPosition (by simp [p.1.property])
      (by simp [q.1.property]) (by simp [r.1.property])
      hpq.1 hpr.1 hqr.1
  exact lt_of_le_of_ne (le_of_not_gt hnotNeg) (Ne.symm hne)

/-- The literal inner horizontal chain stored by the H3 profile is convex
without either outer anchor. -/
theorem hmptInnerHorizontalChain_convex
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (verticalProfile : HMPTVerticalProfile
      outerLeft rightAnchor leftAnchor outerRight s)
    (horizontalProfile : HMPTHorizontalProfile
      outerLeft rightAnchor leftAnchor outerRight s verticalProfile) :
    InConvexPosition (hmptChainPoints horizontalProfile.innerChain) := by
  apply h.horizontalChain_convex_of_ordered_four_l4 verticalProfile
    horizontalProfile.innerChain horizontalProfile.innerMaximum.1.1
  intro p q r t hpq hqr hrt
  have hqt := h.horizontalLT_trans_l4 q.1 r.1 t.1 hqr hrt
  have hpr := h.horizontalLT_trans_l4 p.1 q.1 r.1 hpq hqr
  apply inConvexPosition_four_of_all_orientation_neg
  · exact h.ordered_inner_triple_orientation_neg_l4
      horizontalProfile.innerMaximum.1.2 p q r hpq hqr
  · exact h.ordered_inner_triple_orientation_neg_l4
      horizontalProfile.innerMaximum.1.2 p q t hpq hqt
  · exact h.ordered_inner_triple_orientation_neg_l4
      horizontalProfile.innerMaximum.1.2 p r t hpr hrt
  · exact h.ordered_inner_triple_orientation_neg_l4
      horizontalProfile.innerMaximum.1.2 q r t hqr hrt

/-- The literal outer horizontal chain stored by the H3 profile is convex
without either outer anchor. -/
theorem hmptOuterHorizontalChain_convex
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (verticalProfile : HMPTVerticalProfile
      outerLeft rightAnchor leftAnchor outerRight s)
    (horizontalProfile : HMPTHorizontalProfile
      outerLeft rightAnchor leftAnchor outerRight s verticalProfile) :
    InConvexPosition (hmptChainPoints horizontalProfile.outerChain) := by
  apply h.horizontalChain_convex_of_ordered_four_l4 verticalProfile
    horizontalProfile.outerChain horizontalProfile.outerMaximum.1.1
  intro p q r t hpq hqr hrt
  have hqt := h.horizontalLT_trans_l4 q.1 r.1 t.1 hqr hrt
  have hpr := h.horizontalLT_trans_l4 p.1 q.1 r.1 hpq hqr
  apply inConvexPosition_four_of_all_orientation_pos_l4
  · exact h.ordered_outer_triple_orientation_pos_l4
      horizontalProfile.outerMaximum.1.2 p q r hpq hqr
  · exact h.ordered_outer_triple_orientation_pos_l4
      horizontalProfile.outerMaximum.1.2 p q t hpq hqt
  · exact h.ordered_outer_triple_orientation_pos_l4
      horizontalProfile.outerMaximum.1.2 p r t hpr hrt
  · exact h.ordered_outer_triple_orientation_pos_l4
      horizontalProfile.outerMaximum.1.2 q r t hqr hrt

end SukRegionGeometry

end

end ErdosSzekeres

end
