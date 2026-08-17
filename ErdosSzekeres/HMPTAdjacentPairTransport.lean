module

public import ErdosSzekeres.HMPTVerticalChainDefs
public import ErdosSzekeres.HMPTSpikeOrderGeometry

@[expose] public section

/-!
# Signed transport for adjacent HMPT spike pairs

This module derives the directed supporting-line signs supplied by one strict
vertical comparison in either of two adjacent spike pools.  The sign at the
outer anchor comes directly from triangle containment.  The sign at a point
of the adjacent pool is transported through the raw support-region wedges.
-/

namespace ErdosSzekeres

noncomputable section

/-- The rank-three Grassmann--Plücker identity for five affine points. -/
private theorem hmptPair_orientation_plucker (a b c d e : Point 2) :
    orientation a b c * orientation a d e -
      orientation a b d * orientation a c e +
      orientation a b e * orientation a c d = 0 := by
  simp only [orientation]
  ring

/-- Reversing all three arguments reverses orientation. -/
private theorem hmptPair_orientation_reverse (a b c : Point 2) :
    orientation c b a = -orientation a b c := by
  simp only [orientation]
  ring

private theorem hmptPair_support_left_diagonal_pos
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : 0 < orientation b c p)
    (hcdp : orientation c d p < 0) :
    0 < orientation a c p := by
  have hplucker := hmptPair_orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p,
    orientation_cyclic' a p c, orientation_swap_last a c p,
    orientation_swap b c d] at hplucker
  nlinarith

private theorem hmptPair_support_left_diagonal_neg
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : orientation b c p < 0)
    (hcdp : 0 < orientation c d p) :
    orientation a c p < 0 := by
  have hplucker := hmptPair_orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p,
    orientation_cyclic' a p c, orientation_swap_last a c p,
    orientation_swap b c d] at hplucker
  nlinarith

private theorem hmptPair_support_right_diagonal_pos
    (b c d e p : Point 2)
    (hbcd : orientation b c d < 0)
    (hbce : orientation b c e < 0)
    (hcde : orientation c d e < 0)
    (hcdp : 0 < orientation c d p)
    (hbcp : orientation b c p < 0) :
    0 < orientation c e p := by
  have hplucker := hmptPair_orientation_plucker c b d e p
  rw [orientation_swap b c d, orientation_swap b c e,
    orientation_swap b c p] at hplucker
  nlinarith

private theorem hmptPair_support_right_diagonal_neg
    (b c d e p : Point 2)
    (hbcd : orientation b c d < 0)
    (hbce : orientation b c e < 0)
    (hcde : orientation c d e < 0)
    (hcdp : orientation c d p < 0)
    (hbcp : 0 < orientation b c p) :
    orientation c e p < 0 := by
  have hplucker := hmptPair_orientation_plucker c b d e p
  rw [orientation_swap b c d, orientation_swap b c e,
    orientation_swap b c p] at hplucker
  nlinarith

/-- A point inside a positive-base triangle inherits a positive line sign
from a point in the positive wedge at the triangle's outer vertex. -/
private theorem hmptPair_orientation_pos_of_triangle_order
    (outerLeft outerRight outer inner z : Point 2)
    (houter : 0 < orientation outerLeft outerRight outer)
    (_hbase : 0 ≤ orientation outerLeft outerRight inner)
    (hedge1 : 0 ≤ orientation outerRight outer inner)
    (hedge2 : 0 ≤ orientation outer outerLeft inner)
    (hzLeft : 0 < orientation outer outerLeft z)
    (hzRight : 0 < orientation outer outerRight z)
    (hne : orientation outer inner z ≠ 0) :
    0 < orientation outer inner z := by
  have hplucker := hmptPair_orientation_plucker
    outer outerLeft outerRight inner z
  rw [orientation_cyclic' outerLeft outerRight outer] at hplucker
  have houterRightInner : orientation outer outerRight inner ≤ 0 := by
    rw [orientation_swap outerRight outer inner]
    linarith
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hterm0 :
        orientation outerLeft outerRight outer *
            orientation outer inner z < 0 :=
      mul_neg_of_pos_of_neg houter hneg
    have hterm1 :
        0 ≤ orientation outer outerLeft inner *
            orientation outer outerRight z :=
      mul_nonneg hedge2 hzRight.le
    have hterm2 :
        orientation outer outerLeft z *
            orientation outer outerRight inner ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hzLeft.le houterRightInner
    nlinarith
  · exact hpos

/-- The negative-wedge counterpart of
`hmptPair_orientation_pos_of_triangle_order`. -/
private theorem hmptPair_orientation_neg_of_triangle_order
    (outerLeft outerRight outer inner z : Point 2)
    (houter : 0 < orientation outerLeft outerRight outer)
    (_hbase : 0 ≤ orientation outerLeft outerRight inner)
    (hedge1 : 0 ≤ orientation outerRight outer inner)
    (hedge2 : 0 ≤ orientation outer outerLeft inner)
    (hzLeft : orientation outer outerLeft z < 0)
    (hzRight : orientation outer outerRight z < 0)
    (hne : orientation outer inner z ≠ 0) :
    orientation outer inner z < 0 := by
  have hplucker := hmptPair_orientation_plucker
    outer outerLeft outerRight inner z
  rw [orientation_cyclic' outerLeft outerRight outer] at hplucker
  have houterRightInner : orientation outer outerRight inner ≤ 0 := by
    rw [orientation_swap outerRight outer inner]
    linarith
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact hneg
  · have hterm0 :
        0 < orientation outerLeft outerRight outer *
            orientation outer inner z :=
      mul_pos houter hpos
    have hterm1 :
        orientation outer outerLeft inner *
            orientation outer outerRight z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hedge2 hzRight.le
    have hterm2 :
        0 ≤ orientation outer outerLeft z *
            orientation outer outerRight inner :=
      mul_nonneg_of_nonpos_of_nonpos hzLeft.le houterRightInner
    nlinarith

namespace HMPTAdjacentSpikeGeometry

variable {x0 x1 x2 x3 x4 : Point 2}
  {leftPool rightPool : Finset (Point 2)}

private def leftGeometry
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool) :
    SukRegionGeometry x0 x1 x2 x3 leftPool where
  anchorsCap := h.anchorsCap.leftFour
  generalPosition := by
    apply h.generalPosition.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_union] at hp ⊢
    rcases hp with rfl | rfl | rfl | rfl | hp
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))
  region := by
    intro p hp
    exact h.leftRegion hp

private def rightGeometry
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool) :
    SukRegionGeometry x1 x2 x3 x4 rightPool where
  anchorsCap := h.anchorsCap.rightFour
  generalPosition := by
    apply h.generalPosition.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_union] at hp ⊢
    rcases hp with rfl | rfl | rfl | rfl | hp
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp)))))
  region := by
    intro p hp
    exact h.rightRegion hp

private theorem left_base_orientation_pos
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    {p : Point 2} (hp : p ∈ leftPool) :
    0 < orientation x0 x3 p := by
  exact h.leftGeometry.base_orientation_pos ⟨p, hp⟩

private theorem right_base_orientation_pos
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    {p : Point 2} (hp : p ∈ rightPool) :
    0 < orientation x1 x4 p := by
  exact h.rightGeometry.base_orientation_pos ⟨p, hp⟩

/-- The portion of the left adjacent-support wedge used for remote transport. -/
private theorem left_remote_wedge
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    {p q : Point 2} (hp : p ∈ leftPool) (hq : q ∈ rightPool) :
    0 < orientation p x0 q ∧ 0 < orientation p x3 q := by
  have hpRegion := h.leftRegion hp
  have hqRegion := h.rightRegion hq
  change 0 < orientation x1 x2 p ∧ orientation x0 x1 p < 0 ∧
    orientation x2 x3 p < 0 at hpRegion
  change 0 < orientation x2 x3 q ∧ orientation x1 x2 q < 0 ∧
    orientation x3 x4 q < 0 at hqRegion
  rcases hpRegion with ⟨h12p, h01p, h23p⟩
  rcases hqRegion with ⟨h23q, h12q, h34q⟩
  have h02p : 0 < orientation x0 x2 p :=
    hmptPair_support_left_diagonal_pos x0 x1 x2 x3 p
      h.anchorsCap.orient012 h.anchorsCap.orient023
      h.anchorsCap.orient123 h12p h23p
  have h02q : orientation x0 x2 q < 0 :=
    hmptPair_support_left_diagonal_neg x0 x1 x2 x3 q
      h.anchorsCap.orient012 h.anchorsCap.orient023
      h.anchorsCap.orient123 h12q h23q
  have h03p : 0 < orientation x0 x3 p := h.left_base_orientation_pos hp
  have h03q : 0 < orientation x0 x3 q := by
    have hplucker := hmptPair_orientation_plucker x3 x0 x2 x4 q
    rw [orientation_cyclic' x0 x2 x3,
      orientation_swap x0 x3 x4, orientation_swap x2 x3 q,
      orientation_swap x0 x3 q, orientation_swap x2 x3 x4] at hplucker
    nlinarith [h.anchorsCap.orient023, h.anchorsCap.orient034,
      h.anchorsCap.orient234]
  have h3pq : orientation x3 p q < 0 := by
    have hplucker := hmptPair_orientation_plucker x3 x0 x2 p q
    rw [orientation_cyclic' x0 x2 x3,
      orientation_swap x0 x3 p, orientation_swap x2 x3 q,
      orientation_swap x0 x3 q, orientation_swap x2 x3 p] at hplucker
    nlinarith [h.anchorsCap.orient023]
  have h01q : orientation x0 x1 q < 0 := by
    have hplucker := hmptPair_orientation_plucker x0 x1 x2 x3 q
    nlinarith [h.anchorsCap.orient012, h.anchorsCap.orient013,
      h.anchorsCap.orient023]
  have h0pq : orientation x0 p q < 0 := by
    have hplucker := hmptPair_orientation_plucker x0 x1 x2 p q
    nlinarith [h.anchorsCap.orient012]
  constructor
  · rw [orientation_swap x0 p q]
    linarith
  · rw [orientation_swap x3 p q]
    linarith

/-- The portion of the right adjacent-support wedge used for remote transport. -/
private theorem right_remote_wedge
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    {p q : Point 2} (hp : p ∈ rightPool) (hq : q ∈ leftPool) :
    orientation p x1 q < 0 ∧ orientation p x4 q < 0 := by
  have hpRegion := h.rightRegion hp
  have hqRegion := h.leftRegion hq
  change 0 < orientation x2 x3 p ∧ orientation x1 x2 p < 0 ∧
    orientation x3 x4 p < 0 at hpRegion
  change 0 < orientation x1 x2 q ∧ orientation x0 x1 q < 0 ∧
    orientation x2 x3 q < 0 at hqRegion
  rcases hpRegion with ⟨h23p, h12p, h34p⟩
  rcases hqRegion with ⟨h12q, h01q, h23q⟩
  have h24p : 0 < orientation x2 x4 p :=
    hmptPair_support_right_diagonal_pos x1 x2 x3 x4 p
      h.anchorsCap.orient123 h.anchorsCap.orient124
      h.anchorsCap.orient234 h23p h12p
  have h24q : orientation x2 x4 q < 0 :=
    hmptPair_support_right_diagonal_neg x1 x2 x3 x4 q
      h.anchorsCap.orient123 h.anchorsCap.orient124
      h.anchorsCap.orient234 h23q h12q
  have h14p : 0 < orientation x1 x4 p := h.right_base_orientation_pos hp
  have h14q : 0 < orientation x1 x4 q := by
    have hplucker := hmptPair_orientation_plucker x1 x0 x2 x4 q
    rw [orientation_swap x0 x1 x2, orientation_swap x0 x1 x4,
      orientation_swap x0 x1 q] at hplucker
    nlinarith [h.anchorsCap.orient012, h.anchorsCap.orient014,
      h.anchorsCap.orient124]
  have h1qp : orientation x1 q p < 0 := by
    have hplucker := hmptPair_orientation_plucker x1 x2 x4 q p
    nlinarith [h.anchorsCap.orient124]
  have h4qp : orientation x4 q p < 0 := by
    have hplucker := hmptPair_orientation_plucker x4 x1 x2 q p
    rw [orientation_cyclic' x1 x2 x4,
      orientation_swap x1 x4 q, orientation_swap x2 x4 p,
      orientation_swap x1 x4 p, orientation_swap x2 x4 q] at hplucker
    nlinarith [h.anchorsCap.orient124]
  constructor
  · rw [orientation_cyclic' x1 q p]
    exact h1qp
  · rw [orientation_cyclic' x4 q p]
    exact h4qp

/-- A strict left-pool vertical comparison fixes both the outer-right anchor
and every point of the adjacent right pool on the negative side of the
directed pair. -/
theorem leftPair_orientation_neg
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    {a b q : Point 2}
    (ha : a ∈ leftPool) (hb : b ∈ leftPool) (hq : q ∈ rightPool)
    (hv : HMPTSpikeVerticalLT x0 x3 a b) :
    orientation a b x3 < 0 ∧ orientation a b q < 0 := by
  have haBase := h.left_base_orientation_pos ha
  have hbBase := h.left_base_orientation_pos hb
  have haInside : a ∈ convexHull ℝ (triangle x0 x3 b) :=
    hv.2 (subset_convexHull ℝ (triangle x0 x3 a) (by simp [triangle]))
  have hinside :=
    (mem_convexHull_triangle_iff_of_orientation_pos x0 x3 b a hbBase).mp
      haInside
  have hax3 : a ≠ x3 := by
    intro heq
    subst a
    simp at haBase
  have hbx3 : b ≠ x3 := by
    intro heq
    subst b
    simp at hbBase
  have hanchorNe : orientation a b x3 ≠ 0 :=
    h.generalPosition (by simp [ha]) (by simp [hb]) (by simp)
      hv.1 hax3 hbx3
  have hanchorWeak : orientation a b x3 ≤ 0 := by
    have hedge := hinside.2.1
    rw [hmptPair_orientation_reverse a b x3] at hedge
    linarith
  have hanchor : orientation a b x3 < 0 :=
    lt_of_le_of_ne hanchorWeak hanchorNe
  have hbq : b ≠ q := by
    intro heq
    subst q
    exact Finset.disjoint_left.mp h.disjoint hb hq
  have haq : a ≠ q := by
    intro heq
    subst q
    exact Finset.disjoint_left.mp h.disjoint ha hq
  have hbaqNe : orientation b a q ≠ 0 :=
    h.generalPosition (by simp [hb]) (by simp [ha]) (by simp [hq])
      hv.1.symm hbq haq
  have hwedge := h.left_remote_wedge hb hq
  have hbaqPos : 0 < orientation b a q :=
    hmptPair_orientation_pos_of_triangle_order x0 x3 b a q
      hbBase hinside.1 hinside.2.1 hinside.2.2
      hwedge.1 hwedge.2 hbaqNe
  have hremote : orientation a b q < 0 := by
    rw [orientation_swap a b q] at hbaqPos
    linarith
  exact ⟨hanchor, hremote⟩

/-- A strict right-pool vertical comparison fixes both the outer-left anchor
and every point of the adjacent left pool on the positive side of the
directed pair. -/
theorem rightPair_orientation_pos
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    {a b q : Point 2}
    (ha : a ∈ rightPool) (hb : b ∈ rightPool) (hq : q ∈ leftPool)
    (hv : HMPTSpikeVerticalLT x1 x4 a b) :
    0 < orientation a b x1 ∧ 0 < orientation a b q := by
  have haBase := h.right_base_orientation_pos ha
  have hbBase := h.right_base_orientation_pos hb
  have haInside : a ∈ convexHull ℝ (triangle x1 x4 b) :=
    hv.2 (subset_convexHull ℝ (triangle x1 x4 a) (by simp [triangle]))
  have hinside :=
    (mem_convexHull_triangle_iff_of_orientation_pos x1 x4 b a hbBase).mp
      haInside
  have hax1 : a ≠ x1 := by
    intro heq
    subst a
    simp at haBase
  have hbx1 : b ≠ x1 := by
    intro heq
    subst b
    simp at hbBase
  have hanchorNe : orientation a b x1 ≠ 0 :=
    h.generalPosition (by simp [ha]) (by simp [hb]) (by simp)
      hv.1 hax1 hbx1
  have hanchorWeak : 0 ≤ orientation a b x1 := by
    rw [orientation_cyclic' b x1 a]
    exact hinside.2.2
  have hanchor : 0 < orientation a b x1 :=
    lt_of_le_of_ne hanchorWeak (Ne.symm hanchorNe)
  have hbq : b ≠ q := by
    intro heq
    subst q
    exact Finset.disjoint_left.mp h.disjoint hq hb
  have haq : a ≠ q := by
    intro heq
    subst q
    exact Finset.disjoint_left.mp h.disjoint hq ha
  have hbaqNe : orientation b a q ≠ 0 :=
    h.generalPosition (by simp [hb]) (by simp [ha]) (by simp [hq])
      hv.1.symm hbq haq
  have hwedge := h.right_remote_wedge hb hq
  have hbaqNeg : orientation b a q < 0 :=
    hmptPair_orientation_neg_of_triangle_order x1 x4 b a q
      hbBase hinside.1 hinside.2.1 hinside.2.2
      hwedge.1 hwedge.2 hbaqNe
  have hremote : 0 < orientation a b q := by
    rw [orientation_swap a b q] at hbaqNeg
    linarith
  exact ⟨hanchor, hremote⟩

end HMPTAdjacentSpikeGeometry

end

end ErdosSzekeres

end
