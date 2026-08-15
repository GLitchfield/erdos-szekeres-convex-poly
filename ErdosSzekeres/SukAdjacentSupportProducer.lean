module

public import ErdosSzekeres.SukRegionOrder

@[expose] public section

/-!
# The adjacent Suk support-region producer

This file formalizes the geometric producer in Suk's Observation 3.1.  Its
input contains two actual adjacent support-region chains and their two
anchor-extended caps.  Arrangement-cell and supporting-pair facts are outputs,
not fields of the input structure.
-/

namespace ErdosSzekeres

noncomputable section

/-- Five consecutive anchors of a cap, expressed by their complete local
order type. -/
structure SukFiveCapAnchors
    (x0 x1 x2 x3 x4 : Point 2) : Prop where
  orient012 : orientation x0 x1 x2 < 0
  orient013 : orientation x0 x1 x3 < 0
  orient014 : orientation x0 x1 x4 < 0
  orient023 : orientation x0 x2 x3 < 0
  orient024 : orientation x0 x2 x4 < 0
  orient034 : orientation x0 x3 x4 < 0
  orient123 : orientation x1 x2 x3 < 0
  orient124 : orientation x1 x2 x4 < 0
  orient134 : orientation x1 x3 x4 < 0
  orient234 : orientation x2 x3 x4 < 0

/-- Source-level data for two adjacent support-region chains in Suk's proof.
No field states an arrangement-cell fact, a strict-side fact, or the desired
mixed convexity conclusion. -/
structure SukAdjacentSupportData
    (x0 x1 x2 x3 x4 : Point 2)
    (left right : Finset (Point 2)) : Prop where
  anchorsCap : SukFiveCapAnchors x0 x1 x2 x3 x4
  disjoint : Disjoint left right
  generalPosition : InGeneralPosition
    (insert x0 (insert x1 (insert x2 (insert x3 (insert x4 (left ∪ right))))))
  leftRegion : ∀ ⦃p⦄, p ∈ left → p ∈ SukSupportRegion x0 x1 x2 x3
  rightRegion : ∀ ⦃p⦄, p ∈ right → p ∈ SukSupportRegion x1 x2 x3 x4
  leftChain : ∀ ⦃p⦄, p ∈ left → ∀ ⦃q⦄, q ∈ left → p ≠ q →
    SukRegionLE x0 x3 p q ∨ SukRegionLE x0 x3 q p
  rightChain : ∀ ⦃p⦄, p ∈ right → ∀ ⦃q⦄, q ∈ right → p ≠ q →
    SukRegionLE x1 x4 p q ∨ SukRegionLE x1 x4 q p
  leftCap : InConvexPosition (insert x2 left)
  rightCap : InConvexPosition (insert x2 right)

namespace SukAdjacentSupportData

variable {x0 x1 x2 x3 x4 : Point 2} {left right : Finset (Point 2)}

theorem anchor_not_left
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right) : x2 ∉ left := by
  intro hx2
  have hregion := h.leftRegion hx2
  simp [SukSupportRegion] at hregion

theorem anchor_not_right
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right) : x2 ∉ right := by
  intro hx2
  have hregion := h.rightRegion hx2
  simp [SukSupportRegion] at hregion

theorem certificate_generalPosition
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right) :
    InGeneralPosition (insert x2 (left ∪ right)) := by
  apply h.generalPosition.mono
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_union] at hp ⊢
  rcases hp with rfl | hp
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp))))

/-- The rank-three Grassmann--Plücker identity for five affine points. -/
private theorem orientation_plucker (a b c d e : Point 2) :
    orientation a b c * orientation a d e -
      orientation a b d * orientation a c e +
      orientation a b e * orientation a c d = 0 := by
  simp only [orientation]
  ring

private theorem support_base_orientation_pos
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (habd : orientation a b d < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : 0 < orientation b c p)
    (habp : orientation a b p < 0)
    (hcdp : orientation c d p < 0) :
    0 < orientation a d p := by
  have hpluckerC := orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p, orientation_swap b c d] at hpluckerC
  have hcap : orientation c a p < 0 := by
    nlinarith
  have hacp : 0 < orientation a c p := by
    rw [orientation_swap a c p] at hcap
    linarith
  have hpluckerA := orientation_plucker a b c d p
  nlinarith

private theorem left_base_orientation_pos
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right)
    {p : Point 2} (hp : p ∈ left) : 0 < orientation x0 x3 p := by
  have hregion := h.leftRegion hp
  change 0 < orientation x1 x2 p ∧
    orientation x0 x1 p < 0 ∧ orientation x2 x3 p < 0 at hregion
  rcases hregion with ⟨h12p, h01p, h23p⟩
  exact support_base_orientation_pos x0 x1 x2 x3 p
    h.anchorsCap.orient012 h.anchorsCap.orient013
    h.anchorsCap.orient023 h.anchorsCap.orient123 h12p h01p h23p

private theorem right_base_orientation_pos
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right)
    {p : Point 2} (hp : p ∈ right) : 0 < orientation x1 x4 p := by
  have hregion := h.rightRegion hp
  change 0 < orientation x2 x3 p ∧
    orientation x1 x2 p < 0 ∧ orientation x3 x4 p < 0 at hregion
  rcases hregion with ⟨h23p, h12p, h34p⟩
  exact support_base_orientation_pos x1 x2 x3 x4 p
    h.anchorsCap.orient123 h.anchorsCap.orient124
    h.anchorsCap.orient134 h.anchorsCap.orient234 h23p h12p h34p

/-- Reversing all three arguments reverses orientation. -/
private theorem orientation_reverse (a b c : Point 2) :
    orientation c b a = -orientation a b c := by
  simp only [orientation]
  ring

/-- The support signs on the first three consecutive edges force the
orientation across the first diagonal. -/
private theorem support_left_diagonal_pos
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : 0 < orientation b c p)
    (hcdp : orientation c d p < 0) :
    0 < orientation a c p := by
  have hplucker := orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p,
    orientation_cyclic' a p c, orientation_swap_last a c p,
    orientation_swap b c d] at hplucker
  nlinarith

/-- The adjacent support signs on the other side force the opposite sign
across the same diagonal. -/
private theorem support_left_diagonal_neg
    (a b c d p : Point 2)
    (habc : orientation a b c < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0)
    (hbcp : orientation b c p < 0)
    (hcdp : 0 < orientation c d p) :
    orientation a c p < 0 := by
  have hplucker := orientation_plucker c a b d p
  rw [orientation_cyclic' a b c,
    orientation_cyclic' a d c, orientation_swap_last a c d,
    orientation_swap b c p,
    orientation_cyclic' a p c, orientation_swap_last a c p,
    orientation_swap b c d] at hplucker
  nlinarith

/-- The reflected diagonal consequence for the last three consecutive
edges. -/
private theorem support_right_diagonal_pos
    (b c d e p : Point 2)
    (hbcd : orientation b c d < 0)
    (hbce : orientation b c e < 0)
    (hcde : orientation c d e < 0)
    (hcdp : 0 < orientation c d p)
    (hbcp : orientation b c p < 0) :
    0 < orientation c e p := by
  have hplucker := orientation_plucker c b d e p
  rw [orientation_swap b c d, orientation_swap b c e,
    orientation_swap b c p] at hplucker
  nlinarith

/-- The reflected adjacent support signs force the opposite last-diagonal
sign. -/
private theorem support_right_diagonal_neg
    (b c d e p : Point 2)
    (hbcd : orientation b c d < 0)
    (hbce : orientation b c e < 0)
    (hcde : orientation c d e < 0)
    (hcdp : orientation c d p < 0)
    (hbcp : 0 < orientation b c p) :
    orientation c e p < 0 := by
  have hplucker := orientation_plucker c b d e p
  rw [orientation_swap b c d, orientation_swap b c e,
    orientation_swap b c p] at hplucker
  nlinarith

/-- Every left support point sees the common anchor and every point in the
adjacent right support region inside the same positive wedge based at
`x0,x3`. -/
private theorem left_wedge_orientation_pos
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right)
    {p q : Point 2} (hp : p ∈ left) (hq : q ∈ right) :
    (0 < orientation p x0 x2 ∧ 0 < orientation p x3 x2) ∧
      (0 < orientation p x0 q ∧ 0 < orientation p x3 q) := by
  have hpRegion := h.leftRegion hp
  have hqRegion := h.rightRegion hq
  change 0 < orientation x1 x2 p ∧ orientation x0 x1 p < 0 ∧
    orientation x2 x3 p < 0 at hpRegion
  change 0 < orientation x2 x3 q ∧ orientation x1 x2 q < 0 ∧
    orientation x3 x4 q < 0 at hqRegion
  rcases hpRegion with ⟨h12p, h01p, h23p⟩
  rcases hqRegion with ⟨h23q, h12q, h34q⟩
  have h02p : 0 < orientation x0 x2 p :=
    support_left_diagonal_pos x0 x1 x2 x3 p
      h.anchorsCap.orient012 h.anchorsCap.orient023
      h.anchorsCap.orient123 h12p h23p
  have h02q : orientation x0 x2 q < 0 :=
    support_left_diagonal_neg x0 x1 x2 x3 q
      h.anchorsCap.orient012 h.anchorsCap.orient023
      h.anchorsCap.orient123 h12q h23q
  have h03p : 0 < orientation x0 x3 p := h.left_base_orientation_pos hp
  have h03q : 0 < orientation x0 x3 q := by
    have hplucker := orientation_plucker x3 x0 x2 x4 q
    rw [orientation_cyclic' x0 x2 x3,
      orientation_swap x0 x3 x4, orientation_swap x2 x3 q,
      orientation_swap x0 x3 q, orientation_swap x2 x3 x4] at hplucker
    nlinarith [h.anchorsCap.orient023, h.anchorsCap.orient034,
      h.anchorsCap.orient234]
  have h3pq : orientation x3 p q < 0 := by
    have hplucker := orientation_plucker x3 x0 x2 p q
    rw [orientation_cyclic' x0 x2 x3,
      orientation_swap x0 x3 p, orientation_swap x2 x3 q,
      orientation_swap x0 x3 q, orientation_swap x2 x3 p] at hplucker
    nlinarith [h.anchorsCap.orient023]
  have h01q : orientation x0 x1 q < 0 := by
    have hplucker := orientation_plucker x0 x1 x2 x3 q
    nlinarith [h.anchorsCap.orient012, h.anchorsCap.orient013,
      h.anchorsCap.orient023]
  have h0pq : orientation x0 p q < 0 := by
    have hplucker := orientation_plucker x0 x1 x2 p q
    nlinarith [h.anchorsCap.orient012]
  constructor
  · constructor
    · rw [orientation_cyclic' x0 x2 p]
      exact h02p
    · rw [orientation_reverse x2 x3 p]
      linarith
  · constructor
    · rw [orientation_swap x0 p q]
      linarith
    · rw [orientation_swap x3 p q]
      linarith

/-- The reflected wedge statement for a right support point. -/
private theorem right_wedge_orientation_neg
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right)
    {p q : Point 2} (hp : p ∈ right) (hq : q ∈ left) :
    (orientation p x1 x2 < 0 ∧ orientation p x4 x2 < 0) ∧
      (orientation p x1 q < 0 ∧ orientation p x4 q < 0) := by
  have hpRegion := h.rightRegion hp
  have hqRegion := h.leftRegion hq
  change 0 < orientation x2 x3 p ∧ orientation x1 x2 p < 0 ∧
    orientation x3 x4 p < 0 at hpRegion
  change 0 < orientation x1 x2 q ∧ orientation x0 x1 q < 0 ∧
    orientation x2 x3 q < 0 at hqRegion
  rcases hpRegion with ⟨h23p, h12p, h34p⟩
  rcases hqRegion with ⟨h12q, h01q, h23q⟩
  have h24p : 0 < orientation x2 x4 p :=
    support_right_diagonal_pos x1 x2 x3 x4 p
      h.anchorsCap.orient123 h.anchorsCap.orient124
      h.anchorsCap.orient234 h23p h12p
  have h24q : orientation x2 x4 q < 0 :=
    support_right_diagonal_neg x1 x2 x3 x4 q
      h.anchorsCap.orient123 h.anchorsCap.orient124
      h.anchorsCap.orient234 h23q h12q
  have h14p : 0 < orientation x1 x4 p := h.right_base_orientation_pos hp
  have h14q : 0 < orientation x1 x4 q := by
    have hplucker := orientation_plucker x1 x0 x2 x4 q
    rw [orientation_swap x0 x1 x2, orientation_swap x0 x1 x4,
      orientation_swap x0 x1 q] at hplucker
    nlinarith [h.anchorsCap.orient012, h.anchorsCap.orient014,
      h.anchorsCap.orient124]
  have h1qp : orientation x1 q p < 0 := by
    have hplucker := orientation_plucker x1 x2 x4 q p
    nlinarith [h.anchorsCap.orient124]
  have h4qp : orientation x4 q p < 0 := by
    have hplucker := orientation_plucker x4 x1 x2 q p
    rw [orientation_cyclic' x1 x2 x4,
      orientation_swap x1 x4 q, orientation_swap x2 x4 p,
      orientation_swap x1 x4 p, orientation_swap x2 x4 q] at hplucker
    nlinarith [h.anchorsCap.orient124]
  constructor
  · constructor
    · rw [orientation_cyclic' x1 x2 p]
      exact h12p
    · rw [orientation_reverse x2 x4 p]
      linarith
  · constructor
    · rw [orientation_cyclic' x1 q p]
      exact h1qp
    · rw [orientation_cyclic' x4 q p]
      exact h4qp

/-- A point inside the positive-base triangle inherits a positive line sign
from a point lying in the positive wedge at the triangle's outer vertex. -/
private theorem pair_orientation_pos_of_triangle_order
    (outerLeft outerRight outer inner z : Point 2)
    (houter : 0 < orientation outerLeft outerRight outer)
    (_hbase : 0 ≤ orientation outerLeft outerRight inner)
    (hedge1 : 0 ≤ orientation outerRight outer inner)
    (hedge2 : 0 ≤ orientation outer outerLeft inner)
    (hzLeft : 0 < orientation outer outerLeft z)
    (hzRight : 0 < orientation outer outerRight z)
    (hne : orientation outer inner z ≠ 0) :
    0 < orientation outer inner z := by
  have hplucker := orientation_plucker outer outerLeft outerRight inner z
  rw [orientation_cyclic' outerLeft outerRight outer] at hplucker
  have houterRightInner : orientation outer outerRight inner ≤ 0 := by
    rw [orientation_swap outerRight outer inner]
    linarith
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hterm0 :
        orientation outerLeft outerRight outer * orientation outer inner z < 0 :=
      mul_neg_of_pos_of_neg houter hneg
    have hterm1 :
        0 ≤ orientation outer outerLeft inner * orientation outer outerRight z :=
      mul_nonneg hedge2 hzRight.le
    have hterm2 :
        orientation outer outerLeft z * orientation outer outerRight inner ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hzLeft.le houterRightInner
    nlinarith
  · exact hpos

/-- The negative-wedge counterpart of
`pair_orientation_pos_of_triangle_order`. -/
private theorem pair_orientation_neg_of_triangle_order
    (outerLeft outerRight outer inner z : Point 2)
    (houter : 0 < orientation outerLeft outerRight outer)
    (_hbase : 0 ≤ orientation outerLeft outerRight inner)
    (hedge1 : 0 ≤ orientation outerRight outer inner)
    (hedge2 : 0 ≤ orientation outer outerLeft inner)
    (hzLeft : orientation outer outerLeft z < 0)
    (hzRight : orientation outer outerRight z < 0)
    (hne : orientation outer inner z ≠ 0) :
    orientation outer inner z < 0 := by
  have hplucker := orientation_plucker outer outerLeft outerRight inner z
  rw [orientation_cyclic' outerLeft outerRight outer] at hplucker
  have houterRightInner : orientation outer outerRight inner ≤ 0 := by
    rw [orientation_swap outerRight outer inner]
    linarith
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact hneg
  · have hterm0 :
        0 < orientation outerLeft outerRight outer * orientation outer inner z :=
      mul_pos houter hpos
    have hterm1 :
        orientation outer outerLeft inner * orientation outer outerRight z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hedge2 hzRight.le
    have hterm2 :
        0 ≤ orientation outer outerLeft z * orientation outer outerRight inner :=
      mul_nonneg_of_nonpos_of_nonpos hzLeft.le houterRightInner
    nlinarith

private theorem left_pair_orientation_ne_anchor
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right)
    {a b : Point 2} (ha : a ∈ left) (hb : b ∈ left) (hab : a ≠ b) :
    orientation a b x2 ≠ 0 := by
  have hax2 : a ≠ x2 := by
    intro hEq
    subst a
    exact h.anchor_not_left ha
  have hbx2 : b ≠ x2 := by
    intro hEq
    subst b
    exact h.anchor_not_left hb
  exact h.certificate_generalPosition (by simp [ha]) (by simp [hb]) (by simp)
    hab hax2 hbx2

private theorem right_pair_orientation_ne_anchor
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right)
    {a b : Point 2} (ha : a ∈ right) (hb : b ∈ right) (hab : a ≠ b) :
    orientation a b x2 ≠ 0 := by
  have hax2 : a ≠ x2 := by
    intro hEq
    subst a
    exact h.anchor_not_right ha
  have hbx2 : b ≠ x2 := by
    intro hEq
    subst b
    exact h.anchor_not_right hb
  exact h.certificate_generalPosition (by simp [ha]) (by simp [hb]) (by simp)
    hab hax2 hbx2

private theorem left_pair_orientation_ne_right
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right)
    {a b q : Point 2} (ha : a ∈ left) (hb : b ∈ left) (hq : q ∈ right)
    (hab : a ≠ b) : orientation a b q ≠ 0 := by
  have haq : a ≠ q := by
    intro hEq
    subst q
    exact Finset.disjoint_left.mp h.disjoint ha hq
  have hbq : b ≠ q := by
    intro hEq
    subst q
    exact Finset.disjoint_left.mp h.disjoint hb hq
  exact h.certificate_generalPosition (by simp [ha]) (by simp [hb]) (by simp [hq])
    hab haq hbq

private theorem right_pair_orientation_ne_left
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right)
    {a b q : Point 2} (ha : a ∈ right) (hb : b ∈ right) (hq : q ∈ left)
    (hab : a ≠ b) : orientation a b q ≠ 0 := by
  have haq : a ≠ q := by
    intro hEq
    subst q
    exact Finset.disjoint_left.mp h.disjoint hq ha
  have hbq : b ≠ q := by
    intro hEq
    subst q
    exact Finset.disjoint_left.mp h.disjoint hq hb
  exact h.certificate_generalPosition (by simp [ha]) (by simp [hb]) (by simp [hq])
    hab haq hbq

/-- A line through two comparable points in the left support region leaves the
common anchor and every point of the adjacent right region on the same strict
side. -/
theorem leftPair_sameStrictSide
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right)
    {a b q : Point 2} (ha : a ∈ left) (hb : b ∈ left) (hq : q ∈ right)
    (hab : a ≠ b) : SameStrictSide a b x2 q := by
  have hneAnchor := h.left_pair_orientation_ne_anchor ha hb hab
  have hneRight := h.left_pair_orientation_ne_right ha hb hq hab
  have haWedge := h.left_wedge_orientation_pos ha hq
  have hbWedge := h.left_wedge_orientation_pos hb hq
  rcases h.leftChain ha hb hab with habOrder | hbaOrder
  · have hinside := (mem_convexHull_triangle_iff_of_orientation_pos
      x0 x3 a b (h.left_base_orientation_pos ha)).mp habOrder
    rcases hinside with ⟨hbase, hedge1, hedge2⟩
    right
    constructor
    · exact pair_orientation_pos_of_triangle_order x0 x3 a b x2
        (h.left_base_orientation_pos ha) hbase hedge1 hedge2
        haWedge.1.1 haWedge.1.2 hneAnchor
    · exact pair_orientation_pos_of_triangle_order x0 x3 a b q
        (h.left_base_orientation_pos ha) hbase hedge1 hedge2
        haWedge.2.1 haWedge.2.2 hneRight
  · have hinside := (mem_convexHull_triangle_iff_of_orientation_pos
      x0 x3 b a (h.left_base_orientation_pos hb)).mp hbaOrder
    rcases hinside with ⟨hbase, hedge1, hedge2⟩
    have hneAnchor' : orientation b a x2 ≠ 0 := by
      rw [orientation_swap a b x2]
      exact neg_ne_zero.mpr hneAnchor
    have hneRight' : orientation b a q ≠ 0 := by
      rw [orientation_swap a b q]
      exact neg_ne_zero.mpr hneRight
    left
    constructor
    · have hpos := pair_orientation_pos_of_triangle_order x0 x3 b a x2
        (h.left_base_orientation_pos hb) hbase hedge1 hedge2
        hbWedge.1.1 hbWedge.1.2 hneAnchor'
      rw [orientation_swap a b x2] at hpos
      linarith
    · have hpos := pair_orientation_pos_of_triangle_order x0 x3 b a q
        (h.left_base_orientation_pos hb) hbase hedge1 hedge2
        hbWedge.2.1 hbWedge.2.2 hneRight'
      rw [orientation_swap a b q] at hpos
      linarith

/-- The right-to-left counterpart of `leftPair_sameStrictSide`. -/
theorem rightPair_sameStrictSide
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right)
    {a b q : Point 2} (ha : a ∈ right) (hb : b ∈ right) (hq : q ∈ left)
    (hab : a ≠ b) : SameStrictSide a b x2 q := by
  have hneAnchor := h.right_pair_orientation_ne_anchor ha hb hab
  have hneLeft := h.right_pair_orientation_ne_left ha hb hq hab
  have haWedge := h.right_wedge_orientation_neg ha hq
  have hbWedge := h.right_wedge_orientation_neg hb hq
  rcases h.rightChain ha hb hab with habOrder | hbaOrder
  · have hinside := (mem_convexHull_triangle_iff_of_orientation_pos
      x1 x4 a b (h.right_base_orientation_pos ha)).mp habOrder
    rcases hinside with ⟨hbase, hedge1, hedge2⟩
    left
    constructor
    · exact pair_orientation_neg_of_triangle_order x1 x4 a b x2
        (h.right_base_orientation_pos ha) hbase hedge1 hedge2
        haWedge.1.1 haWedge.1.2 hneAnchor
    · exact pair_orientation_neg_of_triangle_order x1 x4 a b q
        (h.right_base_orientation_pos ha) hbase hedge1 hedge2
        haWedge.2.1 haWedge.2.2 hneLeft
  · have hinside := (mem_convexHull_triangle_iff_of_orientation_pos
      x1 x4 b a (h.right_base_orientation_pos hb)).mp hbaOrder
    rcases hinside with ⟨hbase, hedge1, hedge2⟩
    have hneAnchor' : orientation b a x2 ≠ 0 := by
      rw [orientation_swap a b x2]
      exact neg_ne_zero.mpr hneAnchor
    have hneLeft' : orientation b a q ≠ 0 := by
      rw [orientation_swap a b q]
      exact neg_ne_zero.mpr hneLeft
    right
    constructor
    · have hneg := pair_orientation_neg_of_triangle_order x1 x4 b a x2
        (h.right_base_orientation_pos hb) hbase hedge1 hedge2
        hbWedge.1.1 hbWedge.1.2 hneAnchor'
      rw [orientation_swap a b x2] at hneg
      linarith
    · have hneg := pair_orientation_neg_of_triangle_order x1 x4 b a q
        (h.right_base_orientation_pos hb) hbase hedge1 hedge2
        hbWedge.2.1 hbWedge.2.2 hneLeft'
      rw [orientation_swap a b q] at hneg
      linarith

private theorem sameOpenCellOfLineArrangement_of_pairwise_sameStrictSide
    {t : Finset (Point 2)} {anchor replacement : Point 2}
    (hanchor : anchor ∉ t)
    (hsides : ∀ ⦃a⦄, a ∈ t → ∀ ⦃b⦄, b ∈ t → a ≠ b →
      SameStrictSide a b anchor replacement) :
    SameOpenCellOfLineArrangement t anchor replacement := by
  intro a ha b hb c hc
  change a ∈ insert anchor t at ha
  change b ∈ insert anchor t at hb
  change c ∈ insert anchor t at hc
  simp only [Finset.mem_insert] at ha hb hc
  rcases ha with rfl | ha <;> rcases hb with rfl | hb <;> rcases hc with rfl | hc
  · simp
  · simp
  · simp
  · have hbAnchor : b ≠ a := fun hEq ↦ hanchor (hEq ▸ hb)
    have hcAnchor : c ≠ a := fun hEq ↦ hanchor (hEq ▸ hc)
    by_cases hbc : b = c
    · subst c
      simp [replacePoint, hbAnchor]
    · have hsides' := hsides hb hc hbc
      rcases hsides' with ⟨hAnchor, hReplacement⟩ | ⟨hAnchor, hReplacement⟩
      all_goals
        simp only [replacePoint_self, replacePoint_of_ne hbAnchor,
          replacePoint_of_ne hcAnchor]
        rw [orientation_cyclic' b c replacement, orientation_cyclic' b c a]
        constructor <;> constructor <;> intro hsign <;> linarith
  · simp
  · have haAnchor : a ≠ b := fun hEq ↦ hanchor (hEq ▸ ha)
    have hcAnchor : c ≠ b := fun hEq ↦ hanchor (hEq ▸ hc)
    by_cases hac : a = c
    · subst c
      simp [replacePoint, haAnchor]
    · have hsides' := hsides ha hc hac
      rcases hsides' with ⟨hAnchor, hReplacement⟩ | ⟨hAnchor, hReplacement⟩
      all_goals
        simp only [replacePoint_of_ne haAnchor, replacePoint_self,
          replacePoint_of_ne hcAnchor]
        rw [orientation_swap_last a c replacement, orientation_swap_last a c b]
        constructor <;> constructor <;> intro hsign <;> linarith
  · have haAnchor : a ≠ c := fun hEq ↦ hanchor (hEq ▸ ha)
    have hbAnchor : b ≠ c := fun hEq ↦ hanchor (hEq ▸ hb)
    by_cases hab : a = b
    · subst b
      simp [replacePoint, haAnchor]
    · have hsides' := hsides ha hb hab
      rcases hsides' with ⟨hAnchor, hReplacement⟩ | ⟨hAnchor, hReplacement⟩
      all_goals
        simp only [replacePoint_of_ne haAnchor, replacePoint_of_ne hbAnchor,
          replacePoint_self]
        constructor <;> constructor <;> intro hsign <;> linarith
  · have haAnchor : a ≠ anchor := fun hEq ↦ hanchor (hEq ▸ ha)
    have hbAnchor : b ≠ anchor := fun hEq ↦ hanchor (hEq ▸ hb)
    have hcAnchor : c ≠ anchor := fun hEq ↦ hanchor (hEq ▸ hc)
    simp [replacePoint, haAnchor, hbAnchor, hcAnchor]

private theorem sameStrictSide_of_common
    {a b common c d : Point 2}
    (hc : SameStrictSide a b common c) (hd : SameStrictSide a b common d) :
    SameStrictSide a b c d := by
  rcases hc with ⟨hCommon, hc⟩ | ⟨hCommon, hc⟩ <;>
    rcases hd with ⟨hCommon', hd⟩ | ⟨hCommon', hd⟩
  · exact Or.inl ⟨hc, hd⟩
  · linarith
  · linarith
  · exact Or.inr ⟨hc, hd⟩

/-- The actual support-region and chain hypotheses produce the geometric
certificate consumed by the already formalized adjacent-region gluing
theorem. -/
theorem toCertificate
    (h : SukAdjacentSupportData x0 x1 x2 x3 x4 left right) :
    SukAdjacentRegionCertificate x2 left right where
  disjoint := h.disjoint
  anchor_not_left := h.anchor_not_left
  anchor_not_right := h.anchor_not_right
  generalPosition := h.certificate_generalPosition
  leftCap := h.leftCap
  rightCap := h.rightCap
  leftCell := by
    intro a b c q ha hb hc hq hab hac hbc
    have hsub : ({a, b, c} : Finset (Point 2)) ⊆ left := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    apply sameOpenCellOfLineArrangement_of_pairwise_sameStrictSide
    · exact fun hx2 ↦ h.anchor_not_left (hsub hx2)
    · intro u hu v hv huv
      exact h.leftPair_sameStrictSide (hsub hu) (hsub hv) hq huv
  rightCell := by
    intro a b c q ha hb hc hq hab hac hbc
    have hsub : ({a, b, c} : Finset (Point 2)) ⊆ right := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    apply sameOpenCellOfLineArrangement_of_pairwise_sameStrictSide
    · exact fun hx2 ↦ h.anchor_not_right (hsub hx2)
    · intro u hu v hv huv
      exact h.rightPair_sameStrictSide (hsub hu) (hsub hv) hq huv
  pairSupports := by
    intro a b c d ha hb hc hd hab hcd
    exact ⟨sameStrictSide_of_common
        (h.leftPair_sameStrictSide ha hb hc hab)
        (h.leftPair_sameStrictSide ha hb hd hab),
      sameStrictSide_of_common
        (h.rightPair_sameStrictSide hc hd ha hcd)
        (h.rightPair_sameStrictSide hc hd hb hcd)⟩

end SukAdjacentSupportData

end

end ErdosSzekeres

end
