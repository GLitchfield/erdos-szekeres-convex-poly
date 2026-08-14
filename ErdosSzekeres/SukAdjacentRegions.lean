module

public import ErdosSzekeres.TothValtrOrderType

@[expose] public section

/-!
# Suk support regions and the adjacent-region gluing consumer

This file freezes the geometric vocabulary used in Suk's proof and proves the
local-to-global half of Observation 3.1.  The later producer must still derive
the certificate below from two adjacent support regions and chains in their
triangle-containment orders.
-/

namespace ErdosSzekeres

noncomputable section

/-- The open support region bounded by one edge of a cap and the two adjacent
edge lines. -/
def SukSupportRegion
    (previous left right next : Point 2) : Set (Point 2) :=
  {p | 0 < orientation left right p ∧
    orientation previous left p < 0 ∧ orientation right next p < 0}

/-- The triangle-containment order used inside one support region. -/
def SukRegionLE (outerLeft outerRight p q : Point 2) : Prop :=
  q ∈ convexHull ℝ (triangle outerLeft outerRight p)

/-- Replace one anchor point while fixing every other point. -/
def replacePoint (anchor replacement p : Point 2) : Point 2 :=
  if p = anchor then replacement else p

@[simp] theorem replacePoint_self (anchor replacement : Point 2) :
    replacePoint anchor replacement anchor = replacement := by
  simp [replacePoint]

@[simp] theorem replacePoint_of_ne {anchor replacement p : Point 2}
    (hp : p ≠ anchor) : replacePoint anchor replacement p = p := by
  simp [replacePoint, hp]

/-- Membership in the same open cell of the line arrangement of `t`, stated
as the exact orientation-sign replacement property needed downstream. -/
def SameOpenCellOfLineArrangement
    (t : Finset (Point 2)) (anchor replacement : Point 2) : Prop :=
  PreservesOrientationSignsOn (replacePoint anchor replacement)
    (insert anchor t)

theorem replacePoint_injOn_insert
    {t : Finset (Point 2)} {anchor replacement : Point 2}
    (ha : anchor ∉ t) (hr : replacement ∉ t) :
    Set.InjOn (replacePoint anchor replacement)
      (↑(insert anchor t) : Set (Point 2)) := by
  intro x hx y hy hxy
  change x ∈ insert anchor t at hx
  change y ∈ insert anchor t at hy
  simp only [Finset.mem_insert] at hx hy
  by_cases hxa : x = anchor
  · subst x
    rcases hy with rfl | hy
    · rfl
    · have hya : y ≠ anchor := by
        intro hya
        subst y
        exact ha hy
      rw [replacePoint_self, replacePoint_of_ne hya] at hxy
      exact (hr (hxy.symm ▸ hy)).elim
  · have hxMem : x ∈ t := hx.resolve_left hxa
    rcases hy with rfl | hy
    · rw [replacePoint_of_ne hxa, replacePoint_self] at hxy
      exact (hr (hxy ▸ hxMem)).elim
    · have hya : y ≠ anchor := by
        intro hya
        subst y
        exact ha hy
      rw [replacePoint_of_ne hxa, replacePoint_of_ne hya] at hxy
      exact hxy

theorem image_replacePoint_insert
    {t : Finset (Point 2)} {anchor replacement : Point 2}
    (ha : anchor ∉ t) :
    (insert anchor t).image (replacePoint anchor replacement) =
      insert replacement t := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simp
    · have hqa : q ≠ anchor := by
        intro hqa
        subst q
        exact ha hq
      rw [replacePoint_of_ne hqa]
      exact Finset.mem_insert_of_mem hq
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_image.mpr ⟨anchor, by simp, by simp⟩
    · apply Finset.mem_image.mpr
      have hpa : p ≠ anchor := by
        intro hpa
        subst p
        exact ha hp
      exact ⟨p, Finset.mem_insert_of_mem hp, replacePoint_of_ne hpa⟩

/-- Replacing a point by another point in the same arrangement cell preserves
convexity of the finite set. -/
theorem inConvexPosition_replacePoint_iff
    {t : Finset (Point 2)} {anchor replacement : Point 2}
    (ha : anchor ∉ t) (hr : replacement ∉ t)
    (hgp : InGeneralPosition (insert anchor t))
    (hcell : SameOpenCellOfLineArrangement t anchor replacement) :
    InConvexPosition (insert replacement t) ↔
      InConvexPosition (insert anchor t) := by
  rw [← image_replacePoint_insert ha]
  exact inConvexPosition_image_iff_of_preservesOrientationSignsOn
    hgp (replacePoint_injOn_insert ha hr) hcell

/-- Two points lie strictly on the same side of an oriented line. -/
def SameStrictSide (a b c d : Point 2) : Prop :=
  (orientation a b c < 0 ∧ orientation a b d < 0) ∨
    (0 < orientation a b c ∧ 0 < orientation a b d)

/-- If each of two disjoint pairs supports the other pair on one strict side,
the four points are in convex position. -/
theorem inConvexPosition_four_of_opposite_pair_supports
    (a b c d : Point 2)
    (hgp : InGeneralPosition {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (habSide : SameStrictSide a b c d)
    (hcdSide : SameStrictSide c d a b) :
    InConvexPosition {a, b, c, d} := by
  rw [inConvexPosition_four_iff_orientation_signs a b c d
    hgp hab hac had hbc hbd hcd]
  unfold SameStrictSide at habSide hcdSide
  unfold InsideTriangleBySigns
  have hbca : orientation b c a = orientation a b c :=
    orientation_cyclic a b c
  have hdba : orientation d b a = -orientation a b d := by
    rw [orientation_swap b d a, orientation_cyclic a b d]
  have hacb : orientation a c b = -orientation a b c :=
    orientation_swap_last a b c
  have hdab : orientation d a b = orientation a b d :=
    orientation_cyclic' a b d
  have hbdc : orientation b d c = -orientation c d b := by
    rw [← orientation_cyclic c d b, orientation_swap]
  have hdac : orientation d a c = orientation c d a :=
    orientation_cyclic c d a
  have hbcd : orientation b c d = orientation c d b :=
    (orientation_cyclic b c d).symm
  have hcad : orientation c a d = -orientation c d a :=
    orientation_swap_last c d a
  rw [hbca, hdba, hacb, hdab, hbdc, hdac, hbcd, hcad]
  rcases habSide with habSide | habSide <;>
    rcases hcdSide with hcdSide | hcdSide
  all_goals
    constructor
    · rintro (h | h) <;> rcases h with ⟨h1, h2, h3, h4⟩ <;> linarith
    · constructor
      · rintro (h | h) <;> rcases h with ⟨h1, h2, h3, h4⟩ <;> linarith
      · constructor
        · rintro (h | h) <;> rcases h with ⟨h1, h2, h3, h4⟩ <;> linarith
        · rintro (h | h) <;> rcases h with ⟨h1, h2, h3, h4⟩ <;> linarith

/-- The exact local certificate extracted in the proof of Suk's adjacent-region
observation.  Its fields are arrangement-cell and supporting-line facts, not
the convexity of the final union. -/
structure SukAdjacentRegionCertificate
    (anchor : Point 2) (left right : Finset (Point 2)) : Prop where
  disjoint : Disjoint left right
  anchor_not_left : anchor ∉ left
  anchor_not_right : anchor ∉ right
  generalPosition : InGeneralPosition (insert anchor (left ∪ right))
  leftCap : InConvexPosition (insert anchor left)
  rightCap : InConvexPosition (insert anchor right)
  leftCell : ∀ ⦃a b c q : Point 2⦄,
    a ∈ left → b ∈ left → c ∈ left → q ∈ right →
    a ≠ b → a ≠ c → b ≠ c →
    SameOpenCellOfLineArrangement {a, b, c} anchor q
  rightCell : ∀ ⦃a b c q : Point 2⦄,
    a ∈ right → b ∈ right → c ∈ right → q ∈ left →
    a ≠ b → a ≠ c → b ≠ c →
    SameOpenCellOfLineArrangement {a, b, c} anchor q
  pairSupports : ∀ ⦃a b c d : Point 2⦄,
    a ∈ left → b ∈ left → c ∈ right → d ∈ right →
    a ≠ b → c ≠ d → SameStrictSide a b c d ∧ SameStrictSide c d a b

theorem SukAdjacentRegionCertificate.left_three_right_one
    {anchor : Point 2} {left right : Finset (Point 2)}
    (h : SukAdjacentRegionCertificate anchor left right)
    {a b c q : Point 2}
    (ha : a ∈ left) (hb : b ∈ left) (hc : c ∈ left) (hq : q ∈ right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    InConvexPosition {a, b, c, q} := by
  have hanchorNot : anchor ∉ ({a, b, c} : Finset (Point 2)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun hEq => h.anchor_not_left (hEq ▸ ha),
      fun hEq => h.anchor_not_left (hEq ▸ hb),
      fun hEq => h.anchor_not_left (hEq ▸ hc)⟩
  have hqNot : q ∉ ({a, b, c} : Finset (Point 2)) := by
    intro hqMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqMem
    rcases hqMem with hqa | hqb | hqc
    · subst q
      exact (Finset.disjoint_left.mp h.disjoint ha hq).elim
    · subst q
      exact (Finset.disjoint_left.mp h.disjoint hb hq).elim
    · subst q
      exact (Finset.disjoint_left.mp h.disjoint hc hq).elim
  have hconv : InConvexPosition (insert q {a, b, c}) := by
    apply (inConvexPosition_replacePoint_iff hanchorNot hqNot
    (h.generalPosition.mono <| by
      intro p hp
      simp only [Finset.mem_insert] at hp ⊢
      rcases hp with rfl | hp
      · exact Or.inl rfl
      · apply Or.inr
        apply Finset.mem_union_left
        simp only [Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl <;> assumption)
    (h.leftCell ha hb hc hq hab hac hbc)).mpr
    apply h.leftCap.mono
    intro p hp
    simp only [Finset.mem_insert] at hp ⊢
    rcases hp with rfl | hp
    · exact Or.inl rfl
    · apply Or.inr
      simp only [Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
  convert hconv using 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem SukAdjacentRegionCertificate.right_three_left_one
    {anchor : Point 2} {left right : Finset (Point 2)}
    (h : SukAdjacentRegionCertificate anchor left right)
    {a b c q : Point 2}
    (ha : a ∈ right) (hb : b ∈ right) (hc : c ∈ right) (hq : q ∈ left)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    InConvexPosition {a, b, c, q} := by
  let hswap : SukAdjacentRegionCertificate anchor right left :=
    { disjoint := h.disjoint.symm
      anchor_not_left := h.anchor_not_right
      anchor_not_right := h.anchor_not_left
      generalPosition := by simpa [Finset.union_comm] using h.generalPosition
      leftCap := h.rightCap
      rightCap := h.leftCap
      leftCell := h.rightCell
      rightCell := h.leftCell
      pairSupports := by
        intro x y z w hx hy hz hw hxy hzw
        have hsides := h.pairSupports hz hw hx hy hzw hxy
        exact ⟨hsides.2, hsides.1⟩ }
  exact hswap.left_three_right_one ha hb hc hq hab hac hbc

theorem SukAdjacentRegionCertificate.two_two
    {anchor : Point 2} {left right : Finset (Point 2)}
    (h : SukAdjacentRegionCertificate anchor left right)
    {a b c d : Point 2}
    (ha : a ∈ left) (hb : b ∈ left) (hc : c ∈ right) (hd : d ∈ right)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    InConvexPosition {a, b, c, d} := by
  have hgp : InGeneralPosition ({a, b, c, d} : Finset (Point 2)) := by
    apply h.generalPosition.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals simp [ha, hb, hc, hd]
  apply inConvexPosition_four_of_opposite_pair_supports
    a b c d hgp hab hac had hbc hbd hcd
  · exact (h.pairSupports ha hb hc hd hab hcd).1
  · exact (h.pairSupports ha hb hc hd hab hcd).2

set_option maxHeartbeats 1000000 in
/-- Suk's adjacent-region gluing observation: a left-cap and a right-cap in
adjacent certified regions have a convex union. -/
theorem SukAdjacentRegionCertificate.inConvexPosition_union
    {anchor : Point 2} {left right : Finset (Point 2)}
    (h : SukAdjacentRegionCertificate anchor left right) :
    InConvexPosition (left ∪ right) := by
  apply (inConvexPosition_iff_four_subsets (left ∪ right)
    (h.generalPosition.mono <| by
      intro p hp
      exact Finset.mem_insert_of_mem hp)).mpr
  intro t ht hcard
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ :=
    Finset.card_eq_four.mp hcard
  have ha := ht (by simp : a ∈ ({a, b, c, d} : Finset (Point 2)))
  have hb := ht (by simp : b ∈ ({a, b, c, d} : Finset (Point 2)))
  have hc := ht (by simp : c ∈ ({a, b, c, d} : Finset (Point 2)))
  have hd := ht (by simp : d ∈ ({a, b, c, d} : Finset (Point 2)))
  simp only [Finset.mem_union] at ha hb hc hd
  have hleft : ∀ ⦃w x y z : Point 2⦄,
      w ∈ left → x ∈ left → y ∈ left → z ∈ left →
      InConvexPosition {w, x, y, z} := by
    intro w x y z hw hx hy hz
    apply h.leftCap.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
    aesop
  have hright : ∀ ⦃w x y z : Point 2⦄,
      w ∈ right → x ∈ right → y ∈ right → z ∈ right →
      InConvexPosition {w, x, y, z} := by
    intro w x y z hw hx hy hz
    apply h.rightCap.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
    aesop
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hc with hc | hc <;> rcases hd with hd | hd
  · exact hleft ha hb hc hd
  · exact h.left_three_right_one ha hb hc hd hab hac hbc
  · convert h.left_three_right_one ha hb hd hc hab had hbd using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · exact h.two_two ha hb hc hd hab hac had hbc hbd hcd
  · convert h.left_three_right_one ha hc hd hb hac had hcd using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert h.two_two ha hc hb hd hac hab had hbc.symm hcd hbd using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert h.two_two ha hd hb hc had hab hac hbd.symm hcd.symm hbc using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert h.right_three_left_one hb hc hd ha hbc hbd hcd using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert h.left_three_right_one hb hc hd ha hbc hbd hcd using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert h.two_two hb hc ha hd hbc hab.symm hbd hac.symm hcd had using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert h.two_two hb hd ha hc hbd hab.symm hbc had.symm hcd.symm hac using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert h.right_three_left_one ha hc hd hb hac had hcd using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert h.two_two hc hd ha hb hcd hac.symm hbc.symm had.symm hbd.symm hab using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert h.right_three_left_one ha hb hd hc hab had hbd using 1
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · exact h.right_three_left_one ha hb hc hd hab hac hbc
  · exact hright ha hb hc hd

end

end ErdosSzekeres

end
