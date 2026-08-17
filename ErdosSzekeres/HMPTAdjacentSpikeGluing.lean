module

public import ErdosSzekeres.HMPTAdjacentPairTransport

@[expose] public section

/-!
# Convex gluing of adjacent HMPT spike chains

This file closes the geometric C3 step for two adjacent HMPT spike pools.  The
right anchored subchain of the left profile and the left anchored subchain of
the right profile form one set in convex position.
-/

namespace ErdosSzekeres

noncomputable section

namespace HMPTAdjacentSpikeGeometry

variable {x0 x1 x2 x3 x4 : Point 2}
  {leftPool rightPool : Finset (Point 2)}

private theorem strictVertical_comparable_of_selected
    {outerLeft outerRight : Point 2} {s : Finset (Point 2)}
    {verticalChain selected : Finset (↥s)}
    (hchain : HMPTMaximumChain
      (fun p q : ↥s ↦ HMPTSpikeVerticalLE outerLeft outerRight p.1 q.1)
      verticalChain)
    (hselected : selected ⊆ verticalChain)
    {p q : Point 2}
    (hp : p ∈ hmptChainPoints selected)
    (hq : q ∈ hmptChainPoints selected)
    (hpq : p ≠ q) :
    HMPTSpikeVerticalLT outerLeft outerRight p q ∨
      HMPTSpikeVerticalLT outerLeft outerRight q p := by
  unfold hmptChainPoints at hp hq
  rcases Finset.mem_map.mp hp with ⟨p', hp', rfl⟩
  rcases Finset.mem_map.mp hq with ⟨q', hq', rfl⟩
  have hpq' : p' ≠ q' := by
    intro hpq'
    apply hpq
    exact congrArg Subtype.val hpq'
  have hcompare := hchain.1 (hselected hp') (hselected hq') hpq'
  rcases hcompare with hpqLe | hqpLe
  · rcases hpqLe with hpqEq | hpqLt
    · exact (hpq hpqEq).elim
    · exact Or.inl hpqLt
  · rcases hqpLe with hqpEq | hqpLt
    · exact (hpq hqpEq.symm).elim
    · exact Or.inr hqpLt

private theorem leftSelected_pair_sameStrictSide
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    (leftProfile : HMPTVerticalProfile x0 x1 x2 x3 leftPool)
    (rightProfile : HMPTVerticalProfile x1 x2 x3 x4 rightPool)
    {a b q : Point 2}
    (ha : a ∈ hmptChainPoints leftProfile.rightChain)
    (hb : b ∈ hmptChainPoints leftProfile.rightChain)
    (hq : q ∈ hmptChainPoints rightProfile.leftChain)
    (hab : a ≠ b) : SameStrictSide a b x3 q := by
  have haPool : a ∈ leftPool :=
    hmptChainPoints_subset leftProfile.rightChain ha
  have hbPool : b ∈ leftPool :=
    hmptChainPoints_subset leftProfile.rightChain hb
  have hqPool : q ∈ rightPool :=
    hmptChainPoints_subset rightProfile.leftChain hq
  have hcompare := strictVertical_comparable_of_selected
    leftProfile.verticalMaximum leftProfile.rightMaximum.1.1 ha hb hab
  rcases hcompare with habVertical | hbaVertical
  · exact Or.inl
      (h.leftPair_orientation_neg haPool hbPool hqPool habVertical)
  · have hsigns :=
      h.leftPair_orientation_neg hbPool haPool hqPool hbaVertical
    right
    constructor
    · have hanchor := hsigns.1
      rw [orientation_swap a b x3] at hanchor
      linarith
    · have hremote := hsigns.2
      rw [orientation_swap a b q] at hremote
      linarith

private theorem rightSelected_pair_sameStrictSide
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    (leftProfile : HMPTVerticalProfile x0 x1 x2 x3 leftPool)
    (rightProfile : HMPTVerticalProfile x1 x2 x3 x4 rightPool)
    {a b q : Point 2}
    (ha : a ∈ hmptChainPoints rightProfile.leftChain)
    (hb : b ∈ hmptChainPoints rightProfile.leftChain)
    (hq : q ∈ hmptChainPoints leftProfile.rightChain)
    (hab : a ≠ b) : SameStrictSide a b x1 q := by
  have haPool : a ∈ rightPool :=
    hmptChainPoints_subset rightProfile.leftChain ha
  have hbPool : b ∈ rightPool :=
    hmptChainPoints_subset rightProfile.leftChain hb
  have hqPool : q ∈ leftPool :=
    hmptChainPoints_subset leftProfile.rightChain hq
  have hcompare := strictVertical_comparable_of_selected
    rightProfile.verticalMaximum rightProfile.leftMaximum.1.1 ha hb hab
  rcases hcompare with habVertical | hbaVertical
  · exact Or.inr
      (h.rightPair_orientation_pos haPool hbPool hqPool habVertical)
  · have hsigns :=
      h.rightPair_orientation_pos hbPool haPool hqPool hbaVertical
    left
    constructor
    · have hanchor := hsigns.1
      rw [orientation_swap a b x1] at hanchor
      linarith
    · have hremote := hsigns.2
      rw [orientation_swap a b q] at hremote
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
  rcases ha with rfl | ha <;> rcases hb with rfl | hb <;>
    rcases hc with rfl | hc
  · simp
  · simp
  · simp
  · have hbAnchor : b ≠ a := fun hEq ↦ hanchor (hEq ▸ hb)
    have hcAnchor : c ≠ a := fun hEq ↦ hanchor (hEq ▸ hc)
    by_cases hbc : b = c
    · subst c
      simp [replacePoint, hbAnchor]
    · have hsides' := hsides hb hc hbc
      rcases hsides' with ⟨hAnchor, hReplacement⟩ |
        ⟨hAnchor, hReplacement⟩
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
      rcases hsides' with ⟨hAnchor, hReplacement⟩ |
        ⟨hAnchor, hReplacement⟩
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
      rcases hsides' with ⟨hAnchor, hReplacement⟩ |
        ⟨hAnchor, hReplacement⟩
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
    (hc : SameStrictSide a b common c)
    (hd : SameStrictSide a b common d) : SameStrictSide a b c d := by
  rcases hc with ⟨hCommon, hc⟩ | ⟨hCommon, hc⟩ <;>
    rcases hd with ⟨hCommon', hd⟩ | ⟨hCommon', hd⟩
  · exact Or.inl ⟨hc, hd⟩
  · linarith
  · linarith
  · exact Or.inr ⟨hc, hd⟩

private theorem leftSelected_anchor_not_mem
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    (leftProfile : HMPTVerticalProfile x0 x1 x2 x3 leftPool) :
    x3 ∉ hmptChainPoints leftProfile.rightChain := by
  intro hx3
  have hx3Pool : x3 ∈ leftPool :=
    hmptChainPoints_subset leftProfile.rightChain hx3
  have hregion := h.leftRegion hx3Pool
  change 0 < orientation x1 x2 x3 ∧ orientation x0 x1 x3 < 0 ∧
    orientation x2 x3 x3 < 0 at hregion
  simpa using hregion.2.2

private theorem rightSelected_anchor_not_mem
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    (rightProfile : HMPTVerticalProfile x1 x2 x3 x4 rightPool) :
    x1 ∉ hmptChainPoints rightProfile.leftChain := by
  intro hx1
  have hx1Pool : x1 ∈ rightPool :=
    hmptChainPoints_subset rightProfile.leftChain hx1
  have hregion := h.rightRegion hx1Pool
  change 0 < orientation x2 x3 x1 ∧ orientation x1 x2 x1 < 0 ∧
    orientation x3 x4 x1 < 0 at hregion
  simpa using hregion.2.1

private theorem leftSelected_three_rightSelected_one
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    (leftProfile : HMPTVerticalProfile x0 x1 x2 x3 leftPool)
    (rightProfile : HMPTVerticalProfile x1 x2 x3 x4 rightPool)
    {a b c q : Point 2}
    (ha : a ∈ hmptChainPoints leftProfile.rightChain)
    (hb : b ∈ hmptChainPoints leftProfile.rightChain)
    (hc : c ∈ hmptChainPoints leftProfile.rightChain)
    (hq : q ∈ hmptChainPoints rightProfile.leftChain)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    InConvexPosition {a, b, c, q} := by
  have hsub : ({a, b, c} : Finset (Point 2)) ⊆
      hmptChainPoints leftProfile.rightChain := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  have hanchorNot : x3 ∉ ({a, b, c} : Finset (Point 2)) :=
    fun hx3 ↦ leftSelected_anchor_not_mem h leftProfile (hsub hx3)
  have haPool : a ∈ leftPool :=
    hmptChainPoints_subset leftProfile.rightChain ha
  have hbPool : b ∈ leftPool :=
    hmptChainPoints_subset leftProfile.rightChain hb
  have hcPool : c ∈ leftPool :=
    hmptChainPoints_subset leftProfile.rightChain hc
  have hqPool : q ∈ rightPool :=
    hmptChainPoints_subset rightProfile.leftChain hq
  have hqNot : q ∉ ({a, b, c} : Finset (Point 2)) := by
    intro hqMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqMem
    rcases hqMem with hqa | hqb | hqc
    · subst q
      exact (Finset.disjoint_left.mp h.disjoint haPool hqPool).elim
    · subst q
      exact (Finset.disjoint_left.mp h.disjoint hbPool hqPool).elim
    · subst q
      exact (Finset.disjoint_left.mp h.disjoint hcPool hqPool).elim
  have hcell : SameOpenCellOfLineArrangement {a, b, c} x3 q := by
    apply sameOpenCellOfLineArrangement_of_pairwise_sameStrictSide hanchorNot
    intro u hu v hv huv
    exact leftSelected_pair_sameStrictSide h leftProfile rightProfile
      (hsub hu) (hsub hv) hq huv
  have hconv : InConvexPosition (insert q {a, b, c}) := by
    apply (inConvexPosition_replacePoint_iff hanchorNot hqNot
      (h.generalPosition.mono <| by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl
        all_goals simp [haPool, hbPool, hcPool]) hcell).mpr
    apply leftProfile.rightMaximum.1.2.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
    rcases hp with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ha
    · exact Or.inr hb
    · exact Or.inr hc
  convert hconv using 1
  ext p
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem rightSelected_three_leftSelected_one
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    (leftProfile : HMPTVerticalProfile x0 x1 x2 x3 leftPool)
    (rightProfile : HMPTVerticalProfile x1 x2 x3 x4 rightPool)
    {a b c q : Point 2}
    (ha : a ∈ hmptChainPoints rightProfile.leftChain)
    (hb : b ∈ hmptChainPoints rightProfile.leftChain)
    (hc : c ∈ hmptChainPoints rightProfile.leftChain)
    (hq : q ∈ hmptChainPoints leftProfile.rightChain)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    InConvexPosition {a, b, c, q} := by
  have hsub : ({a, b, c} : Finset (Point 2)) ⊆
      hmptChainPoints rightProfile.leftChain := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  have hanchorNot : x1 ∉ ({a, b, c} : Finset (Point 2)) :=
    fun hx1 ↦ rightSelected_anchor_not_mem h rightProfile (hsub hx1)
  have haPool : a ∈ rightPool :=
    hmptChainPoints_subset rightProfile.leftChain ha
  have hbPool : b ∈ rightPool :=
    hmptChainPoints_subset rightProfile.leftChain hb
  have hcPool : c ∈ rightPool :=
    hmptChainPoints_subset rightProfile.leftChain hc
  have hqPool : q ∈ leftPool :=
    hmptChainPoints_subset leftProfile.rightChain hq
  have hqNot : q ∉ ({a, b, c} : Finset (Point 2)) := by
    intro hqMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqMem
    rcases hqMem with hqa | hqb | hqc
    · subst q
      exact (Finset.disjoint_left.mp h.disjoint hqPool haPool).elim
    · subst q
      exact (Finset.disjoint_left.mp h.disjoint hqPool hbPool).elim
    · subst q
      exact (Finset.disjoint_left.mp h.disjoint hqPool hcPool).elim
  have hcell : SameOpenCellOfLineArrangement {a, b, c} x1 q := by
    apply sameOpenCellOfLineArrangement_of_pairwise_sameStrictSide hanchorNot
    intro u hu v hv huv
    exact rightSelected_pair_sameStrictSide h leftProfile rightProfile
      (hsub hu) (hsub hv) hq huv
  have hconv : InConvexPosition (insert q {a, b, c}) := by
    apply (inConvexPosition_replacePoint_iff hanchorNot hqNot
      (h.generalPosition.mono <| by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl
        all_goals simp [haPool, hbPool, hcPool]) hcell).mpr
    apply rightProfile.leftMaximum.1.2.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
    rcases hp with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ha
    · exact Or.inr hb
    · exact Or.inr hc
  convert hconv using 1
  ext p
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem selected_two_two
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    (leftProfile : HMPTVerticalProfile x0 x1 x2 x3 leftPool)
    (rightProfile : HMPTVerticalProfile x1 x2 x3 x4 rightPool)
    {a b c d : Point 2}
    (ha : a ∈ hmptChainPoints leftProfile.rightChain)
    (hb : b ∈ hmptChainPoints leftProfile.rightChain)
    (hc : c ∈ hmptChainPoints rightProfile.leftChain)
    (hd : d ∈ hmptChainPoints rightProfile.leftChain)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    InConvexPosition {a, b, c, d} := by
  have haPool : a ∈ leftPool :=
    hmptChainPoints_subset leftProfile.rightChain ha
  have hbPool : b ∈ leftPool :=
    hmptChainPoints_subset leftProfile.rightChain hb
  have hcPool : c ∈ rightPool :=
    hmptChainPoints_subset rightProfile.leftChain hc
  have hdPool : d ∈ rightPool :=
    hmptChainPoints_subset rightProfile.leftChain hd
  have hgp : InGeneralPosition ({a, b, c, d} : Finset (Point 2)) := by
    apply h.generalPosition.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals simp [haPool, hbPool, hcPool, hdPool]
  apply inConvexPosition_four_of_opposite_pair_supports
    a b c d hgp hab hac had hbc hbd hcd
  · exact sameStrictSide_of_common
      (leftSelected_pair_sameStrictSide h leftProfile rightProfile ha hb hc hab)
      (leftSelected_pair_sameStrictSide h leftProfile rightProfile ha hb hd hab)
  · exact sameStrictSide_of_common
      (rightSelected_pair_sameStrictSide h leftProfile rightProfile hc hd ha hcd)
      (rightSelected_pair_sameStrictSide h leftProfile rightProfile hc hd hb hcd)

set_option maxHeartbeats 1000000 in
/-- The right anchored chain in the left spike pool and the left anchored chain
in the adjacent right spike pool have a convex union. -/
theorem right_left_union_convex
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    (leftProfile : HMPTVerticalProfile x0 x1 x2 x3 leftPool)
    (rightProfile : HMPTVerticalProfile x1 x2 x3 x4 rightPool) :
    InConvexPosition
      (hmptChainPoints leftProfile.rightChain ∪
        hmptChainPoints rightProfile.leftChain) := by
  apply (inConvexPosition_iff_four_subsets
    (hmptChainPoints leftProfile.rightChain ∪
      hmptChainPoints rightProfile.leftChain)
    (h.generalPosition.mono <| by
      intro p hp
      simp only [Finset.mem_union] at hp
      rcases hp with hp | hp
      · have hpPool : p ∈ leftPool :=
          hmptChainPoints_subset leftProfile.rightChain hp
        simp [hpPool]
      · have hpPool : p ∈ rightPool :=
          hmptChainPoints_subset rightProfile.leftChain hp
        simp [hpPool])).mpr
  intro t ht hcard
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ :=
    Finset.card_eq_four.mp hcard
  have ha := ht (by simp : a ∈ ({a, b, c, d} : Finset (Point 2)))
  have hb := ht (by simp : b ∈ ({a, b, c, d} : Finset (Point 2)))
  have hc := ht (by simp : c ∈ ({a, b, c, d} : Finset (Point 2)))
  have hd := ht (by simp : d ∈ ({a, b, c, d} : Finset (Point 2)))
  simp only [Finset.mem_union] at ha hb hc hd
  have hleft : ∀ ⦃w x y z : Point 2⦄,
      w ∈ hmptChainPoints leftProfile.rightChain →
      x ∈ hmptChainPoints leftProfile.rightChain →
      y ∈ hmptChainPoints leftProfile.rightChain →
      z ∈ hmptChainPoints leftProfile.rightChain →
      InConvexPosition {w, x, y, z} := by
    intro w x y z hw hx hy hz
    apply leftProfile.rightMaximum.1.2.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
    aesop
  have hright : ∀ ⦃w x y z : Point 2⦄,
      w ∈ hmptChainPoints rightProfile.leftChain →
      x ∈ hmptChainPoints rightProfile.leftChain →
      y ∈ hmptChainPoints rightProfile.leftChain →
      z ∈ hmptChainPoints rightProfile.leftChain →
      InConvexPosition {w, x, y, z} := by
    intro w x y z hw hx hy hz
    apply rightProfile.leftMaximum.1.2.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
    aesop
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hc with hc | hc <;> rcases hd with hd | hd
  · exact hleft ha hb hc hd
  · exact leftSelected_three_rightSelected_one h leftProfile rightProfile
      ha hb hc hd hab hac hbc
  · convert leftSelected_three_rightSelected_one h leftProfile rightProfile
      ha hb hd hc hab had hbd using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · exact selected_two_two h leftProfile rightProfile
      ha hb hc hd hab hac had hbc hbd hcd
  · convert leftSelected_three_rightSelected_one h leftProfile rightProfile
      ha hc hd hb hac had hcd using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert selected_two_two h leftProfile rightProfile
      ha hc hb hd hac hab had hbc.symm hcd hbd using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert selected_two_two h leftProfile rightProfile
      ha hd hb hc had hab hac hbd.symm hcd.symm hbc using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert rightSelected_three_leftSelected_one h leftProfile rightProfile
      hb hc hd ha hbc hbd hcd using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert leftSelected_three_rightSelected_one h leftProfile rightProfile
      hb hc hd ha hbc hbd hcd using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert selected_two_two h leftProfile rightProfile
      hb hc ha hd hbc hab.symm hbd hac.symm hcd had using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert selected_two_two h leftProfile rightProfile
      hb hd ha hc hbd hab.symm hbc had.symm hcd.symm hac using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert rightSelected_three_leftSelected_one h leftProfile rightProfile
      ha hc hd hb hac had hcd using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert selected_two_two h leftProfile rightProfile
      hc hd ha hb hcd hac.symm hbc.symm had.symm hbd.symm hab using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · convert rightSelected_three_leftSelected_one h leftProfile rightProfile
      ha hb hd hc hab had hbd using 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · exact rightSelected_three_leftSelected_one h leftProfile rightProfile
      ha hb hc hd hab hac hbc
  · exact hright ha hb hc hd

end HMPTAdjacentSpikeGeometry

end

end ErdosSzekeres

end
