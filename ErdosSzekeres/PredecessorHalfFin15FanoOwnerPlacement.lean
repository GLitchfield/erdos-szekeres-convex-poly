module

public import ErdosSzekeres.PredecessorHalfFin15ExteriorSystem

@[expose] public section

/-!
# Common-owner placement in the seven-block Fin15 branch

An eight-element exterior whose anchors have seven distinct values has only
one unit of collision excess.  Consequently, the five-fold owner supplied by
the complete exterior system occurs in at least four distinct anchor values.
-/

namespace ErdosSzekeres

/-- Passing to a subfamily can lose at most the number of removed domain
elements from the cardinality of a function image. -/
private theorem card_image_add_card_le_of_subset
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (small large : Finset α) (f : α → β) (hsmall : small ⊆ large) :
    (large.image f).card + small.card ≤
      (small.image f).card + large.card := by
  have hlarge : small ∪ (large \ small) = large :=
    Finset.union_sdiff_of_subset hsmall
  have himage :
      large.image f = small.image f ∪ (large \ small).image f := by
    rw [← Finset.image_union, hlarge]
  have himageLe :
      (large.image f).card ≤
        (small.image f).card + ((large \ small).image f).card := by
    rw [himage]
    exact Finset.card_union_le _ _
  have hdiffImageLe :
      ((large \ small).image f).card ≤ (large \ small).card :=
    Finset.card_image_le
  have hdiffCard : (large \ small).card = large.card - small.card :=
    Finset.card_sdiff_of_subset hsmall
  have hsmallCard : small.card ≤ large.card := Finset.card_le_card hsmall
  omega

/-- The image indexed by `Fin 8` is exactly the image over the exterior
subtype enumerated by the supplied equivalence. -/
private theorem indexedAnchor_image_eq_exterior_image
    {support : Finset (Fin 15)} {anchor : Fin 15 → Finset (Fin 15)}
    (index : Fin 8 ≃ {vertex // vertex ∈ Finset.univ \ support}) :
    (Finset.univ.image fun i : Fin 8 ↦ anchor (index i).1) =
      (Finset.univ \ support).image anchor := by
  ext block
  constructor
  · intro hblock
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hblock
    exact Finset.mem_image.mpr ⟨(index i).1, (index i).2, rfl⟩
  · intro hblock
    obtain ⟨vertex, hvertex, rfl⟩ := Finset.mem_image.mp hblock
    let indexedVertex : {vertex // vertex ∈ Finset.univ \ support} :=
      ⟨vertex, hvertex⟩
    refine Finset.mem_image.mpr
      ⟨index.symm indexedVertex, Finset.mem_univ _, ?_⟩
    simp [indexedVertex]

/-- In the seven-block branch, a five-fold support owner occurs in at least
four distinct anchor values, from which three pairwise-distinct owner anchors
can be selected. -/
theorem fin15ExteriorSystem_fano_commonOwner_distinctAnchors
    (chi : TripleColoring 15)
    {support : Finset (Fin 15)}
    {anchor : Fin 15 → Finset (Fin 15)}
    (hsystem : Fin15ExteriorSystem chi support anchor)
    (index : Fin 8 ≃ {vertex // vertex ∈ Finset.univ \ support})
    (hseven :
      (Finset.univ.image fun i : Fin 8 ↦ anchor (index i).1).card = 7) :
    ∃ owner ∈ support,
      5 ≤ ((Finset.univ \ support).filter fun vertex ↦
        owner ∈ anchor vertex).card ∧
      4 ≤ (((Finset.univ \ support).filter fun vertex ↦
        owner ∈ anchor vertex).image anchor).card ∧
      ∃ q ∈ Finset.univ \ support,
        ∃ r ∈ Finset.univ \ support,
          ∃ s ∈ Finset.univ \ support,
            q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
            owner ∈ anchor q ∧ owner ∈ anchor r ∧ owner ∈ anchor s ∧
            anchor q ≠ anchor r ∧ anchor q ≠ anchor s ∧
            anchor r ≠ anchor s := by
  classical
  let outside : Finset (Fin 15) := Finset.univ \ support
  have houtsideCard : outside.card = 8 := by
    simpa [outside] using hsystem.2.2.1
  have hanchorSub : ∀ vertex ∈ outside, anchor vertex ⊆ support := by
    intro vertex hvertex
    exact (hsystem.2.2.2 vertex (by simpa [outside] using hvertex)).1
  have hanchorCard : ∀ vertex ∈ outside, (anchor vertex).card = 4 := by
    intro vertex hvertex
    exact (hsystem.2.2.2 vertex (by simpa [outside] using hvertex)).2.1
  obtain ⟨owner, howner, hownerDegree⟩ :=
    exists_fiveFoldOwner_of_seven_eight_fourAnchors
      support outside anchor hsystem.2.1 houtsideCard hanchorSub hanchorCard
  let fiber : Finset (Fin 15) :=
    outside.filter fun vertex ↦ owner ∈ anchor vertex
  have hfiberSub : fiber ⊆ outside := Finset.filter_subset _ _
  have hfiberCard : 5 ≤ fiber.card := by
    simpa [fiber] using hownerDegree
  have houtsideImageCard : (outside.image anchor).card = 7 := by
    rw [← indexedAnchor_image_eq_exterior_image index]
    exact hseven
  have himageBound :=
    card_image_add_card_le_of_subset fiber outside anchor hfiberSub
  have hfiberImageCard : 4 ≤ (fiber.image anchor).card := by
    omega
  have hthreeImage : 2 < (fiber.image anchor).card := by omega
  obtain ⟨first, hfirst, second, hsecond, third, hthird,
      hfirstSecond, hfirstThird, hsecondThird⟩ :=
    Finset.two_lt_card.mp hthreeImage
  obtain ⟨q, hqFiber, hqAnchor⟩ := Finset.mem_image.mp hfirst
  obtain ⟨r, hrFiber, hrAnchor⟩ := Finset.mem_image.mp hsecond
  obtain ⟨s, hsFiber, hsAnchor⟩ := Finset.mem_image.mp hthird
  have hqData := Finset.mem_filter.mp hqFiber
  have hrData := Finset.mem_filter.mp hrFiber
  have hsData := Finset.mem_filter.mp hsFiber
  have hqrAnchor : anchor q ≠ anchor r := by
    intro heq
    apply hfirstSecond
    exact hqAnchor.symm.trans (heq.trans hrAnchor)
  have hqsAnchor : anchor q ≠ anchor s := by
    intro heq
    apply hfirstThird
    exact hqAnchor.symm.trans (heq.trans hsAnchor)
  have hrsAnchor : anchor r ≠ anchor s := by
    intro heq
    apply hsecondThird
    exact hrAnchor.symm.trans (heq.trans hsAnchor)
  have hqr : q ≠ r := fun heq ↦ hqrAnchor (congrArg anchor heq)
  have hqs : q ≠ s := fun heq ↦ hqsAnchor (congrArg anchor heq)
  have hrs : r ≠ s := fun heq ↦ hrsAnchor (congrArg anchor heq)
  refine ⟨owner, howner, ?_, ?_, q, ?_, r, ?_, s, ?_,
    hqr, hqs, hrs, hqData.2, hrData.2, hsData.2,
    hqrAnchor, hqsAnchor, hrsAnchor⟩
  · simpa [outside, fiber] using hfiberCard
  · simpa [outside, fiber] using hfiberImageCard
  · simpa [outside] using hqData.1
  · simpa [outside] using hrData.1
  · simpa [outside] using hsData.1

end ErdosSzekeres

end
