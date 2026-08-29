module

public import ErdosSzekeres.PredecessorHalfFin15BlockerDesign

@[expose] public section

/-!
# The complete exterior-anchor system at fifteen points

This file packages all eight exterior anchors of an exact seven-versus-eight
maximum-support obstruction.  After indexing the exterior by `Fin 8`, the
seven-point blocker classification gives either its global Fano/multiplicity
alternative together with a repeated blocker, or a distinct pair of blockers
which differ by one point in each direction.
-/

namespace ErdosSzekeres

/-- The complete eight-anchor data attached to an exact Fin15 maximum-support
obstruction. -/
def Fin15ExteriorSystem
    (chi : TripleColoring 15) (support : Finset (Fin 15))
    (anchor : Fin 15 → Finset (Fin 15)) : Prop :=
  IsMaximumPredecessorFreeSupport chi 6 support ∧
    support.card = 7 ∧
    (Finset.univ \ support).card = 8 ∧
    ∀ vertex ∈ Finset.univ \ support,
      anchor vertex ⊆ support ∧
        (anchor vertex).card = 4 ∧
        IsStrongPolygonSet chi (insert vertex (anchor vertex))

/-- The global conclusion of the seven-point blocker classification after all
eight exterior vertices have been indexed. -/
def Fin15ExteriorFanoOrMultiplicity
    (support : Finset (Fin 15)) (anchor : Fin 15 → Finset (Fin 15))
    (index : Fin 8 ≃ {vertex // vertex ∈ Finset.univ \ support}) : Prop :=
  let indexedAnchor : Fin 8 → Finset (Fin 15) := fun i ↦ anchor (index i).1
  let blocks := Finset.univ.image indexedAnchor
  (blocks.card = 7 ∧
      ∀ pair : Finset (Fin 15), pair ⊆ support → pair.card = 2 →
        ∃! block : Finset (Fin 15), block ∈ blocks ∧ pair ⊆ support \ block) ∨
    (blocks.card ≤ 6 ∧
      ((∃ block ∈ blocks,
          3 ≤ (Finset.univ.filter fun i : Fin 8 ↦ indexedAnchor i = block).card) ∨
        ∃ block₁ ∈ blocks, ∃ block₂ ∈ blocks, block₁ ≠ block₂ ∧
          2 ≤ (Finset.univ.filter fun i : Fin 8 ↦ indexedAnchor i = block₁).card ∧
          2 ≤ (Finset.univ.filter fun i : Fin 8 ↦ indexedAnchor i = block₂).card))

/-- A complete eight-anchor system has either a repeated blocker retaining the
global Fano/multiplicity classification, or a distinct one-for-one exchange.
This is the exact two-branch package consumed by the raw contradiction files. -/
theorem fin15ExteriorSystem_raw_branch_package
    (chi : TripleColoring 15)
    {support : Finset (Fin 15)}
    {anchor : Fin 15 → Finset (Fin 15)}
    (hsystem : Fin15ExteriorSystem chi support anchor) :
    (∃ index : Fin 8 ≃ {vertex // vertex ∈ Finset.univ \ support},
      Fin15ExteriorFanoOrMultiplicity support anchor index ∧
        (∀ u ∈ Finset.univ \ support, ∀ v ∈ Finset.univ \ support,
          anchor u ≠ anchor v → (anchor u ∩ anchor v).card ≤ 2) ∧
        ∃ i j : Fin 8, i ≠ j ∧ anchor (index i).1 = anchor (index j).1) ∨
      ∃ q ∈ Finset.univ \ support, ∃ r ∈ Finset.univ \ support,
        q ≠ r ∧
          (anchor q ∩ anchor r).card = 3 ∧
          (anchor q \ anchor r).card = 1 ∧
          (anchor r \ anchor q).card = 1 := by
  classical
  let outside : Finset (Fin 15) := Finset.univ \ support
  let index : Fin 8 ≃ {vertex // vertex ∈ outside} :=
    (outside.equivFinOfCardEq hsystem.2.2.1).symm
  let indexedAnchor : Fin 8 → Finset (Fin 15) := fun i ↦ anchor (index i).1
  let blocks : Finset (Finset (Fin 15)) := Finset.univ.image indexedAnchor
  have hanchorSub : ∀ i, indexedAnchor i ⊆ support := by
    intro i
    exact (hsystem.2.2.2 (index i).1 (by simpa [outside] using (index i).2)).1
  have hanchorCard : ∀ i, (indexedAnchor i).card = 4 := by
    intro i
    exact (hsystem.2.2.2 (index i).1 (by simpa [outside] using (index i).2)).2.1
  by_cases hexchange : ∃ i j : Fin 8,
      indexedAnchor i ≠ indexedAnchor j ∧
        3 ≤ (indexedAnchor i ∩ indexedAnchor j).card
  · obtain ⟨i, j, hanchorsNe, hinter⟩ := hexchange
    have hij : i ≠ j := fun hij ↦ hanchorsNe (congrArg indexedAnchor hij)
    have hverticesNe : (index i).1 ≠ (index j).1 := by
      intro hvertices
      apply hij
      apply index.injective
      exact Subtype.ext hvertices
    have hnormal := four_blocks_three_inter_normalForm
      (indexedAnchor i) (indexedAnchor j) (hanchorCard i) (hanchorCard j) hinter
    rcases hnormal with hanchorsEq | hnormal
    · exact (hanchorsNe hanchorsEq).elim
    · apply Or.inr
      exact ⟨(index i).1, by simpa [outside] using (index i).2,
        (index j).1, by simpa [outside] using (index j).2, hverticesNe,
        hnormal.1, hnormal.2.1, hnormal.2.2⟩
  · have hsmallInter : ∀ i j, indexedAnchor i ≠ indexedAnchor j →
        (indexedAnchor i ∩ indexedAnchor j).card ≤ 2 := by
      intro i j hanchorsNe
      by_contra hlarge
      apply hexchange
      exact ⟨i, j, hanchorsNe, by omega⟩
    have hclassification := eight_fourBlock_family_fano_classification
      support indexedAnchor hsystem.2.1 hanchorSub hanchorCard hsmallInter
    dsimp only at hclassification
    have hsmallGlobal : ∀ u ∈ Finset.univ \ support,
        ∀ v ∈ Finset.univ \ support,
          anchor u ≠ anchor v → (anchor u ∩ anchor v).card ≤ 2 := by
      intro u hu v hv huv
      let u' : {vertex // vertex ∈ outside} := ⟨u, by simpa [outside] using hu⟩
      let v' : {vertex // vertex ∈ outside} := ⟨v, by simpa [outside] using hv⟩
      have hindexed := hsmallInter (index.symm u') (index.symm v') (by
        simpa [indexedAnchor, u', v'] using huv)
      simpa [indexedAnchor, u', v'] using hindexed
    have hglobal : Fin15ExteriorFanoOrMultiplicity support anchor
        index := by
      unfold Fin15ExteriorFanoOrMultiplicity
      dsimp only
      by_cases hseven : (Finset.univ.image fun i : Fin 8 ↦ anchor (index i).1).card = 7
      · apply Or.inl
        refine ⟨hseven, ?_⟩
        simpa [indexedAnchor] using hclassification.2.1 (by
          simpa [indexedAnchor] using hseven)
      · have hsix : (Finset.univ.image fun i : Fin 8 ↦ anchor (index i).1).card ≤ 6 := by
          have hblocksLe : blocks.card ≤ 7 := by
            simpa [blocks] using hclassification.1
          have hnotSeven : blocks.card ≠ 7 := by
            simpa [blocks, indexedAnchor] using hseven
          change blocks.card ≤ 6
          omega
        apply Or.inr
        refine ⟨hsix, ?_⟩
        simpa [indexedAnchor] using hclassification.2.2 (by
          simpa [indexedAnchor] using hsix)
    have himageLt : (Finset.univ.image indexedAnchor).card <
        (Finset.univ : Finset (Fin 8)).card := by
      have hblocksLe : blocks.card ≤ 7 := by
        simpa [blocks] using hclassification.1
      change blocks.card < 8
      omega
    obtain ⟨i, _hi, j, _hj, hij, hanchorsEq⟩ :=
      Finset.exists_ne_map_eq_of_card_image_lt himageLt
    apply Or.inl
    refine ⟨index, hglobal, hsmallGlobal, i, j, hij, ?_⟩
    exact hanchorsEq

end ErdosSzekeres

end
