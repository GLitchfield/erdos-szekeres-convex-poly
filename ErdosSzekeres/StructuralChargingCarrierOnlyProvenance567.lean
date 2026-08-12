module

public import ErdosSzekeres.StructuralChargingCarrierOnlyRectangles567

@[expose] public section

/-!
# Canonical provenance for carrier-contained strong six-sets at state 567

A strong six-set contained in two disjoint six-point carriers is either one
whole carrier or a mixed set.  In the mixed case, cardinality supplies one
omitted anchor from each carrier.  Any bad residual four-block then supplies
the canonical probe provenance for that mixed set.
-/

namespace ErdosSzekeres

/-- Under canonical carrier and bad-probe provenance, every carrier-contained
strong six-set is one original carrier or belongs to the canonical finite
family of carrier-only probe witnesses. -/
theorem carrierContainedStrongSix_classification_of_canonical567
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second block third : Finset (Fin n)}
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second)
    (hfirstSub : first ⊆ ambient) (hsecondSub : second ⊆ ambient)
    (hblock : block ∈ BadResidualFourBlocks567 χ
      (ambient \ (first ∪ second)))
    (hthirdSub : third ⊆ first ∪ second)
    (hthirdCard : third.card = 6)
    (hthirdStrong : IsStrongPolygonSet χ third) :
    third = first ∨ third = second ∨
      third ∈ CarrierOnlyProbeWitnessSets567 χ ambient first second := by
  classical
  by_cases hthirdFirst : Disjoint third first
  · have hthirdSecond : third ⊆ second := by
      intro x hxThird
      rcases Finset.mem_union.mp (hthirdSub hxThird) with hxFirst | hxSecond
      · exact (Finset.disjoint_left.mp hthirdFirst hxThird hxFirst).elim
      · exact hxSecond
    have heq : third = second := by
      apply Finset.eq_of_subset_of_card_le hthirdSecond
      rw [hmutual.2.2.1, hthirdCard]
    exact Or.inr (Or.inl heq)
  by_cases hthirdSecond : Disjoint third second
  · have hthirdFirstSub : third ⊆ first := by
      intro x hxThird
      rcases Finset.mem_union.mp (hthirdSub hxThird) with hxFirst | hxSecond
      · exact hxFirst
      · exact (Finset.disjoint_left.mp hthirdSecond hxThird hxSecond).elim
    have heq : third = first := by
      apply Finset.eq_of_subset_of_card_le hthirdFirstSub
      rw [hmutual.2.1, hthirdCard]
    exact Or.inl heq
  have hfirstNotSubset : ¬first ⊆ third := by
    intro hfirstThird
    have heq : first = third := by
      apply Finset.eq_of_subset_of_card_le hfirstThird
      rw [hthirdCard, hmutual.2.1]
    exact hthirdSecond (heq ▸ hmutual.1)
  have hsecondNotSubset : ¬second ⊆ third := by
    intro hsecondThird
    have heq : second = third := by
      apply Finset.eq_of_subset_of_card_le hsecondThird
      rw [hthirdCard, hmutual.2.2.1]
    exact hthirdFirst (heq ▸ hmutual.1.symm)
  obtain ⟨a, haFirst, haNotThird⟩ := Finset.not_subset.mp hfirstNotSubset
  obtain ⟨b, hbSecond, hbNotThird⟩ := Finset.not_subset.mp hsecondNotSubset
  change block ∈ ((ambient \ (first ∪ second)).powersetCard 4).filter
    (fun candidate ↦
      ¬IsStrongPolygonSet χ ((ambient \ (first ∪ second)) \ candidate))
    at hblock
  have hblockSub : block ⊆ ambient \ (first ∪ second) :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hblock).1).1
  have hthirdAmbient : third ⊆ ambient :=
    hthirdSub.trans (Finset.union_subset hfirstSub hsecondSub)
  have hthirdAvoid : third ⊆ ambient \ insert a (insert b block) := by
    intro x hxThird
    have hxNeA : x ≠ a := by
      intro hxa
      exact haNotThird (hxa ▸ hxThird)
    have hxNeB : x ≠ b := by
      intro hxb
      exact hbNotThird (hxb ▸ hxThird)
    have hxNotBlock : x ∉ block := by
      intro hxBlock
      have hxResidual := Finset.mem_sdiff.mp (hblockSub hxBlock)
      exact hxResidual.2 (hthirdSub hxThird)
    exact Finset.mem_sdiff.mpr
      ⟨hthirdAmbient hxThird, by simp [hxNeA, hxNeB, hxNotBlock]⟩
  have htwoCarrier :
      HasPairEscapeOccupancy first second third .twoCarrier := by
    change ¬Disjoint third first ∧ ¬Disjoint third second
    exact ⟨hthirdFirst, hthirdSecond⟩
  have hzero :
      (third ∩ (ambient \ (first ∪ second))).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    have hxData := Finset.mem_inter.mp hx
    exact (Finset.mem_sdiff.mp hxData.2).2 (hthirdSub hxData.1)
  apply Or.inr (Or.inr ?_)
  change third ∈ (ambient.powersetCard 6).filter
    (IsCarrierOnlyProbeWitnessSet567 χ ambient first second)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powersetCard.mpr ⟨hthirdAmbient, hthirdCard⟩,
      a, haFirst, b, hbSecond, block,
      ⟨hblock, hthirdAvoid, hthirdCard, hthirdStrong,
        Or.inr htwoCarrier⟩,
      hzero⟩

end ErdosSzekeres

end
