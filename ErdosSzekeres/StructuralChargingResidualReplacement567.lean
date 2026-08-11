module

public import ErdosSzekeres.StructuralChargingResidualProbeReuse567

@[expose] public section

/-!
# Light residual replacements at state 567

This file records the exact finite-set replacement carried by a light
carrier-touching residual probe.  It does not assert that such a replacement
is contradictory.
-/

namespace ErdosSzekeres

/-- A carrier-touching probe witness with at most two carrier vertices replaces
exactly one or two vertices of the complementary nonstrong residual six by the
same number of carrier vertices. -/
theorem IsCarrierTouchingProbeWitness567.light_replacement_data
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second block third : Finset (Fin n)} {a b : Fin n}
    (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
      a b block third)
    (hresidualCard : (ambient \ (first ∪ second)).card = 10)
    (hlight : (third ∩ (first ∪ second)).card ≤ 2) :
    let residual := ambient \ (first ∪ second)
    let badSix := residual \ block
    let residualCore := third ∩ residual
    let addedCarrier := third ∩ (first ∪ second)
    let removedResidual := badSix \ residualCore
    badSix.card = 6 ∧
      residualCore ⊆ badSix ∧
      Disjoint residualCore addedCarrier ∧
      third = residualCore ∪ addedCarrier ∧
      Disjoint residualCore removedResidual ∧
      badSix = residualCore ∪ removedResidual ∧
      addedCarrier.card = removedResidual.card ∧
      ¬IsStrongPolygonSet χ badSix ∧
      IsStrongPolygonSet χ residualCore ∧
      ((addedCarrier.card = 1 ∧ residualCore.card = 5 ∧
          removedResidual.card = 1) ∨
        (addedCarrier.card = 2 ∧ residualCore.card = 4 ∧
          removedResidual.card = 2)) := by
  classical
  dsimp only
  let residual := ambient \ (first ∪ second)
  let badSix := residual \ block
  let residualCore := third ∩ residual
  let addedCarrier := third ∩ (first ∪ second)
  let removedResidual := badSix \ residualCore
  have hbad := hincident.1
  change block ∈ (residual.powersetCard 4).filter
    (fun candidate ↦ ¬IsStrongPolygonSet χ (residual \ candidate)) at hbad
  have hbadData := Finset.mem_filter.mp hbad
  have hblockData := Finset.mem_powersetCard.mp hbadData.1
  have hbadNotStrong : ¬IsStrongPolygonSet χ badSix := by
    simpa [badSix] using hbadData.2
  have hbadCard : badSix.card = 6 := by
    simp only [badSix]
    rw [Finset.card_sdiff_of_subset hblockData.1, hresidualCard,
      hblockData.2]
  have hthirdAmbient : third ⊆ ambient :=
    hincident.2.1.trans Finset.sdiff_subset
  have hthirdBlock : Disjoint third block := by
    apply Finset.disjoint_left.mpr
    intro x hxThird hxBlock
    have hxAvoid := Finset.mem_sdiff.mp (hincident.2.1 hxThird)
    exact hxAvoid.2 (by simp [hxBlock])
  have hcoreBad : residualCore ⊆ badSix := by
    intro x hxCore
    have hxCoreData := Finset.mem_inter.mp hxCore
    apply Finset.mem_sdiff.mpr
    exact ⟨hxCoreData.2,
      fun hxBlock ↦ Finset.disjoint_left.mp hthirdBlock hxCoreData.1 hxBlock⟩
  have hcoreAddedDisjoint : Disjoint residualCore addedCarrier := by
    apply Finset.disjoint_left.mpr
    intro x hxCore hxAdded
    have hxResidual := Finset.mem_inter.mp hxCore
    have hxCarrier := Finset.mem_inter.mp hxAdded
    exact (Finset.mem_sdiff.mp hxResidual.2).2 hxCarrier.2
  have hthirdUnion : third = residualCore ∪ addedCarrier := by
    ext x
    constructor
    · intro hxThird
      by_cases hxCarrier : x ∈ first ∪ second
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hxThird, hxCarrier⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr
            ⟨hxThird, Finset.mem_sdiff.mpr
              ⟨hthirdAmbient hxThird, hxCarrier⟩⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxCore | hxAdded
      · exact (Finset.mem_inter.mp hxCore).1
      · exact (Finset.mem_inter.mp hxAdded).1
  have hcoreRemovedDisjoint : Disjoint residualCore removedResidual := by
    exact Finset.disjoint_sdiff
  have hbadUnion : badSix = residualCore ∪ removedResidual := by
    ext x
    constructor
    · intro hxBad
      by_cases hxCore : x ∈ residualCore
      · exact Finset.mem_union_left _ hxCore
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hxBad, hxCore⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxCore | hxRemoved
      · exact hcoreBad hxCore
      · exact (Finset.mem_sdiff.mp hxRemoved).1
  have hsplit : addedCarrier.card + residualCore.card = 6 := by
    simpa [addedCarrier, residualCore, residual] using
      hincident.carrier_add_residual_card
  have hbadSplit : residualCore.card + removedResidual.card = 6 := by
    rw [← Finset.card_union_of_disjoint hcoreRemovedDisjoint,
      ← hbadUnion, hbadCard]
  have hcardEq : addedCarrier.card = removedResidual.card := by omega
  have haddedPos : 1 ≤ addedCarrier.card := by
    simpa [addedCarrier] using hincident.one_le_carrier_card
  have haddedLight : addedCarrier.card ≤ 2 := by
    simpa [addedCarrier] using hlight
  have hcoreStrong : IsStrongPolygonSet χ residualCore := by
    exact FinsetPolygon.IsStrongPolygonSet.mono hincident.2.2.2.1
      Finset.inter_subset_left
  have hcases : addedCarrier.card = 1 ∨ addedCarrier.card = 2 := by
    omega
  refine ⟨hbadCard, hcoreBad, hcoreAddedDisjoint, hthirdUnion,
    hcoreRemovedDisjoint, hbadUnion, hcardEq, hbadNotStrong, hcoreStrong, ?_⟩
  rcases hcases with hone | htwo
  · have hcoreFive : residualCore.card = 5 := by omega
    have hremovedOne : removedResidual.card = 1 := by omega
    exact Or.inl ⟨by simpa [addedCarrier] using hone,
      by simpa [residualCore, residual] using hcoreFive,
      by simpa [removedResidual, badSix, residualCore, residual] using
        hremovedOne⟩
  · have hcoreFour : residualCore.card = 4 := by omega
    have hremovedTwo : removedResidual.card = 2 := by omega
    exact Or.inr ⟨by simpa [addedCarrier] using htwo,
      by simpa [residualCore, residual] using hcoreFour,
      by simpa [removedResidual, badSix, residualCore, residual] using
        hremovedTwo⟩

/-- The vertices displaced by a light carrier-touching witness expose a
same-middle color failure: a one-vertex extension failure in the `1+5` case,
or a two-vertex extension failure in the `2+4` case. -/
theorem IsCarrierTouchingProbeWitness567.light_replacement_color_failure
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second block third : Finset (Fin n)} {a b : Fin n}
    (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
      a b block third)
    (hresidualCard : (ambient \ (first ∪ second)).card = 10)
    (hlight : (third ∩ (first ∪ second)).card ≤ 2) :
    let residual := ambient \ (first ∪ second)
    let badSix := residual \ block
    let residualCore := third ∩ residual
    let removedResidual := badSix \ residualCore
    (∃ q, removedResidual = {q} ∧
        badSix = insert q residualCore ∧
        HasMiddleExtensionFailure χ residualCore q) ∨
      (∃ q r, q ≠ r ∧ removedResidual = {q, r} ∧
        badSix = insert q (insert r residualCore) ∧
        HasMiddlePairExtensionFailure χ residualCore q r) := by
  classical
  dsimp only
  let residual := ambient \ (first ∪ second)
  let badSix := residual \ block
  let residualCore := third ∩ residual
  let addedCarrier := third ∩ (first ∪ second)
  let removedResidual := badSix \ residualCore
  have hdata := hincident.light_replacement_data hresidualCard hlight
  change badSix.card = 6 ∧
      residualCore ⊆ badSix ∧
      Disjoint residualCore addedCarrier ∧
      third = residualCore ∪ addedCarrier ∧
      Disjoint residualCore removedResidual ∧
      badSix = residualCore ∪ removedResidual ∧
      addedCarrier.card = removedResidual.card ∧
      ¬IsStrongPolygonSet χ badSix ∧
      IsStrongPolygonSet χ residualCore ∧
      ((addedCarrier.card = 1 ∧ residualCore.card = 5 ∧
          removedResidual.card = 1) ∨
        (addedCarrier.card = 2 ∧ residualCore.card = 4 ∧
          removedResidual.card = 2)) at hdata
  rcases hdata with ⟨hbadCard, hcoreBad, -, -, hcoreRemoved,
    hbadUnion, -, hbadNotStrong, hcoreStrong, hcases⟩
  have hnoStrongBad : ¬ContainsStrongPolygonSet χ badSix 6 := by
    rintro ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩
    have hpolygonEq : polygon = badSix :=
      Finset.eq_of_subset_of_card_le hpolygonSub (by omega)
    apply hbadNotStrong
    simpa [hpolygonEq] using hpolygonStrong
  rcases hcases with hone | htwo
  · obtain ⟨q, hremovedEq⟩ := Finset.card_eq_one.mp hone.2.2
    have hqRemoved : q ∈ removedResidual := by simp [hremovedEq]
    have hqBad : q ∈ badSix :=
      (Finset.mem_sdiff.mp hqRemoved).1
    have hqCore : q ∉ residualCore := fun hqCore ↦
      Finset.disjoint_left.mp hcoreRemoved hqCore hqRemoved
    have hbadInsert : badSix = insert q residualCore := by
      simpa [hremovedEq, Finset.union_comm] using hbadUnion
    have hfailure : HasMiddleExtensionFailure χ residualCore q := by
      apply middle_extension_failure_of_no_strong_succ
        hcoreBad hone.2.1
        (FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp
          hcoreStrong)
        hqBad hqCore
      simpa using hnoStrongBad
    exact Or.inl ⟨q,
      by simpa [removedResidual, badSix, residualCore, residual] using
        hremovedEq,
      by simpa [badSix, residualCore, residual] using hbadInsert,
      by simpa [residualCore, residual] using hfailure⟩
  · obtain ⟨q, r, hqr, hremovedEq⟩ :=
      Finset.card_eq_two.mp htwo.2.2
    have hqRemoved : q ∈ removedResidual := by simp [hremovedEq]
    have hrRemoved : r ∈ removedResidual := by simp [hremovedEq]
    have hqBad : q ∈ badSix := (Finset.mem_sdiff.mp hqRemoved).1
    have hrBad : r ∈ badSix := (Finset.mem_sdiff.mp hrRemoved).1
    have hqCore : q ∉ residualCore := fun hqCore ↦
      Finset.disjoint_left.mp hcoreRemoved hqCore hqRemoved
    have hrCore : r ∉ residualCore := fun hrCore ↦
      Finset.disjoint_left.mp hcoreRemoved hrCore hrRemoved
    have hbadInsert : badSix = insert q (insert r residualCore) := by
      simpa [hremovedEq, Finset.union_comm, Finset.union_left_comm,
        Finset.union_assoc] using hbadUnion
    have hfailure : HasMiddlePairExtensionFailure χ residualCore q r := by
      apply middle_pair_extension_failure_of_no_strong_add_two
        hcoreBad htwo.2.1
        (FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp
          hcoreStrong)
        hqBad hrBad hqCore hrCore hqr
      simpa using hnoStrongBad
    exact Or.inr ⟨q, r, hqr,
      by simpa [removedResidual, badSix, residualCore, residual] using
        hremovedEq,
      by simpa [badSix, residualCore, residual] using hbadInsert,
      by simpa [residualCore, residual] using hfailure⟩

end ErdosSzekeres

end
