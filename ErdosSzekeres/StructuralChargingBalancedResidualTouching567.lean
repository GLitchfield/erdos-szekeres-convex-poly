module

public import ErdosSzekeres.StructuralChargingCarrierOnlyProfileConsumer567
public import ErdosSzekeres.StructuralChargingCarrierOnlyProvenance567

@[expose] public section

/-!
# A carrier transversal for the balanced state-567 grid

Four disjoint three-by-three omission rectangles cannot cover all pairs of
vertices in either six-point carrier: four three-sets cover at most twelve of
the fifteen pairs.  An uncovered pair in one carrier, together with one point
of the other carrier, therefore meets both carriers and every grid witness.
-/

namespace ErdosSzekeres

private theorem exists_pair_not_contained_in_four_three_sets
    {α : Type*} [DecidableEq α]
    {univ : Finset α} {family : Finset (Finset α)}
    (hunivCard : univ.card = 6)
    (hfamilyCard : family.card = 4)
    (hrowCard : ∀ row ∈ family, row.card = 3) :
    ∃ pair ∈ univ.powersetCard 2,
      ∀ row ∈ family, ¬pair ⊆ row := by
  classical
  by_contra hcontra
  have hcover :
      univ.powersetCard 2 ⊆
        family.biUnion (fun row ↦ row.powersetCard 2) := by
    intro pair hpair
    have hex : ∃ row ∈ family, pair ⊆ row := by
      by_contra hno
      apply hcontra
      refine ⟨pair, hpair, ?_⟩
      intro row hrow hpairRow
      exact hno ⟨row, hrow, hpairRow⟩
    obtain ⟨row, hrow, hpairRow⟩ := hex
    exact Finset.mem_biUnion.mpr
      ⟨row, hrow, Finset.mem_powersetCard.mpr
        ⟨hpairRow, (Finset.mem_powersetCard.mp hpair).2⟩⟩
  have hleft : (univ.powersetCard 2).card = 15 := by
    rw [Finset.card_powersetCard, hunivCard]
    norm_num [Nat.choose]
  have hright :
      (family.biUnion (fun row ↦ row.powersetCard 2)).card ≤ 12 := by
    calc
      (family.biUnion (fun row ↦ row.powersetCard 2)).card ≤
          family.card * 3 := by
        apply Finset.card_biUnion_le_card_mul
        intro row hrow
        rw [Finset.card_powersetCard, hrowCard row hrow]
        norm_num [Nat.choose]
      _ = 12 := by omega
  have hle := Finset.card_le_card hcover
  omega

/-- A balanced four-grid has a three-point carrier transversal: two points in
`first` and one in `second`, meeting both carriers and every strong grid
witness.  This is the color-free coupling needed before invoking global
deletion packing on a residual triple. -/
theorem IsFourDisjointThreeByThreeOmissionGrid567.exists_carrierTransversal
    {n : ℕ} {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hgrid :
      IsFourDisjointThreeByThreeOmissionGrid567 first second witnesses)
    (hfirstCard : first.card = 6)
    (hsecondCard : second.card = 6)
    (hcarrierDisjoint : Disjoint first second) :
    ∃ transversal : Finset (Fin n),
      transversal ⊆ first ∪ second ∧
        transversal.card = 3 ∧
        ¬Disjoint transversal first ∧
        ¬Disjoint transversal second ∧
        ∀ third ∈ witnesses, ¬Disjoint transversal third := by
  classical
  let omittedRows : Finset (Finset (Fin n)) :=
    witnesses.image fun third ↦ first \ third
  have homittedCard : omittedRows.card ≤ 4 := by
    calc
      omittedRows.card ≤ witnesses.card := Finset.card_image_le
      _ = 4 := hgrid.1
  have hpair :
      ∃ pair ∈ first.powersetCard 2,
        ∀ row ∈ omittedRows, ¬pair ⊆ row := by
    by_cases homittedFour : omittedRows.card = 4
    · apply exists_pair_not_contained_in_four_three_sets
        hfirstCard homittedFour
      · intro row hrow
        obtain ⟨third, hthird, rfl⟩ := Finset.mem_image.mp hrow
        exact (hgrid.2.1 third hthird).1
    · have homittedLt : omittedRows.card < 4 := by omega
      -- With fewer than four distinct omitted rows, the same pair count is
      -- even stronger; pad only the numerical estimate, not the family.
      by_contra hcontra
      have hcover :
          first.powersetCard 2 ⊆
            omittedRows.biUnion (fun row ↦ row.powersetCard 2) := by
        intro pair hpairMem
        have hex : ∃ row ∈ omittedRows, pair ⊆ row := by
          by_contra hno
          apply hcontra
          refine ⟨pair, hpairMem, ?_⟩
          intro row hrow hpairRow
          exact hno ⟨row, hrow, hpairRow⟩
        obtain ⟨row, hrow, hpairRow⟩ := hex
        exact Finset.mem_biUnion.mpr
          ⟨row, hrow, Finset.mem_powersetCard.mpr
            ⟨hpairRow, (Finset.mem_powersetCard.mp hpairMem).2⟩⟩
      have hleft : (first.powersetCard 2).card = 15 := by
        rw [Finset.card_powersetCard, hfirstCard]
        norm_num [Nat.choose]
      have hright :
          (omittedRows.biUnion (fun row ↦ row.powersetCard 2)).card ≤
            omittedRows.card * 3 := by
        apply Finset.card_biUnion_le_card_mul
        intro row hrow
        obtain ⟨third, hthird, rfl⟩ := Finset.mem_image.mp hrow
        rw [Finset.card_powersetCard, (hgrid.2.1 third hthird).1]
        norm_num [Nat.choose]
      have hle := Finset.card_le_card hcover
      omega
  obtain ⟨pair, hpairMem, hpairMiss⟩ := hpair
  have hpairData := Finset.mem_powersetCard.mp hpairMem
  have hpairHits : ∀ third ∈ witnesses, ¬Disjoint pair third := by
    intro third hthird hdisjoint
    apply hpairMiss (first \ third)
    · exact Finset.mem_image.mpr ⟨third, hthird, rfl⟩
    · intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨hpairData.1 hx, fun hxThird ↦
          Finset.disjoint_left.mp hdisjoint hx hxThird⟩
  have hsecondNonempty : second.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z, hzSecond⟩ := hsecondNonempty
  have hzPair : z ∉ pair := by
    intro hz
    exact Finset.disjoint_left.mp hcarrierDisjoint (hpairData.1 hz) hzSecond
  refine ⟨insert z pair, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.insert_subset_iff.mpr
      ⟨Finset.mem_union_right first hzSecond,
        hpairData.1.trans Finset.subset_union_left⟩
  · simp [hzPair, hpairData.2]
  · have hpairNonempty : pair.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hxPair⟩ := hpairNonempty
    exact Finset.not_disjoint_iff.mpr
      ⟨x, Finset.mem_insert_of_mem hxPair, hpairData.1 hxPair⟩
  · exact Finset.not_disjoint_iff.mpr
      ⟨z, Finset.mem_insert_self z pair, hzSecond⟩
  · intro third hthird
    obtain ⟨x, hxPair, hxThird⟩ :=
      Finset.not_disjoint_iff.mp (hpairHits third hthird)
    exact Finset.not_disjoint_iff.mpr
      ⟨x, Finset.mem_insert_of_mem hxPair, hxThird⟩

/-- Once the balanced grid is kept with its canonical provenance, the
three-point transversal makes a new use of global packing genuinely different
from the carrier-only witnesses: after deleting the transversal and any three
residual vertices, the surviving strong six must meet the residual. -/
theorem packedInternalPair_has_residualTouchingEscape_of_balancedGrid
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second)
    (hfirstSub : first ⊆ ambient)
    (hsecondSub : second ⊆ ambient)
    (hpacking : StrongSixAvoidsEverySix χ ambient)
    (hwitnesses :
      witnesses = CarrierOnlyProbeWitnessSets567 χ ambient first second)
    (hgrid :
      IsFourDisjointThreeByThreeOmissionGrid567 first second witnesses)
    {bad : Finset (Fin n)}
    (hbad : bad ∈ BadResidualFourBlocks567 χ
      (ambient \ (first ∪ second))) :
    ∃ transversal : Finset (Fin n),
      transversal ⊆ first ∪ second ∧
        transversal.card = 3 ∧
        ∀ residualTriple : Finset (Fin n),
          residualTriple ⊆ ambient \ (first ∪ second) →
          residualTriple.card = 3 →
          ∃ third : Finset (Fin n),
            third ⊆ ambient \ (transversal ∪ residualTriple) ∧
              third.card = 6 ∧
              IsStrongPolygonSet χ third ∧
              ¬Disjoint third (ambient \ (first ∪ second)) := by
  classical
  obtain ⟨transversal, htransversalSub, htransversalCard,
      htransversalFirst, htransversalSecond, htransversalWitnesses⟩ :=
    hgrid.exists_carrierTransversal hmutual.2.1 hmutual.2.2.1 hmutual.1
  refine ⟨transversal, htransversalSub, htransversalCard, ?_⟩
  intro residualTriple htripleSub htripleCard
  have hcarrierSub : first ∪ second ⊆ ambient :=
    Finset.union_subset hfirstSub hsecondSub
  have htransversalAmbient : transversal ⊆ ambient :=
    htransversalSub.trans hcarrierSub
  have htripleAmbient : residualTriple ⊆ ambient :=
    htripleSub.trans Finset.sdiff_subset
  have htransversalTriple : Disjoint transversal residualTriple := by
    apply Finset.disjoint_left.mpr
    intro x hxTransversal hxTriple
    exact (Finset.mem_sdiff.mp (htripleSub hxTriple)).2
      (htransversalSub hxTransversal)
  have hdeletedSub : transversal ∪ residualTriple ⊆ ambient :=
    Finset.union_subset htransversalAmbient htripleAmbient
  have hdeletedCard : (transversal ∪ residualTriple).card = 6 := by
    rw [Finset.card_union_of_disjoint htransversalTriple,
      htransversalCard, htripleCard]
  obtain ⟨third, hthirdSub, hthirdCard, hthirdStrong⟩ :=
    hpacking (transversal ∪ residualTriple) hdeletedSub hdeletedCard
  have hthirdAmbient : third ⊆ ambient :=
    hthirdSub.trans Finset.sdiff_subset
  have hthirdTransversal : Disjoint third transversal := by
    apply Finset.disjoint_left.mpr
    intro x hxThird hxTransversal
    exact (Finset.mem_sdiff.mp (hthirdSub hxThird)).2
      (Finset.mem_union_left residualTriple hxTransversal)
  have hthirdResidual :
      ¬Disjoint third (ambient \ (first ∪ second)) := by
    intro hdisjointResidual
    have hthirdCarrier : third ⊆ first ∪ second := by
      intro x hxThird
      by_contra hxCarrier
      have hxResidual : x ∈ ambient \ (first ∪ second) :=
        Finset.mem_sdiff.mpr ⟨hthirdAmbient hxThird, hxCarrier⟩
      exact Finset.disjoint_left.mp hdisjointResidual hxThird hxResidual
    rcases carrierContainedStrongSix_classification_of_canonical567
        hmutual hfirstSub hsecondSub hbad hthirdCarrier hthirdCard
          hthirdStrong with hfirst | hsecond | hwitness
    · subst third
      exact htransversalFirst
        hthirdTransversal.symm
    · subst third
      exact htransversalSecond
        hthirdTransversal.symm
    · have hwitness' : third ∈ witnesses := by
        simpa [hwitnesses] using hwitness
      exact htransversalWitnesses third hwitness'
        hthirdTransversal.symm
  exact ⟨third, hthirdSub, hthirdCard, hthirdStrong, hthirdResidual⟩

/-- The entire no-collision branch now reaches the genuinely coupled
residual-touching state.  The mixed rectangle profile is discharged by the
all-order finite theorem; the balanced profile supplies the transversal; and
global deletion packing produces a residual-touching strong six after every
residual triple deletion. -/
theorem packedInternalPair_has_balancedResidualTouchingEscape567_of_noCollision
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second : Finset (Fin n)}
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second)
    (hfirstSub : first ⊆ ambient)
    (hsecondSub : second ⊆ ambient)
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (hpacking : StrongSixAvoidsEverySix χ ambient)
    (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5)
    (hnoCup : ¬ContainsCupSet χ ambient 6)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ ambient 7)
    (hnoCollision :
      HasNoCarrierTouchingSameOccupancyCollision567 χ ambient first second) :
    ∃ witnesses : Finset (Finset (Fin n)),
      witnesses = CarrierOnlyProbeWitnessSets567 χ ambient first second ∧
        IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses ∧
        IsFourDisjointThreeByThreeOmissionGrid567 first second witnesses ∧
        ∃ transversal : Finset (Fin n),
          transversal ⊆ first ∪ second ∧
            transversal.card = 3 ∧
            ∀ residualTriple : Finset (Fin n),
              residualTriple ⊆ ambient \ (first ∪ second) →
              residualTriple.card = 3 →
              ∃ third : Finset (Fin n),
                third ⊆ ambient \ (transversal ∪ residualTriple) ∧
                  third.card = 6 ∧
                  IsStrongPolygonSet χ third ∧
                  ¬Disjoint third (ambient \ (first ∪ second)) := by
  classical
  have hpairSub : first ∪ second ⊆ ambient :=
    Finset.union_subset hfirstSub hsecondSub
  obtain ⟨witnesses, hwitnesses, hsystem, hgrid⟩ :=
    packedInternalPair_has_balancedGrid567_of_noCollision
      hmutual hpairSub hescape hone hnoCap hnoCup hnoStrongSeven hnoCollision
  let residual := ambient \ (first ∪ second)
  have hresidualCard : residual.card = 10 := by
    simpa [residual] using hescape.1
  have hnoStrongResidual : ¬ContainsStrongPolygonSet χ residual 7 := by
    intro hstrong
    exact hnoStrongSeven
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.sdiff_subset)
  obtain ⟨seed, hseedSub, hseedCard⟩ :=
    Finset.exists_subset_card_eq (show 3 ≤ residual.card by omega)
  obtain ⟨bad, hbad, _hseedBad⟩ :=
    badResidualFourBlocks567_covers_three hresidualCard hnoStrongResidual
      hseedSub hseedCard
  obtain ⟨transversal, htransversalSub, htransversalCard, htouching⟩ :=
    packedInternalPair_has_residualTouchingEscape_of_balancedGrid
      hmutual hfirstSub hsecondSub hpacking hwitnesses hgrid
        (by simpa [residual] using hbad)
  exact ⟨witnesses, hwitnesses, hsystem, hgrid, transversal,
    htransversalSub, htransversalCard, htouching⟩

end ErdosSzekeres

end
