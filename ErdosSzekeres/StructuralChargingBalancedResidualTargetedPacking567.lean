module

public import ErdosSzekeres.StructuralChargingBalancedResidualTouching567

@[expose] public section

/-!
# Targeted residual-triple packing at state 567

The balanced carrier grid supplies a three-point transversal meeting every
carrier-contained strong six.  Global six-deletion packing can then be
restricted exactly to deletions consisting of that transversal and a residual
triple.  Under the hitting property, this targeted packing is equivalent to
requiring every resulting strong six to have a residual-touching witness.
-/

namespace ErdosSzekeres

/-- A transversal hits every strong six contained in the two carriers. -/
def HitsEveryCarrierStrongSix567 {n : ℕ} (χ : TripleColoring n)
    (first second transversal : Finset (Fin n)) : Prop :=
  ∀ third : Finset (Fin n),
    third ⊆ first ∪ second →
    third.card = 6 →
    IsStrongPolygonSet χ third →
    ¬Disjoint transversal third

/-- Packing restricted to deletions formed from the fixed carrier transversal
and an arbitrary residual triple. -/
def TargetedResidualTriplePacking567 {n : ℕ} (χ : TripleColoring n)
    (ambient first second transversal : Finset (Fin n)) : Prop :=
  ∀ residualTriple : Finset (Fin n),
    residualTriple ⊆ ambient \ (first ∪ second) →
    residualTriple.card = 3 →
    ContainsStrongPolygonSet χ
      (ambient \ (transversal ∪ residualTriple)) 6

/-- Canonical provenance upgrades the balanced-grid transversal to one hitting
every carrier-contained strong six, with no fixed placement or color data. -/
theorem exists_carrierTransversal_hitting_every_carrierStrongSix567
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second bad : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second)
    (hfirstSub : first ⊆ ambient)
    (hsecondSub : second ⊆ ambient)
    (hwitnesses :
      witnesses = CarrierOnlyProbeWitnessSets567 χ ambient first second)
    (hgrid :
      IsFourDisjointThreeByThreeOmissionGrid567 first second witnesses)
    (hbad : bad ∈ BadResidualFourBlocks567 χ
      (ambient \ (first ∪ second))) :
    ∃ transversal : Finset (Fin n),
      transversal ⊆ first ∪ second ∧
      transversal.card = 3 ∧
      HitsEveryCarrierStrongSix567 χ first second transversal := by
  classical
  obtain ⟨transversal, htransversalSub, htransversalCard,
      htransversalFirst, htransversalSecond, htransversalWitnesses⟩ :=
    hgrid.exists_carrierTransversal hmutual.2.1 hmutual.2.2.1 hmutual.1
  refine ⟨transversal, htransversalSub, htransversalCard, ?_⟩
  intro third hthirdSub hthirdCard hthirdStrong
  rcases carrierContainedStrongSix_classification_of_canonical567
      hmutual hfirstSub hsecondSub hbad hthirdSub hthirdCard hthirdStrong with
      hfirst | hsecond | hwitness
  · subst third
    exact htransversalFirst
  · subst third
    exact htransversalSecond
  · have hwitness' : third ∈ witnesses := by
      simpa [hwitnesses] using hwitness
    exact htransversalWitnesses third hwitness'

/-- Under a carrier-hitting transversal, targeted packing is exactly the
universal existence of residual-touching escape witnesses. -/
theorem targetedPacking_iff_residualTouchingEscapes567
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second transversal : Finset (Fin n)}
    (htransversalSub : transversal ⊆ first ∪ second)
    (hhits : HitsEveryCarrierStrongSix567 χ first second transversal)
    (hfirstSub : first ⊆ ambient)
    (hsecondSub : second ⊆ ambient) :
    TargetedResidualTriplePacking567 χ ambient first second transversal ↔
      ∀ residualTriple : Finset (Fin n),
        residualTriple ⊆ ambient \ (first ∪ second) →
        residualTriple.card = 3 →
        ∃ third : Finset (Fin n),
          third ⊆ ambient \ (transversal ∪ residualTriple) ∧
          third.card = 6 ∧
          IsStrongPolygonSet χ third ∧
          ¬Disjoint third (ambient \ (first ∪ second)) := by
  constructor
  · intro hpacking residualTriple htripleSub htripleCard
    obtain ⟨third, hthirdSub, hthirdCard, hthirdStrong⟩ :=
      hpacking residualTriple htripleSub htripleCard
    refine ⟨third, hthirdSub, hthirdCard, hthirdStrong, ?_⟩
    intro hthirdResidual
    have hthirdAmbient : third ⊆ ambient :=
      hthirdSub.trans Finset.sdiff_subset
    have hthirdCarrier : third ⊆ first ∪ second := by
      intro x hxThird
      by_contra hxCarrier
      have hxResidual : x ∈ ambient \ (first ∪ second) :=
        Finset.mem_sdiff.mpr ⟨hthirdAmbient hxThird, hxCarrier⟩
      exact Finset.disjoint_left.mp hthirdResidual hxThird hxResidual
    apply hhits third hthirdCarrier hthirdCard hthirdStrong
    apply Finset.disjoint_left.mpr
    intro x hxTransversal hxThird
    exact (Finset.mem_sdiff.mp (hthirdSub hxThird)).2
      (Finset.mem_union_left residualTriple hxTransversal)
  · intro hescapes residualTriple htripleSub htripleCard
    obtain ⟨third, hthirdSub, hthirdCard, hthirdStrong, _hthirdResidual⟩ :=
      hescapes residualTriple htripleSub htripleCard
    exact ⟨third, hthirdSub, hthirdCard, hthirdStrong⟩

/-- Global packing implies the targeted residual-triple packing interface.
The six-point deletion cardinality is derived from the carrier/residual
disjointness of the transversal and residual triple. -/
theorem targetedResidualTriplePacking567_of_strongSixAvoidsEverySix
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second transversal : Finset (Fin n)}
    (htransversalSub : transversal ⊆ first ∪ second)
    (htransversalCard : transversal.card = 3)
    (hfirstSub : first ⊆ ambient)
    (hsecondSub : second ⊆ ambient)
    (hpacking : StrongSixAvoidsEverySix χ ambient) :
    TargetedResidualTriplePacking567 χ ambient first second transversal := by
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
  exact hpacking (transversal ∪ residualTriple) hdeletedSub hdeletedCard

end ErdosSzekeres

end
