module

public import ErdosSzekeres.StructuralChargingResidualProbeCount567
public import ErdosSzekeres.StructuralChargingStrongSixSignature
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

@[expose] public section

/-!
# Reuse among the thirty state-567 residual probes

This file keeps the probe-to-witness relation choice-free.  It first records
the triple-cover property of the bad residual four-blocks and the exact
binomial capacity of the fiber served by a fixed strong-six witness.
-/

namespace ErdosSzekeres

/-- A bad residual four-block together with a carrier-touching strong-six
witness which survives deletion of the two fixed carrier anchors. -/
def IsCarrierTouchingProbeWitness567 {n : ℕ} (χ : TripleColoring n)
    (ambient first second : Finset (Fin n)) (a b : Fin n)
    (block third : Finset (Fin n)) : Prop :=
  block ∈ BadResidualFourBlocks567 χ (ambient \ (first ∪ second)) ∧
    third ⊆ ambient \ insert a (insert b block) ∧
    third.card = 6 ∧ IsStrongPolygonSet χ third ∧
    (HasPairEscapeOccupancy first second third .oneCarrier ∨
      HasPairEscapeOccupancy first second third .twoCarrier)

/-- All bad probes served by one fixed carrier-touching strong-six witness. -/
noncomputable def CarrierTouchingProbeFiber567 {n : ℕ}
    (χ : TripleColoring n) (ambient first second : Finset (Fin n))
    (a b : Fin n) (third : Finset (Fin n)) : Finset (Finset (Fin n)) := by
  classical
  exact (BadResidualFourBlocks567 χ (ambient \ (first ∪ second))).filter
    (fun block ↦ IsCarrierTouchingProbeWitness567 χ ambient first second
      a b block third)

/-- The finite, choice-free universe of strong-six witnesses incident with at
least one bad residual probe. -/
noncomputable def CarrierTouchingProbeWitnesses567 {n : ℕ}
    (χ : TripleColoring n) (ambient first second : Finset (Fin n))
    (a b : Fin n) : Finset (Finset (Fin n)) := by
  classical
  exact (ambient.powersetCard 6).filter fun third ↦
    ∃ block, IsCarrierTouchingProbeWitness567 χ ambient first second
      a b block third

/-- Two witnesses have the same coarse carrier-touching occupancy when both
are one-carrier witnesses or both are two-carrier witnesses. -/
def SameCarrierTouchingOccupancy567 {n : ℕ}
    (first second third₁ third₂ : Finset (Fin n)) : Prop :=
  (HasPairEscapeOccupancy first second third₁ .oneCarrier ∧
      HasPairEscapeOccupancy first second third₂ .oneCarrier) ∨
    (HasPairEscapeOccupancy first second third₁ .twoCarrier ∧
      HasPairEscapeOccupancy first second third₂ .twoCarrier)

/-- Bad complementary four-blocks cover every triple of a ten-point residual.
This is the choice-free strengthening behind the thirty-probe count. -/
theorem badResidualFourBlocks567_covers_three
    {n : ℕ} {χ : TripleColoring n} {residual triple : Finset (Fin n)}
    (hresidualCard : residual.card = 10)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ residual 7)
    (htripleSub : triple ⊆ residual) (htripleCard : triple.card = 3) :
    ∃ block ∈ BadResidualFourBlocks567 χ residual,
      triple ⊆ block := by
  classical
  let seven := residual \ triple
  have hsevenSub : seven ⊆ residual := Finset.sdiff_subset
  have hsevenCard : seven.card = 7 := by
    simp only [seven]
    rw [Finset.card_sdiff_of_subset htripleSub, hresidualCard, htripleCard]
  have hsevenNotStrong : ¬IsStrongPolygonSet χ seven := by
    intro hstrong
    exact hnoStrongSeven ⟨seven, hsevenSub, hsevenCard, hstrong⟩
  obtain ⟨six, hsixSubSeven, hsixCard, hsixNotStrong⟩ :=
    exists_nonStrong_six_subset_of_notStrong_seven hsevenCard
      hsevenNotStrong
  have hsixSub : six ⊆ residual := hsixSubSeven.trans hsevenSub
  let block := residual \ six
  have hblockSub : block ⊆ residual := Finset.sdiff_subset
  have hblockCard : block.card = 4 := by
    simp only [block]
    rw [Finset.card_sdiff_of_subset hsixSub, hresidualCard, hsixCard]
  have htripleBlock : triple ⊆ block := by
    intro x hxTriple
    apply Finset.mem_sdiff.mpr
    refine ⟨htripleSub hxTriple, ?_⟩
    intro hxSix
    exact (Finset.mem_sdiff.mp (hsixSubSeven hxSix)).2 hxTriple
  refine ⟨block, ?_, htripleBlock⟩
  change block ∈ (residual.powersetCard 4).filter
    (fun candidate ↦ ¬IsStrongPolygonSet χ (residual \ candidate))
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨hblockSub, hblockCard⟩, ?_⟩
  simpa only [block, Finset.sdiff_sdiff_eq_self hsixSub] using hsixNotStrong

/-- If one residual triple lies in at least three bad four-blocks, the full
triple cover needs at least thirty-one bad blocks. -/
theorem thirty_one_le_card_badResidualFourBlocks567_of_three_through_triple
    {n : ℕ} {χ : TripleColoring n} {residual triple : Finset (Fin n)}
    (hresidualCard : residual.card = 10)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ residual 7)
    (htripleSub : triple ⊆ residual) (htripleCard : triple.card = 3)
    (hthree : 3 ≤ ((BadResidualFourBlocks567 χ residual).filter
      (fun block ↦ triple ⊆ block)).card) :
    31 ≤ (BadResidualFourBlocks567 χ residual).card := by
  classical
  let triples := residual.powersetCard 3
  let probes := BadResidualFourBlocks567 χ residual
  let related : Finset (Fin n) → Finset (Fin n) → Prop :=
    fun small block ↦ small ⊆ block
  have hdegreeOne : ∀ small ∈ triples,
      1 ≤ (probes.bipartiteAbove related small).card := by
    intro small hsmall
    have hsmallData := Finset.mem_powersetCard.mp hsmall
    obtain ⟨block, hblock, hsmallBlock⟩ :=
      badResidualFourBlocks567_covers_three hresidualCard hnoStrongSeven
        hsmallData.1 hsmallData.2
    exact Finset.card_pos.mpr
      ⟨block, Finset.mem_filter.mpr ⟨hblock, hsmallBlock⟩⟩
  have htripleMem : triple ∈ triples :=
    Finset.mem_powersetCard.mpr ⟨htripleSub, htripleCard⟩
  have htripleDegree :
      3 ≤ (probes.bipartiteAbove related triple).card := by
    simpa [Finset.bipartiteAbove, probes, related] using hthree
  have hstrict :
      triples.card <
        ∑ small ∈ triples, (probes.bipartiteAbove related small).card := by
    calc
      triples.card = ∑ _small ∈ triples, 1 := by simp
      _ < ∑ small ∈ triples,
          (probes.bipartiteAbove related small).card := by
        apply Finset.sum_lt_sum
        · intro small hsmall
          exact hdegreeOne small hsmall
        · exact ⟨triple, htripleMem, by omega⟩
  have hbelowCard : ∀ block ∈ probes,
      (triples.bipartiteBelow related block).card = 4 := by
    intro block hblock
    change block ∈ (residual.powersetCard 4).filter
      (fun candidate ↦ ¬IsStrongPolygonSet χ (residual \ candidate)) at hblock
    have hblockData := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hblock).1
    have heq : triples.bipartiteBelow related block = block.powersetCard 3 := by
      ext small
      simp only [Finset.mem_bipartiteBelow, Finset.mem_powersetCard,
        triples, related]
      constructor
      · rintro ⟨⟨_smallSub, hsmallCard⟩, hsmallBlock⟩
        exact ⟨hsmallBlock, hsmallCard⟩
      · rintro ⟨hsmallBlock, hsmallCard⟩
        exact ⟨⟨hsmallBlock.trans hblockData.1, hsmallCard⟩, hsmallBlock⟩
    rw [heq, Finset.card_powersetCard, hblockData.2]
    norm_num [Nat.choose]
  have hdoubleCount :
      (∑ small ∈ triples, (probes.bipartiteAbove related small).card) =
        probes.card * 4 := by
    rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    calc
      (∑ block ∈ probes, (triples.bipartiteBelow related block).card) =
          ∑ _block ∈ probes, 4 := by
        apply Finset.sum_congr rfl
        intro block hblock
        exact hbelowCard block hblock
      _ = probes.card * 4 := by simp
  have htriplesCard : triples.card = 120 := by
    simp only [triples, Finset.card_powersetCard, hresidualCard]
    norm_num [Nat.choose]
  rw [hdoubleCount, htriplesCard] at hstrict
  change 31 ≤ probes.card
  omega

/-- A fixed witness can serve at most `choose (10-r) 4` bad probes, where
`r` is the size of its residual intersection. -/
theorem carrierTouchingProbeFiber567_subset_potential
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second third : Finset (Fin n)} {a b : Fin n} :
    CarrierTouchingProbeFiber567 χ ambient first second a b third ⊆
      ((ambient \ (first ∪ second)) \ third).powersetCard 4 := by
  classical
  let residual := ambient \ (first ∪ second)
  intro block hblock
  have hfiber := Finset.mem_filter.mp hblock
  have hbad := hfiber.1
  have hwitness := hfiber.2
  change block ∈ (residual.powersetCard 4).filter
    (fun candidate ↦ ¬IsStrongPolygonSet χ (residual \ candidate)) at hbad
  have hblockData := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hbad).1
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, hblockData.2⟩
  intro x hxBlock
  apply Finset.mem_sdiff.mpr
  refine ⟨hblockData.1 hxBlock, ?_⟩
  intro hxThird
  have hxAvoid := Finset.mem_sdiff.mp (hwitness.2.1 hxThird)
  exact hxAvoid.2 (by simp [hxBlock])

theorem card_carrierTouchingProbeFiber567_le_choose
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second third : Finset (Fin n)} {a b : Fin n}
    (hresidualCard : (ambient \ (first ∪ second)).card = 10) :
    (CarrierTouchingProbeFiber567 χ ambient first second a b third).card ≤
      Nat.choose (10 - (third ∩ (ambient \ (first ∪ second))).card) 4 := by
  classical
  let residual := ambient \ (first ∪ second)
  calc
    (CarrierTouchingProbeFiber567 χ ambient first second a b third).card
        ≤ ((residual \ third).powersetCard 4).card :=
      Finset.card_le_card carrierTouchingProbeFiber567_subset_potential
    _ = Nat.choose (10 - (third ∩ residual).card) 4 := by
      rw [Finset.card_powersetCard, Finset.card_sdiff, hresidualCard]

/-- An incident strong six splits exactly into its carrier and residual
intersections. -/
theorem IsCarrierTouchingProbeWitness567.carrier_add_residual_card
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second block third : Finset (Fin n)} {a b : Fin n}
    (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
      a b block third) :
    (third ∩ (first ∪ second)).card +
      (third ∩ (ambient \ (first ∪ second))).card = 6 := by
  have hthirdAmbient : third ⊆ ambient :=
    hincident.2.1.trans Finset.sdiff_subset
  have hdiff :
      third \ (first ∪ second) =
        third ∩ (ambient \ (first ∪ second)) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨hxThird, hxCarrier⟩
      exact ⟨hxThird, hthirdAmbient hxThird, hxCarrier⟩
    · rintro ⟨hxThird, _hxAmbient, hxCarrier⟩
      exact ⟨hxThird, hxCarrier⟩
  have hcard := Finset.card_sdiff_add_card_inter third (first ∪ second)
  rw [hdiff, hincident.2.2.1] at hcard
  omega

/-- Carrier touching makes the carrier intersection of an incident witness
nonempty. -/
theorem IsCarrierTouchingProbeWitness567.one_le_carrier_card
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second block third : Finset (Fin n)} {a b : Fin n}
    (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
      a b block third) :
    1 ≤ (third ∩ (first ∪ second)).card := by
  have hnonempty : (third ∩ (first ∪ second)).Nonempty := by
    rcases hincident.2.2.2.2 with hone | htwo
    · rcases hone with hone | hone
      · obtain ⟨x, hxThird, hxFirst⟩ := Finset.not_disjoint_iff.mp hone.1
        exact ⟨x, Finset.mem_inter.mpr
          ⟨hxThird, Finset.mem_union_left second hxFirst⟩⟩
      · obtain ⟨x, hxThird, hxSecond⟩ := Finset.not_disjoint_iff.mp hone.2
        exact ⟨x, Finset.mem_inter.mpr
          ⟨hxThird, Finset.mem_union_right first hxSecond⟩⟩
    · obtain ⟨x, hxThird, hxFirst⟩ := Finset.not_disjoint_iff.mp htwo.1
      exact ⟨x, Finset.mem_inter.mpr
        ⟨hxThird, Finset.mem_union_left second hxFirst⟩⟩
  exact Finset.card_pos.mpr hnonempty

/-- Every bad residual probe has an incident carrier-touching strong-six
witness. -/
theorem PackedInternalPairFourResidualEscape.badProbe_has_incident_witness
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second block : Finset (Fin n)} {a b : Fin n}
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (ha : a ∈ first) (hb : b ∈ second)
    (hblock : block ∈ BadResidualFourBlocks567 χ
      (ambient \ (first ∪ second))) :
    ∃ third, IsCarrierTouchingProbeWitness567 χ ambient first second
      a b block third := by
  classical
  let residual := ambient \ (first ∪ second)
  change block ∈ (residual.powersetCard 4).filter
    (fun candidate ↦ ¬IsStrongPolygonSet χ (residual \ candidate)) at hblock
  have hblockData := Finset.mem_filter.mp hblock
  have hblockPowerset := Finset.mem_powersetCard.mp hblockData.1
  obtain ⟨third, hthirdSub, hthirdCard, hthirdStrong, hoccupancy⟩ :=
    hescape.exists_carrierTouching_witness ha hb hblockPowerset.1
      hblockPowerset.2 hblockData.2
  exact ⟨third, hblock, hthirdSub, hthirdCard, hthirdStrong, hoccupancy⟩

/-- Thirty choice-free probe incidences force either a collision in the two
coarse carrier-touching occupancy classes or one witness serving at least
fifteen bad probes. -/
theorem exists_sameOccupancyCollision_or_fifteenProbeWitness567
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second : Finset (Fin n)}
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ ambient 7)
    {a b : Fin n} (ha : a ∈ first) (hb : b ∈ second) :
    (∃ third₁ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
      ∃ third₂ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
        third₁ ≠ third₂ ∧
          SameCarrierTouchingOccupancy567 first second third₁ third₂) ∨
    ∃ third ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
      15 ≤ (CarrierTouchingProbeFiber567 χ ambient first second a b third).card := by
  classical
  let residual := ambient \ (first ∪ second)
  let probes := BadResidualFourBlocks567 χ residual
  let witnesses := CarrierTouchingProbeWitnesses567 χ ambient first second a b
  by_cases hcollision :
      ∃ third₁ ∈ witnesses, ∃ third₂ ∈ witnesses,
        third₁ ≠ third₂ ∧
          SameCarrierTouchingOccupancy567 first second third₁ third₂
  · exact Or.inl hcollision
  · right
    have hnoCollision :
        ∀ third₁ ∈ witnesses, ∀ third₂ ∈ witnesses,
          SameCarrierTouchingOccupancy567 first second third₁ third₂ →
            third₁ = third₂ := by
      intro third₁ hthird₁ third₂ hthird₂ hsame
      by_contra hne
      exact hcollision ⟨third₁, hthird₁, third₂, hthird₂, hne, hsame⟩
    let oneWitnesses := witnesses.filter fun third ↦
      HasPairEscapeOccupancy first second third .oneCarrier
    let twoWitnesses := witnesses.filter fun third ↦
      HasPairEscapeOccupancy first second third .twoCarrier
    have hwitnessesSub : witnesses ⊆ oneWitnesses ∪ twoWitnesses := by
      intro third hthird
      have hthirdWitnesses : third ∈ witnesses := hthird
      change third ∈ (ambient.powersetCard 6).filter
        (fun candidate ↦ ∃ block,
          IsCarrierTouchingProbeWitness567 χ ambient first second
            a b block candidate) at hthird
      obtain ⟨block, hincident⟩ := (Finset.mem_filter.mp hthird).2
      rcases hincident.2.2.2.2 with hone | htwo
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hthirdWitnesses, hone⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hthirdWitnesses, htwo⟩)
    have honeCard : oneWitnesses.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro third₁ hthird₁ third₂ hthird₂
      have hdata₁ := Finset.mem_filter.mp hthird₁
      have hdata₂ := Finset.mem_filter.mp hthird₂
      exact hnoCollision third₁ hdata₁.1 third₂ hdata₂.1
        (Or.inl ⟨hdata₁.2, hdata₂.2⟩)
    have htwoCard : twoWitnesses.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro third₁ hthird₁ third₂ hthird₂
      have hdata₁ := Finset.mem_filter.mp hthird₁
      have hdata₂ := Finset.mem_filter.mp hthird₂
      exact hnoCollision third₁ hdata₁.1 third₂ hdata₂.1
        (Or.inr ⟨hdata₁.2, hdata₂.2⟩)
    have hwitnessesCard : witnesses.card ≤ 2 := by
      have hunion := Finset.card_union_le oneWitnesses twoWitnesses
      exact (Finset.card_le_card hwitnessesSub).trans (by omega)
    by_contra hnoHigh
    push Not at hnoHigh
    have hprobeCover : probes ⊆ witnesses.biUnion
        (fun third ↦ CarrierTouchingProbeFiber567 χ ambient first second
          a b third) := by
      intro block hblock
      obtain ⟨third, hincident⟩ :=
        hescape.badProbe_has_incident_witness ha hb (by simpa [probes, residual] using hblock)
      apply Finset.mem_biUnion.mpr
      refine ⟨third, ?_, ?_⟩
      · change third ∈ (ambient.powersetCard 6).filter
          (fun candidate ↦ ∃ probe,
            IsCarrierTouchingProbeWitness567 χ ambient first second
              a b probe candidate)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powersetCard.mpr
            ⟨hincident.2.1.trans Finset.sdiff_subset, hincident.2.2.1⟩,
            block, hincident⟩
      · exact Finset.mem_filter.mpr
          ⟨by simpa [probes, residual] using hblock, hincident⟩
    have hprobeCard : 30 ≤ probes.card := by
      have hnoStrongResidual : ¬ContainsStrongPolygonSet χ residual 7 := by
        intro hstrong
        exact hnoStrongSeven
          (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.sdiff_subset)
      exact thirty_le_card_badResidualFourBlocks567 hescape.1 hnoStrongResidual
    have hunionCard :
        (witnesses.biUnion
          (fun third ↦ CarrierTouchingProbeFiber567 χ ambient first second
            a b third)).card ≤ witnesses.card * 14 := by
      apply Finset.card_biUnion_le_card_mul
      intro third hthird
      have := hnoHigh third (by simpa [witnesses] using hthird)
      omega
    have := (Finset.card_le_card hprobeCover).trans hunionCard
    omega

/-- In the exact residual-ten packed context, the thirty probes force either
two distinct witnesses in the same coarse occupancy class or an incident
strong six containing at least three vertices of the two original carriers. -/
theorem exists_sameOccupancyCollision_or_threeCarrierWitness567
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second : Finset (Fin n)}
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second)
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ ambient 7)
    {a b : Fin n} (ha : a ∈ first) (hb : b ∈ second) :
    (∃ third₁ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
      ∃ third₂ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
        third₁ ≠ third₂ ∧
          SameCarrierTouchingOccupancy567 first second third₁ third₂) ∨
    ∃ block third,
      IsCarrierTouchingProbeWitness567 χ ambient first second a b block third ∧
        3 ≤ (third ∩ (first ∪ second)).card := by
  classical
  have _anchorsDistinct : a ≠ b := by
    intro hab
    subst b
    exact Finset.disjoint_left.mp hmutual.1 ha hb
  let residual := ambient \ (first ∪ second)
  let probes := BadResidualFourBlocks567 χ residual
  let witnesses := CarrierTouchingProbeWitnesses567 χ ambient first second a b
  by_cases hcollision :
      ∃ third₁ ∈ witnesses, ∃ third₂ ∈ witnesses,
        third₁ ≠ third₂ ∧
          SameCarrierTouchingOccupancy567 first second third₁ third₂
  · exact Or.inl hcollision
  · right
    have hnoCollision :
        ∀ third₁ ∈ witnesses, ∀ third₂ ∈ witnesses,
          SameCarrierTouchingOccupancy567 first second third₁ third₂ →
            third₁ = third₂ := by
      intro third₁ hthird₁ third₂ hthird₂ hsame
      by_contra hne
      exact hcollision ⟨third₁, hthird₁, third₂, hthird₂, hne, hsame⟩
    let oneWitnesses := witnesses.filter fun third ↦
      HasPairEscapeOccupancy first second third .oneCarrier
    let twoWitnesses := witnesses.filter fun third ↦
      HasPairEscapeOccupancy first second third .twoCarrier
    have hwitnessesSub : witnesses ⊆ oneWitnesses ∪ twoWitnesses := by
      intro third hthird
      have hthirdWitnesses : third ∈ witnesses := hthird
      change third ∈ (ambient.powersetCard 6).filter
        (fun candidate ↦ ∃ block,
          IsCarrierTouchingProbeWitness567 χ ambient first second
            a b block candidate) at hthird
      obtain ⟨block, hincident⟩ := (Finset.mem_filter.mp hthird).2
      rcases hincident.2.2.2.2 with hone | htwo
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hthirdWitnesses, hone⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hthirdWitnesses, htwo⟩)
    have honeCard : oneWitnesses.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro third₁ hthird₁ third₂ hthird₂
      have hdata₁ := Finset.mem_filter.mp hthird₁
      have hdata₂ := Finset.mem_filter.mp hthird₂
      exact hnoCollision third₁ hdata₁.1 third₂ hdata₂.1
        (Or.inl ⟨hdata₁.2, hdata₂.2⟩)
    have htwoCard : twoWitnesses.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro third₁ hthird₁ third₂ hthird₂
      have hdata₁ := Finset.mem_filter.mp hthird₁
      have hdata₂ := Finset.mem_filter.mp hthird₂
      exact hnoCollision third₁ hdata₁.1 third₂ hdata₂.1
        (Or.inr ⟨hdata₁.2, hdata₂.2⟩)
    have hwitnessesCard : witnesses.card ≤ 2 := by
      have hunion := Finset.card_union_le oneWitnesses twoWitnesses
      exact (Finset.card_le_card hwitnessesSub).trans (by omega)
    have hprobeCover : probes ⊆ witnesses.biUnion
        (fun third ↦ CarrierTouchingProbeFiber567 χ ambient first second
          a b third) := by
      intro block hblock
      obtain ⟨third, hincident⟩ :=
        hescape.badProbe_has_incident_witness ha hb
          (by simpa [probes, residual] using hblock)
      apply Finset.mem_biUnion.mpr
      refine ⟨third, ?_, ?_⟩
      · change third ∈ (ambient.powersetCard 6).filter
          (fun candidate ↦ ∃ probe,
            IsCarrierTouchingProbeWitness567 χ ambient first second
              a b probe candidate)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powersetCard.mpr
            ⟨hincident.2.1.trans Finset.sdiff_subset, hincident.2.2.1⟩,
            block, hincident⟩
      · exact Finset.mem_filter.mpr
          ⟨by simpa [probes, residual] using hblock, hincident⟩
    by_contra hnoHeavy
    push Not at hnoHeavy
    have hfiberCard : ∀ third ∈ witnesses,
        (CarrierTouchingProbeFiber567 χ ambient first second a b third).card ≤ 15 := by
      intro third hthird
      change third ∈ (ambient.powersetCard 6).filter
        (fun candidate ↦ ∃ block,
          IsCarrierTouchingProbeWitness567 χ ambient first second
            a b block candidate) at hthird
      obtain ⟨block, hincident⟩ := (Finset.mem_filter.mp hthird).2
      have hcarrierLe : (third ∩ (first ∪ second)).card ≤ 2 := by
        have := hnoHeavy block third hincident
        omega
      have hcarrierPos := hincident.one_le_carrier_card
      have hsplit : (third ∩ (first ∪ second)).card +
          (third ∩ residual).card = 6 := by
        simpa [residual] using hincident.carrier_add_residual_card
      have hresidualRange :
          (third ∩ residual).card = 4 ∨ (third ∩ residual).card = 5 := by
        omega
      have hcapacity := card_carrierTouchingProbeFiber567_le_choose
        (χ := χ) (ambient := ambient) (first := first) (second := second)
        (third := third) (a := a) (b := b) hescape.1
      rcases hresidualRange with hr | hr
      · simpa [residual, hr, Nat.choose] using hcapacity
      · have :
            (CarrierTouchingProbeFiber567 χ ambient first second a b third).card ≤ 5 := by
          simpa [residual, hr, Nat.choose] using hcapacity
        omega
    have hprobesCardLe : probes.card ≤ 30 := by
      have hunionCard :
          (witnesses.biUnion
            (fun third ↦ CarrierTouchingProbeFiber567 χ ambient first second
              a b third)).card ≤ witnesses.card * 15 := by
        apply Finset.card_biUnion_le_card_mul
        exact hfiberCard
      have := (Finset.card_le_card hprobeCover).trans hunionCard
      omega
    have hnoStrongResidual : ¬ContainsStrongPolygonSet χ residual 7 := by
      intro hstrong
      exact hnoStrongSeven
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.sdiff_subset)
    have hprobesCardGe : 30 ≤ probes.card :=
      thirty_le_card_badResidualFourBlocks567 hescape.1 hnoStrongResidual
    have hprobesCard : probes.card = 30 := by omega
    rcases exists_sameOccupancyCollision_or_fifteenProbeWitness567
        hescape hnoStrongSeven ha hb with hcollision' | hhigh
    · exact hcollision hcollision'
    · obtain ⟨third, hthirdWitness, hhigh⟩ := hhigh
      change third ∈ (ambient.powersetCard 6).filter
        (fun candidate ↦ ∃ block,
          IsCarrierTouchingProbeWitness567 χ ambient first second
            a b block candidate) at hthirdWitness
      obtain ⟨block, hincident⟩ := (Finset.mem_filter.mp hthirdWitness).2
      have hcarrierLe : (third ∩ (first ∪ second)).card ≤ 2 := by
        have := hnoHeavy block third hincident
        omega
      have hcarrierPos := hincident.one_le_carrier_card
      have hsplit : (third ∩ (first ∪ second)).card +
          (third ∩ residual).card = 6 := by
        simpa [residual] using hincident.carrier_add_residual_card
      have hresidualRange :
          (third ∩ residual).card = 4 ∨ (third ∩ residual).card = 5 := by
        omega
      have hresidualFour : (third ∩ residual).card = 4 := by
        rcases hresidualRange with hr | hr
        · exact hr
        · have hcapacity := card_carrierTouchingProbeFiber567_le_choose
              (χ := χ) (ambient := ambient) (first := first) (second := second)
              (third := third) (a := a) (b := b) hescape.1
          have :
              (CarrierTouchingProbeFiber567 χ ambient first second a b third).card ≤ 5 := by
            simpa [residual, hr, Nat.choose] using hcapacity
          omega
      let available := residual \ third
      have havailableCard : available.card = 6 := by
        simp only [available]
        rw [Finset.card_sdiff, hescape.1, hresidualFour]
      have hpotentialCard : (available.powersetCard 4).card = 15 := by
        rw [Finset.card_powersetCard, havailableCard]
        norm_num [Nat.choose]
      have hfiberSub :
          CarrierTouchingProbeFiber567 χ ambient first second a b third ⊆
            available.powersetCard 4 := by
        simpa [available, residual] using
          (carrierTouchingProbeFiber567_subset_potential
            (χ := χ) (ambient := ambient) (first := first) (second := second)
            (third := third) (a := a) (b := b))
      have hfiberEq :
          CarrierTouchingProbeFiber567 χ ambient first second a b third =
            available.powersetCard 4 := by
        apply Finset.eq_of_subset_of_card_le hfiberSub
        rw [hpotentialCard]
        exact hhigh
      obtain ⟨small, hsmallSub, hsmallCard⟩ :=
        Finset.exists_subset_card_eq (show 3 ≤ available.card by omega)
      let rest := available \ small
      have hrestCard : rest.card = 3 := by
        simp only [rest]
        rw [Finset.card_sdiff_of_subset hsmallSub, havailableCard, hsmallCard]
      obtain ⟨x, y, z, hxy, hxz, hyz, hrest⟩ :=
        Finset.card_eq_three.mp hrestCard
      have hxRest : x ∈ rest := by rw [hrest]; simp
      have hyRest : y ∈ rest := by rw [hrest]; simp
      have hzRest : z ∈ rest := by rw [hrest]; simp
      have hxAvailable := (Finset.mem_sdiff.mp hxRest).1
      have hyAvailable := (Finset.mem_sdiff.mp hyRest).1
      have hzAvailable := (Finset.mem_sdiff.mp hzRest).1
      have hxSmall := (Finset.mem_sdiff.mp hxRest).2
      have hySmall := (Finset.mem_sdiff.mp hyRest).2
      have hzSmall := (Finset.mem_sdiff.mp hzRest).2
      let blockₓ := insert x small
      let blockᵧ := insert y small
      let block_z := insert z small
      have block_mem (q : Fin n) (hqAvailable : q ∈ available)
          (hqSmall : q ∉ small) :
          insert q small ∈ probes ∧ small ⊆ insert q small := by
        have hpotential : insert q small ∈ available.powersetCard 4 := by
          apply Finset.mem_powersetCard.mpr
          exact ⟨Finset.insert_subset hqAvailable hsmallSub, by
            rw [Finset.card_insert_of_notMem hqSmall, hsmallCard]⟩
        have hfiber : insert q small ∈
            CarrierTouchingProbeFiber567 χ ambient first second a b third := by
          rw [hfiberEq]
          exact hpotential
        exact ⟨by
          exact (Finset.mem_filter.mp hfiber).1,
          Finset.subset_insert q small⟩
      have hxBlock := block_mem x hxAvailable hxSmall
      have hyBlock := block_mem y hyAvailable hySmall
      have hzBlock := block_mem z hzAvailable hzSmall
      have hblockxy : blockₓ ≠ blockᵧ := by
        intro heq
        exact hxy ((Finset.insert_inj hxSmall).mp heq)
      have hblockxz : blockₓ ≠ block_z := by
        intro heq
        exact hxz ((Finset.insert_inj hxSmall).mp heq)
      have hblockyz : blockᵧ ≠ block_z := by
        intro heq
        exact hyz ((Finset.insert_inj hySmall).mp heq)
      have hthree : 3 ≤ (probes.filter (fun candidate ↦ small ⊆ candidate)).card := by
        have htwo : 2 < (probes.filter
            (fun candidate ↦ small ⊆ candidate)).card :=
          Finset.two_lt_card_iff.mpr ⟨blockₓ, blockᵧ, block_z,
          Finset.mem_filter.mpr ⟨hxBlock.1, hxBlock.2⟩,
          Finset.mem_filter.mpr ⟨hyBlock.1, hyBlock.2⟩,
          Finset.mem_filter.mpr ⟨hzBlock.1, hzBlock.2⟩,
          hblockxy, hblockxz, hblockyz⟩
        omega
      have hsmallResidual : small ⊆ residual := by
        exact hsmallSub.trans (Finset.sdiff_subset.trans Finset.Subset.rfl)
      have hthirtyOne :=
        thirty_one_le_card_badResidualFourBlocks567_of_three_through_triple
          hescape.1 hnoStrongResidual hsmallResidual hsmallCard
          (by simpa [probes, residual] using hthree)
      have : 31 ≤ probes.card := by simpa [probes, residual] using hthirtyOne
      omega

end ErdosSzekeres

end
