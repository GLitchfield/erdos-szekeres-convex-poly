module

public import ErdosSzekeres.StructuralChargingResidualProbeCarrierOnly567

@[expose] public section

/-!
# Carrier-only omission rectangles for state 567

This file packages the universal-anchor consequence of the carrier-only
probe theorem as a purely structural result.
-/

namespace ErdosSzekeres

/-- A carrier-only witness set, with its anchors and incident bad probe kept
existential rather than stored as part of the finite family. -/
def IsCarrierOnlyProbeWitnessSet567 {n : ℕ} (χ : TripleColoring n)
    (ambient first second third : Finset (Fin n)) : Prop :=
  ∃ a ∈ first, ∃ b ∈ second, ∃ block,
    IsCarrierTouchingProbeWitness567 χ ambient first second a b block third ∧
      (third ∩ (ambient \ (first ∪ second))).card = 0

/-- The choice-free finite family of all carrier-only probe witness sets. -/
noncomputable def CarrierOnlyProbeWitnessSets567 {n : ℕ}
    (χ : TripleColoring n) (ambient first second : Finset (Fin n)) :
    Finset (Finset (Fin n)) := by
  classical
  exact (ambient.powersetCard 6).filter
    (IsCarrierOnlyProbeWitnessSet567 χ ambient first second)

/-- The anchor pairs omitted by a carrier-only witness. -/
def CarrierOnlyOmissionRectangle567 {n : ℕ}
    (first second third : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (first \ third).product (second \ third)

/-- Exact proof-side normalization of a carrier-only strong-six witness. -/
def IsNormalizedCarrierOnlyWitnessSet567 {n : ℕ} (χ : TripleColoring n)
    (first second third : Finset (Fin n)) : Prop :=
  third.card = 6 ∧ IsStrongPolygonSet χ third ∧
    third ⊆ first ∪ second ∧
    HasPairEscapeOccupancy first second third .twoCarrier ∧
    1 ≤ (third ∩ first).card ∧ (third ∩ first).card ≤ 5 ∧
    1 ≤ (third ∩ second).card ∧ (third ∩ second).card ≤ 5 ∧
    (third ∩ first).card + (third ∩ second).card = 6 ∧
    (((third ∩ first).card = 1 ∧ (third ∩ second).card = 5) ∨
      ((third ∩ first).card = 2 ∧ (third ∩ second).card = 4) ∨
      ((third ∩ first).card = 3 ∧ (third ∩ second).card = 3) ∨
      ((third ∩ first).card = 4 ∧ (third ∩ second).card = 2) ∨
      ((third ∩ first).card = 5 ∧ (third ∩ second).card = 1))

/-- A normalized finite family whose omission rectangles cover the anchor
product and are pairwise edge-disjoint. -/
def IsCarrierOnlyOmissionRectangleSystem567 {n : ℕ} (χ : TripleColoring n)
    (first second : Finset (Fin n)) (witnesses : Finset (Finset (Fin n))) :
    Prop :=
  (∀ third ∈ witnesses,
      IsNormalizedCarrierOnlyWitnessSet567 χ first second third) ∧
    (∀ a ∈ first, ∀ b ∈ second, ∃ third ∈ witnesses,
      (a, b) ∈ CarrierOnlyOmissionRectangle567 first second third) ∧
    (∀ third₁ ∈ witnesses, ∀ third₂ ∈ witnesses, third₁ ≠ third₂ →
      Disjoint (CarrierOnlyOmissionRectangle567 first second third₁)
        (CarrierOnlyOmissionRectangle567 first second third₂))

/-- No anchor pair admits two distinct incident witnesses with the same coarse
carrier-touching occupancy. -/
def HasNoCarrierTouchingSameOccupancyCollision567 {n : ℕ}
    (χ : TripleColoring n) (ambient first second : Finset (Fin n)) : Prop :=
  ∀ a ∈ first, ∀ b ∈ second,
    ¬(∃ third₁ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
      ∃ third₂ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
        third₁ ≠ third₂ ∧
          SameCarrierTouchingOccupancy567 first second third₁ third₂)

/-- In the no-collision branch, the carrier-only witnesses form a normalized
omission-rectangle system. -/
theorem exists_carrierOnlyOmissionRectangleSystem567_of_noCollision
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second : Finset (Fin n)}
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second)
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ ambient 7)
    (hnoCollision :
      HasNoCarrierTouchingSameOccupancyCollision567 χ ambient first second) :
    ∃ witnesses : Finset (Finset (Fin n)),
      witnesses = CarrierOnlyProbeWitnessSets567 χ ambient first second ∧
        IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses := by
  classical
  let witnesses := CarrierOnlyProbeWitnessSets567 χ ambient first second
  have incident_mem {a b : Fin n} {block third : Finset (Fin n)}
      (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
        a b block third) :
      third ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b := by
    change third ∈ (ambient.powersetCard 6).filter
      (fun candidate ↦ ∃ probe,
        IsCarrierTouchingProbeWitness567 χ ambient first second
          a b probe candidate)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr
        ⟨hincident.2.1.trans Finset.sdiff_subset, hincident.2.2.1⟩,
        block, hincident⟩
  have reuse_incident {a₀ b₀ a b : Fin n}
      {block third : Finset (Fin n)}
      (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
        a₀ b₀ block third)
      (haNot : a ∉ third) (hbNot : b ∉ third) :
      IsCarrierTouchingProbeWitness567 χ ambient first second
        a b block third := by
    have hsub : third ⊆ ambient \ insert a (insert b block) := by
      intro x hxThird
      have hold := Finset.mem_sdiff.mp (hincident.2.1 hxThird)
      have hxNotBlock : x ∉ block := by
        intro hxBlock
        exact hold.2 (by simp [hxBlock])
      have hxNeA : x ≠ a := by
        intro hxa
        exact haNot (hxa ▸ hxThird)
      have hxNeB : x ≠ b := by
        intro hxb
        exact hbNot (hxb ▸ hxThird)
      exact Finset.mem_sdiff.mpr ⟨hold.1, by simp [hxNeA, hxNeB, hxNotBlock]⟩
    exact ⟨hincident.1, hsub, hincident.2.2.1,
      hincident.2.2.2.1, hincident.2.2.2.2⟩
  refine ⟨witnesses, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro third hthird
    change third ∈ (ambient.powersetCard 6).filter
      (IsCarrierOnlyProbeWitnessSet567 χ ambient first second) at hthird
    obtain ⟨_, a, ha, b, hb, block, hincident, hzero⟩ :=
      Finset.mem_filter.mp hthird
    have hnormal := hincident.carrierOnly_normalization hmutual ha hb hzero
    exact ⟨hincident.2.2.1, hincident.2.2.2.1,
      hnormal.1, hnormal.2.1, hnormal.2.2⟩
  · intro a ha b hb
    rcases exists_sameOccupancyCollision_or_carrierOnlyWitness567
        hmutual hescape hnoStrongSeven ha hb with hcollision | hcarrier
    · exact (hnoCollision a ha b hb hcollision).elim
    · obtain ⟨block, third, hincident, hzero⟩ := hcarrier
      have haNot : a ∉ third := by
        intro haThird
        exact (Finset.mem_sdiff.mp (hincident.2.1 haThird)).2 (by simp)
      have hbNot : b ∉ third := by
        intro hbThird
        exact (Finset.mem_sdiff.mp (hincident.2.1 hbThird)).2 (by simp)
      refine ⟨third, ?_, ?_⟩
      · change third ∈ (ambient.powersetCard 6).filter
          (IsCarrierOnlyProbeWitnessSet567 χ ambient first second)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powersetCard.mpr
            ⟨hincident.2.1.trans Finset.sdiff_subset, hincident.2.2.1⟩,
            a, ha, b, hb, block, hincident, hzero⟩
      · simp [CarrierOnlyOmissionRectangle567, ha, hb, haNot, hbNot]
  · intro third₁ hthird₁ third₂ hthird₂ hne
    apply Finset.disjoint_left.mpr
    intro pair hpair₁ hpair₂
    obtain ⟨a, b⟩ := pair
    have hpair₁' :
        (a ∈ first ∧ a ∉ third₁) ∧ (b ∈ second ∧ b ∉ third₁) := by
      simpa [CarrierOnlyOmissionRectangle567] using hpair₁
    have hpair₂' :
        (a ∈ first ∧ a ∉ third₂) ∧ (b ∈ second ∧ b ∉ third₂) := by
      simpa [CarrierOnlyOmissionRectangle567] using hpair₂
    obtain ⟨⟨ha, haNot₁⟩, ⟨hb, hbNot₁⟩⟩ := hpair₁'
    obtain ⟨⟨_, haNot₂⟩, ⟨_, hbNot₂⟩⟩ := hpair₂'
    change third₁ ∈ (ambient.powersetCard 6).filter
      (IsCarrierOnlyProbeWitnessSet567 χ ambient first second) at hthird₁
    change third₂ ∈ (ambient.powersetCard 6).filter
      (IsCarrierOnlyProbeWitnessSet567 χ ambient first second) at hthird₂
    obtain ⟨_, a₁, ha₁, b₁, hb₁, block₁, hincident₁, hzero₁⟩ :=
      Finset.mem_filter.mp hthird₁
    obtain ⟨_, a₂, ha₂, b₂, hb₂, block₂, hincident₂, hzero₂⟩ :=
      Finset.mem_filter.mp hthird₂
    have hreused₁ := reuse_incident hincident₁ haNot₁ hbNot₁
    have hreused₂ := reuse_incident hincident₂ haNot₂ hbNot₂
    have htwo₁ :=
      (hincident₁.carrierOnly_normalization hmutual ha₁ hb₁ hzero₁).2.1
    have htwo₂ :=
      (hincident₂.carrierOnly_normalization hmutual ha₂ hb₂ hzero₂).2.1
    exact hnoCollision a ha b hb
      ⟨third₁, incident_mem hreused₁, third₂, incident_mem hreused₂,
        hne, Or.inr ⟨htwo₁, htwo₂⟩⟩

end ErdosSzekeres

end
