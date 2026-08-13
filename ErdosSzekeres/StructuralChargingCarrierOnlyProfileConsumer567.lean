module

public import ErdosSzekeres.Mixed567AllOrder

@[expose] public section

/-!
# Consuming the mixed carrier-only omission profile at state 567

The rectangle system has exactly two possible area profiles.  The all-order
mixed certificate eliminates the `4 + 2` profile under the ambient
cap-five/cup-six/strong-seven exclusions, leaving the balanced four-grid.
-/

namespace ErdosSzekeres

/-- The exact no-collision branch of the state-567 probe system reduces to the
balanced four-by-nine omission profile. -/
theorem packedInternalPair_has_balancedGrid567_of_noCollision
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second : Finset (Fin n)}
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second)
    (hpairSub : first ∪ second ⊆ ambient)
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5)
    (hnoCup : ¬ContainsCupSet χ ambient 6)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ ambient 7)
    (hnoCollision :
      HasNoCarrierTouchingSameOccupancyCollision567 χ ambient first second) :
    ∃ witnesses : Finset (Finset (Fin n)),
      witnesses = CarrierOnlyProbeWitnessSets567 χ ambient first second ∧
        IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses ∧
        IsFourDisjointThreeByThreeOmissionGrid567 first second witnesses := by
  classical
  obtain ⟨witnesses, hwitnesses, hsystem⟩ :=
    exists_carrierOnlyOmissionRectangleSystem567_of_noCollision
      hmutual hescape hnoStrongSeven hnoCollision
  have hfirstCard : first.card = 6 := hmutual.2.1
  have hsecondCard : second.card = 6 := hmutual.2.2.1
  rcases hsystem.area_profile_dichotomy hfirstCard hsecondCard with
      hbalanced | hmixed
  · exact ⟨witnesses, hwitnesses, hsystem,
      hsystem.fourGrid_of_balanced_area_profile hfirstCard hsecondCard hbalanced⟩
  · have hnormal := hsystem.mixed_normalForm hmixed.1 hmixed.2.1 hmixed.2.2.1
    have htarget := mixedCarrierOnlyOmissionNormalForm_forces_target567
      hsystem hfirstCard hsecondCard hmutual.1 (hone.mono hpairSub) hnormal
    rcases htarget with hcap | hcup | hstrong
    · rcases hcap with ⟨cap, hcapSub, hcapCard, hcapSet⟩
      have hcapSet' : IsCapSet χ cap := by
        intro t hi hj hk
        exact hcapSet t.hij t.hjk hi hj hk
      exact (hnoCap ⟨cap, hcapSub.trans hpairSub, hcapCard, hcapSet'⟩).elim
    · rcases hcup with ⟨cup, hcupSub, hcupCard, hcupSet⟩
      have hcupSet' : IsCupSet χ cup := by
        intro t hi hj hk
        exact hcupSet t.hij t.hjk hi hj hk
      exact (hnoCup ⟨cup, hcupSub.trans hpairSub, hcupCard, hcupSet'⟩).elim
    · exact (hnoStrongSeven
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hpairSub)).elim

/-- Exact frozen first-stage contract: the packed pair yields either a genuine
same-occupancy collision at one anchor pair or the canonical balanced
four-grid.  The mixed profile is eliminated only by the all-order theorem in
`packedInternalPair_has_balancedGrid567_of_noCollision`. -/
theorem packedInternalPair_has_sameOccupancyCollision_or_balancedGrid567
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second : Finset (Fin n)}
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second)
    (hpairSub : first ∪ second ⊆ ambient)
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (hone : OneChangeOn χ ambient)
    (hnoCap : ¬ContainsCapSet χ ambient 5)
    (hnoCup : ¬ContainsCupSet χ ambient 6)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ ambient 7) :
    (∃ a ∈ first, ∃ b ∈ second,
      ∃ third₁ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
        ∃ third₂ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
          third₁ ≠ third₂ ∧
            SameCarrierTouchingOccupancy567 first second third₁ third₂) ∨
      ∃ witnesses : Finset (Finset (Fin n)),
        witnesses = CarrierOnlyProbeWitnessSets567 χ ambient first second ∧
          IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses ∧
          IsFourDisjointThreeByThreeOmissionGrid567 first second witnesses := by
  classical
  by_cases hcollision :
      ∃ a ∈ first, ∃ b ∈ second,
        ∃ third₁ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
          ∃ third₂ ∈ CarrierTouchingProbeWitnesses567 χ ambient first second a b,
            third₁ ≠ third₂ ∧
              SameCarrierTouchingOccupancy567 first second third₁ third₂
  · exact Or.inl hcollision
  · right
    apply packedInternalPair_has_balancedGrid567_of_noCollision
      hmutual hpairSub hescape hone hnoCap hnoCup hnoStrongSeven
    intro a ha b hb hlocal
    exact hcollision ⟨a, ha, b, hb, hlocal⟩

end ErdosSzekeres

end
