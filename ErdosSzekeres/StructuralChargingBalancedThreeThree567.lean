module

public import ErdosSzekeres.StructuralChargingBalancedFiveWay567

@[expose] public section

/-!
# The exact balanced 3+3 state-567 leaf

This file starts the proof-first analysis of the central balanced terminal.  It
uses the full packed context to replace a selected crossing `3+3` strong six by
a mutually obstructed partner and the complete bounded middle-word failure
state.  The remaining color contradiction is intentionally not asserted here.
-/

namespace ErdosSzekeres

/-- A crossing `3+3` witness in the full balanced context has a disjoint packed
partner.  Both polygons have bounded middle words and every directed extension
failure has the existing explicit five-way normalization. -/
theorem PackedElevenElevenOpen567.threeThree_has_bounded_crossing_state_partner
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hopen : PackedElevenElevenOpen567 χ left right)
    (hthree : HasCrossingStrongSixSplit χ left right 3 3) :
    ∃ (first second : Finset (Fin n))
        (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second),
      first ⊆ left ∪ right ∧
      (first ∩ left).card = 3 ∧
      (first ∩ right).card = 3 ∧
      second ⊆ left ∪ right ∧
      StrongSixMiddleWordWeightOneOrTwo χ first hmutual.2.1 ∧
      StrongSixMiddleWordWeightOneOrTwo χ second hmutual.2.2.1 ∧
      HasProperStrongSixCrossingSplit first left right ∧
      HasProperStrongSixCrossingSplit second left right ∧
      ((∀ q ∈ second,
          HasFullyNormalizedCutFailure χ left right first hmutual.2.1 q) ∧
        (∀ q ∈ first,
          HasFullyNormalizedCutFailure χ left right second hmutual.2.2.1 q)) := by
  rcases hopen with ⟨hdisjoint, horder, _hleftCard, _hrightCard,
    _hnoLeftCap, _hnoRightCap, _hone, hnoCapFive, hnoCupSix,
    hnoStrongSeven, hpacking, hnoLeftStrong, hnoRightStrong⟩
  obtain ⟨first, hfirstSub, hfirstCard, hfirstStrong,
      hfirstLeft, hfirstRight⟩ := hthree
  obtain ⟨second, hsecondSub, hmutual, hstate⟩ :=
    packedStrongSix_has_bounded_crossing_state_partner hdisjoint horder
      hfirstSub hfirstCard hfirstStrong hpacking hnoLeftStrong hnoRightStrong
      hnoCapFive hnoCupSix hnoStrongSeven
  exact ⟨first, second, hmutual, hfirstSub, hfirstLeft, hfirstRight,
    hsecondSub, hstate⟩

end ErdosSzekeres

end
