module

public import ErdosSzekeres.StructuralChargingResidualProbeReuse567

@[expose] public section

/-!
# Carrier-only collapse for the state-567 residual probes

The residual triple cover sharpens the existing probe-reuse dichotomy.  In
the absence of a same-occupancy collision, three distinct incident witnesses
cannot occur.  Hitting two nonempty residual traces by one residual triple
therefore forces one incident witness to have empty residual trace.
-/

namespace ErdosSzekeres

/-- The thirty-probe dichotomy sharpens to a carrier-only witness: unless two
distinct incident witnesses have the same coarse occupancy, one incident
strong six has empty intersection with the ten-point residual. -/
theorem exists_sameOccupancyCollision_or_carrierOnlyWitness567
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
        (third ∩ (ambient \ (first ∪ second))).card = 0 := by
  classical
  let residual := ambient \ (first ∪ second)
  let witnesses := CarrierTouchingProbeWitnesses567 χ ambient first second a b
  have hresidualCard : residual.card = 10 := by
    simpa [residual] using hescape.1
  by_cases hcollision :
      ∃ third₁ ∈ witnesses, ∃ third₂ ∈ witnesses,
        third₁ ≠ third₂ ∧
          SameCarrierTouchingOccupancy567 first second third₁ third₂
  · exact Or.inl hcollision
  right
  have hnoStrongResidual : ¬ContainsStrongPolygonSet χ residual 7 := by
    intro hstrong
    exact hnoStrongSeven
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.sdiff_subset)
  have witness_mem {block third : Finset (Fin n)}
      (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
        a b block third) : third ∈ witnesses := by
    change third ∈ (ambient.powersetCard 6).filter
      (fun candidate ↦ ∃ probe,
        IsCarrierTouchingProbeWitness567 χ ambient first second
          a b probe candidate)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr
        ⟨hincident.2.1.trans Finset.sdiff_subset, hincident.2.2.1⟩,
        block, hincident⟩
  have witness_avoids_block {block third : Finset (Fin n)}
      (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
        a b block third) : Disjoint third block := by
    apply Finset.disjoint_left.mpr
    intro x hxThird hxBlock
    have hxAvoid := Finset.mem_sdiff.mp (hincident.2.1 hxThird)
    exact hxAvoid.2 (by simp [hxBlock])
  rcases exists_sameOccupancyCollision_or_threeCarrierWitness567
      hmutual hescape hnoStrongSeven ha hb with hcollision' | hheavy
  · exact (hcollision hcollision').elim
  obtain ⟨block₁, third₁, hincident₁, _hheavy⟩ := hheavy
  by_cases hzero₁ : (third₁ ∩ residual).card = 0
  · exact ⟨block₁, third₁, hincident₁, by simpa [residual] using hzero₁⟩
  have htrace₁Nonempty : (third₁ ∩ residual).Nonempty :=
    Finset.card_pos.mp (Nat.pos_of_ne_zero hzero₁)
  obtain ⟨x₁, hx₁Trace⟩ := htrace₁Nonempty
  have hx₁Residual : x₁ ∈ residual := (Finset.mem_inter.mp hx₁Trace).2
  obtain ⟨triple₁, hx₁Triple, htriple₁Sub, htriple₁Card⟩ :=
    Finset.exists_subsuperset_card_eq (s := {x₁}) (t := residual) (n := 3)
      (by simpa using hx₁Residual) (by simp) (by omega)
  obtain ⟨block₂, hblock₂, htriple₁Block⟩ :=
    badResidualFourBlocks567_covers_three hescape.1 hnoStrongResidual
      htriple₁Sub htriple₁Card
  obtain ⟨third₂, hincident₂⟩ :=
    hescape.badProbe_has_incident_witness ha hb
      (by simpa [residual] using hblock₂)
  have hx₁Block₂ : x₁ ∈ block₂ :=
    htriple₁Block (hx₁Triple (by simp))
  have hx₁NotThird₂ : x₁ ∉ third₂ := fun hx ↦
    Finset.disjoint_left.mp (witness_avoids_block hincident₂) hx hx₁Block₂
  have hthird₁NeThird₂ : third₁ ≠ third₂ := by
    intro heq
    exact hx₁NotThird₂ (heq ▸ (Finset.mem_inter.mp hx₁Trace).1)
  by_cases hzero₂ : (third₂ ∩ residual).card = 0
  · exact ⟨block₂, third₂, hincident₂, by simpa [residual] using hzero₂⟩
  have htrace₂Nonempty : (third₂ ∩ residual).Nonempty :=
    Finset.card_pos.mp (Nat.pos_of_ne_zero hzero₂)
  obtain ⟨x₂, hx₂Trace⟩ := htrace₂Nonempty
  have hx₂Residual : x₂ ∈ residual := (Finset.mem_inter.mp hx₂Trace).2
  have hx₁NeX₂ : x₁ ≠ x₂ := by
    intro heq
    exact hx₁NotThird₂ (heq ▸ (Finset.mem_inter.mp hx₂Trace).1)
  let pair : Finset (Fin n) := {x₁, x₂}
  have hpairSub : pair ⊆ residual := by
    intro x hx
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hx₁Residual
    · exact hx₂Residual
  have hpairCard : pair.card = 2 := by
    simp [pair, hx₁NeX₂]
  obtain ⟨triple₂, hpairTriple, htriple₂Sub, htriple₂Card⟩ :=
    Finset.exists_subsuperset_card_eq (s := pair) (t := residual) (n := 3)
      hpairSub (by simp [hpairCard]) (by omega)
  obtain ⟨block₃, hblock₃, htriple₂Block⟩ :=
    badResidualFourBlocks567_covers_three hescape.1 hnoStrongResidual
      htriple₂Sub htriple₂Card
  obtain ⟨third₃, hincident₃⟩ :=
    hescape.badProbe_has_incident_witness ha hb
      (by simpa [residual] using hblock₃)
  have hx₁Block₃ : x₁ ∈ block₃ :=
    htriple₂Block (hpairTriple (by simp [pair]))
  have hx₂Block₃ : x₂ ∈ block₃ :=
    htriple₂Block (hpairTriple (by simp [pair]))
  have hx₁NotThird₃ : x₁ ∉ third₃ := fun hx ↦
    Finset.disjoint_left.mp (witness_avoids_block hincident₃) hx hx₁Block₃
  have hx₂NotThird₃ : x₂ ∉ third₃ := fun hx ↦
    Finset.disjoint_left.mp (witness_avoids_block hincident₃) hx hx₂Block₃
  have hthird₁NeThird₃ : third₁ ≠ third₃ := by
    intro heq
    exact hx₁NotThird₃ (heq ▸ (Finset.mem_inter.mp hx₁Trace).1)
  have hthird₂NeThird₃ : third₂ ≠ third₃ := by
    intro heq
    exact hx₂NotThird₃ (heq ▸ (Finset.mem_inter.mp hx₂Trace).1)
  have hmem₁ := witness_mem hincident₁
  have hmem₂ := witness_mem hincident₂
  have hmem₃ := witness_mem hincident₃
  exfalso
  rcases hincident₁.2.2.2.2 with hone₁ | htwo₁ <;>
    rcases hincident₂.2.2.2.2 with hone₂ | htwo₂ <;>
    rcases hincident₃.2.2.2.2 with hone₃ | htwo₃
  all_goals
    apply hcollision
  · exact ⟨third₁, hmem₁, third₂, hmem₂, hthird₁NeThird₂,
      Or.inl ⟨hone₁, hone₂⟩⟩
  · exact ⟨third₁, hmem₁, third₂, hmem₂, hthird₁NeThird₂,
      Or.inl ⟨hone₁, hone₂⟩⟩
  · exact ⟨third₁, hmem₁, third₃, hmem₃, hthird₁NeThird₃,
      Or.inl ⟨hone₁, hone₃⟩⟩
  · exact ⟨third₂, hmem₂, third₃, hmem₃, hthird₂NeThird₃,
      Or.inr ⟨htwo₂, htwo₃⟩⟩
  · exact ⟨third₂, hmem₂, third₃, hmem₃, hthird₂NeThird₃,
      Or.inl ⟨hone₂, hone₃⟩⟩
  · exact ⟨third₁, hmem₁, third₃, hmem₃, hthird₁NeThird₃,
      Or.inr ⟨htwo₁, htwo₃⟩⟩
  · exact ⟨third₁, hmem₁, third₂, hmem₂, hthird₁NeThird₂,
      Or.inr ⟨htwo₁, htwo₂⟩⟩
  · exact ⟨third₁, hmem₁, third₂, hmem₂, hthird₁NeThird₂,
      Or.inr ⟨htwo₁, htwo₂⟩⟩

/-- A carrier-only incident witness is contained in the two original
carriers, touches both of them, and has one of the five positive overlap
splits summing to six. -/
theorem IsCarrierTouchingProbeWitness567.carrierOnly_normalization
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second block third : Finset (Fin n)} {a b : Fin n}
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second)
    (ha : a ∈ first) (hb : b ∈ second)
    (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
      a b block third)
    (hzero : (third ∩ (ambient \ (first ∪ second))).card = 0) :
    third ⊆ first ∪ second ∧
      HasPairEscapeOccupancy first second third .twoCarrier ∧
      1 ≤ (third ∩ first).card ∧ (third ∩ first).card ≤ 5 ∧
      1 ≤ (third ∩ second).card ∧ (third ∩ second).card ≤ 5 ∧
      (third ∩ first).card + (third ∩ second).card = 6 ∧
      (((third ∩ first).card = 1 ∧ (third ∩ second).card = 5) ∨
        ((third ∩ first).card = 2 ∧ (third ∩ second).card = 4) ∨
        ((third ∩ first).card = 3 ∧ (third ∩ second).card = 3) ∨
        ((third ∩ first).card = 4 ∧ (third ∩ second).card = 2) ∨
        ((third ∩ first).card = 5 ∧ (third ∩ second).card = 1)) := by
  classical
  let residual := ambient \ (first ∪ second)
  have hthirdAmbient : third ⊆ ambient :=
    hincident.2.1.trans Finset.sdiff_subset
  have hthirdCarrier : third ⊆ first ∪ second := by
    intro x hxThird
    by_contra hxCarrier
    have hxResidual : x ∈ residual :=
      Finset.mem_sdiff.mpr ⟨hthirdAmbient hxThird, hxCarrier⟩
    have hpositive : 0 < (third ∩ residual).card :=
      Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxThird, hxResidual⟩⟩
    have : (third ∩ residual).card = 0 := by simpa [residual] using hzero
    omega
  have haNotThird : a ∉ third := by
    intro haThird
    have haAvoid := (Finset.mem_sdiff.mp (hincident.2.1 haThird)).2
    exact haAvoid (by simp)
  have hbNotThird : b ∉ third := by
    intro hbThird
    have hbAvoid := (Finset.mem_sdiff.mp (hincident.2.1 hbThird)).2
    exact hbAvoid (by simp)
  have hmeetFirst : ¬Disjoint third first := by
    intro hdisjoint
    have hthirdSecond : third ⊆ second := by
      intro x hxThird
      rcases Finset.mem_union.mp (hthirdCarrier hxThird) with hxFirst | hxSecond
      · exact (Finset.disjoint_left.mp hdisjoint hxThird hxFirst).elim
      · exact hxSecond
    have heq : third = second := by
      apply Finset.eq_of_subset_of_card_le hthirdSecond
      rw [hmutual.2.2.1, hincident.2.2.1]
    apply hbNotThird
    rw [heq]
    exact hb
  have hmeetSecond : ¬Disjoint third second := by
    intro hdisjoint
    have hthirdFirst : third ⊆ first := by
      intro x hxThird
      rcases Finset.mem_union.mp (hthirdCarrier hxThird) with hxFirst | hxSecond
      · exact hxFirst
      · exact (Finset.disjoint_left.mp hdisjoint hxThird hxSecond).elim
    have heq : third = first := by
      apply Finset.eq_of_subset_of_card_le hthirdFirst
      rw [hmutual.2.1, hincident.2.2.1]
    apply haNotThird
    rw [heq]
    exact ha
  have hfirstPositive : 1 ≤ (third ∩ first).card := by
    obtain ⟨x, hxThird, hxFirst⟩ := Finset.not_disjoint_iff.mp hmeetFirst
    exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxThird, hxFirst⟩⟩
  have hsecondPositive : 1 ≤ (third ∩ second).card := by
    obtain ⟨x, hxThird, hxSecond⟩ := Finset.not_disjoint_iff.mp hmeetSecond
    exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxThird, hxSecond⟩⟩
  have hfirstErase : third ∩ first ⊆ first.erase a := by
    intro x hx
    have hxData := Finset.mem_inter.mp hx
    exact Finset.mem_erase.mpr ⟨fun hxa ↦ haNotThird (hxa ▸ hxData.1), hxData.2⟩
  have hsecondErase : third ∩ second ⊆ second.erase b := by
    intro x hx
    have hxData := Finset.mem_inter.mp hx
    exact Finset.mem_erase.mpr ⟨fun hxb ↦ hbNotThird (hxb ▸ hxData.1), hxData.2⟩
  have hfirstLe : (third ∩ first).card ≤ 5 := by
    have hle := Finset.card_le_card hfirstErase
    rw [Finset.card_erase_of_mem ha, hmutual.2.1] at hle
    omega
  have hsecondLe : (third ∩ second).card ≤ 5 := by
    have hle := Finset.card_le_card hsecondErase
    rw [Finset.card_erase_of_mem hb, hmutual.2.2.1] at hle
    omega
  have hdisjointInter : Disjoint (third ∩ first) (third ∩ second) := by
    apply Finset.disjoint_left.mpr
    intro x hxFirst hxSecond
    exact Finset.disjoint_left.mp hmutual.1
      (Finset.mem_inter.mp hxFirst).2 (Finset.mem_inter.mp hxSecond).2
  have hunionEq : (third ∩ first) ∪ (third ∩ second) = third := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).1
      · exact (Finset.mem_inter.mp hx).1
    · intro hxThird
      rcases Finset.mem_union.mp (hthirdCarrier hxThird) with hxFirst | hxSecond
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxThird, hxFirst⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxThird, hxSecond⟩)
  have hsum : (third ∩ first).card + (third ∩ second).card = 6 := by
    rw [← Finset.card_union_of_disjoint hdisjointInter, hunionEq,
      hincident.2.2.1]
  refine ⟨hthirdCarrier, ⟨hmeetFirst, hmeetSecond⟩,
    hfirstPositive, hfirstLe, hsecondPositive, hsecondLe, hsum, ?_⟩
  omega

end ErdosSzekeres

end
