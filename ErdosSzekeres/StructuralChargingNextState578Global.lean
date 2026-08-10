module

public import ErdosSzekeres.StructuralChargingNextState578DeficitDensity

@[expose] public section

/-!
# Global state-578 carriers and residual escape

This file aligns the tight six-column/deletion-density package with the
all-spine expanding carrier on one private-star witness. It also formalizes
the exact limitation of carrier iteration and the residual-boundary consumer
that a future color-sensitive cover theorem would close.
-/

namespace ErdosSzekeres

/-- An expanding carrier replaces rather than contains the old canonical
carrier. Equal cardinality bounds and the escaping cup vertex make inclusion
in the proposed new carrier impossible. -/
theorem ExpandingFullSpineCarrier578.not_oldCarrier_subset_new
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {system : FullSpineLocalBoundarySystem578 joint}
    (expanding : ExpandingFullSpineCarrier578 system) :
    ¬joint.carrierAtFullSpine expanding.spine_mem ⊆
      expanding.spine ∪ expanding.cup := by
  intro hsub
  have heq : joint.carrierAtFullSpine expanding.spine_mem =
      expanding.spine ∪ expanding.cup :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [joint.carrierAtFullSpine_card expanding.spine_mem]
      exact expanding.expandedCarrier_card)
  obtain ⟨x, hx⟩ := expanding.outside_oldCarrier
  have hxData := Finset.mem_sdiff.mp hx
  apply hxData.2
  rw [heq]
  exact Finset.mem_union_right expanding.spine hxData.1

/-- The sharper same-witness form: the exact tight reduction and the
expanding full-spine carrier can be constructed on one common private-star
state. -/
theorem exists_fourthDisjointCup_or_sameJointGlobalState578Packages_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hroot : HasDeepBelowSplit χ {q} reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    (∃ state : SevenWitnessRegenerationPacking578 χ reservoir,
      ∃ cup, cup ∈ capWitnesses χ.dual reservoir 4 ∧
        Disjoint cup state.packing.cupSupport) ∨
    ∃ joint : PrivateCupStarSixCapState578 χ reservoir,
      (2 ≤ (joint.saturation.state.packing.fullCupSpines
          joint.ledger.transversal).card ∨
        Nonempty (TightDeficitDensityReduction578 joint)) ∧
      ∃ system : FullSpineLocalBoundarySystem578 joint,
        Nonempty (ExpandingFullSpineCarrier578 system) := by
  rcases
      exists_fourthDisjointCup_or_twoFullSpines_or_tightDeficitDensityReduction_at_32
        h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong with
    hfourth | ⟨joint, htight⟩
  · exact Or.inl hfourth
  · right
    refine ⟨joint, htight, ?_⟩
    have hnoCupReservoir : ¬ContainsCupSet χ reservoir 5 := by
      intro hcup
      exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup
        Finset.subset_union_right)
    obtain ⟨system⟩ :=
      exists_fullSpineLocalBoundarySystem578 joint hnoCupReservoir
    exact ⟨system, system.exists_expandingFullSpineCarrier
      hreservoir hcard hnoCap hnoStrong⟩

/-- An assignment of one seven-vertex carrier to every full selected spine,
whose assigned carriers collectively contain the full residual cup family. -/
structure FullSpineSevenCarrierCover578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) where
  carrierFor :
    {spine : Finset (Fin n) // spine ∈
      joint.saturation.state.packing.fullCupSpines
        joint.ledger.transversal} → Finset (Fin n)
  carrierFor_sub : ∀ spine, carrierFor spine ⊆ support
  carrierFor_card : ∀ spine, (carrierFor spine).card ≤ 7
  covers_residual : ∀ cup,
    cup ∈ joint.ledger.residualCupFamily
      (joint.saturation.state.packing.fullCupProtected
        joint.ledger.transversal) →
    ∃ spine, cup ⊆ carrierFor spine

/-- A seven-carrier cover gives a local three-boundary on each carrier; their
union is the forbidden `3r` residual boundary. -/
noncomputable def FullSpineSevenCarrierCover578.toFullSpineResidualBoundary
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (cover : FullSpineSevenCarrierCover578 joint)
    (hnoCup : ¬ContainsCupSet χ support 5) :
    FullSpineResidualBoundary578 joint := by
  classical
  let fullSpines := joint.saturation.state.packing.fullCupSpines
    joint.ledger.transversal
  have hexists : ∀ spine : fullSpines,
      ∃ boundary : Finset (Fin n),
        boundary ⊆ cover.carrierFor spine ∧
        boundary.card ≤ 3 ∧
        ∀ cup, cup ∈ capWitnesses χ.dual support 4 →
          cup ⊆ cover.carrierFor spine → ¬Disjoint cup boundary := by
    intro spine
    rcases atMostSeven_fourCupFamily_has_threeTransversal_or_cupFive
        (cover.carrierFor_card spine) with
      hcupFive | ⟨boundary, hboundarySub, hboundaryCard, hhits⟩
    · exact (hnoCup (FinsetPolygon.ContainsCupSet.mono hcupFive
        (cover.carrierFor_sub spine))).elim
    · refine ⟨boundary, hboundarySub, hboundaryCard, ?_⟩
      intro cup hcup hcupSub
      have hcupData := mem_capWitnesses.mp hcup
      exact hhits.2 cup
        (mem_capWitnesses.mpr ⟨hcupSub, hcupData.2⟩)
  choose boundaryFor hboundarySub hboundaryCard hhits using hexists
  let boundary := fullSpines.attach.biUnion fun spine ↦ boundaryFor spine
  refine {
    boundary := boundary
    boundary_sub := ?_
    boundary_card := ?_
    hits := ?_
  }
  · dsimp [boundary]
    rw [Finset.biUnion_subset_iff_forall_subset]
    intro spine _
    exact (hboundarySub spine).trans (cover.carrierFor_sub spine)
  · have hle := Finset.card_biUnion_le_card_mul fullSpines.attach
        boundaryFor 3 (by
          intro spine _
          exact hboundaryCard spine)
    dsimp [boundary]
    calc
      (fullSpines.attach.biUnion boundaryFor).card ≤
          fullSpines.attach.card * 3 := hle
      _ = 3 * fullSpines.card := by rw [Finset.card_attach]; omega
  · intro cup hcup
    obtain ⟨spine, hcupSub⟩ := cover.covers_residual cup hcup
    have hcupWitness :=
      (joint.ledger.mem_residualCupFamily.mp hcup).1
    have hlocal := hhits spine cup hcupWitness hcupSub
    have hlocalSub : boundaryFor spine ⊆ boundary := by
      have hsub := Finset.subset_biUnion_of_mem boundaryFor
        (Finset.mem_attach fullSpines spine)
      simpa [boundary] using hsub
    intro hdisjoint
    exact hlocal (Disjoint.mono_right hlocalSub hdisjoint)

/-- Under the exact 32-point density hypotheses, such a carrier cover is
impossible. -/
theorem FullSpineSevenCarrierCover578.false_of_colorDualLower_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    (cover : FullSpineSevenCarrierCover578 joint)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCup : ¬ContainsCupSet χ reservoir 5)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    False :=
  (cover.toFullSpineResidualBoundary hnoCup).false_of_colorDualLower_at_32
    hreservoir hcard hnoCap hnoStrong

/-- In the tight branch, no single residual row can be promoted to an
absorbing seven-carrier: a local three-boundary on its union with the spine is
missed by another residual cup outside that union. -/
theorem PrivateCupStarSixCapState578.exists_escape_from_any_residualSeed_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ reservoir)
    (seed : joint.ResidualCupIndex)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ reservoir 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1) :
    ∃ boundary cup,
      boundary ⊆ joint.star.spine ∪ seed.1 ∧
      boundary.card ≤ 3 ∧
      cup ∈ joint.ledger.residualCupFamily
        (joint.saturation.state.packing.fullCupProtected
          joint.ledger.transversal) ∧
      Disjoint cup boundary ∧
      ¬cup ⊆ joint.star.spine ∪ seed.1 := by
  have hseedWitness :=
    (joint.ledger.mem_residualCupFamily.mp seed.2).1
  have hseedCard := (mem_capWitnesses.mp hseedWitness).2.1
  have hmeet := joint.residualCup_meets_spine_of_card_eq_one hone seed.2
  have hinterPos : 1 ≤ (joint.star.spine ∩ seed.1).card :=
    Finset.card_pos.mpr (by
      obtain ⟨x, hxSeed, hxSpine⟩ := Finset.not_disjoint_iff.mp hmeet
      exact ⟨x, Finset.mem_inter.mpr ⟨hxSpine, hxSeed⟩⟩)
  have hformula := Finset.card_union_add_card_inter
    joint.star.spine seed.1
  have hcarrierCard : (joint.star.spine ∪ seed.1).card ≤ 7 := by
    rw [joint.star.spine_card, hseedCard] at hformula
    omega
  have hcarrierSub : joint.star.spine ∪ seed.1 ⊆ reservoir :=
    Finset.union_subset
      (mem_capWitnesses.mp joint.star.spine_mem).1
      (mem_capWitnesses.mp hseedWitness).1
  rcases atMostSeven_fourCupFamily_has_threeTransversal_or_cupFive
      hcarrierCard with
    hcupFive | ⟨boundary, hboundarySub, hboundaryCard, hhits⟩
  · exact (hnoCup (FinsetPolygon.ContainsCupSet.mono hcupFive
      hcarrierSub)).elim
  · have hlocalHits : ∀ cup,
        cup ∈ capWitnesses χ.dual reservoir 4 →
        cup ⊆ joint.star.spine ∪ seed.1 →
        ¬Disjoint cup boundary := by
      intro cup hcup hcupSub
      have hcupData := mem_capWitnesses.mp hcup
      exact hhits.2 cup
        (mem_capWitnesses.mpr ⟨hcupSub, hcupData.2⟩)
    obtain ⟨cup, hcupResidual, hdisjoint, hescapes⟩ :=
      exists_escapingResidualCup578_of_localBoundary joint
        hreservoir hcard hnoCap hnoStrong hone hcarrierSub
        hboundarySub hboundaryCard hlocalHits
    exact ⟨boundary, cup, hboundarySub, hboundaryCard,
      hcupResidual, hdisjoint, hescapes⟩

end ErdosSzekeres

end
