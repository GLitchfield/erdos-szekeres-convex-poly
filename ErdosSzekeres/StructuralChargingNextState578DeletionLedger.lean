module

public import ErdosSzekeres.StructuralChargingNextState578CarrierMatrix

@[expose] public section

/-!
# Cap-vertex deletion residual ledger at state `(5,7,8)`

The exact `32/23` density misses every candidate of cardinality at most nine.
In the tight one-spine state, deleting one vertex from a saturated four-cap
therefore produces a residual four-cup avoiding the other three vertices.
This file records all 24 choices and proves the first sharp multiplicity
diagnostic.  It does not claim that distinct rows alone close state 578.
-/

namespace ErdosSzekeres

/-- One residual four-cup for every vertex deletion in each of the six
saturated four-cap blocks. -/
structure SixCapVertexDeletionResidualLedger578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) where
  cupAt : ∀ j : Fin 6,
    {c : Fin n // c ∈ joint.saturation.capAt j} → joint.ResidualCupIndex
  avoidsOther : ∀ j c,
    Disjoint (cupAt j c).1 ((joint.saturation.capAt j).erase c.1)

/-- Density constructs the complete 24-entry deletion ledger.  The ambient
target exclusions are exactly those already used by the generic state-578
small-boundary escape theorem. -/
theorem exists_sixCapVertexDeletionResidualLedger578_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1) :
    Nonempty (SixCapVertexDeletionResidualLedger578 joint) := by
  classical
  have hprotected := joint.fullCupProtected_eq_spine_of_card_eq_one hone
  have hexists (j : Fin 6)
      (c : {x : Fin n // x ∈ joint.saturation.capAt j}) :
      ∃ cup : joint.ResidualCupIndex,
        Disjoint cup.1 ((joint.saturation.capAt j).erase c.1) := by
    have hboundarySub : (joint.saturation.capAt j).erase c.1 ⊆ reservoir :=
      (Finset.erase_subset _ _).trans
        (mem_capWitnesses.mp (joint.saturation.capAt_mem j)).1
    have hcapCard := (mem_capWitnesses.mp
      (joint.saturation.capAt_mem j)).2.1
    have hboundaryCard : ((joint.saturation.capAt j).erase c.1).card ≤
        3 * (joint.saturation.state.packing.fullCupSpines
          joint.ledger.transversal).card := by
      rw [Finset.card_erase_of_mem c.2, hcapCard, hone]
    obtain ⟨cup, hcup, hdisjoint⟩ :=
      exists_residualCup_disjoint_from_fullSpineBoundary578 joint
        hreservoir hcard hnoCap hnoStrong hboundarySub hboundaryCard
    have hcup' : cup ∈ joint.ledger.residualCupFamily joint.star.spine := by
      rwa [hprotected] at hcup
    exact ⟨⟨cup, hcup'⟩, hdisjoint⟩
  choose cupAt havoids using hexists
  exact ⟨{ cupAt := cupAt, avoidsOther := havoids }⟩

/-- In one cap column, either a selected deletion row misses the complete cap
block or the four vertex-indexed rows are injectively distinct. -/
theorem SixCapVertexDeletionResidualLedger578.exists_disjointRow_or_column_injective
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : SixCapVertexDeletionResidualLedger578 joint) (j : Fin 6) :
    (∃ c, Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) ∨
    Function.Injective (ledger.cupAt j) := by
  classical
  by_cases hdisjoint : ∃ c, Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)
  · exact Or.inl hdisjoint
  · right
    intro c d heq
    apply Subtype.ext
    by_contra hcd
    apply hdisjoint
    refine ⟨c, Finset.disjoint_left.mpr ?_⟩
    intro x hxCup hxCap
    have hxc : x = c.1 := by
      by_contra hxne
      exact (Finset.disjoint_left.mp (ledger.avoidsOther j c)) hxCup
        (Finset.mem_erase.mpr ⟨hxne, hxCap⟩)
    have hxCup' : x ∈ (ledger.cupAt j d).1 := by
      rw [← heq]
      exact hxCup
    have hxd : x = d.1 := by
      by_contra hxne
      exact (Finset.disjoint_left.mp (ledger.avoidsOther j d)) hxCup'
        (Finset.mem_erase.mpr ⟨hxne, hxCap⟩)
    exact hcd (hxc.symm.trans hxd)

/-- The disjoint-or-injective diagnostic is available simultaneously in all
six columns.  It is still columnwise and is not a global endpoint consumer. -/
theorem SixCapVertexDeletionResidualLedger578.all_columns_disjointRow_or_injective
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : SixCapVertexDeletionResidualLedger578 joint) :
    ∀ j : Fin 6,
      (∃ c, Disjoint (ledger.cupAt j c).1
        (joint.saturation.capAt j)) ∨
      Function.Injective (ledger.cupAt j) :=
  ledger.exists_disjointRow_or_column_injective

/-! ## Color-sensitive consumption at a common-minimum cell -/

/-- If a deletion row meets its source cap, the reverse-separated branch of
the base-cell trichotomy is impossible: a shared vertex cannot belong to the
two disjoint children of the common-minimum node.  Unlike row multiplicity,
this conclusion uses the cup/cap endpoint laws. -/
theorem SixCapVertexDeletionResidualLedger578.endpointShapes_of_base_of_not_disjoint
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (j : Fin 6) (c : {x : Fin n // x ∈ joint.saturation.capAt j})
    (hbase : (matrix.cell (ledger.cupAt j c) j).path =
      (matrix.cell minimum.row minimum.column).path)
    (hmeet : ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) :
    (¬(ledger.cupAt j c).1 ⊆
        (matrix.cell minimum.row minimum.column).node.upper ∧
      CupFourLowerEndpointShape578 (ledger.cupAt j c).1
        (matrix.cell minimum.row minimum.column).node.lower
        (matrix.cell minimum.row minimum.column).node.upper) ∨
    (¬joint.saturation.capAt j ⊆
        (matrix.cell minimum.row minimum.column).node.lower ∧
      CapFourUpperEndpointShape578 (joint.saturation.capAt j)
        (matrix.cell minimum.row minimum.column).node.lower
        (matrix.cell minimum.row minimum.column).node.upper) := by
  rcases minimum.endpointShapes_or_reverseSeparated_of_cell_eq_base
      (ledger.cupAt j c) j hbase with hcup | hcap | hreverse
  · exact Or.inl hcup
  · exact Or.inr hcap
  · exfalso
    apply hmeet
    apply Finset.disjoint_left.mpr
    intro x hxCup hxCap
    exact (Finset.disjoint_left.mp
      (matrix.cell minimum.row minimum.column).node.deep.disjoint)
        (hreverse.2 hxCap) (hreverse.1 hxCup)

/-- In a base-address deletion column with no cap-disjoint row, either the
source cap has the upper-endpoint shape or all four rows have the dual
lower-endpoint shape.  The cap alternative is shared across the column, so
this is stronger than four unrelated cell trichotomies. -/
theorem SixCapVertexDeletionResidualLedger578.capUpperShape_or_allRowsCupLowerShape
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (j : Fin 6)
    (hbase : ∀ c, (matrix.cell (ledger.cupAt j c) j).path =
      (matrix.cell minimum.row minimum.column).path)
    (hmeet : ∀ c, ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) :
    (¬joint.saturation.capAt j ⊆
        (matrix.cell minimum.row minimum.column).node.lower ∧
      CapFourUpperEndpointShape578 (joint.saturation.capAt j)
        (matrix.cell minimum.row minimum.column).node.lower
        (matrix.cell minimum.row minimum.column).node.upper) ∨
    ∀ c,
      ¬(ledger.cupAt j c).1 ⊆
          (matrix.cell minimum.row minimum.column).node.upper ∧
        CupFourLowerEndpointShape578 (ledger.cupAt j c).1
          (matrix.cell minimum.row minimum.column).node.lower
          (matrix.cell minimum.row minimum.column).node.upper := by
  by_cases hcap :
      ¬joint.saturation.capAt j ⊆
          (matrix.cell minimum.row minimum.column).node.lower ∧
        CapFourUpperEndpointShape578 (joint.saturation.capAt j)
          (matrix.cell minimum.row minimum.column).node.lower
          (matrix.cell minimum.row minimum.column).node.upper
  · exact Or.inl hcap
  · right
    intro c
    rcases ledger.endpointShapes_of_base_of_not_disjoint minimum j c
        (hbase c) (hmeet c) with hcup | hcap'
    · exact hcup
    · exact (hcap hcap').elim

/-- Exact per-column diagnostic at an all-base common minimum: a row is
cap-disjoint, the cap has the upper-endpoint shape, or all four deletion rows
have the lower-endpoint cup shape. -/
theorem SixCapVertexDeletionResidualLedger578.exists_disjointRow_or_endpointShapes
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (j : Fin 6)
    (hbase : ∀ c, (matrix.cell (ledger.cupAt j c) j).path =
      (matrix.cell minimum.row minimum.column).path) :
    (∃ c, Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) ∨
    (¬joint.saturation.capAt j ⊆
        (matrix.cell minimum.row minimum.column).node.lower ∧
      CapFourUpperEndpointShape578 (joint.saturation.capAt j)
        (matrix.cell minimum.row minimum.column).node.lower
        (matrix.cell minimum.row minimum.column).node.upper) ∨
    ∀ c,
      ¬(ledger.cupAt j c).1 ⊆
          (matrix.cell minimum.row minimum.column).node.upper ∧
        CupFourLowerEndpointShape578 (ledger.cupAt j c).1
          (matrix.cell minimum.row minimum.column).node.lower
          (matrix.cell minimum.row minimum.column).node.upper := by
  classical
  by_cases hdisjoint : ∃ c, Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)
  · exact Or.inl hdisjoint
  · right
    exact ledger.capUpperShape_or_allRowsCupLowerShape minimum j hbase
      (by simpa only [not_exists] using hdisjoint)

/-- If all six caps are localized in the lower child, the cap endpoint branch
is impossible.  Every all-base column therefore yields either a genuinely
cap-disjoint residual row or four lower-endpoint cup rows. -/
theorem SixCapVertexDeletionResidualLedger578.all_columns_disjointRow_or_allRowsCupLowerShape
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (hbase : ∀ j c, (matrix.cell (ledger.cupAt j c) j).path =
      (matrix.cell minimum.row minimum.column).path) :
    ∀ j : Fin 6,
      (∃ c, Disjoint (ledger.cupAt j c).1
        (joint.saturation.capAt j)) ∨
      ∀ c,
        ¬(ledger.cupAt j c).1 ⊆
            (matrix.cell minimum.row minimum.column).node.upper ∧
          CupFourLowerEndpointShape578 (ledger.cupAt j c).1
            (matrix.cell minimum.row minimum.column).node.lower
            (matrix.cell minimum.row minimum.column).node.upper := by
  intro j
  rcases ledger.exists_disjointRow_or_endpointShapes minimum j (hbase j) with
      hdisjoint | hcap | hrows
  · exact Or.inl hdisjoint
  · exact (hcap.1 ((joint.saturation.capAt_subset_capSupport j).trans hcaps)).elim
  · exact Or.inr hrows

end ErdosSzekeres

end
