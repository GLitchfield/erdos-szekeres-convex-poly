module

public import ErdosSzekeres.StructuralChargingNextState578BlockerConsumer
public import ErdosSzekeres.StructuralChargingNextState578EightVertex

@[expose] public section

/-!
# The exact residual state-578 localization trichotomy

Opposite strict extensions in the full residual-cup/six-cap address matrix
already force a strong eight-set.  The distinguished-spine plateau from the
pure address classification is therefore unnecessary under the exact open
state hypotheses.  What remains is a three-way alternative: the six cap
blocks are localized in one child, or a complete cap column stays at the
common-minimum address.
-/

namespace ErdosSzekeres

/-- Under strong-eight avoidance, the full residual-family matrix cannot have
strict extensions in both directions from its common minimum. -/
theorem FullResidualCupSixCapCommonMinimum578.no_oppositeExtensions_of_noStrongEight
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hnoStrong : ¬ContainsStrongPolygonSet χ support 8) :
    ¬∃ first second j k leftTail rightTail,
      (matrix.cell first j).path =
          (matrix.cell minimum.row minimum.column).path ++ false :: leftTail ∧
        (matrix.cell second k).path =
          (matrix.cell minimum.row minimum.column).path ++ true :: rightTail := by
  rintro ⟨first, second, j, k, leftTail, rightTail, hleft, hright⟩
  let base := matrix.cell minimum.row minimum.column
  have hfirstLower : first.1 ⊆ base.node.lower :=
    Finset.subset_union_left.trans
      (minimum.cell_union_subset_lower_of_extends hleft)
  have hkUpper : joint.saturation.capAt k ⊆ base.node.upper :=
    Finset.subset_union_right.trans
      (minimum.cell_union_subset_upper_of_extends hright)
  have hcupData := mem_capWitnesses.mp
    (joint.ledger.mem_residualCupFamily.mp first.2).1
  have hcapData := mem_capWitnesses.mp (joint.saturation.capAt_mem k)
  have hstrongNode :
      ContainsStrongPolygonSet χ (base.node.lower ∪ base.node.upper) 8 :=
    base.node.deep.containsStrongPolygonSet_of_containsCupCap
      ⟨first.1, hfirstLower, hcupData.2.1,
        isCapSet_dual_iff.mp hcupData.2.2⟩
      ⟨joint.saturation.capAt k, hkUpper, hcapData.2.1, hcapData.2.2⟩
      (by omega)
  exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrongNode
    (tree.splitAtPath_support_subset base.lookup))

/-- Strong-eight avoidance makes every strict extension from the full-matrix
minimum point in the same direction. -/
theorem FullResidualCupSixCapCommonMinimum578.oneSided_of_noStrongEight
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hnoStrong : ¬ContainsStrongPolygonSet χ support 8) :
    (∀ cup j,
      (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ∨
        ∃ tail, (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ++ true :: tail) ∨
    (∀ cup j,
      (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ∨
        ∃ tail, (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ++ false :: tail) := by
  let base := (matrix.cell minimum.row minimum.column).path
  by_cases hfalse : ∃ cup j tail,
      (matrix.cell cup j).path = base ++ false :: tail
  · by_cases htrue : ∃ cup j tail,
        (matrix.cell cup j).path = base ++ true :: tail
    · obtain ⟨first, j, leftTail, hleft⟩ := hfalse
      obtain ⟨second, k, rightTail, hright⟩ := htrue
      exact (minimum.no_oppositeExtensions_of_noStrongEight hnoStrong
        ⟨first, second, j, k, leftTail, rightTail, hleft, hright⟩).elim
    · right
      intro cup j
      rcases list_eq_or_exists_firstStep_of_prefix
          (minimum.minimal cup j) with heq | ⟨direction, tail, hstep⟩
      · exact Or.inl heq
      · cases direction with
        | false => exact Or.inr ⟨tail, by simpa [base] using hstep⟩
        | true => exact (htrue ⟨cup, j, tail, by simpa [base] using hstep⟩).elim
  · left
    intro cup j
    rcases list_eq_or_exists_firstStep_of_prefix
        (minimum.minimal cup j) with heq | ⟨direction, tail, hstep⟩
    · exact Or.inl heq
    · cases direction with
      | false => exact (hfalse ⟨cup, j, tail, by simpa [base] using hstep⟩).elim
      | true => exact Or.inr ⟨tail, by simpa [base] using hstep⟩

/-- The exact full-family trichotomy under strong-eight avoidance: the six
disjoint cap blocks occupy one child, or one full cap column remains at the
common-minimum address. -/
theorem FullResidualCupSixCapCommonMinimum578.localizedCaps_or_minimumColumn_of_noStrongEight
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hnoStrong : ¬ContainsStrongPolygonSet χ support 8) :
    (joint.saturation.capSupport ⊆
        (matrix.cell minimum.row minimum.column).node.lower ∧
      24 ≤ (matrix.cell minimum.row minimum.column).node.lower.card) ∨
    (joint.saturation.capSupport ⊆
        (matrix.cell minimum.row minimum.column).node.upper ∧
      24 ≤ (matrix.cell minimum.row minimum.column).node.upper.card) ∨
    ∃ j, ∀ cup, (matrix.cell cup j).path =
      (matrix.cell minimum.row minimum.column).path := by
  rcases minimum.oneSided_of_noStrongEight hnoStrong with hright | hleft
  · by_cases hall : ∀ j, ∃ cup tail,
        (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ++ true :: tail
    · right
      left
      have hsub : joint.saturation.capSupport ⊆
          (matrix.cell minimum.row minimum.column).node.upper := by
        apply joint.saturation.capSupport_subset_of_all_capAt_subset
        intro j
        obtain ⟨cup, tail, hstrict⟩ := hall j
        exact Finset.subset_union_right.trans
          (minimum.cell_union_subset_upper_of_extends hstrict)
      exact ⟨hsub, by
        have hcard := Finset.card_le_card hsub
        rw [joint.saturation.capSupport_card] at hcard
        exact hcard⟩
    · push Not at hall
      right
      right
      obtain ⟨j, hj⟩ := hall
      refine ⟨j, fun cup ↦ ?_⟩
      rcases hright cup j with heq | ⟨tail, hstrict⟩
      · exact heq
      · exact (hj cup tail hstrict).elim
  · by_cases hall : ∀ j, ∃ cup tail,
        (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path ++ false :: tail
    · left
      have hsub : joint.saturation.capSupport ⊆
          (matrix.cell minimum.row minimum.column).node.lower := by
        apply joint.saturation.capSupport_subset_of_all_capAt_subset
        intro j
        obtain ⟨cup, tail, hstrict⟩ := hall j
        exact Finset.subset_union_right.trans
          (minimum.cell_union_subset_lower_of_extends hstrict)
      exact ⟨hsub, by
        have hcard := Finset.card_le_card hsub
        rw [joint.saturation.capSupport_card] at hcard
        exact hcard⟩
    · push Not at hall
      right
      right
      obtain ⟨j, hj⟩ := hall
      refine ⟨j, fun cup ↦ ?_⟩
      rcases hleft cup j with heq | ⟨tail, hstrict⟩
      · exact heq
      · exact (hj cup tail hstrict).elim

/-- At support size 32, the two localized-cap branches come with a
three-vertex four-cup boundary on the complementary child. -/
theorem FullResidualCupSixCapCommonMinimum578.localizedCapsWithBoundary_or_minimumColumn_of_noStrongEight_at_32
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hcard : support.card = 32)
    (hnoCup : ¬ContainsCupSet χ support 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ support 8) :
    (joint.saturation.capSupport ⊆
        (matrix.cell minimum.row minimum.column).node.lower ∧
      24 ≤ (matrix.cell minimum.row minimum.column).node.lower.card ∧
      ∃ boundary : Finset (Fin n),
        boundary ⊆ (matrix.cell minimum.row minimum.column).node.upper ∧
        boundary.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ
          (matrix.cell minimum.row minimum.column).node.upper boundary 4) ∨
    (joint.saturation.capSupport ⊆
        (matrix.cell minimum.row minimum.column).node.upper ∧
      24 ≤ (matrix.cell minimum.row minimum.column).node.upper.card ∧
      ∃ boundary : Finset (Fin n),
        boundary ⊆ (matrix.cell minimum.row minimum.column).node.lower ∧
        boundary.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ
          (matrix.cell minimum.row minimum.column).node.lower boundary 4) ∨
    ∃ j, ∀ cup, (matrix.cell cup j).path =
      (matrix.cell minimum.row minimum.column).path := by
  rcases minimum.localizedCaps_or_minimumColumn_of_noStrongEight hnoStrong with
    ⟨hsub, hlower⟩ | ⟨hsub, hupper⟩ | hcolumn
  · left
    exact ⟨hsub, hlower,
      minimum.upper_exists_threeBoundary_of_twentyFour_le_lower_at_32
        hcard hlower hnoCup⟩
  · right
    left
    exact ⟨hsub, hupper,
      minimum.lower_exists_threeBoundary_of_twentyFour_le_upper_at_32
        hcard hupper hnoCup⟩
  · exact Or.inr (Or.inr hcolumn)

/-- The upper-localized counterpart of the existing lower-localized density
escape theorem.  A local three-boundary in the small lower child is missed by
some residual cup; that cup is either wholly upper or its entire matrix row
stays at the common-minimum address. -/
theorem FullResidualCupSixCapCommonMinimum578.exists_lowerBoundary_and_escapeRow_of_capSupport_subset_upper_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    {tree : DecompositionTree χ reservoir}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCup : ¬ContainsCupSet χ reservoir 5)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.upper) :
    ∃ boundary,
      boundary ⊆ (matrix.cell minimum.row minimum.column).node.lower ∧
      boundary.card ≤ 3 ∧
      IsCupWitnessTransversal578 χ
        (matrix.cell minimum.row minimum.column).node.lower boundary 4 ∧
      ∃ cup : joint.ResidualCupIndex,
        Disjoint cup.1 boundary ∧
        (cup.1 ⊆ (matrix.cell minimum.row minimum.column).node.upper ∨
          ∀ j, (matrix.cell cup j).path =
            (matrix.cell minimum.row minimum.column).path) := by
  let base := matrix.cell minimum.row minimum.column
  have hupper : 24 ≤ base.node.upper.card := by
    have hle := Finset.card_le_card hcaps
    rw [joint.saturation.capSupport_card] at hle
    exact hle
  obtain ⟨boundary, hboundarySub, hboundaryCard, hboundaryHits⟩ :=
    minimum.lower_exists_threeBoundary_of_twentyFour_le_upper_at_32
      hcard hupper hnoCup
  have hboundarySupport : boundary ⊆ reservoir :=
    hboundarySub.trans (Finset.subset_union_left.trans
      (tree.splitAtPath_support_subset base.lookup))
  have hbudget : boundary.card ≤
      3 * (joint.saturation.state.packing.fullCupSpines
        joint.ledger.transversal).card := by
    rw [hone]
    simpa using hboundaryCard
  obtain ⟨cup, hcupResidual, hdisjoint⟩ :=
    exists_residualCup_disjoint_from_fullSpineBoundary578 joint
      hreservoir hcard hnoCap hnoStrong hboundarySupport hbudget
  have hprotected := joint.fullCupProtected_eq_spine_of_card_eq_one hone
  have hcupSpine : cup ∈
      joint.ledger.residualCupFamily joint.star.spine := by
    rwa [← hprotected]
  let indexed : joint.ResidualCupIndex := ⟨cup, hcupSpine⟩
  refine ⟨boundary, hboundarySub, hboundaryCard, hboundaryHits,
    indexed, hdisjoint, ?_⟩
  exact minimum.cup_subset_upper_or_rowPlateau_of_capSupport_subset_upper
    hcaps indexed

/-- Exact witness package for the lower-localized branch: 24 cap vertices in
the large child, a three-boundary in the small child, and a residual cup which
escapes that boundary. -/
structure LowerLocalizedResidualEscape578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix) where
  capSupport_lower : joint.saturation.capSupport ⊆
    (matrix.cell minimum.row minimum.column).node.lower
  lower_twentyFour :
    24 ≤ (matrix.cell minimum.row minimum.column).node.lower.card
  boundary : Finset (Fin n)
  boundary_sub : boundary ⊆
    (matrix.cell minimum.row minimum.column).node.upper
  boundary_card : boundary.card ≤ 3
  boundary_hits : IsCupWitnessTransversal578 χ
    (matrix.cell minimum.row minimum.column).node.upper boundary 4
  escapeCup : joint.ResidualCupIndex
  escape_disjoint : Disjoint escapeCup.1 boundary
  escape_local_or_plateau :
    escapeCup.1 ⊆ (matrix.cell minimum.row minimum.column).node.lower ∨
      ∀ j, (matrix.cell escapeCup j).path =
        (matrix.cell minimum.row minimum.column).path

/-- The symmetric witness package for upper localization. -/
structure UpperLocalizedResidualEscape578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix) where
  capSupport_upper : joint.saturation.capSupport ⊆
    (matrix.cell minimum.row minimum.column).node.upper
  upper_twentyFour :
    24 ≤ (matrix.cell minimum.row minimum.column).node.upper.card
  boundary : Finset (Fin n)
  boundary_sub : boundary ⊆
    (matrix.cell minimum.row minimum.column).node.lower
  boundary_card : boundary.card ≤ 3
  boundary_hits : IsCupWitnessTransversal578 χ
    (matrix.cell minimum.row minimum.column).node.lower boundary 4
  escapeCup : joint.ResidualCupIndex
  escape_disjoint : Disjoint escapeCup.1 boundary
  escape_local_or_plateau :
    escapeCup.1 ⊆ (matrix.cell minimum.row minimum.column).node.upper ∨
      ∀ j, (matrix.cell escapeCup j).path =
        (matrix.cell minimum.row minimum.column).path

/-- If a deletion witness meets its source cap, then it meets that cap in
exactly the deleted source vertex. -/
theorem SixCapVertexDeletionResidualLedger578.cupAt_inter_capAt_eq_singleton_of_not_disjoint
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (j : Fin 6) (c : {x : Fin n // x ∈ joint.saturation.capAt j})
    (hmeet : ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) :
    (ledger.cupAt j c).1 ∩ joint.saturation.capAt j = {c.1} := by
  classical
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hxCup, hxCap⟩
    by_contra hxne
    exact (Finset.disjoint_left.mp (ledger.avoidsOther j c)) hxCup
      (Finset.mem_erase.mpr ⟨hxne, hxCap⟩)
  · rintro rfl
    exact ⟨ledger.source_mem_of_not_disjoint j c hmeet, c.2⟩

/-- A universal common-minimum column which meets every residual cup is a
genuine four-owner private-star object: its four deletion witnesses meet the
column cap in four different singleton owners. -/
structure MinimumColumnPrivateResidualStar578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix) where
  column : Fin 6
  all_base : ∀ cup, (matrix.cell cup column).path =
    (matrix.cell minimum.row minimum.column).path
  hits_all : ∀ cup : joint.ResidualCupIndex,
    ¬Disjoint cup.1 (joint.saturation.capAt column)
  deletion_inter : ∀ c,
    (ledger.cupAt column c).1 ∩ joint.saturation.capAt column = {c.1}
  deletion_injective : Function.Injective (ledger.cupAt column)

/-- Exact consumption of a universal minimum column: either a residual cup
avoids the column cap, or the column supports a four-owner private residual
cup star. -/
theorem FullResidualCupSixCapCommonMinimum578.disjointResidualCup_or_privateStar_of_minimumColumn
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (j : Fin 6)
    (hbase : ∀ cup, (matrix.cell cup j).path =
      (matrix.cell minimum.row minimum.column).path) :
    (∃ cup : joint.ResidualCupIndex,
      Disjoint cup.1 (joint.saturation.capAt j)) ∨
      Nonempty (MinimumColumnPrivateResidualStar578 ledger minimum) := by
  classical
  by_cases hdisjoint : ∃ cup : joint.ResidualCupIndex,
      Disjoint cup.1 (joint.saturation.capAt j)
  · exact Or.inl hdisjoint
  · right
    have hhits : ∀ cup : joint.ResidualCupIndex,
        ¬Disjoint cup.1 (joint.saturation.capAt j) := by
      simpa only [not_exists] using hdisjoint
    have hinjective : Function.Injective (ledger.cupAt j) := by
      rcases ledger.exists_disjointRow_or_column_injective j with
        hrow | hinjective
      · obtain ⟨c, hc⟩ := hrow
        exact (hhits (ledger.cupAt j c) hc).elim
      · exact hinjective
    exact ⟨{
      column := j
      all_base := hbase
      hits_all := hhits
      deletion_inter := fun c ↦
        ledger.cupAt_inter_capAt_eq_singleton_of_not_disjoint j c
          (hhits (ledger.cupAt j c))
      deletion_injective := hinjective
    }⟩

/-- Full 32-vertex density converts the exact matrix trichotomy into two
directional escape packages or a universal common-minimum cap column.  This
is the precise remaining state-578 obstruction after opposite extensions are
eliminated. -/
theorem FullResidualCupSixCapCommonMinimum578.exists_localizedResidualEscape_or_minimumColumn_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    {tree : DecompositionTree χ reservoir}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCup : ¬ContainsCupSet χ reservoir 5)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1) :
    Nonempty (LowerLocalizedResidualEscape578 minimum) ∨
      Nonempty (UpperLocalizedResidualEscape578 minimum) ∨
      ∃ j, ∀ cup, (matrix.cell cup j).path =
        (matrix.cell minimum.row minimum.column).path := by
  have hnoStrongReservoir : ¬ContainsStrongPolygonSet χ reservoir 8 := by
    intro hstrong
    exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
      Finset.subset_union_right)
  rcases minimum.localizedCaps_or_minimumColumn_of_noStrongEight
      hnoStrongReservoir with
    ⟨hcaps, hlower⟩ | ⟨hcaps, hupper⟩ | hcolumn
  · left
    obtain ⟨boundary, hboundarySub, hboundaryCard, hboundaryHits,
        cup, hdisjoint, hescape⟩ :=
      minimum.exists_upperBoundary_and_escapeRow_of_capSupport_subset_lower_at_32
        hreservoir hcard hnoCup hnoCap hnoStrong hone hcaps
    exact ⟨{
      capSupport_lower := hcaps
      lower_twentyFour := hlower
      boundary := boundary
      boundary_sub := hboundarySub
      boundary_card := hboundaryCard
      boundary_hits := hboundaryHits
      escapeCup := cup
      escape_disjoint := hdisjoint
      escape_local_or_plateau := hescape
    }⟩
  · right
    left
    obtain ⟨boundary, hboundarySub, hboundaryCard, hboundaryHits,
        cup, hdisjoint, hescape⟩ :=
      minimum.exists_lowerBoundary_and_escapeRow_of_capSupport_subset_upper_at_32
        hreservoir hcard hnoCup hnoCap hnoStrong hone hcaps
    exact ⟨{
      capSupport_upper := hcaps
      upper_twentyFour := hupper
      boundary := boundary
      boundary_sub := hboundarySub
      boundary_card := hboundaryCard
      boundary_hits := hboundaryHits
      escapeCup := cup
      escape_disjoint := hdisjoint
      escape_local_or_plateau := hescape
    }⟩
  · exact Or.inr (Or.inr hcolumn)

/-- With the 24-entry deletion ledger present, the universal-column branch
splits further into an avoiding residual cup or a four-owner private residual
star.  These four cases are the exact remaining full-state obstructions. -/
theorem FullResidualCupSixCapCommonMinimum578.exists_localizedResidualEscape_or_disjointColumnCup_or_privateStar_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    {tree : DecompositionTree χ reservoir}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCup : ¬ContainsCupSet χ reservoir 5)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hone : (joint.saturation.state.packing.fullCupSpines
      joint.ledger.transversal).card = 1) :
    Nonempty (LowerLocalizedResidualEscape578 minimum) ∨
      Nonempty (UpperLocalizedResidualEscape578 minimum) ∨
      (∃ j, (∀ cup, (matrix.cell cup j).path =
          (matrix.cell minimum.row minimum.column).path) ∧
        ∃ cup : joint.ResidualCupIndex,
          Disjoint cup.1 (joint.saturation.capAt j)) ∨
      Nonempty (MinimumColumnPrivateResidualStar578 ledger minimum) := by
  rcases minimum.exists_localizedResidualEscape_or_minimumColumn_at_32
      hreservoir hcard hnoCup hnoCap hnoStrong hone with
    hlower | hupper | ⟨j, hbase⟩
  · exact Or.inl hlower
  · exact Or.inr (Or.inl hupper)
  · rcases minimum.disjointResidualCup_or_privateStar_of_minimumColumn
        ledger j hbase with hdisjoint | hstar
    · exact Or.inr (Or.inr (Or.inl ⟨j, hbase, hdisjoint⟩))
    · exact Or.inr (Or.inr (Or.inr hstar))

/-- In the complete tight reduction, lower localization also removes the
set-theoretic escape from the deletion-ledger outcome.  Thus the lower branch
retains one of the three named ledger obstructions, while upper localization
and the universal minimum column remain separate. -/
theorem TightDeficitDensityReduction578.localizedCapsWithBoundary_or_minimumColumn_of_noStrongEight_at_32
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (tight : TightDeficitDensityReduction578 joint)
    (hcard : support.card = 32)
    (hnoCup : ¬ContainsCupSet χ support 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ support 8) :
    (joint.saturation.capSupport ⊆
        (tight.matrix.cell tight.minimum.row tight.minimum.column).node.lower ∧
      24 ≤ (tight.matrix.cell tight.minimum.row tight.minimum.column).node.lower.card ∧
      (∃ boundary : Finset (Fin n),
        boundary ⊆
          (tight.matrix.cell tight.minimum.row tight.minimum.column).node.upper ∧
        boundary.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ
          (tight.matrix.cell tight.minimum.row tight.minimum.column).node.upper
          boundary 4) ∧
      (Nonempty (TwoBlockerDeletionEscape578 tight.ledger) ∨
        Nonempty (StrictLowerDeletionEscape578 tight.ledger tight.minimum) ∨
        Nonempty (AllBaseMeetingFanDensityOutcome578 tight.ledger
          tight.minimum))) ∨
    (joint.saturation.capSupport ⊆
        (tight.matrix.cell tight.minimum.row tight.minimum.column).node.upper ∧
      24 ≤ (tight.matrix.cell tight.minimum.row tight.minimum.column).node.upper.card ∧
      ∃ boundary : Finset (Fin n),
        boundary ⊆
          (tight.matrix.cell tight.minimum.row tight.minimum.column).node.lower ∧
        boundary.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ
          (tight.matrix.cell tight.minimum.row tight.minimum.column).node.lower
          boundary 4) ∨
    ∃ j, ∀ cup, (tight.matrix.cell cup j).path =
      (tight.matrix.cell tight.minimum.row tight.minimum.column).path := by
  rcases FullResidualCupSixCapCommonMinimum578.localizedCapsWithBoundary_or_minimumColumn_of_noStrongEight_at_32
      tight.minimum hcard hnoCup hnoStrong with
    ⟨hsub, hlower, hboundary⟩ | ⟨hsub, hupper, hboundary⟩ | hcolumn
  · left
    refine ⟨hsub, hlower, hboundary, ?_⟩
    rcases tight.outcome with hnot | htwo | hstrict | hfan
    · exact (hnot hsub).elim
    · exact Or.inl htwo
    · exact Or.inr (Or.inl hstrict)
    · exact Or.inr (Or.inr hfan)
  · exact Or.inr (Or.inl ⟨hsub, hupper, hboundary⟩)
  · exact Or.inr (Or.inr hcolumn)

end ErdosSzekeres

end
