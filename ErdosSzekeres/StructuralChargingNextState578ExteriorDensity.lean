module

public import ErdosSzekeres.StructuralChargingNextState578UpperBracketLedger
public import ErdosSzekeres.StructuralChargingNextState578RestrictedMiddlePairs

@[expose] public section

/-!
# Exterior-density interfaces at state `(5,7,8)`

This file couples the six disjoint cap columns, the nine-source exterior fan,
and the exact `32/23` residual-cup density theorem.  It deliberately stops at
the two surviving escape modes: a residual cup can retreat into the large cap
child, or all six of its cup/cap addresses can remain on the common-minimum
plateau.  Pure incidence and address data do not eliminate either mode.
-/

namespace ErdosSzekeres

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

/-! ## The six-column incidence interface -/

/-- Distinct indexed blocks in a six-cap saturation are disjoint. -/
theorem SixCapSaturation578.capAt_disjoint_of_ne
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    {i j : Fin 6} (hij : i ≠ j) :
    Disjoint (saturation.capAt i) (saturation.capAt j) := by
  let caps := [saturation.state.regenerated,
    saturation.state.packing.cap₁,
    saturation.state.packing.cap₂,
    saturation.state.packing.cap₃,
    saturation.cap₅,
    saturation.cap₆]
  have hcapAt (k : Fin 6) : saturation.capAt k = caps.get k := by
    fin_cases k <;> rfl
  rw [hcapAt i, hcapAt j]
  rcases lt_trichotomy i j with hijlt | hijeq | hjilt
  · exact saturation.sixCaps_pairwise.rel_get_of_lt hijlt
  · exact (hij hijeq).elim
  · exact (saturation.sixCaps_pairwise.rel_get_of_lt hjilt).symm

/-- The cap columns met by a finite vertex set. -/
def metCapColumns578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    (vertices : Finset (Fin n)) : Finset (Fin 6) :=
  Finset.univ.filter fun j ↦ ¬Disjoint vertices (saturation.capAt j)

/-- The cap columns completely avoided by a finite vertex set. -/
def missedCapColumns578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    (vertices : Finset (Fin n)) : Finset (Fin 6) :=
  Finset.univ \ metCapColumns578 saturation vertices

/-- Meeting distinct disjoint cap columns consumes distinct vertices inside
the saturated cap support. -/
theorem metCapColumns578_card_le_inter_capSupport
    {n : ℕ} {χ : TripleColoring n}
    {support vertices : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support) :
    (metCapColumns578 saturation vertices).card ≤
      (vertices ∩ saturation.capSupport).card := by
  classical
  let met := metCapColumns578 saturation vertices
  have hmeet (j : {j // j ∈ met}) :
      ¬Disjoint vertices (saturation.capAt j.1) := by
    have hj := j.2
    change j.1 ∈ Finset.univ.filter
      (fun k ↦ ¬Disjoint vertices (saturation.capAt k)) at hj
    exact (Finset.mem_filter.mp hj).2
  let data (j : {j // j ∈ met}) :=
    Finset.not_disjoint_iff.mp (hmeet j)
  let witness (j : {j // j ∈ met}) :
      {x // x ∈ vertices ∩ saturation.capSupport} :=
    ⟨(data j).choose, Finset.mem_inter.mpr
      ⟨(data j).choose_spec.1,
        saturation.capAt_subset_capSupport j.1 (data j).choose_spec.2⟩⟩
  have hwitnessCap (j : {j // j ∈ met}) :
      (witness j).1 ∈ saturation.capAt j.1 :=
    (data j).choose_spec.2
  have hinjective : Function.Injective witness := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hdisjoint := saturation.capAt_disjoint_of_ne hne
    exact (Finset.disjoint_left.mp hdisjoint)
      (hwitnessCap i) (by simpa [hij] using hwitnessCap j)
  have hcard := Fintype.card_le_of_injective witness hinjective
  simpa only [met, Fintype.card_coe] using hcard

/-- A set of at most four vertices misses at least two of the six disjoint cap
columns. -/
theorem two_le_missedCapColumns578_of_card_le_four
    {n : ℕ} {χ : TripleColoring n}
    {support vertices : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    (hcard : vertices.card ≤ 4) :
    2 ≤ (missedCapColumns578 saturation vertices).card := by
  classical
  have hmet := metCapColumns578_card_le_inter_capSupport saturation
    (vertices := vertices)
  have hinter := Finset.card_le_card
    (Finset.inter_subset_left :
      vertices ∩ saturation.capSupport ⊆ vertices)
  rw [missedCapColumns578,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have huniv : (Finset.univ : Finset (Fin 6)).card = 6 := by simp
  rw [huniv]
  omega

/-- Explicitly select two distinct cap columns missed by any set of at most
four vertices. -/
theorem exists_two_disjoint_capAt578_of_card_le_four
    {n : ℕ} {χ : TripleColoring n}
    {support vertices : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    (hcard : vertices.card ≤ 4) :
    ∃ i j : Fin 6, i ≠ j ∧
      Disjoint vertices (saturation.capAt i) ∧
      Disjoint vertices (saturation.capAt j) := by
  classical
  have hmissed := two_le_missedCapColumns578_of_card_le_four
    saturation hcard
  have htwo : 1 < (missedCapColumns578 saturation vertices).card := by
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp htwo
  refine ⟨i, j, hij, ?_, ?_⟩
  · have hi' := (Finset.mem_sdiff.mp hi).2
    simp [metCapColumns578] at hi'
    exact hi'
  · have hj' := (Finset.mem_sdiff.mp hj).2
    simp [metCapColumns578] at hj'
    exact hj'

/-- A one-upper four-cup has at most three vertices in the lower child. -/
theorem CupFourOneUpperEndpointShape578.inter_lower_card_le_three
    {n : ℕ} {cup lower upper : Finset (Fin n)}
    (hshape : CupFourOneUpperEndpointShape578 cup lower upper)
    (hdisjoint : Disjoint lower upper) :
    (cup ∩ lower).card ≤ 3 := by
  rcases hshape with ⟨hcard, hmiddleOne, hmiddleTwo, hendpoints⟩
  let c := cup.orderEmbOfFin hcard
  have hproper : cup ∩ lower ⊂ cup := by
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    rcases hendpoints with hend | hend
    · have hzeroCup : c 0 ∈ cup := cup.orderEmbOfFin_mem hcard 0
      have hzeroInter : c 0 ∈ cup ∩ lower := by
        rw [heq]
        exact hzeroCup
      exact (Finset.disjoint_left.mp hdisjoint)
        (Finset.mem_inter.mp hzeroInter).2 hend.1
    · have hthreeCup : c 3 ∈ cup := cup.orderEmbOfFin_mem hcard 3
      have hthreeInter : c 3 ∈ cup ∩ lower := by
        rw [heq]
        exact hthreeCup
      exact (Finset.disjoint_left.mp hdisjoint)
        (Finset.mem_inter.mp hthreeInter).2 hend.2
  have hlt := Finset.card_lt_card hproper
  rw [hcard] at hlt
  omega

/-- A one-upper exterior-fan row can meet at most three of the six lower cap
columns.  Thus every such row contributes at least three column deficits. -/
theorem NineOneSidedDeletionFan578.row_metCapColumns_card_le_three
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper :
      (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (fan : NineOneSidedDeletionFan578 ledger minimum hupper)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (j : Fin 6) (c : {x : Fin n // x ∈ joint.saturation.capAt j})
    (hsource : c.1 ∈ fan.sources) :
    (metCapColumns578 joint.saturation (ledger.cupAt j c).1).card ≤ 3 := by
  let base := matrix.cell minimum.row minimum.column
  have hcapInterSub :
      (ledger.cupAt j c).1 ∩ joint.saturation.capSupport ⊆
        (ledger.cupAt j c).1 ∩ base.node.lower := by
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hx).1, hcaps (Finset.mem_inter.mp hx).2⟩
  have hcolumns := metCapColumns578_card_le_inter_capSupport
    joint.saturation (vertices := (ledger.cupAt j c).1)
  have hinter := Finset.card_le_card hcapInterSub
  have hthree :=
    (fan.row_oneUpper j c hsource).inter_lower_card_le_three
      base.node.deep.disjoint
  change ((ledger.cupAt j c).1 ∩ base.node.lower).card ≤ 3 at hthree
  omega

/-- Independently of columns, a four-cup avoids at least five vertices of a
nine-source fan. -/
theorem NineOneSidedDeletionFan578.five_le_sources_sdiff_fourCup
    {n : ℕ} {χ : TripleColoring n}
    {support cup : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper :
      (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (fan : NineOneSidedDeletionFan578 ledger minimum hupper)
    (hcupCard : cup.card = 4) :
    5 ≤ (fan.sources \ cup).card := by
  have hinter : (fan.sources ∩ cup).card ≤ cup.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hsum := Finset.card_sdiff_add_card_inter fan.sources cup
  have hnine := fan.nine_le
  omega

/-! ## Six-column deficit concentration -/

/-- A finite double-counting lemma specialized to six columns: if at least
nine rows each miss at least three columns, one column is missed by at least
five rows. -/
theorem exists_five_column_of_nine_rows_each_three
    {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (misses : ι → Fin 6 → Prop)
    [DecidableRel misses]
    (hnine : 9 ≤ rows.card)
    (hthree : ∀ i ∈ rows,
      3 ≤ (Finset.univ.filter (misses i)).card) :
    ∃ j : Fin 6, 5 ≤ (rows.filter fun i ↦ misses i j).card := by
  classical
  by_contra hno
  push Not at hno
  have hrowSum :
      3 * rows.card ≤
        ∑ i ∈ rows, (Finset.univ.filter (misses i)).card := by
    calc
      3 * rows.card = ∑ i ∈ rows, 3 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hthree
  have hcolSum :
      (∑ j : Fin 6, (rows.filter fun i ↦ misses i j).card) ≤ 24 := by
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin 6)),
        (rows.filter fun i ↦ misses i j).card ≤ 4 := by
      intro j _
      have := hno j
      omega
    calc
      _ ≤ ∑ _j : Fin 6, 4 := Finset.sum_le_sum hle
      _ = 24 := by norm_num
  have hswap :
      (∑ i ∈ rows, (Finset.univ.filter (misses i)).card) =
        ∑ j : Fin 6, (rows.filter fun i ↦ misses i j).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap] at hrowSum
  omega

/-- The source-indexed entries of a nine-source deletion fan. -/
def NineOneSidedDeletionFan578.entries
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper :
      (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (fan : NineOneSidedDeletionFan578 ledger minimum hupper) :
    Finset (Σ j : Fin 6,
      {c : Fin n // c ∈ joint.saturation.capAt j}) :=
  Finset.univ.filter fun p ↦ p.2.1 ∈ fan.sources

/-- Every fan source has a unique entry in the six disjoint cap columns, so
the entry set retains the lower bound of nine. -/
theorem NineOneSidedDeletionFan578.nine_le_entries_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper :
      (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (fan : NineOneSidedDeletionFan578 ledger minimum hupper) :
    9 ≤ fan.entries.card := by
  classical
  let covered := (Finset.univ : Finset (Fin n)).filter fun x ↦
    ∃ j : Fin 6, x ∈ joint.saturation.capAt j
  have hall (j : Fin 6) : joint.saturation.capAt j ⊆ covered := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨j, hx⟩⟩
  have hcover : joint.saturation.capSupport ⊆ covered :=
    joint.saturation.capSupport_subset_of_all_capAt_subset hall
  have hexists (x : {x // x ∈ fan.sources}) :
      ∃ j : Fin 6, x.1 ∈ joint.saturation.capAt j := by
    exact (Finset.mem_filter.mp
      (hcover (fan.sources_subset x.2))).2
  let column (x : {x // x ∈ fan.sources}) : Fin 6 :=
    Classical.choose (hexists x)
  have hcolumn (x : {x // x ∈ fan.sources}) :
      x.1 ∈ joint.saturation.capAt (column x) :=
    Classical.choose_spec (hexists x)
  let entry (x : {x // x ∈ fan.sources}) :
      Σ j : Fin 6, {c : Fin n // c ∈ joint.saturation.capAt j} :=
    ⟨column x, ⟨x.1, hcolumn x⟩⟩
  have hentryMem (x : {x // x ∈ fan.sources}) :
      entry x ∈ fan.entries := by
    simp [NineOneSidedDeletionFan578.entries, entry]
  let indexed (x : {x // x ∈ fan.sources}) :
      {p // p ∈ fan.entries} := ⟨entry x, hentryMem x⟩
  have hinjective : Function.Injective indexed := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun p : Σ j : Fin 6,
        {c : Fin n // c ∈ joint.saturation.capAt j} ↦ p.2.1)
      (congrArg Subtype.val hxy)
  have hcard := Fintype.card_le_of_injective indexed hinjective
  have hsources :
      Fintype.card {x // x ∈ fan.sources} = fan.sources.card := by
    simp
  have hentries :
      Fintype.card {p // p ∈ fan.entries} = fan.entries.card := by
    simp
  rw [hsources, hentries] at hcard
  exact fan.nine_le.trans hcard

/-- Some saturated cap column is missed by at least five source-indexed
one-upper fan rows.  This is the first exterior-fan invariant which uses all
six cap columns essentially; the three-column relaxed counterexample cannot
instantiate its arithmetic. -/
theorem NineOneSidedDeletionFan578.exists_fiveDeficitColumn
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper :
      (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (fan : NineOneSidedDeletionFan578 ledger minimum hupper)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower) :
    ∃ j : Fin 6,
      5 ≤ (fan.entries.filter fun p ↦
        Disjoint (ledger.cupAt p.1 p.2).1
          (joint.saturation.capAt j)).card := by
  classical
  let misses :
      (Σ j : Fin 6,
        {c : Fin n // c ∈ joint.saturation.capAt j}) → Fin 6 → Prop :=
    fun p j ↦ Disjoint (ledger.cupAt p.1 p.2).1
      (joint.saturation.capAt j)
  apply exists_five_column_of_nine_rows_each_three
    fan.entries misses fan.nine_le_entries_card
  intro p hp
  have hsource : p.2.1 ∈ fan.sources :=
    (Finset.mem_filter.mp hp).2
  have hmet :=
    fan.row_metCapColumns_card_le_three hcaps p.1 p.2 hsource
  have hset :
      Finset.univ.filter (misses p) =
        missedCapColumns578 joint.saturation (ledger.cupAt p.1 p.2).1 := by
    ext j
    simp [misses, missedCapColumns578, metCapColumns578]
  rw [hset, missedCapColumns578,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have huniv : (Finset.univ : Finset (Fin 6)).card = 6 := by simp
  rw [huniv]
  omega

/-- The exact output currently available for a concentrated deficit column:
five fan entries miss the same blocker, while density independently supplies
two blocker-avoiding cups with disjoint sweep-middle pairs.  The conclusion
intentionally records no identification between the five selected fan rows
and the two density witnesses; proving such a synchronization is the next
color-sensitive obligation. -/
theorem NineOneSidedDeletionFan578.exists_fiveDeficitColumn_and_two_disjoint_restrictedCupMiddlePairs
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    {tree : DecompositionTree χ reservoir}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    {ledger : SixCapVertexDeletionResidualLedger578 joint}
    {minimum : FullResidualCupSixCapCommonMinimum578 matrix}
    {hupper :
      (matrix.cell minimum.row minimum.column).node.upper.Nonempty}
    (fan : NineOneSidedDeletionFan578 ledger minimum hupper)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCup : ¬ContainsCupSet χ reservoir 5)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower) :
    ∃ j : Fin 6,
      5 ≤ (fan.entries.filter fun p ↦
        Disjoint (ledger.cupAt p.1 p.2).1
          (joint.saturation.capAt j)).card ∧
      ∃ cup₁ cup₂ : FourCupIndex578 χ reservoir,
        Disjoint cup₁.1 (joint.saturation.capAt j) ∧
        Disjoint cup₂.1 (joint.saturation.capAt j) ∧
        ¬cup₁.1 ⊆ (matrix.cell minimum.row minimum.column).node.upper ∧
        ¬cup₂.1 ⊆ (matrix.cell minimum.row minimum.column).node.upper ∧
        Disjoint
          (sweepMiddlePair578 cup₁.1
            (mem_capWitnesses.mp cup₁.2).2.1)
          (sweepMiddlePair578 cup₂.1
            (mem_capWitnesses.mp cup₂.2).2.1) := by
  obtain ⟨j, hj⟩ := fan.exists_fiveDeficitColumn hcaps
  refine ⟨j, hj, ?_⟩
  exact minimum.exists_two_disjoint_restrictedCupMiddlePairs
    hreservoir hcard hnoCup hnoCap hnoStrong hcaps j

/-! ## Density produces an exact escaping row -/

/-- When all six caps occupy the lower child of a common minimum, the
complementary at-most-eight child has a local three-boundary.  Exact `32/23`
density then produces a residual cup missed by that boundary.  The full
six-column address matrix classifies the escape as either lower-local or a
complete common-minimum row plateau.

This theorem is the corrected density consumer.  It does not claim that the
local three-boundary hits the full residual family. -/
theorem FullResidualCupSixCapCommonMinimum578.exists_upperBoundary_and_escapeRow_of_capSupport_subset_lower_at_32
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
      (matrix.cell minimum.row minimum.column).node.lower) :
    ∃ boundary,
      boundary ⊆ (matrix.cell minimum.row minimum.column).node.upper ∧
      boundary.card ≤ 3 ∧
      IsCupWitnessTransversal578 χ
        (matrix.cell minimum.row minimum.column).node.upper boundary 4 ∧
      ∃ cup : joint.ResidualCupIndex,
        Disjoint cup.1 boundary ∧
        (cup.1 ⊆ (matrix.cell minimum.row minimum.column).node.lower ∨
          ∀ j, (matrix.cell cup j).path =
            (matrix.cell minimum.row minimum.column).path) := by
  let base := matrix.cell minimum.row minimum.column
  have hlower : 24 ≤ base.node.lower.card := by
    have hle := Finset.card_le_card hcaps
    rw [joint.saturation.capSupport_card] at hle
    exact hle
  obtain ⟨boundary, hboundarySub, hboundaryCard, hboundaryHits⟩ :=
    minimum.upper_exists_threeBoundary_of_twentyFour_le_lower_at_32
      hcard hlower hnoCup
  have hboundarySupport : boundary ⊆ reservoir :=
    hboundarySub.trans (Finset.subset_union_right.trans
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
  exact minimum.cup_subset_lower_or_rowPlateau_of_capSupport_subset_lower
    hcaps indexed

/-- Total exact reconnect for the lower-localized six-cap branch.  A deletion
row either already misses its own source cap, retreats wholly into the
24-vertex lower child, or the all-base/source-meeting hypotheses construct a
nine-source exterior fan.  In the fan branch one column has five deficit
entries and exact `32/23` density independently supplies two blocker-avoiding
cups with disjoint sweep-middle pairs.

The last branch deliberately does not identify the two density witnesses with
the five selected fan rows.  The exact 13-vertex counterexample in
`StructuralChargingNextState578ExteriorDensityCounterexample` shows that a
local identification or two-cover argument cannot be recovered from the
blocker and five rows alone. -/
theorem FullResidualCupSixCapCommonMinimum578.deletionEscape_or_fiveDeficitDensityCoupling_at_32
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
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower) :
    (∃ j c, Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) ∨
    (∃ j c, (ledger.cupAt j c).1 ⊆
      (matrix.cell minimum.row minimum.column).node.lower) ∨
    ∃ hupper :
        (matrix.cell minimum.row minimum.column).node.upper.Nonempty,
      ∃ fan : NineOneSidedDeletionFan578 ledger minimum hupper,
        ∃ j : Fin 6,
          5 ≤ (fan.entries.filter fun p ↦
            Disjoint (ledger.cupAt p.1 p.2).1
              (joint.saturation.capAt j)).card ∧
          ∃ cup₁ cup₂ : FourCupIndex578 χ reservoir,
            Disjoint cup₁.1 (joint.saturation.capAt j) ∧
            Disjoint cup₂.1 (joint.saturation.capAt j) ∧
            ¬cup₁.1 ⊆
              (matrix.cell minimum.row minimum.column).node.upper ∧
            ¬cup₂.1 ⊆
              (matrix.cell minimum.row minimum.column).node.upper ∧
            Disjoint
              (sweepMiddlePair578 cup₁.1
                (mem_capWitnesses.mp cup₁.2).2.1)
              (sweepMiddlePair578 cup₂.1
                (mem_capWitnesses.mp cup₂.2).2.1) := by
  let base := matrix.cell minimum.row minimum.column
  have hnodeSub : base.node.lower ∪ base.node.upper ⊆ reservoir :=
    tree.splitAtPath_support_subset base.lookup
  have hnoCupNode :
      ¬ContainsCupSet χ (base.node.lower ∪ base.node.upper) 5 := by
    intro hcup
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hnodeSub)
  have hnoCapNode :
      ¬ContainsCapSet χ (base.node.lower ∪ base.node.upper) 7 := by
    intro hcap
    exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap
      (hnodeSub.trans Finset.subset_union_right))
  have hupper : base.node.upper.Nonempty := by
    obtain ⟨x, hxUnion, hxNotLower⟩ :=
      Finset.not_subset.mp base.not_all_lower
    rcases Finset.mem_union.mp (base.union_local hxUnion) with
      hxLower | hxUpper
    · exact (hxNotLower hxLower).elim
    · exact ⟨x, hxUpper⟩
  by_cases hmeet : ∀ j c, ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)
  · by_cases hbase : ∀ j c,
        (matrix.cell (ledger.cupAt j c) j).path = base.path
    · right
      right
      obtain ⟨fan⟩ := minimum.exists_nineOneSidedDeletionFan ledger
        hcaps hupper hnoCupNode hnoCapNode hbase hmeet
      refine ⟨hupper, fan, ?_⟩
      exact fan.exists_fiveDeficitColumn_and_two_disjoint_restrictedCupMiddlePairs
        hreservoir hcard hnoCup hnoCap hnoStrong hcaps
    · right
      left
      push Not at hbase
      obtain ⟨j, c, hne⟩ := hbase
      refine ⟨j, c, ?_⟩
      rcases minimum.cup_subset_lower_or_rowPlateau_of_capSupport_subset_lower
          hcaps (ledger.cupAt j c) with hlower | hplateau
      · exact hlower
      · exact (hne (hplateau j)).elim
  · left
    push Not at hmeet
    exact hmeet

end ErdosSzekeres
