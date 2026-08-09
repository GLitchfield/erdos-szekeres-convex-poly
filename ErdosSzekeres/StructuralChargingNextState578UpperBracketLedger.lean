module

public import ErdosSzekeres.StructuralChargingNextState578UpperBracket

@[expose] public section

/-!
# The exact deletion-ledger bracket split

In the lower-localized all-base branch, every source-indexed deletion cup
either has exactly one upper sweep endpoint or gives an actual upper bracket
containing its source cap vertex.  This is the strongest direct consequence
of the current endpoint law.  The collective state must still eliminate or
charge the one-upper alternative.
-/

namespace ErdosSzekeres

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

/-- If a deletion cup meets its source cap, its source vertex belongs to the
cup: the ledger already makes the cup disjoint from the other three cap
vertices. -/
theorem SixCapVertexDeletionResidualLedger578.source_mem_of_not_disjoint
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (j : Fin 6) (c : {x : Fin n // x ∈ joint.saturation.capAt j})
    (hmeet : ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) :
    c.1 ∈ (ledger.cupAt j c).1 := by
  obtain ⟨x, hxCup, hxCap⟩ := Finset.not_disjoint_iff.mp hmeet
  have hxc : x = c.1 := by
    by_contra hxne
    exact (Finset.disjoint_left.mp (ledger.avoidsOther j c)) hxCup
      (Finset.mem_erase.mpr ⟨hxne, hxCap⟩)
  simpa [hxc] using hxCup

/-- The exact base-row split for one deletion entry.  A lower-localized source
cap makes the cap-endpoint alternative impossible, and base locality makes
the residual cup genuinely straddle the node. -/
theorem SixCapVertexDeletionResidualLedger578.oneUpper_or_twoUpper_of_base
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (j : Fin 6) (c : {x : Fin n // x ∈ joint.saturation.capAt j})
    (hbase : (matrix.cell (ledger.cupAt j c) j).path =
      (matrix.cell minimum.row minimum.column).path)
    (hmeet : ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) :
    CupFourOneUpperEndpointShape578 (ledger.cupAt j c).1
        (matrix.cell minimum.row minimum.column).node.lower
        (matrix.cell minimum.row minimum.column).node.upper ∨
      CupFourTwoUpperBracketShape578 (ledger.cupAt j c).1
        (matrix.cell minimum.row minimum.column).node.lower
        (matrix.cell minimum.row minimum.column).node.upper := by
  let base := matrix.cell minimum.row minimum.column
  let cell := matrix.cell (ledger.cupAt j c) j
  have hnode : cell.node = base.node := by
    have hlookup := cell.lookup
    rw [hbase, base.lookup] at hlookup
    exact (Option.some.inj hlookup).symm
  have hcapLower : joint.saturation.capAt j ⊆ base.node.lower :=
    (joint.saturation.capAt_subset_capSupport j).trans hcaps
  have hshape : CupFourLowerEndpointShape578 (ledger.cupAt j c).1
      base.node.lower base.node.upper := by
    rcases ledger.endpointShapes_of_base_of_not_disjoint minimum j c hbase hmeet with
        hcup | hcap
    · exact hcup.2
    · exact (hcap.1 hcapLower).elim
  have hcupSub : (ledger.cupAt j c).1 ⊆
      base.node.lower ∪ base.node.upper := by
    have hlocal : (ledger.cupAt j c).1 ∪ joint.saturation.capAt j ⊆
        cell.node.lower ∪ cell.node.upper := cell.union_local
    rw [hnode] at hlocal
    exact Finset.subset_union_left.trans hlocal
  have hnotLower : ¬(ledger.cupAt j c).1 ⊆ base.node.lower := by
    intro hcupLower
    apply cell.not_all_lower
    rw [hnode]
    exact Finset.union_subset hcupLower hcapLower
  exact hshape.oneUpper_or_twoUpper hcupSub hnotLower

/-- In the two-upper branch the indexed source itself is paid for by the
corresponding upper bracket. -/
theorem SixCapVertexDeletionResidualLedger578.oneUpper_or_source_in_bracket_of_base
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (j : Fin 6) (c : {x : Fin n // x ∈ joint.saturation.capAt j})
    (hbase : (matrix.cell (ledger.cupAt j c) j).path =
      (matrix.cell minimum.row minimum.column).path)
    (hmeet : ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) :
    CupFourOneUpperEndpointShape578 (ledger.cupAt j c).1
        (matrix.cell minimum.row minimum.column).node.lower
        (matrix.cell minimum.row minimum.column).node.upper ∨
      ∃ hcard : (ledger.cupAt j c).1.card = 4,
        c.1 ∈ lowerBracket578
          (matrix.cell minimum.row minimum.column).node.lower
          ((ledger.cupAt j c).1.orderEmbOfFin hcard 0)
          ((ledger.cupAt j c).1.orderEmbOfFin hcard 3) := by
  rcases ledger.oneUpper_or_twoUpper_of_base minimum hcaps j c hbase hmeet with
      hone | htwo
  · exact Or.inl hone
  · right
    apply htwo.mem_lowerBracket_of_mem_lower
      (matrix.cell minimum.row minimum.column).node.deep.disjoint
      (ledger.source_mem_of_not_disjoint j c hmeet)
    exact (joint.saturation.capAt_subset_capSupport j).trans hcaps c.2

/-- The source payment alternative is available simultaneously for all 24
entries.  This packages the exact global obstruction: the bracket route can
close only after controlling the one-upper rows collectively. -/
theorem SixCapVertexDeletionResidualLedger578.all_sources_oneUpper_or_in_bracket
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (hbase : ∀ j c, (matrix.cell (ledger.cupAt j c) j).path =
      (matrix.cell minimum.row minimum.column).path)
    (hmeet : ∀ j c, ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) :
    ∀ j c,
      CupFourOneUpperEndpointShape578 (ledger.cupAt j c).1
          (matrix.cell minimum.row minimum.column).node.lower
          (matrix.cell minimum.row minimum.column).node.upper ∨
        ∃ hcard : (ledger.cupAt j c).1.card = 4,
          c.1 ∈ lowerBracket578
            (matrix.cell minimum.row minimum.column).node.lower
            ((ledger.cupAt j c).1.orderEmbOfFin hcard 0)
            ((ledger.cupAt j c).1.orderEmbOfFin hcard 3) := by
  intro j c
  exact ledger.oneUpper_or_source_in_bracket_of_base minimum hcaps j c
    (hbase j c) (hmeet j c)

/-! ## The exact `24 → 18 → 9` exterior-fan reduction -/

/-- The global upper span contains at most six of the 24 saturated cap
vertices.  At least nine cap vertices therefore lie strictly on one common
side of that span. -/
theorem FullResidualCupSixCapCommonMinimum578.nine_capSources_on_one_side_of_upperSpan
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty)
    (hnoCup : ¬ContainsCupSet χ
      ((matrix.cell minimum.row minimum.column).node.lower ∪
        (matrix.cell minimum.row minimum.column).node.upper) 5)
    (hnoCap : ¬ContainsCapSet χ
      ((matrix.cell minimum.row minimum.column).node.lower ∪
        (matrix.cell minimum.row minimum.column).node.upper) 7) :
    9 ≤ (belowPivot578 joint.saturation.capSupport
        ((matrix.cell minimum.row minimum.column).node.upper.min' hupper)).card ∨
      9 ≤ (abovePivot578 joint.saturation.capSupport
        ((matrix.cell minimum.row minimum.column).node.upper.max' hupper)).card := by
  let node := (matrix.cell minimum.row minimum.column).node
  let left := node.upper.min' hupper
  let right := node.upper.max' hupper
  let exteriorLeft := belowPivot578 joint.saturation.capSupport left
  let interior := joint.saturation.capSupport.filter fun x ↦ left < x ∧ x < right
  let exteriorRight := abovePivot578 joint.saturation.capSupport right
  have hleftUpper : left ∈ node.upper := Finset.min'_mem _ _
  have hrightUpper : right ∈ node.upper := Finset.max'_mem _ _
  have hinteriorSub : interior ⊆ lowerBracket578 node.lower left right := by
    intro x hx
    have hxData := Finset.mem_filter.mp hx
    exact mem_lowerBracket578.mpr ⟨hcaps hxData.1, hxData.2⟩
  have hinteriorCard : interior.card ≤ 6 := by
    exact (Finset.card_le_card hinteriorSub).trans
      (node.deep.lowerBracket578_card_le_six hleftUpper hrightUpper hnoCup hnoCap)
  have hcover : joint.saturation.capSupport ⊆
      exteriorLeft ∪ interior ∪ exteriorRight := by
    intro x hx
    by_cases hxLeft : x < left
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (mem_belowPivot578.mpr ⟨hx, hxLeft⟩))
    by_cases hxRight : right < x
    · exact Finset.mem_union_right _ (mem_abovePivot578.mpr ⟨hx, hxRight⟩)
    have hleftStrict : left < x := by
      have hxLower : x ∈ node.lower := hcaps hx
      have hxNotUpper : x ∉ node.upper := by
        exact fun hxUpper ↦ (Finset.disjoint_left.mp node.deep.disjoint) hxLower hxUpper
      have hxNe : x ≠ left := fun h ↦ hxNotUpper (h ▸ hleftUpper)
      omega
    have hrightStrict : x < right := by
      have hxLower : x ∈ node.lower := hcaps hx
      have hxNotUpper : x ∉ node.upper := by
        exact fun hxUpper ↦ (Finset.disjoint_left.mp node.deep.disjoint) hxLower hxUpper
      have hxNe : x ≠ right := fun h ↦ hxNotUpper (h ▸ hrightUpper)
      omega
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hx, hleftStrict, hrightStrict⟩))
  by_contra hsmall
  simp only [not_or, not_le] at hsmall
  change exteriorLeft.card < 9 ∧ exteriorRight.card < 9 at hsmall
  have hcapCard := joint.saturation.capSupport_card
  have hcovered := Finset.card_le_card hcover
  have hcoverBound : (exteriorLeft ∪ interior ∪ exteriorRight).card ≤
      exteriorLeft.card + interior.card + exteriorRight.card := by
    calc
      _ ≤ (exteriorLeft ∪ interior).card + exteriorRight.card :=
        Finset.card_union_le _ _
      _ ≤ (exteriorLeft.card + interior.card) + exteriorRight.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  omega

/-- A source strictly below the minimum upper vertex cannot lie in a genuine
two-upper bracket, so its deletion row has exactly one upper endpoint. -/
theorem SixCapVertexDeletionResidualLedger578.oneUpper_of_source_below_upperMin
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty)
    (j : Fin 6) (c : {x : Fin n // x ∈ joint.saturation.capAt j})
    (hbase : (matrix.cell (ledger.cupAt j c) j).path =
      (matrix.cell minimum.row minimum.column).path)
    (hmeet : ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j))
    (hsource : c.1 <
      (matrix.cell minimum.row minimum.column).node.upper.min' hupper) :
    CupFourOneUpperEndpointShape578 (ledger.cupAt j c).1
      (matrix.cell minimum.row minimum.column).node.lower
      (matrix.cell minimum.row minimum.column).node.upper := by
  rcases ledger.oneUpper_or_twoUpper_of_base minimum hcaps j c hbase hmeet with
      hone | htwo
  · exact hone
  · have htwoCopy := htwo
    rcases htwo with ⟨hcard, hleftUpper, _, _, _⟩
    have hsourceBracket := htwoCopy.mem_lowerBracket_of_mem_lower
      (matrix.cell minimum.row minimum.column).node.deep.disjoint
      (ledger.source_mem_of_not_disjoint j c hmeet)
      ((joint.saturation.capAt_subset_capSupport j).trans hcaps c.2)
    rcases hsourceBracket with ⟨_, hsourceBetween⟩
    have hminLe := Finset.min'_le _ _ hleftUpper
    have hleftLt := (mem_lowerBracket578.mp hsourceBetween).2.1
    omega

/-- The symmetric exterior-source statement above the maximum upper vertex. -/
theorem SixCapVertexDeletionResidualLedger578.oneUpper_of_upperMax_lt_source
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty)
    (j : Fin 6) (c : {x : Fin n // x ∈ joint.saturation.capAt j})
    (hbase : (matrix.cell (ledger.cupAt j c) j).path =
      (matrix.cell minimum.row minimum.column).path)
    (hmeet : ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j))
    (hsource :
      (matrix.cell minimum.row minimum.column).node.upper.max' hupper < c.1) :
    CupFourOneUpperEndpointShape578 (ledger.cupAt j c).1
      (matrix.cell minimum.row minimum.column).node.lower
      (matrix.cell minimum.row minimum.column).node.upper := by
  rcases ledger.oneUpper_or_twoUpper_of_base minimum hcaps j c hbase hmeet with
      hone | htwo
  · exact hone
  · have htwoCopy := htwo
    rcases htwo with ⟨hcard, _, hrightUpper, _, _⟩
    have hsourceBracket := htwoCopy.mem_lowerBracket_of_mem_lower
      (matrix.cell minimum.row minimum.column).node.deep.disjoint
      (ledger.source_mem_of_not_disjoint j c hmeet)
      ((joint.saturation.capAt_subset_capSupport j).trans hcaps c.2)
    rcases hsourceBracket with ⟨_, hsourceBetween⟩
    have hleMax := Finset.le_max' _ _ hrightUpper
    have hltRight := (mem_lowerBracket578.mp hsourceBetween).2.2
    omega

/-- The exact surviving global object after the local two-column bracket
candidate fails: nine saturated cap vertices lie on one exterior side of the
upper span, and every corresponding deletion row has exactly one upper sweep
endpoint. -/
structure NineOneSidedDeletionFan578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty) where
  sources : Finset (Fin n)
  sources_subset : sources ⊆ joint.saturation.capSupport
  nine_le : 9 ≤ sources.card
  one_side :
    (∀ x ∈ sources,
      x < (matrix.cell minimum.row minimum.column).node.upper.min' hupper) ∨
    (∀ x ∈ sources,
      (matrix.cell minimum.row minimum.column).node.upper.max' hupper < x)
  row_oneUpper : ∀ j c, c.1 ∈ sources →
    CupFourOneUpperEndpointShape578 (ledger.cupAt j c).1
      (matrix.cell minimum.row minimum.column).node.lower
      (matrix.cell minimum.row minimum.column).node.upper

/-- Nine distinct saturated cap vertices cannot be covered by only two of the
six four-cap columns. -/
theorem SixCapSaturation578.nineSet_not_subset_two_capAt
    {n : ℕ} {χ : TripleColoring n} {support sources : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    (hnine : 9 ≤ sources.card) (i j : Fin 6) :
    ¬sources ⊆ saturation.capAt i ∪ saturation.capAt j := by
  intro hsub
  have hi := (mem_capWitnesses.mp (saturation.capAt_mem i)).2.1
  have hj := (mem_capWitnesses.mp (saturation.capAt_mem j)).2.1
  have hs := Finset.card_le_card hsub
  have hu := Finset.card_union_le (saturation.capAt i) (saturation.capAt j)
  omega

/-- The `24 → 18 → 9` count and the exterior-source lemmas assemble into
an actual nine-source fan.  Any continuation of the bracket route must now
consume this collective object rather than a pair of cap columns. -/
theorem FullResidualCupSixCapCommonMinimum578.exists_nineOneSidedDeletionFan
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    {matrix : FullResidualCupSixCapAddressMatrix578 joint tree}
    (minimum : FullResidualCupSixCapCommonMinimum578 matrix)
    (ledger : SixCapVertexDeletionResidualLedger578 joint)
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (hupper : (matrix.cell minimum.row minimum.column).node.upper.Nonempty)
    (hnoCup : ¬ContainsCupSet χ
      ((matrix.cell minimum.row minimum.column).node.lower ∪
        (matrix.cell minimum.row minimum.column).node.upper) 5)
    (hnoCap : ¬ContainsCapSet χ
      ((matrix.cell minimum.row minimum.column).node.lower ∪
        (matrix.cell minimum.row minimum.column).node.upper) 7)
    (hbase : ∀ j c, (matrix.cell (ledger.cupAt j c) j).path =
      (matrix.cell minimum.row minimum.column).path)
    (hmeet : ∀ j c, ¬Disjoint (ledger.cupAt j c).1
      (joint.saturation.capAt j)) :
    Nonempty (NineOneSidedDeletionFan578 ledger minimum hupper) := by
  rcases minimum.nine_capSources_on_one_side_of_upperSpan hcaps hupper
      hnoCup hnoCap with hleft | hright
  · let sources := belowPivot578 joint.saturation.capSupport
      ((matrix.cell minimum.row minimum.column).node.upper.min' hupper)
    refine ⟨{
      sources := sources
      sources_subset := ?_
      nine_le := hleft
      one_side := Or.inl ?_
      row_oneUpper := ?_
    }⟩
    · intro x hx
      exact (mem_belowPivot578.mp hx).1
    · intro x hx
      exact (mem_belowPivot578.mp hx).2
    · intro j c hc
      exact ledger.oneUpper_of_source_below_upperMin minimum hcaps hupper j c
        (hbase j c) (hmeet j c) (mem_belowPivot578.mp hc).2
  · let sources := abovePivot578 joint.saturation.capSupport
      ((matrix.cell minimum.row minimum.column).node.upper.max' hupper)
    refine ⟨{
      sources := sources
      sources_subset := ?_
      nine_le := hright
      one_side := Or.inr ?_
      row_oneUpper := ?_
    }⟩
    · intro x hx
      exact (mem_abovePivot578.mp hx).1
    · intro x hx
      exact (mem_abovePivot578.mp hx).2
    · intro j c hc
      exact ledger.oneUpper_of_upperMax_lt_source minimum hcaps hupper j c
        (hbase j c) (hmeet j c) (mem_abovePivot578.mp hc).2

end ErdosSzekeres

end
