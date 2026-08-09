module

public import ErdosSzekeres.StructuralChargingNextState578DeletionLedger
public import ErdosSzekeres.StructuralChargingNextState578EightVertex

@[expose] public section

/-!
# Restricted density and sweep-middle pairs at state `(5,7,8)`

The exact `32/23` density remains strong after reserving one saturated
four-cap: every transversal of four-cups disjoint from that cap has at least
six vertices.  At a common-minimum split with all six caps in the large child,
the small child has a three-boundary.  Consequently the sweep-middle pairs of
the remaining cups not wholly in that child cannot have a two-vertex cover.
In particular, two such cups have disjoint sweep-middle pairs.  These cups are
not members of the residual address matrix, so the theorem deliberately does
not claim that their middle vertices lie in the large child.

This is a surviving density consumer, but not yet a local endpoint consumer.
Its next obstruction is to relate the arbitrary density witnesses to the
residual address matrix, or to construct a separate fixed-cap address chain.
-/

namespace ErdosSzekeres

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

/-- A transversal only for reservoir four-cups avoiding a fixed blocker. -/
def IsCupWitnessTransversalAvoiding578
    {n : ℕ} (χ : TripleColoring n)
    (support blocker transversal : Finset (Fin n)) : Prop :=
  transversal ⊆ support ∧
    ∀ cup, cup ∈ capWitnesses χ.dual support 4 →
      Disjoint cup blocker → ¬Disjoint cup transversal

/-- The `32/23` density has an exact blocker/transversal budget: together they
must use at least ten vertices. -/
theorem ten_le_blocker_card_add_restrictedCupTransversal_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir blocker transversal : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hblockerSub : blocker ⊆ reservoir)
    (htransversal : IsCupWitnessTransversalAvoiding578 χ reservoir
      blocker transversal) :
    10 ≤ blocker.card + transversal.card := by
  by_contra hsmall
  have hcandidateSub : blocker ∪ transversal ⊆ reservoir :=
    Finset.union_subset hblockerSub htransversal.1
  have hcandidateCard : (blocker ∪ transversal).card ≤ 9 := by
    have hle := Finset.card_union_le blocker transversal
    omega
  obtain ⟨cup, hcup, hdisjoint⟩ :=
    exists_fourCup_disjoint_from_of_card_le_nine_at_578
      hreservoir hcard hnoCap hnoStrong hcandidateSub hcandidateCard
  have hdisjointBlocker : Disjoint cup blocker :=
    Disjoint.mono_right Finset.subset_union_left hdisjoint
  have hdisjointTransversal : Disjoint cup transversal :=
    Disjoint.mono_right Finset.subset_union_right hdisjoint
  exact (htransversal.2 cup hcup hdisjointBlocker) hdisjointTransversal

/-- Reserving one four-set leaves a sharp six-vertex lower bound for a
transversal of the cups avoiding it. -/
theorem six_le_restrictedCupTransversal_of_blocker_card_four_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir blocker transversal : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (hblockerSub : blocker ⊆ reservoir) (hblockerCard : blocker.card = 4)
    (htransversal : IsCupWitnessTransversalAvoiding578 χ reservoir
      blocker transversal) :
    6 ≤ transversal.card := by
  have hten := ten_le_blocker_card_add_restrictedCupTransversal_at_578
    hreservoir hcard hnoCap hnoStrong hblockerSub htransversal
  omega

/-- The two sweep-middle vertices of a four-set. -/
def sweepMiddlePair578
    {n : ℕ} (four : Finset (Fin n)) (hcard : four.card = 4) :
    Finset (Fin n) :=
  {four.orderEmbOfFin hcard 1, four.orderEmbOfFin hcard 2}

theorem sweepMiddlePair578_card
    {n : ℕ} (four : Finset (Fin n)) (hcard : four.card = 4) :
    (sweepMiddlePair578 four hcard).card = 2 := by
  have hne : four.orderEmbOfFin hcard (1 : Fin 4) ≠
      four.orderEmbOfFin hcard (2 : Fin 4) :=
    (four.orderEmbOfFin hcard).injective.ne (by decide)
  simp [sweepMiddlePair578, hne]

theorem sweepMiddlePair578_subset
    {n : ℕ} (four : Finset (Fin n)) (hcard : four.card = 4) :
    sweepMiddlePair578 four hcard ⊆ four := by
  intro x hx
  simp only [sweepMiddlePair578, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> exact four.orderEmbOfFin_mem hcard _

/-- A vertex set covers the sweep-middle pairs of every four-cup which avoids
`blocker` and is not wholly in `upper`. -/
def CoversRestrictedCupMiddlePairs578
    {n : ℕ} (χ : TripleColoring n)
    (support blocker upper cover : Finset (Fin n)) : Prop :=
  ∀ cup, (hcup : cup ∈ capWitnesses χ.dual support 4) →
    Disjoint cup blocker → ¬cup ⊆ upper →
      ¬Disjoint
        (sweepMiddlePair578 cup (mem_capWitnesses.mp hcup).2.1) cover

/-- A four-cup witness packaged with its ambient membership proof. -/
def FourCupIndex578
    {n : ℕ} (χ : TripleColoring n) (support : Finset (Fin n)) :=
  {cup : Finset (Fin n) // cup ∈ capWitnesses χ.dual support 4}

/-- A three-boundary for upper-local cups plus a two-cover of every remaining
middle pair is a five-vertex transversal of all cups avoiding the blocker. -/
theorem restrictedCupTransversal_union_of_upperBoundary_and_middleCover
    {n : ℕ} {χ : TripleColoring n}
    {support blocker upper upperBoundary middleCover : Finset (Fin n)}
    (hupperSub : upper ⊆ support)
    (hupperBoundary : IsCupWitnessTransversal578 χ upper upperBoundary 4)
    (hmiddleSub : middleCover ⊆ support)
    (hmiddleCover : CoversRestrictedCupMiddlePairs578 χ support blocker upper
      middleCover) :
    IsCupWitnessTransversalAvoiding578 χ support blocker
      (upperBoundary ∪ middleCover) := by
  refine ⟨Finset.union_subset
    (hupperBoundary.1.trans hupperSub) hmiddleSub, ?_⟩
  intro cup hcup hdisjointBlocker
  by_cases hcupUpper : cup ⊆ upper
  · have hcupData := mem_capWitnesses.mp hcup
    have hcupUpperMem : cup ∈ capWitnesses χ.dual upper 4 :=
      mem_capWitnesses.mpr ⟨hcupUpper, hcupData.2⟩
    obtain ⟨x, hxCup, hxBoundary⟩ := Finset.not_disjoint_iff.mp
      (hupperBoundary.2 cup hcupUpperMem)
    exact Finset.not_disjoint_iff.mpr
      ⟨x, hxCup, Finset.mem_union_left _ hxBoundary⟩
  · obtain ⟨x, hxMiddle, hxCover⟩ := Finset.not_disjoint_iff.mp
      (hmiddleCover cup hcup hdisjointBlocker hcupUpper)
    exact Finset.not_disjoint_iff.mpr
      ⟨x, sweepMiddlePair578_subset cup
        (mem_capWitnesses.mp hcup).2.1 hxMiddle,
        Finset.mem_union_right _ hxCover⟩

/-- Under the exact live hypotheses, the crossing-cup middle-pair family
relative to any lower-localized saturated cap has no two-vertex cover. -/
theorem FullResidualCupSixCapCommonMinimum578.no_twoCover_of_restrictedCupMiddlePairs
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
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (j : Fin 6) :
    ¬∃ cover : Finset (Fin n),
      cover ⊆ reservoir ∧ cover.card ≤ 2 ∧
        CoversRestrictedCupMiddlePairs578 χ reservoir
          (joint.saturation.capAt j)
          (matrix.cell minimum.row minimum.column).node.upper cover := by
  rintro ⟨cover, hcoverSub, hcoverCard, hcover⟩
  have hlower : 24 ≤
      (matrix.cell minimum.row minimum.column).node.lower.card := by
    calc
      24 = joint.saturation.capSupport.card :=
        joint.saturation.capSupport_card.symm
      _ ≤ _ := Finset.card_le_card hcaps
  obtain ⟨boundary, hboundarySub, hboundaryCard, hboundary⟩ :=
    minimum.upper_exists_threeBoundary_of_twentyFour_le_lower_at_32
      hcard hlower hnoCup
  have hupperSupport :
      (matrix.cell minimum.row minimum.column).node.upper ⊆ reservoir :=
    Finset.subset_union_right.trans
      (tree.splitAtPath_support_subset
        (matrix.cell minimum.row minimum.column).lookup)
  have htransversal :=
    restrictedCupTransversal_union_of_upperBoundary_and_middleCover
      hupperSupport hboundary hcoverSub hcover
  have hsix := six_le_restrictedCupTransversal_of_blocker_card_four_at_578
    hreservoir hcard hnoCap hnoStrong
    (mem_capWitnesses.mp (joint.saturation.capAt_mem j)).1
    (mem_capWitnesses.mp (joint.saturation.capAt_mem j)).2.1 htransversal
  have hsmall : (boundary ∪ cover).card ≤ 5 := by
    have hle := Finset.card_union_le boundary cover
    omega
  omega

/-- The cover obstruction has a concrete consequence: for every localized
cap column there are two cap-disjoint cups, neither wholly in the small child,
whose ordered sweep-middle pairs are disjoint.  No node-locality conclusion is
claimed for these arbitrary density witnesses. -/
theorem FullResidualCupSixCapCommonMinimum578.exists_two_disjoint_restrictedCupMiddlePairs
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
    (hcaps : joint.saturation.capSupport ⊆
      (matrix.cell minimum.row minimum.column).node.lower)
    (j : Fin 6) :
    ∃ cup₁ cup₂ : FourCupIndex578 χ reservoir,
      Disjoint cup₁.1 (joint.saturation.capAt j) ∧
      Disjoint cup₂.1 (joint.saturation.capAt j) ∧
      ¬cup₁.1 ⊆ (matrix.cell minimum.row minimum.column).node.upper ∧
      ¬cup₂.1 ⊆ (matrix.cell minimum.row minimum.column).node.upper ∧
      Disjoint
        (sweepMiddlePair578 cup₁.1 (mem_capWitnesses.mp cup₁.2).2.1)
        (sweepMiddlePair578 cup₂.1 (mem_capWitnesses.mp cup₂.2).2.1) := by
  classical
  have hnoCover := minimum.no_twoCover_of_restrictedCupMiddlePairs
    hreservoir hcard hnoCup hnoCap hnoStrong hcaps j
  have hexists₁ : ∃ cup₁,
      cup₁ ∈ capWitnesses χ.dual reservoir 4 ∧
      Disjoint cup₁ (joint.saturation.capAt j) ∧
      ¬cup₁ ⊆ (matrix.cell minimum.row minimum.column).node.upper := by
    by_contra hnone
    apply hnoCover
    refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
    intro cup hcup hdisjoint hnotUpper
    exfalso
    exact hnone ⟨cup, hcup, hdisjoint, hnotUpper⟩
  obtain ⟨cup₁, hcup₁, hdisjoint₁, hnotUpper₁⟩ := hexists₁
  let middle₁ := sweepMiddlePair578 cup₁
    (mem_capWitnesses.mp hcup₁).2.1
  have hmiddleCard : middle₁.card = 2 :=
    sweepMiddlePair578_card cup₁ (mem_capWitnesses.mp hcup₁).2.1
  have hmiddleSub : middle₁ ⊆ reservoir :=
    (sweepMiddlePair578_subset cup₁
      (mem_capWitnesses.mp hcup₁).2.1).trans
      (mem_capWitnesses.mp hcup₁).1
  have hexists₂ : ∃ cup₂ : FourCupIndex578 χ reservoir,
      Disjoint cup₂.1 (joint.saturation.capAt j) ∧
      ¬cup₂.1 ⊆ (matrix.cell minimum.row minimum.column).node.upper ∧
      Disjoint
        (sweepMiddlePair578 cup₂.1 (mem_capWitnesses.mp cup₂.2).2.1)
        middle₁ := by
    by_contra hnone
    apply hnoCover
    refine ⟨middle₁, hmiddleSub, by omega, ?_⟩
    intro cup hcup hdisjoint hnotUpper hmiddleDisjoint
    exact hnone ⟨⟨cup, hcup⟩, hdisjoint, hnotUpper, hmiddleDisjoint⟩
  obtain ⟨cup₂, hdisjoint₂, hnotUpper₂, hmiddleDisjoint⟩ := hexists₂
  refine ⟨⟨cup₁, hcup₁⟩, cup₂, hdisjoint₁, hdisjoint₂,
    hnotUpper₁, hnotUpper₂, ?_⟩
  simpa [middle₁] using hmiddleDisjoint.symm

end ErdosSzekeres

end
