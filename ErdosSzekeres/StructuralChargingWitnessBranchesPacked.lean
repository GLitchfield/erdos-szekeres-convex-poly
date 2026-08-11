module

public import ErdosSzekeres.StructuralChargingWitnessBranches

@[expose] public section

/-!
# Exact packed branches for the `(5,6,7)` two-side obstruction

The earlier branch contracts discard the exact total cardinality and the
strong-six deletion packing before reaching their hard leaves.  This file
retains both facts and proves the mechanical reduction to two strictly sharper
obligations.
-/

namespace ErdosSzekeres

/-- Exact internal-witness obstruction at the sharp 22-point boundary. -/
def PackedInternalStrongSixImpossibleAtTwentyTwo567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right polygon : Finset (Fin n)},
    Disjoint left right →
    (∀ x ∈ left, ∀ y ∈ right, x < y) →
    left.card + right.card = 22 →
    7 ≤ left.card → left.card ≤ 15 →
    7 ≤ right.card → right.card ≤ 15 →
    ¬ContainsCapSet χ left 4 →
    ¬ContainsCapSet χ right 4 →
    OneChangeOn χ (left ∪ right) →
    ¬ContainsCapSet χ (left ∪ right) 5 →
    ¬ContainsCupSet χ (left ∪ right) 6 →
    ¬ContainsStrongPolygonSet χ (left ∪ right) 7 →
    StrongSixAvoidsEverySix χ (left ∪ right) →
    polygon.card = 6 →
    IsStrongPolygonSet χ polygon →
    (polygon ⊆ left ∨ polygon ⊆ right) →
    False

/-- The first packed internal leaf after choosing the disjoint strong-six
partner supplied by deletion packing.  Unlike pair-only obstruction
statements, this contract retains the exact 22-point boundary, the internal
placement of `first`, and the full ambient packing hypothesis. -/
def PackedInternalMutuallyMiddleObstructedPairImpossibleAtTwentyTwo567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right first second : Finset (Fin n)},
    Disjoint left right →
    (∀ x ∈ left, ∀ y ∈ right, x < y) →
    left.card + right.card = 22 →
    7 ≤ left.card → left.card ≤ 15 →
    7 ≤ right.card → right.card ≤ 15 →
    ¬ContainsCapSet χ left 4 →
    ¬ContainsCapSet χ right 4 →
    OneChangeOn χ (left ∪ right) →
    ¬ContainsCapSet χ (left ∪ right) 5 →
    ¬ContainsCupSet χ (left ∪ right) 6 →
    ¬ContainsStrongPolygonSet χ (left ∪ right) 7 →
    StrongSixAvoidsEverySix χ (left ∪ right) →
    (first ⊆ left ∨ first ⊆ right) →
    second ⊆ left ∪ right →
    MutuallyMiddleObstructedStrongSixPair χ first second →
    False

/-- At the exact 22-point boundary, two disjoint strong sixes leave a
ten-point residual.  Deletion packing supplies a further strong six after
removing any selected carrier vertex from each polygon and any four residual
vertices. -/
def PackedInternalPairFourResidualEscape {n : ℕ}
    (χ : TripleColoring n)
    (ambient first second : Finset (Fin n)) : Prop :=
  let residual := ambient \ (first ∪ second)
  residual.card = 10 ∧
    ∀ a ∈ first, ∀ b ∈ second,
      ∀ block : Finset (Fin n), block ⊆ residual → block.card = 4 →
        ContainsStrongPolygonSet χ
          (ambient \ insert a (insert b block)) 6

/-- How a third packing witness meets the two designated strong-six
carriers. -/
inductive PairEscapeOccupancy
  | residualOnly
  | oneCarrier
  | twoCarrier

/-- The three exhaustive carrier-occupancy classes for a third witness. -/
def HasPairEscapeOccupancy {n : ℕ}
    (first second third : Finset (Fin n)) : PairEscapeOccupancy → Prop
  | .residualOnly => Disjoint third first ∧ Disjoint third second
  | .oneCarrier =>
      ((¬Disjoint third first) ∧ Disjoint third second) ∨
        (Disjoint third first ∧ (¬Disjoint third second))
  | .twoCarrier => (¬Disjoint third first) ∧ (¬Disjoint third second)

/-- Every third witness belongs to exactly one of the three coarse occupancy
classes.  This logical split is independent of the coloring data. -/
theorem exists_pairEscapeOccupancy {n : ℕ}
    (first second third : Finset (Fin n)) :
    ∃ occupancy, HasPairEscapeOccupancy first second third occupancy := by
  by_cases hfirst : Disjoint third first
  · by_cases hsecond : Disjoint third second
    · exact ⟨.residualOnly, hfirst, hsecond⟩
    · exact ⟨.oneCarrier, Or.inr ⟨hfirst, hsecond⟩⟩
  · by_cases hsecond : Disjoint third second
    · exact ⟨.oneCarrier, Or.inl ⟨hfirst, hsecond⟩⟩
    · exact ⟨.twoCarrier, hfirst, hsecond⟩

/-- The explicit mutually-middle-obstructed pair leaf implies the packed
internal-witness obligation: deletion packing constructs the second polygon,
and strong-seven avoidance supplies all twelve middle failures. -/
theorem packedInternalStrongSixImpossibleAtTwentyTwo567_of_explicit_pair
    (hleaf :
      PackedInternalMutuallyMiddleObstructedPairImpossibleAtTwentyTwo567) :
    PackedInternalStrongSixImpossibleAtTwentyTwo567 := by
  intro n χ left right first hdisjoint horder htotal
    hleftLo hleftHi hrightLo hrightHi hleftCap hrightCap hone
    hnoCap hnoCup hnoStrong hpacking hfirstCard hfirstStrong hfirstSide
  have hfirstSub : first ⊆ left ∪ right :=
    hfirstSide.elim
      (fun h ↦ h.trans Finset.subset_union_left)
      (fun h ↦ h.trans Finset.subset_union_right)
  obtain ⟨second, hsecondSub, hmutual⟩ :=
    exists_mutuallyMiddleObstructed_partner hpacking hfirstSub
      hfirstCard hfirstStrong hnoStrong
  exact hleaf hdisjoint horder htotal hleftLo hleftHi hrightLo hrightHi
    hleftCap hrightCap hone hnoCap hnoCup hnoStrong hpacking
    hfirstSide hsecondSub hmutual

/-- The full packed internal-pair hypotheses imply the universal four-residual
escape normalization.  This is the first point where exact cardinality 22 and
a second use of deletion packing enter after the partner has been chosen. -/
theorem packedInternalPair_has_fourResidualEscape
    {n : ℕ} {χ : TripleColoring n}
    {left right first second : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (htotal : left.card + right.card = 22)
    (hpacking : StrongSixAvoidsEverySix χ (left ∪ right))
    (hfirstSide : first ⊆ left ∨ first ⊆ right)
    (hsecondSub : second ⊆ left ∪ right)
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second) :
    PackedInternalPairFourResidualEscape χ (left ∪ right) first second := by
  have hfirstSub : first ⊆ left ∪ right :=
    hfirstSide.elim
      (fun h ↦ h.trans Finset.subset_union_left)
      (fun h ↦ h.trans Finset.subset_union_right)
  have hpairSub : first ∪ second ⊆ left ∪ right :=
    Finset.union_subset hfirstSub hsecondSub
  have hambientCard : (left ∪ right).card = 22 := by
    rw [Finset.card_union_of_disjoint hdisjoint, htotal]
  have hpairCard : (first ∪ second).card = 12 := by
    rw [Finset.card_union_of_disjoint hmutual.1,
      hmutual.2.1, hmutual.2.2.1]
  refine ⟨?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hpairSub, hambientCard, hpairCard]
  · intro a haFirst b hbSecond block hblockSub hblockCard
    have haAmbient : a ∈ left ∪ right := hfirstSub haFirst
    have hbAmbient : b ∈ left ∪ right := hsecondSub hbSecond
    have hblockAmbient : block ⊆ left ∪ right :=
      hblockSub.trans Finset.sdiff_subset
    have hab : a ≠ b := by
      intro hab
      subst b
      exact Finset.disjoint_left.mp hmutual.1 haFirst hbSecond
    have haBlock : a ∉ block := by
      intro ha
      have haResidual := hblockSub ha
      exact (Finset.mem_sdiff.mp haResidual).2
        (Finset.mem_union_left second haFirst)
    have hbBlock : b ∉ block := by
      intro hb
      have hbResidual := hblockSub hb
      exact (Finset.mem_sdiff.mp hbResidual).2
        (Finset.mem_union_right first hbSecond)
    apply hpacking (insert a (insert b block))
    · exact Finset.insert_subset haAmbient
        (Finset.insert_subset hbAmbient hblockAmbient)
    · simp [hab, haBlock, hbBlock, hblockCard]

/-- In the exact balanced branch, deletion packing should force a strong six
entirely inside one of the two sides. -/
def PackedElevenElevenForcesInternalStrongSix567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right : Finset (Fin n)},
    Disjoint left right →
    (∀ x ∈ left, ∀ y ∈ right, x < y) →
    left.card = 11 →
    right.card = 11 →
    ¬ContainsCapSet χ left 4 →
    ¬ContainsCapSet χ right 4 →
    OneChangeOn χ (left ∪ right) →
    ¬ContainsCapSet χ (left ∪ right) 5 →
    ¬ContainsCupSet χ (left ∪ right) 6 →
    ¬ContainsStrongPolygonSet χ (left ∪ right) 7 →
    StrongSixAvoidsEverySix χ (left ∪ right) →
    ContainsStrongPolygonSet χ left 6 ∨
      ContainsStrongPolygonSet χ right 6

/-- The two exact packed obligations imply the complete two-cap-free-sides
bound.  Any larger counterexample is first restricted to exactly 22 vertices,
without losing order, one-change, or target avoidance. -/
theorem twoCapFreeSidesBound567_of_packed_exact_branches
    (hinternal : PackedInternalStrongSixImpossibleAtTwentyTwo567)
    (hbalanced : PackedElevenElevenForcesInternalStrongSix567) :
    TwoCapFreeSidesBound567 := by
  intro n χ left right hdisjoint horder hleftCap hrightCap hone
    hnoCap hnoCup hnoStrong
  by_contra hnot
  have hlarge : 21 < left.card + right.card := by omega
  have hwindow := two_cap_free_sides_counterexample_card_window
    hone hleftCap hrightCap hnoCup hlarge
  have hrightTarget : 22 - left.card ≤ right.card := by omega
  obtain ⟨right', hrightSub, hrightCard⟩ :=
    Finset.exists_subset_card_eq hrightTarget
  have hdisjoint' : Disjoint left right' :=
    hdisjoint.mono Finset.Subset.rfl hrightSub
  have horder' : ∀ x ∈ left, ∀ y ∈ right', x < y := by
    intro x hx y hy
    exact horder x hx y (hrightSub hy)
  have hunionSub : left ∪ right' ⊆ left ∪ right :=
    Finset.union_subset_union Finset.Subset.rfl hrightSub
  have htotal : left.card + right'.card = 22 := by
    rw [hrightCard]
    omega
  have hrightCap' : ¬ContainsCapSet χ right' 4 := by
    intro hcap
    exact hrightCap (FinsetPolygon.ContainsCapSet.mono hcap hrightSub)
  have hone' : OneChangeOn χ (left ∪ right') := hone.mono hunionSub
  have hnoCap' : ¬ContainsCapSet χ (left ∪ right') 5 := by
    intro hcap
    exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hunionSub)
  have hnoCup' : ¬ContainsCupSet χ (left ∪ right') 6 := by
    intro hcup
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hunionSub)
  have hnoStrong' : ¬ContainsStrongPolygonSet χ (left ∪ right') 7 := by
    intro hstrong
    exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub)
  have hcardUnion : (left ∪ right').card = 22 := by
    rw [Finset.card_union_of_disjoint hdisjoint', htotal]
  have hpacking : StrongSixAvoidsEverySix χ (left ∪ right') :=
    strongSixAvoidsEverySix_of_card_ge_twenty_two hone'
      (by omega) hnoCap' hnoCup'
  rcases two_cap_free_sides_contains_internal_strongSix_or_eleven_eleven
      hone' hleftCap hrightCap' hnoCup' hwindow.2.1 (by
        rw [hrightCard]
        omega) (by omega) with
      hleftStrong | hrightStrong | hbalancedCards
  · obtain ⟨polygon, _hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hleftStrong
    exact hinternal hdisjoint' horder' htotal hwindow.1 hwindow.2.1
      (by rw [hrightCard]; omega) (by rw [hrightCard]; omega)
      hleftCap hrightCap' hone'
      hnoCap' hnoCup' hnoStrong' hpacking hpolygonCard hpolygonStrong
      (Or.inl _hpolygonSub)
  · obtain ⟨polygon, _hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hrightStrong
    exact hinternal hdisjoint' horder' htotal hwindow.1 hwindow.2.1
      (by rw [hrightCard]; omega) (by rw [hrightCard]; omega)
      hleftCap hrightCap' hone'
      hnoCap' hnoCup' hnoStrong' hpacking hpolygonCard hpolygonStrong
      (Or.inr _hpolygonSub)
  · rcases hbalanced hdisjoint' horder' hbalancedCards.1 hbalancedCards.2
      hleftCap hrightCap' hone' hnoCap' hnoCup' hnoStrong' hpacking with
      hleftStrong | hrightStrong
    · obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hleftStrong
      exact hinternal hdisjoint' horder' htotal hwindow.1 hwindow.2.1
        (by rw [hrightCard]; omega) (by rw [hrightCard]; omega)
        hleftCap hrightCap' hone'
        hnoCap' hnoCup' hnoStrong' hpacking hpolygonCard hpolygonStrong
        (Or.inl hpolygonSub)
    · obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hrightStrong
      exact hinternal hdisjoint' horder' htotal hwindow.1 hwindow.2.1
        (by rw [hrightCard]; omega) (by rw [hrightCard]; omega)
        hleftCap hrightCap' hone'
        hnoCap' hnoCup' hnoStrong' hpacking hpolygonCard hpolygonStrong
        (Or.inr hpolygonSub)

end ErdosSzekeres

end
