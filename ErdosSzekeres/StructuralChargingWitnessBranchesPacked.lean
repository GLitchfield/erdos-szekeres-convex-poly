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
