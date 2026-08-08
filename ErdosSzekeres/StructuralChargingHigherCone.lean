module

public import ErdosSzekeres.StructuralChargingPivotOverflow
public import ErdosSzekeres.E3FiniteReduction

@[expose] public section

/-!
# Higher-index pivot cones

The minimum lower vertex is a common cone point for every canonical hidden-lower pivot.
Consequently, excluding an `(a + 1)`-cap in the parent excludes an `a`-cap on the
complete pivot seed.  This is the parameter-uniform geometric half of the higher-index
selected-core capacity bridge.
-/

namespace ErdosSzekeres

/-- Coning an upper pivot cap with the minimum lower vertex would produce a parent cap
with one additional vertex. -/
theorem hiddenLowerGapEnteringPivotSeed_avoids_cap_of_no_parent_cap_succ
    {n a : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlower : lower.Nonempty)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) (a + 1)) :
    ¬ContainsCapSet chi (hiddenGapEnteringPivotSeed lower upper .right) a := by
  let q := lower.min' hlower
  have hqLower : q ∈ lower := Finset.min'_mem lower hlower
  have hnoEndpoint :
      ¬∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = a ∧
        IsCapSet chi cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q := by
    rintro ⟨cap, hcapSub, hcapCard, hcap, hendpoint⟩
    apply hnoCap
    exact hdeep.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcap hqLower hendpoint
  have hrightAvoid : ¬ContainsCapSet chi (upper.filter (q < ·)) a :=
    (gap_sides_avoid_cap_of_no_endpoint_cap hnoEndpoint).2
  intro hseedCap
  apply hrightAvoid
  exact FinsetPolygon.ContainsCapSet.mono hseedCap
    (hiddenLowerGapEnteringPivotSeed_subset_upper_right_of_min hdeep hlower)

/-- The smaller off-diagonal E3 state converts cone avoidance into the sharp
published threshold.  This is stronger than the ordinary cup--cap estimate and
is the noncircular consumer when the predecessor state is available by
well-founded induction. -/
theorem hiddenLowerGapSource_card_le_of_predecessor_state
    {n a u k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlower : lower.Nonempty)
    (hupper : IsDecomposableOn chi upper)
    (hstate : DecomposableStateUpper a u k)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) (a + 1))
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) u)
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    Fintype.card (HiddenGapSource lower upper .right) ≤
      decomposableThreshold a u k := by
  rw [← hiddenGapEnteringPivotSeed_card lower upper .right]
  let seed := hiddenGapEnteringPivotSeed lower upper .right
  have hseedUpper : seed ⊆ upper :=
    (hiddenLowerGapEnteringPivotSeed_subset_upper_right_of_min hdeep hlower).trans
      (Finset.filter_subset _ _)
  have hseedParent : seed ⊆ lower ∪ upper :=
    hseedUpper.trans Finset.subset_union_right
  have hnoSeedCap : ¬ContainsCapSet chi seed a :=
    hiddenLowerGapEnteringPivotSeed_avoids_cap_of_no_parent_cap_succ
      hdeep hlower hnoCap
  by_contra hnot
  have hlarge : decomposableThreshold a u k < seed.card :=
    Nat.lt_of_not_ge hnot
  have hseedNonempty : seed.Nonempty := Finset.card_pos.mp (by omega)
  have hseedDecomposable : IsDecomposableOn chi seed :=
    hupper.subset hseedUpper hseedNonempty
  rcases hstate hseedDecomposable hlarge with hcap | hcup | hstrong
  · exact hnoSeedCap hcap
  · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hseedParent)
  · exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hseedParent)

/-- Every canonical pivot for a hidden upper gap lies in the lower child and
strictly to the left of the maximum upper vertex. -/
theorem hiddenUpperGapEnteringPivotSeed_subset_lower_left_of_max
    {n : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hupper : upper.Nonempty) :
    hiddenGapEnteringPivotSeed lower upper .left ⊆
      lower.filter (· < upper.max' hupper) := by
  intro pivot hpivot
  obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp hpivot
  have hpivotLower := source.enteringPivot_mem_oppositeChild hdeep.disjoint
  have hrightUpper : source.1.right ∈ upper :=
    (mem_hiddenGapSources_iff.mp source.2).1.2.2.1
  have hrightMax : source.1.right ≤ upper.max' hupper :=
    Finset.le_max' upper source.1.right hrightUpper
  exact Finset.mem_filter.mpr
    ⟨hpivotLower, source.enteringPivot_between.2.trans_le hrightMax⟩

/-- Color-dually, coning a lower pivot cup with the maximum upper vertex
would produce a parent cup with one additional vertex. -/
theorem hiddenUpperGapEnteringPivotSeed_avoids_cup_of_no_parent_cup_succ
    {n u : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hupper : upper.Nonempty)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) (u + 1)) :
    ¬ContainsCupSet chi (hiddenGapEnteringPivotSeed lower upper .left) u := by
  let q := upper.max' hupper
  have hqUpper : q ∈ upper := Finset.max'_mem upper hupper
  rintro ⟨cup, hcupSub, hcupCard, hcup⟩
  apply hnoCup
  have hcupLower : cup ⊆ lower :=
    hcupSub.trans
      ((hiddenUpperGapEnteringPivotSeed_subset_lower_left_of_max
        hdeep hupper).trans (Finset.filter_subset _ _))
  have hendpoint : HasDeepBelowSplit.IsSweepEndpoint cup q := Or.inr (by
    intro x hx
    have hxSeed := hcupSub hx
    have hxLeft := hiddenUpperGapEnteringPivotSeed_subset_lower_left_of_max
      hdeep hupper hxSeed
    exact (Finset.mem_filter.mp hxLeft).2.le)
  exact hdeep.containsCupSet_succ_of_upper_endpoint
    hcupLower hcupCard hcup hqUpper hendpoint

/-- The color-dual predecessor state gives the sharp threshold for all hidden
upper-gap sources. -/
theorem hiddenUpperGapSource_card_le_of_predecessor_state
    {n a u k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hupper : upper.Nonempty)
    (hlower : IsDecomposableOn chi lower)
    (hstate : DecomposableStateUpper a u k)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) a)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) (u + 1))
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    Fintype.card (HiddenGapSource lower upper .left) ≤
      decomposableThreshold a u k := by
  rw [← hiddenGapEnteringPivotSeed_card lower upper .left]
  let seed := hiddenGapEnteringPivotSeed lower upper .left
  have hseedLower : seed ⊆ lower :=
    (hiddenUpperGapEnteringPivotSeed_subset_lower_left_of_max hdeep hupper).trans
      (Finset.filter_subset _ _)
  have hseedParent : seed ⊆ lower ∪ upper :=
    hseedLower.trans Finset.subset_union_left
  have hnoSeedCup : ¬ContainsCupSet chi seed u :=
    hiddenUpperGapEnteringPivotSeed_avoids_cup_of_no_parent_cup_succ
      hdeep hupper hnoCup
  by_contra hnot
  have hlarge : decomposableThreshold a u k < seed.card :=
    Nat.lt_of_not_ge hnot
  have hseedNonempty : seed.Nonempty := Finset.card_pos.mp (by omega)
  have hseedDecomposable : IsDecomposableOn chi seed :=
    hlower.subset hseedLower hseedNonempty
  rcases hstate hseedDecomposable hlarge with hcap | hcup | hstrong
  · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hseedParent)
  · exact hnoSeedCup hcup
  · exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hseedParent)

/-- Once the selected upper-child index is identified with the predecessor cap
parameter, the predecessor-state bound constructs one actual published slice
that retains every canonical pivot simultaneously. -/
theorem exists_publishedUpperPivotSlice_of_predecessor_state
    {n outerA a u k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (houterA : 1 ≤ outerA)
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlower : lower.Nonempty)
    (hupperNonempty : upper.Nonempty)
    (hupper : IsDecomposableOn chi upper)
    (hindex : publishedCapChildIndex outerA u k upper.card = a)
    (hstate : DecomposableStateUpper a u k)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) (a + 1))
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) u)
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    ∃ slice : PublishedCapChildSlice outerA u k upper,
      ∀ source : HiddenGapSource lower upper .right,
        source.enteringPivot ∈ slice.core := by
  have hbound := hiddenLowerGapSource_card_le_of_predecessor_state
    hdeep hlower hupper hstate hnoCap hnoCup hnoStrong
  apply exists_publishedUpperPivotSlice_of_card_le
    houterA hupperNonempty hdeep.disjoint
  rw [hindex]
  omega

/-- The color-dual selected lower-child slice retains every hidden-upper-gap
pivot when its published cup index is the available predecessor parameter. -/
theorem exists_publishedLowerPivotSlice_of_predecessor_state
    {n a outerU u k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (houterU : 1 ≤ outerU)
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlowerNonempty : lower.Nonempty)
    (hupper : upper.Nonempty)
    (hlower : IsDecomposableOn chi lower)
    (hindex : publishedChildIndex a outerU k lower.card = u)
    (hstate : DecomposableStateUpper a u k)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) a)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) (u + 1))
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    ∃ slice : PublishedChildSlice a outerU k lower,
      ∀ source : HiddenGapSource lower upper .left,
        source.enteringPivot ∈ slice.core := by
  have hbound := hiddenUpperGapSource_card_le_of_predecessor_state
    hdeep hupper hlower hstate hnoCap hnoCup hnoStrong
  apply exists_publishedLowerPivotSlice_of_card_le
    houterU hlowerNonempty hdeep.disjoint
  rw [hindex]
  omega

/-- The first higher-index scalar gate records why the predecessor state is
essential: ordinary `(4,8)` cup--cap counting permits 28 vertices, while the
active decomposable predecessor threshold is 22 and its retained core has 23
slots. -/
theorem higher_index_cone_predecessor_arithmetic_at_588 :
    Nat.choose 8 2 = 28 ∧
      decomposableThreshold 4 8 8 = 22 ∧
      decomposableThreshold 4 8 8 + 1 = 23 ∧
      ¬Nat.choose 8 2 ≤ decomposableThreshold 4 8 8 + 1 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
    Finset.sum_Icc_succ_top]

end ErdosSzekeres
