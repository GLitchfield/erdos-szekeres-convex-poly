module

public import ErdosSzekeres.StructuralChargingSelectedBranchPivot
public import ErdosSzekeres.Duality

@[expose] public section

/-!
# Extremal pivot-overflow normal forms

The first failure of the coarse selected-core estimate appears when a
ten-vertex lower child could contribute nine hidden lower gaps.  Cardinal
equality would force every lower adjacency to be hidden and give nine distinct
interleaved upper pivots.

Deep-below geometry rules out that apparent overflow.  The minimum lower
vertex cones any cap triple of pivots into a parent four-cap, so no four-cap
makes the whole pivot seed a cup.  No parent `u`-cup then bounds the seed by
`u - 1`, which exactly pays every published index-three upper core.  The file
also proves the color-dual bound and constructs the actual normalized
`(4,8,8)`, `10+13` published slice.
-/

namespace ErdosSzekeres

/-- At equality in the source-adjacency count, forgetting hiddenness is a
bijection onto all source-child adjacencies. -/
theorem hiddenLowerGapSourceAdjacencyEmbedding_bijective_of_card_eq
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hcard : Fintype.card (HiddenGapSource lower upper .right) =
      Fintype.card (SweepAdjacency lower)) :
    Function.Bijective (hiddenLowerGapSourceAdjacencyEmbedding lower upper) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨(hiddenLowerGapSourceAdjacencyEmbedding lower upper).injective, hcard⟩

/-- The resulting canonical equivalence between hidden lower sources and all
lower sweep adjacencies. -/
noncomputable def hiddenLowerGapSourceAdjacencyEquiv
    {n : ℕ} (lower upper : Finset (Fin n))
    (hcard : Fintype.card (HiddenGapSource lower upper .right) =
      Fintype.card (SweepAdjacency lower)) :
    HiddenGapSource lower upper .right ≃ SweepAdjacency lower :=
  Equiv.ofBijective (hiddenLowerGapSourceAdjacencyEmbedding lower upper)
    (hiddenLowerGapSourceAdjacencyEmbedding_bijective_of_card_eq hcard)

/-- Equality means that every lower adjacency is hidden, not merely that the
two finite types have the same size. -/
theorem every_lower_adjacency_hidden_of_card_eq
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hcard : Fintype.card (HiddenGapSource lower upper .right) =
      Fintype.card (SweepAdjacency lower))
    (gap : SweepAdjacency lower) :
    IsHiddenLowerGap lower upper gap.1 := by
  have hbij := hiddenLowerGapSourceAdjacencyEmbedding_bijective_of_card_eq
    hcard
  obtain ⟨source, hsource⟩ := hbij.2 gap
  have hhidden : IsHiddenLowerGap lower upper source.1 :=
    mem_hiddenGapSources_iff.mp source.2
  have hspan : source.1 = gap.1 := congrArg Subtype.val hsource
  simpa [hspan] using hhidden

/-- At the first scalar obstruction, nine possible hidden lower gaps are
necessarily exactly all nine adjacencies of the ten-vertex lower child. -/
theorem k8_hiddenLowerGapSource_card_eq_nine
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hlowerCard : lower.card = 10)
    (hoverflow : 9 ≤ Fintype.card (HiddenGapSource lower upper .right)) :
    Fintype.card (HiddenGapSource lower upper .right) = 9 := by
  have hle := hiddenLowerGapSource_card_le lower upper hlower
  omega

/-- Hence the source-forgetting map is bijective in the normalized `10+13`
overflow state.  The upper-cardinality equation is recorded because it is the
actual first saturated split, although it is not needed for this conclusion. -/
theorem k8_hiddenLowerGapSourceAdjacencyEmbedding_bijective
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hlowerCard : lower.card = 10)
    (_hupperCard : upper.card = 13)
    (hoverflow : 9 ≤ Fintype.card (HiddenGapSource lower upper .right)) :
    Function.Bijective (hiddenLowerGapSourceAdjacencyEmbedding lower upper) := by
  apply hiddenLowerGapSourceAdjacencyEmbedding_bijective_of_card_eq
  rw [k8_hiddenLowerGapSource_card_eq_nine hlower hlowerCard hoverflow,
    sweepAdjacency_card hlower, hlowerCard]

/-- Cardinal equality in a form convenient for transporting geometric facts
from hidden sources to every lower adjacency. -/
theorem k8_hiddenLowerGapSource_card_eq_sweepAdjacency
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hlowerCard : lower.card = 10)
    (hoverflow : 9 ≤ Fintype.card (HiddenGapSource lower upper .right)) :
    Fintype.card (HiddenGapSource lower upper .right) =
      Fintype.card (SweepAdjacency lower) := by
  rw [k8_hiddenLowerGapSource_card_eq_nine hlower hlowerCard hoverflow,
    sweepAdjacency_card hlower, hlowerCard]

/-- In particular, every one of the nine lower adjacencies has a unique hidden
source in the normalized overflow state. -/
theorem k8_every_lower_adjacency_has_unique_hidden_source
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hlowerCard : lower.card = 10)
    (hupperCard : upper.card = 13)
    (hoverflow : 9 ≤ Fintype.card (HiddenGapSource lower upper .right))
    (gap : SweepAdjacency lower) :
    ∃! source : HiddenGapSource lower upper .right,
      hiddenLowerGapSourceAdjacencyEmbedding lower upper source = gap := by
  exact (k8_hiddenLowerGapSourceAdjacencyEmbedding_bijective
    hlower hlowerCard hupperCard hoverflow).existsUnique gap

/-- The canonical upper pivot assigned to a lower adjacency once equality has
made every lower adjacency a hidden source. -/
noncomputable def hiddenLowerGapAdjacencyPivot
    {n : ℕ} (lower upper : Finset (Fin n))
    (hcard : Fintype.card (HiddenGapSource lower upper .right) =
      Fintype.card (SweepAdjacency lower))
    (gap : SweepAdjacency lower) : Fin n :=
  HiddenGapSource.enteringPivot
    ((hiddenLowerGapSourceAdjacencyEquiv lower upper hcard).symm gap)

/-- Equality in the hidden-gap count upgrades the pivot injection to an
embedding of every lower adjacency into actual upper-child vertices. -/
noncomputable def hiddenLowerGapAdjacencyPivotEmbedding
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hdisjoint : Disjoint lower upper)
    (hcard : Fintype.card (HiddenGapSource lower upper .right) =
      Fintype.card (SweepAdjacency lower)) :
    SweepAdjacency lower ↪ RetainedVertexOwner upper where
  toFun gap := ⟨hiddenLowerGapAdjacencyPivot lower upper hcard gap, by
    exact HiddenGapSource.enteringPivot_mem_oppositeChild
      ((hiddenLowerGapSourceAdjacencyEquiv lower upper hcard).symm gap)
      hdisjoint⟩
  inj' := by
    intro first second hpivot
    apply (hiddenLowerGapSourceAdjacencyEquiv lower upper hcard).symm.injective
    apply HiddenGapSource.enteringPivot_injective
    exact congrArg Subtype.val hpivot

/-- Each pivot supplied by the extremal equality lies strictly between the
endpoints of the lower adjacency it represents. -/
theorem hiddenLowerGapAdjacencyPivot_between
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hcard : Fintype.card (HiddenGapSource lower upper .right) =
      Fintype.card (SweepAdjacency lower))
    (gap : SweepAdjacency lower) :
    gap.1.left < hiddenLowerGapAdjacencyPivot lower upper hcard gap ∧
      hiddenLowerGapAdjacencyPivot lower upper hcard gap < gap.1.right := by
  let source := (hiddenLowerGapSourceAdjacencyEquiv lower upper hcard).symm gap
  have hsourceGap : source.1 = gap.1 := by
    exact congrArg Subtype.val
      ((hiddenLowerGapSourceAdjacencyEquiv lower upper hcard).apply_symm_apply gap)
  simpa [hiddenLowerGapAdjacencyPivot, source, hsourceGap] using
    source.enteringPivot_between

/-- The exact `10+13` overflow therefore yields a nine-element family of
pairwise distinct upper pivots, with one pivot inside every lower adjacency. -/
theorem k8_hiddenLowerGapPivotSkeleton
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hlowerCard : lower.card = 10)
    (hupperCard : upper.card = 13) (hdisjoint : Disjoint lower upper)
    (hoverflow : 9 ≤ Fintype.card (HiddenGapSource lower upper .right)) :
    ∃ pivot : SweepAdjacency lower ↪ RetainedVertexOwner upper,
      Fintype.card (SweepAdjacency lower) = 9 ∧
        ∀ gap : SweepAdjacency lower,
          gap.1.left < (pivot gap).1 ∧ (pivot gap).1 < gap.1.right := by
  have hbij := k8_hiddenLowerGapSourceAdjacencyEmbedding_bijective
    hlower hlowerCard hupperCard hoverflow
  have hcard : Fintype.card (HiddenGapSource lower upper .right) =
      Fintype.card (SweepAdjacency lower) :=
    Fintype.card_congr (Equiv.ofBijective
      (hiddenLowerGapSourceAdjacencyEmbedding lower upper) hbij)
  refine ⟨hiddenLowerGapAdjacencyPivotEmbedding hdisjoint hcard, ?_, ?_⟩
  · rw [sweepAdjacency_card hlower, hlowerCard]
  · intro gap
    exact hiddenLowerGapAdjacencyPivot_between hcard gap

/-- Every canonical pivot for a hidden lower gap lies in the upper child and
strictly to the right of the minimum lower vertex. -/
theorem hiddenLowerGapEnteringPivotSeed_subset_upper_right_of_min
    {n : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlower : lower.Nonempty) :
    hiddenGapEnteringPivotSeed lower upper .right ⊆
      upper.filter (lower.min' hlower < ·) := by
  intro pivot hpivot
  obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp hpivot
  have hpivotUpper := source.enteringPivot_mem_oppositeChild hdeep.disjoint
  have hleftLower : source.1.left ∈ lower :=
    (mem_hiddenGapSources_iff.mp source.2).1.2.1
  have hminLeft : lower.min' hlower ≤ source.1.left :=
    Finset.min'_le lower source.1.left hleftLower
  exact Finset.mem_filter.mpr
    ⟨hpivotUpper, hminLeft.trans_lt source.enteringPivot_between.1⟩

/-- A lower extreme acts as a common cone point for the whole hidden-lower
pivot seed.  If the parent has no four-cap, the upper vertices to the right of
that anchor—and therefore the pivot seed—form a cup. -/
theorem hiddenLowerGapEnteringPivotSeed_isCupSet_of_no_cap_four
    {n : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlower : lower.Nonempty)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) 4) :
    IsCupSet chi (hiddenGapEnteringPivotSeed lower upper .right) := by
  let q := lower.min' hlower
  have hqLower : q ∈ lower := Finset.min'_mem lower hlower
  have hnoEndpoint :
      ¬∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = 3 ∧
        IsCapSet chi cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q := by
    rintro ⟨cap, hcapSub, hcapCard, hcap, hendpoint⟩
    apply hnoCap
    simpa using hdeep.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcap hqLower hendpoint
  have hrightCup : IsCupSet chi (upper.filter (q < ·)) :=
    (gap_sides_are_cups_of_no_endpoint_cap_three hnoEndpoint).2
  apply FinsetPolygon.IsCupSet.mono hrightCup
  exact hiddenLowerGapEnteringPivotSeed_subset_upper_right_of_min
    hdeep hlower

/-- Consequently, no parent four-cap and no parent `u`-cup give a direct
strict bound on all hidden lower sources.  This bypasses the coarse
source-child adjacency estimate. -/
theorem hiddenLowerGapSource_card_lt_of_no_cap_four_no_cup
    {n u : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlower : lower.Nonempty)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) u) :
    Fintype.card (HiddenGapSource lower upper .right) < u := by
  rw [← hiddenGapEnteringPivotSeed_card lower upper .right]
  have hcup := hiddenLowerGapEnteringPivotSeed_isCupSet_of_no_cap_four
    hdeep hlower hnoCap
  have hsub : hiddenGapEnteringPivotSeed lower upper .right ⊆
      lower ∪ upper := by
    exact (hiddenLowerGapEnteringPivotSeed_subset_upper_right_of_min
      hdeep hlower).trans
        ((Finset.filter_subset _ _).trans Finset.subset_union_right)
  by_contra hnot
  have hu : u ≤ (hiddenGapEnteringPivotSeed lower upper .right).card :=
    Nat.le_of_not_gt hnot
  obtain ⟨cup, hcupSub, hcupCard⟩ := Finset.exists_subset_card_eq hu
  apply hnoCup
  exact ⟨cup, hcupSub.trans hsub, hcupCard,
    FinsetPolygon.IsCupSet.mono hcup hcupSub⟩

/-- Color-dually, a nonempty upper child, no parent four-cup, and no parent
`a`-cap bound all hidden upper sources strictly by `a`. -/
theorem hiddenUpperGapSource_card_lt_of_no_cup_four_no_cap
    {n a : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hupper : upper.Nonempty)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) 4)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) a) :
    Fintype.card (HiddenGapSource lower upper .left) < a := by
  have hnoCapDual :
      ¬ContainsCapSet chi.dual (upper ∪ lower) 4 := by
    intro hcap
    apply hnoCup
    have horiginal := containsCapSet_dual_iff.mp hcap
    simpa [Finset.union_comm] using horiginal
  have hnoCupDual :
      ¬ContainsCupSet chi.dual (upper ∪ lower) a := by
    intro hcup
    apply hnoCap
    have horiginal := containsCupSet_dual_iff.mp hcup
    simpa [Finset.union_comm] using horiginal
  have hbound := hiddenLowerGapSource_card_lt_of_no_cap_four_no_cup
    hdeep.dual hupper hnoCapDual hnoCupDual
  simpa [hiddenGapSources, IsHiddenLowerGap, IsHiddenUpperGap] using hbound

/-- In the ordinary cup--cap regime, a published cap index three has exactly
`u` retained vertices. -/
theorem decomposableThreshold_three_left_add_one_eq
    {u k : ℕ} (hu : 2 ≤ u) (huk : u ≤ k) :
    decomposableThreshold 3 u k + 1 = u := by
  rw [decomposableThreshold_eq_choose (by omega) hu (by omega)]
  simp [Nat.choose_one_right]
  omega

/-- The color-dual published cup index three has exactly `a` retained
vertices. -/
theorem decomposableThreshold_three_right_add_one_eq
    {a k : ℕ} (ha : 2 ≤ a) (hak : a ≤ k) :
    decomposableThreshold a 3 k + 1 = a := by
  rw [decomposableThreshold_eq_choose ha (by omega) (by omega)]
  have hsub : a + 3 - 4 = a - 1 := by omega
  rw [hsub]
  have hchoose : Nat.choose (a - 1) (a - 2) = a - 1 := by
    have hdecomp : a - 1 = (a - 2) + 1 := by omega
    rw [hdecomp, Nat.choose_symm_add, Nat.choose_one_right]
  rw [hchoose]
  omega

/-- The cone bound exactly pays any selected upper core whose published cap
index is three, uniformly in `u ≤ k`. -/
theorem hiddenLowerGapSource_card_le_cap_index_three_capacity
    {n u k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlower : lower.Nonempty) (hu : 2 ≤ u) (huk : u ≤ k)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) u) :
    Fintype.card (HiddenGapSource lower upper .right) ≤
      decomposableThreshold 3 u k + 1 := by
  rw [decomposableThreshold_three_left_add_one_eq hu huk]
  exact Nat.le_of_lt (hiddenLowerGapSource_card_lt_of_no_cap_four_no_cup
    hdeep hlower hnoCap hnoCup)

/-- Color-dually, the same cone mechanism exactly pays a selected lower core
whose published cup index is three. -/
theorem hiddenUpperGapSource_card_le_cup_index_three_capacity
    {n a k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hupper : upper.Nonempty) (ha : 2 ≤ a) (hak : a ≤ k)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) a)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) 4) :
    Fintype.card (HiddenGapSource lower upper .left) ≤
      decomposableThreshold a 3 k + 1 := by
  rw [decomposableThreshold_three_right_add_one_eq ha hak]
  exact Nat.le_of_lt (hiddenUpperGapSource_card_lt_of_no_cup_four_no_cap
    hdeep hupper hnoCup hnoCap)

/-- At the first scalar leak this gives seven pivots at most, already below
the selected upper core's eight-vertex capacity. -/
theorem hiddenLowerGapSource_card_le_488_upper_core_capacity
    {n : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlower : lower.Nonempty)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) 8) :
    Fintype.card (HiddenGapSource lower upper .right) ≤
      decomposableThreshold 3 8 8 + 1 := by
  exact hiddenLowerGapSource_card_le_cap_index_three_capacity
    hdeep hlower (by omega) (by omega) hnoCap hnoCup

/-- Thirteen upper vertices have published cap index three at the normalized
`(4,8,8)` boundary. -/
theorem publishedCapChildIndex_eq_three_at_488_thirteen :
    publishedCapChildIndex 4 8 8 13 = 3 := by
  rw [publishedCapChildIndex, Nat.findGreatest_eq_iff]
  refine ⟨by omega, ?_, ?_⟩
  · intro _
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]
  · intro index hthree hfour
    have hindex : index = 4 := by omega
    subst index
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]

/-- The geometry-sensitive bound closes the actual selected-core obligation:
all hidden-lower canonical pivots fit simultaneously in one published
eight-vertex upper core. -/
theorem exists_publishedUpperPivotSlice_open_488_thirteen
    {n : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlower : lower.Nonempty) (hupper : upper.Nonempty)
    (hupperCard : upper.card = 13)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) 8) :
    ∃ slice : PublishedCapChildSlice 4 8 8 upper,
      ∀ source : HiddenGapSource lower upper .right,
        source.enteringPivot ∈ slice.core := by
  apply exists_publishedUpperPivotSlice_of_card_le
    (a := 4) (u := 8) (k := 8) (by omega) hupper hdeep.disjoint
  rw [hupperCard, publishedCapChildIndex_eq_three_at_488_thirteen]
  exact hiddenLowerGapSource_card_le_488_upper_core_capacity
    hdeep hlower hnoCap hnoCup

end ErdosSzekeres

end
