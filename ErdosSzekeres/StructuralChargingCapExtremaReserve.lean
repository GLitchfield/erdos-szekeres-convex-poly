module

public import ErdosSzekeres.StructuralChargingCentralCut488

@[expose] public section

/-!
# Two nonpivot extrema in a selected predecessor core

When a selected upper core contains every hidden-lower pivot, its strict
predecessor state supplies a cap inside that same core.  Absence of the
successor parent cap makes the cap straddle every lower vertex.  Its two sweep
extrema therefore lie outside the open interval containing every pivot.  They
form a two-vertex nonpivot reserve inside the selected core.  The color-dual
statement holds for a selected lower core.

At `(4,8,8)` the reserve yields only `hiddenLower + 2 ≤ 8`, hence
`hiddenLower ≤ 6`.  The central-cut theorem proves the sharper bound one, so
this reserve is valid but insufficient for the retired payment direction.
-/

namespace ErdosSzekeres

/-- Extra selected-upper-core vertices disjoint from all hidden-lower pivots.
-/
structure UpperPivotCoreReserve {n a u k : ℕ}
    (lower upper : Finset (Fin n))
    (slice : PublishedCapChildSlice a u k upper) where
  reserve : Finset (Fin n)
  pivots_subset_core :
    hiddenGapEnteringPivotSeed lower upper .right ⊆ slice.core
  reserve_subset_core : reserve ⊆ slice.core
  reserve_disjoint_pivots :
    Disjoint reserve (hiddenGapEnteringPivotSeed lower upper .right)

/-- Extra selected-lower-core vertices disjoint from all hidden-upper pivots.
-/
structure LowerPivotCoreReserve {n a u k : ℕ}
    (lower upper : Finset (Fin n))
    (slice : PublishedChildSlice a u k lower) where
  reserve : Finset (Fin n)
  pivots_subset_core :
    hiddenGapEnteringPivotSeed lower upper .left ⊆ slice.core
  reserve_subset_core : reserve ⊆ slice.core
  reserve_disjoint_pivots :
    Disjoint reserve (hiddenGapEnteringPivotSeed lower upper .left)

/-- Every hidden-lower pivot lies strictly between the lower-child sweep
extrema. -/
theorem hiddenLowerGapEnteringPivotSeed_mem_open_lower_interval
    {n : ℕ} {lower upper : Finset (Fin n)} (hlower : lower.Nonempty)
    {pivot : Fin n}
    (hpivot : pivot ∈ hiddenGapEnteringPivotSeed lower upper .right) :
    lower.min' hlower < pivot ∧ pivot < lower.max' hlower := by
  obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp hpivot
  have hsource := mem_hiddenGapSources_iff.mp source.2
  have hminLeft : lower.min' hlower ≤ source.1.left :=
    Finset.min'_le lower source.1.left hsource.1.2.1
  have hrightMax : source.1.right ≤ lower.max' hlower :=
    Finset.le_max' lower source.1.right hsource.1.2.2.1
  exact ⟨hminLeft.trans_lt source.enteringPivot_between.1,
    source.enteringPivot_between.2.trans_le hrightMax⟩

/-- Every hidden-upper pivot lies strictly between the upper-child sweep
extrema. -/
theorem hiddenUpperGapEnteringPivotSeed_mem_open_upper_interval
    {n : ℕ} {lower upper : Finset (Fin n)} (hupper : upper.Nonempty)
    {pivot : Fin n}
    (hpivot : pivot ∈ hiddenGapEnteringPivotSeed lower upper .left) :
    upper.min' hupper < pivot ∧ pivot < upper.max' hupper := by
  obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp hpivot
  have hsource := mem_hiddenGapSources_iff.mp source.2
  have hminLeft : upper.min' hupper ≤ source.1.left :=
    Finset.min'_le upper source.1.left hsource.1.2.1
  have hrightMax : source.1.right ≤ upper.max' hupper :=
    Finset.le_max' upper source.1.right hsource.1.2.2.1
  exact ⟨hminLeft.trans_lt source.enteringPivot_between.1,
    source.enteringPivot_between.2.trans_le hrightMax⟩

/-- A nonpivot reserve and the pivot seed occupy disjoint selected-upper-core
vertices. -/
theorem UpperPivotCoreReserve.hidden_card_add_reserve_card_le_core
    {n a u k : ℕ} {lower upper : Finset (Fin n)}
    {slice : PublishedCapChildSlice a u k upper}
    (resource : UpperPivotCoreReserve lower upper slice) :
    Fintype.card (HiddenGapSource lower upper .right) +
        resource.reserve.card ≤ slice.core.card := by
  rw [← hiddenGapEnteringPivotSeed_card lower upper .right]
  rw [← Finset.card_union_of_disjoint
    resource.reserve_disjoint_pivots.symm]
  apply Finset.card_le_card
  intro q hq
  rcases Finset.mem_union.mp hq with hqPivot | hqReserve
  · exact resource.pivots_subset_core hqPivot
  · exact resource.reserve_subset_core hqReserve

/-- Color-dual reserve accounting. -/
theorem LowerPivotCoreReserve.hidden_card_add_reserve_card_le_core
    {n a u k : ℕ} {lower upper : Finset (Fin n)}
    {slice : PublishedChildSlice a u k lower}
    (resource : LowerPivotCoreReserve lower upper slice) :
    Fintype.card (HiddenGapSource lower upper .left) +
        resource.reserve.card ≤ slice.core.card := by
  rw [← hiddenGapEnteringPivotSeed_card lower upper .left]
  rw [← Finset.card_union_of_disjoint
    resource.reserve_disjoint_pivots.symm]
  apply Finset.card_le_card
  intro q hq
  rcases Finset.mem_union.mp hq with hqPivot | hqReserve
  · exact resource.pivots_subset_core hqPivot
  · exact resource.reserve_subset_core hqReserve

/-- A predecessor cap inside the selected upper pivot core supplies two
nonpivot extrema. -/
theorem exists_upperPivotCoreReserve_card_two
    {n outerA u k : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (slice : PublishedCapChildSlice outerA u k upper)
    (hlower : lower.Nonempty)
    (hupper : IsDecomposableOn χ upper)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hstate : DecomposableStateUpper slice.index u k)
    (hpivots : ∀ source : HiddenGapSource lower upper .right,
      source.enteringPivot ∈ slice.core)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) (slice.index + 1))
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) u)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) k) :
    ∃ resource : UpperPivotCoreReserve lower upper slice,
      resource.reserve.card = 2 := by
  classical
  have hcoreNonempty : slice.core.Nonempty := by
    apply Finset.card_pos.mp
    rw [slice.core_card]
    omega
  have hcoreDecomposable : IsDecomposableOn χ slice.core :=
    hupper.subset slice.core_subset hcoreNonempty
  have hcoreLarge :
      decomposableThreshold slice.index u k < slice.core.card := by
    rw [slice.core_card]
    omega
  have hcap : ContainsCapSet χ slice.core slice.index := by
    rcases hstate hcoreDecomposable hcoreLarge with hcap | hcup | hstrong
    · exact hcap
    · exact False.elim (hnoCup (FinsetPolygon.ContainsCupSet.mono hcup
        (slice.core_subset.trans Finset.subset_union_right)))
    · exact False.elim (hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
          (slice.core_subset.trans Finset.subset_union_right)))
  obtain ⟨cap, hcapCore, hcapCard, hcapSet⟩ := hcap
  have hcapUpper : cap ⊆ upper := hcapCore.trans slice.core_subset
  obtain ⟨⟨x, hxCap, hxLeft⟩, _⟩ :=
    hdeep.cap_straddles_lower_of_not_containsCapSet_succ
      hcapUpper hcapCard hcapSet (lower.min'_mem hlower) hnoCap
  obtain ⟨_, ⟨y, hyCap, hyRight⟩⟩ :=
    hdeep.cap_straddles_lower_of_not_containsCapSet_succ
      hcapUpper hcapCard hcapSet (lower.max'_mem hlower) hnoCap
  have hseedCore : hiddenGapEnteringPivotSeed lower upper .right ⊆
      slice.core := by
    intro pivot hpivot
    obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp hpivot
    exact hpivots source
  have hxNotSeed : x ∉ hiddenGapEnteringPivotSeed lower upper .right := by
    intro hxSeed
    have hxBounds :=
      hiddenLowerGapEnteringPivotSeed_mem_open_lower_interval hlower hxSeed
    omega
  have hyNotSeed : y ∉ hiddenGapEnteringPivotSeed lower upper .right := by
    intro hySeed
    have hyBounds :=
      hiddenLowerGapEnteringPivotSeed_mem_open_lower_interval hlower hySeed
    omega
  have hxy : x ≠ y := by
    have hminMax : lower.min' hlower ≤ lower.max' hlower :=
      Finset.min'_le lower (lower.max' hlower) (lower.max'_mem hlower)
    omega
  let reserve : Finset (Fin n) := {x, y}
  have hreserveCore : reserve ⊆ slice.core := by
    intro q hq
    simp only [reserve, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hcapCore hxCap
    · exact hcapCore hyCap
  have hreserveDisjoint : Disjoint reserve
      (hiddenGapEnteringPivotSeed lower upper .right) := by
    rw [Finset.disjoint_left]
    intro q hqReserve hqSeed
    simp only [reserve, Finset.mem_insert, Finset.mem_singleton] at hqReserve
    rcases hqReserve with rfl | rfl
    · exact hxNotSeed hqSeed
    · exact hyNotSeed hqSeed
  let resource : UpperPivotCoreReserve lower upper slice :=
    { reserve := reserve
      pivots_subset_core := hseedCore
      reserve_subset_core := hreserveCore
      reserve_disjoint_pivots := hreserveDisjoint }
  refine ⟨resource, ?_⟩
  simp [resource, reserve, hxy]

/-- Color-dually, a predecessor cup inside the selected lower pivot core has
two nonpivot extrema. -/
theorem exists_lowerPivotCoreReserve_card_two
    {n a outerU k : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (slice : PublishedChildSlice a outerU k lower)
    (hupper : upper.Nonempty)
    (hlower : IsDecomposableOn χ lower)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hstate : DecomposableStateUpper a slice.index k)
    (hpivots : ∀ source : HiddenGapSource lower upper .left,
      source.enteringPivot ∈ slice.core)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) a)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) (slice.index + 1))
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) k) :
    ∃ resource : LowerPivotCoreReserve lower upper slice,
      resource.reserve.card = 2 := by
  classical
  have hcoreNonempty : slice.core.Nonempty := by
    apply Finset.card_pos.mp
    rw [slice.core_card]
    omega
  have hcoreDecomposable : IsDecomposableOn χ slice.core :=
    hlower.subset slice.core_subset hcoreNonempty
  have hcoreLarge :
      decomposableThreshold a slice.index k < slice.core.card := by
    rw [slice.core_card]
    omega
  have hcup : ContainsCupSet χ slice.core slice.index := by
    rcases hstate hcoreDecomposable hcoreLarge with hcap | hcup | hstrong
    · exact False.elim (hnoCap (FinsetPolygon.ContainsCapSet.mono hcap
        (slice.core_subset.trans Finset.subset_union_left)))
    · exact hcup
    · exact False.elim (hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
          (slice.core_subset.trans Finset.subset_union_left)))
  obtain ⟨cup, hcupCore, hcupCard, hcupSet⟩ := hcup
  have hcupLower : cup ⊆ lower := hcupCore.trans slice.core_subset
  obtain ⟨⟨x, hxCup, hxLeft⟩, _⟩ :=
    hdeep.cup_straddles_upper_of_not_containsCupSet_succ
      hcupLower hcupCard hcupSet (upper.min'_mem hupper) hnoCup
  obtain ⟨_, ⟨y, hyCup, hyRight⟩⟩ :=
    hdeep.cup_straddles_upper_of_not_containsCupSet_succ
      hcupLower hcupCard hcupSet (upper.max'_mem hupper) hnoCup
  have hseedCore : hiddenGapEnteringPivotSeed lower upper .left ⊆
      slice.core := by
    intro pivot hpivot
    obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp hpivot
    exact hpivots source
  have hxNotSeed : x ∉ hiddenGapEnteringPivotSeed lower upper .left := by
    intro hxSeed
    have hxBounds :=
      hiddenUpperGapEnteringPivotSeed_mem_open_upper_interval hupper hxSeed
    omega
  have hyNotSeed : y ∉ hiddenGapEnteringPivotSeed lower upper .left := by
    intro hySeed
    have hyBounds :=
      hiddenUpperGapEnteringPivotSeed_mem_open_upper_interval hupper hySeed
    omega
  have hxy : x ≠ y := by
    have hminMax : upper.min' hupper ≤ upper.max' hupper :=
      Finset.min'_le upper (upper.max' hupper) (upper.max'_mem hupper)
    omega
  let reserve : Finset (Fin n) := {x, y}
  have hreserveCore : reserve ⊆ slice.core := by
    intro q hq
    simp only [reserve, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hcupCore hxCup
    · exact hcupCore hyCup
  have hreserveDisjoint : Disjoint reserve
      (hiddenGapEnteringPivotSeed lower upper .left) := by
    rw [Finset.disjoint_left]
    intro q hqReserve hqSeed
    simp only [reserve, Finset.mem_insert, Finset.mem_singleton] at hqReserve
    rcases hqReserve with rfl | rfl
    · exact hxNotSeed hqSeed
    · exact hyNotSeed hqSeed
  let resource : LowerPivotCoreReserve lower upper slice :=
    { reserve := reserve
      pivots_subset_core := hseedCore
      reserve_subset_core := hreserveCore
      reserve_disjoint_pivots := hreserveDisjoint }
  refine ⟨resource, ?_⟩
  simp [resource, reserve, hxy]

/-- An eight-vertex selected upper core and the two-extrema reserve give only
the upper bound six on hidden lower gaps. -/
theorem hiddenLowerGapSource_card_le_six_of_two_reserve_at_488
    {n : ℕ} {lower upper : Finset (Fin n)}
    {slice : PublishedCapChildSlice 4 8 8 upper}
    (hindex : slice.index = 3)
    (resource : UpperPivotCoreReserve lower upper slice)
    (hreserveCard : resource.reserve.card = 2) :
    Fintype.card (HiddenGapSource lower upper .right) ≤ 6 := by
  have hbound :
      Fintype.card (HiddenGapSource lower upper .right) +
          resource.reserve.card ≤ slice.core.card :=
    resource.hidden_card_add_reserve_card_le_core
  have hcoreCard : slice.core.card = 8 := by
    rw [slice.core_card, hindex]
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]
  omega

end ErdosSzekeres

end
