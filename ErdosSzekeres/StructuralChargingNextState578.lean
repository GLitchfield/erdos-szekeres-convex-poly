module

public import ErdosSzekeres.StructuralChargingResidualWindow488

@[expose] public section

/-!
# The next fixed-`k = 8` predecessor state

The `(5,7,8)` threshold is forty-one.  At an exact forty-two-vertex critical
root, every middle child-size pair has published auxiliary indices summing to
eight.  Strict predecessor states force that sum to be at most seven, leaving
only the two oriented tails: a lower child of size at most ten, or the extreme
`41+1` split.  This file records that exact reduction while the structural
singleton-tail lemma remains under review.
-/

namespace ErdosSzekeres

/-- In the middle of the exact `(5,7,8)` critical window, the two published
child indices sum to eight. -/
theorem published_indices_add_eq_eight_at_578_middle
    {lowerCard upperCard : ℕ}
    (htotal : lowerCard + upperCard = decomposableThreshold 5 7 8 + 1)
    (hlower : 11 ≤ lowerCard) (hlowerBound : lowerCard ≤ 40) :
    publishedChildIndex 5 7 8 lowerCard +
        publishedCapChildIndex 5 7 8 upperCard = 8 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
    Finset.sum_Icc_succ_top] at htotal
  have hupper : upperCard = 42 - lowerCard := by omega
  interval_cases lowerCard <;>
    norm_num at hupper <;> subst upperCard <;>
    norm_num [publishedChildIndex, publishedCapChildIndex,
      decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]

/-- Assuming all strict fixed-`k = 8` predecessors, an open exact `(5,7,8)`
root cannot have lower-child cardinality between eleven and forty. -/
theorem criticalRoot_578_lower_card_in_tails_of_predecessors
    (hpredecessors : ∀ a u, a + u < 12 → DecomposableStateUpper a u 8)
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hlower : IsDecomposableOn χ lower)
    (hupper : IsDecomposableOn χ upper)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hlowerBound : lower.card ≤ decomposableThreshold 5 7 8)
    (hupperBound : upper.card ≤ decomposableThreshold 5 7 8)
    (hcard : (lower ∪ upper).card = decomposableThreshold 5 7 8 + 1)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 8) :
    lower.card ≤ 10 ∨ 41 ≤ lower.card := by
  have hthreshold : decomposableThreshold 5 7 8 = 41 := by
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]
  have htotal : lower.card + upper.card = 42 := by
    rw [← Finset.card_union_of_disjoint hdeep.disjoint]
    simpa [hthreshold] using hcard
  have hlowerPos : 0 < lower.card := by
    rw [hthreshold] at hupperBound
    omega
  have hupperPos : 0 < upper.card := by
    rw [hthreshold] at hlowerBound
    omega
  have hlowerNonempty : lower.Nonempty := Finset.card_pos.mp hlowerPos
  have hupperNonempty : upper.Nonempty := Finset.card_pos.mp hupperPos
  by_contra htails
  push Not at htails
  obtain ⟨lowerSlice⟩ := exists_publishedChildSlice
    (a := 5) (u := 7) (k := 8) (child := lower) (by omega) hlowerNonempty
  obtain ⟨upperSlice, _⟩ := exists_publishedCapChildSlice_core_superset
    (a := 5) (u := 7) (k := 8) (child := upper) (seed := ∅)
      (by omega) hupperNonempty (by simp) (by simp)
  have hindexLe := published_slice_indices_add_le_of_predecessors
    lowerSlice upperSlice hlowerNonempty hupperNonempty hlower hupper hdeep
    hlowerBound hupperBound (by
      intro a u hau
      exact hpredecessors a u (by omega)) hnoCap hnoCup hnoStrong
  have hindexEq := published_indices_add_eq_eight_at_578_middle
    htotal (by omega) (by omega)
  rw [lowerSlice.index_eq, upperSlice.index_eq] at hindexLe
  omega

/-- Exact pair form of the predecessor-conditional reduction: the residual
root has either a small lower child and at least thirty-two upper vertices, or
the oriented extreme split `41+1`. -/
theorem criticalRoot_578_tail_pairs_of_predecessors
    (hpredecessors : ∀ a u, a + u < 12 → DecomposableStateUpper a u 8)
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hlower : IsDecomposableOn χ lower)
    (hupper : IsDecomposableOn χ upper)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hlowerBound : lower.card ≤ decomposableThreshold 5 7 8)
    (hupperBound : upper.card ≤ decomposableThreshold 5 7 8)
    (hcard : (lower ∪ upper).card = decomposableThreshold 5 7 8 + 1)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 8) :
    (lower.card ≤ 10 ∧ 32 ≤ upper.card) ∨
      (lower.card = 41 ∧ upper.card = 1) := by
  have hthreshold : decomposableThreshold 5 7 8 = 41 := by
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]
  have htotal : lower.card + upper.card = 42 := by
    rw [← Finset.card_union_of_disjoint hdeep.disjoint]
    simpa [hthreshold] using hcard
  rcases criticalRoot_578_lower_card_in_tails_of_predecessors
      hpredecessors hlower hupper hdeep hlowerBound hupperBound hcard
      hnoCap hnoCup hnoStrong with hsmall | hextreme
  · exact Or.inl ⟨hsmall, by omega⟩
  · rw [hthreshold] at hlowerBound
    exact Or.inr ⟨by omega, by omega⟩

/-- First oriented residual gate for `(5,7,8)`: a singleton lower child and
thirty-two decomposable upper vertices cannot form an open deep root.  Any
small-lower critical tail restricts to this exact support size. -/
def SingletonLowerCriticalGate578 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {q : Fin n}
      {upper : Finset (Fin n)},
    IsDecomposableOn χ upper → HasDeepBelowSplit χ {q} upper →
      upper.card = 32 →
        ¬ContainsCapSet χ ({q} ∪ upper) 5 →
          ¬ContainsCupSet χ ({q} ∪ upper) 7 →
            ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8 → False

/-- Second oriented residual gate for `(5,7,8)`: the exact `41+1` critical
split with a singleton upper child is impossible. -/
def SingletonUpperCriticalGate578 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {q : Fin n}
      {lower : Finset (Fin n)},
    IsDecomposableOn χ lower → HasDeepBelowSplit χ lower {q} →
      lower.card = 41 →
        ¬ContainsCapSet χ (lower ∪ {q}) 5 →
          ¬ContainsCupSet χ (lower ∪ {q}) 7 →
            ¬ContainsStrongPolygonSet χ (lower ∪ {q}) 8 → False

/-- A cup on `u` vertices contains a cup on every smaller prescribed number
of vertices. -/
theorem containsCupSet_of_le
    {n r u : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hru : r ≤ u) (hcup : ContainsCupSet χ s u) :
    ContainsCupSet χ s r := by
  obtain ⟨cup, hcupSub, hcupCard, hcupSet⟩ := hcup
  obtain ⟨small, hsmallSub, hsmallCard⟩ :=
    Finset.exists_subset_card_eq (hcupCard ▸ hru)
  exact ⟨small, hsmallSub.trans hcupSub, hsmallCard,
    FinsetPolygon.IsCupSet.mono hcupSet hsmallSub⟩

/-- Every decomposable 23-vertex restriction of an open singleton-lower
`(5,7,8)` upper reservoir contains a four-cap. This is the first direct use of
the completed `(4,8,8)` state in the next bottom-up state. -/
theorem containsCapFour_of_decomposable_large_subset_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper s : Finset (Fin n)}
    (hs : IsDecomposableOn χ s) (hcard : 23 ≤ s.card)
    (hsub : s ⊆ upper)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8) :
    ContainsCapSet χ s 4 := by
  have hthreshold : decomposableThreshold 4 8 8 = 22 := by
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]
  rcases decomposableStateUpper_488 hs (by omega) with hcap | hcup | hstrong
  · exact hcap
  · exact (hnoCup (FinsetPolygon.ContainsCupSet.mono
      (containsCupSet_of_le (by omega) hcup)
      (hsub.trans Finset.subset_union_right))).elim
  · exact (hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
      (hsub.trans Finset.subset_union_right))).elim

/-- The exact cap-reservoir invariant at an open singleton-lower root. Every
23-vertex upper restriction contains a four-cap by `(4,8,8)`, while every
upper four-cap crosses the same sweep cut at the singleton root. -/
theorem dense_straddling_cap_reservoir_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8) :
    (∀ s : Finset (Fin n), s ⊆ upper → s.card = 23 →
      ContainsCapSet χ s 4) ∧
      ∀ (cap : Finset (Fin n)) (hcap : cap ∈ capWitnesses χ upper 4),
        (finsetSweepInterval cap (by
          have hcard := (mem_capWitnesses.mp hcap).2.1
          exact Finset.card_pos.mp (by omega))).StraddlesCut q.val := by
  constructor
  · intro s hsub hcard
    exact containsCapFour_of_decomposable_large_subset_at_578
      (hupper.subset hsub (Finset.card_pos.mp (by omega))) (by omega)
      hsub hnoCup hnoStrong
  · exact hroot.root_straddles_every_upper_cap_of_no_succ_cap
      (a := 4) (by omega) hnoCap

/-- The full 32-vertex singleton-lower reservoir contains three pairwise
disjoint upper four-caps. Absence of a parent five-cap forces every selected
cap to straddle the root's sweep position. This retains 20 unused upper
vertices after the selection, unlike the refuted constant-size cup core. -/
theorem exists_three_disjoint_straddling_four_caps_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hupperCard : upper.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8) :
    ∃ cap1 cap2 cap3 : Finset (Fin n),
      cap1 ∈ capWitnesses χ upper 4 ∧
      cap2 ∈ capWitnesses χ upper 4 ∧
      cap3 ∈ capWitnesses χ upper 4 ∧
      Disjoint cap1 cap2 ∧ Disjoint cap1 cap3 ∧ Disjoint cap2 cap3 ∧
      ¬HasDeepBelowSplit.IsSweepEndpoint cap1 q ∧
      ¬HasDeepBelowSplit.IsSweepEndpoint cap2 q ∧
      ¬HasDeepBelowSplit.IsSweepEndpoint cap3 q := by
  have hfirst := containsCapFour_of_decomposable_large_subset_at_578
    hupper (by omega) Finset.Subset.rfl hnoCup hnoStrong
  obtain ⟨cap1, hcap1Sub, hcap1Card, hcap1Set⟩ := hfirst
  let rest1 := upper \ cap1
  have hrest1Card : rest1.card = 28 := by
    rw [Finset.card_sdiff_of_subset hcap1Sub, hupperCard, hcap1Card]
  have hrest1Nonempty : rest1.Nonempty := Finset.card_pos.mp (by omega)
  have hrest1 : IsDecomposableOn χ rest1 :=
    hupper.subset Finset.sdiff_subset hrest1Nonempty
  have hsecond := containsCapFour_of_decomposable_large_subset_at_578
    hrest1 (by omega) Finset.sdiff_subset hnoCup hnoStrong
  obtain ⟨cap2, hcap2SubRest, hcap2Card, hcap2Set⟩ := hsecond
  have hcap2Sub : cap2 ⊆ upper := hcap2SubRest.trans Finset.sdiff_subset
  let rest2 := rest1 \ cap2
  have hrest2Card : rest2.card = 24 := by
    rw [Finset.card_sdiff_of_subset hcap2SubRest, hrest1Card, hcap2Card]
  have hrest2Nonempty : rest2.Nonempty := Finset.card_pos.mp (by omega)
  have hrest2 : IsDecomposableOn χ rest2 :=
    hrest1.subset Finset.sdiff_subset hrest2Nonempty
  have hthird := containsCapFour_of_decomposable_large_subset_at_578
    hrest2 (by omega) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      hnoCup hnoStrong
  obtain ⟨cap3, hcap3SubRest, hcap3Card, hcap3Set⟩ := hthird
  have hcap3SubRest1 : cap3 ⊆ rest1 :=
    hcap3SubRest.trans Finset.sdiff_subset
  have hcap3Sub : cap3 ⊆ upper :=
    hcap3SubRest1.trans Finset.sdiff_subset
  have hdisjoint12 : Disjoint cap1 cap2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hxRest := hcap2SubRest hx2
    exact (Finset.mem_sdiff.mp hxRest).2 hx1
  have hdisjoint13 : Disjoint cap1 cap3 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx3
    have hxRest := hcap3SubRest1 hx3
    exact (Finset.mem_sdiff.mp hxRest).2 hx1
  have hdisjoint23 : Disjoint cap2 cap3 := by
    rw [Finset.disjoint_left]
    intro x hx2 hx3
    have hxRest := hcap3SubRest hx3
    exact (Finset.mem_sdiff.mp hxRest).2 hx2
  have hnoEndpoint : ∀ cap : Finset (Fin n), cap ⊆ upper → cap.card = 4 →
      IsCapSet χ cap → ¬HasDeepBelowSplit.IsSweepEndpoint cap q := by
    intro cap hcapSub hcapCard hcapSet hendpoint
    apply hnoCap
    simpa using hroot.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcapSet (by simp) hendpoint
  refine ⟨cap1, cap2, cap3,
    mem_capWitnesses.mpr ⟨hcap1Sub, hcap1Card, hcap1Set⟩,
    mem_capWitnesses.mpr ⟨hcap2Sub, hcap2Card, hcap2Set⟩,
    mem_capWitnesses.mpr ⟨hcap3Sub, hcap3Card, hcap3Set⟩,
    hdisjoint12, hdisjoint13, hdisjoint23, ?_, ?_, ?_⟩
  · exact hnoEndpoint cap1 hcap1Sub hcap1Card hcap1Set
  · exact hnoEndpoint cap2 hcap2Sub hcap2Card hcap2Set
  · exact hnoEndpoint cap3 hcap3Sub hcap3Card hcap3Set

/-- A candidate root-centered local replacement for the 33-vertex
singleton-lower gate. It is retained as a precise negative benchmark:
`StructuralChargingNextState578Counterexample` proves that it is false. -/
def RootedCupBlocks55Force578 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {q : Fin n}
      {left right : Finset (Fin n)},
    Disjoint left right →
      (∀ x ∈ left, x < q) → (∀ y ∈ right, q < y) →
        left.card = 5 → right.card = 5 →
          IsCupSet χ left → IsCupSet χ right →
            OneChangeOn χ (left ∪ right) →
              HasDeepBelowSplit χ {q} (left ∪ right) →
                ContainsCapSet χ ({q} ∪ (left ∪ right)) 5 ∨
                  ContainsCupSet χ ({q} ∪ (left ∪ right)) 7 ∨
                    ContainsStrongPolygonSet χ ({q} ∪ (left ∪ right)) 8

/-- A four-cap-free, seven-cup-free one-change set has at most twenty-one
vertices. -/
theorem card_le_twentyOne_of_oneChange_no_capFour_no_cupSeven
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4)
    (hnoCup : ¬ContainsCupSet χ s 7) : s.card ≤ 21 := by
  by_contra hcard
  rcases containsCapFour_or_containsCupSeven_of_oneChange_card_ge_twentyTwo
      hone (by omega) with hcap | hcup
  · exact hnoCap hcap
  · exact hnoCup hcup

/-- The eleven-vertex rooted `5+q+5` gate implies the full singleton-lower
`1+32` gate.  The root cut makes each side four-cap-free; the `(4,7)`
cup--cap bound makes both sides have at least eleven vertices, hence each
contains a five-cup. -/
theorem singletonLowerCriticalGate578_of_rootedCupBlocks55
    (hblocks : RootedCupBlocks55Force578) :
    SingletonLowerCriticalGate578 := by
  intro n χ q upper hupper hroot hupperCard hnoCap hnoCup hnoStrong
  have hqUpper : q ∉ upper := by
    intro hq
    exact (Finset.disjoint_left.mp hroot.disjoint) (by simp) hq
  let left := upper.filter (· < q)
  let right := upper.filter (q < ·)
  have hunion : left ∪ right = upper := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    · intro hx
      have hxq : x ≠ q := by rintro rfl; exact hqUpper hx
      rcases lt_or_gt_of_ne hxq with hxlt | hxgt
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hxgt⟩)
  have hdisjoint : Disjoint left right := by
    rw [Finset.disjoint_left]
    intro x hxLeft hxRight
    have hxlt := (Finset.mem_filter.mp hxLeft).2
    have hxgt := (Finset.mem_filter.mp hxRight).2
    omega
  have hnoEndpoint :
      ¬∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = 4 ∧
        IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q := by
    rintro ⟨cap, hcapSub, hcapCard, hcapSet, hendpoint⟩
    apply hnoCap
    simpa using hroot.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcapSet (by simp) hendpoint
  have hnoSideCap : ¬ContainsCapSet χ left 4 ∧
      ¬ContainsCapSet χ right 4 :=
    gap_sides_avoid_cap_of_no_endpoint_cap hnoEndpoint
  have hupperOne : OneChangeOn χ upper := by
    intro i j k l hij hjk hkl hi hj hk hl
    exact hupper.turnSequenceAllowed hij hjk hkl hi hj hk hl
  have hleftSubParent : left ⊆ {q} ∪ upper :=
    (Finset.filter_subset _ _).trans Finset.subset_union_right
  have hrightSubParent : right ⊆ {q} ∪ upper :=
    (Finset.filter_subset _ _).trans Finset.subset_union_right
  have hnoLeftCup : ¬ContainsCupSet χ left 7 := by
    intro hcup
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hleftSubParent)
  have hnoRightCup : ¬ContainsCupSet χ right 7 := by
    intro hcup
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hrightSubParent)
  have hleftBound : left.card ≤ 21 :=
    card_le_twentyOne_of_oneChange_no_capFour_no_cupSeven
      (hupperOne.mono (Finset.filter_subset _ _)) hnoSideCap.1 hnoLeftCup
  have hrightBound : right.card ≤ 21 :=
    card_le_twentyOne_of_oneChange_no_capFour_no_cupSeven
      (hupperOne.mono (Finset.filter_subset _ _)) hnoSideCap.2 hnoRightCup
  have hsum : left.card + right.card = 32 := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion, hupperCard]
  have hleftLarge : 11 ≤ left.card := by omega
  have hrightLarge : 11 ≤ right.card := by omega
  obtain ⟨leftCup, hleftCupSub, hleftCupCard, hleftCup⟩ :=
    containsCupFive_of_oneChange_no_capFour_card_ge_eleven
      (hupperOne.mono (Finset.filter_subset _ _)) hnoSideCap.1 hleftLarge
  obtain ⟨rightCup, hrightCupSub, hrightCupCard, hrightCup⟩ :=
    containsCupFive_of_oneChange_no_capFour_card_ge_eleven
      (hupperOne.mono (Finset.filter_subset _ _)) hnoSideCap.2 hrightLarge
  have hcupsSub : leftCup ∪ rightCup ⊆ upper := by
    rw [← hunion]
    exact Finset.union_subset_union hleftCupSub hrightCupSub
  have hcupSplit : HasDeepBelowSplit χ {q} (leftCup ∪ rightCup) :=
    hroot.mono Finset.Subset.rfl hcupsSub
  have honeCups : OneChangeOn χ (leftCup ∪ rightCup) :=
    hupperOne.mono hcupsSub
  have hcupDisjoint : Disjoint leftCup rightCup :=
    hdisjoint.mono hleftCupSub hrightCupSub
  have hleftOrder : ∀ x ∈ leftCup, x < q := by
    intro x hx
    exact (Finset.mem_filter.mp (hleftCupSub hx)).2
  have hrightOrder : ∀ y ∈ rightCup, q < y := by
    intro y hy
    exact (Finset.mem_filter.mp (hrightCupSub hy)).2
  have hout := hblocks hcupDisjoint hleftOrder hrightOrder
    hleftCupCard hrightCupCard hleftCup hrightCup honeCups hcupSplit
  have hunionSub : {q} ∪ (leftCup ∪ rightCup) ⊆ {q} ∪ upper :=
    Finset.union_subset_union Finset.Subset.rfl hcupsSub
  rcases hout with hcap | hcup | hstrong
  · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hunionSub)
  · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hunionSub)
  · exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub)

/-- The two oriented singleton gates close every exact `(5,7,8)` critical
root once the strict fixed-`k = 8` predecessor pool is available. -/
theorem criticalRootImpossible_578_of_predecessors_tail_gates
    (hpredecessors : ∀ a u, a + u < 12 → DecomposableStateUpper a u 8)
    (hlowerGate : SingletonLowerCriticalGate578)
    (hupperGate : SingletonUpperCriticalGate578) :
    DecomposableCriticalRootImpossible 5 7 8 := by
  intro n χ lower upper hlower hupper hdeep hlowerBound hupperBound
    hcard hnoCap hnoCup hnoStrong
  rcases criticalRoot_578_tail_pairs_of_predecessors
      hpredecessors hlower hupper hdeep hlowerBound hupperBound hcard
      hnoCap hnoCup hnoStrong with hsmall | hextreme
  · have hlowerNonempty : lower.Nonempty := by
      have hthreshold : decomposableThreshold 5 7 8 = 41 := by
        norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
          Finset.sum_Icc_succ_top]
      have htotal : lower.card + upper.card = 42 := by
        rw [← Finset.card_union_of_disjoint hdeep.disjoint]
        simpa [hthreshold] using hcard
      exact Finset.card_pos.mp (by omega)
    obtain ⟨q, hq⟩ := hlowerNonempty
    obtain ⟨upper', hupperSub, hupperCard⟩ :=
      Finset.exists_subset_card_eq hsmall.2
    have hupperNonempty : upper'.Nonempty :=
      Finset.card_pos.mp (by omega)
    have hupper' : IsDecomposableOn χ upper' :=
      hupper.subset hupperSub hupperNonempty
    have hqSub : {q} ⊆ lower := by simpa using hq
    have hdeep' : HasDeepBelowSplit χ {q} upper' :=
      hdeep.mono hqSub hupperSub
    have hunionSub : {q} ∪ upper' ⊆ lower ∪ upper :=
      Finset.union_subset_union hqSub hupperSub
    exact hlowerGate hupper' hdeep' hupperCard
      (fun hcap ↦ hnoCap
        (FinsetPolygon.ContainsCapSet.mono hcap hunionSub))
      (fun hcup ↦ hnoCup
        (FinsetPolygon.ContainsCupSet.mono hcup hunionSub))
      (fun hstrong ↦ hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub))
  · obtain ⟨q, hupperEq⟩ := Finset.card_eq_one.mp hextreme.2
    subst upper
    exact hupperGate hlower hdeep hextreme.1 hnoCap hnoCup hnoStrong

/-- Root-local tail closure lifts to the hereditary `(5,7,8)` state. -/
theorem decomposableStateUpper_578_of_predecessors_tail_gates
    (hpredecessors : ∀ a u, a + u < 12 → DecomposableStateUpper a u 8)
    (hlowerGate : SingletonLowerCriticalGate578)
    (hupperGate : SingletonUpperCriticalGate578) :
    DecomposableStateUpper 5 7 8 := by
  apply rootTransitionUpper_implies_decomposableStateUpper (by
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top])
  apply criticalRootImpossible_implies_rootTransitionUpper
  exact criticalRootImpossible_578_of_predecessors_tail_gates
    hpredecessors hlowerGate hupperGate

end ErdosSzekeres

end
