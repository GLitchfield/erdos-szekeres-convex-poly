module

public import ErdosSzekeres.StructuralChargingRootExcessContract

@[expose] public section

/-!
# The central-cut obstruction at the `(4,8,8)` boundary

In an open `10+13` critical split, every lower vertex cuts the thirteen upper
vertices into cup blocks of sizes six and seven.  The cut count can therefore
increase across at most one lower adjacency.  Hence at most one lower
adjacency is hidden and at least eight are visible.

This points opposite to the proposed hidden-pivot payment, which would require
at least three hidden lower gaps, or equivalently at most six visible lower
adjacencies.  The final theorem records that incompatibility in Lean.
-/

namespace ErdosSzekeres

/-- A hidden lower gap strictly increases the number of upper vertices lying
to the left of its endpoints. -/
theorem HiddenGapSource.lower_cut_card_lt
    {n : ℕ} {lower upper : Finset (Fin n)}
    (source : HiddenGapSource lower upper .right) :
    (upper.filter (· < source.1.left)).card <
      (upper.filter (· < source.1.right)).card := by
  have hsource := mem_hiddenGapSources_iff.mp source.2
  obtain ⟨q, hqUpper, hleftq, hqright⟩ := hsource.2
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro x hx
    have hxData := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr
      ⟨hxData.1, hxData.2.trans hsource.1.1⟩
  · intro heq
    have hqRight : q ∈ upper.filter (· < source.1.right) :=
      Finset.mem_filter.mpr ⟨hqUpper, hqright⟩
    have hqLeft : q ∈ upper.filter (· < source.1.left) := by
      rw [heq]
      exact hqRight
    exact (not_lt_of_ge hleftq.le) (Finset.mem_filter.mp hqLeft).2

/-- Thirteen vertices partitioned around an external cut into two cups in an
ambient set with no eight-cup have side sizes six and seven. -/
theorem gap_cup_blocks_six_seven
    {n : ℕ} {χ : TripleColoring n}
    {upper ambient : Finset (Fin n)} {q : Fin n}
    (hq : q ∉ upper) (hupperCard : upper.card = 13)
    (hupperAmbient : upper ⊆ ambient)
    (hnoCup : ¬ContainsCupSet χ ambient 8)
    (hcups : IsCupSet χ (upper.filter (· < q)) ∧
      IsCupSet χ (upper.filter (q < ·))) :
    ((upper.filter (· < q)).card = 6 ∧
        (upper.filter (q < ·)).card = 7) ∨
      ((upper.filter (· < q)).card = 7 ∧
        (upper.filter (q < ·)).card = 6) := by
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
      have hxq : x ≠ q := by
        rintro rfl
        exact hq hx
      rcases lt_or_gt_of_ne hxq with hxlt | hxgt
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hx, hxlt⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hx, hxgt⟩)
  have hdisjoint : Disjoint left right := by
    rw [Finset.disjoint_left]
    intro x hxLeft hxRight
    have hxlt := (Finset.mem_filter.mp hxLeft).2
    have hxgt := (Finset.mem_filter.mp hxRight).2
    omega
  have hleftSub : left ⊆ ambient :=
    (Finset.filter_subset _ _).trans hupperAmbient
  have hrightSub : right ⊆ ambient :=
    (Finset.filter_subset _ _).trans hupperAmbient
  have hleftCard : left.card < 8 :=
    card_lt_of_isCupSet_of_no_ambient_cup hleftSub hcups.1 hnoCup
  have hrightCard : right.card < 8 :=
    card_lt_of_isCupSet_of_no_ambient_cup hrightSub hcups.2 hnoCup
  have hsum : left.card + right.card = 13 := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion, hupperCard]
  change (left.card = 6 ∧ right.card = 7) ∨
    (left.card = 7 ∧ right.card = 6)
  omega

/-- At an open `(4,8)` root with thirteen upper vertices, every lower vertex
is a six-seven cut of the upper child. -/
theorem upper_cut_six_or_seven_at_open_488
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hupperCard : upper.card = 13)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 8)
    {q : Fin n} (hqLower : q ∈ lower) :
    ((upper.filter (· < q)).card = 6 ∧
        (upper.filter (q < ·)).card = 7) ∨
      ((upper.filter (· < q)).card = 7 ∧
        (upper.filter (q < ·)).card = 6) := by
  have hqUpper : q ∉ upper := by
    intro hq
    exact (Finset.disjoint_left.mp hdeep.disjoint) hqLower hq
  have hnoEndpoint :
      ¬∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = 3 ∧
        IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q := by
    rintro ⟨cap, hcapSub, hcapCard, hcapSet, hendpoint⟩
    apply hnoCap
    simpa using hdeep.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcapSet hqLower hendpoint
  exact gap_cup_blocks_six_seven hqUpper hupperCard
    Finset.subset_union_right hnoCup
    (gap_sides_are_cups_of_no_endpoint_cap_three hnoEndpoint)

/-- Every hidden lower gap crosses the unique possible increase from a six-cut
to a seven-cut. -/
theorem HiddenGapSource.lower_cut_cards_eq_six_seven_at_open_488
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hupperCard : upper.card = 13)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 8)
    (source : HiddenGapSource lower upper .right) :
    (upper.filter (· < source.1.left)).card = 6 ∧
      (upper.filter (· < source.1.right)).card = 7 := by
  have hsource := mem_hiddenGapSources_iff.mp source.2
  have hleftCut := upper_cut_six_or_seven_at_open_488 hdeep hupperCard
    hnoCap hnoCup hsource.1.2.1
  have hrightCut := upper_cut_six_or_seven_at_open_488 hdeep hupperCard
    hnoCap hnoCup hsource.1.2.2.1
  have hlt := source.lower_cut_card_lt
  rcases hleftCut with hleftCut | hleftCut <;>
    rcases hrightCut with hrightCut | hrightCut <;> omega

/-- Two lower adjacencies carrying a six-to-seven upper cut must be the same
adjacency. -/
theorem hiddenLowerGapSource_eq_of_cut_cards_six_seven
    {n : ℕ} {lower upper : Finset (Fin n)}
    (first second : HiddenGapSource lower upper .right)
    (hfirst : (upper.filter (· < first.1.left)).card = 6 ∧
      (upper.filter (· < first.1.right)).card = 7)
    (hsecond : (upper.filter (· < second.1.left)).card = 6 ∧
      (upper.filter (· < second.1.right)).card = 7) : first = second := by
  apply Subtype.ext
  have hfirstAdj := (mem_hiddenGapSources_iff.mp first.2).1
  have hsecondAdj := (mem_hiddenGapSources_iff.mp second.2).1
  apply hfirstAdj.eq_of_right_eq hsecondAdj
  rcases lt_trichotomy first.1.right second.1.right with hlt | heq | hgt
  · have hrightLeLeft : first.1.right ≤ second.1.left := by
      by_contra hnot
      have hleftRight : second.1.left < first.1.right :=
        lt_of_not_ge hnot
      exact hsecondAdj.2.2.2 first.1.right hfirstAdj.2.2.1
        ⟨hleftRight, hlt⟩
    have hsub : upper.filter (· < first.1.right) ⊆
        upper.filter (· < second.1.left) := by
      intro x hx
      have hxData := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨hxData.1, hxData.2.trans_le hrightLeLeft⟩
    have hcard := Finset.card_le_card hsub
    omega
  · exact heq
  · have hrightLeLeft : second.1.right ≤ first.1.left := by
      by_contra hnot
      have hleftRight : first.1.left < second.1.right :=
        lt_of_not_ge hnot
      exact hfirstAdj.2.2.2 second.1.right hsecondAdj.2.2.1
        ⟨hleftRight, hgt⟩
    have hsub : upper.filter (· < second.1.right) ⊆
        upper.filter (· < first.1.left) := by
      intro x hx
      have hxData := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨hxData.1, hxData.2.trans_le hrightLeLeft⟩
    have hcard := Finset.card_le_card hsub
    omega

/-- The open thirteen-point upper child can hide at most one lower
adjacency. -/
theorem hiddenLowerGapSource_card_le_one_at_open_488
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hupperCard : upper.card = 13)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 8) :
    Fintype.card (HiddenGapSource lower upper .right) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro first second
  exact hiddenLowerGapSource_eq_of_cut_cards_six_seven first second
    (first.lower_cut_cards_eq_six_seven_at_open_488
      hdeep hupperCard hnoCap hnoCup)
    (second.lower_cut_cards_eq_six_seven_at_open_488
      hdeep hupperCard hnoCap hnoCup)

/-- With ten lower vertices, at least eight lower adjacencies remain visible.
-/
theorem visibleLowerAdjacency_card_ge_eight_at_open_488
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hlowerCard : lower.card = 10) (hupperCard : upper.card = 13)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 8) :
    8 ≤ Fintype.card (VisibleLowerAdjacency lower upper) := by
  have hpartition := visibleLowerAdjacency_card_add_hidden_add_one
    (lower := lower) (upper := upper)
      (Finset.card_pos.mp (by omega))
  have hhidden := hiddenLowerGapSource_card_le_one_at_open_488
    hdeep hupperCard hnoCap hnoCup
  omega

/-- The index-four lower slice has a three-vertex residual, while the open root
has at most one hidden lower gap.  Thus the proposed hidden-pivot payment is
strictly impossible at the first boundary. -/
theorem lowerSlice_residual_gt_hidden_at_open_488
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (slice : PublishedChildSlice 4 8 8 lower)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hlowerCard : lower.card = 10) (hupperCard : upper.card = 13)
    (hindex : slice.index = 4)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 8) :
    Fintype.card (HiddenGapSource lower upper .right) <
      (lower \ slice.core).card := by
  have hhidden := hiddenLowerGapSource_card_le_one_at_open_488
    hdeep hupperCard hnoCap hnoCup
  have hsplit := slice.remainder_card_add_core_threshold_eq_child
  rw [hindex] at hsplit
  norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
    Finset.sum_Icc_succ_top] at hsplit
  omega

/-- Consequently the payment inequality and the visible-at-most-six gate are
both false under the open boundary hypotheses. -/
theorem lowerSlice_payment_fails_at_open_488
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (slice : PublishedChildSlice 4 8 8 lower)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hlowerCard : lower.card = 10) (hupperCard : upper.card = 13)
    (hindex : slice.index = 4)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 8) :
    ¬(lower \ slice.core).card ≤
        Fintype.card (HiddenGapSource lower upper .right) ∧
      ¬Fintype.card (VisibleLowerAdjacency lower upper) ≤ 6 := by
  constructor
  · exact Nat.not_le_of_lt (lowerSlice_residual_gt_hidden_at_open_488
      slice hdeep hlowerCard hupperCard hindex hnoCap hnoCup)
  · have hvisible := visibleLowerAdjacency_card_ge_eight_at_open_488
      hdeep hlowerCard hupperCard hnoCap hnoCup
    omega

end ErdosSzekeres

end
