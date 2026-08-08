module

public import ErdosSzekeres.StructuralChargingVisibleAdjacency

@[expose] public section

/-!
# Exact residual budgets for published child slices

The complement of a published retained core is an actual finite set of child
vertices.  This file records its exact cardinal contribution both locally and
inside a critical parent split.  It also converts payment of that complement
by hidden-gap pivots into the equivalent visible-adjacency inequality.

The final visible-adjacency inequality is deliberately left as a geometric
obligation.  The results here identify its exact required bound without
claiming that the bound already holds.
-/

namespace ErdosSzekeres

namespace PublishedChildSlice

variable {α : Type*} {a u k : ℕ} {child : Finset α}

/-- A lower published slice is exactly its threshold-sized core plus its
actual residual vertices. -/
theorem remainder_card_add_core_threshold_eq_child
    [DecidableEq α] (slice : PublishedChildSlice a u k child) :
    (child \ slice.core).card +
        (decomposableThreshold a slice.index k + 1) = child.card := by
  rw [← slice.core_card]
  exact slice.remainder_card_add_core_card

end PublishedChildSlice

namespace PublishedCapChildSlice

variable {α : Type*} {a u k : ℕ} {child : Finset α}

/-- The color-dual published slice has the same exact residual
decomposition. -/
theorem remainder_card_add_core_card [DecidableEq α]
    (slice : PublishedCapChildSlice a u k child) :
    (child \ slice.core).card + slice.core.card = child.card :=
  Finset.card_sdiff_add_card_eq_card slice.core_subset

/-- Rewriting the core cardinality exposes the exact cap-side threshold. -/
theorem remainder_card_add_core_threshold_eq_child
    [DecidableEq α] (slice : PublishedCapChildSlice a u k child) :
    (child \ slice.core).card +
        (decomposableThreshold slice.index u k + 1) = child.card := by
  rw [← slice.core_card]
  exact slice.remainder_card_add_core_card

end PublishedCapChildSlice

/-- If the upper branch is retained inside a critical parent, the lower child
and the discarded upper residual occupy exactly the outer threshold minus the
retained upper threshold. -/
theorem lower_card_add_upperSlice_remainder_eq_threshold_sub
    {n a u k : ℕ} {lower upper : Finset (Fin n)}
    (slice : PublishedCapChildSlice a u k upper)
    (htotal : lower.card + upper.card =
      decomposableThreshold a u k + 1) :
    lower.card + (upper \ slice.core).card =
      decomposableThreshold a u k -
        decomposableThreshold slice.index u k := by
  have hsplit := slice.remainder_card_add_core_threshold_eq_child
  omega

/-- Color-dually, retaining the lower branch leaves the discarded lower
residual together with the upper child in the complementary outer budget. -/
theorem lowerSlice_remainder_add_upper_card_eq_threshold_sub
    {n a u k : ℕ} {lower upper : Finset (Fin n)}
    (slice : PublishedChildSlice a u k lower)
    (htotal : lower.card + upper.card =
      decomposableThreshold a u k + 1) :
    (lower \ slice.core).card + upper.card =
      decomposableThreshold a u k -
        decomposableThreshold a slice.index k := by
  have hsplit := slice.remainder_card_add_core_threshold_eq_child
  omega

/-- For a lower published slice, hidden lower gaps pay every discarded vertex
exactly when the visible lower adjacencies fit in the core's threshold budget.
-/
theorem lowerSlice_remainder_le_hidden_iff_visible_le_threshold
    {n a u k : ℕ} {lower upper : Finset (Fin n)}
    (slice : PublishedChildSlice a u k lower)
    (hlower : lower.Nonempty) :
    (lower \ slice.core).card ≤
        Fintype.card (HiddenGapSource lower upper .right) ↔
      Fintype.card (VisibleLowerAdjacency lower upper) ≤
        decomposableThreshold a slice.index k := by
  rw [lower_remainder_le_hidden_iff_visible_add_one_le_core
    hlower slice.core_subset, slice.core_card]
  omega

/-- Color-dual visible-threshold form of upper residual payment. -/
theorem upperSlice_remainder_le_hidden_iff_visible_le_threshold
    {n a u k : ℕ} {lower upper : Finset (Fin n)}
    (slice : PublishedCapChildSlice a u k upper)
    (hupper : upper.Nonempty) :
    (upper \ slice.core).card ≤
        Fintype.card (HiddenGapSource lower upper .left) ↔
      Fintype.card (VisibleUpperAdjacency lower upper) ≤
        decomposableThreshold slice.index u k := by
  rw [upper_remainder_le_hidden_iff_visible_add_one_le_core
    hupper slice.core_subset, slice.core_card]
  omega

/-- At the first unresolved `(4,8,8)` scalar gate, a lower slice of index four
can be paid precisely when there are at most six visible lower adjacencies.
This is the exact geometric target, not a proof that the target always holds.
-/
theorem lowerSlice_remainder_payment_iff_visible_le_six_at_488
    {n : ℕ} {lower upper : Finset (Fin n)}
    (slice : PublishedChildSlice 4 8 8 lower)
    (hlower : lower.Nonempty) (hindex : slice.index = 4) :
    (lower \ slice.core).card ≤
        Fintype.card (HiddenGapSource lower upper .right) ↔
      Fintype.card (VisibleLowerAdjacency lower upper) ≤ 6 := by
  rw [lowerSlice_remainder_le_hidden_iff_visible_le_threshold slice hlower,
    hindex]
  norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
    Finset.sum_Icc_succ_top]

end ErdosSzekeres

end
