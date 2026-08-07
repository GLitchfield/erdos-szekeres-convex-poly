module

public import ErdosSzekeres.PublishedInductionSemantics

@[expose] public section

/-!
# Canonical saturated branch of the published induction

At an active parent, the published arithmetic proves that exactly one child
parameter reaches its outer value.  This file packages that disjunction as a
unique branch and gives the branch access to its actual retained child core.

This is selection and ownership infrastructure only.  It does not assert that
the selected core pays a parent obligation, is conserved between nodes, or is
unused by another charge.
-/

namespace ErdosSzekeres

/-- The color-dual maximal child index never exceeds its search bound. -/
theorem publishedCapChildIndex_le (a u k childCard : ℕ) :
    publishedCapChildIndex a u k childCard ≤ a :=
  Nat.findGreatest_le a

/-- A nonempty cap-side child has positive color-dual maximal index. -/
theorem publishedCapChildIndex_pos {a u k childCard : ℕ}
    (ha : 1 ≤ a) (hcard : 0 < childCard) :
    0 < publishedCapChildIndex a u k childCard := by
  unfold publishedCapChildIndex
  rw [Nat.findGreatest_pos]
  exact ⟨1, by omega, ha, by simpa using hcard⟩

/-- If the cap-side child fits below the outer threshold, its maximal index is
strictly below the outer cap parameter. -/
theorem publishedCapChildIndex_lt {a u k childCard : ℕ}
    (ha : 1 ≤ a) (hcard : 0 < childCard)
    (hupper : childCard ≤ decomposableThreshold a u k) :
    publishedCapChildIndex a u k childCard < a := by
  have hle : publishedCapChildIndex a u k childCard ≤ a :=
    publishedCapChildIndex_le a u k childCard
  have hlt := publishedCapChildIndex_threshold_lt
    (a := a) (u := u) (k := k) ha hcard
  by_contra hnot
  have heq : publishedCapChildIndex a u k childCard = a :=
    Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  rw [heq] at hlt
  omega

/-- Maximality bounds the cap-side child by the threshold at its next index. -/
theorem childCard_le_threshold_succ_publishedCapChildIndex
    {a u k childCard : ℕ} (ha : 1 ≤ a) (hcard : 0 < childCard)
    (hupper : childCard ≤ decomposableThreshold a u k) :
    childCard ≤ decomposableThreshold
      (publishedCapChildIndex a u k childCard + 1) u k := by
  let index := publishedCapChildIndex a u k childCard
  have hindexLt : index < a := publishedCapChildIndex_lt ha hcard hupper
  have hnot : ¬decomposableThreshold (index + 1) u k < childCard := by
    apply Nat.findGreatest_is_greatest
      (P := fun v ↦ decomposableThreshold v u k < childCard) (n := a)
    · simp [index, publishedCapChildIndex]
    · omega
  exact Nat.le_of_not_gt hnot

namespace PublishedCapChildSlice

variable {α : Type*} {a u k : ℕ} {child : Finset α}

/-- The actual color-dual slice of a nonempty child has positive index. -/
theorem index_pos (slice : PublishedCapChildSlice a u k child)
    (ha : 1 ≤ a) (hchild : child.Nonempty) : 0 < slice.index := by
  rw [slice.index_eq]
  exact publishedCapChildIndex_pos ha hchild.card_pos

/-- The actual color-dual slice index is below the outer cap parameter. -/
theorem index_lt (slice : PublishedCapChildSlice a u k child)
    (ha : 1 ≤ a) (hchild : child.Nonempty)
    (hupper : child.card ≤ decomposableThreshold a u k) :
    slice.index < a := by
  rw [slice.index_eq]
  exact publishedCapChildIndex_lt ha hchild.card_pos hupper

/-- The actual cap-side child fits below the threshold at its next index. -/
theorem child_card_le_next_threshold
    (slice : PublishedCapChildSlice a u k child)
    (ha : 1 ≤ a) (hchild : child.Nonempty)
    (hupper : child.card ≤ decomposableThreshold a u k) :
    child.card ≤ decomposableThreshold (slice.index + 1) u k := by
  rw [slice.index_eq]
  exact childCard_le_threshold_succ_publishedCapChildIndex
    ha hchild.card_pos hupper

end PublishedCapChildSlice

/-- Which actual child has the saturated auxiliary parameter.  The lower child
varies the cup parameter; the upper child varies the cap parameter. -/
inductive PublishedSaturatedBranch where
  | lower
  | upper
  deriving DecidableEq, Repr

namespace PublishedSaturatedBranch

/-- The arithmetic condition certifying a selected saturated branch. -/
def Valid (a u k a' u' : ℕ) : PublishedSaturatedBranch → Prop
  | .lower => u' + 1 = u ∧ a' < k - u + 1
  | .upper => a' + 1 = a ∧ u' < k - a + 1

/-- The actual child selected by a saturated branch. -/
def child {α : Type*} (lower upper : Finset α) :
    PublishedSaturatedBranch → Finset α
  | .lower => lower
  | .upper => upper

/-- The actual retained published core owned by a saturated branch. -/
def retainedCore {α : Type*} {a u k : ℕ}
    {lower upper : Finset α}
    (lowerSlice : PublishedChildSlice a u k lower)
    (upperSlice : PublishedCapChildSlice a u k upper) :
    PublishedSaturatedBranch → Finset α
  | .lower => lowerSlice.core
  | .upper => upperSlice.core

/-- The branch-owned retained core lies in the branch-selected child. -/
theorem retainedCore_subset_child {α : Type*} {a u k : ℕ}
    {lower upper : Finset α}
    (lowerSlice : PublishedChildSlice a u k lower)
    (upperSlice : PublishedCapChildSlice a u k upper)
    (branch : PublishedSaturatedBranch) :
    retainedCore lowerSlice upperSlice branch ⊆ child lower upper branch := by
  cases branch with
  | lower => exact lowerSlice.core_subset
  | upper => exact upperSlice.core_subset

/-- Distinct branches at one split own disjoint retained cores.  This is local
nonoverlap; it does not prevent an ancestor core from overlapping a descendant
core at a different tree address. -/
theorem retainedCore_disjoint_of_ne
    {α : Type*} [DecidableEq α] {a u k : ℕ}
    {lower upper : Finset α}
    (hdisjoint : Disjoint lower upper)
    (lowerSlice : PublishedChildSlice a u k lower)
    (upperSlice : PublishedCapChildSlice a u k upper)
    {first second : PublishedSaturatedBranch} (hne : first ≠ second) :
    Disjoint (retainedCore lowerSlice upperSlice first)
      (retainedCore lowerSlice upperSlice second) := by
  cases first with
  | lower =>
      cases second with
      | lower => exact (hne rfl).elim
      | upper =>
          exact hdisjoint.mono lowerSlice.core_subset upperSlice.core_subset
  | upper =>
      cases second with
      | lower =>
          exact hdisjoint.symm.mono upperSlice.core_subset lowerSlice.core_subset
      | upper => exact (hne rfl).elim

/-- The branch-owned core keeps the exact cardinality advertised by its
published slice. -/
theorem retainedCore_card {α : Type*} {a u k : ℕ}
    {lower upper : Finset α}
    (lowerSlice : PublishedChildSlice a u k lower)
    (upperSlice : PublishedCapChildSlice a u k upper)
    (branch : PublishedSaturatedBranch) :
    (retainedCore lowerSlice upperSlice branch).card =
      match branch with
      | .lower => decomposableThreshold a lowerSlice.index k + 1
      | .upper => decomposableThreshold upperSlice.index u k + 1 := by
  cases branch with
  | lower => exact lowerSlice.core_card
  | upper => exact upperSlice.core_card

end PublishedSaturatedBranch

/-- Feasible active published-induction arithmetic selects exactly one
saturated child branch. -/
theorem published_feasible_auxiliary_saturation_existsUnique
    {a u k a' u' lowerCard upperCard : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (ha' : 1 ≤ a') (hu' : 1 ≤ u')
    (ha'Lt : a' < a) (hu'Lt : u' < u)
    (hsum : a' + u' ≤ k - 1) (hactive : k + 4 ≤ a + u)
    (htotal : lowerCard + upperCard = decomposableThreshold a u k + 1)
    (hlower : lowerCard ≤ decomposableThreshold a (u' + 1) k)
    (hupper : upperCard ≤ decomposableThreshold (a' + 1) u k) :
    ∃! branch : PublishedSaturatedBranch,
      branch.Valid a u k a' u' := by
  have hexists := published_feasible_auxiliary_saturation
    ha hu hak huk ha' hu' ha'Lt hu'Lt hsum hactive htotal hlower hupper
  rcases hexists with hupperBranch | hlowerBranch
  · refine ⟨.upper, hupperBranch, ?_⟩
    intro other hother
    cases other with
    | upper => rfl
    | lower =>
        exfalso
        exact published_saturated_auxiliary_alternatives_exclusive hactive
          ⟨hupperBranch, hother⟩
  · refine ⟨.lower, hlowerBranch, ?_⟩
    intro other hother
    cases other with
    | lower => rfl
    | upper =>
        exfalso
        exact published_saturated_auxiliary_alternatives_exclusive hactive
          ⟨hother, hlowerBranch⟩

/-- The unique branch theorem specialized to the maximal indices and actual
retained cores of a pair of published child slices. -/
theorem published_slice_pair_saturation_existsUnique
    {α : Type*} {a u k : ℕ} {lower upper : Finset α}
    (lowerSlice : PublishedChildSlice a u k lower)
    (upperSlice : PublishedCapChildSlice a u k upper)
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hlowerNonempty : lower.Nonempty) (hupperNonempty : upper.Nonempty)
    (hsum : upperSlice.index + lowerSlice.index ≤ k - 1)
    (hactive : k + 4 ≤ a + u)
    (htotal : lower.card + upper.card = decomposableThreshold a u k + 1)
    (hlowerOuter : lower.card ≤ decomposableThreshold a u k)
    (hupperOuter : upper.card ≤ decomposableThreshold a u k) :
    ∃! branch : PublishedSaturatedBranch,
      branch.Valid a u k upperSlice.index lowerSlice.index := by
  exact published_feasible_auxiliary_saturation_existsUnique
    ha hu hak huk
    (upperSlice.index_pos (by omega) hupperNonempty)
    (lowerSlice.index_pos (by omega) hlowerNonempty)
    (upperSlice.index_lt (by omega) hupperNonempty hupperOuter)
    (lowerSlice.index_lt (by omega) hlowerNonempty hlowerOuter)
    hsum hactive htotal
    (lowerSlice.child_card_le_next_threshold
      (by omega) hlowerNonempty hlowerOuter)
    (upperSlice.child_card_le_next_threshold
      (by omega) hupperNonempty hupperOuter)

end ErdosSzekeres

end
