module

public import ErdosSzekeres.StructuralChargingTransport

@[expose] public section

/-!
# Semantic child slices in the published decomposable-set induction

The proof of Baek--Balko's decomposable-set bound chooses an auxiliary child
parameter maximally from the child's cardinality, then retains an actual subset
of cardinality `decomposableThreshold a index k + 1`.  This file formalizes
that choice independently of the later Pascal-window absorption.

In particular, an auxiliary cup parameter equal to one does not represent an
abstract unit: its retained child subset is literally a singleton.
-/

namespace ErdosSzekeres

/-- The largest child parameter at most `u` whose threshold is strictly below
the actual child cardinality. -/
def publishedChildIndex (a u k childCard : ℕ) : ℕ :=
  Nat.findGreatest (fun v ↦ decomposableThreshold a v k < childCard) u

theorem publishedChildIndex_le (a u k childCard : ℕ) :
    publishedChildIndex a u k childCard ≤ u := by
  exact Nat.findGreatest_le u

theorem publishedChildIndex_threshold_lt {a u k childCard : ℕ}
    (hu : 1 ≤ u) (hcard : 0 < childCard) :
    decomposableThreshold a (publishedChildIndex a u k childCard) k <
      childCard := by
  unfold publishedChildIndex
  exact Nat.findGreatest_spec (P := fun v ↦
    decomposableThreshold a v k < childCard) hu (by simpa using hcard)

theorem publishedChildIndex_pos {a u k childCard : ℕ}
    (hu : 1 ≤ u) (hcard : 0 < childCard) :
    0 < publishedChildIndex a u k childCard := by
  unfold publishedChildIndex
  rw [Nat.findGreatest_pos]
  exact ⟨1, by omega, hu, by simpa using hcard⟩

/-- If the whole child does not exceed the outer parameter's threshold, the
maximal retained parameter is strictly smaller than the outer parameter. -/
theorem publishedChildIndex_lt {a u k childCard : ℕ}
    (hu : 1 ≤ u) (hcard : 0 < childCard)
    (hupper : childCard ≤ decomposableThreshold a u k) :
    publishedChildIndex a u k childCard < u := by
  have hle : publishedChildIndex a u k childCard ≤ u :=
    publishedChildIndex_le a u k childCard
  have hlt := publishedChildIndex_threshold_lt (a := a) (u := u) (k := k)
    hu hcard
  by_contra hnot
  have heq : publishedChildIndex a u k childCard = u :=
    Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  rw [heq] at hlt
  omega

/-- Maximality bounds the whole child by the threshold at the next parameter. -/
theorem childCard_le_threshold_succ_publishedChildIndex
    {a u k childCard : ℕ} (hu : 1 ≤ u) (hcard : 0 < childCard)
    (hupper : childCard ≤ decomposableThreshold a u k) :
    childCard ≤ decomposableThreshold a
      (publishedChildIndex a u k childCard + 1) k := by
  let index := publishedChildIndex a u k childCard
  have hindexLt : index < u := publishedChildIndex_lt hu hcard hupper
  have hnot : ¬decomposableThreshold a (index + 1) k < childCard := by
    apply Nat.findGreatest_is_greatest
      (P := fun v ↦ decomposableThreshold a v k < childCard) (n := u)
    · simp [index, publishedChildIndex]
    · omega
  have hle : childCard ≤ decomposableThreshold a (index + 1) k :=
    Nat.le_of_not_gt hnot
  simpa [index] using hle

/-- The actual retained child subset used by the published induction.  Its
members are vertices, not formal Pascal units. -/
structure PublishedChildSlice {α : Type*} (a u k : ℕ)
    (child : Finset α) where
  index : ℕ
  index_eq : index = publishedChildIndex a u k child.card
  core : Finset α
  core_subset : core ⊆ child
  core_card : core.card = decomposableThreshold a index k + 1

theorem exists_publishedChildSlice {α : Type*} [DecidableEq α]
    {a u k : ℕ} {child : Finset α} (hu : 1 ≤ u) (hchild : child.Nonempty) :
    Nonempty (PublishedChildSlice a u k child) := by
  let index := publishedChildIndex a u k child.card
  have hneeded : decomposableThreshold a index k + 1 ≤ child.card := by
    have := publishedChildIndex_threshold_lt (a := a) (u := u) (k := k)
      hu hchild.card_pos
    change decomposableThreshold a index k < child.card at this
    omega
  obtain ⟨core, hcoreSubset, hcoreCard⟩ :=
    Finset.exists_subset_card_eq hneeded
  exact ⟨⟨index, rfl, core, hcoreSubset, hcoreCard⟩⟩

/-- The retained core may be chosen to contain any prescribed seed that fits
inside its advertised cardinality. This gives a structural witness stable
identity inside the actual published child contribution instead of introducing
an abstract charging token. -/
theorem exists_publishedChildSlice_core_superset
    {α : Type*} [DecidableEq α] {a u k : ℕ} {child seed : Finset α}
    (hu : 1 ≤ u) (hchild : child.Nonempty) (hseedSub : seed ⊆ child)
    (hseedCard : seed.card ≤
      decomposableThreshold a (publishedChildIndex a u k child.card) k + 1) :
    ∃ slice : PublishedChildSlice a u k child, seed ⊆ slice.core := by
  let index := publishedChildIndex a u k child.card
  have hneeded : decomposableThreshold a index k + 1 ≤ child.card := by
    have hlt := publishedChildIndex_threshold_lt (a := a) (u := u) (k := k)
      hu hchild.card_pos
    change decomposableThreshold a index k < child.card at hlt
    omega
  have hseedCard' : seed.card ≤ decomposableThreshold a index k + 1 := by
    simpa [index] using hseedCard
  obtain ⟨core, hseedCore, hcoreChild, hcoreCard⟩ :=
    Finset.exists_subsuperset_card_eq hseedSub hseedCard' hneeded
  exact ⟨⟨index, rfl, core, hcoreChild, hcoreCard⟩, hseedCore⟩

/-- Color-dual maximal child parameter, varying the cap parameter while the
cup parameter remains fixed. -/
def publishedCapChildIndex (a u k childCard : ℕ) : ℕ :=
  Nat.findGreatest (fun v ↦ decomposableThreshold v u k < childCard) a

theorem publishedCapChildIndex_threshold_lt {a u k childCard : ℕ}
    (ha : 1 ≤ a) (hcard : 0 < childCard) :
    decomposableThreshold (publishedCapChildIndex a u k childCard) u k <
      childCard := by
  unfold publishedCapChildIndex
  exact Nat.findGreatest_spec (P := fun v ↦
    decomposableThreshold v u k < childCard) ha (by simpa using hcard)

/-- The actual retained subset for the color-dual child, where the maximal
published index varies the cap parameter. -/
structure PublishedCapChildSlice {α : Type*} (a u k : ℕ)
    (child : Finset α) where
  index : ℕ
  index_eq : index = publishedCapChildIndex a u k child.card
  core : Finset α
  core_subset : core ⊆ child
  core_card : core.card = decomposableThreshold index u k + 1

/-- A color-dual retained core may likewise be chosen to contain a prescribed
seed witness that fits inside the core cardinality. -/
theorem exists_publishedCapChildSlice_core_superset
    {α : Type*} [DecidableEq α] {a u k : ℕ} {child seed : Finset α}
    (ha : 1 ≤ a) (hchild : child.Nonempty) (hseedSub : seed ⊆ child)
    (hseedCard : seed.card ≤
      decomposableThreshold (publishedCapChildIndex a u k child.card) u k + 1) :
    ∃ slice : PublishedCapChildSlice a u k child, seed ⊆ slice.core := by
  let index := publishedCapChildIndex a u k child.card
  have hneeded : decomposableThreshold index u k + 1 ≤ child.card := by
    have hlt := publishedCapChildIndex_threshold_lt (a := a) (u := u) (k := k)
      ha hchild.card_pos
    change decomposableThreshold index u k < child.card at hlt
    omega
  have hseedCard' : seed.card ≤ decomposableThreshold index u k + 1 := by
    simpa [index] using hseedCard
  obtain ⟨core, hseedCore, hcoreChild, hcoreCard⟩ :=
    Finset.exists_subsuperset_card_eq hseedSub hseedCard' hneeded
  exact ⟨⟨index, rfl, core, hcoreChild, hcoreCard⟩, hseedCore⟩

namespace PublishedChildSlice

variable {α : Type*} {a u k : ℕ} {child : Finset α}

theorem index_pos (slice : PublishedChildSlice a u k child)
    (hu : 1 ≤ u) (hchild : child.Nonempty) : 0 < slice.index := by
  rw [slice.index_eq]
  exact publishedChildIndex_pos hu hchild.card_pos

theorem index_lt (slice : PublishedChildSlice a u k child)
    (hu : 1 ≤ u) (hchild : child.Nonempty)
    (hupper : child.card ≤ decomposableThreshold a u k) :
    slice.index < u := by
  rw [slice.index_eq]
  exact publishedChildIndex_lt hu hchild.card_pos hupper

theorem child_card_le_next_threshold (slice : PublishedChildSlice a u k child)
    (hu : 1 ≤ u) (hchild : child.Nonempty)
    (hupper : child.card ≤ decomposableThreshold a u k) :
    child.card ≤ decomposableThreshold a (slice.index + 1) k := by
  rw [slice.index_eq]
  exact childCard_le_threshold_succ_publishedChildIndex hu hchild.card_pos hupper

/-- The child is the disjoint cardinal sum of the retained core and the actual
leftover vertices. -/
theorem remainder_card_add_core_card [DecidableEq α]
    (slice : PublishedChildSlice a u k child) :
    (child \ slice.core).card + slice.core.card = child.card :=
  Finset.card_sdiff_add_card_eq_card slice.core_subset

/-- The exact semantic inequality behind the adjacent child summand. -/
theorem remainder_card_add_core_threshold_le
    [DecidableEq α] (slice : PublishedChildSlice a u k child)
    (hu : 1 ≤ u) (hchild : child.Nonempty)
    (hupper : child.card ≤ decomposableThreshold a u k) :
    (child \ slice.core).card +
        (decomposableThreshold a slice.index k + 1) ≤
      decomposableThreshold a (slice.index + 1) k := by
  have hsplit := slice.remainder_card_add_core_card
  have hnext := slice.child_card_le_next_threshold hu hchild hupper
  rw [slice.core_card] at hsplit
  omega

/-- At the problematic auxiliary value `u' = 1`, the retained lower child is
literally one vertex. -/
theorem core_eq_singleton_of_index_eq_one
    (slice : PublishedChildSlice a u k child) (hindex : slice.index = 1) :
    ∃ q ∈ child, slice.core = {q} := by
  have hcard : slice.core.card = 1 := by
    rw [slice.core_card, hindex]
    simp
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  exact ⟨q, slice.core_subset (by simp [hq]), hq⟩

/-- In the `(4,5,5)` boundary state, auxiliary index one forces the entire
nonempty child—not merely its retained core—to be a singleton. -/
theorem child_eq_singleton_of_index_eq_one
    (slice : PublishedChildSlice a u k child) (ha : 2 ≤ a) (hak : a ≤ k)
    (hu : 1 ≤ u) (hchild : child.Nonempty)
    (hupper : child.card ≤ decomposableThreshold a u k)
    (hindex : slice.index = 1) : ∃ q, child = {q} := by
  have hcardLe : child.card ≤ decomposableThreshold a (slice.index + 1) k :=
    slice.child_card_le_next_threshold hu hchild hupper
  rw [hindex] at hcardLe
  have hthresholdTwo : decomposableThreshold a 2 k = 1 := by
    rw [decomposableThreshold, if_neg (by omega), if_pos (by omega)]
    have hsub : a + 2 - 4 = a - 2 := by omega
    rw [hsub, Nat.choose_self]
  rw [hthresholdTwo] at hcardLe
  have hcard : child.card = 1 := by
    have hpos := hchild.card_pos
    omega
  exact Finset.card_eq_one.mp hcard

/-- The first concrete regression is an instance of the uniform index-one
singleton rule. -/
theorem child_eq_singleton_of_455_index_eq_one
    (slice : PublishedChildSlice 4 5 5 child) (hchild : child.Nonempty)
    (hupper : child.card ≤ decomposableThreshold 4 5 5)
    (hindex : slice.index = 1) : ∃ q, child = {q} := by
  exact slice.child_eq_singleton_of_index_eq_one (by omega) (by omega)
    (by omega) hchild hupper hindex

end PublishedChildSlice

/-- The published `u' = 1` branch of the `(4,5,5)` transition is exactly the
already-proved singleton-root boundary, not an unowned Pascal unit. -/
theorem published_455_index_one_boundary_card_le_seven
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hupperDecomp : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper)
    (slice : PublishedChildSlice 4 5 5 lower) (hindex : slice.index = 1)
    (hlowerBound : lower.card ≤ decomposableThreshold 4 5 5)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 5) :
    (lower ∪ upper).card ≤ 7 := by
  obtain ⟨q, hq⟩ :=
    slice.child_eq_singleton_of_455_index_eq_one hlower hlowerBound hindex
  subst lower
  exact hsplit.singleton_root_card_le_seven hupperDecomp hnoCap hnoCup hnoStrong

/-- Complementary child cardinalities at an outer-threshold counterexample
force the sum of the two adjacent child thresholds to exceed the outer
threshold.  This is the semantic bridge from actual child slices to the
arithmetic saturation question; no independent-child estimate is hidden in
the statement. -/
theorem published_next_threshold_pair_gt_of_complementary_cards
    {a u k a' u' lowerCard upperCard : ℕ}
    (htotal : lowerCard + upperCard = decomposableThreshold a u k + 1)
    (hlower : lowerCard ≤ decomposableThreshold a (u' + 1) k)
    (hupper : upperCard ≤ decomposableThreshold (a' + 1) u k) :
    decomposableThreshold a u k <
      decomposableThreshold a (u' + 1) k +
        decomposableThreshold (a' + 1) u k := by
  omega

/-- In the strictly classical child regime, the next child threshold fits in
the first coefficient of the outer Pascal window.  This is the first of the
three one-sided allocation cases needed by the all-parameter saturation
lemma; the equality boundary consumes two coefficients and the active case
consumes an interval. -/
theorem published_left_child_deep_base_le_first_outer_coefficient
    {a u' k : ℕ} (ha : 2 ≤ a) (hu' : 1 ≤ u') (hak : a ≤ k)
    (hdeep : a + (u' + 1) ≤ k + 2) :
    decomposableThreshold a (u' + 1) k ≤ Nat.choose (k - 2) (k - a) := by
  rw [decomposableThreshold_eq_choose ha (by omega) (by omega)]
  have hrow : a + (u' + 1) - 4 ≤ k - 2 := by omega
  have hmono := Nat.choose_le_choose (a - 2) hrow
  have hindex : k - a = (k - 2) - (a - 2) := by omega
  have hsymm : Nat.choose (k - 2) (k - a) =
      Nat.choose (k - 2) (a - 2) := by
    rw [hindex, Nat.choose_symm (by omega)]
  rw [hsymm]
  exact hmono

/-- At the last classical row before the active-window regime, the next child
threshold is exactly the first two coefficients of the outer row. -/
theorem published_left_child_base_boundary_eq_first_two_outer_coefficients
    {a u' k : ℕ} (ha : 3 ≤ a) (hak : a ≤ k)
    (hboundary : a + (u' + 1) = k + 3) :
    decomposableThreshold a (u' + 1) k =
      Nat.choose (k - 2) (k - a) +
        Nat.choose (k - 2) (k - a + 1) := by
  rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
  have hrow : a + (u' + 1) - 4 = (k - 2) + 1 := by omega
  have hcolumn : a - 2 = (a - 3) + 1 := by omega
  rw [hrow, hcolumn, Nat.choose_succ_succ]
  have hfirstIndex : k - a = (k - 2) - (a - 2) := by omega
  have hsecondIndex : k - a + 1 = (k - 2) - (a - 3) := by omega
  have hfirst : Nat.choose (k - 2) (k - a) =
      Nat.choose (k - 2) (a - 2) := by
    rw [hfirstIndex, Nat.choose_symm (by omega)]
  have hsecond : Nat.choose (k - 2) (k - a + 1) =
      Nat.choose (k - 2) (a - 3) := by
    rw [hsecondIndex, Nat.choose_symm (by omega)]
  rw [hfirst, hsecond]
  have hsucc : (a - 3).succ = a - 2 := by omega
  rw [hsucc]
  omega

/-- Uniform one-sided allocation: the next lower-child threshold is bounded by
a prefix of the outer Pascal window.  In the deep base case the prefix is one
coefficient, at the base/active boundary it is two coefficients, and in the
active case it is the literal child window. -/
theorem published_left_child_le_outer_prefix
    {a u' k : ℕ} (ha : 3 ≤ a) (hu' : 1 ≤ u') (hak : a ≤ k) :
    decomposableThreshold a (u' + 1) k ≤
      ∑ j ∈ Finset.Icc (k - a) (max (k - a) (u' - 1)),
        Nat.choose (k - 2) j := by
  by_cases hdeep : a + (u' + 1) ≤ k + 2
  · calc
      decomposableThreshold a (u' + 1) k ≤
          Nat.choose (k - 2) (k - a) :=
        published_left_child_deep_base_le_first_outer_coefficient
          (by omega) hu' hak hdeep
      _ = ∑ j ∈ ({k - a} : Finset ℕ), Nat.choose (k - 2) j := by simp
      _ ≤ ∑ j ∈ Finset.Icc (k - a) (max (k - a) (u' - 1)),
          Nat.choose (k - 2) j := by
        apply Finset.sum_le_sum_of_subset
        simp
  · by_cases hboundary : a + (u' + 1) = k + 3
    · rw [published_left_child_base_boundary_eq_first_two_outer_coefficients
          ha hak hboundary]
      have hu'Index : u' - 1 = k - a + 1 := by omega
      rw [hu'Index, max_eq_right (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      simp
    · have hactive : k + 4 ≤ a + (u' + 1) := by omega
      rw [decomposableThreshold_eq_window (by omega) (by omega) hactive]
      have hleft : k - a ≤ u' - 1 := by omega
      rw [max_eq_right hleft]
      unfold decomposableBinomialWindow
      have htop : u' + 1 - 2 = u' - 1 := by omega
      rw [htop]

/-- Color-dual deep-base allocation: the next upper-child threshold fits in
the last coefficient of the outer Pascal window. -/
theorem published_right_child_deep_base_le_last_outer_coefficient
    {a' u k : ℕ} (ha' : 1 ≤ a') (hu : 2 ≤ u) (huk : u ≤ k)
    (hdeep : (a' + 1) + u ≤ k + 2) :
    decomposableThreshold (a' + 1) u k ≤
      Nat.choose (k - 2) (u - 2) := by
  rw [decomposableThreshold_eq_choose (by omega) hu (by omega)]
  let childRow := (a' + 1) + u - 4
  have hrow : childRow ≤ k - 2 := by simp [childRow]; omega
  have hchildIndex : childRow - (a' + 1 - 2) = u - 2 := by
    simp [childRow]
    omega
  have hchildSymm : Nat.choose childRow (a' + 1 - 2) =
      Nat.choose childRow (u - 2) := by
    rw [← hchildIndex, Nat.choose_symm (by simp [childRow]; omega)]
  rw [hchildSymm]
  exact Nat.choose_le_choose (u - 2) hrow

/-- At the color-dual base/active boundary, the next child threshold is the
last two coefficients of the outer row. -/
theorem published_right_child_base_boundary_eq_last_two_outer_coefficients
    {a' u k : ℕ} (ha' : 1 ≤ a') (hu : 3 ≤ u)
    (hboundary : (a' + 1) + u = k + 3) :
    decomposableThreshold (a' + 1) u k =
      Nat.choose (k - 2) (u - 3) + Nat.choose (k - 2) (u - 2) := by
  rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
  have hrow : (a' + 1) + u - 4 = (k - 2) + 1 := by omega
  have hchildIndex : (a' + 1) + u - 4 - (a' + 1 - 2) = u - 2 := by
    omega
  have hchildSymm :
      Nat.choose ((a' + 1) + u - 4) (a' + 1 - 2) =
        Nat.choose ((a' + 1) + u - 4) (u - 2) := by
    rw [← hchildIndex, Nat.choose_symm (by omega)]
  rw [hchildSymm, hrow]
  have hcolumn : u - 2 = (u - 3) + 1 := by omega
  rw [hcolumn, Nat.choose_succ_succ]

/-- Uniform color-dual allocation of the next upper-child threshold to a
suffix of the outer Pascal window. -/
theorem published_right_child_le_outer_suffix
    {a' u k : ℕ} (ha' : 1 ≤ a') (hu : 3 ≤ u) (huk : u ≤ k) :
    decomposableThreshold (a' + 1) u k ≤
      ∑ j ∈ Finset.Icc (min (u - 2) (k - (a' + 1))) (u - 2),
        Nat.choose (k - 2) j := by
  by_cases hdeep : (a' + 1) + u ≤ k + 2
  · calc
      decomposableThreshold (a' + 1) u k ≤
          Nat.choose (k - 2) (u - 2) :=
        published_right_child_deep_base_le_last_outer_coefficient
          ha' (by omega) huk hdeep
      _ = ∑ j ∈ ({u - 2} : Finset ℕ), Nat.choose (k - 2) j := by simp
      _ ≤ ∑ j ∈ Finset.Icc (min (u - 2) (k - (a' + 1))) (u - 2),
          Nat.choose (k - 2) j := by
        apply Finset.sum_le_sum_of_subset
        simp
  · by_cases hboundary : (a' + 1) + u = k + 3
    · rw [published_right_child_base_boundary_eq_last_two_outer_coefficients
          ha' hu hboundary]
      have hstart : k - (a' + 1) = u - 3 := by omega
      rw [hstart, min_eq_right (by omega)]
      have hsum : (∑ j ∈ Finset.Icc (u - 3) (u - 2),
          Nat.choose (k - 2) j) =
          Nat.choose (k - 2) (u - 3) + Nat.choose (k - 2) (u - 2) := by
        have htop : u - 2 = (u - 3) + 1 := by omega
        rw [htop, Finset.sum_Icc_succ_top (by omega)]
        simp
      rw [hsum]
    · have hactive : k + 4 ≤ (a' + 1) + u := by omega
      rw [decomposableThreshold_eq_window (by omega) (by omega) hactive]
      have hright : k - (a' + 1) ≤ u - 2 := by omega
      rw [min_eq_right hright]
      rfl

/-- If neither auxiliary parameter is saturated, the two adjacent child
thresholds fit into disjoint prefix and suffix allocations of the outer Pascal
window.  Consequently actual complementary child cardinalities at the outer
threshold are impossible. -/
theorem published_nonsaturated_next_threshold_pair_le
    {a u k a' u' : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (ha' : 1 ≤ a') (hu' : 1 ≤ u')
    (ha'Gap : a' + 1 < a) (hu'Gap : u' + 1 < u)
    (hsum : a' + u' ≤ k - 1) (hactive : k + 4 ≤ a + u) :
    decomposableThreshold a (u' + 1) k +
        decomposableThreshold (a' + 1) u k ≤
      decomposableThreshold a u k := by
  let leftSet : Finset ℕ := Finset.Icc (k - a) (max (k - a) (u' - 1))
  let rightSet : Finset ℕ := Finset.Icc (min (u - 2) (k - (a' + 1))) (u - 2)
  let outerSet : Finset ℕ := Finset.Icc (k - a) (u - 2)
  let coefficient : ℕ → ℕ := fun j ↦ Nat.choose (k - 2) j
  have hleft : decomposableThreshold a (u' + 1) k ≤
      ∑ j ∈ leftSet, coefficient j := by
    exact published_left_child_le_outer_prefix (by omega) hu' hak
  have hright : decomposableThreshold (a' + 1) u k ≤
      ∑ j ∈ rightSet, coefficient j := by
    exact published_right_child_le_outer_suffix ha' (by omega) huk
  have hendStart : max (k - a) (u' - 1) <
      min (u - 2) (k - (a' + 1)) := by
    rw [max_lt_iff]
    constructor
    · rw [lt_min_iff]
      constructor <;> omega
    · rw [lt_min_iff]
      constructor <;> omega
  have hdisjoint : Disjoint leftSet rightSet := by
    rw [Finset.disjoint_left]
    intro j hjPrefix hjSuffix
    simp only [leftSet, rightSet, Finset.mem_Icc] at hjPrefix hjSuffix
    omega
  have hsubset : leftSet ∪ rightSet ⊆ outerSet := by
    have hprefixTop : max (k - a) (u' - 1) ≤ u - 2 := by
      rw [max_le_iff]
      constructor <;> omega
    have hsuffixBottom : k - a ≤ min (u - 2) (k - (a' + 1)) := by
      rw [le_min_iff]
      constructor <;> omega
    intro j hj
    rcases Finset.mem_union.mp hj with hjPrefix | hjSuffix
    · simp only [leftSet, Finset.mem_Icc] at hjPrefix
      simp only [outerSet, Finset.mem_Icc]
      omega
    · simp only [rightSet, Finset.mem_Icc] at hjSuffix
      simp only [outerSet, Finset.mem_Icc]
      omega
  calc
    decomposableThreshold a (u' + 1) k +
        decomposableThreshold (a' + 1) u k ≤
        (∑ j ∈ leftSet, coefficient j) +
          ∑ j ∈ rightSet, coefficient j := Nat.add_le_add hleft hright
    _ = ∑ j ∈ leftSet ∪ rightSet, coefficient j :=
      (Finset.sum_union hdisjoint).symm
    _ ≤ ∑ j ∈ outerSet, coefficient j := Finset.sum_le_sum_of_subset hsubset
    _ = decomposableThreshold a u k := by
      rw [decomposableThreshold_eq_window (by omega) (by omega) hactive]
      rfl

/-- Uniform arithmetic saturation classification.  Whenever actual positive
child sizes at an active parent realize the two adjacent maximal-index bounds,
one auxiliary parameter must be saturated.  The auxiliary parameter on the
other side is then automatically below its active-window endpoint. -/
theorem published_feasible_auxiliary_saturation
    {a u k a' u' lowerCard upperCard : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (ha' : 1 ≤ a') (hu' : 1 ≤ u')
    (ha'Lt : a' < a) (hu'Lt : u' < u)
    (hsum : a' + u' ≤ k - 1) (hactive : k + 4 ≤ a + u)
    (htotal : lowerCard + upperCard = decomposableThreshold a u k + 1)
    (hlower : lowerCard ≤ decomposableThreshold a (u' + 1) k)
    (hupper : upperCard ≤ decomposableThreshold (a' + 1) u k) :
    (a' + 1 = a ∧ u' < k - a + 1) ∨
      (u' + 1 = u ∧ a' < k - u + 1) := by
  have hpairGt := published_next_threshold_pair_gt_of_complementary_cards
    htotal hlower hupper
  have hsaturated : a' + 1 = a ∨ u' + 1 = u := by
    by_contra hnot
    rw [not_or] at hnot
    have hpairLe := published_nonsaturated_next_threshold_pair_le
      ha hu hak huk ha' hu' (by omega) (by omega) hsum hactive
    omega
  rcases hsaturated with ha'Eq | hu'Eq
  · left
    constructor
    · exact ha'Eq
    · omega
  · right
    constructor
    · exact hu'Eq
    · omega

/-- The two alternatives in `published_feasible_auxiliary_saturation` cannot
hold simultaneously at an active parent. -/
theorem published_saturated_auxiliary_alternatives_exclusive
    {a u k a' u' : ℕ} (hactive : k + 4 ≤ a + u) :
    ¬((a' + 1 = a ∧ u' < k - a + 1) ∧
      (u' + 1 = u ∧ a' < k - u + 1)) := by
  omega

/-- The exact arithmetic of the first feasible boundary not covered by the
index-one singleton theorem. -/
theorem first_non_singleton_published_boundary_arithmetic :
    decomposableThreshold 4 6 6 = 11 ∧
      decomposableThreshold 4 2 6 = 1 ∧
      decomposableThreshold 4 3 6 = 3 ∧
      decomposableThreshold 3 6 6 = 5 ∧
      decomposableThreshold 4 2 6 + Nat.choose 4 1 +
          decomposableThreshold 3 6 6 + Nat.choose 4 2 = 16 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
    Finset.sum_Icc_succ_top]

/-- Complementary child cardinalities realizing auxiliary indices
`(a',u') = (3,2)` at the twelve-point `(4,6,6)` boundary are exactly
`(2,10)` and `(3,9)`. -/
theorem first_non_singleton_published_boundary_child_cards
    {lowerCard upperCard : ℕ}
    (htotal : lowerCard + upperCard = decomposableThreshold 4 6 6 + 1)
    (hlowerPrev : decomposableThreshold 4 2 6 < lowerCard)
    (hlowerNext : lowerCard ≤ decomposableThreshold 4 3 6) :
    (lowerCard = 2 ∧ upperCard = 10) ∨
      (lowerCard = 3 ∧ upperCard = 9) := by
  norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
    Finset.sum_Icc_succ_top] at htotal hlowerPrev hlowerNext
  omega

/-- An upper child of cardinality six through eleven has color-dual maximal
cap index three at the first `(4,6,6)` saturated boundary. -/
theorem publishedCapChildIndex_eq_three_at_first_saturated_boundary
    {childCard : ℕ} (hlower : 6 ≤ childCard) (hupper : childCard ≤ 11) :
    publishedCapChildIndex 4 6 6 childCard = 3 := by
  rw [publishedCapChildIndex, Nat.findGreatest_eq_iff]
  refine ⟨by omega, ?_, ?_⟩
  · intro _
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]
    omega
  · intro index hthree hfour
    have hindex : index = 4 := by omega
    subst index
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]
    omega

end ErdosSzekeres

end
