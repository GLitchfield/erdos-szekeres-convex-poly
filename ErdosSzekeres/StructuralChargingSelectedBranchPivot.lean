module

public import ErdosSzekeres.StructuralChargingConservedBranch
public import ErdosSzekeres.StructuralChargingGapTokenConservation

@[expose] public section

/-!
# Selected-branch pivot resources

The conserved right-endpoint owner need not lie in the saturated child.  The
hidden-gap witness nevertheless supplies a different actual vertex there: its
intervening opposite-child pivot.  Because published cores may be chosen to
contain any fitting singleton seed, that pivot can be retained in a published
slice on the selected side.

This is a branch-local existence theorem.  It does not make the pivot
immutable across transports, prevent pivot reuse, or pay a Pascal increment.
-/

namespace ErdosSzekeres

namespace PublishedSaturatedBranch

/-- The promoted hidden-gap color whose intervening pivot lies in the branch:
hidden upper gaps promote cups into the lower branch, while hidden lower gaps
promote caps into the upper branch. -/
def promotedColor : PublishedSaturatedBranch → Turn
  | .lower => .left
  | .upper => .right

end PublishedSaturatedBranch

/-- The canonical active pivot is the left endpoint of the parent crossing
that receives the hidden gap. -/
noncomputable def HiddenGapSource.enteringPivot
    {n : ℕ} {lower upper : Finset (Fin n)} {color : Turn}
    (source : HiddenGapSource lower upper color) : Fin n :=
  source.enteringParentCrossingGap.1.left

theorem HiddenGapSource.enteringPivot_between
    {n : ℕ} {lower upper : Finset (Fin n)} {color : Turn}
    (source : HiddenGapSource lower upper color) :
    source.1.left < source.enteringPivot ∧
      source.enteringPivot < source.1.right := by
  constructor
  · exact source.left_lt_enteringParentCrossingGap_left
  · have htarget := mem_parentCrossingGaps_iff.mp
      source.enteringParentCrossingGap.2
    rw [← source.enteringParentCrossingGap_right]
    exact htarget.1.1

/-- The canonical pivot lies in the child opposite the hidden gap: lower for
a hidden upper gap, and upper for a hidden lower gap. -/
theorem HiddenGapSource.enteringPivot_mem_oppositeChild
    {n : ℕ} {lower upper : Finset (Fin n)} {color : Turn}
    (source : HiddenGapSource lower upper color)
    (hdisjoint : Disjoint lower upper) :
    match color with
    | .left => source.enteringPivot ∈ lower
    | .right => source.enteringPivot ∈ upper := by
  have hsource := mem_hiddenGapSources_iff.mp source.2
  have htarget := mem_parentCrossingGaps_iff.mp
    source.enteringParentCrossingGap.2
  have hright := source.enteringParentCrossingGap_right
  cases color with
  | left =>
      rcases htarget.2.2 with hforward | hreverse
      · exact hforward.1
      · exfalso
        exact (Finset.disjoint_left.mp hdisjoint hreverse.2
          (hright ▸ hsource.1.2.2.1)).elim
  | right =>
      rcases htarget.2.2 with hforward | hreverse
      · exfalso
        exact (Finset.disjoint_left.mp hdisjoint hsource.1.2.2.1
          (hright ▸ hforward.2)).elim
      · exact hreverse.1

/-- Different hidden gaps have different canonical active pivots. -/
theorem HiddenGapSource.enteringPivot_injective
    {n : ℕ} {lower upper : Finset (Fin n)} {color : Turn} :
    Function.Injective
      (HiddenGapSource.enteringPivot
        (lower := lower) (upper := upper) (color := color)) := by
  intro first second hpivot
  apply HiddenGapSource.enteringParentCrossingGap_injective
  apply Subtype.ext
  apply SweepSpanEndpoints.IsAdjacentIn.eq_of_left_eq
    (mem_parentCrossingGaps_iff.mp
      first.enteringParentCrossingGap.2).1
    (mem_parentCrossingGaps_iff.mp
      second.enteringParentCrossingGap.2).1
  exact hpivot

/-- A selected branch's color-compatible hidden gaps embed into actual,
pairwise distinct vertices of that branch. -/
noncomputable def publishedBranchPivotEmbedding
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hdisjoint : Disjoint lower upper)
    (branch : PublishedSaturatedBranch) :
    HiddenGapSource lower upper branch.promotedColor ↪
      RetainedVertexOwner (branch.child lower upper) where
  toFun source := ⟨source.enteringPivot, by
    cases branch with
    | lower => exact source.enteringPivot_mem_oppositeChild hdisjoint
    | upper => exact source.enteringPivot_mem_oppositeChild hdisjoint⟩
  inj' := by
    intro first second heq
    apply HiddenGapSource.enteringPivot_injective
    exact congrArg Subtype.val heq

/-- Hence branch-compatible pivots have the first necessary local nonreuse
bound.  Fitting all of them in one retained core requires a sharper bound. -/
theorem publishedBranchPivot_card_le_child_card
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hdisjoint : Disjoint lower upper)
    (branch : PublishedSaturatedBranch) :
    Fintype.card (HiddenGapSource lower upper branch.promotedColor) ≤
      (branch.child lower upper).card := by
  simpa using Fintype.card_le_of_embedding
    (publishedBranchPivotEmbedding hdisjoint branch)

/-- Forget that a hidden upper gap is hidden and retain its upper-child
adjacency. -/
def hiddenUpperGapSourceAdjacencyEmbedding
    {n : ℕ} (lower upper : Finset (Fin n)) :
    HiddenGapSource lower upper .left ↪ SweepAdjacency upper where
  toFun source :=
    ⟨source.1, (mem_hiddenGapSources_iff.mp source.2).1⟩
  inj' := by
    intro first second heq
    apply Subtype.ext
    exact congrArg (fun gap : SweepAdjacency upper => gap.1) heq

/-- Forget that a hidden lower gap is hidden and retain its lower-child
adjacency. -/
def hiddenLowerGapSourceAdjacencyEmbedding
    {n : ℕ} (lower upper : Finset (Fin n)) :
    HiddenGapSource lower upper .right ↪ SweepAdjacency lower where
  toFun source :=
    ⟨source.1, (mem_hiddenGapSources_iff.mp source.2).1⟩
  inj' := by
    intro first second heq
    apply Subtype.ext
    exact congrArg (fun gap : SweepAdjacency lower => gap.1) heq

/-- Hidden upper gaps are also bounded by one fewer than their source-child
vertices. -/
theorem hiddenUpperGapSource_card_le
    {n : ℕ} (lower upper : Finset (Fin n)) (hupper : upper.Nonempty) :
    Fintype.card (HiddenGapSource lower upper .left) ≤ upper.card - 1 := by
  rw [← sweepAdjacency_card hupper]
  exact Fintype.card_le_of_embedding
    (hiddenUpperGapSourceAdjacencyEmbedding lower upper)

/-- Hidden lower gaps satisfy the color-dual source-child bound. -/
theorem hiddenLowerGapSource_card_le
    {n : ℕ} (lower upper : Finset (Fin n)) (hlower : lower.Nonempty) :
    Fintype.card (HiddenGapSource lower upper .right) ≤ lower.card - 1 := by
  rw [← sweepAdjacency_card hlower]
  exact Fintype.card_le_of_embedding
    (hiddenLowerGapSourceAdjacencyEmbedding lower upper)

/-- The source-child adjacency bound is not by itself sharp enough for the
selected core.  At the feasible saturated scalar state
`(a,u,k,a',u') = (4,8,8,3,4)` with child sizes `10+13`, it permits nine
hidden lower gaps while the upper retained core has only eight vertices. -/
theorem coarse_hiddenLowerGap_capacity_arithmetic_fails_at_488 :
    decomposableThreshold 4 8 8 + 1 = 23 ∧
      decomposableThreshold 4 4 8 < 10 ∧
      10 ≤ decomposableThreshold 4 5 8 ∧
      decomposableThreshold 3 8 8 < 13 ∧
      13 ≤ decomposableThreshold 4 8 8 ∧
      ¬(10 - 1 ≤ decomposableThreshold 3 8 8 + 1) := by
  norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
    Finset.sum_Icc_succ_top]

/-- The finite set of canonical pivots used by one promoted color. -/
noncomputable def hiddenGapEnteringPivotSeed
    {n : ℕ} (lower upper : Finset (Fin n)) (color : Turn) :
    Finset (Fin n) :=
  Finset.univ.image
    (HiddenGapSource.enteringPivot
      (lower := lower) (upper := upper) (color := color))

theorem hiddenGapEnteringPivotSeed_card
    {n : ℕ} (lower upper : Finset (Fin n)) (color : Turn) :
    (hiddenGapEnteringPivotSeed lower upper color).card =
      Fintype.card (HiddenGapSource lower upper color) := by
  classical
  rw [hiddenGapEnteringPivotSeed,
    Finset.card_image_of_injective Finset.univ
      HiddenGapSource.enteringPivot_injective,
    Finset.card_univ]

/-- A sharp enough cardinal estimate puts all lower-branch pivots into one
simultaneously chosen published core. -/
theorem exists_publishedLowerPivotSlice_of_card_le
    {n a u k : ℕ} {lower upper : Finset (Fin n)}
    (hu : 1 ≤ u) (hlower : lower.Nonempty)
    (hdisjoint : Disjoint lower upper)
    (hcapacity : Fintype.card (HiddenGapSource lower upper .left) ≤
      decomposableThreshold a
        (publishedChildIndex a u k lower.card) k + 1) :
    ∃ slice : PublishedChildSlice a u k lower,
      ∀ source : HiddenGapSource lower upper .left,
        source.enteringPivot ∈ slice.core := by
  classical
  let seed := hiddenGapEnteringPivotSeed lower upper .left
  have hseedSub : seed ⊆ lower := by
    intro pivot hpivot
    obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp hpivot
    exact source.enteringPivot_mem_oppositeChild hdisjoint
  have hseedCard : seed.card ≤
      decomposableThreshold a
        (publishedChildIndex a u k lower.card) k + 1 := by
    rw [show seed.card =
      Fintype.card (HiddenGapSource lower upper .left) by
        exact hiddenGapEnteringPivotSeed_card lower upper .left]
    exact hcapacity
  obtain ⟨slice, hseedCore⟩ :=
    exists_publishedChildSlice_core_superset
      hu hlower hseedSub hseedCard
  refine ⟨slice, ?_⟩
  intro source
  apply hseedCore
  exact Finset.mem_image.mpr ⟨source, Finset.mem_univ source, rfl⟩

/-- The color-dual capacity estimate likewise puts all upper-branch pivots in
one simultaneously chosen retained core. -/
theorem exists_publishedUpperPivotSlice_of_card_le
    {n a u k : ℕ} {lower upper : Finset (Fin n)}
    (ha : 1 ≤ a) (hupper : upper.Nonempty)
    (hdisjoint : Disjoint lower upper)
    (hcapacity : Fintype.card (HiddenGapSource lower upper .right) ≤
      decomposableThreshold
        (publishedCapChildIndex a u k upper.card) u k + 1) :
    ∃ slice : PublishedCapChildSlice a u k upper,
      ∀ source : HiddenGapSource lower upper .right,
        source.enteringPivot ∈ slice.core := by
  classical
  let seed := hiddenGapEnteringPivotSeed lower upper .right
  have hseedSub : seed ⊆ upper := by
    intro pivot hpivot
    obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp hpivot
    exact source.enteringPivot_mem_oppositeChild hdisjoint
  have hseedCard : seed.card ≤
      decomposableThreshold
        (publishedCapChildIndex a u k upper.card) u k + 1 := by
    rw [show seed.card =
      Fintype.card (HiddenGapSource lower upper .right) by
        exact hiddenGapEnteringPivotSeed_card lower upper .right]
    exact hcapacity
  obtain ⟨slice, hseedCore⟩ :=
    exists_publishedCapChildSlice_core_superset
      ha hupper hseedSub hseedCard
  refine ⟨slice, ?_⟩
  intro source
  apply hseedCore
  exact Finset.mem_image.mpr ⟨source, Finset.mem_univ source, rfl⟩

/-- A hidden-gap pivot retained in an actual published slice of the selected
branch.  The conserved endpoint owner and this active pivot are deliberately
distinct fields. -/
inductive PublishedBranchPivotResource
    {n a u k : ℕ} {lower upper : Finset (Fin n)} :
    (branch : PublishedSaturatedBranch) →
    HiddenGapSource lower upper branch.promotedColor → Type
  | lower (source : HiddenGapSource lower upper .left)
      (pivot : Fin n) (pivot_mem_child : pivot ∈ lower)
      (left_lt_pivot : source.1.left < pivot)
      (pivot_lt_right : pivot < source.1.right)
      (slice : PublishedChildSlice a u k lower)
      (pivot_mem_core : pivot ∈ slice.core) :
      PublishedBranchPivotResource .lower source
  | upper (source : HiddenGapSource lower upper .right)
      (pivot : Fin n) (pivot_mem_child : pivot ∈ upper)
      (left_lt_pivot : source.1.left < pivot)
      (pivot_lt_right : pivot < source.1.right)
      (slice : PublishedCapChildSlice a u k upper)
      (pivot_mem_core : pivot ∈ slice.core) :
      PublishedBranchPivotResource .upper source

/-- Every color-compatible hidden gap has an intervening pivot in its selected
branch, and a published slice can be chosen to retain that singleton pivot. -/
theorem exists_publishedBranchPivotResource
    {n a u k : ℕ} {lower upper : Finset (Fin n)}
    (ha : 1 ≤ a) (hu : 1 ≤ u)
    (branch : PublishedSaturatedBranch)
    (source : HiddenGapSource lower upper branch.promotedColor) :
    Nonempty (PublishedBranchPivotResource
      (a := a) (u := u) (k := k) branch source) := by
  cases branch with
  | lower =>
      have hhidden : IsHiddenUpperGap lower upper source.1 :=
        mem_hiddenGapSources_iff.mp source.2
      obtain ⟨pivot, hpivotLower, hleft, hright⟩ := hhidden.2
      obtain ⟨slice, hpivotCore⟩ :=
        exists_publishedChildSlice_core_superset
          (seed := {pivot}) hu ⟨pivot, hpivotLower⟩
          (by simp [hpivotLower]) (by simp)
      exact ⟨PublishedBranchPivotResource.lower source pivot
        hpivotLower hleft hright slice
        (hpivotCore (Finset.mem_singleton_self pivot))⟩
  | upper =>
      have hhidden : IsHiddenLowerGap lower upper source.1 :=
        mem_hiddenGapSources_iff.mp source.2
      obtain ⟨pivot, hpivotUpper, hleft, hright⟩ := hhidden.2
      obtain ⟨slice, hpivotCore⟩ :=
        exists_publishedCapChildSlice_core_superset
          (seed := {pivot}) ha ⟨pivot, hpivotUpper⟩
          (by simp [hpivotUpper]) (by simp)
      exact ⟨PublishedBranchPivotResource.upper source pivot
        hpivotUpper hleft hright slice
        (hpivotCore (Finset.mem_singleton_self pivot))⟩

end ErdosSzekeres

end
