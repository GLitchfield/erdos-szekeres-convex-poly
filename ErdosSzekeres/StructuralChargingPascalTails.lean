module

public import ErdosSzekeres.StructuralChargingSaturatedPredecessor
public import ErdosSzekeres.DecomposableStateDuality

@[expose] public section

/-!
# Uniform Pascal tails for saturated published slices

The scalar failures in the published induction do not require a separate
finite arithmetic classification at every state.  Once one auxiliary index
is saturated, maximality places the opposite actual child in one of two
binomial tails of row `k - 3`.
-/

namespace ErdosSzekeres

/-- In an upper-saturated branch, the next lower-child threshold fits in the
left Pascal tail of row `k - 3`. -/
theorem lower_saturated_next_threshold_le_pascal_tail
    {a k u' : ℕ}
    (ha : 4 ≤ a) (hak : a ≤ k) (hu' : 1 ≤ u')
    (hoff : u' < k - a + 1) :
    decomposableThreshold a (u' + 1) k ≤
      Nat.choose (k - 3) (a - 2) := by
  rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
  exact Nat.choose_le_choose (a - 2) (by omega)

/-- The color-dual right-tail bound for a lower-saturated branch. -/
theorem upper_saturated_next_threshold_le_pascal_tail
    {u k a' : ℕ}
    (hu : 4 ≤ u) (huk : u ≤ k) (ha' : 1 ≤ a')
    (hoff : a' < k - u + 1) :
    decomposableThreshold (a' + 1) u k ≤
      Nat.choose (k - 3) (u - 2) := by
  rw [decomposableThreshold_comm (by omega) (by omega) (by omega) huk]
  exact lower_saturated_next_threshold_le_pascal_tail hu huk ha' hoff

/-- The left tail width is no larger than the active outer Pascal window. -/
theorem lower_pascal_tail_le_decomposableThreshold
    {a u k : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k)
    (hactive : k + 4 ≤ a + u) :
    Nat.choose (k - 3) (a - 2) ≤ decomposableThreshold a u k := by
  rw [decomposableThreshold_eq_window (by omega) (by omega) hactive]
  unfold decomposableBinomialWindow
  have hcoefficient : Nat.choose (k - 3) (a - 2) ≤
      Nat.choose (k - 2) (k - a) := by
    by_cases hakEq : a = k
    · subst a
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      omega
    · have hakLt : a < k := by omega
      have hsymm : Nat.choose (k - 3) (a - 2) =
          Nat.choose (k - 3) (k - a - 1) := by
        have hindex : k - a - 1 = (k - 3) - (a - 2) := by omega
        rw [hindex, Nat.choose_symm (by omega)]
      calc
        Nat.choose (k - 3) (a - 2) =
            Nat.choose (k - 3) (k - a - 1) := hsymm
        _ ≤ Nat.choose (k - 3) (k - a - 1) +
            Nat.choose (k - 3) (k - a - 1).succ := Nat.le_add_right _ _
        _ = Nat.choose (k - 3).succ (k - a - 1).succ :=
          (Nat.choose_succ_succ _ _).symm
        _ = Nat.choose (k - 2) (k - a) := by congr 2 <;> omega
  exact hcoefficient.trans (Finset.single_le_sum
    (fun _ _ ↦ Nat.zero_le _) (by simp; omega))

/-- The color-dual right tail also lies within the active outer window. -/
theorem upper_pascal_tail_le_decomposableThreshold
    {a u k : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hactive : k + 4 ≤ a + u) :
    Nat.choose (k - 3) (u - 2) ≤ decomposableThreshold a u k := by
  rw [decomposableThreshold_comm (by omega) (by omega) hak huk]
  exact lower_pascal_tail_le_decomposableThreshold hu ha huk (by omega)

/-- Uniform two-tail classification for the actual cardinalities of a pair
of published child slices.  The result consumes the existing unique
saturation theorem and contains no state-specific interval enumeration. -/
theorem published_slice_pair_card_in_pascal_tails
    {α : Type*} {a u k : ℕ} {lower upper : Finset α}
    (lowerSlice : PublishedChildSlice a u k lower)
    (upperSlice : PublishedCapChildSlice a u k upper)
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hlower : lower.Nonempty) (hupper : upper.Nonempty)
    (hsum : upperSlice.index + lowerSlice.index ≤ k - 1)
    (hactive : k + 4 ≤ a + u)
    (htotal :
      lower.card + upper.card = decomposableThreshold a u k + 1)
    (hlowerOuter : lower.card ≤ decomposableThreshold a u k)
    (hupperOuter : upper.card ≤ decomposableThreshold a u k) :
    lower.card ≤ Nat.choose (k - 3) (a - 2) ∨
      upper.card ≤ Nat.choose (k - 3) (u - 2) := by
  obtain ⟨branch, hvalid, _⟩ :=
    published_slice_pair_saturation_existsUnique
      lowerSlice upperSlice ha hu hak huk hlower hupper hsum hactive htotal
      hlowerOuter hupperOuter
  cases branch with
  | lower =>
      right
      exact (upperSlice.child_card_le_next_threshold
        (by omega) hupper hupperOuter).trans
          (upper_saturated_next_threshold_le_pascal_tail
            hu huk (upperSlice.index_pos (by omega) hupper) hvalid.2)
  | upper =>
      left
      exact (lowerSlice.child_card_le_next_threshold
        (by omega) hlower hlowerOuter).trans
          (lower_saturated_next_threshold_le_pascal_tail
            ha hak (lowerSlice.index_pos (by omega) hlower) hvalid.2)

/-- Reservoir cardinality retained after replacing a small lower Pascal tail
by one singleton vertex. -/
def lowerPascalTailReservoir (a u k : ℕ) : ℕ :=
  decomposableThreshold a u k + 1 - Nat.choose (k - 3) (a - 2)

/-- The color-dual reservoir cardinality for a small upper tail. -/
def upperPascalTailReservoir (a u k : ℕ) : ℕ :=
  decomposableThreshold a u k + 1 - Nat.choose (k - 3) (u - 2)

/-- Uniform lower-tail geometric gate: one lower vertex and an exact
large-child reservoir cannot remain open. -/
def SingletonLowerPascalTailGate (a u k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {q : Fin n}
      {upper : Finset (Fin n)},
    IsDecomposableOn χ upper → HasDeepBelowSplit χ {q} upper →
      upper.card = lowerPascalTailReservoir a u k →
        ¬ContainsCapSet χ ({q} ∪ upper) a →
          ¬ContainsCupSet χ ({q} ∪ upper) u →
            ¬ContainsStrongPolygonSet χ ({q} ∪ upper) k → False

/-- Uniform upper-tail geometric gate. -/
def SingletonUpperPascalTailGate (a u k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {q : Fin n}
      {lower : Finset (Fin n)},
    IsDecomposableOn χ lower → HasDeepBelowSplit χ lower {q} →
      lower.card = upperPascalTailReservoir a u k →
        ¬ContainsCapSet χ (lower ∪ {q}) a →
          ¬ContainsCupSet χ (lower ∪ {q}) u →
            ¬ContainsStrongPolygonSet χ (lower ∪ {q}) k → False

/-- Strict predecessors and the two parameter-uniform singleton gates close
every exact active critical root.  This is the generic integration shell for
the Pascal-tail arithmetic theorem. -/
theorem criticalRootImpossible_of_predecessors_pascal_tail_gates
    {a u k : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hactive : k + 4 ≤ a + u)
    (hpredecessors : ∀ a' u', a' + u' < a + u →
      DecomposableStateUpper a' u' k)
    (hlowerGate : SingletonLowerPascalTailGate a u k)
    (hupperGate : SingletonUpperPascalTailGate a u k) :
    DecomposableCriticalRootImpossible a u k := by
  intro n χ lower upper hlower hupper hdeep hlowerBound hupperBound
    hcard hnoCap hnoCup hnoStrong
  have htotal : lower.card + upper.card =
      decomposableThreshold a u k + 1 := by
    rw [← Finset.card_union_of_disjoint hdeep.disjoint]
    exact hcard
  have hlowerNonempty : lower.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hupperNonempty : upper.Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨lowerSlice⟩ := exists_publishedChildSlice
    (a := a) (u := u) (k := k) (child := lower) (by omega) hlowerNonempty
  obtain ⟨upperSlice, _⟩ := exists_publishedCapChildSlice_core_superset
    (a := a) (u := u) (k := k) (child := upper) (seed := ∅)
      (by omega) hupperNonempty (by simp) (by simp)
  have hindexSum := published_slice_indices_add_le_of_predecessors
    lowerSlice upperSlice hlowerNonempty hupperNonempty hlower hupper hdeep
    hlowerBound hupperBound hpredecessors hnoCap hnoCup hnoStrong
  rcases published_slice_pair_card_in_pascal_tails
      lowerSlice upperSlice ha hu hak huk hlowerNonempty hupperNonempty
      hindexSum hactive htotal hlowerBound hupperBound with
    hlowerSmall | hupperSmall
  · have htailLe := lower_pascal_tail_le_decomposableThreshold
      ha hu hak hactive
    have hreservoirPos : 0 < lowerPascalTailReservoir a u k := by
      simp only [lowerPascalTailReservoir]
      omega
    have hreservoirLe : lowerPascalTailReservoir a u k ≤ upper.card := by
      simp only [lowerPascalTailReservoir]
      omega
    obtain ⟨q, hq⟩ := hlowerNonempty
    obtain ⟨upper', hupperSub, hupperCard⟩ :=
      Finset.exists_subset_card_eq hreservoirLe
    have hupperNonempty' : upper'.Nonempty :=
      Finset.card_pos.mp (hupperCard ▸ hreservoirPos)
    have hupper' : IsDecomposableOn χ upper' :=
      hupper.subset hupperSub hupperNonempty'
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
  · have htailLe := upper_pascal_tail_le_decomposableThreshold
      ha hu hak huk hactive
    have hreservoirPos : 0 < upperPascalTailReservoir a u k := by
      simp only [upperPascalTailReservoir]
      omega
    have hreservoirLe : upperPascalTailReservoir a u k ≤ lower.card := by
      simp only [upperPascalTailReservoir]
      omega
    obtain ⟨q, hq⟩ := hupperNonempty
    obtain ⟨lower', hlowerSub, hlowerCard⟩ :=
      Finset.exists_subset_card_eq hreservoirLe
    have hlowerNonempty' : lower'.Nonempty :=
      Finset.card_pos.mp (hlowerCard ▸ hreservoirPos)
    have hlower' : IsDecomposableOn χ lower' :=
      hlower.subset hlowerSub hlowerNonempty'
    have hqSub : {q} ⊆ upper := by simpa using hq
    have hdeep' : HasDeepBelowSplit χ lower' {q} :=
      hdeep.mono hlowerSub hqSub
    have hunionSub : lower' ∪ {q} ⊆ lower ∪ upper :=
      Finset.union_subset_union hlowerSub hqSub
    exact hupperGate hlower' hdeep' hlowerCard
      (fun hcap ↦ hnoCap
        (FinsetPolygon.ContainsCapSet.mono hcap hunionSub))
      (fun hcup ↦ hnoCup
        (FinsetPolygon.ContainsCupSet.mono hcup hunionSub))
      (fun hstrong ↦ hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub))

end ErdosSzekeres

end
