module

public import ErdosSzekeres.StructuralChargingPascalTails
public import ErdosSzekeres.StructuralChargingTransport
public import ErdosSzekeres.StructuralChargingSaturatedResource
public import ErdosSzekeres.StructuralChargingCupBlocks67Symbolic

@[expose] public section

/-!
# Geometric interfaces for the two uniform Pascal tails

The arithmetic tail theorem leaves one actual child in a binomial-width tail.
This file separates the exact retained-child obligations from the stronger
singleton restrictions used by the first implementations.  It also records
color duality and three certificate-free positive controls.
-/

namespace ErdosSzekeres

/-- Exact geometric obligation for a critical root whose lower child lies in
the left Pascal tail.  Unlike `SingletonLowerPascalTailGate`, this retains the
whole small child. -/
def LowerPascalTailCriticalGate (a u k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)},
    IsDecomposableOn χ lower → IsDecomposableOn χ upper →
      HasDeepBelowSplit χ lower upper →
        lower.card ≤ decomposableThreshold a u k →
          upper.card ≤ decomposableThreshold a u k →
            (lower ∪ upper).card = decomposableThreshold a u k + 1 →
              lower.card ≤ Nat.choose (k - 3) (a - 2) →
                ¬ContainsCapSet χ (lower ∪ upper) a →
                  ¬ContainsCupSet χ (lower ∪ upper) u →
                    ¬ContainsStrongPolygonSet χ (lower ∪ upper) k → False

/-- Color-dual retained-child obligation for the right Pascal tail. -/
def UpperPascalTailCriticalGate (a u k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)},
    IsDecomposableOn χ lower → IsDecomposableOn χ upper →
      HasDeepBelowSplit χ lower upper →
        lower.card ≤ decomposableThreshold a u k →
          upper.card ≤ decomposableThreshold a u k →
            (lower ∪ upper).card = decomposableThreshold a u k + 1 →
              upper.card ≤ Nat.choose (k - 3) (u - 2) →
                ¬ContainsCapSet χ (lower ∪ upper) a →
                  ¬ContainsCupSet χ (lower ∪ upper) u →
                    ¬ContainsStrongPolygonSet χ (lower ∪ upper) k → False

/-- Parameter-uniform local consumer suggested by all established lower-tail
proofs.  Around a singleton root, absence of a parent `a`-cap makes both
ordered gap sides `(a-1)`-cap-free.  Bounding every such pair strictly below
the Pascal reservoir closes the singleton gate. -/
def PascalTailTwoSideBound (a u k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ¬ContainsCapSet χ left (a - 1) →
        ¬ContainsCapSet χ right (a - 1) →
          OneChangeOn χ (left ∪ right) →
            ¬ContainsCapSet χ (left ∪ right) a →
              ¬ContainsCupSet χ (left ∪ right) u →
                ¬ContainsStrongPolygonSet χ (left ∪ right) k →
                  left.card + right.card < lowerPascalTailReservoir a u k

/-- A uniform ordered two-side bound supplies the full singleton-lower
Pascal-tail gate. -/
theorem singletonLowerPascalTailGate_of_twoSideBound
    {a u k : ℕ} (ha : 2 ≤ a) (hbound : PascalTailTwoSideBound a u k) :
    SingletonLowerPascalTailGate a u k := by
  classical
  intro n χ q upper hupper hdeep hcard hnoCap hnoCup hnoStrong
  have hqLower : q ∈ ({q} : Finset (Fin n)) := by simp
  have hqNotUpper : q ∉ upper := by
    intro hqUpper
    exact (Finset.disjoint_left.mp hdeep.disjoint) hqLower hqUpper
  let left := upper.filter (· < q)
  let right := upper.filter (q < ·)
  have haPredSucc : a - 1 + 1 = a := by omega
  have hnoParentCap :
      ¬ContainsCapSet χ ({q} ∪ upper) (a - 1 + 1) := by
    rw [haPredSucc]
    exact hnoCap
  have hsides : ¬ContainsCapSet χ left (a - 1) ∧
      ¬ContainsCapSet χ right (a - 1) := by
    simpa [left, right] using
      (gap_sides_avoid_cap_of_no_parent_succ_cap
        (r := a - 1) hdeep hqLower hnoParentCap)
  have hunion : left ∪ right = upper := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    · intro hx
      have hxq : x ≠ q := by rintro rfl; exact hqNotUpper hx
      rcases lt_or_gt_of_ne hxq with hxlt | hxgt
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hxgt⟩)
  have hdisjoint : Disjoint left right := by
    rw [Finset.disjoint_left]
    intro x hxLeft hxRight
    have hxlt := (Finset.mem_filter.mp hxLeft).2
    have hxgt := (Finset.mem_filter.mp hxRight).2
    omega
  have horder : ∀ x ∈ left, ∀ y ∈ right, x < y := by
    intro x hx y hy
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2
  have honeChange : OneChangeOn χ (left ∪ right) := by
    intro i j l m hij hjl hlm hi hj hl hm
    exact hupper.turnSequenceAllowed hij hjl hlm
      (hunion ▸ hi) (hunion ▸ hj) (hunion ▸ hl) (hunion ▸ hm)
  have hnoCapUpper : ¬ContainsCapSet χ upper a := by
    intro hcap
    exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap Finset.subset_union_right)
  have hnoCupUpper : ¬ContainsCupSet χ upper u := by
    intro hcup
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup Finset.subset_union_right)
  have hnoStrongUpper : ¬ContainsStrongPolygonSet χ upper k := by
    intro hstrong
    exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.subset_union_right)
  have hsidesBound := hbound hdisjoint horder hsides.1 hsides.2 honeChange
    (by simpa [hunion] using hnoCapUpper)
    (by simpa [hunion] using hnoCupUpper)
    (by simpa [hunion] using hnoStrongUpper)
  have hcardSides : left.card + right.card = upper.card := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
  omega

/-- Strict predecessors reduce every exact critical root to the two retained
Pascal-tail obligations. -/
theorem criticalRootImpossible_of_predecessors_pascal_tail_critical_gates
    {a u k : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hactive : k + 4 ≤ a + u)
    (hpredecessors : ∀ a' u', a' + u' < a + u →
      DecomposableStateUpper a' u' k)
    (hlowerGate : LowerPascalTailCriticalGate a u k)
    (hupperGate : UpperPascalTailCriticalGate a u k) :
    DecomposableCriticalRootImpossible a u k := by
  intro n χ lower upper hlower hupper hdeep hlowerBound hupperBound
    hcard hnoCap hnoCup hnoStrong
  have htotal : lower.card + upper.card =
      decomposableThreshold a u k + 1 := by
    rw [← Finset.card_union_of_disjoint hdeep.disjoint]
    exact hcard
  have hlowerNonempty : lower.Nonempty := Finset.card_pos.mp (by omega)
  have hupperNonempty : upper.Nonempty := Finset.card_pos.mp (by omega)
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
  · exact hlowerGate hlower hupper hdeep hlowerBound hupperBound hcard
      hlowerSmall hnoCap hnoCup hnoStrong
  · exact hupperGate hlower hupper hdeep hlowerBound hupperBound hcard
      hupperSmall hnoCap hnoCup hnoStrong

/-- A zero-width left tail is impossible because a decomposable child is
nonempty. -/
theorem lowerPascalTailCriticalGate_of_choose_eq_zero
    {a u k : ℕ} (hzero : Nat.choose (k - 3) (a - 2) = 0) :
    LowerPascalTailCriticalGate a u k := by
  intro n χ lower upper hlower _ _ _ _ _ hlowerSmall
  rw [hzero] at hlowerSmall
  have hlowerPositive := Finset.card_pos.mpr hlower.nonempty
  omega

/-- The color-dual zero-width right tail is likewise vacuous. -/
theorem upperPascalTailCriticalGate_of_choose_eq_zero
    {a u k : ℕ} (hzero : Nat.choose (k - 3) (u - 2) = 0) :
    UpperPascalTailCriticalGate a u k := by
  intro n χ lower upper _ hupper _ _ _ _ hupperSmall
  rw [hzero] at hupperSmall
  have hupperPositive := Finset.card_pos.mpr hupper.nonempty
  omega

/-- Only positive Pascal tails require a geometric hypothesis. -/
theorem criticalRootImpossible_of_predecessors_positive_pascal_tail_gates
    {a u k : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hactive : k + 4 ≤ a + u)
    (hpredecessors : ∀ a' u', a' + u' < a + u →
      DecomposableStateUpper a' u' k)
    (hlowerGate : 0 < Nat.choose (k - 3) (a - 2) →
      LowerPascalTailCriticalGate a u k)
    (hupperGate : 0 < Nat.choose (k - 3) (u - 2) →
      UpperPascalTailCriticalGate a u k) :
    DecomposableCriticalRootImpossible a u k := by
  apply criticalRootImpossible_of_predecessors_pascal_tail_critical_gates
    ha hu hak huk hactive hpredecessors
  · by_cases hzero : Nat.choose (k - 3) (a - 2) = 0
    · exact lowerPascalTailCriticalGate_of_choose_eq_zero hzero
    · exact hlowerGate (Nat.pos_of_ne_zero hzero)
  · by_cases hzero : Nat.choose (k - 3) (u - 2) = 0
    · exact upperPascalTailCriticalGate_of_choose_eq_zero hzero
    · exact hupperGate (Nat.pos_of_ne_zero hzero)

/-- In the active E3 range, the left tail is nonempty exactly away from the
parameter boundary `a = k`. -/
theorem lower_pascal_tail_pos_iff
    {a k : ℕ} (ha : 4 ≤ a) (hak : a ≤ k) :
    0 < Nat.choose (k - 3) (a - 2) ↔ a < k := by
  constructor
  · intro hpos
    have hindex : a - 2 ≤ k - 3 :=
      Nat.choose_ne_zero_iff.mp (Nat.ne_of_gt hpos)
    omega
  · intro hakLt
    exact Nat.choose_pos (by omega)

/-- The right tail is nonempty exactly when `u < k`. -/
theorem upper_pascal_tail_pos_iff
    {u k : ℕ} (hu : 4 ≤ u) (huk : u ≤ k) :
    0 < Nat.choose (k - 3) (u - 2) ↔ u < k := by
  exact lower_pascal_tail_pos_iff hu huk

/-- Equivalent parameter-indexed form of the generic dispatcher: geometric
tail work is required precisely for parameters strictly below `k`. -/
theorem criticalRootImpossible_of_predecessors_interior_pascal_tail_gates
    {a u k : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hactive : k + 4 ≤ a + u)
    (hpredecessors : ∀ a' u', a' + u' < a + u →
      DecomposableStateUpper a' u' k)
    (hlowerGate : a < k → LowerPascalTailCriticalGate a u k)
    (hupperGate : u < k → UpperPascalTailCriticalGate a u k) :
    DecomposableCriticalRootImpossible a u k := by
  exact criticalRootImpossible_of_predecessors_positive_pascal_tail_gates
    ha hu hak huk hactive hpredecessors
    (fun hpos ↦ hlowerGate ((lower_pascal_tail_pos_iff ha hak).mp hpos))
    (fun hpos ↦ hupperGate ((upper_pascal_tail_pos_iff hu huk).mp hpos))

/-- The stronger singleton-lower gate consumes the exact retained lower tail
by selecting one lower vertex and an exact large-child reservoir. -/
theorem lowerPascalTailCriticalGate_of_singleton
    {a u k : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k)
    (hactive : k + 4 ≤ a + u)
    (hgate : SingletonLowerPascalTailGate a u k) :
    LowerPascalTailCriticalGate a u k := by
  intro n χ lower upper hlower hupper hdeep hlowerBound hupperBound
    hcard hlowerSmall hnoCap hnoCup hnoStrong
  have htotal : lower.card + upper.card =
      decomposableThreshold a u k + 1 := by
    rw [← Finset.card_union_of_disjoint hdeep.disjoint]
    exact hcard
  have hlowerNonempty : lower.Nonempty := hlower.nonempty
  have htailLe := lower_pascal_tail_le_decomposableThreshold
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
  exact hgate hupper' hdeep' hupperCard
    (fun hcap ↦ hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hunionSub))
    (fun hcup ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hunionSub))
    (fun hstrong ↦ hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub))

/-- The stronger singleton-upper gate similarly consumes the retained upper
tail. -/
theorem upperPascalTailCriticalGate_of_singleton
    {a u k : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hactive : k + 4 ≤ a + u)
    (hgate : SingletonUpperPascalTailGate a u k) :
    UpperPascalTailCriticalGate a u k := by
  intro n χ lower upper hlower hupper hdeep hlowerBound hupperBound
    hcard hupperSmall hnoCap hnoCup hnoStrong
  have htotal : lower.card + upper.card =
      decomposableThreshold a u k + 1 := by
    rw [← Finset.card_union_of_disjoint hdeep.disjoint]
    exact hcard
  have hupperNonempty : upper.Nonempty := hupper.nonempty
  have htailLe := upper_pascal_tail_le_decomposableThreshold
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
  exact hgate hlower' hdeep' hlowerCard
    (fun hcap ↦ hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hunionSub))
    (fun hcup ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hunionSub))
    (fun hstrong ↦ hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub))

/-- The two reservoir formulas are exchanged by cap--cup duality. -/
theorem upperPascalTailReservoir_eq_lower_dual
    {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
    upperPascalTailReservoir a u k = lowerPascalTailReservoir u a k := by
  unfold upperPascalTailReservoir lowerPascalTailReservoir
  rw [decomposableThreshold_comm ha hu hak huk]

/-- Singleton upper-tail closure at `(a,u,k)` is exactly singleton lower-tail
closure at the color-dual parameters `(u,a,k)`. -/
theorem singletonUpperPascalTailGate_iff_lower_dual
    {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
    SingletonUpperPascalTailGate a u k ↔
      SingletonLowerPascalTailGate u a k := by
  have hreservoir := upperPascalTailReservoir_eq_lower_dual ha hu hak huk
  constructor
  · intro hupper n χ q reservoir hdecomp hdeep hcard
      hnoCap hnoCup hnoStrong
    apply hupper (χ := χ.dual) hdecomp.dual hdeep.dual (hcard.trans hreservoir.symm)
    · intro hcap
      have horiginal := containsCapSet_dual_iff.mp hcap
      exact hnoCup (by simpa [Finset.union_comm] using horiginal)
    · intro hcup
      have horiginal := containsCupSet_dual_iff.mp hcup
      exact hnoCap (by simpa [Finset.union_comm] using horiginal)
    · intro hstrong
      have horiginal := containsStrongPolygonSet_dual_iff.mp hstrong
      exact hnoStrong (by simpa [Finset.union_comm] using horiginal)

  · intro hlower n χ q reservoir hdecomp hdeep hcard
      hnoCap hnoCup hnoStrong
    apply hlower (χ := χ.dual) hdecomp.dual hdeep.dual (hcard.trans hreservoir)
    · intro hcap
      have horiginal := containsCapSet_dual_iff.mp hcap
      exact hnoCup (by simpa [Finset.union_comm] using horiginal)
    · intro hcup
      have horiginal := containsCupSet_dual_iff.mp hcup
      exact hnoCap (by simpa [Finset.union_comm] using horiginal)
    · intro hstrong
      have horiginal := containsStrongPolygonSet_dual_iff.mp hstrong
      exact hnoStrong (by simpa [Finset.union_comm] using horiginal)

/-- A two-side bound at the color-dual parameters closes the original upper
singleton tail. -/
theorem singletonUpperPascalTailGate_of_dual_twoSideBound
    {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hbound : PascalTailTwoSideBound u a k) :
    SingletonUpperPascalTailGate a u k := by
  exact (singletonUpperPascalTailGate_iff_lower_dual ha hu hak huk).2
    (singletonLowerPascalTailGate_of_twoSideBound hu hbound)

/-- One parameter-uniform ordered two-side theorem, used in both color
orientations, is sufficient for every active critical root.  This is the
geometric all-parameter consumer of the Pascal arithmetic reduction. -/
theorem criticalRootImpossible_of_predecessors_pascal_twoSide_bounds
    {a u k : ℕ}
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hactive : k + 4 ≤ a + u)
    (hpredecessors : ∀ a' u', a' + u' < a + u →
      DecomposableStateUpper a' u' k)
    (hlowerBound : a < k → PascalTailTwoSideBound a u k)
    (hupperBound : u < k → PascalTailTwoSideBound u a k) :
    DecomposableCriticalRootImpossible a u k := by
  apply criticalRootImpossible_of_predecessors_interior_pascal_tail_gates
    ha hu hak huk hactive hpredecessors
  · intro haLt
    exact lowerPascalTailCriticalGate_of_singleton ha hu hak hactive
      (singletonLowerPascalTailGate_of_twoSideBound (by omega)
        (hlowerBound haLt))
  · intro huLt
    exact upperPascalTailCriticalGate_of_singleton ha hu hak huk hactive
      (singletonUpperPascalTailGate_of_dual_twoSideBound
        (by omega) (by omega) hak huk (hupperBound huLt))

theorem lowerPascalTailReservoir_455 :
    lowerPascalTailReservoir 4 5 5 = 7 := by
  norm_num [lowerPascalTailReservoir, decomposableThreshold,
    decomposableBinomialWindow, Nat.choose, Finset.sum_Icc_succ_top]

theorem lowerPascalTailReservoir_466 :
    lowerPascalTailReservoir 4 6 6 = 9 := by
  norm_num [lowerPascalTailReservoir, decomposableThreshold,
    decomposableBinomialWindow, Nat.choose, Finset.sum_Icc_succ_top]

theorem lowerPascalTailReservoir_488 :
    lowerPascalTailReservoir 4 8 8 = 13 := by
  norm_num [lowerPascalTailReservoir, decomposableThreshold,
    decomposableBinomialWindow, Nat.choose, Finset.sum_Icc_succ_top]

theorem lowerPascalTailReservoir_567 :
    lowerPascalTailReservoir 5 6 7 = 22 := by
  norm_num [lowerPascalTailReservoir, decomposableThreshold,
    decomposableBinomialWindow, Nat.choose, Finset.sum_Icc_succ_top]

theorem upperPascalTailReservoir_567 :
    upperPascalTailReservoir 5 6 7 = 25 := by
  norm_num [upperPascalTailReservoir, decomposableThreshold,
    decomposableBinomialWindow, Nat.choose, Finset.sum_Icc_succ_top]

/-- The previously isolated `(5,6,7)` two-cap-free-sides theorem is exactly
the first open instance of the uniform two-side Pascal consumer. -/
theorem pascalTailTwoSideBound_567_iff :
    PascalTailTwoSideBound 5 6 7 ↔ TwoCapFreeSidesBound567 := by
  constructor
  · intro h n χ left right hdisjoint horder hleftCap hrightCap hone
      hnoCap hnoCup hnoStrong
    have hcard := h hdisjoint horder hleftCap hrightCap hone
      hnoCap hnoCup hnoStrong
    rw [lowerPascalTailReservoir_567] at hcard
    omega
  · intro h n χ left right hdisjoint horder hleftCap hrightCap hone
      hnoCap hnoCup hnoStrong
    have hcard := h hdisjoint horder hleftCap hrightCap hone
      hnoCap hnoCup hnoStrong
    rw [lowerPascalTailReservoir_567]
    omega

/-- The first width-one tail gate is the certificate-free seven-vertex
singleton-root bound. -/
theorem singletonLowerPascalTailGate_455 :
    SingletonLowerPascalTailGate 4 5 5 := by
  intro n χ q upper hupper hdeep hcard hnoCap hnoCup hnoStrong
  rw [lowerPascalTailReservoir_455] at hcard
  have hbound := hdeep.singleton_root_card_le_seven
    hupper hnoCap hnoCup hnoStrong
  have hunionCard : ({q} ∪ upper).card = 8 := by
    rw [Finset.card_union_of_disjoint hdeep.disjoint]
    simp [hcard]
  omega

/-- The first nonsingleton tail gate follows from the structural open-root
large-child bound, not from the finite state-466 certificate. -/
theorem singletonLowerPascalTailGate_466 :
    SingletonLowerPascalTailGate 4 6 6 := by
  intro n χ q upper hupper hdeep hcard hnoCap hnoCup hnoStrong
  rw [lowerPascalTailReservoir_466] at hcard
  have hbound := upper_card_le_eight_of_nonempty_lower_open_466
    hupper hdeep (by simp) hnoCap hnoCup hnoStrong
  omega

/-- The wider state-488 tail gate is consumed by the symbolic `6+7` cup-block
bound. -/
theorem singletonLowerPascalTailGate_488 :
    SingletonLowerPascalTailGate 4 8 8 := by
  intro n χ q upper hupper hdeep hcard hnoCap hnoCup hnoStrong
  rw [lowerPascalTailReservoir_488] at hcard
  have hbound := upper_card_le_twelve_at_open_488
    (by simp) hupper hdeep hnoCap hnoCup hnoStrong
  omega

/-- The first still-open two-sided Pascal state is already connected exactly
to the repository's earlier two-cap-free-sides obstruction: that local bound
would close its 22-vertex lower-tail reservoir. -/
theorem singletonLowerPascalTailGate_567_of_twoCapFreeSides
    (hbound : TwoCapFreeSidesBound567) :
    SingletonLowerPascalTailGate 5 6 7 := by
  intro n χ q upper hupper hdeep hcard hnoCap hnoCup hnoStrong
  rw [lowerPascalTailReservoir_567] at hcard
  have hlargeChildBound :=
    upper_card_le_twenty_one_of_twoCapFreeSides_open_567
      hbound hupper hdeep (by simp) hnoCap hnoCup hnoStrong
  omega

theorem lowerPascalTailCriticalGate_567_of_twoCapFreeSides
    (hbound : TwoCapFreeSidesBound567) :
    LowerPascalTailCriticalGate 5 6 7 := by
  exact lowerPascalTailCriticalGate_of_singleton
    (a := 5) (u := 6) (k := 7)
    (by omega) (by omega) (by omega) (by omega)
    (singletonLowerPascalTailGate_567_of_twoCapFreeSides hbound)

/-- Color-dual positive controls for the three established lower gates. -/
theorem singletonUpperPascalTailGate_545 :
    SingletonUpperPascalTailGate 5 4 5 :=
  (singletonUpperPascalTailGate_iff_lower_dual
    (a := 5) (u := 4) (k := 5) (by omega) (by omega) (by omega) (by omega)).2
      singletonLowerPascalTailGate_455

theorem singletonUpperPascalTailGate_646 :
    SingletonUpperPascalTailGate 6 4 6 :=
  (singletonUpperPascalTailGate_iff_lower_dual
    (a := 6) (u := 4) (k := 6) (by omega) (by omega) (by omega) (by omega)).2
      singletonLowerPascalTailGate_466

theorem singletonUpperPascalTailGate_848 :
    SingletonUpperPascalTailGate 8 4 8 :=
  (singletonUpperPascalTailGate_iff_lower_dual
    (a := 8) (u := 4) (k := 8) (by omega) (by omega) (by omega) (by omega)).2
      singletonLowerPascalTailGate_488

end ErdosSzekeres

end
