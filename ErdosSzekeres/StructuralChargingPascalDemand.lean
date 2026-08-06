module

public import ErdosSzekeres.StructuralChargingSaturatedResource

@[expose] public section

/-!
# Pascal demand carried by an exact span rank

The published decomposable-set induction bounds the jump from a child index
to its successor by one adjacent coefficient in row `k - 2` of Pascal's
triangle.  This file names that coefficient and proves the two uniform jump
bounds.  It is arithmetic infrastructure for a structural allocation; it does
not claim that the demanded coefficient has already been injected into an
actual retained vertex set.
-/

namespace ErdosSzekeres

/-- The adjacent Pascal coefficient demanded when an exact cup or cap span has
published rank `rank`. -/
def publishedSpanPascalDemand (k rank : ℕ) : ℕ :=
  Nat.choose (k - 2) (rank - 1)

/-- Every in-range positive span rank carries a positive Pascal demand. -/
theorem publishedSpanPascalDemand_pos {k rank : ℕ}
    (hrank : 1 ≤ rank) (hrankTop : rank < k) :
    0 < publishedSpanPascalDemand k rank := by
  unfold publishedSpanPascalDemand
  exact Nat.choose_pos (by omega)

/-- Raising the cup-side published child index by one costs no more than its
adjacent Pascal demand. -/
theorem decomposableThreshold_succ_right_le_add_spanPascalDemand
    {a rank k : ℕ} (ha : 2 ≤ a) (hrank : 1 ≤ rank)
    (haTop : a ≤ k) (hrankTop : rank < k) :
    decomposableThreshold a (rank + 1) k ≤
      decomposableThreshold a rank k + publishedSpanPascalDemand k rank := by
  by_cases hrankOne : rank = 1
  · subst rank
    rw [decomposableThreshold_eq_choose ha (by omega) (by omega)]
    simp [publishedSpanPascalDemand]
  · have hrankTwo : 2 ≤ rank := by omega
    by_cases haTwo : a = 2
    · subst a
      rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
      rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
      simp
    · have haThree : 3 ≤ a := by omega
      by_cases hnextBase : a + (rank + 1) ≤ k + 3
      · rw [decomposableThreshold_eq_choose ha (by omega) hnextBase]
        rw [decomposableThreshold_eq_choose ha (by omega) (by omega)]
        have hrow :
            a + (rank + 1) - 4 = (a + rank - 4) + 1 := by omega
        have hcolumn : a - 2 = (a - 3) + 1 := by omega
        rw [hrow, hcolumn, Nat.choose_succ_succ]
        have hsum : a + rank - 4 = (a - 3) + (rank - 1) := by omega
        have hincrement :
            Nat.choose (a + rank - 4) (a - 3) =
              Nat.choose (a + rank - 4) (rank - 1) := by
          exact Nat.choose_symm_of_eq_add hsum
        rw [hincrement]
        have hrow_le : a + rank - 4 ≤ k - 2 := by omega
        have hmono := Nat.choose_le_choose (rank - 1) hrow_le
        unfold publishedSpanPascalDemand
        simpa [Nat.succ_eq_add_one, Nat.add_comm] using
          Nat.add_le_add_right hmono (Nat.choose (a + rank - 4) (a - 3 + 1))
      · have hnextActive : k + 4 ≤ a + (rank + 1) := by omega
        by_cases hcurrentBase : a + rank ≤ k + 3
        · have hboundary : a + rank = k + 3 := by omega
          rw [decomposableThreshold_eq_window ha (by omega) hnextActive]
          rw [decomposableThreshold_eq_choose ha (by omega) hcurrentBase]
          unfold decomposableBinomialWindow
          have hrankThree : 3 ≤ rank := by omega
          have hlow : k - a = rank - 3 := by omega
          have htop : rank + 1 - 2 = (rank - 2) + 1 := by omega
          rw [hlow, htop, Finset.sum_Icc_succ_top (by omega)]
          have hmid : rank - 2 = (rank - 3) + 1 := by omega
          rw [hmid, Finset.sum_Icc_succ_top (by omega)]
          simp
          have hrow : a + rank - 4 = k - 1 := by omega
          rw [hrow]
          have hsum : k - 1 = (a - 2) + (rank - 2) := by omega
          rw [Nat.choose_symm_of_eq_add hsum]
          have hkrow : k - 1 = (k - 2) + 1 := by omega
          have hrcol : rank - 2 = (rank - 3) + 1 := by omega
          rw [hkrow, hrcol, Nat.choose_succ_succ]
          unfold publishedSpanPascalDemand
          simp only [Nat.succ_eq_add_one]
          have hdem : rank - 3 + 1 + 1 = rank - 1 := by omega
          rw [hdem]
        · have hcurrentActive : k + 4 ≤ a + rank := by omega
          rw [decomposableThreshold_eq_window ha (by omega) hnextActive]
          rw [decomposableThreshold_eq_window ha (by omega) hcurrentActive]
          unfold decomposableBinomialWindow
          have htop : rank + 1 - 2 = (rank - 2) + 1 := by omega
          rw [htop, Finset.sum_Icc_succ_top (by omega)]
          unfold publishedSpanPascalDemand
          have hdem : rank - 2 + 1 = rank - 1 := by omega
          rw [hdem]

/-- Color-dual threshold jump for increasing the cap-side published child
index. -/
theorem decomposableThreshold_succ_left_le_add_spanPascalDemand
    {rank u k : ℕ} (hu : 2 ≤ u) (hrank : 1 ≤ rank)
    (huTop : u ≤ k) (hrankTop : rank < k) :
    decomposableThreshold (rank + 1) u k ≤
      decomposableThreshold rank u k + publishedSpanPascalDemand k rank := by
  by_cases hrankOne : rank = 1
  · subst rank
    rw [decomposableThreshold_eq_choose (by omega) hu (by omega)]
    simp [publishedSpanPascalDemand]
  · have hrankTwo : 2 ≤ rank := by omega
    by_cases huTwo : u = 2
    · subst u
      rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
      rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
      simp
    · have huThree : 3 ≤ u := by omega
      by_cases hnextBase : (rank + 1) + u ≤ k + 3
      · rw [decomposableThreshold_eq_choose (by omega) hu hnextBase]
        rw [decomposableThreshold_eq_choose (by omega) hu (by omega)]
        have hrow :
            (rank + 1) + u - 4 = (rank + u - 4) + 1 := by omega
        have hcolumn : rank + 1 - 2 = (rank - 2) + 1 := by omega
        rw [hrow, hcolumn, Nat.choose_succ_succ]
        simp only [Nat.succ_eq_add_one]
        have hindex : rank - 2 + 1 = rank - 1 := by omega
        rw [hindex]
        have hrow_le : rank + u - 4 ≤ k - 2 := by omega
        have hmono := Nat.choose_le_choose (rank - 1) hrow_le
        unfold publishedSpanPascalDemand
        exact Nat.add_le_add_left hmono _
      · have hnextActive : k + 4 ≤ (rank + 1) + u := by omega
        by_cases hcurrentBase : rank + u ≤ k + 3
        · have hboundary : rank + u = k + 3 := by omega
          rw [decomposableThreshold_eq_window (by omega) hu hnextActive]
          rw [decomposableThreshold_eq_choose (by omega) hu hcurrentBase]
          unfold decomposableBinomialWindow
          have huFour : 4 ≤ u := by omega
          have hlow : k - (rank + 1) = u - 4 := by omega
          have htop : u - 2 = (u - 3) + 1 := by omega
          rw [hlow, htop, Finset.sum_Icc_succ_top (by omega)]
          have hmid : u - 3 = (u - 4) + 1 := by omega
          rw [hmid, Finset.sum_Icc_succ_top (by omega)]
          simp
          have hrow : rank + u - 4 = k - 1 := by omega
          rw [hrow]
          have hsum : k - 1 = (rank - 2) + (u - 2) := by omega
          rw [Nat.choose_symm_of_eq_add hsum]
          have hkrow : k - 1 = (k - 2) + 1 := by omega
          have hucol : u - 2 = (u - 3) + 1 := by omega
          rw [hkrow, hucol, Nat.choose_succ_succ]
          unfold publishedSpanPascalDemand
          have hdemsum : k - 2 = (rank - 1) + (u - 4) := by omega
          rw [Nat.choose_symm_of_eq_add hdemsum]
          simp only [Nat.succ_eq_add_one]
          have hdem : u - 4 + 1 + 1 = u - 2 := by omega
          rw [hdem, ← hmid, ← htop]
          omega
        · have hcurrentActive : k + 4 ≤ rank + u := by omega
          rw [decomposableThreshold_eq_window (by omega) hu hnextActive]
          rw [decomposableThreshold_eq_window (by omega) hu hcurrentActive]
          unfold decomposableBinomialWindow
          have hlowSucc : k - (rank + 1) + 1 = k - rank := by omega
          have hset :
              Finset.Icc (k - (rank + 1)) (u - 2) =
                insert (k - (rank + 1)) (Finset.Icc (k - rank) (u - 2)) := by
            ext j
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          rw [hset, Finset.sum_insert]
          · unfold publishedSpanPascalDemand
            have hindex : k - (rank + 1) = (k - 2) - (rank - 1) := by omega
            have hcoeff :
                Nat.choose (k - 2) (k - (rank + 1)) =
                  Nat.choose (k - 2) (rank - 1) := by
              rw [hindex, Nat.choose_symm (by omega)]
            rw [hcoeff]
            omega
          · simp
            omega

/-- The two next-child thresholds are bounded by their retained base
thresholds plus the two exact-rank Pascal demands. -/
theorem decomposableThreshold_succ_pair_le_add_spanPascalDemands
    {a u aRank uRank k : ℕ}
    (ha : 2 ≤ a) (hu : 2 ≤ u) (haRank : 1 ≤ aRank) (huRank : 1 ≤ uRank)
    (haTop : a ≤ k) (huTop : u ≤ k)
    (haRankTop : aRank < k) (huRankTop : uRank < k) :
    decomposableThreshold a (uRank + 1) k +
        decomposableThreshold (aRank + 1) u k ≤
      decomposableThreshold a uRank k + publishedSpanPascalDemand k uRank +
        (decomposableThreshold aRank u k + publishedSpanPascalDemand k aRank) := by
  simpa only [Nat.add_assoc] using Nat.add_le_add
    (decomposableThreshold_succ_right_le_add_spanPascalDemand
      ha huRank haTop huRankTop)
    (decomposableThreshold_succ_left_le_add_spanPascalDemand
      hu haRank huTop haRankTop)

/-- At the first non-singleton saturated boundary, ranks two and three demand
the adjacent coefficients four and six. -/
theorem first_saturated_boundary_spanPascalDemands :
    publishedSpanPascalDemand 6 2 = 4 ∧
      publishedSpanPascalDemand 6 3 = 6 := by
  norm_num [publishedSpanPascalDemand, Nat.choose]

/-- An ordered endpoint pair together with its unique lowest separating node
in a fixed explicit decomposition tree. -/
structure LowestSeparatedSpanAllocation {n : ℕ} (χ : TripleColoring n)
    {s : Finset (Fin n)} (tree : DecompositionTree χ s) (a b : Fin n) where
  path : List Bool
  node : DecompositionSplit χ
  allocated : DecompositionTree.IsLowestSeparatingPath {a, b} tree path
  lookup : tree.splitAtPath path = some node

namespace LowestSeparatedSpanAllocation

variable {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
  {tree : DecompositionTree χ s} {a b : Fin n}

/-- Distinct retained endpoints have exactly one lowest-node allocation
object in a fixed explicit decomposition tree. -/
theorem exists_unique (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ∃ allocation : LowestSeparatedSpanAllocation χ tree a b,
      ∀ other : LowestSeparatedSpanAllocation χ tree a b,
        allocation = other := by
  classical
  have hsub : ({a, b} : Finset (Fin n)) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hcard : 2 ≤ ({a, b} : Finset (Fin n)).card := by
    simp [hab]
  let path := tree.lowestSeparatingPath hsub hcard
  obtain ⟨node, hlookup, _, _, _⟩ :=
    tree.lowestSeparatingPath_spec hsub hcard
  have hallocated :
      DecompositionTree.IsLowestSeparatingPath {a, b} tree path := by
    exact tree.lowestSeparatingPath_isLowest hsub hcard
  refine ⟨⟨path, node, hallocated, hlookup⟩, ?_⟩
  rintro ⟨otherPath, otherNode, otherAllocated, otherLookup⟩
  have hpath : path = otherPath :=
    hallocated.unique otherAllocated hsub hcard
  subst otherPath
  have hnode : node = otherNode :=
    Option.some.inj (hlookup.symm.trans otherLookup)
  subst otherNode
  rfl

/-- At the allocated node, the two span endpoints lie in opposite children. -/
theorem opposite_children
    (allocation : LowestSeparatedSpanAllocation χ tree a b) :
    (a ∈ allocation.node.lower ∧ b ∈ allocation.node.upper) ∨
      (a ∈ allocation.node.upper ∧ b ∈ allocation.node.lower) := by
  rcases allocation.allocated.splitAtPath_spec allocation.lookup with
    ⟨hsub, hnotLower, hnotUpper⟩
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Finset.mem_union] at hsub hnotLower hnotUpper
  aesop

end LowestSeparatedSpanAllocation

end ErdosSzekeres

end
