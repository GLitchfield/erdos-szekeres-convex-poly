module

public import ErdosSzekeres.StructuralChargingTreeAllocation
public import ErdosSzekeres.PublishedInductionSemantics
public import ErdosSzekeres.Duality
public import ErdosSzekeres.StructuralChargingCapFreeSides

@[expose] public section

/-!
# Sourced covering-cap resources at saturated boundaries

This file connects the first saturated-boundary cap to an actual retained
published core and a stable address in an explicit decomposition tree.  It
does not define consumption or claim a Pascal bound; those are the remaining
falsification targets.
-/

namespace ErdosSzekeres

/-- A covering cap whose identity is owned by an actual color-dual published
child slice and allocated to its unique lowest separating node in a fixed
explicit decomposition tree. -/
structure PublishedCoveringCapResource {n : ℕ} (χ : TripleColoring n)
    {a u k : ℕ} (opposite child : Finset (Fin n))
    (tree : DecompositionTree χ child) where
  slice : PublishedCapChildSlice a u k child
  index_two : 2 ≤ slice.index
  cap : Finset (Fin n)
  cap_mem : cap ∈ capWitnesses χ child slice.index
  cap_in_core : cap ⊆ slice.core
  covers_opposite : ∀ q ∈ opposite,
    (finsetSweepInterval cap (by
      have hcard := (mem_capWitnesses.mp cap_mem).2.1
      exact Finset.card_pos.mp (by omega))).StraddlesCut q.val
  path : List Bool
  node : DecompositionSplit χ
  allocated : DecompositionTree.IsLowestSeparatingPath cap tree path
  lookup : tree.splitAtPath path = some node

namespace PublishedCoveringCapResource

variable {n : ℕ} {χ : TripleColoring n} {a u k : ℕ}
  {opposite child : Finset (Fin n)} {tree : DecompositionTree χ child}

/-- The cap resource is a concrete part of the retained published
contribution, not an external counting token. -/
theorem cap_subset_core
    (resource : PublishedCoveringCapResource χ (a := a) (u := u) (k := k)
      opposite child tree) :
    resource.cap ⊆ resource.slice.core :=
  resource.cap_in_core

/-- Resolving the stored address exposes the split across which the same cap
witness is separated. -/
theorem separated_at_node
    (resource : PublishedCoveringCapResource χ (a := a) (u := u) (k := k)
      opposite child tree) :
    resource.cap ⊆ resource.node.lower ∪ resource.node.upper ∧
      ¬resource.cap ⊆ resource.node.lower ∧
      ¬resource.cap ⊆ resource.node.upper := by
  exact resource.allocated.splitAtPath_spec resource.lookup

/-- Stable cap identity prevents the same witness from being allocated to two
different addresses in the same explicit tree. This is address nonreuse for
the cap itself; it does not yet prevent distinct caps from charging the same
retained vertex. -/
theorem same_cap_same_path
    (first second : PublishedCoveringCapResource χ
      (a := a) (u := u) (k := k) opposite child tree)
    (hcap : first.cap = second.cap) : first.path = second.path := by
  have hsecondAllocated :
      DecompositionTree.IsLowestSeparatingPath first.cap tree second.path := by
    simpa [hcap] using second.allocated
  have hsub : first.cap ⊆ child := (mem_capWitnesses.mp first.cap_mem).1
  have hcard : 2 ≤ first.cap.card := by
    have hcapCard := (mem_capWitnesses.mp first.cap_mem).2.1
    rw [hcapCard]
    exact first.index_two
  exact first.allocated.unique hsecondAllocated hsub hcard

end PublishedCoveringCapResource

/-- Ordered witnesses assigned to one separating address can use only endpoint
ports lying in their common retained core. Thus the local multiplicity-two
bound charges actual retained vertices rather than the whole node support. -/
theorem allocated_ordered_sets_count_le_twice_core_lower
    {m n : ℕ} {χ : TripleColoring n} {s core : Finset (Fin n)}
    {tree : DecompositionTree χ s} {path : List Bool}
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node)
    (sets : Fin m → Finset (Fin n))
    (hcore : ∀ i, sets i ⊆ core)
    (hallocated : ∀ i,
      DecompositionTree.IsLowestSeparatingPath (sets i) tree path)
    (hcard : ∀ i, 2 ≤ (sets i).card)
    (hordered : ∀ {i j}, i < j → FinsetWeaklyBefore (sets i) (sets j)) :
    m ≤ 2 * (core ∩ node.lower).card := by
  classical
  have hseparated (i : Fin m) := (hallocated i).splitAtPath_spec hlookup
  have hcrossCoreLower (i : Fin m) :
      (sets i ∩ (core ∩ node.lower)).Nonempty := by
    have hnotUpper := (hseparated i).2.2
    rw [Finset.not_subset] at hnotUpper
    obtain ⟨q, hqSet, hqNotUpper⟩ := hnotUpper
    have hqParts := Finset.mem_union.mp ((hseparated i).1 hqSet)
    have hqLower := hqParts.resolve_right hqNotUpper
    exact ⟨q, Finset.mem_inter.mpr
      ⟨hqSet, Finset.mem_inter.mpr ⟨hcore i hqSet, hqLower⟩⟩⟩
  calc
    m = ∑ _i : Fin m, 1 := by simp
    _ ≤ ∑ i, (sets i ∩ (core ∩ node.lower)).card := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.card_pos.mpr (hcrossCoreLower i)
    _ = ∑ q ∈ core ∩ node.lower,
        (Finset.univ.filter fun i ↦ q ∈ sets i).card := by
      calc
        (∑ i, (sets i ∩ (core ∩ node.lower)).card) =
            ∑ i, ∑ q ∈ core ∩ node.lower, if q ∈ sets i then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.card_filter]
          congr 1
          ext q
          simp [and_comm]
        _ = ∑ q ∈ core ∩ node.lower,
            ∑ i, if q ∈ sets i then 1 else 0 := Finset.sum_comm
        _ = ∑ q ∈ core ∩ node.lower,
            (Finset.univ.filter fun i ↦ q ∈ sets i).card := by
          apply Finset.sum_congr rfl
          intro q _
          exact (Finset.card_filter (fun i ↦ q ∈ sets i) Finset.univ).symm
    _ ≤ ∑ _q ∈ core ∩ node.lower, 2 := by
      apply Finset.sum_le_sum
      intro q _
      exact ordered_family_vertex_capacity_two sets hcard hordered q
    _ = 2 * (core ∩ node.lower).card := by simp [Nat.mul_comm]

/-- In the three/nine child split at the first saturated boundary, openness
forces the three-vertex lower child to be a cap. If it were a cup, its union
with the sourced upper three-cap would already be a strong six-set. -/
theorem lower_three_contains_cap_three_of_upper_cap_three_and_no_strong_six
    {n : ℕ} {χ : TripleColoring n} {lower upper cap : Finset (Fin n)}
    (hχ : IsSweepRealizable χ) (hsplit : HasDeepBelowSplit χ lower upper)
    (hlowerCard : lower.card = 3)
    (hcap : cap ∈ capWitnesses χ upper 3)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 6) :
    ContainsCapSet χ lower 3 := by
  have hcard : Nat.choose (3 + 3 - 4) (3 - 2) < lower.card := by
    norm_num [hlowerCard]
  rcases containsCapSet_or_containsCupSet_of_choose_lt hχ lower
      (a := 3) (u := 3) (by omega) (by omega) hcard with hcapLower | hcupLower
  · exact hcapLower
  · obtain ⟨cup, hcupSub, hcupCard, hcupSet⟩ := hcupLower
    have hcapData := mem_capWitnesses.mp hcap
    exact (hnoStrong (hsplit.containsStrongPolygonSet_of_cup_cap
      hcupSub hcapData.1 hcupSet hcapData.2.2 (by
        rw [hcupCard, hcapData.2.1]))).elim

/-- In the two/ten child split, any upper three-cap and the whole lower child
already form a strong five-set. The remaining difficulty is precisely whether
that strong five-set can be extended or charged without reuse. -/
theorem lower_two_union_upper_cap_three_contains_strong_five
    {n : ℕ} {χ : TripleColoring n} {lower upper cap : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper) (hlowerCard : lower.card = 2)
    (hcap : cap ∈ capWitnesses χ upper 3) :
    ContainsStrongPolygonSet χ (lower ∪ upper) 5 := by
  have hlowerCup : IsCupSet χ lower := by
    intro triple hi hj hk
    exfalso
    have hsub : ({triple.i, triple.j, triple.k} : Finset (Fin n)) ⊆ lower := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hi, hj, hk⟩
    have hcardLe := Finset.card_le_card hsub
    have hij : triple.i ≠ triple.j := ne_of_lt triple.hij
    have hik : triple.i ≠ triple.k := ne_of_lt (triple.hij.trans triple.hjk)
    have hjk : triple.j ≠ triple.k := ne_of_lt triple.hjk
    have hcardThree : ({triple.i, triple.j, triple.k} : Finset (Fin n)).card = 3 := by
      simp [hij, hik, hjk]
    omega
  have hcapData := mem_capWitnesses.mp hcap
  exact hsplit.containsStrongPolygonSet_of_cup_cap Finset.Subset.rfl
    hcapData.1 hlowerCup hcapData.2.2 (by
      rw [hlowerCard, hcapData.2.1])

/-- Uniform gap-side consequence of a forbidden parent cap. Around any lower
vertex, both upper gap sides avoid caps one size below the parent target. At
the first boundary `r = 3`, being three-cap-free says every triple is a cup,
which is why the gap sides become cup blocks. -/
theorem gap_sides_avoid_cap_of_no_parent_succ_cap
    {n r : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper) {q : Fin n} (hq : q ∈ lower)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) (r + 1)) :
    ¬ContainsCapSet χ (upper.filter (· < q)) r ∧
      ¬ContainsCapSet χ (upper.filter (q < ·)) r := by
  constructor
  · rintro ⟨cap, hcapSub, hcapCard, hcapSet⟩
    apply hnoCap
    apply hsplit.containsCapSet_succ_of_lower_endpoint
      (hcapSub.trans (Finset.filter_subset _ _)) hcapCard hcapSet hq
    exact Or.inr (fun x hx ↦ (Finset.mem_filter.mp (hcapSub hx)).2.le)
  · rintro ⟨cap, hcapSub, hcapCard, hcapSet⟩
    apply hnoCap
    apply hsplit.containsCapSet_succ_of_lower_endpoint
      (hcapSub.trans (Finset.filter_subset _ _)) hcapCard hcapSet hq
    exact Or.inl (fun x hx ↦ (Finset.mem_filter.mp (hcapSub hx)).2.le)

/-- A cup subset of an ambient set avoiding a cup of size `u` has cardinality
strictly below `u`. -/
theorem card_lt_of_isCupSet_of_no_ambient_cup
    {n u : ℕ} {χ : TripleColoring n} {s ambient : Finset (Fin n)}
    (hsub : s ⊆ ambient) (hcup : IsCupSet χ s)
    (hnoCup : ¬ContainsCupSet χ ambient u) : s.card < u := by
  by_contra hnot
  have hu : u ≤ s.card := Nat.le_of_not_gt hnot
  obtain ⟨cup, hcupSub, hcupCard⟩ := Finset.exists_subset_card_eq hu
  apply hnoCup
  exact ⟨cup, hcupSub.trans hsub, hcupCard,
    FinsetPolygon.IsCupSet.mono hcup hcupSub⟩

/-- Uniform elementary closure of every saturated branch whose parent cap
parameter is four. Around a lower vertex the upper gap sides are cups, and a
forbidden parent `u`-cup makes each side smaller than `u`. -/
theorem upper_card_lt_twice_cup_parameter_of_nonempty_lower_open_four
    {n u : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) u) :
    upper.card < 2 * u := by
  classical
  obtain ⟨q, hqLower⟩ := hlower
  have hqNotUpper : q ∉ upper := by
    intro hqUpper
    exact (Finset.disjoint_left.mp hsplit.disjoint) hqLower hqUpper
  let left := upper.filter (· < q)
  let right := upper.filter (q < ·)
  have hnoEndpoint : ¬∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = 3 ∧
      IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q := by
    rintro ⟨cap, hcapSub, hcapCard, hcapSet, hendpoint⟩
    apply hnoCap
    simpa using hsplit.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcapSet hqLower hendpoint
  have hcups : IsCupSet χ left ∧ IsCupSet χ right :=
    gap_sides_are_cups_of_no_endpoint_cap_three hnoEndpoint
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
  have hleftSub : left ⊆ lower ∪ upper := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_filter.mp hx).1
  have hrightSub : right ⊆ lower ∪ upper := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_filter.mp hx).1
  have hleftCard : left.card < u :=
    card_lt_of_isCupSet_of_no_ambient_cup hleftSub hcups.1 hnoCup
  have hrightCard : right.card < u :=
    card_lt_of_isCupSet_of_no_ambient_cup hrightSub hcups.2 hnoCup
  have hcard : left.card + right.card = upper.card := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
  omega

/-- The first `k = 7` saturated state `(4,7,7,3,2)` is already excluded by
the uniform two-gap cup bound: its large child would have size fourteen or
fifteen, while every open parent forces it below fourteen. -/
theorem first_higher_saturated_boundary_477_32_child_cards_impossible
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hcards : (lower.card = 2 ∧ upper.card = 15) ∨
      (lower.card = 3 ∧ upper.card = 14))
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 7) : False := by
  have hupperBound :=
    upper_card_lt_twice_cup_parameter_of_nonempty_lower_open_four
      hsplit hlower hnoCap hnoCup
  rcases hcards with hcards | hcards <;> omega

/-- Color-dual form of the uniform elementary four-cup boundary. -/
theorem lower_card_lt_twice_cap_parameter_of_nonempty_upper_open_four
    {n a : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper) (hupper : upper.Nonempty)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) a)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 4) :
    lower.card < 2 * a := by
  have hnoCapDual : ¬ContainsCapSet χ.dual (upper ∪ lower) 4 := by
    intro hcap
    apply hnoCup
    have horiginal := containsCapSet_dual_iff.mp hcap
    simpa [Finset.union_comm] using horiginal
  have hnoCupDual : ¬ContainsCupSet χ.dual (upper ∪ lower) a := by
    intro hcup
    apply hnoCap
    have horiginal := containsCupSet_dual_iff.mp hcup
    simpa [Finset.union_comm] using horiginal
  exact upper_card_lt_twice_cup_parameter_of_nonempty_lower_open_four
    hsplit.dual hupper hnoCapDual hnoCupDual

/-- The color-dual `(7,4,7,2,3)` child pairs are impossible by the same
certificate-free bound. -/
theorem first_higher_saturated_boundary_747_23_child_cards_impossible
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper) (hupper : upper.Nonempty)
    (hcards : (lower.card = 14 ∧ upper.card = 3) ∨
      (lower.card = 15 ∧ upper.card = 2))
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 7)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 4) : False := by
  have hlowerBound :=
    lower_card_lt_twice_cap_parameter_of_nonempty_upper_open_four
      hsplit hupper hnoCap hnoCup
  rcases hcards with hcards | hcards <;> omega

/-- Reusable bridge from a quantitative theorem about two ordered cup blocks
to an upper-child bound at any open four-cap boundary. -/
theorem upper_card_le_of_gap_cup_block_bound
    {n bound : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hbound : ∀ left right : Finset (Fin n),
      Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
        IsCupSet χ left → IsCupSet χ right → OneChangeOn χ (left ∪ right) →
        left ∪ right = upper → left.card + right.card ≤ bound) :
    upper.card ≤ bound := by
  classical
  obtain ⟨q, hqLower⟩ := hlower
  have hqNotUpper : q ∉ upper := by
    intro hqUpper
    exact (Finset.disjoint_left.mp hsplit.disjoint) hqLower hqUpper
  let left := upper.filter (· < q)
  let right := upper.filter (q < ·)
  have hnoEndpoint : ¬∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = 3 ∧
      IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q := by
    rintro ⟨cap, hcapSub, hcapCard, hcapSet, hendpoint⟩
    apply hnoCap
    simpa using hsplit.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcapSet hqLower hendpoint
  have hcups : IsCupSet χ left ∧ IsCupSet χ right :=
    gap_sides_are_cups_of_no_endpoint_cap_three hnoEndpoint
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
    intro i j k l hij hjk hkl hi hj hk hl
    exact hupper.turnSequenceAllowed hij hjk hkl
      (hunion ▸ hi) (hunion ▸ hj) (hunion ▸ hk) (hunion ▸ hl)
  have hblockBound :=
    hbound left right hdisjoint horder hcups.1 hcups.2 honeChange hunion
  have hcard : left.card + right.card = upper.card := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
  omega

/-- Sharpened elementary two-gap count. In a decomposable upper child, the two
cup sides each have at most `u-1` vertices. -/
theorem upper_card_le_twice_pred_cup_parameter_of_nonempty_lower_open_four
    {n u : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) u) :
    upper.card ≤ 2 * (u - 1) := by
  apply upper_card_le_of_gap_cup_block_bound hupper hsplit hlower hnoCap
  intro left right _hdisjoint _horder hleft hright _hone hunion
  have hsub : left ∪ right ⊆ lower ∪ upper := by
    rw [hunion]
    exact Finset.subset_union_right
  have hleftSub : left ⊆ lower ∪ upper :=
    Finset.Subset.trans Finset.subset_union_left hsub
  have hrightSub : right ⊆ lower ∪ upper :=
    Finset.Subset.trans Finset.subset_union_right hsub
  have hleftCard :=
    card_lt_of_isCupSet_of_no_ambient_cup hleftSub hleft hnoCup
  have hrightCard :=
    card_lt_of_isCupSet_of_no_ambient_cup hrightSub hright hnoCup
  omega

/-- The 13-vertex large-child alternative at `(4,7,7,3,3)` is already
impossible by the elementary two-gap count; only sizes eleven and twelve need
the proposed `5+6/6+5` coupled theorem. -/
theorem higher_saturated_boundary_477_33_thirteen_impossible
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hupperCard : upper.card = 13)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 7) : False := by
  have hupperBound :=
    upper_card_le_twice_pred_cup_parameter_of_nonempty_lower_open_four
      hupper hsplit hlower hnoCap hnoCup
  omega

/-- Conditional certificate-free closure of `(4,7,7,3,3)`. The only remaining
input is the explicit `5+6/6+5` cup-block contract. -/
theorem upper_card_le_ten_of_cupBlocks56_open_477
    (hblocks : CupBlocks56Force477)
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 7) :
    upper.card ≤ 10 := by
  apply upper_card_le_of_gap_cup_block_bound hupper hsplit hlower hnoCap
  intro left right hdisjoint horder hleft hright hone hunion
  apply cup_block_card_add_le_ten_of_cupBlocks56 hblocks hdisjoint horder
    hleft hright hone
  · intro hcap
    apply hnoCap
    exact FinsetPolygon.ContainsCapSet.mono hcap (by
      rw [hunion]
      exact Finset.subset_union_right)
  · intro hcup
    apply hnoCup
    exact FinsetPolygon.ContainsCupSet.mono hcup (by
      rw [hunion]
      exact Finset.subset_union_right)
  · intro hstrong
    apply hnoStrong
    exact FinsetPolygon.ContainsStrongPolygonSet.mono hstrong (by
      rw [hunion]
      exact Finset.subset_union_right)

/-- The proposed local cup-block theorem would eliminate every feasible child
pair at the next `(4,7,7,3,3)` boundary. -/
theorem higher_saturated_boundary_477_33_child_cards_impossible_of_cupBlocks56
    (hblocks : CupBlocks56Force477)
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hcards : (lower.card = 4 ∧ upper.card = 13) ∨
      (lower.card = 5 ∧ upper.card = 12) ∨
      (lower.card = 6 ∧ upper.card = 11))
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 7) : False := by
  have hupperBound := upper_card_le_ten_of_cupBlocks56_open_477
    hblocks hupper hsplit hlower hnoCap hnoCup hnoStrong
  rcases hcards with hcards | hcards | hcards <;> omega

/-- Certificate-free closure of the large-child bound at `(4,7,7,3,3)`. -/
theorem upper_card_le_ten_of_nonempty_lower_open_477
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 7) :
    upper.card ≤ 10 :=
  upper_card_le_ten_of_cupBlocks56_open_477 cupBlocks56Force477
    hupper hsplit hlower hnoCap hnoCup hnoStrong

/-- Every feasible child pair at `(4,7,7,3,3)` is impossible. -/
theorem higher_saturated_boundary_477_33_child_cards_impossible
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hcards : (lower.card = 4 ∧ upper.card = 13) ∨
      (lower.card = 5 ∧ upper.card = 12) ∨
      (lower.card = 6 ∧ upper.card = 11))
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 7) : False :=
  higher_saturated_boundary_477_33_child_cards_impossible_of_cupBlocks56
    cupBlocks56Force477 hupper hsplit hlower hcards hnoCap hnoCup hnoStrong

/-- Color-dual closure of the same boundary when the lower child is large. -/
theorem lower_card_le_ten_of_nonempty_upper_open_747
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hlower : IsDecomposableOn χ lower)
    (hsplit : HasDeepBelowSplit χ lower upper) (hupper : upper.Nonempty)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 7)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 4)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 7) :
    lower.card ≤ 10 := by
  have hnoCapDual : ¬ContainsCapSet χ.dual (upper ∪ lower) 4 := by
    intro hcap
    apply hnoCup
    have horiginal := containsCapSet_dual_iff.mp hcap
    simpa [Finset.union_comm] using horiginal
  have hnoCupDual : ¬ContainsCupSet χ.dual (upper ∪ lower) 7 := by
    intro hcup
    apply hnoCap
    have horiginal := containsCupSet_dual_iff.mp hcup
    simpa [Finset.union_comm] using horiginal
  have hnoStrongDual :
      ¬ContainsStrongPolygonSet χ.dual (upper ∪ lower) 7 := by
    intro hstrong
    apply hnoStrong
    have horiginal := containsStrongPolygonSet_dual_iff.mp hstrong
    simpa [Finset.union_comm] using horiginal
  exact upper_card_le_ten_of_nonempty_lower_open_477
    hlower.dual hsplit.dual hupper hnoCapDual hnoCupDual hnoStrongDual

/-- Every color-dual feasible child pair at `(7,4,7,3,3)` is impossible. -/
theorem higher_saturated_boundary_747_33_child_cards_impossible
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hlower : IsDecomposableOn χ lower)
    (hsplit : HasDeepBelowSplit χ lower upper) (hupper : upper.Nonempty)
    (hcards : (lower.card = 11 ∧ upper.card = 6) ∨
      (lower.card = 12 ∧ upper.card = 5) ∨
      (lower.card = 13 ∧ upper.card = 4))
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 7)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 4)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 7) : False := by
  have hlowerBound := lower_card_le_ten_of_nonempty_upper_open_747
    hlower hsplit hupper hnoCap hnoCup hnoStrong
  rcases hcards with hcards | hcards | hcards <;> omega

/-- The local two-side gate gives the exact upper-child bound needed at the
`(5,6,7,4,2)` saturated boundary. -/
theorem upper_card_le_twenty_one_of_twoCapFreeSides_open_567
    (hbound : TwoCapFreeSidesBound567)
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 7) :
    upper.card ≤ 21 := by
  classical
  obtain ⟨q, hqLower⟩ := hlower
  have hqNotUpper : q ∉ upper := by
    intro hqUpper
    exact (Finset.disjoint_left.mp hsplit.disjoint) hqLower hqUpper
  let left := upper.filter (· < q)
  let right := upper.filter (q < ·)
  have hsides : ¬ContainsCapSet χ left 4 ∧
      ¬ContainsCapSet χ right 4 := by
    simpa [left, right] using
      (gap_sides_avoid_cap_of_no_parent_succ_cap
        (r := 4) hsplit hqLower (by simpa using hnoCap))
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
    intro i j k l hij hjk hkl hi hj hk hl
    exact hupper.turnSequenceAllowed hij hjk hkl
      (hunion ▸ hi) (hunion ▸ hj) (hunion ▸ hk) (hunion ▸ hl)
  have hnoCapUpper : ¬ContainsCapSet χ upper 5 := by
    intro hcap
    exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap Finset.subset_union_right)
  have hnoCupUpper : ¬ContainsCupSet χ upper 6 := by
    intro hcup
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup Finset.subset_union_right)
  have hnoStrongUpper : ¬ContainsStrongPolygonSet χ upper 7 := by
    intro hstrong
    exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.subset_union_right)
  have hcardBound := hbound hdisjoint horder hsides.1 hsides.2 honeChange
    (by simpa [hunion] using hnoCapUpper)
    (by simpa [hunion] using hnoCupUpper)
    (by simpa [hunion] using hnoStrongUpper)
  have hcard : left.card + right.card = upper.card := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
  omega

/-- Conditional elimination of every feasible child pair at
`(5,6,7,4,2)`. -/
theorem higher_saturated_boundary_567_42_child_cards_impossible_of_twoCapFreeSides
    (hbound : TwoCapFreeSidesBound567)
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hcards : (lower.card = 2 ∧ upper.card = 24) ∨
      (lower.card = 3 ∧ upper.card = 23) ∨
      (lower.card = 4 ∧ upper.card = 22))
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 7) : False := by
  have hupperBound := upper_card_le_twenty_one_of_twoCapFreeSides_open_567
    hbound hupper hsplit hlower hnoCap hnoCup hnoStrong
  rcases hcards with hcards | hcards | hcards <;> omega

/-- Color-dual conditional large-child bound at `(6,5,7)`. -/
theorem lower_card_le_twenty_one_of_twoCapFreeSides_open_657
    (hbound : TwoCapFreeSidesBound567)
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hlower : IsDecomposableOn χ lower)
    (hsplit : HasDeepBelowSplit χ lower upper) (hupper : upper.Nonempty)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 6)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 7) :
    lower.card ≤ 21 := by
  have hnoCapDual : ¬ContainsCapSet χ.dual (upper ∪ lower) 5 := by
    intro hcap
    apply hnoCup
    have horiginal := containsCapSet_dual_iff.mp hcap
    simpa [Finset.union_comm] using horiginal
  have hnoCupDual : ¬ContainsCupSet χ.dual (upper ∪ lower) 6 := by
    intro hcup
    apply hnoCap
    have horiginal := containsCupSet_dual_iff.mp hcup
    simpa [Finset.union_comm] using horiginal
  have hnoStrongDual :
      ¬ContainsStrongPolygonSet χ.dual (upper ∪ lower) 7 := by
    intro hstrong
    apply hnoStrong
    have horiginal := containsStrongPolygonSet_dual_iff.mp hstrong
    simpa [Finset.union_comm] using horiginal
  exact upper_card_le_twenty_one_of_twoCapFreeSides_open_567
    hbound hlower.dual hsplit.dual hupper hnoCapDual hnoCupDual hnoStrongDual

/-- Conditional elimination of the color-dual feasible child pairs at
`(6,5,7,2,4)`. -/
theorem higher_saturated_boundary_657_24_child_cards_impossible_of_twoCapFreeSides
    (hbound : TwoCapFreeSidesBound567)
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hlower : IsDecomposableOn χ lower)
    (hsplit : HasDeepBelowSplit χ lower upper) (hupper : upper.Nonempty)
    (hcards : (lower.card = 22 ∧ upper.card = 4) ∨
      (lower.card = 23 ∧ upper.card = 3) ∨
      (lower.card = 24 ∧ upper.card = 2))
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 6)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 7) : False := by
  have hlowerBound := lower_card_le_twenty_one_of_twoCapFreeSides_open_657
    hbound hlower hsplit hupper hnoCap hnoCup hnoStrong
  rcases hcards with hcards | hcards | hcards <;> omega

/-- Certificate-free closure of the first saturated off-window gate.

Choose any lower-child vertex. If an upper three-cap had that vertex as a
sweep endpoint, it would extend to a parent four-cap. Hence both sides of the
vertex's upper-child gap are cups. The symbolic `4+5/5+4` cup-block theorem
then bounds the whole upper child by eight. -/
theorem upper_card_le_eight_of_nonempty_lower_open_466
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 6) :
    upper.card ≤ 8 := by
  classical
  obtain ⟨q, hqLower⟩ := hlower
  have hqNotUpper : q ∉ upper := by
    intro hqUpper
    exact (Finset.disjoint_left.mp hsplit.disjoint) hqLower hqUpper
  let left := upper.filter (· < q)
  let right := upper.filter (q < ·)
  have hnoEndpoint : ¬∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = 3 ∧
      IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q := by
    rintro ⟨cap, hcapSub, hcapCard, hcapSet, hendpoint⟩
    apply hnoCap
    simpa using hsplit.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcapSet hqLower hendpoint
  have hcups : IsCupSet χ left ∧ IsCupSet χ right :=
    gap_sides_are_cups_of_no_endpoint_cap_three hnoEndpoint
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
    intro i j k l hij hjk hkl hi hj hk hl
    exact hupper.turnSequenceAllowed hij hjk hkl
      (hunion ▸ hi) (hunion ▸ hj) (hunion ▸ hk) (hunion ▸ hl)
  have hnoCapUpper : ¬ContainsCapSet χ upper 4 := by
    intro hcap
    exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap Finset.subset_union_right)
  have hnoCupUpper : ¬ContainsCupSet χ upper 6 := by
    intro hcup
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup Finset.subset_union_right)
  have hnoStrongUpper : ¬ContainsStrongPolygonSet χ upper 6 := by
    intro hstrong
    exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.subset_union_right)
  have hbound := cup_block_card_add_le_eight hdisjoint horder hcups.1 hcups.2
    honeChange (by simpa [hunion] using hnoCapUpper)
    (by simpa [hunion] using hnoCupUpper)
    (by simpa [hunion] using hnoStrongUpper)
  have hcard : left.card + right.card = upper.card := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
  omega

/-- The two feasible child-cardinality pairs at `(4,6,6,3,2)` are therefore
impossible in an open parent. This is the first saturated transition gate and
uses neither `decomposableStateUpper_466` nor a finite certificate. -/
theorem first_saturated_boundary_child_cards_impossible
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hsplit : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty)
    (hcards : (lower.card = 2 ∧ upper.card = 10) ∨
      (lower.card = 3 ∧ upper.card = 9))
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 6) : False := by
  have hupperBound := upper_card_le_eight_of_nonempty_lower_open_466
    hupper hsplit hlower hnoCap hnoCup hnoStrong
  rcases hcards with hcards | hcards <;> omega

/-- Color-dual certificate-free closure of the first saturated gate.  Here the
lower child is the large child: avoiding a six-cap, a four-cup, and a strong
six-set bounds it by eight. -/
theorem lower_card_le_eight_of_nonempty_upper_open_646
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hlower : IsDecomposableOn χ lower)
    (hsplit : HasDeepBelowSplit χ lower upper) (hupper : upper.Nonempty)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 6)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 4)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 6) :
    lower.card ≤ 8 := by
  have hnoCapDual :
      ¬ContainsCapSet χ.dual (upper ∪ lower) 4 := by
    intro hcap
    apply hnoCup
    have horiginal := containsCapSet_dual_iff.mp hcap
    simpa [Finset.union_comm] using horiginal
  have hnoCupDual :
      ¬ContainsCupSet χ.dual (upper ∪ lower) 6 := by
    intro hcup
    apply hnoCap
    have horiginal := containsCupSet_dual_iff.mp hcup
    simpa [Finset.union_comm] using horiginal
  have hnoStrongDual :
      ¬ContainsStrongPolygonSet χ.dual (upper ∪ lower) 6 := by
    intro hstrong
    apply hnoStrong
    have horiginal := containsStrongPolygonSet_dual_iff.mp hstrong
    simpa [Finset.union_comm] using horiginal
  exact upper_card_le_eight_of_nonempty_lower_open_466
    hlower.dual hsplit.dual hupper hnoCapDual hnoCupDual hnoStrongDual

/-- The color-dual feasible child-cardinality pairs are impossible as well.
This theorem is derived solely through structural duality from the
certificate-free first-gate bound. -/
theorem first_saturated_boundary_dual_child_cards_impossible
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hlower : IsDecomposableOn χ lower)
    (hsplit : HasDeepBelowSplit χ lower upper) (hupper : upper.Nonempty)
    (hcards : (lower.card = 10 ∧ upper.card = 2) ∨
      (lower.card = 9 ∧ upper.card = 3))
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 6)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 4)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 6) : False := by
  have hlowerBound := lower_card_le_eight_of_nonempty_upper_open_646
    hlower hsplit hupper hnoCap hnoCup hnoStrong
  rcases hcards with hcards | hcards <;> omega

/-- At the first `(4,6,6,3,2)` saturated boundary, the covering upper
three-cap can be chosen inside the actual six-vertex retained core and given
its unique lowest separating-node address.  The hypotheses are the semantic
child-cardinality bounds, not the finite state-466 theorem. -/
theorem first_saturated_boundary_has_published_covering_cap_resource
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hχ : IsSweepRealizable χ) (hsplit : HasDeepBelowSplit χ lower upper)
    (upperTree : DecompositionTree χ upper)
    (hupperLarge : 5 < upper.card) (hupperBound : upper.card ≤ 11)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 6) :
    Nonempty (PublishedCoveringCapResource χ lower upper upperTree
      (a := 4) (u := 6) (k := 6)) := by
  classical
  obtain ⟨cap, hcovers⟩ :=
    first_saturated_boundary_has_covering_upper_three_cap hχ hsplit
      hupperLarge hnoCap hnoCup
  have hindex : publishedCapChildIndex 4 6 6 upper.card = 3 :=
    publishedCapChildIndex_eq_three_at_first_saturated_boundary
      (by omega) hupperBound
  have hseedCard : cap.1.card ≤
      decomposableThreshold (publishedCapChildIndex 4 6 6 upper.card) 6 6 + 1 := by
    have hcapCard := (mem_capWitnesses.mp cap.property).2.1
    rw [hindex]
    norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
      Finset.sum_Icc_succ_top]
    omega
  obtain ⟨slice, hcapCore⟩ :=
    exists_publishedCapChildSlice_core_superset (a := 4) (u := 6) (k := 6)
      (by omega) (by exact Finset.card_pos.mp (by omega))
      (mem_capWitnesses.mp cap.property).1 hseedCard
  have hsliceIndex : slice.index = 3 := by
    rw [slice.index_eq, hindex]
  have hcapMem : cap.1 ∈ capWitnesses χ upper slice.index := by
    rw [hsliceIndex]
    exact cap.property
  have hcapCardTwo : 2 ≤ cap.1.card := by
    have hcard := (mem_capWitnesses.mp hcapMem).2.1
    omega
  let path := upperTree.lowestSeparatingPath
    (mem_capWitnesses.mp hcapMem).1 hcapCardTwo
  obtain ⟨node, hlookup, _, _, _⟩ := upperTree.lowestSeparatingPath_spec
    (mem_capWitnesses.mp hcapMem).1 hcapCardTwo
  refine ⟨{
    slice := slice
    index_two := by omega
    cap := cap.1
    cap_mem := hcapMem
    cap_in_core := hcapCore
    covers_opposite := hcovers
    path := path
    node := node
    allocated := ?_
    lookup := ?_
  }⟩
  · exact upperTree.lowestSeparatingPath_isLowest
      (mem_capWitnesses.mp hcapMem).1 hcapCardTwo
  · exact hlookup

end ErdosSzekeres

end
