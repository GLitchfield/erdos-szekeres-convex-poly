module

public import ErdosSzekeres.StructuralChargingCapExtremaReserve

@[expose] public section

/-!
# The proposed ordered `6+7` cup-block gate

The central-cut theorem reduces the open `(4,8,8)`, `10+13` boundary to two
ordered upper cup blocks of sizes six and seven.  This file freezes the exact
local theorem and proves its application shell.  The local theorem itself is
not proved here.
-/

namespace ErdosSzekeres

/-- Exact local replacement target selected by the central-cut obstruction. -/
def CupBlocks67Force488 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    Disjoint left right →
      (∀ x ∈ left, ∀ y ∈ right, x < y) →
        ((left.card = 6 ∧ right.card = 7) ∨
          (left.card = 7 ∧ right.card = 6)) →
          IsCupSet χ left → IsCupSet χ right →
            OneChangeOn χ (left ∪ right) →
              ContainsCapSet χ (left ∪ right) 4 ∨
                ContainsCupSet χ (left ∪ right) 8 ∨
                  ContainsStrongPolygonSet χ (left ∪ right) 8

/-- The two strict gap sides around an external point partition the support. -/
theorem gap_side_union_eq
    {n : ℕ} {support : Finset (Fin n)} {q : Fin n}
    (hq : q ∉ support) :
    support.filter (· < q) ∪ support.filter (q < ·) = support := by
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

/-- The two strict gap sides are disjoint. -/
theorem gap_sides_disjoint
    {n : ℕ} (support : Finset (Fin n)) (q : Fin n) :
    Disjoint (support.filter (· < q)) (support.filter (q < ·)) := by
  rw [Finset.disjoint_left]
  intro x hxLeft hxRight
  have hxlt := (Finset.mem_filter.mp hxLeft).2
  have hxgt := (Finset.mem_filter.mp hxRight).2
  omega

/-- Every left gap-side vertex precedes every right gap-side vertex. -/
theorem gap_sides_ordered
    {n : ℕ} (support : Finset (Fin n)) (q : Fin n) :
    ∀ x ∈ support.filter (· < q),
      ∀ y ∈ support.filter (q < ·), x < y := by
  intro x hx y hy
  exact (Finset.mem_filter.mp hx).2.trans
    (Finset.mem_filter.mp hy).2

/-- If the ordered `6+7` cup-block gate holds, an open four-cap/eight-cup
root with a nonempty lower child has at most twelve upper vertices. -/
theorem upper_card_le_twelve_of_cupBlocks67
    (hblocks : CupBlocks67Force488)
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty)
    (hupper : IsDecomposableOn χ upper)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 8)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 8) :
    upper.card ≤ 12 := by
  by_contra hnot
  have hthirteen : 13 ≤ upper.card := by omega
  obtain ⟨upper', hupperSub, hupperCard⟩ :=
    Finset.exists_subset_card_eq hthirteen
  have hupperNonempty : upper'.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hupperDecomposable : IsDecomposableOn χ upper' :=
    hupper.subset hupperSub hupperNonempty
  have hdeep' : HasDeepBelowSplit χ lower upper' :=
    hdeep.mono Finset.Subset.rfl hupperSub
  have hparentSub : lower ∪ upper' ⊆ lower ∪ upper :=
    Finset.union_subset_union Finset.Subset.rfl hupperSub
  have hnoCap' : ¬ContainsCapSet χ (lower ∪ upper') 4 :=
    fun hcap ↦ hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hparentSub)
  have hnoCup' : ¬ContainsCupSet χ (lower ∪ upper') 8 :=
    fun hcup ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hparentSub)
  obtain ⟨q, hqLower⟩ := hlower
  have hqUpper : q ∉ upper' := by
    intro hq
    exact (Finset.disjoint_left.mp hdeep'.disjoint) hqLower hq
  let left := upper'.filter (· < q)
  let right := upper'.filter (q < ·)
  have hnoEndpoint :
      ¬∃ cap : Finset (Fin n), cap ⊆ upper' ∧ cap.card = 3 ∧
        IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q := by
    rintro ⟨cap, hcapSub, hcapCard, hcapSet, hendpoint⟩
    apply hnoCap'
    simpa using hdeep'.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcapSet hqLower hendpoint
  have hcups : IsCupSet χ left ∧ IsCupSet χ right :=
    gap_sides_are_cups_of_no_endpoint_cap_three hnoEndpoint
  have hcards : (left.card = 6 ∧ right.card = 7) ∨
      (left.card = 7 ∧ right.card = 6) := by
    exact gap_cup_blocks_six_seven hqUpper hupperCard
      (show upper' ⊆ lower ∪ upper' from Finset.subset_union_right)
      hnoCup' hcups
  have hunion : left ∪ right = upper' :=
    gap_side_union_eq hqUpper
  have hone : OneChangeOn χ (left ∪ right) := by
    rw [hunion]
    intro i j k l hij hjk hkl hi hj hk hl
    exact hupperDecomposable.turnSequenceAllowed
      hij hjk hkl hi hj hk hl
  rcases hblocks (gap_sides_disjoint upper' q)
      (gap_sides_ordered upper' q) hcards hcups.1 hcups.2 hone with
      hcap | hcup | hstrong
  · rw [hunion] at hcap
    exact hnoCap' (FinsetPolygon.ContainsCapSet.mono hcap
      Finset.subset_union_right)
  · rw [hunion] at hcup
    exact hnoCup' (FinsetPolygon.ContainsCupSet.mono hcup
      Finset.subset_union_right)
  · apply hnoStrong
    rw [hunion] at hstrong
    exact FinsetPolygon.ContainsStrongPolygonSet.mono
      hstrong (hupperSub.trans Finset.subset_union_right)

end ErdosSzekeres

end
