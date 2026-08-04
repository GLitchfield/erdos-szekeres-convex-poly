module

public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Witness-level structural charging

This file develops incompatibilities among actual cup and cap witnesses at a
deep-below root. It deliberately carries no quotient or profile state.
-/

namespace ErdosSzekeres

/-- The witness-level upper-child alternative selected by the structural
charging review. -/
def UpperChildGapTrichotomy455 {n : ℕ} (χ : TripleColoring n)
    (upper : Finset (Fin n)) (q : Fin n) : Prop :=
  ContainsCapSet χ upper 4 ∨ ContainsCupSet χ upper 5 ∨
    ContainsStrongPolygonSet χ upper 5 ∨
      ∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = 3 ∧
        IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q

/-- The open structural target: the gap trichotomy for seven decomposable
upper vertices at a singleton deep-below root. -/
def UpperChildGapTrichotomyAtSeven : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n},
    IsDecomposableOn χ upper → HasDeepBelowSplit χ {q} upper →
      upper.card = 7 → UpperChildGapTrichotomy455 χ upper q

/-- The rank-three one-change law restricted to one finite vertex set. -/
def OneChangeOn {n : ℕ} (χ : TripleColoring n) (s : Finset (Fin n)) : Prop :=
  ∀ {i j k l : Fin n}, (hij : i < j) → (hjk : j < k) → (hkl : k < l) →
    i ∈ s → j ∈ s → k ∈ s → l ∈ s →
      TurnSequenceAllowed
        (χ ⟨i, j, k, hij, hjk⟩)
        (χ ⟨i, j, l, hij, hjk.trans hkl⟩)
        (χ ⟨i, k, l, hij.trans hjk, hkl⟩)
        (χ ⟨j, k, l, hjk, hkl⟩)

/-- The irreducible structural core selected by the route review: two
consecutive cup blocks of sizes three and four force the `(4,5,5)` outcome. -/
def CupBlocks34Force455 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ((left.card = 3 ∧ right.card = 4) ∨
        (left.card = 4 ∧ right.card = 3)) →
      IsCupSet χ left → IsCupSet χ right → OneChangeOn χ (left ∪ right) →
      ContainsCapSet χ (left ∪ right) 4 ∨
        ContainsCupSet χ (left ∪ right) 5 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 5

/-- A right-turning ordered triple is a three-cap on its vertex set. -/
theorem isCapSet_three {n : ℕ} {χ : TripleColoring n}
    (t : OrderedTriple n) (hcolor : χ t = Turn.right) :
    IsCapSet χ {t.i, t.j, t.k} := by
  have htij : t.i < t.j := t.hij
  have htjk : t.j < t.k := t.hjk
  rintro ⟨a, b, c, hab, hbc⟩ ha hb hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;> try omega

/-- If no upper three-cap has `q` as a sweep endpoint, the upper vertices on
each side of `q` are cups. -/
theorem gap_sides_are_cups_of_no_endpoint_cap_three {n : ℕ}
    {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n}
    (hno : ¬∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = 3 ∧
      IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q) :
    IsCupSet χ (upper.filter (· < q)) ∧
      IsCupSet χ (upper.filter (q < ·)) := by
  constructor
  · intro t hi hj hk
    cases hcolor : χ t with
    | left => rfl
    | right =>
        exfalso
        apply hno
        refine ⟨{t.i, t.j, t.k}, ?_, ?_, isCapSet_three t hcolor, Or.inr ?_⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact (Finset.mem_filter.mp hi).1
          · exact (Finset.mem_filter.mp hj).1
          · exact (Finset.mem_filter.mp hk).1
        · simp [ne_of_lt t.hij, ne_of_lt t.hjk,
            ne_of_lt (t.hij.trans t.hjk)]
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact (Finset.mem_filter.mp hi).2.le
          · exact (Finset.mem_filter.mp hj).2.le
          · exact (Finset.mem_filter.mp hk).2.le
  · intro t hi hj hk
    cases hcolor : χ t with
    | left => rfl
    | right =>
        exfalso
        apply hno
        refine ⟨{t.i, t.j, t.k}, ?_, ?_, isCapSet_three t hcolor, Or.inl ?_⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact (Finset.mem_filter.mp hi).1
          · exact (Finset.mem_filter.mp hj).1
          · exact (Finset.mem_filter.mp hk).1
        · simp [ne_of_lt t.hij, ne_of_lt t.hjk,
            ne_of_lt (t.hij.trans t.hjk)]
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact (Finset.mem_filter.mp hi).2.le
          · exact (Finset.mem_filter.mp hj).2.le
          · exact (Finset.mem_filter.mp hk).2.le

/-- A cup subset has at most four vertices when the ambient set has no
five-cup. -/
theorem card_le_four_of_isCupSet_of_no_five_cup {n : ℕ}
    {χ : TripleColoring n} {s upper : Finset (Fin n)}
    (hsub : s ⊆ upper) (hcup : IsCupSet χ s)
    (hno : ¬ContainsCupSet χ upper 5) : s.card ≤ 4 := by
  by_contra hcard
  have hfive : 5 ≤ s.card := by omega
  obtain ⟨five, hfiveSub, hfiveCard⟩ := Finset.exists_subset_card_eq hfive
  apply hno
  exact ⟨five, hfiveSub.trans hsub, hfiveCard,
    FinsetPolygon.IsCupSet.mono hcup hfiveSub⟩

/-- Seven vertices split by an external anchor into two cups of size at most
four must have side sizes three and four. -/
theorem gap_cup_blocks_three_four {n : ℕ} {χ : TripleColoring n}
    {upper : Finset (Fin n)} {q : Fin n} (hq : q ∉ upper)
    (hcard : upper.card = 7) (hnoCup : ¬ContainsCupSet χ upper 5)
    (hcups : IsCupSet χ (upper.filter (· < q)) ∧
      IsCupSet χ (upper.filter (q < ·))) :
    (((upper.filter (· < q)).card = 3 ∧
        (upper.filter (q < ·)).card = 4) ∨
      ((upper.filter (· < q)).card = 4 ∧
        (upper.filter (q < ·)).card = 3)) := by
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
      have hxq : x ≠ q := by rintro rfl; exact hq hx
      rcases lt_or_gt_of_ne hxq with hxlt | hxgt
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hxgt⟩)
  have hdisjoint : Disjoint left right := by
    rw [Finset.disjoint_left]
    intro x hxLeft hxRight
    have hxlt := (Finset.mem_filter.mp hxLeft).2
    have hxgt := (Finset.mem_filter.mp hxRight).2
    omega
  have hleftSub : left ⊆ upper := Finset.filter_subset _ _
  have hrightSub : right ⊆ upper := Finset.filter_subset _ _
  have hleftCard : left.card ≤ 4 :=
    card_le_four_of_isCupSet_of_no_five_cup hleftSub hcups.1 hnoCup
  have hrightCard : right.card ≤ 4 :=
    card_le_four_of_isCupSet_of_no_five_cup hrightSub hcups.2 hnoCup
  have hsum : left.card + right.card = 7 := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion, hcard]
  change (left.card = 3 ∧ right.card = 4) ∨
    (left.card = 4 ∧ right.card = 3)
  omega

/-- The two-cup-block core implies the reviewed seven-vertex upper-child gap
trichotomy without a finite certificate. -/
theorem upperChildGapTrichotomyAtSeven_of_cupBlocks34
    (hblocks : CupBlocks34Force455) : UpperChildGapTrichotomyAtSeven := by
  intro n χ upper q hdecomposable hroot hcard
  by_cases hcap : ContainsCapSet χ upper 4
  · exact Or.inl hcap
  by_cases hcup : ContainsCupSet χ upper 5
  · exact Or.inr (Or.inl hcup)
  by_cases hstrong : ContainsStrongPolygonSet χ upper 5
  · exact Or.inr (Or.inr (Or.inl hstrong))
  by_cases hendpoint : ∃ cap : Finset (Fin n), cap ⊆ upper ∧
      cap.card = 3 ∧ IsCapSet χ cap ∧
        HasDeepBelowSplit.IsSweepEndpoint cap q
  · exact Or.inr (Or.inr (Or.inr hendpoint))
  have hq : q ∉ upper := by
    intro hqUpper
    exact (Finset.disjoint_left.mp hroot.disjoint) (by simp) hqUpper
  let left := upper.filter (· < q)
  let right := upper.filter (q < ·)
  have hcups : IsCupSet χ left ∧ IsCupSet χ right :=
    gap_sides_are_cups_of_no_endpoint_cap_three hendpoint
  have hcards : (left.card = 3 ∧ right.card = 4) ∨
      (left.card = 4 ∧ right.card = 3) :=
    gap_cup_blocks_three_four hq hcard hcup hcups
  have hunion : left ∪ right = upper := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    · intro hx
      have hxq : x ≠ q := by rintro rfl; exact hq hx
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
    have hxq := (Finset.mem_filter.mp hx).2
    have hqy := (Finset.mem_filter.mp hy).2
    exact hxq.trans hqy
  have honeChange : OneChangeOn χ (left ∪ right) := by
    intro i j k l hij hjk hkl hi hj hk hl
    exact hdecomposable.turnSequenceAllowed hij hjk hkl
      (hunion ▸ hi) (hunion ▸ hj) (hunion ▸ hk) (hunion ▸ hl)
  have hout := hblocks hdisjoint horder hcards hcups.1 hcups.2 honeChange
  rw [hunion] at hout
  rcases hout with hcap' | hcup' | hstrong'
  · exact (hcap hcap').elim
  · exact (hcup hcup').elim
  · exact (hstrong hstrong').elim

namespace HasDeepBelowSplit

/-- Opposite children cannot simultaneously carry positive saturated chains
when both one-vertex extensions are forbidden. -/
theorem not_both_saturated_cup_cap {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper)
    {cup cap : Finset (Fin n)} {r s : ℕ}
    (hcupSub : cup ⊆ lower) (hcupCard : cup.card = r)
    (hcup : IsCupSet χ cup)
    (hcapSub : cap ⊆ upper) (hcapCard : cap.card = s)
    (hcap : IsCapSet χ cap) (_hr : 0 < r) (hs : 0 < s)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) (r + 1))
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) (s + 1)) : False := by
  have hcapNonempty : cap.Nonempty := Finset.card_pos.mp (by omega)
  let q := cap.min' hcapNonempty
  have hqCap : q ∈ cap := Finset.min'_mem cap hcapNonempty
  have hqUpper : q ∈ upper := hcapSub hqCap
  obtain ⟨⟨x, hxCup, hxq⟩, _⟩ := h.cup_straddles_upper_of_not_containsCupSet_succ
    hcupSub hcupCard hcup hqUpper hnoCup
  have hxLower : x ∈ lower := hcupSub hxCup
  obtain ⟨⟨a, haCap, hax⟩, _⟩ := h.cap_straddles_lower_of_not_containsCapSet_succ
    hcapSub hcapCard hcap hxLower hnoCap
  have hqa : q ≤ a := Finset.min'_le cap a haCap
  omega

/-- Every branch of the upper-child gap trichotomy gives the desired
singleton-root `(4,5,5)` alternative. -/
theorem singleton_root_state455_of_upperChildGap {n : ℕ}
    {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n}
    (h : HasDeepBelowSplit χ {q} upper)
    (hgap : UpperChildGapTrichotomy455 χ upper q) :
    ContainsCapSet χ ({q} ∪ upper) 4 ∨
      ContainsCupSet χ ({q} ∪ upper) 5 ∨
      ContainsStrongPolygonSet χ ({q} ∪ upper) 5 := by
  rcases hgap with hcap | hcup | hstrong | ⟨cap, hcapSub, hcapCard, hcap, hendpoint⟩
  · exact Or.inl (FinsetPolygon.ContainsCapSet.mono hcap Finset.subset_union_right)
  · exact Or.inr (Or.inl
      (FinsetPolygon.ContainsCupSet.mono hcup Finset.subset_union_right))
  · exact Or.inr (Or.inr
      (FinsetPolygon.ContainsStrongPolygonSet.mono
        hstrong Finset.subset_union_right))
  · left
    simpa using h.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcap (by simp) hendpoint

/-- The seven-vertex gap trichotomy mechanically yields the certificate-free
singleton-root cardinal bound. -/
theorem singleton_root_card_le_seven_of_gapTrichotomy
    (hgap : UpperChildGapTrichotomyAtSeven) {n : ℕ}
    {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n}
    (hupper : IsDecomposableOn χ upper)
    (h : HasDeepBelowSplit χ {q} upper)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 5) :
    ({q} ∪ upper).card ≤ 7 := by
  by_contra hcard
  have hcardEq : ({q} ∪ upper).card = 1 + upper.card := by
    rw [Finset.card_union_of_disjoint h.disjoint]
    simp
  have hseven : 7 ≤ upper.card := by omega
  obtain ⟨seven, hsevenSub, hsevenCard⟩ := Finset.exists_subset_card_eq hseven
  have hsevenNonempty : seven.Nonempty := Finset.card_pos.mp (by omega)
  have hsevenDecomposable : IsDecomposableOn χ seven :=
    hupper.subset hsevenSub hsevenNonempty
  have hsevenSplit : HasDeepBelowSplit χ {q} seven :=
    h.mono Finset.Subset.rfl hsevenSub
  have hsmall := singleton_root_state455_of_upperChildGap hsevenSplit
    (hgap hsevenDecomposable hsevenSplit hsevenCard)
  have hsmallSub : {q} ∪ seven ⊆ {q} ∪ upper :=
    Finset.union_subset_union Finset.Subset.rfl hsevenSub
  rcases hsmall with hcap | hcup | hstrong
  · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hsmallSub)
  · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hsmallSub)
  · exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hsmallSub)

end HasDeepBelowSplit
end ErdosSzekeres

end
