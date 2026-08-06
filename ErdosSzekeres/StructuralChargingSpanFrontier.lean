module

public import ErdosSzekeres.StructuralChargingPascalDemand
public import ErdosSzekeres.SpanDominance
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-!
# Exact-rank span frontiers

This file gives the local structural-counting target an executable Lean
carrier.  At a decomposition node, crossing endpoint spans of one color and
one exact rank are pruned by interval containment.  The retained family is an
ordered antichain with injective left and right endpoints.

The final Pascal bound requires an additional injection of this frontier into
one layer of row `k - 2`.  `AllocatedExactRankSlotting` names precisely that
remaining mathematical construction; the cardinal consequence is proved
here without assuming that such a slotting always exists.
-/

namespace ErdosSzekeres

noncomputable section

open HasDeepBelowSplit

/-- An ordered pair used as the exact sweep endpoints of a monochromatic
span.  Non-ordered pairs remain in the finite ambient type but are rejected by
`CrossesSplit`. -/
structure SweepSpanEndpoints (n : ℕ) where
  left : Fin n
  right : Fin n
deriving DecidableEq, Fintype

namespace SweepSpanEndpoints

/-- The outer span contains the inner span in sweep order. -/
def Contains {n : ℕ} (outer inner : SweepSpanEndpoints n) : Prop :=
  outer.left ≤ inner.left ∧ inner.right ≤ outer.right

/-- The endpoints are ordered and occupy opposite children of a split. -/
def CrossesSplit {n : ℕ} (span : SweepSpanEndpoints n)
    (lower upper : Finset (Fin n)) : Prop :=
  span.left < span.right ∧
    ((span.left ∈ lower ∧ span.right ∈ upper) ∨
      (span.left ∈ upper ∧ span.right ∈ lower))

theorem contains_refl {n : ℕ} (span : SweepSpanEndpoints n) : span.Contains span := by
  exact ⟨le_rfl, le_rfl⟩

theorem contains_antisymm {n : ℕ} {first second : SweepSpanEndpoints n}
    (hfirst : first.Contains second) (hsecond : second.Contains first) :
    first = second := by
  cases first
  cases second
  simp only [Contains] at hfirst hsecond
  simp_all only [mk.injEq]
  exact ⟨le_antisymm hfirst.1 hsecond.1, le_antisymm hsecond.2 hfirst.2⟩

end SweepSpanEndpoints

/-- A color-uniform interface to cup and cap span-rank witnesses. -/
def HasSpanRankAtLeast {n : ℕ} (color : Turn) (chi : TripleColoring n)
    (s : Finset (Fin n)) (span : SweepSpanEndpoints n) (rank : ℕ) : Prop :=
  match color with
  | .left => HasCupSpanRankAtLeast chi s span.left span.right rank
  | .right => HasCapSpanRankAtLeast chi s span.left span.right rank

/-- The maximum monochromatic rank at the stated endpoints is exactly
`rank`. -/
def HasExactSpanRank {n : ℕ} (color : Turn) (chi : TripleColoring n)
    (s : Finset (Fin n)) (span : SweepSpanEndpoints n) (rank : ℕ) : Prop :=
  HasSpanRankAtLeast color chi s span rank ∧
    ¬HasSpanRankAtLeast color chi s span (rank + 1)

/-- A lower-child cup of the requested rank starts at `a` and ends before the
upper endpoint `q`. -/
def HasCupRightRayRankAtLeast {n : ℕ} (chi : TripleColoring n)
    (lower : Finset (Fin n)) (a q : Fin n) (rank : ℕ) : Prop :=
  ∃ b ∈ lower, b < q ∧ HasCupSpanRankAtLeast chi lower a b rank

/-- The left-facing version: the lower-child cup starts after the upper
endpoint `q` and ends at `b`. -/
def HasCupLeftRayRankAtLeast {n : ℕ} (chi : TripleColoring n)
    (lower : Finset (Fin n)) (q b : Fin n) (rank : ℕ) : Prop :=
  ∃ a ∈ lower, q < a ∧ HasCupSpanRankAtLeast chi lower a b rank

/-- An upper-child cap starts at `a` and ends before a lower right endpoint. -/
def HasCapRightRayRankAtLeast {n : ℕ} (chi : TripleColoring n)
    (upper : Finset (Fin n)) (a q : Fin n) (rank : ℕ) : Prop :=
  ∃ b ∈ upper, b < q ∧ HasCapSpanRankAtLeast chi upper a b rank

/-- An upper-child cap starts after a lower left endpoint and ends at `b`. -/
def HasCapLeftRayRankAtLeast {n : ℕ} (chi : TripleColoring n)
    (upper : Finset (Fin n)) (q b : Fin n) (rank : ℕ) : Prop :=
  ∃ a ∈ upper, q < a ∧ HasCapSpanRankAtLeast chi upper a b rank

/-- Exact right-facing lower-child cup-ray rank. -/
def HasExactCupRightRayRank {n : ℕ} (chi : TripleColoring n)
    (lower : Finset (Fin n)) (a q : Fin n) (rank : ℕ) : Prop :=
  HasCupRightRayRankAtLeast chi lower a q rank ∧
    ¬HasCupRightRayRankAtLeast chi lower a q (rank + 1)

/-- Exact left-facing lower-child cup-ray rank. -/
def HasExactCupLeftRayRank {n : ℕ} (chi : TripleColoring n)
    (lower : Finset (Fin n)) (q b : Fin n) (rank : ℕ) : Prop :=
  HasCupLeftRayRankAtLeast chi lower q b rank ∧
    ¬HasCupLeftRayRankAtLeast chi lower q b (rank + 1)

/-- Exact right-facing upper-child cap-ray rank. -/
def HasExactCapRightRayRank {n : ℕ} (chi : TripleColoring n)
    (upper : Finset (Fin n)) (a q : Fin n) (rank : ℕ) : Prop :=
  HasCapRightRayRankAtLeast chi upper a q rank ∧
    ¬HasCapRightRayRankAtLeast chi upper a q (rank + 1)

/-- Exact left-facing upper-child cap-ray rank. -/
def HasExactCapLeftRayRank {n : ℕ} (chi : TripleColoring n)
    (upper : Finset (Fin n)) (q b : Fin n) (rank : ℕ) : Prop :=
  HasCapLeftRayRankAtLeast chi upper q b rank ∧
    ¬HasCapLeftRayRankAtLeast chi upper q b (rank + 1)

/-- A sweep endpoint of a set with an exact span is one of its two recorded
endpoints. -/
theorem HasSweepSpan.isSweepEndpoint_eq_left_or_right {n : ℕ}
    {chain : Finset (Fin n)} {a b q : Fin n} (hspan : HasSweepSpan chain a b)
    (hqChain : q ∈ chain) (hqEndpoint : IsSweepEndpoint chain q) :
    q = a ∨ q = b := by
  rcases hqEndpoint with hleft | hright
  · exact Or.inl (le_antisymm (hleft a hspan.left_mem) (hspan.left_endpoint q hqChain))
  · exact Or.inr (le_antisymm (hspan.right_endpoint q hqChain)
      (hright b hspan.right_mem))

/-- Cardinality splits across the two disjoint children. -/
theorem card_eq_card_inter_add_card_inter_of_subset_union {n : ℕ}
    {s lower upper : Finset (Fin n)} (hdisjoint : Disjoint lower upper)
    (hsub : s ⊆ lower ∪ upper) :
    s.card = (s ∩ lower).card + (s ∩ upper).card := by
  have hpartition : (s ∩ lower) ∪ (s ∩ upper) = s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases Finset.mem_union.mp (hsub hx) with hxLower | hxUpper
      · exact Or.inl ⟨hx, hxLower⟩
      · exact Or.inr ⟨hx, hxUpper⟩
  calc
    s.card = ((s ∩ lower) ∪ (s ∩ upper)).card := congrArg Finset.card hpartition.symm
    _ = (s ∩ lower).card + (s ∩ upper).card :=
      Finset.card_union_of_disjoint
        (hdisjoint.mono Finset.inter_subset_right Finset.inter_subset_right)

/-- A cup rank threshold contains a cup of every smaller prescribed
cardinality. -/
theorem HasCupSpanRankAtLeast.toContainsCupSet {n rank size : ℕ}
    {chi : TripleColoring n} {s : Finset (Fin n)} {a b : Fin n}
    (hspan : HasCupSpanRankAtLeast chi s a b rank) (hsize : size ≤ rank) :
    ContainsCupSet chi s size := by
  obtain ⟨cup, hcupSub, hrank, hcup, _⟩ := hspan
  obtain ⟨small, hsmallSub, hsmallCard⟩ :=
    Finset.exists_subset_card_eq (hsize.trans hrank)
  exact ⟨small, hsmallSub.trans hcupSub, hsmallCard,
    FinsetPolygon.IsCupSet.mono hcup hsmallSub⟩

/-- Dual extraction of a cap of prescribed smaller cardinality. -/
theorem HasCapSpanRankAtLeast.toContainsCapSet {n rank size : ℕ}
    {chi : TripleColoring n} {s : Finset (Fin n)} {a b : Fin n}
    (hspan : HasCapSpanRankAtLeast chi s a b rank) (hsize : size ≤ rank) :
    ContainsCapSet chi s size := by
  obtain ⟨cap, hcapSub, hrank, hcap, _⟩ := hspan
  obtain ⟨small, hsmallSub, hsmallCard⟩ :=
    Finset.exists_subset_card_eq (hsize.trans hrank)
  exact ⟨small, hsmallSub.trans hcapSub, hsmallCard,
    FinsetPolygon.IsCapSet.mono hcap hsmallSub⟩

/-- A span rank at least `size` already supplies a strong set of that
cardinality. -/
theorem HasSpanRankAtLeast.toContainsStrongPolygonSet {n rank size : ℕ}
    {chi : TripleColoring n} {s : Finset (Fin n)} {span : SweepSpanEndpoints n}
    {color : Turn} (hspan : HasSpanRankAtLeast color chi s span rank)
    (hsize : size ≤ rank) : ContainsStrongPolygonSet chi s size := by
  cases color with
  | left =>
      exact FinsetPolygon.ContainsCupSet.toContainsStrongPolygonSet
        (HasCupSpanRankAtLeast.toContainsCupSet hspan hsize)
  | right =>
      exact FinsetPolygon.ContainsCapSet.toContainsStrongPolygonSet
        (HasCapSpanRankAtLeast.toContainsCapSet hspan hsize)

/-- In an open no-strong-`k` context, every exact span rank lies below `k`. -/
theorem HasExactSpanRank.lt_of_not_containsStrongPolygonSet {n rank k : ℕ}
    {chi : TripleColoring n} {s : Finset (Fin n)} {span : SweepSpanEndpoints n}
    {color : Turn} (hexact : HasExactSpanRank color chi s span rank)
    (hnoStrong : ¬ContainsStrongPolygonSet chi s k) : rank < k := by
  by_contra hnot
  exact hnoStrong (hexact.1.toContainsStrongPolygonSet (by omega))

/-- A cup with recorded endpoints crossing a deep-below split has exactly one
upper-child vertex.  The general two-port theorem sharpens to one because the
span already records one lower and one upper endpoint. -/
theorem HasDeepBelowSplit.cup_span_inter_upper_card_eq_one {n : ℕ}
    {chi : TripleColoring n} {lower upper cup : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hcupSub : cup ⊆ lower ∪ upper) (hcup : IsCupSet chi cup)
    (hspan : HasSweepSpan cup span.left span.right)
    (hcross : span.CrossesSplit lower upper) :
    (cup ∩ upper).card = 1 := by
  rcases hcross.2 with hsides | hsides
  · have hcupLower : (cup ∩ lower).Nonempty :=
      ⟨span.left, Finset.mem_inter.mpr ⟨hspan.left_mem, hsides.1⟩⟩
    have hupperSub : cup ∩ upper ⊆ {span.right} := by
      intro q hq
      have hqCup := (Finset.mem_inter.mp hq).1
      have hqUpper := (Finset.mem_inter.mp hq).2
      have hqEndpoint := hdeep.upper_mem_cup_isSweepEndpoint
        hcupSub hcup hcupLower hqCup hqUpper
      rcases hspan.isSweepEndpoint_eq_left_or_right hqCup hqEndpoint with hq | hq
      · subst q
        exact (Finset.disjoint_left.mp hdeep.disjoint hsides.1 hqUpper).elim
      · simp [hq]
    have hle : (cup ∩ upper).card ≤ 1 := by
      simpa using Finset.card_le_card hupperSub
    have hpos : 0 < (cup ∩ upper).card := Finset.card_pos.mpr
      ⟨span.right, Finset.mem_inter.mpr ⟨hspan.right_mem, hsides.2⟩⟩
    omega
  · have hcupLower : (cup ∩ lower).Nonempty :=
      ⟨span.right, Finset.mem_inter.mpr ⟨hspan.right_mem, hsides.2⟩⟩
    have hupperSub : cup ∩ upper ⊆ {span.left} := by
      intro q hq
      have hqCup := (Finset.mem_inter.mp hq).1
      have hqUpper := (Finset.mem_inter.mp hq).2
      have hqEndpoint := hdeep.upper_mem_cup_isSweepEndpoint
        hcupSub hcup hcupLower hqCup hqUpper
      rcases hspan.isSweepEndpoint_eq_left_or_right hqCup hqEndpoint with hq | hq
      · simp [hq]
      · subst q
        exact (Finset.disjoint_left.mp hdeep.disjoint hsides.2 hqUpper).elim
    have hle : (cup ∩ upper).card ≤ 1 := by
      simpa using Finset.card_le_card hupperSub
    have hpos : 0 < (cup ∩ upper).card := Finset.card_pos.mpr
      ⟨span.left, Finset.mem_inter.mpr ⟨hspan.left_mem, hsides.1⟩⟩
    omega

/-- Dually, a cap with crossing recorded endpoints has exactly one
lower-child vertex. -/
theorem HasDeepBelowSplit.cap_span_inter_lower_card_eq_one {n : ℕ}
    {chi : TripleColoring n} {lower upper cap : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hcapSub : cap ⊆ lower ∪ upper) (hcap : IsCapSet chi cap)
    (hspan : HasSweepSpan cap span.left span.right)
    (hcross : span.CrossesSplit lower upper) :
    (cap ∩ lower).card = 1 := by
  rcases hcross.2 with hsides | hsides
  · have hcapUpper : (cap ∩ upper).Nonempty :=
      ⟨span.right, Finset.mem_inter.mpr ⟨hspan.right_mem, hsides.2⟩⟩
    have hlowerSub : cap ∩ lower ⊆ {span.left} := by
      intro q hq
      have hqCap := (Finset.mem_inter.mp hq).1
      have hqLower := (Finset.mem_inter.mp hq).2
      have hqEndpoint := hdeep.lower_mem_cap_isSweepEndpoint
        hcapSub hcap hcapUpper hqCap hqLower
      rcases hspan.isSweepEndpoint_eq_left_or_right hqCap hqEndpoint with hq | hq
      · simp [hq]
      · subst q
        exact (Finset.disjoint_left.mp hdeep.disjoint hqLower hsides.2).elim
    have hle : (cap ∩ lower).card ≤ 1 := by
      simpa using Finset.card_le_card hlowerSub
    have hpos : 0 < (cap ∩ lower).card := Finset.card_pos.mpr
      ⟨span.left, Finset.mem_inter.mpr ⟨hspan.left_mem, hsides.1⟩⟩
    omega
  · have hcapUpper : (cap ∩ upper).Nonempty :=
      ⟨span.left, Finset.mem_inter.mpr ⟨hspan.left_mem, hsides.1⟩⟩
    have hlowerSub : cap ∩ lower ⊆ {span.right} := by
      intro q hq
      have hqCap := (Finset.mem_inter.mp hq).1
      have hqLower := (Finset.mem_inter.mp hq).2
      have hqEndpoint := hdeep.lower_mem_cap_isSweepEndpoint
        hcapSub hcap hcapUpper hqCap hqLower
      rcases hspan.isSweepEndpoint_eq_left_or_right hqCap hqEndpoint with hq | hq
      · subst q
        exact (Finset.disjoint_left.mp hdeep.disjoint hqLower hsides.1).elim
      · simp [hq]
    have hle : (cap ∩ lower).card ≤ 1 := by
      simpa using Finset.card_le_card hlowerSub
    have hpos : 0 < (cap ∩ lower).card := Finset.card_pos.mpr
      ⟨span.right, Finset.mem_inter.mpr ⟨hspan.right_mem, hsides.2⟩⟩
    omega

/-- Every crossing cup span of rank at least `rank` leaves an actual
`rank - 1` cup in the lower child. -/
theorem HasDeepBelowSplit.containsCupSet_pred_of_cupSpanRankAtLeast
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hcross : span.CrossesSplit lower upper)
    (hrank : HasCupSpanRankAtLeast chi (lower ∪ upper)
      span.left span.right rank) :
    ContainsCupSet chi lower (rank - 1) := by
  obtain ⟨cup, hcupSub, hcard, hcup, hspan⟩ := hrank
  have hupperCard := hdeep.cup_span_inter_upper_card_eq_one
    hcupSub hcup hspan hcross
  have hpartition := card_eq_card_inter_add_card_inter_of_subset_union
    hdeep.disjoint hcupSub
  have hlowerCard : rank - 1 ≤ (cup ∩ lower).card := by omega
  obtain ⟨small, hsmallSub, hsmallCard⟩ :=
    Finset.exists_subset_card_eq hlowerCard
  exact ⟨small, hsmallSub.trans Finset.inter_subset_right, hsmallCard,
    FinsetPolygon.IsCupSet.mono hcup
      (hsmallSub.trans Finset.inter_subset_left)⟩

/-- Dual child extraction for a crossing cap span. -/
theorem HasDeepBelowSplit.containsCapSet_pred_of_capSpanRankAtLeast
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hcross : span.CrossesSplit lower upper)
    (hrank : HasCapSpanRankAtLeast chi (lower ∪ upper)
      span.left span.right rank) :
    ContainsCapSet chi upper (rank - 1) := by
  obtain ⟨cap, hcapSub, hcard, hcap, hspan⟩ := hrank
  have hlowerCard := hdeep.cap_span_inter_lower_card_eq_one
    hcapSub hcap hspan hcross
  have hpartition := card_eq_card_inter_add_card_inter_of_subset_union
    hdeep.disjoint hcapSub
  have hupperCard : rank - 1 ≤ (cap ∩ upper).card := by omega
  obtain ⟨small, hsmallSub, hsmallCard⟩ :=
    Finset.exists_subset_card_eq hupperCard
  exact ⟨small, hsmallSub.trans Finset.inter_subset_right, hsmallCard,
    FinsetPolygon.IsCapSet.mono hcap
      (hsmallSub.trans Finset.inter_subset_left)⟩

/-- Exact threshold transition for a lower-left/upper-right cup span.  The
upper endpoint contributes one vertex, while the lower witness is a
right-facing anchored ray. -/
theorem HasDeepBelowSplit.hasCupSpanRankAtLeast_succ_iff_rightRay
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {a q : Fin n} (hdeep : HasDeepBelowSplit chi lower upper)
    (haLower : a ∈ lower) (hqUpper : q ∈ upper) (haq : a < q)
    (hrank : 2 ≤ rank) :
    HasCupSpanRankAtLeast chi (lower ∪ upper) a q (rank + 1) ↔
      HasCupRightRayRankAtLeast chi lower a q rank := by
  constructor
  · rintro ⟨cup, hcupSub, hcard, hcup, hspan⟩
    have hupperCard := hdeep.cup_span_inter_upper_card_eq_one
      (span := ⟨a, q⟩) hcupSub hcup hspan
      ⟨haq, Or.inl ⟨haLower, hqUpper⟩⟩
    have hpartition := card_eq_card_inter_add_card_inter_of_subset_union
      hdeep.disjoint hcupSub
    have hlowerCard : rank ≤ (cup ∩ lower).card := by omega
    have hlowerNonempty : (cup ∩ lower).Nonempty :=
      ⟨a, Finset.mem_inter.mpr ⟨hspan.left_mem, haLower⟩⟩
    let b := (cup ∩ lower).max' hlowerNonempty
    have hbInter : b ∈ cup ∩ lower :=
      Finset.max'_mem (cup ∩ lower) hlowerNonempty
    have hbCup : b ∈ cup := (Finset.mem_inter.mp hbInter).1
    have hbLower : b ∈ lower := (Finset.mem_inter.mp hbInter).2
    have haMin : a = (cup ∩ lower).min' hlowerNonempty := by
      apply le_antisymm
      · exact hspan.left_endpoint _
          (Finset.mem_inter.mp (Finset.min'_mem _ _)).1
      · exact Finset.min'_le _ _
          (Finset.mem_inter.mpr ⟨hspan.left_mem, haLower⟩)
    have hab : a < b := by
      rw [haMin]
      exact Finset.min'_lt_max'_of_card _ (by omega)
    have hbq : b < q := by
      have hle := hspan.right_endpoint b hbCup
      have hne : b ≠ q := by
        intro hbq
        exact (Finset.disjoint_left.mp hdeep.disjoint hbLower (hbq ▸ hqUpper))
      omega
    refine ⟨b, hbLower, hbq, cup ∩ lower, Finset.inter_subset_right,
      hlowerCard, FinsetPolygon.IsCupSet.mono hcup Finset.inter_subset_left, ?_⟩
    refine ⟨hab, Finset.mem_inter.mpr ⟨hspan.left_mem, haLower⟩, hbInter, ?_, ?_⟩
    · intro x hx
      exact hspan.left_endpoint x (Finset.mem_inter.mp hx).1
    · intro x hx
      exact Finset.le_max' (cup ∩ lower) x hx
  · rintro ⟨b, hbLower, hbq, hchild⟩
    exact hchild.insert_upper_right hdeep hqUpper hbq

/-- Exact threshold transition for an upper-left/lower-right cup span. -/
theorem HasDeepBelowSplit.hasCupSpanRankAtLeast_succ_iff_leftRay
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {q b : Fin n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hqUpper : q ∈ upper) (hbLower : b ∈ lower) (hqb : q < b)
    (hrank : 2 ≤ rank) :
    HasCupSpanRankAtLeast chi (lower ∪ upper) q b (rank + 1) ↔
      HasCupLeftRayRankAtLeast chi lower q b rank := by
  constructor
  · rintro ⟨cup, hcupSub, hcard, hcup, hspan⟩
    have hupperCard := hdeep.cup_span_inter_upper_card_eq_one
      (span := ⟨q, b⟩) hcupSub hcup hspan
      ⟨hqb, Or.inr ⟨hqUpper, hbLower⟩⟩
    have hpartition := card_eq_card_inter_add_card_inter_of_subset_union
      hdeep.disjoint hcupSub
    have hlowerCard : rank ≤ (cup ∩ lower).card := by omega
    have hlowerNonempty : (cup ∩ lower).Nonempty :=
      ⟨b, Finset.mem_inter.mpr ⟨hspan.right_mem, hbLower⟩⟩
    let a := (cup ∩ lower).min' hlowerNonempty
    have haInter : a ∈ cup ∩ lower :=
      Finset.min'_mem (cup ∩ lower) hlowerNonempty
    have haCup : a ∈ cup := (Finset.mem_inter.mp haInter).1
    have haLower : a ∈ lower := (Finset.mem_inter.mp haInter).2
    have hbMax : b = (cup ∩ lower).max' hlowerNonempty := by
      apply le_antisymm
      · exact Finset.le_max' _ _
          (Finset.mem_inter.mpr ⟨hspan.right_mem, hbLower⟩)
      · exact hspan.right_endpoint _
          (Finset.mem_inter.mp (Finset.max'_mem _ _)).1
    have hab : a < b := by
      rw [hbMax]
      exact Finset.min'_lt_max'_of_card _ (by omega)
    have hqa : q < a := by
      have hle := hspan.left_endpoint a haCup
      have hne : q ≠ a := by
        intro hqa
        exact (Finset.disjoint_left.mp hdeep.disjoint haLower (hqa ▸ hqUpper))
      omega
    refine ⟨a, haLower, hqa, cup ∩ lower, Finset.inter_subset_right,
      hlowerCard, FinsetPolygon.IsCupSet.mono hcup Finset.inter_subset_left, ?_⟩
    refine ⟨hab, haInter, Finset.mem_inter.mpr ⟨hspan.right_mem, hbLower⟩, ?_, ?_⟩
    · intro x hx
      exact Finset.min'_le (cup ∩ lower) x hx
    · intro x hx
      exact hspan.right_endpoint x (Finset.mem_inter.mp hx).1
  · rintro ⟨a, haLower, hqa, hchild⟩
    exact hchild.insert_upper_left hdeep hqUpper hqa

/-- Exact threshold transition for an upper-left/lower-right cap span. -/
theorem HasDeepBelowSplit.hasCapSpanRankAtLeast_succ_iff_rightRay
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {a q : Fin n} (hdeep : HasDeepBelowSplit chi lower upper)
    (haUpper : a ∈ upper) (hqLower : q ∈ lower) (haq : a < q)
    (hrank : 2 ≤ rank) :
    HasCapSpanRankAtLeast chi (lower ∪ upper) a q (rank + 1) ↔
      HasCapRightRayRankAtLeast chi upper a q rank := by
  constructor
  · rintro ⟨cap, hcapSub, hcard, hcap, hspan⟩
    have hlowerCard := hdeep.cap_span_inter_lower_card_eq_one
      (span := ⟨a, q⟩) hcapSub hcap hspan
      ⟨haq, Or.inr ⟨haUpper, hqLower⟩⟩
    have hpartition := card_eq_card_inter_add_card_inter_of_subset_union
      hdeep.disjoint hcapSub
    have hupperCard : rank ≤ (cap ∩ upper).card := by omega
    have hupperNonempty : (cap ∩ upper).Nonempty :=
      ⟨a, Finset.mem_inter.mpr ⟨hspan.left_mem, haUpper⟩⟩
    let b := (cap ∩ upper).max' hupperNonempty
    have hbInter : b ∈ cap ∩ upper :=
      Finset.max'_mem (cap ∩ upper) hupperNonempty
    have hbCap : b ∈ cap := (Finset.mem_inter.mp hbInter).1
    have hbUpper : b ∈ upper := (Finset.mem_inter.mp hbInter).2
    have haMin : a = (cap ∩ upper).min' hupperNonempty := by
      apply le_antisymm
      · exact hspan.left_endpoint _
          (Finset.mem_inter.mp (Finset.min'_mem _ _)).1
      · exact Finset.min'_le _ _
          (Finset.mem_inter.mpr ⟨hspan.left_mem, haUpper⟩)
    have hab : a < b := by
      rw [haMin]
      exact Finset.min'_lt_max'_of_card _ (by omega)
    have hbq : b < q := by
      have hle := hspan.right_endpoint b hbCap
      have hne : b ≠ q := by
        intro hbq
        exact (Finset.disjoint_left.mp hdeep.disjoint (hbq ▸ hqLower) hbUpper)
      omega
    refine ⟨b, hbUpper, hbq, cap ∩ upper, Finset.inter_subset_right,
      hupperCard, FinsetPolygon.IsCapSet.mono hcap Finset.inter_subset_left, ?_⟩
    refine ⟨hab, Finset.mem_inter.mpr ⟨hspan.left_mem, haUpper⟩, hbInter, ?_, ?_⟩
    · intro x hx
      exact hspan.left_endpoint x (Finset.mem_inter.mp hx).1
    · intro x hx
      exact Finset.le_max' (cap ∩ upper) x hx
  · rintro ⟨b, hbUpper, hbq, hchild⟩
    exact hchild.insert_lower_right hdeep hqLower hbq

/-- Exact threshold transition for a lower-left/upper-right cap span. -/
theorem HasDeepBelowSplit.hasCapSpanRankAtLeast_succ_iff_leftRay
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {q b : Fin n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hqLower : q ∈ lower) (hbUpper : b ∈ upper) (hqb : q < b)
    (hrank : 2 ≤ rank) :
    HasCapSpanRankAtLeast chi (lower ∪ upper) q b (rank + 1) ↔
      HasCapLeftRayRankAtLeast chi upper q b rank := by
  constructor
  · rintro ⟨cap, hcapSub, hcard, hcap, hspan⟩
    have hlowerCard := hdeep.cap_span_inter_lower_card_eq_one
      (span := ⟨q, b⟩) hcapSub hcap hspan
      ⟨hqb, Or.inl ⟨hqLower, hbUpper⟩⟩
    have hpartition := card_eq_card_inter_add_card_inter_of_subset_union
      hdeep.disjoint hcapSub
    have hupperCard : rank ≤ (cap ∩ upper).card := by omega
    have hupperNonempty : (cap ∩ upper).Nonempty :=
      ⟨b, Finset.mem_inter.mpr ⟨hspan.right_mem, hbUpper⟩⟩
    let a := (cap ∩ upper).min' hupperNonempty
    have haInter : a ∈ cap ∩ upper :=
      Finset.min'_mem (cap ∩ upper) hupperNonempty
    have haCap : a ∈ cap := (Finset.mem_inter.mp haInter).1
    have haUpper : a ∈ upper := (Finset.mem_inter.mp haInter).2
    have hbMax : b = (cap ∩ upper).max' hupperNonempty := by
      apply le_antisymm
      · exact Finset.le_max' _ _
          (Finset.mem_inter.mpr ⟨hspan.right_mem, hbUpper⟩)
      · exact hspan.right_endpoint _
          (Finset.mem_inter.mp (Finset.max'_mem _ _)).1
    have hab : a < b := by
      rw [hbMax]
      exact Finset.min'_lt_max'_of_card _ (by omega)
    have hqa : q < a := by
      have hle := hspan.left_endpoint a haCap
      have hne : q ≠ a := by
        intro hqa
        exact (Finset.disjoint_left.mp hdeep.disjoint hqLower (hqa ▸ haUpper))
      omega
    refine ⟨a, haUpper, hqa, cap ∩ upper, Finset.inter_subset_right,
      hupperCard, FinsetPolygon.IsCapSet.mono hcap Finset.inter_subset_left, ?_⟩
    refine ⟨hab, haInter, Finset.mem_inter.mpr ⟨hspan.right_mem, hbUpper⟩, ?_, ?_⟩
    · intro x hx
      exact Finset.min'_le (cap ∩ upper) x hx
    · intro x hx
      exact hspan.right_endpoint x (Finset.mem_inter.mp hx).1
  · rintro ⟨a, haUpper, hqa, hchild⟩
    exact hchild.insert_lower_left hdeep hqLower hqa

/-- Exact parent cup rank is exact predecessor right-ray rank. -/
theorem HasDeepBelowSplit.hasExactCupSpanRank_iff_exactRightRay
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {a q : Fin n} (hdeep : HasDeepBelowSplit chi lower upper)
    (haLower : a ∈ lower) (hqUpper : q ∈ upper) (haq : a < q)
    (hrank : 3 ≤ rank) :
    HasExactSpanRank .left chi (lower ∪ upper)
        (⟨a, q⟩ : SweepSpanEndpoints n) rank ↔
      HasExactCupRightRayRank chi lower a q (rank - 1) := by
  have hpred : rank - 1 + 1 = rank := by omega
  have hbase := hdeep.hasCupSpanRankAtLeast_succ_iff_rightRay
    haLower hqUpper haq (rank := rank - 1) (by omega)
  have hnext := hdeep.hasCupSpanRankAtLeast_succ_iff_rightRay
    haLower hqUpper haq (rank := rank) (by omega)
  change (HasCupSpanRankAtLeast chi (lower ∪ upper) a q rank ∧
      ¬HasCupSpanRankAtLeast chi (lower ∪ upper) a q (rank + 1)) ↔
    (HasCupRightRayRankAtLeast chi lower a q (rank - 1) ∧
      ¬HasCupRightRayRankAtLeast chi lower a q (rank - 1 + 1))
  constructor
  · rintro ⟨hcurrent, hnotNext⟩
    refine ⟨hbase.mp (by simpa only [hpred] using hcurrent), ?_⟩
    intro hnextRay
    apply hnotNext
    exact hnext.mpr (by simpa only [hpred] using hnextRay)
  · rintro ⟨hcurrentRay, hnotNextRay⟩
    refine ⟨by simpa only [hpred] using hbase.mpr hcurrentRay, ?_⟩
    intro hnextSpan
    apply hnotNextRay
    simpa only [hpred] using hnext.mp hnextSpan

/-- Exact parent cup rank is exact predecessor left-ray rank. -/
theorem HasDeepBelowSplit.hasExactCupSpanRank_iff_exactLeftRay
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {q b : Fin n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hqUpper : q ∈ upper) (hbLower : b ∈ lower) (hqb : q < b)
    (hrank : 3 ≤ rank) :
    HasExactSpanRank .left chi (lower ∪ upper)
        (⟨q, b⟩ : SweepSpanEndpoints n) rank ↔
      HasExactCupLeftRayRank chi lower q b (rank - 1) := by
  have hpred : rank - 1 + 1 = rank := by omega
  have hbase := hdeep.hasCupSpanRankAtLeast_succ_iff_leftRay
    hqUpper hbLower hqb (rank := rank - 1) (by omega)
  have hnext := hdeep.hasCupSpanRankAtLeast_succ_iff_leftRay
    hqUpper hbLower hqb (rank := rank) (by omega)
  change (HasCupSpanRankAtLeast chi (lower ∪ upper) q b rank ∧
      ¬HasCupSpanRankAtLeast chi (lower ∪ upper) q b (rank + 1)) ↔
    (HasCupLeftRayRankAtLeast chi lower q b (rank - 1) ∧
      ¬HasCupLeftRayRankAtLeast chi lower q b (rank - 1 + 1))
  constructor
  · rintro ⟨hcurrent, hnotNext⟩
    refine ⟨hbase.mp (by simpa only [hpred] using hcurrent), ?_⟩
    intro hnextRay
    apply hnotNext
    exact hnext.mpr (by simpa only [hpred] using hnextRay)
  · rintro ⟨hcurrentRay, hnotNextRay⟩
    refine ⟨by simpa only [hpred] using hbase.mpr hcurrentRay, ?_⟩
    intro hnextSpan
    apply hnotNextRay
    simpa only [hpred] using hnext.mp hnextSpan

/-- Exact parent cap rank is exact predecessor right-ray rank. -/
theorem HasDeepBelowSplit.hasExactCapSpanRank_iff_exactRightRay
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {a q : Fin n} (hdeep : HasDeepBelowSplit chi lower upper)
    (haUpper : a ∈ upper) (hqLower : q ∈ lower) (haq : a < q)
    (hrank : 3 ≤ rank) :
    HasExactSpanRank .right chi (lower ∪ upper)
        (⟨a, q⟩ : SweepSpanEndpoints n) rank ↔
      HasExactCapRightRayRank chi upper a q (rank - 1) := by
  have hpred : rank - 1 + 1 = rank := by omega
  have hbase := hdeep.hasCapSpanRankAtLeast_succ_iff_rightRay
    haUpper hqLower haq (rank := rank - 1) (by omega)
  have hnext := hdeep.hasCapSpanRankAtLeast_succ_iff_rightRay
    haUpper hqLower haq (rank := rank) (by omega)
  change (HasCapSpanRankAtLeast chi (lower ∪ upper) a q rank ∧
      ¬HasCapSpanRankAtLeast chi (lower ∪ upper) a q (rank + 1)) ↔
    (HasCapRightRayRankAtLeast chi upper a q (rank - 1) ∧
      ¬HasCapRightRayRankAtLeast chi upper a q (rank - 1 + 1))
  constructor
  · rintro ⟨hcurrent, hnotNext⟩
    refine ⟨hbase.mp (by simpa only [hpred] using hcurrent), ?_⟩
    intro hnextRay
    apply hnotNext
    exact hnext.mpr (by simpa only [hpred] using hnextRay)
  · rintro ⟨hcurrentRay, hnotNextRay⟩
    refine ⟨by simpa only [hpred] using hbase.mpr hcurrentRay, ?_⟩
    intro hnextSpan
    apply hnotNextRay
    simpa only [hpred] using hnext.mp hnextSpan

/-- Exact parent cap rank is exact predecessor left-ray rank. -/
theorem HasDeepBelowSplit.hasExactCapSpanRank_iff_exactLeftRay
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {q b : Fin n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hqLower : q ∈ lower) (hbUpper : b ∈ upper) (hqb : q < b)
    (hrank : 3 ≤ rank) :
    HasExactSpanRank .right chi (lower ∪ upper)
        (⟨q, b⟩ : SweepSpanEndpoints n) rank ↔
      HasExactCapLeftRayRank chi upper q b (rank - 1) := by
  have hpred : rank - 1 + 1 = rank := by omega
  have hbase := hdeep.hasCapSpanRankAtLeast_succ_iff_leftRay
    hqLower hbUpper hqb (rank := rank - 1) (by omega)
  have hnext := hdeep.hasCapSpanRankAtLeast_succ_iff_leftRay
    hqLower hbUpper hqb (rank := rank) (by omega)
  change (HasCapSpanRankAtLeast chi (lower ∪ upper) q b rank ∧
      ¬HasCapSpanRankAtLeast chi (lower ∪ upper) q b (rank + 1)) ↔
    (HasCapLeftRayRankAtLeast chi upper q b (rank - 1) ∧
      ¬HasCapLeftRayRankAtLeast chi upper q b (rank - 1 + 1))
  constructor
  · rintro ⟨hcurrent, hnotNext⟩
    refine ⟨hbase.mp (by simpa only [hpred] using hcurrent), ?_⟩
    intro hnextRay
    apply hnotNext
    exact hnext.mpr (by simpa only [hpred] using hnextRay)
  · rintro ⟨hcurrentRay, hnotNextRay⟩
    refine ⟨by simpa only [hpred] using hbase.mpr hcurrentRay, ?_⟩
    intro hnextSpan
    apply hnotNextRay
    simpa only [hpred] using hnext.mp hnextSpan

/-- All crossing spans of one color and one exact local rank at the stated
decomposition node. -/
def allocatedExactRankSpans {n : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn) (rank : ℕ) :
    Finset (SweepSpanEndpoints n) := by
  classical
  exact Finset.univ.filter fun span ↦
    span.CrossesSplit lower upper ∧
      HasExactSpanRank color chi (lower ∪ upper) span rank

@[simp] theorem mem_allocatedExactRankSpans {n rank : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)} {color : Turn}
    {span : SweepSpanEndpoints n} :
    span ∈ allocatedExactRankSpans chi lower upper color rank ↔
      span.CrossesSplit lower upper ∧
        HasExactSpanRank color chi (lower ∪ upper) span rank := by
  simp [allocatedExactRankSpans]

/-- Candidate cup spans have a complete two-direction child-ray normal form. -/
theorem mem_allocatedExactRankSpans_left_iff_rays
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hrank : 3 ≤ rank) :
    span ∈ allocatedExactRankSpans chi lower upper .left rank ↔
      span.left < span.right ∧
        ((span.left ∈ lower ∧ span.right ∈ upper ∧
            HasExactCupRightRayRank chi lower span.left span.right (rank - 1)) ∨
          (span.left ∈ upper ∧ span.right ∈ lower ∧
            HasExactCupLeftRayRank chi lower span.left span.right (rank - 1))) := by
  rw [mem_allocatedExactRankSpans]
  constructor
  · rintro ⟨⟨hlt, hsides⟩, hexact⟩
    refine ⟨hlt, ?_⟩
    rcases hsides with hsides | hsides
    · exact Or.inl ⟨hsides.1, hsides.2,
        (hdeep.hasExactCupSpanRank_iff_exactRightRay
          hsides.1 hsides.2 hlt hrank).mp hexact⟩
    · exact Or.inr ⟨hsides.1, hsides.2,
        (hdeep.hasExactCupSpanRank_iff_exactLeftRay
          hsides.1 hsides.2 hlt hrank).mp hexact⟩
  · rintro ⟨hlt, hsides⟩
    rcases hsides with hsides | hsides
    · exact ⟨⟨hlt, Or.inl ⟨hsides.1, hsides.2.1⟩⟩,
        (hdeep.hasExactCupSpanRank_iff_exactRightRay
          hsides.1 hsides.2.1 hlt hrank).mpr hsides.2.2⟩
    · exact ⟨⟨hlt, Or.inr ⟨hsides.1, hsides.2.1⟩⟩,
        (hdeep.hasExactCupSpanRank_iff_exactLeftRay
          hsides.1 hsides.2.1 hlt hrank).mpr hsides.2.2⟩

/-- Candidate cap spans have the color-dual two-direction child-ray normal
form. -/
theorem mem_allocatedExactRankSpans_right_iff_rays
    {n rank : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hrank : 3 ≤ rank) :
    span ∈ allocatedExactRankSpans chi lower upper .right rank ↔
      span.left < span.right ∧
        ((span.left ∈ lower ∧ span.right ∈ upper ∧
            HasExactCapLeftRayRank chi upper span.left span.right (rank - 1)) ∨
          (span.left ∈ upper ∧ span.right ∈ lower ∧
            HasExactCapRightRayRank chi upper span.left span.right (rank - 1))) := by
  rw [mem_allocatedExactRankSpans]
  constructor
  · rintro ⟨⟨hlt, hsides⟩, hexact⟩
    refine ⟨hlt, ?_⟩
    rcases hsides with hsides | hsides
    · exact Or.inl ⟨hsides.1, hsides.2,
        (hdeep.hasExactCapSpanRank_iff_exactLeftRay
          hsides.1 hsides.2 hlt hrank).mp hexact⟩
    · exact Or.inr ⟨hsides.1, hsides.2,
        (hdeep.hasExactCapSpanRank_iff_exactRightRay
          hsides.1 hsides.2 hlt hrank).mp hexact⟩
  · rintro ⟨hlt, hsides⟩
    rcases hsides with hsides | hsides
    · exact ⟨⟨hlt, Or.inl ⟨hsides.1, hsides.2.1⟩⟩,
        (hdeep.hasExactCapSpanRank_iff_exactLeftRay
          hsides.1 hsides.2.1 hlt hrank).mpr hsides.2.2⟩
    · exact ⟨⟨hlt, Or.inr ⟨hsides.1, hsides.2.1⟩⟩,
        (hdeep.hasExactCapSpanRank_iff_exactRightRay
          hsides.1 hsides.2.1 hlt hrank).mpr hsides.2.2⟩

/-- Cup and cap ranks at one crossing endpoint pair have complementary total
at most `k + 1` in a no-strong-`k` node.  Their child witnesses lose exactly
one crossing endpoint each and then glue to a strong polygon. -/
theorem HasDeepBelowSplit.cupCapSpanRanks_add_le_of_noStrong
    {n cupRank capRank k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {span : SweepSpanEndpoints n}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hcross : span.CrossesSplit lower upper)
    (hcup : HasCupSpanRankAtLeast chi (lower ∪ upper)
      span.left span.right cupRank)
    (hcap : HasCapSpanRankAtLeast chi (lower ∪ upper)
      span.left span.right capRank)
    (hcupPos : 1 ≤ cupRank) (hcapPos : 1 ≤ capRank)
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    cupRank + capRank ≤ k + 1 := by
  have hlowerCup := hdeep.containsCupSet_pred_of_cupSpanRankAtLeast hcross hcup
  have hupperCap := hdeep.containsCapSet_pred_of_capSpanRankAtLeast hcross hcap
  by_contra hnot
  apply hnoStrong
  apply hdeep.containsStrongPolygonSet_of_containsCupCap hlowerCup hupperCap
  omega

/-- Inclusion-minimal exact-rank crossing spans.  This is the executable
frontier used by the bounded `k = 6` gate. -/
def allocatedExactRankFrontier {n : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn) (rank : ℕ) :
    Finset (SweepSpanEndpoints n) := by
  classical
  exact (allocatedExactRankSpans chi lower upper color rank).filter fun span ↦
    ∀ other ∈ allocatedExactRankSpans chi lower upper color rank,
      span.Contains other → other = span

@[simp] theorem mem_allocatedExactRankFrontier {n rank : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)} {color : Turn}
    {span : SweepSpanEndpoints n} :
    span ∈ allocatedExactRankFrontier chi lower upper color rank ↔
      span ∈ allocatedExactRankSpans chi lower upper color rank ∧
        ∀ other ∈ allocatedExactRankSpans chi lower upper color rank,
          span.Contains other → other = span := by
  simp [allocatedExactRankFrontier]

/-- Two retained spans cannot properly contain one another. -/
theorem allocatedExactRankFrontier_eq_of_contains {n rank : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)} {color : Turn}
    {outer inner : SweepSpanEndpoints n}
    (houter : outer ∈ allocatedExactRankFrontier chi lower upper color rank)
    (hinner : inner ∈ allocatedExactRankFrontier chi lower upper color rank)
    (hcontains : outer.Contains inner) : outer = inner := by
  have houterData := mem_allocatedExactRankFrontier.mp houter
  have hinnerData := mem_allocatedExactRankFrontier.mp hinner
  exact (houterData.2 inner hinnerData.1 hcontains).symm

/-- The left endpoint projection is injective on the retained frontier. -/
theorem allocatedExactRankFrontier_left_injective {n rank : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)} {color : Turn}
    {first second : SweepSpanEndpoints n}
    (hfirst : first ∈ allocatedExactRankFrontier chi lower upper color rank)
    (hsecond : second ∈ allocatedExactRankFrontier chi lower upper color rank)
    (hleft : first.left = second.left) : first = second := by
  rcases le_total first.right second.right with hright | hright
  · symm
    apply allocatedExactRankFrontier_eq_of_contains hsecond hfirst
    exact ⟨hleft.symm.le, hright⟩
  · apply allocatedExactRankFrontier_eq_of_contains hfirst hsecond
    exact ⟨hleft.le, hright⟩

/-- The right endpoint projection is injective on the retained frontier. -/
theorem allocatedExactRankFrontier_right_injective {n rank : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)} {color : Turn}
    {first second : SweepSpanEndpoints n}
    (hfirst : first ∈ allocatedExactRankFrontier chi lower upper color rank)
    (hsecond : second ∈ allocatedExactRankFrontier chi lower upper color rank)
    (hright : first.right = second.right) : first = second := by
  rcases le_total first.left second.left with hleft | hleft
  · apply allocatedExactRankFrontier_eq_of_contains hfirst hsecond
    exact ⟨hleft, hright.symm.le⟩
  · symm
    apply allocatedExactRankFrontier_eq_of_contains hsecond hfirst
    exact ⟨hleft, hright.le⟩

/-- Along the retained frontier, strict increase of left endpoints is exactly
strict increase of right endpoints. -/
theorem allocatedExactRankFrontier_left_lt_iff_right_lt {n rank : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)} {color : Turn}
    {first second : SweepSpanEndpoints n}
    (hfirst : first ∈ allocatedExactRankFrontier chi lower upper color rank)
    (hsecond : second ∈ allocatedExactRankFrontier chi lower upper color rank) :
    first.left < second.left ↔ first.right < second.right := by
  constructor
  · intro hleft
    by_contra hright
    have hcontains : first.Contains second := ⟨hleft.le, by omega⟩
    have heq := allocatedExactRankFrontier_eq_of_contains hfirst hsecond hcontains
    exact (ne_of_lt hleft) (congrArg SweepSpanEndpoints.left heq)
  · intro hright
    by_contra hleft
    have hcontains : second.Contains first := ⟨by omega, hright.le⟩
    have heq := allocatedExactRankFrontier_eq_of_contains hsecond hfirst hcontains
    exact (ne_of_lt hright) (congrArg SweepSpanEndpoints.right heq.symm)

/-- Every retained span in an open context has rank strictly below the
forbidden strong-polygon size. -/
theorem allocatedExactRankFrontier_rank_lt {n rank k : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)} {color : Turn}
    {span : SweepSpanEndpoints n}
    (hspan : span ∈ allocatedExactRankFrontier chi lower upper color rank)
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    rank < k := by
  have hdata := mem_allocatedExactRankSpans.mp
    (mem_allocatedExactRankFrontier.mp hspan).1
  exact hdata.2.lt_of_not_containsStrongPolygonSet hnoStrong

/-- A retained cup span consumes a lower-child cup of size `rank - 1`; in a
no-strong-`k` context this excludes a complementary upper-child cap. -/
theorem allocatedCupExactRankSpan_child_constraints {n rank k : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hspan : span ∈ allocatedExactRankFrontier chi lower upper .left rank)
    (hrank : 1 ≤ rank)
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    ContainsCupSet chi lower (rank - 1) ∧
      ¬ContainsCapSet chi upper (k + 1 - rank) := by
  have hdata := mem_allocatedExactRankSpans.mp
    (mem_allocatedExactRankFrontier.mp hspan).1
  have hcupRank : HasCupSpanRankAtLeast chi (lower ∪ upper)
      span.left span.right rank := by
    simpa [HasExactSpanRank, HasSpanRankAtLeast] using hdata.2.1
  have hcup := hdeep.containsCupSet_pred_of_cupSpanRankAtLeast hdata.1 hcupRank
  refine ⟨hcup, ?_⟩
  intro hcap
  apply hnoStrong
  apply hdeep.containsStrongPolygonSet_of_containsCupCap hcup hcap
  have hrankTop := allocatedExactRankFrontier_rank_lt hspan hnoStrong
  omega

/-- Color-dual child resource and complementary exclusion for a retained cap
span. -/
theorem allocatedCapExactRankSpan_child_constraints {n rank k : ℕ}
    {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hspan : span ∈ allocatedExactRankFrontier chi lower upper .right rank)
    (hrank : 1 ≤ rank)
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    ContainsCapSet chi upper (rank - 1) ∧
      ¬ContainsCupSet chi lower (k + 1 - rank) := by
  have hdata := mem_allocatedExactRankSpans.mp
    (mem_allocatedExactRankFrontier.mp hspan).1
  have hcapRank : HasCapSpanRankAtLeast chi (lower ∪ upper)
      span.left span.right rank := by
    simpa [HasExactSpanRank, HasSpanRankAtLeast] using hdata.2.1
  have hcap := hdeep.containsCapSet_pred_of_capSpanRankAtLeast hdata.1 hcapRank
  refine ⟨hcap, ?_⟩
  intro hcup
  apply hnoStrong
  apply hdeep.containsStrongPolygonSet_of_containsCupCap hcup hcap
  have hrankTop := allocatedExactRankFrontier_rank_lt hspan hnoStrong
  omega

/-- A proposed assignment of every retained exact-rank span to a distinct
`(rank - 1)`-subset of the `k - 2` Pascal coordinates. -/
structure AllocatedExactRankSlotting {n : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn) (rank k : ℕ) where
  slot : {span // span ∈ allocatedExactRankFrontier chi lower upper color rank} →
    {indices : Finset (Fin (k - 2)) // indices.card = rank - 1}
  injective : Function.Injective slot

/-- Constructing the slot injection is sufficient for the desired adjacent
Pascal bound. -/
theorem allocatedExactRankFrontier_card_le_spanPascalDemand_of_slotting
    {n rank k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    (slotting : AllocatedExactRankSlotting chi lower upper color rank k) :
    (allocatedExactRankFrontier chi lower upper color rank).card ≤
      publishedSpanPascalDemand k rank := by
  have hcard := Fintype.card_le_of_injective slotting.slot slotting.injective
  rw [Fintype.card_coe, Fintype.card_finset_len] at hcard
  simpa [publishedSpanPascalDemand] using hcard

end

end ErdosSzekeres

end
