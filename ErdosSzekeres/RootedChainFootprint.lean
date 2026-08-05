module

public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Rooted chain endpoint footprints

The exact singleton transition in `Decomposable` says that an upper vertex
extends a lower cup, and dually a lower vertex extends an upper cap, precisely
at a sweep endpoint.  The unsplit endpoint predicate is a union of two rays,
not one interval.  This file makes the necessary left/right endpoint side an
explicit finite carrier and proves the two rays have the expected order
closure.
-/

namespace ErdosSzekeres

noncomputable section

open HasDeepBelowSplit

/-- Which endpoint of an ordered child chain lies next to a singleton root. -/
inductive SweepEndpointSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- The side-indexed version of the sweep-endpoint predicate. -/
def HasSweepEndpointSide {n : ℕ} (s : Finset (Fin n)) (q : Fin n) :
    SweepEndpointSide → Prop
  | .left => IsLeftSweepEndpoint s q
  | .right => IsRightSweepEndpoint s q

@[simp] theorem hasSweepEndpointSide_left {n : ℕ} (s : Finset (Fin n)) (q : Fin n) :
    HasSweepEndpointSide s q .left ↔ IsLeftSweepEndpoint s q := by
  rfl

@[simp] theorem hasSweepEndpointSide_right {n : ℕ} (s : Finset (Fin n)) (q : Fin n) :
    HasSweepEndpointSide s q .right ↔ IsRightSweepEndpoint s q := by
  rfl

/-- Forgetting the endpoint side recovers the existing two-ray predicate. -/
theorem exists_hasSweepEndpointSide_iff_isSweepEndpoint {n : ℕ}
    (s : Finset (Fin n)) (q : Fin n) :
    (∃ side, HasSweepEndpointSide s q side) ↔ IsSweepEndpoint s q := by
  constructor
  · rintro ⟨side, hside⟩
    cases side with
    | left => exact Or.inl hside
    | right => exact Or.inr hside
  · rintro (hleft | hright)
    · exact ⟨.left, hleft⟩
    · exact ⟨.right, hright⟩

/-- The left-endpoint ray is downward closed in the singleton position. -/
theorem HasSweepEndpointSide.anti_left {n : ℕ} {s : Finset (Fin n)}
    {q r : Fin n} (hr : HasSweepEndpointSide s r .left) (hqr : q ≤ r) :
    HasSweepEndpointSide s q .left := by
  intro x hx
  exact hqr.trans (hr x hx)

/-- The right-endpoint ray is upward closed in the singleton position. -/
theorem HasSweepEndpointSide.mono_right {n : ℕ} {s : Finset (Fin n)}
    {q r : Fin n} (hq : HasSweepEndpointSide s q .right) (hqr : q ≤ r) :
    HasSweepEndpointSide s r .right := by
  intro x hx
  exact (hq x hx).trans hqr

/-- For a genuine external singleton, the two endpoint-side states are disjoint. -/
theorem not_hasSweepEndpointSide_left_and_right {n : ℕ}
    {s : Finset (Fin n)} {q : Fin n} (hs : s.Nonempty) (hq : q ∉ s) :
    ¬(HasSweepEndpointSide s q .left ∧ HasSweepEndpointSide s q .right) := by
  exact not_isLeft_and_isRightSweepEndpoint hs hq

/-- Exact side-indexed form of the upper-singleton/lower-cup transition. -/
theorem insert_upper_isCupSet_iff_exists_endpointSide {n : ℕ}
    {χ : TripleColoring n} {lower upper cup : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper) (hcupSub : cup ⊆ lower)
    (hcup : IsCupSet χ cup) (hcupNonempty : cup.Nonempty)
    {q : Fin n} (hqUpper : q ∈ upper) :
    IsCupSet χ (insert q cup) ↔ ∃ side, HasSweepEndpointSide cup q side := by
  rw [h.insert_upper_isCupSet_iff_isSweepEndpoint
    hcupSub hcup hcupNonempty hqUpper,
    exists_hasSweepEndpointSide_iff_isSweepEndpoint]

/-- Exact side-indexed form of the lower-singleton/upper-cap transition. -/
theorem insert_lower_isCapSet_iff_exists_endpointSide {n : ℕ}
    {χ : TripleColoring n} {lower upper cap : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper) (hcapSub : cap ⊆ upper)
    (hcap : IsCapSet χ cap) (hcapNonempty : cap.Nonempty)
    {q : Fin n} (hqLower : q ∈ lower) :
    IsCapSet χ (insert q cap) ↔ ∃ side, HasSweepEndpointSide cap q side := by
  rw [h.insert_lower_isCapSet_iff_isSweepEndpoint
    hcapSub hcap hcapNonempty hqLower,
    exists_hasSweepEndpointSide_iff_isSweepEndpoint]

/-- Without the side label, successful singleton positions need not be order-convex. -/
theorem sweepEndpoint_two_ray_counterexample :
    let s : Finset (Fin 5) := {1, 3}
    IsSweepEndpoint s 0 ∧ ¬IsSweepEndpoint s 2 ∧ IsSweepEndpoint s 4 := by
  norm_num [IsSweepEndpoint, IsLeftSweepEndpoint, IsRightSweepEndpoint]
  omega

/-- A chain together with its exact left and right endpoints in the ambient sweep order. -/
structure HasSweepSpan {n : ℕ} (chain : Finset (Fin n)) (a b : Fin n) : Prop where
  lt : a < b
  left_mem : a ∈ chain
  right_mem : b ∈ chain
  left_endpoint : HasSweepEndpointSide chain a .left
  right_endpoint : HasSweepEndpointSide chain b .right

/-- The cup component of the endpoint-span footprint, stated by rank thresholds. -/
def HasCupSpanRankAtLeast {n : ℕ} (χ : TripleColoring n) (s : Finset (Fin n))
    (a b : Fin n) (r : ℕ) : Prop :=
  ∃ cup : Finset (Fin n), cup ⊆ s ∧ r ≤ cup.card ∧ IsCupSet χ cup ∧
    HasSweepSpan cup a b

/-- The cap component of the endpoint-span footprint, stated by rank thresholds. -/
def HasCapSpanRankAtLeast {n : ℕ} (χ : TripleColoring n) (s : Finset (Fin n))
    (a b : Fin n) (r : ℕ) : Prop :=
  ∃ cap : Finset (Fin n), cap ⊆ s ∧ r ≤ cap.card ∧ IsCapSet χ cap ∧
    HasSweepSpan cap a b

/-- Once a chain's exact left endpoint is retained, its left-extension state is just one
order comparison. -/
theorem HasSweepSpan.hasEndpointSide_left_iff {n : ℕ} {chain : Finset (Fin n)}
    {a b q : Fin n} (h : HasSweepSpan chain a b) :
    HasSweepEndpointSide chain q .left ↔ q ≤ a := by
  constructor
  · intro hq
    exact hq a h.left_mem
  · intro hqa x hx
    exact hqa.trans (h.left_endpoint x hx)

/-- The right-extension state is likewise determined by the retained right endpoint. -/
theorem HasSweepSpan.hasEndpointSide_right_iff {n : ℕ} {chain : Finset (Fin n)}
    {a b q : Fin n} (h : HasSweepSpan chain a b) :
    HasSweepEndpointSide chain q .right ↔ b ≤ q := by
  constructor
  · intro hq
    exact hq b h.right_mem
  · intro hbq x hx
    exact (h.right_endpoint x hx).trans hbq

/-- Adjoining a new strict left endpoint updates only the left endpoint of a span. -/
theorem HasSweepSpan.insert_left {n : ℕ} {chain : Finset (Fin n)} {a b q : Fin n}
    (h : HasSweepSpan chain a b) (hqa : q < a) :
    HasSweepSpan (insert q chain) q b := by
  refine ⟨hqa.trans h.lt, Finset.mem_insert_self q chain,
    Finset.mem_insert_of_mem h.right_mem, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact hqa.le.trans (h.left_endpoint x hx)
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hqa.trans h.lt).le
    · exact h.right_endpoint x hx

/-- Adjoining a new strict right endpoint updates only the right endpoint of a span. -/
theorem HasSweepSpan.insert_right {n : ℕ} {chain : Finset (Fin n)} {a b q : Fin n}
    (h : HasSweepSpan chain a b) (hbq : b < q) :
    HasSweepSpan (insert q chain) a q := by
  refine ⟨h.lt.trans hbq, Finset.mem_insert_of_mem h.left_mem,
    Finset.mem_insert_self q chain, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (h.lt.trans hbq).le
    · exact h.left_endpoint x hx
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact (h.right_endpoint x hx).trans hbq.le

/-- Span-rank thresholds are monotone under enlargement of the ambient carrier. -/
theorem HasCupSpanRankAtLeast.mono {n : ℕ} {χ : TripleColoring n}
    {s t : Finset (Fin n)} {a b : Fin n} {r : ℕ}
    (h : HasCupSpanRankAtLeast χ s a b r) (hst : s ⊆ t) :
    HasCupSpanRankAtLeast χ t a b r := by
  obtain ⟨cup, hcupSub, hcard, hcup, hspan⟩ := h
  exact ⟨cup, hcupSub.trans hst, hcard, hcup, hspan⟩

/-- Dual monotonicity for cap span ranks. -/
theorem HasCapSpanRankAtLeast.mono {n : ℕ} {χ : TripleColoring n}
    {s t : Finset (Fin n)} {a b : Fin n} {r : ℕ}
    (h : HasCapSpanRankAtLeast χ s a b r) (hst : s ⊆ t) :
    HasCapSpanRankAtLeast χ t a b r := by
  obtain ⟨cap, hcapSub, hcard, hcap, hspan⟩ := h
  exact ⟨cap, hcapSub.trans hst, hcard, hcap, hspan⟩

/-- An upper singleton extends a lower cup span through a new left endpoint. -/
theorem HasCupSpanRankAtLeast.insert_upper_left {n : ℕ}
    {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    {a b q : Fin n} {r : ℕ} (hdeep : HasDeepBelowSplit χ lower upper)
    (h : HasCupSpanRankAtLeast χ lower a b r) (hqUpper : q ∈ upper) (hqa : q < a) :
    HasCupSpanRankAtLeast χ (lower ∪ upper) q b (r + 1) := by
  obtain ⟨cup, hcupSub, hcard, hcup, hspan⟩ := h
  have hqNotCup : q ∉ cup := by
    intro hqCup
    exact (Finset.disjoint_left.mp hdeep.disjoint) (hcupSub hqCup) hqUpper
  refine ⟨insert q cup, ?_, ?_, ?_, hspan.insert_left hqa⟩
  · exact Finset.insert_subset
      (Finset.mem_union_right lower hqUpper) (hcupSub.trans Finset.subset_union_left)
  · rw [Finset.card_insert_of_notMem hqNotCup]
    omega
  · exact hdeep.insert_upper_isCupSet_of_isLeftSweepEndpoint
      hcupSub hcup hqUpper ((hspan.hasEndpointSide_left_iff).2 hqa.le)

/-- An upper singleton extends a lower cup span through a new right endpoint. -/
theorem HasCupSpanRankAtLeast.insert_upper_right {n : ℕ}
    {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    {a b q : Fin n} {r : ℕ} (hdeep : HasDeepBelowSplit χ lower upper)
    (h : HasCupSpanRankAtLeast χ lower a b r) (hqUpper : q ∈ upper) (hbq : b < q) :
    HasCupSpanRankAtLeast χ (lower ∪ upper) a q (r + 1) := by
  obtain ⟨cup, hcupSub, hcard, hcup, hspan⟩ := h
  have hqNotCup : q ∉ cup := by
    intro hqCup
    exact (Finset.disjoint_left.mp hdeep.disjoint) (hcupSub hqCup) hqUpper
  refine ⟨insert q cup, ?_, ?_, ?_, hspan.insert_right hbq⟩
  · exact Finset.insert_subset
      (Finset.mem_union_right lower hqUpper) (hcupSub.trans Finset.subset_union_left)
  · rw [Finset.card_insert_of_notMem hqNotCup]
    omega
  · exact hdeep.insert_upper_isCupSet_of_isRightSweepEndpoint
      hcupSub hcup hqUpper ((hspan.hasEndpointSide_right_iff).2 hbq.le)

/-- Dually, a lower singleton extends an upper cap span through a new left endpoint. -/
theorem HasCapSpanRankAtLeast.insert_lower_left {n : ℕ}
    {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    {a b q : Fin n} {r : ℕ} (hdeep : HasDeepBelowSplit χ lower upper)
    (h : HasCapSpanRankAtLeast χ upper a b r) (hqLower : q ∈ lower) (hqa : q < a) :
    HasCapSpanRankAtLeast χ (lower ∪ upper) q b (r + 1) := by
  obtain ⟨cap, hcapSub, hcard, hcap, hspan⟩ := h
  have hqNotCap : q ∉ cap := by
    intro hqCap
    exact (Finset.disjoint_left.mp hdeep.disjoint) hqLower (hcapSub hqCap)
  refine ⟨insert q cap, ?_, ?_, ?_, hspan.insert_left hqa⟩
  · exact Finset.insert_subset
      (Finset.mem_union_left upper hqLower) (hcapSub.trans Finset.subset_union_right)
  · rw [Finset.card_insert_of_notMem hqNotCap]
    omega
  · exact hdeep.insert_lower_isCapSet_of_isLeftSweepEndpoint
      hcapSub hcap hqLower ((hspan.hasEndpointSide_left_iff).2 hqa.le)

/-- Dually, a lower singleton extends an upper cap span through a new right endpoint. -/
theorem HasCapSpanRankAtLeast.insert_lower_right {n : ℕ}
    {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    {a b q : Fin n} {r : ℕ} (hdeep : HasDeepBelowSplit χ lower upper)
    (h : HasCapSpanRankAtLeast χ upper a b r) (hqLower : q ∈ lower) (hbq : b < q) :
    HasCapSpanRankAtLeast χ (lower ∪ upper) a q (r + 1) := by
  obtain ⟨cap, hcapSub, hcard, hcap, hspan⟩ := h
  have hqNotCap : q ∉ cap := by
    intro hqCap
    exact (Finset.disjoint_left.mp hdeep.disjoint) hqLower (hcapSub hqCap)
  refine ⟨insert q cap, ?_, ?_, ?_, hspan.insert_right hbq⟩
  · exact Finset.insert_subset
      (Finset.mem_union_left upper hqLower) (hcapSub.trans Finset.subset_union_right)
  · rw [Finset.card_insert_of_notMem hqNotCap]
    omega
  · exact hdeep.insert_lower_isCapSet_of_isRightSweepEndpoint
      hcapSub hcap hqLower ((hspan.hasEndpointSide_right_iff).2 hbq.le)

/-- Removing the upper singleton from a parent set leaves exactly its lower intersection. -/
theorem HasDeepBelowSplit.erase_eq_inter_lower_of_upper_singleton {n : ℕ}
    {χ : TripleColoring n} {lower upper s : Finset (Fin n)} {q : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper) (hupper : upper = {q})
    (hsub : s ⊆ lower ∪ upper) : s.erase q = s ∩ lower := by
  have hqUpper : q ∈ upper := by simp [hupper]
  ext x
  constructor
  · intro hx
    have hxData := Finset.mem_erase.mp hx
    refine Finset.mem_inter.mpr ⟨hxData.2, ?_⟩
    rcases Finset.mem_union.mp (hsub hxData.2) with hxLower | hxUpper
    · exact hxLower
    · have hxq : x = q := by simpa [hupper] using hxUpper
      exact (hxData.1 hxq).elim
  · intro hx
    have hxData := Finset.mem_inter.mp hx
    refine Finset.mem_erase.mpr ⟨?_, hxData.1⟩
    intro hxq
    exact (Finset.disjoint_left.mp hdeep.disjoint) hxData.2 (hxq ▸ hqUpper)

/-- Removing the lower singleton dually leaves exactly the upper intersection. -/
theorem HasDeepBelowSplit.erase_eq_inter_upper_of_lower_singleton {n : ℕ}
    {χ : TripleColoring n} {lower upper s : Finset (Fin n)} {q : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper) (hlower : lower = {q})
    (hsub : s ⊆ lower ∪ upper) : s.erase q = s ∩ upper := by
  have hqLower : q ∈ lower := by simp [hlower]
  ext x
  constructor
  · intro hx
    have hxData := Finset.mem_erase.mp hx
    refine Finset.mem_inter.mpr ⟨hxData.2, ?_⟩
    rcases Finset.mem_union.mp (hsub hxData.2) with hxLower | hxUpper
    · have hxq : x = q := by simpa [hlower] using hxLower
      exact (hxData.1 hxq).elim
    · exact hxUpper
  · intro hx
    have hxData := Finset.mem_inter.mp hx
    refine Finset.mem_erase.mpr ⟨?_, hxData.1⟩
    intro hxq
    exact (Finset.disjoint_left.mp hdeep.disjoint) (hxq ▸ hqLower) hxData.2

/-- Complete active-color witness transition for an upper singleton: erase the root, then
test the child cup and the endpoint side. -/
theorem HasDeepBelowSplit.upper_singleton_isCupSet_iff_erase {n : ℕ}
    {χ : TripleColoring n} {lower upper cup : Finset (Fin n)} {q : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper) (hupper : upper = {q})
    (hcupSub : cup ⊆ lower ∪ upper) (hqCup : q ∈ cup) (hcard : 2 ≤ cup.card) :
    IsCupSet χ cup ↔
      IsCupSet χ (cup.erase q) ∧ ∃ side, HasSweepEndpointSide (cup.erase q) q side := by
  have hqUpper : q ∈ upper := by simp [hupper]
  have heraseSub : cup.erase q ⊆ lower := by
    rw [hdeep.erase_eq_inter_lower_of_upper_singleton hupper hcupSub]
    exact Finset.inter_subset_right
  have heraseNonempty : (cup.erase q).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hqCup]
    omega
  have hinsert : insert q (cup.erase q) = cup := Finset.insert_erase hqCup
  constructor
  · intro hcup
    have heraseCup := FinsetPolygon.IsCupSet.mono hcup (Finset.erase_subset q cup)
    refine ⟨heraseCup, ?_⟩
    apply (insert_upper_isCupSet_iff_exists_endpointSide hdeep
      heraseSub heraseCup heraseNonempty hqUpper).mp
    simpa [hinsert] using hcup
  · rintro ⟨heraseCup, hside⟩
    have := (insert_upper_isCupSet_iff_exists_endpointSide hdeep
      heraseSub heraseCup heraseNonempty hqUpper).mpr hside
    simpa [hinsert] using this

/-- Complete active-color witness transition for a lower singleton and an upper cap. -/
theorem HasDeepBelowSplit.lower_singleton_isCapSet_iff_erase {n : ℕ}
    {χ : TripleColoring n} {lower upper cap : Finset (Fin n)} {q : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper) (hlower : lower = {q})
    (hcapSub : cap ⊆ lower ∪ upper) (hqCap : q ∈ cap) (hcard : 2 ≤ cap.card) :
    IsCapSet χ cap ↔
      IsCapSet χ (cap.erase q) ∧ ∃ side, HasSweepEndpointSide (cap.erase q) q side := by
  have hqLower : q ∈ lower := by simp [hlower]
  have heraseSub : cap.erase q ⊆ upper := by
    rw [hdeep.erase_eq_inter_upper_of_lower_singleton hlower hcapSub]
    exact Finset.inter_subset_right
  have heraseNonempty : (cap.erase q).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hqCap]
    omega
  have hinsert : insert q (cap.erase q) = cap := Finset.insert_erase hqCap
  constructor
  · intro hcap
    have heraseCap := FinsetPolygon.IsCapSet.mono hcap (Finset.erase_subset q cap)
    refine ⟨heraseCap, ?_⟩
    apply (insert_lower_isCapSet_iff_exists_endpointSide hdeep
      heraseSub heraseCap heraseNonempty hqLower).mp
    simpa [hinsert] using hcap
  · rintro ⟨heraseCap, hside⟩
    have := (insert_lower_isCapSet_iff_exists_endpointSide hdeep
      heraseSub heraseCap heraseNonempty hqLower).mpr hside
    simpa [hinsert] using this

/-- The opposite-color contribution of an upper singleton is confined to rank three. -/
theorem HasDeepBelowSplit.upper_singleton_cap_card_le_three {n : ℕ}
    {χ : TripleColoring n} {lower upper cap : Finset (Fin n)} {q : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper) (hupper : upper = {q})
    (hcapSub : cap ⊆ lower ∪ upper) (hcap : IsCapSet χ cap) (hqCap : q ∈ cap) :
    cap.card ≤ 3 := by
  have hqUpper : q ∈ upper := by simp [hupper]
  have hupperNonempty : (cap ∩ upper).Nonempty :=
    ⟨q, Finset.mem_inter.mpr ⟨hqCap, hqUpper⟩⟩
  have hlowerCard := hdeep.cap_inter_lower_card_le_two hcapSub hcap hupperNonempty
  have herase := hdeep.erase_eq_inter_lower_of_upper_singleton hupper hcapSub
  rw [← herase, Finset.card_erase_of_mem hqCap] at hlowerCard
  omega

/-- The opposite-color contribution of a lower singleton is likewise confined to rank three. -/
theorem HasDeepBelowSplit.lower_singleton_cup_card_le_three {n : ℕ}
    {χ : TripleColoring n} {lower upper cup : Finset (Fin n)} {q : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper) (hlower : lower = {q})
    (hcupSub : cup ⊆ lower ∪ upper) (hcup : IsCupSet χ cup) (hqCup : q ∈ cup) :
    cup.card ≤ 3 := by
  have hqLower : q ∈ lower := by simp [hlower]
  have hlowerNonempty : (cup ∩ lower).Nonempty :=
    ⟨q, Finset.mem_inter.mpr ⟨hqCup, hqLower⟩⟩
  have hupperCard := hdeep.cup_inter_upper_card_le_two hcupSub hcup hlowerNonempty
  have herase := hdeep.erase_eq_inter_upper_of_lower_singleton hlower hcupSub
  rw [← herase, Finset.card_erase_of_mem hqCup] at hupperCard
  omega

/-- Terminal transition for an upper singleton: a parent strong `k`-set is inherited or
comes from a lower `(k-1)`-cup together with the root. -/
theorem HasDeepBelowSplit.upper_singleton_containsStrongPolygonSet_iff {n k : ℕ}
    {χ : TripleColoring n} {lower upper : Finset (Fin n)} {q : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper) (hupper : upper = {q}) (hk : 1 ≤ k) :
    ContainsStrongPolygonSet χ (lower ∪ upper) k ↔
      ContainsStrongPolygonSet χ lower k ∨ ContainsCupSet χ lower (k - 1) := by
  have hqUpper : q ∈ upper := by simp [hupper]
  constructor
  · rintro ⟨polygon, hpolygonSub, hcard, hstrong⟩
    by_cases hqPolygon : q ∈ polygon
    · right
      refine ⟨polygon.erase q, ?_, ?_, ?_⟩
      · rw [hdeep.erase_eq_inter_lower_of_upper_singleton hupper hpolygonSub]
        exact Finset.inter_subset_right
      · rw [Finset.card_erase_of_mem hqPolygon, hcard]
      · have hupperNonempty : (polygon ∩ upper).Nonempty :=
          ⟨q, Finset.mem_inter.mpr ⟨hqPolygon, hqUpper⟩⟩
        have hcup := hdeep.strong_inter_lower_isCupSet
          hpolygonSub hstrong hupperNonempty
        rwa [hdeep.erase_eq_inter_lower_of_upper_singleton hupper hpolygonSub]
    · left
      refine ⟨polygon, ?_, hcard, hstrong⟩
      intro x hx
      rcases Finset.mem_union.mp (hpolygonSub hx) with hxLower | hxUpper
      · exact hxLower
      · have hxq : x = q := by simpa [hupper] using hxUpper
        exact (hqPolygon (hxq ▸ hx)).elim
  · rintro (⟨polygon, hpolygonSub, hcard, hstrong⟩ | ⟨cup, hcupSub, hcard, hcup⟩)
    · exact ⟨polygon, hpolygonSub.trans Finset.subset_union_left, hcard, hstrong⟩
    · have hsingletonSub : ({q} : Finset (Fin n)) ⊆ upper := by simp [hupper]
      have hsingletonCap : IsCapSet χ ({q} : Finset (Fin n)) := by
        intro t hi hj hk
        simp only [Finset.mem_singleton] at hi hj hk
        exact ((ne_of_lt t.hij) (hi.trans hj.symm)).elim
      apply hdeep.containsStrongPolygonSet_of_cup_cap
        hcupSub hsingletonSub hcup hsingletonCap
      simp [hcard]
      omega

/-- Dual terminal transition for a lower singleton and an upper `(k-1)`-cap. -/
theorem HasDeepBelowSplit.lower_singleton_containsStrongPolygonSet_iff {n k : ℕ}
    {χ : TripleColoring n} {lower upper : Finset (Fin n)} {q : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper) (hlower : lower = {q}) (hk : 1 ≤ k) :
    ContainsStrongPolygonSet χ (lower ∪ upper) k ↔
      ContainsStrongPolygonSet χ upper k ∨ ContainsCapSet χ upper (k - 1) := by
  have hqLower : q ∈ lower := by simp [hlower]
  constructor
  · rintro ⟨polygon, hpolygonSub, hcard, hstrong⟩
    by_cases hqPolygon : q ∈ polygon
    · right
      refine ⟨polygon.erase q, ?_, ?_, ?_⟩
      · rw [hdeep.erase_eq_inter_upper_of_lower_singleton hlower hpolygonSub]
        exact Finset.inter_subset_right
      · rw [Finset.card_erase_of_mem hqPolygon, hcard]
      · have hlowerNonempty : (polygon ∩ lower).Nonempty :=
          ⟨q, Finset.mem_inter.mpr ⟨hqPolygon, hqLower⟩⟩
        have hcap := hdeep.strong_inter_upper_isCapSet
          hpolygonSub hstrong hlowerNonempty
        rwa [hdeep.erase_eq_inter_upper_of_lower_singleton hlower hpolygonSub]
    · left
      refine ⟨polygon, ?_, hcard, hstrong⟩
      intro x hx
      rcases Finset.mem_union.mp (hpolygonSub hx) with hxLower | hxUpper
      · have hxq : x = q := by simpa [hlower] using hxLower
        exact (hqPolygon (hxq ▸ hx)).elim
      · exact hxUpper
  · rintro (⟨polygon, hpolygonSub, hcard, hstrong⟩ | ⟨cap, hcapSub, hcard, hcap⟩)
    · exact ⟨polygon, hpolygonSub.trans Finset.subset_union_right, hcard, hstrong⟩
    · have hsingletonSub : ({q} : Finset (Fin n)) ⊆ lower := by simp [hlower]
      have hsingletonCup : IsCupSet χ ({q} : Finset (Fin n)) := by
        intro t hi hj hk
        simp only [Finset.mem_singleton] at hi hj hk
        exact ((ne_of_lt t.hij) (hi.trans hj.symm)).elim
      apply hdeep.containsStrongPolygonSet_of_cup_cap
        hsingletonSub hcapSub hsingletonCup hcap
      simp [hcard]
      omega

end

end ErdosSzekeres
