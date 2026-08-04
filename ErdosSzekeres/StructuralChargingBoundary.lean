module

public import ErdosSzekeres.StructuralChargingTransport
public import ErdosSzekeres.E3FiniteReduction

@[expose] public section

/-!
# First `k = 6` boundary for structural charging

This file extracts the endpoint-avoidance charge in arbitrary cardinality and
measures its direct consequence at `k = 6`.  Treating the two gap sides
independently with the already proved `(4,6,6)` state yields only 23 vertices,
exposing the precise interaction still missing from the diagonal threshold 16.
-/

namespace ErdosSzekeres

/-- If no cap of size `a` has `q` as a sweep endpoint, neither gap side
contains an `a`-cap. -/
theorem gap_sides_avoid_cap_of_no_endpoint_cap {n a : ℕ}
    {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n}
    (hno : ¬∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = a ∧
      IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q) :
    ¬ContainsCapSet χ (upper.filter (· < q)) a ∧
      ¬ContainsCapSet χ (upper.filter (q < ·)) a := by
  constructor
  · rintro ⟨cap, hcapSub, hcapCard, hcap⟩
    apply hno
    refine ⟨cap, hcapSub.trans (Finset.filter_subset _ _), hcapCard, hcap, Or.inr ?_⟩
    intro x hx
    exact (Finset.mem_filter.mp (hcapSub hx)).2.le
  · rintro ⟨cap, hcapSub, hcapCard, hcap⟩
    apply hno
    refine ⟨cap, hcapSub.trans (Finset.filter_subset _ _), hcapCard, hcap, Or.inl ?_⟩
    intro x hx
    exact (Finset.mem_filter.mp (hcapSub hx)).2.le

/-- The direct endpoint charge at the first `k = 6` boundary yields only a
coarse singleton-root bound of 23 when combined separately with the existing
`(4,6,6)` theorem on the two gap sides. -/
theorem HasDeepBelowSplit.singleton_root_card_le_twenty_three_at_six
    {n : ℕ} {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n}
    (hupper : IsDecomposableOn χ upper)
    (h : HasDeepBelowSplit χ {q} upper)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 6) :
    ({q} ∪ upper).card ≤ 23 := by
  have hq : q ∉ upper := by
    intro hqUpper
    exact (Finset.disjoint_left.mp h.disjoint) (by simp) hqUpper
  let left := upper.filter (· < q)
  let right := upper.filter (q < ·)
  have hnoEndpoint : ¬∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = 4 ∧
      IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q := by
    rintro ⟨cap, hcapSub, hcapCard, hcapSet, hendpoint⟩
    apply hnoCap
    simpa using h.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcapSet (by simp) hendpoint
  have hnoSideCap : ¬ContainsCapSet χ left 4 ∧
      ¬ContainsCapSet χ right 4 :=
    gap_sides_avoid_cap_of_no_endpoint_cap hnoEndpoint
  have hleftSubParent : left ⊆ {q} ∪ upper :=
    (Finset.filter_subset _ _).trans Finset.subset_union_right
  have hrightSubParent : right ⊆ {q} ∪ upper :=
    (Finset.filter_subset _ _).trans Finset.subset_union_right
  have hleftCard : left.card ≤ 11 := by
    by_cases hleftEmpty : left = ∅
    · simp [hleftEmpty]
    have hleftNonempty : left.Nonempty := Finset.nonempty_iff_ne_empty.mpr hleftEmpty
    have hleftDecomposable := hupper.subset (Finset.filter_subset _ _) hleftNonempty
    by_contra hcard
    have hlarge : decomposableThreshold 4 6 6 < left.card := by
      simpa using (show 11 < left.card by omega)
    rcases decomposableStateUpper_466 hleftDecomposable hlarge with
        hcap | hcup | hstrong
    · exact hnoSideCap.1 hcap
    · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hleftSubParent)
    · exact hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hleftSubParent)
  have hrightCard : right.card ≤ 11 := by
    by_cases hrightEmpty : right = ∅
    · simp [hrightEmpty]
    have hrightNonempty : right.Nonempty := Finset.nonempty_iff_ne_empty.mpr hrightEmpty
    have hrightDecomposable := hupper.subset (Finset.filter_subset _ _) hrightNonempty
    by_contra hcard
    have hlarge : decomposableThreshold 4 6 6 < right.card := by
      simpa using (show 11 < right.card by omega)
    rcases decomposableStateUpper_466 hrightDecomposable hlarge with
        hcap | hcup | hstrong
    · exact hnoSideCap.2 hcap
    · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hrightSubParent)
    · exact hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hrightSubParent)
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
  have hupperCard : upper.card ≤ 22 := by
    rw [← hunion, Finset.card_union_of_disjoint hdisjoint]
    omega
  rw [Finset.card_union_of_disjoint h.disjoint]
  simp
  omega

end ErdosSzekeres
