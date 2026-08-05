module

public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Color duality for abstract order types

This certificate-free module records the elementary symmetry exchanging cups
and caps.  It is deliberately independent of the finite E3 certificates so
structural arguments can use duality without inheriting an enumeration
dependency.
-/

namespace ErdosSzekeres

namespace Turn

/-- Exchange the two colors of a triple coloring. -/
def dual : Turn → Turn
  | .left => .right
  | .right => .left

@[simp] theorem dual_left : dual .left = .right := rfl

@[simp] theorem dual_right : dual .right = .left := rfl

@[simp] theorem dual_dual (c : Turn) : dual (dual c) = c := by
  cases c <;> rfl

theorem dual_injective : Function.Injective dual := by
  intro a b hab
  simpa only [dual_dual] using congrArg dual hab

end Turn

namespace TripleColoring

/-- Pointwise color duality. -/
def dual {n : ℕ} (χ : TripleColoring n) : TripleColoring n :=
  fun t => Turn.dual (χ t)

@[simp] theorem dual_apply {n : ℕ} (χ : TripleColoring n)
    (t : OrderedTriple n) : χ.dual t = Turn.dual (χ t) := rfl

end TripleColoring

/-- Color duality exchanges the two sides of a deep-below split. -/
theorem HasDeepBelowSplit.dual {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)} (h : HasDeepBelowSplit χ lower upper) :
    HasDeepBelowSplit χ.dual upper lower := by
  refine ⟨h.disjoint.symm, ?_⟩
  intro t hi hj hk hnotUpper hnotLower
  have hi' : t.i ∈ lower ∪ upper := by simpa [Finset.union_comm] using hi
  have hj' : t.j ∈ lower ∪ upper := by simpa [Finset.union_comm] using hj
  have hk' : t.k ∈ lower ∪ upper := by simpa [Finset.union_comm] using hk
  have hcolor := h.crossing t hi' hj' hk' hnotLower hnotUpper
  have hdisjoint := Finset.disjoint_left.mp h.disjoint
  by_cases hjLower : t.j ∈ lower
  · have hjNotUpper : t.j ∉ upper := fun hjUpper => hdisjoint hjLower hjUpper
    simp [TripleColoring.dual, hcolor, hjLower, hjNotUpper, Turn.dual]
  · have hjUpper : t.j ∈ upper := by
      rcases Finset.mem_union.mp hj' with hmem | hmem
      · exact (hjLower hmem).elim
      · exact hmem
    simp [TripleColoring.dual, hcolor, hjLower, hjUpper, Turn.dual]

/-- Recursive decomposability is invariant under color duality. -/
theorem IsDecomposableOn.dual {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} (h : IsDecomposableOn χ s) :
    IsDecomposableOn χ.dual s := by
  induction h with
  | singleton i => exact .singleton i
  | @split lower upper hlower hupper hdeep ihlower ihupper =>
      simpa [Finset.union_comm] using
        IsDecomposableOn.split ihupper ihlower hdeep.dual

/-- Cups for the dual coloring are caps for the original coloring. -/
theorem isCupSet_dual_iff {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} : IsCupSet χ.dual s ↔ IsCapSet χ s := by
  constructor <;> intro h t hi hj hk
  · have ht := h t hi hj hk
    cases hχ : χ t <;> simp_all [TripleColoring.dual, Turn.dual]
  · simp [TripleColoring.dual, Turn.dual, h t hi hj hk]

/-- Caps for the dual coloring are cups for the original coloring. -/
theorem isCapSet_dual_iff {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} : IsCapSet χ.dual s ↔ IsCupSet χ s := by
  constructor <;> intro h t hi hj hk
  · have ht := h t hi hj hk
    cases hχ : χ t <;> simp_all [TripleColoring.dual, Turn.dual]
  · simp [TripleColoring.dual, Turn.dual, h t hi hj hk]

/-- The strong-polygon law is invariant under exchanging its two colors. -/
theorem isStrongPolygonSet_dual_iff {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} :
    IsStrongPolygonSet χ.dual s ↔ IsStrongPolygonSet χ s := by
  constructor
  · intro h i j k l hij hjk hkl hi hj hk hl
    obtain ⟨h₁, h₂⟩ := h hij hjk hkl hi hj hk hl
    exact ⟨Turn.dual_injective h₁, Turn.dual_injective h₂⟩
  · intro h i j k l hij hjk hkl hi hj hk hl
    obtain ⟨h₁, h₂⟩ := h hij hjk hkl hi hj hk hl
    exact ⟨congrArg Turn.dual h₁, congrArg Turn.dual h₂⟩

theorem containsCupSet_dual_iff {n u : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} : ContainsCupSet χ.dual s u ↔ ContainsCapSet χ s u := by
  constructor
  · rintro ⟨cup, hsub, hcard, hcup⟩
    exact ⟨cup, hsub, hcard, isCupSet_dual_iff.mp hcup⟩
  · rintro ⟨cap, hsub, hcard, hcap⟩
    exact ⟨cap, hsub, hcard, isCupSet_dual_iff.mpr hcap⟩

theorem containsCapSet_dual_iff {n a : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} : ContainsCapSet χ.dual s a ↔ ContainsCupSet χ s a := by
  constructor
  · rintro ⟨cap, hsub, hcard, hcap⟩
    exact ⟨cap, hsub, hcard, isCapSet_dual_iff.mp hcap⟩
  · rintro ⟨cup, hsub, hcard, hcup⟩
    exact ⟨cup, hsub, hcard, isCapSet_dual_iff.mpr hcup⟩

theorem containsStrongPolygonSet_dual_iff {n k : ℕ}
    {χ : TripleColoring n} {s : Finset (Fin n)} :
    ContainsStrongPolygonSet χ.dual s k ↔ ContainsStrongPolygonSet χ s k := by
  constructor
  · rintro ⟨polygon, hsub, hcard, hstrong⟩
    exact ⟨polygon, hsub, hcard, isStrongPolygonSet_dual_iff.mp hstrong⟩
  · rintro ⟨polygon, hsub, hcard, hstrong⟩
    exact ⟨polygon, hsub, hcard, isStrongPolygonSet_dual_iff.mpr hstrong⟩

end ErdosSzekeres
