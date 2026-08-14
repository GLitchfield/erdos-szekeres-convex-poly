module

public import ErdosSzekeres.FiniteDilworth
public import ErdosSzekeres.SukAdjacentRegions

@[expose] public section

/-!
# The finite order inside a Suk support region

The paper orders points by containment in triangles with a common base.  This
file proves that relation is a partial order on a finite general-position set
lying strictly on one side of the base, then applies the finite height--width
theorem.  Deriving these hypotheses from a full support remains a later
geometric step.
-/

namespace ErdosSzekeres

noncomputable section

theorem sukRegionLE_refl (outerLeft outerRight p : Point 2) :
    SukRegionLE outerLeft outerRight p p := by
  exact subset_convexHull ℝ (triangle outerLeft outerRight p) (by simp [triangle])

theorem sukRegionLE_trans
    (outerLeft outerRight p q r : Point 2)
    (hpq : SukRegionLE outerLeft outerRight p q)
    (hqr : SukRegionLE outerLeft outerRight q r) :
    SukRegionLE outerLeft outerRight p r := by
  apply convexHull_min _ (convex_convexHull ℝ _) hqr
  intro x hx
  simp only [triangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact subset_convexHull ℝ _ (by simp [triangle])
  · exact subset_convexHull ℝ _ (by simp [triangle])
  · exact hpq

theorem orientation_triangle_sum (a b c p : Point 2) :
    orientation a b c =
      orientation a b p + orientation b c p + orientation c a p := by
  simp only [orientation]
  ring

theorem orientation_base_le_of_sukRegionLE
    {outerLeft outerRight p q : Point 2}
    (hp : 0 < orientation outerLeft outerRight p)
    (hpq : SukRegionLE outerLeft outerRight p q) :
    orientation outerLeft outerRight q ≤ orientation outerLeft outerRight p := by
  have hinside :=
    (mem_convexHull_triangle_iff_of_orientation_pos
      outerLeft outerRight p q hp).mp hpq
  have hsum := orientation_triangle_sum outerLeft outerRight p q
  linarith [hinside.2.1, hinside.2.2]

theorem sukRegionLE_antisymm_on
    {outerLeft outerRight p q : Point 2}
    (hp : 0 < orientation outerLeft outerRight p)
    (hq : 0 < orientation outerLeft outerRight q)
    (hgp : InGeneralPosition {outerLeft, outerRight, p, q})
    (hpq : SukRegionLE outerLeft outerRight p q)
    (hqp : SukRegionLE outerLeft outerRight q p) : p = q := by
  by_contra hpne
  have hrightP : outerRight ≠ p := by
    intro h
    subst p
    simp at hp
  have hrightQ : outerRight ≠ q := by
    intro h
    subst q
    simp at hq
  have hnonzero : orientation outerRight p q ≠ 0 :=
    hgp (by simp) (by simp) (by simp) hrightP hrightQ hpne
  have hinside :=
    (mem_convexHull_triangle_iff_of_orientation_pos
      outerLeft outerRight p q hp).mp hpq
  have hpqHeight := orientation_base_le_of_sukRegionLE hp hpq
  have hqpHeight := orientation_base_le_of_sukRegionLE hq hqp
  have hsum := orientation_triangle_sum outerLeft outerRight p q
  have : orientation outerRight p q = 0 := by
    linarith [hinside.2.1, hinside.2.2]
  exact hnonzero this

/-- The paper's triangle-containment relation, bundled as a partial order on a
finite set in general position lying strictly on one side of its common base.
-/
@[reducible] def sukRegionPartialOrder
    (outerLeft outerRight : Point 2) (s : Finset (Point 2))
    (hside : ∀ p ∈ s, 0 < orientation outerLeft outerRight p)
    (hgp : InGeneralPosition (insert outerLeft (insert outerRight s))) :
    PartialOrder (↥s) where
  le p q := SukRegionLE outerLeft outerRight p q
  lt p q := SukRegionLE outerLeft outerRight p q ∧
    ¬SukRegionLE outerLeft outerRight q p
  le_refl p := sukRegionLE_refl outerLeft outerRight p
  le_trans p q r := sukRegionLE_trans outerLeft outerRight p q r
  le_antisymm p q hpq hqp := by
    apply Subtype.ext
    apply sukRegionLE_antisymm_on (hside p p.property) (hside q q.property)
    · apply hgp.mono
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr p.property)
      · exact Or.inr (Or.inr q.property)
    · exact hpq
    · exact hqp
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- The exact finite Dilworth threshold for Suk's region order. -/
theorem sukRegion_chain_or_antichain
    (outerLeft outerRight : Point 2) (s : Finset (Point 2))
    (hside : ∀ p ∈ s, 0 < orientation outerLeft outerRight p)
    (hgp : InGeneralPosition (insert outerLeft (insert outerRight s)))
    (height width : ℕ) (hcard : height * width < s.card) :
    ∃ t : Finset (↥s),
      (height < t.card ∧
        IsChain (fun p q : ↥s => SukRegionLE outerLeft outerRight p q) t) ∨
      (width < t.card ∧
        IsAntichain (fun p q : ↥s => SukRegionLE outerLeft outerRight p q) t) := by
  letI := sukRegionPartialOrder outerLeft outerRight s hside hgp
  have hunivCard : (Finset.univ : Finset (↥s)).card = s.card := by simp
  obtain ⟨t, -, ht⟩ := finiteDilworth_chain_or_antichain
    (Finset.univ : Finset (↥s)) height width (by simpa [hunivCard] using hcard)
  simpa only [sukRegionPartialOrder] using ⟨t, ht⟩

end

end ErdosSzekeres

end
