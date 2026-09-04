module

public import ErdosSzekeres.ES5Encoding
public import ErdosSzekeres.AnchoredPresentation

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-- The fifteen four-tuple consistency conditions on the twenty triples of
six ordered vertices, in lexicographic triple order. -/
def StrongSixValues (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Turn) : Prop :=
  x0 = x1 ∧
  x4 = x10 ∧
  x0 = x2 ∧
  x5 = x11 ∧
  x0 = x3 ∧
  x6 = x12 ∧
  x1 = x2 ∧
  x7 = x13 ∧
  x1 = x3 ∧
  x8 = x14 ∧
  x2 = x3 ∧
  x9 = x15 ∧
  x4 = x5 ∧
  x7 = x16 ∧
  x4 = x6 ∧
  x8 = x17 ∧
  x5 = x6 ∧
  x9 = x18 ∧
  x7 = x8 ∧
  x9 = x19 ∧
  x10 = x11 ∧
  x13 = x16 ∧
  x10 = x12 ∧
  x14 = x17 ∧
  x11 = x12 ∧
  x15 = x18 ∧
  x13 = x14 ∧
  x15 = x19 ∧
  x16 = x17 ∧
  x18 = x19

theorem isStrongPolygonOn_finSix_iff {n : ℕ} (χ : TripleColoring n)
    (f : Fin 6 ↪o Fin n) :
    IsStrongPolygonOn χ f ↔
      StrongSixValues
        (χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 1, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 1, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 2, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 1, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 1, f 2, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 1, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 1, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 1, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 2, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 2, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 2, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 3, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) := by
  constructor
  · intro h
    have h0123 := h (i := 0) (j := 1) (k := 2) (l := 3)
      (by decide) (by decide) (by decide)
    have h0124 := h (i := 0) (j := 1) (k := 2) (l := 4)
      (by decide) (by decide) (by decide)
    have h0125 := h (i := 0) (j := 1) (k := 2) (l := 5)
      (by decide) (by decide) (by decide)
    have h0134 := h (i := 0) (j := 1) (k := 3) (l := 4)
      (by decide) (by decide) (by decide)
    have h0135 := h (i := 0) (j := 1) (k := 3) (l := 5)
      (by decide) (by decide) (by decide)
    have h0145 := h (i := 0) (j := 1) (k := 4) (l := 5)
      (by decide) (by decide) (by decide)
    have h0234 := h (i := 0) (j := 2) (k := 3) (l := 4)
      (by decide) (by decide) (by decide)
    have h0235 := h (i := 0) (j := 2) (k := 3) (l := 5)
      (by decide) (by decide) (by decide)
    have h0245 := h (i := 0) (j := 2) (k := 4) (l := 5)
      (by decide) (by decide) (by decide)
    have h0345 := h (i := 0) (j := 3) (k := 4) (l := 5)
      (by decide) (by decide) (by decide)
    have h1234 := h (i := 1) (j := 2) (k := 3) (l := 4)
      (by decide) (by decide) (by decide)
    have h1235 := h (i := 1) (j := 2) (k := 3) (l := 5)
      (by decide) (by decide) (by decide)
    have h1245 := h (i := 1) (j := 2) (k := 4) (l := 5)
      (by decide) (by decide) (by decide)
    have h1345 := h (i := 1) (j := 3) (k := 4) (l := 5)
      (by decide) (by decide) (by decide)
    have h2345 := h (i := 2) (j := 3) (k := 4) (l := 5)
      (by decide) (by decide) (by decide)
    exact ⟨h0123.1, h0123.2, h0124.1, h0124.2, h0125.1, h0125.2, h0134.1, h0134.2, h0135.1, h0135.2, h0145.1, h0145.2, h0234.1, h0234.2, h0235.1, h0235.2, h0245.1, h0245.2, h0345.1, h0345.2, h1234.1, h1234.2, h1235.1, h1235.2, h1245.1, h1245.2, h1345.1, h1345.2, h2345.1, h2345.2⟩
  · rintro ⟨h0123a, h0123b, h0124a, h0124b, h0125a, h0125b, h0134a, h0134b, h0135a, h0135b, h0145a, h0145b, h0234a, h0234b, h0235a, h0235b, h0245a, h0245b, h0345a, h0345b, h1234a, h1234b, h1235a, h1235b, h1245a, h1245b, h1345a, h1345b, h2345a, h2345b⟩ i j k l hij hjk hkl
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl
    · have hj : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj with rfl | rfl | rfl
      · have hk : k = 2 ∨ k = 3 ∨ k = 4 := by omega
        rcases hk with rfl | rfl | rfl
        · have hl : l = 3 ∨ l = 4 ∨ l = 5 := by omega
          rcases hl with rfl | rfl | rfl
          · exact ⟨h0123a, h0123b⟩
          · exact ⟨h0124a, h0124b⟩
          · exact ⟨h0125a, h0125b⟩
        · have hl : l = 4 ∨ l = 5 := by omega
          rcases hl with rfl | rfl
          · exact ⟨h0134a, h0134b⟩
          · exact ⟨h0135a, h0135b⟩
        · have hl : l = 5 := by omega
          subst hl
          exact ⟨h0145a, h0145b⟩
      · have hk : k = 3 ∨ k = 4 := by omega
        rcases hk with rfl | rfl
        · have hl : l = 4 ∨ l = 5 := by omega
          rcases hl with rfl | rfl
          · exact ⟨h0234a, h0234b⟩
          · exact ⟨h0235a, h0235b⟩
        · have hl : l = 5 := by omega
          subst hl
          exact ⟨h0245a, h0245b⟩
      · have hk : k = 4 := by omega
        subst hk
        have hl : l = 5 := by omega
        subst hl
        exact ⟨h0345a, h0345b⟩
    · have hj : j = 2 ∨ j = 3 := by omega
      rcases hj with rfl | rfl
      · have hk : k = 3 ∨ k = 4 := by omega
        rcases hk with rfl | rfl
        · have hl : l = 4 ∨ l = 5 := by omega
          rcases hl with rfl | rfl
          · exact ⟨h1234a, h1234b⟩
          · exact ⟨h1235a, h1235b⟩
        · have hl : l = 5 := by omega
          subst hl
          exact ⟨h1245a, h1245b⟩
      · have hk : k = 4 := by omega
        subst hk
        have hl : l = 5 := by omega
        subst hl
        exact ⟨h1345a, h1345b⟩
    · have hj : j = 3 := by omega
      subst hj
      have hk : k = 4 := by omega
      subst hk
      have hl : l = 5 := by omega
      subst hl
      exact ⟨h2345a, h2345b⟩

/-- If a selected six-set is not strong, it differs from every strong target
assignment on at least one of its twenty triple colors. -/
theorem strongSix_mismatch {n : ℕ} (χ : TripleColoring n)
    (f : Fin 6 ↪o Fin n) (hnot : ¬ IsStrongPolygonOn χ f)
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Turn}
    (htarget : StrongSixValues x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) :
    χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x0 ∨
    χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x1 ∨
    χ ⟨f 0, f 1, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x2 ∨
    χ ⟨f 0, f 1, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x3 ∨
    χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x4 ∨
    χ ⟨f 0, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x5 ∨
    χ ⟨f 0, f 2, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x6 ∨
    χ ⟨f 0, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x7 ∨
    χ ⟨f 0, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x8 ∨
    χ ⟨f 0, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x9 ∨
    χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x10 ∨
    χ ⟨f 1, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x11 ∨
    χ ⟨f 1, f 2, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x12 ∨
    χ ⟨f 1, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x13 ∨
    χ ⟨f 1, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x14 ∨
    χ ⟨f 1, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x15 ∨
    χ ⟨f 2, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x16 ∨
    χ ⟨f 2, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x17 ∨
    χ ⟨f 2, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x18 ∨
    χ ⟨f 3, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x19 := by
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  apply hnot
  rw [isStrongPolygonOn_finSix_iff]
  simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19] using htarget

/-- An increasing strong six-embedding witnesses a strong six-set. -/
theorem containsStrongPolygonSet_univ_of_isStrongPolygonOn {n : ℕ}
    {χ : TripleColoring n} {f : Fin 6 ↪o Fin n} (h : IsStrongPolygonOn χ f) :
    ContainsStrongPolygonSet χ Finset.univ 6 :=
  ⟨Finset.univ.image f, Finset.subset_univ _,
    by rw [Finset.card_image_of_injective _ f.injective]; simp,
    FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image h⟩

end ErdosSzekeres

end
