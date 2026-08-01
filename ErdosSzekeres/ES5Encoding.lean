import ErdosSzekeres.ES5Unsat

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace ErdosSzekeres

noncomputable section

/-- The five four-tuple consistency conditions on the ten triples of five
ordered vertices, in lexicographic triple order. -/
def StrongFiveValues (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Turn) : Prop :=
  x0 = x1 ∧ x3 = x6 ∧
  x0 = x2 ∧ x4 = x7 ∧
  x1 = x2 ∧ x5 = x8 ∧
  x3 = x4 ∧ x5 = x9 ∧
  x6 = x7 ∧ x8 = x9

theorem isStrongPolygonOn_finFive_iff {n : ℕ} (χ : TripleColoring n)
    (f : Fin 5 ↪o Fin n) :
    IsStrongPolygonOn χ f ↔
      StrongFiveValues
        (χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 1, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 1, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 1, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 2, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) := by
  constructor
  · intro h
    have h0123 := h (i := 0) (j := 1) (k := 2) (l := 3)
      (by decide) (by decide) (by decide)
    have h0124 := h (i := 0) (j := 1) (k := 2) (l := 4)
      (by decide) (by decide) (by decide)
    have h0134 := h (i := 0) (j := 1) (k := 3) (l := 4)
      (by decide) (by decide) (by decide)
    have h0234 := h (i := 0) (j := 2) (k := 3) (l := 4)
      (by decide) (by decide) (by decide)
    have h1234 := h (i := 1) (j := 2) (k := 3) (l := 4)
      (by decide) (by decide) (by decide)
    exact ⟨h0123.1, h0123.2, h0124.1, h0124.2, h0134.1,
      h0134.2, h0234.1, h0234.2, h1234.1, h1234.2⟩
  · rintro ⟨h0123a, h0123b, h0124a, h0124b, h0134a,
      h0134b, h0234a, h0234b, h1234a, h1234b⟩ i j k l hij hjk hkl
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · have hj : j = 1 ∨ j = 2 := by omega
      rcases hj with rfl | rfl
      · have hk : k = 2 ∨ k = 3 := by omega
        rcases hk with rfl | rfl
        · have hl : l = 3 ∨ l = 4 := by omega
          rcases hl with rfl | rfl
          · exact ⟨h0123a, h0123b⟩
          · exact ⟨h0124a, h0124b⟩
        · have hl : l = 4 := by omega
          subst l
          exact ⟨h0134a, h0134b⟩
      · have hk : k = 3 := by omega
        have hl : l = 4 := by omega
        subst k
        subst l
        exact ⟨h0234a, h0234b⟩
    · have hj : j = 2 := by omega
      have hk : k = 3 := by omega
      have hl : l = 4 := by omega
      subst j
      subst k
      subst l
      exact ⟨h1234a, h1234b⟩

/-- If an allowed four-turn sequence differs from a forbidden target
sequence, at least one of its four entries differs. -/
theorem turnSequence_mismatch {a b c d A B C D : Turn}
    (hallowed : TurnSequenceAllowed a b c d)
    (hforbidden : ¬ TurnSequenceAllowed A B C D) :
    a ≠ A ∨ b ≠ B ∨ c ≠ C ∨ d ≠ D := by
  by_contra h
  push Not at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  exact hforbidden hallowed

/-- If a selected five-set is not strong, it differs from every strong target
assignment on at least one of its ten triple colors. -/
theorem strongFive_mismatch {n : ℕ} (χ : TripleColoring n)
    (f : Fin 5 ↪o Fin n) (hnot : ¬ IsStrongPolygonOn χ f)
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Turn}
    (htarget : StrongFiveValues x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :
    χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x0 ∨
    χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x1 ∨
    χ ⟨f 0, f 1, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x2 ∨
    χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x3 ∨
    χ ⟨f 0, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x4 ∨
    χ ⟨f 0, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x5 ∨
    χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x6 ∨
    χ ⟨f 1, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x7 ∨
    χ ⟨f 1, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x8 ∨
    χ ⟨f 2, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x9 := by
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnot
  rw [isStrongPolygonOn_finFive_iff]
  simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] using htarget

@[simp] theorem Turn.ne_right_iff_eq_left (x : Turn) :
    x ≠ Turn.right ↔ x = Turn.left := by cases x <;> simp

end

end ErdosSzekeres
