module

public import ErdosSzekeres.ES5Encoding
public import ErdosSzekeres.E3State455Unsat

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace ErdosSzekeres

noncomputable section

def E3State455CapFourValues (x0 x1 x2 x3 : Turn) : Prop :=
  x0 = Turn.right ∧
  x1 = Turn.right ∧
  x2 = Turn.right ∧
  x3 = Turn.right

theorem e3State455_isCap_finFour_iff {n : ℕ} (χ : TripleColoring n)
    (f : Fin 4 ↪o Fin n) :
    IsCap χ f ↔
      E3State455CapFourValues
        (χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩)
        (χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) := by
  constructor
  · rintro ⟨_, h⟩
    exact ⟨h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide)⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨f.strictMono, ?_⟩
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk <;> simp_all

def E3State455CupFiveValues (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Turn) : Prop :=
  x0 = Turn.left ∧
  x1 = Turn.left ∧
  x2 = Turn.left ∧
  x3 = Turn.left ∧
  x4 = Turn.left ∧
  x5 = Turn.left ∧
  x6 = Turn.left ∧
  x7 = Turn.left ∧
  x8 = Turn.left ∧
  x9 = Turn.left

theorem e3State455_isCup_finFive_iff {n : ℕ} (χ : TripleColoring n)
    (f : Fin 5 ↪o Fin n) :
    IsCup χ f ↔
      E3State455CupFiveValues
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
  · rintro ⟨_, h⟩
    exact ⟨h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    refine ⟨f.strictMono, ?_⟩
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk <;> simp_all

def E3State455StrongFiveValues (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Turn) : Prop :=
  x0 = x1 ∧
  x3 = x6 ∧
  x0 = x2 ∧
  x4 = x7 ∧
  x1 = x2 ∧
  x5 = x8 ∧
  x3 = x4 ∧
  x5 = x9 ∧
  x6 = x7 ∧
  x8 = x9

theorem e3State455_isStrongPolygonOn_finFive_iff {n : ℕ} (χ : TripleColoring n)
    (f : Fin 5 ↪o Fin n) :
    IsStrongPolygonOn χ f ↔
      E3State455StrongFiveValues
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
    exact ⟨(by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 2) (l := 3) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 2) (l := 3) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 2) (l := 4) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 2) (l := 4) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 3) (l := 4) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 3) (l := 4) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 2) (k := 3) (l := 4) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 2) (k := 3) (l := 4) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 1) (j := 2) (k := 3) (l := 4) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 1) (j := 2) (k := 3) (l := 4) (by decide) (by decide) (by decide)).2)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    intro i j k l hij hjk hkl
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [TripleColoring.restrict, OrderedTriple.map] at hij hjk hkl ⊢ <;> simp_all

theorem e3State455_capFour_mismatch {n : ℕ} (χ : TripleColoring n)
    (f : Fin 4 ↪o Fin n) (hnot : ¬ IsCap χ f)
    {x0 x1 x2 x3 : Turn}
    (htarget : E3State455CapFourValues x0 x1 x2 x3) :
    (χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x0 ∨
    (χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x1 ∨
    (χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x2 ∨
    (χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x3 := by
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  apply hnot
  rw [e3State455_isCap_finFour_iff]
  simpa [h0, h1, h2, h3] using htarget

theorem e3State455_cupFive_mismatch {n : ℕ} (χ : TripleColoring n)
    (f : Fin 5 ↪o Fin n) (hnot : ¬ IsCup χ f)
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Turn}
    (htarget : E3State455CupFiveValues x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :
    (χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x0 ∨
    (χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x1 ∨
    (χ ⟨f 0, f 1, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x2 ∨
    (χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x3 ∨
    (χ ⟨f 0, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x4 ∨
    (χ ⟨f 0, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x5 ∨
    (χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x6 ∨
    (χ ⟨f 1, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x7 ∨
    (χ ⟨f 1, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x8 ∨
    (χ ⟨f 2, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x9 := by
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnot
  rw [e3State455_isCup_finFive_iff]
  simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] using htarget

theorem e3State455_strongFive_mismatch {n : ℕ} (χ : TripleColoring n)
    (f : Fin 5 ↪o Fin n) (hnot : ¬ IsStrongPolygonOn χ f)
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Turn}
    (htarget : E3State455StrongFiveValues x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :
    (χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x0 ∨
    (χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x1 ∨
    (χ ⟨f 0, f 1, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x2 ∨
    (χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x3 ∨
    (χ ⟨f 0, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x4 ∨
    (χ ⟨f 0, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x5 ∨
    (χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x6 ∨
    (χ ⟨f 1, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x7 ∨
    (χ ⟨f 1, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x8 ∨
    (χ ⟨f 2, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x9 := by
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnot
  rw [e3State455_isStrongPolygonOn_finFive_iff]
  simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] using htarget

end

end ErdosSzekeres

end
