module

public import ErdosSzekeres.ES5Encoding
public import ErdosSzekeres.E3State466Unsat

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace ErdosSzekeres

noncomputable section

def CapFourValues (x0 x1 x2 x3 : Turn) : Prop :=
  x0 = Turn.right ∧
  x1 = Turn.right ∧
  x2 = Turn.right ∧
  x3 = Turn.right

theorem isCap_finFour_iff {n : ℕ} (χ : TripleColoring n)
    (f : Fin 4 ↪o Fin n) :
    IsCap χ f ↔
      CapFourValues
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

def CupSixValues (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Turn) : Prop :=
  x0 = Turn.left ∧
  x1 = Turn.left ∧
  x2 = Turn.left ∧
  x3 = Turn.left ∧
  x4 = Turn.left ∧
  x5 = Turn.left ∧
  x6 = Turn.left ∧
  x7 = Turn.left ∧
  x8 = Turn.left ∧
  x9 = Turn.left ∧
  x10 = Turn.left ∧
  x11 = Turn.left ∧
  x12 = Turn.left ∧
  x13 = Turn.left ∧
  x14 = Turn.left ∧
  x15 = Turn.left ∧
  x16 = Turn.left ∧
  x17 = Turn.left ∧
  x18 = Turn.left ∧
  x19 = Turn.left

theorem isCup_finSix_iff {n : ℕ} (χ : TripleColoring n)
    (f : Fin 6 ↪o Fin n) :
    IsCup χ f ↔
      CupSixValues
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
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide),
      h (by decide) (by decide)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
    refine ⟨f.strictMono, ?_⟩
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk <;> simp_all

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
    exact ⟨(by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 2) (l := 3) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 2) (l := 3) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 2) (l := 4) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 2) (l := 4) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 2) (l := 5) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 2) (l := 5) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 3) (l := 4) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 3) (l := 4) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 3) (l := 5) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 3) (l := 5) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 4) (l := 5) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 1) (k := 4) (l := 5) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 2) (k := 3) (l := 4) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 2) (k := 3) (l := 4) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 2) (k := 3) (l := 5) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 2) (k := 3) (l := 5) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 2) (k := 4) (l := 5) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 2) (k := 4) (l := 5) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 3) (k := 4) (l := 5) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 0) (j := 3) (k := 4) (l := 5) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 1) (j := 2) (k := 3) (l := 4) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 1) (j := 2) (k := 3) (l := 4) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 1) (j := 2) (k := 3) (l := 5) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 1) (j := 2) (k := 3) (l := 5) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 1) (j := 2) (k := 4) (l := 5) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 1) (j := 2) (k := 4) (l := 5) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 1) (j := 3) (k := 4) (l := 5) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 1) (j := 3) (k := 4) (l := 5) (by decide) (by decide) (by decide)).2),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 2) (j := 3) (k := 4) (l := 5) (by decide) (by decide) (by decide)).1),
      (by simpa [TripleColoring.restrict, OrderedTriple.map] using (h (i := 2) (j := 3) (k := 4) (l := 5) (by decide) (by decide) (by decide)).2)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
    intro i j k l hij hjk hkl
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [TripleColoring.restrict, OrderedTriple.map] at hij hjk hkl ⊢ <;> simp_all

theorem capFour_mismatch {n : ℕ} (χ : TripleColoring n)
    (f : Fin 4 ↪o Fin n) (hnot : ¬ IsCap χ f)
    {x0 x1 x2 x3 : Turn}
    (htarget : CapFourValues x0 x1 x2 x3) :
    (χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x0 ∨
    (χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x1 ∨
    (χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x2 ∨
    (χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x3 := by
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  apply hnot
  rw [isCap_finFour_iff]
  simpa [h0, h1, h2, h3] using htarget

theorem cupSix_mismatch {n : ℕ} (χ : TripleColoring n)
    (f : Fin 6 ↪o Fin n) (hnot : ¬ IsCup χ f)
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Turn}
    (htarget : CupSixValues x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) :
    (χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x0 ∨
    (χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x1 ∨
    (χ ⟨f 0, f 1, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x2 ∨
    (χ ⟨f 0, f 1, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x3 ∨
    (χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x4 ∨
    (χ ⟨f 0, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x5 ∨
    (χ ⟨f 0, f 2, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x6 ∨
    (χ ⟨f 0, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x7 ∨
    (χ ⟨f 0, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x8 ∨
    (χ ⟨f 0, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x9 ∨
    (χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x10 ∨
    (χ ⟨f 1, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x11 ∨
    (χ ⟨f 1, f 2, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x12 ∨
    (χ ⟨f 1, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x13 ∨
    (χ ⟨f 1, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x14 ∨
    (χ ⟨f 1, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x15 ∨
    (χ ⟨f 2, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x16 ∨
    (χ ⟨f 2, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x17 ∨
    (χ ⟨f 2, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x18 ∨
    (χ ⟨f 3, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x19 := by
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  apply hnot
  rw [isCup_finSix_iff]
  simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19] using htarget

theorem strongSix_mismatch {n : ℕ} (χ : TripleColoring n)
    (f : Fin 6 ↪o Fin n) (hnot : ¬ IsStrongPolygonOn χ f)
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : Turn}
    (htarget : StrongSixValues x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) :
    (χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x0 ∨
    (χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x1 ∨
    (χ ⟨f 0, f 1, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x2 ∨
    (χ ⟨f 0, f 1, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x3 ∨
    (χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x4 ∨
    (χ ⟨f 0, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x5 ∨
    (χ ⟨f 0, f 2, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x6 ∨
    (χ ⟨f 0, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x7 ∨
    (χ ⟨f 0, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x8 ∨
    (χ ⟨f 0, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x9 ∨
    (χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x10 ∨
    (χ ⟨f 1, f 2, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x11 ∨
    (χ ⟨f 1, f 2, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x12 ∨
    (χ ⟨f 1, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x13 ∨
    (χ ⟨f 1, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x14 ∨
    (χ ⟨f 1, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x15 ∨
    (χ ⟨f 2, f 3, f 4, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x16 ∨
    (χ ⟨f 2, f 3, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x17 ∨
    (χ ⟨f 2, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x18 ∨
    (χ ⟨f 3, f 4, f 5, f.strictMono (by decide), f.strictMono (by decide)⟩) ≠ x19 := by
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  apply hnot
  rw [isStrongPolygonOn_finSix_iff]
  simpa [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19] using htarget

end

end ErdosSzekeres

end
