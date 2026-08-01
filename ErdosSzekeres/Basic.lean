import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Basic Erdős--Szekeres definitions

This file fixes a direct Euclidean vocabulary for the project.  It deliberately
does not identify this model with the ordered-configuration model used in much
of the modern literature; proving that bridge is a future formal milestone.
-/

namespace ErdosSzekeres

/-- A point in real affine `d`-space, represented by its coordinates. -/
abbrev Point (d : ℕ) := Fin d → ℝ

/-- The signed twice-area of the oriented triangle `abc`. -/
def orientation (a b c : Point 2) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- No three distinct points of a finite planar set are collinear. -/
def InGeneralPosition (s : Finset (Point 2)) : Prop :=
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s →
    a ≠ b → a ≠ c → b ≠ c → orientation a b c ≠ 0

/-- Every point is outside the convex hull of the remaining points. -/
def InConvexPosition {d : ℕ} (s : Finset (Point d)) : Prop :=
  ∀ p ∈ s, p ∉ convexHull ℝ (↑(s.erase p) : Set (Point d))

/-- `s` contains exactly `n` of its points in convex position. -/
def ContainsConvexSubset (s : Finset (Point 2)) (n : ℕ) : Prop :=
  ∃ t : Finset (Point 2), t ⊆ s ∧ t.card = n ∧ InConvexPosition t

/-- The forcing assertion whose least valid `N` is the Erdős--Szekeres number. -/
def ForcesConvexPolygon (n N : ℕ) : Prop :=
  ∀ s : Finset (Point 2), N ≤ s.card → InGeneralPosition s →
    ContainsConvexSubset s n

/-- A sharpness witness showing that `N - 1` points need not force an `n`-gon. -/
def HasSharpnessExample (n N : ℕ) : Prop :=
  ∃ s : Finset (Point 2), s.card + 1 = N ∧ InGeneralPosition s ∧
    ¬ContainsConvexSubset s n

/-- The exact Erdős--Szekeres formula at `n`: both forcing and sharpness. -/
def ErdosSzekeresFormulaAt (n : ℕ) : Prop :=
  let N := 2 ^ (n - 2) + 1
  ForcesConvexPolygon n N ∧ HasSharpnessExample n N

/-- The classical Erdős--Szekeres conjecture, stated without claiming a proof. -/
def ErdosSzekeresConjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ErdosSzekeresFormulaAt n

@[simp] theorem inConvexPosition_empty (d : ℕ) :
    InConvexPosition (∅ : Finset (Point d)) := by
  simp [InConvexPosition]

theorem orientation_swap (a b c : Point 2) :
    orientation b a c = -orientation a b c := by
  simp only [orientation]
  ring

end ErdosSzekeres
