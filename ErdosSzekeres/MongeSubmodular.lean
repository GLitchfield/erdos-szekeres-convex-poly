module

public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Submodularity of the crossing-mismatch energy

This file formalizes the Boolean crossing-mismatch term and proves its submodularity, first for
one ordered triple and then for the sum over every ordered triple. Here `false` means lower and
`true` means upper.
-/

namespace ErdosSzekeres
namespace CrossingMismatch

noncomputable section

local instance orderedTripleFintype (n : ℕ) : Fintype (OrderedTriple n) :=
  Fintype.ofInjective (fun t ↦ (t.i, t.j, t.k)) (by
    intro s t h
    cases s
    cases t
    simp_all)

/-- Three Boolean shore labels cross when they are not all equal. -/
def crossing3 (a b c : Bool) : Prop :=
  ¬(a = b ∧ b = c)

/-- Crossing is decidable by the three finite Boolean labels. -/
instance crossing3Decidable (a b c : Bool) : Decidable (crossing3 a b c) := by
  unfold crossing3
  infer_instance

/-- The expected turn is left for a lower middle label and right for an upper middle label. -/
def expectedTurn (middle : Bool) : Turn :=
  if middle = false then Turn.left else Turn.right

/-- The zero-one mismatch cost for one ordered triple with frozen actual turn. -/
def mismatchTerm (actual : Turn) (a b c : Bool) : ℕ :=
  if crossing3 a b c then
    if actual = expectedTurn b then 0 else 1
  else
    0

/-- Coordinatewise meet of Boolean labelings. -/
def pointwiseMeet {ι : Type*} (x y : ι → Bool) : ι → Bool :=
  fun i ↦ x i && y i

/-- Coordinatewise join of Boolean labelings. -/
def pointwiseJoin {ι : Type*} (x y : ι → Bool) : ι → Bool :=
  fun i ↦ x i || y i

/-- Submodularity in the convention `F (x ⊓ y) + F (x ⊔ y) ≤ F x + F y`. -/
def IsSubmodular {ι : Type*} (F : (ι → Bool) → ℕ) : Prop :=
  ∀ x y, F (pointwiseMeet x y) + F (pointwiseJoin x y) ≤ F x + F y

/-- The literal six-label single-term inequality, for either actual turn. -/
theorem mismatchTerm_submodular_values (actual : Turn) (a b c a' b' c' : Bool) :
    mismatchTerm actual (a && a') (b && b') (c && c') +
        mismatchTerm actual (a || a') (b || b') (c || c') ≤
      mismatchTerm actual a b c + mismatchTerm actual a' b' c' := by
  cases actual <;>
    cases a <;> cases b <;> cases c <;>
    cases a' <;> cases b' <;> cases c' <;> decide

/-- The crossing-mismatch term on a `Fin 3` labeling is submodular. -/
theorem mismatchTerm_submodular (actual : Turn) :
    IsSubmodular (fun x : Fin 3 → Bool ↦ mismatchTerm actual (x 0) (x 1) (x 2)) := by
  intro x y
  simpa [pointwiseMeet, pointwiseJoin] using
    mismatchTerm_submodular_values actual (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)

/-- The mismatch contribution of one ordered triple under a total Boolean labeling. -/
def mismatchAt {n : ℕ} (χ : TripleColoring n) (label : Fin n → Bool)
    (t : OrderedTriple n) : ℕ :=
  mismatchTerm (χ t) (label t.i) (label t.j) (label t.k)

/-- The total crossing-mismatch energy, summed over all increasing triples. -/
def mismatchEnergy {n : ℕ} (χ : TripleColoring n) (label : Fin n → Bool) : ℕ :=
  ∑ t : OrderedTriple n, mismatchAt χ label t

/-- Every finite crossing-mismatch energy is submodular, for every triple coloring. -/
theorem mismatchEnergy_submodular {n : ℕ} (χ : TripleColoring n) :
    IsSubmodular (mismatchEnergy χ) := by
  intro x y
  have h :
      (∑ t : OrderedTriple n,
          (mismatchAt χ (pointwiseMeet x y) t + mismatchAt χ (pointwiseJoin x y) t)) ≤
        ∑ t : OrderedTriple n, (mismatchAt χ x t + mismatchAt χ y t) := by
    refine Finset.sum_le_sum ?_
    intro t _
    simpa [mismatchAt, pointwiseMeet, pointwiseJoin] using
      mismatchTerm_submodular_values (χ t)
        (x t.i) (x t.j) (x t.k) (y t.i) (y t.j) (y t.k)
  simpa [mismatchEnergy, Finset.sum_add_distrib] using h

end

end CrossingMismatch
end ErdosSzekeres

end
