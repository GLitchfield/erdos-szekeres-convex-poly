module

public import ErdosSzekeres.PredecessorHalfFin15CrossExteriorCommonOwner

@[expose] public section

/-! Explicit eight-to-five witness infrastructure for the frozen Fin15 coloring. -/

namespace ErdosSzekeres
namespace Fin15CommonOwnerExplicitWitnessCounterexample

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def rightTriples : Finset (Nat × Nat × Nat) :=
  {(0, 1, 2), (0, 1, 5),
   (0, 3, 5), (0, 3, 6), (0, 3, 7), (0, 3, 8),
   (0, 4, 5), (0, 4, 6), (0, 4, 7), (0, 4, 8), (0, 7, 8),
   (1, 3, 5), (1, 3, 6), (1, 3, 7), (1, 3, 8),
   (1, 4, 5), (1, 4, 6), (1, 4, 7), (1, 4, 8), (1, 7, 8),
   (2, 3, 5), (2, 3, 6), (2, 3, 7), (2, 3, 8),
   (2, 4, 5), (2, 4, 6), (2, 4, 7), (2, 4, 8),
   (2, 5, 6), (2, 7, 8),
   (3, 4, 5), (3, 4, 6), (3, 4, 7), (3, 4, 8), (5, 7, 8),
   (6, 7, 8), (6, 7, 9), (6, 8, 9)}

def coloring : TripleColoring 15 := fun triple =>
  if (triple.i.val, triple.j.val, triple.k.val) ∈ rightTriples then
    Turn.right
  else
    Turn.left

def support : Finset (Fin 15) := Fin15PairOwnerCounterexample.support
def first : Finset (Fin 15) := Fin15PairOwnerCounterexample.block0
def second : Finset (Fin 15) := Fin15PairOwnerCounterexample.block6
def third : Finset (Fin 15) := Fin15PairOwnerCounterexample.block2
def blocks : Finset (Finset (Fin 15)) := Fin15PairOwnerCounterexample.blocks

def q : Fin 15 := 7
def r : Fin 15 := 8
def s : Fin 15 := 9
def x : Fin 15 := 3
def y : Fin 15 := 1
def residue : Finset (Fin 15) := {0, 5, 6}

/-- A collision-free key for a finite subset of the ordered ground set. -/
def eightKey (candidate : Finset (Fin 15)) : List (Fin 15) :=
  candidate.sort (· ≤ ·)

theorem eightKey_injective : Function.Injective eightKey := by
  intro left right heq
  have hfinset := congrArg List.toFinset heq
  simpa [eightKey] using hfinset

/-- The frozen lexicographic enumeration of all eight-subsets. -/
def allEightLists : List (List (Fin 15)) :=
  ((List.finRange 15).sublistsLen 8).reverse

structure WitnessRow where
  eight : List (Fin 15)
  five : Finset (Fin 15)

/-- Only the literal subset, cardinality, and strong-color facts are checked. -/
def WitnessRow.validBool (row : WitnessRow) : Bool :=
  decide (row.five ⊆ row.eight.toFinset) &&
    decide (row.five.card = 5) &&
      Fin15PairOwnerCounterexample.strongPolygonSetBool coloring row.five

/-- A checked explicit witness supplies the logical strong-five containment. -/
theorem WitnessRow.validBool_sound {row : WitnessRow}
    (hvalid : row.validBool = true) :
    ContainsStrongPolygonSet coloring row.eight.toFinset 5 := by
  have hsubsetBool : decide (row.five ⊆ row.eight.toFinset) = true :=
    (Bool.and_eq_true_iff.mp hvalid).1
  have hrest := (Bool.and_eq_true_iff.mp hvalid).2
  have hcardBool : decide (row.five.card = 5) = true :=
    (Bool.and_eq_true_iff.mp hrest).1
  have hstrongBool := (Bool.and_eq_true_iff.mp hrest).2
  exact ⟨row.five, of_decide_eq_true hsubsetBool,
    of_decide_eq_true hcardBool,
    (Fin15PairOwnerCounterexample.strongPolygonSetBool_eq_true_iff
      coloring row.five).mp hstrongBool⟩

end Fin15CommonOwnerExplicitWitnessCounterexample
end ErdosSzekeres

end
