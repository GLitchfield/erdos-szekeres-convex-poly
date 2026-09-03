module

public import ErdosSzekeres.StructuralCharging
public import ErdosSzekeres.TripleColoringExtensionTransition

@[expose] public section

/-!
# Permutation-order normalization for a common-anchor fiber

This file isolates the ten binary cells in the four-owner pair/triple normal form.  The six pair
cells encode a second order of the owners.  Correcting the four owner-triple cells by the parity
of that order makes the selected matching edge one-change in the encoded order.

The local theorem is a closed finite check.  It does not assert that the selected-edge coloring
is one-change in the original owner order.
-/

namespace ErdosSzekeres

set_option maxRecDepth 10000

/-- Interpret `false` as the left turn and `true` as the right turn. -/
def turnOfBool : Bool → Turn
  | false => .left
  | true => .right

local instance turnSequenceAllowedDecidable (a b c d : Turn) :
    Decidable (TurnSequenceAllowed a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [TurnSequenceAllowed] <;> infer_instance

/-- XOR of the four bits occurring on one pair/triple word. -/
def xorFour (a b c d : Bool) : Bool :=
  Bool.xor (Bool.xor (Bool.xor a b) c) d

/-- The six pair cells and four owner-triple cells on four ambiently ordered owners. -/
abbrev CommonAnchorFin4State := Fin 10 → Bool

namespace CommonAnchorFin4State

def p01 (state : CommonAnchorFin4State) : Bool := state 0
def p02 (state : CommonAnchorFin4State) : Bool := state 1
def p03 (state : CommonAnchorFin4State) : Bool := state 2
def p12 (state : CommonAnchorFin4State) : Bool := state 3
def p13 (state : CommonAnchorFin4State) : Bool := state 4
def p23 (state : CommonAnchorFin4State) : Bool := state 5
def t012 (state : CommonAnchorFin4State) : Bool := state 6
def t013 (state : CommonAnchorFin4State) : Bool := state 7
def t023 (state : CommonAnchorFin4State) : Bool := state 8
def t123 (state : CommonAnchorFin4State) : Bool := state 9

/-- The four pair/triple words and the ambient owner-quadruple word are all one-change. -/
def Admissible (state : CommonAnchorFin4State) : Prop :=
  TurnSequenceAllowed (turnOfBool state.p01) (turnOfBool state.p02)
      (turnOfBool state.p12) (turnOfBool state.t012) ∧
    TurnSequenceAllowed (turnOfBool state.p01) (turnOfBool state.p03)
      (turnOfBool state.p13) (turnOfBool state.t013) ∧
    TurnSequenceAllowed (turnOfBool state.p02) (turnOfBool state.p03)
      (turnOfBool state.p23) (turnOfBool state.t023) ∧
    TurnSequenceAllowed (turnOfBool state.p12) (turnOfBool state.p13)
      (turnOfBool state.p23) (turnOfBool state.t123) ∧
    TurnSequenceAllowed (turnOfBool state.t012) (turnOfBool state.t013)
      (turnOfBool state.t023) (turnOfBool state.t123)

instance admissibleDecidable (state : CommonAnchorFin4State) : Decidable state.Admissible := by
  unfold Admissible
  infer_instance

/-- A rank function represents the pair cells when `false` points forward in its order. -/
def RepresentedBy (state : CommonAnchorFin4State) (order : Fin 4 → Fin 4) : Prop :=
  (state.p01 = false ↔ order 0 < order 1) ∧
    (state.p02 = false ↔ order 0 < order 2) ∧
    (state.p03 = false ↔ order 0 < order 3) ∧
    (state.p12 = false ↔ order 1 < order 2) ∧
    (state.p13 = false ↔ order 1 < order 3) ∧
    (state.p23 = false ↔ order 2 < order 3)

instance representedByDecidable (state : CommonAnchorFin4State) (order : Fin 4 → Fin 4) :
    Decidable (state.RepresentedBy order) := by
  unfold RepresentedBy
  infer_instance

/-- The rank function lists every one of the four ranks exactly once. -/
def IsPermutation (order : Fin 4 → Fin 4) : Prop :=
  order 0 ≠ order 1 ∧ order 0 ≠ order 2 ∧ order 0 ≠ order 3 ∧
    order 1 ≠ order 2 ∧ order 1 ≠ order 3 ∧ order 2 ≠ order 3

instance isPermutationDecidable (order : Fin 4 → Fin 4) : Decidable (IsPermutation order) := by
  unfold IsPermutation
  infer_instance

/-- The selected matching-edge color on the natural triple omitting `missing`. -/
def selectedFace (state : CommonAnchorFin4State) (missing : Fin 4) : Turn :=
  if missing = 0 then
    turnOfBool (xorFour state.p12 state.p13 state.p23 state.t123)
  else if missing = 1 then
    turnOfBool (xorFour state.p02 state.p03 state.p23 state.t023)
  else if missing = 2 then
    turnOfBool (xorFour state.p01 state.p03 state.p13 state.t013)
  else
    turnOfBool (xorFour state.p01 state.p02 state.p12 state.t012)

/-- The owner occupying a specified rank, found by a fixed finite search. -/
def ownerAtRank (order : Fin 4 → Fin 4) (rank : Fin 4) : Fin 4 :=
  if order 0 = rank then 0
  else if order 1 = rank then 1
  else if order 2 = rank then 2
  else 3

/-- The selected-face word after listing the four owners in the represented permutation order. -/
def ReorderedOneChange (state : CommonAnchorFin4State) (order : Fin 4 → Fin 4) : Prop :=
  TurnSequenceAllowed
    (state.selectedFace (ownerAtRank order 3))
    (state.selectedFace (ownerAtRank order 2))
    (state.selectedFace (ownerAtRank order 1))
    (state.selectedFace (ownerAtRank order 0))

instance reorderedOneChangeDecidable (state : CommonAnchorFin4State) (order : Fin 4 → Fin 4) :
    Decidable (state.ReorderedOneChange order) := by
  unfold ReorderedOneChange
  infer_instance

/-- The complete four-owner permutation-reorder table.  There are `2^10` states and twenty-four
permutation orders.  The hypotheses reject all rows except the symbolic pair/triple normal form. -/
theorem fin4_permutation_reorder_table :
    ∀ (state : CommonAnchorFin4State) (order : Fin 4 → Fin 4),
      state.Admissible → IsPermutation order → state.RepresentedBy order →
        state.ReorderedOneChange order := by
  native_decide

/-- Reusable implication form of `fin4_permutation_reorder_table`. -/
theorem reorderedOneChange (state : CommonAnchorFin4State) (order : Fin 4 → Fin 4)
    (hadmissible : state.Admissible) (hpermutation : IsPermutation order)
    (horder : state.RepresentedBy order) :
    state.ReorderedOneChange order :=
  fin4_permutation_reorder_table state order hadmissible hpermutation horder

end CommonAnchorFin4State

end ErdosSzekeres
