module

public import ErdosSzekeres.StructuralChargingNextState578CarrierMatrix

@[expose] public section

/-!
# Relaxed crossing-row obstructions at state `(5,7,8)`

These kernel-checked finite-set and address models delimit the information in
the full residual matrix.  They are not triple colorings and do not refute a
future theorem using cup/cap endpoint colors.  They do refute the set-theoretic
inference that a cup crossing the selected `24+8` support partition must meet
the small child of a decomposition node containing all 24 cap vertices.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578CrossingRowCounterexample

abbrev Vertex := Fin 32

def capSupport : Finset Vertex :=
  Finset.univ.filter fun x => x.val < 24

def unused : Finset Vertex := Finset.univ \ capSupport

def largeChild : Finset Vertex := capSupport ∪ {24, 25, 26}

def smallChild : Finset Vertex := {27, 28, 29, 30, 31}

def crossingCup : Finset Vertex := {0, 24, 25, 26}

/-- Exact finite-set obstruction: the cup meets both the selected cap support
and its unused complement, yet remains wholly in the large child and is
disjoint from the at-most-eight small child. -/
theorem crossing_support_does_not_force_smallChild_intersection :
    capSupport.card = 24 ∧
    unused.card = 8 ∧
    largeChild.card = 27 ∧
    smallChild.card = 5 ∧
    Disjoint largeChild smallChild ∧
    largeChild ∪ smallChild = Finset.univ ∧
    capSupport ⊆ largeChild ∧
    crossingCup.card = 4 ∧
    (crossingCup ∩ capSupport).Nonempty ∧
    (crossingCup ∩ unused).Nonempty ∧
    crossingCup ⊆ largeChild ∧
    Disjoint crossingCup smallChild := by
  decide

/-- Two rows and six columns can satisfy all bare prefix-chain and common
minimum requirements while every cell remains at the same address. -/
def allBasePath (_ : Fin 2) (_ : Fin 6) : List Bool := []

theorem allBasePath_satisfies_matrix_prefix_contract :
    (∀ i j k,
      allBasePath i j <+: allBasePath i k ∨
        allBasePath i k <+: allBasePath i j) ∧
    (∀ i k j,
      allBasePath i j <+: allBasePath k j ∨
        allBasePath k j <+: allBasePath i j) ∧
    (∀ i j, allBasePath 0 0 <+: allBasePath i j) ∧
    (∀ i j, allBasePath i j = allBasePath 0 0) := by
  simp [allBasePath]

end StructuralChargingNextState578CrossingRowCounterexample
end ErdosSzekeres

end
