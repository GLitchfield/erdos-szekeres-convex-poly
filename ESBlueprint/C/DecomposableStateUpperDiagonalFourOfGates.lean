import ESBlueprint.C.DecomposableStateUpperFourDiagonalOfGates

namespace ErdosSzekeres

/-- Color dual of the uniform four-diagonal state, retaining the approved singleton lower gate hypothesis.
@node
@ws C
@kind formalization
@depends ErdosSzekeres.decomposableStateUpper_four_diagonal_of_gates
@dangling-ok Approved R21 optional uniform color dual; the coordinator can instantiate the gate-conditional family after reviewed integration. -/
theorem decomposableStateUpper_diagonal_four_of_gates (hgate : ∀ k, 5 ≤ k → SingletonLowerPascalTailGate 4 k k) : ∀ k, 5 ≤ k → DecomposableStateUpper k 4 k := by
  intro k hk
  exact decomposableStateUpper_comm
    (by omega : 2 ≤ 4) (by omega : 2 ≤ k)
    (by omega : 4 ≤ k) (le_refl k)
    (decomposableStateUpper_four_diagonal_of_gates hgate k hk)


end ErdosSzekeres
