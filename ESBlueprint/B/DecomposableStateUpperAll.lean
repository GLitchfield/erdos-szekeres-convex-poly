import ErdosSzekeres.E3FiniteReduction

namespace ErdosSzekeres

/-- The decomposable theorem (Baek–Balko Theorem 8) for all parameters: a decomposable coloring on more than decomposableThreshold a u k vertices contains an a-cap, a u-cup, or a strong k-set. The degenerate a = 1 / u = 1 cases are to be checked against containsCupSet_one before this statement is locked.
@node
@ws B
@kind formalization
@dangling-ok uniform theorem; consumer is E3FiniteReduction's DecomposableExactUpperAt
@measure a + u (published induction) -/
theorem decomposableStateUpper_all (a u k : ℕ) (ha : 1 ≤ a) (hu : 1 ≤ u) (hak : a ≤ k) (huk : u ≤ k) : DecomposableStateUpper a u k := by
  sorry

end ErdosSzekeres
