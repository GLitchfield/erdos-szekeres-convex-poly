import ErdosSzekeres.StrongPredecessorBicoloring

namespace ErdosSzekeres

/-- The predecessor-half conjecture: every sweep-realizable strong-k-free coloring has a support of the required size with no strong (k-1)-set. Falsified against the known extremal constructions (classical Erdős–Szekeres sets and Theorem-19 blow-ups) at k = 6, 7.
@node
@ws E
@kind conjecture
@consumer ErdosSzekeres.sweepExactUpperAt_of_predecessorHalfSubset_all
@falsifier predecessor_half_constructions.py -/
theorem predecessorHalfSubsetAt_all (k : ℕ) (hk : 4 ≤ k) : PredecessorHalfSubsetAt k := by
  sorry

end ErdosSzekeres
