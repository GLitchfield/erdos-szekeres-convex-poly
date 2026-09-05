import ErdosSzekeres.DecomposableRealization

namespace ErdosSzekeres

/-- The Erdős–Tuza–Valtr case with cap parameter 5 (Workstream C): every sweep-realizable coloring on more than decomposableThreshold 5 n n vertices contains a 5-cap, an n-cup, or a strong n-set; through the presentation bridge this is the planar statement that decomposableThreshold 5 n n + 1 points in general position contain a 5-cap, an n-cup, or a convex n-gon. Baek proved cap parameter 4. At n = 5 this is ES(5) = 9; at n = 6 the signotope-tier number is exactly 16 (experiment 0112); at n = 7 it is at least 27 and the 27-point instance is undecided.
@node
@ws C
@kind conjecture
@dangling-ok standing Workstream C problem; the Erdős–Tuza–Valtr family implies ErdosSzekeresConjecture through the monotone implication scheme, which is not yet formalized
@falsifier etv_cap5_small_n.py -/
theorem etvCapFive_all (n : ℕ) (hn : 5 ≤ n) {N : ℕ} {χ : TripleColoring N} (hreal : IsSweepRealizable χ) (hcard : decomposableThreshold 5 n n < N) : ContainsCapSet χ Finset.univ 5 ∨ ContainsCupSet χ Finset.univ n ∨ ContainsStrongPolygonSet χ Finset.univ n := by
  sorry

end ErdosSzekeres
