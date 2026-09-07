import ErdosSzekeres.DecomposableRealization

namespace ErdosSzekeres

/-- Inserting any new vertex into a sweep-realizable, recursively decomposable support of cardinality 2^(k-2) with no strong k-set forces a strong k-set. This extends the decomposable route toward configurations with a decomposable one-vertex deletion. The attached falsifier checks only selected insertion fibers of canonical extremal realizations; its passing result does not establish the general statement.
@node
@ws F
@kind conjecture
@dangling-ok Approved intermediate geometric target: together with the uniform decomposable upper theorem this proves the exact bound for configurations with a decomposable one-vertex deletion.
@falsifier decomposable_extremal_insertion.py -/
theorem decomposable_extremal_insertion {k n : ℕ} (hk : 4 ≤ k) {χ : TripleColoring n}
  (hreal : IsSweepRealizable χ) (S : Finset (Fin n))
  (hdec : IsDecomposableOn χ S) (hcard : S.card = 2 ^ (k - 2))
  (hfree : ¬ContainsStrongPolygonSet χ S k) (q : Fin n) (hq : q ∉ S) :
  ContainsStrongPolygonSet χ (insert q S) k := by
  sorry

end ErdosSzekeres
