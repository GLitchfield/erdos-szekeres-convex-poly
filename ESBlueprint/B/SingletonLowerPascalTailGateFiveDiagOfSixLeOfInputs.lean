import ErdosSzekeres.StructuralChargingPascalCupBlocks

namespace ErdosSzekeres

/-- The diagonal five singleton lower Pascal-tail gate for k at least six, following the audited root split argument and taking the uniform R20 cupblock theorem and exact R21 Baek cardinality bound as explicit hypotheses.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs (hblocks : ∀ k, 5 ≤ k → DiagonalCupBlocksForce4kk k) (hbaek : ∀ {n k : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}, 3 ≤ k → OneChangeOn χ s → ¬ContainsCapSet χ s 4 → ¬ContainsStrongPolygonSet χ s k → s.card ≤ 1 + Nat.choose (k - 1) 2) {k : ℕ} (hk : 6 ≤ k) : SingletonLowerPascalTailGate 5 k k := by
  sorry

end ErdosSzekeres
