module

public import ErdosSzekeres.DecompositionPrime

@[expose] public section

/-!
# Target-reflecting normalization for decomposition-prime configurations

This file states the exact load-bearing Layer-F interface. A normalization
which preserves sweep realizability and reflects targets back to the source
promotes the decomposable upper theorem to every sweep-realizable coloring.
-/

namespace ErdosSzekeres

/-- The upper half of the exact happy-ending formula for every
sweep-realizable coloring, without a decomposability hypothesis. -/
def SweepExactUpperAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}, IsSweepRealizable χ →
    2 ^ (k - 2) < n → ContainsStrongPolygonSet χ Finset.univ k

/-- A target-free realizable coloring can be normalized to a decomposable
realizable coloring on the same ground set, with any target reflected back. -/
def TargetReflectingDecomposableNormalizationAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}, IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ ψ : TripleColoring n,
      IsSweepRealizable ψ ∧ IsDecomposable ψ ∧
        (ContainsStrongPolygonSet ψ Finset.univ k →
          ContainsStrongPolygonSet χ Finset.univ k)

/-- Two ordered triple colorings differ at exactly one increasing triple. -/
def SingleTripleMutation {n : ℕ}
    (χ ψ : TripleColoring n) : Prop :=
  ∃ t, χ t ≠ ψ t ∧ ∀ u, u ≠ t → χ u = ψ u

/-- One realizable mutation step stays inside the target-free locus. -/
def TargetFreeRealizableMutationStepAt
    (k : ℕ) {n : ℕ} (χ ψ : TripleColoring n) : Prop :=
  IsSweepRealizable χ ∧ IsSweepRealizable ψ ∧
    ¬ContainsStrongPolygonSet χ Finset.univ k ∧
    ¬ContainsStrongPolygonSet ψ Finset.univ k ∧
    SingleTripleMutation χ ψ

/-- Every target-free realizable coloring can reach a decomposable coloring
through target-free realizable single-triple mutations. -/
def TargetFreeMutationNormalizesAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}, IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ ψ,
      Relation.ReflTransGen
        (TargetFreeRealizableMutationStepAt k) χ ψ ∧
      IsDecomposable ψ

private theorem targetFree_of_mutationPath
    {k n : ℕ} {χ ψ : TripleColoring n}
    (hχ : ¬ContainsStrongPolygonSet χ Finset.univ k)
    (path : Relation.ReflTransGen
      (TargetFreeRealizableMutationStepAt k) χ ψ) :
    ¬ContainsStrongPolygonSet ψ Finset.univ k := by
  induction path with
  | refl => exact hχ
  | tail _ step _ => exact step.2.2.2.1

/-- Mutation normalization supplies the exact target-reflecting interface. -/
theorem targetReflectingNormalization_of_mutationNormalization
    {k : ℕ} (hnormalize : TargetFreeMutationNormalizesAt k) :
    TargetReflectingDecomposableNormalizationAt k := by
  intro n χ hrealizable htarget
  obtain ⟨ψ, path, hdecomposable⟩ := hnormalize hrealizable htarget
  have hψTargetFree := targetFree_of_mutationPath htarget path
  have hψRealizable : IsSweepRealizable ψ := by
    induction path with
    | refl => exact hrealizable
    | tail _ step _ => exact step.2.1
  exact ⟨ψ, hψRealizable, hdecomposable, fun htargetψ ↦
    (hψTargetFree htargetψ).elim⟩

/-- Target-reflecting normalization promotes the decomposable exact upper
bound to every sweep-realizable coloring. -/
theorem sweepExactUpperAt_of_targetReflectingNormalization
    {k : ℕ}
    (hdecomposable : DecomposableExactUpperAt k)
    (hnormalize : TargetReflectingDecomposableNormalizationAt k) :
    SweepExactUpperAt k := by
  intro n χ hrealizable hcard
  by_contra htarget
  obtain ⟨ψ, hψRealizable, hψDecomposable, hreflect⟩ :=
    hnormalize hrealizable htarget
  exact htarget (hreflect (hdecomposable hψRealizable hψDecomposable hcard))

end ErdosSzekeres

end
