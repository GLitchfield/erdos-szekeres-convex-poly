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

private def emptySweptConfigurationForNormalization : SweptConfiguration 0 where
  point := Fin.elim0
  sweep_strictMono := by
    intro i
    exact Fin.elim0 i
  generalPosition := by
    intro i
    exact Fin.elim0 i

private theorem emptyTripleColoring_noStrong_of_pos
    {k : ℕ} (hk : 0 < k) :
    ¬ContainsStrongPolygonSet
      emptySweptConfigurationForNormalization.tripleColoring Finset.univ k := by
  rintro ⟨polygon, hpolygonSub, hpolygonCard, _⟩
  have hle : polygon.card ≤ (Finset.univ : Finset (Fin 0)).card :=
    Finset.card_le_card hpolygonSub
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- The unthresholded mutation-normalization contract is too strong: its empty
ground-set instance asks for a decomposable coloring on `Fin 0`. -/
theorem not_targetFreeMutationNormalizesAt_of_pos
    {k : ℕ} (hk : 0 < k) :
    ¬TargetFreeMutationNormalizesAt k := by
  intro hnormalizes
  let χ := emptySweptConfigurationForNormalization.tripleColoring
  have hrealizable : IsSweepRealizable χ :=
    emptySweptConfigurationForNormalization.tripleColoring_isSweepRealizable
  obtain ⟨ψ, _, hdecomposable⟩ :=
    hnormalizes hrealizable (emptyTripleColoring_noStrong_of_pos hk)
  have hnonempty := hdecomposable.nonempty
  simp at hnonempty

/-- The original target-reflecting interface has the same empty-ground-set
obstruction as the unthresholded mutation-normalization contract. -/
theorem not_targetReflectingDecomposableNormalizationAt_of_pos
    {k : ℕ} (hk : 0 < k) :
    ¬TargetReflectingDecomposableNormalizationAt k := by
  intro hnormalizes
  let χ := emptySweptConfigurationForNormalization.tripleColoring
  have hrealizable : IsSweepRealizable χ :=
    emptySweptConfigurationForNormalization.tripleColoring_isSweepRealizable
  obtain ⟨ψ, _, hdecomposable, _⟩ :=
    hnormalizes hrealizable (emptyTripleColoring_noStrong_of_pos hk)
  have hnonempty := hdecomposable.nonempty
  simp at hnonempty

/-- The load-bearing mutation-normalization contract only asks for
normalization above the exact upper-bound threshold. -/
def TargetFreeMutationNormalizesAboveAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}, 2 ^ (k - 2) < n →
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ ψ,
      Relation.ReflTransGen
        (TargetFreeRealizableMutationStepAt k) χ ψ ∧
      IsDecomposable ψ

/-- A nonempty relation path with at most three edges. -/
def AtMostThree {α : Type*} (relation : α → α → Prop) (x y : α) : Prop :=
  relation x y ∨
    (∃ z, relation x z ∧ relation z y) ∨
    ∃ z₁ z₂, relation x z₁ ∧ relation z₁ z₂ ∧ relation z₂ y

theorem AtMostThree.toReflTransGen
    {α : Type*} {relation : α → α → Prop} {x y : α}
    (path : AtMostThree relation x y) :
    Relation.ReflTransGen relation x y := by
  rcases path with hxy | ⟨z, hxz, hzy⟩ | ⟨z₁, z₂, hxz₁, hz₁z₂, hz₂y⟩
  · exact .tail .refl hxy
  · exact .tail (.tail .refl hxz) hzy
  · exact .tail (.tail (.tail .refl hxz₁) hz₁z₂) hz₂y

/-- A concrete natural-valued rank can decrease after one, two, or three
target-free realizable mutations whenever the current coloring is not already
decomposable. Intermediate rank values need not decrease. -/
def ThreeStepMutationRankDescendsAboveAt
    (k : ℕ) (rank : (n : ℕ) → TripleColoring n → ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}, 2 ^ (k - 2) < n →
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ¬IsDecomposable χ →
    ∃ ψ,
      AtMostThree (TargetFreeRealizableMutationStepAt k) χ ψ ∧
      rank n ψ < rank n χ

private theorem targetFree_of_mutationPath
    {k n : ℕ} {χ ψ : TripleColoring n}
    (hχ : ¬ContainsStrongPolygonSet χ Finset.univ k)
    (path : Relation.ReflTransGen
      (TargetFreeRealizableMutationStepAt k) χ ψ) :
    ¬ContainsStrongPolygonSet ψ Finset.univ k := by
  induction path with
  | refl => exact hχ
  | tail _ step _ => exact step.2.2.2.1

private theorem sweepRealizable_of_mutationPath
    {k n : ℕ} {χ ψ : TripleColoring n}
    (hχ : IsSweepRealizable χ)
    (path : Relation.ReflTransGen
      (TargetFreeRealizableMutationStepAt k) χ ψ) :
    IsSweepRealizable ψ := by
  induction path with
  | refl => exact hχ
  | tail _ step _ => exact step.2.1

/-- Mutation normalization supplies the exact target-reflecting interface. -/
theorem targetReflectingNormalization_of_mutationNormalization
    {k : ℕ} (hnormalize : TargetFreeMutationNormalizesAt k) :
    TargetReflectingDecomposableNormalizationAt k := by
  intro n χ hrealizable htarget
  obtain ⟨ψ, path, hdecomposable⟩ := hnormalize hrealizable htarget
  have hψTargetFree := targetFree_of_mutationPath htarget path
  have hψRealizable := sweepRealizable_of_mutationPath hrealizable path
  exact ⟨ψ, hψRealizable, hdecomposable, fun htargetψ ↦
    (hψTargetFree htargetψ).elim⟩

/-- A three-step decrease of any concrete natural-valued rank supplies the
threshold-scoped mutation normalization by well-founded induction. -/
theorem targetFreeMutationNormalizesAbove_of_threeStepRankDescent
    {k : ℕ} {rank : (n : ℕ) → TripleColoring n → ℕ}
    (hdescent : ThreeStepMutationRankDescendsAboveAt k rank) :
    TargetFreeMutationNormalizesAboveAt k := by
  intro n χ hcard hrealizable htarget
  generalize hr : rank n χ = r
  induction r using Nat.strong_induction_on generalizing χ with
  | h r ih =>
      by_cases hdecomposable : IsDecomposable χ
      · exact ⟨χ, .refl, hdecomposable⟩
      · obtain ⟨ψ, path, hlt⟩ :=
          hdescent hcard hrealizable htarget hdecomposable
        have hpath := path.toReflTransGen
        have hψRealizable := sweepRealizable_of_mutationPath hrealizable hpath
        have hψTargetFree := targetFree_of_mutationPath htarget hpath
        have hlt' : rank n ψ < r := by simpa [← hr] using hlt
        obtain ⟨ω, tail, hωDecomposable⟩ :=
          ih (rank n ψ) hlt' hψRealizable hψTargetFree rfl
        exact ⟨ω, hpath.trans tail, hωDecomposable⟩

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

/-- Threshold-scoped mutation normalization is sufficient for the exact
unrestricted sweep upper bound. -/
theorem sweepExactUpperAt_of_mutationNormalizationAbove
    {k : ℕ}
    (hdecomposable : DecomposableExactUpperAt k)
    (hnormalize : TargetFreeMutationNormalizesAboveAt k) :
    SweepExactUpperAt k := by
  intro n χ hrealizable hcard
  by_contra htarget
  obtain ⟨ψ, path, hψDecomposable⟩ :=
    hnormalize hcard hrealizable htarget
  have hψRealizable := sweepRealizable_of_mutationPath hrealizable path
  have hψTargetFree := targetFree_of_mutationPath htarget path
  exact hψTargetFree (hdecomposable hψRealizable hψDecomposable hcard)

end ErdosSzekeres

end
