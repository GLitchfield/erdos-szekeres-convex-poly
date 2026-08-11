module

public import ErdosSzekeres.DecompositionPrimeMutationLocality

@[expose] public section

/-!
# Endpoint locality for short mutation paths

A macro of at most three single-triple mutations can change decomposition-prime
status only on supports containing one of at most three changed triples.  This
packages the single-step locality theorem at exactly the path length used by
the Layer-F stratified-rank interface.
-/

namespace ErdosSzekeres

open scoped symmDiff

/-- A family of at most three ordered triples which covers every support whose
decomposition-prime status differs between two endpoint colorings. -/
def HasAtMostThreePrimeCoreCarrierCover {n : ℕ}
    (χ ψ : TripleColoring n) : Prop :=
  ∃ changed : Finset (OrderedTriple n),
    changed.card ≤ 3 ∧
    ∀ support : Finset (Fin n),
      ¬(IsDecompositionPrimeOn χ support ↔
        IsDecompositionPrimeOn ψ support) →
      ∃ t ∈ changed, t.support ⊆ support

/-- Every target-free realizable mutation macro of length at most three has a
three-triple carrier cover for all endpoint prime-core changes. -/
theorem AtMostThree.hasAtMostThreePrimeCoreCarrierCover
    {k n : ℕ} {χ ψ : TripleColoring n}
    (path : AtMostThree (TargetFreeRealizableMutationStepAt k) χ ψ) :
    HasAtMostThreePrimeCoreCarrierCover χ ψ := by
  classical
  rcases path with hχψ | ⟨middle, hχmiddle, hmiddleψ⟩ |
      ⟨middle₁, middle₂, hχmiddle₁, hmiddle₁middle₂, hmiddle₂ψ⟩
  · obtain ⟨t, hchanged, hagree⟩ := hχψ.2.2.2.2
    refine ⟨{t}, by simp, ?_⟩
    intro support hdiff
    refine ⟨t, by simp, ?_⟩
    by_contra houtside
    exact hdiff (SingleTripleMutation.isDecompositionPrimeOn_congr_off_changed
      ⟨hchanged, hagree⟩ houtside)
  · obtain ⟨t₁, hchanged₁, hagree₁⟩ := hχmiddle.2.2.2.2
    obtain ⟨t₂, hchanged₂, hagree₂⟩ := hmiddleψ.2.2.2.2
    refine ⟨{t₁, t₂}, Finset.card_le_two.trans (by omega), ?_⟩
    intro support hdiff
    by_contra hnone
    push Not at hnone
    have houtside₁ : ¬t₁.support ⊆ support := hnone t₁ (by simp)
    have houtside₂ : ¬t₂.support ⊆ support := hnone t₂ (by simp)
    have hfirst := SingleTripleMutation.isDecompositionPrimeOn_congr_off_changed
      ⟨hchanged₁, hagree₁⟩ houtside₁
    have hsecond := SingleTripleMutation.isDecompositionPrimeOn_congr_off_changed
      ⟨hchanged₂, hagree₂⟩ houtside₂
    exact hdiff (hfirst.trans hsecond)
  · obtain ⟨t₁, hchanged₁, hagree₁⟩ := hχmiddle₁.2.2.2.2
    obtain ⟨t₂, hchanged₂, hagree₂⟩ := hmiddle₁middle₂.2.2.2.2
    obtain ⟨t₃, hchanged₃, hagree₃⟩ := hmiddle₂ψ.2.2.2.2
    refine ⟨{t₁, t₂, t₃}, Finset.card_le_three, ?_⟩
    intro support hdiff
    by_contra hnone
    push Not at hnone
    have houtside₁ : ¬t₁.support ⊆ support := hnone t₁ (by simp)
    have houtside₂ : ¬t₂.support ⊆ support := hnone t₂ (by simp)
    have houtside₃ : ¬t₃.support ⊆ support := hnone t₃ (by simp)
    have hfirst := SingleTripleMutation.isDecompositionPrimeOn_congr_off_changed
      ⟨hchanged₁, hagree₁⟩ houtside₁
    have hsecond := SingleTripleMutation.isDecompositionPrimeOn_congr_off_changed
      ⟨hchanged₂, hagree₂⟩ houtside₂
    have hthird := SingleTripleMutation.isDecompositionPrimeOn_congr_off_changed
      ⟨hchanged₃, hagree₃⟩ houtside₃
    exact hdiff (hfirst.trans (hsecond.trans hthird))

/-- The symmetric difference of the endpoint prime-core families is supported
on sets containing one of at most three changed triples. -/
theorem AtMostThree.decompositionPrimeCores_symmDiff_threeCarrierCover
    {k n : ℕ} {χ ψ : TripleColoring n}
    (path : AtMostThree (TargetFreeRealizableMutationStepAt k) χ ψ) :
    ∃ changed : Finset (OrderedTriple n),
      changed.card ≤ 3 ∧
      decompositionPrimeCores χ ∆ decompositionPrimeCores ψ ⊆
        Finset.univ.powerset.filter fun support ↦
          ∃ t ∈ changed, t.support ⊆ support := by
  classical
  obtain ⟨changed, hcard, hcover⟩ :=
    path.hasAtMostThreePrimeCoreCarrierCover
  refine ⟨changed, hcard, ?_⟩
  intro support hsymm
  have hdiff : ¬(IsDecompositionPrimeOn χ support ↔
      IsDecompositionPrimeOn ψ support) := by
    rw [← mem_decompositionPrimeCores_iff,
      ← mem_decompositionPrimeCores_iff]
    rw [Finset.mem_symmDiff] at hsymm
    tauto
  obtain ⟨t, ht, hsub⟩ := hcover support hdiff
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ support), t, ht, hsub⟩

end ErdosSzekeres

end
