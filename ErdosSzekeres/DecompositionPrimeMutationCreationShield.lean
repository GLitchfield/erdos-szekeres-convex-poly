module

public import ErdosSzekeres.DecompositionPrimeMutationFamily
public import ErdosSzekeres.DecompositionPrimeMutationPathLocality
public import ErdosSzekeres.PrimeMutationPositiveControl

@[expose] public section

/-!
# Creation shields for Layer-F mutation macros

A single-triple mutation can affect only supports containing its changed
triple.  This file separates two local certificates on those supports: proper
decomposition splits persist, and new strong targets are excluded.  Together
they turn a realizable mutation into a target-free, prime-core-noncreating
step.  A short sequence of such steps with one destroyed source core supplies
the strict-family producer consumed by the stratified Layer-F rank.
-/

namespace ErdosSzekeres

/-- Every proper split on a support carrying the changed triple persists after
the mutation.  Supports not carrying the changed triple are covered by the
existing coloring-agreement locality theorem. -/
def HasPersistentPrimeSplitShield {n : ℕ}
    (χ ψ : TripleColoring n) (changed : OrderedTriple n) : Prop :=
  ∀ support : Finset (Fin n), changed.support ⊆ support →
    HasProperDeepBelowSplitOn χ support →
      HasProperDeepBelowSplitOn ψ support

/-- Every potentially new strong `k`-set carrying the changed triple is
explicitly excluded at the endpoint. -/
def HasStrongTargetCreationShieldAt {n : ℕ} (k : ℕ)
    (ψ : TripleColoring n) (changed : OrderedTriple n) : Prop :=
  ∀ polygon : Finset (Fin n), polygon.card = k →
    changed.support ⊆ polygon → ¬IsStrongPolygonSet ψ polygon

/-- A decomposable endpoint supplies every required persistent proper split. -/
theorem persistentPrimeSplitShield_of_decomposable
    {n : ℕ} {χ ψ : TripleColoring n} {changed : OrderedTriple n}
    (hdecomposable : IsDecomposable ψ) :
    HasPersistentPrimeSplitShield χ ψ changed := by
  intro support _ hsplitχ
  obtain ⟨lowerχ, upperχ, hlowerχ, hupperχ, hunionχ, hdeepχ⟩ := hsplitχ
  have hcard : 2 ≤ support.card := by
    have hlowerPos : 0 < lowerχ.card := Finset.card_pos.mpr hlowerχ
    have hupperPos : 0 < upperχ.card := Finset.card_pos.mpr hupperχ
    have hunionCard : (lowerχ ∪ upperχ).card = lowerχ.card + upperχ.card :=
      Finset.card_union_of_disjoint hdeepχ.disjoint
    rw [← hunionχ, hunionCard]
    omega
  have hnonempty : support.Nonempty := Finset.card_pos.mp (by omega)
  have hsupportDecomposable := hdecomposable.subset
    (Finset.subset_univ support) hnonempty
  obtain ⟨lower, upper, hlower, hupper, _, _, hdeep, hunion⟩ :=
    hsupportDecomposable.exists_split hcard
  exact ⟨lower, upper, hlower, hupper, hunion.symm, hdeep⟩

/-- An endpoint already known to be target-free supplies its local target
creation shield. -/
theorem strongTargetCreationShield_of_noStrongTarget
    {k n : ℕ} {ψ : TripleColoring n} {changed : OrderedTriple n}
    (htarget : ¬ContainsStrongPolygonSet ψ Finset.univ k) :
    HasStrongTargetCreationShieldAt k ψ changed := by
  intro polygon hcard _ hstrong
  exact htarget ⟨polygon, Finset.subset_univ polygon, hcard, hstrong⟩

/-- Strong-polygon status on a support depends only on the colors of triples
inside that support. -/
theorem isStrongPolygonSet_congr_of_agreeOnTriples
    {n : ℕ} {χ ψ : TripleColoring n} {support : Finset (Fin n)}
    (hagree : χ.AgreeOnTriples ψ support) :
    IsStrongPolygonSet χ support ↔ IsStrongPolygonSet ψ support := by
  constructor
  · intro hstrong i j k l hij hjk hkl hi hj hk hl
    have hijk := hagree ⟨i, j, k, hij, hjk⟩ hi hj hk
    have hijl := hagree ⟨i, j, l, hij, hjk.trans hkl⟩ hi hj hl
    have hikl := hagree ⟨i, k, l, hij.trans hjk, hkl⟩ hi hk hl
    have hjkl := hagree ⟨j, k, l, hjk, hkl⟩ hj hk hl
    obtain ⟨hleft, hright⟩ := hstrong hij hjk hkl hi hj hk hl
    exact ⟨hijk.symm.trans (hleft.trans hijl),
      hikl.symm.trans (hright.trans hjkl)⟩
  · intro hstrong i j k l hij hjk hkl hi hj hk hl
    have hijk := hagree ⟨i, j, k, hij, hjk⟩ hi hj hk
    have hijl := hagree ⟨i, j, l, hij, hjk.trans hkl⟩ hi hj hl
    have hikl := hagree ⟨i, k, l, hij.trans hjk, hkl⟩ hi hk hl
    have hjkl := hagree ⟨j, k, l, hjk, hkl⟩ hj hk hl
    obtain ⟨hleft, hright⟩ := hstrong hij hjk hkl hi hj hk hl
    exact ⟨hijk.trans (hleft.trans hijl.symm),
      hikl.trans (hright.trans hjkl.symm)⟩

/-- The two local shields, exact mutation data, realizability, and source
target-freedom form a checkable one-step lifting interface. -/
def CreationShieldedRealizableMutationStepAt
    (k : ℕ) {n : ℕ} (χ ψ : TripleColoring n) : Prop :=
  ∃ changed : OrderedTriple n,
    IsSweepRealizable χ ∧ IsSweepRealizable ψ ∧
      ¬ContainsStrongPolygonSet χ Finset.univ k ∧
      (χ changed ≠ ψ changed ∧ ∀ u, u ≠ changed → χ u = ψ u) ∧
      HasPersistentPrimeSplitShield χ ψ changed ∧
      HasStrongTargetCreationShieldAt k ψ changed

/-- A strong target cannot be created by a shielded single-triple mutation. -/
theorem noStrongTarget_of_creationShield
    {k n : ℕ} {χ ψ : TripleColoring n} {changed : OrderedTriple n}
    (hsource : ¬ContainsStrongPolygonSet χ Finset.univ k)
    (hmut : χ changed ≠ ψ changed ∧
      ∀ u, u ≠ changed → χ u = ψ u)
    (hshield : HasStrongTargetCreationShieldAt k ψ changed) :
    ¬ContainsStrongPolygonSet ψ Finset.univ k := by
  rintro ⟨polygon, hsub, hcard, hstrong⟩
  by_cases hcarrier : changed.support ⊆ polygon
  · exact hshield polygon hcard hcarrier hstrong
  · have hagree : χ.AgreeOnTriples ψ polygon :=
      SingleTripleMutation.agreeOnTriples_of_not_support_subset
        hmut hcarrier
    have hstrongχ :=
      (isStrongPolygonSet_congr_of_agreeOnTriples hagree).mpr hstrong
    exact hsource ⟨polygon, hsub, hcard, hstrongχ⟩

/-- Persistent proper-split shields prevent every new decomposition-prime
core under one mutation. -/
theorem decompositionPrimeCores_subset_of_persistentSplitShield
    {n : ℕ} {χ ψ : TripleColoring n} {changed : OrderedTriple n}
    (hmut : χ changed ≠ ψ changed ∧
      ∀ u, u ≠ changed → χ u = ψ u)
    (hshield : HasPersistentPrimeSplitShield χ ψ changed) :
    decompositionPrimeCores ψ ⊆ decompositionPrimeCores χ := by
  intro support hsupportψ
  by_cases hsupportχ : support ∈ decompositionPrimeCores χ
  · exact hsupportχ
  have hprimeψ : IsDecompositionPrimeOn ψ support :=
    mem_decompositionPrimeCores_iff.mp hsupportψ
  have hnotPrimeχ : ¬IsDecompositionPrimeOn χ support := by
    intro hprimeχ
    exact hsupportχ (mem_decompositionPrimeCores_iff.mpr hprimeχ)
  by_cases hcarrier : changed.support ⊆ support
  · have hsplitχ : HasProperDeepBelowSplitOn χ support := by
      by_contra hnoSplitχ
      exact hnotPrimeχ ⟨hprimeψ.1, hnoSplitχ⟩
    exact (hprimeψ.2 (hshield support hcarrier hsplitχ)).elim
  · have hprime :=
      SingleTripleMutation.isDecompositionPrimeOn_congr_off_changed
        hmut hcarrier
    exact (hnotPrimeχ (hprime.mpr hprimeψ)).elim

/-- A shielded realizable step is an ordinary target-free realizable mutation
step and creates no prime core. -/
theorem CreationShieldedRealizableMutationStepAt.to_targetFree_and_subset
    {k n : ℕ} {χ ψ : TripleColoring n}
    (hstep : CreationShieldedRealizableMutationStepAt k χ ψ) :
    TargetFreeRealizableMutationStepAt k χ ψ ∧
      decompositionPrimeCores ψ ⊆ decompositionPrimeCores χ := by
  obtain ⟨changed, hχRealizable, hψRealizable, hχTarget,
    hmut, hsplitShield, htargetShield⟩ := hstep
  have hψTarget := noStrongTarget_of_creationShield
    hχTarget hmut htargetShield
  exact ⟨⟨hχRealizable, hψRealizable, hχTarget, hψTarget,
      ⟨changed, hmut.1, hmut.2⟩⟩,
    decompositionPrimeCores_subset_of_persistentSplitShield
      hmut hsplitShield⟩

/-- At most three shielded steps preserve target-freedom and monotonically
delete prime cores. -/
theorem AtMostThree.creationShielded_to_targetFree_and_subset
    {k n : ℕ} {χ ψ : TripleColoring n}
    (path : AtMostThree (CreationShieldedRealizableMutationStepAt k) χ ψ) :
    AtMostThree (TargetFreeRealizableMutationStepAt k) χ ψ ∧
      decompositionPrimeCores ψ ⊆ decompositionPrimeCores χ := by
  rcases path with hχψ | ⟨middle, hχmiddle, hmiddleψ⟩ |
      ⟨middle₁, middle₂, hχmiddle₁, hmiddle₁middle₂, hmiddle₂ψ⟩
  · obtain ⟨hstep, hsub⟩ := hχψ.to_targetFree_and_subset
    exact ⟨Or.inl hstep, hsub⟩
  · obtain ⟨hstep₁, hsub₁⟩ := hχmiddle.to_targetFree_and_subset
    obtain ⟨hstep₂, hsub₂⟩ := hmiddleψ.to_targetFree_and_subset
    exact ⟨Or.inr (Or.inl ⟨middle, hstep₁, hstep₂⟩), hsub₂.trans hsub₁⟩
  · obtain ⟨hstep₁, hsub₁⟩ := hχmiddle₁.to_targetFree_and_subset
    obtain ⟨hstep₂, hsub₂⟩ := hmiddle₁middle₂.to_targetFree_and_subset
    obtain ⟨hstep₃, hsub₃⟩ := hmiddle₂ψ.to_targetFree_and_subset
    exact ⟨Or.inr (Or.inr
        ⟨middle₁, middle₂, hstep₁, hstep₂, hstep₃⟩),
      hsub₃.trans (hsub₂.trans hsub₁)⟩

/-- The exact geometric producer after exposing local split and target
creation certificates. -/
def ThreeStepCreationShieldedPrimeCoreDropsAboveAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}, 2 ^ (k - 2) < n →
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ¬IsDecomposable χ →
    ∃ ψ,
      AtMostThree (CreationShieldedRealizableMutationStepAt k) χ ψ ∧
      ∃ support ∈ decompositionPrimeCores χ,
        support ∉ decompositionPrimeCores ψ

/-- Shielded steps plus one explicit destroyed core discharge the strict
prime-core-family producer. -/
theorem primeCoreFamily_ssubset_of_creationShields
    {k : ℕ} (hshielded : ThreeStepCreationShieldedPrimeCoreDropsAboveAt k) :
    ThreeStepPrimeCoreFamilyShrinksAboveAt k := by
  intro n χ hcard hrealizable htarget hindecomposable
  obtain ⟨ψ, hpath, support, hsupportχ, hsupportψ⟩ :=
    hshielded hcard hrealizable htarget hindecomposable
  obtain ⟨htargetFreePath, hsubset⟩ :=
    hpath.creationShielded_to_targetFree_and_subset
  refine ⟨ψ, htargetFreePath,
    Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩⟩
  intro heq
  apply hsupportψ
  rw [heq]
  exact hsupportχ

/-- The exact rational seven-point mutation is a kernel-checked positive
control for the shielded one-step interface. -/
theorem PrimeMutationPositiveControl.source_to_color_creationShieldedMutation :
    CreationShieldedRealizableMutationStepAt 6
      PrimeTwoDeletionCounterexample.color PrimeMutationPositiveControl.color := by
  obtain ⟨changed, hchanged, hagree⟩ :=
    PrimeMutationPositiveControl.source_to_color_singleMutation
  exact ⟨changed,
    PrimeTwoDeletionCounterexample.color_sweepRealizable,
    PrimeMutationPositiveControl.color_sweepRealizable,
    PrimeTwoDeletionCounterexample.color_noStrongSix,
    ⟨hchanged, hagree⟩,
    persistentPrimeSplitShield_of_decomposable
      PrimeMutationPositiveControl.color_decomposable,
    strongTargetCreationShield_of_noStrongTarget
      PrimeMutationPositiveControl.color_noStrongSix⟩

end ErdosSzekeres

end
