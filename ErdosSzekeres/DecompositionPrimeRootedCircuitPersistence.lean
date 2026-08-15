module

public import ErdosSzekeres.DecompositionPrimeMutationLocality

@[expose] public section

/-!
# Carrier-internal persistence for rooted-circuit mutation proposals

A changed triple lying wholly inside one side of a deep-below split cannot
alter any color constrained by that split: every constrained triple crosses
the two sides.  This file isolates that local fact and its exact source-side
consumer.  It does not produce carrier-internal splits for arbitrary
target-free realizable colorings and therefore does not close the Layer-F
normalization obligation.
-/

namespace ErdosSzekeres

/-- A deep-below split persists across a single-triple mutation when all three
vertices of the changed triple lie on one side of the split. -/
theorem HasDeepBelowSplit.persists_of_singleMutation_internal
    {n : ℕ} {χ ψ : TripleColoring n} {changed : OrderedTriple n}
    {lower upper : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper)
    (hmutation : χ changed ≠ ψ changed ∧
      ∀ u, u ≠ changed → χ u = ψ u)
    (hinternal : changed.support ⊆ lower ∨ changed.support ⊆ upper) :
    HasDeepBelowSplit ψ lower upper := by
  refine ⟨hsplit.disjoint, ?_⟩
  intro t hi hj hk hnotLower hnotUpper
  have ht : t ≠ changed := by
    intro heq
    subst t
    rcases hinternal with hlower | hupper
    · apply hnotLower
      exact ⟨hlower (by simp [OrderedTriple.support]),
        hlower (by simp [OrderedTriple.support]),
        hlower (by simp [OrderedTriple.support])⟩
    · apply hnotUpper
      exact ⟨hupper (by simp [OrderedTriple.support]),
        hupper (by simp [OrderedTriple.support]),
        hupper (by simp [OrderedTriple.support])⟩
  calc
    ψ t = χ t := (hmutation.2 t ht).symm
    _ = if t.j ∈ lower then Turn.left else Turn.right :=
      hsplit.crossing t hi hj hk hnotLower hnotUpper

/-- The source-only witness family needed to use carrier-internal persistence
on supports at or above one cardinality stratum.

This definition is independent of the endpoint coloring, but it remains a
producer obligation: it strengthens mere source split existence by requiring
an internal-carrier witness for every relevant support.  The cardinality bound
is essential: on the support consisting of the changed triple itself, no proper
split can put all three changed vertices on one side. -/
def HasCarrierInternalSourceSplitsAboveAt {n : ℕ}
    (m : ℕ) (χ : TripleColoring n) (changed : OrderedTriple n) : Prop :=
  ∀ support : Finset (Fin n), m ≤ support.card → changed.support ⊆ support →
    HasProperDeepBelowSplitOn χ support →
    ∃ lower upper : Finset (Fin n),
      lower.Nonempty ∧ upper.Nonempty ∧ lower ∪ upper = support ∧
        HasDeepBelowSplit χ lower upper ∧
        (changed.support ⊆ lower ∨ changed.support ⊆ upper)

/-- Source-side internal-carrier witnesses preserve proper splits on the same
bounded family of supports.  This is only a cardinality-restricted consequence,
not the existing unfiltered `HasPersistentPrimeSplitShield`. -/
theorem HasCarrierInternalSourceSplitsAboveAt.to_endpointSplits
    {m n : ℕ} {χ ψ : TripleColoring n} {changed : OrderedTriple n}
    (hsource : HasCarrierInternalSourceSplitsAboveAt m χ changed)
    (hmutation : χ changed ≠ ψ changed ∧
      ∀ u, u ≠ changed → χ u = ψ u) :
    ∀ support : Finset (Fin n), m ≤ support.card → changed.support ⊆ support →
      HasProperDeepBelowSplitOn χ support →
      HasProperDeepBelowSplitOn ψ support := by
  intro support hcard hcarrier hsplit
  obtain ⟨lower, upper, hlower, hupper, hunion, hdeep, hinternal⟩ :=
    hsource support hcard hcarrier hsplit
  exact ⟨lower, upper, hlower, hupper, hunion,
    hdeep.persists_of_singleMutation_internal hmutation hinternal⟩

end ErdosSzekeres

end
