module

public import ErdosSzekeres.StructuralChargingHigherCone
public import ErdosSzekeres.StructuralChargingConservedBranch

@[expose] public section

/-!
# Saturated branches supply exact predecessor parameters

The arithmetic validity predicate for a saturated published branch already
identifies its selected child index as the immediate predecessor of the outer
parameter.  These theorems use that equality to obtain a strictly smaller E3
state, rewrite the outer cap or cup avoidance into the local cone hypothesis,
and construct one actual selected core containing every canonical pivot.
-/

namespace ErdosSzekeres

namespace PublishedSaturatedBranch.Valid

/-- A valid upper saturated branch selects a strictly smaller cap parameter. -/
theorem upper_index_lt {a u k a' u' : ℕ}
    (hvalid : PublishedSaturatedBranch.Valid a u k a' u' .upper) : a' < a := by
  exact hvalid.1 ▸ Nat.lt_succ_self a'

/-- A valid lower saturated branch selects a strictly smaller cup parameter. -/
theorem lower_index_lt {a u k a' u' : ℕ}
    (hvalid : PublishedSaturatedBranch.Valid a u k a' u' .lower) : u' < u := by
  exact hvalid.1 ▸ Nat.lt_succ_self u'

/-- The upper-branch predecessor decreases the sum of the two state parameters. -/
theorem upper_predecessor_sum_lt {a u k a' u' : ℕ}
    (hvalid : PublishedSaturatedBranch.Valid a u k a' u' .upper) :
    a' + u < a + u := by
  exact Nat.add_lt_add_right hvalid.upper_index_lt u

/-- The lower-branch predecessor decreases the sum of the two state parameters. -/
theorem lower_predecessor_sum_lt {a u k a' u' : ℕ}
    (hvalid : PublishedSaturatedBranch.Valid a u k a' u' .lower) :
    a + u' < a + u := by
  exact Nat.add_lt_add_left hvalid.lower_index_lt a

end PublishedSaturatedBranch.Valid

/-- On an upper saturated branch, validity simultaneously supplies strict
cap-parameter descent and rewrites the outer cap avoidance into the exact
successor hypothesis needed by the higher cone. -/
theorem exists_publishedUpperPivotSlice_of_saturated_predecessors
    {n outerA u k lowerIndex : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (upperSlice : PublishedCapChildSlice outerA u k upper)
    (hvalid : PublishedSaturatedBranch.Valid
      outerA u k upperSlice.index lowerIndex .upper)
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlower : lower.Nonempty)
    (hupperNonempty : upper.Nonempty)
    (hupper : IsDecomposableOn chi upper)
    (hpredecessors : ∀ a, a < outerA → DecomposableStateUpper a u k)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) outerA)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) u)
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    ∃ slice : PublishedCapChildSlice outerA u k upper,
      ∀ source : HiddenGapSource lower upper .right,
        source.enteringPivot ∈ slice.core := by
  have hindexLt : upperSlice.index < outerA := hvalid.upper_index_lt
  have hstate : DecomposableStateUpper upperSlice.index u k :=
    hpredecessors upperSlice.index hindexLt
  have hnoCapSucc :
      ¬ContainsCapSet chi (lower ∪ upper) (upperSlice.index + 1) := by
    simpa only [hvalid.1] using hnoCap
  exact exists_publishedUpperPivotSlice_of_predecessor_state
    (outerA := outerA) (a := upperSlice.index)
    (by omega) hdeep hlower hupperNonempty hupper upperSlice.index_eq.symm
    hstate hnoCapSucc hnoCup hnoStrong

/-- Color-dually, a lower saturated branch supplies strict cup-parameter
descent and the exact successor-cup avoidance needed by the lower pivot cone. -/
theorem exists_publishedLowerPivotSlice_of_saturated_predecessors
    {n a outerU k upperIndex : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (lowerSlice : PublishedChildSlice a outerU k lower)
    (hvalid : PublishedSaturatedBranch.Valid
      a outerU k upperIndex lowerSlice.index .lower)
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hlowerNonempty : lower.Nonempty)
    (hupper : upper.Nonempty)
    (hlower : IsDecomposableOn chi lower)
    (hpredecessors : ∀ u, u < outerU → DecomposableStateUpper a u k)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) a)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) outerU)
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    ∃ slice : PublishedChildSlice a outerU k lower,
      ∀ source : HiddenGapSource lower upper .left,
        source.enteringPivot ∈ slice.core := by
  have hindexLt : lowerSlice.index < outerU := hvalid.lower_index_lt
  have hstate : DecomposableStateUpper a lowerSlice.index k :=
    hpredecessors lowerSlice.index hindexLt
  have hnoCupSucc :
      ¬ContainsCupSet chi (lower ∪ upper) (lowerSlice.index + 1) := by
    simpa only [hvalid.1] using hnoCup
  exact exists_publishedLowerPivotSlice_of_predecessor_state
    (outerU := outerU) (u := lowerSlice.index)
    (by omega) hdeep hlowerNonempty hupper hlower lowerSlice.index_eq.symm
    hstate hnoCap hnoCupSucc hnoStrong

/-- Feasible saturated-branch arithmetic and both strictly smaller predecessor
families select a branch on which one actual published core retains every
canonical pivot.  The returned slice may reselect the core, but its index is
the same deterministic published index used by the validity predicate. -/
theorem exists_saturatedPivotSlice_of_predecessors
    {n a u k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (lowerSlice : PublishedChildSlice a u k lower)
    (upperSlice : PublishedCapChildSlice a u k upper)
    (ha : 4 ≤ a) (hu : 4 ≤ u) (hak : a ≤ k) (huk : u ≤ k)
    (hlowerNonempty : lower.Nonempty)
    (hupperNonempty : upper.Nonempty)
    (hlower : IsDecomposableOn chi lower)
    (hupper : IsDecomposableOn chi upper)
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hsum : upperSlice.index + lowerSlice.index ≤ k - 1)
    (hactive : k + 4 ≤ a + u)
    (htotal : lower.card + upper.card = decomposableThreshold a u k + 1)
    (hlowerOuter : lower.card ≤ decomposableThreshold a u k)
    (hupperOuter : upper.card ≤ decomposableThreshold a u k)
    (hpredecessors : ∀ a' u', a' + u' < a + u →
      DecomposableStateUpper a' u' k)
    (hnoCap : ¬ContainsCapSet chi (lower ∪ upper) a)
    (hnoCup : ¬ContainsCupSet chi (lower ∪ upper) u)
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    (∃ slice : PublishedChildSlice a u k lower,
        ∀ source : HiddenGapSource lower upper .left,
          source.enteringPivot ∈ slice.core) ∨
      ∃ slice : PublishedCapChildSlice a u k upper,
        ∀ source : HiddenGapSource lower upper .right,
          source.enteringPivot ∈ slice.core := by
  obtain ⟨branch, hvalid, _⟩ := published_slice_pair_saturation_existsUnique
    lowerSlice upperSlice ha hu hak huk hlowerNonempty hupperNonempty
    hsum hactive htotal hlowerOuter hupperOuter
  cases branch with
  | lower =>
      exact Or.inl (exists_publishedLowerPivotSlice_of_saturated_predecessors
        lowerSlice hvalid hdeep hlowerNonempty hupperNonempty hlower
        (fun u' hu' ↦ hpredecessors a u' (Nat.add_lt_add_left hu' a))
        hnoCap hnoCup hnoStrong)
  | upper =>
      exact Or.inr (exists_publishedUpperPivotSlice_of_saturated_predecessors
        upperSlice hvalid hdeep hlowerNonempty hupperNonempty hupper
        (fun a' ha' ↦ hpredecessors a' u (Nat.add_lt_add_right ha' u))
        hnoCap hnoCup hnoStrong)

end ErdosSzekeres
