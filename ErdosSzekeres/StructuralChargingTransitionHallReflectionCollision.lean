module

public import ErdosSzekeres.StructuralChargingTransitionHallReflection
public import ErdosSzekeres.StructuralChargingTransitionHallCollision

@[expose] public section

/-!
# The reflected encoding separates the frozen rigid collision

The two rigid full-ideal spans in the `n = 12`, `k = 7` counterexample cross
their allocated root in opposite orientations.  The reflected candidate
system leaves the first full ideal unchanged and sends the second to the empty
ideal, so this formerly Hall-deficient pair now expands to two states.
-/

namespace ErdosSzekeres
namespace StructuralChargingTransitionHallCollision

open StructuralChargingTransitionHallCollisionData

/-- The empty `2 x 3` ideal. -/
def emptyIdeal : PascalGridIdeal 2 3 where
  cells := ∅
  isLowerSet := by
    intro _ _ _ hmem
    simp at hmem

theorem reflectedComplement_fullIdeal :
    PascalGridIdeal.reflectedComplement fullIdeal = emptyIdeal := by
  ext cell
  simp [PascalGridIdeal.reflectedComplement, fullIdeal, emptyIdeal]

theorem first_reflectedCandidates :
    allocatedReflectedEndpointRankTransitionCandidates
      color lower upper .right (by decide : 1 ≤ 3) (by decide : 3 < 7) first =
        {fullIdeal} := by
  have hcandidates :
      allocatedEndpointTransitionCandidates profiles first = {fullIdeal} :=
    (allocatedEndpointTransitionCandidates_eq_singleton_iff
      profiles first fullIdeal).mpr first_rigid
  simpa [allocatedReflectedEndpointRankTransitionCandidates, profiles] using hcandidates

theorem second_reflectedCandidates :
    allocatedReflectedEndpointRankTransitionCandidates
      color lower upper .right (by decide : 1 ≤ 3) (by decide : 3 < 7) second =
        {emptyIdeal} := by
  have hcandidates :
      allocatedEndpointTransitionCandidates profiles second = {fullIdeal} :=
    (allocatedEndpointTransitionCandidates_eq_singleton_iff
      profiles second fullIdeal).mpr second_rigid
  simp only [allocatedReflectedEndpointRankTransitionCandidates, second]
  change (allocatedEndpointTransitionCandidates profiles second).map
      (PascalGridIdeal.reflectedComplementEquiv 2 3).toEmbedding = {emptyIdeal}
  rw [hcandidates]
  simp [PascalGridIdeal.reflectedComplementEquiv, reflectedComplement_fullIdeal]

/-- The reflected candidates repair the exact pair expansion that failed for
the unreflected endpoint profiles. -/
theorem reflectedPairExpansion :
    2 ≤ ((allocatedReflectedEndpointRankTransitionCandidates
      color lower upper .right (by decide : 1 ≤ 3) (by decide : 3 < 7) first) ∪
      (allocatedReflectedEndpointRankTransitionCandidates
      color lower upper .right (by decide : 1 ≤ 3) (by decide : 3 < 7) second)).card := by
  rw [first_reflectedCandidates, second_reflectedCandidates]
  decide

end StructuralChargingTransitionHallCollision
end ErdosSzekeres

end
