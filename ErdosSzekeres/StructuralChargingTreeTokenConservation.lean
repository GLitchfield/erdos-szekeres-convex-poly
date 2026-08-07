module

public import ErdosSzekeres.StructuralChargingGapTokenConservation
public import ErdosSzekeres.StructuralChargingTreeAllocation

@[expose] public section

/-!
# Tree-global conservation of sweep-gap tokens

The leaves of an explicit decomposition tree carry its actual vertices.  The
disjointness at every split makes those leaf owners equivalent to the root
support, and hence to the root sweep-gap tokens.  This packages the local
owner merge as a tree-global nonreuse law.

No higher-rank demand, Pascal profile, or geometric payoff is attached to the
conserved tokens here.
-/

namespace ErdosSzekeres
namespace DecompositionTree

variable {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}

/-- Actual vertex owners, retaining the left/right branch history of the leaf
where each owner originates. -/
def LeafOwner : {s : Finset (Fin n)} → DecompositionTree χ s → Type
  | _, .singleton i => RetainedVertexOwner {i}
  | _, .split lowerTree upperTree _ =>
      LeafOwner lowerTree ⊕ LeafOwner upperTree

/-- The Boolean address of the leaf from which an owner originates. -/
def LeafOwner.path : {s : Finset (Fin n)} →
    (tree : DecompositionTree χ s) → LeafOwner tree → List Bool
  | _, .singleton _, _ => []
  | _, .split lowerTree upperTree _, owner =>
      match owner with
      | .inl lowerOwner => false :: LeafOwner.path lowerTree lowerOwner
      | .inr upperOwner => true :: LeafOwner.path upperTree upperOwner

/-- Every explicit decomposition tree has a nonempty support. -/
theorem support_nonempty (tree : DecompositionTree χ s) : s.Nonempty := by
  induction tree with
  | singleton i => simp
  | @split lower upper lowerTree upperTree deep hlower hupper =>
      exact hlower.mono Finset.subset_union_left

/-- The tree's branch-indexed leaf owners are exactly its actual support
vertices.  Split disjointness supplies the nonreuse step. -/
noncomputable def leafOwnerEquiv (tree : DecompositionTree χ s) :
    LeafOwner tree ≃ RetainedVertexOwner s := by
  induction tree with
  | singleton i => exact Equiv.refl _
  | @split lower upper lowerTree upperTree deep hlower hupper =>
      exact (hlower.sumCongr hupper).trans
        (retainedVertexOwnerSumEquivUnion deep.disjoint)

/-- Folding all branch-indexed leaf owners yields exactly the root
gap-or-sentinel token family. -/
noncomputable def leafOwnerSweepGapTokenEquiv
    (tree : DecompositionTree χ s) :
    LeafOwner tree ≃ SweepGapToken s :=
  (leafOwnerEquiv tree).trans
    (sweepGapTokenOwnerEquiv tree.support_nonempty).symm

/-- The tree-global fold preserves the actual vertex owned at the leaf. -/
theorem leafOwnerSweepGapTokenEquiv_owner
    (tree : DecompositionTree χ s) (leaf : LeafOwner tree) :
    (leafOwnerSweepGapTokenEquiv tree leaf).owner tree.support_nonempty =
      leafOwnerEquiv tree leaf := by
  change (sweepGapTokenOwnerEquiv tree.support_nonempty)
      ((sweepGapTokenOwnerEquiv tree.support_nonempty).symm
        (leafOwnerEquiv tree leaf)) =
    leafOwnerEquiv tree leaf
  exact Equiv.apply_symm_apply _ _

/-- At an internal node, the global fold is extensionally the local
owner-preserving token merge applied after the two child folds. -/
theorem leafOwnerSweepGapTokenEquiv_split
    {lower upper : Finset (Fin n)}
    (lowerTree : DecompositionTree χ lower)
    (upperTree : DecompositionTree χ upper)
    (deep : HasDeepBelowSplit χ lower upper)
    (leaf : LeafOwner (.split lowerTree upperTree deep)) :
    leafOwnerSweepGapTokenEquiv (.split lowerTree upperTree deep) leaf =
      sweepGapTokenMergeEquiv lowerTree.support_nonempty
        upperTree.support_nonempty deep.disjoint
        ((leafOwnerSweepGapTokenEquiv lowerTree).sumCongr
          (leafOwnerSweepGapTokenEquiv upperTree) leaf) := by
  apply SweepGapToken.owner_injective
    (lowerTree.support_nonempty.mono Finset.subset_union_left)
  rw [leafOwnerSweepGapTokenEquiv_owner,
    sweepGapTokenMergeEquiv_owner]
  cases leaf with
  | inl leaf =>
      change retainedVertexOwnerOfChild
          (.inl (leafOwnerEquiv lowerTree leaf)) =
        retainedVertexOwnerOfChild
          (.inl ((leafOwnerSweepGapTokenEquiv lowerTree leaf).owner
            lowerTree.support_nonempty))
      rw [leafOwnerSweepGapTokenEquiv_owner]
  | inr leaf =>
      change retainedVertexOwnerOfChild
          (.inr (leafOwnerEquiv upperTree leaf)) =
        retainedVertexOwnerOfChild
          (.inr ((leafOwnerSweepGapTokenEquiv upperTree leaf).owner
            upperTree.support_nonempty))
      rw [leafOwnerSweepGapTokenEquiv_owner]

/-- Equal root owners came from the same leaf charge and therefore the same
tree address.  This is the tree-global nonreuse law for the carrier. -/
theorem leafOwner_nonreuse
    (tree : DecompositionTree χ s) (first second : LeafOwner tree)
    (howner :
      (leafOwnerSweepGapTokenEquiv tree first).owner
          tree.support_nonempty =
        (leafOwnerSweepGapTokenEquiv tree second).owner
          tree.support_nonempty) :
    first = second ∧ first.path tree = second.path tree := by
  have heq : first = second := by
    rw [leafOwnerSweepGapTokenEquiv_owner,
      leafOwnerSweepGapTokenEquiv_owner] at howner
    exact (leafOwnerEquiv tree).injective howner
  exact ⟨heq, congrArg (LeafOwner.path tree) heq⟩

end DecompositionTree
end ErdosSzekeres

end
