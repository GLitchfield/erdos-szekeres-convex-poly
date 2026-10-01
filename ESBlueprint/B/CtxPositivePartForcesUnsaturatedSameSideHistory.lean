import ESBlueprint.B.CtxPartBoundZeroOfSameSideLargeSiblingMaximum

namespace ErdosSzekeres

/-- A positive proper recursive part forces every indexed source sibling maximum on its selected axis to be at most k-3. Positive actual external labels, k>=3 and one actual removed child suffice for arbitrary raw contexts, unused indexed levels, keep lists and new maximum. The closed saturation-annihilation theorem gives the contrapositive. Supplies a strict history ceiling for the positive component of maximal-segment exchange; no well-formedness, run-count, legal-coupling or global assumption and no sufficiency/lower-bound converse.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_bound_zero_of_same_side_large_sibling_maximum
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_positive_part_forces_unsaturated_same_side_history (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (hk : 3 ≤ σ.k) (keep : List ℕ) (s : Ctx.Side) (m r : ℕ) (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep) (hbound : 0 < (σ.part keep s m).bound) : ∀ N ∈ σ.levelsOn s 0, σ.maximumAt N ≤ σ.k - 3 := by
  intro N hN
  by_contra hbad
  have hlarge : σ.k - 2 ≤ σ.maximumAt N := by omega
  have hzero := ctx_part_bound_zero_of_same_side_large_sibling_maximum
    σ hpositive s N hN hlarge keep m r hr hremoved
  omega

end ErdosSzekeres
