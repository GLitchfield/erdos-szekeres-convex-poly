import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

/-- Context-bound additivity for an arbitrary three-block partition of one contiguous child run: the two outer nonempty blocks form one part and the nonempty middle block forms the other. All three block lengths are arbitrary, with both orientations and every admissible coupling. The proposed proof reduces the outer runs to the proved singleton-ended sandwich using restricted contraction and external-letter invariance.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive_single_run
@falsifier ctx_approved_sandwich.py -/
theorem ctx_bound_additive_three_blocks (σ : Ctx.Context) (hwf : σ.WellFormed)
  (b l m r : ℕ) (hpos : σ.childPositions = List.range' b (l + m + r))
  (hl : 0 < l) (hm : 0 < m) (hr : 0 < r)
  (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) :
  (σ.part (List.range' b l ++ List.range' (b + l + m) r) Ctx.Side.lower d).bound +
      (σ.part (List.range' (b + l) m) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧
  (σ.part (List.range' b l ++ List.range' (b + l + m) r) Ctx.Side.upper (σ.k - 1 - d)).bound +
      (σ.part (List.range' (b + l) m) Ctx.Side.lower d).bound ≤ σ.bound := by
  sorry

end ErdosSzekeres
