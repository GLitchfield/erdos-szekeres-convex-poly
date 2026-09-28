import ESBlueprint.B.CtxBoundAdditiveSandwichSingletonEnds

namespace ErdosSzekeres

/-- Sandwich additivity for a contiguous child run split into three nonempty blocks, with at least one outer block a singleton. Includes both orientations, reflection, arbitrary middle and other outer block lengths, and every admissible coupling. The statement is the approved intermediate goal beyond the proved singleton-ended case; it remains open until the unbounded outer-run comparison is established.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_bound_additive_sandwich_one_singleton_end (σ : Ctx.Context) (hwf : σ.WellFormed)
  (b l m r : ℕ) (hpos : σ.childPositions = List.range' b (l + m + r))
  (hl : 0 < l) (hm : 0 < m) (hr : 0 < r) (hend : l = 1 ∨ r = 1)
  (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) :
  (σ.part (List.range' b l ++ List.range' (b + l + m) r) Ctx.Side.lower d).bound +
      (σ.part (List.range' (b + l) m) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧
  (σ.part (List.range' b l ++ List.range' (b + l + m) r) Ctx.Side.upper (σ.k - 1 - d)).bound +
      (σ.part (List.range' (b + l) m) Ctx.Side.lower d).bound ≤ σ.bound := by
  sorry

end ErdosSzekeres
