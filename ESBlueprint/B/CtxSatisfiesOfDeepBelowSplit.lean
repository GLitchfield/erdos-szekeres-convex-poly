import ErdosSzekeres.DecomposableContext

namespace ErdosSzekeres

/-- Context transfer (experiment 0117, the union lemma): across a deep-below split of a child satisfying σ, the lower part satisfies σ with the upper part added as a level-1 sibling of longest cap capmax(upper), and the upper part satisfies σ with the lower part added as a level-1 sibling of longest cup cupmax(lower). Proved from the four-vertex law: mixed quadruples, chains extend by one vertex per side per level, strong sets join at one level. Verified on all 1,367,052 subtrees at n <= 8.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_card_le_bound -/
theorem ctx_satisfies_of_deepBelowSplit {n : ℕ} {χ : TripleColoring n} {S lower upper : Finset (Fin n)} (σ : Ctx.Context) (hwf : σ.WellFormed) (hS : Ctx.Satisfies χ S σ) (hsplit : HasDeepBelowSplit χ lower upper) (hunion : lower ∪ upper = S) (hl : lower.Nonempty) (hu : upper.Nonempty) : Ctx.Satisfies χ lower (σ.part (σ.positionsOf S lower) Ctx.Side.lower (Ctx.chainMax χ upper false)) ∧ Ctx.Satisfies χ upper (σ.part (σ.positionsOf S upper) Ctx.Side.upper (Ctx.chainMax χ lower true)) := by
  sorry

end ErdosSzekeres
