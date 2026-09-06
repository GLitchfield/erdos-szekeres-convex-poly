import ErdosSzekeres.DecomposableContextLemmas
import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit
import ESBlueprint.B.CtxBoundAdditive

namespace ErdosSzekeres

/-- The context induction (experiments 0117-0121): a decomposable coloring on S that satisfies the constraints of a well-formed context σ has at most bound σ vertices. Induction on IsDecomposableOn: split, transfer the context to both parts (ctx_satisfies_of_deepBelowSplit), apply the hypothesis, dominate the two-parameter coupling by the one-parameter one (ctx_bound_antitone), and finish with the additivity conjecture (ctx_bound_additive). At the root context this is DecomposableStateUpper for all parameters.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_satisfies_of_deepBelowSplit, ErdosSzekeres.ctx_bound_antitone, ErdosSzekeres.ctx_bound_additive
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem ctx_card_le_bound {n : ℕ} {χ : TripleColoring n} {S : Finset (Fin n)} (σ : Ctx.Context) (hwf : σ.WellFormed) (hdec : IsDecomposableOn χ S) (hS : Ctx.Satisfies χ S σ) : S.card ≤ σ.bound := by
  induction hdec generalizing σ with
  | singleton i =>
    rw [Finset.card_singleton]
    exact Ctx.one_le_bound_of_satisfies_singleton hS
  | @split lower upper hlower hupper hdeep ihL ihU =>
    have hlne : lower.Nonempty := Ctx.nonempty_of_isDecomposableOn hlower
    have hune : upper.Nonempty := Ctx.nonempty_of_isDecomposableOn hupper
    have hk : 2 ≤ σ.k := hwf.1.trans hwf.2.2.1
    obtain ⟨hSL, hSU⟩ := ctx_satisfies_of_deepBelowSplit σ hwf hS hdeep rfl hlne hune
    have hsum := Ctx.chainMax_add_chainMax_le hdeep hS
    have hmL := Ctx.one_le_chainMax (χ := χ) hlne true
    have hmU := Ctx.one_le_chainMax (χ := χ) hune false
    set mL := Ctx.chainMax χ lower true with hmLdef
    set mU := Ctx.chainMax χ upper false with hmUdef
    have hlen : σ.childPositions.length = (lower ∪ upper).card := hS.1
    -- the lower part with the strengthened sibling maximum `k - 1 - mL`
    have hSL' : Ctx.Satisfies χ lower
        (σ.part (σ.positionsOf (lower ∪ upper) lower) Ctx.Side.lower (σ.k - 1 - mL)) :=
      Ctx.satisfies_part_lower_of_cup_le hwf hSL fun C hC hcup =>
        (Ctx.le_chainMax_of_isCupSet hC hcup).trans (by omega)
    have hwfL := hwf.part (σ.positionsOf (lower ∪ upper) lower) Ctx.Side.lower
      (m := σ.k - 1 - mL) (by omega) (by omega)
    have hwfU := hwf.part (σ.positionsOf (lower ∪ upper) upper) Ctx.Side.upper
      (m := mL) hmL (by omega)
    have h1 := ihL _ hwfL hSL'
    have h2 := ihU _ hwfU hSU
    have hadd := (ctx_bound_additive σ hwf (σ.positionsOf (lower ∪ upper) lower)
      (Ctx.positionsOf_subset hlen Finset.subset_union_left)
      (Ctx.positionsOf_ne_nil σ hlne)
      (Ctx.positionsOf_length_lt hlen hdeep.disjoint hune)
      (σ.k - 1 - mL) (by omega) (by omega)).1
    rw [Ctx.positionsOf_compl hlen hdeep.disjoint, show σ.k - 1 - (σ.k - 1 - mL) = mL by omega] at hadd
    rw [Finset.card_union_of_disjoint hdeep.disjoint]
    exact (Nat.add_le_add h1 h2).trans hadd

end ErdosSzekeres
