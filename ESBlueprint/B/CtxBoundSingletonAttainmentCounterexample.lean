import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

set_option maxHeartbeats 4000000

/-- Full singleton attainment PEEL is false even for WellFormed contexts with a,u>=4, at least two runs and bound>=2. The explicit context (4,4,5), word 3U4LSS1L2USS and maxima (1,1,1,1), has a run-block cut of value2 whereas every one of its24 legal singleton cuts has value1. Oldest unit flanks transport the lower-global SS1L2USS failure into the stated domain. This refutes the auxiliary normal form, not the happy-ending conjecture. Diagnostic witness runs/r19-sol-20261002/PEEL.counterexample.json, exact falsifier20261002-100340-9841d8; search singleton attainment counterexample cut bound found no duplicate.
@node
@ws B
@kind refutation
@depends ErdosSzekeres.ctx_bound_cut_le
@dangling-ok Approved R19 full PEEL counterexample; the original conjecture is preserved on independent node/CtxBoundAttainedBySingletonCut from the same pinned base -/
theorem ctx_bound_singleton_attainment_counterexample : ¬ (∀ (σ : Ctx.Context), σ.WellFormed → 4 ≤ σ.a → 4 ≤ σ.u →
    2 ≤ σ.numRuns → 2 ≤ σ.bound →
    ∃ p ∈ σ.childPositions, ∃ (s : Ctx.Side) (c : ℕ),
      1 ≤ c ∧ c ≤ σ.k - 2 ∧
      σ.bound = (σ.part [p] s c).bound +
        (σ.part (σ.childPositions.filter (fun q => q ≠ p))
          (match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower)
          (σ.k - 1 - c)).bound) := by
  intro h
  let σ : Ctx.Context := ⟨4, 4, 5,
    [Ctx.Letter.ext 3 Ctx.Side.upper, Ctx.Letter.ext 4 Ctx.Side.lower,
      Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
      Ctx.Letter.ext 2 Ctx.Side.upper, Ctx.Letter.child, Ctx.Letter.child],
    [1, 1, 1, 1]⟩
  have hwf : σ.WellFormed := by
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp [σ]
    · intro p l s hletter
      have hp : p < 8 := by
        by_contra hp
        rw [Ctx.Context.letterAt_of_length_le σ
          (show σ.word.length ≤ p by simp [σ]; omega)] at hletter
        cases hletter
      interval_cases p <;> simp [σ, Ctx.Context.letterAt] at hletter
      all_goals
        rcases hletter with ⟨rfl, rfl⟩
        decide
  have hpositions : σ.childPositions = [2, 3, 6, 7] := by decide +kernel
  have hruns : 2 ≤ σ.numRuns := by decide +kernel
  have hbound : 2 ≤ σ.bound := by
    have hle := (ctx_bound_cut_le σ hruns [2, 3] (by decide +kernel) 1
      (by decide) (by decide)).1
    have hvalue :
        (σ.part [2, 3] Ctx.Side.lower 1).bound +
          (σ.part (σ.childPositions.filter (fun p => p ∉ [2, 3])) Ctx.Side.upper
            (σ.k - 1 - 1)).bound = 2 := by
      set_option maxRecDepth 10000 in decide +kernel
    rw [hvalue] at hle
    exact hle
  have hsingleton : ∀ p ∈ [2, 3, 6, 7], ∀ (s : Ctx.Side) (c : ℕ),
      1 ≤ c → c ≤ 3 →
      (σ.part [p] s c).bound +
        (σ.part (σ.childPositions.filter (fun q => q ≠ p))
          (match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower)
          (σ.k - 1 - c)).bound = 1 := by
    intro p hp s c hc1 hc3
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals
      cases s <;> interval_cases c
    all_goals
      set_option maxRecDepth 10000 in decide +kernel
  obtain ⟨p, hp, s, c, hc1, hc2, heq⟩ := h σ hwf (by decide) (by decide) hruns hbound
  rw [hpositions] at hp
  have hc3 : c ≤ 3 := hc2
  have hsum := hsingleton p hp s c hc1 hc3
  omega

end ErdosSzekeres
