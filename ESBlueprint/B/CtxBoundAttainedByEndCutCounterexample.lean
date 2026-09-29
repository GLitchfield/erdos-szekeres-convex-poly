import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

open Ctx

/-- The counterexample context: (a,u,k) = (3,4,5), word `1L S S 2U S S`, maxima (3,1). -/
def ctxEndCutCex : Ctx.Context := ⟨3, 4, 5,
  [Letter.ext 1 Side.lower, Letter.child, Letter.child,
    Letter.ext 2 Side.upper, Letter.child, Letter.child], [3, 1]⟩

theorem ctxEndCutCex_childPositions : ctxEndCutCex.childPositions = [1, 2, 4, 5] := by decide +kernel
theorem ctxEndCutCex_numRuns : 2 ≤ ctxEndCutCex.numRuns := by decide +kernel

theorem ctxEndCutCex_witness_cut :
    (ctxEndCutCex.part [1, 2] Side.lower 1).bound +
      (ctxEndCutCex.part (ctxEndCutCex.childPositions.filter (fun p => p ∉ [1, 2])) Side.upper
        (ctxEndCutCex.k - 1 - 1)).bound = 1 := by decide +kernel

theorem ctxEndCutCex_first_lower :
    ∀ d ∈ [1, 2, 3], (ctxEndCutCex.part [1] Side.lower d).bound +
      (ctxEndCutCex.part (ctxEndCutCex.childPositions.filter (fun q => q ≠ 1)) Side.upper
        (ctxEndCutCex.k - 1 - d)).bound = 0 := by decide +kernel

theorem ctxEndCutCex_first_upper :
    ∀ d ∈ [1, 2, 3], (ctxEndCutCex.part [1] Side.upper (ctxEndCutCex.k - 1 - d)).bound +
      (ctxEndCutCex.part (ctxEndCutCex.childPositions.filter (fun q => q ≠ 1)) Side.lower d).bound = 0 := by
  decide +kernel

theorem ctxEndCutCex_last_lower :
    ∀ d ∈ [1, 2, 3], (ctxEndCutCex.part [5] Side.lower d).bound +
      (ctxEndCutCex.part (ctxEndCutCex.childPositions.filter (fun q => q ≠ 5)) Side.upper
        (ctxEndCutCex.k - 1 - d)).bound = 0 := by decide +kernel

theorem ctxEndCutCex_last_upper :
    ∀ d ∈ [1, 2, 3], (ctxEndCutCex.part [5] Side.upper (ctxEndCutCex.k - 1 - d)).bound +
      (ctxEndCutCex.part (ctxEndCutCex.childPositions.filter (fun q => q ≠ 5)) Side.lower d).bound = 0 := by
  decide +kernel

/-- The end-cut normal form ctx_bound_attained_by_end_cut is false. At (a,u,k) = (3,4,5) the well-formed two-run context with word [ext 1 lower, child, child, ext 2 upper, child, child] and maxima [3,1] has bound 1, attained by the run-boundary cut {1,2} | {4,5}, while every cut isolating the first or the last child position, on either side and at every admissible coupling, is worth 0. Found by the Claude run claude-uniform-mechanism-20260928 (Track A); the same failure occurs on 24 contexts at (3,4,5) and 36 at (3,5,6), all with a = 3, which the conjecture's falsifier never sampled. The proof takes bound >= 1 from ctx_bound_cut_le at the witness cut and decides the twelve end-cut values in the kernel.
@node
@ws B
@kind refutation
@depends ErdosSzekeres.ctx_bound_cut_le
@consumer ErdosSzekeres.ctx_bound_attained_by_end_cut -/
theorem ctx_bound_attained_by_end_cut_counterexample : ¬ (∀ (σ : Ctx.Context), σ.WellFormed → 2 ≤ σ.numRuns → ∃ p ∈ σ.childPositions, ((∀ q ∈ σ.childPositions, p ≤ q) ∨ (∀ q ∈ σ.childPositions, q ≤ p)) ∧ ∃ d, 1 ≤ d ∧ d ≤ σ.k - 2 ∧ (σ.bound ≤ (σ.part [p] Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k - 1 - d)).bound ∨ σ.bound ≤ (σ.part [p] Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d).bound)) := by
  intro h
  have hwf : ctxEndCutCex.WellFormed := by
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp [ctxEndCutCex]
    · intro p l s hletter
      have hp : p < 6 := by
        by_contra hp
        rw [Ctx.Context.letterAt_of_length_le _
          (show ctxEndCutCex.word.length ≤ p by simp [ctxEndCutCex]; omega)] at hletter
        cases hletter
      interval_cases p <;> simp [ctxEndCutCex, Ctx.Context.letterAt] at hletter
      all_goals
        rcases hletter with ⟨rfl, rfl⟩
        decide
  obtain ⟨p, hp, hend, d, hd1, hd2, hcut⟩ := h ctxEndCutCex hwf ctxEndCutCex_numRuns
  have hbound : 1 ≤ ctxEndCutCex.bound := by
    have hle := (ctx_bound_cut_le ctxEndCutCex ctxEndCutCex_numRuns [1, 2] (by decide +kernel) 1
      le_rfl (by decide)).1
    rw [ctxEndCutCex_witness_cut] at hle
    exact hle
  have hd3 : d ≤ 3 := hd2
  have hdmem : d ∈ [1, 2, 3] := by simp; omega
  have hp15 : p = 1 ∨ p = 5 := by
    rw [ctxEndCutCex_childPositions] at hp hend
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp at hend ⊢
  rcases hp15 with rfl | rfl
  · rcases hcut with hc | hc
    · have := ctxEndCutCex_first_lower d hdmem; omega
    · have := ctxEndCutCex_first_upper d hdmem; omega
  · rcases hcut with hc | hc
    · have := ctxEndCutCex_last_lower d hdmem; omega
    · have := ctxEndCutCex_last_upper d hdmem; omega

end ErdosSzekeres
