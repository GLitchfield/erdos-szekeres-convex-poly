import ESBlueprint.B.CtxBoundAttainedByEndCut

namespace ErdosSzekeres

/-- A raw multi-run context has bound at most N exactly when both orientation sums of every proper interval cut at every legal coupling have value at most N. Fuel stability replaces recursive approximations by the actual part bounds. This reusable upper certificate permits a local cut DAG to reuse checked smaller-context values rather than reduce the full recursion repeatedly; no well-formedness or extra k assumption is required.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_cut_le
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_bound_le_iff_all_interval_cuts_le (σ : Ctx.Context) (hruns : 2 ≤ σ.numRuns) (N : ℕ) :
    σ.bound ≤ N ↔
      ∀ (block : List ℕ), block ∈ σ.blocks →
        ∀ (d : ℕ), 1 ≤ d → d ≤ σ.k - 2 →
          (σ.part block Ctx.Side.lower d).bound +
              (σ.part (σ.childPositions.filter (fun p ↦ p ∉ block))
                Ctx.Side.upper (σ.k - 1 - d)).bound ≤ N ∧
          (σ.part block Ctx.Side.upper (σ.k - 1 - d)).bound +
              (σ.part (σ.childPositions.filter (fun p ↦ p ∉ block))
                Ctx.Side.lower d).bound ≤ N := by
  classical
  constructor
  · intro h block hb d hd hdk
    have hcut := ctx_bound_cut_le σ hruns block hb d hd hdk
    exact ⟨hcut.1.trans h, hcut.2.trans h⟩
  · intro hcuts
    unfold Ctx.Context.bound
    rw [Ctx.Context.boundFuel.eq_2, if_neg (by omega : ¬ σ.numRuns ≤ 1)]
    dsimp only
    apply Ctx.getD_max?_le
    intro x hx
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    obtain ⟨block, hb, d', hd', hx⟩ := hx
    have hdk : d' + 1 ≤ σ.k - 2 := by omega
    have hfB : ∀ s m,
        (σ.part block s m).childPositions.length + 1 ≤ σ.childPositions.length :=
      fun s m => Ctx.Context.part_childPositions_length_lt_of_mem_blocks hb s m
    have hfR : ∀ s m,
        (σ.part (σ.childPositions.filter (fun p ↦ p ∉ block)) s m).childPositions.length + 1 ≤
          σ.childPositions.length :=
      fun s m => Ctx.Context.part_rest_childPositions_length_lt_of_mem_blocks hb s m
    rcases hx with rfl | rfl
    · rw [Ctx.Context.boundFuel_eq_bound _ (hfB _ _),
        Ctx.Context.boundFuel_eq_bound _ (hfR _ _)]
      exact (hcuts block hb (d' + 1) (by omega) hdk).1
    · rw [Ctx.Context.boundFuel_eq_bound _ (hfB _ _),
        Ctx.Context.boundFuel_eq_bound _ (hfR _ _)]
      exact (hcuts block hb (d' + 1) (by omega) hdk).2

end ErdosSzekeres
