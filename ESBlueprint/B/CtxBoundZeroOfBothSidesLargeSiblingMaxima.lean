import ESBlueprint.B.CtxBoundLeIffAllIntervalCutsLe
import ESBlueprint.B.CtxPartBoundZeroOfSameSideLargeSiblingMaximum

namespace ErdosSzekeres

/-- A raw context with at least two child runs has zero recursive bound whenever both sides have an indexed sibling maximum at least k-2. Each proper interval block and its complement omit a source child, so same-side saturation annihilates both values in both orientations. The all-cut upper characterization then gives full zero. Positive actual external labels suffice, without well-formedness or further global-parameter restrictions. Supplies a reusable saturation boundary for the positive maximal-segment exchange proof.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_bound_zero_of_same_side_large_sibling_maximum, ErdosSzekeres.ctx_bound_le_iff_all_interval_cuts_le
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_bound_zero_of_both_sides_large_sibling_maxima (σ : Ctx.Context)
  (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
  (hruns : 2 ≤ σ.numRuns)
  (L U : ℕ) (hL : L ∈ σ.levelsOn Ctx.Side.lower 0)
  (hU : U ∈ σ.levelsOn Ctx.Side.upper 0)
  (hmaximumL : σ.k - 2 ≤ σ.maximumAt L)
  (hmaximumU : σ.k - 2 ≤ σ.maximumAt U) :
  σ.bound = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply (ctx_bound_le_iff_all_interval_cuts_le σ hruns 0).2
  intro block hb d _ _
  obtain ⟨hlen, hne, hsub⟩ := Ctx.Context.mem_blocks hb
  have hex : ∃ r, r ∈ σ.childPositions ∧ r ∉ block := by
    by_contra h
    have hsubset : ∀ r ∈ σ.childPositions, r ∈ block := by
      intro r hr
      by_contra hn
      exact h ⟨r, hr, hn⟩
    have hcount := ((Ctx.Context.childPositions_nodup σ).subperm hsubset).length_le
    omega
  obtain ⟨r, hr, hrnot⟩ := hex
  obtain ⟨b, hbb⟩ := List.exists_mem_of_ne_nil block hne
  have hbσ : b ∈ σ.childPositions := hsub b hbb
  let rest := σ.childPositions.filter (fun p => p ∉ block)
  have hbnot : b ∉ rest := by simp [rest, hbb]
  have hblockLower : (σ.part block Ctx.Side.lower d).bound = 0 :=
    ctx_part_bound_zero_of_same_side_large_sibling_maximum
      σ hpositive Ctx.Side.lower L hL hmaximumL block d r hr hrnot
  have hrestUpper : (σ.part rest Ctx.Side.upper (σ.k - 1 - d)).bound = 0 :=
    ctx_part_bound_zero_of_same_side_large_sibling_maximum
      σ hpositive Ctx.Side.upper U hU hmaximumU rest (σ.k - 1 - d) b hbσ hbnot
  have hblockUpper : (σ.part block Ctx.Side.upper (σ.k - 1 - d)).bound = 0 :=
    ctx_part_bound_zero_of_same_side_large_sibling_maximum
      σ hpositive Ctx.Side.upper U hU hmaximumU block (σ.k - 1 - d) r hr hrnot
  have hrestLower : (σ.part rest Ctx.Side.lower d).bound = 0 :=
    ctx_part_bound_zero_of_same_side_large_sibling_maximum
      σ hpositive Ctx.Side.lower L hL hmaximumL rest d b hbσ hbnot
  constructor
  · rw [hblockLower, hrestUpper]
  · rw [hblockUpper, hrestLower]

end ErdosSzekeres
