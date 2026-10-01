import ESBlueprint.B.CtxPartBoundZeroOfNearSaturatedSiblingAndYoungerBoundaryMarker
import ESBlueprint.B.CtxBoundLeIffAllIntervalCutsLe

namespace ErdosSzekeres

/-- A raw positive-label context with at least two child runs has full bound zero if each axis has a younger indexed actual marker outside the whole source-child span and an older same-axis indexed sibling maximum at least k-3. Boundary direction, levels and marker may differ by axis. Proper parts vanish by the accepted two-trace near-boundary zero theorem; all interval cuts vanish, and the exact all-cut upper characterization gives full zero. Arbitrary globals, indexed unused levels and history length; no WellFormed hypothesis. Supplies an unbounded zero criterion and blocks all-positive-point lower shortcuts in the segment-exchange proof.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_bound_zero_of_near_saturated_sibling_and_younger_boundary_marker, ErdosSzekeres.ctx_bound_le_iff_all_interval_cuts_le
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_bound_zero_of_both_sides_near_saturated_boundary_histories (σ : Ctx.Context)
(hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
(hruns : 2 ≤ σ.numRuns)
(hhistories : ∀ s : Ctx.Side, ∃ J M x : ℕ,
  J ∈ σ.levelsOn s 0 ∧ M ∈ σ.levelsOn s 0 ∧ J < M ∧
  x ∈ σ.extPositions J ∧
  ((∀ q ∈ σ.childPositions, x < q) ∨ (∀ q ∈ σ.childPositions, q < x)) ∧
  σ.k - 3 ≤ σ.maximumAt M) :
σ.bound = 0 := by
  classical
  have hPart (s : Ctx.Side) (keep : List ℕ) (m r : ℕ)
      (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep) :
      (σ.part keep s m).bound = 0 := by
    obtain ⟨J, M, x, hJ, hM, hJM, hx, hboundary, hmaximum⟩ := hhistories s
    exact (ctx_part_bound_zero_of_near_saturated_sibling_and_younger_boundary_marker
      σ hpositive s J M x hJ hM hJM hx hboundary hmaximum keep m r hr hremoved).2
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
    hPart .lower block d r hr hrnot
  have hrestUpper : (σ.part rest Ctx.Side.upper (σ.k - 1 - d)).bound = 0 :=
    hPart .upper rest (σ.k - 1 - d) b hbσ hbnot
  have hblockUpper : (σ.part block Ctx.Side.upper (σ.k - 1 - d)).bound = 0 :=
    hPart .upper block (σ.k - 1 - d) r hr hrnot
  have hrestLower : (σ.part rest Ctx.Side.lower d).bound = 0 :=
    hPart .lower rest d b hbσ hbnot
  constructor
  · rw [hblockLower, hrestUpper]
  · rw [hblockUpper, hrestLower]

end ErdosSzekeres
