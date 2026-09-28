import ESBlueprint.B.CtxNonmonotoneTripleSaturatedPotential
import ESBlueprint.B.CtxPartPositiveLetters

namespace ErdosSzekeres

/-- Turn the marker newly created by a context part and two transported old chosen markers in nonmonotone spatial order into the checked four-rank saturated potential. A removed source child becomes an actual chosen marker at level one, while source levels N<M become N+1<M+1. If either the new maximum or a source chosen maximum is at least k-4, then the part has the top-band bound 3k-8 and, when the opposite global is at most k-1, the next-band bound 3k-9. Positive source labels, distinct axes, clear source opposite indexed history, chosen global at most five, opposite global at most k, and k at least five are explicit. The kept set and new maximum are otherwise arbitrary. This is a direct consumer of the checked nonmonotone-triple potential for singleton-end sandwich cuts; it does not assert that every sandwich history contains such a triple. Search evidence and remaining obstruction: runs/sol-trial-20260913/obstruction-review.md.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_part_new_marker_nonmonotone_saturated_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (keep : List ℕ) (s t : Ctx.Side) (hne : s ≠ t) (m q N M x y : ℕ)
  (hq : q ∈ σ.childPositions) (hqnot : q ∉ keep)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hgeometry : (q < x ∧ y < x) ∨ (x < q ∧ x < y))
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hclear : σ.levelsOn t 0 = [])
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hk : 5 ≤ σ.k)
  (hlarge : σ.k - 4 ≤ m ∨
    ∃ R ∈ σ.levels, σ.sideAt R = s ∧ σ.k - 4 ≤ σ.maximumAt R) :
  let A := σ.part keep s m
  (∀ fuel, Ctx.Context.boundFuel fuel A ≤ 3 * A.k - 8) ∧ A.bound ≤ 3 * A.k - 8 ∧
    ((match t with | Ctx.Side.lower => A.u | Ctx.Side.upper => A.a) ≤ A.k - 1 →
      (∀ fuel, Ctx.Context.boundFuel fuel A ≤ 3 * A.k - 9) ∧
        A.bound ≤ 3 * A.k - 9) := by
  let A := σ.part keep s m
  have hPosA : ∀ p j v, A.letterAt p = Ctx.Letter.ext j v → 1 ≤ j :=
    ctx_part_positive_letters σ keep s m
  have hNpos : 1 ≤ N := Ctx.Context.one_le_of_mem_levels hN
  have hMpos : 1 ≤ M := Ctx.Context.one_le_of_mem_levels hM
  have hOne : 1 ∈ A.levels := by
    change 1 ∈ (σ.part keep s m).levels
    rw [Ctx.Context.part_levels]
    simp
  have hNA : N + 1 ∈ A.levels := by
    change N + 1 ∈ (σ.part keep s m).levels
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hMA : M + 1 ∈ A.levels := by
    change M + 1 ∈ (σ.part keep s m).levels
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hqA : q ∈ A.extPositions 1 := by
    change q ∈ (σ.part keep s m).extPositions 1
    rw [Ctx.Context.part_extPositions_one hpositive]
    exact List.mem_filter.mpr ⟨hq, by simp [hqnot]⟩
  have hxA : x ∈ A.extPositions (N + 1) := by
    change x ∈ (σ.part keep s m).extPositions (N + 1)
    rw [Ctx.Context.part_extPositions_succ σ keep s m hNpos]
    exact hx
  have hyA : y ∈ A.extPositions (M + 1) := by
    change y ∈ (σ.part keep s m).extPositions (M + 1)
    rw [Ctx.Context.part_extPositions_succ σ keep s m hMpos]
    exact hy
  have hSideOne : A.sideAt 1 = s := by
    exact Ctx.Context.part_sideAt_one_of_mem hpositive keep s m hqA
  have hNsA : A.sideAt (N + 1) = s := by
    exact (Ctx.Context.part_sideAt_succ σ keep s m hNpos).trans hNs
  have hMsA : A.sideAt (M + 1) = s := by
    exact (Ctx.Context.part_sideAt_succ σ keep s m hMpos).trans hMs
  have hSideNe : A.sideAt 1 ≠ t := by
    rw [hSideOne]
    exact hne
  have hClearA : A.levelsOn t 0 = [] := by
    rw [Ctx.Context.part_levelsOn_other_zero hSideNe, hclear]
    rfl
  have hGlobalA :
      (match s with | Ctx.Side.lower => A.u | Ctx.Side.upper => A.a) ≤ 5 := by
    cases s <;> exact hglobal
  have hOppositeA :
      (match t with | Ctx.Side.lower => A.u | Ctx.Side.upper => A.a) ≤ A.k := by
    cases t <;> exact hopposite
  have hKA : 5 ≤ A.k := hk
  rcases hlarge with hm | ⟨R, hR, hRs, hRmaximum⟩
  · have hMaximumOne : A.k - 4 ≤ A.maximumAt 1 := by
      rw [Ctx.Context.part_maximumAt_one]
      exact hm
    exact ctx_nonmonotone_triple_saturated_potential A hPosA s t hne
      1 (N + 1) (M + 1) q x y hOne hNA hMA (by omega) (by omega)
      hSideOne hNsA hMsA hqA hxA hyA hgeometry hGlobalA hClearA
      (by cases t <;> exact hOppositeA) hKA 1 hOne hSideOne hMaximumOne
  · have hRpos : 1 ≤ R := Ctx.Context.one_le_of_mem_levels hR
    have hRA : R + 1 ∈ A.levels := by
      change R + 1 ∈ (σ.part keep s m).levels
      rw [Ctx.Context.part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨R, hR, rfl⟩)
    have hRsA : A.sideAt (R + 1) = s := by
      exact (Ctx.Context.part_sideAt_succ σ keep s m hRpos).trans hRs
    have hRmaximumA : A.k - 4 ≤ A.maximumAt (R + 1) := by
      rw [Ctx.Context.part_maximumAt_succ σ keep s m hRpos]
      exact hRmaximum
    exact ctx_nonmonotone_triple_saturated_potential A hPosA s t hne
      1 (N + 1) (M + 1) q x y hOne hNA hMA (by omega) (by omega)
      hSideOne hNsA hMsA hqA hxA hyA hgeometry hGlobalA hClearA
      (by cases t <;> exact hOppositeA) hKA (R + 1) hRA hRsA hRmaximumA


end ErdosSzekeres
