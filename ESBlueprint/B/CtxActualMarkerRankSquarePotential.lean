import ESBlueprint.B.CtxYoungestMarkerRankSquareBoundOfBareTwoMarkerPotential
import ESBlueprint.B.CtxBareTwoMarkerSharpPotential
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Establish the exact opposite rank-union square bound for any context with an actual indexed chosen marker and chosen global at most five, with no bare-potential premise. Select the least actual chosen level and discharge the checked youngest-marker reduction using the sharp bare two-marker potential. Positive physical labels, distinct axes, chosen global at most five, and at least one actual indexed chosen marker. Other chosen and opposite history, maxima, inactive children and unindexed physical barriers may be arbitrary. No youngest-level, recursive-potential, or width assumption remains.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_actual_marker_rank_square_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) :
  let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks := active.biUnion (fun p =>
    Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p))
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ ranks.card ^ 2) ∧ σ.bound ≤ ranks.card ^ 2 := by
  classical
  let actual := σ.levels.toFinset.filter (fun j => σ.sideAt j = s ∧ σ.extPositions j ≠ [])
  have hNactual : N ∈ actual := by
    simp only [actual, Finset.mem_filter, List.mem_toFinset]
    exact ⟨hN, hNs, List.ne_nil_of_mem hx⟩
  have hNonempty : actual.Nonempty := ⟨N, hNactual⟩
  let J := actual.min' hNonempty
  have hJactual : J ∈ actual := Finset.min'_mem actual hNonempty
  have hJData : J ∈ σ.levels ∧ σ.sideAt J = s ∧ σ.extPositions J ≠ [] := by
    simpa only [actual, Finset.mem_filter, List.mem_toFinset] using hJactual
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hJData.2.2
  have hYoung : ∀ j ∈ σ.levelsOn s J, σ.extPositions j = [] := by
    intro j hj
    have hh := List.mem_filter.mp hj
    have hPred := of_decide_eq_true hh.2
    have hJpos := one_le_of_mem_levels hJData.1
    by_contra hActual
    have hjActual : j ∈ actual := by
      simp only [actual, Finset.mem_filter, List.mem_toFinset]
      exact ⟨hh.1, hPred.1, hActual⟩
    have hMin : J ≤ j := Finset.min'_le actual j hjActual
    omega
  apply ctx_youngest_marker_rank_square_bound_of_bare_two_marker_potential σ hpositive s t hne
    J y hJData.1 hJData.2.1 hy hglobal hYoung
  intro ρ K H a b hPos _ hSides hK hH hKH ha hb hActual hGlobal _
  dsimp only
  intro hWidth
  have hClear : ρ.levelsOn t 0 = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro j hj
    have hh := List.mem_filter.mp hj
    have hs : ρ.sideAt j = t := (of_decide_eq_true hh.2).1
    exact hne ((hSides j hh.1).symm.trans hs)
  exact (ctx_bare_two_marker_sharp_potential ρ hPos s t hne K H a b hK hH hKH
    (hSides K hK) (hSides H hH) ha hb hGlobal hClear
    (fun j hj p hp => hActual j (List.mem_filter.mp hj).1 p hp)
    (by cases t <;> dsimp only at hWidth ⊢ <;> omega)).2

end ErdosSzekeres
