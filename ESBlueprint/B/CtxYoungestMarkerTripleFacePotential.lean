import ESBlueprint.B.CtxYoungestMarkerTripleFaceBoundOfAnchoredSquare
import ESBlueprint.B.CtxActualMarkerRankSquarePotential
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Remove the anchored-square premise from the youngest-marker ordered-triple face bound. The unconditional actual-marker rank-square potential now pays the merged endpoint group in the checked triple-face reduction; the original-history row and column rank faces bound every fuel approximation and the full context. Positive physical labels, distinct axes, chosen global at most five, and an actual chosen marker at level N. Every younger indexed chosen level has no actual positions. Other history, maxima, inactive children and physical barriers may be arbitrary. No anchored-square or recursive-bound premise remains.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_youngest_marker_triple_face_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = []) :
  let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let interval := fun p => Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p)
  let pairs := fun S : Finset ℕ => (S.product S).filter (fun z => z.1 ≤ z.2)
  let rows := (active.filter (fun p => p < x)).biUnion
    (fun p => ({σ.leftExt t 0 p + 1} : Finset ℕ).product (pairs (interval p)))
  let columns := (active.filter (fun p => x < p)).biUnion
    (fun p => (pairs (interval p)).image (fun z => (z.1, z.2, global - 1 - σ.rightExt t 0 p)))
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (rows ∪ columns).card) ∧
    σ.bound ≤ (rows ∪ columns).card := by
  classical
  apply ctx_youngest_marker_triple_face_bound_of_anchored_square σ hpositive s t hne
    N x hN hNs hx hglobal hyoung
  intro ρ J y hPos hJ hJs hy hGlobal _ _
  exact (ctx_actual_marker_rank_square_potential ρ hPos s t hne J y hJ hJs hy hGlobal).2

end ErdosSzekeres
