import ESBlueprint.B.CtxTwoMarkerPotentialOfOlderExteriorCutBound
import ESBlueprint.B.CtxOlderExteriorInternalComplementCutPotentialBound
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Establish the sharp bare two-marker potential choose(w+1,2)+w-1 with no recursive or cut-bound premise. The checked same-source cut classification is completed by the direct older-exterior opposite-kept cut, whose chosen complement already contains the nonmonotone triple. Positive physical labels, distinct axes, chosen global at most five and opposite width at least two. Exactly two actual indexed chosen positions at N<M; no indexed opposite history. Arbitrary maxima, inactive children and unindexed physical barriers remain allowed. The absence of indexed opposite history is still an explicit hypothesis.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bare_two_marker_sharp_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hclear : σ.levelsOn t 0 = [])
  (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y)
  (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (w + 1).choose 2 + w - 1) ∧
    σ.bound ≤ (w + 1).choose 2 + w - 1 := by
  classical
  have hAtLevel (j i p : ℕ) (hp : p ∈ σ.extPositions j) (hp' : p ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hp).2
    have hi := (List.mem_filter.mp hp').2
    cases hletter : σ.letterAt p <;> simp [hletter] at hj hi
    omega
  have hNpos := one_le_of_mem_levels hN
  have hYoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [] := by
    intro j hj
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    have hh := List.mem_filter.mp hj
    have hPred := of_decide_eq_true hh.2
    have hOn : j ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hh.1, by simp [hPred.1]⟩
    rcases hchosen j hOn p hp with hpx | hpy
    · have he := hAtLevel j N x (by simpa only [hpx] using hp) hx
      omega
    · have he := hAtLevel j M y (by simpa only [hpy] using hp) hy
      omega
  apply ctx_two_marker_potential_of_older_exterior_cut_bound σ hpositive s t hne
    N M x y hN hM hNM hNs hMs hx hy hglobal hclear hchosen hwidth
  intro keep hk q₀ l r m n hq₀ hl hr hlnot hrnot hinside hexterior _ _ _
  exact (ctx_older_exterior_internal_complement_cut_potential_bound σ hpositive s t hne
    N M x y hN hM hNM hNs hMs hx hy hYoung hglobal hwidth
    keep q₀ l r m n hq₀ (mem_blocks hk).2.2 hl hr hlnot hrnot hinside hexterior).2

end ErdosSzekeres
