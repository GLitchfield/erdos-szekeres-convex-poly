import ESBlueprint.B.CtxTwoMarkerInternalComplementCutSixTopWidthYoungerExteriorMaximumTwoResidualClassification
import ESBlueprint.B.CtxTwoMarkerYoungerExteriorInternalComplementCutSixBoundOfMaximumTwo

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every legal two-marker internal-complement cut at k six, with each global at most five and opposite width at least two, has independently fueled and full sums at most twelve. The complete residual classifier is closed by the normalized younger-exterior maximum-two theorem.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_internal_complement_cut_six_top_width_younger_exterior_maximum_two_residual_classification, ErdosSzekeres.ctx_two_marker_younger_exterior_internal_complement_cut_six_bound_of_maximum_two
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_internal_complement_cut_six_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hclear : σ.levelsOn t 0 = []) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (q₀ l r m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hlnot : l ∉ keep) (hrnot : r ∉ keep) (hinside : ∀ p ∈ keep, l < p ∧ p < r) (hconvex : ∀ p ∈ keep, ∀ q ∈ keep, ∀ z ∈ σ.childPositions, p ≤ z → z ≤ q → z ∈ keep) (hk : σ.k = 6) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12 := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let Result : Prop :=
    (∀ f g, boundFuel f (σ.part rest s m) + boundFuel g (σ.part keep t n) ≤ 12) ∧
      (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12
  let Exterior : Prop :=
    (x < y ∧ ∀ p ∈ keep, p < x) ∨ (y < x ∧ ∀ p ∈ keep, x < p)
  change Result
  have hClass :=
    ctx_two_marker_internal_complement_cut_six_top_width_younger_exterior_maximum_two_residual_classification
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite
      hclear hchosen hwidth keep q₀ l r m n hq₀ hkeep hl hr hlnot hrnot hinside
      hconvex hk hm hn hcoupling
  change Result ∨
    ((match t with | Side.lower => σ.u | Side.upper => σ.a) = 5 ∧
      m = 2 ∧ Exterior) at hClass
  rcases hClass with hResult | ⟨_, hmTwo, hExterior⟩
  · exact hResult
  · have hh :=
      ctx_two_marker_younger_exterior_internal_complement_cut_six_bound_of_maximum_two
        σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite
        hclear hchosen hwidth keep q₀ l r m n hq₀ hkeep hl hr hlnot hrnot hinside
        (by simpa only [Exterior] using hExterior) hk hmTwo
    simpa only [Result, rest] using hh

end ErdosSzekeres
