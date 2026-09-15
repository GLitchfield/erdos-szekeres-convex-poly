import ESBlueprint.B.CtxTwoMarkerEndpointCutSixObstructionClassification
import ESBlueprint.B.CtxTwoMarkerOlderSurroundingEndpointCutSixBound
import ESBlueprint.B.CtxTwoMarkerYoungerOnlySurroundingEndpointCutTenBound

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At k=6 every legal endpoint cut for a context with exactly two actual chosen-axis markers has independent-fuel and full-bound sum at most twelve. The obstruction classifier handles all non-surrounding configurations; surrounding the older marker uses the exact coupled theorem, while surrounding only the younger marker uses the stronger uniform bound ten. Positive labels, clear opposite history, both endpoint orientations, maxima, inactive children, and the legal maxima coupling remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_endpoint_cut_six_obstruction_classification, ErdosSzekeres.ctx_two_marker_older_surrounding_endpoint_cut_six_bound, ErdosSzekeres.ctx_two_marker_younger_only_surrounding_endpoint_cut_ten_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_endpoint_cut_six_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hclear : σ.levelsOn t 0 = []) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (q₀ l m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hlnot : l ∉ keep) (endpoint : Bool) (hendpoint : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → if endpoint then q < p else p < q) (hk : σ.k = 6) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12 := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let Result (T : ℕ) : Prop :=
    (∀ f g, boundFuel f (σ.part rest s m) + boundFuel g (σ.part keep t n) ≤ T) ∧
      (σ.part rest s m).bound + (σ.part keep t n).bound ≤ T
  change Result 12
  have hClass := ctx_two_marker_endpoint_cut_six_obstruction_classification σ hpositive
    s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite hclear hchosen hwidth
    keep q₀ l m n hq₀ hkeep hl hlnot endpoint hendpoint hk hm hn hcoupling
  change Result 12 ∨
    ((∃ a ∈ keep, ∃ b ∈ keep, a < x ∧ x < b) ∨
      (∃ a ∈ keep, ∃ b ∈ keep, a < y ∧ y < b)) at hClass
  rcases hClass with hDone | hSurround
  · exact hDone
  · rcases hSurround with hYoung | hOld
    · by_cases hOld' : ∃ a ∈ keep, ∃ b ∈ keep, a < y ∧ y < b
      · obtain ⟨a, ha, b, hb, hay, hyb⟩ := hOld'
        have hh := ctx_two_marker_older_surrounding_endpoint_cut_six_bound σ hpositive
          s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite hchosen hwidth
          keep a b l m n ha hb ⟨hay, hyb⟩ hkeep hl hlnot endpoint hendpoint hk hm hn hcoupling
        simpa only [Result, rest] using hh
      · obtain ⟨a, ha, b, hb, hax, hxb⟩ := hYoung
        have hh := ctx_two_marker_younger_only_surrounding_endpoint_cut_ten_bound σ hpositive
          s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite hchosen hwidth
          keep a b l m n ha hb ⟨hax, hxb⟩ hOld' hkeep hl hlnot endpoint hendpoint
        change Result 10 at hh
        exact ⟨fun f g => (hh.1 f g).trans (by omega), hh.2.trans (by omega)⟩
    · obtain ⟨a, ha, b, hb, hay, hyb⟩ := hOld
      have hh := ctx_two_marker_older_surrounding_endpoint_cut_six_bound σ hpositive
        s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite hchosen hwidth
        keep a b l m n ha hb ⟨hay, hyb⟩ hkeep hl hlnot endpoint hendpoint hk hm hn hcoupling
      simpa only [Result, rest] using hh

end ErdosSzekeres
