import ESBlueprint.B.CtxTwoMarkerInternalComplementCutObstructionClassification
import ESBlueprint.B.CtxOlderExteriorInternalComplementCutSixBound

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At k=6 every legal internal opposite-kept interval cut with exactly two actual chosen-axis markers has independent-fuel and full-bound sum at most twelve whenever the opposite global is at most four. The obstruction classifier potential is then at most eight; its sole older-exterior alternative is discharged by the exact coupled older-exterior theorem. This isolates the remaining internal-complement obstruction to saturated opposite global five. Positive labels, clear opposite history, convexity, arbitrary maxima, inactive children, and the legal coupling remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_internal_complement_cut_obstruction_classification, ErdosSzekeres.ctx_older_exterior_internal_complement_cut_six_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_internal_complement_cut_six_bound_of_opposite_global_le_four (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) (hclear : σ.levelsOn t 0 = []) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (q₀ l r m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hlnot : l ∉ keep) (hrnot : r ∉ keep) (hinside : ∀ p ∈ keep, l < p ∧ p < r) (hconvex : ∀ p ∈ keep, ∀ q ∈ keep, ∀ z ∈ σ.childPositions, p ≤ z → z ≤ q → z ∈ keep) (hk : σ.k = 6) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12 := by
  classical
  let w := (match (generalizing := false) t with
    | Side.lower => σ.u
    | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let Result (T : ℕ) : Prop :=
    (∀ f g, boundFuel f (σ.part rest s m) + boundFuel g (σ.part keep t n) ≤ T) ∧
      (σ.part rest s m).bound + (σ.part keep t n).bound ≤ T
  change Result 12
  have hClass := ctx_two_marker_internal_complement_cut_obstruction_classification σ
    hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hclear hchosen hwidth
    keep q₀ l r m n hq₀ hkeep hl hr hlnot hrnot hinside hconvex
  change Result ((w + 1).choose 2 + w - 1) ∨
    ((x < y ∧ ∀ p ∈ keep, y < p) ∨ (y < x ∧ ∀ p ∈ keep, p < y)) at hClass
  rcases hClass with hPotential | hExterior
  · have hw : w ≤ 3 := by
      dsimp only [w]
      cases t <;> simp only at hopposite ⊢ <;> omega
    have hChoose : (w + 1).choose 2 ≤ 6 :=
      (Nat.choose_le_choose 2 (show w + 1 ≤ 4 by omega)).trans (by decide)
    have hBudget : (w + 1).choose 2 + w - 1 ≤ 12 := by omega
    exact ⟨fun f g => (hPotential.1 f g).trans hBudget,
      hPotential.2.trans hBudget⟩
  · have hAtLevel (j i p : ℕ) (hp : p ∈ σ.extPositions j)
        (hp' : p ∈ σ.extPositions i) : j = i := by
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
      have hOn : j ∈ σ.levelsOn s 0 :=
        List.mem_filter.mpr ⟨hh.1, by simp [hPred.1]⟩
      rcases hchosen j hOn p hp with hpx | hpy
      · have he := hAtLevel j N x (by simpa only [hpx] using hp) hx
        omega
      · have he := hAtLevel j M y (by simpa only [hpy] using hp) hy
        omega
    have hOppFive : (match (generalizing := false) t with
        | Side.lower => σ.u | Side.upper => σ.a) ≤ 5 := by
      cases t <;> simp only at hopposite ⊢ <;> omega
    have hh := ctx_older_exterior_internal_complement_cut_six_bound σ hpositive
      s t hne N M x y hN hM hNM hNs hMs hx hy hYoung hglobal hOppFive hwidth
      keep q₀ l r m n hq₀ hkeep hl hr hlnot hrnot hinside hExterior hk hm hn hcoupling
    simpa only [Result, rest] using hh

end ErdosSzekeres
