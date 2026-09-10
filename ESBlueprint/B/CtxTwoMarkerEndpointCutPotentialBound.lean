import ESBlueprint.B.CtxTwoMarkerSurroundingEndpointCutUnconditionalBound
import ESBlueprint.B.CtxBoundaryMarkerInwardEndpointCutTriangularBound
import ESBlueprint.B.CtxTwoMarkerYoungerExteriorEndpointCutPotentialBound
import ESBlueprint.B.CtxTwoMarkerOlderExteriorEndpointCutPotentialBound
import ESBlueprint.B.CtxTwoMarkerBetweenEndpointCutDoubledRankBound
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Classify every opposite-kept endpoint against both actual chosen markers and apply the unconditional surrounding, inward, outward or between cut bounds. No recursive premise or opposite-history restriction remains.
Positive labels, chosen global at most five, opposite width at least two, and two actual indexed chosen positions containing all chosen positions. A nonempty opposite-kept endpoint with a complementary child witness; arbitrary opposite history, maxima and inactive children. No recursive potential premise.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_endpoint_cut_potential_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y)
  (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
  (keep : List ℕ) (q₀ l m n : ℕ)
  (hq₀ : q₀ ∈ keep)
  (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
  (hl : l ∈ σ.childPositions) (hlnot : l ∉ keep)
  (endpoint : Bool)
  (hendpoint : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep →
    if endpoint then q < p else p < q) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) +
    Ctx.Context.boundFuel g (σ.part keep t n) ≤ (w + 1).choose 2 + w - 1) ∧
    (σ.part rest s m).bound + (σ.part keep t n).bound ≤ (w + 1).choose 2 + w - 1 := by
  classical
  let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let P := (w + 1).choose 2 + w - 1
  let Result (T : ℕ) : Prop :=
    (∀ f g, boundFuel f (σ.part rest s m) + boundFuel g (σ.part keep t n) ≤ T) ∧
      (σ.part rest s m).bound + (σ.part keep t n).bound ≤ T
  change Result P
  have hw : 2 ≤ w := hwidth
  have hWidthOne : 1 ≤ w := by omega
  have hLift {T : ℕ} (h : Result T) (hT : T ≤ P) : Result P :=
    ⟨fun f g ↦ (h.1 f g).trans hT, h.2.trans hT⟩
  have hTriangle : (w + 1).choose 2 ≤ P := by dsimp only [P]; omega
  have hDoubled : 2 * w - 1 ≤ P := by
    have hc : (w + 1).choose 2 = w.choose 2 + w := by
      simpa only [Nat.choose_one_right, Nat.succ_eq_add_one, Nat.add_comm] using Nat.choose_succ_succ w 1
    dsimp only [P]
    omega
  by_cases hYoung : ∃ a ∈ keep, ∃ b ∈ keep, a < x ∧ x < b
  · obtain ⟨a, ha, b, hb, hab⟩ := hYoung
    exact ctx_two_marker_surrounding_endpoint_cut_unconditional_bound σ hpositive s t hne
      N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
      keep a b l m n ha hb (Or.inl hab) hkeep hl hlnot endpoint hendpoint
  by_cases hOld : ∃ a ∈ keep, ∃ b ∈ keep, a < y ∧ y < b
  · obtain ⟨a, ha, b, hb, hab⟩ := hOld
    exact ctx_two_marker_surrounding_endpoint_cut_unconditional_bound σ hpositive s t hne
      N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
      keep a b l m n ha hb (Or.inr hab) hkeep hl hlnot endpoint hendpoint
  have hChildNe (p j z : ℕ) (hp : p ∈ σ.childPositions)
      (hz : z ∈ σ.extPositions j) : p ≠ z := by
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hz).2
    intro h
    subst z
    simp [hc] at he
  have hAvoid (z : ℕ) (hNe : ∀ p ∈ keep, p ≠ z)
      (hNoCut : ¬∃ a ∈ keep, ∃ b ∈ keep, a < z ∧ z < b) :
      (∀ p ∈ keep, p < z) ∨ (∀ p ∈ keep, z < p) := by
    by_cases hq : q₀ < z
    · left
      intro p hp
      have hn := hNe p hp
      by_contra hh
      exact hNoCut ⟨q₀, hq₀, p, hp, hq, by omega⟩
    · right
      have hnq := hNe q₀ hq₀
      have hzq : z < q₀ := by omega
      intro p hp
      have hn := hNe p hp
      by_contra hh
      exact hNoCut ⟨p, hp, q₀, hq₀, by omega, hzq⟩
  have hAvoidX := hAvoid x (fun p hp ↦ hChildNe p N x (hkeep p hp) hx) hYoung
  have hAvoidY := hAvoid y (fun p hp ↦ hChildNe p M y (hkeep p hp) hy) hOld
  have hXY : x ≠ y := by
    intro he
    have hxn := (List.mem_filter.mp hx).2
    have hym := (List.mem_filter.mp hy).2
    rw [← he] at hym
    cases hletter : σ.letterAt x <;> simp [hletter] at hxn hym
    omega
  have hYoungEmpty (j : ℕ) (hj : j ∈ σ.levelsOn s N) (p : ℕ)
      (hp : p ∈ σ.extPositions j) : False := by
    have hf := of_decide_eq_true (List.mem_filter.mp hj).2
    have hNpos := one_le_of_mem_levels hN
    have hjlt : j < N := by rcases hf.2 with h | h <;> omega
    have hOn : j ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨(List.mem_filter.mp hj).1, by simp [hf.1]⟩
    have hAtLevel (i z : ℕ) (hz : z ∈ σ.extPositions i) (hpz : p = z) : j = i := by
      have hJ := (List.mem_filter.mp hp).2
      have hI := (List.mem_filter.mp hz).2
      rw [hpz] at hJ
      cases he : σ.letterAt z <;> simp [he] at hJ hI
      omega
    rcases hchosen j hOn p hp with hpx | hpy
    · have he := hAtLevel N x hx hpx
      omega
    · have he := hAtLevel M y hy hpy
      omega
  have hInwardL (hL : ∀ p ∈ keep, p < x)
      (hEnd : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → q < p) : Result P := by
    apply hLift (ctx_boundary_marker_inward_endpoint_cut_triangular_bound σ hpositive s t hne
      N x hN hNs hx hglobal hWidthOne keep q₀ l m n hq₀ hkeep hl hlnot false hL
      (fun j hj p hp ↦ False.elim (hYoungEmpty j hj p hp)) hEnd) hTriangle
  have hInwardR (hR : ∀ p ∈ keep, x < p)
      (hEnd : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → p < q) : Result P := by
    apply hLift (ctx_boundary_marker_inward_endpoint_cut_triangular_bound σ hpositive s t hne
      N x hN hNs hx hglobal hWidthOne keep q₀ l m n hq₀ hkeep hl hlnot true hR
      (fun j hj p hp ↦ False.elim (hYoungEmpty j hj p hp)) hEnd) hTriangle
  have hEnds :
      (∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → q < p) ∨
      (∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → p < q) := by
    cases endpoint
    · exact Or.inr hendpoint
    · exact Or.inl hendpoint
  rcases hAvoidX with hLX | hRX <;> rcases hAvoidY with hLY | hRY
  · cases he : endpoint
    · have hEnd : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → p < q := by
        simpa [he] using hendpoint
      by_cases hxy : x < y
      · exact ctx_two_marker_younger_exterior_endpoint_cut_potential_bound σ hpositive s t hne
          N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hWidthOne keep q₀ l m n
          hq₀ hkeep hl hlnot (Or.inl ⟨hLX, hxy, hEnd⟩)
      · exact ctx_two_marker_older_exterior_endpoint_cut_potential_bound σ hpositive s t hne
          N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hWidthOne keep q₀ l m n
          hq₀ hkeep hl hlnot (Or.inr ⟨hLY, by omega, hEnd⟩)
    · apply hInwardL hLX
      simpa [he] using hendpoint
  · apply hLift (ctx_two_marker_between_endpoint_cut_doubled_rank_bound σ hpositive s t hne
      N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hWidthOne keep q₀ l m n
      hq₀ hkeep hl hlnot (Or.inr (fun p hp ↦ ⟨hRY p hp, hLX p hp⟩)) hEnds) hDoubled
  · apply hLift (ctx_two_marker_between_endpoint_cut_doubled_rank_bound σ hpositive s t hne
      N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hWidthOne keep q₀ l m n
      hq₀ hkeep hl hlnot (Or.inl (fun p hp ↦ ⟨hRX p hp, hLY p hp⟩)) hEnds) hDoubled
  · cases he : endpoint
    · apply hInwardR hRX
      simpa [he] using hendpoint
    · have hEnd : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → q < p := by
        simpa [he] using hendpoint
      by_cases hxy : x < y
      · exact ctx_two_marker_older_exterior_endpoint_cut_potential_bound σ hpositive s t hne
          N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hWidthOne keep q₀ l m n
          hq₀ hkeep hl hlnot (Or.inl ⟨hRY, hxy, hEnd⟩)
      · exact ctx_two_marker_younger_exterior_endpoint_cut_potential_bound σ hpositive s t hne
          N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hWidthOne keep q₀ l m n
          hq₀ hkeep hl hlnot (Or.inr ⟨hRX, by omega, hEnd⟩)

end ErdosSzekeres
