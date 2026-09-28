import ESBlueprint.B.CtxPartOppositeLimitsEq
import ESBlueprint.B.CtxBaseCrossAxisTransfer
import ESBlueprint.B.CtxBoundOppositeRemovalsCommute

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A computable ordered criterion for exchanging two mixed-side singleton cuts. Four scalar inequalities bound the lost cap capacity at q and gained cup capacity at p, while the original cup at q is at most the original cap at p. The unchanged coordinates follow from opposite-capacity invariance, compensation from cross-axis transfer, and the final residuals commute exactly. Valid for arbitrary distinct children with a nonempty final residual; specializing p to an end gives a strip exchange. No recursive-bound inequality is assumed.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_attained_by_end_cut -/
theorem ctx_mixed_exchange_of_ordered_limits (σ : Ctx.Context) (hwf : σ.WellFormed) (p q : ℕ)
  (hp : p ∈ σ.childPositions) (hq : q ∈ σ.childPositions) (hpq : p ≠ q)
  (hthird : ∃ r ∈ σ.childPositions, r ≠ p ∧ r ≠ q)
  (d e : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) (he : 1 ≤ e) (hek : e ≤ σ.k - 2)
  (c t : ℕ) (hct : c + t ≤ σ.k - 1) (horder : σ.cupLimit q q ≤ σ.capLimit p p) :
  let Rq := σ.part (σ.childPositions.filter (· ∉ [q])) Ctx.Side.lower d
  let Rp := σ.part (σ.childPositions.filter (· ∉ [p])) Ctx.Side.upper (σ.k - 1 - e)
  let A := σ.part [q] Ctx.Side.upper (σ.k - 1 - d)
  let B := Rq.part [p] Ctx.Side.lower e
  let A' := Rp.part [q] Ctx.Side.upper (σ.k - 1 - d)
  let B' := σ.part [p] Ctx.Side.lower e
  let rest := σ.childPositions.filter (fun x => x ∉ [q] ∧ x ∉ [p])
  A.capLimit q q ≤ c + t → c ≤ A'.capLimit q q →
  B.cupLimit p p ≤ c → c + t ≤ B'.cupLimit p p →
  A.bound + B.bound + (Rq.part rest Ctx.Side.upper (σ.k - 1 - e)).bound ≤
    B'.bound + A'.bound + (Rp.part rest Ctx.Side.lower d).bound := by
  dsimp only
  intro hAcap hA'cap hBcup hB'cup
  let Rq := σ.part (σ.childPositions.filter (· ∉ [q])) Side.lower d
  let Rp := σ.part (σ.childPositions.filter (· ∉ [p])) Side.upper (σ.k - 1 - e)
  let A := σ.part [q] Side.upper (σ.k - 1 - d)
  let B := Rq.part [p] Side.lower e
  let A' := Rp.part [q] Side.upper (σ.k - 1 - d)
  let B' := σ.part [p] Side.lower e
  let rest := σ.childPositions.filter (fun x => x ∉ [q] ∧ x ∉ [p])
  have hqp : q ≠ p := Ne.symm hpq
  obtain ⟨r, hr, hrp, hrq⟩ := hthird
  have hRqw : Rq.WellFormed := hwf.part _ Side.lower hd hdk
  have hRpw : Rp.WellFormed := hwf.part _ Side.upper (by omega) (by omega)
  have hpRq : p ∈ Rq.childPositions := by
    change p ∈ (σ.part _ Side.lower d).childPositions
    rw [part_childPositions]
    simp [hp, hpq]
  have hqRp : q ∈ Rp.childPositions := by
    change q ∈ (σ.part _ Side.upper (σ.k - 1 - e)).childPositions
    rw [part_childPositions]
    simp [hq, hqp]
  have hrRq : r ∈ Rq.childPositions := by
    change r ∈ (σ.part _ Side.lower d).childPositions
    rw [part_childPositions]
    simp [hr, hrq]
  have hrRp : r ∈ Rp.childPositions := by
    change r ∈ (σ.part _ Side.upper (σ.k - 1 - e)).childPositions
    rw [part_childPositions]
    simp [hr, hrp]
  have hsingleton (τ : Context) (x : ℕ) (hx : x ∈ τ.childPositions) (s : Side) (m : ℕ) :
      (τ.part [x] s m).bound =
        baseOf ((τ.part [x] s m).cupLimit x x) ((τ.part [x] s m).capLimit x x) τ.k := by
    have hf (ps : List ℕ) (hn : ps.Nodup) (hx : x ∈ ps) : ps.filter (· ∈ [x]) = [x] := by
      induction ps with
      | nil => simp at hx
      | cons a ps ih =>
        have hn' := List.nodup_cons.mp hn
        by_cases ha : a = x
        · subst a
          have hnil : ps.filter (· ∈ [x]) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro y hy
            simp only [List.mem_singleton, decide_eq_false_iff_not]
            intro hyx
            have hyx' : y = x := of_decide_eq_true hyx
            exact hn'.1 (hyx' ▸ hy)
          rw [List.filter_cons, show decide (x ∈ [x]) = true by simp, hnil]
          rfl
        · have hxs : x ∈ ps := by simpa [Ne.symm ha] using hx
          rw [List.filter_cons, show decide (a ∈ [x]) = false by simp [ha]]
          exact ih hn'.2 hxs
    have hps : (τ.part [x] s m).childPositions = [x] := by
      rw [part_childPositions]
      exact hf τ.childPositions (List.nodup_range.filter _) hx
    have hruns : (τ.part [x] s m).numRuns ≤ 1 := by
      have h := numRuns_le_length (τ.part [x] s m)
      simpa only [hps, List.length_singleton] using h
    simp [bound, boundFuel, hruns, base_eq_baseOf, hps]
    rfl
  have hAcup : A.cupLimit q q = σ.cupLimit q q :=
    (ctx_part_opposite_limits_eq σ hwf [q] ⟨p, hp, by simp [hpq]⟩ (σ.k - 1 - d) q q).1
  have hRpcup : Rp.cupLimit q q = σ.cupLimit q q :=
    (ctx_part_opposite_limits_eq σ hwf _ ⟨p, hp, by simp⟩ (σ.k - 1 - e) q q).1
  have hA'cup : A'.cupLimit q q = σ.cupLimit q q :=
    (ctx_part_opposite_limits_eq Rp hRpw [q] ⟨r, hrRp, by simp [hrq]⟩ (σ.k - 1 - d) q q).1.trans hRpcup
  have hRqcap : Rq.capLimit p p = σ.capLimit p p :=
    (ctx_part_opposite_limits_eq σ hwf _ ⟨q, hq, by simp⟩ d p p).2
  have hBcap : B.capLimit p p = σ.capLimit p p :=
    (ctx_part_opposite_limits_eq Rq hRqw [p] ⟨r, hrRq, by simp [hrp]⟩ e p p).2.trans hRqcap
  have hB'cap : B'.capLimit p p = σ.capLimit p p :=
    (ctx_part_opposite_limits_eq σ hwf [p] ⟨q, hq, by simp [hqp]⟩ e p p).2
  have hAb : A.bound ≤ baseOf (σ.cupLimit q q) (c + t) σ.k := by
    rw [hsingleton σ q hq, hAcup]
    exact baseOf_mono le_rfl hAcap
  have hBb : B.bound ≤ baseOf c (σ.capLimit p p) σ.k := by
    rw [hsingleton Rq p hpRq, hBcap]
    exact baseOf_mono hBcup le_rfl
  have hA'b : baseOf (σ.cupLimit q q) c σ.k ≤ A'.bound := by
    rw [hsingleton Rp q hqRp, hA'cup]
    exact baseOf_mono le_rfl hA'cap
  have hB'b : baseOf (c + t) (σ.capLimit p p) σ.k ≤ B'.bound := by
    rw [hsingleton σ p hp, hB'cap]
    exact baseOf_mono hB'cup le_rfl
  have hcomp := ctx_base_cross_axis_transfer c t (σ.cupLimit q q) (σ.capLimit p p) σ.k
    horder (by unfold capLimit; omega) hct
  have hleaves : A.bound + B.bound ≤ B'.bound + A'.bound := by omega
  have hres := ctx_bound_opposite_removals_commute σ hwf [q] [p]
    (by simpa using hq) (by simpa using hp) (by simp) (by simp) (by simp [hqp])
    Side.lower Side.upper (by decide) d (σ.k - 1 - e) hd hdk (by omega) (by omega)
  change A.bound + B.bound + (Rq.part rest Side.upper (σ.k - 1 - e)).bound ≤
    B'.bound + A'.bound + (Rp.part rest Side.lower d).bound
  change (Rq.part rest Side.upper (σ.k - 1 - e)).bound = (Rp.part rest Side.lower d).bound at hres
  rw [hres]
  exact Nat.add_le_add_right hleaves _

end ErdosSzekeres
