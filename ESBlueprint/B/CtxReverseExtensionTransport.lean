import ErdosSzekeres.DecomposableContextLemmas
import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

/-- Reversing a well-formed context word preserves well-formedness, exchanges left and right extension counts, and transports cup and cap limits with the endpoints reversed. This supplies the capacity transport for reflecting the singleton-end sandwich argument; arbitrary external levels and unused maxima are retained.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_reverse_extension_transport (σ : Ctx.Context) (hwf : σ.WellFormed) :
  let ρ : Ctx.Context := { σ with word := σ.word.reverse }
  ρ.WellFormed ∧
    (∀ (s : Ctx.Side) (top p : ℕ), p < σ.word.length →
      ρ.leftExt s top (σ.word.length - 1 - p) = σ.rightExt s top p ∧
      ρ.rightExt s top (σ.word.length - 1 - p) = σ.leftExt s top p) ∧
    (∀ (p q : ℕ), p < σ.word.length → q < σ.word.length →
      ρ.cupLimit (σ.word.length - 1 - q) (σ.word.length - 1 - p) = σ.cupLimit p q ∧
      ρ.capLimit (σ.word.length - 1 - q) (σ.word.length - 1 - p) = σ.capLimit p q) := by
  classical
  dsimp only
  let ρ : Ctx.Context := { σ with word := σ.word.reverse }
  let flip (p : ℕ) := σ.word.length - 1 - p
  have hlt : ∀ p, p < σ.word.length → flip p < σ.word.length := by
    intro p hp
    dsimp [flip]
    omega
  have hinv : ∀ p, p < σ.word.length → flip (flip p) = p := by
    intro p hp
    dsimp [flip]
    omega
  have hletter : ∀ p, p < σ.word.length → ρ.letterAt p = σ.letterAt (flip p) := by
    intro p hp
    simp only [Ctx.Context.letterAt, ρ, List.getElem?_reverse hp]
    rfl
  have hletterFlip : ∀ p, p < σ.word.length → ρ.letterAt (flip p) = σ.letterAt p := by
    intro p hp
    rw [hletter _ (hlt p hp), hinv p hp]
  have hrange : (List.range σ.word.length).reverse.map flip = List.range σ.word.length := by
    have h : (List.range σ.word.length).map flip = (List.range σ.word.length).reverse := by
      simpa [flip, ← List.range_eq_range'] using
        (List.reverse_range' (s := 0) (n := σ.word.length)).symm
    rw [List.map_reverse, h, List.reverse_reverse]
  have hfilter (P Q : ℕ → Bool)
      (hPQ : ∀ p ∈ List.range σ.word.length, P (flip p) = Q p) :
      (List.range σ.word.length).filter P =
        ((List.range σ.word.length).filter Q).reverse.map flip := by
    calc
      _ = ((List.range σ.word.length).reverse.map flip).filter P := by rw [hrange]
      _ = ((List.range σ.word.length).filter (fun p ↦ P (flip p))).reverse.map flip := by
        rw [List.filter_map, List.filter_reverse]
        rfl
      _ = _ := by
        congr 2
        exact List.filter_congr hPQ
  have hext : ∀ N, ρ.extPositions N = (σ.extPositions N).reverse.map flip := by
    intro N
    unfold Ctx.Context.extPositions
    simp only [show ρ.word.length = σ.word.length from List.length_reverse]
    apply hfilter
    intro p hp
    rw [hletterFlip p (List.mem_range.mp hp)]
  have hside : ∀ N, ρ.sideAt N = σ.sideAt N := by
    intro N
    change (match (ρ.extPositions N).head? with
      | some p => match ρ.letterAt p with | Ctx.Letter.ext _ s => s | _ => Ctx.Side.lower
      | none => Ctx.Side.lower) = σ.sideAt N
    cases hh : (ρ.extPositions N).head? with
    | none =>
      have hnil : ρ.extPositions N = [] := List.head?_eq_none_iff.mp hh
      have hlen := congrArg List.length hnil
      rw [hext] at hlen
      simp only [List.length_map, List.length_reverse, List.length_nil] at hlen
      have hnil' : σ.extPositions N = [] := List.eq_nil_of_length_eq_zero hlen
      simp [Ctx.Context.sideAt, hnil']
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      have hplen : p < σ.word.length := by
        have := List.mem_range.mp (List.mem_filter.mp hp).1
        simpa [ρ] using this
      have hpred := (List.mem_filter.mp hp).2
      cases hl : ρ.letterAt p with
      | child => simp [hl] at hpred
      | ext M s =>
        have hMN : M = N := by simpa [hl] using hpred
        subst M
        have hold : σ.letterAt (flip p) = Ctx.Letter.ext N s :=
          (hletter p hplen).symm.trans hl
        simpa only [hl] using (hwf.2.2.2.2.2 _ _ _ hold).2.2
  have hwell : ρ.WellFormed := by
    obtain ⟨ha, hu, hak, huk, hm, hlet⟩ := hwf
    refine ⟨ha, hu, hak, huk, hm, ?_⟩
    intro p N s hp
    have hplen : p < σ.word.length := by
      by_contra h
      have ho : ρ.word.length ≤ p := by simpa [ρ] using Nat.le_of_not_gt h
      rw [Ctx.Context.letterAt_of_length_le ρ ho] at hp
      cases hp
    have hold : σ.letterAt (flip p) = Ctx.Letter.ext N s :=
      (hletter p hplen).symm.trans hp
    obtain ⟨hN, hNl, hs⟩ := hlet _ _ _ hold
    exact ⟨hN, hNl, hs.trans (hside N).symm⟩
  have hlevels : ∀ s top, ρ.levelsOn s top = σ.levelsOn s top := by
    intro s top
    simp only [Ctx.Context.levelsOn, Ctx.Context.levels, hside]
    rfl
  have hpos : ∀ N p, p ∈ σ.extPositions N → p < σ.word.length := by
    intro N p hp
    exact List.mem_range.mp (List.mem_filter.mp hp).1
  have hleftList : ∀ N p, p < σ.word.length →
      (ρ.extPositions N).filter (· < flip p) =
        ((σ.extPositions N).filter (p < ·)).reverse.map flip := by
    intro N p hp
    rw [hext, List.filter_map, List.filter_reverse]
    congr 2
    apply List.filter_congr
    intro x hx
    have hx' := hpos N x hx
    simp only [Function.comp_def, decide_eq_decide]
    dsimp [flip]
    omega
  have hrightList : ∀ N p, p < σ.word.length →
      (ρ.extPositions N).filter (flip p < ·) =
        ((σ.extPositions N).filter (· < p)).reverse.map flip := by
    intro N p hp
    rw [hext, List.filter_map, List.filter_reverse]
    congr 2
    apply List.filter_congr
    intro x hx
    have hx' := hpos N x hx
    simp only [Function.comp_def, decide_eq_decide]
    dsimp [flip]
    omega
  have hleftPick : ∀ N p, p < σ.word.length →
      ((ρ.extPositions N).filter (· < flip p)).getLast? =
        (((σ.extPositions N).filter (p < ·)).head?).map flip := by
    intro N p hp
    rw [hleftList N p hp, List.getLast?_map, List.getLast?_reverse]
  have hrightPick : ∀ N p, p < σ.word.length →
      ((ρ.extPositions N).filter (flip p < ·)).head? =
        (((σ.extPositions N).filter (· < p)).getLast?).map flip := by
    intro N p hp
    rw [hrightList N p hp, List.head?_map, List.head?_reverse]
  have hfoldLeft : ∀ (ls : List ℕ) p c, p < σ.word.length →
      (ls.foldl (Ctx.Context.leftStep ρ) (flip p, c)).2 =
        (ls.foldl (Ctx.Context.rightStep σ) (p, c)).2 := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons N ls ih =>
      intro p c hp
      simp only [List.foldl_cons, Ctx.Context.leftStep, Ctx.Context.rightStep]
      rw [hleftPick N p hp]
      cases hh : ((σ.extPositions N).filter (p < ·)).head? with
      | none => simpa using ih p c hp
      | some x =>
        have hx := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        have hx' := hpos N x (List.mem_filter.mp hx).1
        simpa using ih x (c + 1) hx'
  have hfoldRight : ∀ (ls : List ℕ) p c, p < σ.word.length →
      (ls.foldl (Ctx.Context.rightStep ρ) (flip p, c)).2 =
        (ls.foldl (Ctx.Context.leftStep σ) (p, c)).2 := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons N ls ih =>
      intro p c hp
      simp only [List.foldl_cons, Ctx.Context.leftStep, Ctx.Context.rightStep]
      rw [hrightPick N p hp]
      cases hh : ((σ.extPositions N).filter (· < p)).getLast? with
      | none => simpa using ih p c hp
      | some x =>
        have hx := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
        have hx' := hpos N x (List.mem_filter.mp hx).1
        simpa using ih x (c + 1) hx'
  have hcounts : ∀ s top p, p < σ.word.length →
      ρ.leftExt s top (flip p) = σ.rightExt s top p ∧
      ρ.rightExt s top (flip p) = σ.leftExt s top p := by
    intro s top p hp
    constructor
    · rw [Ctx.Context.leftExt_eq, Ctx.Context.rightExt_eq, hlevels]
      congr 2
      apply List.map_congr_left
      intro ls _
      exact hfoldLeft ls p 0 hp
    · rw [Ctx.Context.rightExt_eq, Ctx.Context.leftExt_eq, hlevels]
      congr 2
      apply List.map_congr_left
      intro ls _
      exact hfoldRight ls p 0 hp
  have hchain : ∀ s p q, p < σ.word.length → q < σ.word.length →
      ρ.chainExt s (flip q) (flip p) = σ.chainExt s p q := by
    intro s p q hp hq
    simp only [Ctx.Context.chainExt, (hcounts s 0 q hq).1, (hcounts s 0 p hp).2]
    omega
  have hjoin : ∀ s p q, p < σ.word.length → q < σ.word.length →
      ρ.joinExt s (flip q) (flip p) = σ.joinExt s p q := by
    intro s p q hp hq
    unfold Ctx.Context.joinExt
    rw [hchain s p q hp hq, hlevels]
    congr 3
    apply List.map_congr_left
    intro N _
    rw [(hcounts s N q hq).1, (hcounts s N p hp).2]
    change σ.rightExt s N q + σ.leftExt s N p + σ.maximumAt N = _
    omega
  refine ⟨hwell, hcounts, ?_⟩
  intro p q hp hq
  constructor
  · change min (σ.u - 1 - ρ.chainExt Ctx.Side.lower (flip q) (flip p))
      (σ.k - 1 - ρ.joinExt Ctx.Side.lower (flip q) (flip p)) = _
    rw [hchain _ p q hp hq, hjoin _ p q hp hq]
    rfl
  · change min (σ.a - 1 - ρ.chainExt Ctx.Side.upper (flip q) (flip p))
      (σ.k - 1 - ρ.joinExt Ctx.Side.upper (flip q) (flip p)) = _
    rw [hchain _ p q hp hq, hjoin _ p q hp hq]
    rfl

end ErdosSzekeres
