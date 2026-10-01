import ESBlueprint.B.CtxBoundChildLetterExpansion
import ESBlueprint.B.CtxNumRunsChildLetterContraction
import ESBlueprint.B.CtxBoundZeroOfUnitGlobalAxis
import ESBlueprint.B.CtxSingletonPartBoundEqThreshold

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Conditional one-level-root run contraction from two explicit local inputs: singleton-cut attainment N_root for the doubled root and the mapped singleton-base/complement exchange X to the shortened root. Neither input theorem is imported or assumed as an axiom. The reverse inequality follows from closed child expansion, including unit global axes; the single-run branch uses closed base contraction and run-count transport. Registers the full R13 conditional interface as the two-hypothesis narrowing authorized for R14.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_num_runs_child_letter_contraction, ErdosSzekeres.ctx_bound_zero_of_unit_global_axis, ErdosSzekeres.ctx_bound_child_letter_expansion, ErdosSzekeres.ctx_singleton_part_bound_eq_threshold, ErdosSzekeres.ctx_bound_cut_le, ErdosSzekeres.ctx_base_child_letter_contraction
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_bound_child_run_contraction_one_level_root_of_singleton_exchange (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k)
    (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2)
    (side : Ctx.Side) (left right : List Ctx.Letter)
    (hletters : ∀ x ∈ left ++ right, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) :
  let σ : Ctx.Context := {a := a, u := u, k := k, word := left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right, maxima := [m]}
  let ρ : Ctx.Context := {a := a, u := u, k := k, word := left ++ [Ctx.Letter.child] ++ right, maxima := [m]}
  let opposite : Ctx.Side → Ctx.Side := fun s => match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower
  (2 ≤ σ.numRuns → ∃ p ∈ σ.childPositions, ∃ (s : Ctx.Side) (c : ℕ),
    1 ≤ c ∧ c ≤ k - 2 ∧
    σ.bound ≤ decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
      ((σ.part [p] s c).cupLimit p p + 1) k +
      (σ.part (σ.childPositions.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)).bound) →
  (2 ≤ σ.numRuns → ∀ p ∈ σ.childPositions, ∀ (s : Ctx.Side) (c : ℕ), 1 ≤ c → c ≤ k - 2 →
    let q := if p ≤ left.length then p else p - 1
    ∃ (t : Ctx.Side) (d : ℕ), 1 ≤ d ∧ d ≤ k - 2 ∧
    decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
      ((σ.part [p] s c).cupLimit p p + 1) k +
      (σ.part (σ.childPositions.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)).bound ≤
    decomposableThreshold ((ρ.part [q] t d).capLimit q q + 1)
      ((ρ.part [q] t d).cupLimit q q + 1) k +
      (ρ.part (ρ.childPositions.filter (fun r => r ≠ q)) (opposite t) (k - 1 - d)).bound) →
  σ.bound = ρ.bound := by
  classical
  dsimp only
  intro hN hX
  let σ : Context := {a := a, u := u, k := k, word := left ++ [Letter.child, Letter.child] ++ right, maxima := [m]}
  let ρ : Context := {a := a, u := u, k := k, word := left ++ [Letter.child] ++ right, maxima := [m]}
  change σ.bound = ρ.bound
  have hrev : ρ.bound ≤ σ.bound := by
    classical
    let σ : Context := {a := a, u := u, k := k, word := left ++ [Letter.child, Letter.child] ++ right, maxima := [m]}
    let ρ : Context := {σ with word := left ++ [Letter.child] ++ right}
    change ρ.bound ≤ σ.bound
    by_cases hzero : a ≤ 1 ∨ u ≤ 1
    · have hb := (ctx_bound_zero_of_unit_global_axis σ hzero).2
      have hs := (ctx_bound_zero_of_unit_global_axis ρ hzero).2
      rw [hb, hs]
    · have ha2 : 2 ≤ a := by omega
      have hu2 : 2 ≤ u := by omega
      have hWF : ∀ w : List Letter,
          (∀ x ∈ w, x = Letter.child ∨ x = Letter.ext 1 side) →
          ({a := a, u := u, k := k, word := w, maxima := [m]} : Context).WellFormed := by
        intro w hw
        let τ : Context := {a := a, u := u, k := k, word := w, maxima := [m]}
        have hshape : ∀ p l t, τ.letterAt p = Letter.ext l t → l = 1 ∧ t = side := by
          intro p l t hext
          have hp : p < τ.word.length := by
            by_contra hn
            have h := letterAt_of_length_le τ (Nat.le_of_not_gt hn)
            rw [h] at hext
            cases hext
          have hmem : Letter.ext l t ∈ w := by
            have hget : τ.word[p] = Letter.ext l t := by
              simpa [letterAt, hp] using hext
            rw [← hget]
            exact List.getElem_mem _
          rcases hw _ hmem with h | h
          · cases h
          · cases h
            exact ⟨rfl, rfl⟩
        refine ⟨ha2, hu2, hak, huk, ?_, ?_⟩
        · intro n hn
          simp only [List.mem_singleton] at hn
          subst n
          exact ⟨hm, hmk⟩
        · intro p l t hext
          change τ.letterAt p = Letter.ext l t at hext
          obtain ⟨rfl, rfl⟩ := hshape p l t hext
          refine ⟨by omega, by simp, ?_⟩
          have hpExt : p ∈ τ.extPositions 1 := by
            have hp : p < τ.word.length := by
              by_contra hn
              have h := letterAt_of_length_le τ (Nat.le_of_not_gt hn)
              rw [h] at hext
              cases hext
            simp [extPositions, hp, hext]
          cases hh : (τ.extPositions 1).head? with
          | none =>
            have hn := List.head?_eq_none_iff.mp hh
            rw [hn] at hpExt
            simp at hpExt
          | some q =>
            have hq := List.mem_of_mem_head? hh
            have hqe := (List.mem_filter.mp hq).2
            cases hl : τ.letterAt q with
            | child => simp [hl] at hqe
            | ext j v =>
              obtain ⟨rfl, rfl⟩ := hshape q j v hl
              change v = τ.sideAt 1
              simp [sideAt, hh, hl]
      have hσletters : ∀ x ∈ σ.word, x = Letter.child ∨ x = Letter.ext 1 side := by
        intro x hx
        by_cases hc : x = Letter.child
        · exact Or.inl hc
        · apply hletters x
          simpa [σ, hc, List.mem_append] using hx
      exact ctx_bound_child_letter_expansion σ (hWF _ hσletters) left right rfl
  have htransport : ∀ (σ : Context) (left right : List Letter)
    (hword : σ.word = left ++ [Letter.child, Letter.child] ++ right)
    (p : ℕ) (hp : p ∈ σ.childPositions),
    (if p ≤ left.length then p else p - 1) ∈
      ({σ with word := left ++ [Letter.child] ++ right} : Context).childPositions := by
    intro σ left right hword p hp
    let small : Context := {σ with word := left ++ [Letter.child] ++ right}
    let q := if p ≤ left.length then p else p - 1
    change q ∈ small.childPositions
    have hpdata := List.mem_filter.mp hp
    have hplen : p < σ.word.length := List.mem_range.mp hpdata.1
    have hpchild : σ.letterAt p = Letter.child := of_decide_eq_true hpdata.2
    have hbw : σ.word = left ++ Letter.child :: Letter.child :: right := by
      simpa [List.append_assoc] using hword
    have hsw : small.word = left ++ Letter.child :: right := by
      simp [small, List.append_assoc]
    have hbiglen : σ.word.length = left.length + 2 + right.length := by
      simp [hword]
      omega
    have hsmalllen : small.word.length = left.length + 1 + right.length := by
      simp [hsw]
      omega
    unfold childPositions
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_range.mpr
      dsimp only [q]
      split_ifs <;> omega
    · simp only [decide_eq_true_eq]
      by_cases hple : p ≤ left.length
      · dsimp only [q]
        rw [if_pos hple]
        by_cases hplt : p < left.length
        · simpa only [letterAt, hsw, hbw, List.getElem?_append_left hplt] using hpchild
        · have hpeq : p = left.length := by omega
          subst p
          simp [letterAt, hsw]
      · dsimp only [q]
        rw [if_neg hple]
        have hpl : left.length ≤ p := by omega
        have hql : left.length ≤ p - 1 := by omega
        have hsub : p - left.length = (p - 1 - left.length) + 1 := by omega
        simp only [letterAt, hbw, List.getElem?_append_right hpl, hsub,
          List.getElem?_cons_succ] at hpchild
        simpa only [letterAt, hsw, List.getElem?_append_right hql] using hpchild
  have hreduce : ∀ (σ ρ : Context) (hruns : 2 ≤ ρ.numRuns)
    (hN : ∃ p ∈ σ.childPositions, ∃ (s : Side) (c : ℕ),
      1 ≤ c ∧ c ≤ σ.k - 2 ∧
      σ.bound ≤ decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
        ((σ.part [p] s c).cupLimit p p + 1) σ.k +
        (σ.part (σ.childPositions.filter (fun r => r ≠ p))
          (match s with | Side.lower => Side.upper | Side.upper => Side.lower)
          (σ.k - 1 - c)).bound)
    (hX : ∀ p ∈ σ.childPositions, ∀ (s : Side) (c : ℕ),
      1 ≤ c → c ≤ σ.k - 2 →
      ∃ q ∈ ρ.childPositions, ∃ (t : Side) (d : ℕ), 1 ≤ d ∧ d ≤ ρ.k - 2 ∧
        decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
          ((σ.part [p] s c).cupLimit p p + 1) σ.k +
          (σ.part (σ.childPositions.filter (fun r => r ≠ p))
            (match s with | Side.lower => Side.upper | Side.upper => Side.lower)
            (σ.k - 1 - c)).bound ≤
        decomposableThreshold ((ρ.part [q] t d).capLimit q q + 1)
          ((ρ.part [q] t d).cupLimit q q + 1) ρ.k +
          (ρ.part (ρ.childPositions.filter (fun r => r ≠ q))
            (match t with | Side.lower => Side.upper | Side.upper => Side.lower)
            (ρ.k - 1 - d)).bound), σ.bound ≤ ρ.bound := by
    intro σ ρ hruns hN hX
    classical
    obtain ⟨p, hp, s, c, hc, hck, hN⟩ := hN
    obtain ⟨q, hq, t, d, hd, hdk, hX⟩ := hX p hp s c hc hck
    have hn : 2 ≤ ρ.childPositions.length := hruns.trans (numRuns_le_length ρ)
    have hb : [q] ∈ ρ.blocks := by
      obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp hq
      have hwindow : (ρ.childPositions.drop i).take 1 = [q] := by
        simpa only [List.get_eq_getElem, hqi] using List.take_one_drop_eq_of_lt_length hi
      unfold blocks
      apply List.mem_filter.mpr
      refine ⟨?_, by simpa using hn⟩
      apply List.mem_flatMap.mpr
      refine ⟨i, List.mem_range.mpr hi, ?_⟩
      apply List.mem_map.mpr
      exact ⟨0, List.mem_range.mpr (by omega), hwindow⟩
    have hcut : decomposableThreshold ((ρ.part [q] t d).capLimit q q + 1)
        ((ρ.part [q] t d).cupLimit q q + 1) ρ.k +
        (ρ.part (ρ.childPositions.filter (fun r => r ≠ q))
          (match (generalizing := false) t with | Side.lower => Side.upper | Side.upper => Side.lower)
          (ρ.k - 1 - d)).bound ≤ ρ.bound := by
      rw [← ctx_singleton_part_bound_eq_threshold ρ q hq t d]
      cases t with
      | lower =>
        simpa only [List.mem_singleton] using (ctx_bound_cut_le ρ hruns [q] hb d hd hdk).1
      | upper =>
        have he1 : 1 ≤ ρ.k - 1 - d := by omega
        have hek : ρ.k - 1 - d ≤ ρ.k - 2 := by omega
        have he : ρ.k - 1 - (ρ.k - 1 - d) = d := by omega
        simpa only [List.mem_singleton, he] using
          (ctx_bound_cut_le ρ hruns [q] hb (ρ.k - 1 - d) he1 hek).2
    exact hN.trans (hX.trans hcut)
  by_cases hsmall : σ.numRuns ≤ 1
  · have hrho : ρ.numRuns ≤ 1 := by
      have h := ctx_num_runs_child_letter_contraction σ left right rfl
      change σ.numRuns = ρ.numRuns at h
      omega
    simp only [Context.bound, boundFuel.eq_2, if_pos hsmall, if_pos hrho]
    exact ctx_base_child_letter_contraction σ left right rfl
  · have hruns : 2 ≤ σ.numRuns := by omega
    have hrhoruns : 2 ≤ ρ.numRuns := by
      have h := ctx_num_runs_child_letter_contraction σ left right rfl
      change σ.numRuns = ρ.numRuns at h
      omega
    apply le_antisymm _ hrev
    apply hreduce σ ρ hrhoruns (hN hruns)
    intro p hp s c hc hck
    let q := if p ≤ left.length then p else p - 1
    obtain ⟨t, d, hd, hdk, hex⟩ := hX hruns p hp s c hc hck
    have hq : q ∈ ρ.childPositions := htransport σ left right rfl p hp
    exact ⟨q, hq, t, d, hd, hdk, hex⟩

end ErdosSzekeres
