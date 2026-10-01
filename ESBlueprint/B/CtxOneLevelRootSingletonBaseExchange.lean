import ESBlueprint.B.CtxOneLevelRootSingletonBaseExchangeUnitAxis
import ESBlueprint.B.CtxOneLevelRootSingletonBaseExchangeChosenAxisTwo
import ESBlueprint.B.CtxPairContractionSingletonValueMonoOfOppositeGlobalTwo
import ESBlueprint.B.CtxOneLevelRootSingletonBaseExchangeInsidePairSourceOppositeThree
import ESBlueprint.B.CtxOneLevelRootSingletonBaseExchangeOutsideSingleRun
import ESBlueprint.B.CtxOneLevelRootSingletonBaseExchangeOutsideMultirunSourceOppositeThree
import ErdosSzekeres.DecomposableContextLemmas

set_option maxHeartbeats 6000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Localized singleton-base versus complement-part exchange for a multi-run one-level root containing an adjacent child pair. Delete the second copy and map the chosen singleton position across that deletion. Its explicit threshold T plus the complement bound is dominated by the same mapped singleton in the shorter root at some orientation and admissible coupling. Both leaf values are explicit thresholds; no contraction or all-cut bound hypothesis is assumed. Finite R13 probes pass, but deriving C1r from this local exchange remains a separate open obligation.
@node
@ws B
@kind conjecture
@depends ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_unit_axis, ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_chosen_axis_two, ErdosSzekeres.ctx_pair_contraction_singleton_value_mono_of_opposite_global_two, ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_inside_pair_source_opposite_three, ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_outside_single_run, ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_outside_multirun_source_opposite_three
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root
@falsifier ctx_one_level_root_singleton_base_exchange.py -/
theorem ctx_one_level_root_singleton_base_exchange (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2) (side : Ctx.Side) (left right : List Ctx.Letter) (hletters : ∀ x ∈ left ++ right, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) :
  let σ : Ctx.Context := { a := a, u := u, k := k, word := left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right, maxima := [m] }
  let ρ : Ctx.Context := { a := a, u := u, k := k, word := left ++ [Ctx.Letter.child] ++ right, maxima := [m] }
  let opposite : Ctx.Side → Ctx.Side := fun s => match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower
  2 ≤ σ.numRuns →
  ∀ p ∈ σ.childPositions, ∀ (s : Ctx.Side) (c : ℕ), 1 ≤ c → c ≤ k - 2 →
    let q := if p ≤ left.length then p else p - 1
    ∃ (t : Ctx.Side) (d : ℕ), 1 ≤ d ∧ d ≤ k - 2 ∧
      decomposableThreshold ((σ.part [p] s c).capLimit p p + 1) ((σ.part [p] s c).cupLimit p p + 1) k +
          (σ.part (σ.childPositions.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)).bound ≤
      decomposableThreshold ((ρ.part [q] t d).capLimit q q + 1) ((ρ.part [q] t d).cupLimit q q + 1) k +
          (ρ.part (ρ.childPositions.filter (fun r => r ≠ q)) (opposite t) (k - 1 - d)).bound := by
  classical
  by_cases hunit : a ≤ 1 ∨ u ≤ 1
  · exact ctx_one_level_root_singleton_base_exchange_unit_axis
      a u k m hk ha hak hu huk hm hmk hunit side left right hletters
  have ha2 : 2 ≤ a := by omega
  have hu2 : 2 ≤ u := by omega
  by_cases hsmall : (match side with | Side.lower => u | Side.upper => a) ≤ 2
  · exact ctx_one_level_root_singleton_base_exchange_chosen_axis_two
      a u k m hk ha hak hu huk hm hmk side hsmall left right hletters
  have hchosen : 3 ≤ (match side with | Side.lower => u | Side.upper => a) := by omega
  dsimp only
  intro hruns p hp s c hc hck
  let σ : Context :=
    ⟨a, u, k, left ++ [Letter.child, Letter.child] ++ right, [m]⟩
  let opposite : Side → Side := fun t => match t with
    | .lower => .upper
    | .upper => .lower
  by_cases hsource : (match s with | Side.lower => a | Side.upper => u) ≤ 2
  ·
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
    have hwf : σ.WellFormed := hWF _ hσletters
    have hmono := ctx_pair_contraction_singleton_value_mono_of_opposite_global_two
      σ hwf left right rfl hruns p hp s c hc hck (by simpa only [σ] using hsource)
    refine ⟨s, c, hc, hck, ?_⟩
    cases s <;> simpa only [σ, opposite] using hmono
  have hsource3 : 3 ≤ (match s with | Side.lower => a | Side.upper => u) := by omega
  by_cases hpinside : p = left.length ∨ p = left.length + 1
  · exact ctx_one_level_root_singleton_base_exchange_inside_pair_source_opposite_three
      a u k m hk ha hak hu huk hm hmk ha2 hu2 side hchosen left right hletters
      hruns p hp s c hc hck hsource3 hpinside
  have hp0 : p ≠ left.length := by omega
  have hp1 : p ≠ left.length + 1 := by omega
  by_cases hcomp : (σ.part (σ.childPositions.filter (fun r => r ≠ p))
      (opposite s) (k - 1 - c)).numRuns ≤ 1
  · exact ctx_one_level_root_singleton_base_exchange_outside_single_run
      a u k m hk ha hak hu huk hm hmk ha2 hu2 side left right hletters
      hruns p hp s c hc hck hp0 hp1 hcomp
  have hcomp2 : 2 ≤ (σ.part (σ.childPositions.filter (fun r => r ≠ p))
      (opposite s) (k - 1 - c)).numRuns := by omega
  exact ctx_one_level_root_singleton_base_exchange_outside_multirun_source_opposite_three
    a u k m hk ha hak hu huk hm hmk ha2 hu2 side hchosen left right hletters
    hruns p hp s c hc hck hsource3 hp0 hp1 hcomp2


end ErdosSzekeres
