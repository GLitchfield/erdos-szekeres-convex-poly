import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank
import ESBlueprint.B.CtxBoundCutLe
import ESBlueprint.B.CtxSingletonPartBoundEqThreshold

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 12000000
set_option maxRecDepth 20000

/-- An explicit kernel-certified legal one-level counterexample to restricting singleton attainment to the first and last global children. Globals a=2/u=3/k=4, maximum one, word child child old-lower-marker child child. WellFormed, exactly two runs/childPositions[0,1,3,4]/source bound one; every legal coupling at either global end has both orientation sums zero. The inner first-run-end singleton at position one with upper maximum two/lower companion one has exact raw-threshold cut value one and attains. Certifies the documented need for inner extreme run ends; this is not a counterexample to N_ends or N_root. Uses closed common-singleton-rank upper and cut domination plus finite ordinary kernel decide evaluations, no native_decide/axiom/certificate assumption.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_one_level_root_global_end_singleton_selector_counterexample : let σ : Ctx.Context := { a := 2, u := 3, k := 4, word := [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.child, Ctx.Letter.child], maxima := [1] }; σ.WellFormed ∧ σ.numRuns = 2 ∧ σ.childPositions = [0,1,3,4] ∧ σ.bound = 1 ∧ (∀ p : ℕ, (σ.childPositions.head? = some p ∨ σ.childPositions.getLast? = some p) → ∀ d : ℕ, 1 ≤ d → d ≤ σ.k-2 → (σ.part [p] Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k-1-d)).bound = 0 ∧ (σ.part [p] Ctx.Side.upper (σ.k-1-d)).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d).bound = 0) ∧ decomposableThreshold ((σ.part [1] Ctx.Side.upper 2).capLimit 1 1+1) ((σ.part [1] Ctx.Side.upper 2).cupLimit 1 1+1) 4 + (σ.part (σ.childPositions.filter (fun q => q ≠ 1)) Ctx.Side.lower 1).bound = 1 := by
  let k : ℕ := 4
  have hRootWF (M : ℕ) (hM : 1 ≤ M) (hMk : M ≤ k-2)
      (a u : ℕ) (ha2 : 2 ≤ a) (hu2 : 2 ≤ u)
      (hak : a ≤ k) (huk : u ≤ k) (v : Side) (w : List Letter)
      (hw : ∀ x ∈ w, x = Letter.child ∨ x = Letter.ext 1 v) :
      ({a := a, u := u, k := k, word := w, maxima := [M]} : Context).WellFormed := by
    let τ : Context := {a := a, u := u, k := k, word := w, maxima := [M]}
    have hshape : ∀ p l t, τ.letterAt p = Letter.ext l t → l = 1 ∧ t = v := by
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
      exact ⟨hM, hMk⟩
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
  let σ : Context :=
    { a := 2, u := 3, k := 4
      word := [Letter.child,Letter.child,Letter.ext 1 Side.lower,Letter.child,Letter.child]
      maxima := [1] }
  change σ.WellFormed ∧ σ.numRuns = 2 ∧ σ.childPositions = [0,1,3,4] ∧ σ.bound = 1 ∧ (∀ p : ℕ, (σ.childPositions.head? = some p ∨ σ.childPositions.getLast? = some p) → ∀ d : ℕ, 1 ≤ d → d ≤ σ.k-2 → (σ.part [p] Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k-1-d)).bound = 0 ∧ (σ.part [p] Ctx.Side.upper (σ.k-1-d)).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d).bound = 0) ∧ decomposableThreshold ((σ.part [1] Ctx.Side.upper 2).capLimit 1 1+1) ((σ.part [1] Ctx.Side.upper 2).cupLimit 1 1+1) 4 + (σ.part (σ.childPositions.filter (fun q => q ≠ 1)) Ctx.Side.lower 1).bound = 1
  have hWord : ∀ z ∈ σ.word, z = Letter.child ∨ z = Letter.ext 1 Side.lower := by
    intro z hz
    simp only [σ,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
  have hWF : σ.WellFormed :=
    hRootWF 1 (by decide) (by decide) 2 3 (by decide) (by decide)
      (by decide) (by decide) Side.lower σ.word hWord
  have hPositive : ∀ p j v, σ.letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v he
    exact (hWF.2.2.2.2.2 p j v he).1
  have hRuns : σ.numRuns = 2 := by decide
  have hPositions : σ.childPositions = [0,1,3,4] := by decide
  have hOppEmpty : σ.levelsOn Side.upper 0 = [] := by decide
  have hRank : ∀ p ∈ σ.childPositions,
      0 < σ.cupLimit p p → 0 < σ.capLimit p p →
      σ.leftExt Side.upper 0 p+1 = 1 ∧
        1+σ.rightExt Side.upper 0 p = σ.a-1 := by
    intro p hp hcu hca
    simp [leftExt,rightExt,hOppEmpty,σ]
  have hUpper : σ.bound ≤ 1 :=
    (ctx_bound_le_one_of_common_singleton_rank σ hPositive Side.upper 1 hRank).2.1
  have hInnerParts :
      (σ.part [1] Side.upper 2).bound +
        (σ.part (σ.childPositions.filter (fun q => q ≠ 1)) Side.lower 1).bound = 1 := by
    decide +kernel
  have hBlock : [1] ∈ σ.blocks := by decide
  have hLow :
      (σ.part [1] Side.upper 2).bound +
        (σ.part (σ.childPositions.filter (fun q => q ≠ 1)) Side.lower 1).bound ≤ σ.bound := by
    have h := (ctx_bound_cut_le σ (by omega : 2 ≤ σ.numRuns) [1] hBlock
      1 (by decide) (by decide)).2
    simpa only [show σ.k = 4 from rfl,Nat.reduceSub,List.mem_singleton] using h
  have hBound : σ.bound = 1 := by omega
  have hGlobal : ∀ p : ℕ,
      (σ.childPositions.head? = some p ∨ σ.childPositions.getLast? = some p) →
      ∀ d : ℕ, 1 ≤ d → d ≤ σ.k-2 →
      (σ.part [p] Side.lower d).bound +
        (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Side.upper (σ.k-1-d)).bound = 0 ∧
      (σ.part [p] Side.upper (σ.k-1-d)).bound +
        (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Side.lower d).bound = 0 := by
    intro p hp d hd1 hd2
    have hp' : p = 0 ∨ p = 4 := by simpa [hPositions,eq_comm] using hp
    have hd' : d = 1 ∨ d = 2 := by change d ≤ 2 at hd2; omega
    rcases hp' with rfl | rfl <;> rcases hd' with rfl | rfl <;> decide +kernel
  have hInnerRaw :
      decomposableThreshold ((σ.part [1] Side.upper 2).capLimit 1 1+1)
        ((σ.part [1] Side.upper 2).cupLimit 1 1+1) 4 +
        (σ.part (σ.childPositions.filter (fun q => q ≠ 1)) Side.lower 1).bound = 1 := by
    have hp : 1 ∈ σ.childPositions := by rw [hPositions]; simp
    rw [← ctx_singleton_part_bound_eq_threshold σ 1 hp Side.upper 2]
    exact hInnerParts
  exact ⟨hWF,hRuns,hPositions,hBound,hGlobal,hInnerRaw⟩

end ErdosSzekeres
