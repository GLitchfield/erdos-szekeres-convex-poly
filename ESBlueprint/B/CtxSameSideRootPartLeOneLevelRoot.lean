import ESBlueprint.B.CtxBoundLeMergeSameSideLevels

set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

namespace ErdosSzekeres
open Ctx Ctx.Context MergeLevels

/-- A legal part taken on the actual old side of a well-formed uniform one-level root is bounded above by a uniform one-level root with the same globals, identical genuine child positions and sibling maximum max(c,m), provided an actual genuine child is removed. Merge the fresh and old same-side levels using the closed merge theorem. This enables the full smaller-root normal-form induction hypothesis for one actual cut component; it does not bound the mixed-side companion or the coupled sum.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_same_side_root_part_le_one_level_root (σ : Ctx.Context) (m c : ℕ) (hmax : σ.maxima = [m])
  (hwf : σ.WellFormed) (s : Ctx.Side)
  (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
  (hside : σ.sideAt 1 = s) (keep : List ℕ) (q : ℕ)
  (hq : q ∈ σ.childPositions) (hnot : q ∉ keep)
  (hc : 1 ≤ c) (hck : c ≤ σ.k - 2) :
  ∃ ρ : Ctx.Context, ρ.a = σ.a ∧ ρ.u = σ.u ∧ ρ.k = σ.k ∧
    ρ.maxima = [max c m] ∧
    (∀ v ∈ ρ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s) ∧
    ρ.childPositions = (σ.part keep s c).childPositions ∧
    (σ.part keep s c).bound ≤ ρ.bound := by
  classical
  let δ := σ.part keep s c
  let letter : Ctx.Letter → Ctx.Letter := fun x => match x with
    | Ctx.Letter.ext j v =>
      if j ≤ 1 then Ctx.Letter.ext j v else Ctx.Letter.ext (j - 1) v
    | Ctx.Letter.child => Ctx.Letter.child
  let ρ : Ctx.Context := {δ with word := δ.word.map letter, maxima := [max c m]}
  have hδmax : δ.maxima = [c,m] := by simp only [δ, Ctx.Context.part_maxima, hmax]
  have hδwf : δ.WellFormed := hwf.part keep s hc hck
  have hqR : q < σ.word.length := List.mem_range.mp (List.mem_filter.mp hq).1
  have hqAt : σ.letterAt q = Ctx.Letter.child :=
    of_decide_eq_true (List.mem_filter.mp hq).2
  have hqNew : δ.letterAt q = Ctx.Letter.ext 1 s := by
    simpa only [δ, hnot, if_false] using
      Ctx.Context.part_letterAt_of_child σ keep s c hqR hqAt
  have hδsideOne : δ.sideAt 1 = s :=
    (hδwf.2.2.2.2.2 q 1 s hqNew).2.2.symm
  have hδsideTwo : δ.sideAt 2 = s := by
    simpa only [δ, hside] using
      Ctx.Context.part_sideAt_succ σ keep s c (by omega : 1 ≤ 1)
  have hMerge := ctx_bound_le_merge_same_side_levels δ hδwf 1 (by omega)
    (by simp only [hδmax, List.length_cons, List.length_nil]; omega)
    (hδsideOne.trans hδsideTwo.symm)
  have hMergedMax : δ.maxima.take (1-1) ++
      [max (δ.maximumAt 1) (δ.maximumAt (1+1))] ++ δ.maxima.drop (1+1) = [max c m] := by
    simp [hδmax, Ctx.Context.maximumAt]
  have hbound : δ.bound ≤ ρ.bound := by
    simpa only [hMergedMax, ρ, letter] using hMerge
  have hLetter (p : ℕ) : ρ.letterAt p = letter (δ.letterAt p) := by
    simp only [ρ, Ctx.Context.letterAt, List.getElem?_map]
    cases δ.word[p]? <;> rfl
  have hChild (p : ℕ) : ρ.letterAt p = Ctx.Letter.child ↔
      δ.letterAt p = Ctx.Letter.child := by
    rw [hLetter]
    cases δ.letterAt p with
    | child => simp [letter]
    | ext j v => by_cases hj : j ≤ 1 <;> simp [letter, hj]
  have hLength : ρ.word.length = δ.word.length := by simp only [ρ, List.length_map]
  have hpositions : ρ.childPositions = δ.childPositions := by
    simp only [Ctx.Context.childPositions, hLength, hChild]
  have hδletters (v : Ctx.Letter) (hv : v ∈ δ.word) :
      v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s ∨ v = Ctx.Letter.ext 2 s := by
    change v ∈ (List.range σ.word.length).map (fun p =>
      match σ.letterAt p with
      | Ctx.Letter.child => if p ∈ keep then Ctx.Letter.child else Ctx.Letter.ext 1 s
      | Ctx.Letter.ext j w => Ctx.Letter.ext (j+1) w) at hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    have hpR : p < σ.word.length := List.mem_range.mp hp
    have hAt : σ.letterAt p = σ.word[p] := by
      simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hpR]
    rcases hletters _ (List.getElem_mem hpR) with h | h
    · rw [hAt, h]
      by_cases hkeep : p ∈ keep <;> simp [hkeep]
    · rw [hAt, h]
      simp
  have hρletters (v : Ctx.Letter) (hv : v ∈ ρ.word) :
      v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s := by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rcases hδletters w hw with h | h | h <;> rw [h] <;> simp [letter]
  exact ⟨ρ, rfl, rfl, rfl, rfl, hρletters, hpositions, hbound⟩

end ErdosSzekeres
