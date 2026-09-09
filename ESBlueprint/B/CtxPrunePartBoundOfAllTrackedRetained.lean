import ESBlueprint.B.CtxPrunePartProjectionOfRemovedWitness

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- If all tracked source children are kept, pruning the part to that tracked group is dominated by pruning the original source to the group, at every fuel and for the full bound. Covers empty groups and arbitrary sibling maxima under positive labels. Erases the new level and compares unindexed marker sides through exact indexed histories. Handles groups lying entirely within one side of a cut in the proposed run-group decomposition.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_prune_part_bound_of_all_tracked_retained (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (support keep : List ℕ) (v : Ctx.Side) (m : ℕ)
  (hall : ∀ p ∈ σ.childPositions, p ∈ support → p ∈ keep) :
  let prune := fun (ρ : Ctx.Context) => { ρ with
    word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
      | Ctx.Letter.child => if p ∈ support then Ctx.Letter.child
          else Ctx.Letter.ext (ρ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j s => Ctx.Letter.ext j s) }
  (∀ fuel, Ctx.Context.boundFuel fuel (prune (σ.part keep v m)) ≤
    Ctx.Context.boundFuel fuel (prune σ)) ∧ (prune (σ.part keep v m)).bound ≤ (prune σ).bound := by
  classical
  let prune (ρ : Context) (ks : List ℕ) (w : Side) : Context := { ρ with
    word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
      | Letter.child => if p ∈ ks then Letter.child else Letter.ext (ρ.maxima.length + 1) w
      | Letter.ext j s => Letter.ext j s) }
  have hPLen (ρ : Context) (ks : List ℕ) (w : Side) :
      (prune ρ ks w).word.length = ρ.word.length := by simp [prune]
  have hPLetter (ρ : Context) (ks : List ℕ) (w : Side) (p : ℕ) (hp : p < ρ.word.length) :
      (prune ρ ks w).letterAt p = (match ρ.letterAt p with
        | Letter.child => if p ∈ ks then Letter.child else Letter.ext (ρ.maxima.length + 1) w
        | Letter.ext j s => Letter.ext j s) := by
    simp only [prune, letterAt, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some]
  have hSideEq (ρ : Context)
      (hpos : ∀ p j w, ρ.letterAt p = Letter.ext j w → 1 ≤ j)
      (ks : List ℕ) (v w : Side) :
      (∀ fuel, boundFuel fuel (prune ρ ks v) = boundFuel fuel (prune ρ ks w)) ∧
        (prune ρ ks v).bound = (prune ρ ks w).bound := by
    have hMono (v w : Side) :
        (∀ fuel, boundFuel fuel (prune ρ ks v) ≤ boundFuel fuel (prune ρ ks w)) ∧
          (prune ρ ks v).bound ≤ (prune ρ ks w).bound := by
      obtain ⟨hVPos, hVChild, hVHist, hVLevels, hVExt, hVLimits, hVActive, hVFuel, hVBound⟩ :=
        ctx_part_pruning_history_transport ρ hpos ks v 0
      obtain ⟨hWPos, hWChild, hWHist, hWLevels, hWExt, hWLimits, hWActive, hWFuel, hWBound⟩ :=
        ctx_part_pruning_history_transport ρ hpos ks w 0
      have hchild (r : ℕ) : (prune ρ ks v).letterAt r = Letter.child ↔
          (prune ρ ks w).letterAt r = Letter.child := by
        by_cases hr : r < ρ.word.length
        · rw [hPLetter ρ ks v r hr, hPLetter ρ ks w r hr]
          cases ρ.letterAt r <;> simp
        · rw [letterAt_of_length_le (prune ρ ks v) (by rw [hPLen]; omega),
            letterAt_of_length_le (prune ρ ks w) (by rw [hPLen]; omega)]
      have hhist (j : ℕ) (hj : j ∈ (prune ρ ks v).levels) :
          (prune ρ ks w).sideAt j = (prune ρ ks v).sideAt j ∧
          (prune ρ ks w).extPositions j ⊆ (prune ρ ks v).extPositions j ∧
          (prune ρ ks w).maximumAt j ≤ (prune ρ ks v).maximumAt j := by
        have hv : (prune ρ ks v).extPositions j = ρ.extPositions j ∧
            (prune ρ ks v).sideAt j = ρ.sideAt j := hVHist j hj
        have hw : (prune ρ ks w).extPositions j = ρ.extPositions j ∧
            (prune ρ ks w).sideAt j = ρ.sideAt j := hWHist j hj
        refine ⟨hw.2.trans hv.2.symm, ?_, le_rfl⟩
        rw [hw.1, hv.1]
        exact fun _ hp => hp
      exact (ctx_bound_mono_of_marker_inclusion (prune ρ ks v) (prune ρ ks w)
        hVPos hWPos le_rfl le_rfl rfl (by rw [hPLen, hPLen]) hchild rfl hhist).2
    exact ⟨fun fuel => le_antisymm ((hMono v w).1 fuel) ((hMono w v).1 fuel),
      le_antisymm (hMono v w).2 (hMono w v).2⟩
  have hPartPos : ∀ r j w, (σ.part keep v m).letterAt r = Letter.ext j w → 1 ≤ j := by
    intro r j w hr
    have hrl : r < σ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (σ.part keep v m)
        (show (σ.part keep v m).word.length ≤ r by rw [part_word_length]; omega)
      rw [hn] at hr
      cases hr
    cases he : σ.letterAt r with
    | child =>
      rw [part_letterAt_of_child σ keep v m hrl he] at hr
      split at hr
      · cases hr
      · cases hr; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ keep v m hrl he] at hr
      cases hr; omega
  let A := prune (σ.part keep v m) support v
  let T := prune σ support v
  let E : Context := { A with
    word := A.word.map (fun x => match x with
      | Letter.child => Letter.child
      | Letter.ext j w => Letter.ext
          (if j = 1 then A.maxima.length else if 1 < j then j - 1 else j) w)
    maxima := A.maxima.eraseIdx (1 - 1) }
  have h1 : 1 ∈ A.levels := by change 1 ∈ (σ.part keep v m).levels; simp [part_levels]
  have hErase := ctx_erase_level_bound_mono A 1 h1
  have hword : E.word = T.word := by
    change ((List.range (σ.part keep v m).word.length).map
      (fun p => match (σ.part keep v m).letterAt p with
        | Letter.child => if p ∈ support then Letter.child
            else Letter.ext ((σ.part keep v m).maxima.length + 1) v
        | Letter.ext j w => Letter.ext j w)).map
      (fun x => match x with
        | Letter.child => Letter.child
        | Letter.ext j w => Letter.ext
            (if j = 1 then (σ.part keep v m).maxima.length else if 1 < j then j - 1 else j) w) =
      (List.range σ.word.length).map (fun p => match σ.letterAt p with
        | Letter.child => if p ∈ support then Letter.child else Letter.ext (σ.maxima.length + 1) v
        | Letter.ext j w => Letter.ext j w)
    rw [List.map_map, part_word_length]
    apply List.map_congr_left
    intro r hr
    have hrl := List.mem_range.mp hr
    simp only [Function.comp_apply]
    cases he : σ.letterAt r with
    | child =>
      have hrc : r ∈ σ.childPositions := by simp [childPositions, hrl, he]
      rw [part_letterAt_of_child σ keep v m hrl he]
      by_cases hk : r ∈ keep
      · by_cases hs : r ∈ support <;> simp [Function.comp_apply, hk, hs, part]
      · have hs : r ∉ support := fun h => hk (hall r hrc h)
        simp [Function.comp_apply, hk, hs, part]
    | ext j w =>
      have hj := hpositive r j w he
      rw [part_letterAt_of_ext σ keep v m hrl he]
      simp [show j ≠ 0 by omega, show 1 < j + 1 by omega]
  have he : E = T := by
    exact congrArg (fun w : List Letter => ({ σ with word := w } : Context)) hword
  have hFrom := hSideEq (σ.part keep v m) hPartPos support Side.lower v
  have hTo := hSideEq σ hpositive support v Side.lower
  change (∀ fuel, boundFuel fuel (prune (σ.part keep v m) support Side.lower) ≤
    boundFuel fuel (prune σ support Side.lower)) ∧
      (prune (σ.part keep v m) support Side.lower).bound ≤ (prune σ support Side.lower).bound
  constructor
  · intro fuel
    rw [hFrom.1 fuel, ← hTo.1 fuel]
    exact (hErase.2.1 fuel).trans_eq (congrArg (boundFuel fuel) he)
  · rw [hFrom.2, ← hTo.2]
    exact hErase.2.2.trans_eq (congrArg Context.bound he)

end ErdosSzekeres
