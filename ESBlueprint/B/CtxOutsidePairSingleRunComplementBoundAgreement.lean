import ESBlueprint.B.CtxBaseChildLetterContraction
import ESBlueprint.B.CtxNumRunsChildLetterContraction

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- For any raw context, contracting an adjacent child pair preserves the complement bound at a singleton outside that pair whenever the original complement has at most one run. The complement word transports by deleting one retained child; run count and base are preserved by the closed raw child-contraction lemmas. No well-formedness, one-level or coupling hypothesis is needed. This is a strict subcase of the weighted complement exchange required by X.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_base_child_letter_contraction, ErdosSzekeres.ctx_num_runs_child_letter_contraction
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange -/
theorem ctx_outside_pair_single_run_complement_bound_agreement (σ : Ctx.Context) (left right : List Ctx.Letter)
    (hword : σ.word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right)
    (p : ℕ) (hp : p ∈ σ.childPositions)
    (hp0 : p ≠ left.length) (hp1 : p ≠ left.length + 1)
    (s : Ctx.Side) (c : ℕ)
    (hcomp : (σ.part (σ.childPositions.filter (fun r => r ≠ p)) s c).numRuns ≤ 1) :
    let ρ : Ctx.Context := { σ with word := left ++ [Ctx.Letter.child] ++ right }
    let q := if p ≤ left.length then p else p - 1
    (σ.part (σ.childPositions.filter (fun r => r ≠ p)) s c).bound =
      (ρ.part (ρ.childPositions.filter (fun r => r ≠ q)) s c).bound := by
  classical
  let ρ : Context := { σ with word := left ++ [Letter.child] ++ right }
  let q := if p ≤ left.length then p else p - 1
  let B := σ.part (σ.childPositions.filter (fun r => r ≠ p)) s c
  let D := ρ.part (ρ.childPositions.filter (fun r => r ≠ q)) s c
  change B.bound = D.bound
  let replace (r : ℕ) (t : Side) (i : ℕ) : Letter → Letter
    | .child => if i = r then .ext 1 t else .child
    | .ext N t' => .ext (N + 1) t'
  have hPartMap : ∀ (τ : Context) r t n,
      (τ.part (τ.childPositions.filter (fun i => i ≠ r)) t n).word =
        τ.word.mapIdx (replace r t) := by
    intro τ r t n
    apply List.ext_getElem (by simp [Context.part])
    intro i hi hj
    have hi' : i < τ.word.length := by simpa [Context.part] using hi
    have hm : i ∈ τ.childPositions ↔ τ.word[i] = Letter.child := by
      simp [childPositions, letterAt, hi', List.getElem?_eq_getElem hi']
    simp only [Context.part, List.getElem_map, List.getElem_range, List.getElem_mapIdx]
    have hletter : τ.letterAt i = τ.word[i] := by
      simp [letterAt, List.getElem?_eq_getElem hi']
    rw [hletter]
    cases hx : τ.word[i] with
    | child =>
        have hic : i ∈ τ.childPositions := hm.mpr hx
        simp [replace, hic, List.mem_filter, hx]
    | ext N t' => rfl
  have hLeftKeep : ∀ i, i < left.length → (i = p ↔ i = q) := by
    intro i hi
    dsimp only [q]
    split_ifs <;> omega
  have hRightKeep : ∀ i,
      (i + left.length + 2 = p ↔ i + left.length + 1 = q) := by
    intro i
    dsimp only [q]
    split_ifs <;> omega
  have hq0 : q ≠ left.length := by
    dsimp only [q]
    split_ifs <;> omega
  let L := left.mapIdx (replace p s)
  let R := right.mapIdx (fun i x ↦ replace p s (i + left.length + 2) x)
  have hL : left.mapIdx (replace q s) = L := by
    apply List.ext_getElem (by simp [L])
    intro i hi hj
    have hi' : i < left.length := by simpa using hi
    simp only [L, List.getElem_mapIdx]
    cases hx : left[i] with
    | child => simp [replace, (hLeftKeep i hi').symm]
    | ext N t => rfl
  have hR : right.mapIdx (fun i x ↦ replace q s (i + left.length + 1) x) = R := by
    apply List.ext_getElem (by simp [R])
    intro i hi hj
    have hi' : i < right.length := by simpa using hi
    simp only [R, List.getElem_mapIdx]
    cases hx : right[i] with
    | child => simp [replace, (hRightKeep i).symm]
    | ext N t => rfl
  have hBigWord : B.word = L ++ [Letter.child, Letter.child] ++ R := by
    dsimp only [B]
    rw [hPartMap, hword]
    simp [List.mapIdx_append, replace, L, R, Ne.symm hp0, Ne.symm hp1,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, List.append_assoc]
  have hSmallWord : D.word = L ++ [Letter.child] ++ R := by
    dsimp only [D]
    rw [hPartMap]
    change (left ++ [Letter.child] ++ right).mapIdx (replace q s) = _
    have hLeaf : replace q s left.length Letter.child = Letter.child := by
      simp [replace, Ne.symm hq0]
    have hR' : right.mapIdx (fun i x ↦ replace q s (i + (left.length + 1)) x) = R := by
      simpa only [Nat.add_assoc] using hR
    simp only [List.mapIdx_append, List.mapIdx_cons, List.mapIdx_nil,
      List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      Nat.zero_add, List.append_nil]
    rw [hLeaf, hL, hR']
  have hCtx : ({B with word := L ++ [Letter.child] ++ R} : Context) = D := by
    cases σ
    simp only [B, D, Context.part, ρ]
    congr 1
    exact hSmallWord.symm
  have hBase := ctx_base_child_letter_contraction B L R hBigWord
  have hRuns := ctx_num_runs_child_letter_contraction B L R hBigWord
  rw [hCtx] at hBase hRuns
  have hB : B.numRuns ≤ 1 := hcomp
  have hD : D.numRuns ≤ 1 := by omega
  simpa only [bound, boundFuel.eq_2, if_pos hB, if_pos hD] using hBase

end ErdosSzekeres
