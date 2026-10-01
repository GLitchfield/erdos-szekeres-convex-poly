import ESBlueprint.B.CtxBoundExtLetterDeletionMonoOfIsolatedChildren
import ESBlueprint.B.CtxSingletonPartBoundEqThreshold

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Deleting either member of an adjacent child pair weakly increases its singleton leaf threshold, provided another child remains outside the pair. The deleted copy becomes a repeated level-one external marker in the singleton part, whose bound is monotone under deletion with isolated children.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_ext_letter_deletion_mono_of_isolated_children, ErdosSzekeres.ctx_singleton_part_bound_eq_threshold
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange -/
theorem ctx_one_level_root_inside_pair_leaf_threshold_mono (σ : Ctx.Context) (hwf : σ.WellFormed)
    (left right : List Ctx.Letter)
    (hword : σ.word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right)
    (p : ℕ) (hpmem : p ∈ σ.childPositions)
    (hp : p = left.length ∨ p = left.length + 1)
    (hother : Ctx.Letter.child ∈ left ++ right)
    (s : Ctx.Side) (c : ℕ) (hc : 1 ≤ c) (hck : c ≤ σ.k - 2) :
    let ρ : Ctx.Context := { σ with word := left ++ [Ctx.Letter.child] ++ right }
    let q := left.length
    decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
        ((σ.part [p] s c).cupLimit p p + 1) σ.k ≤
      decomposableThreshold ((ρ.part [q] s c).capLimit q q + 1)
        ((ρ.part [q] s c).cupLimit q q + 1) σ.k := by
  classical
  let ρ : Context := { σ with word := left ++ [Letter.child] ++ right }
  let q := left.length
  change decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
      ((σ.part [p] s c).cupLimit p p + 1) σ.k ≤
    decomposableThreshold ((ρ.part [q] s c).capLimit q q + 1)
      ((ρ.part [q] s c).cupLimit q q + 1) σ.k
  let replace (keep : List ℕ) (t : Side) (i : ℕ) : Letter → Letter
    | .child => if i ∈ keep then .child else .ext 1 t
    | .ext N t' => .ext (N + 1) t'
  let shift : Letter → Letter
    | .child => .ext 1 s
    | .ext N t => .ext (N + 1) t
  have hPartMap : ∀ (τ : Context) keep t n,
      (τ.part keep t n).word = τ.word.mapIdx (replace keep t) := by
    intro τ keep t n
    apply List.ext_getElem (by simp [Context.part])
    intro i hi hj
    simp only [Context.part, List.getElem_map, List.getElem_range, List.getElem_mapIdx]
    have hi' : i < τ.word.length := by simpa [Context.part] using hi
    simp [Context.letterAt, List.getElem?_eq_getElem hi', replace]
    rfl
  have hSkip : ∀ (W : List Letter) (off r : ℕ),
      (∀ i, i < W.length → i + off ≠ r) →
      W.mapIdx (fun i x ↦ replace [r] s (i + off) x) = W.map shift := by
    intro W off r h
    apply List.ext_getElem (by simp)
    intro i hi hj
    have hi' : i < W.length := by simpa using hi
    simp only [List.getElem_mapIdx, List.getElem_map]
    cases hx : W[i] with
    | child => simp [replace, shift, h i hi']
    | ext N t => rfl
  let L := left.map shift
  let R := right.map shift
  have hL : left.mapIdx (replace [p] s) = L := by
    simpa using hSkip left 0 p (by intro i hi; rcases hp with h | h <;> omega)
  have hR : right.mapIdx (fun i x ↦ replace [p] s (i + (left.length + 2)) x) = R := by
    exact hSkip right (left.length + 2) p
      (by intro i hi; rcases hp with h | h <;> omega)
  have hLq : left.mapIdx (replace [q] s) = L := by
    simpa using hSkip left 0 q (by intro i hi; dsimp only [q]; omega)
  have hRq : right.mapIdx (fun i x ↦ replace [q] s (i + (left.length + 1)) x) = R := by
    exact hSkip right (left.length + 1) q (by intro i hi; dsimp only [q]; omega)
  have hBigWord : (σ.part [p] s c).word =
      L ++ [replace [p] s left.length Letter.child,
        replace [p] s (left.length + 1) Letter.child] ++ R := by
    rw [hPartMap, hword]
    simp only [List.mapIdx_append, List.mapIdx_cons, List.mapIdx_nil,
      List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      Nat.zero_add, List.append_nil]
    rw [hL, hR]
    simp only [Nat.add_comm]
  have hSmallWord : (ρ.part [q] s c).word = L ++ [Letter.child] ++ R := by
    rw [hPartMap]
    change (left ++ [Letter.child] ++ right).mapIdx (replace [q] s) = _
    simp only [List.mapIdx_append, List.mapIdx_cons, List.mapIdx_nil,
      List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      Nat.zero_add, List.append_nil]
    rw [hLq, hRq]
    simp [replace, q]
  have hKept : ∀ r ∈ (σ.part [p] s c).childPositions, r = p := by
    intro r hr
    rw [part_childPositions] at hr
    simpa using of_decide_eq_true (List.mem_filter.mp hr).2
  have hIso : ∀ r ∈ (σ.part [p] s c).childPositions,
      r + 1 ∉ (σ.part [p] s c).childPositions := by
    intro r hr hnext
    have h1 := hKept r hr
    have h2 := hKept (r + 1) hnext
    omega
  have hOther : Letter.ext 1 s ∈ L ++ R := by
    have h := List.mem_map_of_mem (f := shift) hother
    simpa [List.map_append, shift, L, R] using h
  have hContract : (σ.part [p] s c).bound ≤ (ρ.part [q] s c).bound := by
    have hCtx : ({σ.part [p] s c with word := L ++ [Letter.child] ++ R} : Context) =
        ρ.part [q] s c := by
      cases σ
      simp only [Context.part, ρ]
      congr 1
      exact hSmallWord.symm
    rcases hp with h | h
    · have hBig : (σ.part [p] s c).word = L ++ [Letter.child, Letter.ext 1 s] ++ R := by
        simpa [replace, h] using hBigWord
      have hDelete := ctx_bound_ext_letter_deletion_mono_of_isolated_children
        (σ.part [p] s c) (hwf.part [p] s hc hck) hIso (L ++ [Letter.child]) R 1 s
        (by simpa [List.append_assoc] using hBig)
        (by simpa [List.append_assoc] using hOther)
      have hDelete' : (σ.part [p] s c).bound ≤
          ({σ.part [p] s c with word := L ++ [Letter.child] ++ R} : Context).bound := by
        simpa only [List.append_assoc, List.singleton_append] using hDelete
      rw [hCtx] at hDelete'
      exact hDelete'
    · have hBig : (σ.part [p] s c).word = L ++ [Letter.ext 1 s, Letter.child] ++ R := by
        simpa [replace, h] using hBigWord
      have hDelete := ctx_bound_ext_letter_deletion_mono_of_isolated_children
        (σ.part [p] s c) (hwf.part [p] s hc hck) hIso L ([Letter.child] ++ R) 1 s
        (by simpa [List.append_assoc] using hBig)
        (by simpa [List.append_assoc] using hOther)
      have hDelete' : (σ.part [p] s c).bound ≤
          ({σ.part [p] s c with word := L ++ [Letter.child] ++ R} : Context).bound := by
        simpa only [List.append_assoc, List.singleton_append] using hDelete
      rw [hCtx] at hDelete'
      exact hDelete'
  have hq : q ∈ ρ.childPositions := by
    simp [childPositions, letterAt, ρ, q, List.append_assoc,
      List.getElem?_append_right]
  rw [ctx_singleton_part_bound_eq_threshold σ p hpmem s c,
    ctx_singleton_part_bound_eq_threshold ρ q hq s c] at hContract
  exact hContract

end ErdosSzekeres
