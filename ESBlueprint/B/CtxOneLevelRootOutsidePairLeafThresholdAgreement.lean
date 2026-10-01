import ESBlueprint.B.CtxBoundExternalLetterContraction
import ESBlueprint.B.CtxSingletonPartBoundEqThreshold

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- For any well-formed context with an adjacent child pair, deleting the second copy preserves the explicit singleton leaf threshold at every child outside the pair, at the same side and coupling. The chosen position is mapped across deletion. No claim about its complement part or about choosing a rescuing cut.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_external_letter_contraction, ErdosSzekeres.ctx_singleton_part_bound_eq_threshold
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange -/
theorem ctx_one_level_root_outside_pair_leaf_threshold_agreement (σ : Ctx.Context) (hwf : σ.WellFormed)
    (left right : List Ctx.Letter)
    (hword : σ.word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right)
    (p : ℕ) (hp : p ∈ σ.childPositions)
    (hp0 : p ≠ left.length) (hp1 : p ≠ left.length + 1)
    (s : Ctx.Side) (c : ℕ) (hc : 1 ≤ c) (hck : c ≤ σ.k - 2) :
    let ρ : Ctx.Context := { σ with word := left ++ [Ctx.Letter.child] ++ right }
    let q := if p ≤ left.length then p else p - 1
    decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
        ((σ.part [p] s c).cupLimit p p + 1) σ.k =
      decomposableThreshold ((ρ.part [q] s c).capLimit q q + 1)
        ((ρ.part [q] s c).cupLimit q q + 1) σ.k := by
  classical
  let ρ : Context := { σ with word := left ++ [Letter.child] ++ right }
  let q := if p ≤ left.length then p else p - 1
  change decomposableThreshold ((σ.part [p] s c).capLimit p p + 1)
      ((σ.part [p] s c).cupLimit p p + 1) σ.k =
    decomposableThreshold ((ρ.part [q] s c).capLimit q q + 1)
      ((ρ.part [q] s c).cupLimit q q + 1) σ.k
  let replace (keep : List ℕ) (t : Side) (i : ℕ) : Letter → Letter
    | .child => if i ∈ keep then .child else .ext 1 t
    | .ext N t' => .ext (N + 1) t'
  have hPartMap : ∀ (τ : Context) keep t n,
      (τ.part keep t n).word = τ.word.mapIdx (replace keep t) := by
    intro τ keep t n
    apply List.ext_getElem (by simp [Context.part])
    intro i hi hj
    simp only [Context.part, List.getElem_map, List.getElem_range, List.getElem_mapIdx]
    have hi' : i < τ.word.length := by simpa [Context.part] using hi
    simp [Context.letterAt, List.getElem?_eq_getElem hi', replace]
    rfl
  have hLeftKeep : ∀ i, i < left.length → (i = p ↔ i = q) := by
    intro i hi
    dsimp only [q]
    split_ifs <;> omega
  have hRightKeep : ∀ i, (i + left.length + 2 = p ↔ i + left.length + 1 = q) := by
    intro i
    dsimp only [q]
    split_ifs <;> omega
  have hq0 : q ≠ left.length := by
    dsimp only [q]
    split_ifs <;> omega
  let L := left.mapIdx (replace [p] s)
  let R := right.mapIdx (fun i x ↦ replace [p] s (i + left.length + 2) x)
  have hL : left.mapIdx (replace [q] s) = L := by
    apply List.ext_getElem (by simp [L])
    intro i hi hj
    have hi' : i < left.length := by simpa using hi
    simp only [L, List.getElem_mapIdx]
    cases hx : left[i] with
    | child => simp [replace, (hLeftKeep i hi').symm]
    | ext N t => rfl
  have hR : right.mapIdx (fun i x ↦ replace [q] s (i + left.length + 1) x) = R := by
    apply List.ext_getElem (by simp [R])
    intro i hi hj
    have hi' : i < right.length := by simpa using hi
    simp only [R, List.getElem_mapIdx]
    cases hx : right[i] with
    | child => simp [replace, (hRightKeep i).symm]
    | ext N t => rfl
  have hBigWord : (σ.part [p] s c).word =
      L ++ [Letter.ext 1 s, Letter.ext 1 s] ++ R := by
    rw [hPartMap, hword]
    simp [List.mapIdx_append, replace, L, R, Ne.symm hp0, Ne.symm hp1, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc, List.append_assoc]
  have hSmallWord : (ρ.part [q] s c).word = L ++ [Letter.ext 1 s] ++ R := by
    rw [hPartMap]
    change (left ++ [Letter.child] ++ right).mapIdx (replace [q] s) = _
    have hLeaf : replace [q] s left.length Letter.child = Letter.ext 1 s := by
      simp [replace, Ne.symm hq0]
    have hR' : right.mapIdx (fun i x ↦ replace [q] s (i + (left.length + 1)) x) = R := by
      simpa only [Nat.add_assoc] using hR
    simp only [List.mapIdx_append, List.mapIdx_cons, List.mapIdx_nil,
      List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      Nat.zero_add, List.append_nil]
    rw [hLeaf, hL, hR']
  have hContract := ctx_bound_external_letter_contraction (σ.part [p] s c)
    (hwf.part [p] s hc hck) L R 1 s hBigWord
  have hCtx : ({σ.part [p] s c with word := L ++ [Letter.ext 1 s] ++ R} : Context) =
      ρ.part [q] s c := by
    cases σ
    simp only [Context.part, ρ]
    congr 1
    exact hSmallWord.symm
  rw [hCtx] at hContract
  have hpdata := List.mem_filter.mp hp
  have hplen : p < σ.word.length := List.mem_range.mp hpdata.1
  have hpchild : σ.letterAt p = Letter.child := of_decide_eq_true hpdata.2
  have hbw : σ.word = left ++ Letter.child :: Letter.child :: right := by
    simpa [List.append_assoc] using hword
  have hsw : ρ.word = left ++ Letter.child :: right := by
    simp [ρ, List.append_assoc]
  have hbiglen : σ.word.length = left.length + 2 + right.length := by
    simp [hword]
    omega
  have hsmalllen : ρ.word.length = left.length + 1 + right.length := by
    simp [hsw]
    omega
  have hq : q ∈ ρ.childPositions := by
    unfold childPositions
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_range.mpr
      dsimp only [q]
      split_ifs <;> omega
    · simp only [decide_eq_true_eq]
      by_cases hple : p ≤ left.length
      · have hplt : p < left.length := by omega
        dsimp only [q]
        rw [if_pos hple]
        simpa only [letterAt, hsw, hbw, List.getElem?_append_left hplt] using hpchild
      · dsimp only [q]
        rw [if_neg hple]
        have hpl : left.length ≤ p := by omega
        have hql : left.length ≤ p - 1 := by omega
        have hsub : p - left.length = (p - 1 - left.length) + 1 := by omega
        simp only [letterAt, hbw, List.getElem?_append_right hpl, hsub,
          List.getElem?_cons_succ] at hpchild
        simpa only [letterAt, hsw, List.getElem?_append_right hql] using hpchild
  rw [ctx_singleton_part_bound_eq_threshold σ p hp s c,
    ctx_singleton_part_bound_eq_threshold ρ q hq s c] at hContract
  exact hContract

end ErdosSzekeres
