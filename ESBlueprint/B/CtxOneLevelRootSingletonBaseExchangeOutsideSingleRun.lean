import ESBlueprint.B.CtxBoundExternalLetterContraction
import ESBlueprint.B.CtxSingletonPartBoundEqThreshold
import ESBlueprint.B.CtxBaseChildLetterContraction
import ESBlueprint.B.CtxNumRunsChildLetterContraction

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Full localized singleton-base and complement exchange X for positive-axis one-level roots at a singleton outside the doubled pair when its source complement has at most one run. The original legal side and coupling preserve both terms exactly, by outside leaf agreement and raw one-run complement contraction. This leaves the positive-axis multirun complement residual.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_external_letter_contraction, ErdosSzekeres.ctx_singleton_part_bound_eq_threshold, ErdosSzekeres.ctx_base_child_letter_contraction, ErdosSzekeres.ctx_num_runs_child_letter_contraction
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange
@falsifier ctx_one_level_root_singleton_base_exchange_residuals.py -/
theorem ctx_one_level_root_singleton_base_exchange_outside_single_run (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2) (ha2 : 2 ≤ a) (hu2 : 2 ≤ u) (side : Ctx.Side) (left right : List Ctx.Letter) (hletters : ∀ x ∈ left ++ right, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) :
  let σ : Ctx.Context := { a := a, u := u, k := k, word := left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right, maxima := [m] }
  let ρ : Ctx.Context := { a := a, u := u, k := k, word := left ++ [Ctx.Letter.child] ++ right, maxima := [m] }
  let opposite : Ctx.Side → Ctx.Side := fun s => match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower
  2 ≤ σ.numRuns →
  ∀ p ∈ σ.childPositions, ∀ (s : Ctx.Side) (c : ℕ), 1 ≤ c → c ≤ k - 2 →
    p ≠ left.length → p ≠ left.length + 1 →
    (σ.part (σ.childPositions.filter (fun r => r ≠ p))
      (opposite s) (k - 1 - c)).numRuns ≤ 1 →
    let q := if p ≤ left.length then p else p - 1
    ∃ (t : Ctx.Side) (d : ℕ), 1 ≤ d ∧ d ≤ k - 2 ∧
      decomposableThreshold ((σ.part [p] s c).capLimit p p + 1) ((σ.part [p] s c).cupLimit p p + 1) k +
          (σ.part (σ.childPositions.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)).bound ≤
      decomposableThreshold ((ρ.part [q] t d).capLimit q q + 1) ((ρ.part [q] t d).cupLimit q q + 1) k +
          (ρ.part (ρ.childPositions.filter (fun r => r ≠ q)) (opposite t) (k - 1 - d)).bound := by
  classical
  dsimp only
  intro hruns p hp s c hc hck hp0 hp1 hcomp
  let σ : Context :=
    ⟨a, u, k, left ++ [Letter.child, Letter.child] ++ right, [m]⟩
  let ρ : Context := {σ with word := left ++ [Letter.child] ++ right}
  let opposite : Side → Side := fun t => match t with
    | .lower => .upper
    | .upper => .lower
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
  have hLeafEq (σ : Ctx.Context) (hwf : σ.WellFormed)
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
  have hRestEq (σ : Ctx.Context) (left right : List Ctx.Letter)
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
  refine ⟨s, c, hc, hck, ?_⟩
  have hLeaf := hLeafEq σ hwf left right rfl p hp hp0 hp1 s c hc hck
  have hRest := hRestEq σ left right rfl p hp hp0 hp1
    (opposite s) (k - 1 - c) hcomp
  exact (congrArg₂ Nat.add hLeaf hRest).le

end ErdosSzekeres
