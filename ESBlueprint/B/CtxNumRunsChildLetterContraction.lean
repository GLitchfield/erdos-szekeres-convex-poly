import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Deleting one of two adjacent child letters preserves the number of child runs in any raw context. No well-formedness or parameter hypothesis is needed. Exposes the geometric position-map component of the closed child-letter expansion proof, so contraction reductions can transport both the single-run base branch and the multi-run cut hypothesis.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_num_runs_child_letter_contraction (σ : Ctx.Context) (left right : List Ctx.Letter) (hword : σ.word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right) : σ.numRuns = ({ σ with word := left ++ [Ctx.Letter.child] ++ right } : Ctx.Context).numRuns := by
  classical
  let up (p i : ℕ) := if i < p then i else i + 1
  let down (p i : ℕ) := if i ≤ p then i else i + 1
  let expand (p i : ℕ) := if i = p then [i, i + 1] else [up p i]
  have hdown : ∀ p, StrictMono (down p) := by
    intro p i j hij
    dsimp [down]
    split_ifs <;> omega
  have hsame : ∀ p i, i ≠ p → down p i = up p i := by
    intro p i hi
    dsimp [down, up]
    split_ifs <;> omega
  have hRange : ∀ n p, p < n →
      (List.range n).flatMap (expand p) = List.range (n + 1) := by
    intro n
    induction n with
    | zero => intro p hp; omega
    | succ n ih =>
      intro p hp
      by_cases hpn : p = n
      · subst p
        have hpre : (List.range n).flatMap (expand n) = List.range n := by
          calc
            _ = (List.range n).flatMap (fun i ↦ [i]) := by
              apply List.flatMap_congr
              intro i hi
              have hin := List.mem_range.mp hi
              simp [expand, up, hin, Nat.ne_of_lt hin]
            _ = _ := List.flatMap_singleton' _
        simp only [Nat.succ_eq_add_one, List.range_succ, List.flatMap_append,
          List.flatMap_singleton]
        rw [hpre]
        simp [expand, List.append_assoc]
      · have hpn' : p < n := by omega
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih p hpn']
        have hnp : n ≠ p := by omega
        have hnp' : ¬ n < p := by omega
        simp [expand, up, hnp, hnp', List.range_succ]
  have hDownMem : ∀ p i, down p i ∈ expand p i := by
    intro p i
    by_cases hip : i = p
    · simp [expand, down, hip]
    · simp [expand, hip, hsame p i hip]
  have hGeometry : ∀ (big small : Context) p,
      big.word.length = small.word.length + 1 → p < small.word.length →
      small.letterAt p = Letter.child → big.letterAt p = Letter.child →
      (∀ i, i < small.word.length → big.letterAt (up p i) = small.letterAt i) →
      big.numRuns = small.numRuns := by
    intro big small p hlen hp hsp hbp hletter
    have hexpand : ∀ i, i < small.word.length → ∀ j ∈ expand p i,
        big.letterAt j = small.letterAt i := by
      intro i hi j hj
      by_cases hip : i = p
      · subst i
        simp only [expand, if_pos rfl, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hbp.trans hsp.symm
        · simpa [up] using hletter p hp
      · simp only [expand, if_neg hip, List.mem_singleton] at hj
        subst j
        exact hletter i hi
    let pred (c : Context) (i : ℕ) := decide
      (c.letterAt i = Letter.child ∧ (i = 0 ∨ c.letterAt (i - 1) ≠ Letter.child))
    have hfirst : ∀ i, i < small.word.length → pred big (down p i) = pred small i := by
      intro i hi
      have hlet := hexpand i hi (down p i) (hDownMem p i)
      by_cases hi0 : i = 0
      · subst i
        have hd0 : down p 0 = 0 := by simp [down]
        simp [pred, hd0] at hlet ⊢
        exact congrArg (fun x ↦ x = Letter.child) hlet |>.to_iff
      · have hprev : up p (i - 1) = down p i - 1 := by
          dsimp [up, down]; split_ifs <;> omega
        have hd0 : down p i ≠ 0 := Nat.ne_of_gt
          (lt_of_le_of_lt (Nat.zero_le _) (hdown p (Nat.pos_of_ne_zero hi0)))
        simp only [pred, hlet, hd0, hi0, false_or]
        rw [← hprev, hletter (i - 1) (by omega)]
    have hsecond : pred big (p + 1) = false := by
      have hpred : (p + 1) - 1 = p := by omega
      simp [pred, hpred, hbp]
    have hchunk : ∀ i ∈ List.range small.word.length,
        (expand p i).filter (pred big) = if pred small i then [down p i] else [] := by
      intro i hi
      have hh := hfirst i (List.mem_range.mp hi)
      by_cases hip : i = p
      · subst i
        simp only [down, Nat.le_refl, if_true] at hh
        simp only [expand, if_pos rfl, List.filter_cons, List.filter_nil, hsecond,
          Bool.false_eq_true, if_false, hh, down, Nat.le_refl, if_true]
      · have he := hsame p i hip
        simp only [expand, if_neg hip, List.filter_cons, List.filter_nil, ← he, hh]
    have hfiltered : ((List.range small.word.length).flatMap (expand p)).filter (pred big) =
        ((List.range small.word.length).filter (pred small)).map (down p) := by
      rw [List.filter_flatMap]
      have hlist : ∀ A : List ℕ,
          (∀ i ∈ A, (expand p i).filter (pred big) = if pred small i then [down p i] else []) →
          A.flatMap (fun i ↦ (expand p i).filter (pred big)) =
            (A.filter (pred small)).map (down p) := by
        intro A
        induction A with
        | nil => intro _; rfl
        | cons i A ih =>
          intro h
          rw [List.flatMap_cons, h i (List.mem_cons_self ..),
            ih (fun j hj ↦ h j (List.mem_cons_of_mem _ hj))]
          cases he : pred small i <;> simp [he]
      exact hlist _ hchunk
    change ((List.range big.word.length).filter (pred big)).length =
      ((List.range small.word.length).filter (pred small)).length
    rw [hlen, ← hRange _ p hp, hfiltered, List.length_map]
  let small : Context := { σ with word := left ++ [Letter.child] ++ right }
  let p := left.length
  have hsw : small.word = left ++ Letter.child :: right := by
    simp [small, List.append_assoc]
  have hbw : σ.word = left ++ Letter.child :: Letter.child :: right := by
    simpa [List.append_assoc] using hword
  have hp : p < small.word.length := by simp [p, hsw]
  have hlen : σ.word.length = small.word.length + 1 := by simp [hsw, hbw]; omega
  have hsp : small.letterAt p = Letter.child := by
    unfold Context.letterAt
    rw [hsw, List.getElem?_append_right (show left.length ≤ p by rfl)]
    simp [p]
  have hbp : σ.letterAt p = Letter.child := by
    unfold Context.letterAt
    rw [hbw, List.getElem?_append_right (show left.length ≤ p by rfl)]
    simp [p]
  have hletter : ∀ i, i < small.word.length → σ.letterAt (up p i) = small.letterAt i := by
    intro i hi
    by_cases hip : i < p
    · have hil : i < left.length := hip
      simp only [up, if_pos hip, Context.letterAt, hsw, hbw,
        List.getElem?_append_left hil]
    · have hpi : left.length ≤ i := Nat.le_of_not_gt hip
      have hpi' : left.length ≤ i + 1 := by omega
      have hsub : i + 1 - left.length = (i - left.length) + 1 := by omega
      simp only [up, if_neg hip, Context.letterAt, hsw, hbw,
        List.getElem?_append_right hpi', List.getElem?_append_right hpi,
        hsub, List.getElem?_cons_succ]
  exact hGeometry σ small p hlen hp hsp hbp hletter


end ErdosSzekeres
