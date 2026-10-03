import ESBlueprint.B.CtxBoundLeMergeSameSideLevels
import ESBlueprint.B.CtxBoundOppositeLevelSwap

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Swapping two physically present opposite-flank levels preserves the full context bound, with either flank orientation and arbitrary older letters. Different sides preserve each physical level maximum. Same sides use M=max(m1,1+m2) and new maxima M,M-1, in the legal range. Flank steps commute on descendants because every younger marker stays between them.
@node
@ws B
@kind formalization
@dangling-ok R19 exact rotation tool for all-context singleton attainment PEEL; handles the opposite-flank part of cost-based rotations -/
theorem ctx_bound_eq_flank_swap (σ : Ctx.Context) (hwf : σ.WellFormed) (hlevels : 2 ≤ σ.maxima.length)
(hfirst : σ.extPositions 1 ≠ []) (hsecond : σ.extPositions 2 ≠ [])
(hflanks :
  ((∀ p ∈ σ.extPositions 1, ∀ q ∈ σ.childPositions, p < q) ∧
   (∀ p ∈ σ.extPositions 2, ∀ q ∈ σ.childPositions, q < p)) ∨
  ((∀ p ∈ σ.extPositions 2, ∀ q ∈ σ.childPositions, p < q) ∧
   (∀ p ∈ σ.extPositions 1, ∀ q ∈ σ.childPositions, q < p)))
(hlegal : σ.sideAt 1 = σ.sideAt 2 →
  1 ≤ max (σ.maximumAt 1) (1 + σ.maximumAt 2) - 1 ∧
  max (σ.maximumAt 1) (1 + σ.maximumAt 2) ≤ σ.k - 2) :
let M := max (σ.maximumAt 1) (1 + σ.maximumAt 2)
σ.bound = ({ σ with
  word := σ.word.map (fun x ↦ match x with
    | Ctx.Letter.child => Ctx.Letter.child
    | Ctx.Letter.ext j s => Ctx.Letter.ext (if j = 1 then 2 else if j = 2 then 1 else j) s)
  maxima := (σ.maxima.set 0 (if σ.sideAt 1 = σ.sideAt 2 then M else σ.maximumAt 2)).set 1
    (if σ.sideAt 1 = σ.sideAt 2 then M - 1 else σ.maximumAt 1) } : Ctx.Context).bound := by
  classical
  dsimp only
  by_cases hsame : σ.sideAt 1 = σ.sideAt 2
  · simp only [if_pos hsame]
    let perm (L j : ℕ) := if j = L then L + 1 else if j = L + 1 then L else j
    let tag (L : ℕ) : Letter → Letter := fun x ↦ match x with
      | .child => .child
      | .ext j s => .ext (perm L j) s
    let M (ρ : Context) (L : ℕ) := max (ρ.maximumAt L) (1 + ρ.maximumAt (L + 1))
    let norm (ρ : Context) (L : ℕ) : Context :=
      { ρ with
        word := ρ.word.map (tag L)
        maxima := (ρ.maxima.set (L - 1) (M ρ L)).set L (M ρ L - 1) }
    let safe (ρ : Context) (L e : ℕ) : Prop :=
      ((∀ x ∈ ρ.extPositions L, x < e) ∧ (∀ x ∈ ρ.extPositions (L + 1), e < x)) ∨
      ((∀ x ∈ ρ.extPositions (L + 1), x < e) ∧ (∀ x ∈ ρ.extPositions L, e < x))
    let Inv (ρ : Context) (L : ℕ) : Prop :=
      1 ≤ L ∧ L + 1 ≤ ρ.maxima.length ∧
      (∀ p j s, ρ.letterAt p = .ext j s → 1 ≤ j) ∧
      ρ.sideAt L = ρ.sideAt (L + 1) ∧
      (ρ.extPositions L ≠ [] ∧ ρ.extPositions (L + 1) ≠ []) ∧
      (∀ e ∈ ρ.childPositions, safe ρ L e) ∧
      (∀ j, 1 ≤ j → j < L → ∀ e ∈ ρ.extPositions j, safe ρ L e)
    change σ.bound = (norm σ 1).bound
    have hPermInv (L j : ℕ) : perm L (perm L j) = j := by
      dsimp [perm]
      split_ifs <;> omega
    have hPermInj (L : ℕ) : Function.Injective (perm L) := by
      intro i j h
      simpa only [hPermInv] using congrArg (perm L) h
    have hShift (L j : ℕ) : perm (L + 1) (j + 1) = perm L j + 1 := by
      dsimp [perm]
      split_ifs <;> omega
    have hLen (ρ : Context) (L : ℕ) : (norm ρ L).word.length = ρ.word.length := by
      simp only [norm, List.length_map]
    have hDepth (ρ : Context) (L : ℕ) :
        (norm ρ L).maxima.length = ρ.maxima.length := by
      simp [norm]
    have hLetter (ρ : Context) (L p : ℕ) :
        (norm ρ L).letterAt p = tag L (ρ.letterAt p) := by
      simp only [norm, letterAt, List.getElem?_map]
      cases ρ.word[p]? <;> rfl
    have hGeometry (ρ : Context) (L : ℕ) :
        (norm ρ L).childPositions = ρ.childPositions ∧
        (norm ρ L).numRuns = ρ.numRuns ∧
        (∀ j, (norm ρ L).extPositions (perm L j) = ρ.extPositions j) ∧
        (∀ j, (norm ρ L).sideAt (perm L j) = ρ.sideAt j) := by
      have hc (p : ℕ) : (norm ρ L).letterAt p = .child ↔ ρ.letterAt p = .child := by
        rw [hLetter]
        cases ρ.letterAt p <;> simp [tag]
      have he (j : ℕ) : (norm ρ L).extPositions (perm L j) = ρ.extPositions j := by
        unfold extPositions
        rw [hLen]
        apply List.filter_congr
        intro p hp
        rw [hLetter]
        cases h : ρ.letterAt p with
        | child => rfl
        | ext i s => simp [tag, (hPermInj L).eq_iff]
      refine ⟨?_, ?_, he, ?_⟩
      · simp only [childPositions, hLen, hc]
      · simp only [numRuns, hLen, ne_eq, hc]
      · intro j
        unfold sideAt
        rw [he]
        cases hh : (ρ.extPositions j).head? with
        | none => rfl
        | some p =>
          simp only
          rw [hLetter]
          cases ρ.letterAt p <;> rfl
    have hExt (ρ : Context) (L j : ℕ) :
        (norm ρ L).extPositions j = ρ.extPositions (perm L j) := by
      simpa only [hPermInv] using (hGeometry ρ L).2.2.1 (perm L j)
    have hSide (ρ : Context) (L j : ℕ) :
        (norm ρ L).sideAt j = ρ.sideAt (perm L j) := by
      simpa only [hPermInv] using (hGeometry ρ L).2.2.2 (perm L j)
    have hMax (ρ : Context) (L : ℕ) (hL : 1 ≤ L) (hD : L + 1 ≤ ρ.maxima.length)
        (j : ℕ) (hj : 1 ≤ j) :
        (norm ρ L).maximumAt j =
          if j = L then M ρ L else if j = L + 1 then M ρ L - 1 else ρ.maximumAt j := by
      by_cases h₁ : j = L
      · subst j
        simp only [norm, maximumAt]
        rw [List.getElem?_set_ne (show L ≠ L - 1 by omega),
          List.getElem?_set_self (by omega)]
        simp
      by_cases h₂ : j = L + 1
      · subst j
        simp only [norm, maximumAt]
        rw [show L + 1 - 1 = L by omega, List.getElem?_set_self (by simp; omega)]
        simp
      simp only [norm, maximumAt]
      rw [List.getElem?_set_ne (show L ≠ j - 1 by omega),
        List.getElem?_set_ne (show L - 1 ≠ j - 1 by omega)]
      simp [h₁, h₂]
    have hSafeNorm (ρ : Context) (L e : ℕ) : safe (norm ρ L) L e ↔ safe ρ L e := by
      simp only [safe, hExt, perm]
      simp [or_comm]
    have hNormPart (ρ : Context) (L : ℕ) (hL : 1 ≤ L)
        (keep : List ℕ) (s : Side) (m : ℕ) :
        norm (ρ.part keep s m) (L + 1) = (norm ρ L).part keep s m := by
      have hm : M (ρ.part keep s m) (L + 1) = M ρ L := by
        simp only [M, part_maximumAt_succ ρ keep s m hL,
          part_maximumAt_succ ρ keep s m (show 1 ≤ L + 1 by omega)]
      refine MergeLevels.ctx_ext (σ := norm (ρ.part keep s m) (L + 1))
        (τ := (norm ρ L).part keep s m) rfl rfl rfl ?_ ?_
      · change (ρ.part keep s m).word.map (tag (L + 1)) = _
        simp only [part, List.map_map, Function.comp_def, hLen]
        apply List.map_congr_left
        intro p hp
        rw [hLetter]
        cases h : ρ.letterAt p with
        | child =>
          by_cases hk : p ∈ keep <;>
            simp [hk, tag, perm, show L ≠ 0 by omega]
        | ext j v => simp [tag, hShift]
      · change ((m :: ρ.maxima).set (L + 1 - 1) (M (ρ.part keep s m) (L + 1))).set
            (L + 1) (M (ρ.part keep s m) (L + 1) - 1) =
          m :: ((ρ.maxima.set (L - 1) (M ρ L)).set L (M ρ L - 1))
        rw [hm, show L + 1 - 1 = (L - 1) + 1 by omega]
        simp only [List.set_cons_succ]
    have hPositivePart (ρ : Context) (keep : List ℕ) (s : Side) (m : ℕ) :
        ∀ p j v, (ρ.part keep s m).letterAt p = .ext j v → 1 ≤ j := by
      intro p j v hp
      by_cases hplen : p < ρ.word.length
      · cases h : ρ.letterAt p with
        | child =>
          rw [part_letterAt_of_child ρ keep s m hplen h] at hp
          by_cases hk : p ∈ keep
          · simp [hk] at hp
          · simp only [hk, if_false, Letter.ext.injEq] at hp
            omega
        | ext i w =>
          rw [part_letterAt_of_ext ρ keep s m hplen h, Letter.ext.injEq] at hp
          omega
      · rw [letterAt_of_length_le _ (by rw [part_word_length]; omega)] at hp
        cases hp
    have hPartChildren (ρ : Context) (keep : List ℕ) (s : Side) (m e : ℕ)
        (he : e ∈ (ρ.part keep s m).childPositions) : e ∈ ρ.childPositions := by
      simp only [childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq,
        part_word_length] at he ⊢
      refine ⟨he.1, ?_⟩
      cases h : ρ.letterAt e with
      | child => rfl
      | ext j v =>
        rw [part_letterAt_of_ext ρ keep s m he.1 h] at he
        cases he.2
    have hInvPart (ρ : Context) (L : ℕ) (hI : Inv ρ L)
        (keep : List ℕ) (s : Side) (m : ℕ) : Inv (ρ.part keep s m) (L + 1) := by
      obtain ⟨hL, hD, hLet, hSides, hNon, hChild, hYoung⟩ := hI
      have hSafePart (e : ℕ) : safe (ρ.part keep s m) (L + 1) e ↔ safe ρ L e := by
        dsimp only [safe]
        rw [part_extPositions_succ ρ keep s m hL,
          part_extPositions_succ ρ keep s m (show 1 ≤ L + 1 by omega)]
      refine ⟨by omega, by simp only [part_maxima, List.length_cons]; omega,
        hPositivePart ρ keep s m, ?_, ?_, ?_, ?_⟩
      · rw [part_sideAt_succ ρ keep s m hL,
          part_sideAt_succ ρ keep s m (show 1 ≤ L + 1 by omega)]
        exact hSides
      · rw [part_extPositions_succ ρ keep s m hL,
          part_extPositions_succ ρ keep s m (show 1 ≤ L + 1 by omega)]
        exact hNon
      · intro e he
        exact (hSafePart e).mpr (hChild e (hPartChildren ρ keep s m e he))
      · intro j hj hjL e he
        apply (hSafePart e).mpr
        by_cases hj1 : j = 1
        · subst j
          rw [part_extPositions_one hLet] at he
          exact hChild e (List.mem_filter.mp he).1
        · have heq : j = (j - 1) + 1 := by omega
          rw [heq, part_extPositions_succ ρ keep s m (show 1 ≤ j - 1 by omega)] at he
          exact hYoung (j - 1) (by omega) (by omega) e he
    let before (d : Bool) (x y : ℕ) : Prop := if d then x < y else y < x
    let step (d : Bool) (ρ : Context) (st : ℕ × ℕ) (j : ℕ) :=
      if d then leftStep ρ st j else rightStep ρ st j
    have hBeforeTrans (d : Bool) {x y z : ℕ} :
        before d x y → before d y z → before d x z := by
      cases d <;> simp only [before, Bool.false_eq_true, if_false, if_true] <;> omega
    have hBeforeAsymm (d : Bool) {x y : ℕ} : before d x y → ¬ before d y x := by
      cases d <;> simp only [before, Bool.false_eq_true, if_false, if_true] <;> omega
    have hStepCases (d : Bool) (ρ : Context) (st : ℕ × ℕ) (j : ℕ) :
        step d ρ st j = st ∨
          ∃ x ∈ ρ.extPositions j, before d x st.1 ∧ step d ρ st j = (x, st.2 + 1) := by
      cases d with
      | false =>
        change rightStep ρ st j = st ∨ _
        cases hx : ((ρ.extPositions j).filter (st.1 < ·)).head? with
        | none => exact Or.inl (by simp [rightStep, hx])
        | some x =>
          have hm := List.mem_filter.mp (List.mem_of_head? hx)
          exact Or.inr ⟨x, hm.1, by simpa [before] using hm.2,
            by simp only [step, Bool.false_eq_true, if_false, rightStep, hx]⟩
      | true =>
        change leftStep ρ st j = st ∨ _
        cases hx : ((ρ.extPositions j).filter (· < st.1)).getLast? with
        | none => exact Or.inl (by simp [leftStep, hx])
        | some x =>
          have hm := List.mem_filter.mp (List.mem_of_getLast? hx)
          exact Or.inr ⟨x, hm.1, by simpa [before] using hm.2,
            by simp only [step, if_true, leftStep, hx]⟩
    have hStepNone (d : Bool) (ρ : Context) (st : ℕ × ℕ) (j : ℕ)
        (h : ∀ x ∈ ρ.extPositions j, ¬ before d x st.1) : step d ρ st j = st := by
      cases d with
      | false =>
        have hn : (ρ.extPositions j).filter (st.1 < ·) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro x hx
          simpa [before] using h x hx
        simp only [step, Bool.false_eq_true, if_false, rightStep, hn, List.head?_nil]
      | true =>
        have hn : (ρ.extPositions j).filter (· < st.1) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro x hx
          simpa [before] using h x hx
        simp only [step, if_true, leftStep, hn, List.getLast?_nil]
    have hStepMap (d : Bool) (ρ : Context) (L : ℕ) (st : ℕ × ℕ) (j : ℕ) :
        step d (norm ρ L) st (perm L j) = step d ρ st j := by
      simp only [step, leftStep, rightStep, (hGeometry ρ L).2.2.1]
    have hStepNe (d : Bool) (ρ : Context) (L : ℕ) (st : ℕ × ℕ) (j : ℕ)
        (hj : j ≠ L) (hj' : j ≠ L + 1) : step d (norm ρ L) st j = step d ρ st j := by
      simpa only [perm, if_neg hj, if_neg hj'] using hStepMap d ρ L st j
    have hSafeDir (d : Bool) (ρ : Context) (L e : ℕ) (h : safe ρ L e) :
        ((∀ x ∈ ρ.extPositions L, before d x e) ∧
          (∀ x ∈ ρ.extPositions (L + 1), before d e x)) ∨
        ((∀ x ∈ ρ.extPositions (L + 1), before d x e) ∧
          (∀ x ∈ ρ.extPositions L, before d e x)) := by
      cases d <;> simpa [safe, before, and_comm, or_comm] using h
    have hCommute (d : Bool) (ρ : Context) (L : ℕ) (st : ℕ × ℕ)
        (hs : safe ρ L st.1) :
        step d ρ (step d ρ st L) (L + 1) = step d ρ (step d ρ st (L + 1)) L := by
      have hAB (A B : ℕ) (hA : ∀ x ∈ ρ.extPositions A, before d x st.1)
          (hB : ∀ x ∈ ρ.extPositions B, before d st.1 x) :
          step d ρ (step d ρ st A) B = step d ρ (step d ρ st B) A := by
        have hB₀ : step d ρ st B = st := hStepNone d ρ st B
          (fun x hx ↦ hBeforeAsymm d (hB x hx))
        have hB₁ : step d ρ (step d ρ st A) B = step d ρ st A := by
          rcases hStepCases d ρ st A with hn | ⟨x, hx, hxe, heq⟩
          · rw [hn]; exact hB₀
          · rw [heq]
            apply hStepNone
            intro y hy
            exact hBeforeAsymm d (hBeforeTrans d hxe (hB y hy))
        rw [hB₀, hB₁]
      rcases hSafeDir d ρ L st.1 hs with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · exact hAB L (L + 1) hA hB
      · exact (hAB (L + 1) L hA hB).symm
    have hStepSafe (d : Bool) (ρ : Context) (L : ℕ) (hI : Inv ρ L)
        (st : ℕ × ℕ) (hs : safe ρ L st.1) (j : ℕ) (hj : 1 ≤ j) (hjL : j < L) :
        safe ρ L (step d ρ st j).1 := by
      rcases hStepCases d ρ st j with hn | ⟨x, hx, -, heq⟩
      · simpa only [hn] using hs
      · rw [heq]
        exact hI.2.2.2.2.2.2 j hj hjL x hx
    have hFoldMap (d : Bool) (ρ : Context) (L : ℕ) (ls : List ℕ) (st : ℕ × ℕ) :
        (ls.map (perm L)).foldl (step d (norm ρ L)) st = ls.foldl (step d ρ) st := by
      induction ls generalizing st with
      | nil => rfl
      | cons j js ih => simp only [List.map_cons, List.foldl_cons, hStepMap, ih]
    have hFoldNe (d : Bool) (ρ : Context) (L : ℕ) (ls : List ℕ)
        (hls : ∀ j ∈ ls, j ≠ L ∧ j ≠ L + 1) (st : ℕ × ℕ) :
        ls.foldl (step d (norm ρ L)) st = ls.foldl (step d ρ) st := by
      have hm : ls.map (perm L) = ls := by
        calc
          ls.map (perm L) = ls.map id := by
            apply List.map_congr_left
            intro j hj
            simp only [perm, if_neg (hls j hj).1, if_neg (hls j hj).2, id_eq]
          _ = ls := List.map_id ls
      simpa only [hm] using hFoldMap d ρ L ls st
    have hFoldBoth (d : Bool) (ρ : Context) (L : ℕ) (hI : Inv ρ L) :
        ∀ (ls : List ℕ), ls.Pairwise (· < ·) → (∀ j ∈ ls, 1 ≤ j) →
        L ∈ ls → L + 1 ∈ ls → ∀ st : ℕ × ℕ, safe ρ L st.1 →
        ls.foldl (step d (norm ρ L)) st = ls.foldl (step d ρ) st := by
      intro ls
      induction ls with
      | nil => simp
      | cons j js ih =>
        intro hPair hPos hA hB st hs
        have hp := List.pairwise_cons.mp hPair
        by_cases hj : j = L
        · subst j
          have hBjs : L + 1 ∈ js := (List.mem_cons.mp hB).resolve_left (by omega)
          cases js with
          | nil => simp at hBjs
          | cons t ts =>
            have ht : t = L + 1 := by
              have hLt : L < t := hp.1 t (List.mem_cons_self ..)
              rcases List.mem_cons.mp hBjs with he | hm
              · omega
              · have htt := (List.pairwise_cons.mp hp.2).1 (L + 1) hm
                omega
            subst t
            have hTail : ∀ j ∈ ts, j ≠ L ∧ j ≠ L + 1 := by
              intro j hj
              have htj := (List.pairwise_cons.mp hp.2).1 j hj
              omega
            have h₁ : step d (norm ρ L) st L = step d ρ st (L + 1) := by
              simpa [perm, show L + 1 ≠ L by omega] using hStepMap d ρ L st (L + 1)
            have h₂ (st' : ℕ × ℕ) :
                step d (norm ρ L) st' (L + 1) = step d ρ st' L := by
              simpa [perm] using hStepMap d ρ L st' L
            simp only [List.foldl_cons]
            rw [h₁, h₂, ← hCommute d ρ L st hs]
            exact hFoldNe d ρ L ts hTail _
        · have hAjs : L ∈ js := (List.mem_cons.mp hA).resolve_left (Ne.symm hj)
          have hjL : j < L := hp.1 L hAjs
          have hBjs : L + 1 ∈ js := (List.mem_cons.mp hB).resolve_left (by omega)
          simp only [List.foldl_cons]
          rw [hStepNe d ρ L st j hj (by omega)]
          exact ih hp.2 (fun i hi ↦ hPos i (List.mem_cons_of_mem j hi)) hAjs hBjs _
            (hStepSafe d ρ L hI st hs j (hPos j (List.mem_cons_self ..)) hjL)
    have hLevelMem (ρ : Context) (j : ℕ) :
        j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
      simp only [levels, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; omega
      · intro hj; exact ⟨j - 1, by omega, by omega⟩
    have hMem (ρ : Context) (s : Side) (top j : ℕ) : j ∈ ρ.levelsOn s top ↔
        1 ≤ j ∧ j ≤ ρ.maxima.length ∧ ρ.sideAt j = s ∧ (top = 0 ∨ j < top) := by
      simp [levelsOn, hLevelMem, and_assoc]
    have hSorted (ρ : Context) (s : Side) (top : ℕ) :
        (ρ.levelsOn s top).Pairwise (· < ·) := by
      apply List.Pairwise.filter
      exact List.pairwise_lt_range.map (fun i ↦ i + 1) (fun i j h ↦ by dsimp; omega)
    have hSidePerm (ρ : Context) (L : ℕ) (hI : Inv ρ L) (j : ℕ) :
        ρ.sideAt (perm L j) = ρ.sideAt j := by
      dsimp only [perm]
      split_ifs with h₁ h₂
      · subst j; exact hI.2.2.2.1.symm
      · subst j; exact hI.2.2.2.1
      · rfl
    have hLevelsSame (ρ : Context) (L : ℕ) (hI : Inv ρ L) (s : Side) (top : ℕ) :
        (norm ρ L).levelsOn s top = ρ.levelsOn s top := by
      simp only [levelsOn, levels, hDepth, hSide, hSidePerm ρ L hI]
    have hPermMem (ρ : Context) (L : ℕ) (hI : Inv ρ L) (s : Side)
        (top : ℕ) (ht : top ≠ L + 1) (j : ℕ) :
        perm L j ∈ ρ.levelsOn s top ↔ j ∈ ρ.levelsOn s top := by
      rw [hMem, hMem, hSidePerm ρ L hI]
      have hb : (1 ≤ perm L j ∧ perm L j ≤ ρ.maxima.length) ↔
          (1 ≤ j ∧ j ≤ ρ.maxima.length) := by
        have hL := hI.1
        have hD := hI.2.1
        dsimp only [perm]
        split_ifs <;> omega
      have ho : (top = 0 ∨ perm L j < top) ↔ (top = 0 ∨ j < top) := by
        dsimp only [perm]
        split_ifs <;> omega
      tauto
    have hMapSorted (L : ℕ) (ls : List ℕ) (hPair : ls.Pairwise (· < ·))
        (hnot : ¬ (L ∈ ls ∧ L + 1 ∈ ls)) : (ls.map (perm L)).Pairwise (· < ·) := by
      apply List.pairwise_map.mpr
      apply hPair.imp_of_mem
      intro i j hi hj hij
      have hbad : ¬ (i = L ∧ j = L + 1) := by
        rintro ⟨rfl, rfl⟩
        exact hnot ⟨hi, hj⟩
      dsimp only [perm]
      split_ifs <;> omega
    have hWalkBijection (d : Bool) (ρ : Context) (L : ℕ) (hI : Inv ρ L)
        (s : Side) (top : ℕ) (ht : top ≠ L + 1) (p : ℕ) (hp : safe ρ L p)
        (ls : List ℕ) (hls : ls ∈ (ρ.levelsOn s top).sublists) :
        (∃ ts ∈ (ρ.levelsOn s top).sublists,
          ts.foldl (step d (norm ρ L)) (p, 0) = ls.foldl (step d ρ) (p, 0)) ∧
        (∃ ts ∈ (ρ.levelsOn s top).sublists,
          ts.foldl (step d ρ) (p, 0) = ls.foldl (step d (norm ρ L)) (p, 0)) := by
      have hSub := List.mem_sublists.mp hls
      have hPair : ls.Pairwise (· < ·) := (hSorted ρ s top).sublist hSub
      have hPos : ∀ j ∈ ls, 1 ≤ j := fun j hj ↦ ((hMem ρ s top j).mp (hSub.subset hj)).1
      by_cases hb : L ∈ ls ∧ L + 1 ∈ ls
      · have heq := hFoldBoth d ρ L hI ls hPair hPos hb.1 hb.2 (p, 0) hp
        exact ⟨⟨ls, hls, heq⟩, ⟨ls, hls, heq.symm⟩⟩
      · have hts : ls.map (perm L) ∈ (ρ.levelsOn s top).sublists := by
          apply List.mem_sublists.mpr
          apply MergeLevels.sublist_of_pairwise_lt (hMapSorted L ls hPair hb) (hSorted ρ s top)
          intro j hj
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
          exact (hPermMem ρ L hI s top ht i).mpr (hSub.subset hi)
        have hinv : (ls.map (perm L)).map (perm L) = ls := by
          simp only [List.map_map, Function.comp_def, hPermInv, List.map_id']
        refine ⟨⟨ls.map (perm L), hts, hFoldMap d ρ L ls (p, 0)⟩, ?_⟩
        refine ⟨ls.map (perm L), hts, ?_⟩
        simpa only [hinv] using (hFoldMap d ρ L (ls.map (perm L)) (p, 0)).symm
    have hExtEq (ρ : Context) (L : ℕ) (hI : Inv ρ L) (s : Side)
        (top : ℕ) (ht : top ≠ L + 1) (p : ℕ) (hp : safe ρ L p) :
        (norm ρ L).leftExt s top p = ρ.leftExt s top p ∧
        (norm ρ L).rightExt s top p = ρ.rightExt s top p := by
      have hEq (d : Bool) :
          ((((norm ρ L).levelsOn s top).sublists.map fun ls =>
            (ls.foldl (step d (norm ρ L)) (p, 0)).2).max?).getD 0 =
          (((ρ.levelsOn s top).sublists.map fun ls =>
            (ls.foldl (step d ρ) (p, 0)).2).max?).getD 0 := by
        rw [hLevelsSame ρ L hI]
        apply le_antisymm
        · apply Ctx.getD_max?_le_of_forall
          intro x hx
          obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
          obtain ⟨ts, hts, heq⟩ := (hWalkBijection d ρ L hI s top ht p hp ls hls).2
          exact ⟨_, List.mem_map.mpr ⟨ts, hts, rfl⟩, by rw [heq]⟩
        · apply Ctx.getD_max?_le_of_forall
          intro x hx
          obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
          obtain ⟨ts, hts, heq⟩ := (hWalkBijection d ρ L hI s top ht p hp ls hls).1
          exact ⟨_, List.mem_map.mpr ⟨ts, hts, rfl⟩, by rw [heq]⟩
      exact ⟨hEq true, hEq false⟩
    let ext (d : Bool) (ρ : Context) (s : Side) (top p : ℕ) : ℕ :=
      (((ρ.levelsOn s top).sublists.map fun ls => (ls.foldl (step d ρ) (p, 0)).2).max?).getD 0
    have hFoldSafe (d : Bool) (ρ : Context) (L : ℕ) (hI : Inv ρ L) :
        ∀ (ls : List ℕ), (∀ j ∈ ls, 1 ≤ j ∧ j < L) → ∀ st : ℕ × ℕ,
        safe ρ L st.1 → safe ρ L (ls.foldl (step d ρ) st).1 := by
      intro ls
      induction ls with
      | nil => intro h st hs; exact hs
      | cons j js ih =>
        intro h st hs
        simp only [List.foldl_cons]
        exact ih (fun i hi ↦ h i (List.mem_cons_of_mem j hi)) _
          (hStepSafe d ρ L hI st hs j (h j (List.mem_cons_self ..)).1
            (h j (List.mem_cons_self ..)).2)
    have hInvNorm (ρ : Context) (L : ℕ) (hI : Inv ρ L) : Inv (norm ρ L) L := by
      obtain ⟨hL, hD, hLet, hSides, hNon, hChild, hYoung⟩ := hI
      refine ⟨hL, by rw [hDepth]; exact hD, ?_, ?_, ?_, ?_, ?_⟩
      · intro p j v hp
        rw [hLetter] at hp
        cases h : ρ.letterAt p with
        | child => simp only [h, tag] at hp; cases hp
        | ext i w =>
          simp only [h, tag, Letter.ext.injEq] at hp
          have hi := hLet p i w h
          have hj := hp.1
          dsimp only [perm] at hj
          split_ifs at hj <;> omega
      · rw [hSide, hSide]
        simpa [perm, show L + 1 ≠ L by omega] using hSides.symm
      · rw [hExt, hExt]
        simpa [perm, show L + 1 ≠ L by omega, and_comm] using hNon
      · intro e he
        rw [(hGeometry ρ L).1] at he
        exact (hSafeNorm ρ L e).mpr (hChild e he)
      · intro j hj hjL e he
        rw [hExt] at he
        have hjp : perm L j = j := by simp [perm, show j ≠ L by omega, show j ≠ L + 1 by omega]
        rw [hjp] at he
        exact (hSafeNorm ρ L e).mpr (hYoung j hj hjL e he)
    have hOrient (d : Bool) (ρ : Context) (L : ℕ) (hI : Inv ρ L) (p : ℕ)
        (hA : ∀ x ∈ ρ.extPositions L, before d x p)
        (hB : ∀ x ∈ ρ.extPositions (L + 1), before d p x)
        (e : ℕ) (he : safe ρ L e) :
        (∀ x ∈ ρ.extPositions L, before d x e) ∧
        (∀ x ∈ ρ.extPositions (L + 1), before d e x) := by
      rcases hSafeDir d ρ L e he with h | ⟨hB', hA'⟩
      · exact h
      · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hI.2.2.2.2.1.1
        obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hI.2.2.2.2.1.2
        have hab := hBeforeTrans d (hA a ha) (hB b hb)
        have hba := hBeforeTrans d (hB' b hb) (hA' a ha)
        exact False.elim (hBeforeAsymm d hab hba)
    have hStepActiveCount (d : Bool) (ρ : Context) (st : ℕ × ℕ) (j : ℕ)
        (hn : ρ.extPositions j ≠ []) (h : ∀ x ∈ ρ.extPositions j, before d x st.1) :
        (step d ρ st j).2 = st.2 + 1 := by
      cases d with
      | false =>
        have hf : (ρ.extPositions j).filter (st.1 < ·) = ρ.extPositions j := by
          apply List.filter_eq_self.mpr
          intro x hx
          simpa [before] using h x hx
        simp only [step, Bool.false_eq_true, if_false, rightStep, hf]
        cases hh : (ρ.extPositions j).head? with
        | none => exact False.elim (hn (List.head?_eq_none_iff.mp hh))
        | some x => rfl
      | true =>
        have hf : (ρ.extPositions j).filter (· < st.1) = ρ.extPositions j := by
          apply List.filter_eq_self.mpr
          intro x hx
          simpa [before] using h x hx
        simp only [step, if_true, leftStep, hf]
        cases hh : (ρ.extPositions j).getLast? with
        | none => exact False.elim (hn (List.getLast?_eq_none_iff.mp hh))
        | some x => rfl
    have hLevelsIncrement (ρ : Context) (L : ℕ) (hI : Inv ρ L) (s : Side) :
        ρ.levelsOn s (L + 1) =
          if ρ.sideAt L = s then ρ.levelsOn s L ++ [L] else ρ.levelsOn s L := by
      have hL0 : L ≠ 0 := by have h := hI.1; omega
      have hLlen : L ≤ ρ.maxima.length := by have h := hI.2.1; omega
      by_cases hs : ρ.sideAt L = s
      · rw [if_pos hs]
        have hPair : (ρ.levelsOn s L ++ [L]).Pairwise (· < ·) := by
          apply List.pairwise_append.mpr
          refine ⟨hSorted ρ s L, by simp, ?_⟩
          intro j hj t ht
          simp only [List.mem_singleton] at ht
          subst t
          have hm := (hMem ρ s L j).mp hj
          rcases hm.2.2.2 with h0 | hlt
          · exact False.elim (hL0 h0)
          · exact hlt
        apply (hSorted ρ s (L + 1)).eq_of_mem_iff hPair
        intro j
        by_cases hj : j = L
        · subst j
          simp [hMem, hs, hLlen, hI.1]
        · have hlt : j < L + 1 ↔ j < L := by omega
          simp [hMem, hL0, hj, hlt]
      · rw [if_neg hs]
        apply (hSorted ρ s (L + 1)).eq_of_mem_iff (hSorted ρ s L)
        intro j
        by_cases hj : j = L
        · subst j; simp [hMem, hs]
        · have hlt : j < L + 1 ↔ j < L := by omega
          simp [hMem, hL0, hlt]
    have hAppendMax (xs : List ℕ) (f : List ℕ → ℕ) (L c : ℕ)
        (hf : ∀ ls ∈ xs.sublists, f (ls ++ [L]) = f ls + c) :
        (((xs ++ [L]).sublists.map f).max?).getD 0 =
          ((xs.sublists.map f).max?).getD 0 + c := by
      apply le_antisymm
      · apply Ctx.getD_max?_le
        intro x hx
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
        rw [List.sublists_concat] at hls
        rcases List.mem_append.mp hls with h | h
        · exact (Ctx.le_getD_max?_of_mem (List.mem_map.mpr ⟨ls, h, rfl⟩)).trans
            (Nat.le_add_right _ _)
        · obtain ⟨ts, hts, rfl⟩ := List.mem_map.mp h
          rw [hf ts hts]
          exact Nat.add_le_add_right (Ctx.le_getD_max?_of_mem
            (List.mem_map.mpr ⟨ts, hts, rfl⟩)) c
      · have hzero : f [] ∈ xs.sublists.map f := List.mem_map.mpr ⟨[], by simp, rfl⟩
        cases hm : (xs.sublists.map f).max? with
        | none =>
          have hn := List.max?_eq_none_iff.mp hm
          simp only [hn, List.not_mem_nil] at hzero
        | some m =>
          obtain ⟨ls, hls, heq⟩ := List.mem_map.mp (List.max?_mem hm)
          have hnew : f (ls ++ [L]) ∈ (xs ++ [L]).sublists.map f := by
            apply List.mem_map.mpr
            refine ⟨ls ++ [L], ?_, rfl⟩
            rw [List.sublists_concat]
            exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨ls, hls, rfl⟩))
          have hle := Ctx.le_getD_max?_of_mem hnew
          rw [hf ls hls, heq] at hle
          simpa only [hm, Option.getD_some] using hle
    have hIncrement (d : Bool) (ρ : Context) (L : ℕ) (hI : Inv ρ L)
        (s : Side) (p : ℕ) (hp : safe ρ L p) (c : ℕ)
        (hC : ∀ st : ℕ × ℕ, safe ρ L st.1 → (step d ρ st L).2 = st.2 + c) :
        ext d ρ s (L + 1) p = ext d ρ s L p + if ρ.sideAt L = s then c else 0 := by
      dsimp only [ext]
      rw [hLevelsIncrement ρ L hI]
      by_cases hs : ρ.sideAt L = s
      · simp only [if_pos hs]
        apply hAppendMax
        intro ls hls
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        apply hC
        apply hFoldSafe d ρ L hI ls _ (p, 0) hp
        intro j hj
        have hm := (hMem ρ s L j).mp ((List.mem_sublists.mp hls).subset hj)
        refine ⟨hm.1, ?_⟩
        rcases hm.2.2.2 with h0 | hlt
        · have hL := hI.1; omega
        · exact hlt
      · simp only [if_neg hs, Nat.add_zero]
    have hJoinIncrement (ρ : Context) (L : ℕ) (hI : Inv ρ L) (s : Side)
        (p q : ℕ) (hp : safe ρ L p) (hq : safe ρ L q) :
        ρ.leftExt s (L + 1) p + ρ.rightExt s (L + 1) q =
          ρ.leftExt s L p + ρ.rightExt s L q + if ρ.sideAt L = s then 1 else 0 := by
      rcases hSafeDir true ρ L p hp with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · have hU (e : ℕ) (he : safe ρ L e) := hOrient true ρ L hI p hA hB e he
        have hl : ρ.leftExt s (L + 1) p =
            ρ.leftExt s L p + if ρ.sideAt L = s then 1 else 0 := by
          exact hIncrement true ρ L hI s p hp 1 (fun st hs ↦
            hStepActiveCount true ρ st L hI.2.2.2.2.1.1 (hU st.1 hs).1)
        have hr : ρ.rightExt s (L + 1) q = ρ.rightExt s L q := by
          have h := hIncrement false ρ L hI s q hq 0 (by
            intro st hs
            rw [hStepNone false ρ st L (by
              intro x hx
              have hx' := (hU st.1 hs).1 x hx
              simpa [before] using hBeforeAsymm true hx')]
            simp)
          simpa only [ite_self, Nat.add_zero] using h
        rw [hl, hr]
        omega
      · have hA' : ∀ x ∈ ρ.extPositions L, before false x p := by
          simpa [before] using hB
        have hB' : ∀ x ∈ ρ.extPositions (L + 1), before false p x := by
          simpa [before] using hA
        have hU (e : ℕ) (he : safe ρ L e) := hOrient false ρ L hI p hA' hB' e he
        have hl : ρ.leftExt s (L + 1) p = ρ.leftExt s L p := by
          have h := hIncrement true ρ L hI s p hp 0 (by
            intro st hs
            rw [hStepNone true ρ st L (by
              intro x hx
              have hx' := (hU st.1 hs).1 x hx
              simpa [before] using hBeforeAsymm false hx')]
            simp)
          simpa only [ite_self, Nat.add_zero] using h
        have hr : ρ.rightExt s (L + 1) q =
            ρ.rightExt s L q + if ρ.sideAt L = s then 1 else 0 := by
          exact hIncrement false ρ L hI s q hq 1 (fun st hs ↦
            hStepActiveCount false ρ st L hI.2.2.2.2.1.1 (hU st.1 hs).1)
        rw [hl, hr]
        omega
    have hJoinEq (ρ : Context) (L : ℕ) (hI : Inv ρ L) (s : Side)
        (p q : ℕ) (hp : safe ρ L p) (hq : safe ρ L q) :
        (norm ρ L).joinExt s p q = ρ.joinExt s p q := by
      let α := ρ.leftExt s L p + ρ.rightExt s L q
      let term (τ : Context) (N : ℕ) := τ.leftExt s N p + τ.rightExt s N q + τ.maximumAt N
      have hα : (norm ρ L).leftExt s L p + (norm ρ L).rightExt s L q = α := by
        rw [(hExtEq ρ L hI s L (by omega) p hp).1,
          (hExtEq ρ L hI s L (by omega) q hq).2]
      have hM : 1 ≤ M ρ L := by
        have hm : 1 + ρ.maximumAt (L + 1) ≤ M ρ L := le_max_right _ _
        omega
      have hNe (N : ℕ) (hN : 1 ≤ N) (h₁ : N ≠ L) (h₂ : N ≠ L + 1) :
          term (norm ρ L) N = term ρ N := by
        dsimp only [term]
        rw [(hExtEq ρ L hI s N h₂ p hp).1, (hExtEq ρ L hI s N h₂ q hq).2,
          hMax ρ L hI.1 hI.2.1 N hN]
        simp only [if_neg h₁, if_neg h₂]
      have hNormSpecial (hOwn : ρ.sideAt L = s) (N : ℕ) (hN : N = L ∨ N = L + 1) :
          term (norm ρ L) N = α + M ρ L := by
        rcases hN with hN | hN
        · subst N
          dsimp only [term]
          rw [hα, hMax ρ L hI.1 hI.2.1 L hI.1]
          simp only [ite_true]
        · subst N
          dsimp only [term]
          have hOwn' : (norm ρ L).sideAt L = s := by
            rw [hSide, hSidePerm ρ L hI]
            exact hOwn
          rw [hJoinIncrement (norm ρ L) L (hInvNorm ρ L hI) s p q
            ((hSafeNorm ρ L p).mpr hp) ((hSafeNorm ρ L q).mpr hq),
            (hExtEq ρ L hI s L (by omega) p hp).1,
            (hExtEq ρ L hI s L (by omega) q hq).2,
            hMax ρ L hI.1 hI.2.1 (L + 1) (by omega)]
          simp only [if_pos hOwn', if_neg (show L + 1 ≠ L by omega), ite_true]
          dsimp only [α]
          omega
      have hOldSpecial (hOwn : ρ.sideAt L = s) (N : ℕ) (hN : N = L ∨ N = L + 1) :
          term ρ N ≤ α + M ρ L := by
        rcases hN with rfl | rfl
        · exact Nat.add_le_add_left (le_max_left _ _) α
        · dsimp only [term]
          rw [hJoinIncrement ρ L hI s p q hp hq, if_pos hOwn]
          have hm : 1 + ρ.maximumAt (L + 1) ≤ M ρ L := le_max_right _ _
          dsimp only [α]
          omega
      have hLevel₁ (hOwn : ρ.sideAt L = s) : L ∈ ρ.levelsOn s 0 :=
        (hMem ρ s 0 L).mpr ⟨hI.1, by have h := hI.2.1; omega, hOwn, Or.inl rfl⟩
      have hLevel₂ (hOwn : ρ.sideAt L = s) : L + 1 ∈ ρ.levelsOn s 0 :=
        (hMem ρ s 0 (L + 1)).mpr ⟨by omega, hI.2.1,
          hI.2.2.2.1.symm.trans hOwn, Or.inl rfl⟩
      have hBest (hOwn : ρ.sideAt L = s) :
          ∃ N ∈ ρ.levelsOn s 0, term ρ N = α + M ρ L := by
        by_cases hm : 1 + ρ.maximumAt (L + 1) ≤ ρ.maximumAt L
        · refine ⟨L, hLevel₁ hOwn, ?_⟩
          dsimp only [M]
          rw [max_eq_left hm]
        · refine ⟨L + 1, hLevel₂ hOwn, ?_⟩
          dsimp only [term, M]
          rw [hJoinIncrement ρ L hI s p q hp hq, if_pos hOwn,
            max_eq_right (by omega)]
          dsimp only [α]
          omega
      have hOwnOfSpecial (N : ℕ) (hN : N ∈ ρ.levelsOn s 0)
          (hSpec : N = L ∨ N = L + 1) : ρ.sideAt L = s := by
        have hn := (hMem ρ s 0 N).mp hN
        rcases hSpec with rfl | rfl
        · exact hn.2.2.1
        · exact hI.2.2.2.1.trans hn.2.2.1
      have hStrong : ((((norm ρ L).levelsOn s 0).map (term (norm ρ L))).max?).getD 0 =
          (((ρ.levelsOn s 0).map (term ρ)).max?).getD 0 := by
        rw [hLevelsSame ρ L hI]
        apply le_antisymm
        · apply Ctx.getD_max?_le_of_forall
          intro x hx
          obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hx
          by_cases hSpec : N = L ∨ N = L + 1
          · have hOwn := hOwnOfSpecial N hN hSpec
            obtain ⟨J, hJ, heq⟩ := hBest hOwn
            refine ⟨term ρ J, List.mem_map.mpr ⟨J, hJ, rfl⟩, ?_⟩
            rw [hNormSpecial hOwn N hSpec, heq]
          · have hns := not_or.mp hSpec
            refine ⟨term ρ N, List.mem_map.mpr ⟨N, hN, rfl⟩, ?_⟩
            rw [hNe N ((hMem ρ s 0 N).mp hN).1 hns.1 hns.2]
        · apply Ctx.getD_max?_le_of_forall
          intro x hx
          obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hx
          by_cases hSpec : N = L ∨ N = L + 1
          · have hOwn := hOwnOfSpecial N hN hSpec
            refine ⟨term (norm ρ L) L, List.mem_map.mpr ⟨L, hLevel₁ hOwn, rfl⟩, ?_⟩
            rw [hNormSpecial hOwn L (Or.inl rfl)]
            exact hOldSpecial hOwn N hSpec
          · have hns := not_or.mp hSpec
            refine ⟨term (norm ρ L) N, List.mem_map.mpr ⟨N, hN, rfl⟩, ?_⟩
            rw [hNe N ((hMem ρ s 0 N).mp hN).1 hns.1 hns.2]
      have hChain : (norm ρ L).chainExt s p q = ρ.chainExt s p q := by
        simp only [chainExt, (hExtEq ρ L hI s 0 (by omega) p hp).1,
          (hExtEq ρ L hI s 0 (by omega) q hq).2]
      exact congrArg₂ max hChain hStrong
    have hBase (ρ : Context) (L : ℕ) (hI : Inv ρ L) : (norm ρ L).base = ρ.base := by
      unfold base
      rw [(hGeometry ρ L).1]
      cases hh : ρ.childPositions.head? with
      | none => rfl
      | some p =>
        have hp : safe ρ L p := hI.2.2.2.2.2.1 p (List.mem_of_head? hh)
        have hChain (s : Side) : (norm ρ L).chainExt s p p = ρ.chainExt s p p := by
          simp only [chainExt, (hExtEq ρ L hI s 0 (by omega) p hp).1,
            (hExtEq ρ L hI s 0 (by omega) p hp).2]
        have hCup : (norm ρ L).cupLimit p p = ρ.cupLimit p p := by
          unfold cupLimit
          change min (ρ.u - 1 - (norm ρ L).chainExt Side.lower p p)
            (ρ.k - 1 - (norm ρ L).joinExt Side.lower p p) = _
          rw [hChain, hJoinEq ρ L hI Side.lower p p hp hp]
        have hCap : (norm ρ L).capLimit p p = ρ.capLimit p p := by
          unfold capLimit
          change min (ρ.a - 1 - (norm ρ L).chainExt Side.upper p p)
            (ρ.k - 1 - (norm ρ L).joinExt Side.upper p p) = _
          rw [hChain, hJoinEq ρ L hI Side.upper p p hp hp]
        simp only [hCup, hCap]
        rfl
    have hFuel : ∀ fuel (ρ : Context) (L : ℕ), Inv ρ L →
        boundFuel fuel (norm ρ L) = boundFuel fuel ρ := by
      intro fuel
      induction fuel with
      | zero => intros; rfl
      | succ fuel ih =>
        intro ρ L hI
        have hParts (B : List ℕ) (s : Side) (m : ℕ) :
            boundFuel fuel ((norm ρ L).part B s m) = boundFuel fuel (ρ.part B s m) := by
          rw [← hNormPart ρ L hI.1 B s m]
          exact ih (ρ.part B s m) (L + 1) (hInvPart ρ L hI B s m)
        rw [boundFuel.eq_2, boundFuel.eq_2, (hGeometry ρ L).2.1]
        by_cases hrun : ρ.numRuns ≤ 1
        · simp only [if_pos hrun]
          exact hBase ρ L hI
        · simp only [if_neg hrun]
          have hBlocks : (norm ρ L).blocks = ρ.blocks := by
            simp only [blocks, (hGeometry ρ L).1]
          have hk : (norm ρ L).k = ρ.k := rfl
          rw [hBlocks, (hGeometry ρ L).1, hk]
          congr 2
          apply List.flatMap_congr
          intro B hB
          apply List.flatMap_congr
          intro d hd
          rw [hParts, hParts, hParts, hParts]
    have hRoot : Inv σ 1 := by
      refine ⟨by omega, hlevels, ?_, hsame, ⟨hfirst, hsecond⟩, ?_, ?_⟩
      · intro p j s h
        exact (hwf.2.2.2.2.2 p j s h).1
      · intro e he
        rcases hflanks with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · exact Or.inl ⟨fun x hx ↦ hA x hx e he, fun x hx ↦ hB x hx e he⟩
        · exact Or.inr ⟨fun x hx ↦ hA x hx e he, fun x hx ↦ hB x hx e he⟩
      · intro j hj hjL
        omega
    unfold bound
    rw [(hGeometry σ 1).1]
    exact (hFuel _ σ 1 hRoot).symm
  · have hSet (x y : ℕ) : (σ.maxima.set 0 x).set 1 y = [x, y] ++ σ.maxima.drop 2 := by
      cases hm : σ.maxima with
      | nil => simp [hm] at hlevels
      | cons m rest =>
        cases rest with
        | nil => simp [hm] at hlevels
        | cons n tail => simp [hm]
    simpa only [if_neg hsame, hSet] using
      (ctx_bound_opposite_level_swap σ hwf hfirst hsecond hsame).symm


end ErdosSzekeres
