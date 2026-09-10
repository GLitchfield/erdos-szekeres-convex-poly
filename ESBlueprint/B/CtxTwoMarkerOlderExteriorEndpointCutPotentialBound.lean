import ESBlueprint.B.CtxOneLevelRefinedPotentialBound
import ESBlueprint.B.CtxTwoMarkerSurroundOlderInternalComplementCutPotentialBound

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- For two actual chosen markers N<M and a retained endpoint beyond the older marker away from the younger, prove the full and arbitrary-fuel cut sum is at most choose(w+1,2)+w-1. A local three-marker collapse gives the chosen complement bound 2w-1; the opposite companion has at most w-1 available ranks and a triangular bound choose(w,2). Arbitrary positive history, old maxima, inactive children, and new maxima are allowed. No recursive bare-potential premise is used.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_older_exterior_endpoint_cut_potential_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y)
  (hwidth : 1 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
  (keep : List ℕ) (q₀ l m n : ℕ)
  (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
  (hl : l ∈ σ.childPositions) (hlnot : l ∉ keep)
  (horder :
    ((∀ p ∈ keep, y < p) ∧ x < y ∧
      ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → q < p) ∨
    ((∀ p ∈ keep, p < y) ∧ y < x ∧
      ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep → p < q)) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) +
    Ctx.Context.boundFuel g (σ.part keep t n) ≤ (w + 1).choose 2 + w - 1) ∧
    (σ.part rest s m).bound + (σ.part keep t n).bound ≤ (w + 1).choose 2 + w - 1 := by
  classical
  have ctx_three_marker_boundary_collapse_upper_normalize (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s : Ctx.Side) (J N M a x y : ℕ)
    (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels)
    (hJN : J < N) (hNM : N < M)
    (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
    (ha : a ∈ σ.extPositions J) (hNonly : σ.extPositions N = [x]) (hy : y ∈ σ.extPositions M)
    (direction : Bool)
    (horder : if direction then x < y ∧ y < a else a < y ∧ y < x)
    (hboundary : ∀ p ∈ σ.childPositions, if direction then p < a else a < p)
    (hyoung : ∀ j ∈ σ.levelsOn s J, ∀ p ∈ σ.extPositions j,
      if direction then p < a else a < p) :
    let κ : Ctx.Context := { σ with
      word := σ.word.map (fun z => match (generalizing := false) z with
        | Ctx.Letter.child => Ctx.Letter.child
        | Ctx.Letter.ext j v => if j < J ∨ j = N then Ctx.Letter.ext j v
            else Ctx.Letter.ext (σ.maxima.length + 1) v)
      maxima := σ.maxima.mapIdx (fun i m => if i + 1 < J then m else 0) }
    let τ : Ctx.Context := match (generalizing := false) s with
      | Ctx.Side.lower => { κ with u := σ.u - 1 }
      | Ctx.Side.upper => { κ with a := σ.a - 1 }
    (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
      τ.childPositions = σ.childPositions ∧ τ.levels = σ.levels ∧
      τ.sideAt N = s ∧ τ.extPositions N = [x] ∧
      (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧ σ.bound ≤ τ.bound := by
    classical
    let mask (J N j : ℕ) : Prop := j < J ∨ j = N
    let erase (ρ : Context) (J N : ℕ) (z : Letter) := match (generalizing := false) z with
      | Letter.child => Letter.child
      | Letter.ext j v => if mask J N j then Letter.ext j v else Letter.ext (ρ.maxima.length + 1) v
    let norm (ρ : Context) (J N : ℕ) : Context :=
      let κ : Context := { ρ with
        word := ρ.word.map (erase ρ J N)
        maxima := ρ.maxima.mapIdx (fun i m => if i + 1 < J then m else 0) }
      match (generalizing := false) s with
      | Side.lower => { κ with u := ρ.u - 1 }
      | Side.upper => { κ with a := ρ.a - 1 }
    change (∀ p j v, (norm σ J N).letterAt p = Letter.ext j v → 1 ≤ j) ∧
      (norm σ J N).childPositions = σ.childPositions ∧ (norm σ J N).levels = σ.levels ∧
      (norm σ J N).sideAt N = s ∧ (norm σ J N).extPositions N = [x] ∧
      (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel (norm σ J N)) ∧ σ.bound ≤ (norm σ J N).bound
    have hWord (ρ : Context) (J N : ℕ) : (norm ρ J N).word = ρ.word.map (erase ρ J N) := by cases s <;> rfl
    have hMaxima (ρ : Context) (J N : ℕ) : (norm ρ J N).maxima =
        ρ.maxima.mapIdx (fun i m => if i + 1 < J then m else 0) := by cases s <;> rfl
    have hDepth (ρ : Context) (J N : ℕ) : (norm ρ J N).maxima.length = ρ.maxima.length := by
      rw [hMaxima, List.length_mapIdx]
    have hLen (ρ : Context) (J N : ℕ) : (norm ρ J N).word.length = ρ.word.length := by
      rw [hWord, List.length_map]
    have hK (ρ : Context) (J N : ℕ) : (norm ρ J N).k = ρ.k := by cases s <;> rfl
    have hLetter (ρ : Context) (J N p : ℕ) :
        (norm ρ J N).letterAt p = erase ρ J N (ρ.letterAt p) := by
      simp only [letterAt, hWord, List.getElem?_map]
      cases he : ρ.word[p]? <;> simp [he, erase]
    have hIsChild (ρ : Context) (J N p : ℕ) :
        (norm ρ J N).letterAt p = Letter.child ↔ ρ.letterAt p = Letter.child := by
      rw [hLetter]
      cases he : ρ.letterAt p with
      | child => simp [erase]
      | ext j v => by_cases hj : mask J N j <;> simp [erase, hj]
    have hChild (ρ : Context) (J N : ℕ) : (norm ρ J N).childPositions = ρ.childPositions := by
      simp only [childPositions, hLen, hIsChild]
    have hRuns (ρ : Context) (J N : ℕ) : (norm ρ J N).numRuns = ρ.numRuns := by
      simp only [numRuns, hLen, ne_eq, hIsChild]
    have hBlocks (ρ : Context) (J N : ℕ) : (norm ρ J N).blocks = ρ.blocks := by
      simp only [blocks, hChild]
    have hLevels (ρ : Context) (J N : ℕ) : (norm ρ J N).levels = ρ.levels := by
      simp only [levels, hDepth]
    have hPos (ρ : Context) (J N : ℕ)
        (hP : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) :
        ∀ p j v, (norm ρ J N).letterAt p = Letter.ext j v → 1 ≤ j := by
      intro p j v hp
      rw [hLetter] at hp
      cases he : ρ.letterAt p with
      | child => simp [he, erase] at hp
      | ext i u =>
        rw [he] at hp
        dsimp only [erase] at hp
        by_cases hi : mask J N i
        · rw [if_pos hi] at hp
          cases hp
          exact hP p _ _ he
        · rw [if_neg hi] at hp
          cases hp
          omega
    have hExt (ρ : Context) (J N j : ℕ) (hj : j ∈ ρ.levels) :
        (norm ρ J N).extPositions j = if mask J N j then ρ.extPositions j else [] := by
      have hjd : j ≤ ρ.maxima.length := by
        have hh := hj
        simp only [levels, List.mem_map, List.mem_range] at hh
        obtain ⟨i, hi, rfl⟩ := hh
        omega
      have hNe : ρ.maxima.length + 1 ≠ j := by omega
      by_cases hm : mask J N j
      · rw [if_pos hm]
        simp only [extPositions, hLen]
        apply List.filter_congr
        intro p hp
        rw [hLetter]
        cases he : ρ.letterAt p with
        | child => simp [erase]
        | ext i u =>
          by_cases hij : i = j
          · subst i
            simp [erase, hm]
          · by_cases hi : mask J N i <;> simp [erase, hi, hij, hNe]
      · rw [if_neg hm]
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro p hp
        have hh := (List.mem_filter.mp hp).2
        rw [hLetter] at hh
        cases he : ρ.letterAt p with
        | child => simp [he, erase] at hh
        | ext i u =>
          by_cases hij : i = j
          · subst i
            simp [he, erase, hm, hNe] at hh
          · by_cases hi : mask J N i <;> simp [he, erase, hi, hij, hNe] at hh
    have hSide (ρ : Context) (J N j : ℕ) (hj : j ∈ ρ.levels) (hm : mask J N j) :
        (norm ρ J N).sideAt j = ρ.sideAt j := by
      have he : (norm ρ J N).extPositions j = ρ.extPositions j := by rw [hExt ρ J N j hj, if_pos hm]
      simp only [sideAt, he]
      cases hh : (ρ.extPositions j).head? with
      | none => rfl
      | some p =>
        have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        have hjp := (List.mem_filter.mp hp).2
        dsimp only
        rw [hLetter]
        cases hl : ρ.letterAt p with
        | child => simp [hl] at hjp
        | ext i u =>
          have hij : i = j := by simpa [hl] using hjp
          subst i
          simp only [erase, if_pos hm]
    have hMaximum (ρ : Context) (J N j : ℕ) (hj : 1 ≤ j) :
        (norm ρ J N).maximumAt j = if j < J then ρ.maximumAt j else 0 := by
      simp only [maximumAt, hMaxima, List.getElem?_mapIdx]
      have he : j - 1 + 1 = j := by omega
      rw [he]
      cases hm : ρ.maxima[j-1]? <;> by_cases hlt : j < J <;> simp [hm, hlt]
    have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
      simp only [levels, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        omega
      · intro hj
        exact ⟨j-1, by omega, by omega⟩
    have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
      unfold levels
      exact List.pairwise_lt_range.map (fun i => i+1) (fun i j h => Nat.add_lt_add_right h 1)
    have hListOn (ρ : Context) (v : Side) (ls : List ℕ)
        (hls : ls.Sublist ρ.levels) (hs : ∀ j ∈ ls, ρ.sideAt j = v) :
        ls.Sublist (ρ.levelsOn v 0) := by
      have hh := hls.filter (fun j => decide (ρ.sideAt j = v))
      have he : ls.filter (fun j => decide (ρ.sideAt j = v)) = ls := by
        apply List.filter_eq_self.mpr
        intro j hj
        simp [hs j hj]
      simpa only [he, levelsOn, true_or, and_true] using hh
    have hFilteredSub (ρ : Context) (J N top : ℕ) (v : Side) (ls : List ℕ)
        (hls : ls.Sublist ((norm ρ J N).levelsOn v top)) :
        (ls.filter (fun j => decide (mask J N j))).Sublist (ρ.levelsOn v 0) := by
      have hSub : ls.Sublist ρ.levels := by
        simpa only [hLevels] using hls.trans List.filter_sublist
      apply hListOn ρ v _ (List.filter_sublist.trans hSub)
      intro j hj
      have hj' := List.mem_filter.mp hj
      have hm : mask J N j := of_decide_eq_true hj'.2
      have hjL := hSub.subset hj'.1
      have hv := of_decide_eq_true (List.mem_filter.mp (hls.subset hj'.1)).2
      exact (hSide ρ J N j hjL hm).symm.trans hv.1
    have hBelowLevels (ρ : Context) (J N top : ℕ) (htop : 1 ≤ top) (htJ : top ≤ J)
        (v : Side) : (norm ρ J N).levelsOn v top = ρ.levelsOn v top := by
      simp only [levelsOn, hLevels]
      apply List.filter_congr
      intro j hj
      by_cases hlt : j < top
      · have hm : mask J N j := Or.inl (by omega)
        rw [hSide ρ J N j hj hm]
      · simp [show top ≠ 0 by omega, hlt]
    have hFoldLeft (ρ : Context) (J N : ℕ) : ∀ (ls : List ℕ),
        (∀ j ∈ ls, j ∈ ρ.levels) → ∀ z : ℕ × ℕ,
        (ls.foldl (leftStep (norm ρ J N)) z) =
          ((ls.filter (fun j => decide (mask J N j))).foldl (leftStep ρ) z) := by
      intro ls
      induction ls with
      | nil => intro _ z; rfl
      | cons j ls ih =>
        intro hall z
        have hj := hall j (by simp)
        have ht : ∀ i ∈ ls, i ∈ ρ.levels := fun i hi => hall i (List.mem_cons_of_mem _ hi)
        rw [List.foldl_cons]
        by_cases hm : mask J N j
        · have hs : leftStep (norm ρ J N) z j = leftStep ρ z j := by
            simp only [leftStep, hExt ρ J N j hj, if_pos hm]
          rw [hs]
          simpa only [List.filter_cons, hm, decide_true, Bool.true_eq, ite_true, List.foldl_cons]
            using ih ht (leftStep ρ z j)
        · have hs : leftStep (norm ρ J N) z j = z := by
            simp [leftStep, hExt ρ J N j hj, hm]
          rw [hs]
          simpa only [List.filter_cons, hm, decide_false, Bool.false_eq_true, ite_false] using ih ht z
    have hLeftLe (ρ : Context) (J N top p : ℕ) (v : Side) :
        (norm ρ J N).leftExt v top p ≤ ρ.leftExt v 0 p := by
      simp only [leftExt_eq]
      apply Ctx.getD_max?_le_of_forall
      intro c hc
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hc
      have hsub := List.mem_sublists.mp hls
      have hall : ∀ j ∈ ls, j ∈ ρ.levels := by
        intro j hj
        simpa only [hLevels] using (List.mem_filter.mp (hsub.subset hj)).1
      refine ⟨_, List.mem_map.mpr ⟨ls.filter (fun j => decide (mask J N j)),
        List.mem_sublists.mpr (hFilteredSub ρ J N top v ls hsub), rfl⟩, ?_⟩
      exact le_of_eq (congrArg Prod.snd (hFoldLeft ρ J N ls hall (p,0)))
    have hLeftBelow (ρ : Context) (J N top p : ℕ) (htop : 1 ≤ top) (htJ : top ≤ J)
        (v : Side) : (norm ρ J N).leftExt v top p = ρ.leftExt v top p := by
      have hValues : ((ρ.levelsOn v top).sublists.map
          (fun ls => (ls.foldl (leftStep (norm ρ J N)) (p,0)).2)) =
          ((ρ.levelsOn v top).sublists.map (fun ls => (ls.foldl (leftStep ρ) (p,0)).2)) := by
        apply List.map_congr_left
        intro ls hls
        have hh := List.mem_sublists.mp hls
        have hall : ∀ j ∈ ls, j ∈ ρ.levels := fun j hj => (List.mem_filter.mp (hh.subset hj)).1
        have he : ls.filter (fun j => decide (mask J N j)) = ls := by
          apply List.filter_eq_self.mpr
          intro j hj
          have hjP := of_decide_eq_true (List.mem_filter.mp (hh.subset hj)).2
          have hm : mask J N j := Or.inl (by omega)
          simp [hm]
        simpa only [he] using congrArg Prod.snd (hFoldLeft ρ J N ls hall (p,0))
      simp only [leftExt_eq, hBelowLevels ρ J N top htop htJ v, hValues]
    have hFoldRight (ρ : Context) (J N : ℕ) : ∀ (ls : List ℕ),
        (∀ j ∈ ls, j ∈ ρ.levels) → ∀ z : ℕ × ℕ,
        (ls.foldl (rightStep (norm ρ J N)) z) =
          ((ls.filter (fun j => decide (mask J N j))).foldl (rightStep ρ) z) := by
      intro ls
      induction ls with
      | nil => intro _ z; rfl
      | cons j ls ih =>
        intro hall z
        have hj := hall j (by simp)
        have ht : ∀ i ∈ ls, i ∈ ρ.levels := fun i hi => hall i (List.mem_cons_of_mem _ hi)
        rw [List.foldl_cons]
        by_cases hm : mask J N j
        · have hs : rightStep (norm ρ J N) z j = rightStep ρ z j := by
            simp only [rightStep, hExt ρ J N j hj, if_pos hm]
          rw [hs]
          simpa only [List.filter_cons, hm, decide_true, Bool.true_eq, ite_true, List.foldl_cons]
            using ih ht (rightStep ρ z j)
        · have hs : rightStep (norm ρ J N) z j = z := by
            simp [rightStep, hExt ρ J N j hj, hm]
          rw [hs]
          simpa only [List.filter_cons, hm, decide_false, Bool.false_eq_true, ite_false] using ih ht z
    have hRightLe (ρ : Context) (J N top p : ℕ) (v : Side) :
        (norm ρ J N).rightExt v top p ≤ ρ.rightExt v 0 p := by
      simp only [rightExt_eq]
      apply Ctx.getD_max?_le_of_forall
      intro c hc
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hc
      have hsub := List.mem_sublists.mp hls
      have hall : ∀ j ∈ ls, j ∈ ρ.levels := by
        intro j hj
        simpa only [hLevels] using (List.mem_filter.mp (hsub.subset hj)).1
      refine ⟨_, List.mem_map.mpr ⟨ls.filter (fun j => decide (mask J N j)),
        List.mem_sublists.mpr (hFilteredSub ρ J N top v ls hsub), rfl⟩, ?_⟩
      exact le_of_eq (congrArg Prod.snd (hFoldRight ρ J N ls hall (p,0)))
    have hRightBelow (ρ : Context) (J N top p : ℕ) (htop : 1 ≤ top) (htJ : top ≤ J)
        (v : Side) : (norm ρ J N).rightExt v top p = ρ.rightExt v top p := by
      have hValues : ((ρ.levelsOn v top).sublists.map
          (fun ls => (ls.foldl (rightStep (norm ρ J N)) (p,0)).2)) =
          ((ρ.levelsOn v top).sublists.map (fun ls => (ls.foldl (rightStep ρ) (p,0)).2)) := by
        apply List.map_congr_left
        intro ls hls
        have hh := List.mem_sublists.mp hls
        have hall : ∀ j ∈ ls, j ∈ ρ.levels := fun j hj => (List.mem_filter.mp (hh.subset hj)).1
        have he : ls.filter (fun j => decide (mask J N j)) = ls := by
          apply List.filter_eq_self.mpr
          intro j hj
          have hjP := of_decide_eq_true (List.mem_filter.mp (hh.subset hj)).2
          have hm : mask J N j := Or.inl (by omega)
          simp [hm]
        simpa only [he] using congrArg Prod.snd (hFoldRight ρ J N ls hall (p,0))
      simp only [rightExt_eq, hBelowLevels ρ J N top htop htJ v, hValues]
    have hJoinLe (ρ : Context) (J N p q : ℕ) (v : Side) :
        (norm ρ J N).joinExt v p q ≤ ρ.joinExt v p q := by
      change max ((norm ρ J N).chainExt v p q) _ ≤ ρ.joinExt v p q
      apply max_le
      · exact (Nat.add_le_add (hLeftLe ρ J N 0 p v) (hRightLe ρ J N 0 q v)).trans (le_max_left _ _)
      · apply getD_max?_le
        intro c hc
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
        have hjL : j ∈ ρ.levels := by simpa only [hLevels] using (List.mem_filter.mp hj).1
        have hj1 := one_le_of_mem_levels hjL
        by_cases hjJ : j < J
        · have hm : mask J N j := Or.inl hjJ
          have hs := of_decide_eq_true (List.mem_filter.mp hj).2
          have hs' : ρ.sideAt j = v := (hSide ρ J N j hjL hm).symm.trans hs.1
          have hjOn : j ∈ ρ.levelsOn v 0 := List.mem_filter.mpr ⟨hjL, by simp [hs']⟩
          rw [hMaximum ρ J N j hj1, if_pos hjJ,
            hLeftBelow ρ J N j p hj1 (by omega) v, hRightBelow ρ J N j q hj1 (by omega) v]
          exact le_joinExt_of_mem_levelsOn hjOn p q
        · rw [hMaximum ρ J N j hj1, if_neg hjJ]
          have hl := hLeftLe ρ J N j p v
          have hr := hRightLe ρ J N j q v
          have hc : ρ.chainExt v p q ≤ ρ.joinExt v p q := le_max_left _ _
          dsimp only [chainExt] at hc
          omega
    have hSublistSorted (ρ : Context) (v : Side) (ls : List ℕ)
        (hs : ls.Pairwise (· < ·)) (hm : ls ⊆ ρ.levelsOn v 0) : ls.Sublist (ρ.levelsOn v 0) := by
      have he : (ρ.levelsOn v 0).filter (· ∈ ls) = ls := by
        apply (((hSorted ρ).filter _).filter _).eq_of_mem_iff hs
        intro j
        constructor
        · intro hj
          exact of_decide_eq_true (List.mem_filter.mp hj).2
        · intro hj
          exact List.mem_filter.mpr ⟨hm hj, by simp only [hj, decide_true]⟩
      rw [← he]
      exact List.filter_sublist
    have hAppendTail (ρ : Context) (J : ℕ) (v : Side) (pre tail : List ℕ)
        (hpre : pre.Sublist (ρ.levelsOn v J)) (hJpos : 1 ≤ J)
        (htail : tail.Pairwise (· < ·))
        (ht : ∀ j ∈ tail, j ∈ ρ.levelsOn v 0 ∧ J ≤ j) :
        (pre ++ tail).Sublist (ρ.levelsOn v 0) := by
      have hp0 : pre.Sublist (ρ.levelsOn v 0) :=
        hListOn ρ v pre (hpre.trans List.filter_sublist)
          (fun j hj => (of_decide_eq_true (List.mem_filter.mp (hpre.subset hj)).2).1)
      apply hSublistSorted ρ v
      · apply List.pairwise_append.mpr
        refine ⟨List.Pairwise.sublist hp0 ((hSorted ρ).filter _), htail, ?_⟩
        intro i hi j hj
        have hip := of_decide_eq_true (List.mem_filter.mp (hpre.subset hi)).2
        have hjp := (ht j hj).2
        omega
      · intro j hj
        rcases List.mem_append.mp hj with hj | hj
        · exact hp0.subset hj
        · exact (ht j hj).1
    have hSelected (ρ : Context) (J N : ℕ) (hJpos : 1 ≤ J) (hJN : J < N)
        (hN : N ∈ ρ.levels) (hNs : ρ.sideAt N = s) :
        ((norm ρ J N).levelsOn s 0).filter (fun j => decide (mask J N j)) =
          ρ.levelsOn s J ++ [N] := by
      have hNOn : N ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
      have hMaskEq : ((norm ρ J N).levelsOn s 0).filter (fun j => decide (mask J N j)) =
          (ρ.levelsOn s 0).filter (fun j => decide (mask J N j)) := by
        simp only [levelsOn, hLevels, List.filter_filter]
        apply List.filter_congr
        intro j hj
        by_cases hm : mask J N j
        · rw [hSide ρ J N j hj hm]
        · simp [hm]
      rw [hMaskEq]
      have hSortRight : (ρ.levelsOn s J ++ [N]).Pairwise (· < ·) := by
        apply List.pairwise_append.mpr
        refine ⟨(hSorted ρ).filter _, by simp, ?_⟩
        intro i hi j hj
        have hjN : j = N := by simpa using hj
        have hip := of_decide_eq_true (List.mem_filter.mp hi).2
        omega
      apply (((hSorted ρ).filter _).filter _).eq_of_mem_iff hSortRight
      intro j
      constructor
      · intro hj
        have hh := List.mem_filter.mp hj
        have hm : mask J N j := of_decide_eq_true hh.2
        apply List.mem_append.mpr
        rcases hm with hjJ | hjN
        · left
          have hs := of_decide_eq_true (List.mem_filter.mp hh.1).2
          exact List.mem_filter.mpr ⟨(List.mem_filter.mp hh.1).1, by simp [hs.1, hjJ]⟩
        · right
          simpa using hjN
      · intro hj
        rcases List.mem_append.mp hj with hj | hj
        · have hh := List.mem_filter.mp hj
          have hp := of_decide_eq_true hh.2
          have hm : mask J N j := Or.inl (by omega)
          exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hh.1, by simp [hp.1]⟩, by simp [hm]⟩
        · have hjN : j = N := by simpa using hj
          subst j
          exact List.mem_filter.mpr ⟨hNOn, by simp [mask]⟩
    have hEndRight (ρ : Context) (x : ℕ) : ∀ (ls : List ℕ),
        (∀ j ∈ ls, ∀ y ∈ ρ.extPositions j, y < x) → ∀ z : ℕ × ℕ,
        z.1 < x → (ls.foldl (rightStep ρ) z).1 < x := by
      intro ls
      induction ls with
      | nil => intro _ z hz; exact hz
      | cons j ls ih =>
        intro hy z hz
        have ht : ∀ i ∈ ls, ∀ y ∈ ρ.extPositions i, y < x :=
          fun i hi y hiy => hy i (by simp [hi]) y hiy
        cases hh : ((ρ.extPositions j).filter (z.1 < ·)).head? with
        | none => simpa only [List.foldl_cons, rightStep, hh] using ih ht z hz
        | some y =>
          have hm := List.mem_of_mem_head? (Option.mem_def.mpr hh)
          have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
          simpa only [List.foldl_cons, rightStep, hh] using ih ht (y,z.2+1) hyx
    have hEndLeft (ρ : Context) (x : ℕ) : ∀ (ls : List ℕ),
        (∀ j ∈ ls, ∀ y ∈ ρ.extPositions j, x < y) → ∀ z : ℕ × ℕ,
        x < z.1 → x < (ls.foldl (leftStep ρ) z).1 := by
      intro ls
      induction ls with
      | nil => intro _ z hz; exact hz
      | cons j ls ih =>
        intro hy z hz
        have ht : ∀ i ∈ ls, ∀ y ∈ ρ.extPositions i, x < y :=
          fun i hi y hiy => hy i (by simp [hi]) y hiy
        cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? with
        | none => simpa only [List.foldl_cons, leftStep, hh] using ih ht z hz
        | some y =>
          have hm := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
          have hxy := hy j (by simp) y (List.mem_filter.mp hm).1
          simpa only [List.foldl_cons, leftStep, hh] using ih ht (y,z.2+1) hxy
    have hMoreRight (ρ : Context) (J N M a x y p : ℕ)
        (hJ : J ∈ ρ.levels) (hN : N ∈ ρ.levels) (hM : M ∈ ρ.levels)
        (hJN : J < N) (hNM : N < M)
        (hJs : ρ.sideAt J = s) (hNs : ρ.sideAt N = s) (hMs : ρ.sideAt M = s)
        (ha : a ∈ ρ.extPositions J) (hNonly : ρ.extPositions N = [x]) (hy : y ∈ ρ.extPositions M)
        (hXY : x < y) (hYA : y < a)
        (hyoung : ∀ j ∈ ρ.levelsOn s J, ∀ q ∈ ρ.extPositions j, q < a)
        (hp : p < a) : (norm ρ J N).rightExt s 0 p + 1 ≤ ρ.rightExt s 0 p := by
      have hJpos := one_le_of_mem_levels hJ
      have hJOn : J ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hJ, by simp [hJs]⟩
      have hNOn : N ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
      have hMOn : M ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hM, by simp [hMs]⟩
      have hBaseAug (pre : List ℕ) (hpre : pre.Sublist (ρ.levelsOn s J)) :
          (pre.foldl (rightStep ρ) (p,0)).2 + 1 ≤ ρ.rightExt s 0 p := by
        let z := pre.foldl (rightStep ρ) (p,0)
        have hz : z.1 < a := hEndRight ρ a pre
          (fun j hj q hq => hyoung j (hpre.subset hj) q hq) (p,0) hp
        have hm : a ∈ (ρ.extPositions J).filter (z.1 < ·) := by simp [ha, hz]
        have hne := List.ne_nil_of_mem hm
        have hsub := hAppendTail ρ J s pre [J] hpre hJpos (by simp)
          (by
            intro j hj
            have hjJ : j = J := by simpa using hj
            subst j
            exact ⟨hJOn, le_rfl⟩)
        have hv := le_getD_max?_of_mem (L := (ρ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (rightStep ρ) (p,0)).2))
          (List.mem_map.mpr ⟨pre ++ [J], List.mem_sublists.mpr hsub, rfl⟩)
        change _ ≤ ρ.rightExt s 0 p at hv
        rw [List.foldl_append] at hv
        change (rightStep ρ z J).2 ≤ ρ.rightExt s 0 p at hv
        simpa only [rightStep, List.head?_eq_some_head hne] using hv
      have hWithN (pre : List ℕ) (hpre : pre.Sublist (ρ.levelsOn s J)) :
          ((pre ++ [N]).foldl (rightStep ρ) (p,0)).2 + 1 ≤ ρ.rightExt s 0 p := by
        let z := pre.foldl (rightStep ρ) (p,0)
        rw [List.foldl_append]
        change (rightStep ρ z N).2 + 1 ≤ ρ.rightExt s 0 p
        by_cases hStep : z.1 < x
        · have hs : rightStep ρ z N = (x,z.2+1) := by simp [rightStep, hNonly, hStep]
          have hm : y ∈ (ρ.extPositions M).filter (x < ·) := by simp [hy, hXY]
          have hne := List.ne_nil_of_mem hm
          have hsub := hAppendTail ρ J s pre [N,M] hpre hJpos (by simp; omega)
            (by
              intro j hj
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
              rcases hj with rfl | rfl
              · exact ⟨hNOn, by omega⟩
              · exact ⟨hMOn, by omega⟩)
          have hv := le_getD_max?_of_mem (L := (ρ.levelsOn s 0).sublists.map
            (fun ls => (ls.foldl (rightStep ρ) (p,0)).2))
            (List.mem_map.mpr ⟨pre ++ [N,M], List.mem_sublists.mpr hsub, rfl⟩)
          change _ ≤ ρ.rightExt s 0 p at hv
          rw [List.foldl_append] at hv
          change (rightStep ρ (rightStep ρ z N) M).2 ≤ ρ.rightExt s 0 p at hv
          rw [hs] at hv ⊢
          simpa only [rightStep, List.head?_eq_some_head hne] using hv
        · have hs : rightStep ρ z N = z := by simp [rightStep, hNonly, hStep]
          rw [hs]
          exact hBaseAug pre hpre
      have hEach (ls : List ℕ) (hls : ls.Sublist ((norm ρ J N).levelsOn s 0)) :
          (ls.foldl (rightStep (norm ρ J N)) (p,0)).2 + 1 ≤ ρ.rightExt s 0 p := by
        have hall : ∀ j ∈ ls, j ∈ ρ.levels := by
          intro j hj
          simpa only [hLevels] using (List.mem_filter.mp (hls.subset hj)).1
        rw [hFoldRight ρ J N ls hall (p,0)]
        have hf := hls.filter (fun j => decide (mask J N j))
        rw [hSelected ρ J N hJpos hJN hN hNs] at hf
        obtain ⟨pre, tail, he, hpre, htail⟩ := List.sublist_append_iff.mp hf
        rw [he]
        cases tail with
        | nil => simpa only [List.append_nil] using hBaseAug pre hpre
        | cons j tail =>
          have hjN : j = N := by simpa using htail.subset (show j ∈ j :: tail by simp)
          subst j
          cases tail with
          | nil => exact hWithN pre hpre
          | cons b tail =>
            have hl := htail.length_le
            simp at hl
      have hOne : 1 ≤ ρ.rightExt s 0 p := by simpa using hBaseAug [] (List.nil_sublist _)
      have hb : (norm ρ J N).rightExt s 0 p ≤ ρ.rightExt s 0 p - 1 := by
        simp only [rightExt_eq]
        apply getD_max?_le
        intro c hc
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hc
        have hh := hEach ls (List.mem_sublists.mp hls)
        simp only [rightExt_eq] at hh
        omega
      omega
    have hMoreLeft (ρ : Context) (J N M a x y p : ℕ)
        (hJ : J ∈ ρ.levels) (hN : N ∈ ρ.levels) (hM : M ∈ ρ.levels)
        (hJN : J < N) (hNM : N < M)
        (hJs : ρ.sideAt J = s) (hNs : ρ.sideAt N = s) (hMs : ρ.sideAt M = s)
        (ha : a ∈ ρ.extPositions J) (hNonly : ρ.extPositions N = [x]) (hy : y ∈ ρ.extPositions M)
        (hXY : y < x) (hYA : a < y)
        (hyoung : ∀ j ∈ ρ.levelsOn s J, ∀ q ∈ ρ.extPositions j, a < q)
        (hp : a < p) : (norm ρ J N).leftExt s 0 p + 1 ≤ ρ.leftExt s 0 p := by
      have hJpos := one_le_of_mem_levels hJ
      have hJOn : J ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hJ, by simp [hJs]⟩
      have hNOn : N ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
      have hMOn : M ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hM, by simp [hMs]⟩
      have hBaseAug (pre : List ℕ) (hpre : pre.Sublist (ρ.levelsOn s J)) :
          (pre.foldl (leftStep ρ) (p,0)).2 + 1 ≤ ρ.leftExt s 0 p := by
        let z := pre.foldl (leftStep ρ) (p,0)
        have hz : a < z.1 := hEndLeft ρ a pre
          (fun j hj q hq => hyoung j (hpre.subset hj) q hq) (p,0) hp
        have hm : a ∈ (ρ.extPositions J).filter (· < z.1) := by simp [ha, hz]
        have hne := List.ne_nil_of_mem hm
        have hsub := hAppendTail ρ J s pre [J] hpre hJpos (by simp)
          (by
            intro j hj
            have hjJ : j = J := by simpa using hj
            subst j
            exact ⟨hJOn, le_rfl⟩)
        have hv := le_getD_max?_of_mem (L := (ρ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (leftStep ρ) (p,0)).2))
          (List.mem_map.mpr ⟨pre ++ [J], List.mem_sublists.mpr hsub, rfl⟩)
        change _ ≤ ρ.leftExt s 0 p at hv
        rw [List.foldl_append] at hv
        change (leftStep ρ z J).2 ≤ ρ.leftExt s 0 p at hv
        simpa only [leftStep, List.getLast?_eq_some_getLast hne] using hv
      have hWithN (pre : List ℕ) (hpre : pre.Sublist (ρ.levelsOn s J)) :
          ((pre ++ [N]).foldl (leftStep ρ) (p,0)).2 + 1 ≤ ρ.leftExt s 0 p := by
        let z := pre.foldl (leftStep ρ) (p,0)
        rw [List.foldl_append]
        change (leftStep ρ z N).2 + 1 ≤ ρ.leftExt s 0 p
        by_cases hStep : x < z.1
        · have hs : leftStep ρ z N = (x,z.2+1) := by simp [leftStep, hNonly, hStep]
          have hm : y ∈ (ρ.extPositions M).filter (· < x) := by simp [hy, hXY]
          have hne := List.ne_nil_of_mem hm
          have hsub := hAppendTail ρ J s pre [N,M] hpre hJpos (by simp; omega)
            (by
              intro j hj
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
              rcases hj with rfl | rfl
              · exact ⟨hNOn, by omega⟩
              · exact ⟨hMOn, by omega⟩)
          have hv := le_getD_max?_of_mem (L := (ρ.levelsOn s 0).sublists.map
            (fun ls => (ls.foldl (leftStep ρ) (p,0)).2))
            (List.mem_map.mpr ⟨pre ++ [N,M], List.mem_sublists.mpr hsub, rfl⟩)
          change _ ≤ ρ.leftExt s 0 p at hv
          rw [List.foldl_append] at hv
          change (leftStep ρ (leftStep ρ z N) M).2 ≤ ρ.leftExt s 0 p at hv
          rw [hs] at hv ⊢
          simpa only [leftStep, List.getLast?_eq_some_getLast hne] using hv
        · have hs : leftStep ρ z N = z := by simp [leftStep, hNonly, hStep]
          rw [hs]
          exact hBaseAug pre hpre
      have hEach (ls : List ℕ) (hls : ls.Sublist ((norm ρ J N).levelsOn s 0)) :
          (ls.foldl (leftStep (norm ρ J N)) (p,0)).2 + 1 ≤ ρ.leftExt s 0 p := by
        have hall : ∀ j ∈ ls, j ∈ ρ.levels := by
          intro j hj
          simpa only [hLevels] using (List.mem_filter.mp (hls.subset hj)).1
        rw [hFoldLeft ρ J N ls hall (p,0)]
        have hf := hls.filter (fun j => decide (mask J N j))
        rw [hSelected ρ J N hJpos hJN hN hNs] at hf
        obtain ⟨pre, tail, he, hpre, htail⟩ := List.sublist_append_iff.mp hf
        rw [he]
        cases tail with
        | nil => simpa only [List.append_nil] using hBaseAug pre hpre
        | cons j tail =>
          have hjN : j = N := by simpa using htail.subset (show j ∈ j :: tail by simp)
          subst j
          cases tail with
          | nil => exact hWithN pre hpre
          | cons b tail =>
            have hl := htail.length_le
            simp at hl
      have hOne : 1 ≤ ρ.leftExt s 0 p := by simpa using hBaseAug [] (List.nil_sublist _)
      have hb : (norm ρ J N).leftExt s 0 p ≤ ρ.leftExt s 0 p - 1 := by
        simp only [leftExt_eq]
        apply getD_max?_le
        intro c hc
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hc
        have hh := hEach ls (List.mem_sublists.mp hls)
        simp only [leftExt_eq] at hh
        omega
      omega
    have hCaps (ρ : Context) (J N M a x y : ℕ)
        (hJ : J ∈ ρ.levels) (hN : N ∈ ρ.levels) (hM : M ∈ ρ.levels)
        (hJN : J < N) (hNM : N < M)
        (hJs : ρ.sideAt J = s) (hNs : ρ.sideAt N = s) (hMs : ρ.sideAt M = s)
        (ha : a ∈ ρ.extPositions J) (hNonly : ρ.extPositions N = [x]) (hy : y ∈ ρ.extPositions M)
        (dir : Bool) (ho : if dir then x < y ∧ y < a else a < y ∧ y < x)
        (hc : ∀ p ∈ ρ.childPositions, if dir then p < a else a < p)
        (hyoung : ∀ j ∈ ρ.levelsOn s J, ∀ p ∈ ρ.extPositions j, if dir then p < a else a < p)
        (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
        ρ.cupLimit p q ≤ (norm ρ J N).cupLimit p q ∧
        ρ.capLimit p q ≤ (norm ρ J N).capLimit p q := by
      have hPlus : (norm ρ J N).chainExt s p q + 1 ≤ ρ.chainExt s p q := by
        cases dir
        · have ho' : a < y ∧ y < x := ho
          have hl := hMoreLeft ρ J N M a x y p hJ hN hM hJN hNM hJs hNs hMs ha hNonly hy
            ho'.2 ho'.1 (by intro j hj z hz; exact hyoung j hj z hz) (hc p hp)
          have hr := hRightLe ρ J N 0 q s
          dsimp only [chainExt]
          omega
        · have ho' : x < y ∧ y < a := ho
          have hr := hMoreRight ρ J N M a x y q hJ hN hM hJN hNM hJs hNs hMs ha hNonly hy
            ho'.1 ho'.2 (by intro j hj z hz; exact hyoung j hj z hz) (hc q hq)
          have hl := hLeftLe ρ J N 0 p s
          dsimp only [chainExt]
          omega
      have hCl : (norm ρ J N).chainExt Side.lower p q ≤ ρ.chainExt Side.lower p q :=
        Nat.add_le_add (hLeftLe ρ J N 0 p Side.lower) (hRightLe ρ J N 0 q Side.lower)
      have hCu : (norm ρ J N).chainExt Side.upper p q ≤ ρ.chainExt Side.upper p q :=
        Nat.add_le_add (hLeftLe ρ J N 0 p Side.upper) (hRightLe ρ J N 0 q Side.upper)
      have hJl := hJoinLe ρ J N p q Side.lower
      have hJu := hJoinLe ρ J N p q Side.upper
      cases s
      · have ha : (norm ρ J N).a = ρ.a := rfl
        have hu : (norm ρ J N).u = ρ.u - 1 := rfl
        dsimp only [cupLimit, capLimit]
        rw [ha, hu, hK]
        omega
      · have ha : (norm ρ J N).a = ρ.a - 1 := rfl
        have hu : (norm ρ J N).u = ρ.u := rfl
        dsimp only [cupLimit, capLimit]
        rw [ha, hu, hK]
        omega
    have hNormPart (ρ : Context) (keep : List ℕ) (v : Side) (m J N : ℕ) (hJ : 1 ≤ J) :
        norm (ρ.part keep v m) (J+1) (N+1) = (norm ρ J N).part keep v m := by
      have hMax : (m :: ρ.maxima).mapIdx (fun i d => if i+1 < J+1 then d else 0) =
          m :: ρ.maxima.mapIdx (fun i d => if i+1 < J then d else 0) := by
        rw [List.mapIdx_cons]
        have hf : (fun i d : ℕ => if i+1+1 < J+1 then d else 0) =
            (fun i d : ℕ => if i+1 < J then d else 0) := by
          funext i d
          have he : (i+1+1 < J+1) ↔ i+1 < J := by omega
          simp only [he]
        simp only [Nat.zero_add, show 1 < J+1 by omega, if_true, hf]
      have hWords : (norm (ρ.part keep v m) (J+1) (N+1)).word =
          ((norm ρ J N).part keep v m).word := by
        rw [hWord]
        change ((List.range ρ.word.length).map (fun p => match (generalizing := false) ρ.letterAt p with
          | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 v
          | Letter.ext j u => Letter.ext (j+1) u)).map (erase (ρ.part keep v m) (J+1) (N+1)) =
          (List.range (norm ρ J N).word.length).map (fun p => match (generalizing := false) (norm ρ J N).letterAt p with
            | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 v
            | Letter.ext j u => Letter.ext (j+1) u)
        rw [List.map_map, hLen]
        apply List.map_congr_left
        intro p hp
        rw [hLetter]
        simp only [Function.comp_apply]
        cases he : ρ.letterAt p with
        | child =>
          by_cases hpk : p ∈ keep <;> simp [erase, mask, hpk, show 1 < J+1 by omega]
        | ext j u =>
          have hm : mask (J+1) (N+1) (j+1) ↔ mask J N j := by dsimp only [mask]; omega
          by_cases hj : mask J N j
          · have hj' := hm.mpr hj
            simp [erase, hj, hj']
          · have hj' : ¬ mask (J+1) (N+1) (j+1) := fun h => hj (hm.mp h)
            simp [erase, hj, hj', part]
      cases s <;> simp only [norm, part] at hWords ⊢ <;> congr 1
      all_goals first | exact hWords | exact hMax
    have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
        ∀ x j w, (ρ.part keep v m).letterAt x = Letter.ext j w → 1 ≤ j := by
      intro x j w hx
      have hxl : x < ρ.word.length := by
        by_contra h
        have hn := letterAt_of_length_le (ρ.part keep v m)
          (show (ρ.part keep v m).word.length ≤ x by rw [part_word_length]; omega)
        rw [hn] at hx
        cases hx
      cases he : ρ.letterAt x with
      | child =>
        rw [part_letterAt_of_child ρ keep v m hxl he] at hx
        split at hx
        · cases hx
        · cases hx
          omega
      | ext oldLevel oldSide =>
        rw [part_letterAt_of_ext ρ keep v m hxl he] at hx
        cases hx
        omega
    have hNextBoundary (ρ : Context)
        (hPos : ∀ p j w, ρ.letterAt p = Letter.ext j w → 1 ≤ j)
        (L x : ℕ) (hL : L ∈ ρ.levels) (dir : Bool)
        (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
          if dir then p < x else x < p)
        (keep : List ℕ) (v : Side) (m : ℕ) :
        (∀ p ∈ (ρ.part keep v m).childPositions, if dir then p < x else x < p) ∧
        (∀ j ∈ (ρ.part keep v m).levelsOn ((ρ.part keep v m).sideAt (L+1)) (L+1),
          ∀ p ∈ (ρ.part keep v m).extPositions j, if dir then p < x else x < p) := by
      have hL1 := one_le_of_mem_levels hL
      constructor
      · intro p hp
        rw [part_childPositions] at hp
        exact hc p (List.mem_filter.mp hp).1
      · intro j hj p hp
        have hj1 := (one_le_of_mem_levelsOn hj).1
        by_cases he : j = 1
        · subst j
          rw [part_extPositions_one hPos keep v m] at hp
          exact hc p (List.mem_filter.mp hp).1
        · let i := j-1
          have hi : 1 ≤ i := by dsimp [i]; omega
          have he : j = i+1 := by dsimp [i]; omega
          rw [he] at hj hp
          have hjLevel : i+1 ∈ (ρ.part keep v m).levels := (List.mem_filter.mp hj).1
          rw [part_levels] at hjLevel
          have hiLevel : i ∈ ρ.levels := by
            rcases List.mem_cons.mp hjLevel with h | h
            · omega
            · obtain ⟨z, hz, hzi⟩ := List.mem_map.mp h
              have hz' : z = i := by omega
              simpa only [hz'] using hz
          have hjc : (ρ.part keep v m).sideAt (i+1) = (ρ.part keep v m).sideAt (L+1) ∧
              (L+1 = 0 ∨ i+1 < L+1) := of_decide_eq_true (List.mem_filter.mp hj).2
          rw [part_sideAt_succ ρ keep v m hi, part_sideAt_succ ρ keep v m hL1] at hjc
          have hiOn : i ∈ ρ.levelsOn (ρ.sideAt L) L := by
            apply List.mem_filter.mpr
            refine ⟨hiLevel, ?_⟩
            apply decide_eq_true
            exact ⟨hjc.1, Or.inr (by omega)⟩
          rw [part_extPositions_succ ρ keep v m hi] at hp
          exact hy i hiOn p hp
    have hBase (ρ : Context) (J N M a x y : ℕ)
        (hJ : J ∈ ρ.levels) (hN : N ∈ ρ.levels) (hM : M ∈ ρ.levels)
        (hJN : J < N) (hNM : N < M)
        (hJs : ρ.sideAt J = s) (hNs : ρ.sideAt N = s) (hMs : ρ.sideAt M = s)
        (ha : a ∈ ρ.extPositions J) (hNonly : ρ.extPositions N = [x]) (hy : y ∈ ρ.extPositions M)
        (dir : Bool) (ho : if dir then x < y ∧ y < a else a < y ∧ y < x)
        (hc : ∀ p ∈ ρ.childPositions, if dir then p < a else a < p)
        (hyoung : ∀ j ∈ ρ.levelsOn s J, ∀ p ∈ ρ.extPositions j, if dir then p < a else a < p) :
        ρ.base ≤ (norm ρ J N).base := by
      rw [base_eq_baseOf, base_eq_baseOf, hChild]
      cases hh : ρ.childPositions.head? with
      | none => exact le_rfl
      | some p =>
        have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        have h := hCaps ρ J N M a x y hJ hN hM hJN hNM hJs hNs hMs ha hNonly hy dir ho hc hyoung p p hp hp
        simpa only [hK] using baseOf_mono (k := ρ.k) h.1 h.2
    have hFuel : ∀ fuel (ρ : Context),
        (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
        ∀ (J N M a x y : ℕ), J ∈ ρ.levels → N ∈ ρ.levels → M ∈ ρ.levels → J < N → N < M →
        ρ.sideAt J = s → ρ.sideAt N = s → ρ.sideAt M = s →
        a ∈ ρ.extPositions J → ρ.extPositions N = [x] → y ∈ ρ.extPositions M →
        ∀ dir : Bool, (if dir then x < y ∧ y < a else a < y ∧ y < x) →
        (∀ p ∈ ρ.childPositions, if dir then p < a else a < p) →
        (∀ j ∈ ρ.levelsOn s J, ∀ p ∈ ρ.extPositions j, if dir then p < a else a < p) →
        boundFuel fuel ρ ≤ boundFuel fuel (norm ρ J N) := by
      intro fuel
      induction fuel with
      | zero => intro ρ hPos J N M a x y hJ hN hM hJN hNM hJs hNs hMs ha hNx hy dir ho hc hYoung; exact le_rfl
      | succ fuel ih =>
        intro ρ hPos J N M a x y hJ hN hM hJN hNM hJs hNs hMs ha hNx hy dir ho hc hYoung
        have hJ1 := one_le_of_mem_levels hJ
        have hN1 := one_le_of_mem_levels hN
        have hM1 := one_le_of_mem_levels hM
        have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
            boundFuel fuel (ρ.part keep v m) ≤ boundFuel fuel ((norm ρ J N).part keep v m) := by
          have hLevel (L : ℕ) (hL : L ∈ ρ.levels) : L+1 ∈ (ρ.part keep v m).levels := by
            rw [part_levels]
            exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L,hL,rfl⟩)
          have ha' : a ∈ (ρ.part keep v m).extPositions (J+1) := by rw [part_extPositions_succ ρ keep v m hJ1]; exact ha
          have hx' : (ρ.part keep v m).extPositions (N+1) = [x] := by rw [part_extPositions_succ ρ keep v m hN1, hNx]
          have hy' : y ∈ (ρ.part keep v m).extPositions (M+1) := by rw [part_extPositions_succ ρ keep v m hM1]; exact hy
          have hd := hNextBoundary ρ hPos J a hJ dir hc (by rw [hJs]; exact hYoung) keep v m
          have hYoung' : ∀ j ∈ (ρ.part keep v m).levelsOn s (J+1),
              ∀ p ∈ (ρ.part keep v m).extPositions j, if dir then p < a else a < p := by
            have hh := hd.2
            rw [part_sideAt_succ ρ keep v m hJ1, hJs] at hh
            exact hh
          have hh := ih (ρ.part keep v m) (hPartPositive ρ keep v m)
            (J+1) (N+1) (M+1) a x y (hLevel J hJ) (hLevel N hN) (hLevel M hM) (by omega) (by omega)
            ((part_sideAt_succ ρ keep v m hJ1).trans hJs)
            ((part_sideAt_succ ρ keep v m hN1).trans hNs)
            ((part_sideAt_succ ρ keep v m hM1).trans hMs) ha' hx' hy' dir ho hd.1 hYoung'
          rw [hNormPart ρ keep v m J N hJ1] at hh
          exact hh
        simp only [boundFuel, hRuns, hChild, hBlocks, hK]
        split_ifs
        · exact hBase ρ J N M a x y hJ hN hM hJN hNM hJs hNs hMs ha hNx hy dir ho hc hYoung
        · apply Ctx.getD_max?_le_of_forall
          intro x hx
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
          obtain ⟨keep, hkeep, d, hd, hx⟩ := hx
          rcases hx with rfl | rfl
          · refine ⟨_, ?_, Nat.add_le_add (hParts _ _ _) (hParts _ _ _)⟩
            simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
            exact ⟨keep, hkeep, d, hd, Or.inl rfl⟩
          · refine ⟨_, ?_, Nat.add_le_add (hParts _ _ _) (hParts _ _ _)⟩
            simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
            exact ⟨keep, hkeep, d, hd, Or.inr rfl⟩
    refine ⟨hPos σ J N hpositive, hChild σ J N, hLevels σ J N,
      (hSide σ J N N hN (Or.inr rfl)).trans hNs, ?_,
      fun fuel => hFuel fuel σ hpositive J N M a x y hJ hN hM hJN hNM hJs hNs hMs ha hNonly hy
        direction horder hboundary hyoung, ?_⟩
    · rw [hExt σ J N N hN, if_pos (show mask J N N from Or.inr rfl), hNonly]
    · simpa only [bound, hChild] using hFuel (σ.childPositions.length+1) σ hpositive J N M a x y
        hJ hN hM hJN hNM hJs hNs hMs ha hNonly hy direction horder hboundary hyoung

  classical
  let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  let β := σ.part keep t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ (w + 1).choose 2 + w - 1) ∧ α.bound + β.bound ≤ (w + 1).choose 2 + w - 1
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ rest := by
    simp only [α, part_childPositions, rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hChildβ (p : ℕ) : p ∈ β.childPositions ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [β, part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ rest := by
    rw [part_extPositions_one hpositive]
  have hQα : q₀ ∈ α.extPositions 1 := (hExtα q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
  have hLβ : l ∈ β.extPositions 1 := (hExtβ l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
  have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive rest s m hQα
  have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t n hLβ
  have hPositivePart (ks : List ℕ) (v : Side) (q₀ : ℕ) :
      ∀ p j z, (σ.part ks v q₀).letterAt p = Letter.ext j z → 1 ≤ j := by
    intro p j z hp
    have hpl : p < σ.word.length := by
      by_contra h
      have hh := letterAt_of_length_le (σ.part ks v q₀)
        (show (σ.part ks v q₀).word.length ≤ p by rw [part_word_length]; omega)
      rw [hh] at hp
      cases hp
    cases he : σ.letterAt p with
    | child =>
      rw [part_letterAt_of_child σ ks v q₀ hpl he] at hp
      split at hp
      · cases hp
      · cases hp; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ ks v q₀ hpl he] at hp
      cases hp; omega
  have hPosα := hPositivePart rest s m
  have hPosβ := hPositivePart keep t n
  have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
  have hNpos := one_le_of_mem_levels hN
  have hNα : N + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNβ : N + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNsα : α.sideAt (N + 1) = s := (part_sideAt_succ σ rest s m hNpos).trans hNs
  have hNsβ : β.sideAt (N + 1) = s := (part_sideAt_succ σ keep t n hNpos).trans hNs
  have hXα : x ∈ α.extPositions (N + 1) := by rw [part_extPositions_succ σ rest s m hNpos]; exact hx
  have hXβ : x ∈ β.extPositions (N + 1) := by rw [part_extPositions_succ σ keep t n hNpos]; exact hx
  have hw : 1 ≤ w := hwidth
  have hMpos := one_le_of_mem_levels hM
  have hMα : M + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hMβ : M + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hMsα : α.sideAt (M + 1) = s := (part_sideAt_succ σ rest s m hMpos).trans hMs
  have hMsβ : β.sideAt (M + 1) = s := (part_sideAt_succ σ keep t n hMpos).trans hMs
  have hYα : y ∈ α.extPositions (M + 1) := by rw [part_extPositions_succ σ rest s m hMpos]; exact hy
  have hYβ : y ∈ β.extPositions (M + 1) := by rw [part_extPositions_succ σ keep t n hMpos]; exact hy
  have hAtLevel (j i p : ℕ) (hp : p ∈ σ.extPositions j) (hp' : p ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hp).2
    have hi := (List.mem_filter.mp hp').2
    cases hletter : σ.letterAt p <;> simp [hletter] at hj hi
    omega
  have hActual : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j,
      (j = N ∧ p = x) ∨ (j = M ∧ p = y) := by
    intro j hj p hp
    rcases hchosen j hj p hp with hpx | hpy
    · exact Or.inl ⟨hAtLevel j N x (by simpa only [hpx] using hp) hx, hpx⟩
    · exact Or.inr ⟨hAtLevel j M y (by simpa only [hpy] using hp) hy, hpy⟩
  have hBetaActual : ∀ j ∈ β.levelsOn s 0, ∀ p ∈ β.extPositions j,
      (j = N + 1 ∧ p = x) ∨ (j = M + 1 ∧ p = y) := by
    have hs : β.sideAt 1 ≠ s := by rw [hSideβ]; exact Ne.symm hne
    intro j hj p hp
    rw [part_levelsOn_other_zero hs] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [part_extPositions_succ σ keep t n (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
    rcases hActual i hi p hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hBetaBelow (top j : ℕ) (hj : j ∈ β.levelsOn s top) :
      j ∈ β.levelsOn s 0 ∧ (top = 0 ∨ j < top) := by
    have hh := List.mem_filter.mp hj
    have hp := of_decide_eq_true hh.2
    exact ⟨List.mem_filter.mpr ⟨hh.1, by simp [hp.1]⟩, hp.2⟩
  obtain ⟨direction, hOrder, hOutside, hEnd⟩ : ∃ direction : Bool,
      (if direction then x < y ∧ y < q₀ else q₀ < y ∧ y < x) ∧
      (∀ p ∈ keep, if direction then y < p else p < y) ∧
      (∀ p ∈ keep, ∀ q ∈ rest, if direction then q < p else p < q) := by
    rcases horder with ⟨hOut, hXY, hEnd⟩ | ⟨hOut, hYX, hEnd⟩
    · exact ⟨true, ⟨hXY, hOut q₀ hq₀⟩, hOut,
        fun p hp q hq => hEnd p hp q ((hRest q).mp hq).1 ((hRest q).mp hq).2⟩
    · exact ⟨false, ⟨hOut q₀ hq₀, hYX⟩, hOut,
        fun p hp q hq => hEnd p hp q ((hRest q).mp hq).1 ((hRest q).mp hq).2⟩
  have hNonly : σ.extPositions N = [x] := by
    apply (List.pairwise_lt_range.filter _).eq_of_mem_iff (by simp)
    intro p
    simp only [List.mem_singleton]
    constructor
    · intro hp
      have hNon : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
      rcases hActual N hNon p hp with ⟨_, hpx⟩ | ⟨hNM', _⟩
      · exact hpx
      · omega
    · rintro rfl; exact hx
  have hNonlyα : α.extPositions (N + 1) = [x] := by
    rw [part_extPositions_succ σ rest s m hNpos, hNonly]
  let κ : Context := { α with
    word := α.word.map (fun z => match (generalizing := false) z with
      | Letter.child => Letter.child
      | Letter.ext j v => if j < 1 ∨ j = N + 1 then Letter.ext j v
          else Letter.ext (α.maxima.length + 1) v)
    maxima := α.maxima.mapIdx (fun i m => if i + 1 < 1 then m else 0) }
  let τ : Context := match (generalizing := false) s with
    | Side.lower => { κ with u := α.u - 1 }
    | Side.upper => { κ with a := α.a - 1 }
  have hNormalize := ctx_three_marker_boundary_collapse_upper_normalize α hPosα s 1
    (N + 1) (M + 1) q₀ x y hOneα hNα hMα (by omega) (by omega)
    hSideα hNsα hMsα hQα hNonlyα hYα direction hOrder
    (by intro p hp; exact hEnd q₀ hq₀ p ((hChildα p).mp hp))
    (by simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true])
  change (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
    τ.childPositions = α.childPositions ∧ τ.levels = α.levels ∧
    τ.sideAt (N + 1) = s ∧ τ.extPositions (N + 1) = [x] ∧
    (∀ fuel, boundFuel fuel α ≤ boundFuel fuel τ) ∧ α.bound ≤ τ.bound at hNormalize
  obtain ⟨hPosτ, hChildτ, hLevelsτ, hSideτ, hExtτ, hFuelτ, hBoundτ⟩ := hNormalize
  have hChosenτ : (match (generalizing := false) s with | Side.lower => τ.u | Side.upper => τ.a) ≤ 4 := by
    cases s
    · change σ.u - 1 ≤ 4
      change σ.u ≤ 5 at hglobal
      omega
    · change σ.a - 1 ≤ 4
      change σ.a ≤ 5 at hglobal
      omega
  have hOppτ : (match (generalizing := false) t with | Side.lower => τ.u | Side.upper => τ.a) =
      (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · rfl
    · rfl
    · exact False.elim (hne rfl)
  have hOwn : (∀ fuel, boundFuel fuel α ≤ 2 * w - 1) ∧ α.bound ≤ 2 * w - 1 := by
    have hh := ctx_one_level_refined_potential_bound τ hPosτ s t hne (N + 1) x
      (by rw [hLevelsτ]; exact hNα) hSideτ (by rw [hExtτ]; simp) hChosenτ
    have hBounds : (∀ fuel, boundFuel fuel τ ≤ 2 * w - 1) ∧ τ.bound ≤ 2 * w - 1 := by
      cases s <;> cases t
      · exact False.elim (hne rfl)
      · exact ⟨hh.2.2.1, hh.2.2.2⟩
      · exact ⟨hh.2.2.1, hh.2.2.2⟩
      · exact False.elim (hne rfl)
    exact ⟨fun fuel => (hFuelτ fuel).trans (hBounds.1 fuel), hBoundτ.trans hBounds.2⟩
  let active := β.childPositions.toFinset.filter (fun p => 0 < β.cupLimit p p ∧ 0 < β.capLimit p p)
  let I (p : ℕ) := Finset.Icc (β.leftExt t 0 p + 1) (w - β.rightExt t 0 p)
  let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
  let pairs := active.biUnion (fun p => Q (I p))
  have hCardPairs (T : Finset ℕ) : (Q T).card = (T.card + 1).choose 2 := by
    rw [← Finset.card_sym2]
    apply Finset.card_bij (fun z _ => Sym2.mk z.1 z.2)
    · intro z hz
      exact Finset.mk_mem_sym2_iff.mpr (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
    · intro p hp q hq he
      have hpl := (Finset.mem_filter.mp hp).2
      have hql := (Finset.mem_filter.mp hq).2
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · apply Prod.ext <;> omega
    · intro z hz
      induction z using Sym2.ind with
      | h a b =>
        obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hz
        by_cases hab : a ≤ b
        · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
        · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩, Sym2.eq_swap⟩
  have hOneLeftTop (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRightTop (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hOneβ : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
  have hOneOn : 1 ∈ β.levelsOn t 0 := List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ]⟩
  have hLeft : ∀ p ∈ β.childPositions, (if direction then 1 else 0) ≤ β.leftExt t 0 p := by
    intro p hp
    cases hd : direction
    · simp [hd]
    · have hh := hEnd p ((hChildβ p).mp hp).2 l ((hRest l).mpr ⟨hl, hlnot⟩)
      have hlp : l < p := by simpa [hd] using hh
      simpa [hd] using hOneLeftTop β t 0 1 p l hOneOn hLβ hlp
  have hRight : ∀ p ∈ β.childPositions, (if direction then 0 else 1) ≤ β.rightExt t 0 p := by
    intro p hp
    cases hd : direction
    · have hh := hEnd p ((hChildβ p).mp hp).2 l ((hRest l).mpr ⟨hl, hlnot⟩)
      have hpl : p < l := by simpa [hd] using hh
      simpa [hd] using hOneRightTop β t 0 1 p l hOneOn hLβ hpl
    · simp [hd]
  have hBoundary : ∀ p ∈ β.childPositions, if !direction then p < x else x < p := by
    intro p hp
    have hh := hOutside p ((hChildβ p).mp hp).2
    cases hd : direction
    · have hpY : p < y := by simpa [hd] using hh
      have ho : q₀ < y ∧ y < x := by simpa [hd] using hOrder
      have hyX := ho.2
      simpa [hd] using (show p < x by omega)
    · have hyP : y < p := by simpa [hd] using hh
      have ho : x < y ∧ y < q₀ := by simpa [hd] using hOrder
      have hxY := ho.1
      simpa [hd] using (show x < p by omega)
  have hYoung : ∀ j ∈ β.levelsOn (β.sideAt (N + 1)) (N + 1),
      ∀ p ∈ β.extPositions j, if !direction then p < x else x < p := by
    intro j hj p hp
    rw [hNsβ] at hj
    have hj' := hBetaBelow (N + 1) j hj
    rcases hBetaActual j hj'.1 p hp with ⟨hjN, _⟩ | ⟨hjM, _⟩ <;> omega
  have hOther : (∀ fuel, boundFuel fuel β ≤ w.choose 2) ∧ β.bound ≤ w.choose 2 := by
    have hSmallG : min ((match (generalizing := false) β.sideAt (N + 1) with
        | Side.lower => β.u | Side.upper => β.a) - 1) (β.k - β.maximumAt (N + 1)) ≤ 4 := by
      rw [hNsβ]
      change min ((match (generalizing := false) s with | Side.lower => σ.u | Side.upper => σ.a) - 1) _ ≤ 4
      omega
    have hh := ctx_active_boundary_marker_rank_pair_union_bound β hPosβ (N + 1) x hNβ hXβ
      (!direction) (fun p hp _ => hBoundary p hp) hYoung t (by rw [hNsβ]; exact hne) hSmallG
    change (∀ fuel, boundFuel fuel β ≤ pairs.card) ∧ β.bound ≤ pairs.card at hh
    let L := if direction then 2 else 1
    let U := if direction then w else w - 1
    have hInterval (p : ℕ) (hp : p ∈ active) : I p ⊆ Finset.Icc L U := by
      intro z hz
      have hc : p ∈ β.childPositions := List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
      have hl' := hLeft p hc
      have hr' := hRight p hc
      have hz' := Finset.mem_Icc.mp hz
      apply Finset.mem_Icc.mpr
      cases hd : direction
      · have hr1 : 1 ≤ β.rightExt t 0 p := by simpa [hd] using hr'
        simpa only [L, U, hd, Bool.false_eq_true, ite_false] using
          (show 1 ≤ z ∧ z ≤ w - 1 from ⟨by omega, by omega⟩)
      · have hl1 : 1 ≤ β.leftExt t 0 p := by simpa [hd] using hl'
        simpa only [L, U, hd, Bool.true_eq, ite_true] using
          (show 2 ≤ z ∧ z ≤ w from ⟨by omega, by omega⟩)
    have hSub : pairs ⊆ Q (Finset.Icc L U) := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hz' := Finset.mem_filter.mp hz
      obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hz'.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hInterval p hp hza, hInterval p hp hzb⟩, hz'.2⟩
    have hcard : (Q (Finset.Icc L U)).card = w.choose 2 := by
      rw [hCardPairs]
      have hi : (Finset.Icc L U).card = w - 1 := by
        cases hd : direction
        · simp only [L, U, hd, Bool.false_eq_true, ite_false, Nat.card_Icc]
          omega
        · simp only [L, U, hd, Bool.true_eq, ite_true, Nat.card_Icc]
          omega
      rw [hi, show w - 1 + 1 = w by omega]
    have hBudget := (Finset.card_le_card hSub).trans_eq hcard
    exact ⟨fun fuel => (hh.1 fuel).trans hBudget, hh.2.trans hBudget⟩
  have hBudget : (2 * w - 1) + w.choose 2 ≤ (w + 1).choose 2 + w - 1 := by
    have hc : (w + 1).choose 2 = w + w.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ w 1
    omega
  exact ⟨fun f g => (Nat.add_le_add (hOwn.1 f) (hOther.1 g)).trans hBudget,
    (Nat.add_le_add hOwn.2 hOther.2).trans hBudget⟩

end ErdosSzekeres
