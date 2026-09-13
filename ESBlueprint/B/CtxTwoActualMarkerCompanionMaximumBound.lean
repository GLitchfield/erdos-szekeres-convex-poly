import ESBlueprint.B.CtxTwoActualMarkerSharpPotentialArbitraryHistory
import ESBlueprint.B.CtxOldestAxisMaximumEraseNormalize
import ESBlueprint.B.CtxEraseLevelBoundMono
import ESBlueprint.B.CtxBoundLeOneOfClearUnitAxis
import ESBlueprint.B.CtxBoundLeSumPointBases
import ESBlueprint.B.CtxPartPositiveLetters

namespace ErdosSzekeres

/-- Sharpen the companion square to the checked sharp triangular-linear two-marker potential. Erase unselected source levels while transporting two distinct actual chosen markers and commuting erasure with the companion part. At exact selected depth two, the new opposite level one is terminal on its axis; checked oldest-axis maximum erasure caps the opposite global by k-n while retaining both chosen markers, after which the arbitrary-history two-actual-marker sharp potential applies. Normalized opposite widths zero and one are handled respectively by zero point bases and the checked clear unit-axis bound. Positive labels, distinct axes, two actual indexed chosen levels, chosen global at most five, and retained/removed child witnesses are explicit. Kept lists, source history and maxima, new maxima, opposite global and coupling are unrestricted. Every fuel approximation and the full companion are at most choose(budget+1,2)+budget-1 for budget=k-n-1. Pre-draft es searches for 'two actual marker companion maximum triangular linear', 'erase opposite history preserve two chosen markers companion', 'oldest opposite maximum two marker potential', and 'budget zero companion maximum bound' returned no results.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_actual_marker_companion_maximum_bound (σ : Ctx.Context)
  (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep) :
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  let budget := σ.k - n - 1
  (∀ fuel, Ctx.Context.boundFuel fuel B ≤ (budget + 1).choose 2 + budget - 1) ∧
    B.bound ≤ (budget + 1).choose 2 + budget - 1 := by
  set_option maxHeartbeats 8000000 in
    classical
    let G (ρ : Ctx.Context) (v : Ctx.Side) := match v with
      | Ctx.Side.lower => ρ.u
      | Ctx.Side.upper => ρ.a
    let P (b : ℕ) := (b + 1).choose 2 + b - 1
    let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
    let letter (D L : ℕ) : Ctx.Letter → Ctx.Letter := fun z => match z with
      | Ctx.Letter.child => Ctx.Letter.child
      | Ctx.Letter.ext j v => Ctx.Letter.ext (idx D L j) v
    let norm (ρ : Ctx.Context) (L : ℕ) : Ctx.Context :=
      { ρ with word := ρ.word.map (letter ρ.maxima.length L), maxima := ρ.maxima.eraseIdx (L - 1) }
    let up (L j : ℕ) := if j < L then j else j + 1
    have hLevelMem (ρ : Ctx.Context) (j : ℕ) :
        j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
      simp only [Ctx.Context.levels, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        omega
      · intro hj
        exact ⟨j - 1, by omega, by omega⟩
    have hLen (ρ : Ctx.Context) (L : ℕ) : (norm ρ L).word.length = ρ.word.length := by
      simp only [norm, List.length_map]
    have hLetter (ρ : Ctx.Context) (L r : ℕ) :
        (norm ρ L).letterAt r = letter ρ.maxima.length L (ρ.letterAt r) := by
      simp only [norm, Ctx.Context.letterAt, List.getElem?_map]
      cases ρ.word[r]? <;> rfl
    have hIsChild (ρ : Ctx.Context) (L r : ℕ) :
        (norm ρ L).letterAt r = Ctx.Letter.child ↔ ρ.letterAt r = Ctx.Letter.child := by
      rw [hLetter]
      cases ρ.letterAt r <;> simp [letter]
    have hChild (ρ : Ctx.Context) (L : ℕ) :
        (norm ρ L).childPositions = ρ.childPositions := by
      simp only [Ctx.Context.childPositions, hLen, hIsChild]
    have hDepth (ρ : Ctx.Context) (L : ℕ) (hL : L ∈ ρ.levels) :
        (norm ρ L).maxima.length = ρ.maxima.length - 1 := by
      have hh := (hLevelMem ρ L).mp hL
      exact List.length_eraseIdx_of_lt (by omega)
    have hLive (ρ : Ctx.Context) (L j : ℕ) (hL : L ∈ ρ.levels)
        (hj : j ∈ (norm ρ L).levels) : up L j ∈ ρ.levels := by
      have hLB := (hLevelMem ρ L).mp hL
      have hjB := (hLevelMem (norm ρ L) j).mp hj
      rw [hDepth ρ L hL] at hjB
      apply (hLevelMem ρ _).mpr
      dsimp only [up]
      split_ifs <;> omega
    have hIndex (D L i j : ℕ) (hL : 1 ≤ L) (hLD : L ≤ D)
        (hj : 1 ≤ j) (hjD : j < D) : idx D L i = j ↔ i = up L j := by
      dsimp [idx, up]
      split_ifs <;> omega
    have hExt (ρ : Ctx.Context) (L j : ℕ) (hL : L ∈ ρ.levels)
        (hj : j ∈ (norm ρ L).levels) :
        (norm ρ L).extPositions j = ρ.extPositions (up L j) := by
      have hLB := (hLevelMem ρ L).mp hL
      have hjB := (hLevelMem (norm ρ L) j).mp hj
      rw [hDepth ρ L hL] at hjB
      simp only [Ctx.Context.extPositions, hLen, hLetter]
      apply List.filter_congr
      intro r _
      cases ρ.letterAt r with
      | child => rfl
      | ext i v =>
          simp only [letter, hIndex _ _ i j hLB.1 hLB.2 hjB.1 (by omega)]
    have hSide (ρ : Ctx.Context) (L j : ℕ) (hL : L ∈ ρ.levels)
        (hj : j ∈ (norm ρ L).levels) :
        (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
      simp only [Ctx.Context.sideAt, hExt ρ L j hL hj]
      cases hh : (ρ.extPositions (up L j)).head? with
      | none => rfl
      | some r =>
          dsimp only
          rw [hLetter]
          cases ρ.letterAt r <;> rfl
    have hPositive (ρ : Ctx.Context) (L : ℕ) (hL : L ∈ ρ.levels)
        (hPos : ∀ r j v, ρ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j) :
        ∀ r j v, (norm ρ L).letterAt r = Ctx.Letter.ext j v → 1 ≤ j := by
      intro r j v hj
      rw [hLetter] at hj
      have hLB := (hLevelMem ρ L).mp hL
      cases he : ρ.letterAt r with
      | child => simp only [he, letter] at hj; cases hj
      | ext i z =>
          rw [he] at hj
          have hi := hPos r i z he
          have hnew : 1 ≤ idx ρ.maxima.length L i := by
            dsimp only [idx]
            split_ifs <;> omega
          change Ctx.Letter.ext (idx ρ.maxima.length L i) z = Ctx.Letter.ext j v at hj
          cases hj
          exact hnew
    have hNormPart (ρ : Ctx.Context) (keep : List ℕ) (v : Ctx.Side)
        (c L : ℕ) (hL : 1 ≤ L) :
        norm (ρ.part keep v c) (L + 1) = (norm ρ L).part keep v c := by
      have hi (j : ℕ) :
          idx (ρ.maxima.length + 1) (L + 1) (j + 1) = idx ρ.maxima.length L j + 1 := by
        dsimp [idx]
        split_ifs <;> omega
      have hnew : idx (ρ.maxima.length + 1) (L + 1) 1 = 1 := by
        simp [idx]
        omega
      have hm : (c :: ρ.maxima).eraseIdx (L + 1 - 1) =
          c :: ρ.maxima.eraseIdx (L - 1) := by
        rw [show L + 1 - 1 = (L - 1) + 1 by omega, List.eraseIdx_cons_succ]
      have hw : (norm (ρ.part keep v c) (L + 1)).word =
          ((norm ρ L).part keep v c).word := by
        change ((ρ.part keep v c).word.map (letter (c :: ρ.maxima).length (L + 1))) =
          (List.range (norm ρ L).word.length).map (fun r => match (norm ρ L).letterAt r with
            | Ctx.Letter.child => if r ∈ keep then Ctx.Letter.child else Ctx.Letter.ext 1 v
            | Ctx.Letter.ext j w => Ctx.Letter.ext (j + 1) w)
        rw [hLen]
        simp only [Ctx.Context.part, List.map_map, List.length_cons, Function.comp_def]
        apply List.map_congr_left
        intro r _
        rw [hLetter]
        cases ρ.letterAt r with
        | child => by_cases hr : r ∈ keep <;> simp [hr, letter, hnew]
        | ext j w => simp only [letter, hi]
      change Ctx.Context.mk ρ.a ρ.u ρ.k _ ((c :: ρ.maxima).eraseIdx (L + 1 - 1)) =
        Ctx.Context.mk ρ.a ρ.u ρ.k _ (c :: ρ.maxima.eraseIdx (L - 1))
      rw [hm]
      exact congrArg
        (fun word => Ctx.Context.mk ρ.a ρ.u ρ.k word (c :: ρ.maxima.eraseIdx (L - 1))) hw
    have hPartMono (ρ : Ctx.Context) (L : ℕ) (hL : L ∈ ρ.levels)
        (keep : List ℕ) (v : Ctx.Side) (c : ℕ) :
        (ρ.part keep v c).bound ≤ ((norm ρ L).part keep v c).bound := by
      have hnext : L + 1 ∈ (ρ.part keep v c).levels := by
        rw [Ctx.Context.part_levels]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L, hL, rfl⟩)
      have hh := (ctx_erase_level_bound_mono (ρ.part keep v c) (L + 1) hnext).2.2
      change (ρ.part keep v c).bound ≤ (norm (ρ.part keep v c) (L + 1)).bound at hh
      rw [hNormPart ρ keep v c L (Ctx.Context.one_le_of_mem_levels hL)] at hh
      exact hh
    have hFuelFull (ρ : Ctx.Context) (fuel : ℕ) :
        Ctx.Context.boundFuel fuel ρ ≤ ρ.bound := by
      have hh := Ctx.Context.boundFuel_mono
        (Nat.le_max_left fuel (ρ.childPositions.length + 1)) ρ
      rw [Ctx.Context.boundFuel_eq_bound ρ (Nat.le_max_right _ _)] at hh
      exact hh
    have hZero (ρ : Ctx.Context)
        (hz : ∀ r ∈ ρ.childPositions, ρ.cupLimit r r = 0 ∨ ρ.capLimit r r = 0) :
        ρ.bound = 0 := by
      have hs : (ρ.childPositions.map
          (fun r => Ctx.Context.baseOf (ρ.cupLimit r r) (ρ.capLimit r r) ρ.k)).sum = 0 := by
        apply List.sum_eq_zero
        intro z hzmem
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hzmem
        simp only [Ctx.Context.baseOf, if_pos (hz r hr)]
      exact Nat.eq_zero_of_le_zero ((ctx_bound_le_sum_point_bases ρ).trans_eq hs)
    have hBase (ρ : Ctx.Context)
        (hPos : ∀ r j v, ρ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j)
        (hdepth : ρ.maxima.length = 2)
        (N M x y : ℕ) (hN : N ∈ ρ.levels) (hM : M ∈ ρ.levels) (hNM : N < M)
        (hNs : ρ.sideAt N = s) (hMs : ρ.sideAt M = s)
        (hx : x ∈ ρ.extPositions N) (hy : y ∈ ρ.extPositions M)
        (hGs : G ρ s ≤ 5) (keep : List ℕ) (m n p q : ℕ)
        (hp : p ∈ (ρ.part keep s m).childPositions)
        (hq : q ∈ ρ.childPositions) (hRemoved : q ∉ keep) :
        let B := ρ.part (ρ.childPositions.filter (· ∉ keep)) t n
        let budget := ρ.k - n - 1
        B.bound ≤ P budget := by
      have hNB := (hLevelMem ρ N).mp hN
      have hMB := (hLevelMem ρ M).mp hM
      have hN1 : N = 1 := by omega
      have hM2 : M = 2 := by omega
      subst N
      subst M
      let rest := ρ.childPositions.filter (· ∉ keep)
      let B := ρ.part rest t n
      let budget := ρ.k - n - 1
      change B.bound ≤ P budget
      have hPosB : ∀ r j v, B.letterAt r = Ctx.Letter.ext j v → 1 ≤ j :=
        ctx_part_positive_letters ρ rest t n
      have hpa : p ∈ ρ.childPositions ∧ p ∈ keep := by
        simpa only [Ctx.Context.part_childPositions, List.mem_filter, decide_eq_true_eq] using hp
      have hSourceLevels : ρ.levels = [1, 2] := by
        norm_num [Ctx.Context.levels, hdepth, List.range_succ]
      have hBdepth : B.maxima.length = 3 := by simp [B, Ctx.Context.part, hdepth]
      have hBlevels : B.levels = [1, 2, 3] := by
        simp [B, Ctx.Context.part_levels, hSourceLevels]
      have hBlevel : 1 ∈ B.levels := by simp [hBlevels]
      have hBside : B.sideAt 1 = t := by
        apply Ctx.Context.part_sideAt_one_of_mem hPos rest t n (q := p)
        rw [Ctx.Context.part_extPositions_one hPos rest t n]
        exact List.mem_filter.mpr ⟨hpa.1, by simp [rest, hpa.2]⟩
      have hBsideTwo : B.sideAt 2 = s :=
        (Ctx.Context.part_sideAt_succ ρ rest t n (by decide : 1 ≤ 1)).trans hNs
      have hBsideThree : B.sideAt 3 = s :=
        (Ctx.Context.part_sideAt_succ ρ rest t n (by decide : 1 ≤ 2)).trans hMs
      have hBextTwo : B.extPositions 2 = ρ.extPositions 1 :=
        Ctx.Context.part_extPositions_succ ρ rest t n (by decide : 1 ≤ 1)
      have hBextThree : B.extPositions 3 = ρ.extPositions 2 :=
        Ctx.Context.part_extPositions_succ ρ rest t n (by decide : 1 ≤ 2)
      have hterminal : ∀ j ∈ B.levelsOn (B.sideAt 1) 0, j ≤ 1 := by
        intro j hj
        have hmem : j = 1 ∨ j = 2 ∨ j = 3 := by
          simpa [hBlevels] using (List.mem_filter.mp hj).1
        have hsame : B.sideAt j = B.sideAt 1 :=
          (of_decide_eq_true (List.mem_filter.mp hj).2).1
        rcases hmem with rfl | rfl | rfl
        · exact le_rfl
        · rw [hBsideTwo, hBside] at hsame
          exact False.elim (hne hsame)
        · rw [hBsideThree, hBside] at hsame
          exact False.elim (hne hsame)
      let f : Ctx.Letter → Ctx.Letter := fun z => match z with
        | Ctx.Letter.child => Ctx.Letter.child
        | Ctx.Letter.ext j v => Ctx.Letter.ext
            (if j = 1 then B.maxima.length else if 1 < j then j - 1 else j) v
      let E : Ctx.Context :=
        { B with word := B.word.map f, maxima := B.maxima.eraseIdx 0 }
      let ν : Ctx.Context := match B.sideAt 1 with
        | Ctx.Side.lower => { E with u := min B.u (B.k - B.maximumAt 1) }
        | Ctx.Side.upper => { E with a := min B.a (B.k - B.maximumAt 1) }
      have hn := ctx_oldest_axis_maximum_erase_normalize B 1 hBlevel hterminal
      have hνDepth : ν.maxima.length = 2 := by
        have hh := hn.2.1
        change ν.maxima.length = B.maxima.length - 1 at hh
        omega
      have hνLevels : ν.levels = [1, 2] := by
        norm_num [Ctx.Context.levels, hνDepth, List.range_succ]
      have hνN : 1 ∈ ν.levels := by simp [hνLevels]
      have hνM : 2 ∈ ν.levels := by simp [hνLevels]
      have hνHistN := hn.2.2.1 1 hνN
      have hνHistM := hn.2.2.1 2 hνM
      have hνNs : ν.sideAt 1 = s := hνHistN.2.2.2.1.trans hBsideTwo
      have hνMs : ν.sideAt 2 = s := hνHistM.2.2.2.1.trans hBsideThree
      have hνExtN : ν.extPositions 1 = B.extPositions 2 := hνHistN.2.2.1
      have hνExtM : ν.extPositions 2 = B.extPositions 3 := hνHistM.2.2.1
      have hxν : x ∈ ν.extPositions 1 := by
        rw [hνExtN, hBextTwo]
        exact hx
      have hyν : y ∈ ν.extPositions 2 := by
        rw [hνExtM, hBextThree]
        exact hy
      have hνBound : B.bound ≤ ν.bound := hn.2.2.2.2.2
      have hνWord : ν.word = B.word.map f := by
        cases hs : B.sideAt 1 <;> simp [ν, hs, E]
      have hνLetter (r : ℕ) : ν.letterAt r = f (B.letterAt r) := by
        simp only [Ctx.Context.letterAt, hνWord, List.getElem?_map]
        cases B.word[r]? <;> rfl
      have hνPos : ∀ r j v, ν.letterAt r = Ctx.Letter.ext j v → 1 ≤ j := by
        intro r j v hj
        rw [hνLetter] at hj
        cases he : B.letterAt r with
        | child => simp only [he, f] at hj; cases hj
        | ext i z =>
            rw [he] at hj
            have hi := hPosB r i z he
            have hnew : 1 ≤
                (if i = 1 then B.maxima.length else if 1 < i then i - 1 else i) := by
              rw [hBdepth]
              split_ifs <;> omega
            change Ctx.Letter.ext
              (if i = 1 then B.maxima.length else if 1 < i then i - 1 else i) z =
                Ctx.Letter.ext j v at hj
            cases hj
            exact hnew
      have hνChosen : G ν s = G ρ s := by
        cases s <;> cases t
        · exact False.elim (hne rfl)
        · simp only [G, ν, hBside]
          rfl
        · simp only [G, ν, hBside]
          rfl
        · exact False.elim (hne rfl)
      have hνGlobal : G ν s ≤ 5 := by rw [hνChosen]; exact hGs
      have hBmaximum : B.maximumAt 1 = n :=
        Ctx.Context.part_maximumAt_one ρ rest t n
      have hνOpposite : G ν t ≤ ρ.k - n := by
        cases t <;> simp only [G, ν, hBside, hBmaximum]
        all_goals exact Nat.min_le_right _ _
      let width := G ν t - 1
      have hwidthBudget : width ≤ budget := by
        dsimp only [width, budget]
        omega
      have hνNoOpposite : ν.levelsOn t 0 = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro j hj
        have hmem : j = 1 ∨ j = 2 := by
          simpa [hνLevels] using (List.mem_filter.mp hj).1
        have hjt : ν.sideAt j = t :=
          (of_decide_eq_true (List.mem_filter.mp hj).2).1
        rcases hmem with rfl | rfl
        · exact hne (hνNs.symm.trans hjt)
        · exact hne (hνMs.symm.trans hjt)
      have hνFinal : ν.bound ≤ P budget := by
        by_cases hzeroWidth : width = 0
        · have hAxis : G ν t ≤ 1 := by dsimp only [width] at hzeroWidth; omega
          have hDead : ∀ r ∈ ν.childPositions,
              ν.cupLimit r r = 0 ∨ ν.capLimit r r = 0 := by
            intro r hr
            cases t with
            | lower =>
                left
                apply Nat.eq_zero_of_le_zero
                exact (Nat.min_le_left _ _).trans (by simp only [G] at hAxis; omega)
            | upper =>
                right
                apply Nat.eq_zero_of_le_zero
                exact (Nat.min_le_left _ _).trans (by simp only [G] at hAxis; omega)
          have hz := hZero ν hDead
          rw [hz]
          exact Nat.zero_le _
        · by_cases honeWidth : width = 1
          · have hAxis : G ν t ≤ 2 := by dsimp only [width] at honeWidth; omega
            have hUnit : ∀ r ∈ ν.childPositions,
                (match t with
                  | Ctx.Side.lower => ν.cupLimit r r
                  | Ctx.Side.upper => ν.capLimit r r) ≤ 1 := by
              intro r hr
              cases t with
              | lower => exact (Nat.min_le_left _ _).trans (by simp only [G] at hAxis; omega)
              | upper => exact (Nat.min_le_left _ _).trans (by simp only [G] at hAxis; omega)
            have hClear : ∀ r ∈ ν.childPositions, ∀ z ∈ ν.childPositions,
                ∀ l ∈ ν.levelsOn t 0, ∀ a ∈ ν.extPositions l,
                  a < min r z ∨ max r z < a := by
              intro r hr z hz l hl
              rw [hνNoOpposite] at hl
              simp at hl
            have hOne := ctx_bound_le_one_of_clear_unit_axis ν hνPos t hUnit hClear
            have hbudgetOne : 1 ≤ budget := by omega
            have hchoose : 1 ≤ (budget + 1).choose 2 := by
              simpa using Nat.choose_le_choose 2 (show 2 ≤ budget + 1 by omega)
            exact hOne.2.trans (by dsimp only [P]; omega)
          · have hwidth : 2 ≤ width := by omega
            have hTwo := ctx_two_actual_marker_sharp_potential_arbitrary_history ν hνPos
              s t hne 1 2 x y hνN hνM (by decide) hνNs hνMs hxν hyν hνGlobal
              (by cases t <;> exact hwidth)
            have hTwoBound : ν.bound ≤ P width := by
              dsimp only [P, width]
              cases t <;> exact hTwo.2
            have hchoose := Nat.choose_le_choose 2
              (Nat.add_le_add_right hwidthBudget 1)
            exact hTwoBound.trans (by dsimp only [P]; omega)
      exact hνBound.trans hνFinal
    have hMain : ∀ d (ρ : Ctx.Context), ρ.maxima.length = d →
        (∀ r j v, ρ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j) →
        ∀ N M x y, N ∈ ρ.levels → M ∈ ρ.levels → N < M →
        ρ.sideAt N = s → ρ.sideAt M = s →
        x ∈ ρ.extPositions N → y ∈ ρ.extPositions M → G ρ s ≤ 5 →
        ∀ keep : List ℕ, ∀ m n p q,
        p ∈ (ρ.part keep s m).childPositions → q ∈ ρ.childPositions → q ∉ keep →
        (ρ.part (ρ.childPositions.filter (· ∉ keep)) t n).bound ≤ P (ρ.k - n - 1) := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro ρ hd hPos N M x y hN hM hNM hNs hMs hx hy hGs
          keep m n p q hp hq hRemoved
        have hNB := (hLevelMem ρ N).mp hN
        have hMB := (hLevelMem ρ M).mp hM
        by_cases hTwoDepth : ρ.maxima.length = 2
        · exact hBase ρ hPos hTwoDepth N M x y hN hM hNM hNs hMs hx hy hGs
            keep m n p q hp hq hRemoved
        have hDepthThree : 3 ≤ ρ.maxima.length := by omega
        let L := if N = 1 then if M = 2 then 3 else 2 else 1
        have hLB : 1 ≤ L ∧ L ≤ ρ.maxima.length ∧ L ≠ N ∧ L ≠ M := by
          dsimp only [L]
          split_ifs <;> omega
        have hL : L ∈ ρ.levels :=
          (hLevelMem ρ L).mpr ⟨hLB.1, hLB.2.1⟩
        let N' := if N < L then N else N - 1
        let M' := if M < L then M else M - 1
        have hN' : N' ∈ (norm ρ L).levels := by
          apply (hLevelMem (norm ρ L) N').mpr
          rw [hDepth ρ L hL]
          dsimp only [N']
          split_ifs <;> omega
        have hM' : M' ∈ (norm ρ L).levels := by
          apply (hLevelMem (norm ρ L) M').mpr
          rw [hDepth ρ L hL]
          dsimp only [M']
          split_ifs <;> omega
        have hRecoverN : up L N' = N := by
          dsimp only [up, N']
          split_ifs <;> omega
        have hRecoverM : up L M' = M := by
          dsimp only [up, M']
          split_ifs <;> omega
        have hNM' : N' < M' := by
          dsimp only [N', M']
          split_ifs <;> omega
        have hNs' : (norm ρ L).sideAt N' = s := by
          rw [hSide ρ L N' hL hN', hRecoverN]
          exact hNs
        have hMs' : (norm ρ L).sideAt M' = s := by
          rw [hSide ρ L M' hL hM', hRecoverM]
          exact hMs
        have hx' : x ∈ (norm ρ L).extPositions N' := by
          rw [hExt ρ L N' hL hN', hRecoverN]
          exact hx
        have hy' : y ∈ (norm ρ L).extPositions M' := by
          rw [hExt ρ L M' hL hM', hRecoverM]
          exact hy
        have hD : (norm ρ L).maxima.length < d := by
          rw [hDepth ρ L hL, hd]
          omega
        have hBound := ih (norm ρ L).maxima.length hD (norm ρ L) rfl
          (hPositive ρ L hL hPos) N' M' x y hN' hM' hNM' hNs' hMs' hx' hy'
          (by cases s <;> exact hGs) keep m n p q
          (by simpa only [Ctx.Context.part_childPositions, hChild] using hp)
          (by simpa only [hChild] using hq) hRemoved
        rw [hChild] at hBound
        have hB := hPartMono ρ L hL (ρ.childPositions.filter (· ∉ keep)) t n
        exact hB.trans hBound
    let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
    let budget := σ.k - n - 1
    have hBound : B.bound ≤ P budget := by
      exact hMain σ.maxima.length σ rfl hpositive N M x y hN hM hNM hNs hMs hx hy
        (by cases s <;> exact hglobal) keep m n p q hp hq hremoved
    exact ⟨fun fuel => (hFuelFull B fuel).trans hBound, hBound⟩


end ErdosSzekeres
