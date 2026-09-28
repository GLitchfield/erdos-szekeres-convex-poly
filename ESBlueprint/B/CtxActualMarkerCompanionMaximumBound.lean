import ESBlueprint.B.CtxSingleLevelCompanionMaximumBound
import ESBlueprint.B.CtxActualMarkerRankSquarePotential
import ESBlueprint.B.CtxActiveBoundaryMarkerRankPairUnionBound
import ESBlueprint.B.CtxEraseLevelBoundMono
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Bound the opposite companion of a context with an actual indexed chosen marker and chosen global at most five by (k-n-1)^2, where n is the new opposite maximum. A retained chosen capacity of at least three sharpens the bound to choose(k-n,2). Erase unselected source levels locally, transport both parts and the retained capacity, and absorb the new opposite maximum while retaining the selected chosen marker and all physical barriers. Positive external labels, distinct axes, an actual indexed chosen marker, chosen global at most five, and retained/removed child witnesses are required. Additional chosen and opposite history, repeated occurrences, old maxima, kept lists and new maxima are arbitrary. No exact-depth, youngest-marker, empty-history, coupling, opposite-global or recursive-potential premise. The triangular conclusion additionally requires retained chosen capacity at least three.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_actual_marker_companion_maximum_bound (σ : Ctx.Context)
  (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ) (hN : N ∈ σ.levels)
  (hside : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep) :
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  let budget := σ.k - n - 1
  (∀ fuel, Ctx.Context.boundFuel fuel B ≤ budget ^ 2) ∧
    B.bound ≤ budget ^ 2 ∧
    ((3 ≤ (match s with
      | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
      | Ctx.Side.upper => (σ.part keep s m).capLimit p p)) →
      (∀ fuel, Ctx.Context.boundFuel fuel B ≤ (budget + 1).choose 2) ∧ B.bound ≤ (budget + 1).choose 2) := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
  let letter (D L : ℕ) : Letter → Letter := fun x => match x with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext (idx D L j) v
  let norm (ρ : Context) (L : ℕ) : Context :=
    { ρ with word := ρ.word.map (letter ρ.maxima.length L), maxima := ρ.maxima.eraseIdx (L-1) }
  let up (L j : ℕ) := if j < L then j else j+1
  have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
    simp only [levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro hj; exact ⟨j-1, by omega, by omega⟩
  have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
    unfold levels
    exact List.pairwise_lt_range.map (fun x => x+1) (fun a b h => Nat.add_lt_add_right h 1)
  have hLen (ρ : Context) (L : ℕ) : (norm ρ L).word.length = ρ.word.length := by
    simp only [norm, List.length_map]
  have hLetter (ρ : Context) (L p : ℕ) :
      (norm ρ L).letterAt p = letter ρ.maxima.length L (ρ.letterAt p) := by
    simp only [norm, letterAt, List.getElem?_map]
    cases ρ.word[p]? <;> rfl
  have hIsChild (ρ : Context) (L p : ℕ) :
      (norm ρ L).letterAt p = Letter.child ↔ ρ.letterAt p = Letter.child := by
    rw [hLetter]
    cases ρ.letterAt p <;> simp [letter]
  have hChild (ρ : Context) (L : ℕ) : (norm ρ L).childPositions = ρ.childPositions := by
    simp only [childPositions, hLen, hIsChild]
  have hRuns (ρ : Context) (L : ℕ) : (norm ρ L).numRuns = ρ.numRuns := by
    simp only [numRuns, hLen, ne_eq, hIsChild]
  have hBlocks (ρ : Context) (L : ℕ) : (norm ρ L).blocks = ρ.blocks := by
    simp only [blocks, hChild]
  have hK (ρ : Context) (L : ℕ) : (norm ρ L).k = ρ.k := rfl
  have hDepth (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      (norm ρ L).maxima.length = ρ.maxima.length-1 := by
    have hh := (hLevelMem ρ L).mp hL
    exact List.length_eraseIdx_of_lt (by omega)
  have hLive (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) :
      1 ≤ j ∧ j < ρ.maxima.length ∧ up L j ∈ ρ.levels := by
    have hh := (hLevelMem ρ L).mp hL
    have hj' := (hLevelMem (norm ρ L) j).mp hj
    rw [hDepth ρ L hL] at hj'
    refine ⟨hj'.1, by omega, ?_⟩
    apply (hLevelMem ρ _).mpr
    dsimp [up]
    split_ifs <;> omega
  have hIndex (D L i j : ℕ) (hL : 1 ≤ L) (hLD : L ≤ D)
      (hj : 1 ≤ j) (hjD : j < D) : idx D L i = j ↔ i = up L j := by
    dsimp [idx, up]
    split_ifs <;> omega
  have hExt (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) :
      (norm ρ L).extPositions j = ρ.extPositions (up L j) := by
    have hLj := (hLevelMem ρ L).mp hL
    have hj' := hLive ρ L j hL hj
    simp only [extPositions, hLen, hLetter]
    apply List.filter_congr
    intro p _
    cases ρ.letterAt p with
    | child => rfl
    | ext i v => simp only [letter, hIndex _ _ i j hLj.1 hLj.2 hj'.1 hj'.2.1]
  have hSide (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) : (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
    simp only [sideAt, hExt ρ L j hL hj]
    cases hh : (ρ.extPositions (up L j)).head? with
    | none => rfl
    | some p =>
      dsimp only
      rw [hLetter]
      cases ρ.letterAt p <;> rfl
  have hPositive (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) :
      ∀ p j v, (norm ρ L).letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hj
    rw [hLetter] at hj
    have hLB := (hLevelMem ρ L).mp hL
    cases he : ρ.letterAt p with
    | child => simp only [he, letter] at hj; cases hj
    | ext i z =>
      rw [he] at hj
      have hi := hPos p i z he
      have hnew : 1 ≤ idx ρ.maxima.length L i := by
        dsimp only [idx]
        split_ifs <;> omega
      change Letter.ext (idx ρ.maxima.length L i) z = Letter.ext j v at hj
      cases hj
      exact hnew
  have hNormPart (ρ : Context) (keep : List ℕ) (v : Side) (m L : ℕ) (hL : 1 ≤ L) :
      norm (ρ.part keep v m) (L+1) = (norm ρ L).part keep v m := by
    have hi (j : ℕ) : idx (ρ.maxima.length+1) (L+1) (j+1) = idx ρ.maxima.length L j + 1 := by
      dsimp [idx]; split_ifs <;> omega
    have hnew : idx (ρ.maxima.length+1) (L+1) 1 = 1 := by simp [idx]; omega
    have hm : (m :: ρ.maxima).eraseIdx (L+1-1) = m :: ρ.maxima.eraseIdx (L-1) := by
      rw [show L+1-1 = (L-1)+1 by omega, List.eraseIdx_cons_succ]
    have hw : (norm (ρ.part keep v m) (L+1)).word = ((norm ρ L).part keep v m).word := by
      change ((ρ.part keep v m).word.map (letter (m :: ρ.maxima).length (L+1))) =
        (List.range (norm ρ L).word.length).map (fun p => match (norm ρ L).letterAt p with
          | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 v
          | Letter.ext j w => Letter.ext (j+1) w)
      rw [hLen]
      simp only [part, List.map_map, List.length_cons, Function.comp_def]
      apply List.map_congr_left
      intro p _
      rw [hLetter]
      cases ρ.letterAt p with
      | child => by_cases hp : p ∈ keep <;> simp [hp, letter, hnew]
      | ext j w => simp only [letter, hi]
    change Context.mk ρ.a ρ.u ρ.k _ ((m :: ρ.maxima).eraseIdx (L+1-1)) =
      Context.mk ρ.a ρ.u ρ.k _ (m :: ρ.maxima.eraseIdx (L-1))
    rw [hm]
    exact congrArg (fun w => Context.mk ρ.a ρ.u ρ.k w (m :: ρ.maxima.eraseIdx (L-1))) hw
  have hBase (σ : Ctx.Context)
  (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j)
  (hdepth : σ.maxima.length = 1)
  (s t : Ctx.Side) (hne : s ≠ t) (x : ℕ)
  (hside : σ.sideAt 1 = s) (hx : x ∈ σ.extPositions 1)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep) :
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  let budget := σ.k - n - 1
  (∀ fuel, Ctx.Context.boundFuel fuel B ≤ budget ^ 2) ∧
    B.bound ≤ budget ^ 2 ∧
    ((3 ≤ (match s with
      | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
      | Ctx.Side.upper => (σ.part keep s m).capLimit p p)) →
      (∀ fuel, Ctx.Context.boundFuel fuel B ≤ (budget + 1).choose 2) ∧ B.bound ≤ (budget + 1).choose 2) := by
    classical
    let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
    let rest := σ.childPositions.filter (· ∉ keep)
    let A := σ.part keep s m
    let B := σ.part rest t n
    let budget := σ.k - n - 1
    change (∀ fuel, boundFuel fuel B ≤ budget ^ 2) ∧ B.bound ≤ budget ^ 2 ∧
      (3 ≤ (match s with | Side.lower => A.cupLimit p p | Side.upper => A.capLimit p p) →
        (∀ fuel, boundFuel fuel B ≤ (budget + 1).choose 2) ∧ B.bound ≤ (budget + 1).choose 2)
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
    have hPosB := hPartPositive σ rest t n
    have hChild (ks : List ℕ) (v : Side) (c r : ℕ) :
        r ∈ (σ.part ks v c).childPositions ↔ r ∈ σ.childPositions ∧ r ∈ ks := by
      simp only [part_childPositions, List.mem_filter, decide_eq_true_eq]
    have hpa := (hChild keep s m p).mp hp
    have hSourceLevels : σ.levels = [1] := by simp [levels, hdepth]
    have hSourceLevel : 1 ∈ σ.levels := by simp [hSourceLevels]
    have hSourceOn : 1 ∈ σ.levelsOn s 0 := by simp [levelsOn, hSourceLevels, hside]
    have hBdepth : B.maxima.length = 2 := by simp [B, part, hdepth]
    have hBlevels : B.levels = [1, 2] := by simp [B, part_levels, hSourceLevels]
    have hBlevel : 1 ∈ B.levels := by simp [hBlevels]
    have hBside : B.sideAt 1 = t := by
      apply part_sideAt_one_of_mem hpositive rest t n (q := p)
      rw [part_extPositions_one hpositive rest t n]
      exact List.mem_filter.mpr ⟨hpa.1, by simp [rest, hpa.2]⟩
    have hBoldSide : B.sideAt 2 = s := by
      exact (part_sideAt_succ σ rest t n (show 1 ≤ 1 by decide)).trans hside
    have hBoldExt : B.extPositions 2 = σ.extPositions 1 :=
      part_extPositions_succ σ rest t n (show 1 ≤ 1 by decide)
    have hterminal : ∀ j ∈ B.levelsOn (B.sideAt 1) 0, j ≤ 1 := by
      intro j hj
      have hmem : j = 1 ∨ j = 2 := by simpa [hBlevels] using (List.mem_filter.mp hj).1
      have hs : B.sideAt j = B.sideAt 1 :=
        (of_decide_eq_true (List.mem_filter.mp hj).2).1
      rcases hmem with rfl | rfl
      · exact le_rfl
      · rw [hBoldSide, hBside] at hs
        exact False.elim (hne hs)
    let f : Letter → Letter := fun z => match z with
      | Letter.child => Letter.child
      | Letter.ext j v => Letter.ext
          (if j = 1 then B.maxima.length else if 1 < j then j - 1 else j) v
    let E : Context := { B with word := B.word.map f, maxima := B.maxima.eraseIdx 0 }
    let ν : Context := match B.sideAt 1 with
      | Side.lower => { E with u := min B.u (B.k - B.maximumAt 1) }
      | Side.upper => { E with a := min B.a (B.k - B.maximumAt 1) }
    have hn := ctx_oldest_axis_maximum_erase_normalize B 1 hBlevel hterminal
    have hνChild : ν.childPositions = B.childPositions := hn.1
    have hνDepth : ν.maxima.length = 1 := by
      have hh := hn.2.1
      change ν.maxima.length = B.maxima.length - 1 at hh
      omega
    have hνLevel : 1 ∈ ν.levels := by simp [levels, hνDepth]
    have hνHistory : 2 ∈ B.levels ∧ 2 ≠ 1 ∧ ν.extPositions 1 = B.extPositions 2 ∧
        ν.sideAt 1 = B.sideAt 2 ∧ ν.maximumAt 1 = B.maximumAt 2 := hn.2.2.1 1 hνLevel
    have hνSide : ν.sideAt 1 = s := hνHistory.2.2.2.1.trans hBoldSide
    have hνExt : ν.extPositions 1 = σ.extPositions 1 := hνHistory.2.2.1.trans hBoldExt
    have hxν : x ∈ ν.extPositions 1 := by rw [hνExt]; exact hx
    have hνFuel : ∀ fuel, boundFuel fuel B ≤ boundFuel fuel ν := hn.2.2.2.2.1
    have hνBound : B.bound ≤ ν.bound := hn.2.2.2.2.2
    have hνWord : ν.word = B.word.map f := by cases hs : B.sideAt 1 <;> simp [ν, hs, E]
    have hνLetter (r : ℕ) : ν.letterAt r = f (B.letterAt r) := by
      simp only [letterAt, hνWord, List.getElem?_map]
      cases B.word[r]? <;> rfl
    have hνPos : ∀ r j v, ν.letterAt r = Letter.ext j v → 1 ≤ j := by
      intro r j v hj
      rw [hνLetter] at hj
      cases he : B.letterAt r with
      | child =>
        simp only [he, f] at hj
        cases hj
      | ext i z =>
        rw [he] at hj
        have hi := hPosB r i z he
        have hnew : 1 ≤ (if i = 1 then B.maxima.length else if 1 < i then i - 1 else i) := by
          rw [hBdepth]
          split_ifs <;> omega
        change Letter.ext (if i = 1 then B.maxima.length else if 1 < i then i - 1 else i) z =
          Letter.ext j v at hj
        cases hj
        exact hnew
    have hνChosen : G ν s = G σ s := by
      cases s <;> cases t
      · exact False.elim (hne rfl)
      · simp only [G, ν, hBside]
        rfl
      · simp only [G, ν, hBside]
        rfl
      · exact False.elim (hne rfl)
    have hνGlobal : G ν s ≤ 5 := by
      rw [hνChosen]
      cases s <;> exact hglobal
    have hBmaximum : B.maximumAt 1 = n := part_maximumAt_one σ rest t n
    have hνOpposite : G ν t ≤ σ.k - n := by
      cases t <;> simp only [G, ν, hBside, hBmaximum]
      all_goals exact Nat.min_le_right _ _
    have hbudget : G ν t - 1 ≤ budget := by dsimp [budget]; omega
    let active := ν.childPositions.toFinset.filter
      (fun r => 0 < ν.cupLimit r r ∧ 0 < ν.capLimit r r)
    let I (r : ℕ) := Finset.Icc (ν.leftExt t 0 r + 1) (G ν t - 1 - ν.rightExt t 0 r)
    let ranks := active.biUnion I
    let J := Finset.Icc 1 budget
    have hISub (r : ℕ) : I r ⊆ J := by
      intro z hz
      have hh := Finset.mem_Icc.mp hz
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hJCard : J.card = budget := by simp [J]
    have hRankSub : ranks ⊆ J := by
      intro z hz
      obtain ⟨r, _, hz⟩ := Finset.mem_biUnion.mp hz
      exact hISub r hz
    have hRankCard : ranks.card ≤ budget := by
      simpa only [hJCard] using Finset.card_le_card hRankSub
    have hSquare := ctx_actual_marker_rank_square_potential ν hνPos s t hne 1 x
      hνLevel hνSide hxν hνGlobal
    change (∀ fuel, boundFuel fuel ν ≤ ranks.card ^ 2) ∧ ν.bound ≤ ranks.card ^ 2 at hSquare
    have hSquareBudget := Nat.pow_le_pow_left hRankCard 2
    refine ⟨fun fuel => (hνFuel fuel).trans ((hSquare.1 fuel).trans hSquareBudget),
      hνBound.trans (hSquare.2.trans hSquareBudget), ?_⟩
    intro hnonunit
    let μ : Context := match s with
      | Side.lower => {σ with u := σ.u - 1}
      | Side.upper => {σ with a := σ.a - 1}
    have hμPos : ∀ r j v, μ.letterAt r = Letter.ext j v → 1 ≤ j := by
      cases s <;> exact hpositive
    have hμGlobal : (match s with | Side.lower => μ.u | Side.upper => μ.a) ≤ 4 := by
      cases s with
      | lower =>
        change σ.u - 1 ≤ 4
        have hh : σ.u ≤ 5 := hglobal
        omega
      | upper =>
        change σ.a - 1 ≤ 4
        have hh : σ.a ≤ 5 := hglobal
        omega
    have hμCapacity : 2 ≤ (match s with
        | Side.lower => (μ.part keep s m).cupLimit p p
        | Side.upper => (μ.part keep s m).capLimit p p) := by
      cases s with
      | lower =>
        change 3 ≤ min (σ.u-1-A.chainExt Side.lower p p) (σ.k-1-A.joinExt Side.lower p p) at hnonunit
        change 2 ≤ min (σ.u-1-1-A.chainExt Side.lower p p) (σ.k-1-A.joinExt Side.lower p p)
        omega
      | upper =>
        change 3 ≤ min (σ.a-1-A.chainExt Side.upper p p) (σ.k-1-A.joinExt Side.upper p p) at hnonunit
        change 2 ≤ min (σ.a-1-1-A.chainExt Side.upper p p) (σ.k-1-A.joinExt Side.upper p p)
        omega
    have hgeom := ctx_nonunit_part_companion_exterior_rank_bound μ hμPos s t hne 1 x
      (by cases s <;> exact hSourceLevel) (by cases s <;> exact hside)
      (by cases s <;> exact hx) hμGlobal keep m n p q
      (by cases s <;> exact hp) hμCapacity (by cases s <;> exact hq) hremoved
    obtain ⟨dir, _, hremovedSide⟩ := hgeom.1
    have hchildren : ∀ r ∈ ν.childPositions, if dir then r < x else x < r := by
      intro r hr
      rw [hνChild] at hr
      have hh := (hChild rest t n r).mp hr
      have hrnot : r ∉ keep := of_decide_eq_true (List.mem_filter.mp hh.2).2
      exact hremovedSide r (by cases s <;> exact hh.1) hrnot 1
        (by cases s <;> exact hSourceOn) x (by cases s <;> exact hx)
    have hyounger : ∀ j ∈ ν.levelsOn (ν.sideAt 1) 1, ∀ r ∈ ν.extPositions j,
        if dir then r < x else x < r := by
      intro j hj r _
      have hj1 := (one_le_of_mem_levelsOn hj).1
      have hjlt := (of_decide_eq_true (List.mem_filter.mp hj).2).2
      omega
    have hsmall : min ((match ν.sideAt 1 with
        | Side.lower => ν.u | Side.upper => ν.a) - 1) (ν.k - ν.maximumAt 1) ≤ 4 := by
      rw [hνSide]
      change min (G ν s - 1) (ν.k - ν.maximumAt 1) ≤ 4
      omega
    let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
    let pairs := active.biUnion (fun r => Q (I r))
    have hCardPairs (T : Finset ℕ) : (Q T).card = (T.card + 1).choose 2 := by
      rw [← Finset.card_sym2]
      apply Finset.card_bij (fun z _ ↦ Sym2.mk z.1 z.2)
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
          · exact ⟨(b, a), Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩, Sym2.eq_swap⟩
    have hPairsSub : pairs ⊆ Q J := by
      intro z hz
      obtain ⟨r, _, hz⟩ := Finset.mem_biUnion.mp hz
      have hh := Finset.mem_filter.mp hz
      have hp := Finset.mem_product.mp hh.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hISub r hp.1, hISub r hp.2⟩, hh.2⟩
    have hPairsCard : pairs.card ≤ (budget+1).choose 2 := by
      have hh := Finset.card_le_card hPairsSub
      simpa only [hCardPairs, hJCard] using hh
    have hPairBound := ctx_active_boundary_marker_rank_pair_union_bound ν hνPos 1 x hνLevel hxν dir
      (fun r hr _ => hchildren r hr) hyounger t (by rw [hνSide]; exact hne) hsmall
    change (∀ fuel, boundFuel fuel ν ≤ pairs.card) ∧ ν.bound ≤ pairs.card at hPairBound
    exact ⟨fun fuel => (hνFuel fuel).trans ((hPairBound.1 fuel).trans hPairsCard),
      hνBound.trans (hPairBound.2.trans hPairsCard)⟩
  have hPartMono (ρ : Context) (L : ℕ) (hL : L∈ρ.levels)
      (keep : List ℕ) (v : Side) (m : ℕ) :
      (ρ.part keep v m).bound≤((norm ρ L).part keep v m).bound := by
    have hnext : L+1∈(ρ.part keep v m).levels := by
      rw [part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L,hL,rfl⟩)
    have hh := (ctx_erase_level_bound_mono (ρ.part keep v m) (L+1) hnext).2.2
    change (ρ.part keep v m).bound≤(norm (ρ.part keep v m) (L+1)).bound at hh
    rw [hNormPart ρ keep v m L (one_le_of_mem_levels hL)] at hh
    exact hh
  have hPartCaps (ρ : Context) (L : ℕ) (hL : L∈ρ.levels)
      (keep : List ℕ) (v : Side) (m p : ℕ) :
      (ρ.part keep v m).cupLimit p p≤((norm ρ L).part keep v m).cupLimit p p ∧
      (ρ.part keep v m).capLimit p p≤((norm ρ L).part keep v m).capLimit p p := by
    have hnext : L+1∈(ρ.part keep v m).levels := by
      rw [part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L,hL,rfl⟩)
    have hh := (ctx_erase_level_bound_mono (ρ.part keep v m) (L+1) hnext).1 p p
    change (ρ.part keep v m).cupLimit p p≤(norm (ρ.part keep v m) (L+1)).cupLimit p p ∧
      (ρ.part keep v m).capLimit p p≤(norm (ρ.part keep v m) (L+1)).capLimit p p at hh
    rw [hNormPart ρ keep v m L (one_le_of_mem_levels hL)] at hh
    exact hh
  have hMain : ∀ d (ρ : Context), ρ.maxima.length=d →
      (∀ r j v, ρ.letterAt r=Letter.ext j v → 1≤j) →
      ∀ N x, N∈ρ.levels → ρ.sideAt N=s → x∈ρ.extPositions N → G ρ s≤5 →
      ∀ keep : List ℕ, ∀ m n p q,
      p∈(ρ.part keep s m).childPositions → q∈ρ.childPositions → q∉keep →
      (ρ.part (ρ.childPositions.filter (·∉keep)) t n).bound≤(ρ.k-n-1)^2 ∧
      (3≤(match s with
        | Side.lower => (ρ.part keep s m).cupLimit p p
        | Side.upper => (ρ.part keep s m).capLimit p p) →
        (ρ.part (ρ.childPositions.filter (·∉keep)) t n).bound≤(ρ.k-n-1+1).choose 2) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro ρ hd hPos N x hN hNs hx hGs keep m n p q hp hq hRemoved
      have hNB := (hLevelMem ρ N).mp hN
      by_cases hOne : ρ.maxima.length=1
      · have hN1 : N=1 := by omega
        subst N
        have hh := hBase ρ hPos hOne s t hne x hNs hx (by cases s <;> exact hGs) keep m n p q hp hq hRemoved
        exact ⟨hh.2.1,fun hcap => (hh.2.2 (by cases s <;> exact hcap)).2⟩
      let L := if N=1 then 2 else 1
      have hLB : 1≤L ∧ L≤ρ.maxima.length ∧ L≠N := by
        dsimp only [L]
        split_ifs <;> omega
      have hL : L∈ρ.levels := (hLevelMem ρ L).mpr ⟨hLB.1,hLB.2.1⟩
      let N' := if N<L then N else N-1
      have hN' : N'∈(norm ρ L).levels := by
        apply (hLevelMem (norm ρ L) N').mpr
        rw [hDepth ρ L hL]
        dsimp only [N']
        split_ifs <;> omega
      have hRecoverN : up L N'=N := by
        dsimp only [up,N']
        split_ifs <;> omega
      have hNs' : (norm ρ L).sideAt N'=s := by
        rw [hSide ρ L N' hL hN',hRecoverN]
        exact hNs
      have hx' : x∈(norm ρ L).extPositions N' := by
        rw [hExt ρ L N' hL hN',hRecoverN]
        exact hx
      have hD : (norm ρ L).maxima.length<d := by rw [hDepth ρ L hL]; omega
      have hBound := ih (norm ρ L).maxima.length hD (norm ρ L) rfl
        (hPositive ρ L hL hPos) N' x hN' hNs' hx' hGs keep m n p q
        (by simpa only [part_childPositions,hChild] using hp)
        (by simpa only [hChild] using hq) hRemoved
      rw [hChild] at hBound
      have hB := hPartMono ρ L hL (ρ.childPositions.filter (·∉keep)) t n
      refine ⟨hB.trans hBound.1,?_⟩
      intro hcap
      have hCaps := hPartCaps ρ L hL keep s m p
      have hcap' : 3≤(match s with
          | Side.lower => ((norm ρ L).part keep s m).cupLimit p p
          | Side.upper => ((norm ρ L).part keep s m).capLimit p p) := by
        cases s
        · exact hcap.trans hCaps.1
        · exact hcap.trans hCaps.2
      exact hB.trans (hBound.2 hcap')
  have hBound := hMain σ.maxima.length σ rfl hpositive N x hN hside hx (by cases s <;> exact hglobal) keep m n p q
    hp hq hremoved
  have hFuelFull (ρ : Context) (fuel : ℕ) : boundFuel fuel ρ≤ρ.bound := by
    by_cases hf : ρ.childPositions.length+1≤fuel
    · exact (boundFuel_eq_bound ρ hf).le
    · exact boundFuel_mono (by omega : fuel≤ρ.childPositions.length+1) ρ
  refine ⟨fun fuel => (hFuelFull _ fuel).trans hBound.1,hBound.1,?_⟩
  intro hcap
  exact ⟨fun fuel => (hFuelFull _ fuel).trans (hBound.2 (by cases s <;> exact hcap)),hBound.2 (by cases s <;> exact hcap)⟩

end ErdosSzekeres
