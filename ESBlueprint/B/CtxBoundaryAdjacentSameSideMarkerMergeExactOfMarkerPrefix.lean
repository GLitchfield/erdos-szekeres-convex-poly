import ESBlueprint.B.CtxBoundLeMergeSameSideLevels

namespace ErdosSzekeres

open Ctx Ctx.Context MergeLevels
set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

/-- Exactly merge adjacent chosen-axis indexed levels when the sole younger marker precedes all children,all younger chosen markers,and every older-pair marker. Keep both globals unchanged,relabel the pair to one level,and merge maximummax(youngerMaximum,olderMaximum+1). Preserve every child-endpoint limit,every fuel and full bound. Positive labels,MergeLevels.Inv,no selected levels older than the pair,and legal selected global. Provides the unmarked exposed-first-child same-axis complement normal form toward R16 one-marked root selector; arbitrary opposite history and younger levels,both axes.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_boundary_adjacent_same_side_marker_merge_exact_of_marker_prefix (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (N x : ℕ) (hpair : MergeLevels.Inv σ N)
    (hsole : σ.extPositions N = [x])
    (hafter : ∀ y ∈ σ.extPositions (N+1), x < y)
    (hchildren : ∀ p ∈ σ.childPositions, x < p)
    (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j, x < p)
    (holdest : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, j ≤ N+1)
    (hglobal : (match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k) :
    let τ : Ctx.Context :=
      { σ with
        word := σ.word.map (fun z => match z with
          | Ctx.Letter.child => Ctx.Letter.child
          | Ctx.Letter.ext j v => if j ≤ N then Ctx.Letter.ext j v else Ctx.Letter.ext (j-1) v)
        maxima := σ.maxima.take (N-1) ++
          [max (σ.maximumAt N) (σ.maximumAt (N+1)+1)] ++ σ.maxima.drop (N+1) }
    (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
      σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ = Ctx.Context.boundFuel fuel τ) ∧ σ.bound = τ.bound := by
  classical
  let letter (L : ℕ) : Letter → Letter := fun x => match x with
    | Letter.child => Letter.child
    | Letter.ext j s => if j ≤ L then Letter.ext j s else Letter.ext (j - 1) s
  let norm (ρ : Context) (L : ℕ) : Context :=
    { ρ with
      word := ρ.word.map (letter L)
      maxima := ρ.maxima.take (L - 1) ++ [max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)] ++
        ρ.maxima.drop (L + 1) }
  let lv (ρ : Context) (i : ℕ) : ℕ → Bool := fun p => match ρ.letterAt p with
    | Letter.ext j _ => decide (j = i)
    | Letter.child => false
  let up (L j : ℕ) := if j < L then j else j + 1
  let upTop (L t : ℕ) := if t ≤ L then t else t + 1
  let img (L j x : ℕ) : Prop := (j < L ∧ x = j) ∨ (j = L ∧ (x = L ∨ x = L + 1)) ∨ (L < j ∧ x = j + 1)
  change (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
      σ.cupLimit p q = (norm σ N).cupLimit p q ∧
      σ.capLimit p q = (norm σ N).capLimit p q) ∧
    (∀ fuel, boundFuel fuel σ = boundFuel fuel (norm σ N)) ∧
      σ.bound = (norm σ N).bound
  -- basic transport ----------------------------------------------------------
  have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
    simp only [levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro hj; exact ⟨j - 1, by omega, by omega⟩
  have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
    unfold levels
    exact List.pairwise_lt_range.map (fun x => x + 1) (fun a b h => Nat.add_lt_add_right h 1)
  have hLen (ρ : Context) (L : ℕ) : (norm ρ L).word.length = ρ.word.length := by
    simp only [norm, List.length_map]
  have hLetter (ρ : Context) (L p : ℕ) : (norm ρ L).letterAt p = letter L (ρ.letterAt p) := by
    simp only [norm, letterAt, List.getElem?_map]
    cases ρ.word[p]? <;> rfl
  have hIsChild (ρ : Context) (L p : ℕ) :
      (norm ρ L).letterAt p = Letter.child ↔ ρ.letterAt p = Letter.child := by
    rw [hLetter]
    cases ρ.letterAt p with
    | child => simp [letter]
    | ext j v => by_cases hj : j ≤ L <;> simp [letter, hj]
  have hChild (ρ : Context) (L : ℕ) : (norm ρ L).childPositions = ρ.childPositions := by
    simp only [childPositions, hLen, hIsChild]
  have hRuns (ρ : Context) (L : ℕ) : (norm ρ L).numRuns = ρ.numRuns := by
    simp only [numRuns, hLen, ne_eq, hIsChild]
  have hBlocks (ρ : Context) (L : ℕ) : (norm ρ L).blocks = ρ.blocks := by
    simp only [blocks, hChild]
  have hK (ρ : Context) (L : ℕ) : (norm ρ L).k = ρ.k := rfl
  have hDepth (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
      (norm ρ L).maxima.length = ρ.maxima.length - 1 := by
    obtain ⟨h1, h2, -, -⟩ := hL
    simp only [norm, List.length_append, List.length_take, List.length_singleton, List.length_drop]
    omega
  have hNormLevel (ρ : Context) (L : ℕ) (hL : Inv ρ L) (j : ℕ) (hj : j ∈ (norm ρ L).levels) :
      1 ≤ j ∧ j + 1 ≤ ρ.maxima.length := by
    have h := (hLevelMem (norm ρ L) j).mp hj
    rw [hDepth ρ L hL] at h
    omega
  -- levels and letters ---------------------------------------------------------
  have hExtLv (ρ : Context) (i : ℕ) : ρ.extPositions i = (List.range ρ.word.length).filter (lv ρ i) := by
    unfold extPositions
    apply List.filter_congr
    intro p _
    cases h : ρ.letterAt p with
    | child => simp [lv, h]
    | ext j v => simp [lv, h]
  have hExtMerged (ρ : Context) (L : ℕ) :
      (norm ρ L).extPositions L =
        (List.range ρ.word.length).filter (fun p => lv ρ L p || lv ρ (L + 1) p) := by
    unfold extPositions
    rw [hLen]
    apply List.filter_congr
    intro p _
    rw [hLetter]
    cases h : ρ.letterAt p with
    | child => simp [lv, h, letter]
    | ext j v =>
      by_cases hj : j ≤ L
      · simp only [letter, hj, if_true, lv, h]
        by_cases hjL : j = L <;> simp [hjL] <;> omega
      · simp only [letter, hj, if_false, lv, h]
        by_cases hjL : j = L + 1 <;> simp [hjL] <;> omega
  have hExtNe (ρ : Context) (L j : ℕ) (hj1 : 1 ≤ j) (hjL : j ≠ L) :
      (norm ρ L).extPositions j = ρ.extPositions (up L j) := by
    unfold extPositions
    rw [hLen]
    apply List.filter_congr
    intro p _
    rw [hLetter]
    cases h : ρ.letterAt p with
    | child => simp [letter]
    | ext i v =>
      by_cases hi : i ≤ L <;> by_cases hjl : j < L <;> simp [letter, hi, hjl, up] <;> omega
  have hMemMerged (ρ : Context) (L p : ℕ) (hp : p ∈ ρ.extPositions L) :
      p ∈ (norm ρ L).extPositions L := by
    rw [hExtMerged, List.mem_filter]
    rw [hExtLv, List.mem_filter] at hp
    exact ⟨hp.1, by simp [hp.2]⟩
  have hSideL (ρ : Context) (L : ℕ) (hL : Inv ρ L) : (norm ρ L).sideAt L = ρ.sideAt L := by
    obtain ⟨-, -, h3, -⟩ := hL
    rcases hh : ((norm ρ L).extPositions L).head? with _ | p
    · have hρ : (ρ.extPositions L).head? = none := by
        cases hh2 : (ρ.extPositions L).head? with
        | none => rfl
        | some q =>
          exfalso
          have hq := hMemMerged ρ L q (List.mem_of_mem_head? (Option.mem_def.mpr hh2))
          rw [List.head?_eq_none_iff] at hh
          rw [hh] at hq
          exact List.not_mem_nil hq
      simp only [sideAt, hh, hρ]
    · have hp : p ∈ (norm ρ L).extPositions L := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      rw [hExtMerged, List.mem_filter] at hp
      cases hlet : ρ.letterAt p with
      | child => simp [lv, hlet] at hp
      | ext j v =>
        have hj : j = L ∨ j = L + 1 := by
          have := hp.2
          simp only [lv, hlet, Bool.or_eq_true, decide_eq_true_eq] at this
          exact this
        have hv := h3 p j v hlet hj
        rw [← hv]
        simp only [sideAt, hh, hLetter, hlet]
        by_cases hjL : j ≤ L <;> simp [letter, hjL]
  have hSideNe (ρ : Context) (L j : ℕ) (hj1 : 1 ≤ j) (hjL : j ≠ L) :
      (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
    unfold sideAt
    rw [hExtNe ρ L j hj1 hjL]
    cases hh : (ρ.extPositions (up L j)).head? with
    | none => rfl
    | some p =>
      dsimp only
      rw [hLetter]
      cases ρ.letterAt p with
      | child => rfl
      | ext i v => by_cases hi : i ≤ L <;> simp [letter, hi]
  have hMax (ρ : Context) (L : ℕ) (hL : Inv ρ L) (j : ℕ) (hj1 : 1 ≤ j) :
      (norm ρ L).maximumAt j =
        if j < L then ρ.maximumAt j else if j = L then max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)
        else ρ.maximumAt (j + 1) := by
    obtain ⟨h1, h2, -, -⟩ := hL
    simp only [maximumAt, norm]
    rw [getElem?_merge ρ.maxima L (j - 1) _ h1 h2]
    by_cases hjl : j < L
    · simp [hjl, show j - 1 < L - 1 by omega]
    · by_cases hjL : j = L
      · subst hjL; simp
      · simp [hjl, hjL, show ¬ j - 1 < L - 1 by omega, show j - 1 ≠ L - 1 by omega,
          show j - 1 + 1 = j by omega]
  have hUpMono (L i j : ℕ) (h : i < j) : up L i < up L j := by
    dsimp [up]
    split_ifs <;> omega
  have hUpZero (L : ℕ) (hL : 1 ≤ L) : up L 0 = 0 := by
    simp [up, show 0 < L by omega]
  have hLive (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
      (hj : j ∈ (norm ρ L).levels) :
      1 ≤ j ∧ j < ρ.maxima.length ∧ up L j ∈ ρ.levels := by
    have hh := hNormLevel ρ L hL j hj
    refine ⟨hh.1, by omega, ?_⟩
    apply (hLevelMem ρ _).mpr
    dsimp [up]
    split_ifs <;> omega
  have hSide (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
      (hj : j ∈ (norm ρ L).levels) :
      (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
    have hj1 := (hNormLevel ρ L hL j hj).1
    by_cases he : j = L
    · subst j
      rw [hSideL ρ L hL]
      simpa only [up, lt_self_iff_false, if_false] using hL.2.2.2
    · exact hSideNe ρ L j hj1 he
  have hNoMerged (ρ : Context) (L : ℕ) (hL : Inv ρ L)
      (v : Side) (hv : v ≠ ρ.sideAt L) (top j : ℕ)
      (hj : j ∈ (norm ρ L).levelsOn v top) : j ≠ L := by
    intro he
    subst j
    have hc : (norm ρ L).sideAt L = v ∧ (top = 0 ∨ L < top) :=
      of_decide_eq_true (List.mem_filter.mp hj).2
    rw [hSideL ρ L hL] at hc
    exact hv hc.1.symm
  have hMaximum (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
      (hj : j ∈ (norm ρ L).levels) (hne : j ≠ L) :
      (norm ρ L).maximumAt j = ρ.maximumAt (up L j) := by
    rw [hMax ρ L hL j ((hNormLevel ρ L hL j hj).1)]
    by_cases hjl : j < L <;> simp [hjl, hne, up]
  have hOppLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
      (hv : v ≠ ρ.sideAt L) (top : ℕ) :
      (((norm ρ L).levelsOn v top).map (up L)) = ρ.levelsOn v (up L top) := by
    have hs : (((norm ρ L).levelsOn v top).map (up L)).Pairwise (· < ·) :=
      ((hSorted (norm ρ L)).filter _).map (up L) (fun i j hij => hUpMono L i j hij)
    apply hs.eq_of_mem_iff ((hSorted ρ).filter _)
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hjl := (List.mem_filter.mp hj).1
      have hjc : (norm ρ L).sideAt j = v ∧ (top = 0 ∨ j < top) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      apply List.mem_filter.mpr
      refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
      apply decide_eq_true
      refine ⟨?_, ?_⟩
      · rw [← hSide ρ L j hL hjl]
        exact hjc.1
      · rcases hjc.2 with rfl | hlt
        · exact Or.inl (hUpZero L hL.1)
        · exact Or.inr (hUpMono L j top hlt)
    · intro hi
      have hil := (List.mem_filter.mp hi).1
      have hic : ρ.sideAt i = v ∧ (up L top = 0 ∨ i < up L top) :=
        of_decide_eq_true (List.mem_filter.mp hi).2
      have hiL : i ≠ L := by
        intro he
        subst i
        exact hv hic.1.symm
      let j := if i < L then i else i-1
      have hLr : 1 ≤ L ∧ L ≤ ρ.maxima.length := ⟨hL.1, by omega⟩
      have hir := (hLevelMem ρ i).mp hil
      have hjr : 1 ≤ j ∧ j < ρ.maxima.length ∧ up L j = i := by
        dsimp [j, up]
        split_ifs <;> omega
      have hjl : j ∈ (norm ρ L).levels := by
        apply (hLevelMem (norm ρ L) j).mpr
        rw [hDepth ρ L hL]
        omega
      apply List.mem_map.mpr
      refine ⟨j, ?_, hjr.2.2⟩
      apply List.mem_filter.mpr
      refine ⟨hjl, ?_⟩
      apply decide_eq_true
      refine ⟨?_, ?_⟩
      · rw [hSide ρ L j hL hjl, hjr.2.2]
        exact hic.1
      · rcases hic.2 with hzero | hlt
        · left
          by_contra hne
          have h := hUpMono L 0 top (by omega)
          rw [hUpZero L hLr.1, hzero] at h
          omega
        · right
          by_contra hn
          have hm : up L top ≤ up L j := by
            rcases lt_or_eq_of_le (show top ≤ j by omega) with hm | he
            · exact (hUpMono L top j hm).le
            · rw [he]
          rw [hjr.2.2] at hm
          omega
  have hFoldNormLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
      ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (norm ρ L).levels ∧ j ≠ L) → ∀ z,
      ls.foldl (leftStep (norm ρ L)) z =
        (ls.map (up L)).foldl (leftStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ z; rfl
    | cons j ls ih =>
      intro hj z
      simp only [List.foldl_cons, List.map_cons, leftStep,
        hExtNe ρ L j ((hLevelMem (norm ρ L) j).mp (hj j (by simp)).1).1
          (hj j (by simp)).2]
      exact ih (fun i hi => hj i (by simp [hi])) _
  have hFoldNormRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
      ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (norm ρ L).levels ∧ j ≠ L) → ∀ z,
      ls.foldl (rightStep (norm ρ L)) z =
        (ls.map (up L)).foldl (rightStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ z; rfl
    | cons j ls ih =>
      intro hj z
      simp only [List.foldl_cons, List.map_cons, rightStep,
        hExtNe ρ L j ((hLevelMem (norm ρ L) j).mp (hj j (by simp)).1).1
          (hj j (by simp)).2]
      exact ih (fun i hi => hj i (by simp [hi])) _
  have hOppLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
      (hv : v ≠ ρ.sideAt L) (top p : ℕ) :
      (norm ρ L).leftExt v top p = ρ.leftExt v (up L top) p := by
    rw [leftExt_eq, leftExt_eq, ← hOppLevels ρ L hL v hv top,
      List.sublists_map, List.map_map]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    exact congrArg Prod.snd (hFoldNormLeft ρ L hL ls
      (fun j hj => ⟨(List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1,
        hNoMerged ρ L hL v hv top j ((List.mem_sublists.mp hls).subset hj)⟩) (p,0))
  have hOppRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
      (hv : v ≠ ρ.sideAt L) (top p : ℕ) :
      (norm ρ L).rightExt v top p = ρ.rightExt v (up L top) p := by
    rw [rightExt_eq, rightExt_eq, ← hOppLevels ρ L hL v hv top,
      List.sublists_map, List.map_map]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    exact congrArg Prod.snd (hFoldNormRight ρ L hL ls
      (fun j hj => ⟨(List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1,
        hNoMerged ρ L hL v hv top j ((List.mem_sublists.mp hls).subset hj)⟩) (p,0))
  have hOppChain (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
      (hv : v ≠ ρ.sideAt L) (p q : ℕ) :
      (norm ρ L).chainExt v p q = ρ.chainExt v p q := by
    simp only [chainExt, hOppLeft ρ L hL v hv, hOppRight ρ L hL v hv,
      hUpZero L hL.1]
  have hOppJoin (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
      (hv : v ≠ ρ.sideAt L) (p q : ℕ) :
      (norm ρ L).joinExt v p q = ρ.joinExt v p q := by
    have hl : (((norm ρ L).levelsOn v 0).map (up L)) = ρ.levelsOn v 0 := by
      simpa only [hUpZero L hL.1] using hOppLevels ρ L hL v hv 0
    rw [joinExt, joinExt, hOppChain ρ L hL v hv, ← hl, List.map_map]
    congr 1
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro j hj
    rw [hOppLeft ρ L hL v hv, hOppRight ρ L hL v hv,
      hMaximum ρ L j hL (List.mem_filter.mp hj).1
        (hNoMerged ρ L hL v hv 0 j hj)]
    rfl
  have hYoungLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
      (norm ρ L).levelsOn (ρ.sideAt L) L = ρ.levelsOn (ρ.sideAt L) L := by
    apply ((hSorted (norm ρ L)).filter _).eq_of_mem_iff ((hSorted ρ).filter _)
    intro j
    constructor
    · intro hj
      have hjl := (List.mem_filter.mp hj).1
      have hjc : (norm ρ L).sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      have hjlt : j < L := by omega
      have hj1 := (hNormLevel ρ L hL j hjl).1
      have hs := hSideNe ρ L j hj1 (by omega)
      have hu : up L j = j := by simp [up, hjlt]
      rw [hu] at hs
      exact List.mem_filter.mpr ⟨by
        have hh := (hLive ρ L j hL hjl).2.2
        simpa only [hu] using hh,
        by apply decide_eq_true; exact ⟨hs.symm.trans hjc.1, Or.inr hjlt⟩⟩
    · intro hj
      have hjl := (List.mem_filter.mp hj).1
      have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      have hjlt : j < L := by omega
      have hj1 := ((hLevelMem ρ j).mp hjl).1
      have hjn : j ∈ (norm ρ L).levels := by
        apply (hLevelMem (norm ρ L) j).mpr
        rw [hDepth ρ L hL]
        omega
      have hs := hSideNe ρ L j hj1 (by omega)
      have hu : up L j = j := by simp [up, hjlt]
      rw [hu] at hs
      exact List.mem_filter.mpr ⟨hjn,
        by apply decide_eq_true; exact ⟨hs.trans hjc.1, Or.inr hjlt⟩⟩
  have hSourcePairLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
      ρ.levelsOn (ρ.sideAt L) 0 = ρ.levelsOn (ρ.sideAt L) L ++ [L, L + 1] := by
    have hLs : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
      apply List.mem_filter.mpr
      exact ⟨(hLevelMem ρ L).mpr ⟨hL.1, by omega⟩, by simp⟩
    have hL1s : L + 1 ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
      apply List.mem_filter.mpr
      exact ⟨(hLevelMem ρ (L + 1)).mpr ⟨by omega, hL.2.1⟩,
        by apply decide_eq_true; exact ⟨hL.2.2.2.symm, Or.inl rfl⟩⟩
    have hs : (ρ.levelsOn (ρ.sideAt L) L ++ [L, L + 1]).Pairwise (· < ·) := by
      apply List.pairwise_append.mpr
      refine ⟨(hSorted ρ).filter _, by simp, ?_⟩
      intro i hi j hj
      have hc : ρ.sideAt i = ρ.sideAt L ∧ (L = 0 ∨ i < L) :=
        of_decide_eq_true (List.mem_filter.mp hi).2
      have hiL : i < L := by omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> omega
    apply ((hSorted ρ).filter _).eq_of_mem_iff hs
    intro j
    constructor
    · intro hj
      have hjL := ht j hj
      by_cases he : j = L
      · simp [he]
      by_cases he1 : j = L + 1
      · simp [he1]
      apply List.mem_append.mpr
      left
      apply List.mem_filter.mpr
      refine ⟨(List.mem_filter.mp hj).1, ?_⟩
      apply decide_eq_true
      have hc : ρ.sideAt j = ρ.sideAt L ∧ (0 = 0 ∨ j < 0) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      exact ⟨hc.1, Or.inr (by omega)⟩
    · intro hj
      rcases List.mem_append.mp hj with hj | hj
      · apply List.mem_filter.mpr
        refine ⟨(List.mem_filter.mp hj).1, ?_⟩
        apply decide_eq_true
        have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        exact ⟨hc.1, Or.inl rfl⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hLs
        · exact hL1s
  have hSourceOwnLevels (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) :
      ρ.levelsOn (ρ.sideAt L) 0 = ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
    have hLs : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by simp [levelsOn, hL]
    have hs : (ρ.levelsOn (ρ.sideAt L) L ++ [L]).Pairwise (· < ·) := by
      apply List.pairwise_append.mpr
      refine ⟨(hSorted ρ).filter _, by simp, ?_⟩
      intro i hi j hj
      have he : j = L := by simpa using hj
      subst j
      have hc : ρ.sideAt i = ρ.sideAt L ∧ (L = 0 ∨ i < L) :=
        of_decide_eq_true (List.mem_filter.mp hi).2
      have hL1 := one_le_of_mem_levels hL
      omega
    apply ((hSorted ρ).filter _).eq_of_mem_iff hs
    intro j
    constructor
    · intro hj
      have hjL := ht j hj
      by_cases he : j = L
      · simp [he]
      · apply List.mem_append.mpr
        left
        apply List.mem_filter.mpr
        refine ⟨(List.mem_filter.mp hj).1, ?_⟩
        apply decide_eq_true
        have hc : ρ.sideAt j = ρ.sideAt L ∧ (0 = 0 ∨ j < 0) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        exact ⟨hc.1, Or.inr (by omega)⟩
    · intro hj
      rcases List.mem_append.mp hj with hj | hj
      · apply List.mem_filter.mpr
        refine ⟨(List.mem_filter.mp hj).1, ?_⟩
        apply decide_eq_true
        have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        exact ⟨hc.1, Or.inl rfl⟩
      · have he : j = L := by simpa using hj
        simpa [levelsOn, he] using hLs
  have hNormOwnLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
      (norm ρ L).levelsOn (ρ.sideAt L) 0 =
        ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
    have hNL : L ∈ (norm ρ L).levels := by
      apply (hLevelMem (norm ρ L) L).mpr
      rw [hDepth ρ L hL]
      omega
    have hAll : ∀ j ∈ (norm ρ L).levelsOn ((norm ρ L).sideAt L) 0, j ≤ L := by
      intro j hj
      have hjl := (List.mem_filter.mp hj).1
      have hjc : (norm ρ L).sideAt j = (norm ρ L).sideAt L ∧ (0 = 0 ∨ j < 0) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      have hh : up L j ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
        apply List.mem_filter.mpr
        refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
        apply decide_eq_true
        rw [← hSide ρ L j hL hjl, ← hSideL ρ L hL]
        exact ⟨hjc.1, Or.inl rfl⟩
      have hm := ht (up L j) hh
      dsimp [up] at hm
      split_ifs at hm <;> omega
    have hh := hSourceOwnLevels (norm ρ L) L hNL hAll
    rw [hSideL ρ L hL, hYoungLevels ρ L hL] at hh
    exact hh
  have hYoungFoldLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
      ∀ (ls : List ℕ), ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists → ∀ (z : ℕ × ℕ),
      ls.foldl (leftStep (norm ρ L)) z = ls.foldl (leftStep ρ) z := by
    intro ls
    have hGeneral : ∀ (ls : List ℕ),
        (∀ j ∈ ls, j ∈ ρ.levelsOn (ρ.sideAt L) L) → ∀ (z : ℕ × ℕ),
        ls.foldl (leftStep (norm ρ L)) z = ls.foldl (leftStep ρ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; rfl
      | cons j ls ih =>
        intro hj z
        have hjl := (List.mem_filter.mp (hj j (by simp))).1
        have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp (hj j (by simp))).2
        have hjlt : j < L := by omega
        have hj1 := ((hLevelMem ρ j).mp hjl).1
        have he := hExtNe ρ L j hj1 (by omega)
        rw [show up L j = j by simp [up, hjlt]] at he
        simp only [List.foldl_cons, leftStep, he]
        exact ih (fun i hi => hj i (by simp [hi])) _
    intro hls z
    exact hGeneral ls (fun j hj => (List.mem_sublists.mp hls).subset hj) z
  have hDecomposeSublists (Y T ls : List ℕ) (hls : ls ∈ (Y ++ T).sublists) :
      ∃ ys ∈ Y.sublists, ∃ ts ∈ T.sublists, ls = ys ++ ts := by
    rw [List.sublists_append, List.bind_eq_flatMap] at hls
    obtain ⟨ts, hts, hh⟩ := List.mem_flatMap.mp hls
    obtain ⟨ys, hys, he⟩ := List.mem_map.mp hh
    exact ⟨ys, hys, ts, hts, he.symm⟩
  have hFoldCountLeft (ρ : Context) : ∀ (ls : List ℕ) (z : ℕ × ℕ),
      (ls.foldl (leftStep ρ) z).2 ≤ z.2 + ls.length := by
    intro ls
    induction ls with
    | nil => intro z; simp
    | cons j ls ih =>
      intro z
      have hstep : (leftStep ρ z j).2 ≤ z.2 + 1 := by
        cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? <;>
          simp [leftStep, hh]
      have hh := ih (leftStep ρ z j)
      simp only [List.foldl_cons, List.length_cons]
      omega
  have hLeftStepAdd (ρ : Context) (j e c : ℕ)
      (hex : ∃ y ∈ ρ.extPositions j, y < e) :
      (leftStep ρ (e,c) j).2 = c + 1 := by
    cases hh : ((ρ.extPositions j).filter (· < e)).getLast? with
    | some y => simp [leftStep, hh]
    | none =>
      obtain ⟨y, hy, hye⟩ := hex
      have hm : y ∈ (ρ.extPositions j).filter (· < e) := by simp [hy, hye]
      rw [List.getLast?_eq_none_iff] at hh
      rw [hh] at hm
      exact False.elim (List.not_mem_nil hm)
  have hFoldBoundary (ρ : Context) (x : ℕ) (dir : Bool) :
      ∀ (ls : List ℕ),
      (∀ j ∈ ls, ∀ y ∈ ρ.extPositions j, if dir then y < x else x < y) →
      ∀ z : ℕ × ℕ, (if dir then z.1 < x else x < z.1) →
      (if dir then (ls.foldl (leftStep ρ) z).1 < x
        else x < (ls.foldl (leftStep ρ) z).1) ∧
      (if dir then (ls.foldl (rightStep ρ) z).1 < x
        else x < (ls.foldl (rightStep ρ) z).1) := by
    intro ls
    induction ls with
    | nil => intro _ z hz; exact ⟨hz,hz⟩
    | cons j ls ih =>
      intro hy z hz
      have ht := fun i hi y hiy => hy i (List.mem_cons_of_mem j hi) y hiy
      constructor
      · cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? with
        | none => simpa only [List.foldl_cons, leftStep, hh] using (ih ht z hz).1
        | some y =>
          have hm := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
          have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
          simpa only [List.foldl_cons, leftStep, hh] using (ih ht (y,z.2+1) hyx).1
      · cases hh : ((ρ.extPositions j).filter (z.1 < ·)).head? with
        | none => simpa only [List.foldl_cons, rightStep, hh] using (ih ht z hz).2
        | some y =>
          have hm := List.mem_of_mem_head? (Option.mem_def.mpr hh)
          have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
          simpa only [List.foldl_cons, rightStep, hh] using (ih ht (y,z.2+1) hyx).2
  have hSourceLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
      (hsingle : ρ.extPositions L = [x])
      (hafter : ∀ y ∈ ρ.extPositions (L+1), x < y)
      (hc : ∀ p ∈ ρ.childPositions, x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L+1)
      (p : ℕ) (hp : p ∈ ρ.childPositions) :
      ρ.leftExt (ρ.sideAt L) 0 p = ρ.leftExt (ρ.sideAt L) L p + 1 := by
    let Y := ρ.levelsOn (ρ.sideAt L) L
    have hnil : (ρ.extPositions (L+1)).filter (· < x) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro y hy
      simp [show ¬ y < x by have := hafter y hy; omega]
    have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
        ((ys ++ [L,L+1]).foldl (leftStep ρ) (p,0)).2 =
          (ys.foldl (leftStep ρ) (p,0)).2 + 1 := by
      let z := ys.foldl (leftStep ρ) (p,0)
      have hz := (hFoldBoundary ρ x false ys
        (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
        (p,0) (hc p hp)).1
      change x < z.1 at hz
      have hs : leftStep ρ z L = (x,z.2+1) := by
        simp [leftStep,hsingle,hz]
      rw [List.foldl_append]
      change (leftStep ρ (leftStep ρ z L) (L+1)).2 = z.2+1
      rw [hs]
      simp [leftStep,hnil]
    have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
        (ys.foldl (leftStep ρ) (p,0)).2 + 1 ≤ ρ.leftExt (ρ.sideAt L) 0 p := by
      have hsub : ys ++ [L,L+1] ∈ (ρ.levelsOn (ρ.sideAt L) 0).sublists := by
        rw [hSourcePairLevels ρ L hL ht]
        exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
      have hh : ((ys ++ [L,L+1]).foldl (leftStep ρ) (p,0)).2 ≤
          ρ.leftExt (ρ.sideAt L) 0 p := by
        rw [leftExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L,L+1],hsub,rfl⟩)
      rwa [hAdd ys hys] at hh
    apply le_antisymm
    · rw [leftExt_eq]
      apply getD_max?_le
      intro z hz
      obtain ⟨ls,hls,rfl⟩ := List.mem_map.mp hz
      rw [hSourcePairLevels ρ L hL ht] at hls
      obtain ⟨ys,hys,ts,hts,rfl⟩ := hDecomposeSublists Y [L,L+1] ls hls
      have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
          ρ.leftExt (ρ.sideAt L) L p := by
        rw [leftExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys,hys,rfl⟩)
      have htail : (ts.foldl (leftStep ρ) (ys.foldl (leftStep ρ) (p,0))).2 ≤
          (ys.foldl (leftStep ρ) (p,0)).2+1 := by
        change ts ∈ [[],[L],[L+1],[L,L+1]] at hts
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hts
        rcases hts with rfl | rfl | rfl | rfl
        · simp
        · simpa using hFoldCountLeft ρ [L] (ys.foldl (leftStep ρ) (p,0))
        · simpa using hFoldCountLeft ρ [L+1] (ys.foldl (leftStep ρ) (p,0))
        · have he := hAdd ys hys
          rw [List.foldl_append] at he
          exact he.le
      rw [List.foldl_append]
      exact htail.trans (Nat.add_le_add_right hprefix 1)
    · have h1 : 1 ≤ ρ.leftExt (ρ.sideAt L) 0 p := by
        simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
      have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤ ρ.leftExt (ρ.sideAt L) 0 p-1 := by
        rw [leftExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ys,hys,rfl⟩ := List.mem_map.mp hz
        have hh := hLe ys hys
        omega
      omega
  have hNormLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
      (hsingle : ρ.extPositions L = [x])
      (hc : ∀ p ∈ ρ.childPositions, x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (p : ℕ) (hp : p ∈ ρ.childPositions) :
      (norm ρ L).leftExt (ρ.sideAt L) 0 p = ρ.leftExt (ρ.sideAt L) L p + 1 := by
    let Y := ρ.levelsOn (ρ.sideAt L) L
    have hx : x ∈ (norm ρ L).extPositions L :=
      hMemMerged ρ L x (by simp [hsingle])
    have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
        ((ys ++ [L]).foldl (leftStep (norm ρ L)) (p,0)).2 =
          (ys.foldl (leftStep ρ) (p,0)).2 + 1 := by
      let z := ys.foldl (leftStep ρ) (p,0)
      have hz := (hFoldBoundary ρ x false ys
        (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
        (p,0) (hc p hp)).1
      change x < z.1 at hz
      rw [List.foldl_append, hYoungFoldLeft ρ L hL ys hys]
      change (leftStep (norm ρ L) z L).2 = z.2 + 1
      exact hLeftStepAdd (norm ρ L) L z.1 z.2 ⟨x, hx, hz⟩
    have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
        (ys.foldl (leftStep ρ) (p,0)).2 + 1 ≤
          (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
      have hsub : ys ++ [L] ∈ ((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists := by
        rw [hNormOwnLevels ρ L hL ht]
        exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
      have hh : ((ys ++ [L]).foldl (leftStep (norm ρ L)) (p,0)).2 ≤
          (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
        rw [leftExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L], hsub, rfl⟩)
      rwa [hAdd ys hys] at hh
    apply le_antisymm
    · rw [leftExt_eq]
      apply getD_max?_le
      intro z hz
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
      rw [hNormOwnLevels ρ L hL ht] at hls
      obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
      have hcount := hFoldCountLeft (norm ρ L) ts
        (ys.foldl (leftStep (norm ρ L)) (p,0))
      rw [hYoungFoldLeft ρ L hL ys hys] at hcount
      have hlen : ts.length ≤ 1 := by
        simpa using (List.mem_sublists.mp hts).length_le
      have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
          ρ.leftExt (ρ.sideAt L) L p := by
        rw [leftExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
      rw [List.foldl_append, hYoungFoldLeft ρ L hL ys hys]
      omega
    · have h1 : 1 ≤ (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
        simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
      have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤
          (norm ρ L).leftExt (ρ.sideAt L) 0 p - 1 := by
        rw [leftExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
        have hh := hLe ys hys
        omega
      omega
  have hYoungFoldRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
      ∀ (ls : List ℕ), ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists → ∀ (z : ℕ × ℕ),
      ls.foldl (rightStep (norm ρ L)) z = ls.foldl (rightStep ρ) z := by
    intro ls
    have hGeneral : ∀ (ls : List ℕ),
        (∀ j ∈ ls, j ∈ ρ.levelsOn (ρ.sideAt L) L) → ∀ (z : ℕ × ℕ),
        ls.foldl (rightStep (norm ρ L)) z = ls.foldl (rightStep ρ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; rfl
      | cons j ls ih =>
        intro hj z
        have hjl := (List.mem_filter.mp (hj j (by simp))).1
        have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp (hj j (by simp))).2
        have hjlt : j < L := by omega
        have hj1 := ((hLevelMem ρ j).mp hjl).1
        have he := hExtNe ρ L j hj1 (by omega)
        rw [show up L j = j by simp [up, hjlt]] at he
        simp only [List.foldl_cons, rightStep, he]
        exact ih (fun i hi => hj i (by simp [hi])) _
    intro hls z
    exact hGeneral ls (fun j hj => (List.mem_sublists.mp hls).subset hj) z
  have hMergedRightStep (ρ : Context) (L x : ℕ)
      (hsingle : ρ.extPositions L = [x]) (z : ℕ × ℕ) (hx : x < z.1) :
      rightStep (norm ρ L) z L = rightStep ρ z (L + 1) := by
    have he : ((norm ρ L).extPositions L).filter (z.1 < ·) =
        (ρ.extPositions (L + 1)).filter (z.1 < ·) := by
      have hs₁ : ((norm ρ L).extPositions L).Pairwise (· < ·) :=
        List.pairwise_lt_range.filter _
      have hs₂ : (ρ.extPositions (L + 1)).Pairwise (· < ·) :=
        List.pairwise_lt_range.filter _
      apply (hs₁.filter _).eq_of_mem_iff (hs₂.filter _)
      intro p
      rw [hExtMerged, hExtLv]
      simp only [List.mem_filter, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨hp, hpL | hpO⟩, hzp⟩
        · have hm : p ∈ ρ.extPositions L := by
            rw [hExtLv]
            exact List.mem_filter.mpr ⟨hp, hpL⟩
          have hpx : p = x := by simpa [hsingle] using hm
          omega
        · exact ⟨⟨hp, hpO⟩, hzp⟩
      · rintro ⟨⟨hp, hpO⟩, hzp⟩
        exact ⟨⟨hp, Or.inr hpO⟩, hzp⟩
    simp only [rightStep, he]
  have hNewRightStep (ρ : Context) (L x : ℕ)
      (hsingle : ρ.extPositions L = [x]) (z : ℕ × ℕ) (hx : x < z.1) :
      rightStep ρ z L = z := by
    rcases z with ⟨e,c⟩
    simp only at hx
    simp [rightStep, hsingle, show ¬ e < x by omega]
  have hOwnRight (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
      (hsingle : ρ.extPositions L = [x])
      (hc : ∀ p ∈ ρ.childPositions, x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (p : ℕ) (hp : p ∈ ρ.childPositions) :
      ρ.rightExt (ρ.sideAt L) 0 p = (norm ρ L).rightExt (ρ.sideAt L) 0 p := by
    let Y := ρ.levelsOn (ρ.sideAt L) L
    have hTail (ys ts : List ℕ) (hys : ys ∈ Y.sublists)
        (hts : ts ∈ [L, L + 1].sublists) :
        ∃ us ∈ [L].sublists,
          (ys ++ ts).foldl (rightStep ρ) (p,0) =
            (ys ++ us).foldl (rightStep (norm ρ L)) (p,0) := by
      let z := ys.foldl (rightStep ρ) (p,0)
      have hz := (hFoldBoundary ρ x false ys
        (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
        (p,0) (hc p hp)).2
      change x < z.1 at hz
      have hcases : ts = [] ∨ ts = [L] ∨ ts = [L + 1] ∨ ts = [L, L + 1] := by
        simpa [List.sublists_cons] using hts
      rcases hcases with rfl | rfl | rfl | rfl
      · refine ⟨[], by simp, ?_⟩
        simpa only [List.append_nil] using (hYoungFoldRight ρ L hL ys hys (p,0)).symm
      · refine ⟨[], by simp, ?_⟩
        rw [List.foldl_append, List.append_nil, hYoungFoldRight ρ L hL ys hys]
        change rightStep ρ z L = z
        exact hNewRightStep ρ L x hsingle z hz
      · refine ⟨[L], by simp [List.sublists_cons], ?_⟩
        rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
        change rightStep ρ z (L + 1) = rightStep (norm ρ L) z L
        exact (hMergedRightStep ρ L x hsingle z hz).symm
      · refine ⟨[L], by simp [List.sublists_cons], ?_⟩
        rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
        change rightStep ρ (rightStep ρ z L) (L + 1) = rightStep (norm ρ L) z L
        rw [hNewRightStep ρ L x hsingle z hz]
        exact (hMergedRightStep ρ L x hsingle z hz).symm
    have hBack (ys us : List ℕ) (hys : ys ∈ Y.sublists)
        (hus : us ∈ [L].sublists) :
        ∃ ts ∈ [L, L + 1].sublists,
          (ys ++ us).foldl (rightStep (norm ρ L)) (p,0) =
            (ys ++ ts).foldl (rightStep ρ) (p,0) := by
      let z := ys.foldl (rightStep ρ) (p,0)
      have hz := (hFoldBoundary ρ x false ys
        (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
        (p,0) (hc p hp)).2
      change x < z.1 at hz
      have hcases : us = [] ∨ us = [L] := by simpa [List.sublists_cons] using hus
      rcases hcases with rfl | rfl
      · refine ⟨[], by simp, ?_⟩
        simpa only [List.append_nil] using hYoungFoldRight ρ L hL ys hys (p,0)
      · refine ⟨[L + 1], by simp [List.sublists_cons], ?_⟩
        rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
        change rightStep (norm ρ L) z L = rightStep ρ z (L + 1)
        exact hMergedRightStep ρ L x hsingle z hz
    apply le_antisymm
    · rw [rightExt_eq]
      apply getD_max?_le
      intro z hz
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
      rw [hSourcePairLevels ρ L hL ht] at hls
      obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L, L + 1] ls hls
      obtain ⟨us, hus, he⟩ := hTail ys ts hys hts
      have hsub : ys ++ us ∈ ((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists := by
        rw [hNormOwnLevels ρ L hL ht]
        exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.mem_sublists.mp hus))
      rw [he, rightExt_eq]
      exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ us, hsub, rfl⟩)
    · rw [rightExt_eq]
      apply getD_max?_le
      intro z hz
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
      rw [hNormOwnLevels ρ L hL ht] at hls
      obtain ⟨ys, hys, us, hus, rfl⟩ := hDecomposeSublists Y [L] ls hls
      obtain ⟨ts, hts, he⟩ := hBack ys us hys hus
      have hsub : ys ++ ts ∈ (ρ.levelsOn (ρ.sideAt L) 0).sublists := by
        rw [hSourcePairLevels ρ L hL ht]
        exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.mem_sublists.mp hts))
      rw [he, rightExt_eq]
      exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ ts, hsub, rfl⟩)
  have hTopFilter (ρ : Context) (v : Side) (top : ℕ) (htop : 1 ≤ top) :
      ρ.levelsOn v top = (ρ.levelsOn v 0).filter (· < top) := by
    simp only [levelsOn, List.filter_filter]
    apply List.filter_congr
    intro j _
    simp [show top ≠ 0 by omega, Bool.and_comm]
  have hLevelsAtTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) :
      (norm ρ L).levelsOn (ρ.sideAt L) top = ρ.levelsOn (ρ.sideAt L) top := by
    rw [hTopFilter (norm ρ L) (ρ.sideAt L) top htop, hNormOwnLevels ρ L hL ht,
      hTopFilter ρ (ρ.sideAt L) top htop, hSourcePairLevels ρ L hL ht,
      List.filter_append, List.filter_append]
    simp [show ¬ L < top by omega, show ¬ L + 1 < top by omega]
  have hMidLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
      ρ.levelsOn (ρ.sideAt L) (L + 1) = ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
    rw [hTopFilter ρ (ρ.sideAt L) (L + 1) (by omega),
      hSourcePairLevels ρ L hL ht, List.filter_append]
    have hf : (ρ.levelsOn (ρ.sideAt L) L).filter (· < L + 1) =
        ρ.levelsOn (ρ.sideAt L) L := by
      apply List.filter_eq_self.mpr
      intro j hj
      apply decide_eq_true
      have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      omega
    rw [hf]
    simp
  have hYoungLeftTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) (p : ℕ) :
      (norm ρ L).leftExt (ρ.sideAt L) top p = ρ.leftExt (ρ.sideAt L) top p := by
    rw [leftExt_eq, leftExt_eq, hLevelsAtTop ρ L hL ht top htop htL]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    have hs : ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists :=
      List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans
        (levelsOn_sublist_of_le ρ (ρ.sideAt L) htop htL))
    exact congrArg Prod.snd (hYoungFoldLeft ρ L hL ls hs (p,0))
  have hYoungRightTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) (p : ℕ) :
      (norm ρ L).rightExt (ρ.sideAt L) top p = ρ.rightExt (ρ.sideAt L) top p := by
    rw [rightExt_eq, rightExt_eq, hLevelsAtTop ρ L hL ht top htop htL]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    have hs : ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists :=
      List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans
        (levelsOn_sublist_of_le ρ (ρ.sideAt L) htop htL))
    exact congrArg Prod.snd (hYoungFoldRight ρ L hL ls hs (p,0))
  have hMidLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
      (hsingle : ρ.extPositions L = [x])
      (hc : ∀ p ∈ ρ.childPositions, x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (p : ℕ) (hp : p ∈ ρ.childPositions) :
      ρ.leftExt (ρ.sideAt L) (L + 1) p = ρ.leftExt (ρ.sideAt L) L p + 1 := by
    let Y := ρ.levelsOn (ρ.sideAt L) L
    have hx : x ∈ ρ.extPositions L := by simp [hsingle]
    have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
        ((ys ++ [L]).foldl (leftStep ρ) (p,0)).2 =
          (ys.foldl (leftStep ρ) (p,0)).2 + 1 := by
      let z := ys.foldl (leftStep ρ) (p,0)
      have hz := (hFoldBoundary ρ x false ys
        (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
        (p,0) (hc p hp)).1
      change x < z.1 at hz
      rw [List.foldl_append]
      change (leftStep ρ z L).2 = z.2 + 1
      exact hLeftStepAdd ρ L z.1 z.2 ⟨x, hx, hz⟩
    have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
        (ys.foldl (leftStep ρ) (p,0)).2 + 1 ≤
          ρ.leftExt (ρ.sideAt L) (L + 1) p := by
      have hsub : ys ++ [L] ∈ (ρ.levelsOn (ρ.sideAt L) (L + 1)).sublists := by
        rw [hMidLevels ρ L hL ht]
        exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
      have hh : ((ys ++ [L]).foldl (leftStep ρ) (p,0)).2 ≤
          ρ.leftExt (ρ.sideAt L) (L + 1) p := by
        rw [leftExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L], hsub, rfl⟩)
      rwa [hAdd ys hys] at hh
    apply le_antisymm
    · rw [leftExt_eq]
      apply getD_max?_le
      intro z hz
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
      rw [hMidLevels ρ L hL ht] at hls
      obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
      have hcount := hFoldCountLeft ρ ts
        (ys.foldl (leftStep ρ) (p,0))
      have hlen : ts.length ≤ 1 := by
        simpa using (List.mem_sublists.mp hts).length_le
      have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
          ρ.leftExt (ρ.sideAt L) L p := by
        rw [leftExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
      rw [List.foldl_append]
      omega
    · have h1 : 1 ≤ ρ.leftExt (ρ.sideAt L) (L + 1) p := by
        simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
      have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤
          ρ.leftExt (ρ.sideAt L) (L + 1) p - 1 := by
        rw [leftExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
        have hh := hLe ys hys
        omega
      omega
  have hMidRight (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
      (hsingle : ρ.extPositions L = [x])
      (hc : ∀ p ∈ ρ.childPositions, x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (p : ℕ) (hp : p ∈ ρ.childPositions) :
      ρ.rightExt (ρ.sideAt L) (L + 1) p = ρ.rightExt (ρ.sideAt L) L p := by
    let Y := ρ.levelsOn (ρ.sideAt L) L
    apply le_antisymm
    · rw [rightExt_eq]
      apply getD_max?_le
      intro z hz
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
      rw [hMidLevels ρ L hL ht] at hls
      obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
      have hboundary := (hFoldBoundary ρ x false ys
        (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
        (p,0) (hc p hp)).2
      change x < (ys.foldl (rightStep ρ) (p,0)).1 at hboundary
      have hcases : ts = [] ∨ ts = [L] := by simpa [List.sublists_cons] using hts
      have hprefix : (ys.foldl (rightStep ρ) (p,0)).2 ≤
          ρ.rightExt (ρ.sideAt L) L p := by
        rw [rightExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
      rcases hcases with rfl | rfl
      · simpa only [List.append_nil] using hprefix
      · rw [List.foldl_append]
        change (rightStep ρ (ys.foldl (rightStep ρ) (p,0)) L).2 ≤ _
        rw [hNewRightStep ρ L x hsingle _ hboundary]
        exact hprefix
    · rw [rightExt_eq]
      apply getD_max?_le
      intro z hz
      obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
      have hsub : ys ∈ (ρ.levelsOn (ρ.sideAt L) (L + 1)).sublists := by
        rw [hMidLevels ρ L hL ht]
        exact List.mem_sublists.mpr (by
          simpa only [List.append_nil] using
            ((List.mem_sublists.mp hys).append (List.nil_sublist [L])))
      rw [rightExt_eq]
      exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hsub, rfl⟩)
  have hOwnChain (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
      (hsingle : ρ.extPositions L = [x])
      (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
      (hc : ∀ p ∈ ρ.childPositions, x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
      ρ.chainExt (ρ.sideAt L) p q = (norm ρ L).chainExt (ρ.sideAt L) p q := by
    have hl := hSourceLeft ρ L x hL hsingle hafter hc hy ht p hp
    have hn := hNormLeft ρ L x hL hsingle hc hy ht p hp
    have hr := hOwnRight ρ L x hL hsingle hc hy ht q hq
    unfold chainExt
    omega
  have hMaxAppend (A B : List ℕ) :
      ((A ++ B).max?).getD 0 = max (A.max?.getD 0) (B.max?.getD 0) := by
    apply le_antisymm
    · apply getD_max?_le
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact (le_getD_max?_of_mem hz).trans (le_max_left _ _)
      · exact (le_getD_max?_of_mem hz).trans (le_max_right _ _)
    · apply max_le
      · apply getD_max?_le_of_forall
        intro z hz
        exact ⟨z, List.mem_append_left _ hz, le_rfl⟩
      · apply getD_max?_le_of_forall
        intro z hz
        exact ⟨z, List.mem_append_right _ hz, le_rfl⟩
  have hMaxSingle (z : ℕ) : ([z].max?).getD 0 = z := by simp
  have hMaxPair (z w : ℕ) : ([z,w].max?).getD 0 = max z w := by
    simpa only [List.singleton_append, hMaxSingle] using hMaxAppend [z] [w]
  have hOwnJoin (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
      (hsingle : ρ.extPositions L = [x])
      (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
      (hc : ∀ p ∈ ρ.childPositions, x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
      ρ.joinExt (ρ.sideAt L) p q =
        (norm ρ L).joinExt (ρ.sideAt L) p q := by
    let f := fun j => ρ.leftExt (ρ.sideAt L) j p +
      ρ.rightExt (ρ.sideAt L) j q + ρ.maximumAt j
    let g := fun j => (norm ρ L).leftExt (ρ.sideAt L) j p +
      (norm ρ L).rightExt (ρ.sideAt L) j q + (norm ρ L).maximumAt j
    have hYoungMap :
        (ρ.levelsOn (ρ.sideAt L) L).map g =
          (ρ.levelsOn (ρ.sideAt L) L).map f := by
      apply List.map_congr_left
      intro j hj
      have hj1 := one_le_of_mem_levels (List.mem_filter.mp hj).1
      have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      have hjL : j < L := by have := hL.1; omega
      dsimp [f,g]
      rw [hYoungLeftTop ρ L hL ht j hj1 (by omega) p,
        hYoungRightTop ρ L hL ht j hj1 (by omega) q,
        hMax ρ L hL j hj1]
      simp only [hjL, if_true]
    have hMergedValue : g L = max (f L) (f (L + 1)) := by
      dsimp [f,g]
      rw [hYoungLeftTop ρ L hL ht L hL.1 le_rfl p,
        hYoungRightTop ρ L hL ht L hL.1 le_rfl q,
        hMax ρ L hL L hL.1,
        hMidLeft ρ L x hL hsingle hc hy ht p hp,
        hMidRight ρ L x hL hsingle hc hy ht q hq]
      simp only [lt_self_iff_false, if_false, if_true]
      omega
    change max (ρ.chainExt (ρ.sideAt L) p q)
        (((ρ.levelsOn (ρ.sideAt L) 0).map f).max?.getD 0) =
      max ((norm ρ L).chainExt (ρ.sideAt L) p q)
        ((((norm ρ L).levelsOn (ρ.sideAt L) 0).map g).max?.getD 0)
    rw [hOwnChain ρ L x hL hsingle hafter hc hy ht p q hp hq,
      hSourcePairLevels ρ L hL ht, hNormOwnLevels ρ L hL ht,
      List.map_append, List.map_append, hMaxAppend, hMaxAppend, hYoungMap]
    simp only [List.map_cons, List.map_nil, hMaxPair, hMaxSingle]
    rw [← hMergedValue]
  have hCaps (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
      (hsingle : ρ.extPositions L = [x])
      (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
      (hc : ∀ p ∈ ρ.childPositions, x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (hG : (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k)
      (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
      ρ.cupLimit p q = (norm ρ L).cupLimit p q ∧
      ρ.capLimit p q = (norm ρ L).capLimit p q := by
    have hc' := hOwnChain ρ L x hL hsingle hafter hc hy ht p q hp hq
    have hj' := hOwnJoin ρ L x hL hsingle hafter hc hy ht p q hp hq
    cases hs : ρ.sideAt L with
    | lower =>
      rw [hs] at hc' hj' hG
      change ρ.u ≤ ρ.k at hG
      have hOC := hOppChain ρ L hL Side.upper (by simp [hs]) p q
      have hOJ := hOppJoin ρ L hL Side.upper (by simp [hs]) p q
      have ha : (norm ρ L).a = ρ.a := rfl
      have hu : (norm ρ L).u = ρ.u := rfl
      unfold cupLimit capLimit
      rw [ha, hu, hK, hc', hj', hOC, hOJ]
      exact ⟨rfl,rfl⟩
    | upper =>
      rw [hs] at hc' hj' hG
      change ρ.a ≤ ρ.k at hG
      have hOC := hOppChain ρ L hL Side.lower (by simp [hs]) p q
      have hOJ := hOppJoin ρ L hL Side.lower (by simp [hs]) p q
      have ha : (norm ρ L).a = ρ.a := rfl
      have hu : (norm ρ L).u = ρ.u := rfl
      unfold cupLimit capLimit
      rw [ha, hu, hK, hc', hj', hOC, hOJ]
      exact ⟨rfl,rfl⟩
  have hNormPart (ρ : Context) (keep : List ℕ) (v : Side) (m L : ℕ) (hL1 : 1 ≤ L) :
      norm (ρ.part keep v m) (L + 1) = (norm ρ L).part keep v m := by
    have hw : (norm (ρ.part keep v m) (L + 1)).word = ((norm ρ L).part keep v m).word := by
      change ((ρ.part keep v m).word.map (letter (L + 1))) =
        (List.range (norm ρ L).word.length).map (fun p => match (norm ρ L).letterAt p with
          | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 v
          | Letter.ext j w => Letter.ext (j + 1) w)
      rw [hLen]
      simp only [part, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro p _
      rw [hLetter]
      cases ρ.letterAt p with
      | child => by_cases hp : p ∈ keep <;> simp [hp, letter]
      | ext j w =>
        by_cases hj : j ≤ L
        · simp [letter, hj]
        · simp [letter, hj, show j - 1 + 1 = j by omega]
    have e1 : (m :: ρ.maxima).take (L + 1 - 1) = m :: ρ.maxima.take (L - 1) := by
      rw [show L + 1 - 1 = (L - 1) + 1 by omega, List.take_succ_cons]
    have e2 : (m :: ρ.maxima).drop (L + 1 + 1) = ρ.maxima.drop (L + 1) := by
      rw [List.drop_succ_cons]
    have e3 : (ρ.part keep v m).maximumAt (L + 1) = ρ.maximumAt L := by
      simp only [maximumAt, part_maxima]
      rw [show L + 1 - 1 = (L - 1) + 1 by omega, List.getElem?_cons_succ]
    have e4 : (ρ.part keep v m).maximumAt (L + 1 + 1) = ρ.maximumAt (L + 1) := by
      simp only [maximumAt, part_maxima]
      rw [show L + 1 + 1 - 1 = (L + 1 - 1) + 1 by omega, List.getElem?_cons_succ]
    have hmx : (norm (ρ.part keep v m) (L + 1)).maxima = ((norm ρ L).part keep v m).maxima := by
      show (m :: ρ.maxima).take (L + 1 - 1) ++
          [max ((ρ.part keep v m).maximumAt (L + 1)) ((ρ.part keep v m).maximumAt (L + 1 + 1) + 1)] ++
          (m :: ρ.maxima).drop (L + 1 + 1) =
        m :: (ρ.maxima.take (L - 1) ++ [max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)] ++ ρ.maxima.drop (L + 1))
      rw [e1, e2, e3, e4]
      rfl
    have ha : (norm (ρ.part keep v m) (L+1)).a = ((norm ρ L).part keep v m).a := rfl
    have hu : (norm (ρ.part keep v m) (L+1)).u = ((norm ρ L).part keep v m).u := rfl
    exact ctx_ext ha hu rfl hw hmx
  have hInvPart (ρ : Context) (L : ℕ) (hL : Inv ρ L) (keep : List ℕ) (v : Side) (m : ℕ) :
      Inv (ρ.part keep v m) (L + 1) := by
    obtain ⟨h1, h2, h3, h4⟩ := hL
    refine ⟨by omega, by simp only [part_maxima, List.length_cons]; omega, ?_, ?_⟩
    · intro p j w hp hj
      rw [part_sideAt_succ ρ keep v m h1]
      by_cases hplen : p < ρ.word.length
      · cases hlet : ρ.letterAt p with
        | child =>
          rw [part_letterAt_of_child ρ keep v m hplen hlet] at hp
          by_cases hk : p ∈ keep
          · simp [hk] at hp
          · simp only [hk, if_false, Letter.ext.injEq] at hp
            obtain ⟨hj1, -⟩ := hp
            omega
        | ext i u =>
          rw [part_letterAt_of_ext ρ keep v m hplen hlet, Letter.ext.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact h3 p i u hlet (by omega)
      · rw [letterAt_of_length_le _ (by rw [part_word_length]; omega)] at hp
        cases hp
    · rw [part_sideAt_succ ρ keep v m h1, part_sideAt_succ ρ keep v m (by omega : 1 ≤ L + 1)]
      exact h4
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
  have hNextTerminal (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ j ∈ (ρ.part keep v m).levelsOn ((ρ.part keep v m).sideAt (L+1)) 0, j ≤ L+1+1 := by
    intro j hj
    have hj1 := (one_le_of_mem_levelsOn hj).1
    have hL1 := one_le_of_mem_levels hL
    by_cases he : j = 1
    · omega
    · let i := j-1
      have hi : 1 ≤ i := by dsimp [i]; omega
      have he : j = i+1 := by dsimp [i]; omega
      rw [he] at hj ⊢
      have hjLevel : i+1 ∈ (ρ.part keep v m).levels := (List.mem_filter.mp hj).1
      rw [part_levels] at hjLevel
      have hiLevel : i ∈ ρ.levels := by
        rcases List.mem_cons.mp hjLevel with h | h
        · omega
        · obtain ⟨z, hz, hzi⟩ := List.mem_map.mp h
          have hz' : z = i := by omega
          simpa only [hz'] using hz
      have hjc : (ρ.part keep v m).sideAt (i+1) = (ρ.part keep v m).sideAt (L+1) ∧
          (0 = 0 ∨ i+1 < 0) := of_decide_eq_true (List.mem_filter.mp hj).2
      rw [part_sideAt_succ ρ keep v m hi, part_sideAt_succ ρ keep v m hL1] at hjc
      have hiOn : i ∈ ρ.levelsOn (ρ.sideAt L) 0 :=
        List.mem_filter.mpr ⟨hiLevel, by simp [hjc.1]⟩
      have := ht i hiOn
      omega
  have hBase (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
      (hsingle : ρ.extPositions L = [x])
      (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
      (hc : ∀ p ∈ ρ.childPositions, x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
      (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
      (hG : (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k) :
      ρ.base = (norm ρ L).base := by
    rw [base_eq_baseOf, base_eq_baseOf, hChild]
    cases hh : ρ.childPositions.head? with
    | none => rfl
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      have h := hCaps ρ L x hL hsingle hafter hc hy ht hG p p hp hp
      simp only [baseOf, h.1, h.2, hK]
  have hFuel : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      ∀ (L x : ℕ), Inv ρ L → ρ.extPositions L = [x] →
      (∀ y ∈ ρ.extPositions (L + 1), x < y) →
      (∀ p ∈ ρ.childPositions, x < p) →
      (∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p) →
      (∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) →
      (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k →
      boundFuel fuel ρ = boundFuel fuel (norm ρ L) := by
    intro fuel
    induction fuel with
    | zero => intro ρ hPos L x hL hsingle hafter hc hy ht hG; rfl
    | succ fuel ih =>
      intro ρ hPos L x hL hsingle hafter hc hy ht hG
      have hL1 := hL.1
      have hLn : L ∈ ρ.levels :=
        (hLevelMem ρ L).mpr ⟨hL1, by have := hL.2.1; omega⟩
      have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
          boundFuel fuel (ρ.part keep v m) =
            boundFuel fuel ((norm ρ L).part keep v m) := by
        have hs' : (ρ.part keep v m).extPositions (L + 1) = [x] := by
          rw [part_extPositions_succ ρ keep v m hL1, hsingle]
        have hb' : ∀ y ∈ (ρ.part keep v m).extPositions (L + 1 + 1), x < y := by
          rw [part_extPositions_succ ρ keep v m (by omega : 1 ≤ L + 1)]
          exact hafter
        have hd := hNextBoundary ρ hPos L x hLn false hc hy keep v m
        have hg' : (match (ρ.part keep v m).sideAt (L + 1) with
            | Side.lower => (ρ.part keep v m).u
            | Side.upper => (ρ.part keep v m).a) ≤ (ρ.part keep v m).k := by
          rw [part_sideAt_succ ρ keep v m hL1]
          exact hG
        have h := ih (ρ.part keep v m) (hPartPositive ρ keep v m)
          (L + 1) x (hInvPart ρ L hL keep v m) hs' hb' hd.1 hd.2
          (hNextTerminal ρ L hLn ht keep v m) hg'
        rw [hNormPart ρ keep v m L hL1] at h
        exact h
      simp only [boundFuel, hRuns, hChild, hBlocks, hK]
      split_ifs
      · exact hBase ρ L x hL hsingle hafter hc hy ht hG
      · congr 1
        apply congrArg List.max?
        apply List.flatMap_congr
        intro keep _
        apply List.flatMap_congr
        intro m _
        simp only [hParts]
  refine ⟨fun p hp q hq =>
    hCaps σ N x hpair hsole hafter hchildren hyounger holdest hglobal p q hp hq,
    fun fuel => hFuel fuel σ hpositive N x hpair hsole hafter hchildren hyounger holdest hglobal,
    ?_⟩
  simpa only [bound, hChild] using
    hFuel (σ.childPositions.length + 1) σ hpositive N x hpair hsole hafter
      hchildren hyounger holdest hglobal

end ErdosSzekeres
