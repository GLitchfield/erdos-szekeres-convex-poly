import ESBlueprint.B.CtxPartLimitsLe

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Erasing an arbitrary indexed external level can only increase all cup/cap limits and every fuel approximation of the recursive bound. Delete its maximum, relabel its letters to an inactive level, and shift larger labels down by one, preserving the entire pattern of child and external positions. The transformation commutes with taking parts. Indexed membership alone suffices. This supports isolating relevant external history in the unresolved marker and uniform-gap comparisons.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_erase_level_bound_mono (σ : Ctx.Context) (N : ℕ) (hN : N ∈ σ.levels) :
  let τ : Ctx.Context := { σ with
    word := σ.word.map (fun x => match x with
      | Ctx.Letter.child => Ctx.Letter.child
      | Ctx.Letter.ext j v => Ctx.Letter.ext
          (if j = N then σ.maxima.length else if N < j then j - 1 else j) v)
    maxima := σ.maxima.eraseIdx (N - 1) }
  (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧
    σ.bound ≤ τ.bound := by
  classical
  let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
  let letter (D L : ℕ) : Letter → Letter := fun x => match x with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext (idx D L j) v
  let norm (ρ : Context) (L : ℕ) : Context :=
    { ρ with word := ρ.word.map (letter ρ.maxima.length L), maxima := ρ.maxima.eraseIdx (L-1) }
  let up (L j : ℕ) := if j < L then j else j+1
  change (∀ p q, σ.cupLimit p q ≤ (norm σ N).cupLimit p q ∧
      σ.capLimit p q ≤ (norm σ N).capLimit p q) ∧
    (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel (norm σ N)) ∧ σ.bound ≤ (norm σ N).bound
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
  have hMaximum (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) : (norm ρ L).maximumAt j = ρ.maximumAt (up L j) := by
    have hh := (hLevelMem ρ L).mp hL
    have hj' := (hLive ρ L j hL hj).1
    simp only [maximumAt, norm, List.getElem?_eraseIdx]
    by_cases h : j < L
    · simp [up, h, show j-1 < L-1 by omega]
    · simp [up, h, show ¬j-1 < L-1 by omega, show j-1+1 = j by omega]
  have hUpMono (L i j : ℕ) (h : i < j) : up L i < up L j := by
    dsimp [up]; split_ifs <;> omega
  have hUpZero (L : ℕ) (hL : 1 ≤ L) : up L 0 = 0 := by simp [up, show 0 < L by omega]
  have hSub (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side) (top : ℕ) :
      (((norm ρ L).levelsOn v top).map (up L)).Sublist (ρ.levelsOn v (up L top)) := by
    have hs : (((norm ρ L).levelsOn v top).map (up L)).Pairwise (· < ·) :=
      ((hSorted (norm ρ L)).filter _).map (up L) (fun i j hij => hUpMono L i j hij)
    have ho : (ρ.levelsOn v (up L top)).Pairwise (· < ·) := (hSorted ρ).filter _
    have hsubset : (((norm ρ L).levelsOn v top).map (up L)) ⊆ ρ.levelsOn v (up L top) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      have hjl := (List.mem_filter.mp hj).1
      have hjc : (norm ρ L).sideAt j = v ∧ (top = 0 ∨ j < top) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      apply List.mem_filter.mpr
      refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
      apply decide_eq_true
      refine ⟨?_, ?_⟩
      · rw [← hSide ρ L j hL hjl]; exact hjc.1
      · rcases hjc.2 with rfl | hlt
        · exact Or.inl (hUpZero L (one_le_of_mem_levels hL))
        · exact Or.inr (hUpMono L j top hlt)
    have he : (ρ.levelsOn v (up L top)).filter
        (· ∈ (((norm ρ L).levelsOn v top).map (up L))) =
        (((norm ρ L).levelsOn v top).map (up L)) := by
      apply (ho.filter _).eq_of_mem_iff hs
      intro x
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun hx => ⟨hsubset hx, hx⟩⟩
    rw [← he]
    exact List.filter_sublist
  have hFoldLeft (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (norm ρ L).levels) → ∀ z,
      ls.foldl (leftStep (norm ρ L)) z = (ls.map (up L)).foldl (leftStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ z; rfl
    | cons j ls ih =>
      intro hj z
      simp only [List.foldl_cons, List.map_cons, leftStep, hExt ρ L j hL (hj j (by simp))]
      exact ih (fun i hi => hj i (by simp [hi])) _
  have hFoldRight (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (norm ρ L).levels) → ∀ z,
      ls.foldl (rightStep (norm ρ L)) z = (ls.map (up L)).foldl (rightStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ z; rfl
    | cons j ls ih =>
      intro hj z
      simp only [List.foldl_cons, List.map_cons, rightStep, hExt ρ L j hL (hj j (by simp))]
      exact ih (fun i hi => hj i (by simp [hi])) _
  have hLeftLe (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side) (top p : ℕ) :
      (norm ρ L).leftExt v top p ≤ ρ.leftExt v (up L top) p := by
    simp only [leftExt_eq]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    have hsub := List.mem_sublists.mp hls
    have hl : ∀ j ∈ ls, j ∈ (norm ρ L).levels :=
      fun j hj => (List.mem_filter.mp (hsub.subset hj)).1
    refine ⟨_, List.mem_map.mpr ⟨ls.map (up L),
      List.mem_sublists.mpr ((hsub.map _).trans (hSub ρ L hL v top)), rfl⟩, ?_⟩
    exact le_of_eq (congrArg Prod.snd (hFoldLeft ρ L hL ls hl (p,0)))
  have hRightLe (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side) (top p : ℕ) :
      (norm ρ L).rightExt v top p ≤ ρ.rightExt v (up L top) p := by
    simp only [rightExt_eq]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    have hsub := List.mem_sublists.mp hls
    have hl : ∀ j ∈ ls, j ∈ (norm ρ L).levels :=
      fun j hj => (List.mem_filter.mp (hsub.subset hj)).1
    refine ⟨_, List.mem_map.mpr ⟨ls.map (up L),
      List.mem_sublists.mpr ((hsub.map _).trans (hSub ρ L hL v top)), rfl⟩, ?_⟩
    exact le_of_eq (congrArg Prod.snd (hFoldRight ρ L hL ls hl (p,0)))
  have hChainLe (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side) (p q : ℕ) :
      (norm ρ L).chainExt v p q ≤ ρ.chainExt v p q := by
    simpa only [chainExt, hUpZero L (one_le_of_mem_levels hL)] using
      Nat.add_le_add (hLeftLe ρ L hL v 0 p) (hRightLe ρ L hL v 0 q)
  have hJoinLe (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side) (p q : ℕ) :
      (norm ρ L).joinExt v p q ≤ ρ.joinExt v p q := by
    unfold joinExt
    apply max_le_max (hChainLe ρ L hL v p q)
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hjl := (List.mem_filter.mp hj).1
    have hmem := (hSub ρ L hL v 0).subset (List.mem_map.mpr ⟨j, hj, rfl⟩)
    rw [hUpZero L (one_le_of_mem_levels hL)] at hmem
    refine ⟨_, List.mem_map.mpr ⟨up L j, hmem, rfl⟩, ?_⟩
    rw [hMaximum ρ L j hL hjl]
    exact Nat.add_le_add_right (Nat.add_le_add (hLeftLe ρ L hL v j p) (hRightLe ρ L hL v j q)) _
  have hCaps (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (p q : ℕ) :
      ρ.cupLimit p q ≤ (norm ρ L).cupLimit p q ∧
      ρ.capLimit p q ≤ (norm ρ L).capLimit p q := by
    have hcl := hChainLe ρ L hL Side.lower p q
    have hcu := hChainLe ρ L hL Side.upper p q
    have hjl := hJoinLe ρ L hL Side.lower p q
    have hju := hJoinLe ρ L hL Side.upper p q
    have ha : (norm ρ L).a = ρ.a := rfl
    have hu : (norm ρ L).u = ρ.u := rfl
    dsimp only [cupLimit, capLimit]
    rw [ha, hu, hK]
    omega
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
  have hBase (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) : ρ.base ≤ (norm ρ L).base := by
    rw [base_eq_baseOf, base_eq_baseOf, hChild]
    cases hh : ρ.childPositions.head? with
    | none => exact le_rfl
    | some p =>
      have h := baseOf_mono (k := ρ.k) (hCaps ρ L hL p p).1 (hCaps ρ L hL p p).2
      simpa only [hK] using h
  have hFuel : ∀ fuel (ρ : Context) (L : ℕ), L ∈ ρ.levels →
      boundFuel fuel ρ ≤ boundFuel fuel (norm ρ L) := by
    intro fuel
    induction fuel with
    | zero => intro ρ L _; exact le_rfl
    | succ fuel ih =>
      intro ρ L hL
      have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
          boundFuel fuel (ρ.part keep v m) ≤ boundFuel fuel ((norm ρ L).part keep v m) := by
        have hnext : L + 1 ∈ (ρ.part keep v m).levels := by
          rw [part_levels]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L, hL, rfl⟩)
        have h := ih (ρ.part keep v m) (L + 1) hnext
        rw [hNormPart ρ keep v m L (one_le_of_mem_levels hL)] at h
        exact h
      simp only [boundFuel, hRuns, hChild, hBlocks, hK]
      split_ifs
      · exact hBase ρ L hL
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
  refine ⟨fun p q => hCaps σ N hN p q, fun fuel => hFuel fuel σ N hN, ?_⟩
  simpa only [bound, hChild] using hFuel (σ.childPositions.length + 1) σ N hN


end ErdosSzekeres
