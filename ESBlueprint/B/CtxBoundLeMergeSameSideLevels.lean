import ESBlueprint.B.CtxPartLimitsLe

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace MergeLevels

/-- The last element of a filter by a disjunction is the last element of one of the two filters. -/
theorem getLast?_filter_lt_or (l : List ℕ) (A B : ℕ → Bool) (e : ℕ) :
    ((l.filter (fun p => A p || B p)).filter (fun x => decide (x < e))).getLast? =
        ((l.filter A).filter (fun x => decide (x < e))).getLast? ∨
      ((l.filter (fun p => A p || B p)).filter (fun x => decide (x < e))).getLast? =
        ((l.filter B).filter (fun x => decide (x < e))).getLast? := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton t a ih =>
    cases hA : A a <;> cases hB : B a <;> by_cases he : a < e <;>
      first
      | (simpa [List.filter_append, hA, hB, he] using ih)
      | (simp [List.filter_append, hA, hB, he])

/-- The first element of a filter by a disjunction is the first element of one of the two filters. -/
theorem head?_filter_gt_or (l : List ℕ) (A B : ℕ → Bool) (e : ℕ) :
    ((l.filter (fun p => A p || B p)).filter (fun x => decide (e < x))).head? =
        ((l.filter A).filter (fun x => decide (e < x))).head? ∨
      ((l.filter (fun p => A p || B p)).filter (fun x => decide (e < x))).head? =
        ((l.filter B).filter (fun x => decide (e < x))).head? := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases hA : A a <;> cases hB : B a <;> by_cases he : e < a <;>
      first
      | (simpa [List.filter_cons, hA, hB, he] using ih)
      | (simp [List.filter_cons, hA, hB, he])

/-- A strictly increasing list whose members lie in a strictly increasing list is a sublist of it. -/
theorem sublist_of_pairwise_lt {xs ys : List ℕ} (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·))
    (hsub : ∀ x ∈ xs, x ∈ ys) : xs.Sublist ys := by
  have he : ys.filter (· ∈ xs) = xs := by
    apply (hy.filter _).eq_of_mem_iff hx
    intro a
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨hsub a h, h⟩⟩
  rw [← he]
  exact List.filter_sublist

theorem levelsOn_sublist_of_le (σ : Context) (s : Side) {t t' : ℕ} (ht : 1 ≤ t) (htt : t ≤ t') :
    (σ.levelsOn s t).Sublist (σ.levelsOn s t') := by
  unfold levelsOn
  apply List.monotone_filter_right
  intro a ha
  simp only [decide_eq_true_eq] at ha ⊢
  obtain ⟨hs, ht'⟩ := ha
  exact ⟨hs, by omega⟩

theorem leftExt_mono_top (σ : Context) (s : Side) {t t' : ℕ} (ht : 1 ≤ t) (htt : t ≤ t') (p : ℕ) :
    σ.leftExt s t p ≤ σ.leftExt s t' p := by
  rw [leftExt_eq, leftExt_eq]
  apply Ctx.getD_max?_le_of_forall
  intro x hx
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
  exact ⟨_, List.mem_map.mpr ⟨ls, List.mem_sublists.mpr
    ((List.mem_sublists.mp hls).trans (levelsOn_sublist_of_le σ s ht htt)), rfl⟩, le_rfl⟩

theorem rightExt_mono_top (σ : Context) (s : Side) {t t' : ℕ} (ht : 1 ≤ t) (htt : t ≤ t') (p : ℕ) :
    σ.rightExt s t p ≤ σ.rightExt s t' p := by
  rw [rightExt_eq, rightExt_eq]
  apply Ctx.getD_max?_le_of_forall
  intro x hx
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
  exact ⟨_, List.mem_map.mpr ⟨ls, List.mem_sublists.mpr
    ((List.mem_sublists.mp hls).trans (levelsOn_sublist_of_le σ s ht htt)), rfl⟩, le_rfl⟩

theorem getElem?_merge (xs : List ℕ) (L i x : ℕ) (hL : 1 ≤ L) (hlen : L + 1 ≤ xs.length) :
    (xs.take (L - 1) ++ [x] ++ xs.drop (L + 1))[i]? =
      if i < L - 1 then xs[i]? else if i = L - 1 then some x else xs[i + 1]? := by
  have htl : (xs.take (L - 1)).length = L - 1 := by simp; omega
  rw [List.append_assoc, List.getElem?_append]
  rw [htl]
  split_ifs with h1 h2
  · rw [List.getElem?_take]; simp [h1]
  · subst h2; simp
  · simp only [List.singleton_append, List.getElem?_cons, List.getElem?_drop]
    rw [if_neg (by omega)]
    congr 1
    omega

theorem ctx_ext {σ τ : Context} (ha : σ.a = τ.a) (hu : σ.u = τ.u) (hk : σ.k = τ.k)
    (hw : σ.word = τ.word) (hm : σ.maxima = τ.maxima) : σ = τ := by
  cases σ; cases τ
  simp only at ha hu hk hw hm
  subst ha hu hk hw hm
  rfl

/-- The invariant carried through the recursion: the two merged levels exist, every letter of
either level lies on the first level's side, and the two levels report the same side. -/
abbrev Inv (ρ : Context) (L : ℕ) : Prop := 1 ≤ L ∧ L + 1 ≤ ρ.maxima.length ∧
  (∀ p j v, ρ.letterAt p = Letter.ext j v → (j = L ∨ j = L + 1) → v = ρ.sideAt L) ∧
  ρ.sideAt L = ρ.sideAt (L + 1)

end MergeLevels

open MergeLevels

/-- Merging two adjacent external levels on the same side never lowers the context bound. Relabel the letters of level l+1 as level l, shift every higher level down by one, and give the merged level the larger of the two sibling maxima. Extensions cannot grow: at the merged level the greedy step's letter is the rightmost of either original level, so every merged extension walk is an original walk. Joins cannot grow either, the limits and base values do not decrease, merging commutes with taking parts, and induction on fuel finishes. Smaller merged maxima follow by ctx_bound_antitone. Evidence: 758,000 merges at k = 5 to 7 with no failure (Track A, exchange/lemmas).
@node
@ws B
@kind formalization
@dangling-ok general level-merge monotonicity for rotation and exchange arguments on cut trees (Claude run claude-uniform-mechanism-20260928, Track A lemma MERGE); no current consumer -/
theorem ctx_bound_le_merge_same_side_levels (σ : Ctx.Context) (hwf : σ.WellFormed) (l : ℕ) (hl : 1 ≤ l) (hl2 : l + 1 ≤ σ.maxima.length) (hside : σ.sideAt l = σ.sideAt (l + 1)) : σ.bound ≤ ({ σ with word := σ.word.map (fun x => match x with | Ctx.Letter.ext j s => if j ≤ l then Ctx.Letter.ext j s else Ctx.Letter.ext (j - 1) s | Ctx.Letter.child => Ctx.Letter.child), maxima := σ.maxima.take (l - 1) ++ [max (σ.maximumAt l) (σ.maximumAt (l + 1))] ++ σ.maxima.drop (l + 1) } : Ctx.Context).bound := by
  classical
  let letter (L : ℕ) : Letter → Letter := fun x => match x with
    | Letter.ext j s => if j ≤ L then Letter.ext j s else Letter.ext (j - 1) s
    | Letter.child => Letter.child
  let norm (ρ : Context) (L : ℕ) : Context :=
    { ρ with
      word := ρ.word.map (letter L)
      maxima := ρ.maxima.take (L - 1) ++ [max (ρ.maximumAt L) (ρ.maximumAt (L + 1))] ++
        ρ.maxima.drop (L + 1) }
  let lv (ρ : Context) (i : ℕ) : ℕ → Bool := fun p => match ρ.letterAt p with
    | Letter.ext j _ => decide (j = i)
    | Letter.child => false
  let up (L j : ℕ) := if j < L then j else j + 1
  let upTop (L t : ℕ) := if t ≤ L then t else t + 1
  let img (L j x : ℕ) : Prop := (j < L ∧ x = j) ∨ (j = L ∧ (x = L ∨ x = L + 1)) ∨ (L < j ∧ x = j + 1)
  change σ.bound ≤ (norm σ l).bound
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
        if j < L then ρ.maximumAt j else if j = L then max (ρ.maximumAt L) (ρ.maximumAt (L + 1))
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
  -- one greedy step ----------------------------------------------------------
  have hStepL (ρ : Context) (L : ℕ) (e c j : ℕ) (hj1 : 1 ≤ j) :
      ∃ x, img L j x ∧ leftStep (norm ρ L) (e, c) j = leftStep ρ (e, c) x := by
    by_cases hjL : j = L
    · subst hjL
      rcases getLast?_filter_lt_or (List.range ρ.word.length) (lv ρ j) (lv ρ (j + 1)) e with h | h
      · refine ⟨j, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩), ?_⟩
        simp only [leftStep, hExtMerged, hExtLv ρ j, h]
      · refine ⟨j + 1, Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩), ?_⟩
        simp only [leftStep, hExtMerged, hExtLv ρ (j + 1), h]
    · refine ⟨up L j, ?_, ?_⟩
      · dsimp only [img, up]; split_ifs <;> omega
      · simp only [leftStep, hExtNe ρ L j hj1 hjL]
  have hStepR (ρ : Context) (L : ℕ) (e c j : ℕ) (hj1 : 1 ≤ j) :
      ∃ x, img L j x ∧ rightStep (norm ρ L) (e, c) j = rightStep ρ (e, c) x := by
    by_cases hjL : j = L
    · subst hjL
      rcases head?_filter_gt_or (List.range ρ.word.length) (lv ρ j) (lv ρ (j + 1)) e with h | h
      · refine ⟨j, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩), ?_⟩
        simp only [rightStep, hExtMerged, hExtLv ρ j, h]
      · refine ⟨j + 1, Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩), ?_⟩
        simp only [rightStep, hExtMerged, hExtLv ρ (j + 1), h]
    · refine ⟨up L j, ?_, ?_⟩
      · dsimp only [img, up]; split_ifs <;> omega
      · simp only [rightStep, hExtNe ρ L j hj1 hjL]
  -- membership of the simulated level ------------------------------------------
  have hImgMem (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side) (top j x : ℕ)
      (hj : j ∈ (norm ρ L).levelsOn v top) (hx : img L j x) : x ∈ ρ.levelsOn v (upTop L top) := by
    obtain ⟨hjl, hjc⟩ := List.mem_filter.mp hj
    have hjc' : (norm ρ L).sideAt j = v ∧ (top = 0 ∨ j < top) := of_decide_eq_true hjc
    have hjr := hNormLevel ρ L hL j hjl
    obtain ⟨h1, h2, h3, h4⟩ := hL
    apply List.mem_filter.mpr
    refine ⟨(hLevelMem ρ x).mpr (by dsimp only [img] at hx; omega), decide_eq_true ⟨?_, ?_⟩⟩
    · rw [← hjc'.1]
      dsimp only [img] at hx
      rcases hx with ⟨hlt, hxj⟩ | ⟨hjL, hxL | hxL⟩ | ⟨hlt, hxj⟩
      · rw [hxj, hSideNe ρ L j hjr.1 (by omega)]; dsimp only [up]; simp [hlt]
      · rw [hxL, hjL, hSideL ρ L ⟨h1, h2, h3, h4⟩]
      · rw [hxL, hjL, hSideL ρ L ⟨h1, h2, h3, h4⟩, h4]
      · rw [hxj, hSideNe ρ L j hjr.1 (by omega)]; dsimp only [up]; simp [show ¬ j < L by omega]
    · rcases hjc'.2 with htop | hlt
      · left; subst htop; simp [upTop]
      · right; dsimp only [upTop, img] at hx ⊢; split_ifs <;> omega
  -- whole walks ----------------------------------------------------------------
  have hWalkL (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side) (top : ℕ) :
      ∀ ls : List ℕ, ls.Pairwise (· < ·) → (∀ j ∈ ls, j ∈ (norm ρ L).levelsOn v top) → ∀ z : ℕ × ℕ,
        ∃ ls' : List ℕ, ls'.Pairwise (· < ·) ∧ (∀ x ∈ ls', x ∈ ρ.levelsOn v (upTop L top)) ∧
          (∀ x ∈ ls', ∃ j ∈ ls, img L j x) ∧
          ls.foldl (leftStep (norm ρ L)) z = ls'.foldl (leftStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ _ z; exact ⟨[], List.Pairwise.nil, by simp, by simp, rfl⟩
    | cons j rest ih =>
      intro hpw hmem z
      obtain ⟨e, c⟩ := z
      have hjl : j ∈ (norm ρ L).levels := (List.mem_filter.mp (hmem j (by simp))).1
      have hj1 := (hNormLevel ρ L hL j hjl).1
      obtain ⟨x, hx, hstep⟩ := hStepL ρ L e c j hj1
      obtain ⟨rest', hpw', hmem', himg', hfold⟩ :=
        ih (List.pairwise_cons.mp hpw).2 (fun i hi => hmem i (by simp [hi])) (leftStep (norm ρ L) (e, c) j)
      refine ⟨x :: rest', ?_, ?_, ?_, ?_⟩
      · refine List.pairwise_cons.mpr ⟨?_, hpw'⟩
        intro y hy
        obtain ⟨r, hr, hry⟩ := himg' y hy
        have hjr : j < r := (List.pairwise_cons.mp hpw).1 r hr
        dsimp only [img] at hx hry
        omega
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hImgMem ρ L hL v top j y (hmem j (by simp)) hx
        · exact hmem' y hy
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨j, by simp, hx⟩
        · obtain ⟨r, hr, hry⟩ := himg' y hy
          exact ⟨r, by simp [hr], hry⟩
      · simp only [List.foldl_cons]
        rw [← hstep]
        exact hfold
  have hWalkR (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side) (top : ℕ) :
      ∀ ls : List ℕ, ls.Pairwise (· < ·) → (∀ j ∈ ls, j ∈ (norm ρ L).levelsOn v top) → ∀ z : ℕ × ℕ,
        ∃ ls' : List ℕ, ls'.Pairwise (· < ·) ∧ (∀ x ∈ ls', x ∈ ρ.levelsOn v (upTop L top)) ∧
          (∀ x ∈ ls', ∃ j ∈ ls, img L j x) ∧
          ls.foldl (rightStep (norm ρ L)) z = ls'.foldl (rightStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ _ z; exact ⟨[], List.Pairwise.nil, by simp, by simp, rfl⟩
    | cons j rest ih =>
      intro hpw hmem z
      obtain ⟨e, c⟩ := z
      have hjl : j ∈ (norm ρ L).levels := (List.mem_filter.mp (hmem j (by simp))).1
      have hj1 := (hNormLevel ρ L hL j hjl).1
      obtain ⟨x, hx, hstep⟩ := hStepR ρ L e c j hj1
      obtain ⟨rest', hpw', hmem', himg', hfold⟩ :=
        ih (List.pairwise_cons.mp hpw).2 (fun i hi => hmem i (by simp [hi])) (rightStep (norm ρ L) (e, c) j)
      refine ⟨x :: rest', ?_, ?_, ?_, ?_⟩
      · refine List.pairwise_cons.mpr ⟨?_, hpw'⟩
        intro y hy
        obtain ⟨r, hr, hry⟩ := himg' y hy
        have hjr : j < r := (List.pairwise_cons.mp hpw).1 r hr
        dsimp only [img] at hx hry
        omega
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hImgMem ρ L hL v top j y (hmem j (by simp)) hx
        · exact hmem' y hy
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨j, by simp, hx⟩
        · obtain ⟨r, hr, hry⟩ := himg' y hy
          exact ⟨r, by simp [hr], hry⟩
      · simp only [List.foldl_cons]
        rw [← hstep]
        exact hfold
  -- extensions -----------------------------------------------------------------
  have hLeftLe (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side) (top p : ℕ) :
      (norm ρ L).leftExt v top p ≤ ρ.leftExt v (upTop L top) p := by
    rw [leftExt_eq, leftExt_eq]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    have hsub := List.mem_sublists.mp hls
    obtain ⟨ls', hpw', hmem', -, hfold⟩ := hWalkL ρ L hL v top ls
      (((hSorted (norm ρ L)).filter _).sublist hsub) (fun j hj => hsub.subset hj) (p, 0)
    refine ⟨_, List.mem_map.mpr ⟨ls', List.mem_sublists.mpr
      (sublist_of_pairwise_lt hpw' ((hSorted ρ).filter _) hmem'), rfl⟩, ?_⟩
    exact le_of_eq (congrArg Prod.snd hfold)
  have hRightLe (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side) (top q : ℕ) :
      (norm ρ L).rightExt v top q ≤ ρ.rightExt v (upTop L top) q := by
    rw [rightExt_eq, rightExt_eq]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    have hsub := List.mem_sublists.mp hls
    obtain ⟨ls', hpw', hmem', -, hfold⟩ := hWalkR ρ L hL v top ls
      (((hSorted (norm ρ L)).filter _).sublist hsub) (fun j hj => hsub.subset hj) (q, 0)
    refine ⟨_, List.mem_map.mpr ⟨ls', List.mem_sublists.mpr
      (sublist_of_pairwise_lt hpw' ((hSorted ρ).filter _) hmem'), rfl⟩, ?_⟩
    exact le_of_eq (congrArg Prod.snd hfold)
  have hUpTopZero (L : ℕ) : upTop L 0 = 0 := by simp [upTop]
  have hChainLe (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side) (p q : ℕ) :
      (norm ρ L).chainExt v p q ≤ ρ.chainExt v p q := by
    have h1 := hLeftLe ρ L hL v 0 p
    have h2 := hRightLe ρ L hL v 0 q
    rw [hUpTopZero] at h1 h2
    simp only [chainExt]
    omega
  have hJoinLe (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side) (p q : ℕ) :
      (norm ρ L).joinExt v p q ≤ ρ.joinExt v p q := by
    unfold joinExt
    apply max_le_max (hChainLe ρ L hL v p q)
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hx
    try dsimp only
    have hNl := (List.mem_filter.mp hN).1
    have hN1 := (hNormLevel ρ L hL N hNl)
    have hNtop : N ∈ (norm ρ L).levelsOn v 0 := hN
    have hmemρ (y : ℕ) (hy : img L N y) : y ∈ ρ.levelsOn v 0 := by
      have := hImgMem ρ L hL v 0 N y hNtop hy
      rwa [hUpTopZero] at this
    have hL' := hL
    obtain ⟨h1, h2, -, -⟩ := hL'
    rcases lt_trichotomy N L with hlt | rfl | hgt
    · refine ⟨_, List.mem_map.mpr ⟨N, hmemρ N (Or.inl ⟨hlt, rfl⟩), rfl⟩, ?_⟩
      have hl := hLeftLe ρ L hL v N p
      have hr := hRightLe ρ L hL v N q
      have hup : upTop L N = N := by dsimp only [upTop]; simp [show N ≤ L by omega]
      rw [hup] at hl hr
      rw [hMax ρ L hL N hN1.1, if_pos hlt]
      try dsimp only
      omega
    · have hl := hLeftLe ρ N hL v N p
      have hr := hRightLe ρ N hL v N q
      have hup : upTop N N = N := by dsimp only [upTop]; simp
      rw [hup] at hl hr
      rw [hMax ρ N hL N hN1.1, if_neg (lt_irrefl N), if_pos rfl]
      by_cases hm : ρ.maximumAt (N + 1) ≤ ρ.maximumAt N
      · refine ⟨_, List.mem_map.mpr ⟨N, hmemρ N (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)), rfl⟩, ?_⟩
        rw [max_eq_left hm]
        try dsimp only
        omega
      · refine ⟨_, List.mem_map.mpr ⟨N + 1, hmemρ (N + 1) (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)), rfl⟩, ?_⟩
        have hl2 := leftExt_mono_top ρ v h1 (by omega : N ≤ N + 1) p
        have hr2 := rightExt_mono_top ρ v h1 (by omega : N ≤ N + 1) q
        rw [max_eq_right (by omega)]
        try dsimp only
        omega
    · refine ⟨_, List.mem_map.mpr ⟨N + 1, hmemρ (N + 1) (Or.inr (Or.inr ⟨hgt, rfl⟩)), rfl⟩, ?_⟩
      have hl := hLeftLe ρ L hL v N p
      have hr := hRightLe ρ L hL v N q
      have hup : upTop L N = N + 1 := by dsimp only [upTop]; simp [show ¬ N ≤ L by omega]
      rw [hup] at hl hr
      rw [hMax ρ L hL N hN1.1, if_neg (by omega), if_neg (by omega)]
      try dsimp only
      omega
  have hCaps (ρ : Context) (L : ℕ) (hL : Inv ρ L) (p q : ℕ) :
      ρ.cupLimit p q ≤ (norm ρ L).cupLimit p q ∧ ρ.capLimit p q ≤ (norm ρ L).capLimit p q := by
    have hcl := hChainLe ρ L hL Side.lower p q
    have hcu := hChainLe ρ L hL Side.upper p q
    have hjl := hJoinLe ρ L hL Side.lower p q
    have hju := hJoinLe ρ L hL Side.upper p q
    have ha : (norm ρ L).a = ρ.a := rfl
    have hu : (norm ρ L).u = ρ.u := rfl
    dsimp only [cupLimit, capLimit]
    rw [ha, hu, hK]
    omega
  -- parts --------------------------------------------------------------------
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
          [max ((ρ.part keep v m).maximumAt (L + 1)) ((ρ.part keep v m).maximumAt (L + 1 + 1))] ++
          (m :: ρ.maxima).drop (L + 1 + 1) =
        m :: (ρ.maxima.take (L - 1) ++ [max (ρ.maximumAt L) (ρ.maximumAt (L + 1))] ++ ρ.maxima.drop (L + 1))
      rw [e1, e2, e3, e4]
      rfl
    exact ctx_ext rfl rfl rfl hw hmx
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
  have hBase (ρ : Context) (L : ℕ) (hL : Inv ρ L) : ρ.base ≤ (norm ρ L).base := by
    rw [base_eq_baseOf, base_eq_baseOf, hChild]
    cases hh : ρ.childPositions.head? with
    | none => exact le_rfl
    | some p =>
      have h := baseOf_mono (k := ρ.k) (hCaps ρ L hL p p).1 (hCaps ρ L hL p p).2
      simpa only [hK] using h
  have hFuel : ∀ fuel (ρ : Context) (L : ℕ), Inv ρ L → boundFuel fuel ρ ≤ boundFuel fuel (norm ρ L) := by
    intro fuel
    induction fuel with
    | zero => intro ρ L _; exact le_rfl
    | succ fuel ih =>
      intro ρ L hL
      have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
          boundFuel fuel (ρ.part keep v m) ≤ boundFuel fuel ((norm ρ L).part keep v m) := by
        have h := ih (ρ.part keep v m) (L + 1) (hInvPart ρ L hL keep v m)
        rw [hNormPart ρ keep v m L hL.1] at h
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
  -- the statement -------------------------------------------------------------
  have hInv : Inv σ l := by
    refine ⟨hl, hl2, ?_, hside⟩
    intro p j v hp hj
    have h := (hwf.2.2.2.2.2 p j v hp).2.2
    rcases hj with rfl | rfl
    · exact h
    · rw [h, ← hside]
  simpa only [bound, hChild] using hFuel (σ.childPositions.length + 1) σ l hInv


end ErdosSzekeres
