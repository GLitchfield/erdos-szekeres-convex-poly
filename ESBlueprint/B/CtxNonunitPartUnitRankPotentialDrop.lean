import ESBlueprint.B.CtxCutRankBudgetOfNonunitPart

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Raw unit-zone and nonunit-rank potential drop when an own-axis part retains a child of chosen capacity at least two, allowing an inactive witness. Under positive labels, chosen global at most four, two actual indexed chosen-axis levels, and a removed source child, occupied active unit-zone counts add across the chosen-axis part and complementary opposite-axis part. The chosen part nonunit opposite-rank union is contained in the source union and the complement has no nonunit ranks, yielding additive decrease of their sum. Kept sets and new maxima are arbitrary. Nonunit survival places all removed children in the opposite exterior; capacity constancy on a marker-clear interval confines surviving unit children to the old marker interior, while companion unit children remain in the other exterior. Completes the unit/nonunit-count component of the nonunit recursive branch, paired with the existing rank-union-plus-one cut bound for the singleton-end sandwich mixed potential.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonunit_part_unit_rank_potential_drop (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hnonunit : 2 ≤ (match s with
    | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
    | Ctx.Side.upper => (σ.part keep s m).capLimit p p))
  (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep) :
  let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
    (fun r => 0 < ρ.cupLimit r r ∧ 0 < ρ.capLimit r r)
  let limit : Ctx.Context → ℕ → ℕ := fun (ρ : Ctx.Context) (r : ℕ) =>
    match s with | Ctx.Side.lower => ρ.cupLimit r r | Ctx.Side.upper => ρ.capLimit r r
  let markers := fun (ρ : Ctx.Context) => (ρ.levelsOn s 0).toFinset.biUnion
    (fun j => (ρ.extPositions j).toFinset)
  let label := fun (ρ : Ctx.Context) (r : ℕ) =>
    if ((markers ρ).filter (· < r)).Nonempty then
      if ((markers ρ).filter (r < ·)).Nonempty then (1 : ℕ) else 2
    else 0
  let unitZones := fun (ρ : Ctx.Context) =>
    (((active ρ).filter (fun r => limit ρ r ≤ 1)).image (label ρ)).card
  let nonunitRanks := fun (ρ : Ctx.Context) =>
    ((active ρ).filter (fun r => 2 ≤ limit ρ r)).biUnion
      (fun r => Finset.Icc (ρ.leftExt t 0 r + 1)
        ((match t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1 - ρ.rightExt t 0 r))
  let ownPart := σ.part keep s m
  let otherPart := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  (unitZones ownPart + unitZones otherPart ≤ unitZones σ) ∧
    (nonunitRanks ownPart ⊆ nonunitRanks σ) ∧ nonunitRanks otherPart = ∅ ∧
    (unitZones ownPart + (nonunitRanks ownPart).card) +
      (unitZones otherPart + (nonunitRanks otherPart).card) ≤
        unitZones σ + (nonunitRanks σ).card := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let C (ρ : Context) (v : Side) (r : ℕ) := match v with
    | Side.lower => ρ.cupLimit r r
    | Side.upper => ρ.capLimit r r
  let Rel (d : Bool) (a b : ℕ) : Prop := if d then a < b else b < a
  let active (ρ : Context) : Finset ℕ := ρ.childPositions.toFinset.filter
    (fun r => 0 < ρ.cupLimit r r ∧ 0 < ρ.capLimit r r)
  let marks (ρ : Context) : Finset ℕ :=
    (ρ.levelsOn s 0).toFinset.biUnion (fun l => (ρ.extPositions l).toFinset)
  let label (M : Finset ℕ) (r : ℕ) : ℕ :=
    if (M.filter (· < r)).Nonempty then
      if (M.filter (r < ·)).Nonempty then 1 else 2
    else 0
  let units (ρ : Context) := (active ρ).filter (fun r => C ρ s r ≤ 1)
  let colors (ρ : Context) := (units ρ).image (label (marks ρ))
  let ranks (ρ : Context) := ((active ρ).filter (fun r => 2 ≤ C ρ s r)).biUnion
    (fun r => Finset.Icc (ρ.leftExt t 0 r + 1) (G ρ t - 1 - ρ.rightExt t 0 r))
  let rest := σ.childPositions.filter (· ∉ keep)
  let A := σ.part keep s m
  let B := σ.part rest t n
  suffices hMain : ((colors A).card + (colors B).card ≤ (colors σ).card) ∧
    (ranks A ⊆ ranks σ) ∧ ranks B = ∅ ∧
    ((colors A).card + (ranks A).card) + ((colors B).card + (ranks B).card) ≤
      (colors σ).card + (ranks σ).card by
    cases s <;> cases t <;>
      simpa only [colors, units, ranks, active, C, G, marks, label, A, B, rest] using hMain
  have hChild (ks : List ℕ) (v : Side) (c r : ℕ) :
      r ∈ (σ.part ks v c).childPositions ↔ r ∈ σ.childPositions ∧ r ∈ ks := by
    simp only [part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hPosPart (ks : List ℕ) (v : Side) (c : ℕ) :
      ∀ r j w, (σ.part ks v c).letterAt r = Letter.ext j w → 1 ≤ j := by
    intro r j w hr
    have hrl : r < σ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (σ.part ks v c)
        (show (σ.part ks v c).word.length ≤ r by rw [part_word_length]; omega)
      rw [hn] at hr
      cases hr
    cases he : σ.letterAt r with
    | child =>
      rw [part_letterAt_of_child σ ks v c hrl he] at hr
      split at hr
      · cases hr
      · cases hr; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ ks v c hrl he] at hr
      cases hr; omega
  have hSide (ks : List ℕ) (v : Side) (c r : ℕ)
      (hr : r ∈ σ.childPositions) (hn : r ∉ ks) :
      (σ.part ks v c).sideAt 1 = v := by
    apply part_sideAt_one_of_mem hpositive ks v c (q := r)
    rw [part_extPositions_one hpositive ks v c]
    exact List.mem_filter.mpr ⟨hr, by simp [hn]⟩
  have hcp := (hChild keep s m p).mp hp
  have hp2 : 2 ≤ C A s p := by cases s <;> simpa only [C, A] using hnonunit
  have hpOld : 2 ≤ C σ s p := by
    have hle := ctx_part_limits_le σ keep s m p p
    cases s <;> dsimp only [C, A] at hp2 ⊢ <;> omega
  have hG : G σ s ≤ 4 := by cases s <;> simpa only [G] using hglobal
  have hGA : G A s ≤ 4 := hG
  have hA1 : 1 ∈ A.levels := by simp only [A, part_levels, List.mem_cons, true_or]
  have hASide : A.sideAt 1 = s := hSide keep s m q hq hremoved
  have hNew (r : ℕ) (hr : r ∈ σ.childPositions) (hn : r ∉ keep) : r ∈ A.extPositions 1 := by
    rw [show A.extPositions 1 = σ.childPositions.filter (· ∉ keep) from
      part_extPositions_one hpositive keep s m]
    exact List.mem_filter.mpr ⟨hr, by simp [hn]⟩
  have hOld (j : ℕ) (hj : j ∈ σ.levelsOn s 0) :
      j + 1 ∈ A.levels ∧ A.sideAt (j + 1) = s ∧ A.extPositions (j + 1) = σ.extPositions j := by
    have hh := one_le_of_mem_levelsOn hj
    refine ⟨?_, ?_, part_extPositions_succ σ keep s m hh.1⟩
    · rw [show A.levels = 1 :: σ.levels.map (· + 1) from part_levels σ keep s m]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, (List.mem_filter.mp hj).1, rfl⟩)
    · rw [show A.sideAt (j + 1) = σ.sideAt j from part_sideAt_succ σ keep s m hh.1]
      exact hh.2.2
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hglobalPlain : (match s with | Side.lower => σ.u | Side.upper => σ.a) ≤ 4 := by
    cases s <;> simpa only [G] using hG
  obtain ⟨dir, hOutside⟩ : ∃ dir : Bool, ∀ r ∈ σ.childPositions, 2 ≤ C σ s r →
      ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir z r := by
    rcases ctx_nonunit_children_exterior_of_two_levels σ s N M x y hN hM hNM hNs hMs hx hy hglobalPlain with hh | hh
    · refine ⟨true, ?_⟩
      intro r hr h2 j hj z hz
      have h2' : 2 ≤ (match s with | Side.lower => σ.cupLimit r r | Side.upper => σ.capLimit r r) := by
        cases s <;> simpa only [C] using h2
      exact hh.2 r hr h2' j hj z hz
    · refine ⟨false, ?_⟩
      intro r hr h2 j hj z hz
      have h2' : 2 ≤ (match s with | Side.lower => σ.cupLimit r r | Side.upper => σ.capLimit r r) := by
        cases s <;> simpa only [C] using h2
      exact hh.2 r hr h2' j hj z hz
  have hRemoved (r : ℕ) (hr : r ∈ σ.childPositions) (hn : r ∉ keep) :
      ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir r z := by
    intro j hj z hz
    have hj1 := (one_le_of_mem_levelsOn hj).1
    obtain ⟨hjA, hsjA, hextA⟩ := hOld j hj
    have hzA : z ∈ A.extPositions (j + 1) := by rw [hextA]; exact hz
    have hjOnA : j + 1 ∈ A.levelsOn s 0 := List.mem_filter.mpr ⟨hjA, by simp [hsjA]⟩
    have hpz := hOutside p hcp.1 hpOld j hj z hz
    have hglobalA : (match s with | Side.lower => A.u | Side.upper => A.a) ≤ 4 := by
      cases s <;> simpa only [G] using hGA
    have hp2' : 2 ≤ (match s with | Side.lower => A.cupLimit p p | Side.upper => A.capLimit p p) := by
      cases s <;> simpa only [C] using hp2
    rcases ctx_nonunit_children_exterior_of_two_levels A s 1 (j + 1) r z hA1 hjA
      (by omega) hASide hsjA (hNew r hr hn) hzA hglobalA with hh | hh
    · have hzp := hh.2 p hp hp2' (j + 1) hjOnA z hzA
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hpz ⊢ <;> omega
    · have hpz' := hh.2 p hp hp2' (j + 1) hjOnA z hzA
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hpz ⊢ <;> omega
  have hOuterUnit (r : ℕ) (hr : r ∈ σ.childPositions)
      (hout : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir r z) : C σ s r ≤ 1 := by
    by_contra hn
    have h2 : 2 ≤ C σ s r := by omega
    have hxr := hOutside r hr h2 N hNOn x hx
    have hrx := hout N hNOn x hx
    cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hxr hrx <;> omega
  have hMark (ρ : Context) (x : ℕ) :
      x ∈ marks ρ ↔ ∃ l ∈ ρ.levelsOn s 0, x ∈ ρ.extPositions l := by
    simp [marks]
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by
    simp [active]
  have hNoMark (ρ : Context) (p : ℕ) (hp : p ∈ ρ.childPositions) : p ∉ marks ρ := by
    intro hm
    obtain ⟨l, _, hx⟩ := (hMark ρ p).mp hm
    have hc := (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hx).2
    simp only [decide_eq_true_eq] at hc he
    simp [hc] at he
  have hPartActive (ρ : Context) (keep : List ℕ) (t : Side) (m p : ℕ)
      (hp : p ∈ active (ρ.part keep t m)) : p ∈ active ρ ∧ p ∈ keep := by
    obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
    rw [part_childPositions] at hc
    obtain ⟨hc, hk⟩ := List.mem_filter.mp hc
    simp only [decide_eq_true_eq] at hk
    have hle := ctx_part_limits_le ρ keep t m p p
    exact ⟨(hActive _ _).mpr ⟨hc, by omega, by omega⟩, hk⟩
  have hPartMarks (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (keep : List ℕ) (t : Side) (m x : ℕ) (hx : x ∈ marks (ρ.part keep t m)) :
      x ∈ marks ρ ∨ (t = s ∧ x ∈ ρ.childPositions ∧ x ∉ keep) := by
    obtain ⟨l, hl, hx⟩ := (hMark _ _).mp hx
    have hl' := List.mem_filter.mp hl
    have hs : (ρ.part keep t m).sideAt l = s := by simpa using hl'.2
    rw [part_levels] at hl'
    rcases List.mem_cons.mp hl'.1 with rfl | hold
    · right
      have hside := part_sideAt_one_of_mem hPos keep t m hx
      rw [part_extPositions_one hPos keep t m] at hx
      have hr := List.mem_filter.mp hx
      exact ⟨hside.symm.trans hs, hr.1, by simpa using hr.2⟩
    · left
      obtain ⟨j, hj, hjl⟩ := List.mem_map.mp hold
      subst l
      have h1 := one_le_of_mem_levels hj
      rw [part_extPositions_succ ρ keep t m h1] at hx
      rw [part_sideAt_succ ρ keep t m h1] at hs
      exact (hMark ρ x).mpr ⟨j, by simp [Context.levelsOn, hj, hs], hx⟩
  have hZ1 (M : Finset ℕ) (p : ℕ) : label M p = 1 ↔
      (M.filter (· < p)).Nonempty ∧ (M.filter (p < ·)).Nonempty := by
    by_cases hL : (M.filter (· < p)).Nonempty <;>
      by_cases hR : (M.filter (p < ·)).Nonempty <;> simp [label, hL, hR]
  have hZ2 (M : Finset ℕ) (p : ℕ) : label M p = 2 ↔
      (M.filter (· < p)).Nonempty ∧ ¬ (M.filter (p < ·)).Nonempty := by
    by_cases hL : (M.filter (· < p)).Nonempty <;>
      by_cases hR : (M.filter (p < ·)).Nonempty <;> simp [label, hL, hR]
  have hAllRight (M : Finset ℕ) (p : ℕ) (hp : p ∉ M)
      (hL : ¬ (M.filter (· < p)).Nonempty) : ∀ x ∈ M, p < x := by
    intro x hx
    have hne : x ≠ p := by intro he; exact hp (he ▸ hx)
    by_contra h
    exact hL ⟨x, Finset.mem_filter.mpr ⟨hx, by omega⟩⟩
  have hAllLeft (M : Finset ℕ) (p : ℕ) (hp : p ∉ M)
      (hR : ¬ (M.filter (p < ·)).Nonempty) : ∀ x ∈ M, x < p := by
    intro x hx
    have hne : x ≠ p := by intro he; exact hp (he ▸ hx)
    by_contra h
    exact hR ⟨x, Finset.mem_filter.mpr ⟨hx, by omega⟩⟩
  have hOldMarks (ρ : Context) (keep : List ℕ) (t : Side) (m : ℕ) :
      marks ρ ⊆ marks (ρ.part keep t m) := by
    intro x hx
    obtain ⟨j, hj, hx⟩ := (hMark ρ x).mp hx
    have hjlev := (List.mem_filter.mp hj).1
    have hj1 := one_le_of_mem_levels hjlev
    have hside : ρ.sideAt j = s := by simpa using (List.mem_filter.mp hj).2
    have hjnew : j + 1 ∈ (ρ.part keep t m).levels := by
      rw [part_levels]
      exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨j, hjlev, rfl⟩))
    apply (hMark _ _).mpr
    refine ⟨j + 1, ?_, ?_⟩
    · simp [Context.levelsOn, hjnew, part_sideAt_succ ρ keep t m hj1, hside]
    · simpa only [part_extPositions_succ ρ keep t m hj1] using hx
  have hClearEq (ρ : Context) (v : Side) (a b : ℕ)
      (hclear : ∀ j ∈ ρ.levelsOn v 0, ∀ z ∈ ρ.extPositions j,
        z < min a b ∨ max a b < z) : C ρ v a = C ρ v b := by
    have hfilters (j : ℕ) (hj : j ∈ ρ.levelsOn v 0) :
        (ρ.extPositions j).filter (· < a) = (ρ.extPositions j).filter (· < b) ∧
        (ρ.extPositions j).filter (a < ·) = (ρ.extPositions j).filter (b < ·) := by
      constructor <;> apply List.filter_congr <;> intro z hz
      · have hh := hclear j hj z hz
        simp only [decide_eq_decide]
        omega
      · have hh := hclear j hj z hz
        simp only [decide_eq_decide]
        omega
    have hfoldL : ∀ ls : List ℕ, (∀ j ∈ ls, j ∈ ρ.levelsOn v 0) → ∀ c,
        (ls.foldl (leftStep ρ) (a, c)).2 = (ls.foldl (leftStep ρ) (b, c)).2 := by
      intro ls
      induction ls with
      | nil => intros; rfl
      | cons j js ih =>
        intro hj c
        simp only [List.foldl_cons, leftStep]
        rw [(hfilters j (hj j (by simp))).1]
        split
        · rfl
        · exact ih (fun i hi => hj i (by simp [hi])) c
    have hfoldR : ∀ ls : List ℕ, (∀ j ∈ ls, j ∈ ρ.levelsOn v 0) → ∀ c,
        (ls.foldl (rightStep ρ) (a, c)).2 = (ls.foldl (rightStep ρ) (b, c)).2 := by
      intro ls
      induction ls with
      | nil => intros; rfl
      | cons j js ih =>
        intro hj c
        simp only [List.foldl_cons, rightStep]
        rw [(hfilters j (hj j (by simp))).2]
        split
        · rfl
        · exact ih (fun i hi => hj i (by simp [hi])) c
    have hmem (top : ℕ) (ls : List ℕ) (hl : ls ∈ (ρ.levelsOn v top).sublists) :
        ∀ j ∈ ls, j ∈ ρ.levelsOn v 0 := by
      intro j hj
      have hm := (List.mem_sublists.mp hl).subset hj
      simp only [levelsOn, List.mem_filter, decide_eq_true_eq] at hm ⊢
      exact ⟨hm.1, hm.2.1, Or.inl True.intro⟩
    have hL (top : ℕ) : ρ.leftExt v top a = ρ.leftExt v top b := by
      rw [leftExt_eq, leftExt_eq]
      apply congrArg (fun ls : List ℕ => ls.max?.getD 0)
      apply List.map_congr_left
      intro ls hl
      exact hfoldL ls (hmem top ls hl) 0
    have hR (top : ℕ) : ρ.rightExt v top a = ρ.rightExt v top b := by
      rw [rightExt_eq, rightExt_eq]
      apply congrArg (fun ls : List ℕ => ls.max?.getD 0)
      apply List.map_congr_left
      intro ls hl
      exact hfoldR ls (hmem top ls hl) 0
    have hChain : ρ.chainExt v a a = ρ.chainExt v b b := by simp only [chainExt, hL, hR]
    have hJoin : ρ.joinExt v a a = ρ.joinExt v b b := by simp only [joinExt, hChain, hL, hR]
    cases v <;> simp only [C, cupLimit, capLimit, hChain, hJoin]
  have hBracket (r : ℕ) (hr : r ∈ units A) :
      ((marks σ).filter (· < r)).Nonempty ∧ ((marks σ).filter (r < ·)).Nonempty := by
    obtain ⟨hra, hru⟩ := Finset.mem_filter.mp hr
    have hrc := ((hActive _ _).mp (hPartActive σ keep s m r hra).1).1
    have hkeep := (hPartActive σ keep s m r hra).2
    have hNotOpp (hout : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir r z) : False := by
      have hu := hOuterUnit r hrc hout
      have hclear : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j,
          z < min r q ∨ max r q < z := by
        intro j hj z hz
        have hrz := hout j hj z hz
        have hqz := hRemoved q hq hremoved j hj z hz
        cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hrz hqz <;> omega
      have hd := (ctx_part_capacity_drop_in_clear_interval σ hpositive keep s m r q
        hrc hkeep hq hremoved hclear).2.2
      have ha := (hActive A r).mp hra
      cases s <;> dsimp only [C, A] at hu ha hd <;> omega
    have hNotDir (hout : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir z r) : False := by
      have heq : C A s r = C A s p := by
        apply hClearEq
        intro j hj z hz
        have hm : z ∈ marks A := (hMark A z).mpr ⟨j, hj, hz⟩
        rcases hPartMarks σ hpositive keep s m z hm with hold | ⟨_, hzc, hzn⟩
        · obtain ⟨i, hi, hz⟩ := (hMark σ z).mp hold
          have hrz := hout i hi z hz
          have hpz := hOutside p hcp.1 hpOld i hi z hz
          cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hrz hpz <;> omega
        · have hzx := hRemoved z hzc hzn N hNOn x hx
          have hxr := hout N hNOn x hx
          have hxp := hOutside p hcp.1 hpOld N hNOn x hx
          cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hzx hxr hxp <;> omega
      omega
    have hno := hNoMark σ r hrc
    constructor
    · by_contra hL
      have hh := hAllRight (marks σ) r hno hL
      cases hd : dir
      · apply hNotDir
        intro j hj z hz
        simpa only [Rel, hd, Bool.false_eq_true, if_false] using hh z ((hMark σ z).mpr ⟨j, hj, hz⟩)
      · apply hNotOpp
        intro j hj z hz
        simpa only [Rel, hd, if_true] using hh z ((hMark σ z).mpr ⟨j, hj, hz⟩)
    · by_contra hR
      have hh := hAllLeft (marks σ) r hno hR
      cases hd : dir
      · apply hNotOpp
        intro j hj z hz
        simpa only [Rel, hd, Bool.false_eq_true, if_false] using hh z ((hMark σ z).mpr ⟨j, hj, hz⟩)
      · apply hNotDir
        intro j hj z hz
        simpa only [Rel, hd, if_true] using hh z ((hMark σ z).mpr ⟨j, hj, hz⟩)
  have hAInfo (r : ℕ) (hr : r ∈ units A) :
      r ∈ units σ ∧ label (marks A) r = 1 ∧ label (marks σ) r = 1 := by
    obtain ⟨hra, hru⟩ := Finset.mem_filter.mp hr
    have hrσ := (hPartActive σ keep s m r hra).1
    have hrc := ((hActive σ r).mp hrσ).1
    have hbr := hBracket r hr
    have hu : C σ s r ≤ 1 := by
      by_contra hn
      have h2 : 2 ≤ C σ s r := by omega
      obtain ⟨a, ha, har⟩ := Finset.filter_nonempty_iff.mp hbr.1
      obtain ⟨b, hb, hrb⟩ := Finset.filter_nonempty_iff.mp hbr.2
      obtain ⟨i, hi, hai⟩ := (hMark σ a).mp ha
      obtain ⟨j, hj, hbj⟩ := (hMark σ b).mp hb
      have ha' := hOutside r hrc h2 i hi a hai
      have hb' := hOutside r hrc h2 j hj b hbj
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at ha' hb' <;> omega
    refine ⟨Finset.mem_filter.mpr ⟨hrσ, hu⟩, ?_, (hZ1 _ _).mpr hbr⟩
    apply (hZ1 _ _).mpr
    constructor
    · obtain ⟨a, ha, har⟩ := Finset.filter_nonempty_iff.mp hbr.1
      exact ⟨a, Finset.mem_filter.mpr ⟨hOldMarks σ keep s m ha, har⟩⟩
    · obtain ⟨b, hb, hrb⟩ := Finset.filter_nonempty_iff.mp hbr.2
      exact ⟨b, Finset.mem_filter.mpr ⟨hOldMarks σ keep s m hb, hrb⟩⟩
  have hBMarks : marks B = marks σ := by
    apply Finset.Subset.antisymm
    · intro r hr
      rcases hPartMarks σ hpositive rest t n r hr with hold | ⟨he, _, _⟩
      · exact hold
      · exact False.elim (hne he.symm)
    · exact hOldMarks σ rest t n
  have hBChild (r : ℕ) (hr : r ∈ B.childPositions) : r ∈ σ.childPositions ∧ r ∉ keep := by
    have hh := (hChild rest t n r).mp hr
    exact ⟨hh.1, by simpa only [rest, List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hh.2).2⟩
  have hBUnit (r : ℕ) (hr : r ∈ B.childPositions) : C B s r ≤ 1 := by
    have hh := hBChild r hr
    have hu := hOuterUnit r hh.1 (hRemoved r hh.1 hh.2)
    have hle := ctx_part_limits_le σ rest t n r r
    cases s <;> dsimp only [C, B] at hu ⊢ <;> omega
  have hBInfo (r : ℕ) (hr : r ∈ units B) :
      r ∈ units σ ∧ label (marks B) r = label (marks σ) r ∧ label (marks B) r ≠ 1 := by
    obtain ⟨hra, _⟩ := Finset.mem_filter.mp hr
    have hrc := hBChild r ((hActive B r).mp hra).1
    have hout := hRemoved r hrc.1 hrc.2
    have hu := hOuterUnit r hrc.1 hout
    refine ⟨Finset.mem_filter.mpr ⟨(hPartActive σ rest t n r hra).1, hu⟩, ?_, ?_⟩
    · rw [hBMarks]
    · rw [hBMarks]
      intro he
      have hb := (hZ1 _ _).mp he
      obtain ⟨a, ha, har⟩ := Finset.filter_nonempty_iff.mp hb.1
      obtain ⟨b, hb, hrb⟩ := Finset.filter_nonempty_iff.mp hb.2
      obtain ⟨i, hi, hai⟩ := (hMark σ a).mp ha
      obtain ⟨j, hj, hbj⟩ := (hMark σ b).mp hb
      have ha' := hout i hi a hai
      have hb' := hout j hj b hbj
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at ha' hb' <;> omega
  have hColorA : colors A ⊆ colors σ := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    have hh := hAInfo r hr
    exact Finset.mem_image.mpr ⟨r, hh.1, hh.2.2.trans hh.2.1.symm⟩
  have hColorB : colors B ⊆ colors σ := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    have hh := hBInfo r hr
    exact Finset.mem_image.mpr ⟨r, hh.1, hh.2.1.symm⟩
  have hDisjoint : Disjoint (colors A) (colors B) := by
    apply Finset.disjoint_left.mpr
    intro z ha hb
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hb
    exact (hBInfo w hw).2.2 (he.trans (hAInfo r hr).2.1)
  have hColors : (colors A).card + (colors B).card ≤ (colors σ).card := by
    have hh := Finset.card_le_card (Finset.union_subset hColorA hColorB)
    rw [Finset.card_union_of_disjoint hDisjoint] at hh
    exact hh
  have hAT : A.sideAt 1 ≠ t := by rw [hASide]; exact hne
  have hPure (r : ℕ) : A.leftExt t 0 r = σ.leftExt t 0 r ∧ A.rightExt t 0 r = σ.rightExt t 0 r :=
    ⟨(leftExt_part_other hAT r).1, (rightExt_part_other hAT r).1⟩
  have hRankSubset : ranks A ⊆ ranks σ := by
    intro z hz
    obtain ⟨r, hr, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hra, hr2⟩ := Finset.mem_filter.mp hr
    have hrσ := (hPartActive σ keep s m r hra).1
    have h2 : 2 ≤ C σ s r := by
      have hle := ctx_part_limits_le σ keep s m r r
      cases s <;> dsimp only [C, A] at hr2 ⊢ <;> omega
    apply Finset.mem_biUnion.mpr
    refine ⟨r, Finset.mem_filter.mpr ⟨hrσ, h2⟩, ?_⟩
    have hGAT : G A t = G σ t := by cases t <;> rfl
    simpa only [(hPure r).1, (hPure r).2, hGAT] using hz
  have hRankEmpty : ranks B = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨r, hr, _⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hra, hr2⟩ := Finset.mem_filter.mp hr
    have hu := hBUnit r ((hActive B r).mp hra).1
    omega
  refine ⟨hColors, hRankSubset, hRankEmpty, ?_⟩
  have hCard := Finset.card_le_card hRankSubset
  rw [hRankEmpty, Finset.card_empty]
  omega


end ErdosSzekeres
