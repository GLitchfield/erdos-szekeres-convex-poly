import ESBlueprint.B.CtxNonunitPartCompanionExteriorRankBound

import ESBlueprint.B.CtxPartTrackedRankReservation

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Raw exterior-rank potential decreases across a cut with a nonunit chosen-part child and an active companion. The potential counts occupied active chosen-unit zones plus separate opposite-rank unions of active nonunit children in the left and right chosen exteriors. Requires positive labels, chosen global at most four and one actual indexed chosen marker; kept lists and new maxima are arbitrary, and the own nonunit witness may be inactive. One-marker exterior geometry confines the companion to the opposite old exterior. Converted own-part unit zones reserve distinct endpoint ranks there; companion activity excludes coincident reservations. Supplies the raw-count component of the one-level mixed-potential induction, while the empty-companion case needs common-rank covers.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonunit_part_active_companion_exterior_potential_drop (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hnonunit : 2 ≤ (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
    | Ctx.Side.upper => (σ.part keep s m).capLimit p p) s)
  (hq : q ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions)
  (hqcup : 0 < (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit q q)
  (hqcap : 0 < (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit q q) :
  let global := fun (ρ : Ctx.Context) (v : Ctx.Side) =>
    match v with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let limit : Ctx.Context → ℕ → ℕ := fun ρ r =>
    (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => ρ.cupLimit r r | Ctx.Side.upper => ρ.capLimit r r) s
  let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
    (fun r => 0 < ρ.cupLimit r r ∧ 0 < ρ.capLimit r r)
  let markers := fun (ρ : Ctx.Context) => (ρ.levelsOn s 0).toFinset.biUnion
    (fun j => (ρ.extPositions j).toFinset)
  let label := fun (ρ : Ctx.Context) (r : ℕ) =>
    if ((markers ρ).filter (· < r)).Nonempty then
      if ((markers ρ).filter (r < ·)).Nonempty then (1 : ℕ) else 2
    else 0
  let unitZones := fun (ρ : Ctx.Context) =>
    (((active ρ).filter (fun r => limit ρ r ≤ 1)).image (label ρ)).card
  let rankInterval := fun (ρ : Ctx.Context) (r : ℕ) =>
    Finset.Icc (ρ.leftExt t 0 r + 1) (global ρ t - 1 - ρ.rightExt t 0 r)
  let exteriorRanks := fun (ρ : Ctx.Context) (c : ℕ) =>
    ((active ρ).filter (fun r => 2 ≤ limit ρ r ∧ label ρ r = c)).biUnion (rankInterval ρ)
  let potential := fun (ρ : Ctx.Context) =>
    unitZones ρ + (exteriorRanks ρ 0).card + (exteriorRanks ρ 2).card
  potential (σ.part keep s m) +
    potential (σ.part (σ.childPositions.filter (· ∉ keep)) t n) ≤ potential σ := by
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
  let nonunits (ρ : Context) := (active ρ).filter (fun r => 2 ≤ C ρ s r)
  let I (ρ : Context) (r : ℕ) :=
    Finset.Icc (ρ.leftExt t 0 r + 1) (G ρ t - 1 - ρ.rightExt t 0 r)
  let F (ρ : Context) (c : ℕ) := (active ρ).filter
    (fun r => 2 ≤ C ρ s r ∧ label (marks ρ) r = c)
  let RN (ρ : Context) (c : ℕ) := (F ρ c).biUnion (I ρ)
  let T (ρ : Context) := (colors ρ).card + (RN ρ 0).card + (RN ρ 2).card
  let rest := σ.childPositions.filter (· ∉ keep)
  let A := σ.part keep s m
  let B := σ.part rest t n
  change T A + T B ≤ T σ
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
  have hZ0 (M : Finset ℕ) (p : ℕ) :
      label M p = 0 ↔ ¬ (M.filter (· < p)).Nonempty := by
    by_cases hL : (M.filter (· < p)).Nonempty <;>
      by_cases hR : (M.filter (p < ·)).Nonempty <;> simp [label, hL, hR]
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
  have hExcludeClear (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (keep : List ℕ) (m p r : ℕ) (hu : C ρ s p ≤ 1) (hp : p ∈ active (ρ.part keep s m))
      (hr : r ∈ ρ.childPositions) (hremoved : r ∉ keep)
      (hclear : ∀ l ∈ ρ.levelsOn s 0, ∀ x ∈ ρ.extPositions l,
        x < min p r ∨ max p r < x) : False := by
    have hpa := hPartActive ρ keep s m p hp
    have hpc := ((hActive ρ p).mp hpa.1).1
    have hd := (ctx_part_capacity_drop_in_clear_interval ρ hPos keep s m p r
      hpc hpa.2 hr hremoved hclear).2.2
    have hpp := (hActive _ _).mp hp
    cases s <;> dsimp [C] at hu hd <;> omega
  have hExcludeInterior (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (hGlobal : (match s with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 4)
      (keep : List ℕ) (m p r : ℕ) (hp : p ∈ active (ρ.part keep s m))
      (hr : r ∈ ρ.childPositions) (hremoved : r ∉ keep)
      (hpL : ((marks ρ).filter (· < p)).Nonempty)
      (hpR : ((marks ρ).filter (p < ·)).Nonempty)
      (hrL : ((marks ρ).filter (· < r)).Nonempty)
      (hrR : ((marks ρ).filter (r < ·)).Nonempty) : False := by
    have hLeft : ∃ a ∈ marks ρ, a < p ∧ a < r := by
      rcases le_total p r with hpr | hrp
      · obtain ⟨a, ha, hap⟩ := Finset.filter_nonempty_iff.mp hpL
        exact ⟨a, ha, hap, by omega⟩
      · obtain ⟨a, ha, har⟩ := Finset.filter_nonempty_iff.mp hrL
        exact ⟨a, ha, by omega, har⟩
    have hRight : ∃ b ∈ marks ρ, p < b ∧ r < b := by
      rcases le_total p r with hpr | hrp
      · obtain ⟨b, hb, hrb⟩ := Finset.filter_nonempty_iff.mp hrR
        exact ⟨b, hb, by omega, hrb⟩
      · obtain ⟨b, hb, hpb⟩ := Finset.filter_nonempty_iff.mp hpR
        exact ⟨b, hb, hpb, by omega⟩
    obtain ⟨a, ha, hap, har⟩ := hLeft
    obtain ⟨b, hb, hpb, hrb⟩ := hRight
    obtain ⟨N, hN, ha⟩ := (hMark ρ a).mp ha
    obtain ⟨M, hM, hb⟩ := (hMark ρ b).mp hb
    have hNs : ρ.sideAt N = s := by simpa using (List.mem_filter.mp hN).2
    have hMs : ρ.sideAt M = s := by simpa using (List.mem_filter.mp hM).2
    have hpp := (hActive _ _).mp hp
    have hz := (ctx_bracketed_children_unit_bound ρ hPos s N M a b
      (List.mem_filter.mp hN).1 (List.mem_filter.mp hM).1 hNs hMs ha hb hGlobal).1
      keep m r hr hremoved har hrb p hpp.1 hap hpb
    cases s <;> simp only at hz <;> omega
  have hPartLabel (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (keep : List ℕ) (t : Side) (m p : ℕ) (hu : C ρ s p ≤ 1)
      (hp : p ∈ active (ρ.part keep t m)) :
      label (marks (ρ.part keep t m)) p = label (marks ρ) p := by
    have hpc := ((hActive _ _).mp (hPartActive ρ keep t m p hp).1).1
    have hno := hNoMark ρ p hpc
    have hL : ((marks (ρ.part keep t m)).filter (· < p)).Nonempty ↔
        ((marks ρ).filter (· < p)).Nonempty := by
      constructor
      · intro hh
        obtain ⟨x, hx, hxp⟩ := Finset.filter_nonempty_iff.mp hh
        rcases hPartMarks ρ hPos keep t m x hx with hold | ⟨ht, hxchild, hxremoved⟩
        · exact ⟨x, Finset.mem_filter.mpr ⟨hold, hxp⟩⟩
        · by_contra hnone
          subst t
          apply hExcludeClear ρ hPos keep m p x hu hp hxchild hxremoved
          intro j hj y hy
          have hym := (hMark ρ y).mpr ⟨j, hj, hy⟩
          have hyp := hAllRight (marks ρ) p hno hnone y hym
          right
          omega
      · intro hh
        obtain ⟨x, hx, hxp⟩ := Finset.filter_nonempty_iff.mp hh
        exact ⟨x, Finset.mem_filter.mpr ⟨hOldMarks ρ keep t m hx, hxp⟩⟩
    have hR : ((marks (ρ.part keep t m)).filter (p < ·)).Nonempty ↔
        ((marks ρ).filter (p < ·)).Nonempty := by
      constructor
      · intro hh
        obtain ⟨x, hx, hpx⟩ := Finset.filter_nonempty_iff.mp hh
        rcases hPartMarks ρ hPos keep t m x hx with hold | ⟨ht, hxchild, hxremoved⟩
        · exact ⟨x, Finset.mem_filter.mpr ⟨hold, hpx⟩⟩
        · by_contra hnone
          subst t
          apply hExcludeClear ρ hPos keep m p x hu hp hxchild hxremoved
          intro j hj y hy
          have hym := (hMark ρ y).mpr ⟨j, hj, hy⟩
          have hyp := hAllLeft (marks ρ) p hno hnone y hym
          left
          omega
      · intro hh
        obtain ⟨x, hx, hpx⟩ := Finset.filter_nonempty_iff.mp hh
        exact ⟨x, Finset.mem_filter.mpr ⟨hOldMarks ρ keep t m hx, hpx⟩⟩
    simp only [label, hL, hR]
  have hExcludeSame (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (hGlobal : (match s with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 4)
      (keep : List ℕ) (m p r : ℕ) (hu : C ρ s p ≤ 1) (hp : p ∈ active (ρ.part keep s m))
      (hr : r ∈ ρ.childPositions) (hremoved : r ∉ keep)
      (he : label (marks ρ) p = label (marks ρ) r) : False := by
    have hpc := ((hActive _ _).mp (hPartActive ρ keep s m p hp).1).1
    have hnp := hNoMark ρ p hpc
    have hnr := hNoMark ρ r hr
    by_cases hpL : ((marks ρ).filter (· < p)).Nonempty
    · by_cases hpR : ((marks ρ).filter (p < ·)).Nonempty
      · have hrBoth := (hZ1 (marks ρ) r).mp
          (he.symm.trans ((hZ1 (marks ρ) p).mpr ⟨hpL, hpR⟩))
        exact hExcludeInterior ρ hPos hGlobal keep m p r hp hr hremoved hpL hpR
          hrBoth.1 hrBoth.2
      · have hrBoth := (hZ2 (marks ρ) r).mp
          (he.symm.trans ((hZ2 (marks ρ) p).mpr ⟨hpL, hpR⟩))
        apply hExcludeClear ρ hPos keep m p r hu hp hr hremoved
        intro j hj x hx
        have hxm := (hMark ρ x).mpr ⟨j, hj, hx⟩
        have hxp := hAllLeft (marks ρ) p hnp hpR x hxm
        have hxr := hAllLeft (marks ρ) r hnr hrBoth.2 x hxm
        left
        omega
    · have hrL := (hZ0 (marks ρ) r).mp
        (he.symm.trans ((hZ0 (marks ρ) p).mpr hpL))
      apply hExcludeClear ρ hPos keep m p r hu hp hr hremoved
      intro j hj x hx
      have hxm := (hMark ρ x).mpr ⟨j, hj, hx⟩
      have hpx := hAllRight (marks ρ) p hnp hpL x hxm
      have hrx := hAllRight (marks ρ) r hnr hrL x hxm
      right
      omega
  have hG : G σ s ≤ 4 := hglobal
  have hglobalPlain : (match s with | Side.lower => σ.u | Side.upper => σ.a) ≤ 4 := by
    cases s <;> simpa only [G] using hG
  have hpSource := (hChild keep s m p).mp hp
  have hp2 : 2 ≤ C A s p := hnonunit
  have hqA : q ∈ active B := (hActive B q).mpr ⟨hq, hqcup, hqcap⟩
  have hqSource := hPartActive σ rest t n q hqA
  have hqChild := ((hActive σ q).mp hqSource.1).1
  have hqRemoved : q ∉ keep := of_decide_eq_true (List.mem_filter.mp hqSource.2).2
  have hBSide : B.sideAt 1 = t := hSide rest t n p hpSource.1 (by simp [rest, hpSource.2])
  have hBne : B.sideAt 1 ≠ s := by rw [hBSide]; exact hne.symm
  have hBC (r : ℕ) : C B s r = C σ s r := by
    have hc : B.chainExt s r r = σ.chainExt s r r := chainExt_part_other hBne r r
    have hj : B.joinExt s r r = σ.joinExt s r r := joinExt_part_other hBne r r
    cases s <;> simp only [C, cupLimit, capLimit, hc, hj] <;> rfl
  have hBM : marks B = marks σ := by
    apply Finset.Subset.antisymm
    · intro z hz
      rcases hPartMarks σ hpositive rest t n z hz with hh | ⟨he, _⟩
      · exact hh
      · exact False.elim (hne he.symm)
    · exact hOldMarks σ rest t n
  have hASide : A.sideAt 1 = s := hSide keep s m q hqChild hqRemoved
  have hNew (r : ℕ) (hr : r ∈ σ.childPositions) (hn : r ∉ keep) : r ∈ A.extPositions 1 := by
    rw [show A.extPositions 1 = σ.childPositions.filter (· ∉ keep) from
      part_extPositions_one hpositive keep s m]
    exact List.mem_filter.mpr ⟨hr, by simp [hn]⟩
  have hALevels : A.levelsOn s 0 = 1 :: (σ.levelsOn s 0).map (· + 1) :=
    part_levelsOn_self_zero hASide
  have hAOne : 1 ∈ A.levelsOn s 0 := by rw [hALevels]; simp
  have hNewMark (r : ℕ) (hr : r ∈ σ.childPositions) (hn : r ∉ keep) : r ∈ marks A :=
    (hMark A r).mpr ⟨1, hAOne, hNew r hr hn⟩
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hxMark : x ∈ marks σ := (hMark σ x).mpr ⟨N, hNOn, hx⟩
  have hMarksNonempty : (marks σ).Nonempty := ⟨x, hxMark⟩
  have hMarksANonempty : (marks A).Nonempty := ⟨x, hOldMarks σ keep s m hxMark⟩
  obtain ⟨direction, hPOld, hROld⟩ :=
    (ctx_nonunit_part_companion_exterior_rank_bound σ hpositive s t hne N x
      hN hNs hx hglobal keep m n p q hp hnonunit hqChild hqRemoved).1
  obtain ⟨dir, hPIn, hRemovedOut⟩ : ∃ dir : Bool,
      (∀ z ∈ marks σ, Rel dir p z) ∧
      (∀ r ∈ σ.childPositions, r ∉ keep → ∀ z ∈ marks σ, Rel dir z r) := by
    refine ⟨!direction, ?_, ?_⟩
    · intro z hz
      obtain ⟨j, hj, hz⟩ := (hMark σ z).mp hz
      have hh := hPOld j hj z hz
      cases direction <;> simpa only [Rel, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, if_false, if_true] using hh
    · intro r hr hn z hz
      obtain ⟨j, hj, hz⟩ := (hMark σ z).mp hz
      have hh := hROld r hr hn j hj z hz
      cases direction <;> simpa only [Rel, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, if_false, if_true] using hh
  let D : ℕ := if dir then 2 else 0
  let E : ℕ := if dir then 0 else 2
  have hTrans (a b c : ℕ) (hab : Rel dir a b) (hbc : Rel dir b c) : Rel dir a c := by
    cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at * <;> omega
  have hAnti (a b : ℕ) (hab : Rel dir a b) (hba : Rel dir b a) : False := by
    cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at * <;> omega
  have hTotal (a b : ℕ) (hne : a ≠ b) : Rel dir a b ∨ Rel dir b a := by
    cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] <;> omega
  have hExterior (d : Bool) (M : Finset ℕ) (hM : M.Nonempty) (r : ℕ) (hr : r ∉ M) :
      label M r = (if d then 2 else 0) ↔ ∀ z ∈ M, Rel d z r := by
    cases d
    · simp only [Bool.false_eq_true, if_false, Rel]
      rw [hZ0]
      constructor
      · exact hAllRight M r hr
      · intro hh ⟨z, hz⟩
        have hz' := Finset.mem_filter.mp hz
        have := hh z hz'.1
        omega
    · simp only [if_true, Rel]
      rw [hZ2]
      constructor
      · exact fun hh => hAllLeft M r hr hh.2
      · intro hh
        obtain ⟨z, hz⟩ := hM
        refine ⟨⟨z, Finset.mem_filter.mpr ⟨hz, hh z hz⟩⟩, ?_⟩
        intro ⟨w, hw⟩
        have hw' := Finset.mem_filter.mp hw
        have := hh w hw'.1
        omega
  have hLabelCases (M : Finset ℕ) (r : ℕ) : label M r = E ∨ label M r = 1 ∨ label M r = D := by
    cases dir <;> simp only [D, E, Bool.false_eq_true, if_false, if_true] <;>
      unfold label <;> split_ifs <;> omega
  have hED : E ≠ D ∧ E ≠ 1 ∧ D ≠ 1 := by
    cases dir <;> simp [E, D]
  have hBRemoved (r : ℕ) (hr : r ∈ active B) : r ∈ σ.childPositions ∧ r ∉ keep := by
    have hh := hPartActive σ rest t n r hr
    exact ⟨((hActive σ r).mp hh.1).1, of_decide_eq_true (List.mem_filter.mp hh.2).2⟩
  have hAKept (r : ℕ) (hr : r ∈ active A) : r ∈ σ.childPositions ∧ r ∈ keep := by
    have hh := hPartActive σ keep s m r hr
    exact ⟨((hActive σ r).mp hh.1).1, hh.2⟩
  have hABNe (a b : ℕ) (ha : a ∈ active A) (hb : b ∈ active B) : a ≠ b := by
    intro he
    exact (hBRemoved b hb).2 (he ▸ (hAKept a ha).2)
  have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hExteriorEq (ρ : Context) (hM : (marks ρ).Nonempty) (d : Bool)
      (a b : ℕ) (ha : a ∈ ρ.childPositions) (hb : b ∈ ρ.childPositions)
      (haD : label (marks ρ) a = (if d then 2 else 0))
      (hbD : label (marks ρ) b = (if d then 2 else 0)) : C ρ s a = C ρ s b := by
    have haOut := (hExterior d (marks ρ) hM a (hNoMark ρ a ha)).mp haD
    have hbOut := (hExterior d (marks ρ) hM b (hNoMark ρ b hb)).mp hbD
    apply hClearEq
    intro j hj z hz
    have hm := (hMark ρ z).mpr ⟨j, hj, hz⟩
    have hza := haOut z hm
    have hzb := hbOut z hm
    cases d <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hza hzb <;> omega
  have hBSourceD (r : ℕ) (hr : r ∈ active B) : label (marks σ) r = D :=
    (hExterior dir (marks σ) hMarksNonempty r (hNoMark σ r (hBRemoved r hr).1)).mpr
      (hRemovedOut r (hBRemoved r hr).1 (hBRemoved r hr).2)
  have hBD (r : ℕ) (hr : r ∈ active B) : label (marks B) r = D := by
    rw [hBM]; exact hBSourceD r hr
  have hBCConstant (r : ℕ) (hr : r ∈ active B) : C B s r = C B s q := by
    rw [hBC, hBC]
    exact hExteriorEq σ hMarksNonempty dir r q (hBRemoved r hr).1 hqChild
      (hBSourceD r hr) (hBSourceD q hqA)
  have hInteriorUnit (r : ℕ) (h1 : label (marks σ) r = 1) : C σ s r ≤ 1 := by
    obtain ⟨hl, hr⟩ := (hZ1 (marks σ) r).mp h1
    obtain ⟨a, ha, har⟩ := Finset.filter_nonempty_iff.mp hl
    obtain ⟨b, hb, hrb⟩ := Finset.filter_nonempty_iff.mp hr
    obtain ⟨j, hj, haj⟩ := (hMark σ a).mp ha
    obtain ⟨i, hi, hbi⟩ := (hMark σ b).mp hb
    have hL := hOneLeft σ s j r a hj haj har
    have hR := hOneRight σ s i r b hi hbi hrb
    cases s <;> simp only [C, G, cupLimit, capLimit, chainExt] at hG hL hR ⊢ <;> omega
  have hAOut (r : ℕ) (hr : r ∈ A.childPositions) (h2 : 2 ≤ C A s r) :
      ∀ z ∈ marks A, Rel dir r z := by
    have hN1 := one_le_of_mem_levels hN
    have hNA : N + 1 ∈ A.levels := by
      rw [show A.levels = 1 :: σ.levels.map (· + 1) from part_levels σ keep s m]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
    have hNsA : A.sideAt (N + 1) = s := by
      rw [show A.sideAt (N + 1) = σ.sideAt N from part_sideAt_succ σ keep s m hN1]
      exact hNs
    have hxA : x ∈ A.extPositions (N + 1) := by
      simpa only [A, part_extPositions_succ σ keep s m hN1] using hx
    have hNOnA : N + 1 ∈ A.levelsOn s 0 := List.mem_filter.mpr ⟨hNA, by simp [hNsA]⟩
    have hGA : G A s ≤ 4 := hG
    have hpx := hPIn x hxMark
    have hh := ctx_nonunit_children_exterior_of_two_levels A s 1 (N + 1) q x
      (by simp only [A, part_levels, List.mem_cons, true_or]) hNA (by omega)
      hASide hNsA (hNew q hqChild hqRemoved) hxA
      (by cases s <;> simpa only [G] using hGA)
    intro z hz
    obtain ⟨j, hj, hz⟩ := (hMark A z).mp hz
    rcases hh with hh | hh
    · have hxp := hh.2 p hp (by cases s <;> simpa only [C] using hp2) (N + 1) hNOnA x hxA
      have hzr := hh.2 r hr (by cases s <;> simpa only [C] using h2) j hj z hz
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hpx ⊢ <;> omega
    · have hpx' := hh.2 p hp (by cases s <;> simpa only [C] using hp2) (N + 1) hNOnA x hxA
      have hrz := hh.2 r hr (by cases s <;> simpa only [C] using h2) j hj z hz
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hpx ⊢ <;> omega
  have hAE (r : ℕ) (hr : r ∈ A.childPositions) (h2 : 2 ≤ C A s r) :
      label (marks A) r = E := by
    have hh := (hExterior (!dir) (marks A) hMarksANonempty r (hNoMark A r hr)).mpr
      (fun z hz => by
        have hh := hAOut r hr h2 z hz
        cases dir <;> simpa only [Rel, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, if_false, if_true] using hh)
    cases dir <;> simpa only [E, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true] using hh
  have hOldEToNew (r : ℕ) (hr : r ∈ A.childPositions)
      (he : label (marks σ) r = E) : label (marks A) r = E := by
    have hrc := (hChild keep s m r).mp hr
    have hout := (hExterior (!dir) (marks σ) hMarksNonempty r (hNoMark σ r hrc.1)).mp
      (by cases dir <;> simpa only [E, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, if_false, if_true] using he)
    have hh := (hExterior (!dir) (marks A) hMarksANonempty r (hNoMark A r hr)).mpr (by
      intro z hz
      rcases hPartMarks σ hpositive keep s m z hz with hold | ⟨_, hzc, hzn⟩
      · exact hout z hold
      · have hrx := hout x hxMark
        have hxz := hRemovedOut z hzc hzn x hxMark
        cases dir <;> simp only [Rel, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, if_false, if_true] at hrx hxz ⊢ <;> omega)
    cases dir <;> simpa only [E, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true] using hh
  have hConvertedSource (a : ℕ) (ha : a ∈ units A) (ha2 : 2 ≤ C σ s a) :
      label (marks σ) a = D := by
    obtain ⟨haa, hau⟩ := Finset.mem_filter.mp ha
    have hac := ((hActive A a).mp haa).1
    rcases hLabelCases (marks σ) a with he | h1 | hD
    · have heA := hOldEToNew a hac he
      have hpE := hAE p hp hp2
      have heq := hExteriorEq A hMarksANonempty (!dir) a p hac hp
        (by cases dir <;> simpa only [E, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, if_false, if_true] using heA)
        (by cases dir <;> simpa only [E, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, if_false, if_true] using hpE)
      omega
    · have hu := hInteriorUnit a h1
      omega
    · exact hD
  have hConvertedOut (a : ℕ) (ha : a ∈ units A) (ha2 : 2 ≤ C σ s a) :
      ∀ z ∈ marks σ, Rel dir z a :=
    (hExterior dir (marks σ) hMarksNonempty a
      (hNoMark σ a (hAKept a (Finset.mem_filter.mp ha).1).1)).mp (hConvertedSource a ha ha2)
  have hAT : A.sideAt 1 ≠ t := by rw [hASide]; exact hne
  have hPureA (r : ℕ) : I A r = I σ r := by
    have hL : A.leftExt t 0 r = σ.leftExt t 0 r := (leftExt_part_other hAT r).1
    have hR : A.rightExt t 0 r = σ.rightExt t 0 r := (rightExt_part_other hAT r).1
    have hGAT : G A t = G σ t := by cases t <;> rfl
    simp only [I, hL, hR, hGAT]
  have hAInherited : RN A E ⊆ RN σ E := by
    intro z hz
    obtain ⟨r, hr, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hra, hr2, _⟩ := Finset.mem_filter.mp hr
    have hrs := hPartActive σ keep s m r hra
    have hr2s : 2 ≤ C σ s r := by
      have hle := ctx_part_limits_le σ keep s m r r
      cases s <;> simp only [C, A] at hr2 ⊢ <;> omega
    have hrE : label (marks σ) r = E := by
      have hh := (hExterior (!dir) (marks σ) hMarksNonempty r
        (hNoMark σ r ((hActive σ r).mp hrs.1).1)).mpr (fun z hz => by
          have hh := hAOut r ((hActive A r).mp hra).1 hr2 z (hOldMarks σ keep s m hz)
          cases dir <;> simpa only [Rel, Bool.not_false, Bool.not_true,
            Bool.false_eq_true, if_false, if_true] using hh)
      cases dir <;> simpa only [E, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, if_false, if_true] using hh
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hrs.1, hr2s, hrE⟩,
      by rwa [hPureA] at hz⟩
  have hADempty : RN A D = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨r, hr, _⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hra, hr2, hrD⟩ := Finset.mem_filter.mp hr
    exact hED.1 ((hAE r ((hActive A r).mp hra).1 hr2).symm.trans hrD)
  have hBEempty : RN B E = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨r, hr, _⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hra, _, hrE⟩ := Finset.mem_filter.mp hr
    exact hED.1 (hrE.symm.trans (hBD r hra))
  have hT (ρ : Context) : T ρ = (colors ρ).card + (RN ρ E).card + (RN ρ D).card := by
    cases dir <;> simp only [T, E, D, Bool.false_eq_true, if_false, if_true] <;> omega
  have hReduce (hh : (colors A).card + (colors B).card + (RN B D).card ≤
      (colors σ).card + (RN σ D).card) : T A + T B ≤ T σ := by
    have hcard := Finset.card_le_card hAInherited
    rw [hT A, hT B, hT σ, hADempty, hBEempty, Finset.card_empty]
    omega
  by_cases hqUnit : C B s q ≤ 1
  · have hSourceUnitA (a : ℕ) (ha : a ∈ units A) : C σ s a ≤ 1 := by
      by_contra hn
      have ha2 : 2 ≤ C σ s a := by omega
      have hd := hConvertedSource a ha ha2
      have heq := hExteriorEq σ hMarksNonempty dir a q
        (hAKept a (Finset.mem_filter.mp ha).1).1 hqChild hd (hBSourceD q hqA)
      have hq1 : C σ s q ≤ 1 := by rw [← hBC]; exact hqUnit
      omega
    have hBUnit (a : ℕ) (ha : a ∈ active B) : C B s a ≤ 1 := by
      rw [hBCConstant a ha]; exact hqUnit
    have hBEmpty : RN B D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨a, ha, _⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨haa, ha2, _⟩ := Finset.mem_filter.mp ha
      have hu := hBUnit a haa
      omega
    have hColorA : colors A ⊆ colors σ := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      have haa := (Finset.mem_filter.mp ha).1
      have hu := hSourceUnitA a ha
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨(hPartActive σ keep s m a haa).1, hu⟩,
        (hPartLabel σ hpositive keep s m a hu haa).symm⟩
    have hColorB : colors B ⊆ colors σ := by
      intro z hz
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hba, hbu⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr
        ⟨(hPartActive σ rest t n b hba).1, by rw [← hBC]; exact hbu⟩, by rw [hBM]⟩
    have hDisjoint : Disjoint (colors A) (colors B) := by
      apply Finset.disjoint_left.mpr
      intro z hzA hzB
      obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hzA
      obtain ⟨b, hb, hbz⟩ := Finset.mem_image.mp hzB
      have haa := (Finset.mem_filter.mp ha).1
      have hbr := hBRemoved b (Finset.mem_filter.mp hb).1
      have hu := hSourceUnitA a ha
      apply hExcludeSame σ hpositive hglobalPlain keep m a b hu haa hbr.1 hbr.2
      rw [← hPartLabel σ hpositive keep s m a hu haa, haz, ← hbz, hBM]
    have hc := Finset.card_le_card (Finset.union_subset hColorA hColorB)
    rw [Finset.card_union_of_disjoint hDisjoint] at hc
    apply hReduce
    rw [hBEmpty, Finset.card_empty]
    omega
  have hq2 : 2 ≤ C B s q := by omega
  have hBNonunit (a : ℕ) (ha : a ∈ active B) : 2 ≤ C B s a := by
    rw [hBCConstant a ha]; exact hq2
  have hBColorsEmpty : colors B = ∅ := by
    have hu : units B = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨haa, hau⟩ := Finset.mem_filter.mp ha
      have hh := hBNonunit a haa
      omega
    simp only [colors, hu, Finset.image_empty]
  have hFB : F B D = active B := by
    apply Finset.filter_eq_self.mpr
    intro a ha
    exact ⟨hBNonunit a ha, hBD a ha⟩
  have hQBSource (a : ℕ) (ha : a ∈ active B) : a ∈ F σ D := by
    exact Finset.mem_filter.mpr ⟨(hPartActive σ rest t n a ha).1,
      by rw [← hBC]; exact hBNonunit a ha, hBSourceD a ha⟩
  have hCorner (a r w z : ℕ) (ha : a ∈ active A)
      (hr : r ∈ σ.childPositions) (hrn : r ∉ keep)
      (hw : w ∈ σ.childPositions) (hwn : w ∉ keep) (hz : z ∈ marks σ)
      (hzr : Rel dir z r) (hra : Rel dir r a) (haw : Rel dir a w) : False := by
    obtain ⟨j, hj, hzj⟩ := (hMark σ z).mp hz
    have hj1 := (one_le_of_mem_levelsOn hj).1
    have hzNew : z ∈ A.extPositions (j + 1) := by
      simpa only [A, part_extPositions_succ σ keep s m hj1] using hzj
    have hTwo : [1, j + 1].Sublist (A.levelsOn s 0) := by
      rw [hALevels]
      exact (List.singleton_sublist.mpr (List.mem_map.mpr ⟨j, hj, rfl⟩)).cons_cons 1
    have hrNew := hNew r hr hrn
    have hwNew := hNew w hw hwn
    have hSort : (A.extPositions 1).Pairwise (· ≤ ·) :=
      (List.pairwise_lt_range.filter _).imp le_of_lt
    have hChain : 3 ≤ A.chainExt s a a := by
      cases hd : dir
      · have har : a < r := by simpa only [Rel, hd, Bool.false_eq_true, if_false] using hra
        have hrz : r < z := by simpa only [Rel, hd, Bool.false_eq_true, if_false] using hzr
        have hwa : w < a := by simpa only [Rel, hd, Bool.false_eq_true, if_false] using haw
        have hmR : r ∈ (A.extPositions 1).filter (a < ·) := by simp [hrNew, har]
        have hne := List.ne_nil_of_mem hmR
        let b := ((A.extPositions 1).filter (a < ·)).head hne
        have hb : ((A.extPositions 1).filter (a < ·)).head? = some b :=
          List.head?_eq_some_head hne
        have hbr : b ≤ r := (hSort.filter _).rel_head hmR
        have hmz : z ∈ (A.extPositions (j + 1)).filter (b < ·) := by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hzNew, by omega⟩
        have hneOld := List.ne_nil_of_mem hmz
        have hv := le_getD_max?_of_mem (L := (A.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (rightStep A) (a, 0)).2))
          (List.mem_map.mpr ⟨[1, j + 1], List.mem_sublists.mpr hTwo, rfl⟩)
        change _ ≤ A.rightExt s 0 a at hv
        have hR : 2 ≤ A.rightExt s 0 a := by
          simpa only [List.foldl_cons, List.foldl_nil, rightStep, hb,
            List.head?_eq_some_head hneOld] using hv
        have hL := hOneLeft A s 1 a w hAOne hwNew hwa
        simp only [chainExt]
        omega
      · have hra' : r < a := by simpa only [Rel, hd, if_true] using hra
        have hzr' : z < r := by simpa only [Rel, hd, if_true] using hzr
        have haw' : a < w := by simpa only [Rel, hd, if_true] using haw
        have hmR : r ∈ (A.extPositions 1).filter (· < a) := by simp [hrNew, hra']
        have hne := List.ne_nil_of_mem hmR
        let b := ((A.extPositions 1).filter (· < a)).getLast hne
        have hb : ((A.extPositions 1).filter (· < a)).getLast? = some b :=
          List.getLast?_eq_some_getLast hne
        have hrb : r ≤ b := (hSort.filter _).rel_getLast hmR
        have hmz : z ∈ (A.extPositions (j + 1)).filter (· < b) := by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hzNew, by omega⟩
        have hneOld := List.ne_nil_of_mem hmz
        have hv := le_getD_max?_of_mem (L := (A.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (leftStep A) (a, 0)).2))
          (List.mem_map.mpr ⟨[1, j + 1], List.mem_sublists.mpr hTwo, rfl⟩)
        change _ ≤ A.leftExt s 0 a at hv
        have hL : 2 ≤ A.leftExt s 0 a := by
          simpa only [List.foldl_cons, List.foldl_nil, leftStep, hb,
            List.getLast?_eq_some_getLast hneOld] using hv
        have hR := hOneRight A s 1 a w hAOne hwNew haw'
        simp only [chainExt]
        omega
    have hpos := (hActive A a).mp ha
    have hGA : G A s ≤ 4 := hG
    cases s <;> simp only [G, cupLimit, capLimit] at hGA hpos <;> omega
  have hAMarkerAhead (a : ℕ) (ha : a ∈ active A) (hnot : label (marks A) a ≠ D) :
      ∃ w ∈ marks A, Rel dir a w := by
    have hno := hNoMark A a ((hActive A a).mp ha).1
    have hn : ¬ ∀ w ∈ marks A, Rel dir w a := by
      intro hh
      exact hnot ((hExterior dir (marks A) hMarksANonempty a hno).mpr hh)
    push Not at hn
    obtain ⟨w, hw, hn⟩ := hn
    have hne : a ≠ w := by intro he; exact hno (he ▸ hw)
    exact ⟨w, hw, (hTotal a w hne).resolve_right hn⟩
  have hAOuter (a : ℕ) (ha : a ∈ active A) (hD : label (marks A) a = D) :
      ∀ r ∈ σ.childPositions, r ∉ keep → Rel dir r a := by
    have hout := (hExterior dir (marks A) hMarksANonempty a
      (hNoMark A a ((hActive A a).mp ha).1)).mp hD
    exact fun r hr hn => hout r (hNewMark r hr hn)
  have hAInner (a : ℕ) (ha : a ∈ active A) (hnot : label (marks A) a ≠ D)
      (b : ℕ) (hb : b ∈ active B) : Rel dir a b := by
    have hbOut := hRemovedOut b (hBRemoved b hb).1 (hBRemoved b hb).2
    rcases hTotal a b (hABNe a b ha hb) with hab | hba
    · exact hab
    · exfalso
      have haOut : ∀ z ∈ marks σ, Rel dir z a := fun z hz => hTrans z b a (hbOut z hz) hba
      obtain ⟨w, hw, haw⟩ := hAMarkerAhead a ha hnot
      rcases hPartMarks σ hpositive keep s m w hw with hwOld | ⟨_, hwc, hwn⟩
      · exact hAnti a w haw (haOut w hwOld)
      · exact hCorner a b w x ha (hBRemoved b hb).1 (hBRemoved b hb).2
          hwc hwn hxMark (hbOut x hxMark) hba haw
  have hConvertedLabels (a : ℕ) (ha : a ∈ units A) (ha2 : 2 ≤ C σ s a) :
      label (marks A) a = 1 ∨ label (marks A) a = D := by
    rcases hLabelCases (marks A) a with he | hh
    · have hAx := hOldMarks σ keep s m hxMark
      have hxa := hConvertedOut a ha ha2 x hxMark
      have hno := hNoMark A a ((hActive A a).mp (Finset.mem_filter.mp ha).1).1
      have hrev : Rel dir a x := by
        have hh := (hExterior (!dir) (marks A) hMarksANonempty a hno).mp
          (by cases dir <;> simpa only [E, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] using he)
        have hx := hh x hAx
        cases dir <;> simpa only [Rel, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] using hx
      exact False.elim (hAnti a x hrev hxa)
    · exact hh
  let J := (units A).filter (fun a => C σ s a ≤ 1)
  let K := (units A).filter (fun a => 2 ≤ C σ s a)
  let f := label (marks A)
  have hJK : J ∪ K = units A := by
    apply Finset.ext
    intro a
    constructor
    · intro ha
      rcases Finset.mem_union.mp ha with ha | ha <;> exact (Finset.mem_filter.mp ha).1
    · intro ha
      by_cases hu : C σ s a ≤ 1
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨ha, hu⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨ha, by omega⟩))
  have hJColors : J.image f ⊆ colors σ := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha, hu⟩ := Finset.mem_filter.mp ha
    have haa := (Finset.mem_filter.mp ha).1
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨(hPartActive σ keep s m a haa).1, hu⟩,
      (hPartLabel σ hpositive keep s m a hu haa).symm⟩
  let S (F : Finset ℕ) := F.biUnion (I σ)
  let P (Q : Finset ℕ) := Q.biUnion (I B)
  let lo (a : ℕ) := σ.leftExt t 0 a + 1
  let hi (a : ℕ) := G σ t - 1 - σ.rightExt t 0 a
  let reserved (L H : Finset ℕ) := (L.image lo) ∪ (H.image hi)
  have hReserve (F Q L H : Finset ℕ)
      (hF : F ⊆ active σ) (hQ : Q ⊆ active B) (hQF : Q ⊆ F)
      (hL : ∀ a ∈ L, a ∈ F ∧ a ∉ rest) (hH : ∀ a ∈ H, a ∈ F ∧ a ∉ rest)
      (hleft : ∀ a ∈ L, ∀ b ∈ Q, a < b) (hright : ∀ a ∈ H, ∀ b ∈ Q, b < a) :
      reserved L H ⊆ S F ∧ P Q ⊆ S F \ reserved L H ∧
      (P Q).card + (reserved L H).card ≤ (S F).card ∧
      ((∃ a ∈ L, ∃ b ∈ H, hi b ≤ lo a) → Q = ∅) := by
    exact ctx_part_tracked_rank_reservation σ hpositive t rest n F Q L H
      (fun a ha => (hActive σ a).mp (hF ha))
      (fun a ha => (hActive B a).mp (hQ ha)) hQF hL hH hleft hright
  have hQInherited (Q : Finset ℕ) (hQ : Q ⊆ active B) : Q ⊆ active σ :=
    fun a ha => (hPartActive σ rest t n a (hQ ha)).1
  have hNotRest (a : ℕ) (ha : a ∈ active A) : a ∉ rest := by
    have hk := (hAKept a ha).2
    simp [rest, hk]
  let L := K.filter (· < q)
  let H := K.filter (q < ·)
  have hKH : L ∪ H = K := by
    ext a
    have hneq (ha : a ∈ K) : a ≠ q :=
      hABNe a q (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1 hqA
    simp only [L, H, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
    · intro ha
      have hn := hneq ha
      rcases lt_or_gt_of_ne hn with hl | hr
      · exact Or.inl ⟨ha, hl⟩
      · exact Or.inr ⟨ha, hr⟩
  have hKLabel (a : ℕ) (ha : a ∈ K) :
      (f a = 1 ∧ Rel dir a q) ∨ (f a = D ∧ Rel dir q a) := by
    obtain ⟨haU, ha2⟩ := Finset.mem_filter.mp ha
    have haA := (Finset.mem_filter.mp haU).1
    rcases hConvertedLabels a haU ha2 with h1 | hD
    · left
      refine ⟨h1, hAInner a haA ?_ q hqA⟩
      rw [h1]
      exact hED.2.2.symm
    · exact Or.inr ⟨hD, hAOuter a haA hD q hqChild hqRemoved⟩
  have hLConst (a : ℕ) (ha : a ∈ L) : f a = (if dir then 1 else D) := by
    obtain ⟨haK, haq⟩ := Finset.mem_filter.mp ha
    have hh := hKLabel a haK
    cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hh ⊢ <;> omega
  have hHConst (a : ℕ) (ha : a ∈ H) : f a = (if dir then D else 1) := by
    obtain ⟨haK, hqa⟩ := Finset.mem_filter.mp ha
    have hh := hKLabel a haK
    cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hh ⊢ <;> omega
  have hLeftSep (a : ℕ) (ha : a ∈ L) (b : ℕ) (hb : b ∈ active B) : a < b := by
    obtain ⟨haK, haq⟩ := Finset.mem_filter.mp ha
    have haA := (Finset.mem_filter.mp (Finset.mem_filter.mp haK).1).1
    rcases hKLabel a haK with ⟨h1, hdir⟩ | ⟨hD, hdir⟩
    · have hnot : label (marks A) a ≠ D := by change f a ≠ D; rw [h1]; exact hED.2.2.symm
      have hh := hAInner a haA hnot b hb
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hh hdir <;> omega
    · have hbr := hBRemoved b hb
      have hh := hAOuter a haA hD b hbr.1 hbr.2
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hh hdir <;> omega
  have hRightSep (a : ℕ) (ha : a ∈ H) (b : ℕ) (hb : b ∈ active B) : b < a := by
    obtain ⟨haK, hqa⟩ := Finset.mem_filter.mp ha
    have haA := (Finset.mem_filter.mp (Finset.mem_filter.mp haK).1).1
    rcases hKLabel a haK with ⟨h1, hdir⟩ | ⟨hD, hdir⟩
    · have hnot : label (marks A) a ≠ D := by change f a ≠ D; rw [h1]; exact hED.2.2.symm
      have hh := hAInner a haA hnot b hb
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hh hdir <;> omega
    · have hbr := hBRemoved b hb
      have hh := hAOuter a haA hD b hbr.1 hbr.2
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hh hdir <;> omega
  have hKSource (a : ℕ) (ha : a ∈ K) : a ∈ F σ D ∧ a ∉ rest := by
    obtain ⟨haU, ha2⟩ := Finset.mem_filter.mp ha
    have haA := (Finset.mem_filter.mp haU).1
    exact ⟨Finset.mem_filter.mpr ⟨(hPartActive σ keep s m a haA).1, ha2,
      hConvertedSource a haU ha2⟩, hNotRest a haA⟩
  have hRes := hReserve (F σ D) (active B) L H (Finset.filter_subset _ _)
    (fun _ hh => hh) (fun _ hr => hQBSource _ hr)
    (fun a ha => hKSource a (Finset.mem_filter.mp ha).1)
    (fun a ha => hKSource a (Finset.mem_filter.mp ha).1) hLeftSep hRightSep
  have hQB : (active B).Nonempty := ⟨q, hqA⟩
  have hEndDisjoint : Disjoint (L.image lo) (H.image hi) := by
    apply Finset.disjoint_left.mpr
    intro z hzL hzH
    obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hzL
    obtain ⟨b, hb, hbz⟩ := Finset.mem_image.mp hzH
    exact hQB.ne_empty (hRes.2.2.2 ⟨a, ha, b, hb, by omega⟩)
  have hConstCard (F : Finset ℕ) (g h : ℕ → ℕ) (c : ℕ)
      (hc : ∀ a ∈ F, g a = c) : (F.image g).card ≤ (F.image h).card := by
    by_cases hn : F.Nonempty
    · obtain ⟨a, ha⟩ := hn
      have he : F.image g = {c} := by
        apply Finset.Subset.antisymm
        · intro z hz
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
          simpa only [Finset.mem_singleton] using hc b hb
        · intro z hz
          have he := Finset.mem_singleton.mp hz
          subst z
          exact Finset.mem_image.mpr ⟨a, ha, hc a ha⟩
      have hp : 0 < (F.image h).card := Finset.card_pos.mpr ⟨h a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
      rw [he, Finset.card_singleton]
      omega
    · have he := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [he, Finset.image_empty, Finset.card_empty, le_refl]
  have hKCharge : (K.image f).card ≤ (reserved L H).card := by
    have hcL := hConstCard L f lo _ hLConst
    have hcH := hConstCard H f hi _ hHConst
    have hh : (K.image f).card ≤ (L.image f).card + (H.image f).card := by
      rw [← hKH, Finset.image_union]
      exact Finset.card_union_le _ _
    have he : (reserved L H).card = (L.image lo).card + (H.image hi).card :=
      Finset.card_union_of_disjoint hEndDisjoint
    omega
  have hACharge : (colors A).card ≤ (colors σ).card + (reserved L H).card := by
    have hJCard := Finset.card_le_card hJColors
    have hh : (colors A).card ≤ (J.image f).card + (K.image f).card := by
      change ((units A).image f).card ≤ _
      rw [← hJK, Finset.image_union]
      exact Finset.card_union_le _ _
    omega
  apply hReduce
  have hh := hRes.2.2.1
  have hBDRanks : RN B D = P (active B) := by simp only [RN, hFB, P]
  change (P (active B)).card + (reserved L H).card ≤ (RN σ D).card at hh
  rw [hBColorsEmpty, Finset.card_empty, hBDRanks]
  omega

end ErdosSzekeres
