import ESBlueprint.B.CtxNonunitPartUnitRankPotentialDrop
import ESBlueprint.B.CtxPartTrackedRankReservation

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Both potential components decrease across a cut whose opposite-axis companion retains an active child of chosen capacity at least two. Under positive labels, chosen global at most four, two actual indexed chosen-axis levels and a kept source child, every child of the chosen-axis part is forced to have chosen capacity at most one. The raw occupied-unit-zone plus nonunit-opposite-rank count decreases additively, and the chosen-part raw count plus the companion mixed potential is at most the source all-rank cardinality plus one. Consequently the minimum of the two potentials decreases across the cut. Kept sets and independent maxima are arbitrary. Three-extension corner annihilation excludes shared interior zones and separates converted children into inner and outer groups; tracked rank reservations charge their distinct endpoint values. Completes the active-nonunit-companion branch of the singleton-end sandwich mixed-potential induction without assuming unit capacity in the chosen-axis part.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_cut_potential_drop_of_nonunit_companion (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ σ.childPositions) (hkeep : p ∈ keep)
  (hq : q ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions)
  (hqcup : 0 < (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit q q)
  (hqcap : 0 < (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit q q)
  (hnonunit : 2 ≤ (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit q q
    | Ctx.Side.upper => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit q q) s) :
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
  let ranks := fun (ρ : Ctx.Context) => (active ρ).biUnion (rankInterval ρ)
  let nonunitRanks := fun (ρ : Ctx.Context) =>
    ((active ρ).filter (fun r => 2 ≤ limit ρ r)).biUnion (rankInterval ρ)
  let raw := fun (ρ : Ctx.Context) => unitZones ρ + (nonunitRanks ρ).card
  let potential := fun (ρ : Ctx.Context) => min (raw ρ) ((ranks ρ).card + 1)
  let ownPart := σ.part keep s m
  let otherPart := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  (∀ r ∈ ownPart.childPositions, limit ownPart r ≤ 1) ∧
    (raw ownPart + raw otherPart ≤ raw σ) ∧
    (raw ownPart + potential otherPart ≤ (ranks σ).card + 1) ∧
    potential ownPart + potential otherPart ≤ potential σ := by
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
  let RN (ρ : Context) := (nonunits ρ).biUnion (I ρ)
  let R (ρ : Context) := (active ρ).biUnion (I ρ)
  let T (ρ : Context) := (colors ρ).card + (RN ρ).card
  let V (ρ : Context) := min (T ρ) ((R ρ).card + 1)
  let rest := σ.childPositions.filter (· ∉ keep)
  let A := σ.part keep s m
  let B := σ.part rest t n
  change (∀ r ∈ A.childPositions, C A s r ≤ 1) ∧ T A + T B ≤ T σ ∧
    T A + V B ≤ (R σ).card + 1 ∧ V A + V B ≤ V σ
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
  have hqA : q ∈ active B := (hActive B q).mpr ⟨hq, hqcup, hqcap⟩
  have hqSource := hPartActive σ rest t n q hqA
  have hqChild := ((hActive σ q).mp hqSource.1).1
  have hqRemoved : q ∉ keep := of_decide_eq_true (List.mem_filter.mp hqSource.2).2
  have hq2 : 2 ≤ C B s q := hnonunit
  have hBSide : B.sideAt 1 = t := hSide rest t n p hp (by simp [rest, hkeep])
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
  have hPure (ρ : Context) (r : ℕ) (hr : r ∈ active ρ) : (I ρ r).Nonempty := by
    have hh := (hActive ρ r).mp hr
    have hbound : ρ.leftExt t 0 r + 1 ≤ G ρ t - 1 - ρ.rightExt t 0 r := by
      cases t <;> simp only [G, cupLimit, capLimit, chainExt] at hh ⊢ <;> omega
    exact ⟨ρ.leftExt t 0 r + 1, Finset.mem_Icc.mpr ⟨le_rfl, hbound⟩⟩
  have hQB : (nonunits B).Nonempty := ⟨q, Finset.mem_filter.mpr ⟨hqA, hq2⟩⟩
  have hRNB : (RN B).Nonempty := by
    obtain ⟨z, hz⟩ := hPure B q hqA
    exact ⟨z, Finset.mem_biUnion.mpr ⟨q, Finset.mem_filter.mpr ⟨hqA, hq2⟩, hz⟩⟩
  have hUnitA (r : ℕ) (hr : r ∈ A.childPositions) : C A s r ≤ 1 := by
    by_contra hh
    have hdrop := ctx_nonunit_part_unit_rank_potential_drop σ hpositive s t hne N M x y
      hN hM hNM hNs hMs hx hy (by cases s <;> simpa only [G] using hG)
      keep m n r q hr (by cases s <;> dsimp only [C, A] at hh ⊢ <;> omega) hqChild hqRemoved
    have hempty : RN B = ∅ := by
      have he := hdrop.2.2.1
      cases s <;> cases t <;> simpa only [RN, nonunits, active, C, I, G, B, rest] using he
    exact hRNB.ne_empty hempty
  have hUnitsA : units A = active A := by
    apply Finset.filter_eq_self.mpr
    intro r hr
    exact hUnitA r ((hActive A r).mp hr).1
  have hRNA : RN A = ∅ := by
    have he : nonunits A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨ha, h2⟩ := Finset.mem_filter.mp hr
      have hu := hUnitA r ((hActive A r).mp ha).1
      omega
    simp only [RN, he, Finset.biUnion_empty]
  have hTA : T A = ((active A).image (label (marks A))).card := by
    simp only [T, colors, hUnitsA, hRNA, Finset.card_empty, Nat.add_zero]
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
  have hSourceOut (r : ℕ) (hr : r ∈ σ.childPositions) (h2 : 2 ≤ C σ s r) :
      ∀ z ∈ marks σ, Rel dir z r := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := (hMark σ z).mp hz
    exact hOutside r hr h2 j hj z hz
  have hSourceD (r : ℕ) (hr : r ∈ σ.childPositions) (h2 : 2 ≤ C σ s r) :
      label (marks σ) r = D :=
    (hExterior dir (marks σ) hMarksNonempty r (hNoMark σ r hr)).mpr (hSourceOut r hr h2)
  have hUnitNotD (r : ℕ) (hr : r ∈ σ.childPositions) (hu : C σ s r ≤ 1) :
      label (marks σ) r ≠ D := by
    intro he
    have hrOut := (hExterior dir (marks σ) hMarksNonempty r (hNoMark σ r hr)).mp he
    have hq2s : 2 ≤ C σ s q := by rw [← hBC]; exact hq2
    have hqOut := hSourceOut q hqChild hq2s
    have heq : C σ s r = C σ s q := by
      apply hClearEq
      intro j hj z hz
      have hm := (hMark σ z).mpr ⟨j, hj, hz⟩
      have hrz := hrOut z hm
      have hqz := hqOut z hm
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hrz hqz <;> omega
    omega
  have hQBSource (r : ℕ) (hr : r ∈ nonunits B) : r ∈ nonunits σ := by
    obtain ⟨ha, h2⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨(hPartActive σ rest t n r ha).1, by rw [← hBC]; exact h2⟩
  have hBUnit (r : ℕ) (hr : r ∈ units B) : r ∈ units σ := by
    obtain ⟨ha, hu⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨(hPartActive σ rest t n r ha).1, by rw [← hBC]; exact hu⟩
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
      (b : ℕ) (hb : b ∈ nonunits B) : Rel dir a b := by
    obtain ⟨hbA, hb2⟩ := Finset.mem_filter.mp hb
    have hbσ := hQBSource b hb
    have hbOut := hSourceOut b (hBRemoved b hbA).1 (Finset.mem_filter.mp hbσ).2
    rcases hTotal a b (hABNe a b ha hbA) with hab | hba
    · exact hab
    · exfalso
      have haOut : ∀ z ∈ marks σ, Rel dir z a := fun z hz => hTrans z b a (hbOut z hz) hba
      obtain ⟨w, hw, haw⟩ := hAMarkerAhead a ha hnot
      rcases hPartMarks σ hpositive keep s m w hw with hwOld | ⟨_, hwc, hwn⟩
      · exact hAnti a w haw (haOut w hwOld)
      · exact hCorner a b w x ha (hBRemoved b hbA).1 (hBRemoved b hbA).2
          hwc hwn hxMark (hbOut x hxMark) hba haw
  have hConvertedLabels (a : ℕ) (ha : a ∈ active A) (ha2 : 2 ≤ C σ s a) :
      label (marks A) a = 1 ∨ label (marks A) a = D := by
    rcases hLabelCases (marks A) a with he | hh
    · have hAx := hOldMarks σ keep s m hxMark
      have hxa := hSourceOut a (hAKept a ha).1 ha2 x hxMark
      have hno := hNoMark A a ((hActive A a).mp ha).1
      have hrev : Rel dir a x := by
        have hh := (hExterior (!dir) (marks A) hMarksANonempty a hno).mp
          (by cases dir <;> simpa only [E, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] using he)
        have hx := hh x hAx
        cases dir <;> simpa only [Rel, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] using hx
      exact False.elim (hAnti a x hrev hxa)
    · exact hh
  let ZA := (active A).image (label (marks A))
  let UB := colors B
  have hBNoD : D ∉ UB := by
    intro hh
    obtain ⟨b, hb, hbD⟩ := Finset.mem_image.mp hh
    have hbs := Finset.mem_filter.mp (hBUnit b hb)
    apply hUnitNotD b ((hActive σ b).mp hbs.1).1 hbs.2
    simpa only [hBM] using hbD
  have hZoneDisjoint : Disjoint ZA UB := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hzA
    obtain ⟨b, hb, hbz⟩ := Finset.mem_image.mp hzB
    have hbA := (Finset.mem_filter.mp hb).1
    have hbr := hBRemoved b hbA
    have he : label (marks A) a = label (marks σ) b := by
      rw [haz, ← hbz, hBM]
    by_cases hu : C σ s a ≤ 1
    · have hpres := hPartLabel σ hpositive keep s m a hu ha
      exact hExcludeSame σ hpositive hglobalPlain keep m a b hu ha hbr.1 hbr.2
        (hpres.symm.trans he)
    · have ha2 : 2 ≤ C σ s a := by omega
      have hlabels := hConvertedLabels a ha ha2
      have hnot : label (marks A) a ≠ D := by
        intro hh
        apply hBNoD
        simpa only [← haz, hh] using hzB
      have ha1 : label (marks A) a = 1 := hlabels.resolve_right hnot
      have hb1 : label (marks σ) b = 1 := he.symm.trans ha1
      have hbi := (hZ1 (marks σ) b).mp hb1
      obtain ⟨l, hl, hlb⟩ := Finset.filter_nonempty_iff.mp hbi.1
      obtain ⟨r, hr, hbr'⟩ := Finset.filter_nonempty_iff.mp hbi.2
      have hout := hSourceOut a (hAKept a ha).1 ha2
      have hla := hout l hl
      have hra := hout r hr
      obtain ⟨w, hw, haw⟩ := hAMarkerAhead a ha hnot
      rcases hPartMarks σ hpositive keep s m w hw with hwOld | ⟨_, hwc, hwn⟩
      · exact hAnti a w haw (hout w hwOld)
      · cases hd : dir
        · have haz : Rel dir r b := by simpa only [Rel, hd, Bool.false_eq_true, if_false] using hbr'
          have hba : Rel dir b a := by
            simp only [Rel, hd, Bool.false_eq_true, if_false] at hla ⊢
            omega
          exact hCorner a b w r ha hbr.1 hbr.2 hwc hwn hr haz hba haw
        · have haz : Rel dir l b := by simpa only [Rel, hd, if_true] using hlb
          have hba : Rel dir b a := by
            simp only [Rel, hd, if_true] at hra ⊢
            omega
          exact hCorner a b w l ha hbr.1 hbr.2 hwc hwn hl haz hba haw
  have hZoneCard : ZA.card + UB.card ≤ 3 := by
    have hsub : ZA ∪ UB ⊆ ({E, 1, D} : Finset ℕ) := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hLabelCases (marks A) a
      · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hz
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hLabelCases (marks B) b
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hZoneDisjoint] at hh
    have he : ({E, 1, D} : Finset ℕ).card = 3 := by cases dir <;> simp [E, D]
    omega
  have hZoneCardNoD (hn : D ∉ ZA) : ZA.card + UB.card ≤ 2 := by
    have hsub : ZA ∪ UB ⊆ ({E, 1} : Finset ℕ) := by
      intro z hz
      have hzD : z ≠ D := by
        intro he
        subst z
        exact (Finset.mem_union.mp hz).elim hn hBNoD
      have hc : z = E ∨ z = 1 ∨ z = D := by
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
          exact hLabelCases (marks A) a
        · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hz
          exact hLabelCases (marks B) b
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hc.elim Or.inl (fun h => h.elim Or.inr (fun he => False.elim (hzD he)))
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hZoneDisjoint] at hh
    have he : ({E, 1} : Finset ℕ).card = 2 := by cases dir <;> simp [E]
    omega
  have hBColorsSource : UB ⊆ colors σ := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨b, hBUnit b hb, by rw [hBM]⟩
  let J := (active A).filter (fun a => C σ s a ≤ 1)
  let K := (active A).filter (fun a => 2 ≤ C σ s a)
  let f := label (marks A)
  have hJK : J ∪ K = active A := by
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
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨(hPartActive σ keep s m a ha).1, hu⟩,
      (hPartLabel σ hpositive keep s m a hu ha).symm⟩
  have hJZA : J.image f ⊆ ZA := Finset.image_subset_image (Finset.filter_subset _ _)
  have hJCard : (J.image f).card + UB.card ≤ (colors σ).card := by
    have hd : Disjoint (J.image f) UB := hZoneDisjoint.mono_left hJZA
    have hh := Finset.card_le_card (Finset.union_subset hJColors hBColorsSource)
    rw [Finset.card_union_of_disjoint hd] at hh
    exact hh
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
  have hLHA : ∀ a ∈ L ∪ H, a ∈ active A := by
    intro a ha
    rcases Finset.mem_union.mp ha with hh | hh <;>
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
  have hKH : L ∪ H = K := by
    ext a
    have hneq (ha : a ∈ K) : a ≠ q := hABNe a q (Finset.mem_filter.mp ha).1 hqA
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
    obtain ⟨haA, ha2⟩ := Finset.mem_filter.mp ha
    rcases hConvertedLabels a haA ha2 with h1 | hD
    · left
      refine ⟨h1, hAInner a haA ?_ q (Finset.mem_filter.mpr ⟨hqA, hq2⟩)⟩
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
  have hLeftSep (a : ℕ) (ha : a ∈ L) (b : ℕ) (hb : b ∈ nonunits B) : a < b := by
    obtain ⟨haK, haq⟩ := Finset.mem_filter.mp ha
    have haA := (Finset.mem_filter.mp haK).1
    rcases hKLabel a haK with ⟨h1, hdir⟩ | ⟨hD, hdir⟩
    · have hnot : label (marks A) a ≠ D := by change f a ≠ D; rw [h1]; exact hED.2.2.symm
      have hh := hAInner a haA hnot b hb
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hh hdir <;> omega
    · have hbr := hBRemoved b (Finset.mem_filter.mp hb).1
      have hh := hAOuter a haA hD b hbr.1 hbr.2
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hh hdir <;> omega
  have hRightSep (a : ℕ) (ha : a ∈ H) (b : ℕ) (hb : b ∈ nonunits B) : b < a := by
    obtain ⟨haK, hqa⟩ := Finset.mem_filter.mp ha
    have haA := (Finset.mem_filter.mp haK).1
    rcases hKLabel a haK with ⟨h1, hdir⟩ | ⟨hD, hdir⟩
    · have hnot : label (marks A) a ≠ D := by change f a ≠ D; rw [h1]; exact hED.2.2.symm
      have hh := hAInner a haA hnot b hb
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hh hdir <;> omega
    · have hbr := hBRemoved b (Finset.mem_filter.mp hb).1
      have hh := hAOuter a haA hD b hbr.1 hbr.2
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hh hdir <;> omega
  have hLSource (a : ℕ) (ha : a ∈ L) : a ∈ nonunits σ ∧ a ∉ rest := by
    obtain ⟨haK, _⟩ := Finset.mem_filter.mp ha
    obtain ⟨haA, ha2⟩ := Finset.mem_filter.mp haK
    exact ⟨Finset.mem_filter.mpr ⟨(hPartActive σ keep s m a haA).1, ha2⟩, hNotRest a haA⟩
  have hHSource (a : ℕ) (ha : a ∈ H) : a ∈ nonunits σ ∧ a ∉ rest := by
    obtain ⟨haK, _⟩ := Finset.mem_filter.mp ha
    obtain ⟨haA, ha2⟩ := Finset.mem_filter.mp haK
    exact ⟨Finset.mem_filter.mpr ⟨(hPartActive σ keep s m a haA).1, ha2⟩, hNotRest a haA⟩
  have hRes := hReserve (nonunits σ) (nonunits B) L H (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) (fun _ hr => hQBSource _ hr) hLSource hHSource hLeftSep hRightSep
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
  have hZACharge : ZA.card + UB.card ≤ (colors σ).card + (reserved L H).card := by
    have hh : ZA.card ≤ (J.image f).card + (K.image f).card := by
      change ((active A).image f).card ≤ _
      rw [← hJK, Finset.image_union]
      exact Finset.card_union_le _ _
    omega
  have hRaw : T A + T B ≤ T σ := by
    have hh := hRes.2.2.1
    change (RN B).card + (reserved L H).card ≤ (RN σ).card at hh
    rw [hTA]
    change ZA.card + (UB.card + (RN B).card) ≤ (colors σ).card + (RN σ).card
    omega
  have hRankInherited : (R B).card ≤ (R σ).card := by
    have hh := (hReserve (active σ) (active B) ∅ ∅ (fun _ hh => hh) (fun _ hh => hh)
      (hQInherited (active B) (fun _ hh => hh)) (by simp) (by simp) (by simp) (by simp)).2.2.1
    simpa only [P, S, R, reserved, Finset.image_empty, Finset.union_empty,
      Finset.card_empty, Nat.add_zero] using hh
  have hOneCharge (Q : Finset ℕ) (hQ : Q ⊆ active B) (a : ℕ) (ha : a ∈ active A)
      (hsep : (∀ b ∈ Q, a < b) ∨ (∀ b ∈ Q, b < a)) :
      (P Q).card + 1 ≤ (R σ).card := by
    have haF := (hPartActive σ keep s m a ha).1
    have han := hNotRest a ha
    rcases hsep with hl | hr
    · have hh := (hReserve (active σ) Q {a} ∅ (fun _ hh => hh) hQ (hQInherited Q hQ)
        (by intro b hb; have he := Finset.mem_singleton.mp hb; subst b; exact ⟨haF, han⟩)
        (by simp) (by intro b hb; have he := Finset.mem_singleton.mp hb; subst b; exact hl)
        (by simp)).2.2.1
      simpa only [S, R, reserved, Finset.image_singleton, Finset.image_empty,
        Finset.union_empty, Finset.card_singleton] using hh
    · have hh := (hReserve (active σ) Q ∅ {a} (fun _ hh => hh) hQ (hQInherited Q hQ)
        (by simp) (by intro b hb; have he := Finset.mem_singleton.mp hb; subst b; exact ⟨haF, han⟩)
        (by simp) (by intro b hb; have he := Finset.mem_singleton.mp hb; subst b; exact hr)).2.2.1
      simpa only [S, R, reserved, Finset.image_singleton, Finset.image_empty,
        Finset.empty_union, Finset.card_singleton] using hh
  have hTwoCharge (a b : ℕ) (ha : a ∈ active A) (hb : b ∈ active A)
      (hleft : ∀ r ∈ nonunits B, a < r) (hright : ∀ r ∈ nonunits B, r < b) :
      (RN B).card + 2 ≤ (R σ).card := by
    have haF := (hPartActive σ keep s m a ha).1
    have hbF := (hPartActive σ keep s m b hb).1
    have han := hNotRest a ha
    have hbn := hNotRest b hb
    have hh := hReserve (active σ) (nonunits B) {a} {b} (fun _ hh => hh)
      (Finset.filter_subset _ _) (hQInherited (nonunits B) (Finset.filter_subset _ _))
      (by intro r hr; have he := Finset.mem_singleton.mp hr; subst r; exact ⟨haF, han⟩)
      (by intro r hr; have he := Finset.mem_singleton.mp hr; subst r; exact ⟨hbF, hbn⟩)
      (by intro r hr; have he := Finset.mem_singleton.mp hr; subst r; exact hleft)
      (by intro r hr; have he := Finset.mem_singleton.mp hr; subst r; exact hright)
    have hneq : lo a ≠ hi b := by
      intro he
      exact hQB.ne_empty (hh.2.2.2 ⟨a, by simp, b, by simp, by omega⟩)
    have hcard : (reserved {a} {b}).card = 2 := by simp [reserved, hneq]
    have hc := hh.2.2.1
    rw [hcard] at hc
    exact hc
  have hCap : T A + V B ≤ (R σ).card + 1 := by
    have hvT : V B ≤ UB.card + (RN B).card := Nat.min_le_left _ _
    have hvR : V B ≤ (R B).card + 1 := Nat.min_le_right _ _
    rw [hTA]
    change ZA.card + V B ≤ (R σ).card + 1
    by_cases hZA : ZA.Nonempty
    · by_cases hD : D ∈ ZA
      · obtain ⟨a, ha, haD⟩ := Finset.mem_image.mp hD
        by_cases hsmall : ZA.card ≤ 1
        · have hout (b : ℕ) (hb : b ∈ active B) : Rel dir b a :=
            hAOuter a ha haD b (hBRemoved b hb).1 (hBRemoved b hb).2
          have hc := hOneCharge (active B) (fun _ hh => hh) a ha (by
            cases hd : dir
            · left; intro b hb
              simpa only [Rel, hd, Bool.false_eq_true, if_false] using hout b hb
            · right; intro b hb
              simpa only [Rel, hd, if_true] using hout b hb)
          change (R B).card + 1 ≤ (R σ).card at hc
          omega
        · have hother : ∃ z ∈ ZA, z ≠ D := by
            by_contra hn
            push Not at hn
            have hs : ZA ⊆ {D} := fun z hz => Finset.mem_singleton.mpr (hn z hz)
            have hc := Finset.card_le_card hs
            simp only [Finset.card_singleton] at hc
            omega
          obtain ⟨z, hz, hzD⟩ := hother
          obtain ⟨b, hb, hbz⟩ := Finset.mem_image.mp hz
          have hbD : label (marks A) b ≠ D := by rw [hbz]; exact hzD
          have hin (r : ℕ) (hr : r ∈ nonunits B) : Rel dir b r := hAInner b hb hbD r hr
          have hout (r : ℕ) (hr : r ∈ nonunits B) : Rel dir r a :=
            hAOuter a ha haD r (hBRemoved r (Finset.mem_filter.mp hr).1).1
              (hBRemoved r (Finset.mem_filter.mp hr).1).2
          have hc : (RN B).card + 2 ≤ (R σ).card := by
            cases hd : dir
            · apply hTwoCharge a b ha hb
              · intro r hr; simpa only [Rel, hd, Bool.false_eq_true, if_false] using hout r hr
              · intro r hr; simpa only [Rel, hd, Bool.false_eq_true, if_false] using hin r hr
            · apply hTwoCharge b a hb ha
              · intro r hr; simpa only [Rel, hd, if_true] using hin r hr
              · intro r hr; simpa only [Rel, hd, if_true] using hout r hr
          omega
      · obtain ⟨z, hz⟩ := hZA
        obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hz
        have haD : label (marks A) a ≠ D := by
          intro he
          apply hD
          exact Finset.mem_image.mpr ⟨a, ha, he⟩
        have hin (r : ℕ) (hr : r ∈ nonunits B) : Rel dir a r := hAInner a ha haD r hr
        have hc := hOneCharge (nonunits B) (Finset.filter_subset _ _) a ha (by
          cases hd : dir
          · right; intro r hr
            simpa only [Rel, hd, Bool.false_eq_true, if_false] using hin r hr
          · left; intro r hr
            simpa only [Rel, hd, if_true] using hin r hr)
        change (RN B).card + 1 ≤ (R σ).card at hc
        have hz := hZoneCardNoD hD
        omega
    · have he := Finset.not_nonempty_iff_eq_empty.mp hZA
      rw [he, Finset.card_empty, Nat.zero_add]
      omega
  refine ⟨hUnitA, hRaw, hCap, ?_⟩
  have haV : V A ≤ T A := Nat.min_le_left _ _
  have hbV : V B ≤ T B := Nat.min_le_left _ _
  apply Nat.le_min.mpr
  constructor <;> omega

end ErdosSzekeres
