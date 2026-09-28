import ESBlueprint.B.CtxNonunitPartActiveCompanionExteriorPotentialDrop

import ESBlueprint.B.CtxMixedClearOrSingletonRankCoverPotential

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Charge the full chosen-unit part contribution together with the raw companion exterior potential to the source raw exterior potential. Under positive labels, chosen global at most four, one actual indexed chosen marker and witnesses that both kept and removed source sets are nonempty, assume only active children of the chosen part have chosen capacity at most one. Every fuel approximation of that part and its full bound, plus the companion occupied-unit-zone and separate nonunit exterior-rank count, are at most the same source count. Kept lists and new maxima are arbitrary and the companion may be inactive. Original source-unit colors are inherited and unavailable to the companion; converted unit classes receive exterior-tagged endpoint ranks. Coincident endpoint colors spanning two new zones are merged using a common singleton opposite-rank cover, while other colors use clear or interior chosen-rank covers. Supplies the raw-count step for unit-own cuts in the one-level mixed-potential induction toward the singleton-end sandwich proof.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_unit_part_exterior_potential_charge (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep)
  (hunit : ∀ r ∈ (σ.part keep s m).childPositions,
    0 < (σ.part keep s m).cupLimit r r → 0 < (σ.part keep s m).capLimit r r →
    (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => (σ.part keep s m).cupLimit r r
      | Ctx.Side.upper => (σ.part keep s m).capLimit r r) s ≤ 1) :
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
  let ownPart := σ.part keep s m
  let otherPart := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  (∀ fuel, Ctx.Context.boundFuel fuel ownPart + potential otherPart ≤ potential σ) ∧
    ownPart.bound + potential otherPart ≤ potential σ := by
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
  change (∀ fuel, boundFuel fuel A + T B ≤ T σ) ∧ A.bound + T B ≤ T σ
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
  have hGA : G A s ≤ 4 := hG
  have hglobalPlain : (match s with | Side.lower => σ.u | Side.upper => σ.a) ≤ 4 := by
    cases s <;> simpa only [G] using hG
  have hpSource := (hChild keep s m p).mp hp
  have hqChild := hq
  have hqRemoved := hremoved
  have hUnitA (a : ℕ) (ha : a ∈ active A) : C A s a ≤ 1 := by
    obtain ⟨hc, hl, hu⟩ := (hActive A a).mp ha
    exact hunit a hc hl hu
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
  have hInteriorUnit (r : ℕ) (h1 : label (marks σ) r = 1) : C σ s r ≤ 1 := by
    obtain ⟨hl, hr⟩ := (hZ1 (marks σ) r).mp h1
    obtain ⟨a, ha, har⟩ := Finset.filter_nonempty_iff.mp hl
    obtain ⟨b, hb, hrb⟩ := Finset.filter_nonempty_iff.mp hr
    obtain ⟨j, hj, haj⟩ := (hMark σ a).mp ha
    obtain ⟨i, hi, hbi⟩ := (hMark σ b).mp hb
    have hL := hOneLeft σ s j r a hj haj har
    have hR := hOneRight σ s i r b hi hbi hrb
    cases s <;> simp only [C, G, cupLimit, capLimit, chainExt] at hG hL hR ⊢ <;> omega
  have hCorner (dir : Bool) (a r w z : ℕ) (ha : a ∈ active A)
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
  have hSort (ρ : Context) (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp le_of_lt
  have hStepLeft (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : c ≤ d) :
      (leftStep ρ (p, c) j).1 ≤ (leftStep ρ (q, d) j).1 ∧
      (leftStep ρ (p, c) j).2 ≤ (leftStep ρ (q, d) j).2 := by
    cases ha : ((ρ.extPositions j).filter (· < p)).getLast? with
    | none =>
      have hnil := List.getLast?_eq_none_iff.mp ha
      cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
      | none => simpa only [leftStep, ha, hb] using And.intro hpq hcd
      | some y =>
        have hy := List.mem_of_mem_getLast? (Option.mem_def.mpr hb)
        have hpy : p ≤ y := by
          by_contra h
          have hx : y ∈ (ρ.extPositions j).filter (· < p) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hx
          exact List.not_mem_nil hx
        simpa only [leftStep, ha, hb] using And.intro hpy (show c ≤ d + 1 by omega)
    | some x =>
      have hx := List.mem_of_mem_getLast? (Option.mem_def.mpr ha)
      have hxq : x ∈ (ρ.extPositions j).filter (· < q) := by
        have hxp : x < p := of_decide_eq_true (List.mem_filter.mp hx).2
        exact List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
      cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
      | none =>
        have hnil := List.getLast?_eq_none_iff.mp hb
        rw [hnil] at hxq
        exact False.elim (List.not_mem_nil hxq)
      | some y =>
        have hlast : ((ρ.extPositions j).filter (· < q)).getLast (List.ne_nil_of_mem hxq) = y := by
          rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hxq)] at hb
          exact Option.some.inj hb
        have hxy : x ≤ y := by
          simpa only [hlast] using ((hSort ρ j).filter _).rel_getLast hxq
        simpa only [leftStep, ha, hb] using And.intro hxy (show c + 1 ≤ d + 1 by omega)
  have hStepRight (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : d ≤ c) :
      (rightStep ρ (p, c) j).1 ≤ (rightStep ρ (q, d) j).1 ∧
      (rightStep ρ (q, d) j).2 ≤ (rightStep ρ (p, c) j).2 := by
    cases ha : ((ρ.extPositions j).filter (p < ·)).head? with
    | none =>
      have hnil := List.head?_eq_none_iff.mp ha
      cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
      | none => simpa only [rightStep, ha, hb] using And.intro hpq hcd
      | some y =>
        have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
        have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
        have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
          List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
        rw [hnil] at hyp
        exact False.elim (List.not_mem_nil hyp)
    | some x =>
      have hx := List.mem_of_mem_head? (Option.mem_def.mpr ha)
      cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
      | none =>
        have hnil := List.head?_eq_none_iff.mp hb
        have hxq : x ≤ q := by
          by_contra h
          have hmem : x ∈ (ρ.extPositions j).filter (q < ·) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hmem
          exact List.not_mem_nil hmem
        simpa only [rightStep, ha, hb] using And.intro hxq (show d ≤ c + 1 by omega)
      | some y =>
        have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
        have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
        have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
          List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
        have hhead : ((ρ.extPositions j).filter (p < ·)).head (List.ne_nil_of_mem hyp) = x := by
          rw [List.head?_eq_some_head (List.ne_nil_of_mem hyp)] at ha
          exact Option.some.inj ha
        have hxy : x ≤ y := by
          simpa only [hhead] using ((hSort ρ j).filter _).rel_head hyp
        simpa only [rightStep, ha, hb] using And.intro hxy (show d + 1 ≤ c + 1 by omega)
  have hFoldLeft (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → c ≤ d →
      (ls.foldl (leftStep ρ) (p, c)).1 ≤ (ls.foldl (leftStep ρ) (q, d)).1 ∧
      (ls.foldl (leftStep ρ) (p, c)).2 ≤ (ls.foldl (leftStep ρ) (q, d)).2 := by
    intro ls
    induction ls with
    | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
    | cons j ls ih =>
      intro p q c d hpq hcd
      have h := hStepLeft ρ j p q c d hpq hcd
      simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
  have hFoldRight (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → d ≤ c →
      (ls.foldl (rightStep ρ) (p, c)).1 ≤ (ls.foldl (rightStep ρ) (q, d)).1 ∧
      (ls.foldl (rightStep ρ) (q, d)).2 ≤ (ls.foldl (rightStep ρ) (p, c)).2 := by
    intro ls
    induction ls with
    | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
    | cons j ls ih =>
      intro p q c d hpq hcd
      have h := hStepRight ρ j p q c d hpq hcd
      simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
  have hLeftMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
      ρ.leftExt v top p ≤ ρ.leftExt v top q := by
    simp only [leftExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldLeft ρ ls p q 0 0 hpq le_rfl).2⟩
  have hRightMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
      ρ.rightExt v top q ≤ ρ.rightExt v top p := by
    simp only [rightExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldRight ρ ls p q 0 0 hpq le_rfl).2⟩
  have hAT : A.sideAt 1 ≠ t := by rw [hASide]; exact hne
  have hPureA (a : ℕ) : A.leftExt t 0 a = σ.leftExt t 0 a ∧
      A.rightExt t 0 a = σ.rightExt t 0 a :=
    ⟨(leftExt_part_other hAT a).1, (rightExt_part_other hAT a).1⟩
  have hGAT : G A t = G σ t := by cases t <;> rfl
  have hZones (M : Finset ℕ) (a : ℕ) : label M a = 0 ∨ label M a = 1 ∨ label M a = 2 := by
    unfold label
    split_ifs <;> omega
  have hLeftOuter (ρ : Context) (a : ℕ) (ha : a ∈ ρ.childPositions)
      (hz : label (marks ρ) a = 0) : ∀ z ∈ marks ρ, a < z :=
    hAllRight (marks ρ) a (hNoMark ρ a ha) ((hZ0 _ _).mp hz)
  have hRightOuter (ρ : Context) (a : ℕ) (ha : a ∈ ρ.childPositions)
      (hz : label (marks ρ) a = 2) : ∀ z ∈ marks ρ, z < a :=
    hAllLeft (marks ρ) a (hNoMark ρ a ha) ((hZ2 _ _).mp hz).2
  have hConverted (a : ℕ) (ha : a ∈ active A) (h2 : 2 ≤ C σ s a) :
      (label (marks σ) a = 0 ∧ (label (marks A) a = 0 ∨ label (marks A) a = 1)) ∨
      (label (marks σ) a = 2 ∧ (label (marks A) a = 1 ∨ label (marks A) a = 2)) := by
    have hca := ((hActive A a).mp ha).1
    have hcs := (hAKept a ha).1
    have hxA := hOldMarks σ keep s m hxMark
    rcases hZones (marks σ) a with hz | hz | hz
    · left
      refine ⟨hz, ?_⟩
      rcases hZones (marks A) a with h0 | h1 | h2A
      · exact Or.inl h0
      · exact Or.inr h1
      · have hax := hLeftOuter σ a hcs hz x hxMark
        have hxa := hRightOuter A a hca h2A x hxA
        omega
    · have hu := hInteriorUnit a hz
      omega
    · right
      refine ⟨hz, ?_⟩
      rcases hZones (marks A) a with h0 | h1 | h2A
      · have hxa := hRightOuter σ a hcs hz x hxMark
        have hax := hLeftOuter A a hca h0 x hxA
        omega
      · exact Or.inl h1
      · exact Or.inr h2A
  have hZoneOrder (a b : ℕ) (ha : a ∈ active A) (hb : b ∈ active A)
      (hz : label (marks A) a < label (marks A) b) : a < b := by
    have hca := ((hActive A a).mp ha).1
    have hcb := ((hActive A b).mp hb).1
    rcases hZones (marks A) a with ha0 | ha1 | ha2
    · rcases hZones (marks A) b with hb0 | hb1 | hb2
      · omega
      · obtain ⟨z, hzm, hzb⟩ := Finset.filter_nonempty_iff.mp ((hZ1 _ _).mp hb1).1
        have haz := hLeftOuter A a hca ha0 z hzm
        omega
      · have haz := hLeftOuter A a hca ha0 x (hOldMarks σ keep s m hxMark)
        have hzb := hRightOuter A b hcb hb2 x (hOldMarks σ keep s m hxMark)
        omega
    · rcases hZones (marks A) b with hb0 | hb1 | hb2
      · omega
      · omega
      · obtain ⟨z, hzm, haz⟩ := Finset.filter_nonempty_iff.mp ((hZ1 _ _).mp ha1).2
        have hzb := hRightOuter A b hcb hb2 z hzm
        omega
    · have hbz := hZones (marks A) b
      omega
  have hInteriorRank (a : ℕ) (ha : a ∈ active A) (h1 : label (marks A) a = 1) :
      A.leftExt s 0 a + 1 = 2 ∧ 2 + A.rightExt s 0 a = G A s - 1 := by
    obtain ⟨hl, hr⟩ := (hZ1 (marks A) a).mp h1
    obtain ⟨l, hl, hla⟩ := Finset.filter_nonempty_iff.mp hl
    obtain ⟨r, hr, har⟩ := Finset.filter_nonempty_iff.mp hr
    obtain ⟨j, hj, hlj⟩ := (hMark A l).mp hl
    obtain ⟨i, hi, hri⟩ := (hMark A r).mp hr
    have hL := hOneLeft A s j a l hj hlj hla
    have hR := hOneRight A s i a r hi hri har
    have hpos := (hActive A a).mp ha
    cases s <;> simp only [G, cupLimit, capLimit, chainExt] at hGA hL hR hpos ⊢ <;> omega
  have hClearOuter (a b : ℕ) (ha : a ∈ active A) (hb : b ∈ active A)
      (he : label (marks A) a = label (marks A) b) (hn : label (marks A) a ≠ 1) :
      ∀ j ∈ A.levelsOn s 0, ∀ z ∈ A.extPositions j, z < min a b ∨ max a b < z := by
    intro j hj z hz
    have hm := (hMark A z).mpr ⟨j, hj, hz⟩
    have hca := ((hActive A a).mp ha).1
    have hcb := ((hActive A b).mp hb).1
    rcases hZones (marks A) a with h0 | h1 | h2
    · have haz := hLeftOuter A a hca h0 z hm
      have hbz := hLeftOuter A b hcb (he.symm.trans h0) z hm
      omega
    · exact False.elim (hn h1)
    · have hza := hRightOuter A a hca h2 z hm
      have hzb := hRightOuter A b hcb (he.symm.trans h2) z hm
      omega
  let low (a : ℕ) : Prop := label (marks A) a = 0 ∨
    (label (marks σ) a = 2 ∧ label (marks A) a = 1)
  let K (e : ℕ) := (active A).filter (fun a => 2 ≤ C σ s a ∧ label (marks σ) a = e)
  let L (e : ℕ) := (K e).filter low
  let H (e : ℕ) := (K e).filter (fun a => ¬ low a)
  let lo (a : ℕ) := σ.leftExt t 0 a + 1
  let hi (a : ℕ) := G σ t - 1 - σ.rightExt t 0 a
  let endpoint (a : ℕ) := if low a then lo a else hi a
  let reserved (e : ℕ) := ((L e).image lo) ∪ ((H e).image hi)
  have hKInfo (e a : ℕ) (ha : a ∈ K e) : a ∈ active A ∧
      2 ≤ C σ s a ∧ label (marks σ) a = e ∧ (e = 0 ∨ e = 2) := by
    obtain ⟨haa, h2, he⟩ := Finset.mem_filter.mp ha
    have hh := hConverted a haa h2
    exact ⟨haa, h2, he, by rcases hh with ⟨h0, _⟩ | ⟨h2, _⟩ <;> omega⟩
  have hLowZone (e a : ℕ) (ha : a ∈ K e) (hl : low a) :
      label (marks A) a = if e = 0 then 0 else 1 := by
    obtain ⟨haa, h2, he, he0 | he2⟩ := hKInfo e a ha
    · have hh := hConverted a haa h2
      dsimp only [low] at hl
      simp only [he0, if_true]
      omega
    · have hh := hConverted a haa h2
      dsimp only [low] at hl
      simp only [he2, reduceCtorEq, if_false]
      omega
  have hHighZone (e a : ℕ) (ha : a ∈ K e) (hl : ¬ low a) :
      label (marks A) a = if e = 0 then 1 else 2 := by
    obtain ⟨haa, h2, he, he0 | he2⟩ := hKInfo e a ha
    · have hh := hConverted a haa h2
      dsimp only [low] at hl
      simp only [he0, if_true]
      omega
    · have hh := hConverted a haa h2
      dsimp only [low] at hl
      simp only [he2, reduceCtorEq, if_false]
      omega
  have hLHOrder (e a b : ℕ) (ha : a ∈ K e) (hb : b ∈ K e)
      (hl : low a) (hh : ¬ low b) : a < b := by
    apply hZoneOrder a b (hKInfo e a ha).1 (hKInfo e b hb).1
    rw [hLowZone e a ha hl, hHighZone e b hb hh]
    split_ifs <;> omega
  have hQSource (e b : ℕ) (hb : b ∈ F B e) : b ∈ F σ e := by
    obtain ⟨hba, h2, he⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨(hPartActive σ rest t n b hba).1,
      by rw [← hBC]; exact h2, by simpa only [hBM] using he⟩
  have hLowSep (e a : ℕ) (ha : a ∈ L e) : ∀ b ∈ F B e, a < b := by
    obtain ⟨haK, hal⟩ := Finset.mem_filter.mp ha
    obtain ⟨haA, ha2, hae, he0 | he2⟩ := hKInfo e a haK
    · have ha0 : label (marks A) a = 0 := by simpa only [he0, if_true] using hLowZone e a haK hal
      intro b hb
      have hba := (Finset.mem_filter.mp hb).1
      have hbr := hBRemoved b hba
      exact hLeftOuter A a ((hActive A a).mp haA).1 ha0 b (hNewMark b hbr.1 hbr.2)
    · have ha1 : label (marks A) a = 1 := by simpa only [he2, reduceCtorEq, if_false] using hLowZone e a haK hal
      have haOld2 : label (marks σ) a = 2 := hae.trans he2
      obtain ⟨w, hw, haw⟩ := Finset.filter_nonempty_iff.mp ((hZ1 (marks A) a).mp ha1).2
      have hwr : w ∈ σ.childPositions ∧ w ∉ keep := by
        rcases hPartMarks σ hpositive keep s m w hw with hold | ⟨_, hwc, hwn⟩
        · have hwa := hRightOuter σ a (hAKept a haA).1 haOld2 w hold
          omega
        · exact ⟨hwc, hwn⟩
      intro b hb
      have hba := (Finset.mem_filter.mp hb).1
      have hbr := hBRemoved b hba
      have hbOld2 : label (marks σ) b = 2 := by
        have hh := (Finset.mem_filter.mp (hQSource e b hb)).2.2
        exact hh.trans he2
      by_contra hn
      have hne := hABNe a b haA hba
      have hxb := hRightOuter σ b hbr.1 hbOld2 x hxMark
      exact hCorner true a b w x haA hbr.1 hbr.2 hwr.1 hwr.2 hxMark
        hxb (by simpa only [Rel, if_true] using (show b < a by omega)) haw
  have hHighSep (e a : ℕ) (ha : a ∈ H e) : ∀ b ∈ F B e, b < a := by
    obtain ⟨haK, hal⟩ := Finset.mem_filter.mp ha
    obtain ⟨haA, ha2, hae, he0 | he2⟩ := hKInfo e a haK
    · have ha1 : label (marks A) a = 1 := by simpa only [he0, if_true] using hHighZone e a haK hal
      have haOld0 : label (marks σ) a = 0 := hae.trans he0
      obtain ⟨w, hw, hwa⟩ := Finset.filter_nonempty_iff.mp ((hZ1 (marks A) a).mp ha1).1
      have hwr : w ∈ σ.childPositions ∧ w ∉ keep := by
        rcases hPartMarks σ hpositive keep s m w hw with hold | ⟨_, hwc, hwn⟩
        · have haw := hLeftOuter σ a (hAKept a haA).1 haOld0 w hold
          omega
        · exact ⟨hwc, hwn⟩
      intro b hb
      have hba := (Finset.mem_filter.mp hb).1
      have hbr := hBRemoved b hba
      have hbOld0 : label (marks σ) b = 0 := by
        have hh := (Finset.mem_filter.mp (hQSource e b hb)).2.2
        exact hh.trans he0
      by_contra hn
      have hne := hABNe a b haA hba
      have hbx := hLeftOuter σ b hbr.1 hbOld0 x hxMark
      exact hCorner false a b w x haA hbr.1 hbr.2 hwr.1 hwr.2 hxMark
        hbx (by simpa only [Rel, Bool.false_eq_true, if_false] using (show a < b by omega)) hwa
    · have ha2A : label (marks A) a = 2 := by simpa only [he2, reduceCtorEq, if_false] using hHighZone e a haK hal
      intro b hb
      have hba := (Finset.mem_filter.mp hb).1
      have hbr := hBRemoved b hba
      exact hRightOuter A a ((hActive A a).mp haA).1 ha2A b (hNewMark b hbr.1 hbr.2)
  have hWitness (e a : ℕ) (ha : a ∈ K e) : a ∈ F σ e ∧ a ∉ rest := by
    obtain ⟨haa, ha2, he, _⟩ := hKInfo e a ha
    have hh := hPartActive σ keep s m a haa
    exact ⟨Finset.mem_filter.mpr ⟨hh.1, ha2, he⟩, by simp [rest, hh.2]⟩
  have hReserve (e : ℕ) : reserved e ⊆ RN σ e ∧ RN B e ⊆ RN σ e \ reserved e ∧
      (RN B e).card + (reserved e).card ≤ (RN σ e).card := by
    have hh := ctx_part_tracked_rank_reservation σ hpositive t rest n (F σ e) (F B e) (L e) (H e)
      (fun a ha => (hActive σ a).mp (Finset.mem_filter.mp ha).1)
      (fun a ha => (hActive B a).mp (Finset.mem_filter.mp ha).1)
      (fun a ha => hQSource e a ha)
      (fun a ha => hWitness e a (Finset.mem_filter.mp ha).1)
      (fun a ha => hWitness e a (Finset.mem_filter.mp ha).1)
      (fun a ha => hLowSep e a ha) (fun a ha => hHighSep e a ha)
    exact ⟨hh.1, hh.2.1, hh.2.2.1⟩
  have hBColors : colors B ⊆ colors σ := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨haa, hau⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
      ⟨(hPartActive σ rest t n a haa).1, by rw [← hBC]; exact hau⟩, by rw [hBM]⟩
  have hFreeUnit (a : ℕ) (ha : a ∈ active A) (hu : C σ s a ≤ 1) :
      label (marks σ) a ∈ colors σ \ colors B := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨(hPartActive σ keep s m a ha).1, hu⟩, rfl⟩, ?_⟩
    intro hb
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hb
    have hbr := hBRemoved b (Finset.mem_filter.mp hb).1
    apply hExcludeSame σ hpositive hglobalPlain keep m a b hu ha hbr.1 hbr.2
    simpa only [hBM] using he.symm
  have hBounds (a : ℕ) (ha : a ∈ active A) : lo a ≤ hi a := by
    have hh := (hActive σ a).mp (hPartActive σ keep s m a ha).1
    cases t <;> simp only [lo, hi, G, cupLimit, capLimit, chainExt] at hh ⊢ <;> omega
  have hLoMono (a b : ℕ) (hab : a ≤ b) : lo a ≤ lo b := by
    exact Nat.add_le_add_right (hLeftMono σ t 0 a b hab) 1
  have hHiMono (a b : ℕ) (hab : a ≤ b) : hi a ≤ hi b :=
    Nat.sub_le_sub_left (hRightMono σ t 0 a b hab) (G σ t - 1)
  let color (a : ℕ) : ℕ := if C σ s a ≤ 1 then label (marks σ) a else
    3 + 2 * endpoint a + (if label (marks σ) a = 0 then 0 else 1)
  have hColorUnit (a : ℕ) (hu : C σ s a ≤ 1) : color a = label (marks σ) a := by
    simp only [color, hu, if_true]
  have hColorNonunit (a : ℕ) (h2 : 2 ≤ C σ s a) :
      color a = 3 + 2 * endpoint a + (if label (marks σ) a = 0 then 0 else 1) := by
    have hn : ¬ C σ s a ≤ 1 := by omega
    simp only [color, hn, if_false]
  have hColorUnitIff (a : ℕ) (ha : a ∈ active A) : color a ≤ 2 ↔ C σ s a ≤ 1 := by
    by_cases hu : C σ s a ≤ 1
    · rw [hColorUnit a hu]
      have hz := hZones (marks σ) a
      omega
    · have h2 : 2 ≤ C σ s a := by omega
      rw [hColorNonunit a h2]
      omega
  have hSameToken (a b : ℕ) (ha : a ∈ active A) (hb : b ∈ active A)
      (ha2 : 2 ≤ C σ s a) (he : color a = color b) :
      2 ≤ C σ s b ∧ label (marks σ) a = label (marks σ) b ∧ endpoint a = endpoint b := by
    have hb2 : 2 ≤ C σ s b := by
      by_contra hn
      have hb1 : C σ s b ≤ 1 := by omega
      have hcb := (hColorUnitIff b hb).mpr hb1
      have hca := (hColorUnitIff a ha).mp (by omega)
      omega
    have hca := hConverted a ha ha2
    have hcb := hConverted b hb hb2
    rw [hColorNonunit a ha2, hColorNonunit b hb2] at he
    refine ⟨hb2, ?_⟩
    rcases hca with ⟨haZ, _⟩ | ⟨haZ, _⟩ <;>
      rcases hcb with ⟨hbZ, _⟩ | ⟨hbZ, _⟩ <;>
      simp only [haZ, hbZ, reduceCtorEq, if_true, if_false] at he <;> omega
  have hEndpointDecode (a : ℕ) (h2 : 2 ≤ C σ s a) : endpoint a = (color a - 3) / 2 := by
    rw [hColorNonunit a h2]
    split_ifs <;> omega
  let Collision (z : ℕ) : Prop := ∃ a ∈ active A, ∃ b ∈ active A,
    2 ≤ C σ s a ∧ 2 ≤ C σ s b ∧ color a = z ∧ color b = z ∧ low a ∧ ¬ low b
  have hCollisionData (z a : ℕ) (hz : Collision z) (ha : a ∈ active A) (hc : color a = z) :
      2 ≤ C σ s a ∧ lo a = (z - 3) / 2 ∧ hi a = (z - 3) / 2 := by
    obtain ⟨l, hl, h, hh, hl2, hh2, hlc, hhc, hll, hhh⟩ := hz
    have hla := hSameToken l a hl ha hl2 (hlc.trans hc.symm)
    have hha := hSameToken h a hh ha hh2 (hhc.trans hc.symm)
    have hca2 := hla.1
    have hEndA : endpoint a = (z - 3) / 2 := by rw [hEndpointDecode a hca2, hc]
    have haK : a ∈ K (label (marks σ) a) := Finset.mem_filter.mpr ⟨ha, hca2, rfl⟩
    have hlK : l ∈ K (label (marks σ) a) := Finset.mem_filter.mpr ⟨hl, hl2, hla.2.1⟩
    have hhK : h ∈ K (label (marks σ) a) := Finset.mem_filter.mpr ⟨hh, hh2, hha.2.1⟩
    have hbound := hBounds a ha
    by_cases hal : low a
    · have heLo : lo a = (z - 3) / 2 := by simpa only [endpoint, hal, if_true] using hEndA
      have heHi : hi h = (z - 3) / 2 := by
        have he := hha.2.2.trans hEndA
        simpa only [endpoint, hhh, if_false] using he
      have hmono := hHiMono a h (Nat.le_of_lt (hLHOrder _ a h haK hhK hal hhh))
      exact ⟨hca2, heLo, by omega⟩
    · have heHi : hi a = (z - 3) / 2 := by simpa only [endpoint, hal, if_false] using hEndA
      have heLo : lo l = (z - 3) / 2 := by
        have he := hla.2.2.trans hEndA
        simpa only [endpoint, hll, if_true] using he
      have hmono := hLoMono l a (Nat.le_of_lt (hLHOrder _ l a hlK haK hll hal))
      exact ⟨hca2, by omega, heHi⟩
  have hCollisionRank (z a : ℕ) (hz : Collision z) (ha : a ∈ active A) (hc : color a = z) :
      A.leftExt t 0 a + 1 = (z - 3) / 2 ∧
        (z - 3) / 2 + A.rightExt t 0 a = G A t - 1 := by
    obtain ⟨_, hlo, hhi⟩ := hCollisionData z a hz ha hc
    have hbound := hBounds a ha
    dsimp only [lo, hi] at hlo hhi hbound
    rw [(hPureA a).1, (hPureA a).2, hGAT]
    constructor
    · exact hlo
    · omega
  have hNoCollisionZone (z a b : ℕ) (hz : ¬ Collision z)
      (ha : a ∈ active A) (hb : b ∈ active A) (hac : color a = z) (hbc : color b = z) :
      label (marks A) a = label (marks A) b := by
    by_cases hua : C σ s a ≤ 1
    · have hca := (hColorUnitIff a ha).mpr hua
      have hub : C σ s b ≤ 1 := (hColorUnitIff b hb).mp (by omega)
      rw [hPartLabel σ hpositive keep s m a hua ha, hPartLabel σ hpositive keep s m b hub hb]
      have he := hac.trans hbc.symm
      rwa [hColorUnit a hua, hColorUnit b hub] at he
    · have ha2 : 2 ≤ C σ s a := by omega
      obtain ⟨hb2, he, _⟩ := hSameToken a b ha hb ha2 (hac.trans hbc.symm)
      have haK : a ∈ K (label (marks σ) a) := Finset.mem_filter.mpr ⟨ha, ha2, rfl⟩
      have hbK : b ∈ K (label (marks σ) a) := Finset.mem_filter.mpr ⟨hb, hb2, he.symm⟩
      by_cases hal : low a
      · by_cases hbl : low b
        · rw [hLowZone _ a haK hal, hLowZone _ b hbK hbl]
        · exact False.elim (hz ⟨a, ha, b, hb, ha2, hb2, hac, hbc, hal, hbl⟩)
      · by_cases hbl : low b
        · exact False.elim (hz ⟨b, hb, a, ha, hb2, ha2, hbc, hac, hbl, hal⟩)
        · rw [hHighZone _ a haK hal, hHighZone _ b hbK hbl]
  let Interior (z : ℕ) : Prop := ∃ a ∈ active A, color a = z ∧ label (marks A) a = 1
  let axis (z : ℕ) := if Collision z then t else s
  let rankMode (z : ℕ) := decide (Collision z ∨ Interior z)
  let rank (z : ℕ) := if Collision z then (z - 3) / 2 else 2
  have hAssignedUnit (a : ℕ) (ha : a ∈ active A) : C A (axis (color a)) a ≤ 1 := by
    by_cases hc : Collision (color a)
    · have hh := hCollisionRank (color a) a hc ha rfl
      have hax : axis (color a) = t := if_pos hc
      rw [hax]
      cases t <;> simp only [C, G, cupLimit, capLimit, chainExt] at hh ⊢ <;> omega
    · have hax : axis (color a) = s := if_neg hc
      rw [hax]
      exact hUnitA a ha
  have hAssignedClear (a b : ℕ) (ha : a ∈ active A) (hb : b ∈ active A)
      (he : color a = color b) (hm : rankMode (color a) = false) :
      ∀ j ∈ A.levelsOn (axis (color a)) 0, ∀ z ∈ A.extPositions j,
        z < min a b ∨ max a b < z := by
    have hn : ¬ (Collision (color a) ∨ Interior (color a)) := by simpa only [rankMode, decide_eq_false_iff_not] using hm
    have hc : ¬ Collision (color a) := fun hh => hn (Or.inl hh)
    have hi : ¬ Interior (color a) := fun hh => hn (Or.inr hh)
    have hz := hNoCollisionZone (color a) a b hc ha hb rfl he.symm
    have ha1 : label (marks A) a ≠ 1 := fun hh => hi ⟨a, ha, rfl, hh⟩
    simpa only [axis, hc, if_false] using hClearOuter a b ha hb hz ha1
  have hAssignedRank (a : ℕ) (ha : a ∈ active A) (hm : rankMode (color a) = true) :
      A.leftExt (axis (color a)) 0 a + 1 = rank (color a) ∧
        rank (color a) + A.rightExt (axis (color a)) 0 a = G A (axis (color a)) - 1 := by
    by_cases hc : Collision (color a)
    · have hax : axis (color a) = t := if_pos hc
      have hrk : rank (color a) = (color a - 3) / 2 := if_pos hc
      rw [hax, hrk]
      exact hCollisionRank (color a) a hc ha rfl
    · have hi : Interior (color a) := by
        have hh : Collision (color a) ∨ Interior (color a) := by simpa only [rankMode, decide_eq_true_eq] using hm
        exact hh.resolve_left hc
      obtain ⟨b, hb, hbc, hb1⟩ := hi
      have hz := hNoCollisionZone (color a) a b hc ha hb rfl hbc
      have ha1 : label (marks A) a = 1 := hz.trans hb1
      have hax : axis (color a) = s := if_neg hc
      have hrk : rank (color a) = 2 := if_neg hc
      rw [hax, hrk]
      exact hInteriorRank a ha ha1
  have hCover := ctx_mixed_clear_or_singleton_rank_cover_potential A (hPosPart keep s m)
    color axis rankMode rank
    (by
      intro a ha hl hu
      have hh := hAssignedUnit a ((hActive A a).mpr ⟨ha, hl, hu⟩)
      cases he : axis (color a) <;> simpa only [he, C] using hh)
    (by
      intro a ha b hb hal hau hbl hbu he hm
      exact hAssignedClear a b ((hActive A a).mpr ⟨ha, hal, hau⟩)
        ((hActive A b).mpr ⟨hb, hbl, hbu⟩) he hm)
    (by
      intro a ha hl hu hm
      exact hAssignedRank a ((hActive A a).mpr ⟨ha, hl, hu⟩) hm)
  let Free := colors σ \ colors B
  let cover := (Free ∪ ((reserved 0).image (fun r => 3 + 2 * r))) ∪
    ((reserved 2).image (fun r => 4 + 2 * r))
  have hColorCover : (active A).image color ⊆ cover := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    by_cases hu : C σ s a ≤ 1
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      rw [hColorUnit a hu]
      exact hFreeUnit a ha hu
    · have ha2 : 2 ≤ C σ s a := by omega
      have haK : a ∈ K (label (marks σ) a) := Finset.mem_filter.mpr ⟨ha, ha2, rfl⟩
      have he : endpoint a ∈ reserved (label (marks σ) a) := by
        by_cases hl : low a
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
            ⟨a, Finset.mem_filter.mpr ⟨haK, hl⟩, by simp only [endpoint, hl, if_true]⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
            ⟨a, Finset.mem_filter.mpr ⟨haK, hl⟩, by simp only [endpoint, hl, if_false]⟩))
      rcases hConverted a ha ha2 with ⟨h0, _⟩ | ⟨h2, _⟩
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_image.mpr ⟨endpoint a, by simpa only [h0] using he,
          by rw [hColorNonunit a ha2]; simp only [h0, if_true, Nat.add_zero]⟩
      · apply Finset.mem_union.mpr
        right
        exact Finset.mem_image.mpr ⟨endpoint a, by simpa only [h2] using he,
          by rw [hColorNonunit a ha2]; simp only [h2, reduceCtorEq, if_false]; omega⟩
  have hColorCard : ((active A).image color).card ≤ Free.card + (reserved 0).card + (reserved 2).card := by
    have h0 := Finset.card_le_card hColorCover
    have h1 := Finset.card_union_le Free ((reserved 0).image (fun r => 3 + 2 * r))
    have h2 := Finset.card_union_le (Free ∪ ((reserved 0).image (fun r => 3 + 2 * r)))
      ((reserved 2).image (fun r => 4 + 2 * r))
    have h3 := Finset.card_image_le (s := reserved 0) (f := fun r => 3 + 2 * r)
    have h4 := Finset.card_image_le (s := reserved 2) (f := fun r => 4 + 2 * r)
    dsimp only [cover] at h0
    omega
  have hFreeCard : Free.card + (colors B).card = (colors σ).card := by
    have hb := Finset.card_le_card hBColors
    change (colors σ \ colors B).card + (colors B).card = (colors σ).card
    exact Finset.card_sdiff_add_card_eq_card hBColors
  have hCharge : ((active A).image color).card + T B ≤ T σ := by
    have h0 := (hReserve 0).2.2
    have h2 := (hReserve 2).2.2
    dsimp only [T]
    omega
  have hAll : ∀ fuel, boundFuel fuel A + T B ≤ T σ := by
    intro fuel
    have hh := hCover.1 fuel
    change boundFuel fuel A ≤ ((active A).image color).card at hh
    omega
  exact ⟨hAll, hAll _⟩

end ErdosSzekeres
