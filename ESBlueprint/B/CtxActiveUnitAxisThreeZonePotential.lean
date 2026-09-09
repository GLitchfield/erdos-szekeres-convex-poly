import ESBlueprint.B.CtxUnitAxisRegionPotentialAdditive

import ESBlueprint.B.CtxBracketedChildrenUnitBound

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

/-- Three-zone potential for active unit-capacity children when the chosen global parameter is at most four. The left exterior, the entire indexed-marker interior and the right exterior each contribute at most one, so every fuel approximation and the full recursive bound are bounded by the occupied active-zone count and hence by three. The zone potential is additive across arbitrary disjoint kept sets, first on the chosen axis and second on either axis, with arbitrary maxima and no covering requirement. Unit capacity is assumed only at active children. Clear-interval capacity drop handles exterior zones and bracketed-child annihilation merges all interior gaps. Supplies the compressed unit contribution in the singleton-end sandwich rank estimate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_active_unit_axis_three_zone_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s : Ctx.Side)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (hunit : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p) ≤ 1) :
  let zones := fun (ρ : Ctx.Context) =>
    let markers : Finset ℕ := (ρ.levelsOn s 0).toFinset.biUnion
      (fun j => (ρ.extPositions j).toFinset)
    let active : Finset ℕ := ρ.childPositions.toFinset.filter
      (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    (active.image (fun p =>
      if (markers.filter (· < p)).Nonempty then
        if (markers.filter (p < ·)).Nonempty then (1 : ℕ) else 2
      else 0)).card
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ zones σ) ∧
    σ.bound ≤ zones σ ∧ zones σ ≤ 3 ∧
    (∀ (keep rest : List ℕ) (t : Ctx.Side) (m n : ℕ),
      (∀ p ∈ σ.childPositions, p ∈ keep → p ∉ rest) →
      zones (σ.part keep s m) + zones (σ.part rest t n) ≤ zones σ) := by
  classical
  dsimp only
  let lim (ρ : Context) (p : ℕ) := match s with
    | Side.lower => ρ.cupLimit p p
    | Side.upper => ρ.capLimit p p
  let marks (ρ : Context) : Finset ℕ :=
    (ρ.levelsOn s 0).toFinset.biUnion (fun l => (ρ.extPositions l).toFinset)
  let label (M : Finset ℕ) (p : ℕ) : ℕ :=
    if (M.filter (· < p)).Nonempty then
      if (M.filter (p < ·)).Nonempty then 1 else 2
    else 0
  let active (ρ : Context) : Finset ℕ := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let ν (ρ : Context) := ((active ρ).image (label (marks ρ))).card
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
  have hExcludeClear (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (hUnit : ∀ p ∈ active ρ, lim ρ p ≤ 1)
      (keep : List ℕ) (m p r : ℕ) (hp : p ∈ active (ρ.part keep s m))
      (hr : r ∈ ρ.childPositions) (hremoved : r ∉ keep)
      (hclear : ∀ l ∈ ρ.levelsOn s 0, ∀ x ∈ ρ.extPositions l,
        x < min p r ∨ max p r < x) : False := by
    have hpa := hPartActive ρ keep s m p hp
    have hpc := ((hActive ρ p).mp hpa.1).1
    have hd := (ctx_part_capacity_drop_in_clear_interval ρ hPos keep s m p r
      hpc hpa.2 hr hremoved hclear).2.2
    have hu := hUnit p hpa.1
    have hpp := (hActive _ _).mp hp
    cases s <;> dsimp [lim] at hu hd <;> omega
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
      (hUnit : ∀ p ∈ active ρ, lim ρ p ≤ 1)
      (keep : List ℕ) (t : Side) (m p : ℕ)
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
          apply hExcludeClear ρ hPos hUnit keep m p x hp hxchild hxremoved
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
          apply hExcludeClear ρ hPos hUnit keep m p x hp hxchild hxremoved
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
      (hUnit : ∀ p ∈ active ρ, lim ρ p ≤ 1)
      (keep : List ℕ) (m p r : ℕ) (hp : p ∈ active (ρ.part keep s m))
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
        apply hExcludeClear ρ hPos hUnit keep m p r hp hr hremoved
        intro j hj x hx
        have hxm := (hMark ρ x).mpr ⟨j, hj, hx⟩
        have hxp := hAllLeft (marks ρ) p hnp hpR x hxm
        have hxr := hAllLeft (marks ρ) r hnr hrBoth.2 x hxm
        left
        omega
    · have hrL := (hZ0 (marks ρ) r).mp
        (he.symm.trans ((hZ0 (marks ρ) p).mpr hpL))
      apply hExcludeClear ρ hPos hUnit keep m p r hp hr hremoved
      intro j hj x hx
      have hxm := (hMark ρ x).mpr ⟨j, hj, hx⟩
      have hpx := hAllRight (marks ρ) p hnp hpL x hxm
      have hrx := hAllRight (marks ρ) r hnr hrL x hxm
      right
      omega
  have hCut (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (hGlobal : (match s with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 4)
      (hUnit : ∀ p ∈ active ρ, lim ρ p ≤ 1)
      (keep rest : List ℕ) (t : Side) (m n : ℕ)
      (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
      ν (ρ.part keep s m) + ν (ρ.part rest t n) ≤ ν ρ := by
    let A := active (ρ.part keep s m)
    let B := active (ρ.part rest t n)
    let f := label (marks ρ)
    have hCard (ks : List ℕ) (v : Side) (m : ℕ) :
        ν (ρ.part ks v m) ≤ ((active (ρ.part ks v m)).image f).card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨p, hp, (hPartLabel ρ hPos hUnit ks v m p hp).symm⟩
    have hA : ν (ρ.part keep s m) ≤ (A.image f).card := hCard keep s m
    have hB : ν (ρ.part rest t n) ≤ (B.image f).card := hCard rest t n
    have hAB : Disjoint (A.image f) (B.image f) := by
      apply Finset.disjoint_left.mpr
      intro z hzA hzB
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hzA
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hzB
      have hqa := hPartActive ρ rest t n q hq
      have hqc := ((hActive _ _).mp hqa.1).1
      have hnot : q ∉ keep := fun hk => hdis q hqc hk hqa.2
      exact hExcludeSame ρ hPos hGlobal hUnit keep m p q hp hqc hnot hqp.symm
    have hsub : A.image f ∪ B.image f ⊆ (active ρ).image f := by
      intro z hz
      rcases Finset.mem_union.mp hz with ha | hb
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_image.mpr ⟨p, (hPartActive ρ keep s m p hp).1, rfl⟩
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
        exact Finset.mem_image.mpr ⟨p, (hPartActive ρ rest t n p hp).1, rfl⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hAB] at hcard
    exact (Nat.add_le_add hA hB).trans hcard
  have hPositivePart (ρ : Context) (keep : List ℕ) (t : Side) (m : ℕ) :
      ∀ x l u, (ρ.part keep t m).letterAt x = Letter.ext l u → 1 ≤ l := by
    intro x l u hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep t m)
        (show (ρ.part keep t m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep t m hxl he] at hx
      split at hx
      · cases hx
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep t m hxl he] at hx
      cases hx
      omega
  have hUnitPart (ρ : Context) (hUnit : ∀ p ∈ active ρ, lim ρ p ≤ 1)
      (keep : List ℕ) (t : Side) (m : ℕ) :
      ∀ p ∈ active (ρ.part keep t m), lim (ρ.part keep t m) p ≤ 1 := by
    intro p hp
    have hu := hUnit p (hPartActive ρ keep t m p hp).1
    have hle := ctx_part_limits_le ρ keep t m p p
    cases s <;> dsimp [lim] at hu ⊢ <;> omega
  have hBase (ρ : Context) (hUnit : ∀ p ∈ active ρ, lim ρ p ≤ 1) : ρ.base ≤ ν ρ := by
    rw [base_eq_baseOf]
    cases hh : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      by_cases hz : ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0
      · simp [baseOf, hz]
      have hpos : 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by omega
      have ha : p ∈ active ρ := (hActive _ _).mpr ⟨hp, hpos⟩
      have hu := hUnit p ha
      have hone : ρ.cupLimit p p = 1 ∨ ρ.capLimit p p = 1 := by
        cases s <;> dsimp [lim] at hu <;> omega
      have hn : ((active ρ).image (label (marks ρ))).Nonempty :=
        ⟨label (marks ρ) p, Finset.mem_image.mpr ⟨p, ha, rfl⟩⟩
      simpa only [baseOf, if_neg hz, if_pos hone] using Finset.card_pos.mpr hn
  have hCutLR (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (hGlobal : (match s with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 4)
      (hUnit : ∀ p ∈ active ρ, lim ρ p ≤ 1)
      (keep rest : List ℕ) (m n : ℕ)
      (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
      ν (ρ.part keep Side.lower m) + ν (ρ.part rest Side.upper n) ≤ ν ρ := by
    cases hs : s with
    | lower => simpa only [hs] using hCut ρ hPos hGlobal hUnit keep rest Side.upper m n hdis
    | upper =>
      have hrev : ∀ p ∈ ρ.childPositions, p ∈ rest → p ∉ keep := by
        intro p hp hr hk
        exact hdis p hp hk hr
      simpa only [hs, Nat.add_comm] using hCut ρ hPos hGlobal hUnit rest keep Side.lower n m hrev
  have hFuel : ∀ fuel (ρ : Context),
      (∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l) →
      (match s with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 4 →
      (∀ p ∈ active ρ, lim ρ p ≤ 1) → boundFuel fuel ρ ≤ ν ρ := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hPos hGlobal hUnit
      rw [boundFuel]
      split
      · exact hBase ρ hUnit
      · apply Ctx.getD_max?_le
        intro z hz
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hz
        obtain ⟨keep, _, d, _, hz⟩ := hz
        have hparts (keep : List ℕ) (t : Side) (m : ℕ) :
            boundFuel fuel (ρ.part keep t m) ≤ ν (ρ.part keep t m) :=
          ih _ (hPositivePart ρ keep t m) hGlobal (hUnitPart ρ hUnit keep t m)
        rcases hz with rfl | rfl
        · apply (Nat.add_le_add (hparts _ _ _) (hparts _ _ _)).trans
          apply hCutLR ρ hPos hGlobal hUnit
          intro p _ hp hr
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hr).2
          exact hn hp
        · apply (Nat.add_le_add (hparts _ _ _) (hparts _ _ _)).trans
          rw [Nat.add_comm]
          apply hCutLR ρ hPos hGlobal hUnit
          intro p _ hp hk
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hp).2
          exact hn hk
  have hCard (ρ : Context) : ν ρ ≤ 3 := by
    have hsub : (active ρ).image (label (marks ρ)) ⊆ Finset.range 3 := by
      intro z hz
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
      simp only [Finset.mem_range, label]
      split_ifs <;> decide
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hOurUnit : ∀ p ∈ active σ, lim σ p ≤ 1 := by
    intro p hp
    obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
    exact hunit p hc hcup hcap
  change (∀ fuel, boundFuel fuel σ ≤ ν σ) ∧ σ.bound ≤ ν σ ∧ ν σ ≤ 3 ∧
    (∀ (keep rest : List ℕ) (t : Side) (m n : ℕ),
      (∀ p ∈ σ.childPositions, p ∈ keep → p ∉ rest) →
      ν (σ.part keep s m) + ν (σ.part rest t n) ≤ ν σ)
  exact ⟨fun fuel => hFuel fuel σ hpositive hglobal hOurUnit,
    hFuel _ σ hpositive hglobal hOurUnit, hCard σ,
    fun keep rest t m n hdis => hCut σ hpositive hglobal hOurUnit keep rest t m n hdis⟩

end ErdosSzekeres
