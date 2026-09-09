import ESBlueprint.B.CtxUniformRankUnitPartExteriorCharge

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Strict doubled-rank charge for a chosen-unit retained part with arbitrary mixed source capacities and opposite rank intervals. Under positive labels, chosen global at most four, an actual indexed chosen marker, a retained child and an active companion, the retained occupied unit-zone count plus the minimum of the companion raw exterior potential and its doubled-rank-minus-one budget is at most twice the source active opposite-rank-union cardinality minus one. The same inequality holds for every retained fuel approximation and its full bound. Arbitrary older histories, maxima, disconnected rank unions and inactive children are allowed. Outer retained zones reserve global companion ranks; a retained middle zone excludes companion middle children and charges the two exteriors separately. Supplies the remaining chosen-unit cut step for the full one-level refined potential toward the singleton-end sandwich obstruction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_unit_part_refined_exterior_charge (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hq : q ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions)
  (hqcup : 0 < (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit q q)
  (hqcap : 0 < (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit q q)
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
  let ranks := fun (ρ : Ctx.Context) => (active ρ).biUnion (rankInterval ρ)
  let potential := fun (ρ : Ctx.Context) =>
    min (unitZones ρ + (exteriorRanks ρ 0).card + (exteriorRanks ρ 2).card)
      (2 * (ranks ρ).card - 1)
  let ownPart := σ.part keep s m
  let otherPart := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  let sourceRanks := ranks σ
  let budget := 2 * sourceRanks.card - 1
  unitZones ownPart + potential otherPart ≤ budget ∧
    (∀ fuel, Ctx.Context.boundFuel fuel ownPart + potential otherPart ≤ budget) ∧
    ownPart.bound + potential otherPart ≤ budget := by
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
  let ranks (ρ : Context) := (active ρ).biUnion (I ρ)
  let S := ranks σ
  let Q := min (T B) (2 * (ranks B).card - 1)
  let lo (r : ℕ) := σ.leftExt t 0 r + 1
  let hi (r : ℕ) := G σ t - 1 - σ.rightExt t 0 r
  change (colors A).card + Q ≤ 2 * S.card - 1 ∧
    (∀ fuel, boundFuel fuel A + Q ≤ 2 * S.card - 1) ∧
    A.bound + Q ≤ 2 * S.card - 1
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
  have hG : G σ s ≤ 4 := hglobal
  have hGA : G A s ≤ 4 := hG
  have hglobalPlain : (match s with | Side.lower => σ.u | Side.upper => σ.a) ≤ 4 := by
    cases s <;> simpa only [G] using hG
  have hpSource := (hChild keep s m p).mp hp
  have hqRest := (hChild rest t n q).mp hq
  have hqChild := hqRest.1
  have hqRemoved : q ∉ keep := of_decide_eq_true (List.mem_filter.mp hqRest.2).2
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
  have hLabels (M : Finset ℕ) (r : ℕ) :
      label M r = 0 ∨ label M r = 1 ∨ label M r = 2 := by
    simp only [label]
    split_ifs <;> simp
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
  have hOld0 (r : ℕ) (hr : r ∈ σ.childPositions) (he : label (marks σ) r = 0) :
      ∀ z ∈ marks σ, r < z := hAllRight _ _ (hNoMark σ r hr) ((hZ0 _ _).mp he)
  have hOld2 (r : ℕ) (hr : r ∈ σ.childPositions) (he : label (marks σ) r = 2) :
      ∀ z ∈ marks σ, z < r := hAllLeft _ _ (hNoMark σ r hr) ((hZ2 _ _).mp he).2
  have hNew0 (a r : ℕ) (ha : a ∈ active A)
      (hr : r ∈ σ.childPositions) (hrn : r ∉ keep) (he : label (marks A) a = 0) :
      a < r := hAllRight _ _ (hNoMark A a ((hActive A a).mp ha).1)
        ((hZ0 _ _).mp he) r (hNewMark r hr hrn)
  have hNew2 (a r : ℕ) (ha : a ∈ active A)
      (hr : r ∈ σ.childPositions) (hrn : r ∉ keep) (he : label (marks A) a = 2) :
      r < a := hAllLeft _ _ (hNoMark A a ((hActive A a).mp ha).1)
        ((hZ2 _ _).mp he).2 r (hNewMark r hr hrn)
  have hMiddle0 (a r : ℕ) (ha : a ∈ active A)
      (hr : r ∈ σ.childPositions) (hrn : r ∉ keep)
      (ha1 : label (marks A) a = 1) (hr0 : label (marks σ) r = 0) : r < a := by
    obtain ⟨w, hw, hwa⟩ := Finset.filter_nonempty_iff.mp ((hZ1 _ _).mp ha1).1
    rcases hPartMarks σ hpositive keep s m w hw with hold | ⟨_, hwc, hwn⟩
    · have hrw := hOld0 r hr hr0 w hold
      omega
    · by_contra hn
      have hneq : a ≠ r := by intro he; exact hrn (he ▸ (hAKept a ha).2)
      exact hCorner false a r w x ha hr hrn hwc hwn hxMark
        (hOld0 r hr hr0 x hxMark) (by dsimp [Rel]; omega) hwa
  have hMiddle2 (a r : ℕ) (ha : a ∈ active A)
      (hr : r ∈ σ.childPositions) (hrn : r ∉ keep)
      (ha1 : label (marks A) a = 1) (hr2 : label (marks σ) r = 2) : a < r := by
    obtain ⟨w, hw, haw⟩ := Finset.filter_nonempty_iff.mp ((hZ1 _ _).mp ha1).2
    rcases hPartMarks σ hpositive keep s m w hw with hold | ⟨_, hwc, hwn⟩
    · have hwr := hOld2 r hr hr2 w hold
      omega
    · by_contra hn
      have hneq : a ≠ r := by intro he; exact hrn (he ▸ (hAKept a ha).2)
      exact hCorner true a r w x ha hr hrn hwc hwn hxMark
        (hOld2 r hr hr2 x hxMark) (by dsimp [Rel]; omega) haw
  have hBracket (a r z w : ℕ) (ha : a ∈ active A)
      (hr : r ∈ σ.childPositions) (hrn : r ∉ keep)
      (hz : z ∈ marks σ) (hw : w ∈ marks σ)
      (hza : z < a) (hzr : z < r) (haw : a < w) (hrw : r < w) : False := by
    obtain ⟨j, hj, hzj⟩ := (hMark σ z).mp hz
    obtain ⟨i, hi, hwi⟩ := (hMark σ w).mp hw
    have hh := (ctx_bracketed_children_unit_bound σ hpositive s j i z w
      (List.mem_filter.mp hj).1 (List.mem_filter.mp hi).1
      (by simpa using (List.mem_filter.mp hj).2)
      (by simpa using (List.mem_filter.mp hi).2) hzj hwi hglobalPlain).1
      keep m r hr hrn hzr hrw a ((hActive A a).mp ha).1 hza haw
    have hpos := (hActive A a).mp ha
    cases s <;> simp only [A] at hpos hh <;> omega
  have hMiddleNot1 (a r : ℕ) (ha : a ∈ active A)
      (hr : r ∈ σ.childPositions) (hrn : r ∉ keep)
      (ha1 : label (marks A) a = 1) : label (marks σ) r ≠ 1 := by
    intro hr1
    have hneq : a ≠ r := by intro he; exact hrn (he ▸ (hAKept a ha).2)
    rcases lt_or_gt_of_ne hneq with har | hra
    · obtain ⟨z, hz, hrz⟩ := Finset.filter_nonempty_iff.mp ((hZ1 _ _).mp hr1).2
      obtain ⟨w, hw, hwa⟩ := Finset.filter_nonempty_iff.mp ((hZ1 _ _).mp ha1).1
      rcases hPartMarks σ hpositive keep s m w hw with hold | ⟨_, hwc, hwn⟩
      · exact hBracket a r w z ha hr hrn hold hz hwa (by omega) (by omega) hrz
      · exact hCorner false a r w z ha hr hrn hwc hwn hz hrz har hwa
    · obtain ⟨z, hz, hzr⟩ := Finset.filter_nonempty_iff.mp ((hZ1 _ _).mp hr1).1
      obtain ⟨w, hw, haw⟩ := Finset.filter_nonempty_iff.mp ((hZ1 _ _).mp ha1).2
      rcases hPartMarks σ hpositive keep s m w hw with hold | ⟨_, hwc, hwn⟩
      · exact hBracket a r z w ha hr hrn hz hold (by omega) hzr haw (by omega)
      · exact hCorner true a r w z ha hr hrn hwc hwn hz hzr hra haw
  have hReserve (H D E : Finset ℕ) (hH : H ⊆ active B)
      (hD : D ⊆ active A) (hE : E ⊆ active A)
      (hL : ∀ a ∈ D, ∀ b ∈ H, a < b)
      (hR : ∀ a ∈ E, ∀ b ∈ H, b < a) :
      (H.biUnion (I B)).card + ((D.image lo) ∪ (E.image hi)).card ≤ S.card ∧
      ((∃ a ∈ D, ∃ b ∈ E, hi b ≤ lo a) → H = ∅) := by
    have hh := ctx_part_tracked_rank_reservation σ hpositive t rest n (active σ) H D E
      (fun r hr => (hActive σ r).mp hr)
      (fun r hr => (hActive B r).mp (hH hr))
      (fun r hr => (hPartActive σ rest t n r (hH hr)).1)
      (fun r hr => ⟨(hPartActive σ keep s m r (hD hr)).1,
        by simp [rest, (hAKept r (hD hr)).2]⟩)
      (fun r hr => ⟨(hPartActive σ keep s m r (hE hr)).1,
        by simp [rest, (hAKept r (hE hr)).2]⟩) hL hR
    exact ⟨hh.2.2.1, hh.2.2.2⟩
  have hEmpty : (∅ : Finset ℕ) ⊆ active A := Finset.empty_subset _
  have hSingle (a : ℕ) (ha : a ∈ active A) : ({a} : Finset ℕ) ⊆ active A := by
    simpa using ha
  have hqActive : q ∈ active B := (hActive B q).mpr ⟨hq, hqcup, hqcap⟩
  have hRankPos (ρ : Context) (r : ℕ) (hr : r ∈ active ρ) : 1 ≤ (I ρ r).card := by
    have hpos := (hActive ρ r).mp hr
    have hends : ρ.leftExt t 0 r + 1 ≤ G ρ t - 1 - ρ.rightExt t 0 r := by
      cases t <;> simp only [G, cupLimit, capLimit, chainExt] at hpos ⊢ <;> omega
    exact Finset.card_pos.mpr ⟨ρ.leftExt t 0 r + 1, Finset.mem_Icc.mpr ⟨le_rfl, hends⟩⟩
  have hRBpos : 1 ≤ (ranks B).card := by
    have hs : I B q ⊆ ranks B := fun k hk => Finset.mem_biUnion.mpr ⟨q, hqActive, hk⟩
    exact (hRankPos B q hqActive).trans (Finset.card_le_card hs)
  have hRBle : (ranks B).card ≤ S.card := by
    have hh := (hReserve (active B) ∅ ∅ (Finset.Subset.refl _) hEmpty hEmpty
      (by simp) (by simp)).1
    simpa only [Finset.image_empty, Finset.union_empty, Finset.card_empty, Nat.add_zero] using hh
  have hP (a : ℕ) (ha : a ∈ active A) : 2 ≤ S.card := by
    have hqs : ({q} : Finset ℕ) ⊆ active B := by simpa using hqActive
    have hneq := hABNe a q ha hqActive
    have hIq := hRankPos B q hqActive
    rcases lt_or_gt_of_ne hneq with hl | hr
    · have hh := (hReserve {q} {a} ∅ hqs (hSingle a ha) hEmpty
        (by intro x hx y hy; simpa only [Finset.mem_singleton.mp hx,
          Finset.mem_singleton.mp hy] using hl) (by simp)).1
      simp only [Finset.singleton_biUnion, Finset.image_singleton, Finset.image_empty,
        Finset.union_empty, Finset.card_singleton] at hh
      omega
    · have hh := (hReserve {q} ∅ {a} hqs hEmpty (hSingle a ha) (by simp)
        (by intro x hx y hy; simpa only [Finset.mem_singleton.mp hx,
          Finset.mem_singleton.mp hy] using hr)).1
      simp only [Finset.singleton_biUnion, Finset.image_singleton, Finset.image_empty,
        Finset.empty_union, Finset.card_singleton] at hh
      omega
  have hOuterUnit (e : ℕ) (he : e = 0 ∨ e = 2) (hu : e ∈ colors B) : RN B e = ∅ := by
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hu
    obtain ⟨haa, hau⟩ := Finset.mem_filter.mp ha
    have haOld : label (marks σ) a = e := by simpa only [hBM] using hae
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    obtain ⟨b, hb, _⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨hba, hb2, hbe⟩ := Finset.mem_filter.mp hb
    have hbOld : label (marks σ) b = e := by simpa only [hBM] using hbe
    have heq : C σ s a = C σ s b := by
      apply hClearEq σ s a b
      intro j hj z hz
      have hzm := (hMark σ z).mpr ⟨j, hj, hz⟩
      rcases he with rfl | rfl
      · have haz := hOld0 a (hBRemoved a haa).1 haOld z hzm
        have hbz := hOld0 b (hBRemoved b hba).1 hbOld z hzm
        right; omega
      · have hza := hOld2 a (hBRemoved a haa).1 haOld z hzm
        have hzb := hOld2 b (hBRemoved b hba).1 hbOld z hzm
        left; omega
    rw [hBC] at hau hb2
    omega
  have hMiddleCharge (a : ℕ) (ha : a ∈ active A) (ha1 : label (marks A) a = 1) :
      T B + 1 ≤ 2 * S.card - 1 := by
    have hcard := hP a ha
    have hNo1 : 1 ∉ colors B := by
      intro hc
      obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hc
      have hbr := hBRemoved b (Finset.mem_filter.mp hb).1
      exact hMiddleNot1 a b ha hbr.1 hbr.2 ha1 (by simpa only [hBM] using he)
    have hCEq : colors B = (if 0 ∈ colors B then {0} else ∅) ∪
        (if 2 ∈ colors B then {2} else ∅) := by
      ext c
      constructor
      · intro hc
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
        rcases hLabels (marks B) b with h0 | h1 | h2
        · have hm : 0 ∈ colors B := h0 ▸ hc
          simp [h0, hm]
        · exact False.elim (hNo1 (h1 ▸ hc))
        · have hm : 2 ∈ colors B := h2 ▸ hc
          simp [h2, hm]
      · intro hc
        rcases Finset.mem_union.mp hc with hc | hc
        all_goals
          split_ifs at hc with hh
          · simpa only [Finset.mem_singleton.mp hc] using hh
          · exact False.elim (Finset.notMem_empty c hc)
    have hCcard : (colors B).card = (if 0 ∈ colors B then 1 else 0) +
        (if 2 ∈ colors B then 1 else 0) := by
      by_cases h0 : 0 ∈ colors B <;> by_cases h2 : 2 ∈ colors B <;>
        simpa [h0, h2] using congrArg Finset.card hCEq
    have h0 : (RN B 0).card + 1 ≤ S.card := by
      have hh := (hReserve (F B 0) ∅ {a}
        (fun b hb => (Finset.mem_filter.mp hb).1) hEmpty (hSingle a ha) (by simp)
        (by
          intro x hx b hb
          have hxa := Finset.mem_singleton.mp hx
          subst x
          have hbr := hBRemoved b (Finset.mem_filter.mp hb).1
          exact hMiddle0 a b ha hbr.1 hbr.2 ha1
            (by simpa only [hBM] using (Finset.mem_filter.mp hb).2.2))).1
      simpa only [Finset.image_empty, Finset.image_singleton, Finset.empty_union,
        Finset.card_singleton] using hh
    have h2 : (RN B 2).card + 1 ≤ S.card := by
      have hh := (hReserve (F B 2) {a} ∅
        (fun b hb => (Finset.mem_filter.mp hb).1) (hSingle a ha) hEmpty
        (by
          intro x hx b hb
          have hxa := Finset.mem_singleton.mp hx
          subst x
          have hbr := hBRemoved b (Finset.mem_filter.mp hb).1
          exact hMiddle2 a b ha hbr.1 hbr.2 ha1
            (by simpa only [hBM] using (Finset.mem_filter.mp hb).2.2)) (by simp)).1
      simpa only [Finset.image_empty, Finset.image_singleton, Finset.union_empty,
        Finset.card_singleton] using hh
    have h0' : (if 0 ∈ colors B then 1 else 0) + (RN B 0).card + 1 ≤ S.card := by
      by_cases hh : 0 ∈ colors B
      · rw [if_pos hh, hOuterUnit 0 (Or.inl rfl) hh]
        simpa using hcard
      · simpa only [if_neg hh, Nat.zero_add] using h0
    have h2' : (if 2 ∈ colors B then 1 else 0) + (RN B 2).card + 1 ≤ S.card := by
      by_cases hh : 2 ∈ colors B
      · rw [if_pos hh, hOuterUnit 2 (Or.inr rfl) hh]
        simpa using hcard
      · simpa only [if_neg hh, Nat.zero_add] using h2
    dsimp only [T]
    rw [hCcard]
    omega
  let K := (active A).image (label (marks A))
  have hColorsA : colors A = K := by
    dsimp only [colors, K, units]
    rw [Finset.filter_true_of_mem (fun a ha => hUnitA a ha)]
  have hKLabels : ∀ c ∈ K, c = 0 ∨ c = 1 ∨ c = 2 := by
    intro c hc
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
    exact hLabels _ _
  have hK3 : K.card ≤ 3 := by
    have hs : K ⊆ {0, 1, 2} := by
      intro c hc
      rcases hKLabels c hc with rfl | rfl | rfl <;> simp
    simpa using Finset.card_le_card hs
  have hBound : (∀ fuel, boundFuel fuel A ≤ K.card) ∧ A.bound ≤ K.card := by
    have hh := ctx_active_unit_axis_three_zone_potential A (hPosPart keep s m) s
      (by cases s <;> simpa only [G] using hGA)
      (by intro a ha hl hu; exact hunit a ha hl hu)
    exact ⟨hh.1, hh.2.1⟩
  have hQL : Q ≤ T B := Nat.min_le_left _ _
  have hQR : Q ≤ 2 * (ranks B).card - 1 := Nat.min_le_right _ _
  have hCharge : K.card + Q ≤ 2 * S.card - 1 := by
    by_cases h0 : 0 ∈ K
    · obtain ⟨a, ha, ha0⟩ := Finset.mem_image.mp h0
      have hleft : ∀ b ∈ active B, a < b := by
        intro b hb
        exact hNew0 a b ha (hBRemoved b hb).1 (hBRemoved b hb).2 ha0
      by_cases h2 : 2 ∈ K
      · obtain ⟨b, hb, hb2⟩ := Finset.mem_image.mp h2
        have hright : ∀ c ∈ active B, c < b := by
          intro c hc
          exact hNew2 b c hb (hBRemoved c hc).1 (hBRemoved c hc).2 hb2
        have hh := hReserve (active B) {a} {b} (Finset.Subset.refl _)
          (hSingle a ha) (hSingle b hb)
          (by intro c hc d hd; simpa only [Finset.mem_singleton.mp hc] using hleft d hd)
          (by intro c hc d hd; simpa only [Finset.mem_singleton.mp hc] using hright d hd)
        have hneEnds : lo a ≠ hi b := by
          intro he
          have hz := hh.2 ⟨a, by simp, b, by simp, by omega⟩
          exact Finset.notMem_empty q (hz ▸ hqActive)
        have hc := hh.1
        simp only [Finset.image_singleton, Finset.singleton_union] at hc
        have hpair : ({lo a, hi b} : Finset ℕ).card = 2 := by simp [hneEnds]
        rw [hpair] at hc
        change (ranks B).card + 2 ≤ S.card at hc
        omega
      · have hk : K.card ≤ 2 := by
          have hs : K ⊆ {0, 1} := by
            intro c hc
            rcases hKLabels c hc with rfl | rfl | rfl
            · simp
            · simp
            · exact False.elim (h2 hc)
          simpa using Finset.card_le_card hs
        have hh := (hReserve (active B) {a} ∅ (Finset.Subset.refl _)
          (hSingle a ha) hEmpty
          (by intro c hc d hd; simpa only [Finset.mem_singleton.mp hc] using hleft d hd)
          (by simp)).1
        simp only [Finset.image_singleton, Finset.image_empty, Finset.union_empty,
          Finset.card_singleton] at hh
        change (ranks B).card + 1 ≤ S.card at hh
        omega
    · by_cases h2 : 2 ∈ K
      · obtain ⟨b, hb, hb2⟩ := Finset.mem_image.mp h2
        have hk : K.card ≤ 2 := by
          have hs : K ⊆ {1, 2} := by
            intro c hc
            rcases hKLabels c hc with rfl | rfl | rfl
            · exact False.elim (h0 hc)
            · simp
            · simp
          simpa using Finset.card_le_card hs
        have hh := (hReserve (active B) ∅ {b} (Finset.Subset.refl _) hEmpty
          (hSingle b hb) (by simp)
          (by
            intro c hc d hd
            exact hNew2 c d (hSingle b hb hc) (hBRemoved d hd).1 (hBRemoved d hd).2
              (by simpa only [Finset.mem_singleton.mp hc] using hb2))).1
        simp only [Finset.image_singleton, Finset.image_empty, Finset.empty_union,
          Finset.card_singleton] at hh
        change (ranks B).card + 1 ≤ S.card at hh
        omega
      · have hk : K ⊆ {1} := by
          intro c hc
          rcases hKLabels c hc with rfl | rfl | rfl
          · exact False.elim (h0 hc)
          · simp
          · exact False.elim (h2 hc)
        have hk1 : K.card ≤ 1 := by simpa using Finset.card_le_card hk
        by_cases h1 : 1 ∈ K
        · obtain ⟨a, ha, ha1⟩ := Finset.mem_image.mp h1
          have hh := hMiddleCharge a ha ha1
          omega
        · have hk0 : K = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro c hc
            exact h1 (Finset.mem_singleton.mp (hk hc) ▸ hc)
          have hc : K.card = 0 := by rw [hk0]; rfl
          omega
  rw [hColorsA]
  exact ⟨hCharge, fun fuel => (Nat.add_le_add_right (hBound.1 fuel) Q).trans hCharge,
    (Nat.add_le_add_right hBound.2 Q).trans hCharge⟩

end ErdosSzekeres
