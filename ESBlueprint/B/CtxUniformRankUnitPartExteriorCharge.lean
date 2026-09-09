import ESBlueprint.B.CtxUnitPartExteriorPotentialCharge
import ESBlueprint.B.CtxActiveUnitAxisThreeZonePotential

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- A strict doubled-rank charge for a unit retained part when all source children are active and chosen-nonunit and their opposite pure extension traces are uniform. With chosen global at most four, one actual indexed chosen marker, a retained source child and an active companion, the occupied retained unit-zone count plus the companion raw exterior potential is at most twice the common source rank-interval cardinality minus one. The same estimate holds for every retained-part fuel approximation and its full bound. Kept sets and new maxima are arbitrary; both source exteriors may contain arbitrarily many children. A retained point in new zone zero reserves lower endpoints in both companion exteriors; zone one reserves the upper endpoint on the left and lower endpoint on the right; zone two reserves both upper endpoints. Thus any nonempty set of occupied zones reserves at least one more exterior-tagged endpoint than its cardinality; an inactive retained part uses a kept source-active witness. Supplies the sharper unit-own cut component for uniform-rank capacity-three gap estimates toward the sandwich proof.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_uniform_rank_unit_part_exterior_charge (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4)
  (L R : ℕ)
  (hsource : ∀ r ∈ σ.childPositions, 0 < σ.cupLimit r r ∧ 0 < σ.capLimit r r ∧
    2 ≤ (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.cupLimit r r | Ctx.Side.upper => σ.capLimit r r) s)
  (htraces : ∀ r ∈ σ.childPositions,
    σ.leftExt t 0 r = L ∧ σ.rightExt t 0 r = R)
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
  let potential := fun (ρ : Ctx.Context) =>
    unitZones ρ + (exteriorRanks ρ 0).card + (exteriorRanks ρ 2).card
  let ownPart := σ.part keep s m
  let otherPart := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  let sourceRanks := Finset.Icc (L + 1) (global σ t - 1 - R)
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
  let lo := L + 1
  let hi := G σ t - 1 - R
  let S := Finset.Icc lo hi
  change (colors A).card + T B ≤ 2 * S.card - 1 ∧
    (∀ fuel, boundFuel fuel A + T B ≤ 2 * S.card - 1) ∧
    A.bound + T B ≤ 2 * S.card - 1
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
  have hExtreme (r : ℕ) (hr : r ∈ σ.childPositions) :
      label (marks σ) r = 0 ∨ label (marks σ) r = 2 := by
    rcases hLabels (marks σ) r with h0 | h1 | h2
    · exact Or.inl h0
    · have hh := hInteriorUnit r h1
      have hn : 2 ≤ C σ s r := (hsource r hr).2.2
      omega
    · exact Or.inr h2
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
      (har : label (marks A) a = 1) (hr0 : label (marks σ) r = 0) : r < a := by
    have hak := hAKept a ha
    have hneq : a ≠ r := by intro he; exact hrn (he ▸ hak.2)
    rcases hExtreme a hak.1 with ha0 | ha2
    · obtain ⟨w, hw, hwa⟩ := Finset.filter_nonempty_iff.mp ((hZ1 _ _).mp har).1
      rcases hPartMarks σ hpositive keep s m w hw with hold | ⟨_, hwc, hwn⟩
      · have haw := hOld0 a hak.1 ha0 w hold
        omega
      · by_contra h
        exact hCorner false a r w x ha hr hrn hwc hwn hxMark
          (hOld0 r hr hr0 x hxMark) (by dsimp [Rel]; omega) hwa
    · have hrx := hOld0 r hr hr0 x hxMark
      have hxa := hOld2 a hak.1 ha2 x hxMark
      omega
  have hMiddle2 (a r : ℕ) (ha : a ∈ active A)
      (hr : r ∈ σ.childPositions) (hrn : r ∉ keep)
      (har : label (marks A) a = 1) (hr2 : label (marks σ) r = 2) : a < r := by
    have hak := hAKept a ha
    have hneq : a ≠ r := by intro he; exact hrn (he ▸ hak.2)
    rcases hExtreme a hak.1 with ha0 | ha2
    · have hax := hOld0 a hak.1 ha0 x hxMark
      have hxr := hOld2 r hr hr2 x hxMark
      omega
    · obtain ⟨w, hw, haw⟩ := Finset.filter_nonempty_iff.mp ((hZ1 _ _).mp har).2
      rcases hPartMarks σ hpositive keep s m w hw with hold | ⟨_, hwc, hwn⟩
      · have hwa := hOld2 a hak.1 ha2 w hold
        omega
      · by_contra h
        exact hCorner true a r w x ha hr hrn hwc hwn hxMark
          (hOld2 r hr hr2 x hxMark) (by dsimp [Rel]; omega) haw
  have hFActive (e r : ℕ) (hr : r ∈ F B e) : r ∈ active B :=
    (Finset.mem_filter.mp hr).1
  have hFLabel (e r : ℕ) (hr : r ∈ F B e) : label (marks σ) r = e := by
    simpa only [hBM] using (Finset.mem_filter.mp hr).2.2
  have hColorsB : colors B = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨r, hr, _⟩ := Finset.mem_image.mp hc
    obtain ⟨hr, hu⟩ := Finset.mem_filter.mp hr
    have hs : 2 ≤ C σ s r := (hsource r (hBRemoved r hr).1).2.2
    rw [hBC] at hu
    omega
  have hISource (r : ℕ) (hr : r ∈ σ.childPositions) : I σ r = S := by
    obtain ⟨hl, hh⟩ := htraces r hr
    simp only [I, hl, hh, S, lo, hi]
  have hpActive : p ∈ active σ :=
    (hActive σ p).mpr ⟨hpSource.1, (hsource p hpSource.1).1, (hsource p hpSource.1).2.1⟩
  have hSourceRanks : (active σ).biUnion (I σ) = S := by
    apply Finset.Subset.antisymm
    · intro k hk
      obtain ⟨r, hr, hkr⟩ := Finset.mem_biUnion.mp hk
      simpa only [hISource r ((hActive σ r).mp hr).1] using hkr
    · intro k hk
      exact Finset.mem_biUnion.mpr ⟨p, hpActive, by simpa only [hISource p hpSource.1] using hk⟩
  have hReserve (Q D E : Finset ℕ) (hQ : Q ⊆ active B)
      (hD : ∀ r ∈ D, r ∈ σ.childPositions ∧ r ∈ keep)
      (hE : ∀ r ∈ E, r ∈ σ.childPositions ∧ r ∈ keep)
      (hL : ∀ a ∈ D, ∀ b ∈ Q, a < b)
      (hR : ∀ a ∈ E, ∀ b ∈ Q, b < a) :
      (Q.biUnion (I B)).card +
        ((D.image (fun _ => lo)) ∪ (E.image (fun _ => hi))).card ≤ S.card := by
    have hh := ctx_part_tracked_rank_reservation σ hpositive t rest n (active σ) Q D E
      (fun r hr => (hActive σ r).mp hr)
      (fun r hr => (hActive B r).mp (hQ hr))
      (fun r hr => (hPartActive σ rest t n r (hQ hr)).1)
      (fun r hr => ⟨(hActive σ r).mpr ⟨(hD r hr).1,
        (hsource r (hD r hr).1).1, (hsource r (hD r hr).1).2.1⟩,
        by simp [rest, (hD r hr).2]⟩)
      (fun r hr => ⟨(hActive σ r).mpr ⟨(hE r hr).1,
        (hsource r (hE r hr).1).1, (hsource r (hE r hr).1).2.1⟩,
        by simp [rest, (hE r hr).2]⟩) hL hR
    have hc := hh.2.2.1
    change (Q.biUnion (I B)).card +
      ((D.image (fun r => σ.leftExt t 0 r + 1)) ∪
        (E.image (fun r => G σ t - 1 - σ.rightExt t 0 r))).card ≤
      ((active σ).biUnion (I σ)).card at hc
    have hDI : D.image (fun r => σ.leftExt t 0 r + 1) = D.image (fun _ => lo) := by
      apply Finset.image_congr
      intro r hr
      simp only [(htraces r (hD r hr).1).1, lo]
    have hEI : E.image (fun r => G σ t - 1 - σ.rightExt t 0 r) = E.image (fun _ => hi) := by
      apply Finset.image_congr
      intro r hr
      simp only [(htraces r (hE r hr).1).2, hi]
    simpa only [hDI, hEI, hSourceRanks] using hc
  have hEmpty : ∀ r ∈ (∅ : Finset ℕ), r ∈ σ.childPositions ∧ r ∈ keep := by simp
  have hSingle : ∀ r ∈ ({p} : Finset ℕ), r ∈ σ.childPositions ∧ r ∈ keep := by
    intro r hr
    simpa only [Finset.mem_singleton.mp hr] using hpSource
  have hqActive : q ∈ active B := (hActive B q).mpr ⟨hq, hqcup, hqcap⟩
  have hqSubset : ({q} : Finset ℕ) ⊆ active B := by simpa using hqActive
  have hIq : 1 ≤ (I B q).card := by
    have hpos : 0 < C B t q := by cases t <;> assumption
    have hends : B.leftExt t 0 q + 1 ≤ G B t - 1 - B.rightExt t 0 q := by
      cases t <;> simp only [C, G, cupLimit, capLimit, chainExt] at hpos ⊢ <;> omega
    exact Finset.card_pos.mpr ⟨B.leftExt t 0 q + 1, Finset.mem_Icc.mpr ⟨le_rfl, hends⟩⟩
  have hP : 2 ≤ S.card := by
    have hneq : p ≠ q := by intro he; exact hqRemoved (he ▸ hpSource.2)
    rcases lt_or_gt_of_ne hneq with hl | hr
    · have hh := hReserve {q} {p} ∅ hqSubset hSingle hEmpty
        (by intro a ha b hb; simpa only [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb] using hl)
        (by simp)
      simp only [Finset.singleton_biUnion, Finset.image_singleton, Finset.image_empty,
        Finset.union_empty, Finset.card_singleton] at hh
      omega
    · have hh := hReserve {q} ∅ {p} hqSubset hEmpty hSingle (by simp)
        (by intro a ha b hb; simpa only [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb] using hr)
      simp only [Finset.singleton_biUnion, Finset.image_singleton, Finset.image_empty,
        Finset.empty_union, Finset.card_singleton] at hh
      omega
  have hlohi : lo ≠ hi := by
    have hc : S.card = hi + 1 - lo := Nat.card_Icc lo hi
    omega
  let K := (active A).image (label (marks A))
  have hColorsA : colors A = K := by
    dsimp only [colors, K, units]
    rw [Finset.filter_true_of_mem (fun a ha => hUnitA a ha)]
  have hKLabels : ∀ c ∈ K, c = 0 ∨ c = 1 ∨ c = 2 := by
    intro c hc
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
    exact hLabels _ _
  have hBound : (∀ fuel, boundFuel fuel A ≤ K.card) ∧ A.bound ≤ K.card := by
    have hh := ctx_active_unit_axis_three_zone_potential A (hPosPart keep s m) s
      (by cases s <;> simpa only [G] using hGA)
      (by intro a ha hl hu; exact hunit a ha hl hu)
    exact ⟨hh.1, hh.2.1⟩
  have hCharge : K.card + (RN B 0).card + (RN B 2).card ≤ 2 * S.card - 1 := by
    by_cases hK : K.Nonempty
    · let W (c : ℕ) := (active A).filter (fun a => label (marks A) a = c)
      have hW (c : ℕ) : (W c).Nonempty ↔ c ∈ K := by
        simp only [W, K, Finset.filter_nonempty_iff, Finset.mem_image]
      have hWK (c : ℕ) : ∀ a ∈ W c, a ∈ σ.childPositions ∧ a ∈ keep :=
        fun a ha => hAKept a (Finset.mem_filter.mp ha).1
      have hWU (c d : ℕ) : ∀ a ∈ W c ∪ W d, a ∈ σ.childPositions ∧ a ∈ keep := by
        intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact hWK c a ha
        · exact hWK d a ha
      have h0 := hReserve (F B 0) (W 0) (W 1 ∪ W 2)
        (fun r hr => hFActive 0 r hr) (hWK 0) (hWU 1 2)
        (by
          intro a ha b hb
          exact hNew0 a b (Finset.mem_filter.mp ha).1
            (hBRemoved b (hFActive 0 b hb)).1 (hBRemoved b (hFActive 0 b hb)).2
            (Finset.mem_filter.mp ha).2)
        (by
          intro a ha b hb
          have hbr := hBRemoved b (hFActive 0 b hb)
          rcases Finset.mem_union.mp ha with ha | ha
          · exact hMiddle0 a b (Finset.mem_filter.mp ha).1 hbr.1 hbr.2
              (Finset.mem_filter.mp ha).2 (hFLabel 0 b hb)
          · exact hNew2 a b (Finset.mem_filter.mp ha).1 hbr.1 hbr.2
              (Finset.mem_filter.mp ha).2)
      have h2 := hReserve (F B 2) (W 0 ∪ W 1) (W 2)
        (fun r hr => hFActive 2 r hr) (hWU 0 1) (hWK 2)
        (by
          intro a ha b hb
          have hbr := hBRemoved b (hFActive 2 b hb)
          rcases Finset.mem_union.mp ha with ha | ha
          · exact hNew0 a b (Finset.mem_filter.mp ha).1 hbr.1 hbr.2
              (Finset.mem_filter.mp ha).2
          · exact hMiddle2 a b (Finset.mem_filter.mp ha).1 hbr.1 hbr.2
              (Finset.mem_filter.mp ha).2 (hFLabel 2 b hb))
        (by
          intro a ha b hb
          exact hNew2 a b (Finset.mem_filter.mp ha).1
            (hBRemoved b (hFActive 2 b hb)).1 (hBRemoved b (hFActive 2 b hb)).2
            (Finset.mem_filter.mp ha).2)
      have hImage (D : Finset ℕ) (v : ℕ) :
          D.image (fun _ => v) = if D.Nonempty then {v} else ∅ := by
        by_cases hh : D.Nonempty
        · simp only [hh, if_true, Finset.image_const hh]
        · simp only [Finset.not_nonempty_iff_eq_empty.mp hh, Finset.image_empty,
            Finset.not_nonempty_empty, if_false]
      simp only [hImage, Finset.union_nonempty, hW] at h0 h2
      change (RN B 0).card + _ ≤ S.card at h0
      change (RN B 2).card + _ ≤ S.card at h2
      have hKExact : K = (if 0 ∈ K then {0} else ∅) ∪
          (if 1 ∈ K then {1} else ∅) ∪ (if 2 ∈ K then {2} else ∅) := by
        ext c
        by_cases hc : c ∈ K
        · rcases hKLabels c hc with rfl | rfl | rfl <;> simp [hc]
        · simp only [hc, false_iff, Finset.mem_union]
          intro hh
          rcases hh with (hh | hh) | hh
          all_goals
            split_ifs at hh with hd
            · have he := Finset.mem_singleton.mp hh
              exact hc (by simpa only [he] using hd)
            · exact Finset.notMem_empty c hh
      have hcount : K.card + 1 ≤
          ((if 0 ∈ K then ({lo} : Finset ℕ) else ∅) ∪
            (if 1 ∈ K ∨ 2 ∈ K then {hi} else ∅)).card +
          ((if 0 ∈ K ∨ 1 ∈ K then ({lo} : Finset ℕ) else ∅) ∪
            (if 2 ∈ K then {hi} else ∅)).card := by
        have hpos := Finset.card_pos.mpr hK
        by_cases h0K : 0 ∈ K <;> by_cases h1K : 1 ∈ K <;> by_cases h2K : 2 ∈ K <;>
          simp only [h0K, h1K, h2K, if_true, if_false, or_true, true_or, false_or,
            Finset.union_empty, Finset.empty_union] at hKExact ⊢ <;>
          rw [hKExact] at hpos ⊢ <;>
          simp [hlohi, Ne.symm hlohi] at hpos <;>
          norm_num [hlohi, Ne.symm hlohi]
      omega
    · have hKE : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
      have h0 := hReserve (F B 0) ∅ ∅ (fun r hr => hFActive 0 r hr)
        hEmpty hEmpty (by simp) (by simp)
      have h2 := hReserve (F B 2) ∅ ∅ (fun r hr => hFActive 2 r hr)
        hEmpty hEmpty (by simp) (by simp)
      change (RN B 0).card + _ ≤ S.card at h0
      change (RN B 2).card + _ ≤ S.card at h2
      simp only [Finset.image_empty, Finset.union_empty, Finset.card_empty, Nat.add_zero] at h0 h2
      rcases hExtreme p hpSource.1 with hp0 | hp2
      · have hh := hReserve (F B 2) {p} ∅ (fun r hr => hFActive 2 r hr)
          hSingle hEmpty
          (by
            intro a ha b hb
            have hpx := hOld0 p hpSource.1 hp0 x hxMark
            have hxb := hOld2 b (hBRemoved b (hFActive 2 b hb)).1 (hFLabel 2 b hb) x hxMark
            have he := Finset.mem_singleton.mp ha
            omega) (by simp)
        change (RN B 2).card + _ ≤ S.card at hh
        simp only [Finset.image_singleton, Finset.image_empty, Finset.union_empty,
          Finset.card_singleton] at hh
        simp only [hKE, Finset.card_empty]
        omega
      · have hh := hReserve (F B 0) ∅ {p} (fun r hr => hFActive 0 r hr)
          hEmpty hSingle (by simp)
          (by
            intro a ha b hb
            have hxp := hOld2 p hpSource.1 hp2 x hxMark
            have hbx := hOld0 b (hBRemoved b (hFActive 0 b hb)).1 (hFLabel 0 b hb) x hxMark
            have he := Finset.mem_singleton.mp ha
            omega)
        change (RN B 0).card + _ ≤ S.card at hh
        simp only [Finset.image_singleton, Finset.image_empty, Finset.empty_union,
          Finset.card_singleton] at hh
        simp only [hKE, Finset.card_empty]
        omega
  have hTB : T B = (RN B 0).card + (RN B 2).card := by
    simp only [T, hColorsB, Finset.card_empty, Nat.zero_add]
  rw [hColorsA, hTB]
  refine ⟨by omega, ?_, ?_⟩
  · intro fuel
    have hh := hBound.1 fuel
    omega
  · have hh := hBound.2
    omega

end ErdosSzekeres
