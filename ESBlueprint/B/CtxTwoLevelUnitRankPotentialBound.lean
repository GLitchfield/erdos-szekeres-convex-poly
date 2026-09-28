import ESBlueprint.B.CtxBothUnitPartsZoneBudget
import ESBlueprint.B.CtxMixedClearOrSingletonRankCoverPotential
import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Full mixed unit-zone and opposite-rank potential bound for a positive-label context with chosen global at most four and two actual indexed levels on that axis. Every fuel approximation and the full recursive bound are at most the minimum of the occupied active chosen-unit-zone count plus the nonunit opposite-rank union cardinality, and the all-active opposite-rank union cardinality plus one. Consequently both are at most the opposite global parameter. Arbitrary older histories, maxima, repeated markers, inactive children and opposite global parameters are allowed. Empty and singleton rank cases use unit zones and common-rank covers; an active interior child already has chosen singleton rank two. Fuel induction combines the nonunit chosen-part cut estimates, the active-nonunit companion potential drop and the both-active-unit zone budget. Establishes the linear opposite-budget estimate sought for descendants with two chosen-axis levels in the singleton-end sandwich proof.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_level_unit_rank_potential_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4) :
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
  let potential := fun (ρ : Ctx.Context) =>
    min (unitZones ρ + (nonunitRanks ρ).card) ((ranks ρ).card + 1)
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ potential σ) ∧
    σ.bound ≤ potential σ ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ global σ t) ∧ σ.bound ≤ global σ t := by
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
  let I (ρ : Context) (v : Side) (p : ℕ) :=
    Finset.Icc (ρ.leftExt v 0 p + 1) (G ρ v - 1 - ρ.rightExt v 0 p)
  let RN (ρ : Context) := (nonunits ρ).biUnion (I ρ t)
  let R (ρ : Context) := (active ρ).biUnion (I ρ t)
  let T (ρ : Context) := (colors ρ).card + (RN ρ).card
  let V (ρ : Context) := min (T ρ) ((R ρ).card + 1)
  let Z (ρ : Context) := ((active ρ).image (label (marks ρ))).card
  let Good (ρ : Context) : Prop := ∃ N M x y : ℕ,
    N ∈ ρ.levels ∧ M ∈ ρ.levels ∧ N < M ∧ ρ.sideAt N = s ∧ ρ.sideAt M = s ∧
      x ∈ ρ.extPositions N ∧ y ∈ ρ.extPositions M
  change (∀ fuel, boundFuel fuel σ ≤ V σ) ∧ σ.bound ≤ V σ ∧
    (∀ fuel, boundFuel fuel σ ≤ G σ t) ∧ σ.bound ≤ G σ t
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
  have hPositivePart (ρ : Context) (keep : List ℕ) (t : Side) (m : ℕ) :
      ∀ x j v, (ρ.part keep t m).letterAt x = Letter.ext j v → 1 ≤ j := by
    intro x j v hx
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
      · cases hx; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep t m hxl he] at hx
      cases hx; omega
  have hThree (ρ : Context)
      (hPos : ∀ a j v, ρ.letterAt a = Letter.ext j v → 1 ≤ j)
      (hg : G ρ s ≤ 4) (hu : ∀ a ∈ active ρ, C ρ s a ≤ 1) :
      (∀ fuel, boundFuel fuel ρ ≤ Z ρ) ∧ ρ.bound ≤ Z ρ ∧ Z ρ ≤ 3 ∧
      (∀ (ks rs : List ℕ) (v : Side) (c d : ℕ),
        (∀ a ∈ ρ.childPositions, a ∈ ks → a ∉ rs) →
        Z (ρ.part ks s c) + Z (ρ.part rs v d) ≤ Z ρ) := by
    apply ctx_active_unit_axis_three_zone_potential ρ hPos s
    · cases s <;> simpa only [G] using hg
    · intro a ha hc hp
      have hh := hu a ((hActive ρ a).mpr ⟨ha, hc, hp⟩)
      cases s <;> simpa only [C] using hh
  have hGoodPart (ρ : Context) (hg : Good ρ) (keep : List ℕ) (v : Side) (m : ℕ) :
      Good (ρ.part keep v m) := by
    obtain ⟨N, M, x, y, hN, hM, hNM, hNs, hMs, hx, hy⟩ := hg
    have hN1 := one_le_of_mem_levels hN
    have hM1 := one_le_of_mem_levels hM
    refine ⟨N + 1, M + 1, x, y, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
    · rw [part_levels]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
    · rw [part_levels]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
    · simpa only [part_sideAt_succ ρ keep v m hN1] using hNs
    · simpa only [part_sideAt_succ ρ keep v m hM1] using hMs
    · simpa only [part_extPositions_succ ρ keep v m hN1] using hx
    · simpa only [part_extPositions_succ ρ keep v m hM1] using hy
  have hGPart (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) (w : Side) :
      G (ρ.part keep v m) w = G ρ w := by cases w <;> rfl
  have hPure (ρ : Context) (v : Side) (p : ℕ) (hp : p ∈ active ρ) :
      ρ.leftExt v 0 p + ρ.rightExt v 0 p < G ρ v - 1 := by
    have hh := ((hActive ρ p).mp hp).2
    cases v <;> simp only [G, cupLimit, capLimit, chainExt] at hh ⊢ <;> omega
  have hEnds (ρ : Context) (v : Side) (p : ℕ) (hp : p ∈ active ρ) :
      ρ.leftExt v 0 p + 1 ∈ I ρ v p ∧ G ρ v - 1 - ρ.rightExt v 0 p ∈ I ρ v p := by
    have hh := hPure ρ v p hp
    constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega
  have hINonempty (ρ : Context) (v : Side) (p : ℕ) (hp : p ∈ active ρ) : (I ρ v p).Nonempty :=
    ⟨_, (hEnds ρ v p hp).1⟩
  have hRNSubset (ρ : Context) : RN ρ ⊆ R ρ := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨p, (Finset.mem_filter.mp hp).1, hz⟩
  have hRankEq (ρ : Context) (v : Side) (p r : ℕ) (hp : p ∈ active ρ)
      (hs : I ρ v p ⊆ {r}) :
      ρ.leftExt v 0 p + 1 = r ∧ r + ρ.rightExt v 0 p = G ρ v - 1 := by
    have hl := Finset.mem_singleton.mp (hs (hEnds ρ v p hp).1)
    have hr := Finset.mem_singleton.mp (hs (hEnds ρ v p hp).2)
    have hh := hPure ρ v p hp
    exact ⟨hl, by omega⟩
  have hRankUnit (ρ : Context) (v : Side) (p r : ℕ)
      (hr : ρ.leftExt v 0 p + 1 = r ∧ r + ρ.rightExt v 0 p = G ρ v - 1) :
      C ρ v p ≤ 1 := by
    cases v <;> simp only [G, C, cupLimit, capLimit, chainExt] at hr ⊢ <;> omega
  have hEmptyActive (ρ : Context) (he : R ρ = ∅) : active ρ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hm : ρ.leftExt t 0 p + 1 ∈ R ρ :=
      Finset.mem_biUnion.mpr ⟨p, hp, (hEnds ρ t p hp).1⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  have hNoNonunit (ρ : Context) (he : RN ρ = ∅) : ∀ p ∈ active ρ, C ρ s p ≤ 1 := by
    intro p hp
    by_contra hn
    have hp2 : 2 ≤ C ρ s p := by omega
    have hm : ρ.leftExt t 0 p + 1 ∈ RN ρ :=
      Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hp2⟩, (hEnds ρ t p hp).1⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  have hRBound (ρ : Context) : (R ρ).card ≤ G ρ t - 1 := by
    have hs : R ρ ⊆ Finset.Icc 1 (G ρ t - 1) := by
      intro z hz
      obtain ⟨p, _, hz⟩ := Finset.mem_biUnion.mp hz
      have hh := Finset.mem_Icc.mp hz
      apply Finset.mem_Icc.mpr
      change ρ.leftExt t 0 p + 1 ≤ z ∧ z ≤ G ρ t - 1 - ρ.rightExt t 0 p at hh
      constructor <;> omega
    simpa using Finset.card_le_card hs
  have hVGlobal (ρ : Context) : V ρ ≤ G ρ t := by
    by_cases hg : G ρ t = 0
    · have he : active ρ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hh := hPure ρ t p hp
        rw [hg] at hh
        omega
      simp only [V, T, colors, units, RN, nonunits, R, he, Finset.filter_empty,
        Finset.image_empty, Finset.biUnion_empty, Finset.card_empty, Nat.zero_add,
        Nat.min_eq_left (Nat.zero_le _), Nat.zero_le]
    · have hh := hRBound ρ
      have hv : V ρ ≤ (R ρ).card + 1 := Nat.min_le_right _ _
      omega
  have hPositiveV (ρ : Context) (hn : (active ρ).Nonempty) : 1 ≤ V ρ := by
    obtain ⟨p, hp⟩ := hn
    have ht : 1 ≤ T ρ := by
      by_cases hu : C ρ s p ≤ 1
      · have hc : (colors ρ).Nonempty := ⟨label (marks ρ) p,
          Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hu⟩, rfl⟩⟩
        have hh := Finset.card_pos.mpr hc
        dsimp only [T]
        omega
      · have hc : (RN ρ).Nonempty := ⟨ρ.leftExt t 0 p + 1,
          Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, by omega⟩, (hEnds ρ t p hp).1⟩⟩
        have hh := Finset.card_pos.mpr hc
        dsimp only [T]
        omega
    exact Nat.le_min.mpr ⟨ht, by omega⟩
  have hSmallR (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hg : G ρ s ≤ 4) (hsmall : (R ρ).card ≤ 1) : ∀ fuel, boundFuel fuel ρ ≤ V ρ := by
    by_cases he : R ρ = ∅
    · have ha := hEmptyActive ρ he
      have hu : ∀ p ∈ active ρ, C ρ s p ≤ 1 := by simp only [ha, Finset.notMem_empty, false_implies, forall_const]
      have hh := hThree ρ hPos hg hu
      have hz : Z ρ = 0 := by simp only [Z, ha, Finset.image_empty, Finset.card_empty]
      intro fuel
      have hb := hh.1 fuel
      rw [hz] at hb
      omega
    · have hc : (R ρ).card = 1 := by have hn := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he); omega
      obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hc
      have hRank (p : ℕ) (hp : p ∈ active ρ) :
          ρ.leftExt t 0 p + 1 = r ∧ r + ρ.rightExt t 0 p = G ρ t - 1 := by
        apply hRankEq ρ t p r hp
        intro z hz
        rw [← hr]
        exact Finset.mem_biUnion.mpr ⟨p, hp, hz⟩
      have hh := ctx_bound_le_one_of_common_singleton_rank ρ hPos t r (by
        intro p hp hc hd
        have h := hRank p ((hActive ρ p).mpr ⟨hp, hc, hd⟩)
        cases t <;> simpa only [G] using h)
      have hact : (active ρ).Nonempty := by
        obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr he
        obtain ⟨p, hp, _⟩ := Finset.mem_biUnion.mp hz
        exact ⟨p, hp⟩
      exact fun fuel => (hh.1 fuel).trans (hPositiveV ρ hact)
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
  have hLabelLe (M : Finset ℕ) (p : ℕ) : label M p ≤ 2 := by
    unfold label
    split_ifs <;> omega
  have hUnitZonesTwo (ρ : Context) (hg : G ρ s ≤ 4) (hgood : Good ρ)
      (hn : (RN ρ).Nonempty) : (colors ρ).card ≤ 2 := by
    obtain ⟨z, hz⟩ := hn
    obtain ⟨r0, hr0, _⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hr0a, hr02⟩ := Finset.mem_filter.mp hr0
    have hr0c := ((hActive ρ r0).mp hr0a).1
    obtain ⟨N, M, x, y, hN, hM, hNM, hNs, hMs, hx, hy⟩ := hgood
    have hNOn : N ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
    have hxMark : x ∈ marks ρ := (hMark ρ x).mpr ⟨N, hNOn, hx⟩
    have hMarks : (marks ρ).Nonempty := ⟨x, hxMark⟩
    obtain ⟨dir, hout⟩ : ∃ dir : Bool, ∀ j ∈ ρ.levelsOn s 0,
        ∀ z ∈ ρ.extPositions j, Rel dir z r0 := by
      have h0 := ctx_nonunit_children_exterior_of_two_levels ρ s N M x y
        hN hM hNM hNs hMs hx hy (by cases s <;> simpa only [G] using hg)
      rcases h0 with hh | hh
      · exact ⟨true, hh.2 r0 hr0c (by cases s <;> simpa only [C] using hr02)⟩
      · exact ⟨false, hh.2 r0 hr0c (by cases s <;> simpa only [C] using hr02)⟩
    let D : ℕ := if dir then 2 else 0
    let E : ℕ := if dir then 0 else 2
    have hnot (p : ℕ) (hp : p ∈ units ρ) : label (marks ρ) p ≠ D := by
      intro he
      obtain ⟨hpa, hpu⟩ := Finset.mem_filter.mp hp
      have hpc := ((hActive ρ p).mp hpa).1
      have hpout := (hExterior dir (marks ρ) hMarks p (hNoMark ρ p hpc)).mp he
      have heq : C ρ s p = C ρ s r0 := by
        apply hClearEq
        intro j hj z hz
        have hpz := hpout z ((hMark ρ z).mpr ⟨j, hj, hz⟩)
        have h0z := hout j hj z hz
        cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hpz h0z <;> omega
      omega
    have hs : colors ρ ⊆ ({E, 1} : Finset ℕ) := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      have hn := hnot p hp
      have hc : label (marks ρ) p = E ∨ label (marks ρ) p = 1 ∨ label (marks ρ) p = D := by
        cases dir <;> simp only [E, D, Bool.false_eq_true, if_false, if_true] <;>
          unfold label <;> split_ifs <;> omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hc.elim Or.inl (fun hh => hh.elim Or.inr (fun he => False.elim (hn he)))
    have hh := Finset.card_le_card hs
    have hc : ({E, 1} : Finset ℕ).card ≤ 2 := by cases dir <;> simp [E]
    omega
  have hInteriorRank (ρ : Context) (hg : G ρ s ≤ 4) (p : ℕ) (hp : p ∈ active ρ)
      (hz : label (marks ρ) p = 1) :
      ρ.leftExt s 0 p + 1 = 2 ∧ 2 + ρ.rightExt s 0 p = G ρ s - 1 := by
    obtain ⟨hL, hR⟩ := (hZ1 (marks ρ) p).mp hz
    obtain ⟨x, hx, hxp⟩ := Finset.filter_nonempty_iff.mp hL
    obtain ⟨y, hy, hpy⟩ := Finset.filter_nonempty_iff.mp hR
    obtain ⟨N, hN, hx⟩ := (hMark ρ x).mp hx
    obtain ⟨M, hM, hy⟩ := (hMark ρ y).mp hy
    have hl := hOneLeft ρ s N p x hN hx hxp
    have hr := hOneRight ρ s M p y hM hy hpy
    have hpos := hPure ρ s p hp
    constructor <;> omega
  have hClearOuter (ρ : Context) (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions)
      (he : label (marks ρ) p = label (marks ρ) q) (hn : label (marks ρ) p ≠ 1) :
      ∀ j ∈ ρ.levelsOn s 0, ∀ z ∈ ρ.extPositions j,
        z < min p q ∨ max p q < z := by
    have hnp := hNoMark ρ p hp
    have hnq := hNoMark ρ q hq
    by_cases hL : ((marks ρ).filter (· < p)).Nonempty
    · by_cases hR : ((marks ρ).filter (p < ·)).Nonempty
      · exact False.elim (hn ((hZ1 (marks ρ) p).mpr ⟨hL, hR⟩))
      · have hqBoth := (hZ2 (marks ρ) q).mp (he.symm.trans ((hZ2 (marks ρ) p).mpr ⟨hL, hR⟩))
        intro j hj z hz
        have hm := (hMark ρ z).mpr ⟨j, hj, hz⟩
        have hzp := hAllLeft (marks ρ) p hnp hR z hm
        have hzq := hAllLeft (marks ρ) q hnq hqBoth.2 z hm
        left
        omega
    · have hqL := (hZ0 (marks ρ) q).mp (he.symm.trans ((hZ0 (marks ρ) p).mpr hL))
      intro j hj z hz
      have hm := (hMark ρ z).mpr ⟨j, hj, hz⟩
      have hpz := hAllRight (marks ρ) p hnp hL z hm
      have hqz := hAllRight (marks ρ) q hnq hqL z hm
      right
      omega
  have hSmallNonunit (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hg : G ρ s ≤ 4) (hgood : Good ρ) (hsmall : (RN ρ).card ≤ 1) :
      ∀ fuel, boundFuel fuel ρ ≤ T ρ ∧ boundFuel fuel ρ ≤ 3 := by
    by_cases hempty : RN ρ = ∅
    · have hu := hNoNonunit ρ hempty
      have hh := hThree ρ hPos hg hu
      have he : units ρ = active ρ := Finset.filter_eq_self.mpr hu
      have hT : T ρ = Z ρ := by
        simp only [T, colors, he, hempty, Finset.card_empty, Nat.add_zero, Z]
      intro fuel
      exact ⟨by rw [hT]; exact hh.1 fuel, (hh.1 fuel).trans hh.2.2.1⟩
    have hcard : (RN ρ).card = 1 := by
      have hn := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
      omega
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard
    have hRankNonunit (p : ℕ) (hp : p ∈ active ρ) (hp2 : 2 ≤ C ρ s p) :
        ρ.leftExt t 0 p + 1 = r ∧ r + ρ.rightExt t 0 p = G ρ t - 1 := by
      apply hRankEq ρ t p r hp
      intro z hz
      rw [← hr]
      exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hp2⟩, hz⟩
    let color (p : ℕ) := if C ρ s p ≤ 1 then label (marks ρ) p else 3
    let axis (c : ℕ) := if c = 3 then t else s
    let mode (c : ℕ) := decide (c = 1 ∨ c = 3)
    let rank (c : ℕ) := if c = 3 then r else 2
    have hColorUnit (p : ℕ) (hu : C ρ s p ≤ 1) : color p = label (marks ρ) p := by simp only [color, if_pos hu]
    have hColorNonunit (p : ℕ) (hn : ¬ C ρ s p ≤ 1) : color p = 3 := by simp only [color, if_neg hn]
    have hColorNotThree (p : ℕ) (hu : C ρ s p ≤ 1) : color p ≠ 3 := by
      rw [hColorUnit p hu]
      have hh := hLabelLe (marks ρ) p
      omega
    have hCover := ctx_mixed_clear_or_singleton_rank_cover_potential ρ hPos color axis mode rank
      (by
        intro p hp hc hd
        have hpa := (hActive ρ p).mpr ⟨hp, hc, hd⟩
        change C ρ (axis (color p)) p ≤ 1
        by_cases hu : C ρ s p ≤ 1
        · simp only [axis, if_neg (hColorNotThree p hu)]
          exact hu
        · rw [hColorNonunit p hu]
          simp only [axis, if_pos rfl]
          exact hRankUnit ρ t p r (hRankNonunit p hpa (by omega)))
      (by
        intro p hp q hq hpc hpd hqc hqd he hm
        have hm' : ¬ (color p = 1 ∨ color p = 3) := of_decide_eq_false hm
        have hu : C ρ s p ≤ 1 := by
          by_contra hn
          exact hm' (Or.inr (hColorNonunit p hn))
        have hv : C ρ s q ≤ 1 := by
          by_contra hn
          exact hm' (Or.inr (he.trans (hColorNonunit q hn)))
        have hlabel : label (marks ρ) p = label (marks ρ) q := by
          rw [hColorUnit p hu, hColorUnit q hv] at he
          exact he
        have hnot : label (marks ρ) p ≠ 1 := fun hh => hm' (Or.inl ((hColorUnit p hu).trans hh))
        simpa only [axis, if_neg (hColorNotThree p hu)] using hClearOuter ρ p q hp hq hlabel hnot)
      (by
        intro p hp hc hd hm
        have hpa := (hActive ρ p).mpr ⟨hp, hc, hd⟩
        have hm' : color p = 1 ∨ color p = 3 := of_decide_eq_true hm
        change ρ.leftExt (axis (color p)) 0 p + 1 = rank (color p) ∧
          rank (color p) + ρ.rightExt (axis (color p)) 0 p = G ρ (axis (color p)) - 1
        rcases hm' with h1 | h3
        · have hu : C ρ s p ≤ 1 := by
            by_contra hn
            have hh := hColorNonunit p hn
            omega
          have hz : label (marks ρ) p = 1 := (hColorUnit p hu).symm.trans h1
          have hh := hInteriorRank ρ hg p hpa hz
          simpa [h1, axis, rank] using hh
        · have hu : ¬ C ρ s p ≤ 1 := fun hh => hColorNotThree p hh h3
          have hh := hRankNonunit p hpa (by omega)
          simpa [h3, axis, rank] using hh)
    have hCoverCard : ((active ρ).image color).card ≤ (colors ρ).card + 1 := by
      have hs : (active ρ).image color ⊆ colors ρ ∪ {3} := by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
        by_cases hu : C ρ s p ≤ 1
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
            ⟨p, Finset.mem_filter.mpr ⟨hp, hu⟩, (hColorUnit p hu).symm⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr (hColorNonunit p hu)))
      have hh := Finset.card_le_card hs
      have hc := Finset.card_union_le (colors ρ) {3}
      simp only [Finset.card_singleton] at hc
      omega
    have hU := hUnitZonesTwo ρ hg hgood (Finset.nonempty_iff_ne_empty.mpr hempty)
    intro fuel
    have hh : boundFuel fuel ρ ≤ ((active ρ).image color).card := hCover.1 fuel
    change boundFuel fuel ρ ≤ (colors ρ).card + (RN ρ).card ∧ boundFuel fuel ρ ≤ 3
    rw [hcard]
    constructor <;> omega
  have hBaseLower (c p k : ℕ) (hc : c ≤ 2) (hp : p ≤ k - 1) : baseOf c p k ≤ p := by
    unfold baseOf
    by_cases hz : c = 0 ∨ p = 0
    · rw [if_pos hz]
      exact Nat.zero_le _
    rw [if_neg hz]
    by_cases ho : c = 1 ∨ p = 1
    · rw [if_pos ho]
      omega
    rw [if_neg ho]
    have hc2 : c = 2 := by omega
    subst c
    rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hrow : p + 1 + (2 + 1) - 4 = p := by omega
    have hcol : p + 1 - 2 = p - 1 := by omega
    rw [hrow, hcol, Nat.choose_symm (show 1 ≤ p by omega)]
    simp
  have hBaseUpper (c p k : ℕ) (hp : p ≤ 2) (hc : c ≤ k - 1) : baseOf c p k ≤ c := by
    unfold baseOf
    by_cases hz : c = 0 ∨ p = 0
    · rw [if_pos hz]
      exact Nat.zero_le _
    rw [if_neg hz]
    by_cases ho : c = 1 ∨ p = 1
    · rw [if_pos ho]
      omega
    rw [if_neg ho]
    have hp2 : p = 2 := by omega
    subst p
    rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hrow : 2 + 1 + (c + 1) - 4 = c := by omega
    rw [hrow]
    simp
  have hChosenTwo (ρ : Context) (hg : G ρ s ≤ 4) (hgood : Good ρ)
      (p : ℕ) (hp : p ∈ ρ.childPositions) : C ρ s p ≤ 2 := by
    obtain ⟨N, M, x, y, hN, hM, hNM, hNs, hMs, hx, hy⟩ := hgood
    have hNOn : N ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
    have hxMark : x ∈ marks ρ := (hMark ρ x).mpr ⟨N, hNOn, hx⟩
    have hxp : x ≠ p := by intro he; exact hNoMark ρ p hp (he ▸ hxMark)
    have hchain : 1 ≤ ρ.leftExt s 0 p + ρ.rightExt s 0 p := by
      rcases lt_or_gt_of_ne hxp with hl | hr
      · have hh := hOneLeft ρ s N p x hNOn hx hl
        omega
      · have hh := hOneRight ρ s N p x hNOn hx hr
        omega
    cases s <;> simp only [C, G, cupLimit, capLimit, chainExt] at hg hchain ⊢ <;> omega
  have hBase (ρ : Context) (hg : G ρ s ≤ 4) (hgood : Good ρ) : ρ.base ≤ V ρ := by
    rw [base_eq_baseOf]
    cases hh : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      by_cases hz : ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0
      · simp [baseOf, hz]
      have hpos : 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by omega
      have ha : p ∈ active ρ := (hActive ρ p).mpr ⟨hp, hpos⟩
      by_cases hu : C ρ s p ≤ 1
      · have hone : ρ.cupLimit p p = 1 ∨ ρ.capLimit p p = 1 := by
          cases s <;> simp only [C] at hu <;> omega
        have hv := hPositiveV ρ ⟨p, ha⟩
        simpa only [baseOf, if_neg hz, if_pos hone] using hv
      · have hp2 : 2 ≤ C ρ s p := by omega
        have hlim := hChosenTwo ρ hg hgood p hp
        have hcupk : ρ.cupLimit p p ≤ ρ.k - 1 := by dsimp only [cupLimit]; omega
        have hcapk : ρ.capLimit p p ≤ ρ.k - 1 := by dsimp only [capLimit]; omega
        have hOpp : baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ C ρ t p := by
          cases s <;> cases t
          · exact False.elim (hne rfl)
          · exact hBaseLower _ _ _ hlim hcapk
          · exact hBaseUpper _ _ _ hlim hcupk
          · exact False.elim (hne rfl)
        have hwidth : C ρ t p ≤ (I ρ t p).card := by
          simp only [I, Nat.card_Icc]
          cases t <;> simp only [G, C, cupLimit, capLimit, chainExt] <;> omega
        have hsub : I ρ t p ⊆ RN ρ := by
          intro z hz
          exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨ha, hp2⟩, hz⟩
        have hb := hOpp.trans (hwidth.trans (Finset.card_le_card hsub))
        have hr := Finset.card_le_card (hRNSubset ρ)
        change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤
          min ((colors ρ).card + (RN ρ).card) ((R ρ).card + 1)
        apply Nat.le_min.mpr
        constructor <;> omega
  have hCut (fuel : ℕ) (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hg : G ρ s ≤ 4) (hgood : Good ρ) (hbig : 2 ≤ (RN ρ).card)
      (hparts : ∀ (ks : List ℕ) (v : Side) (m : ℕ),
        boundFuel fuel (ρ.part ks v m) ≤ V (ρ.part ks v m))
      (keep : List ℕ) (m n p q : ℕ)
      (hp : p ∈ ρ.childPositions) (hkeep : p ∈ keep)
      (hq : q ∈ ρ.childPositions) (hremoved : q ∉ keep) :
      boundFuel fuel (ρ.part keep s m) +
        boundFuel fuel (ρ.part (ρ.childPositions.filter (· ∉ keep)) t n) ≤ V ρ := by
    let rest := ρ.childPositions.filter (· ∉ keep)
    let A := ρ.part keep s m
    let B := ρ.part rest t n
    change boundFuel fuel A + boundFuel fuel B ≤ V ρ
    obtain ⟨N, M, x, y, hN, hM, hNM, hNs, hMs, hx, hy⟩ := hgood
    have hiA : boundFuel fuel A ≤ V A := hparts keep s m
    have hiB : boundFuel fuel B ≤ V B := hparts rest t n
    by_cases ha : ∃ a ∈ A.childPositions, 2 ≤ C A s a
    · obtain ⟨a, hac, ha2⟩ := ha
      have hraw0 := ctx_nonunit_part_unit_rank_potential_drop ρ hPos s t hne N M x y
        hN hM hNM hNs hMs hx hy (by cases s <;> simpa only [G] using hg)
        keep m n a q hac (by cases s <;> simpa only [C, A] using ha2) hq hremoved
      have hraw : T A + T B ≤ T ρ := by
        cases s <;> cases t <;>
          simpa only [T, colors, units, RN, nonunits, active, C, I, G, marks, label, A, B, rest]
            using hraw0.2.2.2
      have hrank0 := ctx_cut_rank_budget_of_nonunit_part ρ hPos s t hne N M x y
        hN hM hNM hNs hMs hx hy (by cases s <;> simpa only [G] using hg)
        keep m n a q hac (by cases s <;> simpa only [C, A] using ha2) hq hremoved
      have hrankA : boundFuel fuel A ≤ (R ρ).card := by
        cases t <;> simpa only [R, active, I, G, A] using hrank0.1 fuel
      have hrankB : boundFuel fuel B ≤ 1 := hrank0.2.2.1 fuel
      have hVA : V A ≤ T A := Nat.min_le_left _ _
      have hVB : V B ≤ T B := Nat.min_le_left _ _
      apply Nat.le_min.mpr
      constructor <;> omega
    have huA : ∀ a ∈ A.childPositions, C A s a ≤ 1 := by
      intro a hac
      by_contra hn
      exact ha ⟨a, hac, by omega⟩
    by_cases hb : ∃ b ∈ active B, 2 ≤ C B s b
    · obtain ⟨b, hba, hb2⟩ := hb
      obtain ⟨hbc, hbcu, hbca⟩ := (hActive B b).mp hba
      have hdrop := ctx_cut_potential_drop_of_nonunit_companion ρ hPos s t hne N M x y
        hN hM hNM hNs hMs hx hy hg keep m n p b hp hkeep hbc hbcu hbca hb2
      have hdrop' : V A + V B ≤ V ρ := hdrop.2.2.2
      exact (Nat.add_le_add hiA hiB).trans hdrop'
    have huB : ∀ b ∈ active B, C B s b ≤ 1 := by
      intro b hba
      by_contra hn
      exact hb ⟨b, hba, by omega⟩
    have hzones := ctx_both_unit_parts_zone_budget ρ hPos s t hne N M x y
      hN hM hNM hNs hMs hx hy hg keep m n p q hp hkeep hq hremoved
      (by intro a hac _ _; exact huA a hac)
      (by intro b hbc hbcu hbca; exact huB b ((hActive B b).mpr ⟨hbc, hbcu, hbca⟩))
    have hsum : boundFuel fuel A + boundFuel fuel B ≤ min 3 ((colors ρ).card + 2) :=
      hzones.2.1 fuel fuel
    have hr := Finset.card_le_card (hRNSubset ρ)
    have hthree : min 3 ((colors ρ).card + 2) ≤ 3 := Nat.min_le_left _ _
    have hunit : min 3 ((colors ρ).card + 2) ≤ (colors ρ).card + 2 := Nat.min_le_right _ _
    change boundFuel fuel A + boundFuel fuel B ≤
      min ((colors ρ).card + (RN ρ).card) ((R ρ).card + 1)
    apply Nat.le_min.mpr
    constructor <;> omega
  have hFuel : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      G ρ s ≤ 4 → Good ρ → boundFuel fuel ρ ≤ V ρ := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hPos hg hgood
      by_cases hRsmall : (R ρ).card ≤ 1
      · exact hSmallR ρ hPos hg hRsmall (fuel + 1)
      by_cases hRNsmall : (RN ρ).card ≤ 1
      · have hh := hSmallNonunit ρ hPos hg hgood hRNsmall (fuel + 1)
        apply Nat.le_min.mpr
        exact ⟨hh.1, by omega⟩
      have hbig : 2 ≤ (RN ρ).card := by omega
      rw [boundFuel]
      split
      · exact hBase ρ hg hgood
      · apply Ctx.getD_max?_le
        intro z hz
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hz
        obtain ⟨keep, hkeep, d, _, hz⟩ := hz
        obtain ⟨hkl, hkne, hksub⟩ := mem_blocks hkeep
        obtain ⟨p, hpk⟩ := List.exists_mem_of_ne_nil _ hkne
        have hp : p ∈ ρ.childPositions := hksub p hpk
        have hremoved : ∃ q ∈ ρ.childPositions, q ∉ keep := by
          by_contra h
          push Not at h
          have hlen := ((childPositions_nodup ρ).subperm h).length_le
          omega
        obtain ⟨q, hq, hqk⟩ := hremoved
        let rest := ρ.childPositions.filter (· ∉ keep)
        have hparts (ks : List ℕ) (v : Side) (m : ℕ) :
            boundFuel fuel (ρ.part ks v m) ≤ V (ρ.part ks v m) :=
          ih _ (hPositivePart ρ ks v m) (by simpa only [hGPart] using hg)
            (hGoodPart ρ hgood ks v m)
        have hforward (a b : ℕ) : boundFuel fuel (ρ.part keep s a) +
            boundFuel fuel (ρ.part rest t b) ≤ V ρ :=
          hCut fuel ρ hPos hg hgood hbig hparts keep a b p q hp hpk hq hqk
        have hdouble (v : Side) (m : ℕ) :
            ρ.part (ρ.childPositions.filter (· ∉ rest)) v m = ρ.part keep v m := by
          apply part_congr
          intro r hr
          simp only [rest, List.mem_filter, decide_eq_true_eq, hr, true_and, not_not]
        have hbackward (a b : ℕ) : boundFuel fuel (ρ.part rest s a) +
            boundFuel fuel (ρ.part keep t b) ≤ V ρ := by
          have hh := hCut fuel ρ hPos hg hgood hbig hparts rest a b q p
            hq (by simp [rest, hq, hqk]) hp (by simp [rest, hpk])
          rw [hdouble] at hh
          exact hh
        have hboth (a b : ℕ) :
            (boundFuel fuel (ρ.part keep Side.lower a) +
              boundFuel fuel (ρ.part rest Side.upper b) ≤ V ρ) ∧
            (boundFuel fuel (ρ.part keep Side.upper b) +
              boundFuel fuel (ρ.part rest Side.lower a) ≤ V ρ) := by
          cases s <;> cases t
          · exact False.elim (hne rfl)
          · exact ⟨hforward a b, by simpa only [Nat.add_comm] using hbackward a b⟩
          · exact ⟨by simpa only [Nat.add_comm] using hbackward b a, hforward b a⟩
          · exact False.elim (hne rfl)
        rcases hz with rfl | rfl
        · exact (hboth (d + 1) (ρ.k - 1 - (d + 1))).1
        · exact (hboth (d + 1) (ρ.k - 1 - (d + 1))).2
  have hgood : Good σ := ⟨N, M, x, y, hN, hM, hNM, hNs, hMs, hx, hy⟩
  have hf : ∀ fuel, boundFuel fuel σ ≤ V σ := fun fuel => hFuel fuel σ hpositive hglobal hgood
  have hb : σ.bound ≤ V σ := hf _
  exact ⟨hf, hb, fun fuel => (hf fuel).trans (hVGlobal σ), hb.trans (hVGlobal σ)⟩

end ErdosSzekeres
