import ESBlueprint.B.CtxUnitAxisRegionPotentialAdditive

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- A rank-and-region potential for contexts whose global parameter on one axis is at most three. Active children contribute their allowed opposite-axis pure-chain ranks; when indexed markers on the small axis exist, cap this rank count by the active-region count. The potential bounds every fuel approximation and the full bound, fits within the opposite global chain budget, and decreases additively across arbitrary disjoint kept sets with arbitrary new maxima. Positive external labels suffice, including inactive levels. Intended to provide both small-capacity orientations and arbitrary-partition additivity after ancestor normalization.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_small_global_axis_rank_region_potential (σ : Ctx.Context)
  (hpositive : ∀ x l v, σ.letterAt x = Ctx.Letter.ext l v → 1 ≤ l)
  (s t : Ctx.Side) (hne : s ≠ t)
  (hsmall : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 3) :
  let markers := fun (ρ : Ctx.Context) =>
    (ρ.levelsOn s 0).toFinset.biUnion (fun l => (ρ.extPositions l).toFinset)
  let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let budget := fun (ρ : Ctx.Context) =>
    match t with | Ctx.Side.lower => ρ.u - 1 | Ctx.Side.upper => ρ.a - 1
  let ranks := fun (ρ : Ctx.Context) => (active ρ).biUnion
    (fun p => Finset.Icc (ρ.leftExt t 0 p + 1) (budget ρ - ρ.rightExt t 0 p))
  let regions := fun (ρ : Ctx.Context) =>
    ((active ρ).image (fun p => ((markers ρ).filter (· < p)).card)).card
  let potential := fun (ρ : Ctx.Context) =>
    if markers ρ = ∅ then (ranks ρ).card else min (regions ρ) (ranks ρ).card
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ potential σ) ∧
    σ.bound ≤ potential σ ∧ potential σ ≤ budget σ ∧
    (∀ (keep rest : List ℕ) (m n : ℕ),
      (∀ p ∈ σ.childPositions, p ∈ keep → p ∉ rest) →
      potential (σ.part keep s m) + potential (σ.part rest t n) ≤ potential σ) := by
  classical
  let G (ρ : Context) := match s with | Side.lower => ρ.u | Side.upper => ρ.a
  let B (ρ : Context) := match t with | Side.lower => ρ.u - 1 | Side.upper => ρ.a - 1
  let L (ρ : Context) (p : ℕ) := ρ.leftExt t 0 p
  let R (ρ : Context) (p : ℕ) := ρ.rightExt t 0 p
  let opp (ρ : Context) (p : ℕ) := match t with
    | Side.lower => ρ.cupLimit p p
    | Side.upper => ρ.capLimit p p
  let marks (ρ : Context) : Finset ℕ :=
    (ρ.levelsOn s 0).toFinset.biUnion (fun j => (ρ.extPositions j).toFinset)
  let active (ρ : Context) : Finset ℕ := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let ranks (ρ : Context) := (active ρ).biUnion (fun p => Finset.Icc (L ρ p + 1) (B ρ - R ρ p))
  let reg (ρ : Context) := ((active ρ).image (fun p => ((marks ρ).filter (· < p)).card)).card
  let V (ρ : Context) := if marks ρ = ∅ then (ranks ρ).card else min (reg ρ) (ranks ρ).card
  change (∀ fuel, boundFuel fuel σ ≤ V σ) ∧ σ.bound ≤ V σ ∧ V σ ≤ B σ ∧
    (∀ (keep rest : List ℕ) (m n : ℕ),
      (∀ p ∈ σ.childPositions, p ∈ keep → p ∉ rest) →
      V (σ.part keep s m) + V (σ.part rest t n) ≤ V σ)
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by simp [active]
  have hMark (ρ : Context) (p : ℕ) : p ∈ marks ρ ↔
      ∃ j ∈ ρ.levelsOn s 0, p ∈ ρ.extPositions j := by simp [marks]
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
  have hInherit (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) (u : Side) (p : ℕ) :
      ρ.leftExt u 0 p ≤ (ρ.part keep v m).leftExt u 0 p ∧
      ρ.rightExt u 0 p ≤ (ρ.part keep v m).rightExt u 0 p := by
    let τ := ρ.part keep v m
    have hlevels (t : Ctx.Side) (N : ℕ) :
        List.Sublist ((ρ.levelsOn t N).map (· + 1)) (τ.levelsOn t (if N = 0 then 0 else N + 1)) := by
      unfold Ctx.Context.levelsOn
      change List.Sublist _ ((ρ.part keep v m).levels.filter _)
      rw [Ctx.Context.part_levels, List.filter_cons, List.filter_map]
      have heq : ρ.levels.filter (fun l => decide ((ρ.part keep v m).sideAt (l + 1) = t ∧
          ((if N = 0 then 0 else N + 1) = 0 ∨ l + 1 < (if N = 0 then 0 else N + 1)))) =
          ρ.levels.filter (fun l => decide (ρ.sideAt l = t ∧ (N = 0 ∨ l < N))) := by
        apply List.filter_congr
        intro l hl
        have hl1 := Ctx.Context.one_le_of_mem_levels hl
        by_cases hN : N = 0 <;>
          simp [hN, Ctx.Context.part_sideAt_succ ρ keep v m hl1]
      simp only [Function.comp_def]
      rw [heq]
      split_ifs <;> simp_all
    have hleft (t : Ctx.Side) (N p : ℕ) :
        ρ.leftExt t N p ≤ τ.leftExt t (if N = 0 then 0 else N + 1) p := by
      simp only [Ctx.Context.leftExt_eq]
      apply Ctx.getD_max?_le_of_forall
      intro x hx
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
      have hsub := List.mem_sublists.mp hls
      have hpos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
        (Ctx.Context.one_le_of_mem_levelsOn (hsub.subset hl)).1
      refine ⟨((ls.map (· + 1)).foldl (Ctx.Context.leftStep τ) (p, 0)).2,
        List.mem_map.mpr ⟨_, List.mem_sublists.mpr ((hsub.map _).trans (hlevels t N)), rfl⟩, ?_⟩
      exact le_of_eq (congrArg Prod.snd (Ctx.Context.foldl_leftStep_part_map ρ keep v m ls hpos (p, 0))).symm
    have hright (t : Ctx.Side) (N p : ℕ) :
        ρ.rightExt t N p ≤ τ.rightExt t (if N = 0 then 0 else N + 1) p := by
      simp only [Ctx.Context.rightExt_eq]
      apply Ctx.getD_max?_le_of_forall
      intro x hx
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
      have hsub := List.mem_sublists.mp hls
      have hpos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
        (Ctx.Context.one_le_of_mem_levelsOn (hsub.subset hl)).1
      refine ⟨((ls.map (· + 1)).foldl (Ctx.Context.rightStep τ) (p, 0)).2,
        List.mem_map.mpr ⟨_, List.mem_sublists.mpr ((hsub.map _).trans (hlevels t N)), rfl⟩, ?_⟩
      exact le_of_eq (congrArg Prod.snd (Ctx.Context.foldl_rightStep_part_map ρ keep v m ls hpos (p, 0))).symm
    exact ⟨by simpa only [if_pos rfl] using hleft u 0 p,
      by simpa only [if_pos rfl] using hright u 0 p⟩
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
  have hGPart (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) : G (ρ.part keep v m) = G ρ := by
    cases s <;> rfl
  have hBPart (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) : B (ρ.part keep v m) = B ρ := by
    cases t <;> rfl
  have hPartActive (ρ : Context) (keep : List ℕ) (v : Side) (m p : ℕ)
      (hp : p ∈ active (ρ.part keep v m)) : p ∈ active ρ ∧ p ∈ keep := by
    obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
    rw [part_childPositions] at hc
    obtain ⟨hc, hk⟩ := List.mem_filter.mp hc
    have hle := ctx_part_limits_le ρ keep v m p p
    exact ⟨(hActive _ _).mpr ⟨hc, by omega, by omega⟩, by simpa using hk⟩
  have hNoMark (ρ : Context) (p : ℕ) (hp : p ∈ ρ.childPositions) : p ∉ marks ρ := by
    intro hm
    obtain ⟨j, _, hx⟩ := (hMark ρ p).mp hm
    have hc := (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hx).2
    simp only [decide_eq_true_eq] at hc he
    simp [hc] at he
  have hMarksInherit (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      marks ρ ⊆ marks (ρ.part keep v m) := by
    intro p hp
    obtain ⟨j, hj, hp⟩ := (hMark ρ p).mp hp
    have h1 := (one_le_of_mem_levelsOn hj).1
    have hjlevel := (List.mem_filter.mp hj).1
    have hjs : ρ.sideAt j = s := (of_decide_eq_true (List.mem_filter.mp hj).2).1
    apply (hMark _ _).mpr
    refine ⟨j + 1, ?_, ?_⟩
    · apply List.mem_filter.mpr
      constructor
      · rw [part_levels]
        simp [hjlevel]
      · simp [part_sideAt_succ ρ keep v m h1, hjs]
    · rw [part_extPositions_succ ρ keep v m h1]
      exact hp
  have hRank (ρ : Context) (r : ℕ) : r ∈ ranks ρ ↔
      ∃ p ∈ active ρ, L ρ p + 1 ≤ r ∧ r ≤ B ρ - R ρ p := by
    simp [ranks]
  have hRanksInherit (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      ranks (ρ.part keep v m) ⊆ ranks ρ := by
    intro r hr
    obtain ⟨p, hp, hlo, hhi⟩ := (hRank _ _).mp hr
    have he := hInherit ρ keep v m t p
    change L ρ p ≤ L (ρ.part keep v m) p ∧ R ρ p ≤ R (ρ.part keep v m) p at he
    rw [hBPart] at hhi
    exact (hRank _ _).mpr ⟨p, (hPartActive _ _ _ _ _ hp).1, by omega, by omega⟩
  have hOneLeft (ρ : Context) (v : Side) (j p x : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hx : x ∈ ρ.extPositions j) (hxp : x < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : x ∈ (ρ.extPositions j).filter (· < p) := by simp [hx, hxp]
    have hne := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep, List.getLast?_eq_some_getLast hne] using hv
  have hOneRight (ρ : Context) (v : Side) (j p x : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hx : x ∈ ρ.extPositions j) (hpx : p < x) :
      1 ≤ ρ.rightExt v 0 p := by
    have hm : x ∈ (ρ.extPositions j).filter (p < ·) := by simp [hx, hpx]
    have hne := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep, List.head?_eq_some_head hne] using hv
  let lim (ρ : Context) (p : ℕ) := match s with
    | Side.lower => ρ.cupLimit p p
    | Side.upper => ρ.capLimit p p
  have hOwnPure (ρ : Context) (hG : G ρ ≤ 3) (p : ℕ) :
      lim ρ p ≤ 2 - (ρ.leftExt s 0 p + ρ.rightExt s 0 p) := by
    cases s <;> dsimp [lim, G, cupLimit, capLimit, chainExt] at hG ⊢ <;> omega
  have hLimPos (ρ : Context) (p : ℕ) (hp : p ∈ active ρ) : 0 < lim ρ p := by
    have hc := (hActive _ _).mp hp
    cases s <;> dsimp [lim] <;> omega
  have hUnitMarker (ρ : Context) (hG : G ρ ≤ 3) (hm : (marks ρ).Nonempty) :
      ∀ p ∈ ρ.childPositions, lim ρ p ≤ 1 := by
    intro p hp
    obtain ⟨x, hx⟩ := hm
    have hneq : x ≠ p := by intro h; subst x; exact hNoMark ρ p hp hx
    obtain ⟨j, hj, hx⟩ := (hMark _ _).mp hx
    have hlim := hOwnPure ρ hG p
    by_cases hxp : x < p
    · have hleft := hOneLeft ρ s j p x hj hx hxp
      omega
    · have hright := hOneRight ρ s j p x hj hx (by omega)
      omega
  have hExterior (ρ : Context) (hG : G ρ ≤ 3) (p : ℕ) (hp : p ∈ active ρ) :
      (∀ x ∈ marks ρ, x < p) ∨ (∀ x ∈ marks ρ, p < x) := by
    have hpc := ((hActive _ _).mp hp).1
    have hlim := hOwnPure ρ hG p
    have hpos := hLimPos ρ p hp
    by_cases hr : ∃ y ∈ marks ρ, p < y
    · right
      obtain ⟨y, hy, hpy⟩ := hr
      obtain ⟨j, hj, hyj⟩ := (hMark _ _).mp hy
      have hright := hOneRight ρ s j p y hj hyj hpy
      intro x hx
      have hneq : x ≠ p := by intro h; subst x; exact hNoMark ρ p hpc hx
      by_contra hpx
      obtain ⟨i, hi, hxi⟩ := (hMark _ _).mp hx
      have hleft := hOneLeft ρ s i p x hi hxi (by omega)
      omega
    · left
      intro x hx
      have hneq : x ≠ p := by intro h; subst x; exact hNoMark ρ p hpc hx
      have hn : ¬ p < x := fun h => hr ⟨x, hx, h⟩
      omega
  have hOppBudget (ρ : Context) (p : ℕ) (hp : p ∈ active ρ) : L ρ p + R ρ p < B ρ := by
    have hc := (hActive _ _).mp hp
    cases t with
    | lower =>
      change ρ.leftExt Side.lower 0 p + ρ.rightExt Side.lower 0 p < ρ.u - 1
      have hp' := hc.2.1
      dsimp only [cupLimit, chainExt] at hp'
      omega
    | upper =>
      change ρ.leftExt Side.upper 0 p + ρ.rightExt Side.upper 0 p < ρ.a - 1
      have hp' := hc.2.2
      dsimp only [capLimit, chainExt] at hp'
      omega
  have hInterval (ρ : Context) (p : ℕ) (hp : p ∈ active ρ) : L ρ p + 1 ≤ B ρ - R ρ p := by
    have h := hOppBudget ρ p hp
    omega
  have hRankLo (ρ : Context) (p : ℕ) (hp : p ∈ active ρ) : L ρ p + 1 ∈ ranks ρ :=
    (hRank _ _).mpr ⟨p, hp, le_rfl, hInterval ρ p hp⟩
  have hRankHi (ρ : Context) (p : ℕ) (hp : p ∈ active ρ) : B ρ - R ρ p ∈ ranks ρ :=
    (hRank _ _).mpr ⟨p, hp, hInterval ρ p hp, le_rfl⟩
  have hVRank (ρ : Context) : V ρ ≤ (ranks ρ).card := by
    dsimp only [V]
    split_ifs
    · exact le_rfl
    · exact Nat.min_le_right _ _
  have hVReg (ρ : Context) (hm : marks ρ ≠ ∅) : V ρ ≤ reg ρ := by
    dsimp only [V]
    rw [if_neg hm]
    exact Nat.min_le_left _ _
  have hVEmpty (ρ : Context) (ha : active ρ = ∅) : V ρ = 0 := by
    simp [V, ranks, reg, ha]
  have hBudget (ρ : Context) : V ρ ≤ B ρ := by
    have hsub : ranks ρ ⊆ Finset.Icc 1 (B ρ) := by
      intro r hr
      obtain ⟨p, _, hlo, hhi⟩ := (hRank _ _).mp hr
      simp only [Finset.mem_Icc]
      omega
    have hc := Finset.card_le_card hsub
    have hcard : (Finset.Icc 1 (B ρ)).card = B ρ := by simp
    rw [hcard] at hc
    exact (hVRank ρ).trans hc
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
  have hMarksOther (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (v : Side) (m : ℕ) (hv : v ≠ s) :
      marks (ρ.part keep v m) = marks ρ := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases hPartMarks ρ hPos keep v m x hx with hold | ⟨hvs, _, _⟩
      · exact hold
      · exact False.elim (hv hvs)
    · exact hMarksInherit ρ keep v m
  have hPartV (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (hG : G ρ ≤ 3) (keep : List ℕ) (v : Side) (m : ℕ) :
      V (ρ.part keep v m) ≤ V ρ := by
    have hrank := (hVRank (ρ.part keep v m)).trans (Finset.card_le_card (hRanksInherit ρ keep v m))
    by_cases hm : marks ρ = ∅
    · simpa only [V, if_pos hm] using hrank
    · have hn : (marks ρ).Nonempty := Finset.nonempty_iff_ne_empty.mpr hm
      have hnp : (marks (ρ.part keep v m)).Nonempty := hn.mono (hMarksInherit ρ keep v m)
      have hunit := hUnitMarker ρ hG hn
      have hc := ctx_unit_axis_region_potential_additive ρ hPos s hunit [] keep v 0 m
        (by intro p _ hp; simp at hp)
      change reg (ρ.part [] s 0) + reg (ρ.part keep v m) ≤ reg ρ at hc
      have hreg := hVReg (ρ.part keep v m) hnp.ne_empty
      change V (ρ.part keep v m) ≤ if marks ρ = ∅ then (ranks ρ).card else min (reg ρ) (ranks ρ).card
      rw [if_neg hm]
      exact Nat.le_min.mpr ⟨by omega, hrank⟩
  have hPartSide (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (v : Side) (m q : ℕ) (hq : q ∈ ρ.childPositions) (hnot : q ∉ keep) :
      (ρ.part keep v m).sideAt 1 = v := by
    apply part_sideAt_one_of_mem hPos keep v m (q := q)
    rw [part_extPositions_one hPos keep v m]
    exact List.mem_filter.mpr ⟨hq, by simp [hnot]⟩
  have hOtherExt (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (m q p : ℕ) (hq : q ∈ ρ.childPositions) (hnot : q ∉ keep) :
      L (ρ.part keep s m) p = L ρ p ∧ R (ρ.part keep s m) p = R ρ p := by
    have hs := hPartSide ρ hPos keep s m q hq hnot
    have hn : (ρ.part keep s m).sideAt 1 ≠ t := by simpa only [hs] using hne
    exact ⟨(leftExt_part_other hn p).1, (rightExt_part_other hn p).1⟩
  have hMaxWitness : ∀ (xs : List ℕ) (f : List ℕ → ℕ),
      ∃ ls ∈ xs.sublists, ((xs.sublists.map f).max?).getD 0 = f ls := by
    intro xs f
    have hmem : f [] ∈ xs.sublists.map f := List.mem_map.mpr ⟨[], by simp, rfl⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (List.isSome_max?_of_mem hmem)
    obtain ⟨ls, hls, he⟩ := List.mem_map.mp (List.max?_mem hv)
    exact ⟨ls, hls, by simp [hv, he]⟩
  have hReserveLeft (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (v : Side) (m p q : ℕ)
      (hq : q ∈ ρ.childPositions) (hnot : q ∉ keep) (hqp : q < p) :
      ρ.leftExt v 0 q + 1 ≤ (ρ.part keep v m).leftExt v 0 p := by
    let τ := ρ.part keep v m
    let removed := ρ.childPositions.filter (· ∉ keep)
    let xs := removed.filter (· < p)
    have hqxs : q ∈ xs := by simp [xs, removed, hq, hnot, hqp]
    let x := xs.getLast (List.ne_nil_of_mem hqxs)
    have hqx : q ≤ x :=
      ((((childPositions_pairwise ρ).filter _).filter _).imp le_of_lt).rel_getLast hqxs
    have hext : τ.extPositions 1 = removed := part_extPositions_one hPos keep v m
    have hstep : leftStep τ (p, 0) 1 = (x, 1) := by
      simp only [leftStep, hext]
      change (match xs.getLast? with | some y => (y, 0 + 1) | none => (p, 0)) = (x, 1)
      rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hqxs)]
    have hs := hPartSide ρ hPos keep v m q hq hnot
    have hlevels : τ.levelsOn v 0 = 1 :: (ρ.levelsOn v 0).map (· + 1) := part_levelsOn_self_zero hs
    obtain ⟨ls, hls, hval⟩ := hMaxWitness (ρ.levelsOn v 0)
      (fun ls => (ls.foldl (leftStep ρ) (x, 0)).2)
    change ρ.leftExt v 0 x = _ at hval
    have hlspos : ∀ j ∈ ls, 1 ≤ j := fun j hj =>
      (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hj)).1
    have hsub : (1 :: ls.map (· + 1)).Sublist (τ.levelsOn v 0) := by
      rw [hlevels]
      exact ((List.mem_sublists.mp hls).map _).cons₂ 1
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn v 0).sublists.map
      (fun xs => (xs.foldl (leftStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨1 :: ls.map (· + 1), List.mem_sublists.mpr hsub, rfl⟩)
    change _ ≤ τ.leftExt v 0 p at hv
    rw [List.foldl_cons, hstep, foldl_leftStep_part_map ρ keep v m ls hlspos,
      foldl_leftStep_count ρ ls x 1, ← hval] at hv
    have hmono := hLeftMono ρ v 0 q x hqx
    change ρ.leftExt v 0 q + 1 ≤ τ.leftExt v 0 p
    omega
  have hReserveRight (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (v : Side) (m p q : ℕ)
      (hq : q ∈ ρ.childPositions) (hnot : q ∉ keep) (hpq : p < q) :
      ρ.rightExt v 0 q + 1 ≤ (ρ.part keep v m).rightExt v 0 p := by
    let τ := ρ.part keep v m
    let removed := ρ.childPositions.filter (· ∉ keep)
    let xs := removed.filter (p < ·)
    have hqxs : q ∈ xs := by simp [xs, removed, hq, hnot, hpq]
    let x := xs.head (List.ne_nil_of_mem hqxs)
    have hxq : x ≤ q :=
      ((((childPositions_pairwise ρ).filter _).filter _).imp le_of_lt).rel_head hqxs
    have hext : τ.extPositions 1 = removed := part_extPositions_one hPos keep v m
    have hstep : rightStep τ (p, 0) 1 = (x, 1) := by
      simp only [rightStep, hext]
      change (match xs.head? with | some y => (y, 0 + 1) | none => (p, 0)) = (x, 1)
      rw [List.head?_eq_some_head (List.ne_nil_of_mem hqxs)]
    have hs := hPartSide ρ hPos keep v m q hq hnot
    have hlevels : τ.levelsOn v 0 = 1 :: (ρ.levelsOn v 0).map (· + 1) := part_levelsOn_self_zero hs
    obtain ⟨ls, hls, hval⟩ := hMaxWitness (ρ.levelsOn v 0)
      (fun ls => (ls.foldl (rightStep ρ) (x, 0)).2)
    change ρ.rightExt v 0 x = _ at hval
    have hlspos : ∀ j ∈ ls, 1 ≤ j := fun j hj =>
      (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hj)).1
    have hsub : (1 :: ls.map (· + 1)).Sublist (τ.levelsOn v 0) := by
      rw [hlevels]
      exact ((List.mem_sublists.mp hls).map _).cons₂ 1
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn v 0).sublists.map
      (fun xs => (xs.foldl (rightStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨1 :: ls.map (· + 1), List.mem_sublists.mpr hsub, rfl⟩)
    change _ ≤ τ.rightExt v 0 p at hv
    rw [List.foldl_cons, hstep, foldl_rightStep_part_map ρ keep v m ls hlspos,
      foldl_rightStep_count ρ ls x 1, ← hval] at hv
    have hmono := hRightMono ρ v 0 x q hxq
    change ρ.rightExt v 0 q + 1 ≤ τ.rightExt v 0 p
    omega
  have hRegConst (ρ : Context) (c : ℕ)
      (hc : ∀ p ∈ active ρ, ((marks ρ).filter (· < p)).card = c) : reg ρ ≤ 1 := by
    have hs : (active ρ).image (fun p => ((marks ρ).filter (· < p)).card) ⊆ {c} := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      simpa only [Finset.mem_singleton] using hc p hp
    simpa only [Finset.card_singleton] using Finset.card_le_card hs
  have hRegTwo (ρ : Context) (hG : G ρ ≤ 3) : reg ρ ≤ 2 := by
    have hs : (active ρ).image (fun p => ((marks ρ).filter (· < p)).card) ⊆
        {0, (marks ρ).card} := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rcases hExterior ρ hG p hp with hl | hr
      · have he := Finset.filter_eq_self.mpr hl
        simp only [he, Finset.mem_insert, Finset.mem_singleton, or_true]
      · have he : (marks ρ).filter (· < p) = ∅ :=
          Finset.filter_eq_empty_iff.mpr (fun x hx => by have := hr x hx; omega)
        simp only [he, Finset.card_empty, Finset.mem_insert, true_or]
    have hcard : ({0, (marks ρ).card} : Finset ℕ).card ≤ 2 := by
      have h := Finset.card_insert_le 0 ({(marks ρ).card} : Finset ℕ)
      simpa only [Finset.card_singleton] using h
    exact (Finset.card_le_card hs).trans hcard
  have hRegBefore (ρ : Context) (hG : G ρ ≤ 3) (x : ℕ) (hx : x ∈ marks ρ)
      (hbefore : ∀ p ∈ active ρ, p < x) : reg ρ ≤ 1 := by
    apply hRegConst ρ 0
    intro p hp
    rcases hExterior ρ hG p hp with hl | hr
    · have hxp := hl x hx
      have hpx := hbefore p hp
      omega
    · have he : (marks ρ).filter (· < p) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun y hy => by have := hr y hy; omega)
      simp only [he, Finset.card_empty]
  have hRegAfter (ρ : Context) (hG : G ρ ≤ 3) (x : ℕ) (hx : x ∈ marks ρ)
      (hafter : ∀ p ∈ active ρ, x < p) : reg ρ ≤ 1 := by
    apply hRegConst ρ (marks ρ).card
    intro p hp
    rcases hExterior ρ hG p hp with hl | hr
    · rw [Finset.filter_eq_self.mpr hl]
    · have hpx := hr x hx
      have hxp := hafter p hp
      omega
  have hCutRanks (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (hG : G ρ ≤ 3) (keep rest : List ℕ) (m n : ℕ)
      (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
      V (ρ.part keep s m) + V (ρ.part rest t n) ≤ (ranks ρ).card := by
    let α := ρ.part keep s m
    let β := ρ.part rest t n
    change V α + V β ≤ (ranks ρ).card
    by_cases hA : active α = ∅
    · rw [hVEmpty α hA, Nat.zero_add]
      exact (hVRank β).trans (Finset.card_le_card (hRanksInherit ρ rest t n))
    by_cases hB : active β = ∅
    · rw [hVEmpty β hB, Nat.add_zero]
      exact (hVRank α).trans (Finset.card_le_card (hRanksInherit ρ keep s m))
    have hAn : (active α).Nonempty := Finset.nonempty_iff_ne_empty.mpr hA
    obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hB
    have hAold (q : ℕ) (hq : q ∈ active α) : q ∈ active ρ ∧ q ∈ keep :=
      hPartActive ρ keep s m q hq
    have hBold (p : ℕ) (hp : p ∈ active β) : p ∈ active ρ ∧ p ∈ rest :=
      hPartActive ρ rest t n p hp
    have hNotRest (q : ℕ) (hq : q ∈ active α) : q ∉ rest :=
      hdis q ((hActive _ _).mp (hAold q hq).1).1 (hAold q hq).2
    have hNotKeep (p : ℕ) (hp : p ∈ active β) : p ∉ keep := by
      intro hk
      exact hdis p ((hActive _ _).mp (hBold p hp).1).1 hk (hBold p hp).2
    have hp0child := ((hActive _ _).mp (hBold p0 hp0).1).1
    have hs := hPartSide ρ hPos keep s m p0 hp0child (hNotKeep p0 hp0)
    have hMarksB (p : ℕ) (hp : p ∈ active β) : p ∈ marks α := by
      apply (hMark _ _).mpr
      refine ⟨1, ?_, ?_⟩
      · rw [part_levelsOn_self_zero hs]
        simp
      · rw [part_extPositions_one hPos keep s m]
        exact List.mem_filter.mpr ⟨((hActive _ _).mp (hBold p hp).1).1, by simp [hNotKeep p hp]⟩
    have hmp0 := hMarksB p0 hp0
    have hmα : marks α ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨p0, hmp0⟩
    have hGα : G α ≤ 3 := by simpa only [α, hGPart] using hG
    have hVTwo : V α ≤ 2 := (hVReg α hmα).trans (hRegTwo α hGα)
    have hneq (q : ℕ) (hq : q ∈ active α) : q ≠ p0 := by
      intro he
      subst q
      exact hNoMark α p0 ((hActive _ _).mp hq).1 hmp0
    have hBefore (q : ℕ) (hq : q ∈ active α) (hqp : q < p0) :
        ∀ p ∈ active β, q < p := by
      rcases hExterior α hGα q hq with hl | hr
      · have h := hl p0 hmp0
        omega
      · exact fun p hp => hr p (hMarksB p hp)
    have hAfter (q : ℕ) (hq : q ∈ active α) (hpq : p0 < q) :
        ∀ p ∈ active β, p < q := by
      rcases hExterior α hGα q hq with hl | hr
      · exact fun p hp => hl p (hMarksB p hp)
      · have h := hr p0 hmp0
        omega
    have hLoExclude (q : ℕ) (hq : q ∈ active α) (hbefore : ∀ p ∈ active β, q < p) :
        L ρ q + 1 ∉ ranks β := by
      intro hrank
      obtain ⟨p, hp, hlo, _⟩ := (hRank _ _).mp hrank
      have he := hReserveLeft ρ hPos rest t n p q
        ((hActive _ _).mp (hAold q hq).1).1 (hNotRest q hq) (hbefore p hp)
      change L ρ q + 1 ≤ L β p at he
      omega
    have hHiExclude (q : ℕ) (hq : q ∈ active α) (hafter : ∀ p ∈ active β, p < q) :
        B ρ - R ρ q ∉ ranks β := by
      intro hrank
      obtain ⟨p, hp, _, hhi⟩ := (hRank _ _).mp hrank
      have he := hReserveRight ρ hPos rest t n p q
        ((hActive _ _).mp (hAold q hq).1).1 (hNotRest q hq) (hafter p hp)
      change R ρ q + 1 ≤ R β p at he
      have hb : B β = B ρ := hBPart ρ rest t n
      rw [hb] at hhi
      have hbudget := hOppBudget ρ q (hAold q hq).1
      omega
    have hCount (S : Finset ℕ) (hS : S ⊆ ranks ρ) (hSR : Disjoint S (ranks β)) :
        S.card + (ranks β).card ≤ (ranks ρ).card := by
      have hc := Finset.card_le_card (Finset.union_subset hS (hRanksInherit ρ rest t n))
      rw [Finset.card_union_of_disjoint hSR] at hc
      exact hc
    have hOneCount (r : ℕ) (hr : r ∈ ranks ρ) (hn : r ∉ ranks β) :
        1 + (ranks β).card ≤ (ranks ρ).card := by
      have hS : ({r} : Finset ℕ) ⊆ ranks ρ := by
        intro x hx
        have he := Finset.mem_singleton.mp hx
        subst x
        exact hr
      have hd : Disjoint ({r} : Finset ℕ) (ranks β) := by
        apply Finset.disjoint_left.mpr
        intro x hx hxR
        have he := Finset.mem_singleton.mp hx
        subst x
        exact hn hxR
      simpa only [Finset.card_singleton] using hCount {r} hS hd
    have hVB := hVRank β
    by_cases hsmallV : V α ≤ 1
    · obtain ⟨q, hq⟩ := hAn
      by_cases hqp : q < p0
      · have hc := hOneCount (L ρ q + 1) (hRankLo ρ q (hAold q hq).1)
          (hLoExclude q hq (hBefore q hq hqp))
        omega
      · have hpq : p0 < q := by have := hneq q hq; omega
        have hc := hOneCount (B ρ - R ρ q) (hRankHi ρ q (hAold q hq).1)
          (hHiExclude q hq (hAfter q hq hpq))
        omega
    have hVA : V α = 2 := by omega
    let qL := (active α).min' hAn
    let qR := (active α).max' hAn
    have hqL : qL ∈ active α := Finset.min'_mem _ hAn
    have hqR : qR ∈ active α := Finset.max'_mem _ hAn
    have hmin (q : ℕ) (hq : q ∈ active α) : qL ≤ q := Finset.min'_le _ q hq
    have hmax (q : ℕ) (hq : q ∈ active α) : q ≤ qR := Finset.le_max' _ q hq
    have hqLp : qL < p0 := by
      by_contra hn
      have hpq : p0 < qL := by have := hneq qL hqL; omega
      have hc := hRegAfter α hGα p0 hmp0 (fun q hq => lt_of_lt_of_le hpq (hmin q hq))
      have hv := hVReg α hmα
      omega
    have hpqR : p0 < qR := by
      by_contra hn
      have hqp : qR < p0 := by have := hneq qR hqR; omega
      have hc := hRegBefore α hGα p0 hmp0 (fun q hq => lt_of_le_of_lt (hmax q hq) hqp)
      have hv := hVReg α hmα
      omega
    let rL := L ρ qL + 1
    let rR := B ρ - R ρ qR
    have hrL : rL ∈ ranks ρ := hRankLo ρ qL (hAold qL hqL).1
    have hrR : rR ∈ ranks ρ := hRankHi ρ qR (hAold qR hqR).1
    have hnL : rL ∉ ranks β := hLoExclude qL hqL (hBefore qL hqL hqLp)
    have hnR : rR ∉ ranks β := hHiExclude qR hqR (hAfter qR hqR hpqR)
    have hBounds (r : ℕ) (hr : r ∈ ranks α) : rL ≤ r ∧ r ≤ rR := by
      obtain ⟨q, hq, hlo, hhi⟩ := (hRank _ _).mp hr
      have he := hOtherExt ρ hPos keep m p0 q hp0child (hNotKeep p0 hp0)
      change L α q = L ρ q ∧ R α q = R ρ q at he
      rw [he.1] at hlo
      rw [he.2, show B α = B ρ from hBPart ρ keep s m] at hhi
      have hl := hLeftMono ρ t 0 qL q (hmin q hq)
      have hh := hRightMono ρ t 0 q qR (hmax q hq)
      change L ρ qL ≤ L ρ q at hl
      change R ρ qR ≤ R ρ q at hh
      dsimp only [rL, rR]
      omega
    have hrlr : rL < rR := by
      by_contra hn
      have hsub : ranks α ⊆ {rL} := by
        intro r hr
        have hb := hBounds r hr
        simp only [Finset.mem_singleton]
        omega
      have hc := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hc
      have hv := hVRank α
      omega
    have hsub : ({rL, rR} : Finset ℕ) ⊆ ranks ρ := by
      intro r hr
      rcases Finset.mem_insert.mp hr with he | hr
      · simpa only [he] using hrL
      · simpa only [Finset.mem_singleton.mp hr] using hrR
    have hdisj : Disjoint ({rL, rR} : Finset ℕ) (ranks β) := by
      apply Finset.disjoint_left.mpr
      intro r hr hb
      rcases Finset.mem_insert.mp hr with he | hr
      · subst r
        exact hnL hb
      · have he := Finset.mem_singleton.mp hr
        subst r
        exact hnR hb
    have hc := hCount {rL, rR} hsub hdisj
    have he : ({rL, rR} : Finset ℕ).card = 2 := by simp [ne_of_lt hrlr]
    rw [he] at hc
    omega
  have hCut (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (hG : G ρ ≤ 3) (keep rest : List ℕ) (m n : ℕ)
      (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
      V (ρ.part keep s m) + V (ρ.part rest t n) ≤ V ρ := by
    have hRankSum := hCutRanks ρ hPos hG keep rest m n hdis
    by_cases hm : marks ρ = ∅
    · simpa only [V, if_pos hm] using hRankSum
    · have hmn := Finset.nonempty_iff_ne_empty.mpr hm
      have hma := hmn.mono (hMarksInherit ρ keep s m)
      have hmb := hmn.mono (hMarksInherit ρ rest t n)
      have hreg := ctx_unit_axis_region_potential_additive ρ hPos s
        (hUnitMarker ρ hG hmn) keep rest t m n hdis
      change reg (ρ.part keep s m) + reg (ρ.part rest t n) ≤ reg ρ at hreg
      have ha := hVReg (ρ.part keep s m) hma.ne_empty
      have hb := hVReg (ρ.part rest t n) hmb.ne_empty
      change V (ρ.part keep s m) + V (ρ.part rest t n) ≤
        if marks ρ = ∅ then (ranks ρ).card else min (reg ρ) (ranks ρ).card
      rw [if_neg hm]
      exact Nat.le_min.mpr ⟨by omega, hRankSum⟩
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
  have hBase (ρ : Context) (hG : G ρ ≤ 3) : ρ.base ≤ V ρ := by
    rw [base_eq_baseOf]
    cases hh : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      by_cases hz : ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0
      · simp [baseOf, hz]
      have hpos : 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by omega
      have ha : p ∈ active ρ := (hActive _ _).mpr ⟨hp, hpos⟩
      have hlim : lim ρ p ≤ 2 := (hOwnPure ρ hG p).trans (Nat.sub_le _ _)
      have hcupk : ρ.cupLimit p p ≤ ρ.k - 1 := by dsimp only [cupLimit]; omega
      have hcapk : ρ.capLimit p p ≤ ρ.k - 1 := by dsimp only [capLimit]; omega
      have hOpp : baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤
          opp ρ p := by
        cases s <;> cases t
        · exact False.elim (hne rfl)
        · exact hBaseLower _ _ _ hlim hcapk
        · exact hBaseUpper _ _ _ hlim hcupk
        · exact False.elim (hne rfl)
      have hwidth : opp ρ p ≤
          B ρ - R ρ p - L ρ p := by
        cases t <;> dsimp only [opp, B, L, R, cupLimit, capLimit, chainExt] <;> omega
      have hsub : Finset.Icc (L ρ p + 1) (B ρ - R ρ p) ⊆ ranks ρ := by
        intro r hr
        have hh := Finset.mem_Icc.mp hr
        exact (hRank _ _).mpr ⟨p, ha, hh⟩
      have hcard := Finset.card_le_card hsub
      have hsize : (Finset.Icc (L ρ p + 1) (B ρ - R ρ p)).card = B ρ - R ρ p - L ρ p := by
        simp
      rw [hsize] at hcard
      have hbrank := hOpp.trans (hwidth.trans hcard)
      by_cases hm : marks ρ = ∅
      · simpa only [V, if_pos hm] using hbrank
      · have hunit := hUnitMarker ρ hG (Finset.nonempty_iff_ne_empty.mpr hm) p hp
        have hone : ρ.cupLimit p p = 1 ∨ ρ.capLimit p p = 1 := by
          cases s <;> dsimp only [lim] at hunit <;> omega
        have hn : ((active ρ).image (fun q => ((marks ρ).filter (· < q)).card)).Nonempty :=
          ⟨_, Finset.mem_image.mpr ⟨p, ha, rfl⟩⟩
        have hreg : 1 ≤ reg ρ := Finset.card_pos.mpr hn
        have hbreg : baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ reg ρ := by
          simpa only [baseOf, if_neg hz, if_pos hone] using hreg
        change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤
          if marks ρ = ∅ then (ranks ρ).card else min (reg ρ) (ranks ρ).card
        rw [if_neg hm]
        exact Nat.le_min.mpr ⟨hbreg, hbrank⟩
  have hCutLR (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (hG : G ρ ≤ 3) (keep rest : List ℕ) (m n : ℕ)
      (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
      V (ρ.part keep Side.lower m) + V (ρ.part rest Side.upper n) ≤ V ρ := by
    have hrev : ∀ p ∈ ρ.childPositions, p ∈ rest → p ∉ keep := by
      intro p hp hr hk
      exact hdis p hp hk hr
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · exact hCut ρ hPos hG keep rest m n hdis
    · simpa only [Nat.add_comm] using hCut ρ hPos hG rest keep n m hrev
    · exact False.elim (hne rfl)
  have hFuel : ∀ fuel (ρ : Context),
      (∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j) →
      G ρ ≤ 3 → boundFuel fuel ρ ≤ V ρ := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hPos hG
      rw [boundFuel]
      split
      · exact hBase ρ hG
      · apply Ctx.getD_max?_le
        intro x hx
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨keep, _, d, _, hx⟩ := hx
        have hparts (keep : List ℕ) (v : Side) (m : ℕ) :
            boundFuel fuel (ρ.part keep v m) ≤ V (ρ.part keep v m) :=
          ih _ (hPositivePart ρ keep v m) (by simpa only [hGPart] using hG)
        rcases hx with rfl | rfl
        · apply (Nat.add_le_add (hparts _ _ _) (hparts _ _ _)).trans
          apply hCutLR ρ hPos hG
          intro p _ hp hr
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hr).2
          exact hn hp
        · apply (Nat.add_le_add (hparts _ _ _) (hparts _ _ _)).trans
          rw [Nat.add_comm]
          apply hCutLR ρ hPos hG
          intro p _ hp hk
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hp).2
          exact hn hk
  exact ⟨fun fuel => hFuel fuel σ hpositive hsmall, hFuel _ σ hpositive hsmall,
    hBudget σ, fun keep rest m n hdis => hCut σ hpositive hsmall keep rest m n hdis⟩

end ErdosSzekeres
