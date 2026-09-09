import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank

set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Distinct rank reservations for a tracked active subset in a part. A source-active finite support F contains a part-active subset Q. Removed source-active left/right witness sets lie strictly on the indicated side of every tracked part child. Their lower/upper source rank endpoints belong to the source rank union and are all excluded from the part rank union, yielding a cardinal decrease by the number of distinct reserved ranks. If a left endpoint meets or crosses a right endpoint, Q is empty. Allows arbitrary global parameters, positive indexed histories, kept sets and new maxima, inactive untracked children and disconnected rank unions. Supplies one- and two-sided nonunit-rank charges for the all-unit retained-part branch of the singleton-end sandwich mixed potential, without double-counting coincident endpoints or assuming every companion active child is nonunit.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_part_tracked_rank_reservation (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s : Ctx.Side) (keep : List ℕ) (m : ℕ) (F Q L R : Finset ℕ)
  (hF : ∀ p ∈ F, p ∈ σ.childPositions ∧ 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  (hQ : ∀ p ∈ Q, p ∈ (σ.part keep s m).childPositions ∧
    0 < (σ.part keep s m).cupLimit p p ∧ 0 < (σ.part keep s m).capLimit p p)
  (hQF : Q ⊆ F)
  (hL : ∀ p ∈ L, p ∈ F ∧ p ∉ keep)
  (hR : ∀ p ∈ R, p ∈ F ∧ p ∉ keep)
  (hleft : ∀ p ∈ L, ∀ q ∈ Q, p < q)
  (hright : ∀ p ∈ R, ∀ q ∈ Q, q < p) :
  let global := fun (ρ : Ctx.Context) (v : Ctx.Side) =>
    match v with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let rankInterval := fun (ρ : Ctx.Context) (p : ℕ) =>
    Finset.Icc (ρ.leftExt s 0 p + 1) (global ρ s - 1 - ρ.rightExt s 0 p)
  let sourceRanks := F.biUnion (rankInterval σ)
  let partRanks := Q.biUnion (rankInterval (σ.part keep s m))
  let reserved := (L.image (fun p => σ.leftExt s 0 p + 1)) ∪
    (R.image (fun p => global σ s - 1 - σ.rightExt s 0 p))
  (reserved ⊆ sourceRanks) ∧ (partRanks ⊆ sourceRanks \ reserved) ∧
    partRanks.card + reserved.card ≤ sourceRanks.card ∧
    ((∃ p ∈ L, ∃ q ∈ R,
      global σ s - 1 - σ.rightExt s 0 q ≤ σ.leftExt s 0 p + 1) → Q = ∅) := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let budget (ρ : Context) := G ρ s - 1
  let I (ρ : Context) (p : ℕ) := Finset.Icc (ρ.leftExt s 0 p + 1) (budget ρ - ρ.rightExt s 0 p)
  let τ := σ.part keep s m
  let S := F.biUnion (I σ)
  let T := Q.biUnion (I τ)
  let E := (L.image (fun p => σ.leftExt s 0 p + 1)) ∪
    (R.image (fun p => budget σ - σ.rightExt s 0 p))
  change E ⊆ S ∧ T ⊆ S \ E ∧ T.card + E.card ≤ S.card ∧
    ((∃ p ∈ L, ∃ q ∈ R, budget σ - σ.rightExt s 0 q ≤ σ.leftExt s 0 p + 1) → Q = ∅)
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
  have hPartSide (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (v : Side) (m q : ℕ) (hq : q ∈ ρ.childPositions) (hnot : q ∉ keep) :
      (ρ.part keep v m).sideAt 1 = v := by
    apply part_sideAt_one_of_mem hPos keep v m (q := q)
    rw [part_extPositions_one hPos keep v m]
    exact List.mem_filter.mpr ⟨hq, by simp [hnot]⟩
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
  have hBudget : budget τ = budget σ := by cases s <;> rfl
  have hPurePositive (ρ : Context) (p : ℕ)
      (hp : 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) :
      ρ.leftExt s 0 p + ρ.rightExt s 0 p < budget ρ := by
    cases s <;> simp only [budget, G, cupLimit, capLimit, chainExt] at hp ⊢ <;> omega
  have hSourceEnds (p : ℕ) (hp : p ∈ F) :
      σ.leftExt s 0 p + 1 ∈ S ∧ budget σ - σ.rightExt s 0 p ∈ S := by
    have hpos := hPurePositive σ p (hF p hp).2
    constructor <;> apply Finset.mem_biUnion.mpr <;> refine ⟨p, hp, ?_⟩ <;>
      apply Finset.mem_Icc.mpr <;> constructor <;> omega
  have hReserved : E ⊆ S := by
    intro z hz
    rcases Finset.mem_union.mp hz with hl | hr
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hl
      exact (hSourceEnds p (hL p hp).1).1
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
      exact (hSourceEnds p (hR p hp).1).2
  have hPartSubset : T ⊆ S := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    have hi := hInherit σ keep s m s p
    have hh := Finset.mem_Icc.mp hz
    change τ.leftExt s 0 p + 1 ≤ z ∧ z ≤ budget τ - τ.rightExt s 0 p at hh
    rw [hBudget] at hh
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hQF hp, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · change σ.leftExt s 0 p + 1 ≤ z
      change σ.leftExt s 0 p ≤ τ.leftExt s 0 p ∧ σ.rightExt s 0 p ≤ τ.rightExt s 0 p at hi
      omega
    · change z ≤ budget σ - σ.rightExt s 0 p
      change σ.leftExt s 0 p ≤ τ.leftExt s 0 p ∧ σ.rightExt s 0 p ≤ τ.rightExt s 0 p at hi
      omega
  have hAvoidLeft (p : ℕ) (hp : p ∈ Q) (z : ℕ) (hz : z ∈ I τ p)
      (q : ℕ) (hq : q ∈ L) : σ.leftExt s 0 q + 1 < z := by
    have hqF := (hL q hq).1
    have hg := hReserveLeft σ hpositive keep s m p q (hF q hqF).1
      (hL q hq).2 (hleft q hq p hp)
    have hh := (Finset.mem_Icc.mp hz).1
    change τ.leftExt s 0 p + 1 ≤ z at hh
    change σ.leftExt s 0 q + 1 ≤ τ.leftExt s 0 p at hg
    omega
  have hAvoidRight (p : ℕ) (hp : p ∈ Q) (z : ℕ) (hz : z ∈ I τ p)
      (q : ℕ) (hq : q ∈ R) : z < budget σ - σ.rightExt s 0 q := by
    have hqF := (hR q hq).1
    have hg := hReserveRight σ hpositive keep s m p q (hF q hqF).1
      (hR q hq).2 (hright q hq p hp)
    have hh := Finset.mem_Icc.mp hz
    change τ.leftExt s 0 p + 1 ≤ z ∧ z ≤ budget τ - τ.rightExt s 0 p at hh
    rw [hBudget] at hh
    change σ.rightExt s 0 q + 1 ≤ τ.rightExt s 0 p at hg
    omega
  have hDisjoint : Disjoint T E := by
    apply Finset.disjoint_left.mpr
    intro z hz he
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    rcases Finset.mem_union.mp he with hl | hr
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hl
      exact (Nat.lt_irrefl _) (hAvoidLeft p hp _ hz q hq)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
      exact (Nat.lt_irrefl _) (hAvoidRight p hp _ hz q hq)
  have hDifference : T ⊆ S \ E := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨hPartSubset hz, fun he => (Finset.disjoint_left.mp hDisjoint) hz he⟩
  have hCard : T.card + E.card ≤ S.card := by
    have hh := Finset.card_le_card (Finset.union_subset hPartSubset hReserved)
    rw [Finset.card_union_of_disjoint hDisjoint] at hh
    exact hh
  refine ⟨hReserved, hDifference, hCard, ?_⟩
  rintro ⟨p, hp, q, hq, hcross⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hpos := hPurePositive τ w (hQ w hw).2
  have hz : τ.leftExt s 0 w + 1 ∈ I τ w := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hl := hAvoidLeft w hw _ hz p hp
  have hr := hAvoidRight w hw _ hz q hq
  omega


end ErdosSzekeres
