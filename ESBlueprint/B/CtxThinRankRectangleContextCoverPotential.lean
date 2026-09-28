import ESBlueprint.B.CtxBoundAttainedByEndCut
import ESBlueprint.B.CtxThinRankRectangleIntervalDimensionCoverTransfer
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Bound every fuel approximation and the full context recurrence by the summed dimension costs of any finite list cover of active pure-rank rectangles, assuming each chosen interval has at most two ranks. The proof transfers each source cluster across either orientation of an interval cut and uses fuel induction. All physical external labels are positive; the two axes are distinct. Every active child has at most two allowed pure ranks on the chosen axis. Indexed history, maxima and inactive children are otherwise arbitrary. The cover contains only active child positions and covers every active child. No recursive bound or potential premise is assumed.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_thin_rank_rectangle_context_cover_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t)
  (hthin : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt s 0 p ≤
      σ.leftExt s 0 p + 2) :
  let active := σ.childPositions.toFinset.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks := fun (v : Ctx.Side) p => Finset.Icc (σ.leftExt v 0 p + 1)
    ((match v with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt v 0 p)
  let cost := fun (I : Finset ℕ) => if I = ∅ then 0 else
    ((I.biUnion (ranks s)).card - 1) * ((I.biUnion (ranks t)).card - 1) + 1
  ∀ cover : List (Finset ℕ),
    (∀ p ∈ active, ∃ I ∈ cover, p ∈ I) → (∀ I ∈ cover, I ⊆ active) →
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (cover.map cost).sum) ∧
      σ.bound ≤ (cover.map cost).sum := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let active (ρ : Context) : Finset ℕ := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let lo (ρ : Context) (v : Side) (p : ℕ) := ρ.leftExt v 0 p + 1
  let hi (ρ : Context) (v : Side) (p : ℕ) := G ρ v - 1 - ρ.rightExt v 0 p
  let ranks (ρ : Context) (v : Side) (p : ℕ) := Finset.Icc (lo ρ v p) (hi ρ v p)
  let cost (I : Finset ℕ) (U V : ℕ → Finset ℕ) := if I = ∅ then 0 else
    ((I.biUnion U).card - 1) * ((I.biUnion V).card - 1) + 1
  let W (ρ : Context) (I : Finset ℕ) := cost I (ranks ρ s) (ranks ρ t)
  let Thin (ρ : Context) := ∀ p ∈ active ρ, hi ρ s p ≤ lo ρ s p + 1
  let Covers (ρ : Context) (cover : List (Finset ℕ)) :=
    (∀ p ∈ active ρ, ∃ I ∈ cover, p ∈ I) ∧ (∀ I ∈ cover, I ⊆ active ρ)
  let Convex (ρ : Context) (ks : List ℕ) := ∀ a ∈ ks, ∀ b ∈ ks,
    ∀ z ∈ ρ.childPositions, a ≤ z → z ≤ b → z ∈ ks
  change ∀ cover : List (Finset ℕ),
    (∀ p ∈ active σ, ∃ I ∈ cover, p ∈ I) → (∀ I ∈ cover, I ⊆ active σ) →
    (∀ fuel, boundFuel fuel σ ≤ (cover.map (W σ)).sum) ∧ σ.bound ≤ (cover.map (W σ)).sum
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by simp [active]
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
  have hPartActive (ρ : Context) (keep : List ℕ) (v : Side) (m p : ℕ)
      (hp : p ∈ active (ρ.part keep v m)) : p ∈ active ρ ∧ p ∈ keep := by
    obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
    rw [part_childPositions] at hc
    obtain ⟨hc, hk⟩ := List.mem_filter.mp hc
    have hle := ctx_part_limits_le ρ keep v m p p
    exact ⟨(hActive _ _).mpr ⟨hc, by omega, by omega⟩, by simpa using hk⟩
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
  have hBlockConvex (ρ : Context) (ks : List ℕ) (hk : ks ∈ ρ.blocks) : Convex ρ ks := by
    obtain ⟨i, l, _, _, hwindow⟩ := exists_take_drop_of_mem_blocks hk
    have hinfix : ks <:+: ρ.childPositions := by
      refine ⟨ρ.childPositions.take i, (ρ.childPositions.drop i).drop (l+1), ?_⟩
      rw [hwindow, List.append_assoc, List.take_append_drop, List.take_append_drop]
    obtain ⟨pre, post, he⟩ := hinfix
    have he' : pre ++ (ks ++ post) = ρ.childPositions := by simpa only [List.append_assoc] using he
    have hs : (pre ++ (ks ++ post)).Pairwise (· < ·) := by
      rw [he']
      exact childPositions_pairwise ρ
    have hbefore : ∀ a ∈ pre, ∀ b ∈ ks, a < b := by
      intro a ha b hb
      exact (List.pairwise_append.mp hs).2.2 a ha b (List.mem_append_left post hb)
    have hafter : ∀ a ∈ ks, ∀ b ∈ post, a < b :=
      (List.pairwise_append.mp (List.pairwise_append.mp hs).2.1).2.2
    intro a ha b hb z hz haz hzb
    rw [← he'] at hz
    rcases List.mem_append.mp hz with hz | hz
    · have hh := hbefore z hz a ha
      omega
    · rcases List.mem_append.mp hz with hz | hz
      · exact hz
      · have hh := hafter b hb z hz
        omega
  have hGPart (ρ : Context) (keep : List ℕ) (v u : Side) (m : ℕ) :
      G (ρ.part keep v m) u = G ρ u := by cases u <;> rfl
  have hInterval (ρ : Context) (v : Side) (p : ℕ) (hp : p ∈ active ρ) :
      lo ρ v p ≤ hi ρ v p := by
    have hc := (hActive ρ p).mp hp
    cases v <;> dsimp only [lo, hi, G, cupLimit, capLimit, chainExt] at hc ⊢ <;> omega
  have hRanksNonempty (ρ : Context) (v : Side) (p : ℕ) (hp : p ∈ active ρ) :
      (ranks ρ v p).Nonempty :=
    ⟨lo ρ v p, Finset.mem_Icc.mpr ⟨le_rfl, hInterval ρ v p hp⟩⟩
  have hEndpointsInherit (ρ : Context) (keep : List ℕ) (v u : Side) (m p : ℕ) :
      lo ρ u p ≤ lo (ρ.part keep v m) u p ∧ hi (ρ.part keep v m) u p ≤ hi ρ u p := by
    have hh := hInherit ρ keep v m u p
    dsimp only [lo, hi]
    rw [hGPart]
    omega
  have hRanksInherit (ρ : Context) (keep : List ℕ) (v u : Side) (m p : ℕ) :
      ranks (ρ.part keep v m) u p ⊆ ranks ρ u p := by
    intro z hz
    have hh := hEndpointsInherit ρ keep v u m p
    have hz' := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hThinPart (ρ : Context) (hThin : Thin ρ) (keep : List ℕ) (v : Side) (m : ℕ) :
      Thin (ρ.part keep v m) := by
    intro p hp
    have hs := hThin p (hPartActive ρ keep v m p hp).1
    have he := hEndpointsInherit ρ keep v s m p
    omega
  have hCoordinatesMono (ρ : Context) (p q : ℕ) (hpq : p ≤ q) :
      lo ρ s p ≤ lo ρ s q ∧ hi ρ s p ≤ hi ρ s q ∧
      lo ρ t p ≤ lo ρ t q ∧ hi ρ t p ≤ hi ρ t q := by
    have hsl := hLeftMono ρ s 0 p q hpq
    have hsr := hRightMono ρ s 0 p q hpq
    have htl := hLeftMono ρ t 0 p q hpq
    have htr := hRightMono ρ t 0 p q hpq
    dsimp only [lo, hi]
    omega
  have hCostMono (I J : Finset ℕ) (U V U' V' : ℕ → Finset ℕ)
      (hIJ : I ⊆ J) (hU : ∀ p ∈ I, U p ⊆ U' p) (hV : ∀ p ∈ I, V p ⊆ V' p) :
      cost I U V ≤ cost J U' V' := by
    by_cases hI : I = ∅
    · simp only [cost, hI, if_pos rfl]
      exact Nat.zero_le _
    have hJ : J ≠ ∅ := by
      intro he
      apply hI
      exact Finset.subset_empty.mp (by simpa only [he] using hIJ)
    have hu : I.biUnion U ⊆ J.biUnion U' := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      exact Finset.mem_biUnion.mpr ⟨p, hIJ hp, hU p hp hz⟩
    have hv : I.biUnion V ⊆ J.biUnion V' := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      exact Finset.mem_biUnion.mpr ⟨p, hIJ hp, hV p hp hz⟩
    have huc := Finset.card_le_card hu
    have hvc := Finset.card_le_card hv
    simp only [cost, if_neg hI, if_neg hJ]
    exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1
  have hBase (ρ : Context) (hThin : Thin ρ) (cover : List (Finset ℕ))
      (hCover : Covers ρ cover) : ρ.base ≤ (cover.map (W ρ)).sum := by
    rw [base_eq_baseOf]
    cases hh : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      by_cases hz : ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0
      · simp [baseOf, hz]
      have hpos : 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by omega
      have ha : p ∈ active ρ := (hActive _ _).mpr ⟨hp, hpos⟩
      obtain ⟨I, hI, hpI⟩ := hCover.1 p ha
      have hCard (v : Side) : (ranks ρ v p).card = hi ρ v p + 1 - lo ρ v p := by
        exact Nat.card_Icc _ _
      have hChosenSize : (ranks ρ s p).card ≤ 2 := by
        have ht := hThin p ha
        rw [hCard]
        omega
      have hLimRank (v : Side) :
          (match v with | Side.lower => ρ.cupLimit p p | Side.upper => ρ.capLimit p p) ≤
            (ranks ρ v p).card := by
        rw [hCard]
        cases v <;> dsimp only [hi, lo, G, cupLimit, capLimit, chainExt] <;> omega
      have hxPos := Finset.card_pos.mpr (hRanksNonempty ρ s p ha)
      have hyPos := Finset.card_pos.mpr (hRanksNonempty ρ t p ha)
      have hcupk : ρ.cupLimit p p ≤ ρ.k - 1 := by dsimp only [cupLimit]; omega
      have hcapk : ρ.capLimit p p ≤ ρ.k - 1 := by dsimp only [capLimit]; omega
      have hLeaf : baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ W ρ {p} := by
        change _ ≤ cost {p} (ranks ρ s) (ranks ρ t)
        simp only [cost, Finset.singleton_ne_empty, if_false, Finset.singleton_biUnion]
        by_cases hx : (ranks ρ s p).card = 1
        · have hlim := hLimRank s
          have hone : ρ.cupLimit p p = 1 ∨ ρ.capLimit p p = 1 := by
            cases s <;> simp only at hlim <;> omega
          simp only [hx, Nat.sub_self, Nat.zero_mul, Nat.zero_add, baseOf, if_neg hz, if_pos hone]
          exact le_rfl
        · have hx2 : (ranks ρ s p).card = 2 := by omega
          have hlim := (hLimRank s).trans hChosenSize
          have hother : baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤
              (match t with | Side.lower => ρ.cupLimit p p | Side.upper => ρ.capLimit p p) := by
            cases s <;> cases t
            · exact False.elim (hne rfl)
            · exact hBaseLower _ _ _ hlim hcapk
            · exact hBaseUpper _ _ _ hlim hcupk
            · exact False.elim (hne rfl)
          have hh : baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ (ranks ρ t p).card := by
            cases t
            · exact hother.trans (hLimRank Side.lower)
            · exact hother.trans (hLimRank Side.upper)
          simp only [hx2, Nat.reduceSub, Nat.one_mul]
          omega
      have hSubset : ({p} : Finset ℕ) ⊆ I := by simpa only [Finset.singleton_subset_iff] using hpI
      have hMono := hCostMono {p} I (ranks ρ s) (ranks ρ t) (ranks ρ s) (ranks ρ t)
        hSubset (fun _ _ => Finset.Subset.refl _) (fun _ _ => Finset.Subset.refl _)
      have hsum : W ρ I ≤ (cover.map (W ρ)).sum :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨I, hI, rfl⟩)
      exact hLeaf.trans (hMono.trans hsum)
  have hLocalCut (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hThin : Thin ρ) (keep : List ℕ) (hConvex : Convex ρ keep)
      (chosenInterval : Bool) (m n : ℕ) (S : Finset ℕ) (hS : S ⊆ active ρ) :
      let rest := ρ.childPositions.filter (· ∉ keep)
      let α := ρ.part (if chosenInterval then keep else rest) s m
      let β := ρ.part (if chosenInterval then rest else keep) t n
      ∃ CA CB : List (Finset ℕ),
        (∀ p ∈ S ∩ active α, ∃ I ∈ CA, p ∈ I) ∧ (∀ I ∈ CA, I ⊆ S ∩ active α) ∧
        (∀ p ∈ S ∩ active β, ∃ I ∈ CB, p ∈ I) ∧ (∀ I ∈ CB, I ⊆ S ∩ active β) ∧
        (CA.map (W α)).sum + (CB.map (W β)).sum ≤ W ρ S := by
    let rest := ρ.childPositions.filter (· ∉ keep)
    let chosenKeep := if chosenInterval then keep else rest
    let oppositeKeep := if chosenInterval then rest else keep
    let α := ρ.part chosenKeep s m
    let β := ρ.part oppositeKeep t n
    let K := S ∩ keep.toFinset
    let A := S ∩ active α
    let B := S ∩ active β
    have hSource (p : ℕ) (hp : p ∈ S) :
        lo ρ s p ≤ hi ρ s p ∧ lo ρ t p ≤ hi ρ t p ∧ hi ρ s p ≤ lo ρ s p + 1 :=
      ⟨hInterval ρ s p (hS hp), hInterval ρ t p (hS hp), hThin p (hS hp)⟩
    have hChild (p : ℕ) (hp : p ∈ S) : p ∈ ρ.childPositions := ((hActive _ _).mp (hS hp)).1
    have hChosenMem (p : ℕ) (hp : p ∈ S) :
        p ∈ chosenKeep ↔ p ∈ (if chosenInterval then K else S \ K) := by
      have hc := hChild p hp
      cases chosenInterval <;> simp [chosenKeep, rest, K, hp, hc]
    have hOppositeMem (p : ℕ) (hp : p ∈ S) :
        p ∈ oppositeKeep ↔ p ∈ (if chosenInterval then S \ K else K) := by
      have hc := hChild p hp
      cases chosenInterval <;> simp [oppositeKeep, rest, K, hp, hc]
    have hA : A ⊆ if chosenInterval then K else S \ K := by
      intro p hp
      have hp' := Finset.mem_inter.mp hp
      have hh := (hPartActive ρ chosenKeep s m p hp'.2).2
      exact (hChosenMem p hp'.1).mp hh
    have hB : B ⊆ if chosenInterval then S \ K else K := by
      intro p hp
      have hp' := Finset.mem_inter.mp hp
      have hh := (hPartActive ρ oppositeKeep t n p hp'.2).2
      exact (hOppositeMem p hp'.1).mp hh
    have hKS : K ⊆ S := Finset.inter_subset_left
    have hFiniteConvex : ∀ p ∈ K, ∀ q ∈ K, ∀ r ∈ S, p ≤ r → r ≤ q → r ∈ K := by
      intro p hp q hq r hr hpr hrq
      have hpk : p ∈ keep := List.mem_toFinset.mp (Finset.mem_inter.mp hp).2
      have hqk : q ∈ keep := List.mem_toFinset.mp (Finset.mem_inter.mp hq).2
      exact Finset.mem_inter.mpr ⟨hr, List.mem_toFinset.mpr (hConvex p hpk q hqk r (hChild r hr) hpr hrq)⟩
    have hRemovedA (q : ℕ) (hq : q ∈ (if chosenInterval then S \ K else K)) :
        q ∈ ρ.childPositions ∧ q ∉ chosenKeep := by
      have hqS : q ∈ S := by
        cases chosenInterval
        · exact hKS hq
        · exact (Finset.mem_sdiff.mp hq).1
      refine ⟨hChild q hqS, ?_⟩
      intro hqC
      have hh := (hChosenMem q hqS).mp hqC
      cases chosenInterval
      · exact (Finset.mem_sdiff.mp hh).2 hq
      · exact (Finset.mem_sdiff.mp hq).2 hh
    have hRemovedB (q : ℕ) (hq : q ∈ (if chosenInterval then K else S \ K)) :
        q ∈ ρ.childPositions ∧ q ∉ oppositeKeep := by
      have hqS : q ∈ S := by
        cases chosenInterval
        · exact (Finset.mem_sdiff.mp hq).1
        · exact hKS hq
      refine ⟨hChild q hqS, ?_⟩
      intro hqC
      have hh := (hOppositeMem q hqS).mp hqC
      cases chosenInterval
      · exact (Finset.mem_sdiff.mp hq).2 hh
      · exact (Finset.mem_sdiff.mp hh).2 hq
    have hALeft : ∀ p ∈ A, ∀ q ∈ (if chosenInterval then S \ K else K), q < p →
        ∀ z ∈ ranks α s p, lo ρ s q < z := by
      intro p _ q hq hqp z hz
      have hrem := hRemovedA q hq
      have hr := hReserveLeft ρ hPos chosenKeep s m p q hrem.1 hrem.2 hqp
      have hz' := (Finset.mem_Icc.mp hz).1
      change ρ.leftExt s 0 q + 1 ≤ α.leftExt s 0 p at hr
      change α.leftExt s 0 p + 1 ≤ z at hz'
      dsimp only [lo]
      omega
    have hARight : ∀ p ∈ A, ∀ q ∈ (if chosenInterval then S \ K else K), p < q →
        ∀ z ∈ ranks α s p, z < hi ρ s q := by
      intro p hp q hq hpq z hz
      have hrem := hRemovedA q hq
      have hr := hReserveRight ρ hPos chosenKeep s m p q hrem.1 hrem.2 hpq
      have hz' := Finset.mem_Icc.mp hz
      have he := hGPart ρ chosenKeep s s m
      change G α s = G ρ s at he
      change ρ.rightExt s 0 q + 1 ≤ α.rightExt s 0 p at hr
      change α.leftExt s 0 p + 1 ≤ z ∧ z ≤ G α s - 1 - α.rightExt s 0 p at hz'
      dsimp only [hi]
      omega
    have hBLeft : ∀ p ∈ B, ∀ q ∈ (if chosenInterval then K else S \ K), q < p →
        ∀ z ∈ ranks β t p, lo ρ t q < z := by
      intro p _ q hq hqp z hz
      have hrem := hRemovedB q hq
      have hr := hReserveLeft ρ hPos oppositeKeep t n p q hrem.1 hrem.2 hqp
      have hz' := (Finset.mem_Icc.mp hz).1
      change ρ.leftExt t 0 q + 1 ≤ β.leftExt t 0 p at hr
      change β.leftExt t 0 p + 1 ≤ z at hz'
      dsimp only [lo]
      omega
    have hBRight : ∀ p ∈ B, ∀ q ∈ (if chosenInterval then K else S \ K), p < q →
        ∀ z ∈ ranks β t p, z < hi ρ t q := by
      intro p hp q hq hpq z hz
      have hrem := hRemovedB q hq
      have hr := hReserveRight ρ hPos oppositeKeep t n p q hrem.1 hrem.2 hpq
      have hz' := Finset.mem_Icc.mp hz
      have he := hGPart ρ oppositeKeep t t n
      change G β t = G ρ t at he
      change ρ.rightExt t 0 q + 1 ≤ β.rightExt t 0 p at hr
      change β.leftExt t 0 p + 1 ≤ z ∧ z ≤ G β t - 1 - β.rightExt t 0 p at hz'
      dsimp only [hi]
      omega
    exact ctx_thin_rank_rectangle_interval_dimension_cover_transfer S K A B chosenInterval
      (lo ρ s) (hi ρ s) (lo ρ t) (hi ρ t) (ranks α s) (ranks α t) (ranks β s) (ranks β t)
      hSource (fun p _ q _ hpq => hCoordinatesMono ρ p q hpq) hKS hFiniteConvex hA hB
      (fun p hp => ⟨hRanksNonempty α s p (Finset.mem_inter.mp hp).2,
        hRanksNonempty α t p (Finset.mem_inter.mp hp).2⟩)
      (fun p hp => ⟨hRanksNonempty β s p (Finset.mem_inter.mp hp).2,
        hRanksNonempty β t p (Finset.mem_inter.mp hp).2⟩)
      (fun p _ => ⟨hRanksInherit ρ chosenKeep s s m p, hRanksInherit ρ chosenKeep s t m p⟩)
      (fun p _ => ⟨hRanksInherit ρ oppositeKeep t s n p, hRanksInherit ρ oppositeKeep t t n p⟩)
      hALeft hARight hBLeft hBRight
  have hTransfer (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hThin : Thin ρ) (keep : List ℕ) (hConvex : Convex ρ keep)
      (chosenInterval : Bool) (m n : ℕ) (cover : List (Finset ℕ)) (hCover : Covers ρ cover) :
      let rest := ρ.childPositions.filter (· ∉ keep)
      let α := ρ.part (if chosenInterval then keep else rest) s m
      let β := ρ.part (if chosenInterval then rest else keep) t n
      ∃ CA CB : List (Finset ℕ), Covers α CA ∧ Covers β CB ∧
        (CA.map (W α)).sum + (CB.map (W β)).sum ≤ (cover.map (W ρ)).sum := by
    let rest := ρ.childPositions.filter (· ∉ keep)
    let chosenKeep := if chosenInterval then keep else rest
    let oppositeKeep := if chosenInterval then rest else keep
    let α := ρ.part chosenKeep s m
    let β := ρ.part oppositeKeep t n
    have hConstruct : ∀ cs : List (Finset ℕ), (∀ S ∈ cs, S ⊆ active ρ) →
        ∃ CA CB : List (Finset ℕ),
          (∀ p, (∃ S ∈ cs, p ∈ S) → p ∈ active α → ∃ I ∈ CA, p ∈ I) ∧
          (∀ I ∈ CA, I ⊆ active α) ∧
          (∀ p, (∃ S ∈ cs, p ∈ S) → p ∈ active β → ∃ I ∈ CB, p ∈ I) ∧
          (∀ I ∈ CB, I ⊆ active β) ∧
          (CA.map (W α)).sum + (CB.map (W β)).sum ≤ (cs.map (W ρ)).sum := by
      intro cs
      induction cs with
      | nil =>
        intro _
        refine ⟨[], [], ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp
          obtain ⟨S, hS, _⟩ := hp
          exact False.elim (List.not_mem_nil hS)
        · intro I hI
          exact False.elim (List.not_mem_nil hI)
        · intro p hp
          obtain ⟨S, hS, _⟩ := hp
          exact False.elim (List.not_mem_nil hS)
        · intro I hI
          exact False.elim (List.not_mem_nil hI)
        · simp only [List.map_nil, List.sum_nil, Nat.add_zero, le_refl]
      | cons S cs ih =>
        intro hSub
        obtain ⟨LA, LB, hLA, hLASub, hLB, hLBSub, hLocal⟩ :=
          hLocalCut ρ hPos hThin keep hConvex chosenInterval m n S (hSub S (by simp))
        obtain ⟨CA, CB, hCA, hCASub, hCB, hCBSub, hTail⟩ :=
          ih (fun I hI => hSub I (List.mem_cons_of_mem S hI))
        refine ⟨LA ++ CA, LB ++ CB, ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp hpa
          obtain ⟨I, hI, hpI⟩ := hp
          rcases List.mem_cons.mp hI with rfl | hI
          · obtain ⟨J, hJ, hpJ⟩ := hLA p (Finset.mem_inter.mpr ⟨hpI, hpa⟩)
            exact ⟨J, List.mem_append_left CA hJ, hpJ⟩
          · obtain ⟨J, hJ, hpJ⟩ := hCA p ⟨I, hI, hpI⟩ hpa
            exact ⟨J, List.mem_append_right LA hJ, hpJ⟩
        · intro I hI p hp
          rcases List.mem_append.mp hI with hI | hI
          · exact (Finset.mem_inter.mp (hLASub I hI hp)).2
          · exact hCASub I hI hp
        · intro p hp hpb
          obtain ⟨I, hI, hpI⟩ := hp
          rcases List.mem_cons.mp hI with rfl | hI
          · obtain ⟨J, hJ, hpJ⟩ := hLB p (Finset.mem_inter.mpr ⟨hpI, hpb⟩)
            exact ⟨J, List.mem_append_left CB hJ, hpJ⟩
          · obtain ⟨J, hJ, hpJ⟩ := hCB p ⟨I, hI, hpI⟩ hpb
            exact ⟨J, List.mem_append_right LB hJ, hpJ⟩
        · intro I hI p hp
          rcases List.mem_append.mp hI with hI | hI
          · exact (Finset.mem_inter.mp (hLBSub I hI hp)).2
          · exact hCBSub I hI hp
        · change (LA.map (W α)).sum + (LB.map (W β)).sum ≤ W ρ S at hLocal
          simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
          omega
    obtain ⟨CA, CB, hCA, hCASub, hCB, hCBSub, hSum⟩ := hConstruct cover hCover.2
    refine ⟨CA, CB, ⟨?_, hCASub⟩, ⟨?_, hCBSub⟩, hSum⟩
    · intro p hp
      exact hCA p (hCover.1 p (hPartActive ρ chosenKeep s m p hp).1) hp
    · intro p hp
      exact hCB p (hCover.1 p (hPartActive ρ oppositeKeep t n p hp).1) hp
  have hFuel : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) → Thin ρ →
      ∀ cover : List (Finset ℕ), Covers ρ cover → boundFuel fuel ρ ≤ (cover.map (W ρ)).sum := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _ cover _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hPos hThin cover hCover
      rw [boundFuel]
      split
      · exact hBase ρ hThin cover hCover
      · apply Ctx.getD_max?_le
        intro x hx
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨keep, hk, d, _, hx⟩ := hx
        let rest := ρ.childPositions.filter (· ∉ keep)
        have hConvex := hBlockConvex ρ keep hk
        have hCut (chosenInterval : Bool) (a b : ℕ) :
            boundFuel fuel (ρ.part (if chosenInterval then keep else rest) s a) +
              boundFuel fuel (ρ.part (if chosenInterval then rest else keep) t b) ≤
                (cover.map (W ρ)).sum := by
          obtain ⟨CA, CB, hCA, hCB, hSum⟩ :=
            hTransfer ρ hPos hThin keep hConvex chosenInterval a b cover hCover
          have ha := ih _ (hPositivePart ρ _ s a) (hThinPart ρ hThin _ s a) CA hCA
          have hb := ih _ (hPositivePart ρ _ t b) (hThinPart ρ hThin _ t b) CB hCB
          exact (Nat.add_le_add ha hb).trans hSum
        have hBoth (a b : ℕ) :
            (boundFuel fuel (ρ.part keep Side.lower a) + boundFuel fuel (ρ.part rest Side.upper b) ≤
              (cover.map (W ρ)).sum) ∧
            (boundFuel fuel (ρ.part keep Side.upper b) + boundFuel fuel (ρ.part rest Side.lower a) ≤
              (cover.map (W ρ)).sum) := by
          cases s <;> cases t
          · exact False.elim (hne rfl)
          · exact ⟨hCut true a b, by simpa only [Bool.false_eq_true, if_false, Nat.add_comm] using hCut false a b⟩
          · exact ⟨by simpa only [Bool.false_eq_true, if_false, Nat.add_comm] using hCut false b a, hCut true b a⟩
          · exact False.elim (hne rfl)
        rcases hx with rfl | rfl
        · exact (hBoth (d + 1) (ρ.k - 1 - (d + 1))).1
        · exact (hBoth (d + 1) (ρ.k - 1 - (d + 1))).2
  have hThinσ : Thin σ := by
    intro p hp
    have hc := (hActive σ p).mp hp
    have hh := hthin p hc.1 hc.2.1 hc.2.2
    change hi σ s p ≤ lo σ s p + 1
    cases s <;> dsimp only [hi, lo, G] at hh ⊢ <;> omega
  intro cover hCover hSub
  exact ⟨fun fuel => hFuel fuel σ hpositive hThinσ cover ⟨hCover, hSub⟩,
    hFuel _ σ hpositive hThinσ cover ⟨hCover, hSub⟩⟩

end ErdosSzekeres
