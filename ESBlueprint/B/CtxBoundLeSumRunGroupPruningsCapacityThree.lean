import ESBlueprint.B.CtxBoundLeSumRunGroupPrunings
import ESBlueprint.B.CtxBoundAdditiveSingleRunMinCapacityThree

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every-fuel and full context bound are at most the sum of original-history pruned group bounds when each physical child run has one color, colors are covered by a finite set, and every child has minimum point capacity at most three. Positive labels suffice; inactive children and empty groups are included. Extends the minimum-capacity-two decomposition by applying the new all-interval single-run capacity-three cut theorem to projected single-run groups. Supplies a reusable decomposition for the next chosen-global-five rank potential and higher-capacity sandwich estimates.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_le_sum_run_group_prunings_capacity_three (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (color : ℕ → ℕ) (colors : Finset ℕ)
  (hcover : ∀ p ∈ σ.childPositions, color p ∈ colors)
  (hsmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3)
  (hcolor : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions, p ≤ q →
    (∀ r, p ≤ r → r ≤ q → r ∈ σ.childPositions) → color p = color q) :
  let support := fun c => σ.childPositions.filter (fun p => color p = c)
  let group := fun c => ({ σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j s => Ctx.Letter.ext j s) } : Ctx.Context)
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ colors.sum (fun c => (group c).bound)) ∧
    σ.bound ≤ colors.sum (fun c => (group c).bound) := by
  classical
  have hInterval (ρ : Context) (hruns : ρ.numRuns ≤ 1) (hchildNe : ρ.childPositions ≠ []) :
      ∃ b, ρ.childPositions = List.range' b ρ.childPositions.length := by
    obtain ⟨b, tail, hcons⟩ := List.exists_cons_of_ne_nil hchildNe
    have hb : b ∈ ρ.childPositions := by
      rw [hcons]
      exact List.mem_cons_self
    have hordered : ρ.childPositions.Pairwise (· ≤ ·) :=
      (Ctx.Context.childPositions_pairwise ρ).imp le_of_lt
    have hmin : ∀ p ∈ ρ.childPositions, b ≤ p := by
      intro p hp
      have h := hordered.rel_head hp
      simpa [hcons] using h
    let starts := (List.range ρ.word.length).filter fun p ↦
      ρ.letterAt p = Ctx.Letter.child ∧
        (p = 0 ∨ ρ.letterAt (p - 1) ≠ Ctx.Letter.child)
    have hstartsLen : starts.length ≤ 1 := by
      simpa [starts, Ctx.Context.numRuns] using hruns
    have hstartsNodup : starts.Nodup := by
      exact List.nodup_range.filter _
    have hbRange : b < ρ.word.length := by
      exact List.mem_range.1 (List.mem_filter.1 hb).1
    have hbLetter : ρ.letterAt b = Ctx.Letter.child :=
      of_decide_eq_true (List.mem_filter.1 hb).2
    have hbStartCondition :
        b = 0 ∨ ρ.letterAt (b - 1) ≠ Ctx.Letter.child := by
      by_cases hb0 : b = 0
      · exact Or.inl hb0
      · right
        intro hprev
        have hprevMem : b - 1 ∈ ρ.childPositions := by
          apply List.mem_filter.2
          exact ⟨List.mem_range.2 (by omega), by simpa using hprev⟩
        have := hmin (b - 1) hprevMem
        omega
    have hbStart : b ∈ starts := by
      simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hbRange, hbLetter, hbStartCondition⟩
    have hstartUnique : ∀ p ∈ starts, p = b := by
      intro p hp
      by_contra hpb
      have hsubset : ({b, p} : Finset ℕ) ⊆ starts.toFinset := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact List.mem_toFinset.2 hbStart
        · exact List.mem_toFinset.2 hp
      have hcard := Finset.card_le_card hsubset
      rw [List.toFinset_card_of_nodup hstartsNodup] at hcard
      have htwo : ({b, p} : Finset ℕ).card = 2 := by
        simp [Ne.symm hpb]
      rw [htwo] at hcard
      omega
    have hpred : ∀ p ∈ ρ.childPositions, p ≠ b → p - 1 ∈ ρ.childPositions := by
      intro p hp hpb
      have hpRange : p < ρ.word.length :=
        List.mem_range.1 (List.mem_filter.1 hp).1
      have hpLetter : ρ.letterAt p = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.1 hp).2
      have hpPositive : 0 < p := by
        have := hmin p hp
        omega
      by_contra hprevMem
      have hprevLetter : ρ.letterAt (p - 1) ≠ Ctx.Letter.child := by
        intro hletter
        apply hprevMem
        apply List.mem_filter.2
        exact ⟨List.mem_range.2 (by omega), by simpa using hletter⟩
      have hpStart : p ∈ starts := by
        simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hpRange, hpLetter, Or.inr hprevLetter⟩
      exact hpb (hstartUnique p hpStart)
    have hfill : ∀ p ∈ ρ.childPositions, ∀ q, b ≤ q → q ≤ p →
        q ∈ ρ.childPositions := by
      intro p
      induction p using Nat.strong_induction_on with
      | h p ih =>
        intro hp q hbq hqp
        by_cases hpb : p = b
        · have : q = b := by omega
          simpa [this] using hb
        by_cases hqp' : q = p
        · simpa [hqp'] using hp
        exact ih (p - 1) (by omega) (hpred p hp hpb) q hbq (by omega)
    let e := ρ.childPositions.getLast hchildNe
    have he : e ∈ ρ.childPositions := by
      dsimp [e]
      exact List.getLast_mem _
    have hmax : ∀ p ∈ ρ.childPositions, p ≤ e := by
      intro p hp
      simpa [e] using hordered.rel_getLast hp
    have hbe : b ≤ e := hmin e he
    have hmemRange : ∀ p, p ∈ ρ.childPositions ↔
        p ∈ List.range' b (e + 1 - b) := by
      intro p
      simp only [List.mem_range'_1]
      constructor
      · intro hp
        exact ⟨hmin p hp, by have := hmax p hp; omega⟩
      · rintro ⟨hbp, hp⟩
        exact hfill e he p hbp (by omega)
    have hperm : ρ.childPositions.Perm (List.range' b (e + 1 - b)) :=
      (List.perm_ext_iff_of_nodup (Ctx.Context.childPositions_nodup ρ)
        List.nodup_range').2 hmemRange
    have hrange : ρ.childPositions = List.range' b (e + 1 - b) :=
      List.Perm.eq_of_pairwise' (r := (· ≤ ·)) hordered List.pairwise_le_range' hperm
    have hlen : ρ.childPositions.length = e + 1 - b := by
      rw [hrange]
      simp
    have hinterval : ρ.childPositions = List.range' b ρ.childPositions.length := by
      rw [hlen]
      exact hrange
    exact ⟨b, hinterval⟩
  have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ p j s, (ρ.part keep v m).letterAt p = Letter.ext j s → 1 ≤ j := by
    intro p j s hp
    have hpl : p < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep v m)
        (show (ρ.part keep v m).word.length ≤ p by rw [part_word_length]; omega)
      rw [hn] at hp
      cases hp
    cases he : ρ.letterAt p with
    | child =>
      rw [part_letterAt_of_child ρ keep v m hpl he] at hp
      split at hp
      · cases hp
      · cases hp
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep v m hpl he] at hp
      cases hp
      omega
  have hProjected (ρ υ : Context) (hsub : υ.childPositions ⊆ ρ.childPositions)
      (block : List ℕ) (hb : block ∈ ρ.blocks)
      (hne : υ.childPositions.filter (· ∈ block) ≠ [])
      (hlt : (υ.childPositions.filter (· ∈ block)).length < υ.childPositions.length) :
      υ.childPositions.filter (· ∈ block) ∈ υ.blocks := by
    have hy : ρ.childPositions.filter (· ∈ υ.childPositions) = υ.childPositions := by
      apply ((childPositions_pairwise ρ).filter _).eq_of_mem_iff (childPositions_pairwise υ)
      intro p
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun hp => ⟨hsub hp, hp⟩⟩
    obtain ⟨i, l, _, _, hwindow⟩ := exists_take_drop_of_mem_blocks hb
    have hInfix : block <:+: ρ.childPositions := by
      refine ⟨ρ.childPositions.take i, (ρ.childPositions.drop i).drop (l+1), ?_⟩
      rw [hwindow, List.append_assoc, List.take_append_drop, List.take_append_drop]
    have hblockSort := (childPositions_pairwise ρ).sublist hInfix.sublist
    have hB : block.filter (· ∈ υ.childPositions) = υ.childPositions.filter (· ∈ block) := by
      apply (hblockSort.filter _).eq_of_mem_iff ((childPositions_pairwise υ).filter _)
      intro p
      simp only [List.mem_filter, decide_eq_true_eq]
      exact and_comm
    have h := hInfix.filter (fun p => decide (p ∈ υ.childPositions))
    rw [hy, hB] at h
    obtain ⟨pre, post, he⟩ := h
    have hlen := congrArg List.length he
    simp only [List.length_append] at hlen
    have hpos : 0 < (υ.childPositions.filter (· ∈ block)).length := List.length_pos_iff.mpr hne
    simp only [blocks, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map, decide_eq_true_eq]
    refine ⟨⟨pre.length, by omega, (υ.childPositions.filter (· ∈ block)).length - 1, by omega, ?_⟩, hlt⟩
    rw [Nat.sub_add_cancel (by omega : 1 ≤ (υ.childPositions.filter (· ∈ block)).length)]
    have hslice : ((pre ++ υ.childPositions.filter (· ∈ block) ++ post).drop pre.length).take
        (υ.childPositions.filter (· ∈ block)).length = υ.childPositions.filter (· ∈ block) := by
      simp [List.append_assoc]
    exact (congrArg (fun xs : List ℕ => (xs.drop pre.length).take
      (υ.childPositions.filter (· ∈ block)).length) he).symm.trans hslice
  let prune (ρ : Context) (ks : List ℕ) : Context := { ρ with
    word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
      | Letter.child => if p ∈ ks then Letter.child else Letter.ext (ρ.maxima.length + 1) Side.lower
      | Letter.ext j s => Letter.ext j s) }
  let support (ρ : Context) (c : ℕ) := ρ.childPositions.filter (fun p => color p = c)
  let group (ρ : Context) (c : ℕ) := prune ρ (support ρ c)
  let total (ρ : Context) := colors.sum (fun c => (group ρ c).bound)
  let Cover (ρ : Context) := ∀ p ∈ ρ.childPositions, color p ∈ colors
  let Small (ρ : Context) := ∀ p ∈ ρ.childPositions, min (ρ.cupLimit p p) (ρ.capLimit p p) ≤ 3
  let RunColor (ρ : Context) := ∀ p ∈ ρ.childPositions, ∀ q ∈ ρ.childPositions, p ≤ q →
    (∀ r, p ≤ r → r ≤ q → r ∈ ρ.childPositions) → color p = color q
  change (∀ fuel, boundFuel fuel σ ≤ total σ) ∧ σ.bound ≤ total σ
  have hPLen (ρ : Context) (ks : List ℕ) : (prune ρ ks).word.length = ρ.word.length := by
    simp [prune]
  have hPLetter (ρ : Context) (ks : List ℕ) (p : ℕ) (hp : p < ρ.word.length) :
      (prune ρ ks).letterAt p = (match ρ.letterAt p with
        | Letter.child => if p ∈ ks then Letter.child else Letter.ext (ρ.maxima.length + 1) Side.lower
        | Letter.ext j s => Letter.ext j s) := by
    simp only [prune, letterAt, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some]
  have hPChild (ρ : Context) (ks : List ℕ) :
      (prune ρ ks).childPositions = ρ.childPositions.filter (· ∈ ks) := by
    simp only [childPositions, hPLen, List.filter_filter]
    apply List.filter_congr
    intro p hp
    rw [hPLetter ρ ks p (List.mem_range.mp hp)]
    cases ρ.letterAt p <;> simp
  have hGroupChild (ρ : Context) (c : ℕ) : (group ρ c).childPositions = support ρ c := by
    change (prune ρ (support ρ c)).childPositions = support ρ c
    rw [hPChild]
    apply List.filter_congr
    intro p hp
    simp [support, hp]
  have hGroupMem (ρ : Context) (c : ℕ) (p : ℕ) :
      p ∈ (group ρ c).childPositions ↔ p ∈ ρ.childPositions ∧ color p = c := by
    rw [hGroupChild]
    simp [support]
  have hGroupPos (ρ : Context)
      (hpos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) (c : ℕ) :
      ∀ p j v, (group ρ c).letterAt p = Letter.ext j v → 1 ≤ j :=
    (ctx_part_pruning_history_transport ρ hpos (support ρ c) Side.lower 0).1
  have hGroupLimits (ρ : Context)
      (hpos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) (c : ℕ) (p q : ℕ) :
      (group ρ c).cupLimit p q = ρ.cupLimit p q ∧
      (group ρ c).capLimit p q = ρ.capLimit p q :=
    (ctx_part_pruning_history_transport ρ hpos (support ρ c) Side.lower 0).2.2.2.2.2.1 p q
  have hPCongr (ρ : Context) (ks ls : List ℕ)
      (he : ∀ p ∈ ρ.childPositions, p ∈ ks ↔ p ∈ ls) : prune ρ ks = prune ρ ls := by
    unfold prune
    congr 1
    apply List.map_congr_left
    intro p hp
    cases hc : ρ.letterAt p with
    | child =>
      have hm : p ∈ ρ.childPositions := by
        exact List.mem_filter.mpr ⟨hp, by simp [hc]⟩
      simp only [he p hm]
    | ext j v => rfl
  have hPartSub (ρ : Context) (ks : List ℕ) (v : Side) (m : ℕ) :
      (ρ.part ks v m).childPositions ⊆ ρ.childPositions := by
    rw [part_childPositions]
    intro p hp
    exact (List.mem_filter.mp hp).1
  have hGroupPart (ρ : Context) (c : ℕ) (ks : List ℕ) (v : Side) (m : ℕ) :
      group (ρ.part ks v m) c = prune (ρ.part ks v m) (support ρ c) := by
    apply hPCongr
    intro p hp
    have hs := hPartSub ρ ks v m hp
    simp [support, hp, hs]
  have hSmallPart (ρ : Context) (hs : Small ρ) (ks : List ℕ) (v : Side) (m : ℕ) :
      Small (ρ.part ks v m) := by
    intro p hp
    have h := hs p (hPartSub ρ ks v m hp)
    have hl := ctx_part_limits_le ρ ks v m p p
    exact (min_le_min hl.1 hl.2).trans h
  have hColorPart (ρ : Context) (hc : RunColor ρ) (ks : List ℕ) (v : Side) (m : ℕ) :
      RunColor (ρ.part ks v m) := by
    intro p hp q hq hpq hbetween
    exact hc p (hPartSub ρ ks v m hp) q (hPartSub ρ ks v m hq) hpq
      (fun r hpr hrq => hPartSub ρ ks v m (hbetween r hpr hrq))
  have hEmptyGroup (ρ : Context) (c : ℕ)
      (hn : ∀ p ∈ ρ.childPositions, color p ≠ c) : (group ρ c).bound = 0 := by
    have he : (group ρ c).childPositions = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro p hp
      have hh := (hGroupMem ρ c p).mp hp
      exact hn p hh.1 hh.2
    apply Nat.eq_zero_of_le_zero
    simpa only [he, List.map_nil, List.sum_nil] using (ctx_bound_le_sum_point_bases (group ρ c))
  have hAllGroup (ρ : Context)
      (hpos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (c : ℕ) (hall : ∀ p ∈ ρ.childPositions, color p = c) : ρ.bound ≤ (group ρ c).bound := by
    have hletters (p : ℕ) : ρ.letterAt p = Letter.child ↔ (group ρ c).letterAt p = Letter.child := by
      by_cases hp : p < ρ.word.length
      · rw [hPLetter ρ (support ρ c) p hp]
        cases he : ρ.letterAt p with
        | child =>
          have hc : p ∈ ρ.childPositions := by simp [childPositions, hp, he]
          simp [support, hc, hall p hc]
        | ext j v => simp
      · rw [letterAt_of_length_le ρ (by omega),
          letterAt_of_length_le (group ρ c) (by change (prune ρ (support ρ c)).word.length ≤ p; rw [hPLen]; omega)]
    have hh (j : ℕ) (hj : j ∈ ρ.levels) : (group ρ c).sideAt j = ρ.sideAt j ∧
        (group ρ c).extPositions j ⊆ ρ.extPositions j ∧ (group ρ c).maximumAt j ≤ ρ.maximumAt j := by
      have h := (ctx_part_pruning_history_transport ρ hpos (support ρ c) Side.lower 0).2.2.1 j hj
      change (group ρ c).extPositions j = ρ.extPositions j ∧
        (group ρ c).sideAt j = ρ.sideAt j at h
      refine ⟨h.2, ?_, le_rfl⟩
      rw [h.1]
      exact fun _ hp => hp
    exact (ctx_bound_mono_of_marker_inclusion ρ (group ρ c) hpos (hGroupPos ρ hpos c)
      le_rfl le_rfl rfl (hPLen ρ (support ρ c)).symm hletters rfl hh).2.2
  have hBase (ρ : Context)
      (hpos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hc : RunColor ρ) (hcover : Cover ρ) (hruns : ρ.numRuns ≤ 1) : ρ.base ≤ total ρ := by
    by_cases hnil : ρ.childPositions = []
    · simp [base_eq_baseOf, hnil, total]
    obtain ⟨b, hps⟩ := hInterval ρ hruns hnil
    have hN : 0 < ρ.childPositions.length := List.length_pos_iff.mpr hnil
    have hb : b ∈ ρ.childPositions := by rw [hps]; simp [List.mem_range'_1]; omega
    have hall : ∀ p ∈ ρ.childPositions, color p = color b := by
      intro p hp
      have hpp := hp
      rw [hps, List.mem_range'_1] at hpp
      exact (hc b hb p hp hpp.1 (fun r hbr hrp => by rw [hps, List.mem_range'_1]; omega)).symm
    have hbound := hAllGroup ρ hpos (color b) hall
    have he : ρ.bound = ρ.base := by
      change boundFuel (ρ.childPositions.length + 1) ρ = ρ.base
      rw [boundFuel.eq_2, if_pos hruns]
    rw [he] at hbound
    exact hbound.trans (Finset.single_le_sum (fun c _ => Nat.zero_le ((group ρ c).bound))
      (hcover b hb))
  have hTarget (ρ : Context)
      (hpos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hs : Small ρ) (c : ℕ) (block : List ℕ) (hb : block ∈ ρ.blocks)
      (d : ℕ) (hd : d < ρ.k - 2)
      (hSome : ∃ p ∈ (group ρ c).childPositions, p ∈ block)
      (hOther : ∃ p ∈ (group ρ c).childPositions, p ∉ block) :
      ((group ρ c).part block Side.lower (d+1)).bound +
          ((group ρ c).part (ρ.childPositions.filter (· ∉ block)) Side.upper (ρ.k-1-(d+1))).bound ≤
            (group ρ c).bound ∧
      ((group ρ c).part block Side.upper (ρ.k-1-(d+1))).bound +
          ((group ρ c).part (ρ.childPositions.filter (· ∉ block)) Side.lower (d+1)).bound ≤
            (group ρ c).bound := by
    let υ := group ρ c
    let rest := ρ.childPositions.filter (· ∉ block)
    have hsub : υ.childPositions ⊆ ρ.childPositions := fun p hp => ((hGroupMem ρ c p).mp hp).1
    have hυpos := hGroupPos ρ hpos c
    have hυempty : υ.childPositions ≠ [] := by
      obtain ⟨p, hp, _⟩ := hSome
      exact List.ne_nil_of_mem hp
    let B := υ.childPositions.filter (· ∈ block)
    have hBne : B ≠ [] := by
      obtain ⟨p, hp, hpb⟩ := hSome
      apply List.ne_nil_of_mem (a := p)
      exact List.mem_filter.mpr ⟨hp, by simpa using hpb⟩
    have hBlt : B.length < υ.childPositions.length := by
      change (υ.childPositions.filter (· ∈ block)).length < υ.childPositions.length
      have hle := (List.filter_sublist (p := fun p => decide (p ∈ block)) (l := υ.childPositions)).length_le
      by_contra hnot
      have he := (List.filter_sublist (p := fun p => decide (p ∈ block)) (l := υ.childPositions)).eq_of_length (by omega)
      obtain ⟨p, hp, hpn⟩ := hOther
      have hpB : p ∈ B := by
        change p ∈ υ.childPositions.filter (· ∈ block)
        rw [he]
        exact hp
      simp [B, hpn] at hpB
    have hB := hProjected ρ υ hsub block hb hBne hBlt
    have h1 (v : Side) (m : ℕ) : υ.part B v m = υ.part block v m := by
      apply part_congr
      intro p hp
      simp [B, hp]
    have h2 (v : Side) (m : ℕ) :
        υ.part (υ.childPositions.filter (· ∉ B)) v m = υ.part rest v m := by
      apply part_congr
      intro p hp
      simp [B, rest, hp, hsub hp]
    have hk : υ.k = ρ.k := rfl
    have hdk : d+1 ≤ υ.k-2 := by rw [hk]; omega
    by_cases hOne : υ.numRuns ≤ 1
    · obtain ⟨b, hps⟩ := hInterval υ hOne hυempty
      have hN : 0 < υ.childPositions.length := List.length_pos_iff.mpr hυempty
      have hbmem : b ∈ υ.childPositions := by rw [hps]; simp [List.mem_range'_1]; omega
      have hlim := hGroupLimits ρ hpos c b b
      have hsmall : min (υ.cupLimit b b) (υ.capLimit b b) ≤ 3 := by
        rw [hlim.1, hlim.2]
        exact hs b (hsub hbmem)
      have hfirst := ctx_bound_additive_single_run_min_capacity_three υ hυpos b _ hps hsmall B hB
        Side.lower Side.upper (by decide) (d+1) (υ.k-1-(d+1)) (by omega) (by omega) (by omega)
      have hsecond := ctx_bound_additive_single_run_min_capacity_three υ hυpos b _ hps hsmall B hB
        Side.upper Side.lower (by decide) (υ.k-1-(d+1)) (d+1) (by omega) (by omega) (by omega)
      simpa only [h1, h2, hk] using And.intro hfirst hsecond
    · have hc := ctx_bound_cut_le υ (by omega) B hB (d+1) (by omega) hdk
      simpa only [h1, h2, hk] using hc
  have hCutGroup (ρ : Context)
      (hpos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (c : ℕ) (block : List ℕ) (s t : Side) (m n : ℕ)
      (hTarget : (∃ p ∈ (group ρ c).childPositions, p ∈ block) →
        (∃ p ∈ (group ρ c).childPositions, p ∉ block) →
        ((group ρ c).part block s m).bound +
          ((group ρ c).part (ρ.childPositions.filter (· ∉ block)) t n).bound ≤ (group ρ c).bound) :
      (group (ρ.part block s m) c).bound +
        (group (ρ.part (ρ.childPositions.filter (· ∉ block)) t n) c).bound ≤ (group ρ c).bound := by
    let rest := ρ.childPositions.filter (· ∉ block)
    by_cases hSome : ∃ p ∈ (group ρ c).childPositions, p ∈ block
    · by_cases hOther : ∃ p ∈ (group ρ c).childPositions, p ∉ block
      · obtain ⟨q, hq, hqn⟩ := hOther
        obtain ⟨p, hp, hpb⟩ := hSome
        have hqρ := ((hGroupMem ρ c q).mp hq).1
        have hpρ := ((hGroupMem ρ c p).mp hp).1
        have hqs : q ∈ support ρ c := by rw [← hGroupChild]; exact hq
        have hps : p ∈ support ρ c := by rw [← hGroupChild]; exact hp
        have hpn : p ∉ rest := by simp [rest, hpb]
        have ha := (ctx_prune_part_projection_of_removed_witness ρ hpos
          (support ρ c) block s m q hqρ hqs hqn).2.2
        have hb := (ctx_prune_part_projection_of_removed_witness ρ hpos
          (support ρ c) rest t n p hpρ hps hpn).2.2
        rw [hGroupPart, hGroupPart]
        exact (Nat.add_le_add ha hb).trans (hTarget ⟨p, hp, hpb⟩ ⟨q, hq, hqn⟩)
      · have hall : ∀ p ∈ ρ.childPositions, p ∈ support ρ c → p ∈ block := by
          intro p hp hps
          have hg : p ∈ (group ρ c).childPositions := by rw [hGroupChild]; exact hps
          by_contra hn
          exact hOther ⟨p, hg, hn⟩
        have hz : (group (ρ.part rest t n) c).bound = 0 := by
          apply hEmptyGroup
          intro p hp hc
          rw [part_childPositions] at hp
          obtain ⟨hpρ, hpr⟩ := List.mem_filter.mp hp
          have hnot : p ∉ block := (of_decide_eq_true (List.mem_filter.mp
            (of_decide_eq_true hpr)).2)
          exact hOther ⟨p, (hGroupMem ρ c p).mpr ⟨hpρ, hc⟩, hnot⟩
        have ha := (ctx_prune_part_bound_of_all_tracked_retained ρ hpos
          (support ρ c) block s m hall).2
        change (group (ρ.part block s m) c).bound + (group (ρ.part rest t n) c).bound ≤ _
        rw [hz, Nat.add_zero, hGroupPart]
        exact ha
    · have hall : ∀ p ∈ ρ.childPositions, p ∈ support ρ c → p ∈ rest := by
        intro p hp hps
        have hg : p ∈ (group ρ c).childPositions := by rw [hGroupChild]; exact hps
        have hn : p ∉ block := fun h => hSome ⟨p, hg, h⟩
        simp [rest, hp, hn]
      have hz : (group (ρ.part block s m) c).bound = 0 := by
        apply hEmptyGroup
        intro p hp hc
        rw [part_childPositions] at hp
        obtain ⟨hpρ, hpb⟩ := List.mem_filter.mp hp
        exact hSome ⟨p, (hGroupMem ρ c p).mpr ⟨hpρ, hc⟩, of_decide_eq_true hpb⟩
      have hb := (ctx_prune_part_bound_of_all_tracked_retained ρ hpos
        (support ρ c) rest t n hall).2
      change (group (ρ.part block s m) c).bound + (group (ρ.part rest t n) c).bound ≤ _
      rw [hz, Nat.zero_add, hGroupPart]
      exact hb
  have hAll : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) → Small ρ → RunColor ρ → Cover ρ →
      boundFuel fuel ρ ≤ total ρ := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hpos hs hc hcover
      by_cases hruns : ρ.numRuns ≤ 1
      · rw [boundFuel.eq_2, if_pos hruns]
        exact hBase ρ hpos hc hcover hruns
      · rw [boundFuel.eq_2, if_neg hruns]
        apply getD_max?_le
        intro value hv
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hv
        obtain ⟨block, hb, d, hd, hv⟩ := hv
        let rest := ρ.childPositions.filter (· ∉ block)
        have hOwn (ks : List ℕ) (v : Side) (m : ℕ) :
            boundFuel fuel (ρ.part ks v m) ≤ total (ρ.part ks v m) :=
          ih (ρ.part ks v m) (hPartPositive ρ ks v m) (hSmallPart ρ hs ks v m) (hColorPart ρ hc ks v m)
            (fun p hp => hcover p (hPartSub ρ ks v m hp))
        have hCut (s t : Side) (m n : ℕ)
            (ht : ∀ c, (∃ p ∈ (group ρ c).childPositions, p ∈ block) →
              (∃ p ∈ (group ρ c).childPositions, p ∉ block) →
              ((group ρ c).part block s m).bound + ((group ρ c).part rest t n).bound ≤
                (group ρ c).bound) :
            total (ρ.part block s m) + total (ρ.part rest t n) ≤ total ρ := by
          dsimp only [total]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum (fun c _ => hCutGroup ρ hpos c block s t m n (ht c))
        rcases hv with rfl | rfl
        · exact (Nat.add_le_add (hOwn block Side.lower (d+1)) (hOwn rest Side.upper _)).trans
            (hCut Side.lower Side.upper (d+1) _
              (fun c a b => (hTarget ρ hpos hs c block hb d hd a b).1))
        · exact (Nat.add_le_add (hOwn block Side.upper _) (hOwn rest Side.lower (d+1))).trans
            (hCut Side.upper Side.lower _ (d+1)
              (fun c a b => (hTarget ρ hpos hs c block hb d hd a b).2))
  exact ⟨fun fuel => hAll fuel σ hpositive hsmall hcolor hcover, hAll _ σ hpositive hsmall hcolor hcover⟩

end ErdosSzekeres
