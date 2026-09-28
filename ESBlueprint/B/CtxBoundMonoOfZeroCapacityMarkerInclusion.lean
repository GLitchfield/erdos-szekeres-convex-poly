import ESBlueprint.B.CtxBoundMonoOfMarkerInclusion

import ESBlueprint.B.CtxBoundAdditiveDisjointSingleRunSmallAxis
import ESBlueprint.B.CtxEraseLevelBoundMono
import ESBlueprint.B.CtxBoundLeSumPointBases
import ESBlueprint.B.CtxBoundAttainedByEndCut

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- Marker-inclusion comparison permitting extra zero-capacity source children. With common coordinates, indexed depth and k, ordered globals and maxima, and target marker subsets preserving level sides, deleting zero-capacity children cannot lower the full recursive bound provided every target child has minimum cup/cap capacity at most two. Bounds every source fuel approximation by the full target bound. Positive labels suffice; arbitrary histories and empty targets are allowed. Projects interval cuts through the child deletion, uses checked small-axis additivity when the target has only one run, and erases a new level when a projected cut degenerates. Supplies the comparison needed to prune inactive children before boundary estimates in the singleton-end sandwich obstruction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_mono_of_zero_capacity_marker_inclusion (σ τ : Ctx.Context)
  (hσpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (hτpositive : ∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (ha : σ.a ≤ τ.a) (hu : σ.u ≤ τ.u) (hk : σ.k = τ.k)
  (hword : σ.word.length = τ.word.length)
  (hdepth : σ.maxima.length = τ.maxima.length)
  (hhistory : ∀ j ∈ σ.levels, τ.sideAt j = σ.sideAt j ∧
    τ.extPositions j ⊆ σ.extPositions j ∧ τ.maximumAt j ≤ σ.maximumAt j)
  (hchildren : τ.childPositions ⊆ σ.childPositions)
  (hdead : ∀ p ∈ σ.childPositions, p ∉ τ.childPositions →
    σ.cupLimit p p = 0 ∨ σ.capLimit p p = 0)
  (hsmall : ∀ p ∈ τ.childPositions, min (τ.cupLimit p p) (τ.capLimit p p) ≤ 2) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ τ.bound) ∧ σ.bound ≤ τ.bound := by
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
  have hFuelLe (ρ : Context) (fuel : ℕ) : boundFuel fuel ρ ≤ ρ.bound := by
    have h := boundFuel_mono (Nat.le_max_left fuel (ρ.childPositions.length + 1)) ρ
    rw [boundFuel_eq_bound ρ (Nat.le_max_right _ _)] at h
    exact h
  have hZero (ρ : Context)
      (hz : ∀ p ∈ ρ.childPositions, ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0) :
      ρ.bound = 0 := by
    have hs : (ρ.childPositions.map (fun p => baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      simp only [baseOf, if_pos (hz p hp)]
    exact Nat.eq_zero_of_le_zero ((ctx_bound_le_sum_point_bases ρ).trans_eq hs)
  have hRunConst (ρ : Context) (b n : ℕ) (hps : ρ.childPositions = List.range' b n)
      (p : ℕ) (hp : p ∈ ρ.childPositions) :
      ρ.cupLimit p p = ρ.cupLimit b b ∧ ρ.capLimit p p = ρ.capLimit b b := by
    let C := ρ.cupLimit b b
    let P := ρ.capLimit b b
    let υ : Context := { ρ with a := P + 1, u := C + 1, maxima := [] }
    have hCk : C ≤ ρ.k - 1 := by dsimp only [C, cupLimit]; omega
    have hPk : P ≤ ρ.k - 1 := by dsimp only [P, capLimit]; omega
    have h := ctx_single_run_descendant_limits_normalize ρ b n hps ρ 0
      ⟨rfl, rfl, rfl, by simp, by intro j _; simp, by intro j _; simp, by intro j _; simp⟩
      (by intro j x hj hj0 _; omega) p p hp hp
    change ρ.cupLimit p p = υ.cupLimit p p ∧ ρ.capLimit p p = υ.capLimit p p at h
    have hc : υ.cupLimit p p = C := by
      simp [υ, cupLimit, chainExt, joinExt, leftExt, rightExt, levelsOn, levels,
        Nat.min_eq_left hCk]
    have hp' : υ.capLimit p p = P := by
      simp [υ, capLimit, chainExt, joinExt, leftExt, rightExt, levelsOn, levels,
        Nat.min_eq_left hPk]
    exact ⟨h.1.trans hc, h.2.trans hp'⟩
  let prune (ρ : Context) (keep : List ℕ) (v : Side) : Context := { ρ with
    word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
      | Letter.child => if p ∈ keep then Letter.child else Letter.ext (ρ.maxima.length + 1) v
      | Letter.ext j s => Letter.ext j s) }
  have hPLen (ρ : Context) (keep : List ℕ) (v : Side) :
      (prune ρ keep v).word.length = ρ.word.length := by simp [prune]
  have hPLetter (ρ : Context) (keep : List ℕ) (v : Side) (p : ℕ) (hp : p < ρ.word.length) :
      (prune ρ keep v).letterAt p = (match ρ.letterAt p with
      | Letter.child => if p ∈ keep then Letter.child else Letter.ext (ρ.maxima.length + 1) v
      | Letter.ext j s => Letter.ext j s) := by
    simp only [prune, letterAt, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some]
  have hPChild (ρ : Context) (keep : List ℕ) (v : Side) :
      (prune ρ keep v).childPositions = ρ.childPositions.filter (· ∈ keep) := by
    simp only [childPositions, hPLen, List.filter_filter]
    apply List.filter_congr
    intro p hp
    rw [hPLetter ρ keep v p (List.mem_range.mp hp)]
    cases ρ.letterAt p <;> simp
  have hPPos (ρ : Context) (keep : List ℕ) (v : Side)
      (hpos : ∀ p j s, ρ.letterAt p = Letter.ext j s → 1 ≤ j) :
      ∀ p j s, (prune ρ keep v).letterAt p = Letter.ext j s → 1 ≤ j := by
    intro p j s hp
    have hpl : p < ρ.word.length := by
      by_contra h
      have he := letterAt_of_length_le (prune ρ keep v)
        (show (prune ρ keep v).word.length ≤ p by rw [hPLen]; omega)
      rw [he] at hp
      cases hp
    rw [hPLetter ρ keep v p hpl] at hp
    cases he : ρ.letterAt p with
    | child =>
      by_cases hpk : p ∈ keep
      · simp [he, hpk] at hp
      · simp only [he, if_neg hpk, Letter.ext.injEq] at hp
        omega
    | ext i w =>
      have hi := hpos p i w he
      simp only [he, Letter.ext.injEq] at hp
      omega
  have hPExt (ρ : Context) (keep : List ℕ) (v : Side) (j : ℕ) (hj : j ∈ ρ.levels) :
      (prune ρ keep v).extPositions j = ρ.extPositions j := by
    have hjD : j ≤ ρ.maxima.length := by
      simp only [levels, List.mem_map, List.mem_range] at hj
      obtain ⟨i, hi, rfl⟩ := hj; omega
    simp only [extPositions, hPLen]
    apply List.filter_congr
    intro p hp
    rw [hPLetter ρ keep v p (List.mem_range.mp hp)]
    cases ρ.letterAt p with
    | child => split_ifs <;> simp [show ρ.maxima.length + 1 ≠ j by omega]
    | ext i w => rfl
  have hPSide (ρ : Context) (keep : List ℕ) (v : Side) (j : ℕ) (hj : j ∈ ρ.levels) :
      (prune ρ keep v).sideAt j = ρ.sideAt j := by
    simp only [sideAt, hPExt ρ keep v j hj]
    cases hh : (ρ.extPositions j).head? with
    | none => rfl
    | some p =>
      have hp := List.mem_of_mem_head? hh
      have hpl := List.mem_range.mp (List.mem_filter.mp hp).1
      dsimp only
      rw [hPLetter ρ keep v p hpl]
      cases he : ρ.letterAt p with
      | child => simp [extPositions, he] at hp
      | ext i s => rfl
  have hPLimits (ρ : Context) (keep : List ℕ) (v : Side) (p q : ℕ) :
      (prune ρ keep v).cupLimit p q = ρ.cupLimit p q ∧
      (prune ρ keep v).capLimit p q = ρ.capLimit p q := by
    have hlevels (s : Side) (top : ℕ) :
        (prune ρ keep v).levelsOn s top = ρ.levelsOn s top := by
      change ρ.levels.filter _ = ρ.levels.filter _
      apply List.filter_congr
      intro j hj
      rw [hPSide ρ keep v j hj]
    have hfold : ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ ρ.levels) → ∀ z,
        ls.foldl (leftStep (prune ρ keep v)) z = ls.foldl (leftStep ρ) z ∧
        ls.foldl (rightStep (prune ρ keep v)) z = ls.foldl (rightStep ρ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; exact ⟨rfl, rfl⟩
      | cons j ls ih =>
        intro hj z
        have ht := ih (fun i hi => hj i (by simp [hi]))
        simp only [List.foldl_cons, leftStep, rightStep, hPExt ρ keep v j (hj j (by simp))]
        exact ⟨(ht _).1, (ht _).2⟩
    have hext (s : Side) (top x : ℕ) :
        (prune ρ keep v).leftExt s top x = ρ.leftExt s top x ∧
        (prune ρ keep v).rightExt s top x = ρ.rightExt s top x := by
      simp only [leftExt_eq, rightExt_eq, hlevels]
      constructor <;> congr 2 <;> apply List.map_congr_left <;> intro ls hls
      · exact congrArg Prod.snd (hfold ls
          (fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) _).1
      · exact congrArg Prod.snd (hfold ls
          (fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) _).2
    have hchain (s : Side) : (prune ρ keep v).chainExt s p q = ρ.chainExt s p q := by
      simp only [chainExt, (hext s 0 p).1, (hext s 0 q).2]
    have hjoin (s : Side) : (prune ρ keep v).joinExt s p q = ρ.joinExt s p q := by
      simp only [joinExt, hchain, hlevels]
      congr 3
      apply List.map_congr_left
      intro j _
      simp only [(hext s j p).1, (hext s j q).2]
      rfl
    simp only [cupLimit, capLimit, hchain, hjoin]
    exact ⟨rfl, rfl⟩
  have hPruneBound (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ)
      (hpos : ∀ p j s, ρ.letterAt p = Letter.ext j s → 1 ≤ j) :
      (ρ.part keep v m).bound ≤ (prune ρ keep v).bound := by
    have h1 : 1 ∈ (ρ.part keep v m).levels := by simp only [part_levels]; simp
    have h := (ctx_erase_level_bound_mono (ρ.part keep v m) 1 h1).2.2
    have he : ({ ρ.part keep v m with
        word := (ρ.part keep v m).word.map (fun x => match x with
          | Letter.child => Letter.child
          | Letter.ext j s => Letter.ext
              (if j = 1 then (ρ.part keep v m).maxima.length else if 1 < j then j - 1 else j) s)
        maxima := (ρ.part keep v m).maxima.eraseIdx (1 - 1) } : Context) = prune ρ keep v := by
      simp only [part, prune, List.map_map, List.length_cons, Nat.sub_self, List.eraseIdx_zero]
      congr 1
      apply List.map_congr_left
      intro p _
      cases hl : ρ.letterAt p with
      | child => simp only [Function.comp_apply, hl]; split_ifs <;> simp
      | ext j s =>
        have hj := hpos p j s hl
        simp only [Function.comp_apply, hl]
        simp [show j ≠ 0 by omega, show 1 < j + 1 by omega]
    exact h.trans_eq (congrArg Context.bound he)
  let Sim (ρ υ : Context) : Prop :=
    (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
    (∀ p j v, υ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
    ρ.a ≤ υ.a ∧ ρ.u ≤ υ.u ∧ ρ.k = υ.k ∧ ρ.word.length = υ.word.length ∧
    ρ.maxima.length = υ.maxima.length ∧
    (∀ j ∈ ρ.levels, υ.sideAt j = ρ.sideAt j ∧
      υ.extPositions j ⊆ ρ.extPositions j ∧ υ.maximumAt j ≤ ρ.maximumAt j) ∧
    υ.childPositions ⊆ ρ.childPositions ∧
    (∀ p ∈ ρ.childPositions, p ∉ υ.childPositions → ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0) ∧
    (∀ p ∈ υ.childPositions, min (υ.cupLimit p p) (υ.capLimit p p) ≤ 2)
  have hPart {ρ υ : Context} (h : Sim ρ υ) (keep : List ℕ) (v : Side) (m : ℕ)
      (hremoved : ∃ p ∈ υ.childPositions, p ∉ keep) :
      Sim (ρ.part keep v m) (υ.part keep v m) := by
    obtain ⟨hρpos, hυpos, ha, hu, hk, hlen, hdepth, hhist, hsub, hdead, hsmall⟩ := h
    refine ⟨hPartPositive ρ keep v m, hPartPositive υ keep v m, ha, hu, hk, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [part_word_length] using hlen
    · change (m :: ρ.maxima).length = (m :: υ.maxima).length
      simp only [List.length_cons, hdepth]
    · intro j hj
      rw [part_levels] at hj
      rcases List.mem_cons.mp hj with hj | hj
      · subst j
        obtain ⟨p, hp, hpk⟩ := hremoved
        have hpυ : p ∈ (υ.part keep v m).extPositions 1 := by
          rw [part_extPositions_one hυpos]; simp [hp, hpk]
        have hpρ : p ∈ (ρ.part keep v m).extPositions 1 := by
          rw [part_extPositions_one hρpos]; simp [hsub hp, hpk]
        refine ⟨?_, ?_, ?_⟩
        · rw [part_sideAt_one_of_mem hυpos keep v m hpυ,
            part_sideAt_one_of_mem hρpos keep v m hpρ]
        · rw [part_extPositions_one hυpos, part_extPositions_one hρpos]
          intro q hq
          have hq' : q ∈ υ.childPositions ∧ q ∉ keep := by simpa only [List.mem_filter, decide_eq_true_eq] using hq
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hsub hq'.1, hq'.2⟩
        · simp only [part_maximumAt_one, le_refl]
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        have hi1 := one_le_of_mem_levels hi
        simpa only [part_sideAt_succ ρ keep v m hi1, part_sideAt_succ υ keep v m hi1,
          part_extPositions_succ ρ keep v m hi1, part_extPositions_succ υ keep v m hi1,
          part_maximumAt_succ ρ keep v m hi1, part_maximumAt_succ υ keep v m hi1] using hhist i hi
    · simp only [part_childPositions]
      intro p hp
      have hpc := List.mem_filter.mp hp
      exact List.mem_filter.mpr ⟨hsub hpc.1, hpc.2⟩
    · intro p hp hn
      rw [part_childPositions] at hp hn
      have hpc := List.mem_filter.mp hp
      have hpn : p ∉ υ.childPositions := by
        intro hpu
        exact hn (List.mem_filter.mpr ⟨hpu, hpc.2⟩)
      have hd := hdead p hpc.1 hpn
      have hl := ctx_part_limits_le ρ keep v m p p
      omega
    · intro p hp
      rw [part_childPositions] at hp
      have hs := hsmall p (List.mem_filter.mp hp).1
      have hl := ctx_part_limits_le υ keep v m p p
      omega
  have hPruned {ρ υ : Context} (h : Sim ρ υ) (keep : List ℕ) (v : Side)
      (hall : ∀ p ∈ υ.childPositions, p ∈ keep) : Sim (prune ρ keep v) υ := by
    obtain ⟨hρpos, hυpos, ha, hu, hk, hlen, hdepth, hhist, hsub, hdead, hsmall⟩ := h
    refine ⟨hPPos ρ keep v hρpos, hυpos, ha, hu, hk, ?_, hdepth, ?_, ?_, ?_, hsmall⟩
    · simpa only [hPLen] using hlen
    · intro j hj
      have hh := hhist j hj
      simpa only [hPSide ρ keep v j hj, hPExt ρ keep v j hj] using hh
    · rw [hPChild]
      intro p hp
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hsub hp, hall p hp⟩
    · intro p hp hn
      rw [hPChild] at hp
      have hd := hdead p (List.mem_filter.mp hp).1 hn
      rw [(hPLimits ρ keep v p p).1, (hPLimits ρ keep v p p).2]
      exact hd
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
  have hMain : ∀ n (ρ υ : Context), ρ.childPositions.length = n → Sim ρ υ → ρ.bound ≤ υ.bound := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro ρ υ hn h
      have hSaved := h
      obtain ⟨hρpos, hυpos, ha, hu, hk, hlen, hdepth, hhist, hsub, hdead, hsmall⟩ := h
      by_cases hequal : ∀ p ∈ ρ.childPositions, p ∈ υ.childPositions
      · have hletters : ∀ p, ρ.letterAt p = Letter.child ↔ υ.letterAt p = Letter.child := by
          intro p
          by_cases hp : p < ρ.word.length
          · have hpu : p < υ.word.length := by omega
            constructor
            · intro hc
              have hm : p ∈ ρ.childPositions := by simp [childPositions, hp, hc]
              exact of_decide_eq_true (List.mem_filter.mp (hequal p hm)).2
            · intro hc
              have hm : p ∈ υ.childPositions := by simp [childPositions, hpu, hc]
              exact of_decide_eq_true (List.mem_filter.mp (hsub hm)).2
          · rw [letterAt_of_length_le ρ (by omega), letterAt_of_length_le υ (by omega)]
        exact (ctx_bound_mono_of_marker_inclusion ρ υ hρpos hυpos ha hu hk hlen hletters hdepth hhist).2.2
      push Not at hequal
      obtain ⟨dead, hdeadmem, hdeadnot⟩ := hequal
      by_cases hruns : ρ.numRuns ≤ 1
      · obtain ⟨b, hps⟩ := hInterval ρ hruns (List.ne_nil_of_mem hdeadmem)
        have hz := hdead dead hdeadmem hdeadnot
        have hc := hRunConst ρ b _ hps dead hdeadmem
        have hzroot : ρ.cupLimit b b = 0 ∨ ρ.capLimit b b = 0 := by omega
        have hN : 0 < ρ.childPositions.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hdeadmem)
        have hhead : ρ.childPositions.head? = some b := by
          have hh := congrArg List.head? hps
          simpa only [List.head?_range', if_neg (Nat.ne_of_gt hN)] using hh
        change boundFuel (ρ.childPositions.length + 1) ρ ≤ υ.bound
        rw [boundFuel.eq_2, if_pos hruns, base_eq_baseOf, hhead]
        simp only [baseOf, if_pos hzroot]
        exact Nat.zero_le _
      by_cases hυempty : υ.childPositions = []
      · have hz := hZero ρ (fun p hp => hdead p hp (by simp [hυempty]))
        rw [hz]
        exact Nat.zero_le _
      change boundFuel (ρ.childPositions.length + 1) ρ ≤ υ.bound
      rw [boundFuel.eq_2, if_neg hruns]
      apply Ctx.getD_max?_le
      intro x hx
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨block, hb, d, hd, hx⟩ := hx
      let rest := ρ.childPositions.filter (· ∉ block)
      have hpartlt (v : Side) (m : ℕ) : (ρ.part block v m).childPositions.length < n := by
        rw [← hn]
        exact part_childPositions_length_lt_of_mem_blocks hb v m
      have hrestlt (v : Side) (m : ℕ) : (ρ.part rest v m).childPositions.length < n := by
        rw [← hn]
        exact part_rest_childPositions_length_lt_of_mem_blocks hb v m
      have hCut (s t : Side) (m q : ℕ)
          (hTarget : (∃ p ∈ υ.childPositions, p ∈ block) → (∃ p ∈ υ.childPositions, p ∉ block) →
            (υ.part block s m).bound + (υ.part rest t q).bound ≤ υ.bound) :
          (ρ.part block s m).bound + (ρ.part rest t q).bound ≤ υ.bound := by
        by_cases hSome : ∃ p ∈ υ.childPositions, p ∈ block
        · by_cases hOther : ∃ p ∈ υ.childPositions, p ∉ block
          · have ha := ih _ (hpartlt s m) _ _ rfl (hPart hSaved block s m hOther)
            have hRemoveRest : ∃ p ∈ υ.childPositions, p ∉ rest := by
              obtain ⟨p, hp, hpb⟩ := hSome
              refine ⟨p, hp, ?_⟩
              simp [rest, hpb]
            have hb' := ih _ (hrestlt t q) _ _ rfl (hPart hSaved rest t q hRemoveRest)
            exact (Nat.add_le_add ha hb').trans (hTarget hSome hOther)
          · have hall : ∀ p ∈ υ.childPositions, p ∈ block := by
              intro p hp; by_contra hn; exact hOther ⟨p, hp, hn⟩
            have hz : (ρ.part rest t q).bound = 0 := by
              apply hZero
              intro p hp
              rw [part_childPositions] at hp
              have hpρ := (List.mem_filter.mp hp).1
              have hpr : p ∈ rest := of_decide_eq_true (List.mem_filter.mp hp).2
              have hpn : p ∉ υ.childPositions := by
                intro hpυ
                have hb' := hall p hpυ
                simp [rest, hb'] at hpr
              have hz := hdead p hpρ hpn
              have hl := ctx_part_limits_le ρ rest t q p p
              omega
            have hlt : (prune ρ block s).childPositions.length < n := by
              rw [hPChild]
              simpa only [part_childPositions] using hpartlt s m
            have hb' := ih _ hlt _ _ rfl (hPruned hSaved block s hall)
            rw [hz, Nat.add_zero]
            exact (hPruneBound ρ block s m hρpos).trans hb'
        · have hall : ∀ p ∈ υ.childPositions, p ∈ rest := by
            intro p hp
            have hpb : p ∉ block := by intro hpb; exact hSome ⟨p, hp, hpb⟩
            simp [rest, hsub hp, hpb]
          have hz : (ρ.part block s m).bound = 0 := by
            apply hZero
            intro p hp
            rw [part_childPositions] at hp
            have hpρ := (List.mem_filter.mp hp).1
            have hpb : p ∈ block := of_decide_eq_true (List.mem_filter.mp hp).2
            have hpn : p ∉ υ.childPositions := by intro hpυ; exact hSome ⟨p, hpυ, hpb⟩
            have hz := hdead p hpρ hpn
            have hl := ctx_part_limits_le ρ block s m p p
            omega
          have hlt : (prune ρ rest t).childPositions.length < n := by
            rw [hPChild]
            simpa only [part_childPositions] using hrestlt t q
          have hb' := ih _ hlt _ _ rfl (hPruned hSaved rest t hall)
          rw [hz, Nat.zero_add]
          exact (hPruneBound ρ rest t q hρpos).trans hb'
      have hTarget : (∃ p ∈ υ.childPositions, p ∈ block) → (∃ p ∈ υ.childPositions, p ∉ block) →
          (υ.part block Side.lower (d+1)).bound + (υ.part rest Side.upper (ρ.k-1-(d+1))).bound ≤ υ.bound ∧
          (υ.part block Side.upper (ρ.k-1-(d+1))).bound + (υ.part rest Side.lower (d+1)).bound ≤ υ.bound := by
        intro hSome hOther
        by_cases hOne : υ.numRuns ≤ 1
        · obtain ⟨b, hps⟩ := hInterval υ hOne hυempty
          have hN : 0 < υ.childPositions.length := List.length_pos_iff.mpr hυempty
          have hbmem : b ∈ υ.childPositions := by rw [hps]; simp [List.mem_range'_1]; omega
          have hs := hsmall b hbmem
          have hdis : ∀ p ∈ υ.childPositions, p ∈ block → p ∉ rest := by
            intro p _ hp; simp [rest, hp]
          exact ⟨ctx_bound_additive_disjoint_single_run_small_axis υ hυpos b _ hps hN hs block rest
              Side.lower Side.upper (by decide) (d+1) _ hdis,
            ctx_bound_additive_disjoint_single_run_small_axis υ hυpos b _ hps hN hs block rest
              Side.upper Side.lower (by decide) _ (d+1) hdis⟩
        · let B := υ.childPositions.filter (· ∈ block)
          have hBne : B ≠ [] := by
            obtain ⟨p, hp, hpb⟩ := hSome
            apply List.ne_nil_of_mem (a := p)
            simp [B, hp, hpb]
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
          have hc := ctx_bound_cut_le υ (by omega) B hB (d+1) (by omega) (by omega)
          simpa only [h1, h2, ← hk] using hc
      rcases hx with rfl | rfl
      · exact (Nat.add_le_add (hFuelLe _ _) (hFuelLe _ _)).trans
          (hCut Side.lower Side.upper (d+1) _ (fun a b => (hTarget a b).1))
      · exact (Nat.add_le_add (hFuelLe _ _) (hFuelLe _ _)).trans
          (hCut Side.upper Side.lower _ (d+1) (fun a b => (hTarget a b).2))
  have hb := hMain _ σ τ rfl ⟨hσpositive, hτpositive, ha, hu, hk, hword, hdepth,
    hhistory, hchildren, hdead, hsmall⟩
  exact ⟨fun fuel => (hFuelLe σ fuel).trans hb, hb⟩

end ErdosSzekeres
