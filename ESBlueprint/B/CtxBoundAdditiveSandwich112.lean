import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit
import ErdosSzekeres.PublishedInductionSemantics

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000

/-- Sandwich additivity for four consecutive child positions split into outer blocks of lengths one and two and a singleton middle block. Uniform in the well-formed external context, parameters, and admissible coupling, with both orientations. Together with checked middle-block contraction this gives the (1,m,2) sandwich family.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_sandwich_112 (σ : Ctx.Context) (hwf : σ.WellFormed) (b : ℕ)
  (hpos : σ.childPositions = List.range' b 4)
  (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) :
  (σ.part [b, b + 2, b + 3] Ctx.Side.lower d).bound +
      (σ.part [b + 1] Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧
  (σ.part [b, b + 2, b + 3] Ctx.Side.upper (σ.k - 1 - d)).bound +
      (σ.part [b + 1] Ctx.Side.lower d).bound ≤ σ.bound := by
  have hbaseSplit : ∀ cl pl k d : ℕ, cl ≤ k - 1 → pl ≤ k - 1 →
      1 ≤ d → d ≤ k - 2 →
      baseOf (min (cl - 1) (k - 1 - d)) pl k +
          baseOf cl (min (pl - 1) d) k ≤ baseOf cl pl k := by
    as_aux_lemma =>
      intro cl pl k d hc hp hd hdk
      by_cases hc0 : cl = 0
      · simp [hc0, baseOf]
      by_cases hp0 : pl = 0
      · simp [hp0, baseOf]
      by_cases hc1 : cl = 1
      · simpa [hc1, baseOf] using
          (baseOf_mono (k := k) (cl := cl) (cl' := cl) (Nat.le_refl cl)
            (Nat.min_le_left (pl - 1) d |>.trans (Nat.sub_le pl 1)))
      by_cases hp1 : pl = 1
      · simpa [hp1, baseOf] using
          (baseOf_mono (k := k)
            (Nat.min_le_left (cl - 1) (k - 1 - d) |>.trans (Nat.sub_le cl 1))
            (pl := pl) (pl' := pl) (Nat.le_refl pl))
      have hce : 2 ≤ cl := by omega
      have hpe : 2 ≤ pl := by omega
      have hmc : 1 ≤ min (cl - 1) (k - 1 - d) := by omega
      have hmp : 1 ≤ min (pl - 1) d := by omega
      have hconvert : ∀ x y : ℕ, 1 ≤ x → 1 ≤ y → x ≤ k - 1 → y ≤ k - 1 →
          baseOf x y k = decomposableThreshold (y + 1) (x + 1) k := by
        intro x y hx hy hxk hyk
        unfold baseOf
        rw [if_neg (by omega)]
        by_cases h : x = 1 ∨ y = 1
        · rw [if_pos h]
          rcases h with rfl | rfl
          · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
            have hrow : y + 1 + (1 + 1) - 4 = y + 1 - 2 := by omega
            rw [hrow, Nat.choose_self]
          · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
            simp
        · rw [if_neg h]
      rw [hconvert _ _ hmc (by omega) (by omega) hp,
        hconvert _ _ (by omega) hmp hc (by omega),
        hconvert _ _ (by omega) (by omega) hc hp]
      by_cases hsmall : (pl + 1) + (cl + 1) ≤ k + 3
      · calc
          decomposableThreshold (pl + 1) (min (cl - 1) (k - 1 - d) + 1) k +
              decomposableThreshold (min (pl - 1) d + 1) (cl + 1) k ≤
              decomposableThreshold (pl + 1) cl k +
                decomposableThreshold pl (cl + 1) k :=
            Nat.add_le_add
              (decomposableThreshold_mono (by omega) (by omega) (by omega) (by omega))
              (decomposableThreshold_mono (by omega) (by omega) (by omega) (by omega))
          _ = decomposableThreshold (pl + 1) (cl + 1) k := by
            rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega),
              decomposableThreshold_eq_choose (by omega) (by omega) (by omega),
              decomposableThreshold_eq_choose (by omega) (by omega) hsmall]
            have hrow₁ : pl + 1 + cl - 4 = pl + cl - 3 := by omega
            have hrow₂ : pl + (cl + 1) - 4 = pl + cl - 3 := by omega
            have hrow : pl + 1 + (cl + 1) - 4 = (pl + cl - 3) + 1 := by omega
            have hcol : pl + 1 - 2 = (pl - 2) + 1 := by omega
            rw [hrow₁, hrow₂, hrow, hcol, Nat.choose_succ_succ]
            simp only [Nat.succ_eq_add_one]
            omega
      · exact published_nonsaturated_next_threshold_pair_le
          (by omega) (by omega) (by omega) (by omega) hmp hmc
          (by omega) (by omega) (by omega) (by omega)
  have hrunBound : ∀ (τ : Context) (a n : ℕ), 0 < n →
      τ.childPositions = List.range' a n →
      τ.bound = baseOf (τ.cupLimit a a) (τ.capLimit a a) τ.k := by
    intro τ a n hn hps
    have hmem : ∀ p, p ∈ τ.childPositions ↔ a ≤ p ∧ p < a + n := by
      intro p
      rw [hps, List.mem_range'_1]
    let starts := (List.range τ.word.length).filter fun p ↦
      τ.letterAt p = Letter.child ∧ (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child)
    have hsubset : starts.toFinset ⊆ ({a} : Finset ℕ) := by
      intro p hp
      have hstart : p < τ.word.length ∧ τ.letterAt p = Letter.child ∧
          (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child) := by
        simpa [starts] using hp
      have hp' := (hmem p).1
        (by simpa [childPositions] using And.intro hstart.1 hstart.2.1)
      simp only [Finset.mem_singleton]
      by_contra hpa
      have hprev : p - 1 ∈ τ.childPositions := (hmem (p - 1)).2 ⟨by omega, by omega⟩
      have hprev' : τ.letterAt (p - 1) = Letter.child :=
        (List.mem_filter.1 hprev).2 |> of_decide_eq_true
      rcases hstart.2.2 with hz | hnot
      · omega
      · exact hnot hprev'
    have hruns : τ.numRuns ≤ 1 := by
      calc
        τ.numRuns = starts.toFinset.card :=
          (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
        _ ≤ ({a} : Finset ℕ).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    simp [bound, boundFuel, hruns, base_eq_baseOf, hps, List.head?_range', Nat.ne_of_gt hn]
  have hchild : ∀ p, p ∈ σ.childPositions ↔ b ≤ p ∧ p < b + 4 := by
    intro p
    rw [hpos, List.mem_range'_1]
  -- Every old external position lies outside the run. Moving the starting child
  -- within the run therefore leaves both extension folds unchanged.
  have hextOutside : ∀ N p, p ∈ σ.extPositions N → p < b ∨ b + 4 ≤ p := by
    intro N p hp
    by_contra hout
    have hc := (hchild p).2 ⟨by omega, by omega⟩
    have hlet : σ.letterAt p = Letter.child := of_decide_eq_true (List.mem_filter.1 hc).2
    simp [extPositions, hlet] at hp
  have hfilters : ∀ p q, p ∈ σ.childPositions → q ∈ σ.childPositions → ∀ N,
      (σ.extPositions N).filter (· < p) = (σ.extPositions N).filter (· < q) ∧
      (σ.extPositions N).filter (p < ·) = (σ.extPositions N).filter (q < ·) := by
    intro p q hp hq N
    have hp' := (hchild p).1 hp
    have hq' := (hchild q).1 hq
    constructor <;> apply List.filter_congr <;> intro x hx
    · have := hextOutside N x hx
      simp only [decide_eq_decide]
      omega
    · have := hextOutside N x hx
      simp only [decide_eq_decide]
      omega
  have hfoldLeft : ∀ (ls : List ℕ) p q c, p ∈ σ.childPositions → q ∈ σ.childPositions →
      (ls.foldl (leftStep σ) (p, c)).2 = (ls.foldl (leftStep σ) (q, c)).2 := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons N ls ih =>
      intro p q c hp hq
      simp only [List.foldl_cons, leftStep]
      rw [(hfilters p q hp hq N).1]
      split
      · rfl
      · exact ih p q c hp hq
  have hfoldRight : ∀ (ls : List ℕ) p q c, p ∈ σ.childPositions → q ∈ σ.childPositions →
      (ls.foldl (rightStep σ) (p, c)).2 = (ls.foldl (rightStep σ) (q, c)).2 := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons N ls ih =>
      intro p q c hp hq
      simp only [List.foldl_cons, rightStep]
      rw [(hfilters p q hp hq N).2]
      split
      · rfl
      · exact ih p q c hp hq
  have hleftEq : ∀ s top p q, p ∈ σ.childPositions → q ∈ σ.childPositions →
      σ.leftExt s top p = σ.leftExt s top q := by
    intro s top p q hp hq
    simp only [leftExt_eq]
    congr 2
    apply List.map_congr_left
    intro ls _
    exact hfoldLeft ls p q 0 hp hq
  have hrightEq : ∀ s top p q, p ∈ σ.childPositions → q ∈ σ.childPositions →
      σ.rightExt s top p = σ.rightExt s top q := by
    intro s top p q hp hq
    simp only [rightExt_eq]
    congr 2
    apply List.map_congr_left
    intro ls _
    exact hfoldRight ls p q 0 hp hq
  have hchainEq : ∀ s p q, p ∈ σ.childPositions → q ∈ σ.childPositions →
      σ.chainExt s p p = σ.chainExt s q q := by
    intro s p q hp hq
    simp only [chainExt, hleftEq s 0 p q hp hq, hrightEq s 0 p q hp hq]
  have hjoinEq : ∀ s p q, p ∈ σ.childPositions → q ∈ σ.childPositions →
      σ.joinExt s p p = σ.joinExt s q q := by
    intro s p q hp hq
    simp only [joinExt, hchainEq s p q hp hq, hleftEq s _ p q hp hq,
      hrightEq s _ p q hp hq]
  have hlet : ∀ p N s, σ.letterAt p = Letter.ext N s → 1 ≤ N :=
    fun p N s h ↦ (hwf.2.2.2.2.2 p N s h).1
  have hmaxWitness : ∀ (L : List ℕ) (f : List ℕ → ℕ),
      ∃ ls ∈ L.sublists, ((L.sublists.map f).max?).getD 0 = f ls := by
    intro L f
    have hmem : f [] ∈ L.sublists.map f := List.mem_map.2 ⟨[], by simp, rfl⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (List.isSome_max?_of_mem hmem)
    obtain ⟨ls, hls, hval⟩ := List.mem_map.1 (List.max?_mem hv)
    exact ⟨ls, hls, by simp [hv, hval]⟩
  -- New levels form a finite prefix; every old level follows them unchanged.
  have hlevelPrefix (π : Context) (D : ℕ) (hlen : π.maxima.length = D + σ.maxima.length)
      (hside : ∀ N, 1 ≤ N → π.sideAt (N + D) = σ.sideAt N) (s : Side) (N : ℕ) :
      π.levelsOn s (if N = 0 then 0 else N + D) =
        ((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s) ++
          (σ.levelsOn s N).map (· + D) := by
    have hlevels : π.levels = (List.range D).map (· + 1) ++ σ.levels.map (· + D) := by
      simp only [levels, hlen, List.range_add, List.map_append, List.map_map]
      congr 2
      funext i
      simp only [Function.comp_def]
      omega
    unfold levelsOn
    rw [hlevels, List.filter_append]
    congr 1
    · apply List.filter_congr
      intro l hl
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
      have hi' := List.mem_range.mp hi
      by_cases hN : N = 0 <;> simp [hN] <;> omega
    · rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro l hl
      have hl1 := one_le_of_mem_levels hl
      simp only [Function.comp_def, hside l hl1, decide_eq_decide]
      by_cases hN : N = 0 <;> simp [hN] <;> omega
  have hfoldOldLeft (π : Context) (D : ℕ)
      (hext : ∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N)
      (ls : List ℕ) (hls : ∀ N ∈ ls, 1 ≤ N) (st : ℕ × ℕ) :
      ((ls.map (· + D)).foldl (leftStep π) st) = ls.foldl (leftStep σ) st := by
    induction ls generalizing st with
    | nil => rfl
    | cons N ls ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hstep : leftStep π st (N + D) = leftStep σ st N := by
        rcases st with ⟨p, c⟩
        simp only [leftStep, hext N (hls N (by simp))]
      rw [hstep]
      exact ih (fun N hN => hls N (by simp [hN])) _
  have hfoldOldRight (π : Context) (D : ℕ)
      (hext : ∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N)
      (ls : List ℕ) (hls : ∀ N ∈ ls, 1 ≤ N) (st : ℕ × ℕ) :
      ((ls.map (· + D)).foldl (rightStep π) st) = ls.foldl (rightStep σ) st := by
    induction ls generalizing st with
    | nil => rfl
    | cons N ls ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hstep : rightStep π st (N + D) = rightStep σ st N := by
        rcases st with ⟨p, c⟩
        simp only [rightStep, hext N (hls N (by simp))]
      rw [hstep]
      exact ih (fun N hN => hls N (by simp [hN])) _
  have htransfer (π : Context) (D : ℕ)
      (hlen : π.maxima.length = D + σ.maxima.length)
      (hside : ∀ N, 1 ≤ N → π.sideAt (N + D) = σ.sideAt N)
      (hext : ∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N)
      (hmaximum : ∀ N, 1 ≤ N → π.maximumAt (N + D) = σ.maximumAt N)
      (s : Side) (p : ℕ) (hp : p ∈ σ.childPositions) (L R : List ℕ)
      (hL : L.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s)))
      (hR : R.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s)))
      (l r lc rc : ℕ) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
      (hleft : L.foldl (leftStep π) (p, 0) = (l, lc))
      (hright : R.foldl (rightStep π) (p, 0) = (r, rc)) :
      σ.chainExt s p p + (lc + rc) ≤ π.chainExt s p p ∧
      σ.joinExt s p p + (lc + rc) ≤ π.joinExt s p p := by
    have hleftGrow (N : ℕ) : σ.leftExt s N p + lc ≤ π.leftExt s (if N = 0 then 0 else N + D) p := by
      rw [hleftEq s N p l hp hl]
      obtain ⟨ls, hls, hval⟩ := hmaxWitness (σ.levelsOn s N)
        (fun ls => (ls.foldl (leftStep σ) (l, 0)).2)
      have hsub : (L ++ ls.map (· + D)).Sublist (π.levelsOn s (if N = 0 then 0 else N + D)) := by
        rw [hlevelPrefix π D hlen hside s N]
        exact hL.append ((List.mem_sublists.mp hls).map _)
      have hv := le_getD_max?_of_mem (List.mem_map.mpr ⟨_, List.mem_sublists.mpr hsub, rfl⟩ :
        ((L ++ ls.map (· + D)).foldl (leftStep π) (p, 0)).2 ∈
          (π.levelsOn s (if N = 0 then 0 else N + D)).sublists.map
            (fun ls => (ls.foldl (leftStep π) (p, 0)).2))
      rw [List.foldl_append, hleft, hfoldOldLeft π D hext ls
        (fun N hN => (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hN)).1),
        foldl_leftStep_count σ ls l lc] at hv
      change _ ≤ π.leftExt s (if N = 0 then 0 else N + D) p at hv
      rw [leftExt_eq, hval]
      omega
    have hrightGrow (N : ℕ) : σ.rightExt s N p + rc ≤ π.rightExt s (if N = 0 then 0 else N + D) p := by
      rw [hrightEq s N p r hp hr]
      obtain ⟨ls, hls, hval⟩ := hmaxWitness (σ.levelsOn s N)
        (fun ls => (ls.foldl (rightStep σ) (r, 0)).2)
      have hsub : (R ++ ls.map (· + D)).Sublist (π.levelsOn s (if N = 0 then 0 else N + D)) := by
        rw [hlevelPrefix π D hlen hside s N]
        exact hR.append ((List.mem_sublists.mp hls).map _)
      have hv := le_getD_max?_of_mem (List.mem_map.mpr ⟨_, List.mem_sublists.mpr hsub, rfl⟩ :
        ((R ++ ls.map (· + D)).foldl (rightStep π) (p, 0)).2 ∈
          (π.levelsOn s (if N = 0 then 0 else N + D)).sublists.map
            (fun ls => (ls.foldl (rightStep π) (p, 0)).2))
      rw [List.foldl_append, hright, hfoldOldRight π D hext ls
        (fun N hN => (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hN)).1),
        foldl_rightStep_count σ ls r rc] at hv
      change _ ≤ π.rightExt s (if N = 0 then 0 else N + D) p at hv
      rw [rightExt_eq, hval]
      omega
    have hchain : σ.chainExt s p p + (lc + rc) ≤ π.chainExt s p p := by
      have hL : σ.leftExt s 0 p + lc ≤ π.leftExt s 0 p := by simpa using hleftGrow 0
      have hR : σ.rightExt s 0 p + rc ≤ π.rightExt s 0 p := by simpa using hrightGrow 0
      unfold chainExt
      omega
    refine ⟨hchain, ?_⟩
    have hmax : (((σ.levelsOn s 0).map (fun N => σ.leftExt s N p + σ.rightExt s N p + σ.maximumAt N)).max?).getD 0 + (lc + rc) ≤ π.joinExt s p p := by
      cases hh : ((σ.levelsOn s 0).map (fun N => σ.leftExt s N p + σ.rightExt s N p + σ.maximumAt N)).max? with
      | none =>
        simp only [Option.getD_none, Nat.zero_add]
        exact (by omega : lc + rc ≤ π.chainExt s p p).trans (π.chainExt_le_joinExt s p p)
      | some val =>
        obtain ⟨N, hN, heq⟩ := List.mem_map.mp (List.max?_mem hh)
        have hN1 := (one_le_of_mem_levelsOn hN).1
        have hL := hleftGrow N
        have hR := hrightGrow N
        simp only [if_neg (by omega : N ≠ 0)] at hL hR
        have hmem : N + D ∈ π.levelsOn s 0 := by
          rw [show 0 = (if (0 : ℕ) = 0 then 0 else 0 + D) by simp,
            hlevelPrefix π D hlen hside s 0]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
        have hv := le_joinExt_of_mem_levelsOn hmem p p
        rw [hmaximum N hN1] at hv
        simp only [Option.getD_some]
        omega
    have hc := hchain.trans (π.chainExt_le_joinExt s p p)
    change max _ _ + (lc + rc) ≤ _
    omega
  let Anc (π : Context) (D : ℕ) : Prop :=
    π.a = σ.a ∧ π.u = σ.u ∧ π.k = σ.k ∧ π.maxima.length = D + σ.maxima.length ∧
      (∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N) ∧
      (∀ N, 1 ≤ N → π.sideAt (N + D) = σ.sideAt N) ∧
      (∀ N, 1 ≤ N → π.maximumAt (N + D) = σ.maximumAt N)
  have hAnc0 : Anc σ 0 := by simp [Anc]
  have hAncPart (π : Context) (D : ℕ) (hπ : Anc π D) (keep : List ℕ) (s : Side) (m : ℕ) :
      Anc (π.part keep s m) (D + 1) := by
    obtain ⟨ha, hu, hk, hlen, hext, hside, hmax⟩ := hπ
    refine ⟨ha, hu, hk, ?_, ?_, ?_, ?_⟩
    · simp only [part_maxima, List.length_cons, hlen]; omega
    · intro N hN
      rw [← Nat.add_assoc, part_extPositions_succ π keep s m (by omega : 1 ≤ N + D)]
      exact hext N hN
    · intro N hN
      rw [← Nat.add_assoc, part_sideAt_succ π keep s m (by omega : 1 ≤ N + D)]
      exact hside N hN
    · intro N hN
      rw [← Nat.add_assoc, part_maximumAt_succ π keep s m (by omega : 1 ≤ N + D)]
      exact hmax N hN
  have hnewSub (π : Context) (D : ℕ) (hπ : Anc π D) (s : Side) (top : ℕ)
      (ls : List ℕ) (hls : ls.Sublist ((List.range D).map (· + 1)))
      (hs : ∀ l ∈ ls, π.sideAt l = s ∧ (top = 0 ∨ l < top)) :
      ls.Sublist (π.levelsOn s top) := by
    have hpre : ((List.range D).map (· + 1)).Sublist π.levels := by
      unfold levels
      rw [hπ.2.2.2.1, List.range_add, List.map_append]
      exact List.sublist_append_left _ _
    have hf : ls.filter (fun l => decide (π.sideAt l = s ∧ (top = 0 ∨ l < top))) = ls := by
      apply List.filter_eq_self.mpr
      intro l hl
      simp [hs l hl]
    have h := (hls.trans hpre).filter (fun l => decide (π.sideAt l = s ∧ (top = 0 ∨ l < top)))
    simpa only [hf, levelsOn] using h
  have hprefixSideSub (π : Context) (D : ℕ) (s : Side) (ls : List ℕ)
      (hls : ls.Sublist ((List.range D).map (· + 1)))
      (hs : ∀ l ∈ ls, π.sideAt l = s) :
      ls.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s)) := by
    have hf : ls.filter (fun l => decide (π.sideAt l = s)) = ls := by
      apply List.filter_eq_self.mpr
      intro l hl
      simp [hs l hl]
    simpa only [hf] using hls.filter (fun l => decide (π.sideAt l = s))
  have hjoinNew (π : Context) (s : Side) (N p : ℕ)
      (hN : N ∈ π.levelsOn s 0) (L R : List ℕ)
      (hL : L.Sublist (π.levelsOn s N)) (hR : R.Sublist (π.levelsOn s N)) :
      (L.foldl (leftStep π) (p, 0)).2 + (R.foldl (rightStep π) (p, 0)).2 +
        π.maximumAt N ≤ π.joinExt s p p := by
    have hleft := le_getD_max?_of_mem (List.mem_map.mpr ⟨L, List.mem_sublists.mpr hL, rfl⟩ :
      (L.foldl (leftStep π) (p, 0)).2 ∈ (π.levelsOn s N).sublists.map (fun ls => (ls.foldl (leftStep π) (p, 0)).2))
    have hright := le_getD_max?_of_mem (List.mem_map.mpr ⟨R, List.mem_sublists.mpr hR, rfl⟩ :
      (R.foldl (rightStep π) (p, 0)).2 ∈ (π.levelsOn s N).sublists.map (fun ls => (ls.foldl (rightStep π) (p, 0)).2))
    change _ ≤ π.leftExt s N p at hleft
    change _ ≤ π.rightExt s N p at hright
    exact (Nat.add_le_add_right (Nat.add_le_add hleft hright) _).trans (le_joinExt_of_mem_levelsOn hN p p)
  have hleafEstimate (π : Context) (D p n : ℕ) (hπ : Anc π D)
      (hp : p ∈ σ.childPositions) (hn : 0 < n) (hps : π.childPositions = List.range' p n)
      (L₀ R₀ L₁ R₁ : List ℕ)
      (hL₀ : L₀.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = Side.lower)))
      (hR₀ : R₀.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = Side.lower)))
      (hL₁ : L₁.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = Side.upper)))
      (hR₁ : R₁.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = Side.upper)))
      (l₀ r₀ l₁ r₁ c₀ d₀ c₁ d₁ : ℕ)
      (hl₀ : l₀ ∈ σ.childPositions) (hr₀ : r₀ ∈ σ.childPositions)
      (hl₁ : l₁ ∈ σ.childPositions) (hr₁ : r₁ ∈ σ.childPositions)
      (hfL₀ : L₀.foldl (leftStep π) (p, 0) = (l₀, c₀))
      (hfR₀ : R₀.foldl (rightStep π) (p, 0) = (r₀, d₀))
      (hfL₁ : L₁.foldl (leftStep π) (p, 0) = (l₁, c₁))
      (hfR₁ : R₁.foldl (rightStep π) (p, 0) = (r₁, d₁))
      (J₀ J₁ : ℕ) (hj₀ : J₀ ≤ π.joinExt Side.lower p p) (hj₁ : J₁ ≤ π.joinExt Side.upper p p) :
      π.bound ≤ baseOf
        (min (σ.cupLimit b b - (c₀ + d₀)) (σ.k - 1 - J₀))
        (min (σ.capLimit b b - (c₁ + d₁)) (σ.k - 1 - J₁)) σ.k := by
    obtain ⟨ha, hu, hk, hlen, hext, hside, hmaximum⟩ := hπ
    have h₀ := htransfer π D hlen hside hext hmaximum Side.lower p hp L₀ R₀ hL₀ hR₀
      l₀ r₀ c₀ d₀ hl₀ hr₀ hfL₀ hfR₀
    have h₁ := htransfer π D hlen hside hext hmaximum Side.upper p hp L₁ R₁ hL₁ hR₁
      l₁ r₁ c₁ d₁ hl₁ hr₁ hfL₁ hfR₁
    have hb : b ∈ σ.childPositions := by rw [hpos]; simp
    have hcEq : σ.cupLimit p p = σ.cupLimit b b := by
      simp only [cupLimit, hchainEq Side.lower p b hp hb, hjoinEq Side.lower p b hp hb]
    have hpEq : σ.capLimit p p = σ.capLimit b b := by
      simp only [capLimit, hchainEq Side.upper p b hp hb, hjoinEq Side.upper p b hp hb]
    rw [hrunBound π p n hn hps, hk]
    apply baseOf_mono
    · rw [← hcEq]
      unfold cupLimit
      rw [hu, hk]
      omega
    · rw [← hpEq]
      unfold capLimit
      rw [ha, hk]
      omega
  have hcombine (cl pl cr pr C P k : ℕ)
      (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hlC : cl + 1 ≤ C) (hlP : pl ≤ P)
      (hrC : cr ≤ C) (hrP : pr + 1 ≤ P) (hsum : cl + pr ≤ k - 1) :
      baseOf cl pl k + baseOf cr pr k ≤ baseOf C P k := by
    as_aux_lemma =>
      by_cases hzL : cl = 0 ∨ pl = 0
      · have hzero : baseOf cl pl k = 0 := by simp [baseOf, hzL]
        rw [hzero, Nat.zero_add]
        exact baseOf_mono hrC (by omega)
      by_cases hzR : cr = 0 ∨ pr = 0
      · have hzero : baseOf cr pr k = 0 := by simp [baseOf, hzR]
        rw [hzero, Nat.add_zero]
        exact baseOf_mono (by omega) hlP
      have hd1 : 1 ≤ pr := by omega
      have hdk : pr ≤ k - 2 := by omega
      have hs := hbaseSplit C P k pr hC hP hd1 hdk
      have hleft : baseOf cl pl k ≤ baseOf (min (C - 1) (k - 1 - pr)) P k :=
        baseOf_mono (by omega) hlP
      have hright : baseOf cr pr k ≤ baseOf C (min (P - 1) pr) k :=
        baseOf_mono hrC (by omega)
      exact (Nat.add_le_add hleft hright).trans hs
  have halloc_0200 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      baseOf C (min (P - 2) d) k +
        baseOf (min (C - 2) (min (k - 1 - e) (k - 1 - d - 2))) P k +
        baseOf (min (C - 1) (min (k - 1 - f) (k - 1 - d - 1))) (min (P - 1) e) k +
        baseOf (min (C - 1) (k - 1 - d)) (min (P - 1) (min f (e - 1))) k ≤ baseOf C P k := by
    as_aux_lemma =>
      clear * - C P k d e f hC hP hd hdk he hek hf hfk hcombine
      let c0 := C
      let p0 := (min (P - 2) d)
      let c1 := (min (C - 2) (min (k - 1 - e) (k - 1 - d - 2)))
      let p1 := P
      let c2 := (min (C - 1) (min (k - 1 - f) (k - 1 - d - 1)))
      let p2 := (min (P - 1) e)
      let c3 := (min (C - 1) (k - 1 - d))
      let p3 := (min (P - 1) (min f (e - 1)))
      change baseOf c0 p0 k + baseOf c1 p1 k + baseOf c2 p2 k + baseOf c3 p3 k ≤ _
      have hc0b : c0 ≤ C := Nat.le_refl _
      have hp0b : p0 ≤ (P - 2) ∧ p0 ≤ d := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.le_refl _)⟩
      have hc1b : c1 ≤ (C - 2) ∧ c1 ≤ (k - 1 - e) ∧ c1 ≤ (k - 1 - d - 2) := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.min_le_left _ _), (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.le_refl _))⟩
      have hp1b : p1 ≤ P := Nat.le_refl _
      have hc2b : c2 ≤ (C - 1) ∧ c2 ≤ (k - 1 - f) ∧ c2 ≤ (k - 1 - d - 1) := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.min_le_left _ _), (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.le_refl _))⟩
      have hp2b : p2 ≤ (P - 1) ∧ p2 ≤ e := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.le_refl _)⟩
      have hc3b : c3 ≤ (C - 1) ∧ c3 ≤ (k - 1 - d) := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.le_refl _)⟩
      have hp3b : p3 ≤ (P - 1) ∧ p3 ≤ f ∧ p3 ≤ (e - 1) := ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.min_le_left _ _), (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (Nat.le_refl _))⟩
      clear_value c0 p0 c1 p1 c2 p2 c3 p3
      by_cases hs0 : C ≤ 1
      · have hz : c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by omega
        obtain ⟨hz0, hz1, hz2⟩ := hz
        have hzero (x : ℕ) : baseOf 0 x k = 0 := by simp [baseOf]
        rw [hz0, hz1, hz2]
        simp only [hzero, Nat.zero_add, Nat.add_zero]
        exact baseOf_mono (by omega) (by omega)
      by_cases hs1 : P ≤ 1
      · have hz : p0 = 0 ∧ p2 = 0 ∧ p3 = 0 := by omega
        obtain ⟨hz0, hz1, hz2⟩ := hz
        have hzero (x : ℕ) : baseOf x 0 k = 0 := by simp [baseOf]
        rw [hz0, hz1, hz2]
        simp only [hzero, Nat.zero_add, Nat.add_zero]
        exact baseOf_mono (by omega) (by omega)
      have hgood : (c1 + p2 ≤ k - 1) ∧ (c3 + p0 ≤ k - 1) ∧ ((max (c1 + 1) c2) + (max p3 (p0 + 1)) ≤ k - 1) ∧ ((max ((max (c1 + 1) c2) + 1) (max (c3 + 1) c0)) ≤ C) ∧ ((max (max p1 (p2 + 1)) ((max p3 (p0 + 1)) + 1)) ≤ P) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]) <;> omega
      obtain ⟨hg0, hg1, hg2, hg3, hg4⟩ := hgood
      have h0 := hcombine c1 p1 c2 p2 (max (c1 + 1) c2) (max p1 (p2 + 1)) k
        (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega) (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega)
        (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) hg0
      have h1 := hcombine c3 p3 c0 p0 (max (c3 + 1) c0) (max p3 (p0 + 1)) k
        (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega) (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega)
        (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) hg1
      have h2 := hcombine (max (c1 + 1) c2) (max p1 (p2 + 1)) (max (c3 + 1) c0) (max p3 (p0 + 1)) (max ((max (c1 + 1) c2) + 1) (max (c3 + 1) c0)) (max (max p1 (p2 + 1)) ((max p3 (p0 + 1)) + 1)) k
        (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega) (by simp only [← Nat.add_max_add_right, ← Nat.add_max_add_left, max_le_iff]; omega)
        (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) hg2
      have hroot : baseOf (max ((max (c1 + 1) c2) + 1) (max (c3 + 1) c0)) (max (max p1 (p2 + 1)) ((max p3 (p0 + 1)) + 1)) k ≤ baseOf C P k := baseOf_mono hg3 hg4
      clear * - h0 h1 h2 hroot
      omega

  sorry

end ErdosSzekeres
