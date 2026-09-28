import ESBlueprint.B.CtxBoundAdditiveIntervalComplementCapacityThreeFull
import ESBlueprint.B.CtxBoundAdditivePrefixSuffix
import ESBlueprint.B.CtxBoundAdditiveIntervalComplementMiddleCapacityThree

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Interval/complement additivity inside one contiguous child run when the minimum of the two point capacities is at most three. Covers every proper child-order block, both distinct side orientations and positive sibling maxima summing to k-1, for arbitrary positive histories. Interior cuts combine the full outer-capacity-three estimate and the new middle-capacity-three estimate. Prefix/suffix cases reuse the positive-history portion of the existing boundary proof. Supplies the projected single-run inequality needed to extend original-history run-group pruning decomposition beyond minimum capacity two.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_single_run_min_capacity_three (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (b N : ℕ) (hpos : σ.childPositions = List.range' b N)
  (hsmall : min (σ.cupLimit b b) (σ.capLimit b b) ≤ 3)
  (block : List ℕ) (hblock : block ∈ σ.blocks)
  (s t : Ctx.Side) (hne : s ≠ t) (m n : ℕ)
  (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) :
  (σ.part block s m).bound +
    (σ.part (σ.childPositions.filter (· ∉ block)) t n).bound ≤ σ.bound := by
  classical
  have hPrefix (b l r : ℕ)
      (hpos : σ.childPositions = List.range' b (l+r)) (hl : 0 < l) (hr : 0 < r)
      (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) :
      (σ.part (List.range' b l) Side.lower d).bound +
          (σ.part (List.range' (b+l) r) Side.upper (σ.k-1-d)).bound ≤ σ.bound ∧
      (σ.part (List.range' b l) Side.upper (σ.k-1-d)).bound +
          (σ.part (List.range' (b+l) r) Side.lower d).bound ≤ σ.bound := by
    -- Pascal's identity handles the classical range; the existing window allocation
    -- handles the active range. Keep the zero and singleton conventions explicit.
    have hbaseSplit : ∀ cl pl k d : ℕ, cl ≤ k - 1 → pl ≤ k - 1 →
        1 ≤ d → d ≤ k - 2 →
        baseOf (min (cl - 1) (k - 1 - d)) pl k +
            baseOf cl (min (pl - 1) d) k ≤ baseOf cl pl k := by
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
    -- A contiguous interval of child positions has at most one run, so its bound is a base.
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
    have hchild : ∀ p, p ∈ σ.childPositions ↔ b ≤ p ∧ p < b + (l + r) := by
      intro p
      rw [hpos, List.mem_range'_1]
    -- Every old external position lies outside the run. Moving the starting child
    -- within the run therefore leaves both extension folds unchanged.
    have hextOutside : ∀ N p, p ∈ σ.extPositions N → p < b ∨ b + (l + r) ≤ p := by
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
      hpositive
    have hmaxWitness : ∀ (L : List ℕ) (f : List ℕ → ℕ),
        ∃ ls ∈ L.sublists, ((L.sublists.map f).max?).getD 0 = f ls := by
      intro L f
      have hmem : f [] ∈ L.sublists.map f := List.mem_map.2 ⟨[], by simp, rfl⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (List.isSome_max?_of_mem hmem)
      obtain ⟨ls, hls, hval⟩ := List.mem_map.1 (List.max?_mem hv)
      exact ⟨ls, hls, by simp [hv, hval]⟩
    -- Prepending the new sibling level adds one extension on its side. The sibling
    -- maximum also gives a separate lower bound on the new join extension.
    have hgrow : ∀ (keep : List ℕ) (s : Side) (m p q : ℕ),
        p ∈ σ.childPositions → q ∈ σ.childPositions → q ∉ keep → p ≠ q →
        σ.chainExt s p p + 1 ≤ (σ.part keep s m).chainExt s p p ∧
        σ.joinExt s p p + 1 ≤ (σ.part keep s m).joinExt s p p ∧
        m ≤ (σ.part keep s m).joinExt s p p := by
      intro keep s m p q hp hq hnot hpq
      have hqext : q ∈ (σ.part keep s m).extPositions 1 := by
        rw [part_extPositions_one hlet]
        simp [hq, hnot]
      have hside := part_sideAt_one_of_mem hlet keep s m hqext
      have hboth : ∀ top top',
          (σ.part keep s m).levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1) →
          σ.leftExt s top p + σ.rightExt s top p + 1 ≤
            (σ.part keep s m).leftExt s top' p + (σ.part keep s m).rightExt s top' p := by
        intro top top' hlevels
        have hpositive : ∀ ls ∈ (σ.levelsOn s top).sublists, ∀ N ∈ ls, 1 ≤ N := by
          intro ls hls N hN
          exact (one_le_of_mem_levelsOn ((List.mem_sublists.1 hls).subset hN)).1
        have hleft : σ.leftExt s top p ≤ (σ.part keep s m).leftExt s top' p := by
          obtain ⟨ls, hls, heq⟩ := hmaxWitness (σ.levelsOn s top)
            (fun ls ↦ (ls.foldl (leftStep σ) (p, 0)).2)
          rw [leftExt_eq, heq]
          have hsub : ls.map (· + 1) ∈ ((σ.part keep s m).levelsOn s top').sublists := by
            rw [hlevels, List.mem_sublists]
            exact List.sublist_cons_iff.2 (Or.inl ((List.mem_sublists.1 hls).map _))
          have hle := le_getD_max?_of_mem
            (List.mem_map.2 ⟨ls.map (· + 1), hsub, rfl⟩ :
              ((ls.map (· + 1)).foldl (leftStep (σ.part keep s m)) (p, 0)).2 ∈
                ((σ.part keep s m).levelsOn s top').sublists.map
                  (fun xs ↦ (xs.foldl (leftStep (σ.part keep s m)) (p, 0)).2))
          rw [foldl_leftStep_part_map σ keep s m ls (hpositive ls hls)] at hle
          exact hle
        have hright : σ.rightExt s top p ≤ (σ.part keep s m).rightExt s top' p := by
          obtain ⟨ls, hls, heq⟩ := hmaxWitness (σ.levelsOn s top)
            (fun ls ↦ (ls.foldl (rightStep σ) (p, 0)).2)
          rw [rightExt_eq, heq]
          have hsub : ls.map (· + 1) ∈ ((σ.part keep s m).levelsOn s top').sublists := by
            rw [hlevels, List.mem_sublists]
            exact List.sublist_cons_iff.2 (Or.inl ((List.mem_sublists.1 hls).map _))
          have hle := le_getD_max?_of_mem
            (List.mem_map.2 ⟨ls.map (· + 1), hsub, rfl⟩ :
              ((ls.map (· + 1)).foldl (rightStep (σ.part keep s m)) (p, 0)).2 ∈
                ((σ.part keep s m).levelsOn s top').sublists.map
                  (fun xs ↦ (xs.foldl (rightStep (σ.part keep s m)) (p, 0)).2))
          rw [foldl_rightStep_part_map σ keep s m ls (hpositive ls hls)] at hle
          exact hle
        rcases lt_or_gt_of_ne hpq with hqp | hqp
        · have hinc : σ.rightExt s top p + 1 ≤
              (σ.part keep s m).rightExt s top' p := by
            obtain ⟨ls, hls, heq⟩ := hmaxWitness (σ.levelsOn s top)
              (fun ls ↦ (ls.foldl (rightStep σ) (p, 0)).2)
            have hqfilter : q ∈ ((σ.part keep s m).extPositions 1).filter (p < ·) := by
              simp [hqext, hqp]
            rcases hh : (((σ.part keep s m).extPositions 1).filter (p < ·)).head? with _ | x
            · have hnil := List.head?_eq_none_iff.1 hh
              rw [hnil] at hqfilter
              simp at hqfilter
            · have hx := List.mem_of_mem_head? (Option.mem_def.2 hh)
              have hxext := (List.mem_filter.1 hx).1
              rw [part_extPositions_one hlet] at hxext
              have hxchild := (List.mem_filter.1 hxext).1
              have hsub : 1 :: ls.map (· + 1) ∈
                  ((σ.part keep s m).levelsOn s top').sublists := by
                rw [hlevels, List.mem_sublists]
                exact List.sublist_cons_iff.2 (Or.inr ⟨_, rfl, (List.mem_sublists.1 hls).map _⟩)
              have hle := le_getD_max?_of_mem
                (List.mem_map.2 ⟨1 :: ls.map (· + 1), hsub, rfl⟩ :
                  ((1 :: ls.map (· + 1)).foldl (rightStep (σ.part keep s m)) (p, 0)).2 ∈
                    ((σ.part keep s m).levelsOn s top').sublists.map
                      (fun xs ↦ (xs.foldl (rightStep (σ.part keep s m)) (p, 0)).2))
              have hstep : rightStep (σ.part keep s m) (p, 0) 1 = (x, 1) := by
                simp [rightStep, hh]
              rw [List.foldl_cons, hstep,
                foldl_rightStep_part_map σ keep s m ls (hpositive ls hls),
                foldl_rightStep_count, hfoldRight ls x p 0 hxchild hp] at hle
              change 1 + (ls.foldl (rightStep σ) (p, 0)).2 ≤
                (σ.part keep s m).rightExt s top' p at hle
              rw [rightExt_eq, heq]
              omega
          omega
        · have hinc : σ.leftExt s top p + 1 ≤
              (σ.part keep s m).leftExt s top' p := by
            obtain ⟨ls, hls, heq⟩ := hmaxWitness (σ.levelsOn s top)
              (fun ls ↦ (ls.foldl (leftStep σ) (p, 0)).2)
            have hqfilter : q ∈ ((σ.part keep s m).extPositions 1).filter (· < p) := by
              simp [hqext, hqp]
            rcases hh : (((σ.part keep s m).extPositions 1).filter (· < p)).getLast? with _ | x
            · have hnil := List.getLast?_eq_none_iff.1 hh
              rw [hnil] at hqfilter
              simp at hqfilter
            · have hx := List.mem_of_mem_getLast? (Option.mem_def.2 hh)
              have hxext := (List.mem_filter.1 hx).1
              rw [part_extPositions_one hlet] at hxext
              have hxchild := (List.mem_filter.1 hxext).1
              have hsub : 1 :: ls.map (· + 1) ∈
                  ((σ.part keep s m).levelsOn s top').sublists := by
                rw [hlevels, List.mem_sublists]
                exact List.sublist_cons_iff.2 (Or.inr ⟨_, rfl, (List.mem_sublists.1 hls).map _⟩)
              have hle := le_getD_max?_of_mem
                (List.mem_map.2 ⟨1 :: ls.map (· + 1), hsub, rfl⟩ :
                  ((1 :: ls.map (· + 1)).foldl (leftStep (σ.part keep s m)) (p, 0)).2 ∈
                    ((σ.part keep s m).levelsOn s top').sublists.map
                      (fun xs ↦ (xs.foldl (leftStep (σ.part keep s m)) (p, 0)).2))
              have hstep : leftStep (σ.part keep s m) (p, 0) 1 = (x, 1) := by
                simp [leftStep, hh]
              rw [List.foldl_cons, hstep,
                foldl_leftStep_part_map σ keep s m ls (hpositive ls hls),
                foldl_leftStep_count, hfoldLeft ls x p 0 hxchild hp] at hle
              change 1 + (ls.foldl (leftStep σ) (p, 0)).2 ≤
                (σ.part keep s m).leftExt s top' p at hle
              rw [leftExt_eq, heq]
              omega
          omega
      have hc : σ.chainExt s p p + 1 ≤ (σ.part keep s m).chainExt s p p :=
        hboth 0 0 (part_levelsOn_self_zero hside)
      have hone : 1 ≤ (σ.part keep s m).joinExt s p p := by
        have := (σ.part keep s m).chainExt_le_joinExt s p p
        omega
      have hterms :
          ((((σ.levelsOn s 0).map fun N ↦
            σ.leftExt s N p + σ.rightExt s N p + σ.maximumAt N).max?).getD 0) + 1 ≤
            (σ.part keep s m).joinExt s p p := by
        rcases hv : ((σ.levelsOn s 0).map fun N ↦
            σ.leftExt s N p + σ.rightExt s N p + σ.maximumAt N).max? with _ | v
        · simpa [hv] using hone
        · obtain ⟨N, hN, hval⟩ := List.mem_map.1 (List.max?_mem hv)
          have hN1 := (one_le_of_mem_levelsOn hN).1
          have hb := hboth N (N + 1) (part_levelsOn_self_succ hside hN1)
          have hnew : N + 1 ∈ (σ.part keep s m).levelsOn s 0 := by
            rw [part_levelsOn_self_zero hside]
            exact List.mem_cons.2 (Or.inr (List.mem_map.2 ⟨N, hN, rfl⟩))
          have hj := le_joinExt_of_mem_levelsOn hnew p p
          rw [part_maximumAt_succ σ keep s m hN1] at hj
          simp only [Option.getD_some]
          omega
      refine ⟨hc, ?_, ?_⟩
      · have hc' := hc.trans ((σ.part keep s m).chainExt_le_joinExt s p p)
        change max (σ.chainExt s p p)
            ((((σ.levelsOn s 0).map fun N ↦
              σ.leftExt s N p + σ.rightExt s N p + σ.maximumAt N).max?).getD 0) + 1 ≤
            (σ.part keep s m).joinExt s p p
        omega
      · have hnew : 1 ∈ (σ.part keep s m).levelsOn s 0 := by
          rw [part_levelsOn_self_zero hside]
          simp
        have hj := le_joinExt_of_mem_levelsOn hnew p p
        rw [part_maximumAt_one] at hj
        omega
    have hb : b ∈ σ.childPositions := (hchild b).2 ⟨by omega, by omega⟩
    have hbr : b + l ∈ σ.childPositions := (hchild (b + l)).2 ⟨by omega, by omega⟩
    -- Translate extension growth into a reduced cup or cap limit; the opposite
    -- limit is preserved by the previously proved part-context transfer lemmas.
    have hpartBound : ∀ (keep : List ℕ) (s : Side) (m p n q : ℕ),
        0 < n → (σ.part keep s m).childPositions = List.range' p n →
        q ∈ σ.childPositions → q ∉ keep → p ≠ q →
        (σ.part keep s m).bound ≤
          match s with
          | Side.lower => baseOf (min (σ.cupLimit b b - 1) (σ.k - 1 - m))
              (σ.capLimit b b) σ.k
          | Side.upper => baseOf (σ.cupLimit b b)
              (min (σ.capLimit b b - 1) (σ.k - 1 - m)) σ.k := by
      intro keep s m p n q hn hps hq hnot hpq
      have hpnew : p ∈ (σ.part keep s m).childPositions := by
        rw [hps]
        simp only [List.mem_range'_1]
        omega
      rw [part_childPositions] at hpnew
      have hp := (List.mem_filter.1 hpnew).1
      have hg := hgrow keep s m p q hp hq hnot hpq
      have hqext : q ∈ (σ.part keep s m).extPositions 1 := by
        rw [part_extPositions_one hlet]
        simp [hq, hnot]
      have hside := part_sideAt_one_of_mem hlet keep s m hqext
      rw [hrunBound _ p n hn hps]
      cases s with
      | lower =>
        have hc : (σ.part keep Side.lower m).cupLimit p p ≤
            min (σ.cupLimit b b - 1) (σ.k - 1 - m) := by
          rw [hchainEq Side.lower p b hp hb, hjoinEq Side.lower p b hp hb] at hg
          change min (σ.u - 1 - (σ.part keep Side.lower m).chainExt Side.lower p p)
              (σ.k - 1 - (σ.part keep Side.lower m).joinExt Side.lower p p) ≤
            min (min (σ.u - 1 - σ.chainExt Side.lower b b)
              (σ.k - 1 - σ.joinExt Side.lower b b) - 1) (σ.k - 1 - m)
          omega
        have hp' : (σ.part keep Side.lower m).capLimit p p = σ.capLimit b b := by
          have hs : (σ.part keep Side.lower m).sideAt 1 ≠ Side.upper := by
            rw [hside]
            decide
          change min (σ.a - 1 - (σ.part keep Side.lower m).chainExt Side.upper p p)
              (σ.k - 1 - (σ.part keep Side.lower m).joinExt Side.upper p p) = _
          rw [chainExt_part_other hs, joinExt_part_other hs,
            hchainEq Side.upper p b hp hb, hjoinEq Side.upper p b hp hb]
          rfl
        exact baseOf_mono hc hp'.le
      | upper =>
        have hp' : (σ.part keep Side.upper m).capLimit p p ≤
            min (σ.capLimit b b - 1) (σ.k - 1 - m) := by
          rw [hchainEq Side.upper p b hp hb, hjoinEq Side.upper p b hp hb] at hg
          change min (σ.a - 1 - (σ.part keep Side.upper m).chainExt Side.upper p p)
              (σ.k - 1 - (σ.part keep Side.upper m).joinExt Side.upper p p) ≤
            min (min (σ.a - 1 - σ.chainExt Side.upper b b)
              (σ.k - 1 - σ.joinExt Side.upper b b) - 1) (σ.k - 1 - m)
          omega
        have hc : (σ.part keep Side.upper m).cupLimit p p = σ.cupLimit b b := by
          have hs : (σ.part keep Side.upper m).sideAt 1 ≠ Side.lower := by
            rw [hside]
            decide
          change min (σ.u - 1 - (σ.part keep Side.upper m).chainExt Side.lower p p)
              (σ.k - 1 - (σ.part keep Side.upper m).joinExt Side.lower p p) = _
          rw [chainExt_part_other hs, joinExt_part_other hs,
            hchainEq Side.lower p b hp hb, hjoinEq Side.lower p b hp hb]
          rfl
        exact baseOf_mono hc.le hp'
    -- Both boundary pieces remain single runs. Their two base bounds fit in the
    -- parent's threshold by the arithmetic inequality above.
    have hprefix : ∀ s m, (σ.part (List.range' b l) s m).childPositions = List.range' b l := by
      intro s m
      rw [part_childPositions, hpos, ← List.range'_append_1, List.filter_append]
      have hself : (List.range' b l).filter (fun p ↦ p ∈ List.range' b l) = List.range' b l :=
        List.filter_eq_self.2 (fun p hp ↦ by simpa using hp)
      have hnil : (List.range' (b + l) r).filter (fun p ↦ p ∈ List.range' b l) = [] := by
        apply List.filter_eq_nil_iff.2
        intro p hp
        simp only [List.mem_range'_1] at hp
        simp only [decide_eq_true_eq, List.mem_range'_1]
        omega
      rw [hself, hnil, List.append_nil]
    have hsuffix : ∀ s m, (σ.part (List.range' (b + l) r) s m).childPositions =
        List.range' (b + l) r := by
      intro s m
      rw [part_childPositions, hpos, ← List.range'_append_1, List.filter_append]
      have hself : (List.range' (b + l) r).filter (fun p ↦ p ∈ List.range' (b + l) r) =
          List.range' (b + l) r := List.filter_eq_self.2 (fun p hp ↦ by simpa using hp)
      have hnil : (List.range' b l).filter (fun p ↦ p ∈ List.range' (b + l) r) = [] := by
        apply List.filter_eq_nil_iff.2
        intro p hp
        simp only [List.mem_range'_1] at hp
        simp only [decide_eq_true_eq, List.mem_range'_1]
        omega
      rw [hnil, hself, List.nil_append]
    have hbnot : b ∉ List.range' (b + l) r := by simp; omega
    have hbrnot : b + l ∉ List.range' b l := by simp
    have hPL := hpartBound (List.range' b l) Side.lower d b l (b + l)
      hl (hprefix _ _) hbr hbrnot (by omega)
    have hPU := hpartBound (List.range' b l) Side.upper (σ.k - 1 - d) b l (b + l)
      hl (hprefix _ _) hbr hbrnot (by omega)
    have hSL := hpartBound (List.range' (b + l) r) Side.lower d (b + l) r b
      hr (hsuffix _ _) hb hbnot (by omega)
    have hSU := hpartBound (List.range' (b + l) r) Side.upper (σ.k - 1 - d) (b + l) r b
      hr (hsuffix _ _) hb hbnot (by omega)
    have hcancel : σ.k - 1 - (σ.k - 1 - d) = d := by omega
    simp only [hcancel] at hPL hPU hSL hSU
    have hc : σ.cupLimit b b ≤ σ.k - 1 := by unfold cupLimit; omega
    have hp : σ.capLimit b b ≤ σ.k - 1 := by unfold capLimit; omega
    have hsplit := hbaseSplit (σ.cupLimit b b) (σ.capLimit b b) σ.k d hc hp hd hdk
    rw [hrunBound σ b (l + r) (by omega) hpos]
    constructor <;> omega
  have hPrefixAny (a l r : ℕ) (hpos : σ.childPositions = List.range' a (l+r))
      (hl : 0 < l) (hr : 0 < r) (s t : Side) (hne : s ≠ t)
      (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (hc : u + v = σ.k - 1) :
      (σ.part (List.range' a l) s u).bound +
        (σ.part (List.range' (a+l) r) t v).bound ≤ σ.bound := by
    have huk : u ≤ σ.k - 2 := by omega
    have hvk : v ≤ σ.k - 2 := by omega
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · have he : σ.k - 1 - u = v := by omega
      simpa only [he] using (hPrefix a l r hpos hl hr u hu huk).1
    · have he : σ.k - 1 - v = u := by omega
      simpa only [he] using (hPrefix a l r hpos hl hr v hv hvk).2
    · exact False.elim (hne rfl)
  obtain ⟨i, j, hi, hj, hwindow⟩ := exists_take_drop_of_mem_blocks hblock
  have hproper : block.length < σ.childPositions.length := by
    exact of_decide_eq_true (List.mem_filter.mp hblock).2
  have hiN : i < N := by simpa only [hpos, List.length_range'] using hi
  have hjN : j < N - i := by simpa only [hpos, List.length_range'] using hj
  have hblockRange : block = List.range' (b+i) (j+1) := by
    rw [hwindow, hpos, List.drop_range', Nat.mul_one,
      List.take_range'_of_length_ge (show j+1 ≤ N-i by omega)]
  have hproperN : j+1 < N := by
    simpa only [hblockRange, hpos, List.length_range'] using hproper
  let r := N - i - (j+1)
  have hsum : i + (j+1) + r = N := by dsimp only [r]; omega
  have hroot : σ.childPositions = List.range' b (i+(j+1)+r) := by rw [hsum]; exact hpos
  let O := List.range' b i ++ List.range' (b+i+(j+1)) r
  have hrest : σ.part (σ.childPositions.filter (· ∉ block)) t n = σ.part O t n := by
    apply part_congr
    intro p hp
    have hp' : b ≤ p ∧ p < b + N := by simpa only [hpos, List.mem_range'_1] using hp
    simp only [List.mem_filter, decide_eq_true_eq, hp, true_and, hblockRange,
      List.mem_range'_1, O, List.mem_append]
    omega
  rw [hrest, hblockRange]
  by_cases hi0 : i = 0
  · have hr : 0 < r := by omega
    have he : σ.childPositions = List.range' b ((j+1)+r) := by
      simpa only [hi0, Nat.zero_add] using hroot
    simpa only [O, hi0, Nat.add_zero, List.range'_zero, List.nil_append] using
      hPrefixAny b (j+1) r he (by omega) hr s t hne m n hm hn hcoupling
  by_cases hr0 : r = 0
  · have he : σ.childPositions = List.range' b (i+(j+1)) := by
      simpa only [hr0, Nat.add_zero] using hroot
    simpa only [O, hr0, List.range'_zero, List.append_nil, Nat.add_comm] using
      hPrefixAny b i (j+1) he (by omega) (by omega) t s (Ne.symm hne) n m hn hm (by omega)
  have hiPos : 0 < i := by omega
  have hrPos : 0 < r := by omega
  by_cases hOuter : (match t with | Side.lower => σ.cupLimit b b | Side.upper => σ.capLimit b b) ≤ 3
  · have hh := ctx_bound_additive_interval_complement_capacity_three_full σ hpositive b i (j+1) r
      hroot hiPos (by omega) hrPos t s (Ne.symm hne) n m hOuter (by omega)
    simpa only [O, Nat.add_comm] using hh
  · have hMiddle : (match s with | Side.lower => σ.cupLimit b b | Side.upper => σ.capLimit b b) ≤ 3 := by
      cases s <;> cases t <;> simp only at hOuter ⊢ <;> first | omega | exact False.elim (hne rfl)
    have hh := ctx_bound_additive_interval_complement_middle_capacity_three σ hpositive b i (j+1) r
      hroot hiPos (by omega) hrPos t s (Ne.symm hne) n m hn hMiddle
    simpa only [O, Nat.add_comm] using hh

end ErdosSzekeres
