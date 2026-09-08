import ESBlueprint.B.CtxBoundAdditivePrefixSuffix

namespace ErdosSzekeres

open Ctx Ctx.Context

set_option maxHeartbeats 2400000

/-- Context-bound additivity for a contiguous child run split into two singleton outer blocks and a nonempty middle block, with arbitrary well-formed external context, both orientations and every admissible coupling. This is the first finite-recursion sandwich case.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_additive_prefix_suffix
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_bound_additive_sandwich_singleton_ends (σ : Ctx.Context) (hwf : σ.WellFormed) (b m : ℕ) (hpos : σ.childPositions = List.range' b (m + 2)) (hm : 0 < m) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (σ.part [b, b + m + 1] Ctx.Side.lower d).bound + (σ.part (List.range' (b + 1) m) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part [b, b + m + 1] Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (List.range' (b + 1) m) Ctx.Side.lower d).bound ≤ σ.bound := by
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
  have hthreeBase : ∀ cl pl k d e : ℕ, cl ≤ k - 1 → pl ≤ k - 1 →
      1 ≤ d → d ≤ k - 2 → 1 ≤ e → e ≤ k - 2 →
      baseOf (min (min (cl - 1) (k - 1 - e)) (k - 2 - d)) pl k +
          baseOf (min (cl - 1) (k - 1 - d)) (min (pl - 1) e) k +
          baseOf cl (min (pl - 2) d) k ≤ baseOf cl pl k := by
    intro cl pl k d e hc hp hd hdk he hek
    by_cases htop : d = k - 2
    · have hzero :
          baseOf (min (min (cl - 1) (k - 1 - e)) (k - 2 - d)) pl k = 0 := by
        simp [htop, baseOf]
      rw [hzero, Nat.zero_add]
      have hB : baseOf (min (cl - 1) (k - 1 - d)) (min (pl - 1) e) k ≤
          baseOf (min (cl - 1) (k - 1 - d)) pl k :=
        baseOf_mono (Nat.le_refl _) (by omega)
      have hC : baseOf cl (min (pl - 2) d) k ≤ baseOf cl (min (pl - 1) d) k :=
        baseOf_mono (Nat.le_refl _) (by omega)
      exact (Nat.add_le_add hB hC).trans (hbaseSplit cl pl k d hc hp hd hdk)
    · let E := max e (d + 1)
      let P := min (pl - 1) E
      have hEe : e ≤ E := Nat.le_max_left _ _
      have hEd : d + 1 ≤ E := Nat.le_max_right _ _
      have hEk : E ≤ k - 2 := by dsimp [E]; omega
      have hP : P ≤ k - 1 := by dsimp [P]; omega
      have hA :
          baseOf (min (min (cl - 1) (k - 1 - e)) (k - 2 - d)) pl k ≤
            baseOf (min (cl - 1) (k - 1 - E)) pl k :=
        baseOf_mono (by dsimp [E]; omega) (Nat.le_refl _)
      have hB : baseOf (min (cl - 1) (k - 1 - d)) (min (pl - 1) e) k ≤
          baseOf (min (cl - 1) (k - 1 - d)) P k :=
        baseOf_mono (Nat.le_refl _) (by dsimp [P]; omega)
      have hC : baseOf cl (min (pl - 2) d) k ≤ baseOf cl (min (P - 1) d) k :=
        baseOf_mono (Nat.le_refl _) (by dsimp [P]; omega)
      have hinner := hbaseSplit cl P k d hc hP hd hdk
      have houter := hbaseSplit cl pl k E hc hp (by omega) hEk
      calc
        _ ≤ baseOf (min (cl - 1) (k - 1 - E)) pl k +
            (baseOf (min (cl - 1) (k - 1 - d)) P k +
              baseOf cl (min (P - 1) d) k) := by
          simpa only [Nat.add_assoc] using Nat.add_le_add (Nat.add_le_add hA hB) hC
        _ ≤ baseOf (min (cl - 1) (k - 1 - E)) pl k + baseOf cl P k :=
          Nat.add_le_add_left hinner _
        _ ≤ baseOf cl pl k := houter
  have hthreeBaseDual : ∀ cl pl k d e : ℕ, cl ≤ k - 1 → pl ≤ k - 1 →
      1 ≤ d → d ≤ k - 2 → 1 ≤ e → e ≤ k - 2 →
      baseOf cl (min (min (pl - 1) e) (d - 1)) k +
          baseOf (min (cl - 1) (k - 1 - e)) (min (pl - 1) d) k +
          baseOf (min (cl - 2) (k - 1 - d)) pl k ≤ baseOf cl pl k := by
    intro cl pl k d e hc hp hd hdk he hek
    by_cases hbot : d = 1
    · have hzero : baseOf cl (min (min (pl - 1) e) (d - 1)) k = 0 := by
        simp [hbot, baseOf]
      rw [hzero, Nat.zero_add]
      have hB : baseOf (min (cl - 1) (k - 1 - e)) (min (pl - 1) d) k ≤
          baseOf cl (min (pl - 1) d) k :=
        baseOf_mono (by omega) (Nat.le_refl _)
      have hC : baseOf (min (cl - 2) (k - 1 - d)) pl k ≤
          baseOf (min (cl - 1) (k - 1 - d)) pl k :=
        baseOf_mono (by omega) (Nat.le_refl _)
      have hsum := (Nat.add_le_add hC hB).trans (hbaseSplit cl pl k d hc hp hd hdk)
      omega
    · let E := min e (d - 1)
      let P := min (cl - 1) (k - 1 - E)
      have hEe : E ≤ e := Nat.min_le_left _ _
      have hEd : E ≤ d - 1 := Nat.min_le_right _ _
      have hE1 : 1 ≤ E := by dsimp [E]; omega
      have hEk : E ≤ k - 2 := by omega
      have hP : P ≤ k - 1 := by dsimp [P]; omega
      have hA : baseOf cl (min (min (pl - 1) e) (d - 1)) k ≤
          baseOf cl (min (pl - 1) E) k :=
        baseOf_mono (Nat.le_refl _) (by dsimp [E]; omega)
      have hB : baseOf (min (cl - 1) (k - 1 - e)) (min (pl - 1) d) k ≤
          baseOf P (min (pl - 1) d) k :=
        baseOf_mono (by dsimp [P]; omega) (Nat.le_refl _)
      have hC : baseOf (min (cl - 2) (k - 1 - d)) pl k ≤
          baseOf (min (P - 1) (k - 1 - d)) pl k :=
        baseOf_mono (by dsimp [P]; omega) (Nat.le_refl _)
      have hinner := hbaseSplit P pl k d hP hp hd hdk
      have houter := hbaseSplit cl pl k E hc hp hE1 hEk
      have hCB := (Nat.add_le_add hC hB).trans hinner
      have hsum := (Nat.add_le_add hCB hA).trans houter
      omega
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
  have hchild : ∀ p, p ∈ σ.childPositions ↔ b ≤ p ∧ p < b + (m + 2) := by
    intro p
    rw [hpos, List.mem_range'_1]
  -- Every old external position lies outside the run. Moving the starting child
  -- within the run therefore leaves both extension folds unchanged.
  have hextOutside : ∀ N p, p ∈ σ.extPositions N → p < b ∨ b + (m + 2) ≤ p := by
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
  have hsplit : List.range' b (m + 2) =
      [b] ++ List.range' (b + 1) m ++ [b + m + 1] := by
    calc
      List.range' b (m + 2) = List.range' b (1 + (m + 1)) :=
        congrArg (List.range' b) (by omega)
      _ = List.range' b 1 ++ List.range' (b + 1) (m + 1) :=
        List.range'_append_1.symm
      _ = List.range' b 1 ++
          (List.range' (b + 1) m ++ List.range' (b + 1 + m) 1) := by
        exact congrArg (fun xs : List ℕ ↦ List.range' b 1 ++ xs)
          (List.range'_append_1 (s := b + 1) (m := m) (n := 1)).symm
      _ = [b] ++ List.range' (b + 1) m ++ [b + m + 1] := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hb : b ∈ σ.childPositions := (hchild b).2 ⟨by omega, by omega⟩
  have hp : b + 1 ∈ σ.childPositions := (hchild (b + 1)).2 ⟨by omega, by omega⟩
  have hq : b + m + 1 ∈ σ.childPositions :=
    (hchild (b + m + 1)).2 ⟨by omega, by omega⟩
  have hbnot : b ∉ List.range' (b + 1) m := by
    simp only [List.mem_range'_1]
    omega
  have hqnot : b + m + 1 ∉ List.range' (b + 1) m := by
    simp only [List.mem_range'_1]
    omega
  have hpartMiddle : ∀ s n,
      (σ.part (List.range' (b + 1) m) s n).childPositions =
        List.range' (b + 1) m := by
    intro s n
    rw [part_childPositions, hpos, hsplit]
    simp only [List.filter_append]
    have hself : (List.range' (b + 1) m).filter
        (fun x ↦ x ∈ List.range' (b + 1) m) = List.range' (b + 1) m :=
      List.filter_eq_self.2 fun x hx ↦ by simpa using hx
    rw [hself]
    simp [hbnot, hqnot] <;> omega
  have htwoGrow : ∀ (s : Side) (n : ℕ),
      σ.chainExt s (b + 1) (b + 1) + 2 ≤
          (σ.part (List.range' (b + 1) m) s n).chainExt s (b + 1) (b + 1) ∧
      σ.joinExt s (b + 1) (b + 1) + 2 ≤
          (σ.part (List.range' (b + 1) m) s n).joinExt s (b + 1) (b + 1) ∧
      n ≤ (σ.part (List.range' (b + 1) m) s n).joinExt s (b + 1) (b + 1) := by
    intro s n
    let τ := σ.part (List.range' (b + 1) m) s n
    have hbext : b ∈ τ.extPositions 1 := by
      dsimp [τ]
      rw [part_extPositions_one hlet]
      simp [hb, hbnot]
    have hqext : b + m + 1 ∈ τ.extPositions 1 := by
      dsimp [τ]
      rw [part_extPositions_one hlet]
      simp [hq, hqnot] <;> omega
    have hside : τ.sideAt 1 = s := by
      dsimp [τ]
      exact part_sideAt_one_of_mem hlet (List.range' (b + 1) m) s n hbext
    have hleftInc : ∀ top top',
        τ.levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1) →
        σ.leftExt s top (b + 1) + 1 ≤ τ.leftExt s top' (b + 1) := by
      intro top top' hlevels
      have hpositive : ∀ ls ∈ (σ.levelsOn s top).sublists, ∀ N ∈ ls, 1 ≤ N := by
        intro ls hls N hN
        exact (one_le_of_mem_levelsOn ((List.mem_sublists.1 hls).subset hN)).1
      obtain ⟨ls, hls, heq⟩ := hmaxWitness (σ.levelsOn s top)
        (fun ls ↦ (ls.foldl (leftStep σ) (b + 1, 0)).2)
      have hbfilter : b ∈ (τ.extPositions 1).filter (· < b + 1) := by
        simp [hbext]
      rcases hh : ((τ.extPositions 1).filter (· < b + 1)).getLast? with _ | x
      · have hnil := List.getLast?_eq_none_iff.1 hh
        rw [hnil] at hbfilter
        simp at hbfilter
      · have hx := List.mem_of_mem_getLast? (Option.mem_def.2 hh)
        have hxext := (List.mem_filter.1 hx).1
        dsimp [τ] at hxext
        rw [part_extPositions_one hlet] at hxext
        have hxchild := (List.mem_filter.1 hxext).1
        have hsub : 1 :: ls.map (· + 1) ∈ (τ.levelsOn s top').sublists := by
          rw [hlevels, List.mem_sublists]
          exact List.sublist_cons_iff.2
            (Or.inr ⟨_, rfl, (List.mem_sublists.1 hls).map _⟩)
        have hle := le_getD_max?_of_mem
          (List.mem_map.2 ⟨1 :: ls.map (· + 1), hsub, rfl⟩ :
            ((1 :: ls.map (· + 1)).foldl (leftStep τ) (b + 1, 0)).2 ∈
              (τ.levelsOn s top').sublists.map
                (fun xs ↦ (xs.foldl (leftStep τ) (b + 1, 0)).2))
        have hstep : leftStep τ (b + 1, 0) 1 = (x, 1) := by
          calc
            leftStep τ (b + 1, 0) 1 =
                match ((τ.extPositions 1).filter (· < b + 1)).getLast? with
                | some y => (y, 1)
                | none => (b + 1, 0) := rfl
            _ = (x, 1) := by rw [hh]
        rw [List.foldl_cons, hstep,
          foldl_leftStep_part_map σ (List.range' (b + 1) m) s n ls
            (hpositive ls hls),
          foldl_leftStep_count, hfoldLeft ls x (b + 1) 0 hxchild hp] at hle
        change 1 + (ls.foldl (leftStep σ) (b + 1, 0)).2 ≤
          τ.leftExt s top' (b + 1) at hle
        rw [leftExt_eq, heq]
        omega
    have hrightInc : ∀ top top',
        τ.levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1) →
        σ.rightExt s top (b + 1) + 1 ≤ τ.rightExt s top' (b + 1) := by
      intro top top' hlevels
      have hpositive : ∀ ls ∈ (σ.levelsOn s top).sublists, ∀ N ∈ ls, 1 ≤ N := by
        intro ls hls N hN
        exact (one_le_of_mem_levelsOn ((List.mem_sublists.1 hls).subset hN)).1
      obtain ⟨ls, hls, heq⟩ := hmaxWitness (σ.levelsOn s top)
        (fun ls ↦ (ls.foldl (rightStep σ) (b + 1, 0)).2)
      have hqfilter : b + m + 1 ∈ (τ.extPositions 1).filter (b + 1 < ·) := by
        simp [hqext]
        omega
      rcases hh : ((τ.extPositions 1).filter (b + 1 < ·)).head? with _ | x
      · have hnil := List.head?_eq_none_iff.1 hh
        rw [hnil] at hqfilter
        simp at hqfilter
      · have hx := List.mem_of_mem_head? (Option.mem_def.2 hh)
        have hxext := (List.mem_filter.1 hx).1
        dsimp [τ] at hxext
        rw [part_extPositions_one hlet] at hxext
        have hxchild := (List.mem_filter.1 hxext).1
        have hsub : 1 :: ls.map (· + 1) ∈ (τ.levelsOn s top').sublists := by
          rw [hlevels, List.mem_sublists]
          exact List.sublist_cons_iff.2
            (Or.inr ⟨_, rfl, (List.mem_sublists.1 hls).map _⟩)
        have hle := le_getD_max?_of_mem
          (List.mem_map.2 ⟨1 :: ls.map (· + 1), hsub, rfl⟩ :
            ((1 :: ls.map (· + 1)).foldl (rightStep τ) (b + 1, 0)).2 ∈
              (τ.levelsOn s top').sublists.map
                (fun xs ↦ (xs.foldl (rightStep τ) (b + 1, 0)).2))
        have hstep : rightStep τ (b + 1, 0) 1 = (x, 1) := by
          calc
            rightStep τ (b + 1, 0) 1 =
                match ((τ.extPositions 1).filter (b + 1 < ·)).head? with
                | some y => (y, 1)
                | none => (b + 1, 0) := rfl
            _ = (x, 1) := by rw [hh]
        rw [List.foldl_cons, hstep,
          foldl_rightStep_part_map σ (List.range' (b + 1) m) s n ls
            (hpositive ls hls),
          foldl_rightStep_count, hfoldRight ls x (b + 1) 0 hxchild hp] at hle
        change 1 + (ls.foldl (rightStep σ) (b + 1, 0)).2 ≤
          τ.rightExt s top' (b + 1) at hle
        rw [rightExt_eq, heq]
        omega
    have hboth : ∀ top top',
        τ.levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1) →
        σ.leftExt s top (b + 1) + σ.rightExt s top (b + 1) + 2 ≤
          τ.leftExt s top' (b + 1) + τ.rightExt s top' (b + 1) := by
      intro top top' hlevels
      have hl := hleftInc top top' hlevels
      have hr := hrightInc top top' hlevels
      omega
    have hc : σ.chainExt s (b + 1) (b + 1) + 2 ≤
        τ.chainExt s (b + 1) (b + 1) := by
      change σ.leftExt s 0 (b + 1) + σ.rightExt s 0 (b + 1) + 2 ≤
        τ.leftExt s 0 (b + 1) + τ.rightExt s 0 (b + 1)
      exact hboth 0 0 (by
        dsimp [τ]
        exact part_levelsOn_self_zero hside)
    have hone : 2 ≤ τ.joinExt s (b + 1) (b + 1) := by
      have := hc.trans (τ.chainExt_le_joinExt s (b + 1) (b + 1))
      omega
    have hterms :
        ((((σ.levelsOn s 0).map fun N ↦
          σ.leftExt s N (b + 1) + σ.rightExt s N (b + 1) +
            σ.maximumAt N).max?).getD 0) + 2 ≤
          τ.joinExt s (b + 1) (b + 1) := by
      rcases hv : ((σ.levelsOn s 0).map fun N ↦
          σ.leftExt s N (b + 1) + σ.rightExt s N (b + 1) +
            σ.maximumAt N).max? with _ | v
      · simpa [hv] using hone
      · obtain ⟨N, hN, hval⟩ := List.mem_map.1 (List.max?_mem hv)
        have hN1 := (one_le_of_mem_levelsOn hN).1
        have hbGrow := hboth N (N + 1) (by
          dsimp [τ]
          exact part_levelsOn_self_succ hside hN1)
        have hnew : N + 1 ∈ τ.levelsOn s 0 := by
          dsimp [τ]
          rw [part_levelsOn_self_zero hside]
          exact List.mem_cons.2 (Or.inr (List.mem_map.2 ⟨N, hN, rfl⟩))
        have hj : τ.leftExt s (N + 1) (b + 1) +
              τ.rightExt s (N + 1) (b + 1) + τ.maximumAt (N + 1) ≤
            τ.joinExt s (b + 1) (b + 1) :=
          le_joinExt_of_mem_levelsOn hnew (b + 1) (b + 1)
        have hmaxEq : τ.maximumAt (N + 1) = σ.maximumAt N := by
          dsimp [τ]
          exact part_maximumAt_succ σ (List.range' (b + 1) m) s n hN1
        rw [hmaxEq] at hj
        simp only [Option.getD_some]
        rw [← hval]
        dsimp [τ] at hbGrow hj ⊢
        omega
    refine ⟨hc, ?_, ?_⟩
    · have hc' := hc.trans (τ.chainExt_le_joinExt s (b + 1) (b + 1))
      change max (σ.chainExt s (b + 1) (b + 1))
          ((((σ.levelsOn s 0).map fun N ↦
            σ.leftExt s N (b + 1) + σ.rightExt s N (b + 1) +
              σ.maximumAt N).max?).getD 0) + 2 ≤
        τ.joinExt s (b + 1) (b + 1)
      omega
    · have hnew : 1 ∈ τ.levelsOn s 0 := by
        dsimp [τ]
        rw [part_levelsOn_self_zero hside]
        simp
      have hj : τ.leftExt s 1 (b + 1) + τ.rightExt s 1 (b + 1) +
            τ.maximumAt 1 ≤ τ.joinExt s (b + 1) (b + 1) :=
        le_joinExt_of_mem_levelsOn hnew (b + 1) (b + 1)
      have hmaxEq : τ.maximumAt 1 = n := by
        dsimp [τ]
        exact part_maximumAt_one σ (List.range' (b + 1) m) s n
      rw [hmaxEq] at hj
      dsimp [τ] at hj ⊢
      omega
  have hmiddleBound : ∀ (s : Side) (n : ℕ),
      (σ.part (List.range' (b + 1) m) s n).bound ≤
        match s with
        | Side.lower =>
            baseOf (min (σ.cupLimit b b - 2) (σ.k - 1 - n))
              (σ.capLimit b b) σ.k
        | Side.upper =>
            baseOf (σ.cupLimit b b)
              (min (σ.capLimit b b - 2) (σ.k - 1 - n)) σ.k := by
    intro s n
    have hg := htwoGrow s n
    rw [hrunBound _ (b + 1) m hm (hpartMiddle s n)]
    cases s with
    | lower =>
      have hc : (σ.part (List.range' (b + 1) m) Side.lower n).cupLimit
          (b + 1) (b + 1) ≤
          min (σ.cupLimit b b - 2) (σ.k - 1 - n) := by
        rw [hchainEq Side.lower (b + 1) b hp hb,
          hjoinEq Side.lower (b + 1) b hp hb] at hg
        change min
            (σ.u - 1 - (σ.part (List.range' (b + 1) m) Side.lower n).chainExt
              Side.lower (b + 1) (b + 1))
            (σ.k - 1 - (σ.part (List.range' (b + 1) m) Side.lower n).joinExt
              Side.lower (b + 1) (b + 1)) ≤
          min (min (σ.u - 1 - σ.chainExt Side.lower b b)
            (σ.k - 1 - σ.joinExt Side.lower b b) - 2) (σ.k - 1 - n)
        omega
      have hp' : (σ.part (List.range' (b + 1) m) Side.lower n).capLimit
          (b + 1) (b + 1) = σ.capLimit b b := by
        have hnewSide :
            (σ.part (List.range' (b + 1) m) Side.lower n).sideAt 1 ≠ Side.upper := by
          have hbext : b ∈
              (σ.part (List.range' (b + 1) m) Side.lower n).extPositions 1 := by
            rw [part_extPositions_one hlet]
            simp [hb, hbnot]
          rw [part_sideAt_one_of_mem hlet (List.range' (b + 1) m)
            Side.lower n hbext]
          decide
        change min
            (σ.a - 1 - (σ.part (List.range' (b + 1) m) Side.lower n).chainExt
              Side.upper (b + 1) (b + 1))
            (σ.k - 1 - (σ.part (List.range' (b + 1) m) Side.lower n).joinExt
              Side.upper (b + 1) (b + 1)) = _
        rw [chainExt_part_other hnewSide, joinExt_part_other hnewSide,
          hchainEq Side.upper (b + 1) b hp hb,
          hjoinEq Side.upper (b + 1) b hp hb]
        rfl
      exact baseOf_mono hc hp'.le
    | upper =>
      have hp' : (σ.part (List.range' (b + 1) m) Side.upper n).capLimit
          (b + 1) (b + 1) ≤
          min (σ.capLimit b b - 2) (σ.k - 1 - n) := by
        rw [hchainEq Side.upper (b + 1) b hp hb,
          hjoinEq Side.upper (b + 1) b hp hb] at hg
        change min
            (σ.a - 1 - (σ.part (List.range' (b + 1) m) Side.upper n).chainExt
              Side.upper (b + 1) (b + 1))
            (σ.k - 1 - (σ.part (List.range' (b + 1) m) Side.upper n).joinExt
              Side.upper (b + 1) (b + 1)) ≤
          min (min (σ.a - 1 - σ.chainExt Side.upper b b)
            (σ.k - 1 - σ.joinExt Side.upper b b) - 2) (σ.k - 1 - n)
        omega
      have hc : (σ.part (List.range' (b + 1) m) Side.upper n).cupLimit
          (b + 1) (b + 1) = σ.cupLimit b b := by
        have hnewSide :
            (σ.part (List.range' (b + 1) m) Side.upper n).sideAt 1 ≠ Side.lower := by
          have hbext : b ∈
              (σ.part (List.range' (b + 1) m) Side.upper n).extPositions 1 := by
            rw [part_extPositions_one hlet]
            simp [hb, hbnot]
          rw [part_sideAt_one_of_mem hlet (List.range' (b + 1) m)
            Side.upper n hbext]
          decide
        change min
            (σ.u - 1 - (σ.part (List.range' (b + 1) m) Side.upper n).chainExt
              Side.lower (b + 1) (b + 1))
            (σ.k - 1 - (σ.part (List.range' (b + 1) m) Side.upper n).joinExt
              Side.lower (b + 1) (b + 1)) = _
        rw [chainExt_part_other hnewSide, joinExt_part_other hnewSide,
          hchainEq Side.lower (b + 1) b hp hb,
          hjoinEq Side.lower (b + 1) b hp hb]
        rfl
      exact baseOf_mono hc.le hp'
  have two_child_bound_of_singleton_cuts :
      ∀ (τ : Ctx.Context) (p q B : ℕ),
        τ.childPositions = [p, q] →
        p ≠ q →
        2 ≤ τ.numRuns →
        (∀ d, 1 ≤ d → d ≤ τ.k - 2 →
          (τ.part [p] Ctx.Side.lower d).bound +
                (τ.part [q] Ctx.Side.upper (τ.k - 1 - d)).bound ≤ B ∧
            (τ.part [p] Ctx.Side.upper (τ.k - 1 - d)).bound +
                (τ.part [q] Ctx.Side.lower d).bound ≤ B) →
        τ.bound ≤ B := by
    intro τ p q B hpos hpq hruns hcut
    have hqp : q ≠ p := Ne.symm hpq
    have hblocks : τ.blocks = [[p], [q]] := by
      simp [Ctx.Context.blocks, hpos, List.range_succ]
    have hrestP : τ.childPositions.filter (fun x ↦ x ∉ [p]) = [q] := by
      rw [hpos]
      simp [hpq, hqp]
    have hrestQ : τ.childPositions.filter (fun x ↦ x ∉ [q]) = [p] := by
      rw [hpos]
      simp [hpq, hqp]
    have hpartP : ∀ s m, (τ.part [p] s m).childPositions = [p] := by
      intro s m
      rw [Ctx.Context.part_childPositions, hpos]
      simp [hpq, hqp]
    have hpartQ : ∀ s m, (τ.part [q] s m).childPositions = [q] := by
      intro s m
      rw [Ctx.Context.part_childPositions, hpos]
      simp [hpq, hqp]
    have hfuelP : ∀ s m,
        Ctx.Context.boundFuel 2 (τ.part [p] s m) = (τ.part [p] s m).bound := by
      intro s m
      unfold Ctx.Context.bound
      rw [hpartP]
      rfl
    have hfuelQ : ∀ s m,
        Ctx.Context.boundFuel 2 (τ.part [q] s m) = (τ.part [q] s m).bound := by
      intro s m
      unfold Ctx.Context.bound
      rw [hpartQ]
      rfl
    unfold Ctx.Context.bound
    rw [hpos]
    change Ctx.Context.boundFuel 3 τ ≤ B
    rw [Ctx.Context.boundFuel.eq_2, if_neg (by omega)]
    dsimp only
    apply Ctx.getD_max?_le
    intro x hx
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    obtain ⟨block, hblock, d', hd', hx⟩ := hx
    rw [hblocks] at hblock
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hblock
    have hc := hcut (d' + 1) (by omega) (by omega)
    rcases hblock with rfl | rfl
    · rw [hrestP] at hx
      rcases hx with rfl | rfl
      · rw [hfuelP Side.lower (d' + 1),
          hfuelQ Side.upper (τ.k - 1 - (d' + 1))]
        exact hc.1
      · rw [hfuelP Side.upper (τ.k - 1 - (d' + 1)),
          hfuelQ Side.lower (d' + 1)]
        exact hc.2
    · rw [hrestQ] at hx
      rcases hx with rfl | rfl
      · rw [hfuelQ Side.lower (d' + 1),
          hfuelP Side.upper (τ.k - 1 - (d' + 1))]
        simpa only [Nat.add_comm] using hc.2
      · rw [hfuelQ Side.upper (τ.k - 1 - (d' + 1)),
          hfuelP Side.lower (d' + 1)]
        simpa only [Nat.add_comm] using hc.1
  have hjoinEarlier : ∀ (π : Context) (s : Side) (L N p q : ℕ),
      L ∈ π.levelsOn s N → N ∈ π.levelsOn s 0 →
      q ∈ π.extPositions L → p ≠ q →
      π.maximumAt N + 1 ≤ π.joinExt s p p := by
    intro π s L N p q hL hN hq hpq
    have hsub : [L] ∈ (π.levelsOn s N).sublists :=
      List.mem_sublists.2 (List.singleton_sublist.2 hL)
    have hj := le_joinExt_of_mem_levelsOn hN p p
    rcases lt_or_gt_of_ne hpq with hpq | hqp
    · have hqfilter : q ∈ (π.extPositions L).filter (p < ·) := by
        simp [hq, hpq]
      rcases hh : ((π.extPositions L).filter (p < ·)).head? with _ | x
      · have hnil := List.head?_eq_none_iff.1 hh
        rw [hnil] at hqfilter
        simp at hqfilter
      · have hle := le_getD_max?_of_mem
          (List.mem_map.2 ⟨[L], hsub, rfl⟩ :
            ([L].foldl (rightStep π) (p, 0)).2 ∈
              (π.levelsOn s N).sublists.map
                (fun xs ↦ (xs.foldl (rightStep π) (p, 0)).2))
        have hstep : ([L].foldl (rightStep π) (p, 0)).2 = 1 := by
          simp [rightStep, hh]
        rw [hstep] at hle
        change 1 ≤ π.rightExt s N p at hle
        omega
    · have hqfilter : q ∈ (π.extPositions L).filter (· < p) := by
        simp [hq, hqp]
      rcases hh : ((π.extPositions L).filter (· < p)).getLast? with _ | x
      · have hnil := List.getLast?_eq_none_iff.1 hh
        rw [hnil] at hqfilter
        simp at hqfilter
      · have hle := le_getD_max?_of_mem
          (List.mem_map.2 ⟨[L], hsub, rfl⟩ :
            ([L].foldl (leftStep π) (p, 0)).2 ∈
              (π.levelsOn s N).sublists.map
                (fun xs ↦ (xs.foldl (leftStep π) (p, 0)).2))
        have hstep : ([L].foldl (leftStep π) (p, 0)).2 = 1 := by
          simp [leftStep, hh]
        rw [hstep] at hle
        change 1 ≤ π.leftExt s N p at hle
        omega
  have hpartSelfMonotone : ∀ (τ : Context) (keep : List ℕ) (s : Side) (m p : ℕ),
      (τ.part keep s m).sideAt 1 = s →
      τ.chainExt s p p ≤ (τ.part keep s m).chainExt s p p ∧
      τ.joinExt s p p ≤ (τ.part keep s m).joinExt s p p := by
    intro τ keep s m p hside
    have hboth : ∀ top top',
        (τ.part keep s m).levelsOn s top' = 1 :: (τ.levelsOn s top).map (· + 1) →
        τ.leftExt s top p ≤ (τ.part keep s m).leftExt s top' p ∧
        τ.rightExt s top p ≤ (τ.part keep s m).rightExt s top' p := by
      intro top top' hlevels
      have hpositive : ∀ ls ∈ (τ.levelsOn s top).sublists, ∀ N ∈ ls, 1 ≤ N := by
        intro ls hls N hN
        exact (one_le_of_mem_levelsOn ((List.mem_sublists.1 hls).subset hN)).1
      have hsub : ∀ ls ∈ (τ.levelsOn s top).sublists,
          ls.map (· + 1) ∈ ((τ.part keep s m).levelsOn s top').sublists := by
        intro ls hls
        rw [hlevels, List.mem_sublists]
        exact List.sublist_cons_iff.2 (Or.inl ((List.mem_sublists.1 hls).map _))
      constructor
      · obtain ⟨ls, hls, heq⟩ := hmaxWitness (τ.levelsOn s top)
          (fun ls ↦ (ls.foldl (leftStep τ) (p, 0)).2)
        rw [leftExt_eq, heq]
        have hle := le_getD_max?_of_mem
          (List.mem_map.2 ⟨ls.map (· + 1), hsub ls hls, rfl⟩ :
            ((ls.map (· + 1)).foldl (leftStep (τ.part keep s m)) (p, 0)).2 ∈
              ((τ.part keep s m).levelsOn s top').sublists.map
                (fun xs ↦ (xs.foldl (leftStep (τ.part keep s m)) (p, 0)).2))
        rw [foldl_leftStep_part_map τ keep s m ls (hpositive ls hls)] at hle
        exact hle
      · obtain ⟨ls, hls, heq⟩ := hmaxWitness (τ.levelsOn s top)
          (fun ls ↦ (ls.foldl (rightStep τ) (p, 0)).2)
        rw [rightExt_eq, heq]
        have hle := le_getD_max?_of_mem
          (List.mem_map.2 ⟨ls.map (· + 1), hsub ls hls, rfl⟩ :
            ((ls.map (· + 1)).foldl (rightStep (τ.part keep s m)) (p, 0)).2 ∈
              ((τ.part keep s m).levelsOn s top').sublists.map
                (fun xs ↦ (xs.foldl (rightStep (τ.part keep s m)) (p, 0)).2))
        rw [foldl_rightStep_part_map τ keep s m ls (hpositive ls hls)] at hle
        exact hle
    have hc : τ.chainExt s p p ≤ (τ.part keep s m).chainExt s p p := by
      have h := hboth 0 0 (part_levelsOn_self_zero hside)
      exact Nat.add_le_add h.1 h.2
    have ht : (((τ.levelsOn s 0).map fun N ↦
        τ.leftExt s N p + τ.rightExt s N p + τ.maximumAt N).max?).getD 0 ≤
        (τ.part keep s m).joinExt s p p := by
      apply getD_max?_le
      intro x hx
      obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hx
      have hN1 := (one_le_of_mem_levelsOn hN).1
      have h := hboth N (N + 1) (part_levelsOn_self_succ hside hN1)
      have hnew : N + 1 ∈ (τ.part keep s m).levelsOn s 0 := by
        rw [part_levelsOn_self_zero hside]
        exact List.mem_cons.2 (Or.inr (List.mem_map.2 ⟨N, hN, rfl⟩))
      have hj := le_joinExt_of_mem_levelsOn hnew p p
      rw [part_maximumAt_succ τ keep s m hN1] at hj
      omega
    exact ⟨hc, max_le (hc.trans ((τ.part keep s m).chainExt_le_joinExt s p p)) ht⟩
  have hpartOuter : ∀ s n,
      (σ.part [b, b + m + 1] s n).childPositions = [b, b + m + 1] := by
    intro s n
    rw [part_childPositions, hpos, hsplit]
    have hmiddleNil : (List.range' (b + 1) m).filter
        (fun x ↦ x ∈ [b, b + m + 1]) = [] := by
      apply List.filter_eq_nil_iff.2
      intro x hx
      simp only [List.mem_range'_1] at hx
      rw [show b + 1 + m = b + m + 1 by omega] at hx
      simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨
        ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self b) hx.1),
        ne_of_lt hx.2⟩
    rw [List.filter_append, List.filter_append, hmiddleNil]
    simp [show b ≠ b + m + 1 by omega, show b + m + 1 ≠ b by omega]
  have hpartLeaf : ∀ s n t e p,
      (p = b ∨ p = b + m + 1) →
      ((σ.part [b, b + m + 1] s n).part [p] t e).childPositions = [p] := by
    intro s n t e p hpEnd
    rw [part_childPositions, hpartOuter]
    rcases hpEnd with hpEnd | hpEnd
    · simpa [hpEnd, show b + m + 1 ≠ b by omega]
    · simpa [hpEnd, show b ≠ b + m + 1 by omega]
  have hmiddleNotOuter : b + 1 ∉ [b, b + m + 1] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by omega, ne_of_lt (by omega)⟩
  have htwoSeparatedRuns : ∀ (τ : Context) (p q : ℕ),
      τ.childPositions = [p, q] → p + 1 < q → 2 ≤ τ.numRuns := by
    intro τ p q hτpos hpq
    let starts := (List.range τ.word.length).filter fun x ↦
      τ.letterAt x = Letter.child ∧
        (x = 0 ∨ τ.letterAt (x - 1) ≠ Letter.child)
    have hpMem : p ∈ τ.childPositions := by rw [hτpos]; simp
    have hqMem : q ∈ τ.childPositions := by rw [hτpos]; simp
    have hstart : ∀ x ∈ τ.childPositions, x = p ∨ x = q → x ∈ starts := by
      intro x hx hxEnd
      have hxRange : x < τ.word.length := List.mem_range.1 (List.mem_filter.1 hx).1
      have hxLetter : τ.letterAt x = Letter.child :=
        of_decide_eq_true (List.mem_filter.1 hx).2
      have hxCondition : x = 0 ∨ τ.letterAt (x - 1) ≠ Letter.child := by
        by_cases hx0 : x = 0
        · exact Or.inl hx0
        · right
          intro hprevLetter
          have hx1 : 1 ≤ x := by omega
          have hprevSucc : x - 1 + 1 = x := Nat.sub_add_cancel hx1
          have hprevMem : x - 1 ∈ τ.childPositions := by
            apply List.mem_filter.2
            exact ⟨List.mem_range.2 (by omega), by simpa using hprevLetter⟩
          rw [hτpos] at hprevMem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hprevMem
          rcases hxEnd with hxP | hxQ
          · rcases hprevMem with hprevP | hprevQ
            · rw [hprevP] at hprevSucc
              omega
            · rw [hprevQ] at hprevSucc
              omega
          · rcases hprevMem with hprevP | hprevQ
            · rw [hprevP] at hprevSucc
              omega
            · rw [hprevQ] at hprevSucc
              omega
      simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hxRange, hxLetter, hxCondition⟩
    have hpStart := hstart p hpMem (Or.inl rfl)
    have hqStart := hstart q hqMem (Or.inr rfl)
    have hsubset : ({p, q} : Finset ℕ) ⊆ starts.toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact List.mem_toFinset.2 hpStart
      · exact List.mem_toFinset.2 hqStart
    have hcard := Finset.card_le_card hsubset
    have hpair : ({p, q} : Finset ℕ).card = 2 :=
      Finset.card_pair (by omega)
    rw [hpair, List.toFinset_card_of_nodup (List.nodup_range.filter _)] at hcard
    simpa [starts, Context.numRuns] using hcard
  have houterRuns : ∀ s n, 2 ≤ (σ.part [b, b + m + 1] s n).numRuns := by
    intro s n
    exact htwoSeparatedRuns _ b (b + m + 1) (hpartOuter s n) (by omega)
  have hotherGrow : ∀ (s t : Side) (d e p q : ℕ),
      1 ≤ d → d ≤ σ.k - 2 → s ≠ t →
      (p = b ∨ p = b + m + 1) → (q = b ∨ q = b + m + 1) → p ≠ q →
      σ.chainExt t p p + 1 ≤
          ((σ.part [b, b + m + 1] s d).part [p] t e).chainExt t p p ∧
      σ.joinExt t p p + 1 ≤
          ((σ.part [b, b + m + 1] s d).part [p] t e).joinExt t p p ∧
      e ≤ ((σ.part [b, b + m + 1] s d).part [p] t e).joinExt t p p := by
    intro s t d e p q hd1 hdk hst hpEnd hqEnd hpq
    let outer : List ℕ := [b, b + m + 1]
    let τ := σ.part outer s d
    have hpTau : p ∈ τ.childPositions := by
      dsimp [τ, outer]
      rw [hpartOuter]
      rcases hpEnd with rfl | rfl <;> simp
    have hqTau : q ∈ τ.childPositions := by
      dsimp [τ, outer]
      rw [hpartOuter]
      rcases hqEnd with rfl | rfl <;> simp
    have hrExt : b + 1 ∈ τ.extPositions 1 := by
      dsimp [τ, outer]
      rw [part_extPositions_one hlet]
      simp [hp, hmiddleNotOuter] <;> omega
    have hτside : τ.sideAt 1 = s := by
      dsimp [τ, outer]
      exact part_sideAt_one_of_mem hlet [b, b + m + 1] s d hrExt
    have hwfTau : τ.WellFormed := by
      dsimp [τ, outer]
      exact hwf.part [b, b + m + 1] s hd1 hdk
    have hletTau : ∀ x N v, τ.letterAt x = Letter.ext N v → 1 ≤ N :=
      fun x N v h ↦ (hwfTau.2.2.2.2.2 x N v h).1
    have hlevelsTauTwo : ∀ top N, N ∈ τ.levelsOn t top → 2 ≤ N := by
      intro top N hN
      obtain ⟨hN1, _, hNt⟩ := one_le_of_mem_levelsOn hN
      by_contra hN2
      have hN_eq : N = 1 := by omega
      subst N
      rw [hτside] at hNt
      exact hst hNt

    have hfoldLeftTau : ∀ (ls : List ℕ) x y c,
        (∀ N ∈ ls, 2 ≤ N) →
        x ∈ τ.childPositions → y ∈ τ.childPositions →
        (ls.foldl (leftStep τ) (x, c)).2 =
          (ls.foldl (leftStep τ) (y, c)).2 := by
      intro ls x y c htwo hx hy
      let oldls := ls.map (· - 1)
      have hold : ∀ N ∈ oldls, 1 ≤ N := by
        intro N hN
        obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hN
        have := htwo L hL
        omega
      have hmap : oldls.map (· + 1) = ls := by
        dsimp [oldls]
        calc
          (ls.map (· - 1)).map (· + 1) =
              ls.map ((· + 1) ∘ (· - 1)) := List.map_map
          _ = ls.map (id : ℕ → ℕ) := by
            apply List.map_congr_left
            intro N hN
            simp only [Function.comp_apply, id_eq]
            have := htwo N hN
            omega
          _ = ls := List.map_id ls
      have hxSigma : x ∈ σ.childPositions := by
        have hx' := hx
        dsimp [τ] at hx'
        rw [part_childPositions] at hx'
        exact (List.mem_filter.1 hx').1
      have hySigma : y ∈ σ.childPositions := by
        have hy' := hy
        dsimp [τ] at hy'
        rw [part_childPositions] at hy'
        exact (List.mem_filter.1 hy').1
      calc
        (ls.foldl (leftStep τ) (x, c)).2 =
            ((oldls.map (· + 1)).foldl (leftStep τ) (x, c)).2 := by
          rw [hmap]
        _ = (oldls.foldl (leftStep σ) (x, c)).2 := by
          dsimp [τ]
          rw [foldl_leftStep_part_map σ outer s d oldls hold]
        _ = (oldls.foldl (leftStep σ) (y, c)).2 :=
          hfoldLeft oldls x y c hxSigma hySigma
        _ = ((oldls.map (· + 1)).foldl (leftStep τ) (y, c)).2 := by
          dsimp [τ]
          rw [foldl_leftStep_part_map σ outer s d oldls hold]
        _ = (ls.foldl (leftStep τ) (y, c)).2 := by
          rw [hmap]

    have hfoldRightTau : ∀ (ls : List ℕ) x y c,
        (∀ N ∈ ls, 2 ≤ N) →
        x ∈ τ.childPositions → y ∈ τ.childPositions →
        (ls.foldl (rightStep τ) (x, c)).2 =
          (ls.foldl (rightStep τ) (y, c)).2 := by
      intro ls x y c htwo hx hy
      let oldls := ls.map (· - 1)
      have hold : ∀ N ∈ oldls, 1 ≤ N := by
        intro N hN
        obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hN
        have := htwo L hL
        omega
      have hmap : oldls.map (· + 1) = ls := by
        dsimp [oldls]
        calc
          (ls.map (· - 1)).map (· + 1) =
              ls.map ((· + 1) ∘ (· - 1)) := List.map_map
          _ = ls.map (id : ℕ → ℕ) := by
            apply List.map_congr_left
            intro N hN
            simp only [Function.comp_apply, id_eq]
            have := htwo N hN
            omega
          _ = ls := List.map_id ls
      have hxSigma : x ∈ σ.childPositions := by
        have hx' := hx
        dsimp [τ] at hx'
        rw [part_childPositions] at hx'
        exact (List.mem_filter.1 hx').1
      have hySigma : y ∈ σ.childPositions := by
        have hy' := hy
        dsimp [τ] at hy'
        rw [part_childPositions] at hy'
        exact (List.mem_filter.1 hy').1
      calc
        (ls.foldl (rightStep τ) (x, c)).2 =
            ((oldls.map (· + 1)).foldl (rightStep τ) (x, c)).2 := by
          rw [hmap]
        _ = (oldls.foldl (rightStep σ) (x, c)).2 := by
          dsimp [τ]
          rw [foldl_rightStep_part_map σ outer s d oldls hold]
        _ = (oldls.foldl (rightStep σ) (y, c)).2 :=
          hfoldRight oldls x y c hxSigma hySigma
        _ = ((oldls.map (· + 1)).foldl (rightStep τ) (y, c)).2 := by
          dsimp [τ]
          rw [foldl_rightStep_part_map σ outer s d oldls hold]
        _ = (ls.foldl (rightStep τ) (y, c)).2 := by
          rw [hmap]

    have hgrowTauOther :
        τ.chainExt t p p + 1 ≤ (τ.part [p] t e).chainExt t p p ∧
        τ.joinExt t p p + 1 ≤ (τ.part [p] t e).joinExt t p p ∧
        e ≤ (τ.part [p] t e).joinExt t p p := by
      have hqp : q ≠ p := Ne.symm hpq
      have hqext : q ∈ (τ.part [p] t e).extPositions 1 := by
        rw [part_extPositions_one hletTau]
        simp [hqTau, hqp]
      have hside := part_sideAt_one_of_mem hletTau [p] t e hqext
      have hboth : ∀ top top',
          (τ.part [p] t e).levelsOn t top' =
              1 :: (τ.levelsOn t top).map (· + 1) →
          τ.leftExt t top p + τ.rightExt t top p + 1 ≤
            (τ.part [p] t e).leftExt t top' p +
              (τ.part [p] t e).rightExt t top' p := by
        intro top top' hlevels
        have hpositiveTwo : ∀ ls ∈ (τ.levelsOn t top).sublists,
            ∀ N ∈ ls, 2 ≤ N := by
          intro ls hls N hN
          exact hlevelsTauTwo top N ((List.mem_sublists.1 hls).subset hN)
        have hpositive : ∀ ls ∈ (τ.levelsOn t top).sublists,
            ∀ N ∈ ls, 1 ≤ N := by
          intro ls hls N hN
          have := hpositiveTwo ls hls N hN
          omega
        have hleft : τ.leftExt t top p ≤
            (τ.part [p] t e).leftExt t top' p := by
          obtain ⟨ls, hls, heq⟩ := hmaxWitness (τ.levelsOn t top)
            (fun ls ↦ (ls.foldl (leftStep τ) (p, 0)).2)
          rw [leftExt_eq, heq]
          have hsub : ls.map (· + 1) ∈
              ((τ.part [p] t e).levelsOn t top').sublists := by
            rw [hlevels, List.mem_sublists]
            exact List.sublist_cons_iff.2
              (Or.inl ((List.mem_sublists.1 hls).map _))
          have hle := le_getD_max?_of_mem
            (List.mem_map.2 ⟨ls.map (· + 1), hsub, rfl⟩ :
              ((ls.map (· + 1)).foldl
                (leftStep (τ.part [p] t e)) (p, 0)).2 ∈
                ((τ.part [p] t e).levelsOn t top').sublists.map
                  (fun xs ↦ (xs.foldl (leftStep (τ.part [p] t e)) (p, 0)).2))
          rw [foldl_leftStep_part_map τ [p] t e ls (hpositive ls hls)] at hle
          exact hle
        have hright : τ.rightExt t top p ≤
            (τ.part [p] t e).rightExt t top' p := by
          obtain ⟨ls, hls, heq⟩ := hmaxWitness (τ.levelsOn t top)
            (fun ls ↦ (ls.foldl (rightStep τ) (p, 0)).2)
          rw [rightExt_eq, heq]
          have hsub : ls.map (· + 1) ∈
              ((τ.part [p] t e).levelsOn t top').sublists := by
            rw [hlevels, List.mem_sublists]
            exact List.sublist_cons_iff.2
              (Or.inl ((List.mem_sublists.1 hls).map _))
          have hle := le_getD_max?_of_mem
            (List.mem_map.2 ⟨ls.map (· + 1), hsub, rfl⟩ :
              ((ls.map (· + 1)).foldl
                (rightStep (τ.part [p] t e)) (p, 0)).2 ∈
                ((τ.part [p] t e).levelsOn t top').sublists.map
                  (fun xs ↦ (xs.foldl (rightStep (τ.part [p] t e)) (p, 0)).2))
          rw [foldl_rightStep_part_map τ [p] t e ls (hpositive ls hls)] at hle
          exact hle
        rcases lt_or_gt_of_ne hpq with hpq' | hqp'
        · have hinc : τ.rightExt t top p + 1 ≤
              (τ.part [p] t e).rightExt t top' p := by
            obtain ⟨ls, hls, heq⟩ := hmaxWitness (τ.levelsOn t top)
              (fun ls ↦ (ls.foldl (rightStep τ) (p, 0)).2)
            have hqfilter :
                q ∈ ((τ.part [p] t e).extPositions 1).filter (p < ·) := by
              simp [hqext, hpq']
            rcases hh : (((τ.part [p] t e).extPositions 1).filter
                (p < ·)).head? with _ | x
            · have hnil := List.head?_eq_none_iff.1 hh
              rw [hnil] at hqfilter
              simp at hqfilter
            · have hx := List.mem_of_mem_head? (Option.mem_def.2 hh)
              have hxext := (List.mem_filter.1 hx).1
              rw [part_extPositions_one hletTau] at hxext
              have hxchild := (List.mem_filter.1 hxext).1
              have hsub : 1 :: ls.map (· + 1) ∈
                  ((τ.part [p] t e).levelsOn t top').sublists := by
                rw [hlevels, List.mem_sublists]
                exact List.sublist_cons_iff.2
                  (Or.inr ⟨_, rfl, (List.mem_sublists.1 hls).map _⟩)
              have hle := le_getD_max?_of_mem
                (List.mem_map.2 ⟨1 :: ls.map (· + 1), hsub, rfl⟩ :
                  ((1 :: ls.map (· + 1)).foldl
                    (rightStep (τ.part [p] t e)) (p, 0)).2 ∈
                    ((τ.part [p] t e).levelsOn t top').sublists.map
                      (fun xs ↦
                        (xs.foldl (rightStep (τ.part [p] t e)) (p, 0)).2))
              have hstep : rightStep (τ.part [p] t e) (p, 0) 1 =
                  (x, 1) := by
                simp [rightStep, hh]
              rw [List.foldl_cons, hstep,
                foldl_rightStep_part_map τ [p] t e ls (hpositive ls hls),
                foldl_rightStep_count,
                hfoldRightTau ls x p 0 (hpositiveTwo ls hls) hxchild hpTau] at hle
              change 1 + (ls.foldl (rightStep τ) (p, 0)).2 ≤
                (τ.part [p] t e).rightExt t top' p at hle
              rw [rightExt_eq, heq]
              omega
          omega
        · have hinc : τ.leftExt t top p + 1 ≤
              (τ.part [p] t e).leftExt t top' p := by
            obtain ⟨ls, hls, heq⟩ := hmaxWitness (τ.levelsOn t top)
              (fun ls ↦ (ls.foldl (leftStep τ) (p, 0)).2)
            have hqfilter :
                q ∈ ((τ.part [p] t e).extPositions 1).filter (· < p) := by
              simp [hqext, hqp']
            rcases hh : (((τ.part [p] t e).extPositions 1).filter
                (· < p)).getLast? with _ | x
            · have hnil := List.getLast?_eq_none_iff.1 hh
              rw [hnil] at hqfilter
              simp at hqfilter
            · have hx := List.mem_of_mem_getLast? (Option.mem_def.2 hh)
              have hxext := (List.mem_filter.1 hx).1
              rw [part_extPositions_one hletTau] at hxext
              have hxchild := (List.mem_filter.1 hxext).1
              have hsub : 1 :: ls.map (· + 1) ∈
                  ((τ.part [p] t e).levelsOn t top').sublists := by
                rw [hlevels, List.mem_sublists]
                exact List.sublist_cons_iff.2
                  (Or.inr ⟨_, rfl, (List.mem_sublists.1 hls).map _⟩)
              have hle := le_getD_max?_of_mem
                (List.mem_map.2 ⟨1 :: ls.map (· + 1), hsub, rfl⟩ :
                  ((1 :: ls.map (· + 1)).foldl
                    (leftStep (τ.part [p] t e)) (p, 0)).2 ∈
                    ((τ.part [p] t e).levelsOn t top').sublists.map
                      (fun xs ↦
                        (xs.foldl (leftStep (τ.part [p] t e)) (p, 0)).2))
              have hstep : leftStep (τ.part [p] t e) (p, 0) 1 =
                  (x, 1) := by
                simp [leftStep, hh]
              rw [List.foldl_cons, hstep,
                foldl_leftStep_part_map τ [p] t e ls (hpositive ls hls),
                foldl_leftStep_count,
                hfoldLeftTau ls x p 0 (hpositiveTwo ls hls) hxchild hpTau] at hle
              change 1 + (ls.foldl (leftStep τ) (p, 0)).2 ≤
                (τ.part [p] t e).leftExt t top' p at hle
              rw [leftExt_eq, heq]
              omega
          omega
      have hc : τ.chainExt t p p + 1 ≤
          (τ.part [p] t e).chainExt t p p :=
        hboth 0 0 (part_levelsOn_self_zero hside)
      have hone : 1 ≤ (τ.part [p] t e).joinExt t p p := by
        have := (τ.part [p] t e).chainExt_le_joinExt t p p
        omega
      have hterms :
          ((((τ.levelsOn t 0).map fun N ↦
            τ.leftExt t N p + τ.rightExt t N p + τ.maximumAt N).max?).getD 0) + 1 ≤
            (τ.part [p] t e).joinExt t p p := by
        rcases hv : ((τ.levelsOn t 0).map fun N ↦
            τ.leftExt t N p + τ.rightExt t N p + τ.maximumAt N).max? with _ | v
        · simpa [hv] using hone
        · obtain ⟨N, hN, hval⟩ := List.mem_map.1 (List.max?_mem hv)
          have hN1 := (one_le_of_mem_levelsOn hN).1
          have hbGrow := hboth N (N + 1)
            (part_levelsOn_self_succ hside hN1)
          have hnew : N + 1 ∈ (τ.part [p] t e).levelsOn t 0 := by
            rw [part_levelsOn_self_zero hside]
            exact List.mem_cons.2
              (Or.inr (List.mem_map.2 ⟨N, hN, rfl⟩))
          have hj := le_joinExt_of_mem_levelsOn hnew p p
          rw [part_maximumAt_succ τ [p] t e hN1] at hj
          simp only [Option.getD_some]
          rw [← hval]
          omega
      refine ⟨hc, ?_, ?_⟩
      · have hc' := hc.trans ((τ.part [p] t e).chainExt_le_joinExt t p p)
        change max (τ.chainExt t p p)
            ((((τ.levelsOn t 0).map fun N ↦
              τ.leftExt t N p + τ.rightExt t N p + τ.maximumAt N).max?).getD 0) + 1 ≤
            (τ.part [p] t e).joinExt t p p
        omega
      · have hnew : 1 ∈ (τ.part [p] t e).levelsOn t 0 := by
          rw [part_levelsOn_self_zero hside]
          simp
        have hj := le_joinExt_of_mem_levelsOn hnew p p
        rw [part_maximumAt_one] at hj
        omega

    -- Rewrite the parent side of hgrowTauOther to σ.  The level one of τ is s,
    -- hence it is not t.
    have hτother : τ.sideAt 1 ≠ t := by
      rw [hτside]
      exact hst
    have hgrowSigmaInner :
        σ.chainExt t p p + 1 ≤ (τ.part [p] t e).chainExt t p p ∧
        σ.joinExt t p p + 1 ≤ (τ.part [p] t e).joinExt t p p ∧
        e ≤ (τ.part [p] t e).joinExt t p p := by
      have hτChain : τ.chainExt t p p = σ.chainExt t p p := by
        dsimp [τ, outer]
        exact chainExt_part_other hτother p p
      have hτJoin : τ.joinExt t p p = σ.joinExt t p p := by
        dsimp [τ, outer]
        exact joinExt_part_other hτother p p
      rw [hτChain, hτJoin] at hgrowTauOther
      exact hgrowTauOther
    change σ.chainExt t p p + 1 ≤ (τ.part [p] t e).chainExt t p p ∧
      σ.joinExt t p p + 1 ≤ (τ.part [p] t e).joinExt t p p ∧
      e ≤ (τ.part [p] t e).joinExt t p p
    exact hgrowSigmaInner
  have hsameLeaf : ∀ (s : Side) (od im p q : ℕ),
      1 ≤ od → od ≤ σ.k - 2 → 1 ≤ im → im ≤ σ.k - 2 →
      (p = b ∨ p = b + m + 1) → (q = b ∨ q = b + m + 1) → p ≠ q →
      ((σ.part [b, b + m + 1] s od).part [p] s im).bound ≤
        match s with
        | Side.lower =>
            baseOf (min (min (σ.cupLimit b b - 1) (σ.k - 1 - im))
              (σ.k - 2 - od)) (σ.capLimit b b) σ.k
        | Side.upper =>
            baseOf (σ.cupLimit b b)
              (min (min (σ.capLimit b b - 1) (σ.k - 1 - im))
                (σ.k - 2 - od)) σ.k := by
    intro s od im p q hod1 hodk him1 himk hpEnd hqEnd hpq
    let τ := σ.part [b, b + m + 1] s od
    let π := τ.part [p] s im
    have hpσ : p ∈ σ.childPositions := by
      rcases hpEnd with hp | hp <;> subst p
      · exact hb
      · exact hq
    have hqσ : q ∈ σ.childPositions := by
      rcases hqEnd with hq' | hq' <;> subst q
      · exact hb
      · exact hq
    have hpMid : p ≠ b + 1 := by
      rcases hpEnd with hp | hp <;> omega
    have hg := hgrow [b, b + m + 1] s od p (b + 1) hpσ hp
      hmiddleNotOuter hpMid
    change σ.chainExt s p p + 1 ≤ τ.chainExt s p p ∧
      σ.joinExt s p p + 1 ≤ τ.joinExt s p p ∧
      od ≤ τ.joinExt s p p at hg
    have hrExt : b + 1 ∈ τ.extPositions 1 := by
      dsimp [τ]
      rw [part_extPositions_one hlet]
      simp [hp, hmiddleNotOuter] <;> omega
    have hτside : τ.sideAt 1 = s := by
      dsimp [τ]
      exact part_sideAt_one_of_mem hlet [b, b + m + 1] s od hrExt
    have hwfτ : τ.WellFormed := by
      dsimp [τ]
      exact hwf.part [b, b + m + 1] s hod1 hodk
    have hletτ : ∀ x N t, τ.letterAt x = Letter.ext N t → 1 ≤ N :=
      fun x N t h ↦ (hwfτ.2.2.2.2.2 x N t h).1
    have hqτ : q ∈ τ.childPositions := by
      dsimp [τ]
      rw [hpartOuter]
      rcases hqEnd with rfl | rfl <;> simp
    have hqNot : q ∉ [p] := by simp [Ne.symm hpq]
    have hqExt : q ∈ π.extPositions 1 := by
      dsimp [π]
      rw [part_extPositions_one hletτ]
      simp [hqτ, Ne.symm hpq]
    have hπside : π.sideAt 1 = s := by
      dsimp [π]
      exact part_sideAt_one_of_mem hletτ [p] s im hqExt
    have hmono := hpartSelfMonotone τ [p] s im p hπside
    change τ.chainExt s p p ≤ π.chainExt s p p ∧
      τ.joinExt s p p ≤ π.joinExt s p p at hmono
    have himJoin : im ≤ π.joinExt s p p := by
      have hnew : 1 ∈ π.levelsOn s 0 := by
        dsimp [π]
        rw [part_levelsOn_self_zero hπside]
        simp
      have hj := le_joinExt_of_mem_levelsOn hnew p p
      have hmaxEq : π.maximumAt 1 = im := by
        dsimp [π]
        exact part_maximumAt_one τ [p] s im
      rw [hmaxEq] at hj
      omega
    have honeτ : 1 ∈ τ.levelsOn s 0 := by
      dsimp [τ]
      rw [part_levelsOn_self_zero hτside]
      simp
    have honeBelow : 1 ∈ π.levelsOn s 2 := by
      dsimp [π]
      rw [part_levelsOn_self_succ hπside (N := 1) (by omega)]
      simp
    have htwoπ : 2 ∈ π.levelsOn s 0 := by
      dsimp [π]
      rw [part_levelsOn_self_zero hπside]
      exact List.mem_cons.2 (Or.inr (List.mem_map.2 ⟨1, honeτ, rfl⟩))
    have hodJoin : od + 1 ≤ π.joinExt s p p := by
      have hj := hjoinEarlier π s 1 2 p q honeBelow htwoπ hqExt hpq
      have hmaxEq : π.maximumAt 2 = od := by
        calc
          π.maximumAt 2 = τ.maximumAt 1 := by
            dsimp [π]
            exact part_maximumAt_succ τ [p] s im (by omega)
          _ = od := by
            dsimp [τ]
            exact part_maximumAt_one σ [b, b + m + 1] s od
      rw [hmaxEq] at hj
      exact hj
    have hπpos : π.childPositions = [p] := by
      dsimp [π, τ]
      exact hpartLeaf s od s im p hpEnd
    rw [hrunBound π p 1 (by omega) hπpos]
    cases s with
    | lower =>
      have hc : π.cupLimit p p ≤
          min (min (σ.cupLimit b b - 1) (σ.k - 1 - im))
            (σ.k - 2 - od) := by
        rw [hchainEq Side.lower p b hpσ hb,
          hjoinEq Side.lower p b hpσ hb] at hg
        change min (σ.u - 1 - π.chainExt Side.lower p p)
            (σ.k - 1 - π.joinExt Side.lower p p) ≤
          min (min (min (σ.u - 1 - σ.chainExt Side.lower b b)
            (σ.k - 1 - σ.joinExt Side.lower b b) - 1)
            (σ.k - 1 - im)) (σ.k - 2 - od)
        omega
      have hcap : π.capLimit p p = σ.capLimit b b := by
        have hπne : π.sideAt 1 ≠ Side.upper := by rw [hπside]; decide
        have hτne : τ.sideAt 1 ≠ Side.upper := by rw [hτside]; decide
        change min (σ.a - 1 - π.chainExt Side.upper p p)
            (σ.k - 1 - π.joinExt Side.upper p p) = _
        rw [chainExt_part_other hπne, joinExt_part_other hπne,
          chainExt_part_other hτne, joinExt_part_other hτne,
          hchainEq Side.upper p b hpσ hb, hjoinEq Side.upper p b hpσ hb]
        rfl
      exact baseOf_mono hc hcap.le
    | upper =>
      have hcap : π.capLimit p p ≤
          min (min (σ.capLimit b b - 1) (σ.k - 1 - im))
            (σ.k - 2 - od) := by
        rw [hchainEq Side.upper p b hpσ hb,
          hjoinEq Side.upper p b hpσ hb] at hg
        change min (σ.a - 1 - π.chainExt Side.upper p p)
            (σ.k - 1 - π.joinExt Side.upper p p) ≤
          min (min (min (σ.a - 1 - σ.chainExt Side.upper b b)
            (σ.k - 1 - σ.joinExt Side.upper b b) - 1)
            (σ.k - 1 - im)) (σ.k - 2 - od)
        omega
      have hcup : π.cupLimit p p = σ.cupLimit b b := by
        have hπne : π.sideAt 1 ≠ Side.lower := by rw [hπside]; decide
        have hτne : τ.sideAt 1 ≠ Side.lower := by rw [hτside]; decide
        change min (σ.u - 1 - π.chainExt Side.lower p p)
            (σ.k - 1 - π.joinExt Side.lower p p) = _
        rw [chainExt_part_other hπne, joinExt_part_other hπne,
          chainExt_part_other hτne, joinExt_part_other hτne,
          hchainEq Side.lower p b hpσ hb, hjoinEq Side.lower p b hpσ hb]
        rfl
      exact baseOf_mono hcup.le hcap
  have hoppLeaf : ∀ (s t : Side) (d e p q : ℕ),
      1 ≤ d → d ≤ σ.k - 2 → s ≠ t →
      (p = b ∨ p = b + m + 1) → (q = b ∨ q = b + m + 1) → p ≠ q →
      ((σ.part [b, b + m + 1] s d).part [p] t e).bound ≤
        match s with
        | Side.lower =>
            baseOf (min (σ.cupLimit b b - 1) (σ.k - 1 - d))
              (min (σ.capLimit b b - 1) (σ.k - 1 - e)) σ.k
        | Side.upper =>
            baseOf (min (σ.cupLimit b b - 1) (σ.k - 1 - e))
              (min (σ.capLimit b b - 1) (σ.k - 1 - d)) σ.k := by
    intro s t d e p q hd1 hdk hst hpEnd hqEnd hpq
    let τ := σ.part [b, b + m + 1] s d
    let pi := τ.part [p] t e
    rw [show (σ.part [b, b + m + 1] s d).part [p] t e = pi by rfl]
    have hpσ : p ∈ σ.childPositions := by
      rcases hpEnd with hp' | hp' <;> subst p
      · exact hb
      · exact hq
    have hpMid : p ≠ b + 1 := by
      rcases hpEnd with hp' | hp' <;> omega
    have hgrowOuter :
        σ.chainExt s p p + 1 ≤ τ.chainExt s p p ∧
        σ.joinExt s p p + 1 ≤ τ.joinExt s p p ∧
        d ≤ τ.joinExt s p p := by
      dsimp [τ]
      exact hgrow [b, b + m + 1] s d p (b + 1) hpσ hp
        hmiddleNotOuter hpMid
    have hrExt : b + 1 ∈ τ.extPositions 1 := by
      dsimp [τ]
      rw [part_extPositions_one hlet]
      simp [hp, hmiddleNotOuter] <;> omega
    have hτside : τ.sideAt 1 = s := by
      dsimp [τ]
      exact part_sideAt_one_of_mem hlet [b, b + m + 1] s d hrExt
    have hwfτ : τ.WellFormed := by
      dsimp [τ]
      exact hwf.part [b, b + m + 1] s hd1 hdk
    have hletτ : ∀ x N v, τ.letterAt x = Letter.ext N v → 1 ≤ N :=
      fun x N v h ↦ (hwfτ.2.2.2.2.2 x N v h).1
    have hqτ : q ∈ τ.childPositions := by
      dsimp [τ]
      rw [hpartOuter]
      rcases hqEnd with rfl | rfl <;> simp
    have hqNot : q ∉ [p] := by simp [Ne.symm hpq]
    have hqExt : q ∈ pi.extPositions 1 := by
      dsimp [pi]
      rw [part_extPositions_one hletτ]
      simp [hqτ, Ne.symm hpq]
    have hpiSide : pi.sideAt 1 = t := by
      dsimp [pi]
      exact part_sideAt_one_of_mem hletτ [p] t e hqExt
    have hpiPos : pi.childPositions = [p] := by
      dsimp [pi, τ]
      exact hpartLeaf s d t e p hpEnd
    have hgrowSigmaInner :
        σ.chainExt t p p + 1 ≤ pi.chainExt t p p ∧
        σ.joinExt t p p + 1 ≤ pi.joinExt t p p ∧
        e ≤ pi.joinExt t p p := by
      simpa [pi, τ] using
        hotherGrow s t d e p q hd1 hdk hst hpEnd hqEnd hpq
    have hpiOther : pi.sideAt 1 ≠ s := by
      rw [hpiSide]
      exact Ne.symm hst
    have hgrowSigmaOuter :
        σ.chainExt s p p + 1 ≤ pi.chainExt s p p ∧
        σ.joinExt s p p + 1 ≤ pi.joinExt s p p ∧
        d ≤ pi.joinExt s p p := by
      constructor
      · rw [chainExt_part_other hpiOther]
        exact hgrowOuter.1
      constructor
      · rw [joinExt_part_other hpiOther]
        exact hgrowOuter.2.1
      · rw [joinExt_part_other hpiOther]
        exact hgrowOuter.2.2
    have hgrowSigmaInner' := hgrowSigmaInner
    rw [hchainEq t p b hpσ hb, hjoinEq t p b hpσ hb] at hgrowSigmaInner'
    have hgrowSigmaOuter' := hgrowSigmaOuter
    rw [hchainEq s p b hpσ hb, hjoinEq s p b hpσ hb] at hgrowSigmaOuter'
    rw [hrunBound pi p 1 (by omega) hpiPos]
    cases s with
    | lower =>
      have ht : t = Side.upper := by
        cases t
        · exact (hst rfl).elim
        · rfl
      rw [ht] at hgrowSigmaInner'
      have hc : pi.cupLimit p p ≤
          min (σ.cupLimit b b - 1) (σ.k - 1 - d) := by
        change min (σ.u - 1 - pi.chainExt Side.lower p p)
            (σ.k - 1 - pi.joinExt Side.lower p p) ≤
          min (min (σ.u - 1 - σ.chainExt Side.lower b b)
            (σ.k - 1 - σ.joinExt Side.lower b b) - 1) (σ.k - 1 - d)
        omega
      have hp' : pi.capLimit p p ≤
          min (σ.capLimit b b - 1) (σ.k - 1 - e) := by
        change min (σ.a - 1 - pi.chainExt Side.upper p p)
            (σ.k - 1 - pi.joinExt Side.upper p p) ≤
          min (min (σ.a - 1 - σ.chainExt Side.upper b b)
            (σ.k - 1 - σ.joinExt Side.upper b b) - 1) (σ.k - 1 - e)
        omega
      exact baseOf_mono hc hp'
    | upper =>
      have ht : t = Side.lower := by
        cases t
        · rfl
        · exact (hst rfl).elim
      rw [ht] at hgrowSigmaInner'
      have hc : pi.cupLimit p p ≤
          min (σ.cupLimit b b - 1) (σ.k - 1 - e) := by
        change min (σ.u - 1 - pi.chainExt Side.lower p p)
            (σ.k - 1 - pi.joinExt Side.lower p p) ≤
          min (min (σ.u - 1 - σ.chainExt Side.lower b b)
            (σ.k - 1 - σ.joinExt Side.lower b b) - 1) (σ.k - 1 - e)
        omega
      have hp' : pi.capLimit p p ≤
          min (σ.capLimit b b - 1) (σ.k - 1 - d) := by
        change min (σ.a - 1 - pi.chainExt Side.upper p p)
            (σ.k - 1 - pi.joinExt Side.upper p p) ≤
          min (min (σ.a - 1 - σ.chainExt Side.upper b b)
            (σ.k - 1 - σ.joinExt Side.upper b b) - 1) (σ.k - 1 - d)
        omega
      exact baseOf_mono hc hp'
  have hc : σ.cupLimit b b ≤ σ.k - 1 := by
    unfold cupLimit
    omega
  have hpLim : σ.capLimit b b ≤ σ.k - 1 := by
    unfold capLimit
    omega
  have hcomp1 : 1 ≤ σ.k - 1 - d := by omega
  have hcompk : σ.k - 1 - d ≤ σ.k - 2 := by omega
  have hcancel : σ.k - 1 - (σ.k - 1 - d) = d := by omega
  have hcancelPred : σ.k - 2 - (σ.k - 1 - d) = d - 1 := by omega
  have houterLower :
      (σ.part [b, b + m + 1] Side.lower d).bound ≤
        baseOf (σ.cupLimit b b) (σ.capLimit b b) σ.k -
          baseOf (σ.cupLimit b b) (min (σ.capLimit b b - 2) d) σ.k := by
    apply two_child_bound_of_singleton_cuts
      (σ.part [b, b + m + 1] Side.lower d) b (b + m + 1)
    · exact hpartOuter _ _
    · omega
    · exact houterRuns _ _
    · intro e he hek
      rw [part_k] at hek ⊢
      have heComp1 : 1 ≤ σ.k - 1 - e := by omega
      have heCompk : σ.k - 1 - e ≤ σ.k - 2 := by omega
      have heCancel : σ.k - 1 - (σ.k - 1 - e) = e := by omega
      have hAleft :
          ((σ.part [b, b + m + 1] Side.lower d).part [b] Side.lower e).bound ≤
            baseOf (min (min (σ.cupLimit b b - 1) (σ.k - 1 - e))
              (σ.k - 2 - d)) (σ.capLimit b b) σ.k := by
        simpa only using hsameLeaf Side.lower d e b (b + m + 1)
          hd hdk he hek (Or.inl rfl) (Or.inr rfl) (by omega)
      have hBright :
          ((σ.part [b, b + m + 1] Side.lower d).part [b + m + 1]
              Side.upper (σ.k - 1 - e)).bound ≤
            baseOf (min (σ.cupLimit b b - 1) (σ.k - 1 - d))
              (min (σ.capLimit b b - 1) e) σ.k := by
        simpa only [heCancel] using
          hoppLeaf Side.lower Side.upper d (σ.k - 1 - e)
            (b + m + 1) b hd hdk (by decide)
            (Or.inr rfl) (Or.inl rfl) (by omega)
      have hBleft :
          ((σ.part [b, b + m + 1] Side.lower d).part [b]
              Side.upper (σ.k - 1 - e)).bound ≤
            baseOf (min (σ.cupLimit b b - 1) (σ.k - 1 - d))
              (min (σ.capLimit b b - 1) e) σ.k := by
        simpa only [heCancel] using
          hoppLeaf Side.lower Side.upper d (σ.k - 1 - e)
            b (b + m + 1) hd hdk (by decide)
            (Or.inl rfl) (Or.inr rfl) (by omega)
      have hAright :
          ((σ.part [b, b + m + 1] Side.lower d).part [b + m + 1]
              Side.lower e).bound ≤
            baseOf (min (min (σ.cupLimit b b - 1) (σ.k - 1 - e))
              (σ.k - 2 - d)) (σ.capLimit b b) σ.k := by
        simpa only using hsameLeaf Side.lower d e (b + m + 1) b
          hd hdk he hek (Or.inr rfl) (Or.inl rfl) (by omega)
      have halloc := hthreeBase (σ.cupLimit b b) (σ.capLimit b b)
        σ.k d e hc hpLim hd hdk he hek
      constructor
      · apply Nat.le_sub_of_add_le
        omega
      · apply Nat.le_sub_of_add_le
        omega
  have houterUpper :
      (σ.part [b, b + m + 1] Side.upper (σ.k - 1 - d)).bound ≤
        baseOf (σ.cupLimit b b) (σ.capLimit b b) σ.k -
          baseOf (min (σ.cupLimit b b - 2) (σ.k - 1 - d))
            (σ.capLimit b b) σ.k := by
    apply two_child_bound_of_singleton_cuts
      (σ.part [b, b + m + 1] Side.upper (σ.k - 1 - d)) b (b + m + 1)
    · exact hpartOuter _ _
    · omega
    · exact houterRuns _ _
    · intro e he hek
      rw [part_k] at hek ⊢
      have heComp1 : 1 ≤ σ.k - 1 - e := by omega
      have heCompk : σ.k - 1 - e ≤ σ.k - 2 := by omega
      have heCancel : σ.k - 1 - (σ.k - 1 - e) = e := by omega
      have hBleft :
          ((σ.part [b, b + m + 1] Side.upper (σ.k - 1 - d)).part [b]
              Side.lower e).bound ≤
            baseOf (min (σ.cupLimit b b - 1) (σ.k - 1 - e))
              (min (σ.capLimit b b - 1) d) σ.k := by
        simpa only [hcancel] using
          hoppLeaf Side.upper Side.lower (σ.k - 1 - d) e
            b (b + m + 1) hcomp1 hcompk (by decide)
            (Or.inl rfl) (Or.inr rfl) (by omega)
      have hAright :
          ((σ.part [b, b + m + 1] Side.upper (σ.k - 1 - d)).part
              [b + m + 1] Side.upper (σ.k - 1 - e)).bound ≤
            baseOf (σ.cupLimit b b)
              (min (min (σ.capLimit b b - 1) e) (d - 1)) σ.k := by
        simpa only [heCancel, hcancelPred] using
          hsameLeaf Side.upper (σ.k - 1 - d) (σ.k - 1 - e)
            (b + m + 1) b hcomp1 hcompk heComp1 heCompk
            (Or.inr rfl) (Or.inl rfl) (by omega)
      have hAleft :
          ((σ.part [b, b + m + 1] Side.upper (σ.k - 1 - d)).part [b]
              Side.upper (σ.k - 1 - e)).bound ≤
            baseOf (σ.cupLimit b b)
              (min (min (σ.capLimit b b - 1) e) (d - 1)) σ.k := by
        simpa only [heCancel, hcancelPred] using
          hsameLeaf Side.upper (σ.k - 1 - d) (σ.k - 1 - e)
            b (b + m + 1) hcomp1 hcompk heComp1 heCompk
            (Or.inl rfl) (Or.inr rfl) (by omega)
      have hBright :
          ((σ.part [b, b + m + 1] Side.upper (σ.k - 1 - d)).part
              [b + m + 1] Side.lower e).bound ≤
            baseOf (min (σ.cupLimit b b - 1) (σ.k - 1 - e))
              (min (σ.capLimit b b - 1) d) σ.k := by
        simpa only [hcancel] using
          hoppLeaf Side.upper Side.lower (σ.k - 1 - d) e
            (b + m + 1) b hcomp1 hcompk (by decide)
            (Or.inr rfl) (Or.inl rfl) (by omega)
      have halloc := hthreeBaseDual (σ.cupLimit b b) (σ.capLimit b b)
        σ.k d e hc hpLim hd hdk he hek
      constructor
      · apply Nat.le_sub_of_add_le
        omega
      · apply Nat.le_sub_of_add_le
        omega
  have hmiddleUpper :
      (σ.part (List.range' (b + 1) m) Side.upper (σ.k - 1 - d)).bound ≤
        baseOf (σ.cupLimit b b)
          (min (σ.capLimit b b - 2) d) σ.k := by
    simpa only [hcancel] using hmiddleBound Side.upper (σ.k - 1 - d)
  have hmiddleLower :
      (σ.part (List.range' (b + 1) m) Side.lower d).bound ≤
        baseOf (min (σ.cupLimit b b - 2) (σ.k - 1 - d))
          (σ.capLimit b b) σ.k := by
    simpa only using hmiddleBound Side.lower d
  have hcupMiddleLe :
      baseOf (min (σ.cupLimit b b - 2) (σ.k - 1 - d))
          (σ.capLimit b b) σ.k ≤
        baseOf (σ.cupLimit b b) (σ.capLimit b b) σ.k :=
    baseOf_mono ((Nat.min_le_left _ _).trans (Nat.sub_le _ _)) (Nat.le_refl _)
  have hcapMiddleLe :
      baseOf (σ.cupLimit b b) (min (σ.capLimit b b - 2) d) σ.k ≤
        baseOf (σ.cupLimit b b) (σ.capLimit b b) σ.k :=
    baseOf_mono (Nat.le_refl _)
      ((Nat.min_le_left _ _).trans (Nat.sub_le _ _))
  rw [hrunBound σ b (m + 2) (by omega) hpos]
  constructor <;> omega

end ErdosSzekeres
