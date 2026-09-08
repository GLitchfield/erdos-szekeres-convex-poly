import ErdosSzekeres.PublishedInductionSemantics
import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit
import ESBlueprint.B.CtxBasePascalCombine
import ESBlueprint.B.CtxBaseCrossAxisTransfer
import ESBlueprint.B.CtxBaseSandwich112Case0200
import ESBlueprint.B.CtxBaseSandwich112Case0210
import ESBlueprint.B.CtxBaseSandwich112Case0211
import ESBlueprint.B.CtxBaseSandwich112Case0300
import ESBlueprint.B.CtxBaseSandwich112Case0310
import ESBlueprint.B.CtxBaseSandwich112Case0311
import ESBlueprint.B.CtxSingleRunDescendantLeafBound

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Geometric leaf bounds for the (1,1,2) sandwich, family three. Uniform in every well-formed external context and admissible coupling. Both outer sides and both inner-cut orientations, with a contiguous two-child residual. Explicit new-level extension paths feed the general descendant leaf estimate and the checked scalar allocations.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_112 -/
theorem ctx_sandwich_112_leaf_cases_three (σ : Ctx.Context) (hwf : σ.WellFormed) (b : ℕ) (hpos : σ.childPositions = List.range' b 4) :
  (∀ (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2),
      let O := σ.part [b, (b + 2), (b + 3)] Ctx.Side.lower (od)
      let M := σ.part [(b + 1)] Ctx.Side.upper (σ.k - 1 - od)
      let Q := O.part [b] Ctx.Side.lower (e)
      let R := O.part [(b + 2), (b + 3)] Ctx.Side.upper (σ.k - 1 - e)
      M.bound + Q.bound + R.bound ≤ σ.bound) ∧
  (∀ (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2),
      let O := σ.part [b, (b + 2), (b + 3)] Ctx.Side.lower (od)
      let M := σ.part [(b + 1)] Ctx.Side.upper (σ.k - 1 - od)
      let Q := O.part [b] Ctx.Side.upper (σ.k - 1 - e)
      let R := O.part [(b + 2), (b + 3)] Ctx.Side.lower (e)
      M.bound + Q.bound + R.bound ≤ σ.bound) ∧
  (∀ (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2),
      let O := σ.part [b, (b + 2), (b + 3)] Ctx.Side.upper (od)
      let M := σ.part [(b + 1)] Ctx.Side.lower (σ.k - 1 - od)
      let Q := O.part [b] Ctx.Side.lower (e)
      let R := O.part [(b + 2), (b + 3)] Ctx.Side.upper (σ.k - 1 - e)
      M.bound + Q.bound + R.bound ≤ σ.bound) ∧
  (∀ (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2),
      let O := σ.part [b, (b + 2), (b + 3)] Ctx.Side.upper (od)
      let M := σ.part [(b + 1)] Ctx.Side.lower (σ.k - 1 - od)
      let Q := O.part [b] Ctx.Side.upper (σ.k - 1 - e)
      let R := O.part [(b + 2), (b + 3)] Ctx.Side.lower (e)
      M.bound + Q.bound + R.bound ≤ σ.bound) := by
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
  have hleafEstimate := ctx_single_run_descendant_leaf_bound σ b 4 hpos (by decide)
  have hcombine := ctx_base_pascal_combine
  have hbaseSplit : ∀ cl pl k d : ℕ, cl ≤ k - 1 → pl ≤ k - 1 →
      1 ≤ d → d ≤ k - 2 →
      baseOf (min (cl - 1) (k - 1 - d)) pl k +
          baseOf cl (min (pl - 1) d) k ≤ baseOf cl pl k := by
    intro cl pl k d hc hp hd hdk
    clear * - cl pl k d hc hp hd hdk
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
    clear * - cl pl k d e hc hp hd hdk he hek hbaseSplit
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
    clear * - cl pl k d e hc hp hd hdk he hek hbaseSplit
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
  have hquad_0000 (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2) :
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      let Q := O.part [b] Side.lower (e)
      let R := O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    as_aux_lemma =>
      clear * - σ hwf b hpos od e f hod hodk he hek hf hfk hrunBound Anc hAnc0 hAncPart hnewSub hprefixSideSub hjoinNew hleafEstimate hthreeBase
      dsimp only
      have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by
        simpa [List.range'_succ, Nat.add_assoc] using hpos
      have hC : σ.cupLimit b b ≤ σ.k - 1 := by unfold cupLimit; omega
      have hP : σ.capLimit b b ≤ σ.k - 1 := by unfold capLimit; omega
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      have hOw : O.WellFormed := hwf.part [b, (b + 2), (b + 3)] Side.lower (by omega) (by omega)
      have hOa : Anc O 1 := hAncPart σ 0 hAnc0 [b, (b + 2), (b + 3)] Side.lower (od)
      have hOc : O.childPositions = [b, (b + 2), (b + 3)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hOe1 : O.extPositions 1 = [(b + 1)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hOs1 : O.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [b, (b + 2), (b + 3)] Side.lower (od) (q := (b + 1))
        change _ ∈ O.extPositions 1
        rw [hOe1]
        simp
      have hOm1 : O.maximumAt 1 = od := rfl
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMw : M.WellFormed := hwf.part [(b + 1)] Side.upper (by omega) (by omega)
      have hMa : Anc M 1 := hAncPart σ 0 hAnc0 [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMc : M.childPositions = [(b + 1)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hMe1 : M.extPositions 1 = [b, (b + 2), (b + 3)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hMs1 : M.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [(b + 1)] Side.upper (σ.k - 1 - od) (q := b)
        change _ ∈ M.extPositions 1
        rw [hMe1]
        simp
      have hMm1 : M.maximumAt 1 = σ.k - 1 - od := rfl
      let Q := O.part [b] Side.lower (e)
      have hQw : Q.WellFormed := hOw.part [b] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hQa : Anc Q 2 := hAncPart O 1 hOa [b] Side.lower (e)
      have hQc : Q.childPositions = [b] := by
        change (O.part [b] Side.lower (e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hQe1 : Q.extPositions 1 = [(b + 2), (b + 3)] := by
        change (O.part [b] Side.lower (e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hQs1 : Q.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [b] Side.lower (e) (q := (b + 2))
        change _ ∈ Q.extPositions 1
        rw [hQe1]
        simp
      have hQm1 : Q.maximumAt 1 = e := rfl
      have hQe2 : Q.extPositions 2 = [(b + 1)] := by
        change (O.part [b] Side.lower (e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [b] Side.lower (e) (by decide : 1 ≤ 1), hOe1]
      have hQs2 : Q.sideAt 2 = Side.lower := by
        change (O.part [b] Side.lower (e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [b] Side.lower (e) (by decide : 1 ≤ 1), hOs1]
      have hQm2 : Q.maximumAt 2 = od := by
        change (O.part [b] Side.lower (e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [b] Side.lower (e) (by decide : 1 ≤ 1), hOm1]
      let R := O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)
      have hRw : R.WellFormed := hOw.part [(b + 2), (b + 3)] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hRa : Anc R 2 := hAncPart O 1 hOa [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)
      have hRc : R.childPositions = [(b + 2), (b + 3)] := by
        change (O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hRe1 : R.extPositions 1 = [b] := by
        change (O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hRs1 : R.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e) (q := b)
        change _ ∈ R.extPositions 1
        rw [hRe1]
        simp
      have hRm1 : R.maximumAt 1 = σ.k - 1 - e := rfl
      have hRe2 : R.extPositions 2 = [(b + 1)] := by
        change (O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOe1]
      have hRs2 : R.sideAt 2 = Side.lower := by
        change (O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOs1]
      have hRm2 : R.maximumAt 2 = od := by
        change (O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOm1]
      have hMbound : M.bound ≤ baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 2) od) σ.k := by
        have hj0 : 0 ≤ M.joinExt Side.lower (b + 1) (b + 1) := by
          exact Nat.zero_le _
        have hj1 : (σ.k - 1 - od) ≤ M.joinExt Side.upper (b + 1) (b + 1) := by
          have hjN1 := hjoinNew M Side.upper 1 (b + 1) (List.singleton_sublist.mp (hnewSub M 1 hMa Side.upper 0 [1] (by decide) (by simp [hMs1]))) [] []
            (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1])) (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1]))
          norm_num [leftStep, rightStep, hMe1, hMm1, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate M 1 (b + 1) 1 hMa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hMc)
          [] [] [1] [1]
          (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1]))
          (b + 1) (b + 1) b (b + 2) 0 0 1 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc]) (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc])
          0 (σ.k - 1 - od) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hQbound : Q.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (min (σ.k - 1 - e) (σ.k - 1 - od - 1))) (σ.capLimit b b) σ.k := by
        have hj0 : (max (e) (od + 1)) ≤ Q.joinExt Side.lower b b := by
          have hjN1 := hjoinNew Q Side.lower 1 b (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.lower 0 [1] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.lower 1 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.lower 1 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN1
          have hjN2 := hjoinNew Q Side.lower 2 b (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.lower 0 [2] (by decide) (by simp [hQs1, hQs2]))) [] [1]
            (hnewSub Q 2 hQa Side.lower 2 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.lower 2 [1] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN2
          omega
        have hj1 : 0 ≤ Q.joinExt Side.upper b b := by
          exact Nat.zero_le _
        have hh := hleafEstimate Q 2 b 1 hQa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hQc)
          [] [1] [] []
          (hprefixSideSub Q 2 Side.lower [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.lower [1] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [] (by decide) (by simp [hQs1, hQs2]))
          b (b + 2) b b 0 1 0 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc])
          (max (e) (od + 1)) 0 hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hRbound : R.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - od)) (min ((σ.capLimit b b) - 1) e) σ.k := by
        have hj0 : (od) ≤ R.joinExt Side.lower (b + 2) (b + 2) := by
          have hjN2 := hjoinNew R Side.lower 2 (b + 2) (List.singleton_sublist.mp (hnewSub R 2 hRa Side.lower 0 [2] (by decide) (by simp [hRs1, hRs2]))) [] []
            (hnewSub R 2 hRa Side.lower 2 [] (by decide) (by simp [hRs1, hRs2])) (hnewSub R 2 hRa Side.lower 2 [] (by decide) (by simp [hRs1, hRs2]))
          norm_num [leftStep, rightStep, hRe1, hRe2, hRm1, hRm2, Nat.add_assoc] at hjN2
          omega
        have hj1 : (σ.k - 1 - e) ≤ R.joinExt Side.upper (b + 2) (b + 2) := by
          have hjN1 := hjoinNew R Side.upper 1 (b + 2) (List.singleton_sublist.mp (hnewSub R 2 hRa Side.upper 0 [1] (by decide) (by simp [hRs1, hRs2]))) [] []
            (hnewSub R 2 hRa Side.upper 1 [] (by decide) (by simp [hRs1, hRs2])) (hnewSub R 2 hRa Side.upper 1 [] (by decide) (by simp [hRs1, hRs2]))
          norm_num [leftStep, rightStep, hRe1, hRe2, hRm1, hRm2, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate R 2 (b + 2) 2 hRa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hRc)
          [2] [] [1] []
          (hprefixSideSub R 2 Side.lower [2] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.lower [] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.upper [1] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.upper [] (by decide) (by simp [hRs1, hRs2]))
          (b + 1) (b + 2) b (b + 2) 1 0 1 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [rightStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [leftStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [rightStep, hRe1, hRe2, Nat.add_assoc])
          (od) (σ.k - 1 - e) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      change M.bound + Q.bound + R.bound ≤ _
      have hn := hthreeBase (σ.cupLimit b b) (σ.capLimit b b) σ.k od e hC hP (by omega) (by omega) he hek
      have hnum : baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 2) od) σ.k + baseOf (min ((σ.cupLimit b b) - 1) (min (σ.k - 1 - e) (σ.k - 1 - od - 1))) (σ.capLimit b b) σ.k + baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - od)) (min ((σ.capLimit b b) - 1) e) σ.k ≤ baseOf (σ.cupLimit b b) (σ.capLimit b b) σ.k := by
        have hkd : σ.k - 2 - od = σ.k - 1 - od - 1 := by omega
        have hkc : σ.k - 1 - (σ.k - 1 - od) = od := by omega
        simpa only [hkd, hkc, min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hn
      rw [hrunBound σ b 4 (by decide) hpos]
      exact (Nat.add_le_add (Nat.add_le_add hMbound hQbound) hRbound).trans hnum
  have hquad_0010 (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2) :
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      let Q := O.part [b] Side.upper (σ.k - 1 - e)
      let R := O.part [(b + 2), (b + 3)] Side.lower (e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    as_aux_lemma =>
      clear * - σ hwf b hpos od e f hod hodk he hek hf hfk hrunBound Anc hAnc0 hAncPart hnewSub hprefixSideSub hjoinNew hleafEstimate hthreeBase
      dsimp only
      have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by
        simpa [List.range'_succ, Nat.add_assoc] using hpos
      have hC : σ.cupLimit b b ≤ σ.k - 1 := by unfold cupLimit; omega
      have hP : σ.capLimit b b ≤ σ.k - 1 := by unfold capLimit; omega
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      have hOw : O.WellFormed := hwf.part [b, (b + 2), (b + 3)] Side.lower (by omega) (by omega)
      have hOa : Anc O 1 := hAncPart σ 0 hAnc0 [b, (b + 2), (b + 3)] Side.lower (od)
      have hOc : O.childPositions = [b, (b + 2), (b + 3)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hOe1 : O.extPositions 1 = [(b + 1)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hOs1 : O.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [b, (b + 2), (b + 3)] Side.lower (od) (q := (b + 1))
        change _ ∈ O.extPositions 1
        rw [hOe1]
        simp
      have hOm1 : O.maximumAt 1 = od := rfl
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMw : M.WellFormed := hwf.part [(b + 1)] Side.upper (by omega) (by omega)
      have hMa : Anc M 1 := hAncPart σ 0 hAnc0 [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMc : M.childPositions = [(b + 1)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hMe1 : M.extPositions 1 = [b, (b + 2), (b + 3)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hMs1 : M.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [(b + 1)] Side.upper (σ.k - 1 - od) (q := b)
        change _ ∈ M.extPositions 1
        rw [hMe1]
        simp
      have hMm1 : M.maximumAt 1 = σ.k - 1 - od := rfl
      let Q := O.part [b] Side.upper (σ.k - 1 - e)
      have hQw : Q.WellFormed := hOw.part [b] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hQa : Anc Q 2 := hAncPart O 1 hOa [b] Side.upper (σ.k - 1 - e)
      have hQc : Q.childPositions = [b] := by
        change (O.part [b] Side.upper (σ.k - 1 - e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hQe1 : Q.extPositions 1 = [(b + 2), (b + 3)] := by
        change (O.part [b] Side.upper (σ.k - 1 - e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hQs1 : Q.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [b] Side.upper (σ.k - 1 - e) (q := (b + 2))
        change _ ∈ Q.extPositions 1
        rw [hQe1]
        simp
      have hQm1 : Q.maximumAt 1 = σ.k - 1 - e := rfl
      have hQe2 : Q.extPositions 2 = [(b + 1)] := by
        change (O.part [b] Side.upper (σ.k - 1 - e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [b] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOe1]
      have hQs2 : Q.sideAt 2 = Side.lower := by
        change (O.part [b] Side.upper (σ.k - 1 - e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [b] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOs1]
      have hQm2 : Q.maximumAt 2 = od := by
        change (O.part [b] Side.upper (σ.k - 1 - e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [b] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOm1]
      let R := O.part [(b + 2), (b + 3)] Side.lower (e)
      have hRw : R.WellFormed := hOw.part [(b + 2), (b + 3)] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hRa : Anc R 2 := hAncPart O 1 hOa [(b + 2), (b + 3)] Side.lower (e)
      have hRc : R.childPositions = [(b + 2), (b + 3)] := by
        change (O.part [(b + 2), (b + 3)] Side.lower (e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hRe1 : R.extPositions 1 = [b] := by
        change (O.part [(b + 2), (b + 3)] Side.lower (e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hRs1 : R.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [(b + 2), (b + 3)] Side.lower (e) (q := b)
        change _ ∈ R.extPositions 1
        rw [hRe1]
        simp
      have hRm1 : R.maximumAt 1 = e := rfl
      have hRe2 : R.extPositions 2 = [(b + 1)] := by
        change (O.part [(b + 2), (b + 3)] Side.lower (e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [(b + 2), (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOe1]
      have hRs2 : R.sideAt 2 = Side.lower := by
        change (O.part [(b + 2), (b + 3)] Side.lower (e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [(b + 2), (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOs1]
      have hRm2 : R.maximumAt 2 = od := by
        change (O.part [(b + 2), (b + 3)] Side.lower (e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [(b + 2), (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOm1]
      have hMbound : M.bound ≤ baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 2) od) σ.k := by
        have hj0 : 0 ≤ M.joinExt Side.lower (b + 1) (b + 1) := by
          exact Nat.zero_le _
        have hj1 : (σ.k - 1 - od) ≤ M.joinExt Side.upper (b + 1) (b + 1) := by
          have hjN1 := hjoinNew M Side.upper 1 (b + 1) (List.singleton_sublist.mp (hnewSub M 1 hMa Side.upper 0 [1] (by decide) (by simp [hMs1]))) [] []
            (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1])) (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1]))
          norm_num [leftStep, rightStep, hMe1, hMm1, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate M 1 (b + 1) 1 hMa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hMc)
          [] [] [1] [1]
          (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1]))
          (b + 1) (b + 1) b (b + 2) 0 0 1 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc]) (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc])
          0 (σ.k - 1 - od) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hQbound : Q.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - od)) (min ((σ.capLimit b b) - 1) e) σ.k := by
        have hj0 : (od) ≤ Q.joinExt Side.lower b b := by
          have hjN2 := hjoinNew Q Side.lower 2 b (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.lower 0 [2] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.lower 2 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.lower 2 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN2
          omega
        have hj1 : (σ.k - 1 - e) ≤ Q.joinExt Side.upper b b := by
          have hjN1 := hjoinNew Q Side.upper 1 b (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.upper 0 [1] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.upper 1 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.upper 1 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate Q 2 b 1 hQa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hQc)
          [] [2] [] [1]
          (hprefixSideSub Q 2 Side.lower [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.lower [2] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [1] (by decide) (by simp [hQs1, hQs2]))
          b (b + 1) b (b + 2) 0 1 0 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc])
          (od) (σ.k - 1 - e) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hRbound : R.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (min (σ.k - 1 - e) (σ.k - 1 - od - 1))) (σ.capLimit b b) σ.k := by
        have hj0 : (max (e) (od + 1)) ≤ R.joinExt Side.lower (b + 2) (b + 2) := by
          have hjN1 := hjoinNew R Side.lower 1 (b + 2) (List.singleton_sublist.mp (hnewSub R 2 hRa Side.lower 0 [1] (by decide) (by simp [hRs1, hRs2]))) [] []
            (hnewSub R 2 hRa Side.lower 1 [] (by decide) (by simp [hRs1, hRs2])) (hnewSub R 2 hRa Side.lower 1 [] (by decide) (by simp [hRs1, hRs2]))
          norm_num [leftStep, rightStep, hRe1, hRe2, hRm1, hRm2, Nat.add_assoc] at hjN1
          have hjN2 := hjoinNew R Side.lower 2 (b + 2) (List.singleton_sublist.mp (hnewSub R 2 hRa Side.lower 0 [2] (by decide) (by simp [hRs1, hRs2]))) [1] []
            (hnewSub R 2 hRa Side.lower 2 [1] (by decide) (by simp [hRs1, hRs2])) (hnewSub R 2 hRa Side.lower 2 [] (by decide) (by simp [hRs1, hRs2]))
          norm_num [leftStep, rightStep, hRe1, hRe2, hRm1, hRm2, Nat.add_assoc] at hjN2
          omega
        have hj1 : 0 ≤ R.joinExt Side.upper (b + 2) (b + 2) := by
          exact Nat.zero_le _
        have hh := hleafEstimate R 2 (b + 2) 2 hRa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hRc)
          [1] [] [] []
          (hprefixSideSub R 2 Side.lower [1] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.lower [] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.upper [] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.upper [] (by decide) (by simp [hRs1, hRs2]))
          b (b + 2) (b + 2) (b + 2) 1 0 0 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [rightStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [leftStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [rightStep, hRe1, hRe2, Nat.add_assoc])
          (max (e) (od + 1)) 0 hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      change M.bound + Q.bound + R.bound ≤ _
      have hn := hthreeBase (σ.cupLimit b b) (σ.capLimit b b) σ.k od e hC hP (by omega) (by omega) he hek
      have hnum : baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 2) od) σ.k + baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - od)) (min ((σ.capLimit b b) - 1) e) σ.k + baseOf (min ((σ.cupLimit b b) - 1) (min (σ.k - 1 - e) (σ.k - 1 - od - 1))) (σ.capLimit b b) σ.k ≤ baseOf (σ.cupLimit b b) (σ.capLimit b b) σ.k := by
        have hkd : σ.k - 2 - od = σ.k - 1 - od - 1 := by omega
        have hkc : σ.k - 1 - (σ.k - 1 - od) = od := by omega
        simpa only [hkd, hkc, min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hn
      rw [hrunBound σ b 4 (by decide) hpos]
      exact (Nat.add_le_add (Nat.add_le_add hMbound hQbound) hRbound).trans hnum
  have hquad_1000 (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2) :
      let O := σ.part [b, (b + 2), (b + 3)] Side.upper (od)
      let M := σ.part [(b + 1)] Side.lower (σ.k - 1 - od)
      let Q := O.part [b] Side.lower (e)
      let R := O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    as_aux_lemma =>
      clear * - σ hwf b hpos od e f hod hodk he hek hf hfk hrunBound Anc hAnc0 hAncPart hnewSub hprefixSideSub hjoinNew hleafEstimate hthreeBaseDual
      dsimp only
      have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by
        simpa [List.range'_succ, Nat.add_assoc] using hpos
      have hC : σ.cupLimit b b ≤ σ.k - 1 := by unfold cupLimit; omega
      have hP : σ.capLimit b b ≤ σ.k - 1 := by unfold capLimit; omega
      let O := σ.part [b, (b + 2), (b + 3)] Side.upper (od)
      have hOw : O.WellFormed := hwf.part [b, (b + 2), (b + 3)] Side.upper (by omega) (by omega)
      have hOa : Anc O 1 := hAncPart σ 0 hAnc0 [b, (b + 2), (b + 3)] Side.upper (od)
      have hOc : O.childPositions = [b, (b + 2), (b + 3)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.upper (od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hOe1 : O.extPositions 1 = [(b + 1)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.upper (od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hOs1 : O.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [b, (b + 2), (b + 3)] Side.upper (od) (q := (b + 1))
        change _ ∈ O.extPositions 1
        rw [hOe1]
        simp
      have hOm1 : O.maximumAt 1 = od := rfl
      let M := σ.part [(b + 1)] Side.lower (σ.k - 1 - od)
      have hMw : M.WellFormed := hwf.part [(b + 1)] Side.lower (by omega) (by omega)
      have hMa : Anc M 1 := hAncPart σ 0 hAnc0 [(b + 1)] Side.lower (σ.k - 1 - od)
      have hMc : M.childPositions = [(b + 1)] := by
        change (σ.part [(b + 1)] Side.lower (σ.k - 1 - od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hMe1 : M.extPositions 1 = [b, (b + 2), (b + 3)] := by
        change (σ.part [(b + 1)] Side.lower (σ.k - 1 - od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hMs1 : M.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [(b + 1)] Side.lower (σ.k - 1 - od) (q := b)
        change _ ∈ M.extPositions 1
        rw [hMe1]
        simp
      have hMm1 : M.maximumAt 1 = σ.k - 1 - od := rfl
      let Q := O.part [b] Side.lower (e)
      have hQw : Q.WellFormed := hOw.part [b] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hQa : Anc Q 2 := hAncPart O 1 hOa [b] Side.lower (e)
      have hQc : Q.childPositions = [b] := by
        change (O.part [b] Side.lower (e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hQe1 : Q.extPositions 1 = [(b + 2), (b + 3)] := by
        change (O.part [b] Side.lower (e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hQs1 : Q.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [b] Side.lower (e) (q := (b + 2))
        change _ ∈ Q.extPositions 1
        rw [hQe1]
        simp
      have hQm1 : Q.maximumAt 1 = e := rfl
      have hQe2 : Q.extPositions 2 = [(b + 1)] := by
        change (O.part [b] Side.lower (e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [b] Side.lower (e) (by decide : 1 ≤ 1), hOe1]
      have hQs2 : Q.sideAt 2 = Side.upper := by
        change (O.part [b] Side.lower (e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [b] Side.lower (e) (by decide : 1 ≤ 1), hOs1]
      have hQm2 : Q.maximumAt 2 = od := by
        change (O.part [b] Side.lower (e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [b] Side.lower (e) (by decide : 1 ≤ 1), hOm1]
      let R := O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)
      have hRw : R.WellFormed := hOw.part [(b + 2), (b + 3)] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hRa : Anc R 2 := hAncPart O 1 hOa [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)
      have hRc : R.childPositions = [(b + 2), (b + 3)] := by
        change (O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hRe1 : R.extPositions 1 = [b] := by
        change (O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hRs1 : R.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e) (q := b)
        change _ ∈ R.extPositions 1
        rw [hRe1]
        simp
      have hRm1 : R.maximumAt 1 = σ.k - 1 - e := rfl
      have hRe2 : R.extPositions 2 = [(b + 1)] := by
        change (O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOe1]
      have hRs2 : R.sideAt 2 = Side.upper := by
        change (O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOs1]
      have hRm2 : R.maximumAt 2 = od := by
        change (O.part [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [(b + 2), (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOm1]
      have hMbound : M.bound ≤ baseOf (min ((σ.cupLimit b b) - 2) od) (σ.capLimit b b) σ.k := by
        have hj0 : (σ.k - 1 - od) ≤ M.joinExt Side.lower (b + 1) (b + 1) := by
          have hjN1 := hjoinNew M Side.lower 1 (b + 1) (List.singleton_sublist.mp (hnewSub M 1 hMa Side.lower 0 [1] (by decide) (by simp [hMs1]))) [] []
            (hnewSub M 1 hMa Side.lower 1 [] (by decide) (by simp [hMs1])) (hnewSub M 1 hMa Side.lower 1 [] (by decide) (by simp [hMs1]))
          norm_num [leftStep, rightStep, hMe1, hMm1, Nat.add_assoc] at hjN1
          omega
        have hj1 : 0 ≤ M.joinExt Side.upper (b + 1) (b + 1) := by
          exact Nat.zero_le _
        have hh := hleafEstimate M 1 (b + 1) 1 hMa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hMc)
          [1] [1] [] []
          (hprefixSideSub M 1 Side.lower [1] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.lower [1] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [] (by decide) (by simp [hMs1]))
          b (b + 2) (b + 1) (b + 1) 1 1 0 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc]) (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc])
          (σ.k - 1 - od) 0 hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hQbound : Q.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - e)) (min ((σ.capLimit b b) - 1) (σ.k - 1 - od)) σ.k := by
        have hj0 : (e) ≤ Q.joinExt Side.lower b b := by
          have hjN1 := hjoinNew Q Side.lower 1 b (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.lower 0 [1] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.lower 1 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.lower 1 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN1
          omega
        have hj1 : (od) ≤ Q.joinExt Side.upper b b := by
          have hjN2 := hjoinNew Q Side.upper 2 b (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.upper 0 [2] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.upper 2 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.upper 2 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN2
          omega
        have hh := hleafEstimate Q 2 b 1 hQa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hQc)
          [] [1] [] [2]
          (hprefixSideSub Q 2 Side.lower [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.lower [1] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [2] (by decide) (by simp [hQs1, hQs2]))
          b (b + 2) b (b + 1) 0 1 0 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc])
          (e) (od) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hRbound : R.bound ≤ baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 1) (min e (σ.k - 1 - od - 1))) σ.k := by
        have hj0 : 0 ≤ R.joinExt Side.lower (b + 2) (b + 2) := by
          exact Nat.zero_le _
        have hj1 : (max (σ.k - 1 - e) (od + 1)) ≤ R.joinExt Side.upper (b + 2) (b + 2) := by
          have hjN1 := hjoinNew R Side.upper 1 (b + 2) (List.singleton_sublist.mp (hnewSub R 2 hRa Side.upper 0 [1] (by decide) (by simp [hRs1, hRs2]))) [] []
            (hnewSub R 2 hRa Side.upper 1 [] (by decide) (by simp [hRs1, hRs2])) (hnewSub R 2 hRa Side.upper 1 [] (by decide) (by simp [hRs1, hRs2]))
          norm_num [leftStep, rightStep, hRe1, hRe2, hRm1, hRm2, Nat.add_assoc] at hjN1
          have hjN2 := hjoinNew R Side.upper 2 (b + 2) (List.singleton_sublist.mp (hnewSub R 2 hRa Side.upper 0 [2] (by decide) (by simp [hRs1, hRs2]))) [1] []
            (hnewSub R 2 hRa Side.upper 2 [1] (by decide) (by simp [hRs1, hRs2])) (hnewSub R 2 hRa Side.upper 2 [] (by decide) (by simp [hRs1, hRs2]))
          norm_num [leftStep, rightStep, hRe1, hRe2, hRm1, hRm2, Nat.add_assoc] at hjN2
          omega
        have hh := hleafEstimate R 2 (b + 2) 2 hRa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hRc)
          [] [] [1] []
          (hprefixSideSub R 2 Side.lower [] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.lower [] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.upper [1] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.upper [] (by decide) (by simp [hRs1, hRs2]))
          (b + 2) (b + 2) b (b + 2) 0 0 1 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [rightStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [leftStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [rightStep, hRe1, hRe2, Nat.add_assoc])
          0 (max (σ.k - 1 - e) (od + 1)) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      change M.bound + Q.bound + R.bound ≤ _
      have hn := hthreeBaseDual (σ.cupLimit b b) (σ.capLimit b b) σ.k (σ.k - 1 - od) e hC hP (by omega) (by omega) he hek
      have hnum : baseOf (min ((σ.cupLimit b b) - 2) od) (σ.capLimit b b) σ.k + baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - e)) (min ((σ.capLimit b b) - 1) (σ.k - 1 - od)) σ.k + baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 1) (min e (σ.k - 1 - od - 1))) σ.k ≤ baseOf (σ.cupLimit b b) (σ.capLimit b b) σ.k := by
        have hkd : σ.k - 2 - od = σ.k - 1 - od - 1 := by omega
        have hkc : σ.k - 1 - (σ.k - 1 - od) = od := by omega
        simpa only [hkd, hkc, min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hn
      rw [hrunBound σ b 4 (by decide) hpos]
      exact (Nat.add_le_add (Nat.add_le_add hMbound hQbound) hRbound).trans hnum
  have hquad_1010 (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2) :
      let O := σ.part [b, (b + 2), (b + 3)] Side.upper (od)
      let M := σ.part [(b + 1)] Side.lower (σ.k - 1 - od)
      let Q := O.part [b] Side.upper (σ.k - 1 - e)
      let R := O.part [(b + 2), (b + 3)] Side.lower (e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    as_aux_lemma =>
      clear * - σ hwf b hpos od e f hod hodk he hek hf hfk hrunBound Anc hAnc0 hAncPart hnewSub hprefixSideSub hjoinNew hleafEstimate hthreeBaseDual
      dsimp only
      have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by
        simpa [List.range'_succ, Nat.add_assoc] using hpos
      have hC : σ.cupLimit b b ≤ σ.k - 1 := by unfold cupLimit; omega
      have hP : σ.capLimit b b ≤ σ.k - 1 := by unfold capLimit; omega
      let O := σ.part [b, (b + 2), (b + 3)] Side.upper (od)
      have hOw : O.WellFormed := hwf.part [b, (b + 2), (b + 3)] Side.upper (by omega) (by omega)
      have hOa : Anc O 1 := hAncPart σ 0 hAnc0 [b, (b + 2), (b + 3)] Side.upper (od)
      have hOc : O.childPositions = [b, (b + 2), (b + 3)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.upper (od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hOe1 : O.extPositions 1 = [(b + 1)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.upper (od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hOs1 : O.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [b, (b + 2), (b + 3)] Side.upper (od) (q := (b + 1))
        change _ ∈ O.extPositions 1
        rw [hOe1]
        simp
      have hOm1 : O.maximumAt 1 = od := rfl
      let M := σ.part [(b + 1)] Side.lower (σ.k - 1 - od)
      have hMw : M.WellFormed := hwf.part [(b + 1)] Side.lower (by omega) (by omega)
      have hMa : Anc M 1 := hAncPart σ 0 hAnc0 [(b + 1)] Side.lower (σ.k - 1 - od)
      have hMc : M.childPositions = [(b + 1)] := by
        change (σ.part [(b + 1)] Side.lower (σ.k - 1 - od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hMe1 : M.extPositions 1 = [b, (b + 2), (b + 3)] := by
        change (σ.part [(b + 1)] Side.lower (σ.k - 1 - od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hMs1 : M.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [(b + 1)] Side.lower (σ.k - 1 - od) (q := b)
        change _ ∈ M.extPositions 1
        rw [hMe1]
        simp
      have hMm1 : M.maximumAt 1 = σ.k - 1 - od := rfl
      let Q := O.part [b] Side.upper (σ.k - 1 - e)
      have hQw : Q.WellFormed := hOw.part [b] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hQa : Anc Q 2 := hAncPart O 1 hOa [b] Side.upper (σ.k - 1 - e)
      have hQc : Q.childPositions = [b] := by
        change (O.part [b] Side.upper (σ.k - 1 - e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hQe1 : Q.extPositions 1 = [(b + 2), (b + 3)] := by
        change (O.part [b] Side.upper (σ.k - 1 - e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hQs1 : Q.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [b] Side.upper (σ.k - 1 - e) (q := (b + 2))
        change _ ∈ Q.extPositions 1
        rw [hQe1]
        simp
      have hQm1 : Q.maximumAt 1 = σ.k - 1 - e := rfl
      have hQe2 : Q.extPositions 2 = [(b + 1)] := by
        change (O.part [b] Side.upper (σ.k - 1 - e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [b] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOe1]
      have hQs2 : Q.sideAt 2 = Side.upper := by
        change (O.part [b] Side.upper (σ.k - 1 - e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [b] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOs1]
      have hQm2 : Q.maximumAt 2 = od := by
        change (O.part [b] Side.upper (σ.k - 1 - e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [b] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOm1]
      let R := O.part [(b + 2), (b + 3)] Side.lower (e)
      have hRw : R.WellFormed := hOw.part [(b + 2), (b + 3)] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hRa : Anc R 2 := hAncPart O 1 hOa [(b + 2), (b + 3)] Side.lower (e)
      have hRc : R.childPositions = [(b + 2), (b + 3)] := by
        change (O.part [(b + 2), (b + 3)] Side.lower (e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hRe1 : R.extPositions 1 = [b] := by
        change (O.part [(b + 2), (b + 3)] Side.lower (e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hRs1 : R.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [(b + 2), (b + 3)] Side.lower (e) (q := b)
        change _ ∈ R.extPositions 1
        rw [hRe1]
        simp
      have hRm1 : R.maximumAt 1 = e := rfl
      have hRe2 : R.extPositions 2 = [(b + 1)] := by
        change (O.part [(b + 2), (b + 3)] Side.lower (e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [(b + 2), (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOe1]
      have hRs2 : R.sideAt 2 = Side.upper := by
        change (O.part [(b + 2), (b + 3)] Side.lower (e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [(b + 2), (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOs1]
      have hRm2 : R.maximumAt 2 = od := by
        change (O.part [(b + 2), (b + 3)] Side.lower (e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [(b + 2), (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOm1]
      have hMbound : M.bound ≤ baseOf (min ((σ.cupLimit b b) - 2) od) (σ.capLimit b b) σ.k := by
        have hj0 : (σ.k - 1 - od) ≤ M.joinExt Side.lower (b + 1) (b + 1) := by
          have hjN1 := hjoinNew M Side.lower 1 (b + 1) (List.singleton_sublist.mp (hnewSub M 1 hMa Side.lower 0 [1] (by decide) (by simp [hMs1]))) [] []
            (hnewSub M 1 hMa Side.lower 1 [] (by decide) (by simp [hMs1])) (hnewSub M 1 hMa Side.lower 1 [] (by decide) (by simp [hMs1]))
          norm_num [leftStep, rightStep, hMe1, hMm1, Nat.add_assoc] at hjN1
          omega
        have hj1 : 0 ≤ M.joinExt Side.upper (b + 1) (b + 1) := by
          exact Nat.zero_le _
        have hh := hleafEstimate M 1 (b + 1) 1 hMa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hMc)
          [1] [1] [] []
          (hprefixSideSub M 1 Side.lower [1] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.lower [1] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [] (by decide) (by simp [hMs1]))
          b (b + 2) (b + 1) (b + 1) 1 1 0 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc]) (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc])
          (σ.k - 1 - od) 0 hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hQbound : Q.bound ≤ baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 1) (min e (σ.k - 1 - od - 1))) σ.k := by
        have hj0 : 0 ≤ Q.joinExt Side.lower b b := by
          exact Nat.zero_le _
        have hj1 : (max (σ.k - 1 - e) (od + 1)) ≤ Q.joinExt Side.upper b b := by
          have hjN1 := hjoinNew Q Side.upper 1 b (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.upper 0 [1] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.upper 1 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.upper 1 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN1
          have hjN2 := hjoinNew Q Side.upper 2 b (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.upper 0 [2] (by decide) (by simp [hQs1, hQs2]))) [] [1]
            (hnewSub Q 2 hQa Side.upper 2 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.upper 2 [1] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN2
          omega
        have hh := hleafEstimate Q 2 b 1 hQa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hQc)
          [] [] [] [1]
          (hprefixSideSub Q 2 Side.lower [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.lower [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [1] (by decide) (by simp [hQs1, hQs2]))
          b b b (b + 2) 0 0 0 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc])
          0 (max (σ.k - 1 - e) (od + 1)) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hRbound : R.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - e)) (min ((σ.capLimit b b) - 1) (σ.k - 1 - od)) σ.k := by
        have hj0 : (e) ≤ R.joinExt Side.lower (b + 2) (b + 2) := by
          have hjN1 := hjoinNew R Side.lower 1 (b + 2) (List.singleton_sublist.mp (hnewSub R 2 hRa Side.lower 0 [1] (by decide) (by simp [hRs1, hRs2]))) [] []
            (hnewSub R 2 hRa Side.lower 1 [] (by decide) (by simp [hRs1, hRs2])) (hnewSub R 2 hRa Side.lower 1 [] (by decide) (by simp [hRs1, hRs2]))
          norm_num [leftStep, rightStep, hRe1, hRe2, hRm1, hRm2, Nat.add_assoc] at hjN1
          omega
        have hj1 : (od) ≤ R.joinExt Side.upper (b + 2) (b + 2) := by
          have hjN2 := hjoinNew R Side.upper 2 (b + 2) (List.singleton_sublist.mp (hnewSub R 2 hRa Side.upper 0 [2] (by decide) (by simp [hRs1, hRs2]))) [] []
            (hnewSub R 2 hRa Side.upper 2 [] (by decide) (by simp [hRs1, hRs2])) (hnewSub R 2 hRa Side.upper 2 [] (by decide) (by simp [hRs1, hRs2]))
          norm_num [leftStep, rightStep, hRe1, hRe2, hRm1, hRm2, Nat.add_assoc] at hjN2
          omega
        have hh := hleafEstimate R 2 (b + 2) 2 hRa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hRc)
          [1] [] [2] []
          (hprefixSideSub R 2 Side.lower [1] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.lower [] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.upper [2] (by decide) (by simp [hRs1, hRs2])) (hprefixSideSub R 2 Side.upper [] (by decide) (by simp [hRs1, hRs2]))
          b (b + 2) (b + 1) (b + 2) 1 0 1 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [rightStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [leftStep, hRe1, hRe2, Nat.add_assoc]) (by norm_num [rightStep, hRe1, hRe2, Nat.add_assoc])
          (e) (od) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      change M.bound + Q.bound + R.bound ≤ _
      have hn := hthreeBaseDual (σ.cupLimit b b) (σ.capLimit b b) σ.k (σ.k - 1 - od) e hC hP (by omega) (by omega) he hek
      have hnum : baseOf (min ((σ.cupLimit b b) - 2) od) (σ.capLimit b b) σ.k + baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 1) (min e (σ.k - 1 - od - 1))) σ.k + baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - e)) (min ((σ.capLimit b b) - 1) (σ.k - 1 - od)) σ.k ≤ baseOf (σ.cupLimit b b) (σ.capLimit b b) σ.k := by
        have hkd : σ.k - 2 - od = σ.k - 1 - od - 1 := by omega
        have hkc : σ.k - 1 - (σ.k - 1 - od) = od := by omega
        simpa only [hkd, hkc, min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hn
      rw [hrunBound σ b 4 (by decide) hpos]
      exact (Nat.add_le_add (Nat.add_le_add hMbound hQbound) hRbound).trans hnum
  exact ⟨hquad_0000, hquad_0010, hquad_1000, hquad_1010⟩

end ErdosSzekeres
