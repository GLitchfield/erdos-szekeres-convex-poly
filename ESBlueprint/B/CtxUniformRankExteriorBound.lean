import ESBlueprint.B.CtxUniformRankUnitPartExteriorCharge

import ESBlueprint.B.CtxOneLevelExteriorPotentialBound

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Full strict doubled-rank bound for positive-label contexts whose source children are all active with chosen capacity at least two and have uniform opposite pure extension traces. Under chosen global at most four and one actual indexed chosen marker, every fuel approximation and the full recursive bound are at most twice the common opposite-rank interval cardinality minus one. Both exteriors may contain arbitrarily many children, older indexed histories and maxima are arbitrary, and empty child sets are allowed. Fuel induction combines the strict uniform-rank unit-part charge, the nonunit-part active-companion cut estimate, and the full one-level raw exterior potential; an inactive companion is removed using original-history pruning, which preserves all source hypotheses for the prior-fuel induction. Supplies a reusable full-context estimate for uniform-rank capacity-three gaps toward the singleton-end sandwich obstruction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_uniform_rank_exterior_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4)
  (L R : ℕ)
  (hsource : ∀ r ∈ σ.childPositions, 0 < σ.cupLimit r r ∧ 0 < σ.capLimit r r ∧
    2 ≤ (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.cupLimit r r | Ctx.Side.upper => σ.capLimit r r) s)
  (htraces : ∀ r ∈ σ.childPositions,
    σ.leftExt t 0 r = L ∧ σ.rightExt t 0 r = R) :
  let global := fun (ρ : Ctx.Context) (v : Ctx.Side) =>
    match v with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let sourceRanks := Finset.Icc (L + 1) (global σ t - 1 - R)
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2 * sourceRanks.card - 1) ∧
    σ.bound ≤ 2 * sourceRanks.card - 1 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let C (ρ : Context) (v : Side) (r : ℕ) := match v with
    | Side.lower => ρ.cupLimit r r | Side.upper => ρ.capLimit r r
  let active (ρ : Context) : Finset ℕ := ρ.childPositions.toFinset.filter
    (fun r => 0 < ρ.cupLimit r r ∧ 0 < ρ.capLimit r r)
  let marks (ρ : Context) : Finset ℕ :=
    (ρ.levelsOn s 0).toFinset.biUnion (fun j => (ρ.extPositions j).toFinset)
  let label (M : Finset ℕ) (r : ℕ) : ℕ :=
    if (M.filter (· < r)).Nonempty then
      if (M.filter (r < ·)).Nonempty then 1 else 2
    else 0
  let units (ρ : Context) := (active ρ).filter (fun r => C ρ s r ≤ 1)
  let colors (ρ : Context) := (units ρ).image (label (marks ρ))
  let I (ρ : Context) (v : Side) (p : ℕ) :=
    Finset.Icc (ρ.leftExt v 0 p + 1) (G ρ v - 1 - ρ.rightExt v 0 p)
  let F (ρ : Context) (e : ℕ) :=
    (active ρ).filter (fun p => 2 ≤ C ρ s p ∧ label (marks ρ) p = e)
  let RN (ρ : Context) (e : ℕ) := (F ρ e).biUnion (I ρ t)
  let T (ρ : Context) := (colors ρ).card + (RN ρ 0).card + (RN ρ 2).card
  let Good (ρ : Context) : Prop := ∃ N x : ℕ,
    N ∈ ρ.levels ∧ ρ.sideAt N = s ∧ x ∈ ρ.extPositions N
  let Src (ρ : Context) : Prop := ∀ r ∈ ρ.childPositions,
    0 < ρ.cupLimit r r ∧ 0 < ρ.capLimit r r ∧ 2 ≤ C ρ s r
  let Tr (ρ : Context) : Prop := ∀ r ∈ ρ.childPositions,
    ρ.leftExt t 0 r = L ∧ ρ.rightExt t 0 r = R
  let S (ρ : Context) := Finset.Icc (L + 1) (G ρ t - 1 - R)
  let Budget (ρ : Context) := 2 * (S ρ).card - 1
  change (∀ fuel, boundFuel fuel σ ≤ Budget σ) ∧ σ.bound ≤ Budget σ
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
  have hGoodPart (ρ : Context) (hg : Good ρ) (keep : List ℕ) (v : Side) (m : ℕ) :
      Good (ρ.part keep v m) := by
    obtain ⟨N, x, hN, hNs, hx⟩ := hg
    have hN1 := one_le_of_mem_levels hN
    refine ⟨N + 1, x, ?_, ?_, ?_⟩
    · rw [part_levels]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
    · simpa only [part_sideAt_succ ρ keep v m hN1] using hNs
    · simpa only [part_extPositions_succ ρ keep v m hN1] using hx
  have hGPart (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) (w : Side) :
      G (ρ.part keep v m) w = G ρ w := by cases w <;> rfl
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
    obtain ⟨N, x, hN, hNs, hx⟩ := hgood
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
  have hISource (ρ : Context) (hTr : Tr ρ) (p : ℕ) (hp : p ∈ ρ.childPositions) :
      I ρ t p = S ρ := by
    obtain ⟨hl, hr⟩ := hTr p hp
    simp only [I, S, hl, hr]
  have hWidth (ρ : Context) (p : ℕ) : C ρ t p ≤ (I ρ t p).card := by
    simp only [I, Nat.card_Icc]
    cases t <;> simp only [G, C, cupLimit, capLimit, chainExt] <;> omega
  have hSourceRanks (ρ : Context) (hSrc : Src ρ) (hTr : Tr ρ)
      (p : ℕ) (hp : p ∈ ρ.childPositions) :
      (active ρ).biUnion (I ρ t) = S ρ := by
    apply Finset.Subset.antisymm
    · intro z hz
      obtain ⟨a, ha, hz⟩ := Finset.mem_biUnion.mp hz
      simpa only [hISource ρ hTr a ((hActive ρ a).mp ha).1] using hz
    · intro z hz
      exact Finset.mem_biUnion.mpr ⟨p,
        (hActive ρ p).mpr ⟨hp, (hSrc p hp).1, (hSrc p hp).2.1⟩,
        by simpa only [hISource ρ hTr p hp] using hz⟩
  have hBase (ρ : Context) (hg : G ρ s ≤ 4) (hgood : Good ρ)
      (hSrc : Src ρ) (hTr : Tr ρ) : ρ.base ≤ Budget ρ := by
    rw [base_eq_baseOf]
    cases he : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr he)
      have hs := hSrc p hp
      have hlim := hChosenTwo ρ hg hgood p hp
      have hcupk : ρ.cupLimit p p ≤ ρ.k - 1 := by dsimp only [cupLimit]; omega
      have hcapk : ρ.capLimit p p ≤ ρ.k - 1 := by dsimp only [capLimit]; omega
      have hOpp : baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ C ρ t p := by
        cases s <;> cases t
        · exact False.elim (hne rfl)
        · exact hBaseLower _ _ _ hlim hcapk
        · exact hBaseUpper _ _ _ hlim hcupk
        · exact False.elim (hne rfl)
      have hpos : 0 < C ρ t p := by
        cases t
        · exact hs.1
        · exact hs.2.1
      have hw := hWidth ρ p
      rw [hISource ρ hTr p hp] at hw
      dsimp only [Budget]
      omega
  have hRaw (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hg : G ρ s ≤ 4) (hgood : Good ρ) (fuel : ℕ) : boundFuel fuel ρ ≤ T ρ := by
    obtain ⟨N, x, hN, hNs, hx⟩ := hgood
    exact (ctx_one_level_exterior_potential_bound ρ hPos s t hne N x hN hNs hx hg).1 fuel
  have hCut (fuel : ℕ) (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hg : G ρ s ≤ 4) (hgood : Good ρ) (hSrc : Src ρ) (hTr : Tr ρ)
      (ih : ∀ υ : Context,
        (∀ p j v, υ.letterAt p = Letter.ext j v → 1 ≤ j) →
        G υ s ≤ 4 → Good υ → Src υ → Tr υ → boundFuel fuel υ ≤ Budget υ)
      (keep : List ℕ) (m n p q : ℕ)
      (hp : p ∈ ρ.childPositions) (hkeep : p ∈ keep)
      (hq : q ∈ ρ.childPositions) (hremoved : q ∉ keep) :
      boundFuel fuel (ρ.part keep s m) +
        boundFuel fuel (ρ.part (ρ.childPositions.filter (· ∉ keep)) t n) ≤ Budget ρ := by
    let rest := ρ.childPositions.filter (· ∉ keep)
    let A := ρ.part keep s m
    let B := ρ.part rest t n
    change boundFuel fuel A + boundFuel fuel B ≤ Budget ρ
    have hiB : boundFuel fuel B ≤ T B :=
      hRaw B (hPositivePart ρ rest t n) (by simpa only [B, hGPart] using hg)
        (hGoodPart ρ hgood rest t n) fuel
    obtain ⟨N, x, hN, hNs, hx⟩ := hgood
    by_cases hb : (active B).Nonempty
    · obtain ⟨b, hb⟩ := hb
      obtain ⟨hbc, hbcu, hbca⟩ := (hActive B b).mp hb
      by_cases huA : ∀ a ∈ active A, C A s a ≤ 1
      · have hpa : p ∈ A.childPositions := by
          simp only [A, part_childPositions, List.mem_filter, decide_eq_true_eq]
          exact ⟨hp, hkeep⟩
        have hh := ctx_uniform_rank_unit_part_exterior_charge ρ hPos s t hne N x hN hNs hx hg
          L R hSrc hTr keep m n p b hpa hbc hbcu hbca (by
            intro a hac hcu hca
            have hh := huA a ((hActive A a).mpr ⟨hac, hcu, hca⟩)
            cases s <;> simpa only [C, A] using hh)
        have hcharge : boundFuel fuel A + T B ≤ Budget ρ := hh.2.1 fuel
        omega
      · push_neg at huA
        obtain ⟨a, ha, ha2⟩ := huA
        obtain ⟨hac, hacu, haca⟩ := (hActive A a).mp ha
        have hanonunit : 2 ≤ C A s a := by omega
        have hh := ctx_nonunit_part_active_companion_cut_potential_bound ρ hPos s t hne
          N x hN hNs hx hg keep m n a b hac
          (by cases s <;> simpa only [C, A] using hanonunit) hbc hbcu hbca
        have hcharge := (hh.1 fuel fuel).trans (Nat.min_le_right _ _)
        change boundFuel fuel A + boundFuel fuel B ≤
          2 * ((active ρ).biUnion (I ρ t)).card - 1 at hcharge
        rw [hSourceRanks ρ hSrc hTr p hp] at hcharge
        exact hcharge
    have hbempty : active B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
    have hTB : T B = 0 := by simp [T, colors, units, RN, F, hbempty]
    have hbzero : boundFuel fuel B = 0 := by omega
    let τ : Context := { ρ with
      word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
        | Letter.child => if p ∈ keep then Letter.child else Letter.ext (ρ.maxima.length + 1) s
        | Letter.ext j v => Letter.ext j v) }
    have hpr := ctx_part_pruning_history_transport ρ hPos keep s m
    change (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
      τ.childPositions = ρ.childPositions.filter (· ∈ keep) ∧
      (∀ j ∈ ρ.levels, τ.extPositions j = ρ.extPositions j ∧ τ.sideAt j = ρ.sideAt j) ∧
      (∀ v top, τ.levelsOn v top = ρ.levelsOn v top) ∧
      (∀ v top a, τ.leftExt v top a = ρ.leftExt v top a ∧
        τ.rightExt v top a = ρ.rightExt v top a) ∧
      (∀ a b, τ.cupLimit a b = ρ.cupLimit a b ∧ τ.capLimit a b = ρ.capLimit a b) ∧
      active τ = (active ρ).filter (· ∈ keep) ∧
      (∀ fuel, boundFuel fuel A ≤ boundFuel fuel τ) ∧ A.bound ≤ τ.bound at hpr
    obtain ⟨hτPos, hτChild, hτHist, hτLevels, hτExt, hτLimits, hτActive, hτFuel, hτBound⟩ := hpr
    have hChild (a : ℕ) (ha : a ∈ τ.childPositions) : a ∈ ρ.childPositions := by
      rw [hτChild] at ha
      exact (List.mem_filter.mp ha).1
    have hC (a : ℕ) : C τ s a = C ρ s a := by
      cases s
      · exact (hτLimits a a).1
      · exact (hτLimits a a).2
    have hτSrc : Src τ := by
      intro a ha
      have hh := hSrc a (hChild a ha)
      refine ⟨?_, ?_, ?_⟩
      · rw [(hτLimits a a).1]; exact hh.1
      · rw [(hτLimits a a).2]; exact hh.2.1
      · rw [hC]; exact hh.2.2
    have hτTr : Tr τ := by
      intro a ha
      rw [(hτExt t 0 a).1, (hτExt t 0 a).2]
      exact hTr a (hChild a ha)
    have hτGood : Good τ := by
      refine ⟨N, x, hN, ?_, ?_⟩
      · exact (hτHist N hN).2.trans hNs
      · simpa only [(hτHist N hN).1] using hx
    have hτG : G τ s ≤ 4 := by cases s <;> simpa only [G, τ] using hg
    have hτIH : boundFuel fuel τ ≤ Budget τ := ih τ hτPos hτG hτGood hτSrc hτTr
    rw [hbzero, Nat.add_zero]
    exact (hτFuel fuel).trans hτIH
  have hFuel : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      G ρ s ≤ 4 → Good ρ → Src ρ → Tr ρ → boundFuel fuel ρ ≤ Budget ρ := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _ _ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hPos hg hgood hSrc hTr
      rw [boundFuel]
      split
      · exact hBase ρ hg hgood hSrc hTr
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
        have hforward (a b : ℕ) : boundFuel fuel (ρ.part keep s a) +
            boundFuel fuel (ρ.part rest t b) ≤ Budget ρ :=
          hCut fuel ρ hPos hg hgood hSrc hTr ih keep a b p q hp hpk hq hqk
        have hdouble (v : Side) (m : ℕ) :
            ρ.part (ρ.childPositions.filter (· ∉ rest)) v m = ρ.part keep v m := by
          apply part_congr
          intro r hr
          simp only [rest, List.mem_filter, decide_eq_true_eq, hr, true_and, not_not]
        have hbackward (a b : ℕ) : boundFuel fuel (ρ.part rest s a) +
            boundFuel fuel (ρ.part keep t b) ≤ Budget ρ := by
          have hh := hCut fuel ρ hPos hg hgood hSrc hTr ih rest a b q p
            hq (by simp [rest, hq, hqk]) hp (by simp [rest, hpk])
          rw [hdouble] at hh
          exact hh
        have hboth (a b : ℕ) :
            (boundFuel fuel (ρ.part keep Side.lower a) +
              boundFuel fuel (ρ.part rest Side.upper b) ≤ Budget ρ) ∧
            (boundFuel fuel (ρ.part keep Side.upper b) +
              boundFuel fuel (ρ.part rest Side.lower a) ≤ Budget ρ) := by
          cases s <;> cases t
          · exact False.elim (hne rfl)
          · exact ⟨hforward a b, by simpa only [Nat.add_comm] using hbackward a b⟩
          · exact ⟨by simpa only [Nat.add_comm] using hbackward b a, hforward b a⟩
          · exact False.elim (hne rfl)
        rcases hz with rfl | rfl
        · exact (hboth (d + 1) (ρ.k - 1 - (d + 1))).1
        · exact (hboth (d + 1) (ρ.k - 1 - (d + 1))).2
  have hf : ∀ fuel, boundFuel fuel σ ≤ Budget σ :=
    fun fuel => hFuel fuel σ hpositive hglobal ⟨N, x, hN, hNs, hx⟩ hsource htraces
  exact ⟨hf, hf _⟩


end ErdosSzekeres
