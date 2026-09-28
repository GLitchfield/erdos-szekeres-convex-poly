import ESBlueprint.B.CtxUnitPartRefinedExteriorCharge
import ESBlueprint.B.CtxOneLevelExteriorPotentialBound

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Full refined one-level exterior potential for arbitrary positive histories. If the chosen global parameter is at most four and there is an actual indexed chosen marker, every fuel approximation and the full recursive bound are at most the minimum of the occupied active chosen-unit-zone count plus the two separate nonunit exterior opposite-rank-union cardinalities, and twice the all-active opposite-rank-union cardinality minus one. Consequently they are at most twice the opposite global parameter minus three, using natural subtraction. Source capacities may be mixed, rank unions disconnected, and inactive children arbitrary. Fuel induction combines the refined unit-part charge, the nonunit active-companion cut bound, and exact original-history pruning for inactive companions; the previously checked raw exterior theorem supplies the other component. Removes the uniform-rank and source-nonunit restrictions from the one-level capacity-three estimate toward the singleton-end sandwich obstruction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_one_level_refined_potential_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4) :
  let global := fun (ρ : Ctx.Context) (v : Ctx.Side) =>
    match v with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let limit : Ctx.Context → ℕ → ℕ := fun ρ r =>
    (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => ρ.cupLimit r r | Ctx.Side.upper => ρ.capLimit r r) s
  let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
    (fun r => 0 < ρ.cupLimit r r ∧ 0 < ρ.capLimit r r)
  let markers := fun (ρ : Ctx.Context) => (ρ.levelsOn s 0).toFinset.biUnion
    (fun j => (ρ.extPositions j).toFinset)
  let label := fun (ρ : Ctx.Context) (r : ℕ) =>
    if ((markers ρ).filter (· < r)).Nonempty then
      if ((markers ρ).filter (r < ·)).Nonempty then (1 : ℕ) else 2
    else 0
  let unitZones := fun (ρ : Ctx.Context) =>
    (((active ρ).filter (fun r => limit ρ r ≤ 1)).image (label ρ)).card
  let rankInterval := fun (ρ : Ctx.Context) (r : ℕ) =>
    Finset.Icc (ρ.leftExt t 0 r + 1) (global ρ t - 1 - ρ.rightExt t 0 r)
  let exteriorRanks := fun (ρ : Ctx.Context) (c : ℕ) =>
    ((active ρ).filter (fun r => 2 ≤ limit ρ r ∧ label ρ r = c)).biUnion (rankInterval ρ)
  let ranks := fun (ρ : Ctx.Context) => (active ρ).biUnion (rankInterval ρ)
  let potential := fun (ρ : Ctx.Context) =>
    min (unitZones ρ + (exteriorRanks ρ 0).card + (exteriorRanks ρ 2).card)
      (2 * (ranks ρ).card - 1)
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ potential σ) ∧ σ.bound ≤ potential σ ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2 * (global σ t - 1) - 1) ∧
      σ.bound ≤ 2 * (global σ t - 1) - 1 := by
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
  let S (ρ : Context) := (active ρ).biUnion (I ρ t)
  let Budget (ρ : Context) := 2 * (S ρ).card - 1
  change (∀ fuel, boundFuel fuel σ ≤ min (T σ) (Budget σ)) ∧
    σ.bound ≤ min (T σ) (Budget σ) ∧
    (∀ fuel, boundFuel fuel σ ≤ 2 * (G σ t - 1) - 1) ∧
      σ.bound ≤ 2 * (G σ t - 1) - 1
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
  have hWidth (ρ : Context) (p : ℕ) : C ρ t p ≤ (I ρ t p).card := by
    simp only [I, Nat.card_Icc]
    cases t <;> simp only [G, C, cupLimit, capLimit, chainExt] <;> omega
  have hBase (ρ : Context) (hg : G ρ s ≤ 4) (hgood : Good ρ) :
      ρ.base ≤ Budget ρ := by
    rw [base_eq_baseOf]
    cases he : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr he)
      by_cases hz : ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0
      · simp [baseOf, hz]
      have hpos : 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by omega
      have hlim := hChosenTwo ρ hg hgood p hp
      have hcupk : ρ.cupLimit p p ≤ ρ.k - 1 := by dsimp only [cupLimit]; omega
      have hcapk : ρ.capLimit p p ≤ ρ.k - 1 := by dsimp only [capLimit]; omega
      have hOpp : baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ C ρ t p := by
        cases s <;> cases t
        · exact False.elim (hne rfl)
        · exact hBaseLower _ _ _ hlim hcapk
        · exact hBaseUpper _ _ _ hlim hcupk
        · exact False.elim (hne rfl)
      have hsub : I ρ t p ⊆ S ρ := fun z hz =>
        Finset.mem_biUnion.mpr ⟨p, (hActive ρ p).mpr ⟨hp, hpos⟩, hz⟩
      have hw := (hWidth ρ p).trans (Finset.card_le_card hsub)
      have htpos : 0 < C ρ t p := by cases t <;> simp only [C] <;> omega
      dsimp only [Budget]
      omega
  have hRaw (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hg : G ρ s ≤ 4) (hgood : Good ρ) (fuel : ℕ) : boundFuel fuel ρ ≤ T ρ := by
    obtain ⟨N, x, hN, hNs, hx⟩ := hgood
    exact (ctx_one_level_exterior_potential_bound ρ hPos s t hne N x hN hNs hx hg).1 fuel
  have hCut (fuel : ℕ) (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hg : G ρ s ≤ 4) (hgood : Good ρ)
      (ih : ∀ υ : Context,
        (∀ p j v, υ.letterAt p = Letter.ext j v → 1 ≤ j) →
        G υ s ≤ 4 → Good υ → boundFuel fuel υ ≤ Budget υ)
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
    have hiB2 : boundFuel fuel B ≤ Budget B :=
      ih B (hPositivePart ρ rest t n) (by simpa only [B, hGPart] using hg)
        (hGoodPart ρ hgood rest t n)
    have hiBQ : boundFuel fuel B ≤ min (T B) (Budget B) := le_min hiB hiB2
    obtain ⟨N, x, hN, hNs, hx⟩ := hgood
    by_cases hb : (active B).Nonempty
    · obtain ⟨b, hb⟩ := hb
      obtain ⟨hbc, hbcu, hbca⟩ := (hActive B b).mp hb
      by_cases huA : ∀ a ∈ active A, C A s a ≤ 1
      · have hpa : p ∈ A.childPositions := by
          simp only [A, part_childPositions, List.mem_filter, decide_eq_true_eq]
          exact ⟨hp, hkeep⟩
        have hh := ctx_unit_part_refined_exterior_charge ρ hPos s t hne N x hN hNs hx hg
          keep m n p b hpa hbc hbcu hbca (by
            intro a hac hcu hca
            have hh := huA a ((hActive A a).mpr ⟨hac, hcu, hca⟩)
            cases s <;> simpa only [C, A] using hh)
        have hcharge : boundFuel fuel A + min (T B) (Budget B) ≤ Budget ρ := hh.2.1 fuel
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
    have hRanks : S τ ⊆ S ρ := by
      intro z hz
      obtain ⟨a, ha, hz⟩ := Finset.mem_biUnion.mp hz
      have haa : a ∈ active ρ := by
        rw [hτActive] at ha
        exact (Finset.mem_filter.mp ha).1
      refine Finset.mem_biUnion.mpr ⟨a, haa, ?_⟩
      have hI : I τ t a = I ρ t a := by
        dsimp only [I]
        rw [(hτExt t 0 a).1, (hτExt t 0 a).2]
      simpa only [hI] using hz
    have hBudget : Budget τ ≤ Budget ρ :=
      Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 (Finset.card_le_card hRanks)) 1
    have hτGood : Good τ := by
      refine ⟨N, x, hN, ?_, ?_⟩
      · exact (hτHist N hN).2.trans hNs
      · simpa only [(hτHist N hN).1] using hx
    have hτG : G τ s ≤ 4 := by cases s <;> simpa only [G, τ] using hg
    have hτIH : boundFuel fuel τ ≤ Budget τ := ih τ hτPos hτG hτGood
    rw [hbzero, Nat.add_zero]
    exact (hτFuel fuel).trans (hτIH.trans hBudget)
  have hFuel : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      G ρ s ≤ 4 → Good ρ → boundFuel fuel ρ ≤ Budget ρ := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hPos hg hgood
      rw [boundFuel]
      split
      · exact hBase ρ hg hgood
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
          hCut fuel ρ hPos hg hgood ih keep a b p q hp hpk hq hqk
        have hdouble (v : Side) (m : ℕ) :
            ρ.part (ρ.childPositions.filter (· ∉ rest)) v m = ρ.part keep v m := by
          apply part_congr
          intro r hr
          simp only [rest, List.mem_filter, decide_eq_true_eq, hr, true_and, not_not]
        have hbackward (a b : ℕ) : boundFuel fuel (ρ.part rest s a) +
            boundFuel fuel (ρ.part keep t b) ≤ Budget ρ := by
          have hh := hCut fuel ρ hPos hg hgood ih rest a b q p
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
    fun fuel => hFuel fuel σ hpositive hglobal ⟨N, x, hN, hNs, hx⟩
  have hmin : ∀ fuel, boundFuel fuel σ ≤ min (T σ) (Budget σ) :=
    fun fuel => le_min (hRaw σ hpositive hglobal ⟨N, x, hN, hNs, hx⟩ fuel) (hf fuel)
  have hS : S σ ⊆ Finset.Icc 1 (G σ t - 1) := by
    intro z hz
    obtain ⟨a, ha, hz⟩ := Finset.mem_biUnion.mp hz
    have hh := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcard : (S σ).card ≤ G σ t - 1 := by
    have hh := Finset.card_le_card hS
    simpa only [Nat.card_Icc] using hh
  have hBudget : Budget σ ≤ 2 * (G σ t - 1) - 1 :=
    Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hcard) 1
  exact ⟨hmin, hmin _, fun fuel => (hf fuel).trans hBudget, (hf _).trans hBudget⟩

end ErdosSzekeres
