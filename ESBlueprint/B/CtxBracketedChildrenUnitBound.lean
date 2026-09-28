import ESBlueprint.B.CtxBoundLeSumPointBases

import ESBlueprint.B.CtxBoundAttainedByEndCut

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Bracketed-child capacity annihilation and a shared unit bound. With chosen global parameter at most four, two indexed markers on that axis bracketing a kept child and a removed child force the kept child to have zero chosen capacity in the corresponding same-axis part. Other children may lie outside the bracket. If all children lie between the two markers, every fuel approximation and the full recursive bound are at most one. The boundary levels may coincide and arbitrary other histories, internal markers, maxima and empty child sets are allowed under positive labels. The new removed-child marker and both old boundary witnesses supply three extension units; induction leaves only the opposite-axis branch. Supplies a single contribution for an entire interior marker region in the singleton-end sandwich potential.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bracketed_children_unit_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s : Ctx.Side) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) :
  (∀ (keep : List ℕ) (newMax r : ℕ), r ∈ σ.childPositions → r ∉ keep → x < r → r < y →
    ∀ p ∈ (σ.part keep s newMax).childPositions, x < p → p < y →
      (match s with
        | Ctx.Side.lower => (σ.part keep s newMax).cupLimit p p
        | Ctx.Side.upper => (σ.part keep s newMax).capLimit p p) = 0) ∧
  ((∀ p ∈ σ.childPositions, x < p ∧ p < y) →
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 1) ∧ σ.bound ≤ 1) := by
  classical
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
  have hLocal (ρ : Context)
      (hpos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (n m a b : ℕ) (hn : n ∈ ρ.levels) (hm : m ∈ ρ.levels)
      (hns : ρ.sideAt n = s) (hms : ρ.sideAt m = s)
      (ha : a ∈ ρ.extPositions n) (hb : b ∈ ρ.extPositions m)
      (hglob : (match s with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 4)
      (keep : List ℕ) (newMax r : ℕ) (hr : r ∈ ρ.childPositions)
      (hrnot : r ∉ keep) (har : a < r) (hrb : r < b)
      (p : ℕ) (hp : p ∈ (ρ.part keep s newMax).childPositions)
      (hap : a < p) (hpb : p < b) :
      (match s with
        | Side.lower => (ρ.part keep s newMax).cupLimit p p
        | Side.upper => (ρ.part keep s newMax).capLimit p p) = 0 := by
    let τ := ρ.part keep s newMax
    have hn1 := one_le_of_mem_levels hn
    have hm1 := one_le_of_mem_levels hm
    have hRemoved : r ∈ τ.extPositions 1 := by
      simp only [τ, part_extPositions_one hpos, List.mem_filter, decide_eq_true_eq]
      exact ⟨hr, hrnot⟩
    have hSide : τ.sideAt 1 = s := part_sideAt_one_of_mem hpos keep s newMax hRemoved
    have hLevels : τ.levelsOn s 0 = 1 :: (ρ.levelsOn s 0).map (· + 1) :=
      part_levelsOn_self_zero hSide
    have hnOn : n ∈ ρ.levelsOn s 0 := by
      exact List.mem_filter.mpr ⟨hn, by simp [hns]⟩
    have hmOn : m ∈ ρ.levelsOn s 0 := by
      exact List.mem_filter.mpr ⟨hm, by simp [hms]⟩
    have hnNew : n + 1 ∈ τ.levelsOn s 0 := by rw [hLevels]; simp [hnOn]
    have hmNew : m + 1 ∈ τ.levelsOn s 0 := by rw [hLevels]; simp [hmOn]
    have hTwoN : [1, n + 1].Sublist (τ.levelsOn s 0) := by
      rw [hLevels]
      exact (List.singleton_sublist.mpr (List.mem_map.mpr ⟨n, hnOn, rfl⟩)).cons_cons 1
    have hTwoM : [1, m + 1].Sublist (τ.levelsOn s 0) := by
      rw [hLevels]
      exact (List.singleton_sublist.mpr (List.mem_map.mpr ⟨m, hmOn, rfl⟩)).cons_cons 1
    have haNew : a ∈ τ.extPositions (n + 1) := by
      simpa only [τ, part_extPositions_succ ρ keep s newMax hn1] using ha
    have hbNew : b ∈ τ.extPositions (m + 1) := by
      simpa only [τ, part_extPositions_succ ρ keep s newMax hm1] using hb
    have hSort : (τ.extPositions 1).Pairwise (· ≤ ·) :=
      (List.pairwise_lt_range.filter _).imp le_of_lt
    have hpr : p ≠ r := by
      have hpKeep : p ∈ keep := by
        simpa only [part_childPositions, List.mem_filter, decide_eq_true_eq] using
          (show p ∈ ρ.childPositions ∧ p ∈ keep from by
            simpa only [part_childPositions, List.mem_filter, decide_eq_true_eq] using hp).2
      intro h
      exact hrnot (h ▸ hpKeep)
    have hChain : 3 ≤ τ.chainExt s p p := by
      by_cases hrp : r < p
      · have hmR : r ∈ (τ.extPositions 1).filter (· < p) := by simp [hRemoved, hrp]
        have hne := List.ne_nil_of_mem hmR
        let w := ((τ.extPositions 1).filter (· < p)).getLast hne
        have hw : ((τ.extPositions 1).filter (· < p)).getLast? = some w :=
          List.getLast?_eq_some_getLast hne
        have hrw : r ≤ w := (hSort.filter _).rel_getLast hmR
        have hma : a ∈ (τ.extPositions (n + 1)).filter (· < w) := by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨haNew, by omega⟩
        have hneOld := List.ne_nil_of_mem hma
        have hv := le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (leftStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[1, n + 1], List.mem_sublists.mpr hTwoN, rfl⟩)
        change _ ≤ τ.leftExt s 0 p at hv
        have hL : 2 ≤ τ.leftExt s 0 p := by
          simpa only [List.foldl_cons, List.foldl_nil, leftStep, hw,
            List.getLast?_eq_some_getLast hneOld] using hv
        have hR := hOneRight τ s (m + 1) p b hmNew hbNew hpb
        simp only [chainExt]
        omega
      · have hpr' : p < r := by omega
        have hmR : r ∈ (τ.extPositions 1).filter (p < ·) := by simp [hRemoved, hpr']
        have hne := List.ne_nil_of_mem hmR
        let w := ((τ.extPositions 1).filter (p < ·)).head hne
        have hw : ((τ.extPositions 1).filter (p < ·)).head? = some w :=
          List.head?_eq_some_head hne
        have hwr : w ≤ r := (hSort.filter _).rel_head hmR
        have hmb : b ∈ (τ.extPositions (m + 1)).filter (w < ·) := by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hbNew, by omega⟩
        have hneOld := List.ne_nil_of_mem hmb
        have hv := le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (rightStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[1, m + 1], List.mem_sublists.mpr hTwoM, rfl⟩)
        change _ ≤ τ.rightExt s 0 p at hv
        have hR : 2 ≤ τ.rightExt s 0 p := by
          simpa only [List.foldl_cons, List.foldl_nil, rightStep, hw,
            List.head?_eq_some_head hneOld] using hv
        have hL := hOneLeft τ s (n + 1) p a hnNew haNew hap
        simp only [chainExt]
        omega
    have hg : (match s with | Side.lower => τ.u | Side.upper => τ.a) ≤ 4 := by
      simpa only [τ, part] using hglob
    change (match s with | Side.lower => τ.cupLimit p p | Side.upper => τ.capLimit p p) = 0
    cases hs : s <;> simp only [hs] at hg hChain ⊢
    · simp only [cupLimit]
      omega
    · simp only [capLimit]
      omega
  let Good (ρ : Context) : Prop :=
    (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
    (match s with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 4 ∧
    ∃ n m a b, n ∈ ρ.levels ∧ m ∈ ρ.levels ∧ ρ.sideAt n = s ∧ ρ.sideAt m = s ∧
      a ∈ ρ.extPositions n ∧ b ∈ ρ.extPositions m ∧
      ∀ p ∈ ρ.childPositions, a < p ∧ p < b
  have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ p j t, (ρ.part keep v m).letterAt p = Letter.ext j t → 1 ≤ j := by
    intro p j t hp
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
  have hGoodPart (ρ : Context) (hgood : Good ρ) (keep : List ℕ) (v : Side) (newMax : ℕ) :
      Good (ρ.part keep v newMax) := by
    obtain ⟨hpos, hg, n, m, a, b, hn, hm, hns, hms, ha, hb, hbr⟩ := hgood
    refine ⟨hPartPositive ρ keep v newMax, hg, n + 1, m + 1, a, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [part_levels]
      exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨n, hn, rfl⟩))
    · rw [part_levels]
      exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨m, hm, rfl⟩))
    · simpa only [part_sideAt_succ ρ keep v newMax (one_le_of_mem_levels hn)] using hns
    · simpa only [part_sideAt_succ ρ keep v newMax (one_le_of_mem_levels hm)] using hms
    · simpa only [part_extPositions_succ ρ keep v newMax (one_le_of_mem_levels hn)] using ha
    · simpa only [part_extPositions_succ ρ keep v newMax (one_le_of_mem_levels hm)] using hb
    · intro p hp
      rw [part_childPositions] at hp
      exact hbr p (List.mem_filter.mp hp).1
  have hPointUnit (ρ : Context) (hgood : Good ρ) (p : ℕ) (hp : p ∈ ρ.childPositions) :
      (match s with | Side.lower => ρ.cupLimit p p | Side.upper => ρ.capLimit p p) ≤ 1 := by
    obtain ⟨_, hg, n, m, a, b, hn, hm, hns, hms, ha, hb, hbr⟩ := hgood
    have hnOn : n ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hn, by simp [hns]⟩
    have hmOn : m ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hm, by simp [hms]⟩
    have hL := hOneLeft ρ s n p a hnOn ha (hbr p hp).1
    have hR := hOneRight ρ s m p b hmOn hb (hbr p hp).2
    have hc : 2 ≤ ρ.chainExt s p p := by simp only [chainExt]; omega
    cases hs : s <;> simp only [hs] at hg hc ⊢
    · simp only [cupLimit]
      omega
    · simp only [capLimit]
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
  have hPartZero (ρ : Context) (hgood : Good ρ) (keep : List ℕ) (newMax : ℕ)
      (hremoved : ∃ r ∈ ρ.childPositions, r ∉ keep) (fuel : ℕ) :
      boundFuel fuel (ρ.part keep s newMax) = 0 := by
    obtain ⟨hpos, hg, n, m, a, b, hn, hm, hns, hms, ha, hb, hbr⟩ := hgood
    obtain ⟨r, hr, hrnot⟩ := hremoved
    have hz : (ρ.part keep s newMax).bound = 0 := by
      apply hZero
      intro p hp
      have hpOld : p ∈ ρ.childPositions := by
        rw [part_childPositions] at hp
        exact (List.mem_filter.mp hp).1
      have hc := hLocal ρ hpos n m a b hn hm hns hms ha hb hg keep newMax r hr hrnot
        (hbr r hr).1 (hbr r hr).2 p hp (hbr p hpOld).1 (hbr p hpOld).2
      cases hs : s <;> simp only [hs] at hc ⊢
      · exact Or.inl hc
      · exact Or.inr hc
    exact Nat.eq_zero_of_le_zero ((hFuelLe _ fuel).trans_eq hz)
  have hFuel : ∀ fuel (ρ : Context), Good ρ → boundFuel fuel ρ ≤ 1 := by
    intro fuel
    induction fuel with
    | zero => intro ρ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hgood
      rw [boundFuel]
      split
      · rw [base_eq_baseOf]
        cases hh : ρ.childPositions.head? with
        | none => exact Nat.zero_le _
        | some p =>
          have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
          have hu := hPointUnit ρ hgood p hp
          have hsmall : min (ρ.cupLimit p p) (ρ.capLimit p p) ≤ 1 := by
            cases s <;> simp only at hu <;> omega
          change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ 1
          unfold baseOf
          split_ifs <;> omega
      · apply Ctx.getD_max?_le
        intro z hz
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hz
        obtain ⟨keep, hkeep, d, _, hz⟩ := hz
        obtain ⟨hkl, hkne, hksub⟩ := mem_blocks hkeep
        have hremovedKeep : ∃ r ∈ ρ.childPositions, r ∉ keep := by
          by_contra h
          push Not at h
          have hlen := ((childPositions_nodup ρ).subperm h).length_le
          omega
        have hremovedRest : ∃ r ∈ ρ.childPositions, r ∉ ρ.childPositions.filter (· ∉ keep) := by
          obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hkne
          exact ⟨r, hksub r hr, by simp [hr]⟩
        have hparts (ks : List ℕ) (v : Side) (m : ℕ) :
            boundFuel fuel (ρ.part ks v m) ≤ 1 := ih _ (hGoodPart ρ hgood ks v m)
        rcases hz with rfl | rfl
        · cases hs : s
          · have hz0 := hPartZero ρ hgood keep (d + 1) hremovedKeep fuel
            simp only [hs] at hz0
            rw [hz0, Nat.zero_add]
            exact hparts _ _ _
          · have hz0 := hPartZero ρ hgood (ρ.childPositions.filter (· ∉ keep))
              (ρ.k - 1 - (d + 1)) hremovedRest fuel
            simp only [hs] at hz0
            rw [hz0, Nat.add_zero]
            exact hparts _ _ _
        · cases hs : s
          · have hz0 := hPartZero ρ hgood (ρ.childPositions.filter (· ∉ keep))
              (d + 1) hremovedRest fuel
            simp only [hs] at hz0
            rw [hz0, Nat.add_zero]
            exact hparts _ _ _
          · have hz0 := hPartZero ρ hgood keep (ρ.k - 1 - (d + 1)) hremovedKeep fuel
            simp only [hs] at hz0
            rw [hz0, Nat.zero_add]
            exact hparts _ _ _
  refine ⟨hLocal σ hpositive N M x y hN hM hNs hMs hx hy hglobal, ?_⟩
  intro hbracket
  have hgood : Good σ := ⟨hpositive, hglobal, N, M, x, y, hN, hM, hNs, hMs, hx, hy, hbracket⟩
  exact ⟨fun fuel => hFuel fuel σ hgood, hFuel _ σ hgood⟩

end ErdosSzekeres
