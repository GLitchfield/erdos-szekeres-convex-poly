import ESBlueprint.B.CtxSingleLevelCompanionMaximumBound
import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A saturated linear bound for contexts with exactly one indexed history level, an actual chosen marker, chosen global at most four, opposite global at most k, and k at least four. Every fuel approximation and the full recursive bound are at most 2*k-4, for arbitrary child patterns, source maximum, repeated and unindexed positive markers. Each first cut is controlled by the complementary sibling-maximum charges, the active unit-zone bound, the two-level global bound and near-maximum normalization. Supplies the last one-unit saving in the normalized critical capacity-three interval/complement additivity case.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_single_level_saturated_linear_bound (σ : Ctx.Context)
  (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j)
  (hdepth : σ.maxima.length = 1)
  (s t : Ctx.Side) (hne : s ≠ t) (x : ℕ)
  (hside : σ.sideAt 1 = s) (hx : x ∈ σ.extPositions 1)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hk : 4 ≤ σ.k) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2 * σ.k - 4) ∧ σ.bound ≤ 2 * σ.k - 4 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let C (ρ : Context) (v : Side) (r : ℕ) := match v with
    | Side.lower => ρ.cupLimit r r | Side.upper => ρ.capLimit r r
  have hLevel : 1 ∈ σ.levels := by simp [levels, hdepth]
  have hOn : 1 ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hLevel, by simp [hside]⟩
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
  have hChosen (p : ℕ) (hp : p ∈ σ.childPositions) : C σ s p ≤ 2 := by
    have hxp : x ≠ p := by
      intro he
      subst x
      have hc := of_decide_eq_true (List.mem_filter.mp hp).2
      have he := (List.mem_filter.mp hx).2
      simp [hc] at he
    have hchain : 1 ≤ σ.leftExt s 0 p + σ.rightExt s 0 p := by
      rcases lt_or_gt_of_ne hxp with hl | hr
      · have hh := hOneLeft σ s 1 p x hOn hx hl
        omega
      · have hh := hOneRight σ s 1 p x hOn hx hr
        omega
    cases s <;> simp only [C, cupLimit, capLimit, chainExt] at hglobal hchain ⊢ <;> omega
  have hBase : σ.base ≤ 2 * σ.k - 4 := by
    rw [base_eq_baseOf]
    cases hh : σ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      change baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k ≤ 2 * σ.k - 4
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      have hchosen := hChosen p hp
      have hcupk : σ.cupLimit p p ≤ σ.k - 1 := by dsimp only [cupLimit]; omega
      have hcapk : σ.capLimit p p ≤ σ.k - 1 := by dsimp only [capLimit]; omega
      have hb : baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k ≤ C σ t p := by
        cases s <;> cases t
        · exact False.elim (hne rfl)
        · exact hBaseLower _ _ _ hchosen hcapk
        · exact hBaseUpper _ _ _ hchosen hcupk
        · exact False.elim (hne rfl)
      have ho : C σ t p ≤ G σ t - 1 := by
        cases t <;> simp only [C, G, cupLimit, capLimit] <;> omega
      change G σ t ≤ σ.k at hopposite
      omega
  have hCut (fuel : ℕ) (keep : List ℕ) (m n p q : ℕ)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m + n = σ.k - 1)
      (hp : p ∈ σ.childPositions) (hpk : p ∈ keep)
      (hq : q ∈ σ.childPositions) (hqk : q ∉ keep) :
      boundFuel fuel (σ.part keep s m) +
        boundFuel fuel (σ.part (σ.childPositions.filter (· ∉ keep)) t n) ≤ 2 * σ.k - 4 := by
    let rest := σ.childPositions.filter (· ∉ keep)
    let A := σ.part keep s m
    let B := σ.part rest t n
    have hpa : p ∈ A.childPositions := by simp [A, part_childPositions, hp, hpk]
    have hPosA := hPositivePart σ keep s m
    have hAlevel : 1 ∈ A.levels := by simp [A, part_levels]
    have hAmaximum : A.maximumAt 1 = m := part_maximumAt_one σ keep s m
    have hAx : q ∈ A.extPositions 1 := by
      simp [A, part_extPositions_one hpositive keep s m, hq, hqk]
    have hAside : A.sideAt 1 = s := part_sideAt_one_of_mem hpositive keep s m hAx
    have hAg : G A s ≤ 4 := by cases s <;> exact hglobal
    have hbudget : σ.k - n - 1 = m := by omega
    have hcomp := ctx_single_level_companion_maximum_bound σ hpositive hdepth s t hne x
      hside hx hglobal keep m n p q hpa hq hqk
    have hB : boundFuel fuel B ≤ 2 * m - 1 := by
      simpa only [hbudget] using hcomp.1 fuel
    by_cases hlarge : σ.k - 2 ≤ m
    · have hA := (ctx_bound_le_one_of_large_sibling_maximum A hPosA 1 hAlevel
        (by change σ.k - 2 ≤ A.maximumAt 1; rw [hAmaximum]; exact hlarge)).1 fuel
      change boundFuel fuel A + boundFuel fuel B ≤ 2 * σ.k - 4
      omega
    have hmle : m ≤ σ.k - 3 := by omega
    by_cases hunit : ∀ r ∈ A.childPositions, 0 < A.cupLimit r r → 0 < A.capLimit r r →
        C A s r ≤ 1
    · have hzones := ctx_active_unit_axis_three_zone_potential A hPosA s hAg hunit
      have hA : boundFuel fuel A ≤ 3 := (hzones.1 fuel).trans hzones.2.2.1
      change boundFuel fuel A + boundFuel fuel B ≤ 2 * σ.k - 4
      omega
    push Not at hunit
    obtain ⟨r, hr, hrcu, hrca, hrc⟩ := hunit
    have hnonunit : 2 ≤ C A s r := by omega
    have hsharp := ctx_single_level_companion_maximum_bound σ hpositive hdepth s t hne x
      hside hx hglobal keep m n r q hr hq hqk
    have hBsharp : boundFuel fuel B ≤ m := by
      simpa only [hbudget] using (hsharp.2.2 hnonunit).1 fuel
    by_cases hnear : σ.k - 3 ≤ m
    · let ν : Context := match s with
        | Side.lower => { A with u := min A.u (A.k - m), maxima := [] }
        | Side.upper => { A with a := min A.a (A.k - m), maxima := [] }
      have hνLetter (r : ℕ) : ν.letterAt r = A.letterAt r := by cases s <;> rfl
      have hνPos : ∀ r j v, ν.letterAt r = Letter.ext j v → 1 ≤ j := by
        intro r j v hj
        rw [hνLetter] at hj
        exact hPosA r j v hj
      have hνG : G ν s ≤ 3 := by
        cases s <;> simp only [G, ν]
        all_goals exact (Nat.min_le_right _ _).trans (show σ.k - m ≤ 3 by omega)
      have hνOpp : G ν t = G σ t := by
        cases s <;> cases t
        · exact False.elim (hne rfl)
        · rfl
        · rfl
        · exact False.elim (hne rfl)
      have hnorm := ctx_sibling_maximum_upper_normalize A 1 hAlevel
      have hAν : boundFuel fuel A ≤ boundFuel fuel ν := by
        cases s <;>
          simpa only [ν, hAside, hAmaximum, Nat.sub_self, List.take_zero] using hnorm.2.1 fuel
      have hsmall := ctx_small_global_axis_rank_region_potential ν hνPos s t hne hνG
      have hνbound : boundFuel fuel ν ≤ G ν t - 1 := by
        cases t <;> exact (hsmall.1 fuel).trans hsmall.2.2.1
      rw [hνOpp] at hνbound
      change G σ t ≤ σ.k at hopposite
      change boundFuel fuel A + boundFuel fuel B ≤ 2 * σ.k - 4
      omega
    have hAold : 2 ∈ A.levels := by
      rw [show A.levels = 1 :: σ.levels.map (· + 1) from part_levels σ keep s m]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨1, hLevel, rfl⟩)
    have hAoldSide : A.sideAt 2 = s :=
      (part_sideAt_succ σ keep s m (show 1 ≤ 1 by decide)).trans hside
    have hAoldX : x ∈ A.extPositions 2 := by
      rw [show A.extPositions 2 = σ.extPositions 1 from
        part_extPositions_succ σ keep s m (show 1 ≤ 1 by decide)]
      exact hx
    have htwo := ctx_two_level_unit_rank_potential_bound A hPosA s t hne 1 2 q x
      hAlevel hAold (by decide) hAside hAoldSide hAx hAoldX hAg
    have hA : boundFuel fuel A ≤ G σ t := htwo.2.2.1 fuel
    change G σ t ≤ σ.k at hopposite
    change boundFuel fuel A + boundFuel fuel B ≤ 2 * σ.k - 4
    omega
  have hFuel : ∀ fuel, boundFuel fuel σ ≤ 2 * σ.k - 4 := by
    intro fuel
    cases fuel with
    | zero => exact Nat.zero_le _
    | succ fuel =>
      rw [boundFuel]
      split
      · exact hBase
      · apply Ctx.getD_max?_le
        intro z hz
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hz
        obtain ⟨keep, hkeep, d, hd, hz⟩ := hz
        have hd' := List.mem_range.mp hd
        obtain ⟨hkl, hkne, hksub⟩ := mem_blocks hkeep
        obtain ⟨p, hpk⟩ := List.exists_mem_of_ne_nil _ hkne
        have hp : p ∈ σ.childPositions := hksub p hpk
        have hremoved : ∃ q ∈ σ.childPositions, q ∉ keep := by
          by_contra h
          push Not at h
          have hlen := ((childPositions_nodup σ).subperm h).length_le
          omega
        obtain ⟨q, hq, hqk⟩ := hremoved
        let rest := σ.childPositions.filter (· ∉ keep)
        have hforward (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a+b = σ.k-1) :
            boundFuel fuel (σ.part keep s a) + boundFuel fuel (σ.part rest t b) ≤ 2 * σ.k - 4 :=
          hCut fuel keep a b p q ha hb hab hp hpk hq hqk
        have hdouble (v : Side) (m : ℕ) :
            σ.part (σ.childPositions.filter (· ∉ rest)) v m = σ.part keep v m := by
          apply part_congr
          intro r hr
          simp only [rest, List.mem_filter, decide_eq_true_eq, hr, true_and, not_not]
        have hbackward (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a+b = σ.k-1) :
            boundFuel fuel (σ.part rest s a) + boundFuel fuel (σ.part keep t b) ≤ 2 * σ.k - 4 := by
          have hh := hCut fuel rest a b q p ha hb hab
            hq (by simp [rest, hq, hqk]) hp (by simp [rest, hpk])
          rw [hdouble] at hh
          exact hh
        have hboth (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a+b = σ.k-1) :
            (boundFuel fuel (σ.part keep Side.lower a) +
              boundFuel fuel (σ.part rest Side.upper b) ≤ 2 * σ.k - 4) ∧
            (boundFuel fuel (σ.part keep Side.upper b) +
              boundFuel fuel (σ.part rest Side.lower a) ≤ 2 * σ.k - 4) := by
          cases s <;> cases t
          · exact False.elim (hne rfl)
          · exact ⟨hforward a b ha hb hab,
              by simpa only [Nat.add_comm] using hbackward a b ha hb hab⟩
          · exact ⟨by simpa only [Nat.add_comm] using hbackward b a hb ha (by omega),
              hforward b a hb ha (by omega)⟩
          · exact False.elim (hne rfl)
        have hall := hboth (d+1) (σ.k-1-(d+1)) (by omega) (by omega) (by omega)
        rcases hz with rfl | rfl
        · exact hall.1
        · exact hall.2
  exact ⟨hFuel, hFuel _⟩

end ErdosSzekeres
