import ESBlueprint.B.CtxPartBoundRankPairEndReservations

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- For a positive-label context with an actual chosen marker and chosen global at most four, every proper chosen/opposite cut has sum of bounds at most twice the source active opposite-rank union size minus one. The kept list may interleave, the two new maxima are unrestricted, and the two fuel values are independent. Exposes the general local cut argument underlying the refined one-level bound and supplies the per-group estimate for a future arbitrary-cut rank-pair potential theorem.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_one_level_arbitrary_cut_rank_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ σ.childPositions) (hkeep : p ∈ keep)
  (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep) :
  let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active := σ.childPositions.toFinset.filter
    (fun r => 0 < σ.cupLimit r r ∧ 0 < σ.capLimit r r)
  let ranks := active.biUnion (fun r =>
    Finset.Icc (σ.leftExt t 0 r + 1) (global - 1 - σ.rightExt t 0 r))
  let own := σ.part keep s m
  let other := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  (∀ ownFuel otherFuel, Ctx.Context.boundFuel ownFuel own + Ctx.Context.boundFuel otherFuel other ≤
    2 * ranks.card - 1) ∧ own.bound + other.bound ≤ 2 * ranks.card - 1 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let C (ρ : Context) (v : Side) (r : ℕ) := match v with
    | Side.lower => ρ.cupLimit r r | Side.upper => ρ.capLimit r r
  let active (ρ : Context) : Finset ℕ := ρ.childPositions.toFinset.filter
    (fun r ↦ 0 < ρ.cupLimit r r ∧ 0 < ρ.capLimit r r)
  let marks (ρ : Context) : Finset ℕ :=
    (ρ.levelsOn s 0).toFinset.biUnion (fun j ↦ (ρ.extPositions j).toFinset)
  let label (M : Finset ℕ) (r : ℕ) : ℕ :=
    if (M.filter (· < r)).Nonempty then
      if (M.filter (r < ·)).Nonempty then 1 else 2
    else 0
  let units (ρ : Context) := (active ρ).filter (fun r ↦ C ρ s r ≤ 1)
  let colors (ρ : Context) := (units ρ).image (label (marks ρ))
  let I (ρ : Context) (v : Side) (p : ℕ) :=
    Finset.Icc (ρ.leftExt v 0 p + 1) (G ρ v - 1 - ρ.rightExt v 0 p)
  let F (ρ : Context) (e : ℕ) :=
    (active ρ).filter (fun p ↦ 2 ≤ C ρ s p ∧ label (marks ρ) p = e)
  let RN (ρ : Context) (e : ℕ) := (F ρ e).biUnion (I ρ t)
  let T (ρ : Context) := (colors ρ).card + (RN ρ 0).card + (RN ρ 2).card
  let Good (ρ : Context) : Prop := ∃ N x : ℕ,
    N ∈ ρ.levels ∧ ρ.sideAt N = s ∧ x ∈ ρ.extPositions N
  let S (ρ : Context) := (active ρ).biUnion (I ρ t)
  let Budget (ρ : Context) := 2 * (S ρ).card - 1
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by
    simp [active]
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
      word := (List.range ρ.word.length).map (fun p ↦ match ρ.letterAt p with
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
  let A := σ.part keep s m
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  change (∀ ownFuel otherFuel, boundFuel ownFuel A + boundFuel otherFuel B ≤ Budget σ) ∧
    A.bound + B.bound ≤ Budget σ
  have hAll (fuel : ℕ) (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hg : G ρ s ≤ 4) (hgood : Good ρ) : boundFuel fuel ρ ≤ Budget ρ := by
    obtain ⟨N, x, hN, hNs, hx⟩ := hgood
    exact ((ctx_one_level_refined_potential_bound ρ hPos s t hne N x hN hNs hx hg).1 fuel).trans
      (Nat.min_le_right _ _)
  have hSame (fuel : ℕ) : boundFuel fuel A + boundFuel fuel B ≤ Budget σ :=
    hCut fuel σ hpositive hglobal ⟨N, x, hN, hNs, hx⟩ (hAll fuel)
      keep m n p q hp hkeep hq hremoved
  have hBoth (f g : ℕ) : boundFuel f A + boundFuel g B ≤ Budget σ :=
    (Nat.add_le_add (boundFuel_mono (Nat.le_max_left f g) A)
      (boundFuel_mono (Nat.le_max_right f g) B)).trans (hSame (max f g))
  exact ⟨hBoth, hBoth _ _⟩

end ErdosSzekeres
