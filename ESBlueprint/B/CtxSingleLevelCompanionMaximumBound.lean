import ESBlueprint.B.CtxOldestAxisMaximumEraseNormalize
import ESBlueprint.B.CtxOneLevelRefinedPotentialBound
import ESBlueprint.B.CtxNonunitPartCompanionExteriorRankBound

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A sibling-maximum bound for the complementary opposite-axis part of a context with one actual indexed chosen level and chosen global at most four. With nonempty kept and removed child witnesses, every fuel approximation and the full complementary bound are at most twice k-n-1 minus one, where n is the new complementary sibling maximum. If the retained witness has chosen capacity at least two, the complementary bound sharpens to k-n-1. Maxima, child pattern, repeated and unindexed positive markers are arbitrary; no coupling or opposite-global assumption is needed. Oldest-axis normalization preserves the original chosen marker while absorbing the new opposite maximum; the nonunit companion exterior geometry supplies the sharper boundary estimate. Provides the two companion charges needed for the critical saturated capacity-three bound.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_single_level_companion_maximum_bound (σ : Ctx.Context)
  (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j)
  (hdepth : σ.maxima.length = 1)
  (s t : Ctx.Side) (hne : s ≠ t) (x : ℕ)
  (hside : σ.sideAt 1 = s) (hx : x ∈ σ.extPositions 1)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep) :
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  let budget := σ.k - n - 1
  (∀ fuel, Ctx.Context.boundFuel fuel B ≤ 2 * budget - 1) ∧
    B.bound ≤ 2 * budget - 1 ∧
    ((2 ≤ (match s with
      | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
      | Ctx.Side.upper => (σ.part keep s m).capLimit p p)) →
      (∀ fuel, Ctx.Context.boundFuel fuel B ≤ budget) ∧ B.bound ≤ budget) := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let rest := σ.childPositions.filter (· ∉ keep)
  let A := σ.part keep s m
  let B := σ.part rest t n
  let budget := σ.k - n - 1
  change (∀ fuel, boundFuel fuel B ≤ 2 * budget - 1) ∧ B.bound ≤ 2 * budget - 1 ∧
    (2 ≤ (match s with | Side.lower => A.cupLimit p p | Side.upper => A.capLimit p p) →
      (∀ fuel, boundFuel fuel B ≤ budget) ∧ B.bound ≤ budget)
  have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ x j w, (ρ.part keep v m).letterAt x = Letter.ext j w → 1 ≤ j := by
    intro x j w hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep v m)
        (show (ρ.part keep v m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep v m hxl he] at hx
      split at hx
      · cases hx
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep v m hxl he] at hx
      cases hx
      omega
  have hPosB := hPartPositive σ rest t n
  have hChild (ks : List ℕ) (v : Side) (c r : ℕ) :
      r ∈ (σ.part ks v c).childPositions ↔ r ∈ σ.childPositions ∧ r ∈ ks := by
    simp only [part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hpa := (hChild keep s m p).mp hp
  have hSourceLevels : σ.levels = [1] := by simp [levels, hdepth]
  have hSourceLevel : 1 ∈ σ.levels := by simp [hSourceLevels]
  have hSourceOn : 1 ∈ σ.levelsOn s 0 := by simp [levelsOn, hSourceLevels, hside]
  have hBdepth : B.maxima.length = 2 := by simp [B, part, hdepth]
  have hBlevels : B.levels = [1, 2] := by simp [B, part_levels, hSourceLevels]
  have hBlevel : 1 ∈ B.levels := by simp [hBlevels]
  have hBside : B.sideAt 1 = t := by
    apply part_sideAt_one_of_mem hpositive rest t n (q := p)
    rw [part_extPositions_one hpositive rest t n]
    exact List.mem_filter.mpr ⟨hpa.1, by simp [rest, hpa.2]⟩
  have hBoldSide : B.sideAt 2 = s := by
    exact (part_sideAt_succ σ rest t n (show 1 ≤ 1 by decide)).trans hside
  have hBoldExt : B.extPositions 2 = σ.extPositions 1 :=
    part_extPositions_succ σ rest t n (show 1 ≤ 1 by decide)
  have hterminal : ∀ j ∈ B.levelsOn (B.sideAt 1) 0, j ≤ 1 := by
    intro j hj
    have hmem : j = 1 ∨ j = 2 := by simpa [hBlevels] using (List.mem_filter.mp hj).1
    have hs : B.sideAt j = B.sideAt 1 :=
      (of_decide_eq_true (List.mem_filter.mp hj).2).1
    rcases hmem with rfl | rfl
    · exact le_rfl
    · rw [hBoldSide, hBside] at hs
      exact False.elim (hne hs)
  let f : Letter → Letter := fun z => match z with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext
        (if j = 1 then B.maxima.length else if 1 < j then j - 1 else j) v
  let E : Context := { B with word := B.word.map f, maxima := B.maxima.eraseIdx 0 }
  let ν : Context := match B.sideAt 1 with
    | Side.lower => { E with u := min B.u (B.k - B.maximumAt 1) }
    | Side.upper => { E with a := min B.a (B.k - B.maximumAt 1) }
  have hn := ctx_oldest_axis_maximum_erase_normalize B 1 hBlevel hterminal
  have hνChild : ν.childPositions = B.childPositions := hn.1
  have hνDepth : ν.maxima.length = 1 := by
    have hh := hn.2.1
    change ν.maxima.length = B.maxima.length - 1 at hh
    omega
  have hνLevel : 1 ∈ ν.levels := by simp [levels, hνDepth]
  have hνHistory : 2 ∈ B.levels ∧ 2 ≠ 1 ∧ ν.extPositions 1 = B.extPositions 2 ∧
      ν.sideAt 1 = B.sideAt 2 ∧ ν.maximumAt 1 = B.maximumAt 2 := hn.2.2.1 1 hνLevel
  have hνSide : ν.sideAt 1 = s := hνHistory.2.2.2.1.trans hBoldSide
  have hνExt : ν.extPositions 1 = σ.extPositions 1 := hνHistory.2.2.1.trans hBoldExt
  have hxν : x ∈ ν.extPositions 1 := by rw [hνExt]; exact hx
  have hνFuel : ∀ fuel, boundFuel fuel B ≤ boundFuel fuel ν := hn.2.2.2.2.1
  have hνBound : B.bound ≤ ν.bound := hn.2.2.2.2.2
  have hνWord : ν.word = B.word.map f := by cases hs : B.sideAt 1 <;> simp [ν, hs, E]
  have hνLetter (r : ℕ) : ν.letterAt r = f (B.letterAt r) := by
    simp only [letterAt, hνWord, List.getElem?_map]
    cases B.word[r]? <;> rfl
  have hνPos : ∀ r j v, ν.letterAt r = Letter.ext j v → 1 ≤ j := by
    intro r j v hj
    rw [hνLetter] at hj
    cases he : B.letterAt r with
    | child =>
      simp only [he, f] at hj
      cases hj
    | ext i z =>
      rw [he] at hj
      have hi := hPosB r i z he
      have hnew : 1 ≤ (if i = 1 then B.maxima.length else if 1 < i then i - 1 else i) := by
        rw [hBdepth]
        split_ifs <;> omega
      change Letter.ext (if i = 1 then B.maxima.length else if 1 < i then i - 1 else i) z =
        Letter.ext j v at hj
      cases hj
      exact hnew
  have hνChosen : G ν s = G σ s := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · simp only [G, ν, hBside]
      rfl
    · simp only [G, ν, hBside]
      rfl
    · exact False.elim (hne rfl)
  have hνGlobal : G ν s ≤ 4 := by rw [hνChosen]; exact hglobal
  have hBmaximum : B.maximumAt 1 = n := part_maximumAt_one σ rest t n
  have hνOpposite : G ν t ≤ σ.k - n := by
    cases t <;> simp only [G, ν, hBside, hBmaximum]
    all_goals exact Nat.min_le_right _ _
  have hbudget : G ν t - 1 ≤ budget := by dsimp [budget]; omega
  have hdouble : 2 * (G ν t - 1) - 1 ≤ 2 * budget - 1 := by omega
  have hνRefined := ctx_one_level_refined_potential_bound ν hνPos s t hne 1 x
    hνLevel hνSide hxν hνGlobal
  have hνAll : ∀ fuel, boundFuel fuel ν ≤ 2 * (G ν t - 1) - 1 := hνRefined.2.2.1
  have hνFull : ν.bound ≤ 2 * (G ν t - 1) - 1 := hνRefined.2.2.2
  refine ⟨fun fuel => (hνFuel fuel).trans ((hνAll fuel).trans hdouble),
    hνBound.trans (hνFull.trans hdouble), ?_⟩
  intro hnonunit
  have hgeom := ctx_nonunit_part_companion_exterior_rank_bound σ hpositive s t hne 1 x
    hSourceLevel hside hx hglobal keep m n p q hp hnonunit hq hremoved
  obtain ⟨dir, _, hremovedSide⟩ := hgeom.1
  have hchildren : ∀ r ∈ ν.childPositions, if dir then r < x else x < r := by
    intro r hr
    rw [hνChild] at hr
    have hh := (hChild rest t n r).mp hr
    have hrnot : r ∉ keep := of_decide_eq_true (List.mem_filter.mp hh.2).2
    exact hremovedSide r hh.1 hrnot 1 hSourceOn x hx
  have hyounger : ∀ j ∈ ν.levelsOn (ν.sideAt 1) 1, ∀ r ∈ ν.extPositions j,
      if dir then r < x else x < r := by
    intro j hj r _
    have hj1 := (one_le_of_mem_levelsOn hj).1
    have hjlt := (of_decide_eq_true (List.mem_filter.mp hj).2).2
    omega
  have hsmall : min ((match ν.sideAt 1 with
      | Side.lower => ν.u | Side.upper => ν.a) - 1) (ν.k - ν.maximumAt 1) ≤ 3 := by
    rw [hνSide]
    change min (G ν s - 1) (ν.k - ν.maximumAt 1) ≤ 3
    omega
  have hb := ctx_boundary_marker_rank_budget_all_history ν hνPos 1 x hνLevel hxν dir
    hchildren hyounger t (by rw [hνSide]; exact hne) hsmall 0 0
    (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _)
  have hbAll : ∀ fuel, boundFuel fuel ν ≤ G ν t - 1 := by
    simpa only [Nat.sub_zero] using hb.1
  have hbFull : ν.bound ≤ G ν t - 1 := by simpa only [Nat.sub_zero] using hb.2
  exact ⟨fun fuel => (hνFuel fuel).trans ((hbAll fuel).trans hbudget),
    hνBound.trans (hbFull.trans hbudget)⟩

end ErdosSzekeres
