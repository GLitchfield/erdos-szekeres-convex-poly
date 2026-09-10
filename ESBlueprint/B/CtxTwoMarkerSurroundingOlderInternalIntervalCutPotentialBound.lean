import ESBlueprint.B.CtxTwoMarkerSurroundingYoungestInternalIntervalCutPotentialBound
import ESBlueprint.B.CtxTwoMarkerNonunitBracketedPartCutPotentialBound
import ESBlueprint.B.CtxActiveBoundaryMarkerRankPairUnionBound
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsCapacityThree
import ESBlueprint.B.CtxMixedAxisClearUnitCoverPotential
import ESBlueprint.B.CtxOneLevelRefinedPotentialBound
import ESBlueprint.B.CtxBoundaryMarkerRankBudget
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Combine nonunit bracketed-part geometry with a two-zone all-unit chosen charge. Normalize the older-boundary opposite arm to a retained-marker doubled rank budget; the other arm has the younger-boundary triangular charge. The sum satisfies P(w) without a recursive premise. Positive external labels, chosen global at most five and opposite width w at least two. Two distinct actual chosen marker positions at levels N<M; all actual chosen positions are one of these. The chosen kept set is a convex child interval straddling the older marker and bracketed by complementary child witnesses on both ends. Arbitrary opposite history, original and new maxima and inactive children are allowed; no recursive potential premise.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_surrounding_older_internal_interval_cut_potential_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y)
  (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
  (keep : List ℕ) (a b l r m n : ℕ)
  (ha : a ∈ keep) (hb : b ∈ keep)
  (hsurround : a < y ∧ y < b)
  (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
  (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
  (hlnot : l ∉ keep) (hrnot : r ∉ keep)
  (hinside : ∀ p ∈ keep, l < p ∧ p < r)
  (hconvex : ∀ p ∈ keep, ∀ q ∈ keep, ∀ z ∈ σ.childPositions,
    p ≤ z → z ≤ q → z ∈ keep) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) +
    Ctx.Context.boundFuel g (σ.part rest t n) ≤ (w + 1).choose 2 + w - 1) ∧
    (σ.part keep s m).bound + (σ.part rest t n).bound ≤ (w + 1).choose 2 + w - 1 := by
  classical
  have ctx_boundary_retained_doubled_rank_budget (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (N J x y : ℕ) (hN : N ∈ σ.levels) (hJ : J ∈ σ.levels) (hJN : J < N)
    (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions J)
    (hside : σ.sideAt J = σ.sideAt N)
    (outer : Bool)
    (hOuter : ∀ p ∈ σ.childPositions, if outer then p < x else x < p)
    (hOuterYoung : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
      if outer then p < x else x < p)
    (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
    (hglobal : (match (generalizing := false) σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (A B : ℕ)
    (hLeft : ∀ p ∈ σ.childPositions, A ≤ σ.leftExt t N p)
    (hRight : ∀ p ∈ σ.childPositions, B ≤ σ.rightExt t N p) :
    let budget := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - A - B
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2 * budget - 1) ∧ σ.bound ≤ 2 * budget - 1 := by
    classical
    let τ : Context := match (generalizing := false) σ.sideAt N with
      | Side.lower => { σ with u := min (σ.u - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
      | Side.upper => { σ with a := min (σ.a - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
    let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
    change (∀ fuel, boundFuel fuel σ ≤ 2 * (w - A - B) - 1) ∧ σ.bound ≤ 2 * (w - A - B) - 1
    have hNorm := ctx_boundary_marker_upper_normalize σ hpositive N x hN hx outer hOuter hOuterYoung
    have hFuel : ∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ := hNorm.2.1
    have hFull : σ.bound ≤ τ.bound := hNorm.2.2
    have hWord : τ.word = σ.word := by cases hs : σ.sideAt N <;> simp only [τ, hs]
    have hMaxima : τ.maxima = σ.maxima.take (N - 1) := by cases hs : σ.sideAt N <;> simp only [τ, hs]
    have hLetter (p : ℕ) : τ.letterAt p = σ.letterAt p := by simp only [letterAt, hWord]
    have hChild : τ.childPositions = σ.childPositions := by simp only [childPositions, hWord, hLetter]
    have hExt (j : ℕ) : τ.extPositions j = σ.extPositions j := by simp only [extPositions, hWord, hLetter]
    have hSide (j : ℕ) : τ.sideAt j = σ.sideAt j := by simp only [sideAt, hExt, hLetter]
    have hPositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
      intro p j v hp
      rw [hLetter] at hp
      exact hpositive p j v hp
    have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
      simp only [levels, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        omega
      · intro hj
        exact ⟨j - 1, by omega, by omega⟩
    have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
      unfold levels
      exact List.pairwise_lt_range.map (fun x => x + 1) (fun a b hab => Nat.add_lt_add_right hab 1)
    have hLevels : τ.levels = σ.levels.filter (· < N) := by
      apply (hSorted τ).eq_of_mem_iff ((hSorted σ).filter _)
      intro j
      simp only [List.mem_filter, hLevelMem, hMaxima, List.length_take, decide_eq_true_eq]
      omega
    have hLevelsOn (v : Side) (top : ℕ) : τ.levelsOn v top = (σ.levelsOn v top).filter (· < N) := by
      simp only [levelsOn, hLevels, hSide, List.filter_filter]
      apply List.filter_congr
      intro j _
      simp only [Bool.and_comm]
    have hNpos := one_le_of_mem_levels hN
    have hJτ : J ∈ τ.levels := by
      rw [hLevels]
      exact List.mem_filter.mpr ⟨hJ, by simp [hJN]⟩
    have hBelow (v : Side) : τ.levelsOn v 0 = σ.levelsOn v N := by
      rw [hLevelsOn]
      simp only [levelsOn, List.filter_filter]
      apply List.filter_congr
      intro j hj
      by_cases hv : σ.sideAt j = v <;> by_cases hjN : j < N <;>
        simp [hv, hjN, show N ≠ 0 by omega]
    have hLeftStep : leftStep τ = leftStep σ := by
      funext z j
      simp only [leftStep, hExt]
    have hRightStep : rightStep τ = rightStep σ := by
      funext z j
      simp only [rightStep, hExt]
    have hLeftEq (p : ℕ) : τ.leftExt t 0 p = σ.leftExt t N p := by
      simp only [leftExt_eq, hLeftStep, hBelow]
    have hRightEq (p : ℕ) : τ.rightExt t 0 p = σ.rightExt t N p := by
      simp only [rightExt_eq, hRightStep, hBelow]
    have hChosen : (match (generalizing := false) τ.sideAt J with
        | Side.lower => τ.u | Side.upper => τ.a) ≤ 4 := by
      rw [hSide, hside]
      cases hs : σ.sideAt N
      · simp only [τ, hs] at hglobal ⊢
        exact (Nat.min_le_left (σ.u - 1) (σ.k - σ.maximumAt N)).trans (by omega)
      · simp only [τ, hs] at hglobal ⊢
        exact (Nat.min_le_left (σ.a - 1) (σ.k - σ.maximumAt N)).trans (by omega)
    let budget := (match (generalizing := false) t with | Side.lower => τ.u | Side.upper => τ.a) - 1
    have hBudget : budget = w := by
      dsimp only [budget, τ, w]
      cases hs : σ.sideAt N <;> cases ht : t <;> simp_all only [ne_eq, not_true_eq_false]
    let active := τ.childPositions.toFinset.filter
      (fun p ↦ 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p)
    let I (p : ℕ) := Finset.Icc (τ.leftExt t 0 p + 1) (budget - τ.rightExt t 0 p)
    let ranks := active.biUnion I
    have hh := ctx_one_level_refined_potential_bound τ hPositive (τ.sideAt J) t
      (by rw [hSide, hside]; exact hne) J y hJτ rfl (by rw [hExt]; exact hy) hChosen
    have hRf : ∀ fuel, boundFuel fuel τ ≤ 2 * ranks.card - 1 := by
      intro fuel
      exact (hh.1 fuel).trans (Nat.min_le_right _ _)
    have hRb : τ.bound ≤ 2 * ranks.card - 1 := hh.2.1.trans (Nat.min_le_right _ _)
    have hsub : ranks ⊆ Finset.Icc (A + 1) (w - B) := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hc : p ∈ σ.childPositions := by
        rw [← hChild]
        exact List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
      have hL : A ≤ τ.leftExt t 0 p := by rw [hLeftEq]; exact hLeft p hc
      have hR : B ≤ τ.rightExt t 0 p := by rw [hRightEq]; exact hRight p hc
      have hz' : τ.leftExt t 0 p + 1 ≤ z ∧ z ≤ budget - τ.rightExt t 0 p :=
        Finset.mem_Icc.mp hz
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hc : ranks.card ≤ w - A - B := by
      have hh := Finset.card_le_card hsub
      rw [Nat.card_Icc] at hh
      omega
    have hFinal : 2 * ranks.card - 1 ≤ 2 * (w - A - B) - 1 := by omega
    exact ⟨fun fuel ↦ (hFuel fuel).trans ((hRf fuel).trans hFinal),
      hFull.trans (hRb.trans hFinal)⟩

  by_cases hNon : ∃ p ∈ keep, 2 ≤ (match (generalizing := false) s with
      | Side.lower => (σ.part keep s m).cupLimit p p
      | Side.upper => (σ.part keep s m).capLimit p p)
  · obtain ⟨p, hp, hcap⟩ := hNon
    exact ctx_two_marker_nonunit_bracketed_part_cut_potential_bound σ hpositive s t hne
      N M x y hN hM hNM hNs hMs hx hy hglobal hchosen (Nat.le_trans (by decide : 1 ≤ 2) hwidth)
      keep p l r m n hp hkeep hl hr hlnot hrnot hinside hcap
  by_cases hYoung : ∃ c ∈ keep, ∃ d ∈ keep, c < x ∧ x < d
  · obtain ⟨c, hc, d, hd, hcd⟩ := hYoung
    exact ctx_two_marker_surrounding_youngest_internal_interval_cut_potential_bound σ hpositive
      s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hchosen (Nat.le_trans (by decide : 1 ≤ 2) hwidth)
      keep c d l r m n hc hd hcd hkeep hl hr hlnot hrnot hinside hconvex
  let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part keep s m
  let β := σ.part rest t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ (w + 1).choose 2 + w - 1) ∧
    α.bound + β.bound ≤ (w + 1).choose 2 + w - 1
  have hw : 2 ≤ w := hwidth
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [α, part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hChildβ (p : ℕ) : p ∈ β.childPositions ↔ p ∈ rest := by
    simp only [β, part_childPositions, rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔ p ∈ rest := by
    rw [part_extPositions_one hpositive]
  have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hLα : l ∈ α.extPositions 1 := (hExtα l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
  have hRα : r ∈ α.extPositions 1 := (hExtα r).mpr ((hRest r).mpr ⟨hr, hrnot⟩)
  have hAβ : a ∈ β.extPositions 1 := (hExtβ a).mpr ⟨hkeep a ha, ha⟩
  have hBβ : b ∈ β.extPositions 1 := (hExtβ b).mpr ⟨hkeep b hb, hb⟩
  have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive keep s m hLα
  have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive rest t n hAβ
  have hPosPart (ks : List ℕ) (v : Side) (q : ℕ) :
      ∀ p j z, (σ.part ks v q).letterAt p = Letter.ext j z → 1 ≤ j := by
    intro p j z hp
    have hpl : p < σ.word.length := by
      by_contra h
      have hh := letterAt_of_length_le (σ.part ks v q)
        (show (σ.part ks v q).word.length ≤ p by rw [part_word_length]; omega)
      rw [hh] at hp
      cases hp
    cases he : σ.letterAt p with
    | child =>
      rw [part_letterAt_of_child σ ks v q hpl he] at hp
      split at hp
      · cases hp
      · cases hp; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ ks v q hpl he] at hp
      cases hp; omega
  have hPosα := hPosPart keep s m
  have hPosβ := hPosPart rest t n
  have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
  have hOneβ : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
  have hChildNe (ρ : Context) (p j z : ℕ) (hp : p ∈ ρ.childPositions)
      (hz : z ∈ ρ.extPositions j) : p ≠ z := by
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hz).2
    intro h
    subst z
    simp [hc] at he
  have hAvoidX : (∀ p ∈ keep, p < x) ∨ (∀ p ∈ keep, x < p) := by
    by_cases hax : a < x
    · left
      intro p hp
      have hpne := hChildNe σ p N x (hkeep p hp) hx
      by_contra hn
      exact hYoung ⟨a, ha, p, hp, hax, by omega⟩
    · right
      have hane := hChildNe σ a N x (hkeep a ha) hx
      have hxa : x < a := by omega
      intro p hp
      have hpne := hChildNe σ p N x (hkeep p hp) hx
      by_contra hn
      exact hYoung ⟨p, hp, a, ha, by omega, hxa⟩
  have hMarkα (j z : ℕ) (hj : j ∈ α.levelsOn s 0)
      (hz : z ∈ α.extPositions j) : z ∈ rest ∨ z = x ∨ z = y := by
    have hjl := (List.mem_filter.mp hj).1
    have hjs : α.sideAt j = s := (of_decide_eq_true (List.mem_filter.mp hj).2).1
    rw [part_levels] at hjl
    rcases List.mem_cons.mp hjl with rfl | hjold
    · exact Or.inl ((hExtα z).mp hz)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hjold
      have hipos := one_le_of_mem_levels hi
      have hs : σ.sideAt i = s := (part_sideAt_succ σ keep s m hipos).symm.trans hjs
      rw [part_extPositions_succ σ keep s m hipos] at hz
      exact Or.inr (hchosen i (List.mem_filter.mpr ⟨hi, by simp [hs]⟩) z hz)
  have hUnit : ∀ p ∈ α.childPositions, (match (generalizing := false) s with
      | Side.lower => α.cupLimit p p | Side.upper => α.capLimit p p) ≤ 1 := by
    intro p hp
    have hk := ((hChildα p).mp hp).2
    have hn : ¬2 ≤ (match (generalizing := false) s with
        | Side.lower => α.cupLimit p p | Side.upper => α.capLimit p p) := by
      intro h
      exact hNon ⟨p, hk, h⟩
    omega
  let unitColor (p : ℕ) := if p < y then (0 : ℕ) else 1
  have hOwn : (∀ fuel, boundFuel fuel α ≤ 2) ∧ α.bound ≤ 2 := by
    have hClear : ∀ p ∈ α.childPositions, ∀ q ∈ α.childPositions,
        unitColor p = unitColor q → ∀ j ∈ α.levelsOn s 0, ∀ z ∈ α.extPositions j,
        z < min p q ∨ max p q < z := by
      intro p hp q hq he j hj z hz
      have hpk := ((hChildα p).mp hp).2
      have hqk := ((hChildα q).mp hq).2
      rcases hMarkα j z hj hz with hr | hzx | hzy
      · have hh := (hRest z).mp hr
        by_contra hn
        apply hh.2
        by_cases hpq : p ≤ q
        · exact hconvex p hpk q hqk z hh.1 (by omega) (by omega)
        · exact hconvex q hqk p hpk z hh.1 (by omega) (by omega)
      · subst z
        rcases hAvoidX with hL | hR
        · have h1 := hL p hpk
          have h2 := hL q hqk
          right
          omega
        · have h1 := hR p hpk
          have h2 := hR q hqk
          left
          omega
      · subst z
        have hpne := hChildNe σ p M y (hkeep p hpk) hy
        have hqne := hChildNe σ q M y (hkeep q hqk) hy
        dsimp only [unitColor] at he
        split_ifs at he <;> omega
    have hh := ctx_mixed_axis_clear_unit_cover_potential α hPosα unitColor (fun _ ↦ s)
      (fun p hp _ _ ↦ hUnit p hp)
      (fun p hp q hq _ _ _ _ he j hj z hz ↦ hClear p hp q hq he j hj z hz)
    let active := α.childPositions.toFinset.filter
      (fun p ↦ 0 < α.cupLimit p p ∧ 0 < α.capLimit p p)
    have hsub : active.image unitColor ⊆ ({0, 1} : Finset ℕ) := by
      intro c hc
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
      dsimp only [unitColor]
      split_ifs <;> simp
    have hc : (active.image unitColor).card ≤ 2 := by
      have h := Finset.card_le_card hsub
      simpa using h
    exact ⟨fun f ↦ (hh.1 f).trans hc, hh.2.1.trans hc⟩
  have hNpos := one_le_of_mem_levels hN
  have hMpos := one_le_of_mem_levels hM
  have hNβ : N + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hMβ : M + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hNsβ : β.sideAt (N + 1) = s := (part_sideAt_succ σ rest t n hNpos).trans hNs
  have hMsβ : β.sideAt (M + 1) = s := (part_sideAt_succ σ rest t n hMpos).trans hMs
  have hXβ : x ∈ β.extPositions (N + 1) := by
    rw [part_extPositions_succ σ rest t n hNpos]; exact hx
  have hYβ : y ∈ β.extPositions (M + 1) := by
    rw [part_extPositions_succ σ rest t n hMpos]; exact hy
  have hAtLevel (j i p : ℕ) (hp : p ∈ σ.extPositions j)
      (hp' : p ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hp).2
    have hi := (List.mem_filter.mp hp').2
    cases he : σ.letterAt p <;> simp [he] at hj hi
    omega
  have hActual : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j,
      (j = N ∧ p = x) ∨ (j = M ∧ p = y) := by
    intro j hj p hp
    rcases hchosen j hj p hp with hpx | hpy
    · exact Or.inl ⟨hAtLevel j N x (by simpa only [hpx] using hp) hx, hpx⟩
    · exact Or.inr ⟨hAtLevel j M y (by simpa only [hpy] using hp) hy, hpy⟩
  have hActualβ : ∀ j ∈ β.levelsOn s 0, ∀ p ∈ β.extPositions j,
      (j = N + 1 ∧ p = x) ∨ (j = M + 1 ∧ p = y) := by
    have hs : β.sideAt 1 ≠ s := by rw [hSideβ]; exact Ne.symm hne
    intro j hj p hp
    rw [part_levelsOn_other_zero hs] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [part_extPositions_succ σ rest t n
      (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
    rcases hActual i hi p hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hBelow (top j : ℕ) (hj : j ∈ β.levelsOn s top) :
      j ∈ β.levelsOn s 0 ∧ (top = 0 ∨ j < top) := by
    have hh := List.mem_filter.mp hj
    have hp := of_decide_eq_true hh.2
    exact ⟨List.mem_filter.mpr ⟨hh.1, by simp [hp.1]⟩, hp.2⟩
  have hOutside (p : ℕ) (hp : p ∈ β.childPositions) : p < a ∨ b < p := by
    have hh := (hRest p).mp ((hChildβ p).mp hp)
    by_contra hn
    exact hh.2 (hconvex a ha b hb p hh.1 (by omega) (by omega))
  have hNoX (p : ℕ) (hp : p ∈ β.childPositions) : p ≠ x :=
    hChildNe β p (N + 1) x hp hXβ
  have hNoY (p : ℕ) (hp : p ∈ β.childPositions) : p ≠ y :=
    hChildNe β p (M + 1) y hp hYβ
  have hOneLeft (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls ↦ (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (top j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v top) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v top p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v top).sublists.map
      (fun ls ↦ (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v top p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  let color (p : ℕ) := if p < y then (0 : ℕ) else 1
  let support (c : ℕ) := β.childPositions.filter (fun p ↦ color p = c)
  let group (c : ℕ) : Context := { β with
    word := (List.range β.word.length).map (fun p ↦ match β.letterAt p with
      | Letter.child => if p ∈ support c then Letter.child
          else Letter.ext (β.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  have hSmall : ∀ p ∈ β.childPositions, min (β.cupLimit p p) (β.capLimit p p) ≤ 3 := by
    intro p hp
    have hOn : N + 1 ∈ β.levelsOn s 0 := List.mem_filter.mpr ⟨hNβ, by simp [hNsβ]⟩
    by_cases hh : p < x
    · have he := hOneRight β s 0 (N + 1) p x hOn hXβ hh
      cases s <;> simp only [β, part, cupLimit, capLimit, chainExt] at hglobal he ⊢ <;> omega
    · have he := hOneLeft β s 0 (N + 1) p x hOn hXβ (by have := hNoX p hp; omega)
      cases s <;> simp only [β, part, cupLimit, capLimit, chainExt] at hglobal he ⊢ <;> omega
  have hCover : ∀ p ∈ β.childPositions, color p ∈ ({0, 1} : Finset ℕ) := by
    intro p hp
    dsimp only [color]
    split_ifs <;> simp
  have hColor : ∀ p ∈ β.childPositions, ∀ q ∈ β.childPositions, p ≤ q →
      (∀ z, p ≤ z → z ≤ q → z ∈ β.childPositions) → color p = color q := by
    intro p hp q hq hpq hbetween
    have hside : (p < y) = (q < y) := by
      apply propext
      constructor
      · intro hpx
        by_contra hqx
        exact hNoY y (hbetween y (by omega) (by omega)) rfl
      · omega
    simp only [color, hside]
  have hPos (c : ℕ) : ∀ p j v, (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
    (ctx_part_pruning_history_transport β hPosβ (support c) Side.lower 0).1
  have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔
      p ∈ β.childPositions ∧ color p = c := by
    have hh : (group c).childPositions = β.childPositions.filter (· ∈ support c) :=
      (ctx_part_pruning_history_transport β hPosβ (support c) Side.lower 0).2.1
    rw [hh]
    simp [support]
  have hHist (c j : ℕ) (hj : j ∈ β.levels) :
      (group c).extPositions j = β.extPositions j ∧ (group c).sideAt j = β.sideAt j :=
    (ctx_part_pruning_history_transport β hPosβ (support c) Side.lower 0).2.2.1 j hj
  have hLevels (c : ℕ) (v : Side) (top : ℕ) :
      (group c).levelsOn v top = β.levelsOn v top :=
    (ctx_part_pruning_history_transport β hPosβ (support c) Side.lower 0).2.2.2.1 v top
  have hSideN (c : ℕ) : (group c).sideAt (N + 1) = s := (hHist c _ hNβ).2.trans hNsβ
  have hSideM (c : ℕ) : (group c).sideAt (M + 1) = s := (hHist c _ hMβ).2.trans hMsβ
  have hX (c : ℕ) : x ∈ (group c).extPositions (N + 1) := by
    rw [(hHist c _ hNβ).1]; exact hXβ
  have hY (c : ℕ) : y ∈ (group c).extPositions (M + 1) := by
    rw [(hHist c _ hMβ).1]; exact hYβ
  have hLeft (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < y := by
    have hc := ((hChild 0 p).mp hp).2
    have ho := hOutside p ((hChild 0 p).mp hp).1
    dsimp only [color] at hc
    split_ifs at hc <;> omega
  have hRight (p : ℕ) (hp : p ∈ (group 1).childPositions) : y < p := by
    have hc := ((hChild 1 p).mp hp).2
    have ho := hOutside p ((hChild 1 p).mp hp).1
    dsimp only [color] at hc
    split_ifs at hc <;> omega
  have hYoung (c j : ℕ) (hj : j ∈ (group c).levelsOn s (N + 1))
      (p : ℕ) (hp : p ∈ (group c).extPositions j) : False := by
    rw [hLevels] at hj
    have hj' := hBelow (N + 1) j hj
    rw [(hHist c j (List.mem_filter.mp hj).1).1] at hp
    rcases hActualβ j hj'.1 p hp with ⟨h1, _⟩ | ⟨h2, _⟩ <;> omega
  have hOlder (c j : ℕ) (hj : j ∈ (group c).levelsOn s (M + 1))
      (p : ℕ) (hp : p ∈ (group c).extPositions j) : p = x := by
    rw [hLevels] at hj
    have hj' := hBelow (M + 1) j hj
    rw [(hHist c j (List.mem_filter.mp hj).1).1] at hp
    rcases hActualβ j hj'.1 p hp with ⟨_, hpx⟩ | ⟨hjM, _⟩
    · exact hpx
    · omega
  have hLeftLoss (p : ℕ) (hp : p ∈ (group 1).childPositions) :
      1 ≤ (group 1).leftExt t 0 p := by
    apply hOneLeft (group 1) t 0 1 p a
    · rw [hLevels]; exact List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ]⟩
    · rw [(hHist 1 1 hOneβ).1]; exact hAβ
    · have hh := hRight p hp; omega
  have hRightLoss (p : ℕ) (hp : p ∈ (group 0).childPositions) :
      1 ≤ (group 0).rightExt t 0 p := by
    apply hOneRight (group 0) t 0 1 p b
    · rw [hLevels]; exact List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ]⟩
    · rw [(hHist 0 1 hOneβ).1]; exact hBβ
    · have hh := hLeft p hp; omega
  have hLeftLossOlder (p : ℕ) (hp : p ∈ (group 1).childPositions) :
      1 ≤ (group 1).leftExt t (M + 1) p := by
    apply hOneLeft (group 1) t (M + 1) 1 p a
    · rw [hLevels]; exact List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ]; omega⟩
    · rw [(hHist 1 1 hOneβ).1]; exact hAβ
    · have hh := hRight p hp; omega
  have hRightLossOlder (p : ℕ) (hp : p ∈ (group 0).childPositions) :
      1 ≤ (group 0).rightExt t (M + 1) p := by
    apply hOneRight (group 0) t (M + 1) 1 p b
    · rw [hLevels]; exact List.mem_filter.mpr ⟨hOneβ, by simp [hSideβ]; omega⟩
    · rw [(hHist 0 1 hOneβ).1]; exact hBβ
    · have hh := hLeft p hp; omega
  have hPairBound (ρ : Context)
      (hPosρ : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (J z : ℕ) (hJ : J ∈ ρ.levels) (hJs : ρ.sideAt J = s)
      (hz : z ∈ ρ.extPositions J) (direction : Bool)
      (hChildren : ∀ p ∈ ρ.childPositions, if direction then p < z else z < p)
      (hYounger : ∀ j ∈ ρ.levelsOn s J, ∀ p ∈ ρ.extPositions j,
        if direction then p < z else z < p)
      (hG : (match (generalizing := false) s with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 5)
      (hW : (match (generalizing := false) t with | Side.lower => ρ.u | Side.upper => ρ.a) - 1 = w)
      (A B : ℕ) (hAB : A + B = 1)
      (hL : ∀ p ∈ ρ.childPositions, A ≤ ρ.leftExt t 0 p)
      (hR : ∀ p ∈ ρ.childPositions, B ≤ ρ.rightExt t 0 p) : ρ.bound ≤ w.choose 2 := by
    let active := ρ.childPositions.toFinset.filter
      (fun p ↦ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    let I (p : ℕ) := Finset.Icc (ρ.leftExt t 0 p + 1) (w - ρ.rightExt t 0 p)
    let Q (S : Finset ℕ) := (S.product S).filter (fun z ↦ z.1 ≤ z.2)
    let pairs := active.biUnion (fun p ↦ Q (I p))
    have hCardPairs (T : Finset ℕ) : (Q T).card = (T.card + 1).choose 2 := by
      rw [← Finset.card_sym2]
      apply Finset.card_bij (fun z _ ↦ Sym2.mk z.1 z.2)
      · intro z hz
        exact Finset.mk_mem_sym2_iff.mpr (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
      · intro p hp q hq he
        have hpl := (Finset.mem_filter.mp hp).2
        have hql := (Finset.mem_filter.mp hq).2
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext h1 h2
        · apply Prod.ext <;> omega
      · intro z hz
        induction z using Sym2.ind with
        | h a b =>
          obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hz
          by_cases hab : a ≤ b
          · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
          · exact ⟨(b, a), Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩, Sym2.eq_swap⟩
    have hSmallG : min ((match (generalizing := false) ρ.sideAt J with
        | Side.lower => ρ.u | Side.upper => ρ.a) - 1) (ρ.k - ρ.maximumAt J) ≤ 4 := by
      rw [hJs]
      apply (Nat.min_le_left _ _).trans
      omega
    have hh := ctx_active_boundary_marker_rank_pair_union_bound ρ hPosρ J z hJ hz
      direction (fun p hp _ ↦ hChildren p hp) (by rw [hJs]; exact hYounger)
      t (by rw [hJs]; exact hne) hSmallG
    have hPairFull : ρ.bound ≤ pairs.card := by
      cases t <;> simpa only [pairs, active, Q, I, hW] using hh.2
    have hsub : pairs ⊆ Q (Finset.Icc (A + 1) (w - B)) := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hc := List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
      have hL' := hL p hc
      have hR' := hR p hc
      have hz' := Finset.mem_filter.mp hz
      obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hz'.1
      have hza' := Finset.mem_Icc.mp hza
      have hzb' := Finset.mem_Icc.mp hzb
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
         Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, hz'.2⟩
    have hi : (Finset.Icc (A + 1) (w - B)).card = w - 1 := by
      rw [Nat.card_Icc]
      omega
    have hc : (Q (Finset.Icc (A + 1) (w - B))).card = w.choose 2 := by
      rw [hCardPairs, hi, show w - 1 + 1 = w by omega]
    exact hPairFull.trans ((Finset.card_le_card hsub).trans_eq hc)
  have hXY : x ≠ y := by
    intro he
    have hh := hAtLevel N M x hx (by simpa only [he] using hy)
    omega
  have hSum : (group 0).bound + (group 1).bound ≤ w.choose 2 + (2 * (w - 1) - 1) := by
    by_cases hxy : x < y
    · have hPair1 : (group 1).bound ≤ w.choose 2 :=
        hPairBound (group 1) (hPos 1) (N + 1) x hNβ (hSideN 1) (hX 1) false
          (fun p hp ↦ lt_trans hxy (hRight p hp))
          (fun j hj p hp ↦ False.elim (hYoung 1 j hj p hp)) hglobal rfl 1 0 rfl
          hLeftLoss (fun p hp ↦ Nat.zero_le _)
      have hh := ctx_boundary_retained_doubled_rank_budget (group 0) (hPos 0)
        (M + 1) (N + 1) y x hMβ hNβ (by omega) (hY 0) (hX 0)
        (by rw [hSideN, hSideM]) true
        (fun p hp ↦ hLeft p hp)
        (by
          rw [hSideM]
          intro j hj p hp
          have he := hOlder 0 j hj p hp
          change p < y
          omega)
        t (by rw [hSideM]; exact hne) (by rw [hSideM]; exact hglobal)
        0 1 (fun p hp ↦ Nat.zero_le _) hRightLossOlder
      have hDouble : (group 0).bound ≤ 2 * (w - 1) - 1 := by simpa using hh.2
      omega
    · have hyx : y < x := by omega
      have hPair0 : (group 0).bound ≤ w.choose 2 :=
        hPairBound (group 0) (hPos 0) (N + 1) x hNβ (hSideN 0) (hX 0) true
          (fun p hp ↦ lt_trans (hLeft p hp) hyx)
          (fun j hj p hp ↦ False.elim (hYoung 0 j hj p hp)) hglobal rfl 0 1 rfl
          (fun p hp ↦ Nat.zero_le _) hRightLoss
      have hh := ctx_boundary_retained_doubled_rank_budget (group 1) (hPos 1)
        (M + 1) (N + 1) y x hMβ hNβ (by omega) (hY 1) (hX 1)
        (by rw [hSideN, hSideM]) false
        (fun p hp ↦ hRight p hp)
        (by
          rw [hSideM]
          intro j hj p hp
          have he := hOlder 1 j hj p hp
          change y < p
          omega)
        t (by rw [hSideM]; exact hne) (by rw [hSideM]; exact hglobal)
        1 0 hLeftLossOlder (fun p hp ↦ Nat.zero_le _)
      have hDouble : (group 1).bound ≤ 2 * (w - 1) - 1 := by simpa using hh.2
      omega
  have hDecomp := ctx_bound_le_sum_run_group_prunings_capacity_three β hPosβ color
    ({0, 1} : Finset ℕ) hCover hSmall hColor
  change (∀ fuel, boundFuel fuel β ≤ ({0, 1} : Finset ℕ).sum (fun c ↦ (group c).bound)) ∧
    β.bound ≤ ({0, 1} : Finset ℕ).sum (fun c ↦ (group c).bound) at hDecomp
  have hSum' : ({0, 1} : Finset ℕ).sum (fun c ↦ (group c).bound) ≤
      w.choose 2 + (2 * (w - 1) - 1) := by simpa using hSum
  have hBudget : 2 + (w.choose 2 + (2 * (w - 1) - 1)) ≤ (w + 1).choose 2 + w - 1 := by
    have hc : (w + 1).choose 2 = w + w.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ w 1
    omega
  exact ⟨fun f g ↦ (Nat.add_le_add (hOwn.1 f) ((hDecomp.1 g).trans hSum')).trans hBudget,
    (Nat.add_le_add hOwn.2 (hDecomp.2.trans hSum')).trans hBudget⟩

end ErdosSzekeres
