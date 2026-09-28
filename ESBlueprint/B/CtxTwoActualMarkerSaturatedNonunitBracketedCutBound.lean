import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxTwoActualMarkerSharpPotentialArbitraryHistory
import ESBlueprint.B.CtxActiveTwoBoundaryMarkerRankUnionBound
import ESBlueprint.B.CtxOldestAxisMaximumEraseNormalize
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential
import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Sharpen every nonunit bracketed chosen cut in the top two opposite-global bands. The chosen part costs at most w; erasing the only opposite maximum in the companion retains two actual chosen levels and caps its width at k-3. This pays choose(w+1,2)-2 in the top band and choose(w+1,2)+w-2 in the next band. Positive physical labels, distinct axes, chosen global at most five, two actual chosen levels and no indexed opposite history. Opposite width w is at least four and the opposite global is k or k-1; the two new maxima sum to k-1. A nonempty chosen kept set is bracketed by complementary children and has a chosen-capacity-two witness. Convexity, exact occurrence counts and bounds on additional chosen history are not required. No recursive potential premise. Unit cuts and other cut geometries are outside this theorem.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_actual_marker_saturated_nonunit_bracketed_cut_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hclear : σ.levelsOn t 0 = [])
  (hwidth : 4 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
  (hband : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) = σ.k ∨
    (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) + 1 = σ.k)
  (keep : List ℕ) (q₀ l r m n : ℕ)
  (hq₀ : q₀ ∈ keep)
  (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
  (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
  (hlnot : l ∉ keep) (hrnot : r ∉ keep)
  (hinside : ∀ p ∈ keep, l < p ∧ p < r)
  (hcoupling : m + n = σ.k - 1)
  (hnonunit : 2 ≤ (match s with
    | Ctx.Side.lower => (σ.part keep s m).cupLimit q₀ q₀
    | Ctx.Side.upper => (σ.part keep s m).capLimit q₀ q₀)) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let budget := (w + 1).choose 2 + (if w + 2 = σ.k then w else 0) - 2
  (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) +
    Ctx.Context.boundFuel g (σ.part rest t n) ≤ budget) ∧
    (σ.part keep s m).bound + (σ.part rest t n).bound ≤ budget := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let P (v : ℕ) := (v+1).choose 2+v-1
  let a := q₀
  let b := q₀
  have ha : a ∈ keep := hq₀
  have hb : b ∈ keep := hq₀
  let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part keep s m
  let β := σ.part rest t n
  let budget := (w + 1).choose 2 + (if w + 2 = σ.k then w else 0) - 2
  change (∀ f g, boundFuel f α + boundFuel g β ≤ budget) ∧ α.bound + β.bound ≤ budget
  have hw : 4 ≤ w := hwidth
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
  have hOwn : (∀ fuel, boundFuel fuel α ≤ w) ∧ α.bound ≤ w := by
    have hsmall : min ((match (generalizing := false) α.sideAt 1 with
        | Side.lower => α.u | Side.upper => α.a) - 2) (α.k - α.maximumAt 1) ≤ 3 := by
      rw [hSideα]
      apply (Nat.min_le_left _ _).trans
      change (match (generalizing := false) s with
        | Side.lower => σ.u | Side.upper => σ.a) - 2 ≤ 3
      omega
    have hh := ctx_active_two_boundary_marker_rank_union_bound α hPosα 1 l r
      hOneα hLα hRα (fun p hp _ ↦ hinside p ((hChildα p).mp hp).2)
      (by simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true])
      t (by rw [hSideα]; exact hne) hsmall
    let active := α.childPositions.toFinset.filter
      (fun p ↦ 0 < α.cupLimit p p ∧ 0 < α.capLimit p p)
    let ranks := active.biUnion
      (fun p ↦ Finset.Icc (α.leftExt t 0 p + 1) (w - α.rightExt t 0 p))
    change (∀ fuel, boundFuel fuel α ≤ ranks.card) ∧ α.bound ≤ ranks.card at hh
    have hsub : ranks ⊆ Finset.Icc 1 w := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hz' := Finset.mem_Icc.mp hz
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hc : ranks.card ≤ w := by
      have h := Finset.card_le_card hsub
      simpa using h
    exact ⟨fun f ↦ (hh.1 f).trans hc, hh.2.trans hc⟩
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
  have hBand : w+1 = σ.k ∨ w+2 = σ.k := by
    change G σ t = σ.k ∨ G σ t+1 = σ.k at hband
    change 4 ≤ G σ t-1 at hwidth
    dsimp only [G] at hband hwidth
    dsimp only [w]
    rcases hband with h | h <;> omega
  have hk : 5 ≤ σ.k := by omega
  have hNewMaximum : m ≤ α.joinExt s q₀ q₀ := by
    have hOn : 1 ∈ α.levelsOn s 0 := by rw [part_levelsOn_self_zero hSideα]; simp
    have hh := le_joinExt_of_mem_levelsOn hOn q₀ q₀
    rw [part_maximumAt_one] at hh
    omega
  have hm : m ≤ σ.k-3 := by
    cases s <;> simp only [cupLimit, capLimit] at hnonunit
    all_goals change 2 ≤ min _ (σ.k-1-α.joinExt _ q₀ q₀) at hnonunit
    all_goals omega
  have hterminal : ∀ j ∈ β.levelsOn (β.sideAt 1) 0, j ≤ 1 := by
    rw [hSideβ, part_levelsOn_self_zero hSideβ, hclear]
    simp
  let f : Letter → Letter := fun z => match z with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext
        (if j = 1 then β.maxima.length else if 1 < j then j-1 else j) v
  let E : Context := {β with word := β.word.map f, maxima := β.maxima.eraseIdx 0}
  let ν : Context := match β.sideAt 1 with
    | Side.lower => {E with u := min β.u (β.k-β.maximumAt 1)}
    | Side.upper => {E with a := min β.a (β.k-β.maximumAt 1)}
  have hn := ctx_oldest_axis_maximum_erase_normalize β 1 hOneβ hterminal
  have hToνFuel : ∀ fuel, boundFuel fuel β ≤ boundFuel fuel ν := hn.2.2.2.2.1
  have hToν : β.bound ≤ ν.bound := hn.2.2.2.2.2
  have hβDepth : β.maxima.length = σ.maxima.length+1 := by simp [β, part]
  have hνDepth : ν.maxima.length = σ.maxima.length := by
    have hh := hn.2.1
    change ν.maxima.length = β.maxima.length-1 at hh
    omega
  have hνLevels : ν.levels = σ.levels := by simp only [levels, hνDepth]
  have hNν : N ∈ ν.levels := by rw [hνLevels]; exact hN
  have hMν : M ∈ ν.levels := by rw [hνLevels]; exact hM
  have hMapN := hn.2.2.1 N hNν
  have hMapM := hn.2.2.1 M hMν
  simp only [show ¬N<1 by omega, if_false] at hMapN
  simp only [show ¬M<1 by omega, if_false] at hMapM
  have hNsν : ν.sideAt N = s := hMapN.2.2.2.1.trans hNsβ
  have hMsν : ν.sideAt M = s := hMapM.2.2.2.1.trans hMsβ
  have hxν : x ∈ ν.extPositions N := by
    have he : ν.extPositions N = β.extPositions (N + 1) := hMapN.2.2.1
    rw [he]
    exact hXβ
  have hyν : y ∈ ν.extPositions M := by
    have he : ν.extPositions M = β.extPositions (M + 1) := hMapM.2.2.1
    rw [he]
    exact hYβ
  have hνWord : ν.word = β.word.map f := by cases hs : β.sideAt 1 <;> simp only [ν, hs, E]
  have hνLetter (p : ℕ) : ν.letterAt p = f (β.letterAt p) := by
    simp only [letterAt, hνWord, List.getElem?_map]
    cases β.word[p]? <;> rfl
  have hνPos : ∀ p j v, ν.letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hj
    rw [hνLetter] at hj
    cases he : β.letterAt p with
    | child => simp only [he, f] at hj; cases hj
    | ext i z =>
      rw [he] at hj
      have hi := hPosβ p i z he
      have hnew : 1 ≤ (if i = 1 then β.maxima.length else if 1 < i then i - 1 else i) := by
        rw [hβDepth]
        split_ifs <;> omega
      change Letter.ext (if i = 1 then β.maxima.length else if 1 < i then i - 1 else i) z = Letter.ext j v at hj
      cases hj
      exact hnew
  have hνChosen : G ν s = G σ s := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · simp only [G, ν, hSideβ]; rfl
    · simp only [G, ν, hSideβ]; rfl
    · exact False.elim (hne rfl)
  have hνGlobal : G ν s ≤ 5 := by rw [hνChosen]; exact hglobal
  have hβMaximum : β.maximumAt 1 = n := part_maximumAt_one σ rest t n
  have hνOpposite : G ν t ≤ σ.k-n := by
    cases t <;> simp only [G, ν, hSideβ, hβMaximum]
    all_goals exact Nat.min_le_right _ _
  have hνWidth : G ν t-1 ≤ σ.k-3 := by omega
  have hMonoP (v q : ℕ) (h : v ≤ q) : P v ≤ P q := by
    dsimp only [P]
    exact Nat.sub_le_sub_right (Nat.add_le_add
      (Nat.choose_le_choose 2 (Nat.add_le_add_right h 1)) h) 1
  have hOther : (∀ fuel, boundFuel fuel β ≤ P (σ.k-3)) ∧ β.bound ≤ P (σ.k-3) := by
    by_cases hwν : 2 ≤ G ν t-1
    · have hh := ctx_two_actual_marker_sharp_potential_arbitrary_history ν hνPos s t hne
        N M x y hNν hMν hNM hNsν hMsν hxν hyν hνGlobal hwν
      have hb := hMonoP _ _ hνWidth
      exact ⟨fun fuel => (hToνFuel fuel).trans ((hh.1 fuel).trans hb), hToν.trans (hh.2.trans hb)⟩
    · have hh := ctx_small_global_axis_rank_region_potential ν hνPos t s (Ne.symm hne)
        (show G ν t ≤ 3 by omega)
      have hBound : ν.bound ≤ G ν s-1 := by
        cases s <;> exact hh.2.1.trans hh.2.2.1
      have hFour : 4 ≤ P (σ.k-3) := by
        have hh := hMonoP 2 (σ.k-3) (by omega)
        norm_num [P] at hh ⊢
        omega
      have hFull : β.bound ≤ P (σ.k-3) := hToν.trans (hBound.trans ((by omega : G ν s-1 ≤ 4).trans hFour))
      have hFuelFull (fuel : ℕ) : boundFuel fuel β ≤ β.bound := by
        by_cases hf : β.childPositions.length+1 ≤ fuel
        · exact (boundFuel_eq_bound β hf).le
        · exact boundFuel_mono (by omega : fuel ≤ β.childPositions.length+1) β
      exact ⟨fun fuel => (hFuelFull fuel).trans hFull, hFull⟩
  have hBudget : w + P (σ.k-3) ≤ budget := by
    have hA : (w+1).choose 2 = w.choose 2+w := by
      simpa only [Nat.choose_one_right, Nat.succ_eq_add_one, Nat.add_comm] using Nat.choose_succ_succ w 1
    have hB : w.choose 2 = (w-1).choose 2+(w-1) := by
      simpa only [Nat.choose_one_right, Nat.succ_eq_add_one, show w-1+1=w by omega, Nat.add_comm] using Nat.choose_succ_succ (w-1) 1
    rcases hBand with h | h
    · have hK : σ.k-3=w-2 := by omega
      have hNe : ¬w+2=σ.k := by omega
      simp only [P, budget, hK, if_neg hNe, Nat.add_zero, show w-2+1=w-1 by omega]
      have hc := Nat.choose_le_choose 2 (show 3 ≤ w-1 by omega)
      norm_num at hc
      omega
    · have hK : σ.k-3=w-1 := by omega
      simp only [P, budget, hK, if_pos h, show w-1+1=w by omega]
      have hc := Nat.choose_le_choose 2 (show 3 ≤ w by omega)
      norm_num at hc
      omega
  exact ⟨fun f g => (Nat.add_le_add (hOwn.1 f) (hOther.1 g)).trans hBudget,
    (Nat.add_le_add hOwn.2 hOther.2).trans hBudget⟩


end ErdosSzekeres
