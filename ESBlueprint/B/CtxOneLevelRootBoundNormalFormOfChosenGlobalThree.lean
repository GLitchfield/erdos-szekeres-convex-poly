import ESBlueprint.B.CtxBoundLeMergeSameSideLevels
import ESBlueprint.B.CtxBoundZeroOfUnitGlobalAxis
import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank
import ESBlueprint.B.CtxBoundCutLe
import ESBlueprint.B.CtxTwoBoundaryMarkerUpperNormalize
import ESBlueprint.B.CtxPartBoundZeroOfSameSideLargeSiblingMaximum
import ESBlueprint.B.CtxBoundReverse
import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum
import ESBlueprint.B.CtxSingleLevelLimitsExact
import ESBlueprint.B.CtxSingletonPartBoundEqThreshold
import ESBlueprint.B.CtxPartPositiveLetters
import ESBlueprint.B.CtxPositiveBoundAttainedByIntervalCut
import ESBlueprint.B.CtxBoundaryMarkerUpperNormalize
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential
import ESBlueprint.B.CtxUnitAxisActiveRegionPotential
import ESBlueprint.B.CtxChainOneChildrenExteriorOfTwoLevels

set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

namespace ErdosSzekeres

open Ctx Ctx.Context MergeLevels

/-- Exact ROOT-NF equality for every legal uniform one-level root whose chosen global axis is three, with arbitrary physical run lengths, marker multiplicities and all endpoint configurations. The normal form preserves actual endpoint marker presence and clamps at three on a global axis two and two otherwise; empty, unit, single-run, opposite-axis-two and saturated cases included. Marked roots have exact bound zero or one, and unmarked nonsaturated opposite-axis-at-least-three roots have exact bound two via a legal coupled singleton cut and whole complementary prefix merge. No general normal-form or contraction assumption.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_one_level_root_bound_normal_form_of_chosen_global_three (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k)
    (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2)
    (side : Ctx.Side) (word : List Ctx.Letter)
    (hletters : ∀ x ∈ word, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side)
    (hchosen3 : (match side with | Ctx.Side.lower => u | Ctx.Side.upper => a) = 3) :
    let σ : Ctx.Context := {a := a, u := u, k := k, word := word, maxima := [m]}
    let r := min σ.numRuns (if a = 2 ∨ u = 2 then 3 else 2)
    let marker := Ctx.Letter.ext 1 side
    let normalWord :=
      (if word.head? = some marker then [marker] else []) ++
      (List.replicate r Ctx.Letter.child).intersperse marker ++
      (if word.getLast? = some marker then [marker] else [])
    σ.bound = ({σ with word := normalWord} : Ctx.Context).bound := by
  classical
  have hemptyBound (ρ : Ctx.Context) (hρ : ρ.childPositions = []) : ρ.bound = 0 := by
    have hr : ρ.numRuns ≤ 1 := by
      have h := Ctx.numRuns_le_length ρ
      rw [hρ] at h
      simp only [List.length_nil] at h
      omega
    simp only [Ctx.Context.bound, hρ, List.length_nil, Nat.zero_add]
    rw [Ctx.Context.boundFuel.eq_2, if_pos hr]
    simp [Ctx.Context.base, hρ]
  have hSingle (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m]) (side : Ctx.Side)
      (hletters : ∀ x ∈ σ.word, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side)
      (hruns : σ.numRuns ≤ 1) :
      let marker := Ctx.Letter.ext 1 side
      let normalWord :=
        (if σ.word.head? = some marker then [marker] else []) ++
        (List.replicate σ.numRuns Ctx.Letter.child).intersperse marker ++
        (if σ.word.getLast? = some marker then [marker] else [])
      σ.bound = ({σ with word := normalWord} : Ctx.Context).bound := by
    classical
    let marker := Ctx.Letter.ext 1 side
    have hmarker : Ctx.Letter.child ≠ marker := by simp [marker]
    let normalWord :=
      (if σ.word.head? = some marker then [marker] else []) ++
      (List.replicate σ.numRuns Ctx.Letter.child).intersperse marker ++
      (if σ.word.getLast? = some marker then [marker] else [])
    let τ : Ctx.Context := {σ with word := normalWord}
    change σ.bound = τ.bound
    have hemptyBound (ρ : Ctx.Context) (hρ : ρ.childPositions = []) : ρ.bound = 0 := by
      have hh : ρ.numRuns ≤ 1 := by
        have h := Ctx.numRuns_le_length ρ
        rw [hρ] at h
        simp only [List.length_nil] at h
        omega
      simp only [Ctx.Context.bound, hρ, List.length_nil, Nat.zero_add]
      rw [Ctx.Context.boundFuel.eq_2, if_pos hh]
      simp [Ctx.Context.base, hρ]
    by_cases hempty : σ.childPositions = []
    · have hruns0 : σ.numRuns = 0 := by
        have h := Ctx.numRuns_le_length σ
        rw [hempty] at h
        simp only [List.length_nil] at h
        omega
      have hτempty : τ.childPositions = [] := by
        by_cases hleft : σ.word.head? = some marker <;>
          by_cases hright : σ.word.getLast? = some marker <;>
          simp [τ, normalWord, hruns0, hleft, hright,
            Ctx.Context.childPositions, Ctx.Context.letterAt, marker] <;>
          intro p hp <;> interval_cases p <;> simp
      rw [hemptyBound σ hempty, hemptyBound τ hτempty]
    have hInterval (ρ : Ctx.Context) (hruns : ρ.numRuns ≤ 1)
        (hchildNe : ρ.childPositions ≠ []) :
        ∃ b, ρ.childPositions = List.range' b ρ.childPositions.length := by
      obtain ⟨b, tail, hcons⟩ := List.exists_cons_of_ne_nil hchildNe
      have hb : b ∈ ρ.childPositions := by
        rw [hcons]
        exact List.mem_cons_self
      have hordered : ρ.childPositions.Pairwise (· ≤ ·) :=
        (Ctx.Context.childPositions_pairwise ρ).imp le_of_lt
      have hmin : ∀ p ∈ ρ.childPositions, b ≤ p := by
        intro p hp
        have h := hordered.rel_head hp
        simpa [hcons] using h
      let starts := (List.range ρ.word.length).filter fun p ↦
        ρ.letterAt p = Ctx.Letter.child ∧
          (p = 0 ∨ ρ.letterAt (p - 1) ≠ Ctx.Letter.child)
      have hstartsLen : starts.length ≤ 1 := by
        simpa [starts, Ctx.Context.numRuns] using hruns
      have hstartsNodup : starts.Nodup := by
        exact List.nodup_range.filter _
      have hbRange : b < ρ.word.length := by
        exact List.mem_range.1 (List.mem_filter.1 hb).1
      have hbLetter : ρ.letterAt b = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.1 hb).2
      have hbStartCondition :
          b = 0 ∨ ρ.letterAt (b - 1) ≠ Ctx.Letter.child := by
        by_cases hb0 : b = 0
        · exact Or.inl hb0
        · right
          intro hprev
          have hprevMem : b - 1 ∈ ρ.childPositions := by
            apply List.mem_filter.2
            exact ⟨List.mem_range.2 (by omega), by simpa using hprev⟩
          have := hmin (b - 1) hprevMem
          omega
      have hbStart : b ∈ starts := by
        simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hbRange, hbLetter, hbStartCondition⟩
      have hstartUnique : ∀ p ∈ starts, p = b := by
        intro p hp
        by_contra hpb
        have hsubset : ({b, p} : Finset ℕ) ⊆ starts.toFinset := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact List.mem_toFinset.2 hbStart
          · exact List.mem_toFinset.2 hp
        have hcard := Finset.card_le_card hsubset
        rw [List.toFinset_card_of_nodup hstartsNodup] at hcard
        have htwo : ({b, p} : Finset ℕ).card = 2 := by
          simp [Ne.symm hpb]
        rw [htwo] at hcard
        omega
      have hpred : ∀ p ∈ ρ.childPositions, p ≠ b → p - 1 ∈ ρ.childPositions := by
        intro p hp hpb
        have hpRange : p < ρ.word.length :=
          List.mem_range.1 (List.mem_filter.1 hp).1
        have hpLetter : ρ.letterAt p = Ctx.Letter.child :=
          of_decide_eq_true (List.mem_filter.1 hp).2
        have hpPositive : 0 < p := by
          have := hmin p hp
          omega
        by_contra hprevMem
        have hprevLetter : ρ.letterAt (p - 1) ≠ Ctx.Letter.child := by
          intro hletter
          apply hprevMem
          apply List.mem_filter.2
          exact ⟨List.mem_range.2 (by omega), by simpa using hletter⟩
        have hpStart : p ∈ starts := by
          simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
          exact ⟨hpRange, hpLetter, Or.inr hprevLetter⟩
        exact hpb (hstartUnique p hpStart)
      have hfill : ∀ p ∈ ρ.childPositions, ∀ q, b ≤ q → q ≤ p →
          q ∈ ρ.childPositions := by
        intro p
        induction p using Nat.strong_induction_on with
        | h p ih =>
          intro hp q hbq hqp
          by_cases hpb : p = b
          · have : q = b := by omega
            simpa [this] using hb
          by_cases hqp' : q = p
          · simpa [hqp'] using hp
          exact ih (p - 1) (by omega) (hpred p hp hpb) q hbq (by omega)
      let e := ρ.childPositions.getLast hchildNe
      have he : e ∈ ρ.childPositions := by
        dsimp [e]
        exact List.getLast_mem _
      have hmax : ∀ p ∈ ρ.childPositions, p ≤ e := by
        intro p hp
        simpa [e] using hordered.rel_getLast hp
      have hbe : b ≤ e := hmin e he
      have hmemRange : ∀ p, p ∈ ρ.childPositions ↔
          p ∈ List.range' b (e + 1 - b) := by
        intro p
        simp only [List.mem_range'_1]
        constructor
        · intro hp
          exact ⟨hmin p hp, by have := hmax p hp; omega⟩
        · rintro ⟨hbp, hp⟩
          exact hfill e he p hbp (by omega)
      have hperm : ρ.childPositions.Perm (List.range' b (e + 1 - b)) :=
        (List.perm_ext_iff_of_nodup (Ctx.Context.childPositions_nodup ρ)
          List.nodup_range').2 hmemRange
      have hrange : ρ.childPositions = List.range' b (e + 1 - b) :=
        List.Perm.eq_of_pairwise' (r := (· ≤ ·)) hordered List.pairwise_le_range' hperm
      have hlen : ρ.childPositions.length = e + 1 - b := by
        rw [hrange]
        simp
      have hinterval : ρ.childPositions = List.range' b ρ.childPositions.length := by
        rw [hlen]
        exact hrange
      exact ⟨b, hinterval⟩
    obtain ⟨b, hspan⟩ := hInterval σ hruns hempty
    have hN : 0 < σ.childPositions.length := List.length_pos_iff.mpr hempty
    have hmemChild (x : ℕ) : x ∈ σ.childPositions ↔
        b ≤ x ∧ x < b + σ.childPositions.length := by
      rw [hspan]
      simpa only [List.length_range'] using (List.mem_range'_1 (m := x) (s := b) (n := σ.childPositions.length))
    have hb : b ∈ σ.childPositions := (hmemChild b).mpr ⟨le_rfl, by omega⟩
    have hbRange : b < σ.word.length := List.mem_range.mp (List.mem_filter.mp hb).1
    have hbLetter : σ.letterAt b = Ctx.Letter.child :=
      of_decide_eq_true (List.mem_filter.mp hb).2
    have hfirst : σ.childPositions.head? = some b := by
      rw [hspan, List.head?_range']
      simp [ne_of_gt hN]
    have hprev : b = 0 ∨ σ.letterAt (b - 1) ≠ Ctx.Letter.child := by
      by_cases hb0 : b = 0
      · exact Or.inl hb0
      · right
        intro he
        have hp : b - 1 ∈ σ.childPositions := by
          exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simpa using he⟩
        have := (hmemChild (b - 1)).mp hp
        omega
    have hstart : b ∈ ((List.range σ.word.length).filter fun p =>
        σ.letterAt p = Ctx.Letter.child ∧
          (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child)) := by
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hbRange, hbLetter, hprev⟩
    have hruns1 : σ.numRuns = 1 := by
      have hh : 0 < σ.numRuns := List.length_pos_iff.mpr (List.ne_nil_of_mem hstart)
      omega
    have hlen : 0 < σ.word.length := by omega
    have hlastRange : σ.word.length - 1 < σ.word.length := by omega
    have hAt (x : ℕ) (hx : x < σ.word.length) :
        σ.letterAt x = Ctx.Letter.child ∨ σ.letterAt x = marker := by
      have hw := hletters _ (List.getElem_mem hx)
      simpa [Ctx.Context.letterAt, List.getElem?_eq_getElem hx, marker] using hw
    have hExtMem (x : ℕ) :
        x ∈ σ.extPositions 1 ↔ x < σ.word.length ∧ σ.letterAt x = marker := by
      constructor
      · intro hx
        have hxr : x < σ.word.length := List.mem_range.mp (List.mem_filter.mp hx).1
        rcases hAt x hxr with hc | hm
        · simp [Ctx.Context.extPositions, hc] at hx
        · exact ⟨hxr, hm⟩
      · rintro ⟨hxr, hm⟩
        simp [Ctx.Context.extPositions, hxr, hm, marker]
    have hheadAt : σ.word.head? = some marker ↔ σ.letterAt 0 = marker := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen]
      simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hlen]
    have hlastAt : σ.word.getLast? = some marker ↔
        σ.letterAt (σ.word.length - 1) = marker := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlastRange]
      simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hlastRange]
    have hleft : ((σ.extPositions 1).filter (· < b)) ≠ [] ↔
        σ.word.head? = some marker := by
      constructor
      · intro hn
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hn
        have hxb : x < b := of_decide_eq_true (List.mem_filter.mp hx).2
        apply hheadAt.mpr
        rcases hAt 0 hlen with hc | hm
        · have hzeroChild : 0 ∈ σ.childPositions :=
            List.mem_filter.mpr ⟨List.mem_range.mpr hlen, by simpa using hc⟩
          have := (hmemChild 0).mp hzeroChild
          omega
        · exact hm
      · intro hh
        have hzero := hheadAt.mp hh
        have hb0 : b ≠ 0 := by
          intro h
          subst b
          rw [hbLetter] at hzero
          exact hmarker hzero
        have hm : 0 ∈ (σ.extPositions 1).filter (· < b) :=
          List.mem_filter.mpr ⟨(hExtMem 0).mpr ⟨hlen, hzero⟩,
            by simpa using Nat.pos_of_ne_zero hb0⟩
        exact List.ne_nil_of_mem hm
    have hright : ((σ.extPositions 1).filter (b < ·)) ≠ [] ↔
        σ.word.getLast? = some marker := by
      constructor
      · intro hn
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hn
        have hbx : b < x := of_decide_eq_true (List.mem_filter.mp hx).2
        have hxm := (hExtMem x).mp (List.mem_filter.mp hx).1
        have houtside : b + σ.childPositions.length ≤ x := by
          by_contra h
          have hxc := (hmemChild x).mpr ⟨by omega, by omega⟩
          have hc := of_decide_eq_true (List.mem_filter.mp hxc).2
          rw [hc] at hxm
          exact hmarker hxm.2
        apply hlastAt.mpr
        rcases hAt (σ.word.length - 1) hlastRange with hc | hm
        · have hlastChild : σ.word.length - 1 ∈ σ.childPositions :=
            List.mem_filter.mpr ⟨List.mem_range.mpr hlastRange, by simpa using hc⟩
          have := (hmemChild (σ.word.length - 1)).mp hlastChild
          omega
        · exact hm
      · intro hh
        have hlast := hlastAt.mp hh
        have hne : σ.word.length - 1 ≠ b := by
          intro h
          rw [h, hbLetter] at hlast
          exact hmarker hlast
        have hbl : b < σ.word.length - 1 := by omega
        have hm : σ.word.length - 1 ∈ (σ.extPositions 1).filter (b < ·) :=
          List.mem_filter.mpr ⟨(hExtMem _).mpr ⟨hlastRange, hlast⟩, by simpa using hbl⟩
        exact List.ne_nil_of_mem hm
    let q := if σ.word.head? = some marker then 1 else 0
    have hτchildren : τ.childPositions = [q] := by
      by_cases hL : σ.word.head? = some marker <;>
        by_cases hR : σ.word.getLast? = some marker <;>
        simp [τ, normalWord, hruns1, q, hL, hR, marker,
          Ctx.Context.childPositions, Ctx.Context.letterAt, List.range_succ]
    have hτleft : ((τ.extPositions 1).filter (· < q)) ≠ [] ↔
        σ.word.head? = some marker := by
      by_cases hL : σ.word.head? = some marker <;>
        by_cases hR : σ.word.getLast? = some marker <;>
        simp [τ, normalWord, hruns1, q, hL, hR, marker,
          Ctx.Context.extPositions, Ctx.Context.letterAt, List.range_succ]
    have hτright : ((τ.extPositions 1).filter (q < ·)) ≠ [] ↔
        σ.word.getLast? = some marker := by
      by_cases hL : σ.word.head? = some marker <;>
        by_cases hR : σ.word.getLast? = some marker <;>
        simp [τ, normalWord, hruns1, q, hL, hR, marker,
          Ctx.Context.extPositions, Ctx.Context.letterAt, List.range_succ]
    have hsideActual (hn : σ.extPositions 1 ≠ []) : σ.sideAt 1 = side := by
      obtain ⟨x, xs, he⟩ := List.exists_cons_of_ne_nil hn
      have hx : x ∈ σ.extPositions 1 := by rw [he]; simp
      have hm := (hExtMem x).mp hx
      simp [Ctx.Context.sideAt, he, hm.2, marker]
    have hrootSide : σ.sideAt 1 =
        if σ.word.head? = some marker ∨ σ.word.getLast? = some marker then side
        else Ctx.Side.lower := by
      by_cases he : σ.word.head? = some marker ∨ σ.word.getLast? = some marker
      · rw [if_pos he]
        apply hsideActual
        intro hn
        rcases he with hL | hR
        · have h := hleft.mpr hL
          simp [hn] at h
        · have h := hright.mpr hR
          simp [hn] at h
      · rw [if_neg he]
        have hn : σ.extPositions 1 = [] := by
          by_contra hn
          obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hn
          have hm := (hExtMem x).mp hx
          have hne : x ≠ b := by
            intro h
            rw [h, hbLetter] at hm
            exact hmarker hm.2
          by_cases hxb : x < b
          · exact he (Or.inl (hleft.mp (List.ne_nil_of_mem
              (List.mem_filter.mpr ⟨hx, by simpa using hxb⟩))))
          · have hbx : b < x := by omega
            exact he (Or.inr (hright.mp (List.ne_nil_of_mem
              (List.mem_filter.mpr ⟨hx, by simpa using hbx⟩))))
        simp [Ctx.Context.sideAt, hn]
    have hsideEq : σ.sideAt 1 = τ.sideAt 1 := by
      rw [hrootSide]
      by_cases hL : σ.word.head? = some marker <;>
        by_cases hR : σ.word.getLast? = some marker <;>
        simp [τ, normalWord, hruns1, hL, hR, marker,
          Ctx.Context.sideAt, Ctx.Context.extPositions, Ctx.Context.letterAt, List.range_succ]
    have hτmax : τ.maxima = [m] := hmax
    have hLeftCount (ρ : Ctx.Context) (p : ℕ) (v : Ctx.Side) (hm : ρ.maxima = [m]) :
        ρ.leftExt v 0 p =
          if ρ.sideAt 1 = v ∧ ((ρ.extPositions 1).filter (· < p)) ≠ [] then 1 else 0 := by
      by_cases hs : ρ.sideAt 1 = v
      · have hon : ρ.levelsOn v 0 = [1] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
        by_cases hn : ((ρ.extPositions 1).filter (· < p)) = []
        · simp [Ctx.Context.leftExt, hon, hn, hs, -List.getLast?_filter]
        · simp [Ctx.Context.leftExt, hon,
            List.getLast?_eq_some_getLast hn, hs, hn, -List.getLast?_filter,
            -List.getLast_filter]
      · have hon : ρ.levelsOn v 0 = [] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
        simp [Ctx.Context.leftExt, hon, hs]
    have hRightCount (ρ : Ctx.Context) (p : ℕ) (v : Ctx.Side) (hm : ρ.maxima = [m]) :
        ρ.rightExt v 0 p =
          if ρ.sideAt 1 = v ∧ ((ρ.extPositions 1).filter (p < ·)) ≠ [] then 1 else 0 := by
      by_cases hs : ρ.sideAt 1 = v
      · have hon : ρ.levelsOn v 0 = [1] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
        by_cases hn : ((ρ.extPositions 1).filter (p < ·)) = []
        · simp [Ctx.Context.rightExt, hon, hn, hs, -List.head?_filter]
        · simp [Ctx.Context.rightExt, hon,
            List.head?_eq_some_head hn, hs, hn, -List.head?_filter,
            -List.head_filter]
      · have hon : ρ.levelsOn v 0 = [] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
        simp [Ctx.Context.rightExt, hon, hs]
    have hleftEq (v : Ctx.Side) : σ.leftExt v 0 b = τ.leftExt v 0 q := by
      simp only [hLeftCount σ b v hmax, hLeftCount τ q v hτmax, hsideEq, hleft, hτleft]
    have hrightEq (v : Ctx.Side) : σ.rightExt v 0 b = τ.rightExt v 0 q := by
      simp only [hRightCount σ b v hmax, hRightCount τ q v hτmax, hsideEq, hright, hτright]
    have hchainEq (v : Ctx.Side) : σ.chainExt v b b = τ.chainExt v q q := by
      simp only [Ctx.Context.chainExt, hleftEq, hrightEq]
    have hJoinCount (ρ : Ctx.Context) (p : ℕ) (v : Ctx.Side) (hm : ρ.maxima = [m]) :
        ρ.joinExt v p p = max (ρ.chainExt v p p) (if ρ.sideAt 1 = v then m else 0) := by
      by_cases hs : ρ.sideAt 1 = v
      · have hon : ρ.levelsOn v 0 = [1] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
        simp [Ctx.Context.joinExt, hon, Ctx.Context.leftExt_one,
          Ctx.Context.rightExt_one, Ctx.Context.maximumAt, hm, hs]
      · have hon : ρ.levelsOn v 0 = [] := by simp [Ctx.Context.levelsOn, Ctx.Context.levels, hm, hs]
        simp [Ctx.Context.joinExt, hon, hs]
    have hjoinEq (v : Ctx.Side) : σ.joinExt v b b = τ.joinExt v q q := by
      rw [hJoinCount σ b v hmax, hJoinCount τ q v hτmax, hchainEq, hsideEq]
    have hcup : σ.cupLimit b b = τ.cupLimit q q := by
      simp only [Ctx.Context.cupLimit, hchainEq, hjoinEq]
      all_goals rfl
    have hcap : σ.capLimit b b = τ.capLimit q q := by
      simp only [Ctx.Context.capLimit, hchainEq, hjoinEq]
      all_goals rfl
    have hbase (ρ : Ctx.Context) (p : ℕ) (hh : ρ.childPositions.head? = some p)
        (hr : ρ.numRuns ≤ 1) :
        ρ.bound = Ctx.Context.baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k := by
      unfold Ctx.Context.bound
      rw [Ctx.Context.boundFuel.eq_2, if_pos hr, Ctx.Context.base_eq_baseOf, hh]
      all_goals rfl
    have hτfirst : τ.childPositions.head? = some q := by rw [hτchildren]; rfl
    have hτruns : τ.numRuns ≤ 1 := by
      have h := Ctx.numRuns_le_length τ
      simpa [hτchildren] using h
    rw [hbase σ b hfirst hruns, hbase τ q hτfirst hτruns, hcup, hcap]
  have hTwoSites (σ : Ctx.Context) (s : Ctx.Side)
    (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
    (hruns : 2 ≤ σ.numRuns) :
    ∃ x l y,
      x ∈ σ.childPositions ∧ y ∈ σ.childPositions ∧
      x < l ∧ l < y ∧ σ.letterAt l = Ctx.Letter.ext 1 s := by
    classical
    let starts := (List.range σ.word.length).filter fun p =>
      σ.letterAt p = Ctx.Letter.child ∧
        (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child)
    have hlen : 2 ≤ starts.length := hruns
    have hsort : starts.Pairwise (· < ·) := List.pairwise_lt_range.filter _
    have hData (p : ℕ) (hp : p ∈ starts) :
        p < σ.word.length ∧ σ.letterAt p = Ctx.Letter.child ∧
          (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child) := by
      simpa only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq] using hp
    have hChild (p : ℕ) (hp : p ∈ starts) : p ∈ σ.childPositions := by
      have hd := hData p hp
      simp [Ctx.Context.childPositions, hd.1, hd.2.1]
    have hLetter (p : ℕ) (hp : p < σ.word.length) :
        σ.letterAt p = Ctx.Letter.child ∨ σ.letterAt p = Ctx.Letter.ext 1 s := by
      have he : σ.letterAt p = σ.word[p] := by
        simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hp]
      rw [he]
      exact hletters _ (List.getElem_mem hp)
    cases hs : starts with
    | nil => simp [hs] at hlen
    | cons x xs =>
      cases hxs : xs with
      | nil => simp [hs, hxs] at hlen
      | cons y ys =>
        have hform : starts = x :: y :: ys := by rw [hs, hxs]
        have hx : x ∈ starts := by rw [hform]; simp
        have hy : y ∈ starts := by rw [hform]; simp
        have hsort' : (x :: y :: ys).Pairwise (· < ·) := by rw [← hform]; exact hsort
        have hxy : x < y := (List.pairwise_cons.mp hsort').1 _ (by simp)
        have hxD := hData x hx
        have hyD := hData y hy
        have hlnot : σ.letterAt (y - 1) ≠ Ctx.Letter.child := by
          rcases hyD.2.2 with h0 | hno
          · omega
          · exact hno
        have hl : σ.letterAt (y - 1) = Ctx.Letter.ext 1 s :=
          (hLetter (y - 1) (by omega)).resolve_left hlnot
        have hxl : x < y - 1 := by
          have hne : x ≠ y - 1 := by
            intro he
            rw [he, hl] at hxD
            cases hxD.2.1
          omega
        exact ⟨x, y - 1, y, hChild x hx, hChild y hy, hxl, by omega, hl⟩

  have hInterval (ρ : Ctx.Context) (hruns : ρ.numRuns ≤ 1)
      (hchildNe : ρ.childPositions ≠ []) :
      ∃ b, ρ.childPositions = List.range' b ρ.childPositions.length := by
    obtain ⟨b, tail, hcons⟩ := List.exists_cons_of_ne_nil hchildNe
    have hb : b ∈ ρ.childPositions := by
      rw [hcons]
      exact List.mem_cons_self
    have hordered : ρ.childPositions.Pairwise (· ≤ ·) :=
      (Ctx.Context.childPositions_pairwise ρ).imp le_of_lt
    have hmin : ∀ p ∈ ρ.childPositions, b ≤ p := by
      intro p hp
      have h := hordered.rel_head hp
      simpa [hcons] using h
    let starts := (List.range ρ.word.length).filter fun p ↦
      ρ.letterAt p = Ctx.Letter.child ∧
        (p = 0 ∨ ρ.letterAt (p - 1) ≠ Ctx.Letter.child)
    have hstartsLen : starts.length ≤ 1 := by
      simpa [starts, Ctx.Context.numRuns] using hruns
    have hstartsNodup : starts.Nodup := by
      exact List.nodup_range.filter _
    have hbRange : b < ρ.word.length := by
      exact List.mem_range.1 (List.mem_filter.1 hb).1
    have hbLetter : ρ.letterAt b = Ctx.Letter.child :=
      of_decide_eq_true (List.mem_filter.1 hb).2
    have hbStartCondition :
        b = 0 ∨ ρ.letterAt (b - 1) ≠ Ctx.Letter.child := by
      by_cases hb0 : b = 0
      · exact Or.inl hb0
      · right
        intro hprev
        have hprevMem : b - 1 ∈ ρ.childPositions := by
          apply List.mem_filter.2
          exact ⟨List.mem_range.2 (by omega), by simpa using hprev⟩
        have := hmin (b - 1) hprevMem
        omega
    have hbStart : b ∈ starts := by
      simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hbRange, hbLetter, hbStartCondition⟩
    have hstartUnique : ∀ p ∈ starts, p = b := by
      intro p hp
      by_contra hpb
      have hsubset : ({b, p} : Finset ℕ) ⊆ starts.toFinset := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact List.mem_toFinset.2 hbStart
        · exact List.mem_toFinset.2 hp
      have hcard := Finset.card_le_card hsubset
      rw [List.toFinset_card_of_nodup hstartsNodup] at hcard
      have htwo : ({b, p} : Finset ℕ).card = 2 := by
        simp [Ne.symm hpb]
      rw [htwo] at hcard
      omega
    have hpred : ∀ p ∈ ρ.childPositions, p ≠ b → p - 1 ∈ ρ.childPositions := by
      intro p hp hpb
      have hpRange : p < ρ.word.length :=
        List.mem_range.1 (List.mem_filter.1 hp).1
      have hpLetter : ρ.letterAt p = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.1 hp).2
      have hpPositive : 0 < p := by
        have := hmin p hp
        omega
      by_contra hprevMem
      have hprevLetter : ρ.letterAt (p - 1) ≠ Ctx.Letter.child := by
        intro hletter
        apply hprevMem
        apply List.mem_filter.2
        exact ⟨List.mem_range.2 (by omega), by simpa using hletter⟩
      have hpStart : p ∈ starts := by
        simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hpRange, hpLetter, Or.inr hprevLetter⟩
      exact hpb (hstartUnique p hpStart)
    have hfill : ∀ p ∈ ρ.childPositions, ∀ q, b ≤ q → q ≤ p →
        q ∈ ρ.childPositions := by
      intro p
      induction p using Nat.strong_induction_on with
      | h p ih =>
        intro hp q hbq hqp
        by_cases hpb : p = b
        · have : q = b := by omega
          simpa [this] using hb
        by_cases hqp' : q = p
        · simpa [hqp'] using hp
        exact ih (p - 1) (by omega) (hpred p hp hpb) q hbq (by omega)
    let e := ρ.childPositions.getLast hchildNe
    have he : e ∈ ρ.childPositions := by
      dsimp [e]
      exact List.getLast_mem _
    have hmax : ∀ p ∈ ρ.childPositions, p ≤ e := by
      intro p hp
      simpa [e] using hordered.rel_getLast hp
    have hbe : b ≤ e := hmin e he
    have hmemRange : ∀ p, p ∈ ρ.childPositions ↔
        p ∈ List.range' b (e + 1 - b) := by
      intro p
      simp only [List.mem_range'_1]
      constructor
      · intro hp
        exact ⟨hmin p hp, by have := hmax p hp; omega⟩
      · rintro ⟨hbp, hp⟩
        exact hfill e he p hbp (by omega)
    have hperm : ρ.childPositions.Perm (List.range' b (e + 1 - b)) :=
      (List.perm_ext_iff_of_nodup (Ctx.Context.childPositions_nodup ρ)
        List.nodup_range').2 hmemRange
    have hrange : ρ.childPositions = List.range' b (e + 1 - b) :=
      List.Perm.eq_of_pairwise' (r := (· ≤ ·)) hordered List.pairwise_le_range' hperm
    have hlen : ρ.childPositions.length = e + 1 - b := by
      rw [hrange]
      simp
    have hinterval : ρ.childPositions = List.range' b ρ.childPositions.length := by
      rw [hlen]
      exact hrange
    exact ⟨b, hinterval⟩

  have hFirstSingleton (σ : Ctx.Context)
    (hpositive : ∀ q j v, σ.letterAt q = Ctx.Letter.ext j v → 1 ≤ j)
    (m : ℕ) (hmax : σ.maxima = [m])
    (s t : Ctx.Side) (hne : s ≠ t) (hside : σ.sideAt 1 = s)
    (p : ℕ) (hhead : σ.childPositions.head? = some p) (hruns : 2 ≤ σ.numRuns)
    (hchosen : 4 + (if (σ.extPositions 1).filter (· < p) = [] then 0 else 1) ≤
      (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s)
    (hchosenK : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ σ.k)
    (hunit : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t = 2)
    (hms : m ≤ σ.k - 3) :
    (σ.part [p] s 1).bound = 1 ∧ σ.bound = 1 := by
    classical
    have hProfile (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [1, m])
      (s : Ctx.Side) (hs1 : σ.sideAt 1 = s) (hs2 : σ.sideAt 2 = s)
      (p : ℕ) (hn : σ.extPositions 1 ≠ [])
      (hfresh : ∀ x ∈ σ.extPositions 1, p < x) :
      let left := if (σ.extPositions 2).filter (· < p) = [] then 0 else 1
      let right := if ∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y then 2 else 1
      σ.leftExt s 0 p = left ∧ σ.rightExt s 0 p = right ∧
        σ.joinExt s p p = max (left + right) (m + 1) ∧
        (∀ t : Ctx.Side, t ≠ s → σ.chainExt t p p = 0 ∧ σ.joinExt t p p = 0) := by
      classical
      let L := if (σ.extPositions 2).filter (· < p) = [] then 0 else 1
      let R := if ∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y then 2 else 1
      change σ.leftExt s 0 p = L ∧ σ.rightExt s 0 p = R ∧
        σ.joinExt s p p = max (L + R) (m + 1) ∧
        (∀ t : Ctx.Side, t ≠ s → σ.chainExt t p p = 0 ∧ σ.joinExt t p p = 0)
      have hlevels : σ.levelsOn s 0 = [1, 2] := by
        simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hs1, hs2, List.range_succ]
      have hbelow : σ.levelsOn s 2 = [1] := by
        simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hs1, hs2, List.range_succ]
      obtain ⟨a, tail, hA⟩ := List.exists_cons_of_ne_nil hn
      have ha : a ∈ σ.extPositions 1 := by rw [hA]; simp
      have hpa : p < a := hfresh a ha
      have hsorted : (σ.extPositions 1).Pairwise (· ≤ ·) :=
        (List.pairwise_lt_range.filter _).imp le_of_lt
      have hmin : ∀ x ∈ σ.extPositions 1, a ≤ x := by
        intro x hx
        simpa [hA] using hsorted.rel_head hx
      have hleftA : (σ.extPositions 1).filter (· < p) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        have hp := hfresh x hx
        simp only [decide_eq_true_eq]
        omega
      have hrightA : (σ.extPositions 1).filter (p < ·) = σ.extPositions 1 := by
        apply List.filter_eq_self.mpr
        intro x hx
        simpa using hfresh x hx
      have hheadA : ((σ.extPositions 1).filter (p < ·)).head? = some a := by
        rw [hrightA, hA]
        rfl
      have hthread : (∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y) ↔
          (σ.extPositions 2).filter (a < ·) ≠ [] := by
        constructor
        · rintro ⟨x, hx, y, hy, hxy⟩
          have hxy' : a < y := lt_of_le_of_lt (hmin x hx) hxy
          exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hy, by simpa using hxy'⟩)
        · intro hne
          obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
          exact ⟨a, ha, y, (List.mem_filter.mp hy).1,
            of_decide_eq_true (List.mem_filter.mp hy).2⟩
      have hleft : σ.leftExt s 0 p = L := by
        cases hB : ((σ.extPositions 2).filter (· < p)).getLast? with
        | none =>
          have he : (σ.extPositions 2).filter (· < p) = [] := List.getLast?_eq_none_iff.mp hB
          simp [Ctx.Context.leftExt_eq, hlevels, Ctx.Context.leftStep,
            List.sublists_cons, hleftA, hB, L, he,
            -List.getLast?_filter, -List.getLast_filter]
        | some b =>
          have hne : (σ.extPositions 2).filter (· < p) ≠ [] := by
            intro he
            simp [he] at hB
          simp [Ctx.Context.leftExt_eq, hlevels, Ctx.Context.leftStep,
            List.sublists_cons, hleftA, hB, L, hne,
            -List.getLast?_filter, -List.getLast_filter]
      have hright : σ.rightExt s 0 p = R := by
        cases hB : ((σ.extPositions 2).filter (p < ·)).head? with
        | none =>
          cases hC : ((σ.extPositions 2).filter (a < ·)).head? with
          | none =>
            have he : (σ.extPositions 2).filter (a < ·) = [] := List.head?_eq_none_iff.mp hC
            have ht : ¬(∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y) := by
              intro ht
              exact (hthread.mp ht) he
            simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
              List.sublists_cons, hheadA, hB, hC, R, ht,
              -List.head?_filter, -List.head_filter]
          | some c =>
            have hne : (σ.extPositions 2).filter (a < ·) ≠ [] := by
              intro he
              simp [he] at hC
            have ht := hthread.mpr hne
            simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
              List.sublists_cons, hheadA, hB, hC, R, ht,
              -List.head?_filter, -List.head_filter]
        | some b =>
          cases hC : ((σ.extPositions 2).filter (a < ·)).head? with
          | none =>
            have he : (σ.extPositions 2).filter (a < ·) = [] := List.head?_eq_none_iff.mp hC
            have ht : ¬(∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y) := by
              intro ht
              exact (hthread.mp ht) he
            simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
              List.sublists_cons, hheadA, hB, hC, R, ht,
              -List.head?_filter, -List.head_filter]
          | some c =>
            have hne : (σ.extPositions 2).filter (a < ·) ≠ [] := by
              intro he
              simp [he] at hC
            have ht := hthread.mpr hne
            simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
              List.sublists_cons, hheadA, hB, hC, R, ht,
              -List.head?_filter, -List.head_filter]
      have hleftBelow : σ.leftExt s 2 p = 0 := by
        simp [Ctx.Context.leftExt_eq, hbelow, Ctx.Context.leftStep, hleftA,
          -List.getLast?_filter]
      have hrightBelow : σ.rightExt s 2 p = 1 := by
        simp [Ctx.Context.rightExt_eq, hbelow, Ctx.Context.rightStep, hheadA,
          -List.head?_filter]
      have hchain : σ.chainExt s p p = L + R := by
        simp only [Ctx.Context.chainExt, hleft, hright]
      have hjoin : σ.joinExt s p p = max (L + R) (m + 1) := by
        simp [Ctx.Context.joinExt, hlevels, hchain, Ctx.Context.leftExt_one,
          Ctx.Context.rightExt_one, hleftBelow, hrightBelow,
          Ctx.Context.maximumAt, hmax, Nat.add_comm]
      refine ⟨hleft, hright, hjoin, ?_⟩
      intro t ht
      have hs : s ≠ t := Ne.symm ht
      have hother : σ.levelsOn t 0 = [] := by
        simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hs1, hs2, hs, List.range_succ]
      have hc : σ.chainExt t p p = 0 := by
        simp [Ctx.Context.chainExt, Ctx.Context.leftExt_eq, Ctx.Context.rightExt_eq, hother]
      exact ⟨hc, by simp [Ctx.Context.joinExt, hother, hc]⟩
    have hGlobalTwo (ρ : Ctx.Context)
        (hpositive : ∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
        (s : Ctx.Side)
        (hglobal : (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) s ≤ 2) :
        ρ.bound ≤ 1 := by
      have hrank : ∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p → 0 < ρ.capLimit p p →
          ρ.leftExt s 0 p + 1 = 1 ∧
            1 + ρ.rightExt s 0 p =
              (fun v : Ctx.Side => match v with
                | Ctx.Side.lower => ρ.u - 1 | Ctx.Side.upper => ρ.a - 1) s := by
        intro p hp hc ha
        cases s with
        | lower =>
          change ρ.u ≤ 2 at hglobal
          change ρ.leftExt Ctx.Side.lower 0 p + 1 = 1 ∧
            1 + ρ.rightExt Ctx.Side.lower 0 p = ρ.u - 1
          have hh := Nat.min_le_left (ρ.u - 1 - ρ.chainExt Ctx.Side.lower p p)
            (ρ.k - 1 - ρ.joinExt Ctx.Side.lower p p)
          change ρ.cupLimit p p ≤ ρ.u - 1 -
            (ρ.leftExt Ctx.Side.lower 0 p + ρ.rightExt Ctx.Side.lower 0 p) at hh
          constructor <;> omega
        | upper =>
          change ρ.a ≤ 2 at hglobal
          change ρ.leftExt Ctx.Side.upper 0 p + 1 = 1 ∧
            1 + ρ.rightExt Ctx.Side.upper 0 p = ρ.a - 1
          have hh := Nat.min_le_left (ρ.a - 1 - ρ.chainExt Ctx.Side.upper p p)
            (ρ.k - 1 - ρ.joinExt Ctx.Side.upper p p)
          change ρ.capLimit p p ≤ ρ.a - 1 -
            (ρ.leftExt Ctx.Side.upper 0 p + ρ.rightExt Ctx.Side.upper 0 p) at hh
          constructor <;> omega
      exact (ctx_bound_le_one_of_common_singleton_rank ρ hpositive s 1 hrank).2.1
    let left := if (σ.extPositions 1).filter (· < p) = [] then 0 else 1
    change 4 + left ≤ (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s at hchosen
    have hk : 4 + left ≤ σ.k := le_trans hchosen hchosenK
    have hcount : 2 ≤ σ.childPositions.length :=
      le_trans hruns (Ctx.numRuns_le_length σ)
    obtain ⟨tail, hcons⟩ := List.head?_eq_some_iff.mp hhead
    have hpnot : p ∉ tail := by
      have hn := Ctx.Context.childPositions_nodup σ
      rw [hcons] at hn
      exact (List.nodup_cons.mp hn).1
    have hTailRight : ∀ q ∈ tail, p < q := by
      have hs := Ctx.Context.childPositions_pairwise σ
      rw [hcons] at hs
      exact (List.pairwise_cons.mp hs).1
    have htailNe : tail ≠ [] := by
      intro hnil
      rw [hcons, hnil] at hcount
      simp at hcount
    let τ := σ.part [p] s 1
    have hKeepTail : tail.filter (fun q => q ∈ [p]) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq
      have hqp : q ≠ p := by
        intro he
        subst q
        exact hpnot hq
      simpa using hqp
    have hτchildren : τ.childPositions = [p] := by
      rw [Ctx.Context.part_childPositions, hcons, List.filter_cons, hKeepTail]
      simp
    have hRemoveTail : tail.filter (fun q => q ∉ [p]) = tail := by
      apply List.filter_eq_self.mpr
      intro q hq
      have hqp : q ≠ p := by
        intro he
        subst q
        exact hpnot hq
      simpa using hqp
    have hτfresh : τ.extPositions 1 = tail := by
      rw [Ctx.Context.part_extPositions_one hpositive [p] s 1,
        hcons, List.filter_cons, hRemoveTail]
      simp
    have hτold : τ.extPositions 2 = σ.extPositions 1 :=
      Ctx.Context.part_extPositions_succ σ [p] s 1 (by omega : 1 ≤ 1)
    have hblock : [p] ∈ σ.blocks := by
      simp only [Ctx.Context.blocks, List.mem_filter, List.mem_flatMap,
        List.mem_range, List.mem_map, decide_eq_true_eq]
      refine ⟨⟨0, by omega, 0, by omega, ?_⟩, ?_⟩
      · simp [hcons]
      · simp only [List.length_singleton]
        omega
    have hτruns : τ.numRuns ≤ 1 := by
      have h := Ctx.numRuns_le_length τ
      simpa only [hτchildren, List.length_singleton] using h
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ htailNe
    have hFreshWitness : q ∈ τ.extPositions 1 := by rw [hτfresh]; exact hq
    have hs1 : τ.sideAt 1 = s :=
      Ctx.Context.part_sideAt_one_of_mem hpositive [p] s 1 hFreshWitness
    have hs2 : τ.sideAt 2 = s :=
      (Ctx.Context.part_sideAt_succ σ [p] s 1 (by omega : 1 ≤ 1)).trans hside
    have hmaxτ : τ.maxima = [1, m] := by simp [τ, Ctx.Context.part, hmax]
    have hFreshRight : ∀ q ∈ τ.extPositions 1, p < q := by
      intro q hq
      rw [hτfresh] at hq
      exact hTailRight q hq
    have hProfileAt := hProfile τ m hmaxτ s hs1 hs2 p
      (List.ne_nil_of_mem hFreshWitness) hFreshRight
    dsimp only at hProfileAt
    have hLeft : τ.leftExt s 0 p = left := by
      simpa only [hτold, left] using hProfileAt.1
    have hRight : τ.rightExt s 0 p ≤ 2 := by
      rw [hProfileAt.2.1]
      split_ifs <;> omega
    have hChain : τ.chainExt s p p ≤ left + 2 := by
      change τ.leftExt s 0 p + τ.rightExt s 0 p ≤ left + 2
      rw [hLeft]
      omega
    have hJoinEq : τ.joinExt s p p = max (τ.chainExt s p p) (m + 1) := by
      rw [hProfileAt.2.2.1]
      simp only [Ctx.Context.chainExt, hProfileAt.1, hProfileAt.2.1]
    have hJoin : τ.joinExt s p p ≤ σ.k - 2 := by
      rw [hJoinEq]
      apply Nat.max_le.mpr
      constructor <;> omega
    have hOpp := hProfileAt.2.2.2 t (Ne.symm hne)
    have hChosenLimit : 1 ≤ (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => τ.cupLimit p p | Ctx.Side.upper => τ.capLimit p p) s := by
      cases hs : s with
      | lower =>
        have hg : 4 + left ≤ σ.u := by simpa only [hs] using hchosen
        have hc : τ.chainExt Ctx.Side.lower p p ≤ left + 2 := by simpa only [hs] using hChain
        have hj : τ.joinExt Ctx.Side.lower p p ≤ σ.k - 2 := by simpa only [hs] using hJoin
        change 1 ≤ min (σ.u - 1 - τ.chainExt Ctx.Side.lower p p)
          (σ.k - 1 - τ.joinExt Ctx.Side.lower p p)
        apply Nat.le_min.mpr
        constructor <;> omega
      | upper =>
        have hg : 4 + left ≤ σ.a := by simpa only [hs] using hchosen
        have hc : τ.chainExt Ctx.Side.upper p p ≤ left + 2 := by simpa only [hs] using hChain
        have hj : τ.joinExt Ctx.Side.upper p p ≤ σ.k - 2 := by simpa only [hs] using hJoin
        change 1 ≤ min (σ.a - 1 - τ.chainExt Ctx.Side.upper p p)
          (σ.k - 1 - τ.joinExt Ctx.Side.upper p p)
        apply Nat.le_min.mpr
        constructor <;> omega
    have hOppLimit : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => τ.cupLimit p p | Ctx.Side.upper => τ.capLimit p p) t = 1 := by
      cases ht : t with
      | lower =>
        have hg : σ.u = 2 := by simpa only [ht] using hunit
        have hc : τ.chainExt Ctx.Side.lower p p = 0 := by simpa only [ht] using hOpp.1
        have hj : τ.joinExt Ctx.Side.lower p p = 0 := by simpa only [ht] using hOpp.2
        change min (σ.u - 1 - τ.chainExt Ctx.Side.lower p p)
          (σ.k - 1 - τ.joinExt Ctx.Side.lower p p) = 1
        rw [hg, hc, hj]
        change min 1 (σ.k - 1) = 1
        exact Nat.min_eq_left (by omega)
      | upper =>
        have hg : σ.a = 2 := by simpa only [ht] using hunit
        have hc : τ.chainExt Ctx.Side.upper p p = 0 := by simpa only [ht] using hOpp.1
        have hj : τ.joinExt Ctx.Side.upper p p = 0 := by simpa only [ht] using hOpp.2
        change min (σ.a - 1 - τ.chainExt Ctx.Side.upper p p)
          (σ.k - 1 - τ.joinExt Ctx.Side.upper p p) = 1
        rw [hg, hc, hj]
        change min 1 (σ.k - 1) = 1
        exact Nat.min_eq_left (by omega)
    have hτhead : τ.childPositions.head? = some p := by rw [hτchildren]; rfl
    have hBase : τ.base = 1 := by
      cases hs : s with
      | lower =>
        have ht : t = Ctx.Side.upper := by
          cases t with
          | lower => exact (hne hs).elim
          | upper => rfl
        have hcPos : 1 ≤ τ.cupLimit p p := by simpa only [hs] using hChosenLimit
        have hc : τ.cupLimit p p ≠ 0 := by omega
        have ha : τ.capLimit p p = 1 := by simpa only [ht] using hOppLimit
        simp [Ctx.Context.base, hτhead, hc, ha]
      | upper =>
        have ht : t = Ctx.Side.lower := by
          cases t with
          | lower => rfl
          | upper => exact (hne hs).elim
        have hcPos : 1 ≤ τ.capLimit p p := by simpa only [hs] using hChosenLimit
        have hc : τ.capLimit p p ≠ 0 := by omega
        have hu : τ.cupLimit p p = 1 := by simpa only [ht] using hOppLimit
        simp [Ctx.Context.base, hτhead, hc, hu]
    have hPart : τ.bound = 1 := by
      unfold Ctx.Context.bound
      rw [Ctx.Context.boundFuel.eq_2, if_pos hτruns]
      exact hBase
    refine ⟨hPart, Nat.le_antisymm (hGlobalTwo σ hpositive t hunit.le) ?_⟩
    cases hs : s with
    | lower =>
      have hCut := (ctx_bound_cut_le σ hruns [p] hblock 1 (by omega) (by omega)).1
      have hτ : (σ.part [p] Ctx.Side.lower 1).bound = 1 :=
        by simpa only [τ, hs] using hPart
      rw [hτ] at hCut
      omega
    | upper =>
      have hCut := (ctx_bound_cut_le σ hruns [p] hblock (σ.k - 2) (by omega) le_rfl).2
      have hc : σ.k - 1 - (σ.k - 2) = 1 := by omega
      rw [hc] at hCut
      have hτ : (σ.part [p] Ctx.Side.upper 1).bound = 1 :=
        by simpa only [τ, hs] using hPart
      rw [hτ] at hCut
      omega

  have hRootPositive (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
      (s t : Ctx.Side) (hne : s ≠ t)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 2 ≤ σ.numRuns)
      (hchosen : 4 + (if σ.word.head? = some (Ctx.Letter.ext 1 s) then 1 else 0) ≤
        (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s)
      (hchosenK : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ σ.k)
      (hunit : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t = 2)
      (hms : m ≤ σ.k - 3) : σ.bound = 1 := by
    classical
    let marker := Ctx.Letter.ext 1 s
    have hAt (q : ℕ) (hq : q < σ.word.length) :
        σ.letterAt q = Ctx.Letter.child ∨ σ.letterAt q = marker := by
      have he : σ.letterAt q = σ.word[q] := by
        simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hq]
      rw [he]
      exact hletters _ (List.getElem_mem hq)
    have hExtMem (q : ℕ) (hq : q < σ.word.length)
        (he : σ.letterAt q = marker) : q ∈ σ.extPositions 1 := by
      simp [Ctx.Context.extPositions, hq, he, marker]
    have hOldAt (q : ℕ) (hq : q ∈ σ.extPositions 1) : σ.letterAt q = marker := by
      have hqR := List.mem_range.mp (List.mem_filter.mp hq).1
      rcases hAt q hqR with hc | hm
      · simp [Ctx.Context.extPositions, hc] at hq
      · exact hm
    have hpositive : ∀ q j v, σ.letterAt q = Ctx.Letter.ext j v → 1 ≤ j := by
      intro q j v he
      have hqR : q < σ.word.length := by
        by_contra hn
        rw [Ctx.Context.letterAt_of_length_le σ (by omega)] at he
        cases he
      rcases hAt q hqR with hc | hm
      · rw [hc] at he
        cases he
      · rw [hm] at he
        have hj : 1 = j := (Ctx.Letter.ext.inj he).1
        omega
    obtain ⟨first, sep, other, hfirst, hother, hFirstSep, hSepOther, hSep⟩ :=
      hTwoSites σ s hletters hruns
    have hSepR : sep < σ.word.length := by
      have hh := List.mem_range.mp (List.mem_filter.mp hother).1
      omega
    have hSepMem : sep ∈ σ.extPositions 1 := hExtMem sep hSepR hSep
    obtain ⟨x, oldTail, hOldCons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hSepMem)
    have hxOld : x ∈ σ.extPositions 1 := by rw [hOldCons]; exact List.mem_cons_self
    have hxAt := hOldAt x hxOld
    have hside : σ.sideAt 1 = s := by
      simp [Ctx.Context.sideAt, hOldCons, hxAt, marker]
    obtain ⟨p, tail, hcons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hfirst)
    have hp : p ∈ σ.childPositions := by rw [hcons]; exact List.mem_cons_self
    have hpR : p < σ.word.length := List.mem_range.mp (List.mem_filter.mp hp).1
    have hpAt : σ.letterAt p = Ctx.Letter.child :=
      of_decide_eq_true (List.mem_filter.mp hp).2
    have hpMin : ∀ q ∈ σ.childPositions, p ≤ q := by
      intro q hq
      have hs : σ.childPositions.Pairwise (· ≤ ·) :=
        (Ctx.Context.childPositions_pairwise σ).imp le_of_lt
      simpa [hcons] using hs.rel_head hq
    have hLeft : (if (σ.extPositions 1).filter (· < p) = [] then 0 else 1) =
        (if σ.word.head? = some marker then 1 else 0) := by
      by_cases hheadMarker : σ.word.head? = some marker
      · obtain ⟨wordTail, hword⟩ := List.head?_eq_some_iff.mp hheadMarker
        have hZero : σ.letterAt 0 = marker := by simp [Ctx.Context.letterAt, hword]
        have hZeroR : 0 < σ.word.length := by rw [hword]; simp
        have hpPos : 0 < p := by
          have hpNe : p ≠ 0 := by
            intro he
            rw [he, hZero] at hpAt
            simp [marker] at hpAt
          omega
        have hZeroMem := hExtMem 0 hZeroR hZero
        have hnonempty : (σ.extPositions 1).filter (· < p) ≠ [] :=
          List.ne_nil_of_mem (List.mem_filter.mpr ⟨hZeroMem, by simpa using hpPos⟩)
        simp only [if_neg hnonempty, if_pos hheadMarker]
      · have hwordNe : σ.word ≠ [] := by
          intro he
          rw [he] at hpR
          simp at hpR
        obtain ⟨v, wordTail, hword⟩ := List.exists_cons_of_ne_nil hwordNe
        have hv : v = Ctx.Letter.child := by
          rcases hletters v (by rw [hword]; simp) with hc | hm
          · exact hc
          · have hbad : σ.word.head? = some marker := by simp [hword, hm, marker]
            exact (hheadMarker hbad).elim
        have hZeroAt : σ.letterAt 0 = Ctx.Letter.child := by
          simp [Ctx.Context.letterAt, hword, hv]
        have hZeroMem : 0 ∈ σ.childPositions := by
          simp [Ctx.Context.childPositions, hword, hZeroAt]
        have hpZero : p = 0 := by have hh := hpMin 0 hZeroMem; omega
        simp [hpZero, hheadMarker]
    have hhead : σ.childPositions.head? = some p := by rw [hcons]; rfl
    have hChosen' : 4 + (if (σ.extPositions 1).filter (· < p) = [] then 0 else 1) ≤
        (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s := by
      rw [hLeft]
      exact hchosen
    exact (hFirstSingleton σ hpositive m hmax s t hne hside p hhead hruns
      hChosen' hchosenK hunit hms).2

  have hTwoRunsPositive (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
    (s t : Ctx.Side) (hne : s ≠ t)
    (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
    (hhead : σ.word.head? = some Ctx.Letter.child)
    (hlast : σ.word.getLast? = some Ctx.Letter.child)
    (hrunsEq : σ.numRuns = 2)
    (hchosen : 3 ≤ (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s)
    (hchosenK : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ σ.k)
    (hunit : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t = 2)
    (hms : m ≤ σ.k - 3) : σ.bound = 1 := by
    classical
    have hProfile (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [1, m])
      (s : Ctx.Side) (hs1 : σ.sideAt 1 = s) (hs2 : σ.sideAt 2 = s)
      (p : ℕ) (hn : σ.extPositions 1 ≠ [])
      (hfresh : ∀ x ∈ σ.extPositions 1, p < x) :
      let left := if (σ.extPositions 2).filter (· < p) = [] then 0 else 1
      let right := if ∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y then 2 else 1
      σ.leftExt s 0 p = left ∧ σ.rightExt s 0 p = right ∧
        σ.joinExt s p p = max (left + right) (m + 1) ∧
        (∀ t : Ctx.Side, t ≠ s → σ.chainExt t p p = 0 ∧ σ.joinExt t p p = 0) := by
      classical
      let L := if (σ.extPositions 2).filter (· < p) = [] then 0 else 1
      let R := if ∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y then 2 else 1
      change σ.leftExt s 0 p = L ∧ σ.rightExt s 0 p = R ∧
        σ.joinExt s p p = max (L + R) (m + 1) ∧
        (∀ t : Ctx.Side, t ≠ s → σ.chainExt t p p = 0 ∧ σ.joinExt t p p = 0)
      have hlevels : σ.levelsOn s 0 = [1, 2] := by
        simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hs1, hs2, List.range_succ]
      have hbelow : σ.levelsOn s 2 = [1] := by
        simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hs1, hs2, List.range_succ]
      obtain ⟨a, tail, hA⟩ := List.exists_cons_of_ne_nil hn
      have ha : a ∈ σ.extPositions 1 := by rw [hA]; simp
      have hpa : p < a := hfresh a ha
      have hsorted : (σ.extPositions 1).Pairwise (· ≤ ·) :=
        (List.pairwise_lt_range.filter _).imp le_of_lt
      have hmin : ∀ x ∈ σ.extPositions 1, a ≤ x := by
        intro x hx
        simpa [hA] using hsorted.rel_head hx
      have hleftA : (σ.extPositions 1).filter (· < p) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        have hp := hfresh x hx
        simp only [decide_eq_true_eq]
        omega
      have hrightA : (σ.extPositions 1).filter (p < ·) = σ.extPositions 1 := by
        apply List.filter_eq_self.mpr
        intro x hx
        simpa using hfresh x hx
      have hheadA : ((σ.extPositions 1).filter (p < ·)).head? = some a := by
        rw [hrightA, hA]
        rfl
      have hthread : (∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y) ↔
          (σ.extPositions 2).filter (a < ·) ≠ [] := by
        constructor
        · rintro ⟨x, hx, y, hy, hxy⟩
          have hxy' : a < y := lt_of_le_of_lt (hmin x hx) hxy
          exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hy, by simpa using hxy'⟩)
        · intro hne
          obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
          exact ⟨a, ha, y, (List.mem_filter.mp hy).1,
            of_decide_eq_true (List.mem_filter.mp hy).2⟩
      have hleft : σ.leftExt s 0 p = L := by
        cases hB : ((σ.extPositions 2).filter (· < p)).getLast? with
        | none =>
          have he : (σ.extPositions 2).filter (· < p) = [] := List.getLast?_eq_none_iff.mp hB
          simp [Ctx.Context.leftExt_eq, hlevels, Ctx.Context.leftStep,
            List.sublists_cons, hleftA, hB, L, he,
            -List.getLast?_filter, -List.getLast_filter]
        | some b =>
          have hne : (σ.extPositions 2).filter (· < p) ≠ [] := by
            intro he
            simp [he] at hB
          simp [Ctx.Context.leftExt_eq, hlevels, Ctx.Context.leftStep,
            List.sublists_cons, hleftA, hB, L, hne,
            -List.getLast?_filter, -List.getLast_filter]
      have hright : σ.rightExt s 0 p = R := by
        cases hB : ((σ.extPositions 2).filter (p < ·)).head? with
        | none =>
          cases hC : ((σ.extPositions 2).filter (a < ·)).head? with
          | none =>
            have he : (σ.extPositions 2).filter (a < ·) = [] := List.head?_eq_none_iff.mp hC
            have ht : ¬(∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y) := by
              intro ht
              exact (hthread.mp ht) he
            simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
              List.sublists_cons, hheadA, hB, hC, R, ht,
              -List.head?_filter, -List.head_filter]
          | some c =>
            have hne : (σ.extPositions 2).filter (a < ·) ≠ [] := by
              intro he
              simp [he] at hC
            have ht := hthread.mpr hne
            simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
              List.sublists_cons, hheadA, hB, hC, R, ht,
              -List.head?_filter, -List.head_filter]
        | some b =>
          cases hC : ((σ.extPositions 2).filter (a < ·)).head? with
          | none =>
            have he : (σ.extPositions 2).filter (a < ·) = [] := List.head?_eq_none_iff.mp hC
            have ht : ¬(∃ x ∈ σ.extPositions 1, ∃ y ∈ σ.extPositions 2, x < y) := by
              intro ht
              exact (hthread.mp ht) he
            simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
              List.sublists_cons, hheadA, hB, hC, R, ht,
              -List.head?_filter, -List.head_filter]
          | some c =>
            have hne : (σ.extPositions 2).filter (a < ·) ≠ [] := by
              intro he
              simp [he] at hC
            have ht := hthread.mpr hne
            simp [Ctx.Context.rightExt_eq, hlevels, Ctx.Context.rightStep,
              List.sublists_cons, hheadA, hB, hC, R, ht,
              -List.head?_filter, -List.head_filter]
      have hleftBelow : σ.leftExt s 2 p = 0 := by
        simp [Ctx.Context.leftExt_eq, hbelow, Ctx.Context.leftStep, hleftA,
          -List.getLast?_filter]
      have hrightBelow : σ.rightExt s 2 p = 1 := by
        simp [Ctx.Context.rightExt_eq, hbelow, Ctx.Context.rightStep, hheadA,
          -List.head?_filter]
      have hchain : σ.chainExt s p p = L + R := by
        simp only [Ctx.Context.chainExt, hleft, hright]
      have hjoin : σ.joinExt s p p = max (L + R) (m + 1) := by
        simp [Ctx.Context.joinExt, hlevels, hchain, Ctx.Context.leftExt_one,
          Ctx.Context.rightExt_one, hleftBelow, hrightBelow,
          Ctx.Context.maximumAt, hmax, Nat.add_comm]
      refine ⟨hleft, hright, hjoin, ?_⟩
      intro t ht
      have hs : s ≠ t := Ne.symm ht
      have hother : σ.levelsOn t 0 = [] := by
        simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hs1, hs2, hs, List.range_succ]
      have hc : σ.chainExt t p p = 0 := by
        simp [Ctx.Context.chainExt, Ctx.Context.leftExt_eq, Ctx.Context.rightExt_eq, hother]
      exact ⟨hc, by simp [Ctx.Context.joinExt, hother, hc]⟩
    have hGlobalTwo (ρ : Ctx.Context)
        (hpositive : ∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
        (s : Ctx.Side)
        (hglobal : (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) s ≤ 2) :
        ρ.bound ≤ 1 := by
      have hrank : ∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p → 0 < ρ.capLimit p p →
          ρ.leftExt s 0 p + 1 = 1 ∧
            1 + ρ.rightExt s 0 p =
              (fun v : Ctx.Side => match v with
                | Ctx.Side.lower => ρ.u - 1 | Ctx.Side.upper => ρ.a - 1) s := by
        intro p hp hc ha
        cases s with
        | lower =>
          change ρ.u ≤ 2 at hglobal
          change ρ.leftExt Ctx.Side.lower 0 p + 1 = 1 ∧
            1 + ρ.rightExt Ctx.Side.lower 0 p = ρ.u - 1
          have hh := Nat.min_le_left (ρ.u - 1 - ρ.chainExt Ctx.Side.lower p p)
            (ρ.k - 1 - ρ.joinExt Ctx.Side.lower p p)
          change ρ.cupLimit p p ≤ ρ.u - 1 -
            (ρ.leftExt Ctx.Side.lower 0 p + ρ.rightExt Ctx.Side.lower 0 p) at hh
          constructor <;> omega
        | upper =>
          change ρ.a ≤ 2 at hglobal
          change ρ.leftExt Ctx.Side.upper 0 p + 1 = 1 ∧
            1 + ρ.rightExt Ctx.Side.upper 0 p = ρ.a - 1
          have hh := Nat.min_le_left (ρ.a - 1 - ρ.chainExt Ctx.Side.upper p p)
            (ρ.k - 1 - ρ.joinExt Ctx.Side.upper p p)
          change ρ.capLimit p p ≤ ρ.a - 1 -
            (ρ.leftExt Ctx.Side.upper 0 p + ρ.rightExt Ctx.Side.upper 0 p) at hh
          constructor <;> omega
      exact (ctx_bound_le_one_of_common_singleton_rank ρ hpositive s 1 hrank).2.1
    have hTwoSites (σ : Ctx.Context) (s : Ctx.Side)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 2 ≤ σ.numRuns) :
      ∃ x l y,
        x ∈ σ.childPositions ∧ y ∈ σ.childPositions ∧
        x < l ∧ l < y ∧ σ.letterAt l = Ctx.Letter.ext 1 s := by
      classical
      let starts := (List.range σ.word.length).filter fun p =>
        σ.letterAt p = Ctx.Letter.child ∧
          (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child)
      have hlen : 2 ≤ starts.length := hruns
      have hsort : starts.Pairwise (· < ·) := List.pairwise_lt_range.filter _
      have hData (p : ℕ) (hp : p ∈ starts) :
          p < σ.word.length ∧ σ.letterAt p = Ctx.Letter.child ∧
            (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child) := by
        simpa only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq] using hp
      have hChild (p : ℕ) (hp : p ∈ starts) : p ∈ σ.childPositions := by
        have hd := hData p hp
        simp [Ctx.Context.childPositions, hd.1, hd.2.1]
      have hLetter (p : ℕ) (hp : p < σ.word.length) :
          σ.letterAt p = Ctx.Letter.child ∨ σ.letterAt p = Ctx.Letter.ext 1 s := by
        have he : σ.letterAt p = σ.word[p] := by
          simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hp]
        rw [he]
        exact hletters _ (List.getElem_mem hp)
      cases hs : starts with
      | nil => simp [hs] at hlen
      | cons x xs =>
        cases hxs : xs with
        | nil => simp [hs, hxs] at hlen
        | cons y ys =>
          have hform : starts = x :: y :: ys := by rw [hs, hxs]
          have hx : x ∈ starts := by rw [hform]; simp
          have hy : y ∈ starts := by rw [hform]; simp
          have hsort' : (x :: y :: ys).Pairwise (· < ·) := by rw [← hform]; exact hsort
          have hxy : x < y := (List.pairwise_cons.mp hsort').1 _ (by simp)
          have hxD := hData x hx
          have hyD := hData y hy
          have hlnot : σ.letterAt (y - 1) ≠ Ctx.Letter.child := by
            rcases hyD.2.2 with h0 | hno
            · omega
            · exact hno
          have hl : σ.letterAt (y - 1) = Ctx.Letter.ext 1 s :=
            (hLetter (y - 1) (by omega)).resolve_left hlnot
          have hxl : x < y - 1 := by
            have hne : x ≠ y - 1 := by
              intro he
              rw [he, hl] at hxD
              cases hxD.2.1
            omega
          exact ⟨x, y - 1, y, hChild x hx, hChild y hy, hxl, by omega, hl⟩
    have hThreeSites (σ : Ctx.Context) (x l y r z : ℕ)
      (hx : x ∈ σ.childPositions) (hy : y ∈ σ.childPositions)
      (hz : z ∈ σ.childPositions)
      (hl : σ.letterAt l ≠ Ctx.Letter.child)
      (hr : σ.letterAt r ≠ Ctx.Letter.child)
      (hxl : x < l) (hly : l < y) (hyr : y < r) (hrz : r < z) :
      3 ≤ σ.numRuns := by
      classical
      let starts := (List.range σ.word.length).filter fun p =>
        σ.letterAt p = Ctx.Letter.child ∧
          (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child)
      have hAfter (v : ℕ) (hv : σ.letterAt v ≠ Ctx.Letter.child) :
          ∀ p ∈ σ.childPositions, v < p → ∃ q ∈ starts, v < q ∧ q ≤ p := by
        intro p
        induction p using Nat.strong_induction_on with
        | h p ih =>
          intro hp hvp
          have hpR : p < σ.word.length := List.mem_range.mp (List.mem_filter.mp hp).1
          have hpC : σ.letterAt p = Ctx.Letter.child :=
            of_decide_eq_true (List.mem_filter.mp hp).2
          by_cases hstart : p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child
          · refine ⟨p, ?_, hvp, le_rfl⟩
            simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
            exact ⟨hpR, hpC, hstart⟩
          have hp0 : p ≠ 0 := fun he => hstart (Or.inl he)
          have hprev : σ.letterAt (p - 1) = Ctx.Letter.child := by
            by_contra hn
            exact hstart (Or.inr hn)
          have hprevMem : p - 1 ∈ σ.childPositions := by
            apply List.mem_filter.mpr
            exact ⟨List.mem_range.mpr (by omega), by simpa using hprev⟩
          have hvprev : v < p - 1 := by
            have hne : v ≠ p - 1 := by
              intro he
              rw [← he] at hprev
              exact hv hprev
            omega
          obtain ⟨q, hq, hvq, hqp⟩ := ih (p - 1) (by omega) hprevMem hvprev
          exact ⟨q, hq, hvq, by omega⟩
      obtain ⟨b, tail, hcons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hx)
      have hb : b ∈ σ.childPositions := by rw [hcons]; exact List.mem_cons_self
      have hsorted : σ.childPositions.Pairwise (· ≤ ·) :=
        (Ctx.Context.childPositions_pairwise σ).imp le_of_lt
      have hmin : ∀ p ∈ σ.childPositions, b ≤ p := by
        intro p hp
        have hh := hsorted.rel_head hp
        simpa [hcons] using hh
      have hbR : b < σ.word.length := List.mem_range.mp (List.mem_filter.mp hb).1
      have hbC : σ.letterAt b = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hb).2
      have hbStart : b = 0 ∨ σ.letterAt (b - 1) ≠ Ctx.Letter.child := by
        by_cases hb0 : b = 0
        · exact Or.inl hb0
        · right
          intro hprev
          have hprevMem : b - 1 ∈ σ.childPositions := by
            apply List.mem_filter.mpr
            exact ⟨List.mem_range.mpr (by omega), by simpa using hprev⟩
          have hh := hmin (b - 1) hprevMem
          omega
      have hbStarts : b ∈ starts := by
        simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hbR, hbC, hbStart⟩
      obtain ⟨c, hc, hlc, hcy⟩ := hAfter l hl y hy hly
      obtain ⟨d, hd, hrd, hdz⟩ := hAfter r hr z hz hrz
      have hbx := hmin x hx
      have hbc : b < c := by omega
      have hbd : b < d := by omega
      have hcd : c < d := by omega
      have hsub : ({b, c, d} : Finset ℕ) ⊆ starts.toFinset := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · exact List.mem_toFinset.mpr hbStarts
        · exact List.mem_toFinset.mpr hc
        · exact List.mem_toFinset.mpr hd
      have hcard := Finset.card_le_card hsub
      have hthree : ({b, c, d} : Finset ℕ).card = 3 := by
        simp [ne_of_lt hbc, ne_of_lt hbd, ne_of_lt hcd]
      have hn : starts.Nodup := List.nodup_range.filter _
      rw [hthree, List.toFinset_card_of_nodup hn] at hcard
      exact hcard
    have hruns : 2 ≤ σ.numRuns := by omega
    have hk : 3 ≤ σ.k := le_trans hchosen hchosenK
    let marker := Ctx.Letter.ext 1 s
    have hAt (q : ℕ) (hq : q < σ.word.length) :
        σ.letterAt q = Ctx.Letter.child ∨ σ.letterAt q = marker := by
      have he : σ.letterAt q = σ.word[q] := by
        simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hq]
      rw [he]
      exact hletters _ (List.getElem_mem hq)
    have hExtMem (q : ℕ) (hq : q < σ.word.length)
        (he : σ.letterAt q = marker) : q ∈ σ.extPositions 1 := by
      simp [Ctx.Context.extPositions, hq, he, marker]
    have hOldAt (q : ℕ) (hq : q ∈ σ.extPositions 1) : σ.letterAt q = marker := by
      have hqR := List.mem_range.mp (List.mem_filter.mp hq).1
      rcases hAt q hqR with hc | hm
      · simp [Ctx.Context.extPositions, hc] at hq
      · exact hm
    have hpositive : ∀ q j v, σ.letterAt q = Ctx.Letter.ext j v → 1 ≤ j := by
      intro q j v he
      have hqR : q < σ.word.length := by
        by_contra hn
        rw [Ctx.Context.letterAt_of_length_le σ (by omega)] at he
        cases he
      rcases hAt q hqR with hc | hm
      · rw [hc] at he
        cases he
      · rw [hm] at he
        have hj : 1 = j := (Ctx.Letter.ext.inj he).1
        omega
    obtain ⟨first, sep, other, hfirst, hother, hFirstSep, hSepOther, hSep⟩ :=
      hTwoSites σ s hletters hruns
    have hSepR : sep < σ.word.length := by
      have hh := List.mem_range.mp (List.mem_filter.mp hother).1
      omega
    have hSepMem : sep ∈ σ.extPositions 1 := hExtMem sep hSepR hSep
    obtain ⟨x, oldTail, hOldCons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hSepMem)
    have hxOld : x ∈ σ.extPositions 1 := by rw [hOldCons]; exact List.mem_cons_self
    have hxR : x < σ.word.length := List.mem_range.mp (List.mem_filter.mp hxOld).1
    have hxAt : σ.letterAt x = marker := hOldAt x hxOld
    have hOldSorted : (σ.extPositions 1).Pairwise (· ≤ ·) :=
      (List.pairwise_lt_range.filter _).imp le_of_lt
    have hOldMin : ∀ q ∈ σ.extPositions 1, x ≤ q := by
      intro q hq
      have hh := hOldSorted.rel_head hq
      simpa [hOldCons] using hh
    obtain ⟨wordTail, hWordCons⟩ := List.head?_eq_some_iff.mp hhead
    have hWordPos : 0 < σ.word.length := by rw [hWordCons]; simp
    have hZeroAt : σ.letterAt 0 = Ctx.Letter.child := by
      simp [Ctx.Context.letterAt, hWordCons]
    have hZeroMem : 0 ∈ σ.childPositions := by
      simp [Ctx.Context.childPositions, hWordPos, hZeroAt]
    have hxPos : 0 < x := by
      have hx0 : x ≠ 0 := by
        intro he
        rw [he, hZeroAt] at hxAt
        simp [marker] at hxAt
      omega
    have hPrefix (q : ℕ) (hq : q < x) : σ.letterAt q = Ctx.Letter.child := by
      rcases hAt q (by omega) with hc | hm
      · exact hc
      · have hh := hOldMin q (hExtMem q (by omega) hm)
        omega
    have hRange : List.range σ.word.length =
        List.range x ++ List.range' x (σ.word.length - x) := by
      have hsum : x + (σ.word.length - x) = σ.word.length := by omega
      simpa only [List.range_eq_range', Nat.zero_add, hsum] using
        (List.range'_append_1 (s := 0) (m := x) (n := σ.word.length - x)).symm
    let tail := (List.range' x (σ.word.length - x)).filter
      (fun q => σ.letterAt q = Ctx.Letter.child)
    have hPrefixFilter : (List.range x).filter
        (fun q => σ.letterAt q = Ctx.Letter.child) = List.range x := by
      apply List.filter_eq_self.mpr
      intro q hq
      simpa using hPrefix q (List.mem_range.mp hq)
    have hchildren : σ.childPositions = List.range x ++ tail := by
      change (List.range σ.word.length).filter _ = List.range x ++ tail
      rw [hRange, List.filter_append, hPrefixFilter]
    have hTailLower : ∀ q ∈ tail, x ≤ q := by
      intro q hq
      exact (List.mem_range'_1.mp (List.mem_filter.mp hq).1).1
    have hOtherTail : other ∈ tail := by
      have hh := List.mem_range.mp (List.mem_filter.mp hother).1
      have hxSep := hOldMin sep hSepMem
      apply List.mem_filter.mpr
      refine ⟨List.mem_range'_1.mpr ⟨by omega, by omega⟩, (List.mem_filter.mp hother).2⟩
    have htailNe : tail ≠ [] := List.ne_nil_of_mem hOtherTail
    have htailLen : 0 < tail.length := List.length_pos_iff.mpr htailNe
    let keep := List.range x
    let τ := σ.part keep s 1
    have hKeepFirst : (List.range x).filter (fun q => q ∈ keep) = List.range x := by
      apply List.filter_eq_self.mpr
      intro q hq
      simpa only [keep, decide_eq_true_eq] using hq
    have hKeepTail : tail.filter (fun q => q ∈ keep) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq
      have hh := hTailLower q hq
      simp only [keep, List.mem_range, decide_eq_true_eq]
      omega
    have hτchildren : τ.childPositions = List.range x := by
      rw [Ctx.Context.part_childPositions, hchildren, List.filter_append,
        hKeepFirst, hKeepTail, List.append_nil]
    have hRemoveFirst : (List.range x).filter (fun q => q ∉ keep) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq
      simp [keep, hq]
    have hRemoveTail : tail.filter (fun q => q ∉ keep) = tail := by
      apply List.filter_eq_self.mpr
      intro q hq
      have hh := hTailLower q hq
      simp only [keep, List.mem_range, decide_eq_true_eq]
      omega
    have hτfresh : τ.extPositions 1 = tail := by
      rw [Ctx.Context.part_extPositions_one hpositive keep s 1,
        hchildren, List.filter_append, hRemoveFirst, hRemoveTail, List.nil_append]
    have hτold : τ.extPositions 2 = σ.extPositions 1 :=
      Ctx.Context.part_extPositions_succ σ keep s 1 (by omega : 1 ≤ 1)
    have hblock : keep ∈ σ.blocks := by
      simp only [Ctx.Context.blocks, List.mem_filter, List.mem_flatMap,
        List.mem_range, List.mem_map, decide_eq_true_eq]
      refine ⟨⟨0, ?_, x - 1, ?_, ?_⟩, ?_⟩
      · simp only [hchildren, List.length_append, List.length_range]
        omega
      · simp only [hchildren, List.length_append, List.length_range]
        omega
      · simp [hchildren, keep, Nat.sub_add_cancel (by omega : 1 ≤ x)]
      · simp only [keep, List.length_range, hchildren, List.length_append]
        omega
    have hside : σ.sideAt 1 = s := by
      simp [Ctx.Context.sideAt, hOldCons, hxAt, marker]
    have hFreshWitness : other ∈ τ.extPositions 1 := by rw [hτfresh]; exact hOtherTail
    have hs1 : τ.sideAt 1 = s :=
      Ctx.Context.part_sideAt_one_of_mem hpositive keep s 1 hFreshWitness
    have hs2 : τ.sideAt 2 = s :=
      (Ctx.Context.part_sideAt_succ σ keep s 1 (by omega : 1 ≤ 1)).trans hside
    have hmaxτ : τ.maxima = [1, m] := by simp [τ, Ctx.Context.part, hmax]
    have hFreshRight : ∀ q ∈ τ.extPositions 1, 0 < q := by
      intro q hq
      rw [hτfresh] at hq
      have hh := hTailLower q hq
      omega
    have hLeftNil : (τ.extPositions 2).filter (· < 0) = [] := by simp
    let z := σ.word.length - 1
    have hzR : z < σ.word.length := by dsimp [z]; omega
    have hzAt : σ.letterAt z = Ctx.Letter.child := by
      simp only [z, Ctx.Context.letterAt, ← List.getLast?_eq_getElem?, hlast,
        Option.getD_some]
    have hzMem : z ∈ σ.childPositions := by
      simp [Ctx.Context.childPositions, hzR, hzAt]
    have hNoThread : ¬(∃ q ∈ τ.extPositions 1, ∃ y ∈ τ.extPositions 2, q < y) := by
      rintro ⟨q, hq, y, hy, hqy⟩
      rw [hτfresh] at hq
      rw [hτold] at hy
      have hqChild : q ∈ σ.childPositions := by
        rw [hchildren]
        exact List.mem_append_right _ hq
      have hqLower := hTailLower q hq
      have hyR := List.mem_range.mp (List.mem_filter.mp hy).1
      have hyAt := hOldAt y hy
      have hxq : x < q := by
        have hneq : x ≠ q := by
          intro he
          have hqAt := of_decide_eq_true (List.mem_filter.mp hqChild).2
          rw [← he, hxAt] at hqAt
          simp [marker] at hqAt
        omega
      have hyz : y < z := by
        have hneq : y ≠ z := by
          intro he
          rw [he, hzAt] at hyAt
          simp [marker] at hyAt
        change y < σ.word.length - 1
        have hneq' : y ≠ σ.word.length - 1 := hneq
        omega
      have hxNot : σ.letterAt x ≠ Ctx.Letter.child := by simp [hxAt, marker]
      have hyNot : σ.letterAt y ≠ Ctx.Letter.child := by simp [hyAt, marker]
      have hh := hThreeSites σ 0 x q y z hZeroMem hqChild hzMem
        hxNot hyNot hxPos hxq hqy hyz
      omega
    have hτruns : τ.numRuns ≤ 1 := by
      let ts := (List.range τ.word.length).filter fun p =>
        τ.letterAt p = Ctx.Letter.child ∧
          (p = 0 ∨ τ.letterAt (p - 1) ≠ Ctx.Letter.child)
      change ts.length ≤ 1
      have hOnly : ∀ p ∈ ts, p = 0 := by
        intro p hp
        have hpR : p < τ.word.length := List.mem_range.mp (List.mem_filter.mp hp).1
        have hh : τ.letterAt p = Ctx.Letter.child ∧
            (p = 0 ∨ τ.letterAt (p - 1) ≠ Ctx.Letter.child) :=
          of_decide_eq_true (List.mem_filter.mp hp).2
        have hpMem : p ∈ τ.childPositions := by
          simp [Ctx.Context.childPositions, hpR, hh.1]
        rw [hτchildren] at hpMem
        have hpL := List.mem_range.mp hpMem
        by_contra hp0
        have hPrevMem : p - 1 ∈ τ.childPositions := by
          rw [hτchildren]
          exact List.mem_range.mpr (by omega)
        have hPrev : τ.letterAt (p - 1) = Ctx.Letter.child :=
          of_decide_eq_true (List.mem_filter.mp hPrevMem).2
        rcases hh.2 with he | hno
        · exact hp0 he
        · exact hno hPrev
      have hNodup : ts.Nodup := List.nodup_range.filter _
      have hsub : ts.toFinset ⊆ ({0} : Finset ℕ) := by
        intro p hp
        simpa only [Finset.mem_singleton] using hOnly p (List.mem_toFinset.mp hp)
      have hcard := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hNodup] at hcard
      simpa only [Finset.card_singleton] using hcard
    have hp := hProfile τ m hmaxτ s hs1 hs2 0
      (List.ne_nil_of_mem hFreshWitness) hFreshRight
    dsimp only at hp
    have hLeft : τ.leftExt s 0 0 = 0 := by simpa only [if_pos hLeftNil] using hp.1
    have hRight : τ.rightExt s 0 0 = 1 := by simpa only [if_neg hNoThread] using hp.2.1
    have hChain : τ.chainExt s 0 0 = 1 := by
      simp only [Ctx.Context.chainExt, hLeft, hRight, Nat.zero_add]
    have hJoin : τ.joinExt s 0 0 = m + 1 := by
      simpa only [if_pos hLeftNil, if_neg hNoThread, Nat.zero_add,
        Nat.max_eq_right (by omega : 1 ≤ m + 1)] using hp.2.2.1
    have hOpp := hp.2.2.2 t (Ne.symm hne)
    have hChosenLimit : 1 ≤ (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => τ.cupLimit 0 0 | Ctx.Side.upper => τ.capLimit 0 0) s := by
      cases hs : s with
      | lower =>
        have hg : 3 ≤ σ.u := by simpa only [hs] using hchosen
        have hc : τ.chainExt Ctx.Side.lower 0 0 = 1 := by simpa only [hs] using hChain
        have hj : τ.joinExt Ctx.Side.lower 0 0 = m + 1 := by simpa only [hs] using hJoin
        change 1 ≤ min (σ.u - 1 - τ.chainExt Ctx.Side.lower 0 0)
          (σ.k - 1 - τ.joinExt Ctx.Side.lower 0 0)
        rw [hc, hj]
        apply Nat.le_min.mpr
        constructor <;> omega
      | upper =>
        have hg : 3 ≤ σ.a := by simpa only [hs] using hchosen
        have hc : τ.chainExt Ctx.Side.upper 0 0 = 1 := by simpa only [hs] using hChain
        have hj : τ.joinExt Ctx.Side.upper 0 0 = m + 1 := by simpa only [hs] using hJoin
        change 1 ≤ min (σ.a - 1 - τ.chainExt Ctx.Side.upper 0 0)
          (σ.k - 1 - τ.joinExt Ctx.Side.upper 0 0)
        rw [hc, hj]
        apply Nat.le_min.mpr
        constructor <;> omega
    have hOppLimit : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => τ.cupLimit 0 0 | Ctx.Side.upper => τ.capLimit 0 0) t = 1 := by
      cases ht : t with
      | lower =>
        have hg : σ.u = 2 := by simpa only [ht] using hunit
        have hc : τ.chainExt Ctx.Side.lower 0 0 = 0 := by simpa only [ht] using hOpp.1
        have hj : τ.joinExt Ctx.Side.lower 0 0 = 0 := by simpa only [ht] using hOpp.2
        change min (σ.u - 1 - τ.chainExt Ctx.Side.lower 0 0)
          (σ.k - 1 - τ.joinExt Ctx.Side.lower 0 0) = 1
        rw [hg, hc, hj]
        change min 1 (σ.k - 1) = 1
        exact Nat.min_eq_left (by omega)
      | upper =>
        have hg : σ.a = 2 := by simpa only [ht] using hunit
        have hc : τ.chainExt Ctx.Side.upper 0 0 = 0 := by simpa only [ht] using hOpp.1
        have hj : τ.joinExt Ctx.Side.upper 0 0 = 0 := by simpa only [ht] using hOpp.2
        change min (σ.a - 1 - τ.chainExt Ctx.Side.upper 0 0)
          (σ.k - 1 - τ.joinExt Ctx.Side.upper 0 0) = 1
        rw [hg, hc, hj]
        change min 1 (σ.k - 1) = 1
        exact Nat.min_eq_left (by omega)
    have hτhead : τ.childPositions.head? = some 0 := by
      simp [hτchildren, List.head?_range, Nat.ne_of_gt hxPos]
    have hBase : τ.base = 1 := by
      cases hs : s with
      | lower =>
        have ht : t = Ctx.Side.upper := by
          cases t with
          | lower => exact (hne hs).elim
          | upper => rfl
        have hcPos : 1 ≤ τ.cupLimit 0 0 := by simpa only [hs] using hChosenLimit
        have hc : τ.cupLimit 0 0 ≠ 0 := by omega
        have ha : τ.capLimit 0 0 = 1 := by simpa only [ht] using hOppLimit
        simp [Ctx.Context.base, hτhead, hc, ha]
      | upper =>
        have ht : t = Ctx.Side.lower := by
          cases t with
          | lower => rfl
          | upper => exact (hne hs).elim
        have hcPos : 1 ≤ τ.capLimit 0 0 := by simpa only [hs] using hChosenLimit
        have hc : τ.capLimit 0 0 ≠ 0 := by omega
        have hu : τ.cupLimit 0 0 = 1 := by simpa only [ht] using hOppLimit
        simp [Ctx.Context.base, hτhead, hc, hu]
    have hPart : τ.bound = 1 := by
      unfold Ctx.Context.bound
      rw [Ctx.Context.boundFuel.eq_2, if_pos hτruns]
      exact hBase
    apply Nat.le_antisymm
    · exact hGlobalTwo σ hpositive t hunit.le
    · cases hs : s with
      | lower =>
        have hCut := (ctx_bound_cut_le σ hruns keep hblock 1 (by omega) (by omega)).1
        have hτ : (σ.part keep Ctx.Side.lower 1).bound = 1 :=
          by simpa only [τ, hs] using hPart
        rw [hτ] at hCut
        omega
      | upper =>
        have hCut := (ctx_bound_cut_le σ hruns keep hblock (σ.k - 2) (by omega) le_rfl).2
        have hc : σ.k - 1 - (σ.k - 2) = 1 := by omega
        rw [hc] at hCut
        have hτ : (σ.part keep Ctx.Side.upper 1).bound = 1 :=
          by simpa only [τ, hs] using hPart
        rw [hτ] at hCut
        omega

  have hRootData (σ : Ctx.Context) (s : Ctx.Side)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 2 ≤ σ.numRuns) :
      (∀ q j v, σ.letterAt q = Ctx.Letter.ext j v → 1 ≤ j) ∧ σ.sideAt 1 = s := by
    classical
    let marker := Ctx.Letter.ext 1 s
    have hAt (q : ℕ) (hq : q < σ.word.length) :
        σ.letterAt q = Ctx.Letter.child ∨ σ.letterAt q = marker := by
      have he : σ.letterAt q = σ.word[q] := by
        simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hq]
      rw [he]
      exact hletters _ (List.getElem_mem hq)
    have hExtMem (q : ℕ) (hq : q < σ.word.length)
        (he : σ.letterAt q = marker) : q ∈ σ.extPositions 1 := by
      simp [Ctx.Context.extPositions, hq, he, marker]
    have hOldAt (q : ℕ) (hq : q ∈ σ.extPositions 1) : σ.letterAt q = marker := by
      have hqR := List.mem_range.mp (List.mem_filter.mp hq).1
      rcases hAt q hqR with hc | hm
      · simp [Ctx.Context.extPositions, hc] at hq
      · exact hm
    have hpositive : ∀ q j v, σ.letterAt q = Ctx.Letter.ext j v → 1 ≤ j := by
      intro q j v he
      have hqR : q < σ.word.length := by
        by_contra hn
        rw [Ctx.Context.letterAt_of_length_le σ (by omega)] at he
        cases he
      rcases hAt q hqR with hc | hm
      · rw [hc] at he
        cases he
      · rw [hm] at he
        have hj : 1 = j := (Ctx.Letter.ext.inj he).1
        omega
    obtain ⟨first, sep, other, hfirst, hother, hFirstSep, hSepOther, hSep⟩ :=
      hTwoSites σ s hletters hruns
    have hSepR : sep < σ.word.length := by
      have hh := List.mem_range.mp (List.mem_filter.mp hother).1
      omega
    have hSepMem : sep ∈ σ.extPositions 1 := hExtMem sep hSepR hSep
    obtain ⟨x, oldTail, hOldCons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hSepMem)
    have hxOld : x ∈ σ.extPositions 1 := by rw [hOldCons]; exact List.mem_cons_self
    have hxAt := hOldAt x hxOld
    have hside : σ.sideAt 1 = s := by
      simp [Ctx.Context.sideAt, hOldCons, hxAt, marker]
    exact ⟨hpositive, hside⟩

  have hRootWF (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
      (ha : 2 ≤ σ.a) (hu : 2 ≤ σ.u) (hak : σ.a ≤ σ.k) (huk : σ.u ≤ σ.k)
      (hm : 1 ≤ m) (hmk : m ≤ σ.k - 2) (s : Ctx.Side)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 2 ≤ σ.numRuns) : σ.WellFormed := by
    have hData := hRootData σ s hletters hruns
    refine ⟨ha, hu, hak, huk, ?_, ?_⟩
    · intro M hM
      have hEq : M = m := by simpa only [hmax, List.mem_singleton] using hM
      subst M
      exact ⟨hm, hmk⟩
    · intro p j v he
      have hp : p < σ.word.length := by
        by_contra hn
        rw [Ctx.Context.letterAt_of_length_le σ (by omega)] at he
        cases he
      have hletter : σ.letterAt p = σ.word[p] := by
        simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hp]
      have hmem : Ctx.Letter.ext j v ∈ σ.word := by
        have hElem : σ.word[p] = Ctx.Letter.ext j v := hletter.symm.trans he
        rw [← hElem]
        exact List.getElem_mem hp
      rcases hletters _ hmem with hc | ht
      · cases hc
      · have hj : j = 1 := (Ctx.Letter.ext.inj ht).1
        have hv : v = s := (Ctx.Letter.ext.inj ht).2
        subst j
        subst v
        refine ⟨by omega, ?_, hData.2.symm⟩
        rw [hmax]
        simp

  have hReflectedPositive (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
      (s t : Ctx.Side) (hne : s ≠ t)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 2 ≤ σ.numRuns) (hlast : σ.word.getLast? = some Ctx.Letter.child)
      (hchosen : 4 ≤ (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s)
      (hchosenK : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ σ.k)
      (hunit : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t = 2)
      (hms : m ≤ σ.k - 3)
      (hreverse : ({σ with word := σ.word.reverse} : Ctx.Context).bound = σ.bound) :
      σ.bound = 1 := by
    classical
    let ρ : Ctx.Context := {σ with word := σ.word.reverse}
    let flip := fun q : ℕ => σ.word.length - 1 - q
    have hflipLt (q : ℕ) (hq : q < σ.word.length) : flip q < σ.word.length := by
      dsimp [flip]
      omega
    have hflipInv (q : ℕ) (hq : q < σ.word.length) : flip (flip q) = q := by
      dsimp [flip]
      omega
    have hletter (q : ℕ) (hq : q < σ.word.length) :
        ρ.letterAt (flip q) = σ.letterAt q := by
      simp only [Ctx.Context.letterAt, ρ, List.getElem?_reverse (hflipLt q hq)]
      change σ.word[flip (flip q)]?.getD Ctx.Letter.child =
        σ.word[q]?.getD Ctx.Letter.child
      rw [hflipInv q hq]
    have hChildFlip (q : ℕ) (hq : q ∈ σ.childPositions) : flip q ∈ ρ.childPositions := by
      have hqR := List.mem_range.mp (List.mem_filter.mp hq).1
      have hqAt : σ.letterAt q = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hq).2
      apply List.mem_filter.mpr
      refine ⟨List.mem_range.mpr ?_, ?_⟩
      · simpa only [ρ, List.length_reverse] using hflipLt q hqR
      · simpa only [decide_eq_true_eq, hletter q hqR] using hqAt
    obtain ⟨first, sep, other, hfirst, hother, hFirstSep, hSepOther, hSep⟩ :=
      hTwoSites σ s hletters hruns
    have hFirstR := List.mem_range.mp (List.mem_filter.mp hfirst).1
    have hOtherR := List.mem_range.mp (List.mem_filter.mp hother).1
    have hSepR : sep < σ.word.length := by omega
    have hOtherFlip := hChildFlip other hother
    have hFirstFlip := hChildFlip first hfirst
    have hSepOrder : flip other < flip sep ∧ flip sep < flip first := by
      dsimp [flip]
      constructor <;> omega
    have hρruns : 2 ≤ ρ.numRuns := by
      by_contra hbad
      have hsingle : ρ.numRuns ≤ 1 := by omega
      obtain ⟨b, hb⟩ := hInterval ρ hsingle (List.ne_nil_of_mem hOtherFlip)
      have hLow : b ≤ flip other ∧ flip other < b + ρ.childPositions.length := by
        rw [hb] at hOtherFlip
        exact List.mem_range'_1.mp hOtherFlip
      have hHigh : b ≤ flip first ∧ flip first < b + ρ.childPositions.length := by
        rw [hb] at hFirstFlip
        exact List.mem_range'_1.mp hFirstFlip
      have hSepChild : flip sep ∈ ρ.childPositions := by
        rw [hb]
        apply List.mem_range'_1.mpr
        constructor <;> omega
      have hSepAt : ρ.letterAt (flip sep) = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hSepChild).2
      rw [hletter sep hSepR, hSep] at hSepAt
      cases hSepAt
    have hρletters : ∀ v ∈ ρ.word,
        v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s := by
      intro v hv
      exact hletters v (List.mem_reverse.mp hv)
    have hρhead : ρ.word.head? = some Ctx.Letter.child := by
      simpa only [ρ, List.head?_reverse] using hlast
    have hρchosen : 4 + (if ρ.word.head? = some (Ctx.Letter.ext 1 s) then 1 else 0) ≤
        (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) s := by
      change 4 + (if ρ.word.head? = some (Ctx.Letter.ext 1 s) then 1 else 0) ≤
        (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s
      simpa [hρhead] using hchosen
    have hρmax : ρ.maxima = [m] := hmax
    have hPositive := hRootPositive ρ m hρmax s t hne hρletters hρruns
      hρchosen hchosenK hunit hms
    have hEq : ρ.bound = σ.bound := hreverse
    exact hEq.symm.trans hPositive

  have hPartUnitZero (σ : Ctx.Context)
    (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
    (s : Ctx.Side)
    (hunit : match s with | Ctx.Side.lower => σ.u ≤ 2 | Ctx.Side.upper => σ.a ≤ 2)
    (keep : List ℕ) (m r : ℕ)
    (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep) :
    (∀ p ∈ (σ.part keep s m).childPositions,
      (match s with
      | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
      | Ctx.Side.upper => (σ.part keep s m).capLimit p p) = 0) ∧
      (σ.part keep s m).bound = 0 := by
    classical
    let τ := σ.part keep s m
    have hrnew : r ∈ τ.extPositions 1 := by
      rw [Ctx.Context.part_extPositions_one hpositive keep s m]
      exact List.mem_filter.mpr ⟨hr, by simpa using hremoved⟩
    have hside : τ.sideAt 1 = s :=
      Ctx.Context.part_sideAt_one_of_mem hpositive keep s m hrnew
    have hone : 1 ∈ τ.levelsOn s 0 := by
      apply List.mem_filter.mpr
      refine ⟨?_, by simp [hside]⟩
      change 1 ∈ (σ.part keep s m).levels
      rw [Ctx.Context.part_levels]
      exact List.mem_cons_self
    have hsub : [1].Sublist (τ.levelsOn s 0) := List.singleton_sublist.mpr hone
    have hzero : ∀ p ∈ τ.childPositions,
        (match s with
        | Ctx.Side.lower => τ.cupLimit p p
        | Ctx.Side.upper => τ.capLimit p p) = 0 := by
      intro p hp
      have hpkeep : p ∈ keep := by
        rw [Ctx.Context.part_childPositions] at hp
        simpa using (List.mem_filter.mp hp).2
      have hne : p ≠ r := by intro h; subst p; exact hremoved hpkeep
      have hExt : 1 ≤ τ.leftExt s 0 p + τ.rightExt s 0 p := by
        by_cases hrp : r < p
        · have hnon : ((τ.extPositions 1).filter (· < p)) ≠ [] := by
            intro hn
            have hm : r ∈ (τ.extPositions 1).filter (· < p) :=
              List.mem_filter.mpr ⟨hrnew, by simpa using hrp⟩
            rw [hn] at hm
            cases hm
          have hv := Ctx.le_getD_max?_of_mem
            (L := (τ.levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
            (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
          change ([1].foldl (Ctx.Context.leftStep τ) (p, 0)).2 ≤ τ.leftExt s 0 p at hv
          simp only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
            List.getLast?_eq_some_getLast hnon] at hv
          omega
        · have hpr : p < r := by omega
          have hnon : ((τ.extPositions 1).filter (p < ·)) ≠ [] := by
            intro hn
            have hm : r ∈ (τ.extPositions 1).filter (p < ·) :=
              List.mem_filter.mpr ⟨hrnew, by simpa using hpr⟩
            rw [hn] at hm
            cases hm
          have hv := Ctx.le_getD_max?_of_mem
            (L := (τ.levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (Ctx.Context.rightStep τ) (p, 0)).2))
            (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
          change ([1].foldl (Ctx.Context.rightStep τ) (p, 0)).2 ≤ τ.rightExt s 0 p at hv
          simp only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
            List.head?_eq_some_head hnon] at hv
          omega
      have hchain : 1 ≤ τ.chainExt s p p := hExt
      cases s with
      | lower =>
        change σ.u ≤ 2 at hunit
        change min (σ.u - 1 - τ.chainExt Ctx.Side.lower p p)
          (σ.k - 1 - τ.joinExt Ctx.Side.lower p p) = 0
        omega
      | upper =>
        change σ.a ≤ 2 at hunit
        change min (σ.a - 1 - τ.chainExt Ctx.Side.upper p p)
          (σ.k - 1 - τ.joinExt Ctx.Side.upper p p) = 0
        omega
    have hz : ∀ p ∈ τ.childPositions, τ.cupLimit p p = 0 ∨ τ.capLimit p p = 0 := by
      intro p hp
      have h := hzero p hp
      cases s with
      | lower => exact Or.inl h
      | upper => exact Or.inr h
    have hsum : (τ.childPositions.map
        (fun p => Ctx.Context.baseOf (τ.cupLimit p p) (τ.capLimit p p) τ.k)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      simp only [Ctx.Context.baseOf, if_pos (hz p hp)]
    exact ⟨hzero, Nat.eq_zero_of_le_zero ((ctx_bound_le_sum_point_bases τ).trans_eq hsum)⟩

  have hAllProperZero (σ : Ctx.Context) (hruns : 2 ≤ σ.numRuns)
      (hkill : ∀ (keep : List ℕ) (s : Ctx.Side) (m r : ℕ),
        r ∈ σ.childPositions → r ∉ keep → (σ.part keep s m).bound = 0) :
      σ.bound = 0 := by
    classical
    have hMissing (keep : List ℕ) (s : Ctx.Side) (m : ℕ)
        (hsmall : (σ.part keep s m).childPositions.length < σ.childPositions.length) :
        ∃ r ∈ σ.childPositions, r ∉ keep := by
      by_contra hbad
      have hAll : ∀ r ∈ σ.childPositions, r ∈ keep := by
        intro r hr
        by_contra hnot
        exact hbad ⟨r, hr, hnot⟩
      have hEq : σ.childPositions.filter (fun r => r ∈ keep) = σ.childPositions := by
        apply List.filter_eq_self.mpr
        intro r hr
        simpa only [decide_eq_true_eq] using hAll r hr
      rw [Ctx.Context.part_childPositions, hEq] at hsmall
      omega
    have hFuelPart (keep : List ℕ) (s : Ctx.Side) (m : ℕ)
        (hsmall : (σ.part keep s m).childPositions.length < σ.childPositions.length) :
        Ctx.Context.boundFuel σ.childPositions.length (σ.part keep s m) = 0 := by
      rw [Ctx.Context.boundFuel_eq_bound (σ.part keep s m) (by omega)]
      obtain ⟨r, hr, hnot⟩ := hMissing keep s m hsmall
      exact hkill keep s m r hr hnot
    unfold Ctx.Context.bound
    rw [Ctx.Context.boundFuel.eq_2, if_neg (by omega : ¬ σ.numRuns ≤ 1)]
    apply Nat.eq_zero_of_le_zero
    apply Ctx.getD_max?_le
    intro z hz
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hz
    obtain ⟨block, hb, d, hd, hz⟩ := hz
    have hBlock (s : Ctx.Side) (m : ℕ) :=
      Ctx.Context.part_childPositions_length_lt_of_mem_blocks hb s m
    have hRest (s : Ctx.Side) (m : ℕ) :=
      Ctx.Context.part_rest_childPositions_length_lt_of_mem_blocks hb s m
    rcases hz with rfl | rfl
    · rw [hFuelPart block Ctx.Side.lower (d + 1) (hBlock _ _),
        hFuelPart (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.upper
          (σ.k - 1 - (d + 1)) (hRest _ _)]
    · rw [hFuelPart block Ctx.Side.upper (σ.k - 1 - (d + 1)) (hBlock _ _),
        hFuelPart (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.lower
          (d + 1) (hRest _ _)]
  have hBothGlobalsZero (σ : Ctx.Context)
      (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
      (ha : σ.a ≤ 2) (hu : σ.u ≤ 2) (hruns : 2 ≤ σ.numRuns) : σ.bound = 0 := by
    apply hAllProperZero σ hruns
    intro keep s m r hr hnot
    cases s with
    | lower => exact (hPartUnitZero σ hpositive Ctx.Side.lower hu keep m r hr hnot).2
    | upper => exact (hPartUnitZero σ hpositive Ctx.Side.upper ha keep m r hr hnot).2

  have hSaturatedZero (σ : Ctx.Context)
      (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
      (s t : Ctx.Side) (hne : s ≠ t) (N : ℕ) (hN : N ∈ σ.levelsOn s 0)
      (hM : σ.k - 2 ≤ σ.maximumAt N)
      (hunit : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t ≤ 2)
      (hruns : 2 ≤ σ.numRuns) : σ.bound = 0 := by
    apply hAllProperZero σ hruns
    intro keep v m r hr hnot
    by_cases hv : v = s
    · subst v
      exact ctx_part_bound_zero_of_same_side_large_sibling_maximum
        σ hpositive s N hN hM keep m r hr hnot
    · have hvt : v = t := by
        cases s <;> cases t <;> cases v <;>
          first | rfl | exact (hne rfl).elim | exact (hv rfl).elim
      subst v
      have hunit' : match t with
          | Ctx.Side.lower => σ.u ≤ 2 | Ctx.Side.upper => σ.a ≤ 2 := by
        cases t <;> exact hunit
      exact (hPartUnitZero σ hpositive t hunit' keep m r hr hnot).2

  have hBoundaryZero (σ : Ctx.Context)
      (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
      (N x : ℕ)
      (hchosen : (match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 3)
      (hopposite : (match σ.sideAt N with | Ctx.Side.lower => σ.a | Ctx.Side.upper => σ.u) ≤ 2)
      (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N) (rightward : Bool)
      (hchildren : ∀ p ∈ σ.childPositions, if rightward then p < x else x < p)
      (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
        if rightward then p < x else x < p)
      (hruns : 2 ≤ σ.numRuns) : σ.bound = 0 := by
    classical
    let τ : Context := match σ.sideAt N with
      | Side.lower => {σ with u := min (σ.u-1) (σ.k-σ.maximumAt N), maxima := σ.maxima.take (N-1)}
      | Side.upper => {σ with a := min (σ.a-1) (σ.k-σ.maximumAt N), maxima := σ.maxima.take (N-1)}
    have hWord : τ.word = σ.word := by
      cases h : σ.sideAt N <;> simp only [τ,h]
    have hLetter (p : ℕ) : τ.letterAt p = σ.letterAt p := by
      simp only [letterAt,hWord]
    have hPositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
      intro p j v he
      rw [hLetter] at he
      exact hpositive p j v he
    have hRuns : 2 ≤ τ.numRuns := by
      simpa only [numRuns,hWord,hLetter] using hruns
    have haτ : τ.a ≤ 2 := by
      cases h : σ.sideAt N with
      | lower =>
        have haσ : σ.a ≤ 2 := by simpa only [h] using hopposite
        simpa only [τ,h] using haσ
      | upper =>
        have haσ : σ.a ≤ 3 := by simpa only [h] using hchosen
        simp only [τ,h]
        exact (Nat.min_le_left _ _).trans (by omega)
    have huτ : τ.u ≤ 2 := by
      cases h : σ.sideAt N with
      | lower =>
        have huσ : σ.u ≤ 3 := by simpa only [h] using hchosen
        simp only [τ,h]
        exact (Nat.min_le_left _ _).trans (by omega)
      | upper =>
        have huσ : σ.u ≤ 2 := by simpa only [h] using hopposite
        simpa only [τ,h] using huσ
    have hZero := hBothGlobalsZero τ hPositive haτ huτ hRuns
    have hNormalize := ctx_boundary_marker_upper_normalize σ hpositive
      N x hN hx rightward hchildren hyounger
    have hDom : σ.bound ≤ τ.bound := hNormalize.2.2
    rw [hZero] at hDom
    exact Nat.eq_zero_of_le_zero hDom
  have hTwoBoundaryZero (σ : Ctx.Context)
      (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
      (N x y : ℕ)
      (hchosen : (match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
      (hopposite : (match σ.sideAt N with | Ctx.Side.lower => σ.a | Ctx.Side.upper => σ.u) ≤ 2)
      (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions N)
      (hchildren : ∀ p ∈ σ.childPositions, x < p ∧ p < y)
      (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j, x < p ∧ p < y)
      (hruns : 2 ≤ σ.numRuns) : σ.bound = 0 := by
    classical
    let τ : Context := match σ.sideAt N with
      | Side.lower => {σ with u := min (σ.u-2) (σ.k-σ.maximumAt N), maxima := σ.maxima.take (N-1)}
      | Side.upper => {σ with a := min (σ.a-2) (σ.k-σ.maximumAt N), maxima := σ.maxima.take (N-1)}
    have hWord : τ.word = σ.word := by
      cases h : σ.sideAt N <;> simp only [τ,h]
    have hLetter (p : ℕ) : τ.letterAt p = σ.letterAt p := by
      simp only [letterAt,hWord]
    have hPositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
      intro p j v he
      rw [hLetter] at he
      exact hpositive p j v he
    have hRuns : 2 ≤ τ.numRuns := by
      simpa only [numRuns,hWord,hLetter] using hruns
    have haτ : τ.a ≤ 2 := by
      cases h : σ.sideAt N with
      | lower =>
        have haσ : σ.a ≤ 2 := by simpa only [h] using hopposite
        simpa only [τ,h] using haσ
      | upper =>
        have haσ : σ.a ≤ 4 := by simpa only [h] using hchosen
        simp only [τ,h]
        exact (Nat.min_le_left _ _).trans (by omega)
    have huτ : τ.u ≤ 2 := by
      cases h : σ.sideAt N with
      | lower =>
        have huσ : σ.u ≤ 4 := by simpa only [h] using hchosen
        simp only [τ,h]
        exact (Nat.min_le_left _ _).trans (by omega)
      | upper =>
        have huσ : σ.u ≤ 2 := by simpa only [h] using hopposite
        simpa only [τ,h] using huσ
    have hZero := hBothGlobalsZero τ hPositive haτ huτ hRuns
    have hNormalize := ctx_two_boundary_marker_upper_normalize σ hpositive
      N x y hN hx hy hchildren hyounger
    have hDom : σ.bound ≤ τ.bound := hNormalize.2.2
    rw [hZero] at hDom
    exact Nat.eq_zero_of_le_zero hDom

  have hIndexedMarkerZero (σ : Ctx.Context) (s : Ctx.Side) (N x : ℕ) (hN : N ∈ σ.levels) (hs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 2) : (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ = 0) ∧ σ.bound = 0 := by
    classical
    have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
        1 ≤ ρ.leftExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq,hqp]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (leftStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
      change _ ≤ ρ.leftExt v 0 p at hv
      simpa only [List.foldl_cons,List.foldl_nil,leftStep,
        List.getLast?_eq_some_getLast hnonempty] using hv
    have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
        1 ≤ ρ.rightExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq,hpq]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (rightStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
      change _ ≤ ρ.rightExt v 0 p at hv
      simpa only [List.foldl_cons,List.foldl_nil,rightStep,
        List.head?_eq_some_head hnonempty] using hv
    have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN,by simp [hs]⟩
    have hPoint : ∀ p ∈ σ.childPositions,
        baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k = 0 := by
      intro p hp
      have hpx : p ≠ x := by
        intro he
        subst x
        have hc := of_decide_eq_true (List.mem_filter.mp hp).2
        have he := (List.mem_filter.mp hx).2
        simp [hc] at he
      have hChain : 1 ≤ σ.chainExt s p p := by
        by_cases h : p < x
        · have hright := hOneRight σ s N p x hNOn hx h
          unfold chainExt
          omega
        · have hleft := hOneLeft σ s N p x hNOn hx (by omega)
          unfold chainExt
          omega
      cases s with
      | lower =>
        dsimp only at hglobal
        have hzero : σ.cupLimit p p = 0 := by
          simp only [cupLimit]
          omega
        simp [baseOf,hzero]
      | upper =>
        dsimp only at hglobal
        have hzero : σ.capLimit p p = 0 := by
          simp only [capLimit]
          omega
        simp [baseOf,hzero]
    have hMap :
        σ.childPositions.map (fun p => baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k) =
          σ.childPositions.map (fun _ => 0) := by
      apply List.map_congr_left
      intro p hp
      exact hPoint p hp
    have hBound : σ.bound = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [hMap,List.sum_map_zero] using ctx_bound_le_sum_point_bases σ
    have hFuel (fuel : ℕ) : boundFuel fuel σ = 0 := by
      have hle : boundFuel fuel σ ≤ σ.bound := by
        by_cases hf : σ.childPositions.length+1 ≤ fuel
        · exact (boundFuel_eq_bound σ hf).le
        · exact boundFuel_mono (by omega : fuel ≤ σ.childPositions.length+1) σ
      rw [hBound] at hle
      exact Nat.eq_zero_of_le_zero hle
    exact ⟨hFuel,hBound⟩

  have hRootThreeZero (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
    (s t : Ctx.Side) (hne : s ≠ t)
    (hchosen : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 3)
    (hunit : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t ≤ 2)
    (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
    (hruns : 3 ≤ σ.numRuns) : σ.bound = 0 := by
    classical
    have hLeaf (σ : Ctx.Context)
      (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
      (s t : Ctx.Side) (hne : s ≠ t)
      (hunit : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t ≤ 2)
      (hbound : 0 < σ.bound) :
      ∃ (τ : Ctx.Context) (history : List ℕ),
        τ.a = σ.a ∧ τ.u = σ.u ∧ τ.k = σ.k ∧
        τ.word.length = σ.word.length ∧ τ.maxima = history ++ σ.maxima ∧
        (∀ c ∈ history, 1 ≤ c ∧ c ≤ σ.k - 2) ∧
        τ.numRuns ≤ 1 ∧ 0 < τ.base ∧
        (∀ p ∈ τ.childPositions, p ∈ σ.childPositions) ∧
        (∀ p, p < σ.word.length →
          match σ.letterAt p with
          | Ctx.Letter.child =>
            τ.letterAt p = Ctx.Letter.child ∨
              ∃ j, 1 ≤ j ∧ j ≤ history.length ∧ τ.letterAt p = Ctx.Letter.ext j s
          | Ctx.Letter.ext j v => τ.letterAt p = Ctx.Letter.ext (j + history.length) v) ∧
        (∀ j, 1 ≤ j → τ.sideAt (j + history.length) = σ.sideAt j) ∧
        (∀ j, 1 ≤ j → j ≤ history.length → τ.sideAt j = s) := by
      classical
      -- Reuse the accepted R18 raw proper-part-zero proof locally on this main-based branch.
      have hUnitZero (σ : Ctx.Context)
        (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
        (s : Ctx.Side)
        (hunit : match s with | Ctx.Side.lower => σ.u ≤ 2 | Ctx.Side.upper => σ.a ≤ 2)
        (keep : List ℕ) (m r : ℕ)
        (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep) :
        (∀ p ∈ (σ.part keep s m).childPositions,
          (match s with
          | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
          | Ctx.Side.upper => (σ.part keep s m).capLimit p p) = 0) ∧
          (σ.part keep s m).bound = 0 := by
        classical
        let τ := σ.part keep s m
        have hrnew : r ∈ τ.extPositions 1 := by
          rw [Ctx.Context.part_extPositions_one hpositive keep s m]
          exact List.mem_filter.mpr ⟨hr, by simpa using hremoved⟩
        have hside : τ.sideAt 1 = s :=
          Ctx.Context.part_sideAt_one_of_mem hpositive keep s m hrnew
        have hone : 1 ∈ τ.levelsOn s 0 := by
          apply List.mem_filter.mpr
          refine ⟨?_, by simp [hside]⟩
          change 1 ∈ (σ.part keep s m).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_self
        have hsub : [1].Sublist (τ.levelsOn s 0) := List.singleton_sublist.mpr hone
        have hzero : ∀ p ∈ τ.childPositions,
            (match s with
            | Ctx.Side.lower => τ.cupLimit p p
            | Ctx.Side.upper => τ.capLimit p p) = 0 := by
          intro p hp
          have hpkeep : p ∈ keep := by
            rw [Ctx.Context.part_childPositions] at hp
            simpa using (List.mem_filter.mp hp).2
          have hne : p ≠ r := by intro h; subst p; exact hremoved hpkeep
          have hExt : 1 ≤ τ.leftExt s 0 p + τ.rightExt s 0 p := by
            by_cases hrp : r < p
            · have hnon : ((τ.extPositions 1).filter (· < p)) ≠ [] := by
                intro hn
                have hm : r ∈ (τ.extPositions 1).filter (· < p) :=
                  List.mem_filter.mpr ⟨hrnew, by simpa using hrp⟩
                rw [hn] at hm
                cases hm
              have hv := Ctx.le_getD_max?_of_mem
                (L := (τ.levelsOn s 0).sublists.map
                  (fun ls => (ls.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
                (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
              change ([1].foldl (Ctx.Context.leftStep τ) (p, 0)).2 ≤ τ.leftExt s 0 p at hv
              simp only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
                List.getLast?_eq_some_getLast hnon] at hv
              omega
            · have hpr : p < r := by omega
              have hnon : ((τ.extPositions 1).filter (p < ·)) ≠ [] := by
                intro hn
                have hm : r ∈ (τ.extPositions 1).filter (p < ·) :=
                  List.mem_filter.mpr ⟨hrnew, by simpa using hpr⟩
                rw [hn] at hm
                cases hm
              have hv := Ctx.le_getD_max?_of_mem
                (L := (τ.levelsOn s 0).sublists.map
                  (fun ls => (ls.foldl (Ctx.Context.rightStep τ) (p, 0)).2))
                (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
              change ([1].foldl (Ctx.Context.rightStep τ) (p, 0)).2 ≤ τ.rightExt s 0 p at hv
              simp only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
                List.head?_eq_some_head hnon] at hv
              omega
          have hchain : 1 ≤ τ.chainExt s p p := hExt
          cases s with
          | lower =>
            change σ.u ≤ 2 at hunit
            change min (σ.u - 1 - τ.chainExt Ctx.Side.lower p p)
              (σ.k - 1 - τ.joinExt Ctx.Side.lower p p) = 0
            omega
          | upper =>
            change σ.a ≤ 2 at hunit
            change min (σ.a - 1 - τ.chainExt Ctx.Side.upper p p)
              (σ.k - 1 - τ.joinExt Ctx.Side.upper p p) = 0
            omega
        have hz : ∀ p ∈ τ.childPositions, τ.cupLimit p p = 0 ∨ τ.capLimit p p = 0 := by
          intro p hp
          have h := hzero p hp
          cases s with
          | lower => exact Or.inl h
          | upper => exact Or.inr h
        have hsum : (τ.childPositions.map
            (fun p => Ctx.Context.baseOf (τ.cupLimit p p) (τ.capLimit p p) τ.k)).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
          simp only [Ctx.Context.baseOf, if_pos (hz p hp)]
        exact ⟨hzero, Nat.eq_zero_of_le_zero ((ctx_bound_le_sum_point_bases τ).trans_eq hsum)⟩
      let Witness (ρ : Ctx.Context) : Prop :=
        ∃ (τ : Ctx.Context) (history : List ℕ),
          τ.a = ρ.a ∧ τ.u = ρ.u ∧ τ.k = ρ.k ∧
          τ.word.length = ρ.word.length ∧ τ.maxima = history ++ ρ.maxima ∧
          (∀ c ∈ history, 1 ≤ c ∧ c ≤ ρ.k - 2) ∧
          τ.numRuns ≤ 1 ∧ 0 < τ.base ∧
          (∀ p ∈ τ.childPositions, p ∈ ρ.childPositions) ∧
          (∀ p, p < ρ.word.length →
            match ρ.letterAt p with
            | Ctx.Letter.child =>
              τ.letterAt p = Ctx.Letter.child ∨
                ∃ j, 1 ≤ j ∧ j ≤ history.length ∧ τ.letterAt p = Ctx.Letter.ext j s
            | Ctx.Letter.ext j v => τ.letterAt p = Ctx.Letter.ext (j + history.length) v) ∧
          (∀ j, 1 ≤ j → τ.sideAt (j + history.length) = ρ.sideAt j) ∧
          (∀ j, 1 ≤ j → j ≤ history.length → τ.sideAt j = s)
      change Witness σ
      have hPositivePart (ρ : Ctx.Context) (keep : List ℕ) (v : Ctx.Side) (m : ℕ) :
          ∀ p j u, (ρ.part keep v m).letterAt p = Ctx.Letter.ext j u → 1 ≤ j := by
        intro p j u hx
        have hp : p < ρ.word.length := by
          by_contra h
          rw [Ctx.Context.letterAt_of_length_le (ρ.part keep v m)
            (by rw [Ctx.Context.part_word_length]; omega)] at hx
          cases hx
        cases he : ρ.letterAt p with
        | child =>
          rw [Ctx.Context.part_letterAt_of_child ρ keep v m hp he] at hx
          split at hx
          · cases hx
          · cases hx; omega
        | ext l w =>
          rw [Ctx.Context.part_letterAt_of_ext ρ keep v m hp he] at hx
          cases hx
          omega
      have hRemoved (ρ : Ctx.Context) (keep : List ℕ) (v : Ctx.Side) (m : ℕ)
          (hsmall : (ρ.part keep v m).childPositions.length < ρ.childPositions.length) :
          ∃ r ∈ ρ.childPositions, r ∉ keep := by
        by_contra hn
        push_neg at hn
        have he : ρ.childPositions.filter (fun p => p ∈ keep) = ρ.childPositions := by
          apply List.filter_eq_self.mpr
          intro p hp
          simpa using hn p hp
        rw [Ctx.Context.part_childPositions, he] at hsmall
        omega
      have hmain : ∀ n : ℕ, ∀ (ρ : Ctx.Context), ρ.childPositions.length = n →
          (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
          (fun v : Ctx.Side => match v with
            | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) t ≤ 2 →
          0 < ρ.bound → Witness ρ := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
          intro ρ hcount hPos hUnit hBound
          by_cases hruns : ρ.numRuns ≤ 1
          · have hbase : 0 < ρ.base := by
              simpa only [Ctx.Context.bound, Ctx.Context.boundFuel.eq_2, if_pos hruns] using hBound
            refine ⟨ρ, [], rfl, rfl, rfl, rfl, rfl, ?_, hruns, hbase, ?_, ?_, ?_, ?_⟩
            · simp
            · intro p hp; exact hp
            · intro p hp
              cases he : ρ.letterAt p with
              | child => exact Or.inl rfl
              | ext j v => simpa using he
            · intro j hj; simp
            · intro j hj hle; simp at hle; omega
          have hruns2 : 2 ≤ ρ.numRuns := by omega
          have hRecurse (keep : List ℕ) (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ ρ.k - 2)
              (hSmall : (ρ.part keep s m).childPositions.length < ρ.childPositions.length)
              (hPart : 0 < (ρ.part keep s m).bound) : Witness ρ := by
            let A := ρ.part keep s m
            have hAcount : A.childPositions.length < n := by simpa only [hcount] using hSmall
            have hAunit : (fun v : Ctx.Side => match v with
                | Ctx.Side.lower => A.u | Ctx.Side.upper => A.a) t ≤ 2 := hUnit
            obtain ⟨τ, history, ha, hu, hk, hlen, hmax, hlegal,
              hrun, hbase, hchildren, hword, hold, hnew⟩ :=
              ih A.childPositions.length hAcount A rfl (hPositivePart ρ keep s m) hAunit hPart
            obtain ⟨r, hr, hnot⟩ := hRemoved ρ keep s m hSmall
            have hrnew : r ∈ A.extPositions 1 := by
              rw [Ctx.Context.part_extPositions_one hPos keep s m]
              exact List.mem_filter.mpr ⟨hr, by simpa using hnot⟩
            have hAnew : A.sideAt 1 = s := Ctx.Context.part_sideAt_one_of_mem hPos keep s m hrnew
            have hprefix : (history ++ [m]).length = history.length + 1 := by simp
            refine ⟨τ, history ++ [m], ha, hu, hk, ?_, ?_, ?_, hrun, hbase, ?_, ?_, ?_, ?_⟩
            · exact hlen.trans (Ctx.Context.part_word_length ρ keep s m)
            · simpa only [A, Ctx.Context.part, List.append_assoc, List.cons_append,
                List.nil_append] using hmax
            · intro c hc
              rcases List.mem_append.mp hc with hc | hc
              · simpa only [A, Ctx.Context.part] using hlegal c hc
              · have hc' : c = m := by simpa using hc
                subst c
                exact ⟨hm, hmk⟩
            · intro p hp
              have hpA := hchildren p hp
              rw [Ctx.Context.part_childPositions] at hpA
              exact (List.mem_filter.mp hpA).1
            · intro p hp
              have hpA : p < A.word.length := by rw [Ctx.Context.part_word_length]; exact hp
              cases he : ρ.letterAt p with
              | child =>
                by_cases hkeep : p ∈ keep
                · have heA : A.letterAt p = Ctx.Letter.child := by
                    rw [Ctx.Context.part_letterAt_of_child ρ keep s m hp he, if_pos hkeep]
                  have hw := hword p hpA
                  rw [heA] at hw
                  rcases hw with hc | ⟨j, hj, hjlen, heτ⟩
                  · exact Or.inl hc
                  · exact Or.inr ⟨j, hj, by rw [hprefix]; omega, heτ⟩
                · have heA : A.letterAt p = Ctx.Letter.ext 1 s := by
                    rw [Ctx.Context.part_letterAt_of_child ρ keep s m hp he, if_neg hkeep]
                  have hw := hword p hpA
                  rw [heA] at hw
                  exact Or.inr ⟨history.length + 1, by omega, by rw [hprefix],
                    by simpa only [Nat.add_comm] using hw⟩
              | ext j v =>
                have heA : A.letterAt p = Ctx.Letter.ext (j + 1) v :=
                  Ctx.Context.part_letterAt_of_ext ρ keep s m hp he
                have hw := hword p hpA
                rw [heA] at hw
                simpa only [hprefix, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw
            · intro j hj
              have ho := hold (j + 1) (by omega)
              rw [Ctx.Context.part_sideAt_succ ρ keep s m hj] at ho
              simpa only [hprefix, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ho
            · intro j hj hle
              rw [hprefix] at hle
              by_cases hjp : j ≤ history.length
              · exact hnew j hj hjp
              · have hj' : j = 1 + history.length := by omega
                rw [hj']
                exact (hold 1 (by omega)).trans hAnew
          obtain ⟨block, hb, d, hd, hdk, hatt⟩ :=
            ctx_positive_bound_attained_by_interval_cut ρ hruns2 hBound
          let rest := ρ.childPositions.filter (fun p => p ∉ block)
          have hBsmall (v : Ctx.Side) (m : ℕ) :
              (ρ.part block v m).childPositions.length < ρ.childPositions.length :=
            Ctx.Context.part_childPositions_length_lt_of_mem_blocks hb v m
          have hRsmall (v : Ctx.Side) (m : ℕ) :
              (ρ.part rest v m).childPositions.length < ρ.childPositions.length :=
            Ctx.Context.part_rest_childPositions_length_lt_of_mem_blocks hb v m
          have hc : 1 ≤ ρ.k - 1 - d ∧ ρ.k - 1 - d ≤ ρ.k - 2 := by omega
          have hPair (keep rest : List ℕ) (m c : ℕ)
              (hm : 1 ≤ m) (hmk : m ≤ ρ.k - 2) (hc : 1 ≤ c) (hck : c ≤ ρ.k - 2)
              (hKS : ∀ v c, (ρ.part keep v c).childPositions.length < ρ.childPositions.length)
              (hRS : ∀ v c, (ρ.part rest v c).childPositions.length < ρ.childPositions.length)
              (hp : 0 < (ρ.part keep Ctx.Side.lower m).bound + (ρ.part rest Ctx.Side.upper c).bound) :
              Witness ρ := by
            cases hs : s with
            | lower =>
              have ht : t = Ctx.Side.upper := by
                cases t with
                | lower => exact (hne hs).elim
                | upper => rfl
              obtain ⟨r, hr, hnot⟩ := hRemoved ρ rest Ctx.Side.upper c (hRS _ _)
              have hz := (hUnitZero ρ hPos Ctx.Side.upper
                (by simpa only [ht] using hUnit) rest c r hr hnot).2
              have hChosen : 0 < (ρ.part keep Ctx.Side.lower m).bound := by
                rw [hz, Nat.add_zero] at hp
                exact hp
              exact hRecurse keep m hm hmk (by simpa only [hs] using hKS Ctx.Side.lower m)
                (by simpa only [hs] using hChosen)
            | upper =>
              have ht : t = Ctx.Side.lower := by
                cases t with
                | lower => rfl
                | upper => exact (hne hs).elim
              obtain ⟨r, hr, hnot⟩ := hRemoved ρ keep Ctx.Side.lower m (hKS _ _)
              have hz := (hUnitZero ρ hPos Ctx.Side.lower
                (by simpa only [ht] using hUnit) keep m r hr hnot).2
              have hChosen : 0 < (ρ.part rest Ctx.Side.upper c).bound := by
                rw [hz, Nat.zero_add] at hp
                exact hp
              exact hRecurse rest c hc hck (by simpa only [hs] using hRS Ctx.Side.upper c)
                (by simpa only [hs] using hChosen)
          rcases hatt with hatt | hatt
          · apply hPair block rest d (ρ.k - 1 - d) hd hdk hc.1 hc.2 hBsmall hRsmall
            rw [← hatt]
            exact hBound
          · apply hPair rest block d (ρ.k - 1 - d) hd hdk hc.1 hc.2 hRsmall hBsmall
            rw [Nat.add_comm, ← hatt]
            exact hBound
      exact hmain σ.childPositions.length σ rfl hpositive hunit hbound
    have hShadow (τ : Ctx.Context) (s : Ctx.Side) (N : ℕ)
      (hN : N ∈ τ.levelsOn s 0)
      (hnew : ∀ j, 1 ≤ j → j < N → τ.sideAt j = s)
      (x l y r z : ℕ) (hx : x < τ.word.length) (hz : z < τ.word.length)
      (hxl : x < l) (hly : l < y) (hyr : y < r) (hrz : r < z)
      (hl : τ.letterAt l = Ctx.Letter.ext N s)
      (hr : τ.letterAt r = Ctx.Letter.ext N s)
      (hxsite : τ.letterAt x = Ctx.Letter.child ∨
        ∃ j, 1 ≤ j ∧ j < N ∧ τ.letterAt x = Ctx.Letter.ext j s)
      (hysite : τ.letterAt y = Ctx.Letter.child ∨
        ∃ j, 1 ≤ j ∧ j < N ∧ τ.letterAt y = Ctx.Letter.ext j s)
      (hzsite : τ.letterAt z = Ctx.Letter.child ∨
        ∃ j, 1 ≤ j ∧ j < N ∧ τ.letterAt z = Ctx.Letter.ext j s)
      (hruns : τ.numRuns ≤ 1) :
      ∀ p ∈ τ.childPositions, 2 ≤ τ.chainExt s p p := by
      classical
      -- Reuse accepted R18 raw one-run interval proof, then R15 ordered two-level fold witnesses.
      have hInterval (ρ : Ctx.Context) (hruns : ρ.numRuns ≤ 1)
          (hchildNe : ρ.childPositions ≠ []) :
          ∃ b, ρ.childPositions = List.range' b ρ.childPositions.length := by
        obtain ⟨b, tail, hcons⟩ := List.exists_cons_of_ne_nil hchildNe
        have hb : b ∈ ρ.childPositions := by
          rw [hcons]
          exact List.mem_cons_self
        have hordered : ρ.childPositions.Pairwise (· ≤ ·) :=
          (Ctx.Context.childPositions_pairwise ρ).imp le_of_lt
        have hmin : ∀ p ∈ ρ.childPositions, b ≤ p := by
          intro p hp
          have h := hordered.rel_head hp
          simpa [hcons] using h
        let starts := (List.range ρ.word.length).filter fun p ↦
          ρ.letterAt p = Ctx.Letter.child ∧
            (p = 0 ∨ ρ.letterAt (p - 1) ≠ Ctx.Letter.child)
        have hstartsLen : starts.length ≤ 1 := by
          simpa [starts, Ctx.Context.numRuns] using hruns
        have hstartsNodup : starts.Nodup := by
          exact List.nodup_range.filter _
        have hbRange : b < ρ.word.length := by
          exact List.mem_range.1 (List.mem_filter.1 hb).1
        have hbLetter : ρ.letterAt b = Ctx.Letter.child :=
          of_decide_eq_true (List.mem_filter.1 hb).2
        have hbStartCondition :
            b = 0 ∨ ρ.letterAt (b - 1) ≠ Ctx.Letter.child := by
          by_cases hb0 : b = 0
          · exact Or.inl hb0
          · right
            intro hprev
            have hprevMem : b - 1 ∈ ρ.childPositions := by
              apply List.mem_filter.2
              exact ⟨List.mem_range.2 (by omega), by simpa using hprev⟩
            have := hmin (b - 1) hprevMem
            omega
        have hbStart : b ∈ starts := by
          simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
          exact ⟨hbRange, hbLetter, hbStartCondition⟩
        have hstartUnique : ∀ p ∈ starts, p = b := by
          intro p hp
          by_contra hpb
          have hsubset : ({b, p} : Finset ℕ) ⊆ starts.toFinset := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact List.mem_toFinset.2 hbStart
            · exact List.mem_toFinset.2 hp
          have hcard := Finset.card_le_card hsubset
          rw [List.toFinset_card_of_nodup hstartsNodup] at hcard
          have htwo : ({b, p} : Finset ℕ).card = 2 := by
            simp [Ne.symm hpb]
          rw [htwo] at hcard
          omega
        have hpred : ∀ p ∈ ρ.childPositions, p ≠ b → p - 1 ∈ ρ.childPositions := by
          intro p hp hpb
          have hpRange : p < ρ.word.length :=
            List.mem_range.1 (List.mem_filter.1 hp).1
          have hpLetter : ρ.letterAt p = Ctx.Letter.child :=
            of_decide_eq_true (List.mem_filter.1 hp).2
          have hpPositive : 0 < p := by
            have := hmin p hp
            omega
          by_contra hprevMem
          have hprevLetter : ρ.letterAt (p - 1) ≠ Ctx.Letter.child := by
            intro hletter
            apply hprevMem
            apply List.mem_filter.2
            exact ⟨List.mem_range.2 (by omega), by simpa using hletter⟩
          have hpStart : p ∈ starts := by
            simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
            exact ⟨hpRange, hpLetter, Or.inr hprevLetter⟩
          exact hpb (hstartUnique p hpStart)
        have hfill : ∀ p ∈ ρ.childPositions, ∀ q, b ≤ q → q ≤ p →
            q ∈ ρ.childPositions := by
          intro p
          induction p using Nat.strong_induction_on with
          | h p ih =>
            intro hp q hbq hqp
            by_cases hpb : p = b
            · have : q = b := by omega
              simpa [this] using hb
            by_cases hqp' : q = p
            · simpa [hqp'] using hp
            exact ih (p - 1) (by omega) (hpred p hp hpb) q hbq (by omega)
        let e := ρ.childPositions.getLast hchildNe
        have he : e ∈ ρ.childPositions := by
          dsimp [e]
          exact List.getLast_mem _
        have hmax : ∀ p ∈ ρ.childPositions, p ≤ e := by
          intro p hp
          simpa [e] using hordered.rel_getLast hp
        have hbe : b ≤ e := hmin e he
        have hmemRange : ∀ p, p ∈ ρ.childPositions ↔
            p ∈ List.range' b (e + 1 - b) := by
          intro p
          simp only [List.mem_range'_1]
          constructor
          · intro hp
            exact ⟨hmin p hp, by have := hmax p hp; omega⟩
          · rintro ⟨hbp, hp⟩
            exact hfill e he p hbp (by omega)
        have hperm : ρ.childPositions.Perm (List.range' b (e + 1 - b)) :=
          (List.perm_ext_iff_of_nodup (Ctx.Context.childPositions_nodup ρ)
            List.nodup_range').2 hmemRange
        have hrange : ρ.childPositions = List.range' b (e + 1 - b) :=
          List.Perm.eq_of_pairwise' (r := (· ≤ ·)) hordered List.pairwise_le_range' hperm
        have hlen : ρ.childPositions.length = e + 1 - b := by
          rw [hrange]
          simp
        have hinterval : ρ.childPositions = List.range' b ρ.childPositions.length := by
          rw [hlen]
          exact hrange
        exact ⟨b, hinterval⟩
      have hNlen : N ≤ τ.maxima.length := by
        have hm := (List.mem_filter.mp hN).1
        simp only [Ctx.Context.levels, List.mem_map, List.mem_range] at hm
        obtain ⟨i, hi, he⟩ := hm
        omega
      have hNewOn (j : ℕ) (hj : 1 ≤ j) (hjN : j < N) : j ∈ τ.levelsOn s 0 := by
        apply List.mem_filter.mpr
        refine ⟨?_, by simp [hnew j hj hjN]⟩
        simp only [Ctx.Context.levels, List.mem_map, List.mem_range]
        exact ⟨j - 1, by omega, by omega⟩
      have hSorted : (τ.levelsOn s 0).Pairwise (· < ·) := by
        apply List.Pairwise.filter
        exact List.pairwise_lt_range.map (fun i => i + 1) (fun i j h => by dsimp; omega)
      have hTwoSub (j : ℕ) (hj : j ∈ τ.levelsOn s 0) (hjN : j < N) :
          [j, N].Sublist (τ.levelsOn s 0) := by
        have hs : [j, N].Pairwise (· < ·) := by simp [hjN]
        have hsub : [j, N] ⊆ τ.levelsOn s 0 := by
          intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · exact hj
          · exact hN
        have he : (τ.levelsOn s 0).filter (· ∈ [j, N]) = [j, N] := by
          apply (hSorted.filter _).eq_of_mem_iff hs
          intro q
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨And.right, fun hq => ⟨hsub hq, hq⟩⟩
        rw [← he]
        exact List.filter_sublist
      have hExtMem (q j : ℕ) (hq : q < τ.word.length)
          (he : τ.letterAt q = Ctx.Letter.ext j s) : q ∈ τ.extPositions j := by
        simp [Ctx.Context.extPositions, hq, he]
      have hOneLeft (j q p : ℕ) (hj : j ∈ τ.levelsOn s 0)
          (hq : q ∈ τ.extPositions j) (hqp : q < p) : 1 ≤ τ.leftExt s 0 p := by
        have hm : q ∈ (τ.extPositions j).filter (· < p) := by simp [hq, hqp]
        have hne := List.ne_nil_of_mem hm
        have hv := Ctx.le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
        change _ ≤ τ.leftExt s 0 p at hv
        simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
          List.getLast?_eq_some_getLast hne] using hv
      have hOneRight (j q p : ℕ) (hj : j ∈ τ.levelsOn s 0)
          (hq : q ∈ τ.extPositions j) (hpq : p < q) : 1 ≤ τ.rightExt s 0 p := by
        have hm : q ∈ (τ.extPositions j).filter (p < ·) := by simp [hq, hpq]
        have hne := List.ne_nil_of_mem hm
        have hv := Ctx.le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (Ctx.Context.rightStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
        change _ ≤ τ.rightExt s 0 p at hv
        simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
          List.head?_eq_some_head hne] using hv
      have hTwoLeft (j q v p : ℕ) (hj : j ∈ τ.levelsOn s 0) (hjN : j < N)
          (hq : q ∈ τ.extPositions j) (hv : v ∈ τ.extPositions N)
          (hvq : v < q) (hqp : q < p) : 2 ≤ τ.leftExt s 0 p := by
        have hSort : (τ.extPositions j).Pairwise (· ≤ ·) :=
          (List.pairwise_lt_range.filter _).imp le_of_lt
        have hm : q ∈ (τ.extPositions j).filter (· < p) := by simp [hq, hqp]
        have hne := List.ne_nil_of_mem hm
        let a := ((τ.extPositions j).filter (· < p)).getLast hne
        have ha : ((τ.extPositions j).filter (· < p)).getLast? = some a :=
          List.getLast?_eq_some_getLast hne
        have hqa : q ≤ a := (hSort.filter _).rel_getLast hm
        have hmOld : v ∈ (τ.extPositions N).filter (· < a) := by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hv, by omega⟩
        have hneOld := List.ne_nil_of_mem hmOld
        have hmax := Ctx.le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[j, N], List.mem_sublists.mpr (hTwoSub j hj hjN), rfl⟩)
        change _ ≤ τ.leftExt s 0 p at hmax
        simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep, ha,
          List.getLast?_eq_some_getLast hneOld] using hmax
      have hTwoRight (j q v p : ℕ) (hj : j ∈ τ.levelsOn s 0) (hjN : j < N)
          (hq : q ∈ τ.extPositions j) (hv : v ∈ τ.extPositions N)
          (hpq : p < q) (hqv : q < v) : 2 ≤ τ.rightExt s 0 p := by
        have hSort : (τ.extPositions j).Pairwise (· ≤ ·) :=
          (List.pairwise_lt_range.filter _).imp le_of_lt
        have hm : q ∈ (τ.extPositions j).filter (p < ·) := by simp [hq, hpq]
        have hne := List.ne_nil_of_mem hm
        let a := ((τ.extPositions j).filter (p < ·)).head hne
        have ha : ((τ.extPositions j).filter (p < ·)).head? = some a :=
          List.head?_eq_some_head hne
        have haq : a ≤ q := (hSort.filter _).rel_head hm
        have hmOld : v ∈ (τ.extPositions N).filter (a < ·) := by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hv, by omega⟩
        have hneOld := List.ne_nil_of_mem hmOld
        have hmax := Ctx.le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (Ctx.Context.rightStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[j, N], List.mem_sublists.mpr (hTwoSub j hj hjN), rfl⟩)
        change _ ≤ τ.rightExt s 0 p at hmax
        simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep, ha,
          List.head?_eq_some_head hneOld] using hmax
      intro p hp
      have hne : τ.childPositions ≠ [] := List.ne_nil_of_mem hp
      obtain ⟨b, hspan⟩ := hInterval τ hruns hne
      have hMem (q : ℕ) : q ∈ τ.childPositions ↔
          b ≤ q ∧ q < b + τ.childPositions.length := by
        rw [hspan]
        simpa only [List.length_range'] using
          (List.mem_range'_1 (m := q) (s := b) (n := τ.childPositions.length))
      have hpSpan := (hMem p).mp hp
      have hNoCross (q v : ℕ) (hq : q < τ.word.length)
          (hv : τ.letterAt v = Ctx.Letter.ext N s)
          (hbetween : (p < v ∧ v < q) ∨ (q < v ∧ v < p)) :
          τ.letterAt q ≠ Ctx.Letter.child := by
        intro hqchild
        have hqmem : q ∈ τ.childPositions := by
          simp [Ctx.Context.childPositions, hq, hqchild]
        have hqSpan := (hMem q).mp hqmem
        have hvmem : v ∈ τ.childPositions := (hMem v).mpr (by rcases hbetween with h | h <;> omega)
        have hvchild : τ.letterAt v = Ctx.Letter.child :=
          of_decide_eq_true (List.mem_filter.mp hvmem).2
        rw [hv] at hvchild
        cases hvchild
      have hyBound : y < τ.word.length := by omega
      have hlBound : l < τ.word.length := by omega
      have hrBound : r < τ.word.length := by omega
      have hpneL : p ≠ l := by
        intro he
        subst p
        have hc : τ.letterAt l = Ctx.Letter.child := of_decide_eq_true (List.mem_filter.mp hp).2
        rw [hl] at hc
        cases hc
      have hpneR : p ≠ r := by
        intro he
        subst p
        have hc : τ.letterAt r = Ctx.Letter.child := of_decide_eq_true (List.mem_filter.mp hp).2
        rw [hr] at hc
        cases hc
      change 2 ≤ τ.leftExt s 0 p + τ.rightExt s 0 p
      by_cases hpl : p < l
      · have hnotY := hNoCross y l hyBound hl (Or.inl ⟨hpl, hly⟩)
        rcases hysite with h | ⟨j, hj, hjN, he⟩
        · exact (hnotY h).elim
        · have hright := hTwoRight j y r p (hNewOn j hj hjN) hjN
            (hExtMem y j hyBound he) (hExtMem r N hrBound hr) (by omega) hyr
          omega
      have hlp : l < p := by omega
      by_cases hpr : p < r
      · have hnotX := hNoCross x l hx hl (Or.inr ⟨hxl, hlp⟩)
        have hnotZ := hNoCross z r hz hr (Or.inl ⟨hpr, hrz⟩)
        rcases hxsite with h | ⟨j, hj, hjN, he⟩
        · exact (hnotX h).elim
        rcases hzsite with h | ⟨i, hi, hiN, he'⟩
        · exact (hnotZ h).elim
        have hleft := hOneLeft j x p (hNewOn j hj hjN) (hExtMem x j hx he) (by omega)
        have hright := hOneRight i z p (hNewOn i hi hiN) (hExtMem z i hz he') (by omega)
        omega
      have hrp : r < p := by omega
      have hnotY := hNoCross y r hyBound hr (Or.inr ⟨hyr, hrp⟩)
      rcases hysite with h | ⟨j, hj, hjN, he⟩
      · exact (hnotY h).elim
      · have hleft := hTwoLeft j y l p (hNewOn j hj hjN) hjN
          (hExtMem y j hyBound he) (hExtMem l N hlBound hl) hly (by omega)
        omega
    have hThree (σ : Ctx.Context) (s : Ctx.Side)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 3 ≤ σ.numRuns) :
      ∃ x l y r z,
        x ∈ σ.childPositions ∧ y ∈ σ.childPositions ∧ z ∈ σ.childPositions ∧
        x < l ∧ l < y ∧ y < r ∧ r < z ∧
        σ.letterAt l = Ctx.Letter.ext 1 s ∧ σ.letterAt r = Ctx.Letter.ext 1 s := by
      classical
      let starts := (List.range σ.word.length).filter fun p =>
        σ.letterAt p = Ctx.Letter.child ∧
          (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child)
      have hlen : 3 ≤ starts.length := hruns
      have hsort : starts.Pairwise (· < ·) := List.pairwise_lt_range.filter _
      have hData (p : ℕ) (hp : p ∈ starts) :
          p < σ.word.length ∧ σ.letterAt p = Ctx.Letter.child ∧
            (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child) := by
        simpa only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq] using hp
      have hChild (p : ℕ) (hp : p ∈ starts) : p ∈ σ.childPositions := by
        have hd := hData p hp
        simp [Ctx.Context.childPositions, hd.1, hd.2.1]
      have hLetter (p : ℕ) (hp : p < σ.word.length) :
          σ.letterAt p = Ctx.Letter.child ∨ σ.letterAt p = Ctx.Letter.ext 1 s := by
        have he : σ.letterAt p = σ.word[p] := by
          simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hp]
        rw [he]
        exact hletters _ (List.getElem_mem hp)
      cases hs : starts with
      | nil => simp [hs] at hlen
      | cons x xs =>
        cases hxs : xs with
        | nil => simp [hs, hxs] at hlen
        | cons y ys =>
          cases hys : ys with
          | nil => simp [hs, hxs, hys] at hlen
          | cons z zs =>
            have hform : starts = x :: y :: z :: zs := by rw [hs, hxs, hys]
            have hx : x ∈ starts := by rw [hform]; simp
            have hy : y ∈ starts := by rw [hform]; simp
            have hz : z ∈ starts := by rw [hform]; simp
            have hsort' : (x :: y :: z :: zs).Pairwise (· < ·) := by rw [← hform]; exact hsort
            have hxy : x < y := (List.pairwise_cons.mp hsort').1 _ (by simp)
            have hyz : y < z := (List.pairwise_cons.mp (List.pairwise_cons.mp hsort').2).1 _ (by simp)
            have hxD := hData x hx
            have hyD := hData y hy
            have hzD := hData z hz
            have hlnot : σ.letterAt (y - 1) ≠ Ctx.Letter.child := by
              rcases hyD.2.2 with h0 | hno
              · omega
              · exact hno
            have hrnot : σ.letterAt (z - 1) ≠ Ctx.Letter.child := by
              rcases hzD.2.2 with h0 | hno
              · omega
              · exact hno
            have hl : σ.letterAt (y - 1) = Ctx.Letter.ext 1 s :=
              (hLetter (y - 1) (by omega)).resolve_left hlnot
            have hr : σ.letterAt (z - 1) = Ctx.Letter.ext 1 s :=
              (hLetter (z - 1) (by omega)).resolve_left hrnot
            have hxl : x < y - 1 := by
              have hne : x ≠ y - 1 := by
                intro he
                rw [he, hl] at hxD
                cases hxD.2.1
              omega
            have hyr : y < z - 1 := by
              have hne : y ≠ z - 1 := by
                intro he
                rw [he, hr] at hyD
                cases hyD.2.1
              omega
            exact ⟨x, y - 1, y, z - 1, z, hChild x hx, hChild y hy, hChild z hz,
              hxl, by omega, hyr, by omega, hl, hr⟩
    have hLetter (p : ℕ) (hp : p < σ.word.length) :
        σ.letterAt p = Ctx.Letter.child ∨ σ.letterAt p = Ctx.Letter.ext 1 s := by
      have he : σ.letterAt p = σ.word[p] := by
        simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hp]
      rw [he]
      exact hletters _ (List.getElem_mem hp)
    have hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j := by
      intro p j v he
      have hp : p < σ.word.length := by
        by_contra hn
        rw [Ctx.Context.letterAt_of_length_le σ (by omega)] at he
        cases he
      rcases hLetter p hp with hc | hm
      · rw [he] at hc
        cases hc
      · rw [he] at hm
        have hj := (Ctx.Letter.ext.inj hm).1
        omega
    by_contra hzero
    have hbound : 0 < σ.bound := by omega
    obtain ⟨τ, history, ha, hu, hk, hlen, hmaxτ, hlegal,
      hrunτ, hbase, hchildren, hword, hold, hnew⟩ :=
      hLeaf σ hpositive s t hne hunit hbound
    obtain ⟨x, l, y, r, z, hx, hy, hz, hxl, hly, hyr, hrz, hl, hr⟩ :=
      hThree σ s hletters hruns
    have hxR : x < σ.word.length := List.mem_range.mp (List.mem_filter.mp hx).1
    have hyR : y < σ.word.length := List.mem_range.mp (List.mem_filter.mp hy).1
    have hzR : z < σ.word.length := List.mem_range.mp (List.mem_filter.mp hz).1
    have hlR : l < σ.word.length := by omega
    have hrR : r < σ.word.length := by omega
    have hxC : σ.letterAt x = Ctx.Letter.child := of_decide_eq_true (List.mem_filter.mp hx).2
    have hyC : σ.letterAt y = Ctx.Letter.child := of_decide_eq_true (List.mem_filter.mp hy).2
    have hzC : σ.letterAt z = Ctx.Letter.child := of_decide_eq_true (List.mem_filter.mp hz).2
    have hside : σ.sideAt 1 = s := by
      have hlMem : l ∈ σ.extPositions 1 := by
        simp [Ctx.Context.extPositions, hlR, hl]
      obtain ⟨q, qs, hcons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hlMem)
      have hq : q ∈ σ.extPositions 1 := by rw [hcons]; exact List.mem_cons_self
      have hqR : q < σ.word.length := List.mem_range.mp (List.mem_filter.mp hq).1
      have hqNot : σ.letterAt q ≠ Ctx.Letter.child := by
        intro hc
        simp [Ctx.Context.extPositions, hc] at hq
      have hqS := (hLetter q hqR).resolve_left hqNot
      simp only [Ctx.Context.sideAt, hcons, List.head?_cons, hqS]
    let N := history.length + 1
    have hN : N ∈ τ.levelsOn s 0 := by
      apply List.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · simp only [Ctx.Context.levels, List.mem_map, List.mem_range]
        refine ⟨history.length, ?_, ?_⟩
        · rw [hmaxτ, hmax]
          simp
        · rfl
      · have hNside : τ.sideAt N = s := by
          simpa only [N, Nat.add_comm, hside] using hold 1 (by omega)
        simp [hNside]
    have hnewN : ∀ j, 1 ≤ j → j < N → τ.sideAt j = s := by
      intro j hj hjN
      exact hnew j hj (by dsimp [N] at hjN; omega)
    have hSite (p : ℕ) (hp : p < σ.word.length) (hc : σ.letterAt p = Ctx.Letter.child) :
        τ.letterAt p = Ctx.Letter.child ∨
          ∃ j, 1 ≤ j ∧ j < N ∧ τ.letterAt p = Ctx.Letter.ext j s := by
      have hw := hword p hp
      rw [hc] at hw
      rcases hw with h | ⟨j, hj, hjlen, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, by dsimp [N]; omega, he⟩
    have hOld (p : ℕ) (hp : p < σ.word.length) (he : σ.letterAt p = Ctx.Letter.ext 1 s) :
        τ.letterAt p = Ctx.Letter.ext N s := by
      have hw := hword p hp
      rw [he] at hw
      simpa only [N, Nat.add_comm] using hw
    have hcost : ∀ p ∈ τ.childPositions, 2 ≤ τ.chainExt s p p :=
      hShadow τ s N hN hnewN x l y r z (by rw [hlen]; exact hxR)
        (by rw [hlen]; exact hzR) hxl hly hyr hrz
        (hOld l hlR hl) (hOld r hrR hr) (hSite x hxR hxC)
        (hSite y hyR hyC) (hSite z hzR hzC) hrunτ
    have hglobal : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => τ.u | Ctx.Side.upper => τ.a) s ≤ 3 := by
      simpa only [ha, hu] using hchosen
    cases hc : τ.childPositions with
    | nil => simp [Ctx.Context.base, hc] at hbase
    | cons p ps =>
      have hp : p ∈ τ.childPositions := by rw [hc]; exact List.mem_cons_self
      have hpCost := hcost p hp
      cases hs : s with
      | lower =>
        have hg : τ.u ≤ 3 := by simpa only [hs] using hglobal
        have hge : 2 ≤ τ.chainExt Ctx.Side.lower p p := by simpa only [hs] using hpCost
        have hz : τ.u - 1 - τ.chainExt Ctx.Side.lower p p = 0 := by omega
        have hlim : τ.cupLimit p p = 0 := by
          simp only [Ctx.Context.cupLimit, hz, Nat.zero_min]
        simp [Ctx.Context.base, hc, hlim] at hbase
      | upper =>
        have hg : τ.a ≤ 3 := by simpa only [hs] using hglobal
        have hge : 2 ≤ τ.chainExt Ctx.Side.upper p p := by simpa only [hs] using hpCost
        have hz : τ.a - 1 - τ.chainExt Ctx.Side.upper p p = 0 := by omega
        have hlim : τ.capLimit p p = 0 := by
          simp only [Ctx.Context.capLimit, hz, Nat.zero_min]
        simp [Ctx.Context.base, hc, hlim] at hbase

  have hRootEnds (σ : Ctx.Context) (s : Ctx.Side)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 2 ≤ σ.numRuns) :
      (σ.word.head? = some Ctx.Letter.child ∨ σ.word.head? = some (Ctx.Letter.ext 1 s)) ∧
      (σ.word.getLast? = some Ctx.Letter.child ∨ σ.word.getLast? = some (Ctx.Letter.ext 1 s)) ∧
      (σ.word.head? = some (Ctx.Letter.ext 1 s) →
        0 ∈ σ.extPositions 1 ∧ ∀ p ∈ σ.childPositions, 0 < p) ∧
      (σ.word.getLast? = some (Ctx.Letter.ext 1 s) →
        σ.word.length - 1 ∈ σ.extPositions 1 ∧
        ∀ p ∈ σ.childPositions, p < σ.word.length - 1) := by
    classical
    obtain ⟨first, sep, other, hfirst, hother, hFirstSep, hSepOther, hSep⟩ :=
      hTwoSites σ s hletters hruns
    have hFirstR := List.mem_range.mp (List.mem_filter.mp hfirst).1
    have hLen : 0 < σ.word.length := by omega
    have hWordNe : σ.word ≠ [] := by intro he; simp [he] at hLen
    have hHead : σ.word.head? = some Ctx.Letter.child ∨
        σ.word.head? = some (Ctx.Letter.ext 1 s) := by
      obtain ⟨v, tail, hcons⟩ := List.exists_cons_of_ne_nil hWordNe
      rcases hletters v (by rw [hcons]; simp) with hc | hm
      · exact Or.inl (by simp [hcons, hc])
      · exact Or.inr (by simp [hcons, hm])
    have hLast : σ.word.getLast? = some Ctx.Letter.child ∨
        σ.word.getLast? = some (Ctx.Letter.ext 1 s) := by
      have hEq := List.getLast?_eq_some_getLast hWordNe
      rcases hletters _ (List.getLast_mem hWordNe) with hc | hm
      · exact Or.inl (hEq.trans (congrArg some hc))
      · exact Or.inr (hEq.trans (congrArg some hm))
    refine ⟨hHead, hLast, ?_, ?_⟩
    · intro hhead
      obtain ⟨tail, hcons⟩ := List.head?_eq_some_iff.mp hhead
      have hAt : σ.letterAt 0 = Ctx.Letter.ext 1 s := by
        simp [Ctx.Context.letterAt, hcons]
      refine ⟨?_, ?_⟩
      · simp [Ctx.Context.extPositions, hLen, hAt]
      · intro p hp
        have hpAt : σ.letterAt p = Ctx.Letter.child :=
          of_decide_eq_true (List.mem_filter.mp hp).2
        have hpNe : p ≠ 0 := by
          intro he
          rw [he, hAt] at hpAt
          cases hpAt
        omega
    · intro hlast
      have hAt : σ.letterAt (σ.word.length - 1) = Ctx.Letter.ext 1 s := by
        simp only [Ctx.Context.letterAt, ← List.getLast?_eq_getElem?, hlast,
          Option.getD_some]
      refine ⟨?_, ?_⟩
      · simp [Ctx.Context.extPositions, hAt, show σ.word.length - 1 < σ.word.length by omega]
      · intro p hp
        have hpR := List.mem_range.mp (List.mem_filter.mp hp).1
        have hpAt : σ.letterAt p = Ctx.Letter.child :=
          of_decide_eq_true (List.mem_filter.mp hp).2
        have hpNe : p ≠ σ.word.length - 1 := by
          intro he
          rw [he, hAt] at hpAt
          cases hpAt
        omega


  have hExtremeFreshThree (σ : Ctx.Context) (hpositive : ∀ x j v, σ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (hk : 3 ≤ σ.k) (hglobal : 3 ≤ (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)) (hempty : σ.levelsOn s 0 = []) (p r : ℕ) (hp : p ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hrne : r ≠ p) (hextreme : σ.childPositions.head? = some p ∨ σ.childPositions.getLast? = some p) (hpoint : 0 < (match t with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p)) : (σ.part [p] s (σ.k - 2)).bound = 1 := by
    classical
    let τ := σ.part [p] s (σ.k - 2)
    have hrnot : r ∉ [p] := by simpa using hrne
    have hrnew : r ∈ τ.extPositions 1 := by
      rw [Ctx.Context.part_extPositions_one hpositive [p] s (σ.k - 2)]
      exact List.mem_filter.mpr ⟨hr, by simpa using hrnot⟩
    have hFresh : τ.sideAt 1 = s :=
      Ctx.Context.part_sideAt_one_of_mem hpositive [p] s (σ.k - 2) hrnew
    have hLevels : τ.levelsOn s 0 = [1] := by
      rw [Ctx.Context.part_levelsOn_self_zero hFresh, hempty]
      rfl
    have hLeft : τ.leftExt s 0 p ≤ 1 := by
      cases h : ((τ.extPositions 1).filter (· < p)).getLast? <;>
        simp [Ctx.Context.leftExt_eq, hLevels, Ctx.Context.leftStep, h]
    have hRight : τ.rightExt s 0 p ≤ 1 := by
      cases h : ((τ.extPositions 1).filter (p < ·)).head? <;>
        simp [Ctx.Context.rightExt_eq, hLevels, Ctx.Context.rightStep, h]
    have hChain : τ.chainExt s p p ≤ 1 := by
      rcases hextreme with hhead | hlast
      · obtain ⟨tail, hcons⟩ := List.head?_eq_some_iff.mp hhead
        have hNoLeft : (τ.extPositions 1).filter (· < p) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro x hx
          obtain ⟨hx, hxp⟩ := List.mem_filter.mp hx
          rw [Ctx.Context.part_extPositions_one hpositive [p] s (σ.k - 2)] at hx
          have hxc := (List.mem_filter.mp hx).1
          have hord : (p :: tail).Pairwise (· ≤ ·) := by
            simpa [hcons] using (Ctx.Context.childPositions_pairwise σ).imp le_of_lt
          have hpx : p ≤ x := by
            simpa using hord.rel_head (by simpa [hcons] using hxc)
          have hxp' : x < p := by simpa using hxp
          omega
        have hz : τ.leftExt s 0 p = 0 := by
          simp [Ctx.Context.leftExt_eq, hLevels, Ctx.Context.leftStep, hNoLeft]
        simp only [Ctx.Context.chainExt]
        omega
      · have hn : σ.childPositions ≠ [] := List.ne_nil_of_mem hp
        have hlast' : σ.childPositions.getLast hn = p :=
          Option.some.inj ((List.getLast?_eq_some_getLast hn).symm.trans hlast)
        have hNoRight : (τ.extPositions 1).filter (p < ·) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro x hx
          obtain ⟨hx, hpx⟩ := List.mem_filter.mp hx
          rw [Ctx.Context.part_extPositions_one hpositive [p] s (σ.k - 2)] at hx
          have hxc := (List.mem_filter.mp hx).1
          have hxp : x ≤ p := by
            simpa [hlast'] using ((Ctx.Context.childPositions_pairwise σ).imp le_of_lt).rel_getLast hxc
          have hpx' : p < x := by simpa using hpx
          omega
        have hz : τ.rightExt s 0 p = 0 := by
          simp [Ctx.Context.rightExt_eq, hLevels, Ctx.Context.rightStep, hNoRight]
        simp only [Ctx.Context.chainExt]
        omega
    have hMaximum : τ.maximumAt 1 = σ.k - 2 :=
      Ctx.Context.part_maximumAt_one σ [p] s (σ.k - 2)
    have hJoin : τ.joinExt s p p = σ.k - 2 := by
      have hj : τ.joinExt s p p = max (τ.chainExt s p p) (σ.k - 2) := by
        simp [Ctx.Context.joinExt, hLevels, Ctx.Context.leftExt_one,
          Ctx.Context.rightExt_one, hMaximum]
      rw [hj]
      apply max_eq_right
      omega
    have hGlobals : τ.a = σ.a ∧ τ.u = σ.u ∧ τ.k = σ.k := ⟨rfl, rfl, rfl⟩
    have hSelected : (match s with
        | Ctx.Side.lower => τ.cupLimit p p
        | Ctx.Side.upper => τ.capLimit p p) = 1 := by
      cases s <;> simp only [Ctx.Context.cupLimit, Ctx.Context.capLimit,
        hGlobals.1, hGlobals.2.1, hGlobals.2.2, hJoin]
      all_goals simp only at hglobal; omega
    have hFreshNe : τ.sideAt 1 ≠ t := by rw [hFresh]; exact hne
    have hOther : (match t with
        | Ctx.Side.lower => τ.cupLimit p p
        | Ctx.Side.upper => τ.capLimit p p) =
        (match t with
        | Ctx.Side.lower => σ.cupLimit p p
        | Ctx.Side.upper => σ.capLimit p p) := by
      cases t <;> simp only [Ctx.Context.cupLimit, Ctx.Context.capLimit,
        hGlobals.1, hGlobals.2.1, hGlobals.2.2]
      all_goals rw [Ctx.Context.chainExt_part_other hFreshNe,
        Ctx.Context.joinExt_part_other hFreshNe]
    have hOtherPos : 0 < (match t with
        | Ctx.Side.lower => τ.cupLimit p p
        | Ctx.Side.upper => τ.capLimit p p) := by
      cases t <;> rw [hOther] <;> exact hpoint
    have hPoint : 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := by
      cases s <;> cases t
      · exact (hne rfl).elim
      · change τ.cupLimit p p = 1 at hSelected
        exact ⟨by omega, hOtherPos⟩
      · change τ.capLimit p p = 1 at hSelected
        exact ⟨hOtherPos, by omega⟩
      · exact (hne rfl).elim
    have hLower : 1 ≤ τ.bound := by
      change 1 ≤ (σ.part [p] s (σ.k - 2)).bound
      rw [ctx_singleton_part_bound_eq_threshold σ p hp s (σ.k - 2)]
      exact one_le_decomposableThreshold (by change 2 ≤ τ.capLimit p p + 1; omega)
        (by change 2 ≤ τ.cupLimit p p + 1; omega)
    have hOne : 1 ∈ τ.levels := by
      rw [Ctx.Context.part_levels]
      simp
    have hPos : ∀ x j v, τ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j :=
      ctx_part_positive_letters σ [p] s (σ.k - 2)
    have hUpper : τ.bound ≤ 1 :=
      (ctx_bound_le_one_of_large_sibling_maximum τ hPos 1 hOne
        (by rw [hMaximum, hGlobals.2.2])).2
    exact Nat.le_antisymm hUpper hLower

  have hSourcePoint (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
      (ha : σ.a ≤ σ.k) (hu : σ.u ≤ σ.k) (hmk : m ≤ σ.k - 2)
      (s : Ctx.Side) (hside : σ.sideAt 1 = s) (p C : ℕ)
      (hchain : σ.chainExt s p p ≤ C)
      (hglobal : C + 2 ≤ (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s) :
      0 < (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p) s := by
    have hLimits := ctx_single_level_limits_exact σ m hmax ha hu s hside p p
    cases s with
    | lower =>
      change 0 < σ.cupLimit p p
      rw [hLimits.2.2.2.1]
      change C + 2 ≤ σ.u at hglobal
      omega
    | upper =>
      change 0 < σ.capLimit p p
      rw [hLimits.2.2.2.1]
      change C + 2 ≤ σ.a at hglobal
      omega
  have hExtremeSourcePoint (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
      (ha : σ.a ≤ σ.k) (hu : σ.u ≤ σ.k) (hmk : m ≤ σ.k - 2)
      (s : Ctx.Side)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 2 ≤ σ.numRuns)
      (hglobal : 3 + (if σ.word.head? = some (Ctx.Letter.ext 1 s) ∧
        σ.word.getLast? = some (Ctx.Letter.ext 1 s) then 1 else 0) ≤
        (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s) :
      ∃ p, p ∈ σ.childPositions ∧
        (σ.childPositions.head? = some p ∨ σ.childPositions.getLast? = some p) ∧
        0 < (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p) s := by
    classical
    have hData := hRootData σ s hletters hruns
    have hEnds := hRootEnds σ s hletters hruns
    have hLevels : σ.levelsOn s 0 = [1] := by
      simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hData.2]
    have hLeft (p : ℕ) : σ.leftExt s 0 p ≤ 1 := by
      cases h : ((σ.extPositions 1).filter (· < p)).getLast? <;>
        simp [Ctx.Context.leftExt_eq, hLevels, Ctx.Context.leftStep, h]
    have hRight (p : ℕ) : σ.rightExt s 0 p ≤ 1 := by
      cases h : ((σ.extPositions 1).filter (p < ·)).head? <;>
        simp [Ctx.Context.rightExt_eq, hLevels, Ctx.Context.rightStep, h]
    obtain ⟨first, sep, other, hfirst, hother, hFirstSep, hSepOther, hSep⟩ :=
      hTwoSites σ s hletters hruns
    obtain ⟨p, tail, hcons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hfirst)
    have hp : p ∈ σ.childPositions := by rw [hcons]; exact List.mem_cons_self
    have hheadP : σ.childPositions.head? = some p := by rw [hcons]; rfl
    have hMin : ∀ q ∈ σ.childPositions, p ≤ q := by
      intro q hq
      simpa [hcons] using ((Ctx.Context.childPositions_pairwise σ).imp le_of_lt).rel_head hq
    have hFirstR := List.mem_range.mp (List.mem_filter.mp hfirst).1
    have hLen : 0 < σ.word.length := by omega
    rcases hEnds.1 with hhead | hhead
    · have hh : σ.word.head? ≠ some (Ctx.Letter.ext 1 s) := by simp [hhead]
      obtain ⟨wordTail, hword⟩ := List.head?_eq_some_iff.mp hhead
      have hZeroAt : σ.letterAt 0 = Ctx.Letter.child := by
        simp [Ctx.Context.letterAt, hword]
      have hZeroChild : 0 ∈ σ.childPositions := by
        simp [Ctx.Context.childPositions, hLen, hZeroAt]
      have hpZero : p = 0 := by have h := hMin 0 hZeroChild; omega
      have hNoLeft : (σ.extPositions 1).filter (· < p) = [] := by simp [hpZero]
      have hLeftZero : σ.leftExt s 0 p = 0 := by
        simp [Ctx.Context.leftExt_eq, hLevels, Ctx.Context.leftStep, hNoLeft]
      have hChain : σ.chainExt s p p ≤ 1 := by
        simp only [Ctx.Context.chainExt]
        have h := hRight p
        omega
      have hG : 3 ≤ (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s := by
        simpa [hh] using hglobal
      exact ⟨p, hp, Or.inl hheadP, hSourcePoint σ m hmax ha hu hmk s hData.2 p 1 hChain hG⟩
    · rcases hEnds.2.1 with hlast | hlast
      · let q := σ.word.length - 1
        have hLastAt : σ.letterAt q = Ctx.Letter.child := by
          simp only [Ctx.Context.letterAt, q, ← List.getLast?_eq_getElem?, hlast,
            Option.getD_some]
        have hqR : q < σ.word.length := by dsimp [q]; omega
        have hq : q ∈ σ.childPositions := by
          simp [Ctx.Context.childPositions, hqR, hLastAt]
        have hn : σ.childPositions ≠ [] := List.ne_nil_of_mem hq
        have hLastEq : σ.childPositions.getLast hn = q := by
          have hqLe := ((Ctx.Context.childPositions_pairwise σ).imp le_of_lt).rel_getLast hq
          have hLastMem := List.getLast_mem hn
          have hLastR := List.mem_range.mp (List.mem_filter.mp hLastMem).1
          dsimp [q] at *
          omega
        have hLastP : σ.childPositions.getLast? = some q := by
          rw [List.getLast?_eq_some_getLast hn, hLastEq]
        have hNoRight : (σ.extPositions 1).filter (q < ·) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro x hx
          have hxR := List.mem_range.mp (List.mem_filter.mp hx).1
          have hxq : ¬ q < x := by dsimp [q]; omega
          simpa using hxq
        have hRightZero : σ.rightExt s 0 q = 0 := by
          simp [Ctx.Context.rightExt_eq, hLevels, Ctx.Context.rightStep, hNoRight]
        have hChain : σ.chainExt s q q ≤ 1 := by
          simp only [Ctx.Context.chainExt]
          have h := hLeft q
          omega
        have ht : σ.word.getLast? ≠ some (Ctx.Letter.ext 1 s) := by simp [hlast]
        have hG : 3 ≤ (fun v : Ctx.Side => match v with
            | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s := by
          simpa [ht] using hglobal
        exact ⟨q, hq, Or.inr hLastP,
          hSourcePoint σ m hmax ha hu hmk s hData.2 q 1 hChain hG⟩
      · have hChain : σ.chainExt s p p ≤ 2 := by
          simp only [Ctx.Context.chainExt]
          have hl := hLeft p
          have hr := hRight p
          omega
        have hG : 4 ≤ (fun v : Ctx.Side => match v with
            | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s := by
          simpa [hhead, hlast] using hglobal
        exact ⟨p, hp, Or.inl hheadP,
          hSourcePoint σ m hmax ha hu hmk s hData.2 p 2 hChain hG⟩

  have hExtremeBlock (σ : Ctx.Context) (p : ℕ)
      (hcount : 2 ≤ σ.childPositions.length)
      (hextreme : σ.childPositions.head? = some p ∨ σ.childPositions.getLast? = some p) :
      [p] ∈ σ.blocks := by
    classical
    rcases hextreme with hhead | hlast
    · obtain ⟨tail, hcons⟩ := List.head?_eq_some_iff.mp hhead
      simp only [Ctx.Context.blocks, List.mem_filter, List.mem_flatMap,
        List.mem_range, List.mem_map, decide_eq_true_eq]
      refine ⟨⟨0, by omega, 0, by omega, ?_⟩, ?_⟩
      · simp [hcons]
      · simp only [List.length_singleton]; omega
    · obtain ⟨beforeTail, hcons⟩ := List.getLast?_eq_some_iff.mp hlast
      have hlen : σ.childPositions.length = beforeTail.length + 1 := by simp [hcons]
      simp only [Ctx.Context.blocks, List.mem_filter, List.mem_flatMap,
        List.mem_range, List.mem_map, decide_eq_true_eq]
      refine ⟨⟨beforeTail.length, by omega, 0, by omega, ?_⟩, ?_⟩
      · simp [hcons]
      · simp only [List.length_singleton]; omega
  have hOppositeExtremeLower (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
      (hk : 3 ≤ σ.k) (ha : σ.a ≤ σ.k) (hu : σ.u ≤ σ.k) (hmk : m ≤ σ.k - 2)
      (s t : Ctx.Side) (hne : s ≠ t)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 2 ≤ σ.numRuns)
      (hchosen : 3 + (if σ.word.head? = some (Ctx.Letter.ext 1 s) ∧
        σ.word.getLast? = some (Ctx.Letter.ext 1 s) then 1 else 0) ≤
        (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s)
      (hother : 3 ≤ (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t) : 1 ≤ σ.bound := by
    classical
    have hData := hRootData σ s hletters hruns
    obtain ⟨p, hp, hextreme, hpoint⟩ := hExtremeSourcePoint σ m hmax ha hu hmk
      s hletters hruns hchosen
    obtain ⟨first, sep, other, hfirst, hotherChild, hFirstSep, hSepOther, hSep⟩ :=
      hTwoSites σ s hletters hruns
    have hRemoved : ∃ r, r ∈ σ.childPositions ∧ r ≠ p := by
      by_cases heq : p = first
      · exact ⟨other, hotherChild, by omega⟩
      · exact ⟨first, hfirst, Ne.symm heq⟩
    obtain ⟨r, hr, hrne⟩ := hRemoved
    have hEmpty : σ.levelsOn t 0 = [] := by
      cases s <;> cases t <;>
        first | exact (hne rfl).elim |
          simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hData.2]
    have hPart := hExtremeFreshThree σ hData.1 t s (Ne.symm hne) hk
      (by cases t <;> exact hother) hEmpty p r hp hr hrne hextreme
      (by cases s <;> exact hpoint)
    have hCount : 2 ≤ σ.childPositions.length := hruns.trans (Ctx.numRuns_le_length σ)
    have hBlock := hExtremeBlock σ p hCount hextreme
    cases t with
    | lower =>
      have hCut := (ctx_bound_cut_le σ hruns [p] hBlock (σ.k - 2)
        (by omega) (by rfl)).1
      rw [hPart] at hCut
      omega
    | upper =>
      have hCut := (ctx_bound_cut_le σ hruns [p] hBlock 1 (by omega) (by omega)).2
      have he : σ.k - 1 - 1 = σ.k - 2 := by omega
      rw [he, hPart] at hCut
      omega

  have hAllBracketedZero (σ : Ctx.Context) (s : Ctx.Side) (N x y : ℕ) (hN : N ∈ σ.levels) (hs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions N) (hbracket : ∀ p ∈ σ.childPositions, x < p ∧ p < y) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 3) : (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ = 0) ∧ σ.bound = 0 := by
    classical
    have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
        1 ≤ ρ.leftExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq,hqp]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (leftStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
      change _ ≤ ρ.leftExt v 0 p at hv
      simpa only [List.foldl_cons,List.foldl_nil,leftStep,
        List.getLast?_eq_some_getLast hnonempty] using hv
    have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
        1 ≤ ρ.rightExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq,hpq]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (rightStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
      change _ ≤ ρ.rightExt v 0 p at hv
      simpa only [List.foldl_cons,List.foldl_nil,rightStep,
        List.head?_eq_some_head hnonempty] using hv
    have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN,by simp [hs]⟩
    have hPoint : ∀ p ∈ σ.childPositions,
        baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k = 0 := by
      intro p hp
      have hleft := hOneLeft σ s N p x hNOn hx (hbracket p hp).1
      have hright := hOneRight σ s N p y hNOn hy (hbracket p hp).2
      have hChain : 2 ≤ σ.chainExt s p p := by
        unfold chainExt
        omega
      cases s with
      | lower =>
        dsimp only at hglobal
        have hzero : σ.cupLimit p p = 0 := by
          simp only [cupLimit]
          omega
        simp [baseOf,hzero]
      | upper =>
        dsimp only at hglobal
        have hzero : σ.capLimit p p = 0 := by
          simp only [capLimit]
          omega
        simp [baseOf,hzero]
    have hMap :
        σ.childPositions.map (fun p => baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k) =
          σ.childPositions.map (fun _ => 0) := by
      apply List.map_congr_left
      intro p hp
      exact hPoint p hp
    have hBound : σ.bound = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [hMap,List.sum_map_zero] using ctx_bound_le_sum_point_bases σ
    have hFuel (fuel : ℕ) : boundFuel fuel σ = 0 := by
      have hle : boundFuel fuel σ ≤ σ.bound := by
        by_cases hf : σ.childPositions.length+1 ≤ fuel
        · exact (boundFuel_eq_bound σ hf).le
        · exact boundFuel_mono (by omega : fuel ≤ σ.childPositions.length+1) σ
      rw [hBound] at hle
      exact Nat.eq_zero_of_le_zero hle
    exact ⟨hFuel,hBound⟩

  have hSaturatedExact (σ : Ctx.Context) (hmax : σ.maxima = [σ.k - 2])
    (hk : 3 ≤ σ.k) (ha : σ.a ≤ σ.k) (hu : σ.u ≤ σ.k)
    (s t : Ctx.Side) (hne : s ≠ t)
    (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
    (hruns : 2 ≤ σ.numRuns) :
    σ.bound = if 3 ≤ (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t ∧
      3 + (if σ.word.head? = some (Ctx.Letter.ext 1 s) ∧
        σ.word.getLast? = some (Ctx.Letter.ext 1 s) then 1 else 0) ≤
        (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s
      then 1 else 0 := by
    classical
    have hData := hRootData σ s hletters hruns
    have hEnds := hRootEnds σ s hletters hruns
    have hN : 1 ∈ σ.levels := by simp [Ctx.Context.levels, hmax]
    have hNOn : 1 ∈ σ.levelsOn s 0 := by
      simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hData.2]
    have hMaximum : σ.maximumAt 1 = σ.k - 2 := by
      simp [Ctx.Context.maximumAt, hmax]
    have hUpper : σ.bound ≤ 1 :=
      (ctx_bound_le_one_of_large_sibling_maximum σ hData.1 1 hN
        (by rw [hMaximum])).2
    by_cases hGood : 3 ≤ (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t ∧
        3 + (if σ.word.head? = some (Ctx.Letter.ext 1 s) ∧
          σ.word.getLast? = some (Ctx.Letter.ext 1 s) then 1 else 0) ≤
          (fun v : Ctx.Side => match v with
            | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s
    · rw [if_pos hGood]
      exact Nat.le_antisymm hUpper
        (hOppositeExtremeLower σ (σ.k - 2) hmax hk ha hu (by rfl)
          s t hne hletters hruns hGood.2 hGood.1)
    · rw [if_neg hGood]
      by_cases hOther : 3 ≤ (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t
      · have hBudget := fun h => hGood ⟨hOther, h⟩
        by_cases hBoth : σ.word.head? = some (Ctx.Letter.ext 1 s) ∧
            σ.word.getLast? = some (Ctx.Letter.ext 1 s)
        · have hG : (fun v : Ctx.Side => match v with
              | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 3 := by
            simp [hBoth] at hBudget
            dsimp only at *; omega
          have hh := hEnds.2.2.1 hBoth.1
          have ht := hEnds.2.2.2 hBoth.2
          exact (hAllBracketedZero σ s 1 0 (σ.word.length - 1) hN hData.2
            hh.1 ht.1 (fun p hp => ⟨hh.2 p hp, ht.2 p hp⟩) (by cases s <;> exact hG)).2
        · have hG : (fun v : Ctx.Side => match v with
              | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 2 := by
            simp [hBoth] at hBudget
            dsimp only at *; omega
          obtain ⟨first, sep, other, hfirst, hotherChild, hFirstSep, hSepOther, hSep⟩ :=
            hTwoSites σ s hletters hruns
          have hOtherR := List.mem_range.mp (List.mem_filter.mp hotherChild).1
          have hSepR : sep < σ.word.length := by dsimp only at *; omega
          have hSepMem : sep ∈ σ.extPositions 1 := by
            simp [Ctx.Context.extPositions, hSepR, hSep]
          exact (hIndexedMarkerZero σ s 1 sep hN hData.2 hSepMem (by cases s <;> exact hG)).2
      · exact hSaturatedZero σ hData.1 s t hne 1 hNOn (by rw [hMaximum])
          (by dsimp only at *; omega) hruns

  have hCriterion (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
    (hk : 3 ≤ σ.k) (hm : 1 ≤ m) (hmk : m ≤ σ.k - 2)
    (s t : Ctx.Side) (hne : s ≠ t)
    (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
    (hruns : 2 ≤ σ.numRuns)
    (hchosenK : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ σ.k)
    (hunit : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t = 2) :
    σ.bound = if m ≤ σ.k - 3 ∧
      3 + (if σ.word.head? = some (Ctx.Letter.ext 1 s) then 1 else 0) +
        (if σ.word.getLast? = some (Ctx.Letter.ext 1 s) then 1 else 0) +
        (if σ.word.head? ≠ some (Ctx.Letter.ext 1 s) ∧
          σ.word.getLast? ≠ some (Ctx.Letter.ext 1 s) ∧ 3 ≤ σ.numRuns then 1 else 0) ≤
        (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s
      then 1 else 0 := by
    classical
    have hData := hRootData σ s hletters hruns
    have hEnds := hRootEnds σ s hletters hruns
    have hN : 1 ∈ σ.levels := by simp [Ctx.Context.levels, hmax]
    have hNOn : 1 ∈ σ.levelsOn s 0 := by
      simp [Ctx.Context.levelsOn, Ctx.Context.levels, hmax, hData.2]
    have hOpposite : (match σ.sideAt 1 with
        | Ctx.Side.lower => σ.a | Ctx.Side.upper => σ.u) ≤ 2 := by
      rw [hData.2]
      cases s <;> cases t <;> simp only at hunit
      all_goals first | exact (hne rfl).elim | dsimp only at *; omega
    have hYounger : ∀ j ∈ σ.levelsOn (σ.sideAt 1) 1, ∀ p ∈ σ.extPositions j, True := by
      intro j hj
      rw [Ctx.Context.levelsOn_one] at hj
      cases hj
    have hMarker : ∃ x, x ∈ σ.extPositions 1 := by
      obtain ⟨first, sep, other, hfirst, hother, hFirstSep, hSepOther, hSep⟩ :=
        hTwoSites σ s hletters hruns
      have hOtherR := List.mem_range.mp (List.mem_filter.mp hother).1
      have hSepR : sep < σ.word.length := by dsimp only at *; omega
      exact ⟨sep, by simp [Ctx.Context.extPositions, hSepR, hSep]⟩
    have hBoundaryHead (hhead : σ.word.head? = some (Ctx.Letter.ext 1 s))
        (hG : (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 3) : σ.bound = 0 := by
      have he := hEnds.2.2.1 hhead
      apply hBoundaryZero σ hData.1 1 0 (by simpa [hData.2] using hG)
        hOpposite hN he.1 false
      · intro p hp; simpa using he.2 p hp
      · intro j hj
        rw [Ctx.Context.levelsOn_one] at hj
        cases hj
      · exact hruns
    have hBoundaryTail (hlast : σ.word.getLast? = some (Ctx.Letter.ext 1 s))
        (hG : (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 3) : σ.bound = 0 := by
      have he := hEnds.2.2.2 hlast
      apply hBoundaryZero σ hData.1 1 (σ.word.length - 1)
        (by simpa [hData.2] using hG) hOpposite hN he.1 true
      · intro p hp; simpa using he.2 p hp
      · intro j hj
        rw [Ctx.Context.levelsOn_one] at hj
        cases hj
      · exact hruns
    have hBothBoundary (hhead : σ.word.head? = some (Ctx.Letter.ext 1 s))
        (hlast : σ.word.getLast? = some (Ctx.Letter.ext 1 s))
        (hG : (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4) : σ.bound = 0 := by
      have hh := hEnds.2.2.1 hhead
      have ht := hEnds.2.2.2 hlast
      apply hTwoBoundaryZero σ hData.1 1 0 (σ.word.length - 1)
        (by simpa [hData.2] using hG) hOpposite hN hh.1 ht.1
      · intro p hp; exact ⟨hh.2 p hp, ht.2 p hp⟩
      · intro j hj
        rw [Ctx.Context.levelsOn_one] at hj
        cases hj
      · exact hruns
    have hReflection (hlast : σ.word.getLast? = some Ctx.Letter.child)
        (hG : 4 ≤ (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s)
        (hms : m ≤ σ.k - 3) : σ.bound = 1 := by
      have hAxes : 2 ≤ σ.a ∧ 2 ≤ σ.u ∧ σ.a ≤ σ.k ∧ σ.u ≤ σ.k := by
        cases s <;> cases t <;> simp only at hG hchosenK hunit
        all_goals first | exact (hne rfl).elim | dsimp only at *; omega
      have hWF := hRootWF σ m hmax hAxes.1 hAxes.2.1 hAxes.2.2.1
        hAxes.2.2.2 hm hmk s hletters hruns
      exact hReflectedPositive σ m hmax s t hne hletters hruns hlast
        hG hchosenK hunit hms (ctx_bound_reverse σ hWF)
    by_cases hGood : m ≤ σ.k - 3 ∧
        3 + (if σ.word.head? = some (Ctx.Letter.ext 1 s) then 1 else 0) +
          (if σ.word.getLast? = some (Ctx.Letter.ext 1 s) then 1 else 0) +
          (if σ.word.head? ≠ some (Ctx.Letter.ext 1 s) ∧
            σ.word.getLast? ≠ some (Ctx.Letter.ext 1 s) ∧ 3 ≤ σ.numRuns then 1 else 0) ≤
          (fun v : Ctx.Side => match v with
            | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s
    · rw [if_pos hGood]
      have hms := hGood.1
      have hCap := hGood.2
      rcases hEnds.1 with hhead | hhead
      · have hh : σ.word.head? ≠ some (Ctx.Letter.ext 1 s) := by simp [hhead]
        rcases hEnds.2.1 with hlast | hlast
        · have ht : σ.word.getLast? ≠ some (Ctx.Letter.ext 1 s) := by simp [hlast]
          by_cases hr3 : 3 ≤ σ.numRuns
          · have hG : 4 ≤ (fun v : Ctx.Side => match v with
                | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s := by
              simpa [hh, ht, hr3] using hCap
            exact hRootPositive σ m hmax s t hne hletters hruns
              (by simpa [hh] using hG) hchosenK hunit hms
          · have hr2 : σ.numRuns = 2 := by dsimp only at *; omega
            have hG : 3 ≤ (fun v : Ctx.Side => match v with
                | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s := by
              simpa [hh, ht, hr3] using hCap
            exact hTwoRunsPositive σ m hmax s t hne hletters hhead hlast
              hr2 hG hchosenK hunit hms
        · have hG : 4 ≤ (fun v : Ctx.Side => match v with
              | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s := by
            simpa [hh, hlast] using hCap
          exact hRootPositive σ m hmax s t hne hletters hruns
            (by simpa [hh] using hG) hchosenK hunit hms
      · rcases hEnds.2.1 with hlast | hlast
        · have ht : σ.word.getLast? ≠ some (Ctx.Letter.ext 1 s) := by simp [hlast]
          have hG : 4 ≤ (fun v : Ctx.Side => match v with
              | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s := by
            simpa [hhead, ht] using hCap
          exact hReflection hlast hG hms
        · have hG : 5 ≤ (fun v : Ctx.Side => match v with
              | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s := by
            simpa [hhead, hlast] using hCap
          exact hRootPositive σ m hmax s t hne hletters hruns
            (by simpa [hhead] using hG) hchosenK hunit hms
    · rw [if_neg hGood]
      by_cases hms : m ≤ σ.k - 3
      · have hCap := fun h => hGood ⟨hms, h⟩
        by_cases hG2 : (fun v : Ctx.Side => match v with
            | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 2
        · obtain ⟨x, hx⟩ := hMarker
          exact (hIndexedMarkerZero σ s 1 x hN hData.2 hx (by cases s <;> exact hG2)).2
        · rcases hEnds.1 with hhead | hhead
          · have hh : σ.word.head? ≠ some (Ctx.Letter.ext 1 s) := by simp [hhead]
            rcases hEnds.2.1 with hlast | hlast
            · have ht : σ.word.getLast? ≠ some (Ctx.Letter.ext 1 s) := by simp [hlast]
              by_cases hr3 : 3 ≤ σ.numRuns
              · have hG : (fun v : Ctx.Side => match v with
                    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 3 := by
                  simp [hh, ht, hr3] at hCap
                  dsimp only at *; omega
                exact hRootThreeZero σ m hmax s t hne hG (by rw [hunit]) hletters hr3
              · have hG : (fun v : Ctx.Side => match v with
                    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 2 := by
                  simp [hh, ht, hr3] at hCap
                  dsimp only at *; omega
                exact (hG2 hG).elim
            · have hG : (fun v : Ctx.Side => match v with
                  | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 3 := by
                simp [hh, hlast] at hCap
                dsimp only at *; omega
              exact hBoundaryTail hlast hG
          · rcases hEnds.2.1 with hlast | hlast
            · have ht : σ.word.getLast? ≠ some (Ctx.Letter.ext 1 s) := by simp [hlast]
              have hG : (fun v : Ctx.Side => match v with
                  | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 3 := by
                simp [hhead, ht] at hCap
                dsimp only at *; omega
              exact hBoundaryHead hhead hG
            · have hG : (fun v : Ctx.Side => match v with
                  | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4 := by
                simp [hhead, hlast] at hCap
                dsimp only at *; omega
              exact hBothBoundary hhead hlast hG
      · have hM : σ.k - 2 ≤ σ.maximumAt 1 := by
          simp only [Ctx.Context.maximumAt, hmax]
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          omega
        have hU : (fun v : Ctx.Side => match v with
            | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t ≤ 2 := by
          rw [hunit]
        exact hSaturatedZero σ hData.1 s t hne 1 hNOn hM hU hruns


  have hOldChosenTwoZero (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
      (s : Ctx.Side)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 2 ≤ σ.numRuns)
      (hglobal : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 2) : σ.bound = 0 := by
    have hData := hRootData σ s hletters hruns
    obtain ⟨first, sep, other, hfirst, hother, hFirstSep, hSepOther, hSep⟩ :=
      hTwoSites σ s hletters hruns
    have hOtherR := List.mem_range.mp (List.mem_filter.mp hother).1
    have hSepR : sep < σ.word.length := by omega
    have hSepMem : sep ∈ σ.extPositions 1 := by
      simp [Ctx.Context.extPositions, hSepR, hSep]
    have hN : 1 ∈ σ.levels := by simp [Ctx.Context.levels, hmax]
    exact (hIndexedMarkerZero σ s 1 sep hN hData.2 hSepMem (by cases s <;> exact hglobal)).2

  have hNormalFacts (σ : Ctx.Context) (s : Ctx.Side) (hruns : 2 ≤ σ.numRuns) :
      let r := min σ.numRuns (if σ.a = 2 ∨ σ.u = 2 then 3 else 2)
      let marker := Ctx.Letter.ext 1 s
      let normalWord :=
        (if σ.word.head? = some marker then [marker] else []) ++
        (List.replicate r Ctx.Letter.child).intersperse marker ++
        (if σ.word.getLast? = some marker then [marker] else [])
      let ρ : Ctx.Context := {σ with word := normalWord}
      (∀ v ∈ ρ.word, v = Ctx.Letter.child ∨ v = marker) ∧
        ρ.numRuns = r ∧
        (ρ.word.head? = some marker ↔ σ.word.head? = some marker) ∧
        (ρ.word.getLast? = some marker ↔ σ.word.getLast? = some marker) := by
    classical
    let r := min σ.numRuns (if σ.a = 2 ∨ σ.u = 2 then 3 else 2)
    let marker := Ctx.Letter.ext 1 s
    let normalWord :=
      (if σ.word.head? = some marker then [marker] else []) ++
      (List.replicate r Ctx.Letter.child).intersperse marker ++
      (if σ.word.getLast? = some marker then [marker] else [])
    let ρ : Ctx.Context := {σ with word := normalWord}
    change (∀ v ∈ ρ.word, v = Ctx.Letter.child ∨ v = marker) ∧
      ρ.numRuns = r ∧
      (ρ.word.head? = some marker ↔ σ.word.head? = some marker) ∧
      (ρ.word.getLast? = some marker ↔ σ.word.getLast? = some marker)
    have hCases : r = 2 ∨ r = 3 := by
      dsimp [r]
      split_ifs
      · have hlo : 2 ≤ min σ.numRuns 3 := Nat.le_min.mpr ⟨hruns, by omega⟩
        have hhi : min σ.numRuns 3 ≤ 3 := Nat.min_le_right _ _
        omega
      · exact Or.inl (Nat.min_eq_right hruns)
    constructor
    · intro v hv
      change v ∈ normalWord at hv
      rcases hCases with hc | hc <;>
        by_cases hL : σ.word.head? = some marker <;>
        by_cases hR : σ.word.getLast? = some marker <;>
        simpa [normalWord, hc, hL, hR, marker,
          or_comm, or_left_comm, or_assoc] using hv
    · refine ⟨?_, ?_, ?_⟩
      · rcases hCases with hc | hc <;>
          by_cases hL : σ.word.head? = some marker <;>
          by_cases hR : σ.word.getLast? = some marker <;>
          simp [ρ, normalWord, hc, hL, hR, marker,
            Ctx.Context.numRuns, Ctx.Context.letterAt, List.range_succ]
      · rcases hCases with hc | hc <;>
          by_cases hL : σ.word.head? = some marker <;>
          by_cases hR : σ.word.getLast? = some marker <;>
          simp [ρ, normalWord, hc, hL, hR, marker]
      · rcases hCases with hc | hc <;>
          by_cases hL : σ.word.head? = some marker <;>
          by_cases hR : σ.word.getLast? = some marker <;>
          simp [ρ, normalWord, hc, hL, hR, marker]

  have hActiveBoundaryThree (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s : Ctx.Side) (N x : ℕ) (hN : N ∈ σ.levels)
    (hs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
    (hglobal : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 3)
    (rightward : Bool)
    (hboundary : ∀ p ∈ σ.childPositions,
      0 < σ.cupLimit p p → 0 < σ.capLimit p p →
      if rightward then p < x else x < p) :
    (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ ≤ 1) ∧ σ.bound ≤ 1 := by
    classical
    have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
        1 ≤ ρ.leftExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq,hqp]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (leftStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
      change _ ≤ ρ.leftExt v 0 p at hv
      simpa only [List.foldl_cons,List.foldl_nil,leftStep,
        List.getLast?_eq_some_getLast hnonempty] using hv
    have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
        1 ≤ ρ.rightExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq,hpq]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (rightStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
      change _ ≤ ρ.rightExt v 0 p at hv
      simpa only [List.foldl_cons,List.foldl_nil,rightStep,
        List.head?_eq_some_head hnonempty] using hv
    have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hs]⟩
    let rank : ℕ := if rightward then 1 else 2
    have hRank : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
        σ.leftExt s 0 p + 1 = rank ∧ rank + σ.rightExt s 0 p =
          (match s with | Ctx.Side.lower => σ.u - 1 | Ctx.Side.upper => σ.a - 1) := by
      intro p hp hcup hcap
      have hSide := hboundary p hp hcup hcap
      cases rightward with
      | false =>
        have hxp : x < p := by simpa using hSide
        have hleft := hOneLeft σ s N p x hNOn hx hxp
        cases s with
        | lower =>
          change σ.leftExt Ctx.Side.lower 0 p + 1 = 2 ∧
            2 + σ.rightExt Ctx.Side.lower 0 p = σ.u - 1
          simp only [Ctx.Context.cupLimit, Ctx.Context.chainExt] at hcup
          dsimp only at hglobal
          omega
        | upper =>
          change σ.leftExt Ctx.Side.upper 0 p + 1 = 2 ∧
            2 + σ.rightExt Ctx.Side.upper 0 p = σ.a - 1
          simp only [Ctx.Context.capLimit, Ctx.Context.chainExt] at hcap
          dsimp only at hglobal
          omega
      | true =>
        have hpx : p < x := by simpa using hSide
        have hright := hOneRight σ s N p x hNOn hx hpx
        cases s with
        | lower =>
          change σ.leftExt Ctx.Side.lower 0 p + 1 = 1 ∧
            1 + σ.rightExt Ctx.Side.lower 0 p = σ.u - 1
          simp only [Ctx.Context.cupLimit, Ctx.Context.chainExt] at hcup
          dsimp only at hglobal
          omega
        | upper =>
          change σ.leftExt Ctx.Side.upper 0 p + 1 = 1 ∧
            1 + σ.rightExt Ctx.Side.upper 0 p = σ.a - 1
          simp only [Ctx.Context.capLimit, Ctx.Context.chainExt] at hcap
          dsimp only at hglobal
          omega
    cases s with
    | lower =>
      have hCommon := ctx_bound_le_one_of_common_singleton_rank σ hpositive Ctx.Side.lower rank hRank
      exact ⟨hCommon.1, hCommon.2.1⟩
    | upper =>
      have hCommon := ctx_bound_le_one_of_common_singleton_rank σ hpositive Ctx.Side.upper rank hRank
      exact ⟨hCommon.1, hCommon.2.1⟩

  have hMarkedThreeExact (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
      (hk : 3 ≤ σ.k) (ha : σ.a ≤ σ.k) (hu : σ.u ≤ σ.k) (hmk : m ≤ σ.k - 2)
      (s t : Ctx.Side) (hne : s ≠ t)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 2 ≤ σ.numRuns)
      (hchosen : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s = 3)
      (hother : 3 ≤ (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) t)
      (hmarked : σ.word.head? = some (Ctx.Letter.ext 1 s) ∨
        σ.word.getLast? = some (Ctx.Letter.ext 1 s)) :
      σ.bound = if σ.word.head? = some (Ctx.Letter.ext 1 s) ∧
        σ.word.getLast? = some (Ctx.Letter.ext 1 s) then 0 else 1 := by
    classical
    have hData := hRootData σ s hletters hruns
    have hEnds := hRootEnds σ s hletters hruns
    have hOne : 1 ∈ σ.levels := by simp [Ctx.Context.levels, hmax]
    have hG : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 3 := by omega
    by_cases hBoth : σ.word.head? = some (Ctx.Letter.ext 1 s) ∧
        σ.word.getLast? = some (Ctx.Letter.ext 1 s)
    · rw [if_pos hBoth]
      have hHead := hEnds.2.2.1 hBoth.1
      have hLast := hEnds.2.2.2 hBoth.2
      exact (hAllBracketedZero σ s 1 0 (σ.word.length - 1) hOne hData.2
        hHead.1 hLast.1 (by intro p hp; exact ⟨hHead.2 p hp, hLast.2 p hp⟩)
        (by cases s <;> exact hG)).2
    · rw [if_neg hBoth]
      have hUpper : σ.bound ≤ 1 := by
        rcases hmarked with hhead | hlast
        · have hHead := hEnds.2.2.1 hhead
          exact (hActiveBoundaryThree σ hData.1 s 1 0 hOne hData.2 hHead.1 hG false
            (by intro p hp _ _; simpa using hHead.2 p hp)).2
        · have hLast := hEnds.2.2.2 hlast
          exact (hActiveBoundaryThree σ hData.1 s 1 (σ.word.length - 1) hOne
            hData.2 hLast.1 hG true
            (by intro p hp _ _; simpa using hLast.2 p hp)).2
      have hLower := hOppositeExtremeLower σ m hmax hk ha hu hmk s t hne
        hletters hruns (by rw [if_neg hBoth]; omega) hother
      exact Nat.le_antisymm hUpper hLower

  have hChosenThreeNoneExact (A k m : ℕ) (hk : 3 ≤ k) (hA : 3 ≤ A) (hAk : A ≤ k)
      (hm : 1 ≤ m) (hmk : m ≤ k - 2) (hunsat : m ≤ k - 3)
      (side : Ctx.Side) (word : List Ctx.Letter)
      (hletters : ∀ z ∈ word, z = Ctx.Letter.child ∨ z = Ctx.Letter.ext 1 side)
      (hmarker : Ctx.Letter.ext 1 side ∈ word)
      (hfirst : word.head? = some Ctx.Letter.child)
      (hlast : word.getLast? = some Ctx.Letter.child)
      (hchild : Ctx.Letter.child ∈ word) :
      let σ : Ctx.Context :=
        {a := match side with | Ctx.Side.lower => A | Ctx.Side.upper => 3,
         u := match side with | Ctx.Side.lower => 3 | Ctx.Side.upper => A,
         k := k, word := word, maxima := [m]}
      2 ≤ σ.numRuns → σ.bound = 2 := by
    classical
    have hWindowComm
        {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
        decomposableBinomialWindow a u k =
          decomposableBinomialWindow u a k := by
      unfold decomposableBinomialWindow
      apply Finset.sum_nbij' (fun j ↦ k - 2 - j) (fun j ↦ k - 2 - j)
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        exact (Nat.choose_symm (by omega)).symm
    have hThresholdComm
        {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
        decomposableThreshold a u k = decomposableThreshold u a k := by
      rw [decomposableThreshold, decomposableThreshold]
      simp only [show ¬(a = 1 ∨ u = 1) by omega,
        show ¬(u = 1 ∨ a = 1) by omega, ↓reduceIte]
      by_cases hbase : a + u ≤ k + 3
      · rw [if_pos hbase, if_pos (by omega)]
        simpa [add_comm] using Nat.choose_symm_of_eq_add
          (n := a + u - 4) (a := a - 2) (b := u - 2) (by omega)
      · rw [if_neg hbase, if_neg (by omega)]
        exact hWindowComm ha hu hak huk
    have hSingleLeft (ρ : Context) (v : Side) (L p : ℕ)
        (hls : ρ.levelsOn v 0 = [L])
        (hx : ∃ x ∈ ρ.extPositions L, x < p) : ρ.leftExt v 0 p = 1 := by
      cases he : ((ρ.extPositions L).filter (· < p)).getLast? with
      | none =>
        obtain ⟨x,hx,hxp⟩ := hx
        have hm : x ∈ (ρ.extPositions L).filter (· < p) := by simp [hx,hxp]
        have hn := List.getLast?_eq_none_iff.mp he
        rw [hn] at hm
        exact False.elim (List.not_mem_nil hm)
      | some x =>
        simp [leftExt_eq,hls,List.sublists_cons,leftStep,he]
    have hSingleRight (ρ : Context) (v : Side) (L p : ℕ)
        (hls : ρ.levelsOn v 0 = [L])
        (hx : ∃ x ∈ ρ.extPositions L, p < x) : ρ.rightExt v 0 p = 1 := by
      cases he : ((ρ.extPositions L).filter (p < ·)).head? with
      | none =>
        obtain ⟨x,hx,hpx⟩ := hx
        have hm : x ∈ (ρ.extPositions L).filter (p < ·) := by simp [hx,hpx]
        have hn := List.head?_eq_none_iff.mp he
        rw [hn] at hm
        exact False.elim (List.not_mem_nil hm)
      | some x =>
        simp [rightExt_eq,hls,List.sublists_cons,rightStep,he]
    have hSingleLeftZero (ρ : Context) (v : Side) (L p : ℕ)
        (hls : ρ.levelsOn v 0 = [L])
        (hx : ∀ x ∈ ρ.extPositions L, ¬ x < p) : ρ.leftExt v 0 p = 0 := by
      have hf : (ρ.extPositions L).filter (· < p) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx'
        simp [hx x hx']
      simp [leftExt_eq,hls,List.sublists_cons,leftStep,hf]
    have hTopFilter (ρ : Context) (v : Side) (top : ℕ) (htop : 1 ≤ top) :
        ρ.levelsOn v top = (ρ.levelsOn v 0).filter (· < top) := by
      simp only [levelsOn,List.filter_filter]
      apply List.filter_congr
      intro j _
      simp [show top ≠ 0 by omega,Bool.and_comm]
    have hSingleJoin (ρ : Context) (v : Side) (L p q : ℕ)
        (hL : 1 ≤ L) (hls : ρ.levelsOn v 0 = [L]) :
        ρ.joinExt v p q = max (ρ.chainExt v p q) (ρ.maximumAt L) := by
      have ht : ρ.levelsOn v L = [] := by
        rw [hTopFilter ρ v L hL,hls]
        simp
      have hl : ρ.leftExt v L p = 0 := by simp [leftExt_eq,ht]
      have hr : ρ.rightExt v L q = 0 := by simp [rightExt_eq,ht]
      simp [joinExt,hls,hl,hr]
    have hEmptyAxis (ρ : Context) (v : Side) (p q : ℕ)
        (hls : ρ.levelsOn v 0 = []) :
        ρ.chainExt v p q = 0 ∧ ρ.joinExt v p q = 0 := by
      have hl : ρ.leftExt v 0 p = 0 := by simp [leftExt_eq,hls]
      have hr : ρ.rightExt v 0 q = 0 := by simp [rightExt_eq,hls]
      simp [chainExt,joinExt,hls,hl,hr]
    have hChildMem (ρ : Context) (p : ℕ) (hp : p ∈ ρ.childPositions) :
        p < ρ.word.length ∧ ρ.letterAt p = Letter.child := by
      simpa only [childPositions,List.mem_filter,List.mem_range,decide_eq_true_eq] using hp
    have hShape (ρ : Context) (v : Side)
        (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v) :
        ∀ p j w, ρ.letterAt p = Letter.ext j w → j = 1 ∧ w = v := by
      intro p j w hext
      have hp : p < ρ.word.length := by
        by_contra hn
        have h := letterAt_of_length_le ρ (Nat.le_of_not_gt hn)
        rw [h] at hext
        cases hext
      have hget : ρ.word[p] = Letter.ext j w := by
        simpa [letterAt,hp] using hext
      have hmem : Letter.ext j w ∈ ρ.word := by
        rw [← hget]
        exact List.getElem_mem _
      rcases hw _ hmem with h | h
      · cases h
      · cases h
        exact ⟨rfl,rfl⟩
    have hSideOne (ρ : Context) (v : Side)
        (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v)
        (hx : ∃ x, x ∈ ρ.extPositions 1) : ρ.sideAt 1 = v := by
      cases hh : (ρ.extPositions 1).head? with
      | none =>
        obtain ⟨x,hx⟩ := hx
        have hn := List.head?_eq_none_iff.mp hh
        rw [hn] at hx
        exact False.elim (List.not_mem_nil hx)
      | some p =>
        have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        cases he : ρ.letterAt p with
        | child => simp [extPositions,he] at hp
        | ext j w =>
          have hs := (hShape ρ v hw p j w he).2
          simp [sideAt,hh,he,hs]
    have hChildExists (ρ : Context) (hc : Letter.child ∈ ρ.word) :
        ∃ p, p ∈ ρ.childPositions := by
      obtain ⟨p,hp⟩ := List.mem_iff_getElem?.mp hc
      have hlt := (List.getElem?_eq_some_iff.mp hp).1
      have hget := (List.getElem?_eq_some_iff.mp hp).2
      refine ⟨p,?_⟩
      simp [childPositions,hlt,letterAt,hget]
    have hRootLevels (ρ : Context) (v : Side) (m : ℕ)
        (hmx : ρ.maxima = [m]) (hs : ρ.sideAt 1 = v) :
        ρ.levelsOn v 0 = [1] := by
      simp [levelsOn,levels,hmx,hs]
    have hOtherLevels (ρ : Context) (v w : Side) (m : ℕ)
        (hmx : ρ.maxima = [m]) (hs : ρ.sideAt 1 = v) (hw : w ≠ v) :
        ρ.levelsOn w 0 = [] := by
      simp [levelsOn,levels,hmx,hs,hw.symm]
    let mkRoot (B H K M : ℕ) (v : Side) (w : List Letter) : Context :=
      { a := match v with | Side.lower => B | Side.upper => H
        u := match v with | Side.lower => H | Side.upper => B
        k := K, word := w, maxima := [M] }
    let opp : Side → Side := fun v => match v with
      | Side.lower => Side.upper | Side.upper => Side.lower
    let ownLimit (ρ : Context) (v : Side) (p q : ℕ) : ℕ :=
      match v with
      | Side.lower => ρ.cupLimit p q
      | Side.upper => ρ.capLimit p q
    let otherLimit (ρ : Context) (v : Side) (p q : ℕ) : ℕ :=
      match v with
      | Side.lower => ρ.capLimit p q
      | Side.upper => ρ.cupLimit p q
    have hRootPositive (ρ : Context) (v : Side)
        (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v) :
        ∀ p j w, ρ.letterAt p = Letter.ext j w → 1 ≤ j := by
      intro p j w he
      have hj := (hShape ρ v hw p j w he).1
      omega
    have hFirstTail (ρ : Context) (p : ℕ) (ps : List ℕ)
        (hcp : ρ.childPositions = p :: ps) : ∀ q ∈ ps, p < q := by
      have h := childPositions_pairwise ρ
      rw [hcp] at h
      exact (List.pairwise_cons.mp h).1
    have hPartShape (ρ : Context) (v : Side)
        (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v)
        (keep : List ℕ) (s : Side) (n : ℕ) :
        ∀ x j t, (ρ.part keep s n).letterAt x = Letter.ext j t →
          (j = 1 ∧ t = s) ∨ (j = 2 ∧ t = v) := by
      intro x j t hx
      have hxl : x < ρ.word.length := by
        by_contra h
        have hn := letterAt_of_length_le (ρ.part keep s n)
          (show (ρ.part keep s n).word.length ≤ x by rw [part_word_length]; omega)
        rw [hn] at hx
        cases hx
      cases he : ρ.letterAt x with
      | child =>
        rw [part_letterAt_of_child ρ keep s n hxl he] at hx
        by_cases hm : x ∈ keep
        · simp [hm] at hx
        · simp only [hm,if_false,Letter.ext.injEq] at hx
          obtain ⟨rfl,rfl⟩ := hx
          exact Or.inl ⟨rfl,rfl⟩
      | ext oldLevel oldSide =>
        have hs := hShape ρ v hw x oldLevel oldSide he
        obtain ⟨rfl,rfl⟩ := hs
        rw [part_letterAt_of_ext ρ keep s n hxl he] at hx
        cases hx
        exact Or.inr ⟨rfl,rfl⟩
    let mergeLetter : Letter → Letter := fun z => match z with
      | Letter.child => Letter.child
      | Letter.ext j v => if j ≤ 1 then Letter.ext j v else Letter.ext (j-1) v
    have hFirstBlock (ρ : Context) (p : ℕ) (ps : List ℕ)
        (hcp : ρ.childPositions = p :: ps) (hne : ps ≠ []) :
        [p] ∈ ρ.blocks ∧ ρ.childPositions.filter (· ∉ [p]) = ps := by
      have hlt := hFirstTail ρ p ps hcp
      have hlen : 1 ≤ ps.length := by
        by_contra h
        exact hne (List.length_eq_zero_iff.mp (by omega))
      have hblockLen : [p].length < ρ.childPositions.length := by
        rw [hcp]
        simp only [List.length_cons,List.length_nil]
        omega
      have hzero : 0 ∈ List.range ρ.childPositions.length := by
        simp only [List.mem_range,hcp,List.length_cons]
        omega
      have hzero' : 0 ∈ List.range (ρ.childPositions.length-0) := by simpa using hzero
      constructor
      · unfold blocks
        apply List.mem_filter.mpr
        refine ⟨?_,by simpa using hblockLen⟩
        apply List.mem_flatMap.mpr
        refine ⟨0,hzero,?_⟩
        apply List.mem_map.mpr
        refine ⟨0,hzero',?_⟩
        rw [hcp]
        rfl
      · have hf : ps.filter (· ∉ [p]) = ps := by
          apply List.filter_eq_self.mpr
          intro q hq
          have hpq := hlt q hq
          simp [show q ≠ p by omega]
        simpa [hcp] using hf
    have hPrefixMerge (σ : Ctx.Context)
      (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
      (N x : ℕ) (hpair : MergeLevels.Inv σ N)
      (hsole : σ.extPositions N = [x])
      (hafter : ∀ y ∈ σ.extPositions (N+1), x < y)
      (hchildren : ∀ p ∈ σ.childPositions, x < p)
      (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j, x < p)
      (holdest : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, j ≤ N+1)
      (hglobal : (match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k) :
      let τ : Ctx.Context :=
        { σ with
          word := σ.word.map (fun z => match z with
            | Ctx.Letter.child => Ctx.Letter.child
            | Ctx.Letter.ext j v => if j ≤ N then Ctx.Letter.ext j v else Ctx.Letter.ext (j-1) v)
          maxima := σ.maxima.take (N-1) ++
            [max (σ.maximumAt N) (σ.maximumAt (N+1)+1)] ++ σ.maxima.drop (N+1) }
      (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
        σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q) ∧
      (∀ fuel, Ctx.Context.boundFuel fuel σ = Ctx.Context.boundFuel fuel τ) ∧ σ.bound = τ.bound := by
      classical
      let letter (L : ℕ) : Letter → Letter := fun x => match x with
        | Letter.child => Letter.child
        | Letter.ext j s => if j ≤ L then Letter.ext j s else Letter.ext (j - 1) s
      let norm (ρ : Context) (L : ℕ) : Context :=
        { ρ with
          word := ρ.word.map (letter L)
          maxima := ρ.maxima.take (L - 1) ++ [max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)] ++
            ρ.maxima.drop (L + 1) }
      let lv (ρ : Context) (i : ℕ) : ℕ → Bool := fun p => match ρ.letterAt p with
        | Letter.ext j _ => decide (j = i)
        | Letter.child => false
      let up (L j : ℕ) := if j < L then j else j + 1
      let upTop (L t : ℕ) := if t ≤ L then t else t + 1
      let img (L j x : ℕ) : Prop := (j < L ∧ x = j) ∨ (j = L ∧ (x = L ∨ x = L + 1)) ∨ (L < j ∧ x = j + 1)
      change (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
          σ.cupLimit p q = (norm σ N).cupLimit p q ∧
          σ.capLimit p q = (norm σ N).capLimit p q) ∧
        (∀ fuel, boundFuel fuel σ = boundFuel fuel (norm σ N)) ∧
          σ.bound = (norm σ N).bound
      -- basic transport ----------------------------------------------------------
      have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
        simp only [levels, List.mem_map, List.mem_range]
        constructor
        · rintro ⟨i, hi, rfl⟩; omega
        · intro hj; exact ⟨j - 1, by omega, by omega⟩
      have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
        unfold levels
        exact List.pairwise_lt_range.map (fun x => x + 1) (fun a b h => Nat.add_lt_add_right h 1)
      have hLen (ρ : Context) (L : ℕ) : (norm ρ L).word.length = ρ.word.length := by
        simp only [norm, List.length_map]
      have hLetter (ρ : Context) (L p : ℕ) : (norm ρ L).letterAt p = letter L (ρ.letterAt p) := by
        simp only [norm, letterAt, List.getElem?_map]
        cases ρ.word[p]? <;> rfl
      have hIsChild (ρ : Context) (L p : ℕ) :
          (norm ρ L).letterAt p = Letter.child ↔ ρ.letterAt p = Letter.child := by
        rw [hLetter]
        cases ρ.letterAt p with
        | child => simp [letter]
        | ext j v => by_cases hj : j ≤ L <;> simp [letter, hj]
      have hChild (ρ : Context) (L : ℕ) : (norm ρ L).childPositions = ρ.childPositions := by
        simp only [childPositions, hLen, hIsChild]
      have hRuns (ρ : Context) (L : ℕ) : (norm ρ L).numRuns = ρ.numRuns := by
        simp only [numRuns, hLen, ne_eq, hIsChild]
      have hBlocks (ρ : Context) (L : ℕ) : (norm ρ L).blocks = ρ.blocks := by
        simp only [blocks, hChild]
      have hK (ρ : Context) (L : ℕ) : (norm ρ L).k = ρ.k := rfl
      have hDepth (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
          (norm ρ L).maxima.length = ρ.maxima.length - 1 := by
        obtain ⟨h1, h2, -, -⟩ := hL
        simp only [norm, List.length_append, List.length_take, List.length_singleton, List.length_drop]
        omega
      have hNormLevel (ρ : Context) (L : ℕ) (hL : Inv ρ L) (j : ℕ) (hj : j ∈ (norm ρ L).levels) :
          1 ≤ j ∧ j + 1 ≤ ρ.maxima.length := by
        have h := (hLevelMem (norm ρ L) j).mp hj
        rw [hDepth ρ L hL] at h
        omega
      -- levels and letters ---------------------------------------------------------
      have hExtLv (ρ : Context) (i : ℕ) : ρ.extPositions i = (List.range ρ.word.length).filter (lv ρ i) := by
        unfold extPositions
        apply List.filter_congr
        intro p _
        cases h : ρ.letterAt p with
        | child => simp [lv, h]
        | ext j v => simp [lv, h]
      have hExtMerged (ρ : Context) (L : ℕ) :
          (norm ρ L).extPositions L =
            (List.range ρ.word.length).filter (fun p => lv ρ L p || lv ρ (L + 1) p) := by
        unfold extPositions
        rw [hLen]
        apply List.filter_congr
        intro p _
        rw [hLetter]
        cases h : ρ.letterAt p with
        | child => simp [lv, h, letter]
        | ext j v =>
          by_cases hj : j ≤ L
          · simp only [letter, hj, if_true, lv, h]
            by_cases hjL : j = L <;> simp [hjL] <;> omega
          · simp only [letter, hj, if_false, lv, h]
            by_cases hjL : j = L + 1 <;> simp [hjL] <;> omega
      have hExtNe (ρ : Context) (L j : ℕ) (hj1 : 1 ≤ j) (hjL : j ≠ L) :
          (norm ρ L).extPositions j = ρ.extPositions (up L j) := by
        unfold extPositions
        rw [hLen]
        apply List.filter_congr
        intro p _
        rw [hLetter]
        cases h : ρ.letterAt p with
        | child => simp [letter]
        | ext i v =>
          by_cases hi : i ≤ L <;> by_cases hjl : j < L <;> simp [letter, hi, hjl, up] <;> omega
      have hMemMerged (ρ : Context) (L p : ℕ) (hp : p ∈ ρ.extPositions L) :
          p ∈ (norm ρ L).extPositions L := by
        rw [hExtMerged, List.mem_filter]
        rw [hExtLv, List.mem_filter] at hp
        exact ⟨hp.1, by simp [hp.2]⟩
      have hSideL (ρ : Context) (L : ℕ) (hL : Inv ρ L) : (norm ρ L).sideAt L = ρ.sideAt L := by
        obtain ⟨-, -, h3, -⟩ := hL
        rcases hh : ((norm ρ L).extPositions L).head? with _ | p
        · have hρ : (ρ.extPositions L).head? = none := by
            cases hh2 : (ρ.extPositions L).head? with
            | none => rfl
            | some q =>
              exfalso
              have hq := hMemMerged ρ L q (List.mem_of_mem_head? (Option.mem_def.mpr hh2))
              rw [List.head?_eq_none_iff] at hh
              rw [hh] at hq
              exact List.not_mem_nil hq
          simp only [sideAt, hh, hρ]
        · have hp : p ∈ (norm ρ L).extPositions L := List.mem_of_mem_head? (Option.mem_def.mpr hh)
          rw [hExtMerged, List.mem_filter] at hp
          cases hlet : ρ.letterAt p with
          | child => simp [lv, hlet] at hp
          | ext j v =>
            have hj : j = L ∨ j = L + 1 := by
              have := hp.2
              simp only [lv, hlet, Bool.or_eq_true, decide_eq_true_eq] at this
              exact this
            have hv := h3 p j v hlet hj
            rw [← hv]
            simp only [sideAt, hh, hLetter, hlet]
            by_cases hjL : j ≤ L <;> simp [letter, hjL]
      have hSideNe (ρ : Context) (L j : ℕ) (hj1 : 1 ≤ j) (hjL : j ≠ L) :
          (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
        unfold sideAt
        rw [hExtNe ρ L j hj1 hjL]
        cases hh : (ρ.extPositions (up L j)).head? with
        | none => rfl
        | some p =>
          dsimp only
          rw [hLetter]
          cases ρ.letterAt p with
          | child => rfl
          | ext i v => by_cases hi : i ≤ L <;> simp [letter, hi]
      have hMax (ρ : Context) (L : ℕ) (hL : Inv ρ L) (j : ℕ) (hj1 : 1 ≤ j) :
          (norm ρ L).maximumAt j =
            if j < L then ρ.maximumAt j else if j = L then max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)
            else ρ.maximumAt (j + 1) := by
        obtain ⟨h1, h2, -, -⟩ := hL
        simp only [maximumAt, norm]
        rw [getElem?_merge ρ.maxima L (j - 1) _ h1 h2]
        by_cases hjl : j < L
        · simp [hjl, show j - 1 < L - 1 by omega]
        · by_cases hjL : j = L
          · subst hjL; simp
          · simp [hjl, hjL, show ¬ j - 1 < L - 1 by omega, show j - 1 ≠ L - 1 by omega,
              show j - 1 + 1 = j by omega]
      have hUpMono (L i j : ℕ) (h : i < j) : up L i < up L j := by
        dsimp [up]
        split_ifs <;> omega
      have hUpZero (L : ℕ) (hL : 1 ≤ L) : up L 0 = 0 := by
        simp [up, show 0 < L by omega]
      have hLive (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
          (hj : j ∈ (norm ρ L).levels) :
          1 ≤ j ∧ j < ρ.maxima.length ∧ up L j ∈ ρ.levels := by
        have hh := hNormLevel ρ L hL j hj
        refine ⟨hh.1, by omega, ?_⟩
        apply (hLevelMem ρ _).mpr
        dsimp [up]
        split_ifs <;> omega
      have hSide (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
          (hj : j ∈ (norm ρ L).levels) :
          (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
        have hj1 := (hNormLevel ρ L hL j hj).1
        by_cases he : j = L
        · subst j
          rw [hSideL ρ L hL]
          simpa only [up, lt_self_iff_false, if_false] using hL.2.2.2
        · exact hSideNe ρ L j hj1 he
      have hNoMerged (ρ : Context) (L : ℕ) (hL : Inv ρ L)
          (v : Side) (hv : v ≠ ρ.sideAt L) (top j : ℕ)
          (hj : j ∈ (norm ρ L).levelsOn v top) : j ≠ L := by
        intro he
        subst j
        have hc : (norm ρ L).sideAt L = v ∧ (top = 0 ∨ L < top) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        rw [hSideL ρ L hL] at hc
        exact hv hc.1.symm
      have hMaximum (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
          (hj : j ∈ (norm ρ L).levels) (hne : j ≠ L) :
          (norm ρ L).maximumAt j = ρ.maximumAt (up L j) := by
        rw [hMax ρ L hL j ((hNormLevel ρ L hL j hj).1)]
        by_cases hjl : j < L <;> simp [hjl, hne, up]
      have hOppLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
          (hv : v ≠ ρ.sideAt L) (top : ℕ) :
          (((norm ρ L).levelsOn v top).map (up L)) = ρ.levelsOn v (up L top) := by
        have hs : (((norm ρ L).levelsOn v top).map (up L)).Pairwise (· < ·) :=
          ((hSorted (norm ρ L)).filter _).map (up L) (fun i j hij => hUpMono L i j hij)
        apply hs.eq_of_mem_iff ((hSorted ρ).filter _)
        intro i
        constructor
        · intro hi
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
          have hjl := (List.mem_filter.mp hj).1
          have hjc : (norm ρ L).sideAt j = v ∧ (top = 0 ∨ j < top) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          apply List.mem_filter.mpr
          refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
          apply decide_eq_true
          refine ⟨?_, ?_⟩
          · rw [← hSide ρ L j hL hjl]
            exact hjc.1
          · rcases hjc.2 with rfl | hlt
            · exact Or.inl (hUpZero L hL.1)
            · exact Or.inr (hUpMono L j top hlt)
        · intro hi
          have hil := (List.mem_filter.mp hi).1
          have hic : ρ.sideAt i = v ∧ (up L top = 0 ∨ i < up L top) :=
            of_decide_eq_true (List.mem_filter.mp hi).2
          have hiL : i ≠ L := by
            intro he
            subst i
            exact hv hic.1.symm
          let j := if i < L then i else i-1
          have hLr : 1 ≤ L ∧ L ≤ ρ.maxima.length := ⟨hL.1, by omega⟩
          have hir := (hLevelMem ρ i).mp hil
          have hjr : 1 ≤ j ∧ j < ρ.maxima.length ∧ up L j = i := by
            dsimp [j, up]
            split_ifs <;> omega
          have hjl : j ∈ (norm ρ L).levels := by
            apply (hLevelMem (norm ρ L) j).mpr
            rw [hDepth ρ L hL]
            omega
          apply List.mem_map.mpr
          refine ⟨j, ?_, hjr.2.2⟩
          apply List.mem_filter.mpr
          refine ⟨hjl, ?_⟩
          apply decide_eq_true
          refine ⟨?_, ?_⟩
          · rw [hSide ρ L j hL hjl, hjr.2.2]
            exact hic.1
          · rcases hic.2 with hzero | hlt
            · left
              by_contra hne
              have h := hUpMono L 0 top (by omega)
              rw [hUpZero L hLr.1, hzero] at h
              omega
            · right
              by_contra hn
              have hm : up L top ≤ up L j := by
                rcases lt_or_eq_of_le (show top ≤ j by omega) with hm | he
                · exact (hUpMono L top j hm).le
                · rw [he]
              rw [hjr.2.2] at hm
              omega
      have hFoldNormLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
          ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (norm ρ L).levels ∧ j ≠ L) → ∀ z,
          ls.foldl (leftStep (norm ρ L)) z =
            (ls.map (up L)).foldl (leftStep ρ) z := by
        intro ls
        induction ls with
        | nil => intro _ z; rfl
        | cons j ls ih =>
          intro hj z
          simp only [List.foldl_cons, List.map_cons, leftStep,
            hExtNe ρ L j ((hLevelMem (norm ρ L) j).mp (hj j (by simp)).1).1
              (hj j (by simp)).2]
          exact ih (fun i hi => hj i (by simp [hi])) _
      have hFoldNormRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
          ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (norm ρ L).levels ∧ j ≠ L) → ∀ z,
          ls.foldl (rightStep (norm ρ L)) z =
            (ls.map (up L)).foldl (rightStep ρ) z := by
        intro ls
        induction ls with
        | nil => intro _ z; rfl
        | cons j ls ih =>
          intro hj z
          simp only [List.foldl_cons, List.map_cons, rightStep,
            hExtNe ρ L j ((hLevelMem (norm ρ L) j).mp (hj j (by simp)).1).1
              (hj j (by simp)).2]
          exact ih (fun i hi => hj i (by simp [hi])) _
      have hOppLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
          (hv : v ≠ ρ.sideAt L) (top p : ℕ) :
          (norm ρ L).leftExt v top p = ρ.leftExt v (up L top) p := by
        rw [leftExt_eq, leftExt_eq, ← hOppLevels ρ L hL v hv top,
          List.sublists_map, List.map_map]
        apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
        apply List.map_congr_left
        intro ls hls
        exact congrArg Prod.snd (hFoldNormLeft ρ L hL ls
          (fun j hj => ⟨(List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1,
            hNoMerged ρ L hL v hv top j ((List.mem_sublists.mp hls).subset hj)⟩) (p,0))
      have hOppRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
          (hv : v ≠ ρ.sideAt L) (top p : ℕ) :
          (norm ρ L).rightExt v top p = ρ.rightExt v (up L top) p := by
        rw [rightExt_eq, rightExt_eq, ← hOppLevels ρ L hL v hv top,
          List.sublists_map, List.map_map]
        apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
        apply List.map_congr_left
        intro ls hls
        exact congrArg Prod.snd (hFoldNormRight ρ L hL ls
          (fun j hj => ⟨(List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1,
            hNoMerged ρ L hL v hv top j ((List.mem_sublists.mp hls).subset hj)⟩) (p,0))
      have hOppChain (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
          (hv : v ≠ ρ.sideAt L) (p q : ℕ) :
          (norm ρ L).chainExt v p q = ρ.chainExt v p q := by
        simp only [chainExt, hOppLeft ρ L hL v hv, hOppRight ρ L hL v hv,
          hUpZero L hL.1]
      have hOppJoin (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
          (hv : v ≠ ρ.sideAt L) (p q : ℕ) :
          (norm ρ L).joinExt v p q = ρ.joinExt v p q := by
        have hl : (((norm ρ L).levelsOn v 0).map (up L)) = ρ.levelsOn v 0 := by
          simpa only [hUpZero L hL.1] using hOppLevels ρ L hL v hv 0
        rw [joinExt, joinExt, hOppChain ρ L hL v hv, ← hl, List.map_map]
        congr 1
        apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
        apply List.map_congr_left
        intro j hj
        rw [hOppLeft ρ L hL v hv, hOppRight ρ L hL v hv,
          hMaximum ρ L j hL (List.mem_filter.mp hj).1
            (hNoMerged ρ L hL v hv 0 j hj)]
        rfl
      have hYoungLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
          (norm ρ L).levelsOn (ρ.sideAt L) L = ρ.levelsOn (ρ.sideAt L) L := by
        apply ((hSorted (norm ρ L)).filter _).eq_of_mem_iff ((hSorted ρ).filter _)
        intro j
        constructor
        · intro hj
          have hjl := (List.mem_filter.mp hj).1
          have hjc : (norm ρ L).sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          have hjlt : j < L := by omega
          have hj1 := (hNormLevel ρ L hL j hjl).1
          have hs := hSideNe ρ L j hj1 (by omega)
          have hu : up L j = j := by simp [up, hjlt]
          rw [hu] at hs
          exact List.mem_filter.mpr ⟨by
            have hh := (hLive ρ L j hL hjl).2.2
            simpa only [hu] using hh,
            by apply decide_eq_true; exact ⟨hs.symm.trans hjc.1, Or.inr hjlt⟩⟩
        · intro hj
          have hjl := (List.mem_filter.mp hj).1
          have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          have hjlt : j < L := by omega
          have hj1 := ((hLevelMem ρ j).mp hjl).1
          have hjn : j ∈ (norm ρ L).levels := by
            apply (hLevelMem (norm ρ L) j).mpr
            rw [hDepth ρ L hL]
            omega
          have hs := hSideNe ρ L j hj1 (by omega)
          have hu : up L j = j := by simp [up, hjlt]
          rw [hu] at hs
          exact List.mem_filter.mpr ⟨hjn,
            by apply decide_eq_true; exact ⟨hs.trans hjc.1, Or.inr hjlt⟩⟩
      have hSourcePairLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
          ρ.levelsOn (ρ.sideAt L) 0 = ρ.levelsOn (ρ.sideAt L) L ++ [L, L + 1] := by
        have hLs : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
          apply List.mem_filter.mpr
          exact ⟨(hLevelMem ρ L).mpr ⟨hL.1, by omega⟩, by simp⟩
        have hL1s : L + 1 ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
          apply List.mem_filter.mpr
          exact ⟨(hLevelMem ρ (L + 1)).mpr ⟨by omega, hL.2.1⟩,
            by apply decide_eq_true; exact ⟨hL.2.2.2.symm, Or.inl rfl⟩⟩
        have hs : (ρ.levelsOn (ρ.sideAt L) L ++ [L, L + 1]).Pairwise (· < ·) := by
          apply List.pairwise_append.mpr
          refine ⟨(hSorted ρ).filter _, by simp, ?_⟩
          intro i hi j hj
          have hc : ρ.sideAt i = ρ.sideAt L ∧ (L = 0 ∨ i < L) :=
            of_decide_eq_true (List.mem_filter.mp hi).2
          have hiL : i < L := by omega
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl <;> omega
        apply ((hSorted ρ).filter _).eq_of_mem_iff hs
        intro j
        constructor
        · intro hj
          have hjL := ht j hj
          by_cases he : j = L
          · simp [he]
          by_cases he1 : j = L + 1
          · simp [he1]
          apply List.mem_append.mpr
          left
          apply List.mem_filter.mpr
          refine ⟨(List.mem_filter.mp hj).1, ?_⟩
          apply decide_eq_true
          have hc : ρ.sideAt j = ρ.sideAt L ∧ (0 = 0 ∨ j < 0) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          exact ⟨hc.1, Or.inr (by omega)⟩
        · intro hj
          rcases List.mem_append.mp hj with hj | hj
          · apply List.mem_filter.mpr
            refine ⟨(List.mem_filter.mp hj).1, ?_⟩
            apply decide_eq_true
            have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
              of_decide_eq_true (List.mem_filter.mp hj).2
            exact ⟨hc.1, Or.inl rfl⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl
            · exact hLs
            · exact hL1s
      have hSourceOwnLevels (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) :
          ρ.levelsOn (ρ.sideAt L) 0 = ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
        have hLs : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by simp [levelsOn, hL]
        have hs : (ρ.levelsOn (ρ.sideAt L) L ++ [L]).Pairwise (· < ·) := by
          apply List.pairwise_append.mpr
          refine ⟨(hSorted ρ).filter _, by simp, ?_⟩
          intro i hi j hj
          have he : j = L := by simpa using hj
          subst j
          have hc : ρ.sideAt i = ρ.sideAt L ∧ (L = 0 ∨ i < L) :=
            of_decide_eq_true (List.mem_filter.mp hi).2
          have hL1 := one_le_of_mem_levels hL
          omega
        apply ((hSorted ρ).filter _).eq_of_mem_iff hs
        intro j
        constructor
        · intro hj
          have hjL := ht j hj
          by_cases he : j = L
          · simp [he]
          · apply List.mem_append.mpr
            left
            apply List.mem_filter.mpr
            refine ⟨(List.mem_filter.mp hj).1, ?_⟩
            apply decide_eq_true
            have hc : ρ.sideAt j = ρ.sideAt L ∧ (0 = 0 ∨ j < 0) :=
              of_decide_eq_true (List.mem_filter.mp hj).2
            exact ⟨hc.1, Or.inr (by omega)⟩
        · intro hj
          rcases List.mem_append.mp hj with hj | hj
          · apply List.mem_filter.mpr
            refine ⟨(List.mem_filter.mp hj).1, ?_⟩
            apply decide_eq_true
            have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
              of_decide_eq_true (List.mem_filter.mp hj).2
            exact ⟨hc.1, Or.inl rfl⟩
          · have he : j = L := by simpa using hj
            simpa [levelsOn, he] using hLs
      have hNormOwnLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
          (norm ρ L).levelsOn (ρ.sideAt L) 0 =
            ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
        have hNL : L ∈ (norm ρ L).levels := by
          apply (hLevelMem (norm ρ L) L).mpr
          rw [hDepth ρ L hL]
          omega
        have hAll : ∀ j ∈ (norm ρ L).levelsOn ((norm ρ L).sideAt L) 0, j ≤ L := by
          intro j hj
          have hjl := (List.mem_filter.mp hj).1
          have hjc : (norm ρ L).sideAt j = (norm ρ L).sideAt L ∧ (0 = 0 ∨ j < 0) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          have hh : up L j ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
            apply List.mem_filter.mpr
            refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
            apply decide_eq_true
            rw [← hSide ρ L j hL hjl, ← hSideL ρ L hL]
            exact ⟨hjc.1, Or.inl rfl⟩
          have hm := ht (up L j) hh
          dsimp [up] at hm
          split_ifs at hm <;> omega
        have hh := hSourceOwnLevels (norm ρ L) L hNL hAll
        rw [hSideL ρ L hL, hYoungLevels ρ L hL] at hh
        exact hh
      have hYoungFoldLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
          ∀ (ls : List ℕ), ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists → ∀ (z : ℕ × ℕ),
          ls.foldl (leftStep (norm ρ L)) z = ls.foldl (leftStep ρ) z := by
        intro ls
        have hGeneral : ∀ (ls : List ℕ),
            (∀ j ∈ ls, j ∈ ρ.levelsOn (ρ.sideAt L) L) → ∀ (z : ℕ × ℕ),
            ls.foldl (leftStep (norm ρ L)) z = ls.foldl (leftStep ρ) z := by
          intro ls
          induction ls with
          | nil => intro _ z; rfl
          | cons j ls ih =>
            intro hj z
            have hjl := (List.mem_filter.mp (hj j (by simp))).1
            have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
              of_decide_eq_true (List.mem_filter.mp (hj j (by simp))).2
            have hjlt : j < L := by omega
            have hj1 := ((hLevelMem ρ j).mp hjl).1
            have he := hExtNe ρ L j hj1 (by omega)
            rw [show up L j = j by simp [up, hjlt]] at he
            simp only [List.foldl_cons, leftStep, he]
            exact ih (fun i hi => hj i (by simp [hi])) _
        intro hls z
        exact hGeneral ls (fun j hj => (List.mem_sublists.mp hls).subset hj) z
      have hDecomposeSublists (Y T ls : List ℕ) (hls : ls ∈ (Y ++ T).sublists) :
          ∃ ys ∈ Y.sublists, ∃ ts ∈ T.sublists, ls = ys ++ ts := by
        rw [List.sublists_append, List.bind_eq_flatMap] at hls
        obtain ⟨ts, hts, hh⟩ := List.mem_flatMap.mp hls
        obtain ⟨ys, hys, he⟩ := List.mem_map.mp hh
        exact ⟨ys, hys, ts, hts, he.symm⟩
      have hFoldCountLeft (ρ : Context) : ∀ (ls : List ℕ) (z : ℕ × ℕ),
          (ls.foldl (leftStep ρ) z).2 ≤ z.2 + ls.length := by
        intro ls
        induction ls with
        | nil => intro z; simp
        | cons j ls ih =>
          intro z
          have hstep : (leftStep ρ z j).2 ≤ z.2 + 1 := by
            cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? <;>
              simp [leftStep, hh]
          have hh := ih (leftStep ρ z j)
          simp only [List.foldl_cons, List.length_cons]
          omega
      have hLeftStepAdd (ρ : Context) (j e c : ℕ)
          (hex : ∃ y ∈ ρ.extPositions j, y < e) :
          (leftStep ρ (e,c) j).2 = c + 1 := by
        cases hh : ((ρ.extPositions j).filter (· < e)).getLast? with
        | some y => simp [leftStep, hh]
        | none =>
          obtain ⟨y, hy, hye⟩ := hex
          have hm : y ∈ (ρ.extPositions j).filter (· < e) := by simp [hy, hye]
          rw [List.getLast?_eq_none_iff] at hh
          rw [hh] at hm
          exact False.elim (List.not_mem_nil hm)
      have hFoldBoundary (ρ : Context) (x : ℕ) (dir : Bool) :
          ∀ (ls : List ℕ),
          (∀ j ∈ ls, ∀ y ∈ ρ.extPositions j, if dir then y < x else x < y) →
          ∀ z : ℕ × ℕ, (if dir then z.1 < x else x < z.1) →
          (if dir then (ls.foldl (leftStep ρ) z).1 < x
            else x < (ls.foldl (leftStep ρ) z).1) ∧
          (if dir then (ls.foldl (rightStep ρ) z).1 < x
            else x < (ls.foldl (rightStep ρ) z).1) := by
        intro ls
        induction ls with
        | nil => intro _ z hz; exact ⟨hz,hz⟩
        | cons j ls ih =>
          intro hy z hz
          have ht := fun i hi y hiy => hy i (List.mem_cons_of_mem j hi) y hiy
          constructor
          · cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? with
            | none => simpa only [List.foldl_cons, leftStep, hh] using (ih ht z hz).1
            | some y =>
              have hm := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
              have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
              simpa only [List.foldl_cons, leftStep, hh] using (ih ht (y,z.2+1) hyx).1
          · cases hh : ((ρ.extPositions j).filter (z.1 < ·)).head? with
            | none => simpa only [List.foldl_cons, rightStep, hh] using (ih ht z hz).2
            | some y =>
              have hm := List.mem_of_mem_head? (Option.mem_def.mpr hh)
              have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
              simpa only [List.foldl_cons, rightStep, hh] using (ih ht (y,z.2+1) hyx).2
      have hSourceLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
          (hsingle : ρ.extPositions L = [x])
          (hafter : ∀ y ∈ ρ.extPositions (L+1), x < y)
          (hc : ∀ p ∈ ρ.childPositions, x < p)
          (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L+1)
          (p : ℕ) (hp : p ∈ ρ.childPositions) :
          ρ.leftExt (ρ.sideAt L) 0 p = ρ.leftExt (ρ.sideAt L) L p + 1 := by
        let Y := ρ.levelsOn (ρ.sideAt L) L
        have hnil : (ρ.extPositions (L+1)).filter (· < x) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro y hy
          simp [show ¬ y < x by have := hafter y hy; omega]
        have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
            ((ys ++ [L,L+1]).foldl (leftStep ρ) (p,0)).2 =
              (ys.foldl (leftStep ρ) (p,0)).2 + 1 := by
          let z := ys.foldl (leftStep ρ) (p,0)
          have hz := (hFoldBoundary ρ x false ys
            (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
            (p,0) (hc p hp)).1
          change x < z.1 at hz
          have hs : leftStep ρ z L = (x,z.2+1) := by
            simp [leftStep,hsingle,hz]
          rw [List.foldl_append]
          change (leftStep ρ (leftStep ρ z L) (L+1)).2 = z.2+1
          rw [hs]
          simp [leftStep,hnil]
        have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
            (ys.foldl (leftStep ρ) (p,0)).2 + 1 ≤ ρ.leftExt (ρ.sideAt L) 0 p := by
          have hsub : ys ++ [L,L+1] ∈ (ρ.levelsOn (ρ.sideAt L) 0).sublists := by
            rw [hSourcePairLevels ρ L hL ht]
            exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
          have hh : ((ys ++ [L,L+1]).foldl (leftStep ρ) (p,0)).2 ≤
              ρ.leftExt (ρ.sideAt L) 0 p := by
            rw [leftExt_eq]
            exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L,L+1],hsub,rfl⟩)
          rwa [hAdd ys hys] at hh
        apply le_antisymm
        · rw [leftExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ls,hls,rfl⟩ := List.mem_map.mp hz
          rw [hSourcePairLevels ρ L hL ht] at hls
          obtain ⟨ys,hys,ts,hts,rfl⟩ := hDecomposeSublists Y [L,L+1] ls hls
          have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
              ρ.leftExt (ρ.sideAt L) L p := by
            rw [leftExt_eq]
            exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys,hys,rfl⟩)
          have htail : (ts.foldl (leftStep ρ) (ys.foldl (leftStep ρ) (p,0))).2 ≤
              (ys.foldl (leftStep ρ) (p,0)).2+1 := by
            change ts ∈ [[],[L],[L+1],[L,L+1]] at hts
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hts
            rcases hts with rfl | rfl | rfl | rfl
            · simp
            · simpa using hFoldCountLeft ρ [L] (ys.foldl (leftStep ρ) (p,0))
            · simpa using hFoldCountLeft ρ [L+1] (ys.foldl (leftStep ρ) (p,0))
            · have he := hAdd ys hys
              rw [List.foldl_append] at he
              exact he.le
          rw [List.foldl_append]
          exact htail.trans (Nat.add_le_add_right hprefix 1)
        · have h1 : 1 ≤ ρ.leftExt (ρ.sideAt L) 0 p := by
            simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
          have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤ ρ.leftExt (ρ.sideAt L) 0 p-1 := by
            rw [leftExt_eq]
            apply getD_max?_le
            intro z hz
            obtain ⟨ys,hys,rfl⟩ := List.mem_map.mp hz
            have hh := hLe ys hys
            omega
          omega
      have hNormLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
          (hsingle : ρ.extPositions L = [x])
          (hc : ∀ p ∈ ρ.childPositions, x < p)
          (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (p : ℕ) (hp : p ∈ ρ.childPositions) :
          (norm ρ L).leftExt (ρ.sideAt L) 0 p = ρ.leftExt (ρ.sideAt L) L p + 1 := by
        let Y := ρ.levelsOn (ρ.sideAt L) L
        have hx : x ∈ (norm ρ L).extPositions L :=
          hMemMerged ρ L x (by simp [hsingle])
        have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
            ((ys ++ [L]).foldl (leftStep (norm ρ L)) (p,0)).2 =
              (ys.foldl (leftStep ρ) (p,0)).2 + 1 := by
          let z := ys.foldl (leftStep ρ) (p,0)
          have hz := (hFoldBoundary ρ x false ys
            (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
            (p,0) (hc p hp)).1
          change x < z.1 at hz
          rw [List.foldl_append, hYoungFoldLeft ρ L hL ys hys]
          change (leftStep (norm ρ L) z L).2 = z.2 + 1
          exact hLeftStepAdd (norm ρ L) L z.1 z.2 ⟨x, hx, hz⟩
        have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
            (ys.foldl (leftStep ρ) (p,0)).2 + 1 ≤
              (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
          have hsub : ys ++ [L] ∈ ((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists := by
            rw [hNormOwnLevels ρ L hL ht]
            exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
          have hh : ((ys ++ [L]).foldl (leftStep (norm ρ L)) (p,0)).2 ≤
              (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
            rw [leftExt_eq]
            exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L], hsub, rfl⟩)
          rwa [hAdd ys hys] at hh
        apply le_antisymm
        · rw [leftExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
          rw [hNormOwnLevels ρ L hL ht] at hls
          obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
          have hcount := hFoldCountLeft (norm ρ L) ts
            (ys.foldl (leftStep (norm ρ L)) (p,0))
          rw [hYoungFoldLeft ρ L hL ys hys] at hcount
          have hlen : ts.length ≤ 1 := by
            simpa using (List.mem_sublists.mp hts).length_le
          have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
              ρ.leftExt (ρ.sideAt L) L p := by
            rw [leftExt_eq]
            exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
          rw [List.foldl_append, hYoungFoldLeft ρ L hL ys hys]
          omega
        · have h1 : 1 ≤ (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
            simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
          have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤
              (norm ρ L).leftExt (ρ.sideAt L) 0 p - 1 := by
            rw [leftExt_eq]
            apply getD_max?_le
            intro z hz
            obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
            have hh := hLe ys hys
            omega
          omega
      have hYoungFoldRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
          ∀ (ls : List ℕ), ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists → ∀ (z : ℕ × ℕ),
          ls.foldl (rightStep (norm ρ L)) z = ls.foldl (rightStep ρ) z := by
        intro ls
        have hGeneral : ∀ (ls : List ℕ),
            (∀ j ∈ ls, j ∈ ρ.levelsOn (ρ.sideAt L) L) → ∀ (z : ℕ × ℕ),
            ls.foldl (rightStep (norm ρ L)) z = ls.foldl (rightStep ρ) z := by
          intro ls
          induction ls with
          | nil => intro _ z; rfl
          | cons j ls ih =>
            intro hj z
            have hjl := (List.mem_filter.mp (hj j (by simp))).1
            have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
              of_decide_eq_true (List.mem_filter.mp (hj j (by simp))).2
            have hjlt : j < L := by omega
            have hj1 := ((hLevelMem ρ j).mp hjl).1
            have he := hExtNe ρ L j hj1 (by omega)
            rw [show up L j = j by simp [up, hjlt]] at he
            simp only [List.foldl_cons, rightStep, he]
            exact ih (fun i hi => hj i (by simp [hi])) _
        intro hls z
        exact hGeneral ls (fun j hj => (List.mem_sublists.mp hls).subset hj) z
      have hMergedRightStep (ρ : Context) (L x : ℕ)
          (hsingle : ρ.extPositions L = [x]) (z : ℕ × ℕ) (hx : x < z.1) :
          rightStep (norm ρ L) z L = rightStep ρ z (L + 1) := by
        have he : ((norm ρ L).extPositions L).filter (z.1 < ·) =
            (ρ.extPositions (L + 1)).filter (z.1 < ·) := by
          have hs₁ : ((norm ρ L).extPositions L).Pairwise (· < ·) :=
            List.pairwise_lt_range.filter _
          have hs₂ : (ρ.extPositions (L + 1)).Pairwise (· < ·) :=
            List.pairwise_lt_range.filter _
          apply (hs₁.filter _).eq_of_mem_iff (hs₂.filter _)
          intro p
          rw [hExtMerged, hExtLv]
          simp only [List.mem_filter, Bool.or_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨⟨hp, hpL | hpO⟩, hzp⟩
            · have hm : p ∈ ρ.extPositions L := by
                rw [hExtLv]
                exact List.mem_filter.mpr ⟨hp, hpL⟩
              have hpx : p = x := by simpa [hsingle] using hm
              omega
            · exact ⟨⟨hp, hpO⟩, hzp⟩
          · rintro ⟨⟨hp, hpO⟩, hzp⟩
            exact ⟨⟨hp, Or.inr hpO⟩, hzp⟩
        simp only [rightStep, he]
      have hNewRightStep (ρ : Context) (L x : ℕ)
          (hsingle : ρ.extPositions L = [x]) (z : ℕ × ℕ) (hx : x < z.1) :
          rightStep ρ z L = z := by
        rcases z with ⟨e,c⟩
        simp only at hx
        simp [rightStep, hsingle, show ¬ e < x by omega]
      have hOwnRight (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
          (hsingle : ρ.extPositions L = [x])
          (hc : ∀ p ∈ ρ.childPositions, x < p)
          (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (p : ℕ) (hp : p ∈ ρ.childPositions) :
          ρ.rightExt (ρ.sideAt L) 0 p = (norm ρ L).rightExt (ρ.sideAt L) 0 p := by
        let Y := ρ.levelsOn (ρ.sideAt L) L
        have hTail (ys ts : List ℕ) (hys : ys ∈ Y.sublists)
            (hts : ts ∈ [L, L + 1].sublists) :
            ∃ us ∈ [L].sublists,
              (ys ++ ts).foldl (rightStep ρ) (p,0) =
                (ys ++ us).foldl (rightStep (norm ρ L)) (p,0) := by
          let z := ys.foldl (rightStep ρ) (p,0)
          have hz := (hFoldBoundary ρ x false ys
            (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
            (p,0) (hc p hp)).2
          change x < z.1 at hz
          have hcases : ts = [] ∨ ts = [L] ∨ ts = [L + 1] ∨ ts = [L, L + 1] := by
            simpa [List.sublists_cons] using hts
          rcases hcases with rfl | rfl | rfl | rfl
          · refine ⟨[], by simp, ?_⟩
            simpa only [List.append_nil] using (hYoungFoldRight ρ L hL ys hys (p,0)).symm
          · refine ⟨[], by simp, ?_⟩
            rw [List.foldl_append, List.append_nil, hYoungFoldRight ρ L hL ys hys]
            change rightStep ρ z L = z
            exact hNewRightStep ρ L x hsingle z hz
          · refine ⟨[L], by simp [List.sublists_cons], ?_⟩
            rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
            change rightStep ρ z (L + 1) = rightStep (norm ρ L) z L
            exact (hMergedRightStep ρ L x hsingle z hz).symm
          · refine ⟨[L], by simp [List.sublists_cons], ?_⟩
            rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
            change rightStep ρ (rightStep ρ z L) (L + 1) = rightStep (norm ρ L) z L
            rw [hNewRightStep ρ L x hsingle z hz]
            exact (hMergedRightStep ρ L x hsingle z hz).symm
        have hBack (ys us : List ℕ) (hys : ys ∈ Y.sublists)
            (hus : us ∈ [L].sublists) :
            ∃ ts ∈ [L, L + 1].sublists,
              (ys ++ us).foldl (rightStep (norm ρ L)) (p,0) =
                (ys ++ ts).foldl (rightStep ρ) (p,0) := by
          let z := ys.foldl (rightStep ρ) (p,0)
          have hz := (hFoldBoundary ρ x false ys
            (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
            (p,0) (hc p hp)).2
          change x < z.1 at hz
          have hcases : us = [] ∨ us = [L] := by simpa [List.sublists_cons] using hus
          rcases hcases with rfl | rfl
          · refine ⟨[], by simp, ?_⟩
            simpa only [List.append_nil] using hYoungFoldRight ρ L hL ys hys (p,0)
          · refine ⟨[L + 1], by simp [List.sublists_cons], ?_⟩
            rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
            change rightStep (norm ρ L) z L = rightStep ρ z (L + 1)
            exact hMergedRightStep ρ L x hsingle z hz
        apply le_antisymm
        · rw [rightExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
          rw [hSourcePairLevels ρ L hL ht] at hls
          obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L, L + 1] ls hls
          obtain ⟨us, hus, he⟩ := hTail ys ts hys hts
          have hsub : ys ++ us ∈ ((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists := by
            rw [hNormOwnLevels ρ L hL ht]
            exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.mem_sublists.mp hus))
          rw [he, rightExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ us, hsub, rfl⟩)
        · rw [rightExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
          rw [hNormOwnLevels ρ L hL ht] at hls
          obtain ⟨ys, hys, us, hus, rfl⟩ := hDecomposeSublists Y [L] ls hls
          obtain ⟨ts, hts, he⟩ := hBack ys us hys hus
          have hsub : ys ++ ts ∈ (ρ.levelsOn (ρ.sideAt L) 0).sublists := by
            rw [hSourcePairLevels ρ L hL ht]
            exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.mem_sublists.mp hts))
          rw [he, rightExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ ts, hsub, rfl⟩)
      have hTopFilter (ρ : Context) (v : Side) (top : ℕ) (htop : 1 ≤ top) :
          ρ.levelsOn v top = (ρ.levelsOn v 0).filter (· < top) := by
        simp only [levelsOn, List.filter_filter]
        apply List.filter_congr
        intro j _
        simp [show top ≠ 0 by omega, Bool.and_comm]
      have hLevelsAtTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) :
          (norm ρ L).levelsOn (ρ.sideAt L) top = ρ.levelsOn (ρ.sideAt L) top := by
        rw [hTopFilter (norm ρ L) (ρ.sideAt L) top htop, hNormOwnLevels ρ L hL ht,
          hTopFilter ρ (ρ.sideAt L) top htop, hSourcePairLevels ρ L hL ht,
          List.filter_append, List.filter_append]
        simp [show ¬ L < top by omega, show ¬ L + 1 < top by omega]
      have hMidLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
          ρ.levelsOn (ρ.sideAt L) (L + 1) = ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
        rw [hTopFilter ρ (ρ.sideAt L) (L + 1) (by omega),
          hSourcePairLevels ρ L hL ht, List.filter_append]
        have hf : (ρ.levelsOn (ρ.sideAt L) L).filter (· < L + 1) =
            ρ.levelsOn (ρ.sideAt L) L := by
          apply List.filter_eq_self.mpr
          intro j hj
          apply decide_eq_true
          have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          omega
        rw [hf]
        simp
      have hYoungLeftTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) (p : ℕ) :
          (norm ρ L).leftExt (ρ.sideAt L) top p = ρ.leftExt (ρ.sideAt L) top p := by
        rw [leftExt_eq, leftExt_eq, hLevelsAtTop ρ L hL ht top htop htL]
        apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
        apply List.map_congr_left
        intro ls hls
        have hs : ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists :=
          List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans
            (levelsOn_sublist_of_le ρ (ρ.sideAt L) htop htL))
        exact congrArg Prod.snd (hYoungFoldLeft ρ L hL ls hs (p,0))
      have hYoungRightTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) (p : ℕ) :
          (norm ρ L).rightExt (ρ.sideAt L) top p = ρ.rightExt (ρ.sideAt L) top p := by
        rw [rightExt_eq, rightExt_eq, hLevelsAtTop ρ L hL ht top htop htL]
        apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
        apply List.map_congr_left
        intro ls hls
        have hs : ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists :=
          List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans
            (levelsOn_sublist_of_le ρ (ρ.sideAt L) htop htL))
        exact congrArg Prod.snd (hYoungFoldRight ρ L hL ls hs (p,0))
      have hMidLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
          (hsingle : ρ.extPositions L = [x])
          (hc : ∀ p ∈ ρ.childPositions, x < p)
          (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (p : ℕ) (hp : p ∈ ρ.childPositions) :
          ρ.leftExt (ρ.sideAt L) (L + 1) p = ρ.leftExt (ρ.sideAt L) L p + 1 := by
        let Y := ρ.levelsOn (ρ.sideAt L) L
        have hx : x ∈ ρ.extPositions L := by simp [hsingle]
        have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
            ((ys ++ [L]).foldl (leftStep ρ) (p,0)).2 =
              (ys.foldl (leftStep ρ) (p,0)).2 + 1 := by
          let z := ys.foldl (leftStep ρ) (p,0)
          have hz := (hFoldBoundary ρ x false ys
            (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
            (p,0) (hc p hp)).1
          change x < z.1 at hz
          rw [List.foldl_append]
          change (leftStep ρ z L).2 = z.2 + 1
          exact hLeftStepAdd ρ L z.1 z.2 ⟨x, hx, hz⟩
        have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
            (ys.foldl (leftStep ρ) (p,0)).2 + 1 ≤
              ρ.leftExt (ρ.sideAt L) (L + 1) p := by
          have hsub : ys ++ [L] ∈ (ρ.levelsOn (ρ.sideAt L) (L + 1)).sublists := by
            rw [hMidLevels ρ L hL ht]
            exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
          have hh : ((ys ++ [L]).foldl (leftStep ρ) (p,0)).2 ≤
              ρ.leftExt (ρ.sideAt L) (L + 1) p := by
            rw [leftExt_eq]
            exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L], hsub, rfl⟩)
          rwa [hAdd ys hys] at hh
        apply le_antisymm
        · rw [leftExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
          rw [hMidLevels ρ L hL ht] at hls
          obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
          have hcount := hFoldCountLeft ρ ts
            (ys.foldl (leftStep ρ) (p,0))
          have hlen : ts.length ≤ 1 := by
            simpa using (List.mem_sublists.mp hts).length_le
          have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
              ρ.leftExt (ρ.sideAt L) L p := by
            rw [leftExt_eq]
            exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
          rw [List.foldl_append]
          omega
        · have h1 : 1 ≤ ρ.leftExt (ρ.sideAt L) (L + 1) p := by
            simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
          have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤
              ρ.leftExt (ρ.sideAt L) (L + 1) p - 1 := by
            rw [leftExt_eq]
            apply getD_max?_le
            intro z hz
            obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
            have hh := hLe ys hys
            omega
          omega
      have hMidRight (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
          (hsingle : ρ.extPositions L = [x])
          (hc : ∀ p ∈ ρ.childPositions, x < p)
          (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (p : ℕ) (hp : p ∈ ρ.childPositions) :
          ρ.rightExt (ρ.sideAt L) (L + 1) p = ρ.rightExt (ρ.sideAt L) L p := by
        let Y := ρ.levelsOn (ρ.sideAt L) L
        apply le_antisymm
        · rw [rightExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
          rw [hMidLevels ρ L hL ht] at hls
          obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
          have hboundary := (hFoldBoundary ρ x false ys
            (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
            (p,0) (hc p hp)).2
          change x < (ys.foldl (rightStep ρ) (p,0)).1 at hboundary
          have hcases : ts = [] ∨ ts = [L] := by simpa [List.sublists_cons] using hts
          have hprefix : (ys.foldl (rightStep ρ) (p,0)).2 ≤
              ρ.rightExt (ρ.sideAt L) L p := by
            rw [rightExt_eq]
            exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
          rcases hcases with rfl | rfl
          · simpa only [List.append_nil] using hprefix
          · rw [List.foldl_append]
            change (rightStep ρ (ys.foldl (rightStep ρ) (p,0)) L).2 ≤ _
            rw [hNewRightStep ρ L x hsingle _ hboundary]
            exact hprefix
        · rw [rightExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
          have hsub : ys ∈ (ρ.levelsOn (ρ.sideAt L) (L + 1)).sublists := by
            rw [hMidLevels ρ L hL ht]
            exact List.mem_sublists.mpr (by
              simpa only [List.append_nil] using
                ((List.mem_sublists.mp hys).append (List.nil_sublist [L])))
          rw [rightExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hsub, rfl⟩)
      have hOwnChain (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
          (hsingle : ρ.extPositions L = [x])
          (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
          (hc : ∀ p ∈ ρ.childPositions, x < p)
          (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
          ρ.chainExt (ρ.sideAt L) p q = (norm ρ L).chainExt (ρ.sideAt L) p q := by
        have hl := hSourceLeft ρ L x hL hsingle hafter hc hy ht p hp
        have hn := hNormLeft ρ L x hL hsingle hc hy ht p hp
        have hr := hOwnRight ρ L x hL hsingle hc hy ht q hq
        unfold chainExt
        omega
      have hMaxAppend (A B : List ℕ) :
          ((A ++ B).max?).getD 0 = max (A.max?.getD 0) (B.max?.getD 0) := by
        apply le_antisymm
        · apply getD_max?_le
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact (le_getD_max?_of_mem hz).trans (le_max_left _ _)
          · exact (le_getD_max?_of_mem hz).trans (le_max_right _ _)
        · apply max_le
          · apply getD_max?_le_of_forall
            intro z hz
            exact ⟨z, List.mem_append_left _ hz, le_rfl⟩
          · apply getD_max?_le_of_forall
            intro z hz
            exact ⟨z, List.mem_append_right _ hz, le_rfl⟩
      have hMaxSingle (z : ℕ) : ([z].max?).getD 0 = z := by simp
      have hMaxPair (z w : ℕ) : ([z,w].max?).getD 0 = max z w := by
        simpa only [List.singleton_append, hMaxSingle] using hMaxAppend [z] [w]
      have hOwnJoin (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
          (hsingle : ρ.extPositions L = [x])
          (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
          (hc : ∀ p ∈ ρ.childPositions, x < p)
          (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
          ρ.joinExt (ρ.sideAt L) p q =
            (norm ρ L).joinExt (ρ.sideAt L) p q := by
        let f := fun j => ρ.leftExt (ρ.sideAt L) j p +
          ρ.rightExt (ρ.sideAt L) j q + ρ.maximumAt j
        let g := fun j => (norm ρ L).leftExt (ρ.sideAt L) j p +
          (norm ρ L).rightExt (ρ.sideAt L) j q + (norm ρ L).maximumAt j
        have hYoungMap :
            (ρ.levelsOn (ρ.sideAt L) L).map g =
              (ρ.levelsOn (ρ.sideAt L) L).map f := by
          apply List.map_congr_left
          intro j hj
          have hj1 := one_le_of_mem_levels (List.mem_filter.mp hj).1
          have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          have hjL : j < L := by have := hL.1; omega
          dsimp [f,g]
          rw [hYoungLeftTop ρ L hL ht j hj1 (by omega) p,
            hYoungRightTop ρ L hL ht j hj1 (by omega) q,
            hMax ρ L hL j hj1]
          simp only [hjL, if_true]
        have hMergedValue : g L = max (f L) (f (L + 1)) := by
          dsimp [f,g]
          rw [hYoungLeftTop ρ L hL ht L hL.1 le_rfl p,
            hYoungRightTop ρ L hL ht L hL.1 le_rfl q,
            hMax ρ L hL L hL.1,
            hMidLeft ρ L x hL hsingle hc hy ht p hp,
            hMidRight ρ L x hL hsingle hc hy ht q hq]
          simp only [lt_self_iff_false, if_false, if_true]
          omega
        change max (ρ.chainExt (ρ.sideAt L) p q)
            (((ρ.levelsOn (ρ.sideAt L) 0).map f).max?.getD 0) =
          max ((norm ρ L).chainExt (ρ.sideAt L) p q)
            ((((norm ρ L).levelsOn (ρ.sideAt L) 0).map g).max?.getD 0)
        rw [hOwnChain ρ L x hL hsingle hafter hc hy ht p q hp hq,
          hSourcePairLevels ρ L hL ht, hNormOwnLevels ρ L hL ht,
          List.map_append, List.map_append, hMaxAppend, hMaxAppend, hYoungMap]
        simp only [List.map_cons, List.map_nil, hMaxPair, hMaxSingle]
        rw [← hMergedValue]
      have hCaps (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
          (hsingle : ρ.extPositions L = [x])
          (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
          (hc : ∀ p ∈ ρ.childPositions, x < p)
          (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (hG : (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k)
          (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
          ρ.cupLimit p q = (norm ρ L).cupLimit p q ∧
          ρ.capLimit p q = (norm ρ L).capLimit p q := by
        have hc' := hOwnChain ρ L x hL hsingle hafter hc hy ht p q hp hq
        have hj' := hOwnJoin ρ L x hL hsingle hafter hc hy ht p q hp hq
        cases hs : ρ.sideAt L with
        | lower =>
          rw [hs] at hc' hj' hG
          change ρ.u ≤ ρ.k at hG
          have hOC := hOppChain ρ L hL Side.upper (by simp [hs]) p q
          have hOJ := hOppJoin ρ L hL Side.upper (by simp [hs]) p q
          have ha : (norm ρ L).a = ρ.a := rfl
          have hu : (norm ρ L).u = ρ.u := rfl
          unfold cupLimit capLimit
          rw [ha, hu, hK, hc', hj', hOC, hOJ]
          exact ⟨rfl,rfl⟩
        | upper =>
          rw [hs] at hc' hj' hG
          change ρ.a ≤ ρ.k at hG
          have hOC := hOppChain ρ L hL Side.lower (by simp [hs]) p q
          have hOJ := hOppJoin ρ L hL Side.lower (by simp [hs]) p q
          have ha : (norm ρ L).a = ρ.a := rfl
          have hu : (norm ρ L).u = ρ.u := rfl
          unfold cupLimit capLimit
          rw [ha, hu, hK, hc', hj', hOC, hOJ]
          exact ⟨rfl,rfl⟩
      have hNormPart (ρ : Context) (keep : List ℕ) (v : Side) (m L : ℕ) (hL1 : 1 ≤ L) :
          norm (ρ.part keep v m) (L + 1) = (norm ρ L).part keep v m := by
        have hw : (norm (ρ.part keep v m) (L + 1)).word = ((norm ρ L).part keep v m).word := by
          change ((ρ.part keep v m).word.map (letter (L + 1))) =
            (List.range (norm ρ L).word.length).map (fun p => match (norm ρ L).letterAt p with
              | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 v
              | Letter.ext j w => Letter.ext (j + 1) w)
          rw [hLen]
          simp only [part, List.map_map, Function.comp_def]
          apply List.map_congr_left
          intro p _
          rw [hLetter]
          cases ρ.letterAt p with
          | child => by_cases hp : p ∈ keep <;> simp [hp, letter]
          | ext j w =>
            by_cases hj : j ≤ L
            · simp [letter, hj]
            · simp [letter, hj, show j - 1 + 1 = j by omega]
        have e1 : (m :: ρ.maxima).take (L + 1 - 1) = m :: ρ.maxima.take (L - 1) := by
          rw [show L + 1 - 1 = (L - 1) + 1 by omega, List.take_succ_cons]
        have e2 : (m :: ρ.maxima).drop (L + 1 + 1) = ρ.maxima.drop (L + 1) := by
          rw [List.drop_succ_cons]
        have e3 : (ρ.part keep v m).maximumAt (L + 1) = ρ.maximumAt L := by
          simp only [maximumAt, part_maxima]
          rw [show L + 1 - 1 = (L - 1) + 1 by omega, List.getElem?_cons_succ]
        have e4 : (ρ.part keep v m).maximumAt (L + 1 + 1) = ρ.maximumAt (L + 1) := by
          simp only [maximumAt, part_maxima]
          rw [show L + 1 + 1 - 1 = (L + 1 - 1) + 1 by omega, List.getElem?_cons_succ]
        have hmx : (norm (ρ.part keep v m) (L + 1)).maxima = ((norm ρ L).part keep v m).maxima := by
          show (m :: ρ.maxima).take (L + 1 - 1) ++
              [max ((ρ.part keep v m).maximumAt (L + 1)) ((ρ.part keep v m).maximumAt (L + 1 + 1) + 1)] ++
              (m :: ρ.maxima).drop (L + 1 + 1) =
            m :: (ρ.maxima.take (L - 1) ++ [max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)] ++ ρ.maxima.drop (L + 1))
          rw [e1, e2, e3, e4]
          rfl
        have ha : (norm (ρ.part keep v m) (L+1)).a = ((norm ρ L).part keep v m).a := rfl
        have hu : (norm (ρ.part keep v m) (L+1)).u = ((norm ρ L).part keep v m).u := rfl
        exact ctx_ext ha hu rfl hw hmx
      have hInvPart (ρ : Context) (L : ℕ) (hL : Inv ρ L) (keep : List ℕ) (v : Side) (m : ℕ) :
          Inv (ρ.part keep v m) (L + 1) := by
        obtain ⟨h1, h2, h3, h4⟩ := hL
        refine ⟨by omega, by simp only [part_maxima, List.length_cons]; omega, ?_, ?_⟩
        · intro p j w hp hj
          rw [part_sideAt_succ ρ keep v m h1]
          by_cases hplen : p < ρ.word.length
          · cases hlet : ρ.letterAt p with
            | child =>
              rw [part_letterAt_of_child ρ keep v m hplen hlet] at hp
              by_cases hk : p ∈ keep
              · simp [hk] at hp
              · simp only [hk, if_false, Letter.ext.injEq] at hp
                obtain ⟨hj1, -⟩ := hp
                omega
            | ext i u =>
              rw [part_letterAt_of_ext ρ keep v m hplen hlet, Letter.ext.injEq] at hp
              obtain ⟨rfl, rfl⟩ := hp
              exact h3 p i u hlet (by omega)
          · rw [letterAt_of_length_le _ (by rw [part_word_length]; omega)] at hp
            cases hp
        · rw [part_sideAt_succ ρ keep v m h1, part_sideAt_succ ρ keep v m (by omega : 1 ≤ L + 1)]
          exact h4
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
      have hNextBoundary (ρ : Context)
          (hPos : ∀ p j w, ρ.letterAt p = Letter.ext j w → 1 ≤ j)
          (L x : ℕ) (hL : L ∈ ρ.levels) (dir : Bool)
          (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
          (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
            if dir then p < x else x < p)
          (keep : List ℕ) (v : Side) (m : ℕ) :
          (∀ p ∈ (ρ.part keep v m).childPositions, if dir then p < x else x < p) ∧
          (∀ j ∈ (ρ.part keep v m).levelsOn ((ρ.part keep v m).sideAt (L+1)) (L+1),
            ∀ p ∈ (ρ.part keep v m).extPositions j, if dir then p < x else x < p) := by
        have hL1 := one_le_of_mem_levels hL
        constructor
        · intro p hp
          rw [part_childPositions] at hp
          exact hc p (List.mem_filter.mp hp).1
        · intro j hj p hp
          have hj1 := (one_le_of_mem_levelsOn hj).1
          by_cases he : j = 1
          · subst j
            rw [part_extPositions_one hPos keep v m] at hp
            exact hc p (List.mem_filter.mp hp).1
          · let i := j-1
            have hi : 1 ≤ i := by dsimp [i]; omega
            have he : j = i+1 := by dsimp [i]; omega
            rw [he] at hj hp
            have hjLevel : i+1 ∈ (ρ.part keep v m).levels := (List.mem_filter.mp hj).1
            rw [part_levels] at hjLevel
            have hiLevel : i ∈ ρ.levels := by
              rcases List.mem_cons.mp hjLevel with h | h
              · omega
              · obtain ⟨z, hz, hzi⟩ := List.mem_map.mp h
                have hz' : z = i := by omega
                simpa only [hz'] using hz
            have hjc : (ρ.part keep v m).sideAt (i+1) = (ρ.part keep v m).sideAt (L+1) ∧
                (L+1 = 0 ∨ i+1 < L+1) := of_decide_eq_true (List.mem_filter.mp hj).2
            rw [part_sideAt_succ ρ keep v m hi, part_sideAt_succ ρ keep v m hL1] at hjc
            have hiOn : i ∈ ρ.levelsOn (ρ.sideAt L) L := by
              apply List.mem_filter.mpr
              refine ⟨hiLevel, ?_⟩
              apply decide_eq_true
              exact ⟨hjc.1, Or.inr (by omega)⟩
            rw [part_extPositions_succ ρ keep v m hi] at hp
            exact hy i hiOn p hp
      have hNextTerminal (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (keep : List ℕ) (v : Side) (m : ℕ) :
          ∀ j ∈ (ρ.part keep v m).levelsOn ((ρ.part keep v m).sideAt (L+1)) 0, j ≤ L+1+1 := by
        intro j hj
        have hj1 := (one_le_of_mem_levelsOn hj).1
        have hL1 := one_le_of_mem_levels hL
        by_cases he : j = 1
        · omega
        · let i := j-1
          have hi : 1 ≤ i := by dsimp [i]; omega
          have he : j = i+1 := by dsimp [i]; omega
          rw [he] at hj ⊢
          have hjLevel : i+1 ∈ (ρ.part keep v m).levels := (List.mem_filter.mp hj).1
          rw [part_levels] at hjLevel
          have hiLevel : i ∈ ρ.levels := by
            rcases List.mem_cons.mp hjLevel with h | h
            · omega
            · obtain ⟨z, hz, hzi⟩ := List.mem_map.mp h
              have hz' : z = i := by omega
              simpa only [hz'] using hz
          have hjc : (ρ.part keep v m).sideAt (i+1) = (ρ.part keep v m).sideAt (L+1) ∧
              (0 = 0 ∨ i+1 < 0) := of_decide_eq_true (List.mem_filter.mp hj).2
          rw [part_sideAt_succ ρ keep v m hi, part_sideAt_succ ρ keep v m hL1] at hjc
          have hiOn : i ∈ ρ.levelsOn (ρ.sideAt L) 0 :=
            List.mem_filter.mpr ⟨hiLevel, by simp [hjc.1]⟩
          have := ht i hiOn
          omega
      have hBase (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
          (hsingle : ρ.extPositions L = [x])
          (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
          (hc : ∀ p ∈ ρ.childPositions, x < p)
          (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
          (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
          (hG : (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k) :
          ρ.base = (norm ρ L).base := by
        rw [base_eq_baseOf, base_eq_baseOf, hChild]
        cases hh : ρ.childPositions.head? with
        | none => rfl
        | some p =>
          have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
          have h := hCaps ρ L x hL hsingle hafter hc hy ht hG p p hp hp
          simp only [baseOf, h.1, h.2, hK]
      have hFuel : ∀ fuel (ρ : Context),
          (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
          ∀ (L x : ℕ), Inv ρ L → ρ.extPositions L = [x] →
          (∀ y ∈ ρ.extPositions (L + 1), x < y) →
          (∀ p ∈ ρ.childPositions, x < p) →
          (∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p) →
          (∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) →
          (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k →
          boundFuel fuel ρ = boundFuel fuel (norm ρ L) := by
        intro fuel
        induction fuel with
        | zero => intro ρ hPos L x hL hsingle hafter hc hy ht hG; rfl
        | succ fuel ih =>
          intro ρ hPos L x hL hsingle hafter hc hy ht hG
          have hL1 := hL.1
          have hLn : L ∈ ρ.levels :=
            (hLevelMem ρ L).mpr ⟨hL1, by have := hL.2.1; omega⟩
          have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
              boundFuel fuel (ρ.part keep v m) =
                boundFuel fuel ((norm ρ L).part keep v m) := by
            have hs' : (ρ.part keep v m).extPositions (L + 1) = [x] := by
              rw [part_extPositions_succ ρ keep v m hL1, hsingle]
            have hb' : ∀ y ∈ (ρ.part keep v m).extPositions (L + 1 + 1), x < y := by
              rw [part_extPositions_succ ρ keep v m (by omega : 1 ≤ L + 1)]
              exact hafter
            have hd := hNextBoundary ρ hPos L x hLn false hc hy keep v m
            have hg' : (match (ρ.part keep v m).sideAt (L + 1) with
                | Side.lower => (ρ.part keep v m).u
                | Side.upper => (ρ.part keep v m).a) ≤ (ρ.part keep v m).k := by
              rw [part_sideAt_succ ρ keep v m hL1]
              exact hG
            have h := ih (ρ.part keep v m) (hPartPositive ρ keep v m)
              (L + 1) x (hInvPart ρ L hL keep v m) hs' hb' hd.1 hd.2
              (hNextTerminal ρ L hLn ht keep v m) hg'
            rw [hNormPart ρ keep v m L hL1] at h
            exact h
          simp only [boundFuel, hRuns, hChild, hBlocks, hK]
          split_ifs
          · exact hBase ρ L x hL hsingle hafter hc hy ht hG
          · congr 1
            apply congrArg List.max?
            apply List.flatMap_congr
            intro keep _
            apply List.flatMap_congr
            intro m _
            simp only [hParts]
      refine ⟨fun p hp q hq =>
        hCaps σ N x hpair hsole hafter hchildren hyounger holdest hglobal p q hp hq,
        fun fuel => hFuel fuel σ hpositive N x hpair hsole hafter hchildren hyounger holdest hglobal,
        ?_⟩
      simpa only [bound, hChild] using
        hFuel (σ.childPositions.length + 1) σ hpositive N x hpair hsole hafter
          hchildren hyounger holdest hglobal

    have hChildZero (ρ : Context) (hf : ρ.word.head? = some Letter.child) :
        0 < ρ.word.length ∧ ρ.letterAt 0 = Letter.child ∧ 0 ∈ ρ.childPositions := by
      have hlen : 0 < ρ.word.length := by
        obtain ⟨ws,hws⟩ := List.head?_eq_some_iff.mp hf
        simp [hws]
      have hz : ρ.letterAt 0 = Letter.child := by
        unfold letterAt
        rw [← List.head?_eq_getElem?,hf]
        rfl
      exact ⟨hlen,hz,by simp [childPositions,hlen,hz]⟩
    have hFirstIsZero (ρ : Context) (hf : ρ.word.head? = some Letter.child)
        (p : ℕ) (ps : List ℕ) (hcp : ρ.childPositions = p :: ps) : p = 0 := by
      have hz := (hChildZero ρ hf).2.2
      rw [hcp] at hz
      rcases List.mem_cons.mp hz with h | h
      · exact h.symm
      · have hh := hFirstTail ρ p ps hcp 0 h
        omega
    have hOldAfterZero (ρ : Context) (hf : ρ.word.head? = some Letter.child) :
        ∀ y ∈ ρ.extPositions 1, 0 < y := by
      intro y hy
      have hz := (hChildZero ρ hf).2.1
      by_contra hn
      have hy0 : y = 0 := by omega
      subst y
      simp [extPositions,hz] at hy
    let mergePrefix (ρ : Context) : Context :=
      { ρ with
        word := ρ.word.map mergeLetter
        maxima := [max (ρ.maximumAt 1) (ρ.maximumAt 2+1)] ++ ρ.maxima.drop 2 }
    have hMergePrefixLength (ρ : Context) :
        (mergePrefix ρ).word.length = ρ.word.length := by simp [mergePrefix]
    have hMergePrefixLetter (ρ : Context) (x : ℕ) :
        (mergePrefix ρ).letterAt x = mergeLetter (ρ.letterAt x) := by
      simp only [mergePrefix,letterAt,List.getElem?_map]
      cases ρ.word[x]? <;> rfl

    have hRootWF (M : ℕ) (hM : 1 ≤ M) (hMk : M ≤ k-2)
        (a u : ℕ) (ha2 : 2 ≤ a) (hu2 : 2 ≤ u)
        (hak : a ≤ k) (huk : u ≤ k) (v : Side) (w : List Letter)
        (hw : ∀ x ∈ w, x = Letter.child ∨ x = Letter.ext 1 v) :
        ({a := a, u := u, k := k, word := w, maxima := [M]} : Context).WellFormed := by
      let τ : Context := {a := a, u := u, k := k, word := w, maxima := [M]}
      have hshape : ∀ p l t, τ.letterAt p = Letter.ext l t → l = 1 ∧ t = v := by
        intro p l t hext
        have hp : p < τ.word.length := by
          by_contra hn
          have h := letterAt_of_length_le τ (Nat.le_of_not_gt hn)
          rw [h] at hext
          cases hext
        have hmem : Letter.ext l t ∈ w := by
          have hget : τ.word[p] = Letter.ext l t := by
            simpa [letterAt, hp] using hext
          rw [← hget]
          exact List.getElem_mem _
        rcases hw _ hmem with h | h
        · cases h
        · cases h
          exact ⟨rfl, rfl⟩
      refine ⟨ha2, hu2, hak, huk, ?_, ?_⟩
      · intro n hn
        simp only [List.mem_singleton] at hn
        subst n
        exact ⟨hM, hMk⟩
      · intro p l t hext
        change τ.letterAt p = Letter.ext l t at hext
        obtain ⟨rfl, rfl⟩ := hshape p l t hext
        refine ⟨by omega, by simp, ?_⟩
        have hpExt : p ∈ τ.extPositions 1 := by
          have hp : p < τ.word.length := by
            by_contra hn
            have h := letterAt_of_length_le τ (Nat.le_of_not_gt hn)
            rw [h] at hext
            cases hext
          simp [extPositions, hp, hext]
        cases hh : (τ.extPositions 1).head? with
        | none =>
          have hn := List.head?_eq_none_iff.mp hh
          rw [hn] at hpExt
          simp at hpExt
        | some q =>
          have hq := List.mem_of_mem_head? hh
          have hqe := (List.mem_filter.mp hq).2
          cases hl : τ.letterAt q with
          | child => simp [hl] at hqe
          | ext j v =>
            obtain ⟨rfl, rfl⟩ := hshape q j v hl
            change v = τ.sideAt 1
            simp [sideAt, hh, hl]

    have hMarkerExists (ρ : Context) (v : Side)
        (hmark : Letter.ext 1 v ∈ ρ.word) : ∃ x, x ∈ ρ.extPositions 1 := by
      obtain ⟨x,hx⟩ := List.mem_iff_getElem?.mp hmark
      have hxl : x < ρ.word.length := (List.getElem?_eq_some_iff.mp hx).1
      have hletter : ρ.letterAt x = Letter.ext 1 v := by simp [letterAt,hx]
      exact ⟨x,by simp [extPositions,hxl,hletter]⟩
    have hAnyExposedPoint (B H K M : ℕ) (hB : 3 ≤ B) (hBK : B ≤ K)
        (hH : 3 ≤ H) (hHK : H ≤ K) (hM : 1 ≤ M) (hMK : M ≤ K-2)
        (v : Side) (w : List Letter)
        (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
        (hf : w.head? = some Letter.child)
        (hmark : Letter.ext 1 v ∈ w) :
        ownLimit (mkRoot B H K M v w) v 0 0 = min (H-1) (K-M)-1 ∧
        otherLimit (mkRoot B H K M v w) v 0 0 = B-1 := by
      let ρ := mkRoot B H K M v w
      obtain ⟨y,hy⟩ := hMarkerExists ρ v hmark
      have hypos := hOldAfterZero ρ hf y hy
      have hs := hSideOne ρ v hw ⟨y,hy⟩
      have hls := hRootLevels ρ v M rfl hs
      have hleft := hSingleLeftZero ρ v 1 0 hls (fun x _ => by omega)
      have hright := hSingleRight ρ v 1 0 hls
        ⟨y,hy,hypos⟩
      have hOwnC : ρ.chainExt v 0 0 = 1 := by simp [chainExt,hleft,hright]
      have hOwnJ : ρ.joinExt v 0 0 = M := by
        rw [hSingleJoin ρ v 1 0 0 (by omega) hls,hOwnC]
        simp [maximumAt,ρ,mkRoot,show 1 ≤ M from hM]
      have hOtherLs := hOtherLevels ρ v (opp v) M rfl hs
        (by cases v <;> simp [opp])
      have hOC := hEmptyAxis ρ (opp v) 0 0 hOtherLs
      cases v with
      | lower =>
        change
          min (H-1-ρ.chainExt Side.lower 0 0) (K-1-ρ.joinExt Side.lower 0 0) =
            min (H-1) (K-M)-1 ∧
          min (B-1-ρ.chainExt Side.upper 0 0) (K-1-ρ.joinExt Side.upper 0 0) = B-1
        rw [hOwnC,hOwnJ,hOC.1,hOC.2]
        constructor <;> omega
      | upper =>
        change
          min (H-1-ρ.chainExt Side.upper 0 0) (K-1-ρ.joinExt Side.upper 0 0) =
            min (H-1) (K-M)-1 ∧
          min (B-1-ρ.chainExt Side.lower 0 0) (K-1-ρ.joinExt Side.lower 0 0) = B-1
        rw [hOwnC,hOwnJ,hOC.1,hOC.2]
        constructor <;> omega
    have hLeafAnyExposed (B H K M : ℕ) (hB : 3 ≤ B) (hBK : B ≤ K)
        (hH : 3 ≤ H) (hHK : H ≤ K) (hM : 1 ≤ M) (hMK : M ≤ K-2)
        (v : Side) (w : List Letter)
        (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
        (hf : w.head? = some Letter.child)
        (hmark : Letter.ext 1 v ∈ w)
        (p : ℕ) (ps : List ℕ)
        (hcp : (mkRoot B H K M v w).childPositions = p :: ps) (hne : ps ≠ []) :
        ((mkRoot B H K M v w).part [p] (opp v) (K-B+1)).bound =
          decomposableThreshold (B-1) (min (H-1) (K-M)) K := by
      let ρ := mkRoot B H K M v w
      let c := K-B+1
      let V := min (H-1) (K-M)
      let leaf := ρ.part [p] (opp v) c
      have hcp : ρ.childPositions = p :: ps := hcp
      have hpzero := hFirstIsZero ρ hf p ps hcp
      have hp : p ∈ ρ.childPositions := by simp [hcp]
      have hlt := hFirstTail ρ p ps hcp
      obtain ⟨q,hq⟩ := List.exists_mem_of_ne_nil ps hne
      have hqρ : q ∈ ρ.childPositions := by simp [hcp,hq]
      have hqp : p < q := hlt q hq
      have hpos := hRootPositive ρ v hw
      have hExt : leaf.extPositions 1 = ρ.childPositions.filter (· ∉ [p]) :=
        part_extPositions_one hpos [p] (opp v) c
      have hFresh : q ∈ leaf.extPositions 1 := by
        rw [hExt]
        simp [hqρ,show q ≠ p by omega]
      have hSide : leaf.sideAt 1 = opp v :=
        part_sideAt_one_of_mem hpos [p] (opp v) c hFresh
      obtain ⟨y,hy⟩ := hMarkerExists ρ v hmark
      have hOldSide := hSideOne ρ v hw ⟨y,hy⟩
      have hOldOther := hOtherLevels ρ v (opp v) M rfl hOldSide
        (by cases v <;> simp [opp])
      have hLevels : leaf.levelsOn (opp v) 0 = [1] := by
        rw [part_levelsOn_self_zero hSide,hOldOther]
        rfl
      have hNoLeft : ∀ x ∈ leaf.extPositions 1, ¬ x < p := by
        intro x hx
        rw [hExt] at hx
        have hxρ := (List.mem_filter.mp hx).1
        have hxn : x ≠ p := by simpa using (List.mem_filter.mp hx).2
        rw [hcp] at hxρ
        rcases List.mem_cons.mp hxρ with he | ht
        · exact False.elim (hxn he)
        · have hpx := hlt x ht
          omega
      have hLeft := hSingleLeftZero leaf (opp v) 1 p hLevels hNoLeft
      have hRight := hSingleRight leaf (opp v) 1 p hLevels ⟨q,hFresh,hqp⟩
      have hOC : leaf.chainExt (opp v) p p = 1 := by
        simp [chainExt,hLeft,hRight]
      have hNewMax : leaf.maximumAt 1 = c := by simp [maximumAt,leaf,part]
      have hc1 : 1 ≤ c := by dsimp [c]; omega
      have hOJ : leaf.joinExt (opp v) p p = c := by
        rw [hSingleJoin leaf (opp v) 1 p p (by omega) hLevels,hOC,hNewMax]
        omega
      have hSideNe : leaf.sideAt 1 ≠ v := by
        rw [hSide]
        cases v <;> simp [opp]
      have hOwnC := chainExt_part_other (σ := ρ) (keep := [p])
        (s := opp v) (m := c) hSideNe p p
      have hOwnJ := joinExt_part_other (σ := ρ) (keep := [p])
        (s := opp v) (m := c) hSideNe p p
      have hRP : ownLimit ρ v p p = V-1 ∧ otherLimit ρ v p p = B-1 := by
        simpa only [hpzero] using hAnyExposedPoint B H K M hB hBK hH hHK hM hMK v w hw hf hmark
      have hOwn : ownLimit leaf v p p = V-1 := by
        cases v with
        | lower =>
          dsimp only [ownLimit] at hRP ⊢
          change min (H-1-leaf.chainExt Side.lower p p)
            (K-1-leaf.joinExt Side.lower p p) = V-1
          rw [hOwnC,hOwnJ]
          exact hRP.1
        | upper =>
          dsimp only [ownLimit] at hRP ⊢
          change min (H-1-leaf.chainExt Side.upper p p)
            (K-1-leaf.joinExt Side.upper p p) = V-1
          rw [hOwnC,hOwnJ]
          exact hRP.1
      have hOther : otherLimit leaf v p p = B-2 := by
        cases v with
        | lower =>
          change min (B-1-leaf.chainExt Side.upper p p)
            (K-1-leaf.joinExt Side.upper p p) = B-2
          change leaf.chainExt Side.upper p p = 1 at hOC
          change leaf.joinExt Side.upper p p = c at hOJ
          rw [hOC,hOJ]
          dsimp [c]
          omega
        | upper =>
          change min (B-1-leaf.chainExt Side.lower p p)
            (K-1-leaf.joinExt Side.lower p p) = B-2
          change leaf.chainExt Side.lower p p = 1 at hOC
          change leaf.joinExt Side.lower p p = c at hOJ
          rw [hOC,hOJ]
          dsimp [c]
          omega
      change leaf.bound = decomposableThreshold (B-1) V K
      rw [ctx_singleton_part_bound_eq_threshold ρ p hp (opp v) c]
      have hV2 : 2 ≤ V := by dsimp [V]; omega
      have hVk : V ≤ K := by dsimp [V]; omega
      have hbe : B-2+1 = B-1 := by omega
      have hve : V-1+1 = V := by omega
      cases v with
      | lower =>
        dsimp only [ownLimit,otherLimit] at hOwn hOther
        rw [hOwn,hOther,hbe,hve]
      | upper =>
        dsimp only [ownLimit,otherLimit] at hOwn hOther
        rw [hOwn,hOther,hbe,hve]
        simpa only [ρ,mkRoot] using
          hThresholdComm (a := V) (u := B-1) (k := K) hV2 (by omega) hVk (by omega)
    have hComplementNeither (B H K M : ℕ) (hHk : H ≤ K)
        (v : Side) (w : List Letter)
        (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
        (hf : w.head? = some Letter.child)
        (hl : w.getLast? = some Letter.child)
        (hmark : Letter.ext 1 v ∈ w)
        (p : ℕ) (ps : List ℕ)
        (hcp : (mkRoot B H K M v w).childPositions = p :: ps) (hne : ps ≠ []) :
        ∃ w' : List Letter,
          (∀ z ∈ w', z = Letter.child ∨ z = Letter.ext 1 v) ∧
          w'.head? = some (Letter.ext 1 v) ∧
          w'.getLast? = some Letter.child ∧
          Letter.child ∈ w' ∧
          ((mkRoot B H K M v w).part ps v (B-2)).bound =
            (mkRoot B H K (max (B-2) (M+1)) v w').bound := by
      let ρ := mkRoot B H K M v w
      let δ := ρ.part ps v (B-2)
      let τ := mergePrefix δ
      have hcp : ρ.childPositions = p :: ps := hcp
      have hpzero := hFirstIsZero ρ hf p ps hcp
      have hlt := hFirstTail ρ p ps hcp
      have hnot : p ∉ ps := by
        intro hp
        have h := hlt p hp
        omega
      have hpos := hRootPositive ρ v hw
      have hShapeδ := hPartShape ρ v hw ps v (B-2)
      have hδpos : ∀ x j t, δ.letterAt x = Letter.ext j t → 1 ≤ j := by
        intro x j t hx
        rcases hShapeδ x j t hx with h | h <;> omega
      have hsole : δ.extPositions 1 = [p] := by
        rw [part_extPositions_one hpos,hcp]
        simp [hnot]
      have hside : δ.sideAt 1 = v :=
        part_sideAt_one_of_mem hpos ps v (B-2) (q := p) (by rw [hsole]; simp)
      obtain ⟨y,hy⟩ := hMarkerExists ρ v hmark
      have hsideρ := hSideOne ρ v hw ⟨y,hy⟩
      have hside2 : δ.sideAt 2 = v := by
        rw [part_sideAt_succ ρ ps v (B-2) (by omega : 1 ≤ 1),hsideρ]
      have hInv : Inv δ 1 := by
        refine ⟨by omega,?_,?_,?_⟩
        · simp [δ,part,ρ,mkRoot]
        · intro x j t hx _
          rcases hShapeδ x j t hx with h | h <;> simpa [hside] using h.2
        · rw [hside,hside2]
      have hafter : ∀ y ∈ δ.extPositions 2, p < y := by
        intro y hy
        rw [part_extPositions_succ ρ ps v (B-2) (by omega : 1 ≤ 1)] at hy
        have hh := hOldAfterZero ρ hf y hy
        omega
      have hchildren : ∀ q ∈ δ.childPositions, p < q := by
        intro q hq
        rw [part_childPositions] at hq
        have hqps : q ∈ ps := of_decide_eq_true (List.mem_filter.mp hq).2
        exact hlt q hqps
      have hyounger : ∀ j ∈ δ.levelsOn (δ.sideAt 1) 1,
          ∀ q ∈ δ.extPositions j, p < q := by
        simp [levelsOn_one]
      have holdest : ∀ j ∈ δ.levelsOn (δ.sideAt 1) 0, j ≤ 2 := by
        intro j hj
        have hj' : j ∈ δ.levels := (List.mem_filter.mp hj).1
        simp [levels,δ,part,ρ,mkRoot] at hj'
        omega
      have hglobal :
          (match δ.sideAt 1 with | Side.lower => δ.u | Side.upper => δ.a) ≤ δ.k := by
        rw [hside]
        cases v <;> simpa [δ,part,ρ,mkRoot] using hHk
      have hEq := (hPrefixMerge δ hδpos 1 p hInv hsole hafter hchildren hyounger holdest hglobal).2.2
      change δ.bound = τ.bound at hEq
      have hFields : τ = mkRoot B H K (max (B-2) (M+1)) v τ.word := by
        apply MergeLevels.ctx_ext
        · rfl
        · rfl
        · rfl
        · rfl
        · simp [τ,mergePrefix,maximumAt,δ,part,ρ,mkRoot]
      have hUniform : ∀ z ∈ τ.word, z = Letter.child ∨ z = Letter.ext 1 v := by
        intro z hz
        obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hz
        obtain ⟨x,hx⟩ := List.mem_iff_getElem?.mp hold
        have hOld : δ.letterAt x = old := by simp [letterAt,hx]
        cases old with
        | child => exact Or.inl rfl
        | ext j t =>
          rcases hShapeδ x j t hOld with h | h
          · obtain ⟨rfl,rfl⟩ := h
            exact Or.inr rfl
          · obtain ⟨rfl,rfl⟩ := h
            exact Or.inr rfl
      have hlen : 1 ≤ ρ.word.length := by
        have hh := (hChildZero ρ hf).1
        omega
      have hδzero : δ.letterAt 0 = Letter.ext 1 v := by
        have hnot0 : 0 ∉ ps := by simpa only [hpzero] using hnot
        rw [part_letterAt_of_child ρ ps v (B-2)
          (hChildZero ρ hf).1 (hChildZero ρ hf).2.1,if_neg hnot0]

      obtain ⟨q0,hq0⟩ := List.exists_mem_of_ne_nil ps hne
      have hq0ρ : q0 ∈ ρ.childPositions := by simp [hcp,hq0]
      have hq0len := (hChildMem ρ q0 hq0ρ).1
      have hpq0 := hlt q0 hq0
      have hlen2 : 2 ≤ ρ.word.length := by omega
      have hOriginalLast : ρ.letterAt (ρ.word.length-1) = Letter.child := by
        unfold letterAt
        rw [← List.getLast?_eq_getElem?,hl]
        rfl
      have hLastMem : ρ.word.length-1 ∈ ρ.childPositions := by
        simp [childPositions,show ρ.word.length-1 < ρ.word.length by omega,hOriginalLast]
      have hLastPS : ρ.word.length-1 ∈ ps := by
        rw [hcp] at hLastMem
        rcases List.mem_cons.mp hLastMem with he | ht
        · omega
        · exact ht
      have hδlast : δ.letterAt (δ.word.length-1) = Letter.child := by
        rw [part_word_length]
        rw [part_letterAt_of_child ρ ps v (B-2)
          (by omega) hOriginalLast,if_pos hLastPS]
      have hτzero : τ.letterAt 0 = Letter.ext 1 v := by
        rw [hMergePrefixLetter,hδzero]
        rfl
      have hτlast : τ.letterAt (τ.word.length-1) = Letter.child := by
        rw [hMergePrefixLength,hMergePrefixLetter,hδlast]
      have hτlen : 1 ≤ τ.word.length := by
        rw [hMergePrefixLength,part_word_length]
        exact hlen
      have hFirst : τ.word.head? = some (Letter.ext 1 v) := by
        rw [List.head?_eq_getElem?]
        apply List.getElem?_eq_some_iff.mpr
        refine ⟨by omega,?_⟩
        simpa [letterAt,show 0 < τ.word.length by omega] using hτzero
      have hLast : τ.word.getLast? = some Letter.child := by
        rw [List.getLast?_eq_getElem?]
        apply List.getElem?_eq_some_iff.mpr
        refine ⟨by omega,?_⟩
        simpa [letterAt,show τ.word.length-1 < τ.word.length by omega] using hτlast
      obtain ⟨q,hq⟩ := List.exists_mem_of_ne_nil ps hne
      have hqρ : q ∈ ρ.childPositions := by simp [hcp,hq]
      have hqmem := hChildMem ρ q hqρ
      have hδq : δ.letterAt q = Letter.child := by
        rw [part_letterAt_of_child ρ ps v (B-2) hqmem.1 hqmem.2,if_pos hq]
      have hτq : τ.letterAt q = Letter.child := by
        rw [hMergePrefixLetter,hδq]
      have hqlen : q < τ.word.length := by
        rw [hMergePrefixLength,part_word_length]
        exact hqmem.1
      have hChild : Letter.child ∈ τ.word := by
        have hget : τ.word[q] = Letter.child := by simpa [letterAt,hqlen] using hτq
        rw [← hget]
        exact List.getElem_mem _
      exact ⟨τ.word,hUniform,hFirst,hLast,hChild,hEq.trans (congrArg Context.bound hFields)⟩

    have hThree (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s : Ctx.Side) (N x : ℕ) (hN : N ∈ σ.levels) (hs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 3) : (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ ≤ 2) ∧ σ.bound ≤ 2 ∧ (∀ M y : ℕ, M ∈ σ.levels → N ≠ M → σ.sideAt M = s → y ∈ σ.extPositions M → (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ ≤ 1) ∧ σ.bound ≤ 1) := by
      classical
      let marks : Finset ℕ := (σ.levelsOn s 0).toFinset.biUnion
        (fun j => (σ.extPositions j).toFinset)
      let active : Finset ℕ := σ.childPositions.toFinset.filter
        (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
      let label (p : ℕ) := (marks.filter (· < p)).card
      let regions := (active.image label).card
      have hMark (z : ℕ) :
          z ∈ marks ↔ ∃ j ∈ σ.levelsOn s 0, z ∈ σ.extPositions j := by
        simp [marks]
      have hActive (p : ℕ) : p ∈ active ↔
          p ∈ σ.childPositions ∧ 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p := by
        simp [active]
      have hNoMark (p : ℕ) (hp : p ∈ σ.childPositions) : p ∉ marks := by
        intro hz
        obtain ⟨j,_,hj⟩ := (hMark p).mp hz
        have hc := (List.mem_filter.mp hp).2
        have he := (List.mem_filter.mp hj).2
        simp only [decide_eq_true_eq] at hc he
        simp [hc] at he
      have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
          (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
          1 ≤ ρ.leftExt v 0 p := by
        have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq,hqp]
        have hnonempty := List.ne_nil_of_mem hm
        have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
          (fun ls => (ls.foldl (leftStep ρ) (p,0)).2))
          (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
        change _ ≤ ρ.leftExt v 0 p at hv
        simpa only [List.foldl_cons,List.foldl_nil,leftStep,
          List.getLast?_eq_some_getLast hnonempty] using hv
      have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
          (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
          1 ≤ ρ.rightExt v 0 p := by
        have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq,hpq]
        have hnonempty := List.ne_nil_of_mem hm
        have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
          (fun ls => (ls.foldl (rightStep ρ) (p,0)).2))
          (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
        change _ ≤ ρ.rightExt v 0 p at hv
        simpa only [List.foldl_cons,List.foldl_nil,rightStep,
          List.head?_eq_some_head hnonempty] using hv
      have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN,by simp [hs]⟩
      have hxMark : x ∈ marks := (hMark x).mpr ⟨N,hNOn,hx⟩
      have hChain (p : ℕ) (hp : p ∈ σ.childPositions) : 1 ≤ σ.chainExt s p p := by
        have hpx : p ≠ x := by
          intro he
          subst x
          exact hNoMark p hp hxMark
        by_cases h : x < p
        · have hL := hOneLeft σ s N p x hNOn hx h
          unfold chainExt
          omega
        · have hR := hOneRight σ s N p x hNOn hx (by omega)
          unfold chainExt
          omega
      have hUnit : ∀ p ∈ σ.childPositions,
          (match s with | Side.lower => σ.cupLimit p p | Side.upper => σ.capLimit p p) ≤ 1 := by
        intro p hp
        have hc := hChain p hp
        cases s with
        | lower =>
          dsimp only at hglobal ⊢
          simp only [cupLimit]
          omega
        | upper =>
          dsimp only at hglobal ⊢
          simp only [capLimit]
          omega
      have hChainActive (p : ℕ) (hp : p ∈ active) : σ.chainExt s p p ≤ 1 := by
        obtain ⟨_,hcup,hcap⟩ := (hActive p).mp hp
        cases s with
        | lower =>
          dsimp only at hglobal
          simp only [cupLimit] at hcup
          omega
        | upper =>
          dsimp only at hglobal
          simp only [capLimit] at hcap
          omega
      have hLabelLeft (p : ℕ) (hAll : ∀ z ∈ marks, z < p) : label p = marks.card := by
        change (marks.filter (· < p)).card = marks.card
        exact congrArg Finset.card (Finset.filter_eq_self.mpr hAll)
      have hLabelRight (p : ℕ) (hAll : ∀ z ∈ marks, p < z) : label p = 0 := by
        have he : marks.filter (· < p) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro z hz
          have hh := hAll z hz
          omega
        simp only [label,he,Finset.card_empty]
      have hLabelCases (p : ℕ) (hp : p ∈ active) : label p = 0 ∨ label p = marks.card := by
        have hpc := ((hActive p).mp hp).1
        by_cases hleft : ∃ z ∈ marks, z < p
        · right
          apply hLabelLeft
          obtain ⟨z,hz,hzp⟩ := hleft
          obtain ⟨j,hj,hzj⟩ := (hMark z).mp hz
          have hL := hOneLeft σ s j p z hj hzj hzp
          intro q hq
          by_contra hqp
          have hpq : p ≠ q := by
            intro he
            subst q
            exact hNoMark p hpc hq
          have hpq' : p < q := by omega
          obtain ⟨l,hl,hql⟩ := (hMark q).mp hq
          have hR := hOneRight σ s l p q hl hql hpq'
          have hc := hChainActive p hp
          unfold chainExt at hc
          omega
        · left
          apply hLabelRight
          intro z hz
          have hzp : ¬ z < p := by
            intro he
            exact hleft ⟨z,hz,he⟩
          have hpz : p ≠ z := by
            intro he
            subst z
            exact hNoMark p hpc hz
          omega
      have hRegionsTwo : regions ≤ 2 := by
        have hsub : active.image label ⊆ ({0,marks.card} : Finset ℕ) := by
          intro z hz
          obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
          simpa only [Finset.mem_insert,Finset.mem_singleton] using hLabelCases p hp
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
      have hPotential := ctx_unit_axis_active_region_potential σ hpositive s hUnit
      change (∀ fuel, boundFuel fuel σ ≤ regions) ∧
        σ.bound ≤ regions ∧ regions ≤ σ.numRuns at hPotential
      have hUniform (r : ℕ) (hlabels : ∀ p ∈ active, label p = r) : regions ≤ 1 := by
        have hsub : active.image label ⊆ ({r} : Finset ℕ) := by
          intro z hz
          obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
          simpa only [Finset.mem_singleton] using hlabels p hp
        simpa only [Finset.card_singleton] using Finset.card_le_card hsub
      have hTwo (J L v w : ℕ) (hJ : J ∈ σ.levels) (hL : L ∈ σ.levels) (hJL : J < L)
          (hJs : σ.sideAt J = s) (hLs : σ.sideAt L = s)
          (hv : v ∈ σ.extPositions J) (hw : w ∈ σ.extPositions L) : regions ≤ 1 := by
        rcases ctx_chain_one_children_exterior_of_two_levels σ s J L v w
          hJ hL hJL hJs hLs hv hw with hl | hr
        · apply hUniform marks.card
          intro p hp
          apply hLabelLeft
          intro z hz
          obtain ⟨j,hj,hzj⟩ := (hMark z).mp hz
          exact hl.2 p ((hActive p).mp hp).1 (hChainActive p hp) j hj z hzj
        · apply hUniform 0
          intro p hp
          apply hLabelRight
          intro z hz
          obtain ⟨j,hj,hzj⟩ := (hMark z).mp hz
          exact hr.2 p ((hActive p).mp hp).1 (hChainActive p hp) j hj z hzj
      refine ⟨fun fuel => (hPotential.1 fuel).trans hRegionsTwo,
        hPotential.2.1.trans hRegionsTwo,?_⟩
      intro M y hM hNM hMs hy
      have hRegionsOne : regions ≤ 1 := by
        rcases lt_or_gt_of_ne hNM with hlt | hgt
        · exact hTwo N M x y hN hM hlt hs hMs hx hy
        · exact hTwo M N y x hM hN hgt hMs hs hy hx
      exact ⟨fun fuel => (hPotential.1 fuel).trans hRegionsOne,
        hPotential.2.1.trans hRegionsOne⟩
    have hThresholdUnit (B : ℕ) (hB : 2 ≤ B) (hBk : B ≤ k) :
        decomposableThreshold B 2 k = 1 := by
      rw [decomposableThreshold_eq_choose hB (by omega) (by omega)]
      have he : B+2-4 = B-2 := by omega
      rw [he,Nat.choose_self]
    have hExposedUnitLower (M : ℕ) (hM : 1 ≤ M) (hMk : M ≤ k-2)
        (v : Side) (w : List Letter)
        (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
        (hf : w.head? = some Letter.child)
        (hmark : Letter.ext 1 v ∈ w) (hc : Letter.child ∈ w) :
        1 ≤ (mkRoot A 3 k M v w).bound := by
      let ρ := mkRoot A 3 k M v w
      change 1 ≤ ρ.bound
      have hExist := hChildExists ρ hc
      cases hcp : ρ.childPositions with
      | nil =>
        obtain ⟨p,hp⟩ := hExist
        rw [hcp] at hp
        cases hp
      | cons p ps =>
        have hhead : ρ.childPositions.head? = some p := by rw [hcp]; rfl
        have hpzero := hFirstIsZero ρ hf p ps hcp
        have hMin : min (3-1) (k-M) = 2 := by omega
        have hBase : ρ.base = 1 := by
          have hLimits := hAnyExposedPoint A 3 k M hA hAk
            (by omega) hk hM hMk v w hw hf hmark
          rw [hMin] at hLimits
          simp only [Nat.reduceSub] at hLimits
          rw [base_eq_baseOf,hhead]
          change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) k = 1
          rw [hpzero]
          cases v with
          | lower =>
            dsimp only [ownLimit,otherLimit] at hLimits
            rw [hLimits.1,hLimits.2]
            simp [baseOf,show A-1 ≠ 0 by omega]
          | upper =>
            dsimp only [ownLimit,otherLimit] at hLimits
            rw [hLimits.1,hLimits.2]
            simp [baseOf,show A-1 ≠ 0 by omega]
        by_cases hr : ρ.numRuns ≤ 1
        · rw [bound,boundFuel.eq_2,if_pos hr,hBase]
        · have hRuns : 2 ≤ ρ.numRuns := by omega
          have hlen := numRuns_le_length ρ
          have hne : ps ≠ [] := by
            intro he
            rw [hcp,he] at hlen
            simp only [List.length_cons,List.length_nil] at hlen
            omega
          obtain ⟨hBlock,hRest⟩ := hFirstBlock ρ p ps hcp hne
          have hLeaf := hLeafAnyExposed A 3 k M hA hAk
            (by omega) hk hM hMk v w hw hf hmark p ps hcp hne
          rw [hMin,hThresholdUnit (A-1) (by omega) (by omega)] at hLeaf
          have hCut :
              (ρ.part [p] (opp v) (k-A+1)).bound +
                (ρ.part ps v (A-2)).bound ≤ ρ.bound := by
            cases v with
            | lower =>
              have hcut := (ctx_bound_cut_le ρ hRuns [p] hBlock (A-2)
                (by omega) (by change A-2 ≤ k-2; omega)).2
              have he : k-1-(A-2) = k-A+1 := by omega
              simpa only [opp,show ρ.k = k from rfl,he,hRest] using hcut
            | upper =>
              have hcut := (ctx_bound_cut_le ρ hRuns [p] hBlock (k-A+1)
                (by omega) (by change k-A+1 ≤ k-2; omega)).1
              have he : k-1-(k-A+1) = A-2 := by omega
              simpa only [opp,show ρ.k = k from rfl,he,hRest] using hcut
          change (ρ.part [p] (opp v) (k-A+1)).bound = 1 at hLeaf
          omega
    have hMarkedUnitLower (M : ℕ) (hM : 1 ≤ M) (hMk : M ≤ k-2)
        (v : Side) (w : List Letter)
        (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
        (hf : w.head? = some (Letter.ext 1 v))
        (hl : w.getLast? = some Letter.child) (hc : Letter.child ∈ w) :
        1 ≤ (mkRoot A 3 k M v w).bound := by
      let σ := mkRoot A 3 k M v w
      have hσwf : σ.WellFormed := by
        cases v with
        | lower =>
          exact hRootWF M hM hMk A 3 (by omega) (by omega) hAk hk Side.lower w hw
        | upper =>
          exact hRootWF M hM hMk 3 A (by omega) (by omega) hk hAk Side.upper w hw
      have hwrev : ∀ z ∈ w.reverse, z = Letter.child ∨ z = Letter.ext 1 v := by
        intro z hz
        exact hw z (List.mem_reverse.mp hz)
      have hfrev : w.reverse.head? = some Letter.child := by simpa using hl
      have hmark : Letter.ext 1 v ∈ w :=
        List.mem_of_mem_head? (Option.mem_def.mpr hf)
      have hmarkrev : Letter.ext 1 v ∈ w.reverse := List.mem_reverse.mpr hmark
      have hcrev : Letter.child ∈ w.reverse := List.mem_reverse.mpr hc
      have hLower := hExposedUnitLower M hM hMk v w.reverse hwrev hfrev hmarkrev hcrev
      have hEq : (mkRoot A 3 k M v w.reverse).bound = σ.bound :=
        ctx_bound_reverse σ hσwf
      rw [hEq] at hLower
      exact hLower
    have hUpperTwo (v : Side) (w : List Letter)
        (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
        (hmark : Letter.ext 1 v ∈ w) :
        (mkRoot A 3 k m v w).bound ≤ 2 := by
      let ρ := mkRoot A 3 k m v w
      obtain ⟨x,hx⟩ := hMarkerExists ρ v hmark
      have hN : 1 ∈ ρ.levels := by simp [levels,ρ,mkRoot]
      have hs := hSideOne ρ v hw ⟨x,hx⟩
      cases v with
      | lower =>
        exact (hThree ρ (hRootPositive ρ Side.lower hw) Side.lower 1 x hN hs hx
          (by simp [ρ,mkRoot])).2.1
      | upper =>
        exact (hThree ρ (hRootPositive ρ Side.upper hw) Side.upper 1 x hN hs hx
          (by simp [ρ,mkRoot])).2.1
    have hMaximumEdge (v : Side) (w : List Letter)
        (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
        (hmark : Letter.ext 1 v ∈ w) (hM : m = k-2) :
        (mkRoot A 3 k m v w).bound ≤ 1 := by
      let ρ := mkRoot A 3 k m v w
      let τ : Context := {a := match v with | Side.lower => A | Side.upper => 2, u := match v with | Side.lower => 2 | Side.upper => A, k := k, word := w, maxima := []}
      obtain ⟨x,hx⟩ := hMarkerExists ρ v hmark
      have hN : 1 ∈ ρ.levels := by simp [levels,ρ,mkRoot]
      have hs := hSideOne ρ v hw ⟨x,hx⟩
      have hSub : k-m = 2 := by omega
      have hNorm := (ctx_sibling_maximum_upper_normalize ρ 1 hN).2.2
      have hDom : ρ.bound ≤ τ.bound := by
        cases v <;> simpa [ρ,mkRoot,τ,hs,maximumAt,hSub] using hNorm
      have hLevels : τ.levelsOn v 0 = [] := by simp [levelsOn,levels,τ]
      have hLeft (p : ℕ) : τ.leftExt v 0 p = 0 := by simp [leftExt_eq,hLevels]
      have hRight (p : ℕ) : τ.rightExt v 0 p = 0 := by simp [rightExt_eq,hLevels]
      have hRank : ∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p → 0 < τ.capLimit p p →
          τ.leftExt v 0 p+1 = 1 ∧
            1+τ.rightExt v 0 p = (match v with | Side.lower => τ.u-1 | Side.upper => τ.a-1) := by
        intro p hp hc hp'
        rw [hLeft,hRight]
        cases v <;> simp [τ]
      cases v with
      | lower =>
        exact hDom.trans ((ctx_bound_le_one_of_common_singleton_rank τ
          (hRootPositive τ Side.lower hw) Side.lower 1 hRank).2.1)
      | upper =>
        exact hDom.trans ((ctx_bound_le_one_of_common_singleton_rank τ
          (hRootPositive τ Side.upper hw) Side.upper 1 hRank).2.1)
    dsimp only
    intro hRuns
    let ρ := mkRoot A 3 k m side word
    suffices hBound : ρ.bound = 2 from by
      convert hBound using 1 <;> cases side <;> rfl
    have hρRuns : 2 ≤ ρ.numRuns := by
      convert hRuns using 1 <;> cases side <;> rfl
    have hUpper := hUpperTwo side word hletters hmarker
    change ρ.bound ≤ 2 at hUpper
    have hExist := hChildExists ρ hchild
    have hNonempty : ρ.childPositions ≠ [] := by
      intro he
      obtain ⟨q, hq⟩ := hExist
      rw [he] at hq
      cases hq
    obtain ⟨p, ps, hcp⟩ := List.exists_cons_of_ne_nil hNonempty
    have hlen := Ctx.numRuns_le_length ρ
    have hne : ps ≠ [] := by
      intro he
      rw [hcp, he] at hlen
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    obtain ⟨hBlock, hRest⟩ := hFirstBlock ρ p ps hcp hne
    have hMin : min (3 - 1) (k - m) = 2 := by omega
    have hLeaf := hLeafAnyExposed A 3 k m hA hAk
      (by omega) hk hm hmk side word hletters hfirst hmarker p ps hcp hne
    rw [hMin, hThresholdUnit (A - 1) (by omega) (by omega)] at hLeaf
    change (ρ.part [p] (opp side) (k - A + 1)).bound = 1 at hLeaf
    obtain ⟨w', hw', hf', hl', hc', hEq⟩ :=
      hComplementNeither A 3 k m hk side word hletters hfirst hlast hmarker p ps hcp hne
    have hLegal : max (A - 2) (m + 1) ≤ k - 2 := by omega
    have hLow := hMarkedUnitLower (max (A - 2) (m + 1))
      (by omega) hLegal side w' hw' hf' hl' hc'
    have hComp : 1 ≤ (ρ.part ps side (A - 2)).bound := by
      rw [hEq]
      exact hLow
    have hCut : (ρ.part [p] (opp side) (k - A + 1)).bound +
        (ρ.part ps side (A - 2)).bound ≤ ρ.bound := by
      cases side with
      | lower =>
        have hc := (ctx_bound_cut_le ρ hρRuns [p] hBlock (A - 2)
          (by omega) (by change A - 2 ≤ k - 2; omega)).2
        have he : k - 1 - (A - 2) = k - A + 1 := by omega
        simpa only [opp, show ρ.k = k from rfl, he, hRest] using hc
      | upper =>
        have hc := (ctx_bound_cut_le ρ hρRuns [p] hBlock (k - A + 1)
          (by omega) (by change k - A + 1 ≤ k - 2; omega)).1
        have he : k - 1 - (k - A + 1) = A - 2 := by omega
        simpa only [opp, show ρ.k = k from rfl, he, hRest] using hc
    omega

  have hChosenThreeNoneRaw (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
      (hk : 3 ≤ σ.k) (ha : σ.a ≤ σ.k) (hu : σ.u ≤ σ.k)
      (hm : 1 ≤ m) (hmk : m ≤ σ.k - 2) (hunsat : m ≤ σ.k - 3)
      (s : Ctx.Side)
      (hletters : ∀ v ∈ σ.word, v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 s)
      (hruns : 2 ≤ σ.numRuns)
      (hchosen : (fun v : Ctx.Side => match v with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s = 3)
      (hother : 3 ≤ (match s with | Ctx.Side.lower => σ.a | Ctx.Side.upper => σ.u))
      (hhead : σ.word.head? = some Ctx.Letter.child)
      (hlast : σ.word.getLast? = some Ctx.Letter.child) : σ.bound = 2 := by
    classical
    obtain ⟨first, sep, last, hfirst, hlastChild, hfirstSep, hsepLast, hsep⟩ :=
      hTwoSites σ s hletters hruns
    have hsepR : sep < σ.word.length := by
      by_contra hn
      rw [Ctx.Context.letterAt_of_length_le σ (by omega)] at hsep
      cases hsep
    have hmarker : Ctx.Letter.ext 1 s ∈ σ.word := by
      have he : σ.word[sep] = Ctx.Letter.ext 1 s := by
        simpa [Ctx.Context.letterAt, List.getElem?_eq_getElem hsepR] using hsep
      rw [← he]
      exact List.getElem_mem hsepR
    have hchild : Ctx.Letter.child ∈ σ.word :=
      List.mem_of_mem_head? (Option.mem_def.mpr hhead)
    cases s with
    | lower =>
      change σ.u = 3 at hchosen
      change 3 ≤ σ.a at hother
      have hExact := hChosenThreeNoneExact σ.a σ.k m hk hother ha hm hmk hunsat
        Ctx.Side.lower σ.word hletters hmarker hhead hlast hchild
      let ρ : Ctx.Context :=
        {a := σ.a, u := 3, k := σ.k, word := σ.word, maxima := [m]}
      change 2 ≤ ρ.numRuns → ρ.bound = 2 at hExact
      have hEq : ρ = σ := by
        dsimp only [ρ]
        cases σ with
        | mk aa uu kk ww mm =>
          change uu = 3 at hchosen
          change mm = [m] at hmax
          subst uu
          subst mm
          rfl
      rw [hEq] at hExact
      exact hExact hruns
    | upper =>
      change σ.a = 3 at hchosen
      change 3 ≤ σ.u at hother
      have hExact := hChosenThreeNoneExact σ.u σ.k m hk hother hu hm hmk hunsat
        Ctx.Side.upper σ.word hletters hmarker hhead hlast hchild
      let ρ : Ctx.Context :=
        {a := 3, u := σ.u, k := σ.k, word := σ.word, maxima := [m]}
      change 2 ≤ ρ.numRuns → ρ.bound = 2 at hExact
      have hEq : ρ = σ := by
        dsimp only [ρ]
        cases σ with
        | mk aa uu kk ww mm =>
          change aa = 3 at hchosen
          change mm = [m] at hmax
          subst aa
          subst mm
          rfl
      rw [hEq] at hExact
      exact hExact hruns

  let σ : Ctx.Context := {a := a, u := u, k := k, word := word, maxima := [m]}
  let marker := Ctx.Letter.ext 1 side
  let normalWord :=
    (if word.head? = some marker then [marker] else []) ++
    (List.replicate (min σ.numRuns (if a = 2 ∨ u = 2 then 3 else 2))
      Ctx.Letter.child).intersperse marker ++
    (if word.getLast? = some marker then [marker] else [])
  let τ : Ctx.Context := {σ with word := normalWord}
  change σ.bound = τ.bound
  by_cases hzero : a ≤ 1 ∨ u ≤ 1
  · exact (ctx_bound_zero_of_unit_global_axis σ hzero).2.trans
      (ctx_bound_zero_of_unit_global_axis τ hzero).2.symm
  by_cases hempty : σ.childPositions = []
  · have hruns : σ.numRuns = 0 := by
      have h := Ctx.numRuns_le_length σ
      rw [hempty] at h
      simp only [List.length_nil] at h
      omega
    have hτ : τ.childPositions = [] := by
      by_cases hleft : word.head? = some marker <;>
        by_cases hright : word.getLast? = some marker <;>
        simp [τ, normalWord, hruns, hleft, hright,
          Ctx.Context.childPositions, Ctx.Context.letterAt, marker] <;>
        intro p hp <;> interval_cases p <;> simp
    rw [hemptyBound σ hempty, hemptyBound τ hτ]
  by_cases hsingle : σ.numRuns ≤ 1
  · have hclamp : min σ.numRuns (if a = 2 ∨ u = 2 then 3 else 2) = σ.numRuns := by
      apply Nat.min_eq_left
      split_ifs <;> omega
    have hsingleEq := hSingle σ m rfl side hletters hsingle
    simpa only [τ, normalWord, hclamp] using hsingleEq
  have hruns : 2 ≤ σ.numRuns := by omega
  have hsourcePositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j := by
    intro p j v hx
    have hp : p < σ.word.length := by
      by_contra hn
      rw [Ctx.Context.letterAt_of_length_le σ (by omega)] at hx
      cases hx
    have hm : Ctx.Letter.ext j v ∈ word := by
      have he : σ.word[p] = Ctx.Letter.ext j v := by
        simpa [Ctx.Context.letterAt, List.getElem?_eq_getElem hp] using hx
      rw [← he]
      exact List.getElem_mem hp
    rcases hletters _ hm with h | h
    · cases h
    · have hj := (Ctx.Letter.ext.inj h).1
      omega
  let global := fun v : Ctx.Side => match v with
    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let other := match side with
    | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower
  have hne : side ≠ other := by cases side <;> simp [other]
  have hChosenK : global side ≤ σ.k := by
    cases side with
    | lower => exact huk
    | upper => exact hak
  have hFacts := hNormalFacts σ side hruns
  have hτletters : ∀ v ∈ τ.word,
      v = Ctx.Letter.child ∨ v = Ctx.Letter.ext 1 side := hFacts.1
  have hτnum : τ.numRuns = min σ.numRuns (if a = 2 ∨ u = 2 then 3 else 2) := hFacts.2.1
  have hτruns : 2 ≤ τ.numRuns := by
    rw [hτnum]
    apply Nat.le_min.mpr
    refine ⟨hruns, ?_⟩
    split_ifs <;> omega
  have hτa : τ.a = σ.a := rfl
  have hτu : τ.u = σ.u := rfl
  have hτk : τ.k = σ.k := rfl
  have hτhead : τ.word.head? = some (Ctx.Letter.ext 1 side) ↔
      σ.word.head? = some (Ctx.Letter.ext 1 side) := hFacts.2.2.1
  have hτlast : τ.word.getLast? = some (Ctx.Letter.ext 1 side) ↔
      σ.word.getLast? = some (Ctx.Letter.ext 1 side) := hFacts.2.2.2
  by_cases hOtherTwo : global other = 2
  · have hAxis : a = 2 ∨ u = 2 := by
      cases side <;> simp only [global, other, σ] at hOtherTwo <;> omega
    have hτthree : 3 ≤ τ.numRuns ↔ 3 ≤ σ.numRuns := by
      rw [hτnum, if_pos hAxis]
      simp [Nat.le_min]
    rw [hCriterion σ m rfl hk hm hmk side other hne hletters hruns hChosenK hOtherTwo,
      hCriterion τ m rfl hk hm hmk side other hne hτletters hτruns hChosenK hOtherTwo]
    simp only [ne_eq, hτhead, hτlast, hτthree, hτa, hτu, hτk]
  by_cases hChosenTwo : global side ≤ 2
  · have hσzero := hOldChosenTwoZero σ m rfl side hletters hruns hChosenTwo
    have hτzero := hOldChosenTwoZero τ m rfl side hτletters hτruns hChosenTwo
    exact hσzero.trans hτzero.symm
  by_cases hSaturated : m = k - 2
  · have hσmax : σ.maxima = [σ.k - 2] := by
      change [m] = [k - 2]
      rw [hSaturated]
    have hτmax : τ.maxima = [τ.k - 2] := by
      change [m] = [k - 2]
      rw [hSaturated]
    rw [hSaturatedExact σ hσmax hk hak huk side other hne hletters hruns,
      hSaturatedExact τ hτmax hk hak huk side other hne hτletters hτruns]
    simp only [hτhead, hτlast, hτa, hτu, hτk]
  by_cases hChosenThree : global side = 3
  · have hOtherThree : 3 ≤ global other := by
      cases side <;> simp only [global, other, σ] at hOtherTwo ⊢ <;> omega
    by_cases hMarked : σ.word.head? = some (Ctx.Letter.ext 1 side) ∨
        σ.word.getLast? = some (Ctx.Letter.ext 1 side)
    · have hσEq := hMarkedThreeExact σ m rfl hk hak huk hmk side other hne
        hletters hruns hChosenThree hOtherThree hMarked
      have hτMarked : τ.word.head? = some (Ctx.Letter.ext 1 side) ∨
          τ.word.getLast? = some (Ctx.Letter.ext 1 side) :=
        hMarked.elim (fun h => Or.inl (hτhead.mpr h))
          (fun h => Or.inr (hτlast.mpr h))
      have hτEq := hMarkedThreeExact τ m rfl hk hak huk hmk side other hne
        hτletters hτruns hChosenThree hOtherThree hτMarked
      rw [hσEq, hτEq]
      simp only [hτhead, hτlast]
    · have hEnds := hRootEnds σ side hletters hruns
      have hHead : σ.word.head? = some Ctx.Letter.child :=
        hEnds.1.elim id (fun h => False.elim (hMarked (Or.inl h)))
      have hLast : σ.word.getLast? = some Ctx.Letter.child :=
        hEnds.2.1.elim id (fun h => False.elim (hMarked (Or.inr h)))
      have hτEnds := hRootEnds τ side hτletters hτruns
      have hτHead : τ.word.head? = some Ctx.Letter.child :=
        hτEnds.1.elim id (fun h => False.elim (hMarked (Or.inl (hτhead.mp h))))
      have hτLast : τ.word.getLast? = some Ctx.Letter.child :=
        hτEnds.2.1.elim id (fun h => False.elim (hMarked (Or.inr (hτlast.mp h))))
      have hUnSat : m ≤ k - 3 := by omega
      have hσExact := hChosenThreeNoneRaw σ m rfl hk hak huk hm hmk hUnSat
        side hletters hruns hChosenThree (by cases side <;> exact hOtherThree) hHead hLast
      have hτExact := hChosenThreeNoneRaw τ m rfl hk hak huk hm hmk hUnSat
        side hτletters hτruns hChosenThree (by cases side <;> exact hOtherThree) hτHead hτLast
      exact hσExact.trans hτExact.symm
  exfalso
  exact hChosenThree (by simpa only [global, σ] using hchosen3)

end ErdosSzekeres
