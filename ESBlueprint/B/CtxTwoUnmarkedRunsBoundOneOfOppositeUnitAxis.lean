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

set_option maxHeartbeats 12000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- A raw uniform one-level context with exactly two child runs and unmarked word endpoints has bound one when its old maximum is at most k minus three, its chosen global lies between three and k and its opposite global equals two. The proof retains the entire first physical run, rules out an old marker after an omitted child using three-run geometry, evaluates the exact unilateral two-level profile and lifts the positive part by an interval cut. Arbitrary run and separator multiplicities, no WF or positive-old-maximum assumption.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_two_unmarked_runs_bound_one_of_opposite_unit_axis (σ : Ctx.Context) (m : ℕ) (hmax : σ.maxima = [m])
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

end ErdosSzekeres
