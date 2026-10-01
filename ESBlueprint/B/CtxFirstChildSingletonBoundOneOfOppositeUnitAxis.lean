import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank
import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

/-- A raw one-level context with positive actual labels, at least two runs and opposite global exactly two has bound one when the chosen global is at least four plus the old-left-marker indicator, does not exceed k, and the old maximum is at most k minus three. Its first-child singleton part on the chosen side at maximum one has bound one. The exact two-level unilateral extension profile supplies a positive base, the interval cut lifts it, and common singleton rank supplies the matching upper bound.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_first_child_singleton_bound_one_of_opposite_unit_axis (σ : Ctx.Context)
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

end ErdosSzekeres
