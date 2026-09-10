import ESBlueprint.B.CtxBoundaryMarkerRankBudget
import ESBlueprint.B.CtxSingleLevelOccurrencePruneBoundMono
import ESBlueprint.B.CtxSmallOppositeGlobalMarkerSquareBound
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- When a kept endpoint contains children surrounding either of the two actual chosen markers, bound the chosen complement by w+1 and erase the new opposite boundary to reduce the companion width to w-1. The actual full and independent-fuel cut sum satisfies the two-marker potential under an explicit bare two-marker premise only at widths at most w-1. The original opposite history is empty; old maxima, inactive children, physical barriers, and independent new maxima are allowed.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_surrounding_endpoint_cut_potential_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hclear : σ.levelsOn t 0 = [])
  (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y)
  (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
  (keep : List ℕ) (a b l m n : ℕ)
  (ha : a ∈ keep) (hb : b ∈ keep)
  (hsurround : (a < x ∧ x < b) ∨ (a < y ∧ y < b))
  (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
  (hl : l ∈ σ.childPositions) (hlnot : l ∉ keep)
  (endpoint : Bool)
  (hendpoint : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep →
    if endpoint then q < p else p < q)
  (htwo : ∀ (ρ : Ctx.Context) (J K a b : ℕ),
    (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
    (∀ j ∈ ρ.levels, ρ.maximumAt j = 0) →
    (∀ j ∈ ρ.levels, ρ.sideAt j = s) →
    J ∈ ρ.levels → K ∈ ρ.levels → J < K →
    a ∈ ρ.extPositions J → b ∈ ρ.extPositions K →
    (∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = a ∨ p = b) →
    (match s with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) ≤ 5 →
    (∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) →
    let v := (match t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1
    v ≤ ((match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) - 1 →
    4 ≤ v → ρ.bound ≤ (v + 1).choose 2 + v - 1) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) +
    Ctx.Context.boundFuel g (σ.part keep t n) ≤ (w + 1).choose 2 + w - 1) ∧
    (σ.part rest s m).bound + (σ.part keep t n).bound ≤ (w + 1).choose 2 + w - 1 := by
  classical
  have ctx_nested_boundary_markers_rank_budget (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (N J x y : ℕ) (hN : N ∈ σ.levels) (hJ : J ∈ σ.levels) (hJN : J < N)
    (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions J)
    (hside : σ.sideAt J = σ.sideAt N)
    (outer inner : Bool)
    (hOuter : ∀ p ∈ σ.childPositions, if outer then p < x else x < p)
    (hOuterYoung : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
      if outer then p < x else x < p)
    (hInner : ∀ p ∈ σ.childPositions, if inner then p < y else y < p)
    (hInnerYoung : ∀ j ∈ σ.levelsOn (σ.sideAt J) J, ∀ p ∈ σ.extPositions j,
      if inner then p < y else y < p)
    (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
    (hglobal : (match (generalizing := false) σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (A B : ℕ)
    (hLeft : ∀ p ∈ σ.childPositions, A ≤ σ.leftExt t J p)
    (hRight : ∀ p ∈ σ.childPositions, B ≤ σ.rightExt t J p) :
    let budget := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - A - B
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ budget) ∧ σ.bound ≤ budget := by
    classical
    let τ : Context := match (generalizing := false) σ.sideAt N with
      | Side.lower => { σ with u := min (σ.u - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
      | Side.upper => { σ with a := min (σ.a - 1) (σ.k - σ.maximumAt N), maxima := σ.maxima.take (N - 1) }
    let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
    change (∀ fuel, boundFuel fuel σ ≤ w - A - B) ∧ σ.bound ≤ w - A - B
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
    have hJpos := one_le_of_mem_levels hJ
    have hJτ : J ∈ τ.levels := by rw [hLevels]; exact List.mem_filter.mpr ⟨hJ, by simp [hJN]⟩
    have hBelow (v : Side) : τ.levelsOn v J = σ.levelsOn v J := by
      rw [hLevelsOn]
      apply List.filter_eq_self.mpr
      intro j hj
      have hh := of_decide_eq_true (List.mem_filter.mp hj).2
      simp only [decide_eq_true_eq]
      omega
    have hLeftStep : leftStep τ = leftStep σ := by funext z j; simp only [leftStep, hExt]
    have hRightStep : rightStep τ = rightStep σ := by funext z j; simp only [rightStep, hExt]
    have hLeftEq (p : ℕ) : τ.leftExt t J p = σ.leftExt t J p := by
      simp only [leftExt_eq, hLeftStep, hBelow]
    have hRightEq (p : ℕ) : τ.rightExt t J p = σ.rightExt t J p := by
      simp only [rightExt_eq, hRightStep, hBelow]
    have hChosen : (match (generalizing := false) τ.sideAt J with | Side.lower => τ.u | Side.upper => τ.a) ≤ 4 := by
      rw [hSide, hside]
      cases hs : σ.sideAt N
      · simp only [τ, hs] at hglobal ⊢
        exact (Nat.min_le_left (σ.u - 1) (σ.k - σ.maximumAt N)).trans (by omega)
      · simp only [τ, hs] at hglobal ⊢
        exact (Nat.min_le_left (σ.a - 1) (σ.k - σ.maximumAt N)).trans (by omega)
    have hSmall : min ((match (generalizing := false) τ.sideAt J with | Side.lower => τ.u | Side.upper => τ.a) - 1)
        (τ.k - τ.maximumAt J) ≤ 3 := by
      apply (Nat.min_le_left _ _).trans
      omega
    have hBudget : (match (generalizing := false) t with | Side.lower => τ.u | Side.upper => τ.a) - 1 = w := by
      dsimp only [τ, w]
      cases hs : σ.sideAt N <;> cases ht : t <;> simp_all only [ne_eq, not_true_eq_false]
    have hBound := ctx_boundary_marker_rank_budget τ hPositive J y hJτ (by rw [hExt]; exact hy)
      inner (by intro p hp; rw [hChild] at hp; exact hInner p hp)
      (by
        intro j hj p hp
        rw [hSide, hBelow] at hj
        rw [hExt] at hp
        exact hInnerYoung j hj p hp)
      t (by rw [hSide, hside]; exact hne) hSmall A B
      (by intro p hp; rw [hChild] at hp; rw [hLeftEq]; exact hLeft p hp)
      (by intro p hp; rw [hChild] at hp; rw [hRightEq]; exact hRight p hp)
    change (∀ fuel, boundFuel fuel τ ≤
        ((match (generalizing := false) t with | Side.lower => τ.u | Side.upper => τ.a) - 1) - A - B) ∧
      τ.bound ≤ ((match (generalizing := false) t with | Side.lower => τ.u | Side.upper => τ.a) - 1) - A - B at hBound
    rw [hBudget] at hBound
    exact ⟨fun fuel => (hFuel fuel).trans (hBound.1 fuel), hFull.trans hBound.2⟩

  have ctx_three_ordered_markers_exterior_unit_bound (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s : Ctx.Side) (J N M a x y : ℕ)
    (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels)
    (hJN : J < N) (hNM : N < M)
    (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
    (ha : a ∈ σ.extPositions J) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (horder : (a < x ∧ x < y ∧ ∀ p ∈ σ.childPositions, p < a) ∨
      (y < x ∧ x < a ∧ ∀ p ∈ σ.childPositions, a < p)) :
    σ.bound ≤ 1 := by
    classical
    have hTrip (ρ : Context) (A B D a b d : ℕ)
        (hA : A ∈ ρ.levels) (hB : B ∈ ρ.levels) (hD : D ∈ ρ.levels)
        (hAB : A < B) (hBD : B < D)
        (hAs : ρ.sideAt A = s) (hBs : ρ.sideAt B = s) (hDs : ρ.sideAt D = s)
        (ha : a ∈ ρ.extPositions A) (hb : b ∈ ρ.extPositions B) (hd : d ∈ ρ.extPositions D) :
        (∀ p, p < a → a < b → b < d → 3 ≤ ρ.rightExt s 0 p) ∧
        (∀ p, a < p → b < a → d < b → 3 ≤ ρ.leftExt s 0 p) := by
      have hAOn : A ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hA, by simp [hAs]⟩
      have hBOn : B ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hB, by simp [hBs]⟩
      have hDOn : D ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hD, by simp [hDs]⟩
      have hSorted : (ρ.levelsOn s 0).Pairwise (· < ·) := by
        apply List.Pairwise.filter
        exact List.pairwise_lt_range.map (fun i ↦ i + 1) (fun i j h ↦ by dsimp; omega)
      have hThree : [A, B, D].Sublist (ρ.levelsOn s 0) := by
        have hs : [A, B, D].Pairwise (· < ·) := by simp; omega
        have hsub : [A, B, D] ⊆ ρ.levelsOn s 0 := by
          intro j hj
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl
          · exact hAOn
          · exact hBOn
          · exact hDOn
        have he : (ρ.levelsOn s 0).filter (· ∈ [A, B, D]) = [A, B, D] := by
          apply (hSorted.filter _).eq_of_mem_iff hs
          intro j
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨And.right, fun hj => ⟨hsub hj, hj⟩⟩
        rw [← he]
        exact List.filter_sublist
      have hSort (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
        (List.pairwise_lt_range.filter _).imp le_of_lt
      constructor
      · intro p hpa hab hbd
        have hmA : a ∈ (ρ.extPositions A).filter (p < ·) := by simp [ha, hpa]
        have hneA := List.ne_nil_of_mem hmA
        let u := ((ρ.extPositions A).filter (p < ·)).head hneA
        have hu : ((ρ.extPositions A).filter (p < ·)).head? = some u := List.head?_eq_some_head hneA
        have hua : u ≤ a := ((hSort A).filter _).rel_head hmA
        have hmB : b ∈ (ρ.extPositions B).filter (u < ·) := by simp [hb]; omega
        have hneB := List.ne_nil_of_mem hmB
        let v := ((ρ.extPositions B).filter (u < ·)).head hneB
        have hv : ((ρ.extPositions B).filter (u < ·)).head? = some v := List.head?_eq_some_head hneB
        have hvb : v ≤ b := ((hSort B).filter _).rel_head hmB
        have hmD : d ∈ (ρ.extPositions D).filter (v < ·) := by simp [hd]; omega
        have hneD := List.ne_nil_of_mem hmD
        have hh := le_getD_max?_of_mem (L := (ρ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
          (List.mem_map.mpr ⟨[A, B, D], List.mem_sublists.mpr hThree, rfl⟩)
        change _ ≤ ρ.rightExt s 0 p at hh
        simpa only [List.foldl_cons, List.foldl_nil, rightStep, hu, hv,
          List.head?_eq_some_head hneD] using hh
      · intro p hap hba hdb
        have hmA : a ∈ (ρ.extPositions A).filter (· < p) := by simp [ha, hap]
        have hneA := List.ne_nil_of_mem hmA
        let u := ((ρ.extPositions A).filter (· < p)).getLast hneA
        have hu : ((ρ.extPositions A).filter (· < p)).getLast? = some u := List.getLast?_eq_some_getLast hneA
        have hau : a ≤ u := ((hSort A).filter _).rel_getLast hmA
        have hmB : b ∈ (ρ.extPositions B).filter (· < u) := by simp [hb]; omega
        have hneB := List.ne_nil_of_mem hmB
        let v := ((ρ.extPositions B).filter (· < u)).getLast hneB
        have hv : ((ρ.extPositions B).filter (· < u)).getLast? = some v := List.getLast?_eq_some_getLast hneB
        have hbv : b ≤ v := ((hSort B).filter _).rel_getLast hmB
        have hmD : d ∈ (ρ.extPositions D).filter (· < v) := by simp [hd]; omega
        have hneD := List.ne_nil_of_mem hmD
        have hh := le_getD_max?_of_mem (L := (ρ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
          (List.mem_map.mpr ⟨[A, B, D], List.mem_sublists.mpr hThree, rfl⟩)
        change _ ≤ ρ.leftExt s 0 p at hh
        simpa only [List.foldl_cons, List.foldl_nil, leftStep, hu, hv,
          List.getLast?_eq_some_getLast hneD] using hh
    rcases horder with ⟨hax, hxy, hChildren⟩ | ⟨hyx, hxa, hChildren⟩
    · have hRank : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p →
          0 < σ.capLimit p p → σ.leftExt s 0 p + 1 = 1 ∧
          1 + σ.rightExt s 0 p =
            (match (generalizing := false) s with | Side.lower => σ.u - 1 | Side.upper => σ.a - 1) := by
        intro p hp hcup hcap
        have ht := (hTrip σ J N M a x y hJ hN hM hJN hNM hJs hNs hMs ha hx hy).1
          p (hChildren p hp) hax hxy
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal hcup hcap ⊢ <;> omega
      exact (ctx_bound_le_one_of_common_singleton_rank σ hpositive s 1 hRank).2.1
    · have hRank : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p →
          0 < σ.capLimit p p → σ.leftExt s 0 p + 1 = 4 ∧
          4 + σ.rightExt s 0 p =
            (match (generalizing := false) s with | Side.lower => σ.u - 1 | Side.upper => σ.a - 1) := by
        intro p hp hcup hcap
        have ht := (hTrip σ J N M a x y hJ hN hM hJN hNM hJs hNs hMs ha hx hy).2
          p (hChildren p hp) hxa hyx
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal hcup hcap ⊢ <;> omega
      exact (ctx_bound_le_one_of_common_singleton_rank σ hpositive s 4 hRank).2.1

  have ctx_surrounded_younger_marker_complement_width_plus_one_bound (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t) (J N M a b x y : ℕ)
    (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels)
    (hJN : J < N) (hNM : N < M)
    (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
    (ha : a ∈ σ.extPositions J) (hb : b ∈ σ.extPositions J)
    (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
    (hax : a < x) (hxb : x < b)
    (houtside : ∀ p ∈ σ.childPositions, p < a ∨ b < p)
    (hBeforeN : ∀ j ∈ σ.levelsOn s N, ∀ p ∈ σ.extPositions j, j = J)
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) :
    let w := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ w + 1) ∧ σ.bound ≤ w + 1 := by
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
    let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
    let color (p : ℕ) := if p < x then (0 : ℕ) else 1
    let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
    let group (c : ℕ) : Context := { σ with
      word := (List.range σ.word.length).map (fun p => match (generalizing := false) σ.letterAt p with
        | Letter.child => if p ∈ support c then Letter.child else Letter.ext (σ.maxima.length + 1) Side.lower
        | Letter.ext j v => Letter.ext j v) }
    change (∀ fuel, boundFuel fuel σ ≤ w + 1) ∧
      σ.bound ≤ w + 1
    have hNe (p : ℕ) (hp : p ∈ σ.childPositions) : p ≠ x := by
      intro he
      subst p
      have hc := of_decide_eq_true (List.mem_filter.mp hp).2
      have he := (List.mem_filter.mp hx).2
      simp [hc] at he
    have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
    have hSmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3 := by
      intro p hp
      have hn := hNe p hp
      by_cases hpx : p < x
      · have he := hOneRight σ s N p x hNOn hx hpx
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
      · have he := hOneLeft σ s N p x hNOn hx (by omega)
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
    have hCover : ∀ p ∈ σ.childPositions, color p ∈ ({0, 1} : Finset ℕ) := by
      intro p hp
      dsimp only [color]
      split_ifs <;> simp
    have hColor : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions, p ≤ q →
        (∀ z, p ≤ z → z ≤ q → z ∈ σ.childPositions) → color p = color q := by
      intro p hp q hq hpq hbetween
      have hside : (p < x) = (q < x) := by
        apply propext
        constructor
        · intro hpx
          by_contra hqx
          have hxc := hbetween x (by omega) (by omega)
          exact hNe x hxc rfl
        · omega
      simp only [color, hside]
    have hPos (c : ℕ) : ∀ p j v, (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
      (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).1
    have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔ p ∈ σ.childPositions ∧ color p = c := by
      have hh : (group c).childPositions = σ.childPositions.filter (· ∈ support c) :=
        (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.1
      rw [hh]
      simp [support]
    have hHist (c j : ℕ) (hj : j ∈ σ.levels) :
        (group c).extPositions j = σ.extPositions j ∧ (group c).sideAt j = σ.sideAt j :=
      (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.1 j hj
    have hLevels (c : ℕ) (v : Side) (top : ℕ) : (group c).levelsOn v top = σ.levelsOn v top :=
      (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.1 v top
    have hA (c : ℕ) : a ∈ (group c).extPositions J := by rw [(hHist c J hJ).1]; exact ha
    have hB (c : ℕ) : b ∈ (group c).extPositions J := by rw [(hHist c J hJ).1]; exact hb
    have hX (c : ℕ) : x ∈ (group c).extPositions N := by rw [(hHist c N hN).1]; exact hx
    have hY (c : ℕ) : y ∈ (group c).extPositions M := by rw [(hHist c M hM).1]; exact hy
    have hSide (c j : ℕ) (hj : j ∈ σ.levels) : (group c).sideAt j = σ.sideAt j := (hHist c j hj).2
    have h0 (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < x := by
      have hh := ((hChild 0 p).mp hp).2
      dsimp only [color] at hh
      split_ifs at hh <;> omega
    have h1 (p : ℕ) (hp : p ∈ (group 1).childPositions) : x < p := by
      have hh := ((hChild 1 p).mp hp).2
      have hn := hNe p ((hChild 1 p).mp hp).1
      dsimp only [color] at hh
      split_ifs at hh <;> omega
    have hLeftChild (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < a := by
      have hh := h0 p hp
      have ho := houtside p ((hChild 0 p).mp hp).1
      omega
    have hRightChild (p : ℕ) (hp : p ∈ (group 1).childPositions) : b < p := by
      have hh := h1 p hp
      have ho := houtside p ((hChild 1 p).mp hp).1
      omega
    have hLinear (c q : ℕ) (hq : q ∈ σ.extPositions J) (direction : Bool)
        (hBoundary : ∀ p ∈ (group c).childPositions, if direction then p < q else q < p)
        (hqx : if direction then q < x else x < q) : (group c).bound ≤ w := by
      let ρ : Context := { group c with word := (List.range (group c).word.length).map (fun p =>
        match (generalizing := false) (group c).letterAt p with
        | Letter.child => Letter.child
        | Letter.ext j v => if j = J then
            if p ∈ [q] then Letter.ext J ((group c).sideAt J)
              else Letter.ext ((group c).maxima.length + 1) v
            else Letter.ext j v) }
      have hqG : q ∈ (group c).extPositions J := by rw [(hHist c J hJ).1]; exact hq
      have hp := ctx_single_level_occurrence_prune_bound_mono (group c) (hPos c) J hJ [q] q hqG (by simp)
      have hPosρ : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j := hp.1
      have hChildρ : ρ.childPositions = (group c).childPositions := hp.2.1
      have hHistρ : ∀ j ∈ σ.levels, ρ.sideAt j = (group c).sideAt j ∧
          ρ.maximumAt j = (group c).maximumAt j ∧
          ρ.extPositions j = if j = J then ((group c).extPositions j).filter (· ∈ [q])
            else (group c).extPositions j := hp.2.2.1
      have hSideρ (j : ℕ) (hj : j ∈ σ.levels) : ρ.sideAt j = σ.sideAt j :=
        (hHistρ j hj).1.trans (hSide c j hj)
      have hQ : q ∈ ρ.extPositions J := by
        rw [(hHistρ J hJ).2.2, if_pos rfl]
        simp [hqG]
      have hXP : x ∈ ρ.extPositions N := by
        rw [(hHistρ N hN).2.2, if_neg (show N ≠ J by omega)]
        exact hX c
      have hOnly (j : ℕ) (hj : j ∈ ρ.levelsOn s N) (p : ℕ) (hp : p ∈ ρ.extPositions j) :
          j = J ∧ p = q := by
        have hjL : j ∈ σ.levels := (List.mem_filter.mp hj).1
        have hjP := of_decide_eq_true (List.mem_filter.mp hj).2
        have hjOld : j ∈ σ.levelsOn s N := by
          apply List.mem_filter.mpr
          refine ⟨hjL, ?_⟩
          have hs : σ.sideAt j = s := (hSideρ j hjL).symm.trans hjP.1
          simp [hs, hjP.2]
        rw [(hHistρ j hjL).2.2] at hp
        have hpOld : p ∈ σ.extPositions j := by
          rw [← (hHist c j hjL).1]
          by_cases hjJ : j = J
          · rw [if_pos hjJ] at hp
            exact (List.mem_filter.mp hp).1
          · simpa only [if_neg hjJ] using hp
        have hjJ := hBeforeN j hjOld p hpOld
        refine ⟨hjJ, ?_⟩
        rw [if_pos hjJ] at hp
        exact List.mem_singleton.mp (of_decide_eq_true (List.mem_filter.mp hp).2)
      have hOuter : ∀ p ∈ ρ.childPositions, if direction then p < x else x < p := by
        intro p hp
        rw [hChildρ] at hp
        have hh := hBoundary p hp
        cases direction
        · change x < p
          have hqp : q < p := hh
          have hxq : x < q := hqx
          omega
        · change p < x
          have hpq : p < q := hh
          have hqx' : q < x := hqx
          omega
      have hOuterYoung : ∀ j ∈ ρ.levelsOn (ρ.sideAt N) N, ∀ p ∈ ρ.extPositions j,
          if direction then p < x else x < p := by
        intro j hj p hp
        rw [hSideρ N hN, hNs] at hj
        have hh := hOnly j hj p hp
        rw [hh.2]
        exact hqx
      have hInnerYoung : ∀ j ∈ ρ.levelsOn (ρ.sideAt J) J, ∀ p ∈ ρ.extPositions j,
          if direction then p < q else q < p := by
        intro j hj p hp
        have hjP := of_decide_eq_true (List.mem_filter.mp hj).2
        have hJpos := one_le_of_mem_levels hJ
        have hjN : j ∈ ρ.levelsOn s N := by
          apply List.mem_filter.mpr
          refine ⟨(List.mem_filter.mp hj).1, ?_⟩
          have hs : ρ.sideAt j = s := hjP.1.trans ((hSideρ J hJ).trans hJs)
          simp [hs]; omega
        have hh := hOnly j hjN p hp
        omega
      have hh := ctx_nested_boundary_markers_rank_budget ρ hPosρ N J x q hN hJ hJN hXP hQ
        (by rw [hSideρ J hJ, hSideρ N hN, hJs, hNs]) direction direction
        hOuter hOuterYoung (by intro p hp; rw [hChildρ] at hp; exact hBoundary p hp) hInnerYoung
        t (by rw [hSideρ N hN, hNs]; exact hne)
        (by rw [hSideρ N hN, hNs]; exact hglobal) 0 0
        (by intro p hp; exact Nat.zero_le _) (by intro p hp; exact Nat.zero_le _)
      have hFull : (group c).bound ≤ ρ.bound := hp.2.2.2.2.2.2
      exact hFull.trans hh.2
    have hXY : x ≠ y := by
      intro he
      subst y
      have hx' := (List.mem_filter.mp hx).2
      have hy' := (List.mem_filter.mp hy).2
      cases hh : σ.letterAt x <;> simp [hh] at hx' hy'
      omega
    have hSum : (group 0).bound + (group 1).bound ≤ w + 1 := by
      by_cases hxy : x < y
      · have hu := ctx_three_ordered_markers_exterior_unit_bound (group 0) (hPos 0) s J N M a x y
          hJ hN hM hJN hNM ((hSide 0 J hJ).trans hJs) ((hSide 0 N hN).trans hNs)
          ((hSide 0 M hM).trans hMs) (hA 0) (hX 0) (hY 0) hglobal
          (Or.inl ⟨hax, hxy, hLeftChild⟩)
        have hl := hLinear 1 b hb false hRightChild hxb
        omega
      · have hyx : y < x := by omega
        have hu := ctx_three_ordered_markers_exterior_unit_bound (group 1) (hPos 1) s J N M b x y
          hJ hN hM hJN hNM ((hSide 1 J hJ).trans hJs) ((hSide 1 N hN).trans hNs)
          ((hSide 1 M hM).trans hMs) (hB 1) (hX 1) (hY 1) hglobal
          (Or.inr ⟨hyx, hxb, hRightChild⟩)
        have hl := hLinear 0 a ha true hLeftChild hax
        omega
    have hDecomp := ctx_bound_le_sum_run_group_prunings_capacity_three σ hpositive color ({0, 1} : Finset ℕ)
      hCover hSmall hColor
    change (∀ fuel, boundFuel fuel σ ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
      σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hDecomp
    have hBudget : ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) ≤ w + 1 := by simpa using hSum
    exact ⟨fun fuel => (hDecomp.1 fuel).trans hBudget, hDecomp.2.trans hBudget⟩

  have ctx_surrounded_older_marker_endpoint_complement_width_bound (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t) (J N M a b x y : ℕ)
    (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels)
    (hJN : J < N) (hNM : N < M)
    (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
    (ha : a ∈ σ.extPositions J) (hb : b ∈ σ.extPositions J)
    (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
    (hay : a < y) (hyb : y < b)
    (houtside : ∀ p ∈ σ.childPositions, p < a ∨ b < p)
    (hBeforeN : ∀ j ∈ σ.levelsOn s N, ∀ p ∈ σ.extPositions j, j = J)
    (hBeforeM : ∀ j ∈ σ.levelsOn s M, ∀ p ∈ σ.extPositions j, j = J ∨ (j = N ∧ p = x))
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (endpoint : Bool)
    (hEnd : ∀ p ∈ σ.childPositions, if endpoint then p < a else b < p) :
    let w := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ w) ∧ σ.bound ≤ w := by
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
    let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
    let color (p : ℕ) := if p < y then (0 : ℕ) else 1
    let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
    let group (c : ℕ) : Context := { σ with
      word := (List.range σ.word.length).map (fun p => match (generalizing := false) σ.letterAt p with
        | Letter.child => if p ∈ support c then Letter.child else Letter.ext (σ.maxima.length + 1) Side.lower
        | Letter.ext j v => Letter.ext j v) }
    change (∀ fuel, boundFuel fuel σ ≤ w) ∧
      σ.bound ≤ w
    have hNe (p : ℕ) (hp : p ∈ σ.childPositions) : p ≠ y := by
      intro he
      subst p
      have hc := of_decide_eq_true (List.mem_filter.mp hp).2
      have he := (List.mem_filter.mp hy).2
      simp [hc] at he
    have hNOn : M ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hM, by simp [hMs]⟩
    have hSmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3 := by
      intro p hp
      have hn := hNe p hp
      by_cases hpx : p < y
      · have he := hOneRight σ s M p y hNOn hy hpx
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
      · have he := hOneLeft σ s M p y hNOn hy (by omega)
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
    have hCover : ∀ p ∈ σ.childPositions, color p ∈ ({0, 1} : Finset ℕ) := by
      intro p hp
      dsimp only [color]
      split_ifs <;> simp
    have hColor : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions, p ≤ q →
        (∀ z, p ≤ z → z ≤ q → z ∈ σ.childPositions) → color p = color q := by
      intro p hp q hq hpq hbetween
      have hside : (p < y) = (q < y) := by
        apply propext
        constructor
        · intro hpx
          by_contra hqx
          have hxc := hbetween y (by omega) (by omega)
          exact hNe y hxc rfl
        · omega
      simp only [color, hside]
    have hPos (c : ℕ) : ∀ p j v, (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
      (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).1
    have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔ p ∈ σ.childPositions ∧ color p = c := by
      have hh : (group c).childPositions = σ.childPositions.filter (· ∈ support c) :=
        (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.1
      rw [hh]
      simp [support]
    have hHist (c j : ℕ) (hj : j ∈ σ.levels) :
        (group c).extPositions j = σ.extPositions j ∧ (group c).sideAt j = σ.sideAt j :=
      (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.1 j hj
    have hLevels (c : ℕ) (v : Side) (top : ℕ) : (group c).levelsOn v top = σ.levelsOn v top :=
      (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.1 v top
    have hA (c : ℕ) : a ∈ (group c).extPositions J := by rw [(hHist c J hJ).1]; exact ha
    have hB (c : ℕ) : b ∈ (group c).extPositions J := by rw [(hHist c J hJ).1]; exact hb
    have hX (c : ℕ) : x ∈ (group c).extPositions N := by rw [(hHist c N hN).1]; exact hx
    have hY (c : ℕ) : y ∈ (group c).extPositions M := by rw [(hHist c M hM).1]; exact hy
    have hSide (c j : ℕ) (hj : j ∈ σ.levels) : (group c).sideAt j = σ.sideAt j := (hHist c j hj).2
    have h0 (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < y := by
      have hh := ((hChild 0 p).mp hp).2
      dsimp only [color] at hh
      split_ifs at hh <;> omega
    have h1 (p : ℕ) (hp : p ∈ (group 1).childPositions) : y < p := by
      have hh := ((hChild 1 p).mp hp).2
      have hn := hNe p ((hChild 1 p).mp hp).1
      dsimp only [color] at hh
      split_ifs at hh <;> omega
    have hLeftChild (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < a := by
      have hh := h0 p hp
      have ho := houtside p ((hChild 0 p).mp hp).1
      omega
    have hRightChild (p : ℕ) (hp : p ∈ (group 1).childPositions) : b < p := by
      have hh := h1 p hp
      have ho := houtside p ((hChild 1 p).mp hp).1
      omega
    have hLinear (c q L z : ℕ) (hq : q ∈ σ.extPositions J)
        (hL : L ∈ σ.levels) (hJL : J < L) (hLs : σ.sideAt L = s) (hz : z ∈ σ.extPositions L)
        (direction : Bool)
        (hBoundary : ∀ p ∈ (group c).childPositions, if direction then p < q else q < p)
        (hqz : if direction then q < z else z < q)
        (hHistory : ∀ j ∈ σ.levelsOn s L, ∀ p ∈ σ.extPositions j,
          j = J ∨ (if direction then p < z else z < p)) : (group c).bound ≤ w := by
      let ρ : Context := { group c with word := (List.range (group c).word.length).map (fun p =>
        match (generalizing := false) (group c).letterAt p with
        | Letter.child => Letter.child
        | Letter.ext j v => if j = J then
            if p ∈ [q] then Letter.ext J ((group c).sideAt J)
              else Letter.ext ((group c).maxima.length + 1) v
            else Letter.ext j v) }
      have hqG : q ∈ (group c).extPositions J := by rw [(hHist c J hJ).1]; exact hq
      have hp := ctx_single_level_occurrence_prune_bound_mono (group c) (hPos c) J hJ [q] q hqG (by simp)
      have hPosρ : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j := hp.1
      have hChildρ : ρ.childPositions = (group c).childPositions := hp.2.1
      have hHistρ : ∀ j ∈ σ.levels, ρ.sideAt j = (group c).sideAt j ∧
          ρ.maximumAt j = (group c).maximumAt j ∧
          ρ.extPositions j = if j = J then ((group c).extPositions j).filter (· ∈ [q])
            else (group c).extPositions j := hp.2.2.1
      have hSideρ (j : ℕ) (hj : j ∈ σ.levels) : ρ.sideAt j = σ.sideAt j :=
        (hHistρ j hj).1.trans (hSide c j hj)
      have hQ : q ∈ ρ.extPositions J := by
        rw [(hHistρ J hJ).2.2, if_pos rfl]
        simp [hqG]
      have hZP : z ∈ ρ.extPositions L := by
        rw [(hHistρ L hL).2.2, if_neg (show L ≠ J by omega), (hHist c L hL).1]
        exact hz
      have hOld (j : ℕ) (hj : j ∈ σ.levels) (p : ℕ) (hp : p ∈ ρ.extPositions j) :
          p ∈ σ.extPositions j := by
        rw [(hHistρ j hj).2.2] at hp
        rw [← (hHist c j hj).1]
        by_cases hjJ : j = J
        · rw [if_pos hjJ] at hp
          exact (List.mem_filter.mp hp).1
        · simpa only [if_neg hjJ] using hp
      have hMemOld (j top : ℕ) (hj : j ∈ ρ.levelsOn s top) : j ∈ σ.levelsOn s top := by
        have hjL : j ∈ σ.levels := (List.mem_filter.mp hj).1
        have hjP := of_decide_eq_true (List.mem_filter.mp hj).2
        apply List.mem_filter.mpr
        refine ⟨hjL, ?_⟩
        have hs : σ.sideAt j = s := (hSideρ j hjL).symm.trans hjP.1
        simp [hs, hjP.2]
      have hOuter : ∀ p ∈ ρ.childPositions, if direction then p < z else z < p := by
        intro p hp
        rw [hChildρ] at hp
        have hh := hBoundary p hp
        cases direction
        · change z < p
          have hqp : q < p := hh
          have hxq : z < q := hqz
          omega
        · change p < z
          have hpq : p < q := hh
          have hqx' : q < z := hqz
          omega
      have hOuterYoung : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
          if direction then p < z else z < p := by
        intro j hj p hp
        rw [hSideρ L hL, hLs] at hj
        have hjL : j ∈ σ.levels := (List.mem_filter.mp hj).1
        rcases hHistory j (hMemOld j L hj) p (hOld j hjL p hp) with hjJ | hpos
        · rw [(hHistρ j hjL).2.2, if_pos hjJ] at hp
          have hpq := List.mem_singleton.mp (of_decide_eq_true (List.mem_filter.mp hp).2)
          rw [hpq]
          exact hqz
        · exact hpos
      have hInnerYoung : ∀ j ∈ ρ.levelsOn (ρ.sideAt J) J, ∀ p ∈ ρ.extPositions j,
          if direction then p < q else q < p := by
        intro j hj p hp
        have hjP := of_decide_eq_true (List.mem_filter.mp hj).2
        have hJpos := one_le_of_mem_levels hJ
        have hjN : j ∈ ρ.levelsOn s N := by
          apply List.mem_filter.mpr
          refine ⟨(List.mem_filter.mp hj).1, ?_⟩
          have hs : ρ.sideAt j = s := hjP.1.trans ((hSideρ J hJ).trans hJs)
          simp [hs]; omega
        have hh := hBeforeN j (hMemOld j N hjN) p (hOld j (List.mem_filter.mp hjN).1 p hp)
        omega
      have hh := ctx_nested_boundary_markers_rank_budget ρ hPosρ L J z q hL hJ hJL hZP hQ
        (by rw [hSideρ J hJ, hSideρ L hL, hJs, hLs]) direction direction
        hOuter hOuterYoung (by intro p hp; rw [hChildρ] at hp; exact hBoundary p hp) hInnerYoung
        t (by rw [hSideρ L hL, hLs]; exact hne)
        (by rw [hSideρ L hL, hLs]; exact hglobal) 0 0
        (by intro p hp; exact Nat.zero_le _) (by intro p hp; exact Nat.zero_le _)
      have hFull : (group c).bound ≤ ρ.bound := hp.2.2.2.2.2.2
      exact hFull.trans hh.2
    have hXY : x ≠ y := by
      intro he
      subst y
      have hx' := (List.mem_filter.mp hx).2
      have hy' := (List.mem_filter.mp hy).2
      cases hh : σ.letterAt x <;> simp [hh] at hx' hy'
      omega
    have hEmpty (c : ℕ) (hNo : ∀ p ∈ (group c).childPositions, False) : (group c).bound = 0 := by
      have he : (group c).childPositions = [] := List.eq_nil_iff_forall_not_mem.mpr hNo
      simp [bound, he, boundFuel, base, blocks]
    have hZero : (group 0).bound = 0 ∨ (group 1).bound = 0 := by
      cases hd : endpoint
      · left
        apply hEmpty 0
        intro p hp
        have hpY := h0 p hp
        have hbP : b < p := by simpa [hd] using hEnd p ((hChild 0 p).mp hp).1
        omega
      · right
        apply hEmpty 1
        intro p hp
        have hyP := h1 p hp
        have hpA : p < a := by simpa [hd] using hEnd p ((hChild 1 p).mp hp).1
        omega
    have hSum : (group 0).bound + (group 1).bound ≤ w := by
      by_cases hxy : x < y
      · have hLeft := hLinear 0 a M y ha hM (by omega) hMs hy true hLeftChild hay
          (by
            intro j hj p hp
            rcases hBeforeM j hj p hp with hjJ | ⟨_, hpx⟩
            · exact Or.inl hjJ
            · right; change p < y; omega)
        have hRight := hLinear 1 b N x hb hN hJN hNs hx false hRightChild
          (by change x < b; omega) (by intro j hj p hp; exact Or.inl (hBeforeN j hj p hp))
        rcases hZero with hz | hz <;> omega
      · have hyx : y < x := by omega
        have hLeft := hLinear 0 a N x ha hN hJN hNs hx true hLeftChild
          (by change a < x; omega) (by intro j hj p hp; exact Or.inl (hBeforeN j hj p hp))
        have hRight := hLinear 1 b M y hb hM (by omega) hMs hy false hRightChild hyb
          (by
            intro j hj p hp
            rcases hBeforeM j hj p hp with hjJ | ⟨_, hpx⟩
            · exact Or.inl hjJ
            · right; change y < p; omega)
        rcases hZero with hz | hz <;> omega
    have hDecomp := ctx_bound_le_sum_run_group_prunings_capacity_three σ hpositive color ({0, 1} : Finset ℕ)
      hCover hSmall hColor
    change (∀ fuel, boundFuel fuel σ ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
      σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hDecomp
    have hBudget : ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) ≤ w := by simpa using hSum
    exact ⟨fun fuel => (hDecomp.1 fuel).trans hBudget, hDecomp.2.trans hBudget⟩

  have ctx_opposite_endpoint_part_upper_normalize (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (t : Ctx.Side) (hclear : σ.levelsOn t 0 = [])
    (keep : List ℕ) (l m : ℕ)
    (hl : l ∈ σ.childPositions) (hlnot : l ∉ keep)
    (endpoint : Bool)
    (hEnd : ∀ p ∈ keep, if endpoint then l < p else p < l) :
    let κ : Ctx.Context := { σ with
      word := (List.range σ.word.length).map (fun p => match (generalizing := false) σ.letterAt p with
        | Ctx.Letter.child => if p ∈ keep then Ctx.Letter.child
            else Ctx.Letter.ext (σ.maxima.length + 1) t
        | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
    let τ : Ctx.Context := match (generalizing := false) t with
      | Ctx.Side.lower => { κ with u := σ.u - 1 }
      | Ctx.Side.upper => { κ with a := σ.a - 1 }
    (∀ fuel, Ctx.Context.boundFuel fuel (σ.part keep t m) ≤ Ctx.Context.boundFuel fuel τ) ∧
      (σ.part keep t m).bound ≤ τ.bound := by
    classical
    let β := σ.part keep t m
    let κ : Context := { σ with
      word := (List.range σ.word.length).map (fun p => match (generalizing := false) σ.letterAt p with
        | Letter.child => if p ∈ keep then Letter.child else Letter.ext (σ.maxima.length + 1) t
        | Letter.ext j v => Letter.ext j v) }
    let τ : Context := match (generalizing := false) t with
      | Side.lower => { κ with u := σ.u - 1 }
      | Side.upper => { κ with a := σ.a - 1 }
    change (∀ fuel, boundFuel fuel β ≤ boundFuel fuel τ) ∧ β.bound ≤ τ.bound
    have hL : l ∈ β.extPositions 1 := by
      rw [part_extPositions_one hpositive]
      simp [hl, hlnot]
    have hSide : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t m hL
    have hOne : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
    have hPos : ∀ p j v, β.letterAt p = Letter.ext j v → 1 ≤ j := by
      intro p j v hp
      have hpl : p < σ.word.length := by
        by_contra h
        have hh := letterAt_of_length_le β (show β.word.length ≤ p by rw [part_word_length]; omega)
        rw [hh] at hp
        cases hp
      cases he : σ.letterAt p with
      | child =>
        rw [part_letterAt_of_child σ keep t m hpl he] at hp
        split at hp
        · cases hp
        · cases hp; omega
      | ext oldLevel oldSide =>
        rw [part_letterAt_of_ext σ keep t m hpl he] at hp
        cases hp; omega
    have hChildren : ∀ p ∈ β.childPositions, if !endpoint then p < l else l < p := by
      intro p hp
      rw [part_childPositions] at hp
      have hh := hEnd p (of_decide_eq_true (List.mem_filter.mp hp).2)
      cases endpoint <;> simpa using hh
    have hTerminal : ∀ j ∈ β.levelsOn (β.sideAt 1) 0, j ≤ 1 := by
      intro j hj
      rw [hSide, part_levelsOn_self_zero hSide, hclear] at hj
      have hj1 : j = 1 := by simpa using hj
      omega
    let ρ : Context := { β with
      word := β.word.map (fun z => match (generalizing := false) z with
        | Letter.child => Letter.child
        | Letter.ext j v => Letter.ext
            (if j = 1 then β.maxima.length else if 1 < j then j - 1 else j) v)
      maxima := β.maxima.eraseIdx (1 - 1) }
    let υ : Context := match (generalizing := false) β.sideAt 1 with
      | Side.lower => { ρ with u := β.u - 1 }
      | Side.upper => { ρ with a := β.a - 1 }
    have hn := ctx_separating_marker_erase_normalize β hPos 1 l hOne hL (!endpoint) hChildren
      (by simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true])
      (by
        intro j hj hOneJ p hp
        have hh := hTerminal j hj
        omega)
    have hFuel : ∀ fuel, boundFuel fuel β ≤ boundFuel fuel υ := hn.2.2.2.2.2.2.1
    have hFull : β.bound ≤ υ.bound := hn.2.2.2.2.2.2.2
    have hWord : ρ.word = κ.word := by
      change ((List.range σ.word.length).map (fun p => match (generalizing := false) σ.letterAt p with
        | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 t
        | Letter.ext j v => Letter.ext (j + 1) v)).map _ = _
      rw [List.map_map]
      apply List.map_congr_left
      intro p hp
      have hpl : p < σ.word.length := List.mem_range.mp hp
      cases he : σ.letterAt p with
      | child =>
        simp only [Function.comp_apply, he]
        by_cases hpk : p ∈ keep <;> simp [hpk, β, part, κ]
      | ext j v =>
        have hj := hpositive p j v he
        simp [Function.comp_apply, he, show j ≠ 0 by omega, show j + 1 ≠ 1 by omega, show 1 < j + 1 by omega, κ]
    have hRho : ρ = κ := by
      change Context.mk σ.a σ.u σ.k ρ.word σ.maxima = Context.mk σ.a σ.u σ.k κ.word σ.maxima
      rw [hWord]
    have hEq : υ = τ := by
      rw [show υ = (match (generalizing := false) β.sideAt 1 with
        | Side.lower => { ρ with u := β.u - 1 }
        | Side.upper => { ρ with a := β.a - 1 }) from rfl]
      rw [hSide, hRho]
      cases t <;> rfl
    rw [hEq] at hFuel hFull
    exact ⟨hFuel, hFull⟩

  have ctx_two_chosen_levels_small_opposite_triangular_linear_bound (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
    (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
    (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
    (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (hopposite : (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) :
    let w := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (w + 1).choose 2 + w - 1) ∧
      σ.bound ≤ (w + 1).choose 2 + w - 1 := by
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
    let G (v : Side) := match (generalizing := false) v with | Side.lower => σ.u | Side.upper => σ.a
    let w := G t - 1
    change (∀ fuel, boundFuel fuel σ ≤ (w + 1).choose 2 + w - 1) ∧
      σ.bound ≤ (w + 1).choose 2 + w - 1
    have hGs : G s ≤ 5 := hglobal
    have hGt : G t ≤ 4 := hopposite
    have hw : w ≤ 3 := by dsimp only [w]; omega
    by_cases hw3 : w = 3
    swap
    · have hh := ctx_small_opposite_global_marker_square_bound σ hpositive s t hne N x
        hN hNs hx hglobal hopposite
      have hArith (n : ℕ) (hn : n ≤ 2) : n ^ 2 ≤ (n + 1).choose 2 + n - 1 := by
        interval_cases n <;> decide
      have hle := hArith w (by omega)
      exact ⟨fun fuel => (hh.1 fuel).trans hle, hh.2.trans hle⟩
    let active := σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let I (p : ℕ) := Finset.Icc (σ.leftExt s 0 p + 1) (G s - 1 - σ.rightExt s 0 p)
    let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
    let potential := active.biUnion (fun p => Q (I p))
    have hp := ctx_small_global_axis_rank_pair_potential σ hpositive t s (Ne.symm hne) hopposite
    change (∀ fuel, boundFuel fuel σ ≤ potential.card) ∧ σ.bound ≤ potential.card at hp
    have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
    have hCount : potential.card ≤ 8 := by
      rcases ctx_chain_one_children_exterior_of_two_levels σ s N M x y
        hN hM hNM hNs hMs hx hy with h | h
      · have hSub : potential ⊆ Q (Finset.Icc 2 4) ∪ Q (Finset.Icc 1 2) := by
          intro z hz
          obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
          have hc : p ∈ σ.childPositions := List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
          obtain ⟨hz, ho⟩ := Finset.mem_filter.mp hz
          obtain ⟨h1, h2⟩ := Finset.mem_product.mp hz
          have hz1 := Finset.mem_Icc.mp h1
          have hz2 := Finset.mem_Icc.mp h2
          have hCases : 1 ≤ σ.leftExt s 0 p ∨ 2 ≤ σ.rightExt s 0 p := by
            by_cases hl : 1 ≤ σ.leftExt s 0 p
            · exact Or.inl hl
            · right
              have hchain : 2 ≤ σ.chainExt s p p := by
                by_contra hh
                have hxp := h.2 p hc (by omega) N hNOn x hx
                have hL := hOneLeft σ s N p x hNOn hx hxp
                omega
              dsimp only [chainExt] at hchain
              omega
          rcases hCases with hL | hR
          · apply Finset.mem_union_left
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ho⟩ <;> apply Finset.mem_Icc.mpr <;> omega
          · apply Finset.mem_union_right
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ho⟩ <;> apply Finset.mem_Icc.mpr <;> omega
        have hCard : (Q (Finset.Icc 2 4) ∪ Q (Finset.Icc 1 2)).card = 8 := by decide
        rw [← hCard]
        exact Finset.card_le_card hSub
      · have hSub : potential ⊆ Q (Finset.Icc 1 3) ∪ Q (Finset.Icc 3 4) := by
          intro z hz
          obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
          have hc : p ∈ σ.childPositions := List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
          obtain ⟨hz, ho⟩ := Finset.mem_filter.mp hz
          obtain ⟨h1, h2⟩ := Finset.mem_product.mp hz
          have hz1 := Finset.mem_Icc.mp h1
          have hz2 := Finset.mem_Icc.mp h2
          have hCases : 1 ≤ σ.rightExt s 0 p ∨ 2 ≤ σ.leftExt s 0 p := by
            by_cases hr : 1 ≤ σ.rightExt s 0 p
            · exact Or.inl hr
            · right
              have hchain : 2 ≤ σ.chainExt s p p := by
                by_contra hh
                have hpx := h.2 p hc (by omega) N hNOn x hx
                have hR := hOneRight σ s N p x hNOn hx hpx
                omega
              dsimp only [chainExt] at hchain
              omega
          rcases hCases with hR | hL
          · apply Finset.mem_union_left
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ho⟩ <;> apply Finset.mem_Icc.mpr <;> omega
          · apply Finset.mem_union_right
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ho⟩ <;> apply Finset.mem_Icc.mpr <;> omega
        have hCard : (Q (Finset.Icc 1 3) ∪ Q (Finset.Icc 3 4)).card = 8 := by decide
        rw [← hCard]
        exact Finset.card_le_card hSub
    have hBudget : (w + 1).choose 2 + w - 1 = 8 := by rw [hw3]; decide
    rw [hBudget]
    exact ⟨fun fuel => (hp.1 fuel).trans hCount, hp.2.trans hCount⟩

  have ctx_active_zero_maxima_upper_normalize (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (hsmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3) :
    let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
      (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    let keep := σ.childPositions.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let τ : Ctx.Context := { σ with
      word := (List.range σ.word.length).map (fun p => match (generalizing := false) σ.letterAt p with
        | Ctx.Letter.child => if p ∈ keep then Ctx.Letter.child
            else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
        | Ctx.Letter.ext j v => Ctx.Letter.ext j v)
      maxima := List.replicate σ.maxima.length 0 }
    (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
      τ.childPositions = keep ∧
      (∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p) ∧
      active τ = active σ ∧
      (∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧
        τ.sideAt j = σ.sideAt j ∧ τ.maximumAt j = 0) ∧
      (∀ s top p, τ.leftExt s top p = σ.leftExt s top p ∧
        τ.rightExt s top p = σ.rightExt s top p) ∧
      (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
      (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ τ.bound) ∧ σ.bound ≤ τ.bound := by
    classical
    let active (υ : Context) := υ.childPositions.toFinset.filter
      (fun p => 0 < υ.cupLimit p p ∧ 0 < υ.capLimit p p)
    let keep := σ.childPositions.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let ρ : Context := { σ with
      word := (List.range σ.word.length).map (fun p => match (generalizing := false) σ.letterAt p with
        | Letter.child => if p ∈ keep then Letter.child else Letter.ext (σ.maxima.length + 1) Side.lower
        | Letter.ext j v => Letter.ext j v) }
    let τ : Context := { ρ with maxima := List.replicate σ.maxima.length 0 }
    change (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
      τ.childPositions = keep ∧
      (∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p) ∧
      active τ = active σ ∧
      (∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧
        τ.sideAt j = σ.sideAt j ∧ τ.maximumAt j = 0) ∧
      (∀ s top p, τ.leftExt s top p = σ.leftExt s top p ∧
        τ.rightExt s top p = σ.rightExt s top p) ∧
      (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
      (∀ fuel, boundFuel fuel σ ≤ τ.bound) ∧ σ.bound ≤ τ.bound
    have hp := ctx_part_pruning_history_transport σ hpositive keep Side.lower 0
    have hρPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j := hp.1
    have hρChild : ρ.childPositions = σ.childPositions.filter (· ∈ keep) := hp.2.1
    have hρHistory : ∀ j ∈ σ.levels, ρ.extPositions j = σ.extPositions j ∧
        ρ.sideAt j = σ.sideAt j := hp.2.2.1
    have hρPure : ∀ s top p, ρ.leftExt s top p = σ.leftExt s top p ∧
        ρ.rightExt s top p = σ.rightExt s top p := hp.2.2.2.2.1
    have hρLimits : ∀ p q, ρ.cupLimit p q = σ.cupLimit p q ∧
        ρ.capLimit p q = σ.capLimit p q := hp.2.2.2.2.2.1
    have hPos : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := hρPos
    have hDepth : ρ.maxima.length = τ.maxima.length := by simp [τ, ρ]
    have hτLevels : τ.levels = ρ.levels := by simp only [levels, ← hDepth]
    have hτLevelsOn (s : Side) (top : ℕ) : τ.levelsOn s top = ρ.levelsOn s top := by
      simp only [levelsOn, hτLevels]
      rfl
    have hZero (j : ℕ) : τ.maximumAt j = 0 := by
      simp only [maximumAt, τ, List.getElem?_replicate]
      split_ifs <;> rfl
    have hComparison := ctx_bound_mono_of_marker_inclusion ρ τ hρPos hPos
      le_rfl le_rfl rfl rfl (fun _ => Iff.rfl) hDepth
      (fun j _ => ⟨rfl, fun _ h => h, by rw [hZero]; exact Nat.zero_le _⟩)
    have hLimits (p q : ℕ) : σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q := by
      rw [← (hρLimits p q).1, ← (hρLimits p q).2]
      exact hComparison.1 p q
    have hChild : τ.childPositions = keep := by
      change ρ.childPositions = keep
      rw [hρChild]
      apply List.filter_congr
      intro p hp
      simp [keep, hp]
    have hAllActive : ∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := by
      intro p hp
      rw [hChild] at hp
      have ha : 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p :=
        of_decide_eq_true (List.mem_filter.mp hp).2
      exact ⟨lt_of_lt_of_le ha.1 (hLimits p p).1, lt_of_lt_of_le ha.2 (hLimits p p).2⟩
    have hActive : active τ = active σ := by
      ext p
      simp only [active, Finset.mem_filter, List.mem_toFinset]
      constructor
      · intro hp
        rw [hChild] at hp
        exact ⟨(List.mem_filter.mp hp.1).1, of_decide_eq_true (List.mem_filter.mp hp.1).2⟩
      · intro hp
        have hm : p ∈ τ.childPositions := by rw [hChild]; simp [keep, hp.1, hp.2]
        exact ⟨hm, hAllActive p hm⟩
    have hPure (s : Side) (top p : ℕ) : τ.leftExt s top p = σ.leftExt s top p ∧
        τ.rightExt s top p = σ.rightExt s top p := by
      have ht : τ.leftExt s top p = ρ.leftExt s top p ∧
          τ.rightExt s top p = ρ.rightExt s top p := by
        simp only [leftExt_eq, rightExt_eq, hτLevelsOn]
        exact ⟨rfl, rfl⟩
      exact ⟨ht.1.trans (hρPure s top p).1, ht.2.trans (hρPure s top p).2⟩
    have hPrune := ctx_bound_le_inactive_prune_capacity_three σ hpositive hsmall
    change (∀ fuel, boundFuel fuel σ ≤ ρ.bound) ∧ σ.bound ≤ ρ.bound at hPrune
    refine ⟨hPos, hChild, hAllActive, hActive, ?_, hPure, hLimits,
      fun fuel => (hPrune.1 fuel).trans hComparison.2.2, hPrune.2.trans hComparison.2.2⟩
    intro j hj
    exact ⟨(hρHistory j hj).1, (hρHistory j hj).2, hZero j⟩

  have ctx_two_chosen_markers_bound_of_bounded_bare_two_marker_potential (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
    (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
    (hsides : ∀ j ∈ σ.levels, σ.sideAt j = s)
    (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
    (hother : ∀ j ∈ σ.levels, j ≠ N → ∀ p ∈ σ.extPositions j, p = y)
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (hwidth : 4 ≤ (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
    (htwo : ∀ (ρ : Ctx.Context) (J K a b : ℕ),
      (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
      (∀ j ∈ ρ.levels, ρ.maximumAt j = 0) →
      (∀ j ∈ ρ.levels, ρ.sideAt j = s) →
      J ∈ ρ.levels → K ∈ ρ.levels → J < K →
      a ∈ ρ.extPositions J → b ∈ ρ.extPositions K →
      (∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = a ∨ p = b) →
      (match (generalizing := false) s with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) ≤ 5 →
      (∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) →
      let w := (match (generalizing := false) t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1
      w ≤ (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 →
      4 ≤ w → ρ.bound ≤ (w + 1).choose 2 + w - 1) :
    let w := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (w + 1).choose 2 + w - 1) ∧
      σ.bound ≤ (w + 1).choose 2 + w - 1 := by
    classical
    let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
    let τ : Context := { σ with word := (List.range σ.word.length).map (fun p =>
      match (generalizing := false) σ.letterAt p with
      | Letter.child => Letter.child
      | Letter.ext j v => if j = N then
          if p ∈ [x] then Letter.ext N (σ.sideAt N) else Letter.ext (σ.maxima.length + 1) v
          else Letter.ext j v) }
    change (∀ fuel, boundFuel fuel σ ≤ (w + 1).choose 2 + w - 1) ∧
      σ.bound ≤ (w + 1).choose 2 + w - 1
    have hp := ctx_single_level_occurrence_prune_bound_mono σ hpositive N hN [x] x hx (by simp)
    have hPosτ : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := hp.1
    have hHistτ : ∀ j ∈ σ.levels, τ.sideAt j = σ.sideAt j ∧ τ.maximumAt j = σ.maximumAt j ∧
        τ.extPositions j = if j = N then (σ.extPositions j).filter (· ∈ [x]) else σ.extPositions j :=
      hp.2.2.1
    have hSidesτ : ∀ j ∈ τ.levels, τ.sideAt j = s := by
      intro j hj
      exact ((hHistτ j hj).1).trans (hsides j hj)
    have hXτ : x ∈ τ.extPositions N := by
      rw [(hHistτ N hN).2.2, if_pos rfl]
      simp [hx]
    have hYτ : y ∈ τ.extPositions M := by
      rw [(hHistτ M hM).2.2, if_neg (show M ≠ N by omega)]
      exact hy
    have hOnlyτ : ∀ j ∈ τ.levels, ∀ p ∈ τ.extPositions j, p = x ∨ p = y := by
      intro j hj p hp
      rw [(hHistτ j hj).2.2] at hp
      by_cases hjN : j = N
      · rw [if_pos hjN] at hp
        have hm := of_decide_eq_true (List.mem_filter.mp hp).2
        exact Or.inl (List.mem_singleton.mp hm)
      · rw [if_neg hjN] at hp
        exact Or.inr (hother j hj hjN p hp)
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
    have hNOnτ : N ∈ τ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hSidesτ N hN]⟩
    have hNeτ (p : ℕ) (hp : p ∈ τ.childPositions) : p ≠ x := by
      intro he
      subst p
      have hc := of_decide_eq_true (List.mem_filter.mp hp).2
      have he := (List.mem_filter.mp hXτ).2
      simp [hc] at he
    have hSmallτ : ∀ p ∈ τ.childPositions, min (τ.cupLimit p p) (τ.capLimit p p) ≤ 3 := by
      intro p hp
      have hn := hNeτ p hp
      have hg : (match (generalizing := false) s with | Side.lower => τ.u | Side.upper => τ.a) ≤ 5 := hglobal
      by_cases hpx : p < x
      · have he := hOneRight τ s N p x hNOnτ hXτ hpx
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hg ⊢ <;> omega
      · have he := hOneLeft τ s N p x hNOnτ hXτ (by omega)
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hg ⊢ <;> omega
    let live := τ.childPositions.filter (fun p => 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p)
    let ρ : Context := { τ with
      word := (List.range τ.word.length).map (fun p => match (generalizing := false) τ.letterAt p with
        | Letter.child => if p ∈ live then Letter.child else Letter.ext (τ.maxima.length + 1) Side.lower
        | Letter.ext j v => Letter.ext j v)
      maxima := List.replicate τ.maxima.length 0 }
    have hz := ctx_active_zero_maxima_upper_normalize τ hPosτ hSmallτ
    have hPosρ : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j := hz.1
    have hActiveρ : ∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := hz.2.2.1
    have hHistρ : ∀ j ∈ τ.levels, ρ.extPositions j = τ.extPositions j ∧
        ρ.sideAt j = τ.sideAt j ∧ ρ.maximumAt j = 0 := hz.2.2.2.2.1
    have hDepth : τ.maxima.length = ρ.maxima.length := by simp [ρ]
    have hLevels : ρ.levels = τ.levels := by simp only [levels, ← hDepth]
    have hNρ : N ∈ ρ.levels := by rw [hLevels]; exact hN
    have hMρ : M ∈ ρ.levels := by rw [hLevels]; exact hM
    have hZeroρ : ∀ j ∈ ρ.levels, ρ.maximumAt j = 0 := by
      intro j hj
      rw [hLevels] at hj
      exact (hHistρ j hj).2.2
    have hSidesρ : ∀ j ∈ ρ.levels, ρ.sideAt j = s := by
      intro j hj
      rw [hLevels] at hj
      exact (hHistρ j hj).2.1.trans (hSidesτ j hj)
    have hXρ : x ∈ ρ.extPositions N := by rw [(hHistρ N hN).1]; exact hXτ
    have hYρ : y ∈ ρ.extPositions M := by rw [(hHistρ M hM).1]; exact hYτ
    have hOnlyρ : ∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = x ∨ p = y := by
      intro j hj p hp
      rw [hLevels] at hj
      rw [(hHistρ j hj).1] at hp
      exact hOnlyτ j hj p hp
    have hFinal : ρ.bound ≤ (w + 1).choose 2 + w - 1 :=
      htwo ρ N M x y hPosρ hZeroρ hSidesρ hNρ hMρ hNM hXρ hYρ hOnlyρ hglobal hActiveρ le_rfl hwidth
    have hFuelPrune : ∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ := hp.2.2.2.2.2.1
    have hFullPrune : σ.bound ≤ τ.bound := hp.2.2.2.2.2.2
    have hFuelZero : ∀ fuel, boundFuel fuel τ ≤ ρ.bound := hz.2.2.2.2.2.2.2.1
    have hFullZero : τ.bound ≤ ρ.bound := hz.2.2.2.2.2.2.2.2
    exact ⟨fun fuel => (hFuelPrune fuel).trans ((hFuelZero fuel).trans hFinal),
      hFullPrune.trans (hFullZero.trans hFinal)⟩

  classical
  let w := (match (generalizing := false) t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  let β := σ.part keep t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ (w + 1).choose 2 + w - 1) ∧ α.bound + β.bound ≤ (w + 1).choose 2 + w - 1
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ rest := by
    simp only [α, part_childPositions, rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hChildβ (p : ℕ) : p ∈ β.childPositions ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [β, part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ rest := by
    rw [part_extPositions_one hpositive]
  have hAα : a ∈ α.extPositions 1 := (hExtα a).mpr ⟨hkeep a ha, ha⟩
  have hLβ : l ∈ β.extPositions 1 := (hExtβ l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
  have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive rest s m hAα
  have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t n hLβ
  have hPositivePart (ks : List ℕ) (v : Side) (a : ℕ) :
      ∀ p j z, (σ.part ks v a).letterAt p = Letter.ext j z → 1 ≤ j := by
    intro p j z hp
    have hpl : p < σ.word.length := by
      by_contra h
      have hh := letterAt_of_length_le (σ.part ks v a)
        (show (σ.part ks v a).word.length ≤ p by rw [part_word_length]; omega)
      rw [hh] at hp
      cases hp
    cases he : σ.letterAt p with
    | child =>
      rw [part_letterAt_of_child σ ks v a hpl he] at hp
      split at hp
      · cases hp
      · cases hp; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ ks v a hpl he] at hp
      cases hp; omega
  have hPosα := hPositivePart rest s m
  have hPosβ := hPositivePart keep t n
  have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
  have hNpos := one_le_of_mem_levels hN
  have hNα : N + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNβ : N + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNsα : α.sideAt (N + 1) = s := (part_sideAt_succ σ rest s m hNpos).trans hNs
  have hNsβ : β.sideAt (N + 1) = s := (part_sideAt_succ σ keep t n hNpos).trans hNs
  have hXα : x ∈ α.extPositions (N + 1) := by rw [part_extPositions_succ σ rest s m hNpos]; exact hx
  have hXβ : x ∈ β.extPositions (N + 1) := by rw [part_extPositions_succ σ keep t n hNpos]; exact hx
  have hLevelsβ : β.levelsOn t 0 = [1] := by
    rw [part_levelsOn_self_zero hSideβ, hclear]
    rfl
  have hw : 2 ≤ w := hwidth
  have hMpos := one_le_of_mem_levels hM
  have hMα : M + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hMβ : M + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hMsα : α.sideAt (M + 1) = s := (part_sideAt_succ σ rest s m hMpos).trans hMs
  have hMsβ : β.sideAt (M + 1) = s := (part_sideAt_succ σ keep t n hMpos).trans hMs
  have hYα : y ∈ α.extPositions (M + 1) := by rw [part_extPositions_succ σ rest s m hMpos]; exact hy
  have hYβ : y ∈ β.extPositions (M + 1) := by rw [part_extPositions_succ σ keep t n hMpos]; exact hy
  have hAtLevel (j i p : ℕ) (hp : p ∈ σ.extPositions j) (hp' : p ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hp).2
    have hi := (List.mem_filter.mp hp').2
    cases hletter : σ.letterAt p <;> simp [hletter] at hj hi
    omega
  have hActual : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j,
      (j = N ∧ p = x) ∨ (j = M ∧ p = y) := by
    intro j hj p hp
    rcases hchosen j hj p hp with hpx | hpy
    · exact Or.inl ⟨hAtLevel j N x (by simpa only [hpx] using hp) hx, hpx⟩
    · exact Or.inr ⟨hAtLevel j M y (by simpa only [hpy] using hp) hy, hpy⟩
  have hBetaActual : ∀ j ∈ β.levelsOn s 0, ∀ p ∈ β.extPositions j,
      (j = N + 1 ∧ p = x) ∨ (j = M + 1 ∧ p = y) := by
    have hs : β.sideAt 1 ≠ s := by rw [hSideβ]; exact Ne.symm hne
    intro j hj p hp
    rw [part_levelsOn_other_zero hs] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [part_extPositions_succ σ keep t n (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
    rcases hActual i hi p hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hBetaBelow (top j : ℕ) (hj : j ∈ β.levelsOn s top) :
      j ∈ β.levelsOn s 0 ∧ (top = 0 ∨ j < top) := by
    have hh := List.mem_filter.mp hj
    have hp := of_decide_eq_true hh.2
    exact ⟨List.mem_filter.mpr ⟨hh.1, by simp [hp.1]⟩, hp.2⟩
  have hAlphaActual : ∀ j ∈ α.levelsOn s 0, ∀ p ∈ α.extPositions j,
      (j = 1 ∧ p ∈ keep) ∨ (j = N + 1 ∧ p = x) ∨ (j = M + 1 ∧ p = y) := by
    intro j hj p hp
    rw [part_levelsOn_self_zero hSideα] at hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact Or.inl ⟨rfl, ((hExtα p).mp hp).2⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      rw [part_extPositions_succ σ rest s m (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
      rcases hActual i hi p hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  have hAlphaBelow (top j : ℕ) (hj : j ∈ α.levelsOn s top) :
      j ∈ α.levelsOn s 0 ∧ (top = 0 ∨ j < top) := by
    have hh := List.mem_filter.mp hj
    have hp := of_decide_eq_true hh.2
    exact ⟨List.mem_filter.mpr ⟨hh.1, by simp [hp.1]⟩, hp.2⟩
  have hBα : b ∈ α.extPositions 1 := (hExtα b).mpr ⟨hkeep b hb, hb⟩
  have hEndα : ∀ p ∈ α.childPositions, if endpoint then p < a else b < p := by
    intro p hp
    have hh := (hRest p).mp ((hChildα p).mp hp)
    cases hd : endpoint
    · simpa [hd] using hendpoint b hb p hh.1 hh.2
    · simpa [hd] using hendpoint a ha p hh.1 hh.2
  have hOutside : ∀ p ∈ α.childPositions, p < a ∨ b < p := by
    intro p hp
    have hh := hEndα p hp
    cases endpoint
    · exact Or.inr hh
    · exact Or.inl hh
  have hBeforeN : ∀ j ∈ α.levelsOn s (N + 1), ∀ p ∈ α.extPositions j, j = 1 := by
    intro j hj p hp
    have hj' := hAlphaBelow (N + 1) j hj
    rcases hAlphaActual j hj'.1 p hp with ⟨hj1, _⟩ | ⟨hjN, _⟩ | ⟨hjM, _⟩
    · exact hj1
    · omega
    · omega
  have hBeforeM : ∀ j ∈ α.levelsOn s (M + 1), ∀ p ∈ α.extPositions j,
      j = 1 ∨ (j = N + 1 ∧ p = x) := by
    intro j hj p hp
    have hj' := hAlphaBelow (M + 1) j hj
    rcases hAlphaActual j hj'.1 p hp with ⟨hj1, _⟩ | ⟨hjN, hpx⟩ | ⟨hjM, _⟩
    · exact Or.inl hj1
    · exact Or.inr ⟨hjN, hpx⟩
    · omega
  have hOwn : (∀ fuel, boundFuel fuel α ≤ w + 1) ∧ α.bound ≤ w + 1 := by
    rcases hsurround with ⟨hax, hxb⟩ | ⟨hay, hyb⟩
    · exact ctx_surrounded_younger_marker_complement_width_plus_one_bound α hPosα s t hne
        1 (N + 1) (M + 1) a b x y hOneα hNα hMα (by omega) (by omega)
        hSideα hNsα hMsα hAα hBα hXα hYα hax hxb hOutside hBeforeN hglobal
    · have hh := ctx_surrounded_older_marker_endpoint_complement_width_bound α hPosα s t hne
        1 (N + 1) (M + 1) a b x y hOneα hNα hMα (by omega) (by omega)
        hSideα hNsα hMsα hAα hBα hXα hYα hay hyb hOutside hBeforeN hBeforeM hglobal endpoint hEndα
      exact ⟨fun fuel => (hh.1 fuel).trans (Nat.le_succ _), hh.2.trans (Nat.le_succ _)⟩
  let κ : Context := { σ with
    word := (List.range σ.word.length).map (fun p => match (generalizing := false) σ.letterAt p with
      | Letter.child => if p ∈ keep then Letter.child else Letter.ext (σ.maxima.length + 1) t
      | Letter.ext j v => Letter.ext j v) }
  let τ : Context := match (generalizing := false) t with
    | Side.lower => { κ with u := σ.u - 1 }
    | Side.upper => { κ with a := σ.a - 1 }
  let v := (match (generalizing := false) t with | Side.lower => τ.u | Side.upper => τ.a) - 1
  have hNorm := ctx_opposite_endpoint_part_upper_normalize σ hpositive t hclear keep l n
    hl hlnot endpoint (by intro p hp; exact hendpoint p hp l hl hlnot)
  have hFuel : ∀ fuel, boundFuel fuel β ≤ boundFuel fuel τ := hNorm.1
  have hFull : β.bound ≤ τ.bound := hNorm.2
  have hTransport := ctx_part_pruning_history_transport σ hpositive keep t n
  have hWord : τ.word = κ.word := by cases t <;> rfl
  have hDepth : τ.maxima = σ.maxima := by cases t <;> rfl
  have hLevel : τ.levels = σ.levels := by simp only [levels, hDepth]
  have hExt (j : ℕ) : τ.extPositions j = κ.extPositions j := by
    simp only [extPositions, letterAt, hWord]
  have hSide (j : ℕ) : τ.sideAt j = κ.sideAt j := by
    simp only [sideAt, hExt, letterAt, hWord]
  have hHist : ∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧ τ.sideAt j = σ.sideAt j := by
    intro j hj
    have hh := hTransport.2.2.1 j hj
    exact ⟨(hExt j).trans hh.1, (hSide j).trans hh.2⟩
  have hPositiveτ : ∀ p j z, τ.letterAt p = Letter.ext j z → 1 ≤ j := by
    intro p j z hp
    have hh : κ.letterAt p = Letter.ext j z := by simpa only [letterAt, hWord] using hp
    exact hTransport.1 p j z hh
  have hChosenGlobal : (match (generalizing := false) s with | Side.lower => τ.u | Side.upper => τ.a) =
      (match (generalizing := false) s with | Side.lower => σ.u | Side.upper => σ.a) := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · rfl
    · rfl
    · exact False.elim (hne rfl)
  have hWidthτ : v ≤ w - 1 := by
    cases t
    · change σ.u - 1 - 1 ≤ σ.u - 1 - 1
      exact le_rfl
    · change σ.a - 1 - 1 ≤ σ.a - 1 - 1
      exact le_rfl
  have hNτ : N ∈ τ.levels := by rw [hLevel]; exact hN
  have hMτ : M ∈ τ.levels := by rw [hLevel]; exact hM
  have hXτ : x ∈ τ.extPositions N := by rw [(hHist N hN).1]; exact hx
  have hYτ : y ∈ τ.extPositions M := by rw [(hHist M hM).1]; exact hy
  have hSides : ∀ j ∈ σ.levels, σ.sideAt j = s := by
    intro j hj
    by_contra hh
    have ht : σ.sideAt j = t := by
      cases hs : σ.sideAt j <;> cases s <;> cases t <;>
        simp only [hs, ne_eq, not_true_eq_false] at hh hne ⊢
    have hjt : j ∈ σ.levelsOn t 0 := List.mem_filter.mpr ⟨hj, by simp [ht]⟩
    rw [hclear] at hjt
    exact List.not_mem_nil hjt
  have hSidesτ : ∀ j ∈ τ.levels, τ.sideAt j = s := by
    intro j hj
    rw [hLevel] at hj
    exact (hHist j hj).2.trans (hSides j hj)
  have hOtherτ : ∀ j ∈ τ.levels, j ≠ N → ∀ p ∈ τ.extPositions j, p = y := by
    intro j hj hjN p hp
    rw [hLevel] at hj
    rw [(hHist j hj).1] at hp
    have hjOn : j ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hj, by simp [hSides j hj]⟩
    rcases hActual j hjOn p hp with ⟨hjN', _⟩ | ⟨_, hpy⟩
    · exact False.elim (hjN hjN')
    · exact hpy
  have hτ : (∀ fuel, boundFuel fuel τ ≤ (v + 1).choose 2 + v - 1) ∧
      τ.bound ≤ (v + 1).choose 2 + v - 1 := by
    by_cases hv : 4 ≤ v
    · apply ctx_two_chosen_markers_bound_of_bounded_bare_two_marker_potential τ hPositiveτ s t hne
        N M x y hNτ hMτ hNM hSidesτ hXτ hYτ hOtherτ
        (by rw [hChosenGlobal]; exact hglobal) hv
      intro ρ J K c d hPos hZero hSidesρ hJ hK hJK hc hd hOnly hG hActive
      dsimp only
      intro hWidth hFour
      exact htwo ρ J K c d hPos hZero hSidesρ hJ hK hJK hc hd hOnly hG hActive
        (hWidth.trans hWidthτ) hFour
    · have hSmall : (match (generalizing := false) t with | Side.lower => τ.u | Side.upper => τ.a) ≤ 4 := by
        dsimp only [v] at hv
        omega
      exact ctx_two_chosen_levels_small_opposite_triangular_linear_bound τ hPositiveτ s t hne
        N M x y hNτ hMτ hNM (hSidesτ N hNτ) (hSidesτ M hMτ) hXτ hYτ
        (by rw [hChosenGlobal]; exact hglobal) hSmall
  have hMono : (v + 1).choose 2 + v - 1 ≤ (w - 1 + 1).choose 2 + (w - 1) - 1 :=
    Nat.sub_le_sub_right (Nat.add_le_add (Nat.choose_le_choose 2 (by omega)) hWidthτ) 1
  have hOther : (∀ fuel, boundFuel fuel β ≤ (w - 1 + 1).choose 2 + (w - 1) - 1) ∧
      β.bound ≤ (w - 1 + 1).choose 2 + (w - 1) - 1 :=
    ⟨fun fuel => (hFuel fuel).trans ((hτ.1 fuel).trans hMono), hFull.trans (hτ.2.trans hMono)⟩
  have hBudget : (w + 1) + ((w - 1 + 1).choose 2 + (w - 1) - 1) ≤
      (w + 1).choose 2 + w - 1 := by
    rw [show w - 1 + 1 = w by omega]
    have hc : (w + 1).choose 2 = w + w.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ w 1
    omega
  exact ⟨fun f g => (Nat.add_le_add (hOwn.1 f) (hOther.1 g)).trans hBudget,
    (Nat.add_le_add hOwn.2 hOther.2).trans hBudget⟩

end ErdosSzekeres
