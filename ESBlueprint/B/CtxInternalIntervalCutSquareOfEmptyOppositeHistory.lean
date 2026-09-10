import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank
import ESBlueprint.B.CtxNonunitChildrenExteriorOfTwoLevels
import ESBlueprint.B.CtxActiveBoundaryMarkerRankPairUnionBound
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsCapacityThree
import ESBlueprint.B.RankPairClippedIntervalUnionMissingCorner
import ESBlueprint.B.CtxActiveTwoBoundaryMarkerRankUnionBound
import ESBlueprint.B.CtxSmallOppositeGlobalMarkerSquareBound

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- An internal interval cut with its kept block on the chosen axis satisfies the opposite-width square budget when the chosen global is at most five, the source has a youngest actual chosen pivot, and its opposite indexed history is empty. The kept support is nonempty and order-convex among source children, with removed witnesses on both sides. Opposite width is at least two; both new maxima and both fuel amounts are arbitrary. Chosen histories/maxima, inactive children and positive unindexed barriers remain allowed. Derives exact complementary rank clips, then combines the chosen linear or unit charge with the complementary width or one-unit saving. Covers the chosen-interval orientation of internal cuts; endpoint cuts and the chosen-complement orientation remain separate. The unit and exact clipped-pair charges are proved as local components. No square estimate is assumed. Only the actual cut theorem is exported.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_internal_interval_cut_square_of_empty_opposite_history (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [])
  (hclear : σ.levelsOn t 0 = [])
  (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
  (keep : List ℕ) (q₀ l r m n : ℕ)
  (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
  (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
  (hlnot : l ∉ keep) (hrnot : r ∉ keep)
  (hinside : ∀ p ∈ keep, l < p ∧ p < r)
  (hconvex : ∀ p ∈ keep, ∀ q ∈ keep, ∀ z ∈ σ.childPositions,
    p ≤ z → z ≤ q → z ∈ keep) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) +
    Ctx.Context.boundFuel g (σ.part rest t n) ≤ w ^ 2) ∧
    (σ.part keep s m).bound + (σ.part rest t n).bound ≤ w ^ 2 := by
  classical
  have ctx_bracketed_older_exterior_marker_unit_bound (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s : Ctx.Side) (N M x y z : ℕ)
    (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
    (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
    (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hz : z ∈ σ.extPositions N)
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (houtside : y < x ∨ z < y)
    (hbracket : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
      x < p ∧ p < z) :
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 1) ∧ σ.bound ≤ 1 := by
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
    have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
    have hMOn : M ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hM, by simp [hMs]⟩
    have hSorted : (σ.levelsOn s 0).Pairwise (· < ·) := by
      apply List.Pairwise.filter
      exact List.pairwise_lt_range.map (fun i ↦ i + 1) (fun i j h ↦ by dsimp; omega)
    have hTwo : [N, M].Sublist (σ.levelsOn s 0) := by
      have hs : [N, M].Pairwise (· < ·) := by simp [hNM]
      have hsub : [N, M] ⊆ σ.levelsOn s 0 := by
        intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hNOn
        · exact hMOn
      have he : (σ.levelsOn s 0).filter (· ∈ [N, M]) = [N, M] := by
        apply (hSorted.filter _).eq_of_mem_iff hs
        intro j
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨And.right, fun hj => ⟨hsub hj, hj⟩⟩
      rw [← he]
      exact List.filter_sublist
    have hSortN : (σ.extPositions N).Pairwise (· ≤ ·) :=
      (List.pairwise_lt_range.filter _).imp le_of_lt
    have hTwoRight (p b : ℕ) (hb : b ∈ σ.extPositions N) (hpx : p < b) (hxy : b < y) : 2 ≤ σ.rightExt s 0 p := by
      have hm : b ∈ (σ.extPositions N).filter (p < ·) := by simp [hb, hpx]
      have hne := List.ne_nil_of_mem hm
      let w := ((σ.extPositions N).filter (p < ·)).head hne
      have hw : ((σ.extPositions N).filter (p < ·)).head? = some w :=
        List.head?_eq_some_head hne
      have hwx : w ≤ b := (hSortN.filter _).rel_head hm
      have hmOld : y ∈ (σ.extPositions M).filter (w < ·) := by
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨hy, by omega⟩
      have hneOld := List.ne_nil_of_mem hmOld
      have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (rightStep σ) (p, 0)).2))
        (List.mem_map.mpr ⟨[N, M], List.mem_sublists.mpr hTwo, rfl⟩)
      change _ ≤ σ.rightExt s 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, rightStep, hw,
        List.head?_eq_some_head hneOld] using hv
    have hTwoLeft (p b : ℕ) (hb : b ∈ σ.extPositions N) (hxp : b < p) (hyx : y < b) : 2 ≤ σ.leftExt s 0 p := by
      have hm : b ∈ (σ.extPositions N).filter (· < p) := by simp [hb, hxp]
      have hne := List.ne_nil_of_mem hm
      let w := ((σ.extPositions N).filter (· < p)).getLast hne
      have hw : ((σ.extPositions N).filter (· < p)).getLast? = some w :=
        List.getLast?_eq_some_getLast hne
      have hxw : b ≤ w := (hSortN.filter _).rel_getLast hm
      have hmOld : y ∈ (σ.extPositions M).filter (· < w) := by
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨hy, by omega⟩
      have hneOld := List.ne_nil_of_mem hmOld
      have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (leftStep σ) (p, 0)).2))
        (List.mem_map.mpr ⟨[N, M], List.mem_sublists.mpr hTwo, rfl⟩)
      change _ ≤ σ.leftExt s 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, leftStep, hw,
        List.getLast?_eq_some_getLast hneOld] using hv
    rcases houtside with hyx | hzy
    · have hRank : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
          σ.leftExt s 0 p + 1 = 3 ∧
            3 + σ.rightExt s 0 p = (match (generalizing := false) s with | Side.lower => σ.u - 1 | Side.upper => σ.a - 1) := by
        intro p hp hcup hcap
        obtain ⟨hxp, hpz⟩ := hbracket p hp hcup hcap
        have hL := hTwoLeft p x hx hxp hyx
        have hR := hOneRight σ s N p z hNOn hz hpz
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal hcup hcap ⊢ <;> omega
      have hh := ctx_bound_le_one_of_common_singleton_rank σ hpositive s 3 hRank
      exact ⟨hh.1, hh.2.1⟩
    · have hRank : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
          σ.leftExt s 0 p + 1 = 2 ∧
            2 + σ.rightExt s 0 p = (match (generalizing := false) s with | Side.lower => σ.u - 1 | Side.upper => σ.a - 1) := by
        intro p hp hcup hcap
        obtain ⟨hxp, hpz⟩ := hbracket p hp hcup hcap
        have hL := hOneLeft σ s N p x hNOn hx hxp
        have hR := hTwoRight p z hz hpz hzy
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal hcup hcap ⊢ <;> omega
      have hh := ctx_bound_le_one_of_common_singleton_rank σ hpositive s 2 hRank
      exact ⟨hh.1, hh.2.1⟩

  have ctx_youngest_marker_clipped_pair_square_pred_bound (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t) (N x a b : ℕ)
    (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = []) (hab : a < b) :
    let budget := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    let active := σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let I := fun p => Finset.Icc (σ.leftExt t 0 p + 1) (budget - σ.rightExt t 0 p)
    let L := Finset.Icc a (b - 1)
    let R := Finset.Icc (a + 1) b
    (∀ p ∈ active, I p ⊆ L ∨ I p ⊆ R) →
    ((∀ p ∈ active, p < x → I p ⊆ L) ∨ (∀ p ∈ active, x < p → I p ⊆ R)) →
    (∀ fuel, Ctx.Context.boundFuel fuel σ + 1 ≤ (Finset.Icc a b).card ^ 2) ∧
      σ.bound + 1 ≤ (Finset.Icc a b).card ^ 2 ∧
    (((∀ p ∈ active, p < x → I p ⊆ L) ∧ (∀ p ∈ active, x < p → I p ⊆ R)) →
      (∀ fuel, Ctx.Context.boundFuel fuel σ + (Finset.Icc a b).card ≤ (Finset.Icc a b).card ^ 2) ∧
        σ.bound + (Finset.Icc a b).card ≤ (Finset.Icc a b).card ^ 2) := by
    classical
    let budget := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
    let active := σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let I (p : ℕ) := Finset.Icc (σ.leftExt t 0 p + 1) (budget - σ.rightExt t 0 p)
    let L := Finset.Icc a (b - 1)
    let R := Finset.Icc (a + 1) b
    let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
    let left := active.filter (fun p => p < x)
    let right := active.filter (fun p => x < p)
    let PL := left.biUnion (fun p => Q (I p))
    let PR := right.biUnion (fun p => Q (I p))
    change (∀ p ∈ active, I p ⊆ L ∨ I p ⊆ R) →
      ((∀ p ∈ active, p < x → I p ⊆ L) ∨ (∀ p ∈ active, x < p → I p ⊆ R)) →
      (∀ fuel, boundFuel fuel σ + 1 ≤ (Finset.Icc a b).card ^ 2) ∧
        σ.bound + 1 ≤ (Finset.Icc a b).card ^ 2 ∧
      (((∀ p ∈ active, p < x → I p ⊆ L) ∧ (∀ p ∈ active, x < p → I p ⊆ R)) →
        (∀ fuel, boundFuel fuel σ + (Finset.Icc a b).card ≤ (Finset.Icc a b).card ^ 2) ∧
          σ.bound + (Finset.Icc a b).card ≤ (Finset.Icc a b).card ^ 2)
    intro hAll hSparse
    have hTwoSides : (∀ fuel, boundFuel fuel σ ≤ PL.card + PR.card) ∧
        σ.bound ≤ PL.card + PR.card := by
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
      let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
      let active (ρ : Context) := ρ.childPositions.toFinset.filter
        (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
      let I (ρ : Context) (r : ℕ) :=
        Finset.Icc (ρ.leftExt t 0 r + 1) (G ρ t - 1 - ρ.rightExt t 0 r)
      let total := (active σ).biUnion (I σ)
      let color (p : ℕ) := if p < x then (0 : ℕ) else 1
      let ranks (c : ℕ) := ((active σ).filter (fun p => color p = c)).biUnion (I σ)
      let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
      let group (c : ℕ) : Context := { σ with
        word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
          | Letter.child => if p ∈ support c then Letter.child else Letter.ext (σ.maxima.length + 1) Side.lower
          | Letter.ext j v => Letter.ext j v) }
      let pairs (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
      let P (c : ℕ) := ((active σ).filter (fun p => color p = c)).biUnion (fun p => pairs (I σ p))
      have hNe (p : ℕ) (hp : p ∈ σ.childPositions) : p ≠ x := by
        intro he
        subst x
        have hc := of_decide_eq_true (List.mem_filter.mp hp).2
        have he := (List.mem_filter.mp hx).2
        simp [hc] at he
      have hActiveChild (p : ℕ) (hp : p ∈ active σ) : p ∈ σ.childPositions :=
        List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
      have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
      have hSmall (r : ℕ) (hr : r ∈ σ.childPositions) : min (σ.cupLimit r r) (σ.capLimit r r) ≤ 3 := by
        have hrx : r ≠ x := by
          intro he
          subst x
          have hc := of_decide_eq_true (List.mem_filter.mp hr).2
          have he := (List.mem_filter.mp hx).2
          simp [hc] at he
        by_cases h : r < x
        · have he := hOneRight σ s N r x hNOn hx h
          cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
        · have he := hOneLeft σ s N r x hNOn hx (by omega)
          cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
      have hCover : ∀ p ∈ σ.childPositions, color p ∈ ({0, 1} : Finset ℕ) := by
        intro p hp
        dsimp only [color]
        split_ifs <;> simp
      have hColor : ∀ a ∈ σ.childPositions, ∀ b ∈ σ.childPositions, a ≤ b →
          (∀ r, a ≤ r → r ≤ b → r ∈ σ.childPositions) → color a = color b := by
        intro a ha b hb hab hbetween
        have hside : (a < x) = (b < x) := by
          apply propext
          constructor
          · intro hax
            by_contra hbx
            have hxc := hbetween x (by omega) (by omega)
            exact hNe x hxc rfl
          · omega
        simp only [color, hside]
      have hPos (c : ℕ) : ∀ p j v, (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
        (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).1
      have hChild (c r : ℕ) : r ∈ (group c).childPositions ↔ r ∈ σ.childPositions ∧ color r = c := by
        have hh : (group c).childPositions = σ.childPositions.filter (· ∈ support c) :=
          (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.1
        rw [hh]
        simp [support, and_assoc]
      have hLimits (c p q : ℕ) : (group c).cupLimit p q = σ.cupLimit p q ∧
          (group c).capLimit p q = σ.capLimit p q :=
        (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.2.2.1 p q
      have hHist (c j : ℕ) (hj : j ∈ σ.levels) :
          (group c).extPositions j = σ.extPositions j ∧ (group c).sideAt j = σ.sideAt j :=
        (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.1 j hj
      have hLevels (c : ℕ) (v : Side) (top : ℕ) : (group c).levelsOn v top = σ.levelsOn v top :=
        (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.1 v top
      have hPure (c : ℕ) (v : Side) (top p : ℕ) :
          (group c).leftExt v top p = σ.leftExt v top p ∧
          (group c).rightExt v top p = σ.rightExt v top p :=
        (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.2.1 v top p
      have hActive (c r : ℕ) : r ∈ active (group c) ↔ r ∈ active σ ∧ color r = c := by
        simp only [active, Finset.mem_filter, List.mem_toFinset, hChild, (hLimits c r r).1,
          (hLimits c r r).2]
        tauto
      have hI (c r : ℕ) : I (group c) r = I σ r := by
        simp only [I, (hPure c t 0 r).1, (hPure c t 0 r).2]
        rfl
      have hRanks (c : ℕ) : (active (group c)).biUnion (I (group c)) = ranks c := by
        ext z
        simp only [ranks, Finset.mem_biUnion, Finset.mem_filter, hActive, hI]
      have hNSide (c : ℕ) : (group c).sideAt N = s := (hHist c N hN).2.trans hNs
      have hX (c : ℕ) : x ∈ (group c).extPositions N := by rw [(hHist c N hN).1]; exact hx
      have hPairEq (c : ℕ) :
          (active (group c)).biUnion (fun p => pairs (I (group c) p)) = P c := by
        ext z
        simp only [P, Finset.mem_biUnion, Finset.mem_filter, hActive, hI]
      have hBoundary (c : ℕ) (rightward : Bool)
          (hside : ∀ p ∈ active (group c), if rightward then p < x else x < p) :
          (group c).bound ≤ (P c).card := by
        have hy : ∀ j ∈ (group c).levelsOn ((group c).sideAt N) N,
            ∀ p ∈ (group c).extPositions j, if rightward then p < x else x < p := by
          intro j hj p hp
          rw [hNSide c, hLevels c s N] at hj
          rw [(hHist c j (List.mem_filter.mp hj).1).1, hyoung j hj] at hp
          exact False.elim (List.not_mem_nil hp)
        have hs : min ((match (group c).sideAt N with
            | Side.lower => (group c).u | Side.upper => (group c).a) - 1)
            ((group c).k - (group c).maximumAt N) ≤ 4 := by
          rw [hNSide c]
          change min (G σ s - 1) _ ≤ 4
          have hg : G σ s ≤ 5 := hglobal
          omega
        have hh := ctx_active_boundary_marker_rank_pair_union_bound (group c) (hPos c) N x hN (hX c)
          rightward (by
            intro p hp hact
            exact hside p (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hp, hact⟩))
          hy t (by rw [hNSide c]; exact hne) hs
        have hb := hh.2
        change (group c).bound ≤ ((active (group c)).biUnion
          (fun p => pairs (I (group c) p))).card at hb
        rw [hPairEq c] at hb
        exact hb
      have hB0 : (group 0).bound ≤ (P 0).card := by
        apply hBoundary 0 true
        intro p hp
        have hc := ((hActive 0 p).mp hp).2
        simp only [Bool.true_eq, if_true]
        dsimp only [color] at hc
        split_ifs at hc <;> omega
      have hB1 : (group 1).bound ≤ (P 1).card := by
        apply hBoundary 1 false
        intro p hp
        have hh := (hActive 1 p).mp hp
        have hn := hNe p (hActiveChild p hh.1)
        have hc := hh.2
        simp only [Bool.false_eq_true, if_false]
        dsimp only [color] at hc
        split_ifs at hc <;> omega
      have hP0 : P 0 = ((active σ).filter (fun p => p < x)).biUnion (fun p => pairs (I σ p)) := by
        unfold P
        congr 1
        ext p
        simp [color]
      have hP1 : P 1 = ((active σ).filter (fun p => x < p)).biUnion (fun p => pairs (I σ p)) := by
        unfold P
        congr 1
        ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hp, hc⟩
          have hn := hNe p (hActiveChild p hp)
          refine ⟨hp, ?_⟩
          dsimp only [color] at hc
          split_ifs at hc <;> omega
        · rintro ⟨hp, hxp⟩
          exact ⟨hp, by simp [color, show ¬p < x by omega]⟩
      have hd := ctx_bound_le_sum_run_group_prunings_capacity_three σ hpositive color {0, 1}
        hCover hSmall hColor
      change (∀ fuel, boundFuel fuel σ ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
        σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hd
      have hSum : ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) =
          (group 0).bound + (group 1).bound := by simp
      rw [hSum] at hd
      have hb := Nat.add_le_add hB0 hB1
      have hResult : (∀ fuel, boundFuel fuel σ ≤ (P 0).card + (P 1).card) ∧
          σ.bound ≤ (P 0).card + (P 1).card :=
        ⟨fun fuel => (hd.1 fuel).trans hb, hd.2.trans hb⟩
      simpa only [hP0, hP1] using hResult
    have hQMono (S T : Finset ℕ) (hst : S ⊆ T) : Q S ⊆ Q T := by
      intro z hz
      obtain ⟨hz, ho⟩ := Finset.mem_filter.mp hz
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hst h1, hst h2⟩, ho⟩
    have hCover (F : Finset ℕ) (hf : F ⊆ active) :
        F.biUnion (fun p => Q (I p)) ⊆ Q L ∪ Q R := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      rcases hAll p (hf hp) with h | h
      · exact Finset.mem_union_left _ (hQMono _ _ h hz)
      · exact Finset.mem_union_right _ (hQMono _ _ h hz)
    have hMono (F S : Finset ℕ) (hf : ∀ p ∈ F, I p ⊆ S) :
        F.biUnion (fun p => Q (I p)) ⊆ Q S := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      exact hQMono _ _ (hf p hp) hz
    have hCardPairs (T : Finset ℕ) :
        ((T.product T).filter (fun z => z.1 ≤ z.2)).card = (T.card + 1).choose 2 := by
      rw [← Finset.card_sym2]
      apply Finset.card_bij (fun z _ => Sym2.mk z.1 z.2)
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
          · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩,
              Sym2.eq_swap⟩
    have hSame : (Q R).card = (Q L).card := by
      change ((R.product R).filter (fun z => z.1 ≤ z.2)).card =
        ((L.product L).filter (fun z => z.1 ≤ z.2)).card
      rw [hCardPairs, hCardPairs]
      have he : R.card = L.card := by
        simp only [R, L, Nat.card_Icc]
        omega
      rw [he]
    have hCount := (rank_pair_clipped_interval_union_missing_corner a b hab).2
    change (Q L).card + (Q L ∪ Q R).card + 1 = (Finset.Icc a b).card ^ 2 at hCount
    have hBudget : PL.card + PR.card + 1 ≤ (Finset.Icc a b).card ^ 2 := by
      rcases hSparse with h | h
      · have hL : PL ⊆ Q L := hMono left L (by
          intro p hp
          obtain ⟨hp, hx⟩ := Finset.mem_filter.mp hp
          exact h p hp hx)
        have hR : PR ⊆ Q L ∪ Q R := hCover right (fun _ hp => (Finset.mem_filter.mp hp).1)
        have hcL := Finset.card_le_card hL
        have hcR := Finset.card_le_card hR
        omega
      · have hL : PL ⊆ Q L ∪ Q R := hCover left (fun _ hp => (Finset.mem_filter.mp hp).1)
        have hR : PR ⊆ Q R := hMono right R (by
          intro p hp
          obtain ⟨hp, hx⟩ := Finset.mem_filter.mp hp
          exact h p hp hx)
        have hcL := Finset.card_le_card hL
        have hcR := Finset.card_le_card hR
        omega
    refine ⟨fun fuel => (Nat.add_le_add_right (hTwoSides.1 fuel) 1).trans hBudget,
      (Nat.add_le_add_right hTwoSides.2 1).trans hBudget, ?_⟩
    intro hBoth
    have hTwoChoose (n : ℕ) : 2 * (n + 1).choose 2 = n * n + n := by
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        nlinarith
    have hLength : L.card + 1 = (Finset.Icc a b).card := by
      simp only [L, Nat.card_Icc]
      omega
    have hPairCard : (Q L).card = (L.card + 1).choose 2 := hCardPairs L
    have hTwoCount : (Q L).card + (Q R).card + (Finset.Icc a b).card =
        (Finset.Icc a b).card ^ 2 := by
      have hh := hTwoChoose L.card
      rw [hSame, hPairCard, ← hLength]
      nlinarith
    have hL : PL ⊆ Q L := hMono left L (by
      intro p hp
      obtain ⟨hp, hx⟩ := Finset.mem_filter.mp hp
      exact hBoth.1 p hp hx)
    have hR : PR ⊆ Q R := hMono right R (by
      intro p hp
      obtain ⟨hp, hx⟩ := Finset.mem_filter.mp hp
      exact hBoth.2 p hp hx)
    have hBudgetBoth : PL.card + PR.card + (Finset.Icc a b).card ≤
        (Finset.Icc a b).card ^ 2 := by
      have hcL := Finset.card_le_card hL
      have hcR := Finset.card_le_card hR
      omega
    exact ⟨fun fuel => (Nat.add_le_add_right (hTwoSides.1 fuel) _).trans hBudgetBoth,
      (Nat.add_le_add_right hTwoSides.2 _).trans hBudgetBoth⟩

  classical
  let w := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part keep s m
  let β := σ.part rest t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ w ^ 2) ∧ α.bound + β.bound ≤ w ^ 2
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
  have hQβ : q₀ ∈ β.extPositions 1 := (hExtβ q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
  have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive keep s m hLα
  have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive rest t n hQβ
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
  have hPosα := hPositivePart keep s m
  have hPosβ := hPositivePart rest t n
  have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
  have hNpos := one_le_of_mem_levels hN
  have hNα : N + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNβ : N + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNsα : α.sideAt (N + 1) = s := (part_sideAt_succ σ keep s m hNpos).trans hNs
  have hNsβ : β.sideAt (N + 1) = s := (part_sideAt_succ σ rest t n hNpos).trans hNs
  have hXα : x ∈ α.extPositions (N + 1) := by rw [part_extPositions_succ σ keep s m hNpos]; exact hx
  have hXβ : x ∈ β.extPositions (N + 1) := by rw [part_extPositions_succ σ rest t n hNpos]; exact hx
  have hYoungβ : ∀ j ∈ β.levelsOn s (N + 1), β.extPositions j = [] := by
    have hs : β.sideAt 1 ≠ s := by rw [hSideβ]; exact Ne.symm hne
    have he := part_levelsOn_other_succ hs hNpos
    intro j hj
    rw [he] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [part_extPositions_succ σ rest t n (one_le_of_mem_levels (List.mem_filter.mp hi).1), hyoung i hi]
  have hLevelsβ : β.levelsOn t 0 = [1] := by
    rw [part_levelsOn_self_zero hSideβ, hclear]
    rfl
  have hOutside (p : ℕ) (hp : p ∈ rest) :
      (∀ q ∈ keep, p < q) ∨ (∀ q ∈ keep, q < p) := by
    obtain ⟨hpσ, hpnot⟩ := (hRest p).mp hp
    have hpne : p ≠ q₀ := by intro he; exact hpnot (he ▸ hq₀)
    by_cases hpq : p < q₀
    · left
      intro q hq
      by_contra h
      exact hpnot (hconvex q hq q₀ hq₀ p hpσ (by omega) (by omega))
    · right
      intro q hq
      by_contra h
      exact hpnot (hconvex q₀ hq₀ q hq p hpσ (by omega) (by omega))
  let active := β.childPositions.toFinset.filter
    (fun p => 0 < β.cupLimit p p ∧ 0 < β.capLimit p p)
  let I (p : ℕ) := Finset.Icc (β.leftExt t 0 p + 1) (w - β.rightExt t 0 p)
  let L := Finset.Icc 1 (w - 1)
  let R := Finset.Icc 2 w
  have hActive (p : ℕ) (hp : p ∈ active) : p ∈ rest :=
    (hChildβ p).mp (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
  have hLeftRank (p : ℕ) (hp : ∀ q ∈ keep, p < q) : I p = L := by
    have hEmpty : (β.extPositions 1).filter (· < p) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq hbad
      have hqp : q < p := of_decide_eq_true hbad
      have hpq := hp q ((hExtβ q).mp hq).2
      omega
    have hMem : q₀ ∈ (β.extPositions 1).filter (p < ·) := by simp [hQβ, hp q₀ hq₀]
    have hNE := List.ne_nil_of_mem hMem
    have hLeft : β.leftExt t 0 p = 0 := by simp [leftExt, hLevelsβ, hEmpty, -List.getLast?_filter]
    have hRight : β.rightExt t 0 p = 1 := by
      unfold rightExt
      rw [hLevelsβ]
      change ([0, (match ((β.extPositions 1).filter (p < ·)).head? with
        | some q => (q, 1) | none => (p, 0)).2].max?).getD 0 = 1
      rw [List.head?_eq_some_head hNE]
      rfl
    simp only [I, L, hLeft, hRight, Nat.zero_add]
  have hRightRank (p : ℕ) (hp : ∀ q ∈ keep, q < p) : I p = R := by
    have hEmpty : (β.extPositions 1).filter (p < ·) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq hbad
      have hpq : p < q := of_decide_eq_true hbad
      have hqp := hp q ((hExtβ q).mp hq).2
      omega
    have hMem : q₀ ∈ (β.extPositions 1).filter (· < p) := by simp [hQβ, hp q₀ hq₀]
    have hNE := List.ne_nil_of_mem hMem
    have hLeft : β.leftExt t 0 p = 1 := by
      unfold leftExt
      rw [hLevelsβ]
      change ([0, (match ((β.extPositions 1).filter (· < p)).getLast? with
        | some q => (q, 1) | none => (p, 0)).2].max?).getD 0 = 1
      rw [List.getLast?_eq_some_getLast hNE]
      rfl
    have hRight : β.rightExt t 0 p = 0 := by simp [rightExt, hLevelsβ, hEmpty, -List.head?_filter]
    simp only [I, R, hLeft, hRight, Nat.sub_zero]
  have hAll : ∀ p ∈ active, I p ⊆ L ∨ I p ⊆ R := by
    intro p hp
    rcases hOutside p (hActive p hp) with h | h
    · left
      rw [hLeftRank p h]
    · right
      rw [hRightRank p h]
  have hSparse : (∀ p ∈ active, p < x → I p ⊆ L) ∨
      (∀ p ∈ active, x < p → I p ⊆ R) := by
    by_cases hxq : x < q₀
    · left
      intro p hp hpx
      rcases hOutside p (hActive p hp) with h | h
      · rw [hLeftRank p h]
      · have hh := h q₀ hq₀
        omega
    · right
      intro p hp hxp
      rcases hOutside p (hActive p hp) with h | h
      · have hh := h q₀ hq₀
        omega
      · rw [hRightRank p h]
  have hw : 2 ≤ w := hwidth
  have hComp := ctx_youngest_marker_clipped_pair_square_pred_bound β hPosβ s t hne
    (N + 1) x 1 w hNβ hNsβ hXβ hglobal hYoungβ (by omega) hAll hSparse
  have hCard : (Finset.Icc 1 w).card = w := by simp only [Nat.card_Icc]; omega
  rw [hCard] at hComp
  let ownActive := α.childPositions.toFinset.filter
    (fun p => 0 < α.cupLimit p p ∧ 0 < α.capLimit p p)
  let ownI (p : ℕ) := Finset.Icc (α.leftExt t 0 p + 1) (w - α.rightExt t 0 p)
  let ownRanks := ownActive.biUnion ownI
  have hSmall : min ((match α.sideAt 1 with | Side.lower => α.u | Side.upper => α.a) - 2)
      (α.k - α.maximumAt 1) ≤ 3 := by
    rw [hSideα]
    change min ((match s with | Side.lower => σ.u | Side.upper => σ.a) - 2) _ ≤ 3
    omega
  have hOwn := ctx_active_two_boundary_marker_rank_union_bound α hPosα 1 l r hOneα hLα hRα
    (by intro p hp ha; exact hinside p ((hChildα p).mp hp).2)
    (by simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true])
    t (by rw [hSideα]; exact hne) hSmall
  change (∀ fuel, boundFuel fuel α ≤ ownRanks.card) ∧ α.bound ≤ ownRanks.card at hOwn
  have hOwnSub : ownRanks ⊆ Finset.Icc 1 w := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    have hh := Finset.mem_Icc.mp hz
    apply Finset.mem_Icc.mpr
    omega
  have hOwnCard : ownRanks.card ≤ w := by
    rw [← hCard]
    exact Finset.card_le_card hOwnSub
  have hLinear : (∀ fuel, boundFuel fuel α ≤ w) ∧ α.bound ≤ w :=
    ⟨fun fuel => (hOwn.1 fuel).trans hOwnCard, hOwn.2.trans hOwnCard⟩
  have hUnit (a b : ℕ) (ha : a ∈ rest) (hb : b ∈ rest)
      (hout : x < a ∨ b < x) (hbetween : ∀ p ∈ keep, a < p ∧ p < b) :
      (∀ fuel, boundFuel fuel α ≤ 1) ∧ α.bound ≤ 1 := by
    exact ctx_bracketed_older_exterior_marker_unit_bound α hPosα s 1 (N + 1) a x b
      hOneα hNα (by omega) hSideα hNsα ((hExtα a).mpr ha) hXα ((hExtα b).mpr hb)
      hglobal hout (by intro p hp hcup hcap; exact hbetween p ((hChildα p).mp hp).2)
  by_cases hBadL : ∃ p ∈ rest, (∀ q ∈ keep, p < q) ∧ x < p
  · obtain ⟨p, hp, hBefore, hxp⟩ := hBadL
    have hu := hUnit p r hp ((hRest r).mpr ⟨hr, hrnot⟩) (Or.inl hxp)
      (fun q hq => ⟨hBefore q hq, (hinside q hq).2⟩)
    constructor
    · intro f g
      have ha := hu.1 f
      have hb := hComp.1 g
      omega
    · have ha := hu.2
      have hb := hComp.2.1
      omega
  by_cases hBadR : ∃ p ∈ rest, (∀ q ∈ keep, q < p) ∧ p < x
  · obtain ⟨p, hp, hAfter, hpx⟩ := hBadR
    have hu := hUnit l p ((hRest l).mpr ⟨hl, hlnot⟩) hp (Or.inr hpx)
      (fun q hq => ⟨(hinside q hq).1, hAfter q hq⟩)
    constructor
    · intro f g
      have ha := hu.1 f
      have hb := hComp.1 g
      omega
    · have ha := hu.2
      have hb := hComp.2.1
      omega
  have hBothL : ∀ p ∈ active, p < x → I p ⊆ L := by
    intro p hp hpx
    rcases hOutside p (hActive p hp) with h | h
    · rw [hLeftRank p h]
    · exact False.elim (hBadR ⟨p, hActive p hp, h, hpx⟩)
  have hBothR : ∀ p ∈ active, x < p → I p ⊆ R := by
    intro p hp hxp
    rcases hOutside p (hActive p hp) with h | h
    · exact False.elim (hBadL ⟨p, hActive p hp, h, hxp⟩)
    · rw [hRightRank p h]
  have hStrong := hComp.2.2 ⟨hBothL, hBothR⟩
  constructor
  · intro f g
    have ha := hLinear.1 f
    have hb := hStrong.1 g
    omega
  · have ha := hLinear.2
    have hb := hStrong.2
    omega

end ErdosSzekeres
