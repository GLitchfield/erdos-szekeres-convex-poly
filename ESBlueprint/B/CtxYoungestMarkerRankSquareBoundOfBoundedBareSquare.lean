import ESBlueprint.B.CtxBoundLeInactivePruneCapacityThree
import ESBlueprint.B.CtxBoundMonoOfMarkerInclusion
import ESBlueprint.B.CtxActiveBoundaryMarkerRankPairUnionBound
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsCapacityThree
import ESBlueprint.B.CtxAxisCapacityIntervalLowerBound
import ESBlueprint.B.CtxSharedRankBareMarkerUpperNormalize

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Reduce the general youngest-marker rank-square estimate with chosen global at most five to the explicit bare-marker square estimate only for opposite widths at most the source exact rank-union cardinality. Arbitrary source maxima, opposite histories, inactive children, and positive unindexed barriers remain allowed. The bounded hypothesis supports later induction on width. The reduction packages active-support normalization, proper-side rank loss, and endpoint anchoring locally. The bare-marker square hypothesis is explicit and remains unproved.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_youngest_marker_rank_square_bound_of_bounded_bare_square (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = []) :
  let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks := active.biUnion (fun p =>
    Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p))
  (∀ (ρ : Ctx.Context) (J y : ℕ),
    (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
    (∀ j ∈ ρ.levels, ρ.maximumAt j = 0) →
    (∀ j ∈ ρ.levels, ρ.sideAt j = s) →
    J ∈ ρ.levels → y ∈ ρ.extPositions J →
    (∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = y) →
    (match s with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) ≤ 5 →
    (∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) →
    ((match t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1) ≤ ranks.card →
    ρ.bound ≤ ((match t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1) ^ 2) →
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ ranks.card ^ 2) ∧ σ.bound ≤ ranks.card ^ 2 := by
  classical
  have ctx_active_zero_maxima_upper_normalize (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (hsmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3) :
    let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
      (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    let keep := σ.childPositions.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let τ : Ctx.Context := { σ with
      word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
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
      word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
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

  have ctx_youngest_marker_square_bound_of_one_sided_rank_loss (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
    (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = []) :
    let active := σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let budget := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    let interval := fun p => Finset.Icc (σ.leftExt t 0 p + 1) (budget - σ.rightExt t 0 p)
    let ranks := active.biUnion interval
    ((active.filter (fun p => p < x)).biUnion interval ≠ ranks ∨
      (active.filter (fun p => x < p)).biUnion interval ≠ ranks) →
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ ranks.card ^ 2) ∧ σ.bound ≤ ranks.card ^ 2 := by
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
    change (((active σ).filter (fun p => p < x)).biUnion (I σ) ≠ total ∨
      ((active σ).filter (fun p => x < p)).biUnion (I σ) ≠ total) →
      (∀ fuel, boundFuel fuel σ ≤ total.card ^ 2) ∧ σ.bound ≤ total.card ^ 2
    intro hproper
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
    have hPairSub (c : ℕ) :
        (active (group c)).biUnion (fun p => pairs (I (group c) p)) ⊆ pairs (ranks c) := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨hz, horder⟩ := Finset.mem_filter.mp hz
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hz
      have hMem (v : ℕ) (hv : v ∈ I (group c) p) : v ∈ ranks c := by
        rw [← hRanks c]
        exact Finset.mem_biUnion.mpr ⟨p, hp, hv⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hMem _ ha, hMem _ hb⟩, horder⟩
    have hBoundary (c : ℕ) (rightward : Bool)
        (hside : ∀ p ∈ active (group c), if rightward then p < x else x < p) :
        (group c).bound ≤ (pairs (ranks c)).card := by
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
      exact hb.trans (Finset.card_le_card (hPairSub c))
    have hB0 : (group 0).bound ≤ (pairs (ranks 0)).card := by
      apply hBoundary 0 true
      intro p hp
      have hc := ((hActive 0 p).mp hp).2
      simp only [Bool.true_eq, if_true]
      dsimp only [color] at hc
      split_ifs at hc <;> omega
    have hB1 : (group 1).bound ≤ (pairs (ranks 1)).card := by
      apply hBoundary 1 false
      intro p hp
      have hh := (hActive 1 p).mp hp
      have hn := hNe p (hActiveChild p hh.1)
      have hc := hh.2
      simp only [Bool.false_eq_true, if_false]
      dsimp only [color] at hc
      split_ifs at hc <;> omega
    have hR0 : ranks 0 = ((active σ).filter (fun p => p < x)).biUnion (I σ) := by
      unfold ranks
      congr 1
      ext p
      simp [color]
    have hR1 : ranks 1 = ((active σ).filter (fun p => x < p)).biUnion (I σ) := by
      unfold ranks
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
    rw [← hR0, ← hR1] at hproper
    have hSub (c : ℕ) : ranks c ⊆ total := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      exact Finset.mem_biUnion.mpr ⟨p, (Finset.mem_filter.mp hp).1, hz⟩
    have hCard (c : ℕ) : (ranks c).card ≤ total.card := Finset.card_le_card (hSub c)
    have hStrict (c : ℕ) (hc : ranks c ≠ total) : (ranks c).card < total.card := by
      by_contra h
      exact hc (Finset.eq_of_subset_of_card_le (hSub c) (by omega))
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
    have hTriangle (w : ℕ) : (w + 1).choose 2 + w.choose 2 = w ^ 2 := by
      induction w with
      | zero => norm_num
      | succ w ih =>
        have h1 : (w + 1).choose 2 = w + w.choose 2 := by
          simpa only [Nat.choose_one_right] using Nat.choose_succ_succ w 1
        have h2 : (w + 1 + 1).choose 2 = w + 1 + (w + 1).choose 2 := by
          simpa only [Nat.choose_one_right] using Nat.choose_succ_succ (w + 1) 1
        change (w + 1 + 1).choose 2 + (w + 1).choose 2 = (w + 1) ^ 2
        nlinarith
    have hBudget : (pairs (ranks 0)).card + (pairs (ranks 1)).card ≤ total.card ^ 2 := by
      change (((ranks 0).product (ranks 0)).filter (fun z => z.1 ≤ z.2)).card +
        (((ranks 1).product (ranks 1)).filter (fun z => z.1 ≤ z.2)).card ≤ _
      rw [hCardPairs, hCardPairs]
      have hEq := hTriangle total.card
      rcases hproper with h | h
      · have hlt := hStrict 0 h
        have hl := Nat.choose_le_choose 2 (show (ranks 0).card + 1 ≤ total.card by omega)
        have hr := Nat.choose_le_choose 2 (Nat.add_le_add_right (hCard 1) 1)
        omega
      · have hlt := hStrict 1 h
        have hr := Nat.choose_le_choose 2 (show (ranks 1).card + 1 ≤ total.card by omega)
        have hl := Nat.choose_le_choose 2 (Nat.add_le_add_right (hCard 0) 1)
        omega
    have hd := ctx_bound_le_sum_run_group_prunings_capacity_three σ hpositive color {0, 1}
      hCover hSmall hColor
    change (∀ fuel, boundFuel fuel σ ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
      σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hd
    have hSum : ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) =
        (group 0).bound + (group 1).bound := by simp
    rw [hSum] at hd
    have hb := (Nat.add_le_add hB0 hB1).trans hBudget
    exact ⟨fun fuel => (hd.1 fuel).trans hb, hd.2.trans hb⟩

  have ctx_shared_side_rank_unions_anchor_endpoints (σ : Ctx.Context) (t : Ctx.Side) (x : ℕ) :
    let active := σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    let lo := fun p => σ.leftExt t 0 p + 1
    let hi := fun p => budget - σ.rightExt t 0 p
    let interval := fun p => Finset.Icc (lo p) (hi p)
    let ranks := active.biUnion interval
    (active.filter (fun p => p < x)).biUnion interval = ranks →
    (active.filter (fun p => x < p)).biUnion interval = ranks →
    ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p →
      if p < x then lo p = lo x else hi p = hi x := by
    classical
    let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
    let active := σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let lo (p : ℕ) := σ.leftExt t 0 p + 1
    let hi (p : ℕ) := G σ t - 1 - σ.rightExt t 0 p
    let I (p : ℕ) := Finset.Icc (lo p) (hi p)
    let ranks := active.biUnion I
    change (active.filter (fun p => p < x)).biUnion I = ranks →
      (active.filter (fun p => x < p)).biUnion I = ranks →
      ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p →
        if p < x then lo p = lo x else hi p = hi x
    intro hL hR
    have hSort (ρ : Context) (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
      (List.pairwise_lt_range.filter _).imp le_of_lt
    have hStepLeft (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : c ≤ d) :
        (leftStep ρ (p, c) j).1 ≤ (leftStep ρ (q, d) j).1 ∧
        (leftStep ρ (p, c) j).2 ≤ (leftStep ρ (q, d) j).2 := by
      cases ha : ((ρ.extPositions j).filter (· < p)).getLast? with
      | none =>
        have hnil := List.getLast?_eq_none_iff.mp ha
        cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
        | none => simpa only [leftStep, ha, hb] using And.intro hpq hcd
        | some y =>
          have hy := List.mem_of_mem_getLast? (Option.mem_def.mpr hb)
          have hpy : p ≤ y := by
            by_contra h
            have hx : y ∈ (ρ.extPositions j).filter (· < p) :=
              List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
            rw [hnil] at hx
            exact List.not_mem_nil hx
          simpa only [leftStep, ha, hb] using And.intro hpy (show c ≤ d + 1 by omega)
      | some x =>
        have hx := List.mem_of_mem_getLast? (Option.mem_def.mpr ha)
        have hxq : x ∈ (ρ.extPositions j).filter (· < q) := by
          have hxp : x < p := of_decide_eq_true (List.mem_filter.mp hx).2
          exact List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
        cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
        | none =>
          have hnil := List.getLast?_eq_none_iff.mp hb
          rw [hnil] at hxq
          exact False.elim (List.not_mem_nil hxq)
        | some y =>
          have hlast : ((ρ.extPositions j).filter (· < q)).getLast (List.ne_nil_of_mem hxq) = y := by
            rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hxq)] at hb
            exact Option.some.inj hb
          have hxy : x ≤ y := by
            simpa only [hlast] using ((hSort ρ j).filter _).rel_getLast hxq
          simpa only [leftStep, ha, hb] using And.intro hxy (show c + 1 ≤ d + 1 by omega)
    have hStepRight (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : d ≤ c) :
        (rightStep ρ (p, c) j).1 ≤ (rightStep ρ (q, d) j).1 ∧
        (rightStep ρ (q, d) j).2 ≤ (rightStep ρ (p, c) j).2 := by
      cases ha : ((ρ.extPositions j).filter (p < ·)).head? with
      | none =>
        have hnil := List.head?_eq_none_iff.mp ha
        cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
        | none => simpa only [rightStep, ha, hb] using And.intro hpq hcd
        | some y =>
          have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
          have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
          have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hyp
          exact False.elim (List.not_mem_nil hyp)
      | some x =>
        have hx := List.mem_of_mem_head? (Option.mem_def.mpr ha)
        cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
        | none =>
          have hnil := List.head?_eq_none_iff.mp hb
          have hxq : x ≤ q := by
            by_contra h
            have hmem : x ∈ (ρ.extPositions j).filter (q < ·) :=
              List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
            rw [hnil] at hmem
            exact List.not_mem_nil hmem
          simpa only [rightStep, ha, hb] using And.intro hxq (show d ≤ c + 1 by omega)
        | some y =>
          have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
          have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
          have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
          have hhead : ((ρ.extPositions j).filter (p < ·)).head (List.ne_nil_of_mem hyp) = x := by
            rw [List.head?_eq_some_head (List.ne_nil_of_mem hyp)] at ha
            exact Option.some.inj ha
          have hxy : x ≤ y := by
            simpa only [hhead] using ((hSort ρ j).filter _).rel_head hyp
          simpa only [rightStep, ha, hb] using And.intro hxy (show d + 1 ≤ c + 1 by omega)
    have hFoldLeft (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → c ≤ d →
        (ls.foldl (leftStep ρ) (p, c)).1 ≤ (ls.foldl (leftStep ρ) (q, d)).1 ∧
        (ls.foldl (leftStep ρ) (p, c)).2 ≤ (ls.foldl (leftStep ρ) (q, d)).2 := by
      intro ls
      induction ls with
      | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
      | cons j ls ih =>
        intro p q c d hpq hcd
        have h := hStepLeft ρ j p q c d hpq hcd
        simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
    have hFoldRight (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → d ≤ c →
        (ls.foldl (rightStep ρ) (p, c)).1 ≤ (ls.foldl (rightStep ρ) (q, d)).1 ∧
        (ls.foldl (rightStep ρ) (q, d)).2 ≤ (ls.foldl (rightStep ρ) (p, c)).2 := by
      intro ls
      induction ls with
      | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
      | cons j ls ih =>
        intro p q c d hpq hcd
        have h := hStepRight ρ j p q c d hpq hcd
        simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
    have hLeftMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
        ρ.leftExt v top p ≤ ρ.leftExt v top q := by
      simp only [leftExt_eq]
      apply getD_max?_le_of_forall
      intro value hv
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
      exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldLeft ρ ls p q 0 0 hpq le_rfl).2⟩
    have hRightMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
        ρ.rightExt v top q ≤ ρ.rightExt v top p := by
      simp only [rightExt_eq]
      apply getD_max?_le_of_forall
      intro value hv
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
      exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldRight ρ ls p q 0 0 hpq le_rfl).2⟩
    have hLo (p q : ℕ) (hpq : p ≤ q) : lo p ≤ lo q := by
      have h := hLeftMono σ t 0 p q hpq
      dsimp only [lo]
      omega
    have hHi (p q : ℕ) (hpq : p ≤ q) : hi p ≤ hi q := by
      have h := hRightMono σ t 0 p q hpq
      dsimp only [hi]
      omega
    have hValid (p : ℕ) (hp : p ∈ active) : lo p ≤ hi p := by
      have ha := (Finset.mem_filter.mp hp).2
      cases t
      · have h := ha.1
        simp only [cupLimit, chainExt] at h
        dsimp only [lo, hi, G]
        omega
      · have h := ha.2
        simp only [capLimit, chainExt] at h
        dsimp only [lo, hi, G]
        omega
    intro p hp ha
    have hpa : p ∈ active := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hp, ha⟩
    by_cases hpx : p < x
    · rw [if_pos hpx]
      have hm : lo p ∈ (active.filter (fun q => x < q)).biUnion I := by
        rw [hR]
        exact Finset.mem_biUnion.mpr ⟨p, hpa, Finset.mem_Icc.mpr ⟨le_rfl, hValid p hpa⟩⟩
      obtain ⟨q, hq, hqI⟩ := Finset.mem_biUnion.mp hm
      have hxq := (Finset.mem_filter.mp hq).2
      have hql := (Finset.mem_Icc.mp hqI).1
      exact le_antisymm (hLo p x (by omega)) ((hLo x q (by omega)).trans hql)
    · rw [if_neg hpx]
      by_cases he : p = x
      · subst p
        rfl
      have hxp : x < p := by omega
      have hm : hi p ∈ (active.filter (fun q => q < x)).biUnion I := by
        rw [hL]
        exact Finset.mem_biUnion.mpr ⟨p, hpa, Finset.mem_Icc.mpr ⟨hValid p hpa, le_rfl⟩⟩
      obtain ⟨q, hq, hqI⟩ := Finset.mem_biUnion.mp hm
      have hqx := (Finset.mem_filter.mp hq).2
      have hqh := (Finset.mem_Icc.mp hqI).2
      exact le_antisymm (hqh.trans (hHi q x (by omega))) (hHi x p (by omega))

  have ctx_youngest_marker_rank_square_bound_of_zero_maxima_square (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
    (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [])
    (hzeroSquare : ∀ (ρ : Ctx.Context) (J y : ℕ),
      (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
      J ∈ ρ.levels → ρ.sideAt J = s → y ∈ ρ.extPositions J →
      (match (generalizing := false) s with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) ≤ 5 →
      (∀ j ∈ ρ.levelsOn s J, ρ.extPositions j = []) →
      (∀ j ∈ ρ.levels, ρ.maximumAt j = 0) →
      (∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) →
      (∀ p ∈ ρ.childPositions,
        if p < y then ρ.leftExt t 0 p + 1 = ρ.leftExt t 0 y + 1
        else (match (generalizing := false) t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1 - ρ.rightExt t 0 p =
          (match (generalizing := false) t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1 - ρ.rightExt t 0 y) →
      let budget := (match (generalizing := false) t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1
      let active := ρ.childPositions.toFinset.filter
        (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
      let ranks := active.biUnion (fun p =>
        Finset.Icc (ρ.leftExt t 0 p + 1) (budget - ρ.rightExt t 0 p))
      ranks.card ≤ ((σ.childPositions.toFinset.filter
        (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)).biUnion (fun p =>
        Finset.Icc (σ.leftExt t 0 p + 1)
          ((match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 - σ.rightExt t 0 p))).card →
      ρ.bound ≤ ranks.card ^ 2) :
    let global := match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
    let active := σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let ranks := active.biUnion (fun p =>
      Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p))
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ ranks.card ^ 2) ∧ σ.bound ≤ ranks.card ^ 2 := by
    classical
    let G (υ : Context) (v : Side) := match v with | Side.lower => υ.u | Side.upper => υ.a
    let active (υ : Context) := υ.childPositions.toFinset.filter
      (fun p => 0 < υ.cupLimit p p ∧ 0 < υ.capLimit p p)
    let ranks (υ : Context) := (active υ).biUnion
      (fun p => Finset.Icc (υ.leftExt t 0 p + 1) (G υ t - 1 - υ.rightExt t 0 p))
    change (∀ fuel, boundFuel fuel σ ≤ (ranks σ).card ^ 2) ∧ σ.bound ≤ (ranks σ).card ^ 2
    let interval (p : ℕ) := Finset.Icc (σ.leftExt t 0 p + 1) (G σ t - 1 - σ.rightExt t 0 p)
    let leftRanks := ((active σ).filter (fun p => p < x)).biUnion interval
    let rightRanks := ((active σ).filter (fun p => x < p)).biUnion interval
    by_cases hproper : leftRanks ≠ ranks σ ∨ rightRanks ≠ ranks σ
    · exact ctx_youngest_marker_square_bound_of_one_sided_rank_loss σ hpositive s t hne
        N x hN hNs hx hglobal hyoung hproper
    have hLeft : leftRanks = ranks σ := by tauto
    have hRight : rightRanks = ranks σ := by tauto
    have hanchor := ctx_shared_side_rank_unions_anchor_endpoints σ t x hLeft hRight
    have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
    have hOneLeft (p : ℕ) (hxp : x < p) : 1 ≤ σ.leftExt s 0 p := by
      have hm : x ∈ (σ.extPositions N).filter (· < p) := by simp [hx, hxp]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (leftStep σ) (p, 0)).2))
        (List.mem_map.mpr ⟨[N], List.mem_sublists.mpr (List.singleton_sublist.mpr hNOn), rfl⟩)
      change _ ≤ σ.leftExt s 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, leftStep,
        List.getLast?_eq_some_getLast hnonempty] using hv
    have hOneRight (p : ℕ) (hpx : p < x) : 1 ≤ σ.rightExt s 0 p := by
      have hm : x ∈ (σ.extPositions N).filter (p < ·) := by simp [hx, hpx]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (σ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (rightStep σ) (p, 0)).2))
        (List.mem_map.mpr ⟨[N], List.mem_sublists.mpr (List.singleton_sublist.mpr hNOn), rfl⟩)
      change _ ≤ σ.rightExt s 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, rightStep,
        List.head?_eq_some_head hnonempty] using hv
    have hChain (p : ℕ) (hp : p ∈ σ.childPositions) : 1 ≤ σ.chainExt s p p := by
      have hlet : σ.letterAt p = Letter.child := of_decide_eq_true (List.mem_filter.mp hp).2
      have hpx : p ≠ x := by
        intro heq
        subst p
        simp [extPositions, hlet] at hx
      rcases lt_or_gt_of_ne hpx with hpx | hxp
      · have hr := hOneRight p hpx
        simp only [chainExt]
        omega
      · have hl := hOneLeft p hxp
        simp only [chainExt]
        omega
    have hSmall (p : ℕ) (hp : p ∈ σ.childPositions) :
        min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3 := by
      have hc := hChain p hp
      have hglobal : G σ s ≤ 5 := hglobal
      cases hs : s <;> simp only [G, hs] at hc hglobal
      · simp only [cupLimit, capLimit]
        omega
      · simp only [cupLimit, capLimit]
        omega
    let keep := σ.childPositions.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let τ : Context := { σ with
      word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
        | Letter.child => if p ∈ keep then Letter.child else Letter.ext (σ.maxima.length + 1) Side.lower
        | Letter.ext j v => Letter.ext j v)
      maxima := List.replicate σ.maxima.length 0 }
    have hn := ctx_active_zero_maxima_upper_normalize σ hpositive hSmall
    have hPos : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := hn.1
    have hChild : τ.childPositions = keep := hn.2.1
    have hAllActive : ∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := hn.2.2.1
    have hActive : active τ = active σ := hn.2.2.2.1
    have hHistory : ∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧
        τ.sideAt j = σ.sideAt j ∧ τ.maximumAt j = 0 := hn.2.2.2.2.1
    have hPure : ∀ v top p, τ.leftExt v top p = σ.leftExt v top p ∧
        τ.rightExt v top p = σ.rightExt v top p := hn.2.2.2.2.2.1
    have hBound : σ.bound ≤ τ.bound := hn.2.2.2.2.2.2.2.2
    have hFuel : ∀ fuel, boundFuel fuel σ ≤ τ.bound := hn.2.2.2.2.2.2.2.1
    have hLevels : τ.levels = σ.levels := by simp [levels, τ]
    have hJτ : N ∈ τ.levels := by rw [hLevels]; exact hN
    have hSide : τ.sideAt N = s := (hHistory N hN).2.1.trans hNs
    have hY : x ∈ τ.extPositions N := by rw [(hHistory N hN).1]; exact hx
    have hGlobal : G τ s ≤ 5 := hglobal
    have hYoung : ∀ j ∈ τ.levelsOn s N, τ.extPositions j = [] := by
      intro j hj
      have hjl : j ∈ σ.levels := by simpa only [hLevels] using (List.mem_filter.mp hj).1
      have hjc : τ.sideAt j = s ∧ (N = 0 ∨ j < N) := of_decide_eq_true (List.mem_filter.mp hj).2
      rw [(hHistory j hjl).2.1] at hjc
      have hjρ : j ∈ σ.levelsOn s N := List.mem_filter.mpr ⟨hjl, decide_eq_true hjc⟩
      exact (hHistory j hjl).1.trans (hyoung j hjρ)
    have hZero : ∀ j ∈ τ.levels, τ.maximumAt j = 0 := by
      intro j hj
      rw [hLevels] at hj
      exact (hHistory j hj).2.2
    have hAnchor : ∀ p ∈ τ.childPositions,
        if p < x then τ.leftExt t 0 p + 1 = τ.leftExt t 0 x + 1
        else G τ t - 1 - τ.rightExt t 0 p = G τ t - 1 - τ.rightExt t 0 x := by
      intro p hp
      rw [hChild] at hp
      have hcp := (List.mem_filter.mp hp).1
      have ha := of_decide_eq_true (List.mem_filter.mp hp).2
      have he := hanchor p hcp ha
      simpa only [(hPure t 0 p).1, (hPure t 0 x).1, (hPure t 0 p).2, (hPure t 0 x).2] using he
    have hSquare := hzeroSquare τ N x hPos hJτ hSide hY hGlobal hYoung hZero hAllActive hAnchor
    change (ranks τ).card ≤ (ranks σ).card → τ.bound ≤ (ranks τ).card ^ 2 at hSquare
    have hInterval (p : ℕ) :
        Finset.Icc (τ.leftExt t 0 p + 1) (G τ t - 1 - τ.rightExt t 0 p) =
          Finset.Icc (σ.leftExt t 0 p + 1) (G σ t - 1 - σ.rightExt t 0 p) := by
      rw [(hPure t 0 p).1, (hPure t 0 p).2]
    have hRanks : ranks τ = ranks σ := by simp only [ranks, hActive, hInterval]
    have hSquareBound := hSquare (le_of_eq (congrArg Finset.card hRanks))
    rw [hRanks] at hSquareBound
    exact ⟨fun fuel => (hFuel fuel).trans hSquareBound, hBound.trans hSquareBound⟩

  classical
  dsimp only
  intro hbare
  apply ctx_youngest_marker_rank_square_bound_of_zero_maxima_square σ hpositive s t hne
    N x hN hNs hx hglobal hyoung
  intro ρ J y hPos hJ hJs hy hGlobal hYoung hZero hAll hAnchor
  dsimp only
  intro hRankBound
  let G (υ : Context) := match t with | Side.lower => υ.u | Side.upper => υ.a
  let active (υ : Context) := υ.childPositions.toFinset.filter
    (fun p => 0 < υ.cupLimit p p ∧ 0 < υ.capLimit p p)
  let I (υ : Context) (p : ℕ) :=
    Finset.Icc (υ.leftExt t 0 p + 1) (G υ - 1 - υ.rightExt t 0 p)
  let ranks (υ : Context) := (active υ).biUnion (I υ)
  change ρ.bound ≤ (ranks ρ).card ^ 2
  let L := ((active ρ).filter (fun p => p < y)).biUnion (I ρ)
  let R := ((active ρ).filter (fun p => y < p)).biUnion (I ρ)
  by_cases hproper : L ≠ ranks ρ ∨ R ≠ ranks ρ
  · exact (ctx_youngest_marker_square_bound_of_one_sided_rank_loss ρ hPos s t hne
      J y hJ hJs hy hGlobal hYoung hproper).2
  have hL : L = ranks ρ := by tauto
  have hR : R = ranks ρ := by tauto
  by_cases hNE : (ranks ρ).Nonempty
  · obtain ⟨τ, K, hK, hChild, hPosτ, hZeroτ, hChosenτ, hLevelτ, hyτ, hOnlyτ,
        hGlobalτ, hWidthτ, hAllτ, hFuelτ, hBoundτ⟩ :=
      ctx_shared_rank_bare_marker_upper_normalize ρ hPos hZero s t hne J y hJ hJs hy
        hGlobal hYoung hAll hL hR hNE
    have hb := hbare τ K y hPosτ hZeroτ hChosenτ hLevelτ hyτ hOnlyτ hGlobalτ hAllτ (hWidthτ.trans hRankBound)
    have hPower : (G τ - 1) ^ 2 ≤ (ranks ρ).card ^ 2 := by
      exact Nat.pow_le_pow_left hWidthτ 2
    exact hBoundτ.trans (hb.trans hPower)
  · have hEmpty : ρ.childPositions = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro p hp
      have ha := hAll p hp
      have hLow : ρ.leftExt t 0 p + 1 ≤ G ρ - 1 - ρ.rightExt t 0 p := by
        cases t <;> simp only [cupLimit, capLimit, chainExt, G] at ha ⊢ <;> omega
      have hpA : p ∈ active ρ := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hp, ha⟩
      have hz : ρ.leftExt t 0 p + 1 ∈ I ρ p := Finset.mem_Icc.mpr ⟨le_rfl, hLow⟩
      exact hNE ⟨_, Finset.mem_biUnion.mpr ⟨p, hpA, hz⟩⟩
    have hb : ρ.bound ≤ 0 := by
      simpa only [hEmpty, List.map_nil, List.sum_nil] using ctx_bound_le_sum_point_bases ρ
    exact hb.trans (Nat.zero_le _)

end ErdosSzekeres
