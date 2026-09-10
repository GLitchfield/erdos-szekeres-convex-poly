import ESBlueprint.B.CtxAxisCapacityIntervalLowerBound
import ESBlueprint.B.CtxBoundMonoOfMarkerInclusion
import ESBlueprint.B.CtxSingleRunDescendantLimitsNormalize
import ESBlueprint.B.CtxSingleRunDescendantBoundNormalize
import ESBlueprint.B.CtxSeparatingMarkerRetainedLevelDoubledRankBound

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Reduce the nonempty shared-rank case to a bare chosen-axis marker context. Assume positive labels, zero original indexed maxima, all children active, a youngest actual chosen pivot, chosen global at most five, and both side rank unions equal to the total. The target preserves k and child positions, retains positive labels and zero maxima, has only chosen-axis indexed levels with every actual indexed marker at the pivot, and keeps a surviving indexed pivot. Its chosen global is at most five; its opposite global minus one is at most the original rank-union cardinality. All children remain active and every fuel/full bound can only increase. Exterior opposite history is absorbed without contracting the physical child pattern. The square estimate for this bare context remains a separate theorem to prove. The normalization proof packages its history-transport, pruning, reindexing, and exterior-history calculations as local proof components. No square-bound assumption is used or concluded.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_shared_rank_bare_marker_upper_normalize (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (hzero : ∀ j ∈ σ.levels, σ.maximumAt j = 0)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [])
  (hactive : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p) :
  let G := fun (ρ : Ctx.Context) => match t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let I := fun (ρ : Ctx.Context) (p : ℕ) =>
    Finset.Icc (ρ.leftExt t 0 p + 1) (G ρ - 1 - ρ.rightExt t 0 p)
  let ranks := fun (ρ : Ctx.Context) => (active ρ).biUnion (I ρ)
  ((active σ).filter (fun p => p < x)).biUnion (I σ) = ranks σ →
  ((active σ).filter (fun p => x < p)).biUnion (I σ) = ranks σ →
  (ranks σ).Nonempty →
  ∃ (τ : Ctx.Context) (J : ℕ),
    τ.k = σ.k ∧ τ.childPositions = σ.childPositions ∧
    (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
    (∀ j ∈ τ.levels, τ.maximumAt j = 0) ∧
    (∀ j ∈ τ.levels, τ.sideAt j = s) ∧
    J ∈ τ.levels ∧ x ∈ τ.extPositions J ∧
    (∀ j ∈ τ.levels, ∀ p ∈ τ.extPositions j, p = x) ∧
    (match s with | Ctx.Side.lower => τ.u | Ctx.Side.upper => τ.a) ≤ 5 ∧
    G τ - 1 ≤ (ranks σ).card ∧
    (∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧ σ.bound ≤ τ.bound := by
  classical
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

  have ctx_bound_mono_of_marker_inclusion_empty_zero_levels (σ τ : Ctx.Context)
    (hσpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (hτpositive : ∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (ha : σ.a ≤ τ.a) (hu : σ.u ≤ τ.u) (hk : σ.k = τ.k)
    (hword : σ.word.length = τ.word.length)
    (hchild : ∀ p, σ.letterAt p = Ctx.Letter.child ↔ τ.letterAt p = Ctx.Letter.child)
    (hdepth : σ.maxima.length = τ.maxima.length)
    (hhistory : ∀ j ∈ σ.levels,
      (τ.extPositions j = [] ∧ τ.maximumAt j = 0) ∨
      (τ.sideAt j = σ.sideAt j ∧ τ.extPositions j ⊆ σ.extPositions j ∧
        τ.maximumAt j ≤ σ.maximumAt j)) :
    (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
      (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧ σ.bound ≤ τ.bound := by
    classical
    let Sim (ρ υ : Context) : Prop :=
      ρ.a ≤ υ.a ∧ ρ.u ≤ υ.u ∧ ρ.k = υ.k ∧ ρ.word.length = υ.word.length ∧
      (∀ p, ρ.letterAt p = Letter.child ↔ υ.letterAt p = Letter.child) ∧
      ρ.maxima.length = υ.maxima.length ∧
      (∀ j ∈ ρ.levels,
        (υ.extPositions j = [] ∧ υ.maximumAt j = 0) ∨
        (υ.sideAt j = ρ.sideAt j ∧ υ.extPositions j ⊆ ρ.extPositions j ∧
          υ.maximumAt j ≤ ρ.maximumAt j)) ∧
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
      (∀ p j v, υ.letterAt p = Letter.ext j v → 1 ≤ j)
    have hInitial : Sim σ τ := ⟨ha, hu, hk, hword, hchild, hdepth, hhistory, hσpositive, hτpositive⟩
    have hK {ρ υ : Context} (h : Sim ρ υ) : υ.k = ρ.k := h.2.2.1.symm
    have hChild {ρ υ : Context} (h : Sim ρ υ) : υ.childPositions = ρ.childPositions := by
      rcases h with ⟨_, _, _, hlen, hletters, _⟩
      simp only [childPositions, hlen, hletters]
    have hRuns {ρ υ : Context} (h : Sim ρ υ) : υ.numRuns = ρ.numRuns := by
      rcases h with ⟨_, _, _, hlen, hletters, _⟩
      simp only [numRuns, hlen, ne_eq, hletters]
    have hBlocks {ρ υ : Context} (h : Sim ρ υ) : υ.blocks = ρ.blocks := by
      simp only [blocks, hChild h]
    have hLevels {ρ υ : Context} (h : Sim ρ υ) : υ.levels = ρ.levels := by
      rcases h with ⟨_, _, _, _, _, hdepth, _⟩
      simp only [levels, hdepth]
    have hHistory {ρ υ : Context} (h : Sim ρ υ) (j : ℕ) (hj : j ∈ ρ.levels) :
        (υ.extPositions j = [] ∧ υ.maximumAt j = 0) ∨
        (υ.sideAt j = ρ.sideAt j ∧ υ.extPositions j ⊆ ρ.extPositions j ∧
          υ.maximumAt j ≤ ρ.maximumAt j) := h.2.2.2.2.2.2.1 j hj
    have hExtSubset {ρ υ : Context} (h : Sim ρ υ) (j : ℕ) (hj : j ∈ ρ.levels) :
        υ.extPositions j ⊆ ρ.extPositions j := by
      rcases hHistory h j hj with hz | hn
      · intro p hp
        rw [hz.1] at hp
        exact False.elim (List.not_mem_nil hp)
      · exact hn.2.1
    have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
      unfold levels
      exact List.pairwise_lt_range.map (fun x => x+1) (fun a b h => Nat.add_lt_add_right h 1)
    have hSort (ρ : Context) (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
      (List.pairwise_lt_range.filter _).imp le_of_lt
    have hLeftWitness (ρ υ : Context) : ∀ (ls : List ℕ),
        (∀ j ∈ ls, υ.extPositions j ⊆ ρ.extPositions j) →
        ∀ p q c d : ℕ, p ≤ q → c ≤ d →
        ∃ ks : List ℕ, ks.Sublist ls ∧
          (ls.foldl (leftStep υ) (p, c)).1 ≤ (ks.foldl (leftStep ρ) (q, d)).1 ∧
          (ls.foldl (leftStep υ) (p, c)).2 ≤ (ks.foldl (leftStep ρ) (q, d)).2 := by
      intro ls
      induction ls with
      | nil =>
        intro _ p q c d hpq hcd
        exact ⟨[], List.Sublist.refl _, hpq, hcd⟩
      | cons j ls ih =>
        intro hext p q c d hpq hcd
        have hrest : ∀ i ∈ ls, υ.extPositions i ⊆ ρ.extPositions i :=
          fun i hi => hext i (List.mem_cons_of_mem _ hi)
        cases hx : ((υ.extPositions j).filter (· < p)).getLast? with
        | none =>
          obtain ⟨ks, hks, hends, hcounts⟩ := ih hrest p q c d hpq hcd
          refine ⟨ks, hks.cons j, ?_⟩
          simpa only [List.foldl_cons, leftStep, hx] using And.intro hends hcounts
        | some x =>
          have hxmem := List.mem_of_mem_getLast? (Option.mem_def.mpr hx)
          have hxp : x < p := of_decide_eq_true (List.mem_filter.mp hxmem).2
          have hxq : x ∈ (ρ.extPositions j).filter (· < q) :=
            List.mem_filter.mpr ⟨hext j (by simp) (List.mem_filter.mp hxmem).1,
              by simp only [decide_eq_true_eq]; omega⟩
          have hnonempty := List.ne_nil_of_mem hxq
          let y := ((ρ.extPositions j).filter (· < q)).getLast hnonempty
          have hy : ((ρ.extPositions j).filter (· < q)).getLast? = some y :=
            List.getLast?_eq_some_getLast hnonempty
          have hxy : x ≤ y := ((hSort ρ j).filter _).rel_getLast hxq
          obtain ⟨ks, hks, hends, hcounts⟩ := ih hrest x y (c + 1) (d + 1) hxy (by omega)
          refine ⟨j :: ks, hks.cons_cons j, ?_⟩
          simpa only [List.foldl_cons, leftStep, hx, hy] using And.intro hends hcounts
    have hRightWitness (ρ υ : Context) : ∀ (ls : List ℕ),
        (∀ j ∈ ls, υ.extPositions j ⊆ ρ.extPositions j) →
        ∀ p q c d : ℕ, q ≤ p → c ≤ d →
        ∃ ks : List ℕ, ks.Sublist ls ∧
          (ks.foldl (rightStep ρ) (q, d)).1 ≤ (ls.foldl (rightStep υ) (p, c)).1 ∧
          (ls.foldl (rightStep υ) (p, c)).2 ≤ (ks.foldl (rightStep ρ) (q, d)).2 := by
      intro ls
      induction ls with
      | nil =>
        intro _ p q c d hqp hcd
        exact ⟨[], List.Sublist.refl _, hqp, hcd⟩
      | cons j ls ih =>
        intro hext p q c d hqp hcd
        have hrest : ∀ i ∈ ls, υ.extPositions i ⊆ ρ.extPositions i :=
          fun i hi => hext i (List.mem_cons_of_mem _ hi)
        cases hx : ((υ.extPositions j).filter (p < ·)).head? with
        | none =>
          obtain ⟨ks, hks, hends, hcounts⟩ := ih hrest p q c d hqp hcd
          refine ⟨ks, hks.cons j, ?_⟩
          simpa only [List.foldl_cons, rightStep, hx] using And.intro hends hcounts
        | some x =>
          have hxmem := List.mem_of_mem_head? (Option.mem_def.mpr hx)
          have hpx : p < x := of_decide_eq_true (List.mem_filter.mp hxmem).2
          have hxq : x ∈ (ρ.extPositions j).filter (q < ·) :=
            List.mem_filter.mpr ⟨hext j (by simp) (List.mem_filter.mp hxmem).1,
              by simp only [decide_eq_true_eq]; omega⟩
          have hnonempty := List.ne_nil_of_mem hxq
          let y := ((ρ.extPositions j).filter (q < ·)).head hnonempty
          have hy : ((ρ.extPositions j).filter (q < ·)).head? = some y :=
            List.head?_eq_some_head hnonempty
          have hyx : y ≤ x := ((hSort ρ j).filter _).rel_head hxq
          obtain ⟨ks, hks, hends, hcounts⟩ := ih hrest x y (c + 1) (d + 1) hyx (by omega)
          refine ⟨j :: ks, hks.cons_cons j, ?_⟩
          simpa only [List.foldl_cons, rightStep, hx, hy] using And.intro hends hcounts
    have hLiveFold (υ : Context) : ∀ (ls : List ℕ) (z : ℕ × ℕ),
        ((ls.filter (fun j => υ.extPositions j ≠ [])).foldl (leftStep υ) z = ls.foldl (leftStep υ) z) ∧
        ((ls.filter (fun j => υ.extPositions j ≠ [])).foldl (rightStep υ) z = ls.foldl (rightStep υ) z) := by
      intro ls
      induction ls with
      | nil => intro z; exact ⟨rfl, rfl⟩
      | cons j ls ih =>
        intro z
        by_cases hj : υ.extPositions j ≠ []
        · simp only [List.filter_cons, decide_eq_true hj, if_true, List.foldl_cons]
          exact ⟨(ih _).1, (ih _).2⟩
        · have he : υ.extPositions j = [] := by tauto
          simp only [List.filter_cons, decide_eq_false hj, if_false, List.foldl_cons,
            leftStep, rightStep, he, List.filter_nil, List.getLast?_nil, List.head?_nil]
          exact ih z
    have hLiveSub {ρ υ : Context} (h : Sim ρ υ) (v : Side) (top : ℕ)
        (ls : List ℕ) (hls : ls.Sublist (υ.levelsOn v top)) :
        (ls.filter (fun j => υ.extPositions j ≠ [])).Sublist (ρ.levelsOn v top) := by
      let ks := ls.filter (fun j => υ.extPositions j ≠ [])
      have hks : ks.Pairwise (· < ·) := (((hSorted υ).filter _).sublist hls).filter _
      have hSubset : ks ⊆ ρ.levelsOn v top := by
        intro j hj
        have hjls := (List.mem_filter.mp hj).1
        have hjlive : υ.extPositions j ≠ [] := of_decide_eq_true (List.mem_filter.mp hj).2
        have hjυ := hls.subset hjls
        have hjρ : j ∈ ρ.levels := by
          rw [← hLevels h]
          exact (List.mem_filter.mp hjυ).1
        have hjc : υ.sideAt j = v ∧ (top = 0 ∨ j < top) :=
          of_decide_eq_true (List.mem_filter.mp hjυ).2
        rcases hHistory h j hjρ with hz | hn
        · exact False.elim (hjlive hz.1)
        · rw [hn.1] at hjc
          exact List.mem_filter.mpr ⟨hjρ, decide_eq_true hjc⟩
      have hEq : (ρ.levelsOn v top).filter (· ∈ ks) = ks := by
        apply (((hSorted ρ).filter _).filter _).eq_of_mem_iff hks
        intro j
        exact ⟨fun hj => of_decide_eq_true (List.mem_filter.mp hj).2,
          fun hj => List.mem_filter.mpr ⟨hSubset hj, decide_eq_true hj⟩⟩
      change ks.Sublist (ρ.levelsOn v top)
      rw [← hEq]
      exact List.filter_sublist
    have hLeft {ρ υ : Context} (h : Sim ρ υ) (v : Side) (top p : ℕ) :
        υ.leftExt v top p ≤ ρ.leftExt v top p := by
      simp only [leftExt_eq]
      apply Ctx.getD_max?_le_of_forall
      intro x hx
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
      let ks := ls.filter (fun j => υ.extPositions j ≠ [])
      have hsub : ks.Sublist (ρ.levelsOn v top) := hLiveSub h v top ls (List.mem_sublists.mp hls)
      have hext : ∀ j ∈ ks, υ.extPositions j ⊆ ρ.extPositions j :=
        fun j hj => hExtSubset h j (List.mem_filter.mp (hsub.subset hj)).1
      obtain ⟨ws, hws, _, hcount⟩ := hLeftWitness ρ υ ks hext p p 0 0 le_rfl le_rfl
      have heq := congrArg Prod.snd (hLiveFold υ ls (p,0)).1
      change (ks.foldl (leftStep υ) (p,0)).2 = (ls.foldl (leftStep υ) (p,0)).2 at heq
      rw [heq] at hcount
      exact ⟨_, List.mem_map.mpr ⟨ws, List.mem_sublists.mpr (hws.trans hsub), rfl⟩, hcount⟩
    have hRight {ρ υ : Context} (h : Sim ρ υ) (v : Side) (top p : ℕ) :
        υ.rightExt v top p ≤ ρ.rightExt v top p := by
      simp only [rightExt_eq]
      apply Ctx.getD_max?_le_of_forall
      intro x hx
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
      let ks := ls.filter (fun j => υ.extPositions j ≠ [])
      have hsub : ks.Sublist (ρ.levelsOn v top) := hLiveSub h v top ls (List.mem_sublists.mp hls)
      have hext : ∀ j ∈ ks, υ.extPositions j ⊆ ρ.extPositions j :=
        fun j hj => hExtSubset h j (List.mem_filter.mp (hsub.subset hj)).1
      obtain ⟨ws, hws, _, hcount⟩ := hRightWitness ρ υ ks hext p p 0 0 le_rfl le_rfl
      have heq := congrArg Prod.snd (hLiveFold υ ls (p,0)).2
      change (ks.foldl (rightStep υ) (p,0)).2 = (ls.foldl (rightStep υ) (p,0)).2 at heq
      rw [heq] at hcount
      exact ⟨_, List.mem_map.mpr ⟨ws, List.mem_sublists.mpr (hws.trans hsub), rfl⟩, hcount⟩
    have hChain {ρ υ : Context} (h : Sim ρ υ) (v : Side) (p q : ℕ) :
        υ.chainExt v p q ≤ ρ.chainExt v p q :=
      Nat.add_le_add (hLeft h v 0 p) (hRight h v 0 q)
    have hCutoff (ρ : Context) (s : Side) (top : ℕ) : (ρ.levelsOn s top).Sublist (ρ.levelsOn s 0) := by
      have he : ρ.levelsOn s top =
          (ρ.levelsOn s 0).filter (fun j => decide (top = 0 ∨ j < top)) := by
        simp only [levelsOn, List.filter_filter]
        apply List.filter_congr
        intro j _
        simp [Bool.and_comm]
      rw [he]
      exact List.filter_sublist
    have hLeftCutoff (ρ : Context) (s : Side) (top p : ℕ) : ρ.leftExt s top p ≤ ρ.leftExt s 0 p := by
      simp only [leftExt_eq]
      apply getD_max?_le_of_forall
      intro value hv
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
      exact ⟨_, List.mem_map.mpr ⟨ls,
        List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans (hCutoff ρ s top)), rfl⟩, le_rfl⟩
    have hRightCutoff (ρ : Context) (s : Side) (top p : ℕ) : ρ.rightExt s top p ≤ ρ.rightExt s 0 p := by
      simp only [rightExt_eq]
      apply getD_max?_le_of_forall
      intro value hv
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
      exact ⟨_, List.mem_map.mpr ⟨ls,
        List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans (hCutoff ρ s top)), rfl⟩, le_rfl⟩
    have hJoin {ρ υ : Context} (h : Sim ρ υ) (v : Side) (p q : ℕ) :
        υ.joinExt v p q ≤ ρ.joinExt v p q := by
      change max (υ.chainExt v p q) _ ≤ _
      apply max_le ((hChain h v p q).trans (ρ.chainExt_le_joinExt v p q))
      apply getD_max?_le
      intro value hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      have hjρ : j ∈ ρ.levels := by
        rw [← hLevels h]
        exact (List.mem_filter.mp hj).1
      rcases hHistory h j hjρ with hz | hn
      · rw [hz.2, Nat.add_zero]
        have hc := Nat.add_le_add (hLeftCutoff υ v j p) (hRightCutoff υ v j q)
        exact hc.trans ((hChain h v p q).trans (ρ.chainExt_le_joinExt v p q))
      · have hjc : υ.sideAt j = v ∧ (0 = 0 ∨ j < 0) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        rw [hn.1] at hjc
        have hjOn : j ∈ ρ.levelsOn v 0 := List.mem_filter.mpr ⟨hjρ, decide_eq_true hjc⟩
        have hm := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).map
          (fun i => ρ.leftExt v i p + ρ.rightExt v i q + ρ.maximumAt i))
          (List.mem_map.mpr ⟨j, hjOn, rfl⟩)
        have hterm := Nat.add_le_add (Nat.add_le_add (hLeft h v j p) (hRight h v j q)) hn.2.2
        exact hterm.trans (hm.trans (le_max_right _ _))
    have hLimits {ρ υ : Context} (h : Sim ρ υ) (p q : ℕ) :
        ρ.cupLimit p q ≤ υ.cupLimit p q ∧ ρ.capLimit p q ≤ υ.capLimit p q := by
      have hcl := hChain h Side.lower p q
      have hcu := hChain h Side.upper p q
      have hjl := hJoin h Side.lower p q
      have hju := hJoin h Side.upper p q
      have ha : ρ.a ≤ υ.a := h.1
      have hu : ρ.u ≤ υ.u := h.2.1
      simp only [cupLimit, capLimit, hK h]
      omega
    have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
        ∀ p j s, (ρ.part keep v m).letterAt p = Letter.ext j s → 1 ≤ j := by
      intro p j s hp
      have hpl : p < ρ.word.length := by
        by_contra h
        have hn := letterAt_of_length_le (ρ.part keep v m)
          (show (ρ.part keep v m).word.length ≤ p by rw [part_word_length]; omega)
        rw [hn] at hp
        cases hp
      cases he : ρ.letterAt p with
      | child =>
        rw [part_letterAt_of_child ρ keep v m hpl he] at hp
        split at hp
        · cases hp
        · cases hp
          omega
      | ext oldLevel oldSide =>
        rw [part_letterAt_of_ext ρ keep v m hpl he] at hp
        cases hp
        omega
    have hPartChildAt {ρ υ : Context} (h : Sim ρ υ) (keep : List ℕ) (v : Side) (m p : ℕ) :
        (ρ.part keep v m).letterAt p = Letter.child ↔
          (υ.part keep v m).letterAt p = Letter.child := by
      rcases h with ⟨_, _, _, hlen, hletters, _⟩
      by_cases hpl : p < ρ.word.length
      · have hpu : p < υ.word.length := by omega
        cases hr : ρ.letterAt p with
        | child =>
          have hs : υ.letterAt p = Letter.child := (hletters p).mp hr
          rw [part_letterAt_of_child ρ keep v m hpl hr, part_letterAt_of_child υ keep v m hpu hs]
        | ext j s =>
          have hs : υ.letterAt p ≠ Letter.child := by
            intro hc
            have he := (hletters p).mpr hc
            rw [hr] at he
            cases he
          cases ht : υ.letterAt p with
          | child => exact False.elim (hs ht)
          | ext i t =>
            rw [part_letterAt_of_ext ρ keep v m hpl hr, part_letterAt_of_ext υ keep v m hpu ht]
            simp
      · have hpρ : (ρ.part keep v m).word.length ≤ p := by rw [part_word_length]; omega
        have hpυ : (υ.part keep v m).word.length ≤ p := by rw [part_word_length]; omega
        rw [letterAt_of_length_le (ρ.part keep v m) hpρ, letterAt_of_length_le (υ.part keep v m) hpυ]
    have hPart {ρ υ : Context} (h : Sim ρ υ) (keep : List ℕ) (v : Side) (m : ℕ) :
        Sim (ρ.part keep v m) (υ.part keep v m) := by
      have hSaved := h
      obtain ⟨ha, hu, hk, hlen, hletters, hdepth, hhist, hρpos, hυpos⟩ := h
      refine ⟨ha, hu, hk, ?_, fun p => hPartChildAt hSaved keep v m p, ?_, ?_,
        hPartPositive ρ keep v m, hPartPositive υ keep v m⟩
      · simpa only [part_word_length] using hlen
      · change (m :: ρ.maxima).length = (m :: υ.maxima).length
        simp only [List.length_cons, hdepth]
      · intro j hj
        have hj' : j ∈ 1 :: ρ.levels.map (· + 1) := by simpa only [part_levels] using hj
        rcases List.mem_cons.mp hj' with hjone | hjold
        · subst j
          have hExtOne : (υ.part keep v m).extPositions 1 = (ρ.part keep v m).extPositions 1 := by
            rw [part_extPositions_one hυpos, part_extPositions_one hρpos, hChild hSaved]
          have hSideOne : (υ.part keep v m).sideAt 1 = (ρ.part keep v m).sideAt 1 := by
            by_cases hempty : (ρ.part keep v m).extPositions 1 = []
            · simp only [sideAt, hExtOne, hempty, List.head?_nil]
            · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hempty
              have hpυ : p ∈ (υ.part keep v m).extPositions 1 := by simpa only [hExtOne] using hp
              rw [part_sideAt_one_of_mem hυpos keep v m hpυ, part_sideAt_one_of_mem hρpos keep v m hp]
          refine Or.inr ⟨hSideOne, ?_, ?_⟩
          · intro p hp
            simpa only [hExtOne] using hp
          · simp only [part_maximumAt_one, le_refl]
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hjold
          have hi1 := one_le_of_mem_levels hi
          simpa only [part_sideAt_succ ρ keep v m hi1, part_sideAt_succ υ keep v m hi1,
            part_extPositions_succ ρ keep v m hi1, part_extPositions_succ υ keep v m hi1,
            part_maximumAt_succ ρ keep v m hi1, part_maximumAt_succ υ keep v m hi1] using hhist i hi
    have hBase {ρ υ : Context} (h : Sim ρ υ) : ρ.base ≤ υ.base := by
      rw [base_eq_baseOf, base_eq_baseOf, hChild h]
      cases hh : ρ.childPositions.head? with
      | none => exact le_rfl
      | some p =>
        simpa only [hK h] using baseOf_mono (k := ρ.k) (hLimits h p p).1 (hLimits h p p).2
    have hFuel : ∀ fuel (ρ υ : Context), Sim ρ υ → boundFuel fuel ρ ≤ boundFuel fuel υ := by
      intro fuel
      induction fuel with
      | zero => intro ρ υ _; exact le_rfl
      | succ fuel ih =>
        intro ρ υ h
        have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
            boundFuel fuel (ρ.part keep v m) ≤ boundFuel fuel (υ.part keep v m) :=
          ih _ _ (hPart h keep v m)
        simp only [boundFuel, hRuns h, hChild h, hBlocks h, hK h]
        split_ifs
        · exact hBase h
        · apply Ctx.getD_max?_le_of_forall
          intro x hx
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
          obtain ⟨keep, hkeep, d, hd, hx⟩ := hx
          rcases hx with rfl | rfl
          · refine ⟨_, ?_, Nat.add_le_add (hParts _ _ _) (hParts _ _ _)⟩
            simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
            exact ⟨keep, hkeep, d, hd, Or.inl rfl⟩
          · refine ⟨_, ?_, Nat.add_le_add (hParts _ _ _) (hParts _ _ _)⟩
            simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
            exact ⟨keep, hkeep, d, hd, Or.inr rfl⟩
    refine ⟨fun p q => hLimits hInitial p q, fun fuel => hFuel fuel σ τ hInitial, ?_⟩
    simpa only [bound, hChild hInitial] using hFuel (σ.childPositions.length + 1) σ τ hInitial

  have ctx_shared_side_rank_unions_full_interval_witnesses (σ : Ctx.Context) (t : Ctx.Side) (x : ℕ) :
    let active := σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    let lo := fun p => σ.leftExt t 0 p + 1
    let hi := fun p => budget - σ.rightExt t 0 p
    let interval := fun p => Finset.Icc (lo p) (hi p)
    let ranks := active.biUnion interval
    (active.filter (fun p => p < x)).biUnion interval = ranks →
    (active.filter (fun p => x < p)).biUnion interval = ranks →
    ranks.Nonempty →
    ranks = interval x ∧
    (∃ p ∈ active, p < x ∧ interval p = ranks) ∧
    (∃ q ∈ active, x < q ∧ interval q = ranks) := by
    classical
    let active := σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let budget := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
    let lo := fun p => σ.leftExt t 0 p + 1
    let hi := fun p => budget - σ.rightExt t 0 p
    let I := fun p => Finset.Icc (lo p) (hi p)
    let ranks := active.biUnion I
    change (active.filter (fun p => p < x)).biUnion I = ranks →
      (active.filter (fun p => x < p)).biUnion I = ranks → ranks.Nonempty →
      ranks = I x ∧ (∃ p ∈ active, p < x ∧ I p = ranks) ∧
        (∃ q ∈ active, x < q ∧ I q = ranks)
    intro hL hR hnonempty
    have hanchor := ctx_shared_side_rank_unions_anchor_endpoints σ t x hL hR
    have hLo (p : ℕ) (hp : p ∈ active) (hpx : p < x) : lo p = lo x := by
      have h := hanchor p (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
        (Finset.mem_filter.mp hp).2
      simpa only [if_pos hpx] using h
    have hHi (p : ℕ) (hp : p ∈ active) (hxp : x < p) : hi p = hi x := by
      have h := hanchor p (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
        (Finset.mem_filter.mp hp).2
      simpa only [if_neg (show ¬ p < x by omega)] using h
    have hMember (p : ℕ) (hp : p ∈ active) : I p ⊆ ranks := by
      intro r hr
      exact Finset.mem_biUnion.mpr ⟨p, hp, hr⟩
    have hSub : ranks ⊆ I x := by
      intro r hr
      have hl : r ∈ (active.filter (fun p => p < x)).biUnion I := by simpa only [hL] using hr
      have hr' : r ∈ (active.filter (fun p => x < p)).biUnion I := by simpa only [hR] using hr
      obtain ⟨p, hp, hpr⟩ := Finset.mem_biUnion.mp hl
      obtain ⟨q, hq, hqr⟩ := Finset.mem_biUnion.mp hr'
      have hlo := hLo p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
      have hhi := hHi q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
      have hpr' := Finset.mem_Icc.mp hpr
      have hqr' := Finset.mem_Icc.mp hqr
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hLoMem : lo x ∈ ranks := by
      obtain ⟨r, hr⟩ := hnonempty
      have hl : r ∈ (active.filter (fun p => p < x)).biUnion I := by simpa only [hL] using hr
      obtain ⟨p, hp, hpr⟩ := Finset.mem_biUnion.mp hl
      have hlo := hLo p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
      have hv := Finset.mem_Icc.mp hpr
      apply hMember p (Finset.mem_filter.mp hp).1
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hLoRight : lo x ∈ (active.filter (fun p => x < p)).biUnion I := by
      simpa only [hR] using hLoMem
    obtain ⟨q, hq, hqlo⟩ := Finset.mem_biUnion.mp hLoRight
    have hqactive := (Finset.mem_filter.mp hq).1
    have hxq := (Finset.mem_filter.mp hq).2
    have hqhi := hHi q hqactive hxq
    have hPivotQ : I x ⊆ I q := by
      intro r hr
      have hv := Finset.mem_Icc.mp hr
      have hqv := Finset.mem_Icc.mp hqlo
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hEq : ranks = I x := Finset.Subset.antisymm hSub (hPivotQ.trans (hMember q hqactive))
    have hHiMem : hi x ∈ ranks := by
      have hv := Finset.mem_Icc.mp (hSub hLoMem)
      rw [hEq]
      exact Finset.mem_Icc.mpr ⟨hv.2, le_rfl⟩
    have hHiLeft : hi x ∈ (active.filter (fun p => p < x)).biUnion I := by
      simpa only [hL] using hHiMem
    obtain ⟨p, hp, hphi⟩ := Finset.mem_biUnion.mp hHiLeft
    have hpactive := (Finset.mem_filter.mp hp).1
    have hpx := (Finset.mem_filter.mp hp).2
    have hplo := hLo p hpactive hpx
    have hPivotP : I x ⊆ I p := by
      intro r hr
      have hv := Finset.mem_Icc.mp hr
      have hpv := Finset.mem_Icc.mp hphi
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact ⟨hEq, ⟨p, hpactive, hpx,
      Finset.Subset.antisymm (hMember p hpactive) (hSub.trans hPivotP)⟩,
      ⟨q, hqactive, hxq, Finset.Subset.antisymm (hMember q hqactive) (hSub.trans hPivotQ)⟩⟩

  have ctx_pure_extensions_eq_of_live_axis_history (σ τ : Ctx.Context) (t : Ctx.Side) (top : ℕ)
    (hlevels : (σ.levelsOn t top).filter (fun j => σ.extPositions j ≠ []) =
      (τ.levelsOn t top).filter (fun j => τ.extPositions j ≠ []))
    (hhistory : ∀ j ∈ (σ.levelsOn t top).filter (fun i => σ.extPositions i ≠ []),
      σ.extPositions j = τ.extPositions j) :
    ∀ p, σ.leftExt t top p = τ.leftExt t top p ∧
      σ.rightExt t top p = τ.rightExt t top p := by
    classical
    have hLiveFold (υ : Context) : ∀ (ls : List ℕ) (z : ℕ × ℕ),
        ((ls.filter (fun j => υ.extPositions j ≠ [])).foldl (leftStep υ) z = ls.foldl (leftStep υ) z) ∧
        ((ls.filter (fun j => υ.extPositions j ≠ [])).foldl (rightStep υ) z = ls.foldl (rightStep υ) z) := by
      intro ls
      induction ls with
      | nil => intro z; exact ⟨rfl, rfl⟩
      | cons j ls ih =>
        intro z
        by_cases hj : υ.extPositions j ≠ []
        · simp only [List.filter_cons, decide_eq_true hj, if_true, List.foldl_cons]
          exact ⟨(ih _).1, (ih _).2⟩
        · have he : υ.extPositions j = [] := by tauto
          simp only [List.filter_cons, decide_eq_false hj, if_false, List.foldl_cons,
            leftStep, rightStep, he, List.filter_nil, List.getLast?_nil, List.head?_nil]
          exact ih z
    have hFolds (ρ υ : Context) : ∀ (ls : List ℕ),
        (∀ j ∈ ls, ρ.extPositions j = υ.extPositions j) → ∀ z,
        ls.foldl (leftStep ρ) z = ls.foldl (leftStep υ) z ∧
        ls.foldl (rightStep ρ) z = ls.foldl (rightStep υ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; exact ⟨rfl, rfl⟩
      | cons j ls ih =>
        intro hh z
        have hr := ih (fun i hi => hh i (List.mem_cons_of_mem _ hi))
        simp only [List.foldl_cons, leftStep, rightStep, hh j (by simp)]
        exact ⟨(hr _).1, (hr _).2⟩
    have hCompare (ρ υ : Context)
        (hl : (ρ.levelsOn t top).filter (fun j => ρ.extPositions j ≠ []) =
          (υ.levelsOn t top).filter (fun j => υ.extPositions j ≠ []))
        (he : ∀ j ∈ (ρ.levelsOn t top).filter (fun i => ρ.extPositions i ≠ []),
          ρ.extPositions j = υ.extPositions j) (p : ℕ) :
        ρ.leftExt t top p ≤ υ.leftExt t top p ∧
        ρ.rightExt t top p ≤ υ.rightExt t top p := by
      have hWitness (ls : List ℕ) (hls : ls.Sublist (ρ.levelsOn t top)) :
          (ls.filter (fun j => ρ.extPositions j ≠ [])).Sublist (υ.levelsOn t top) ∧
          (∀ j ∈ ls.filter (fun i => ρ.extPositions i ≠ []),
            ρ.extPositions j = υ.extPositions j) := by
        have hs := hls.filter (fun j => decide (ρ.extPositions j ≠ []))
        constructor
        · rw [hl] at hs
          exact hs.trans List.filter_sublist
        · intro j hj
          exact he j (hs.subset hj)
      constructor
      · simp only [leftExt_eq]
        apply getD_max?_le_of_forall
        intro value hv
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
        let ks := ls.filter (fun j => ρ.extPositions j ≠ [])
        obtain ⟨hsub, hext⟩ := hWitness ls (List.mem_sublists.mp hls)
        have hCount : (ls.foldl (leftStep ρ) (p,0)).2 =
            (ks.foldl (leftStep υ) (p,0)).2 :=
          (congrArg Prod.snd (hLiveFold ρ ls (p,0)).1).symm.trans
            (congrArg Prod.snd (hFolds ρ υ ks hext (p,0)).1)
        exact ⟨_, List.mem_map.mpr ⟨ks, List.mem_sublists.mpr hsub, rfl⟩, le_of_eq hCount⟩
      · simp only [rightExt_eq]
        apply getD_max?_le_of_forall
        intro value hv
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
        let ks := ls.filter (fun j => ρ.extPositions j ≠ [])
        obtain ⟨hsub, hext⟩ := hWitness ls (List.mem_sublists.mp hls)
        have hCount : (ls.foldl (rightStep ρ) (p,0)).2 =
            (ks.foldl (rightStep υ) (p,0)).2 :=
          (congrArg Prod.snd (hLiveFold ρ ls (p,0)).2).symm.trans
            (congrArg Prod.snd (hFolds ρ υ ks hext (p,0)).2)
        exact ⟨_, List.mem_map.mpr ⟨ks, List.mem_sublists.mpr hsub, rfl⟩, le_of_eq hCount⟩
    intro p
    have hστ := hCompare σ τ hlevels hhistory p
    have hτσ := hCompare τ σ hlevels.symm (fun j hj =>
      (hhistory j (by rw [hlevels]; exact hj)).symm) p
    exact ⟨le_antisymm hστ.1 hτσ.1, le_antisymm hστ.2 hτσ.2⟩

  have ctx_zero_maxima_single_axis_marker_upper_normalize (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (hzero : ∀ j ∈ σ.levels, σ.maximumAt j = 0)
    (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N) :
    let τ : Ctx.Context := { σ with word := (List.range σ.word.length).map (fun p =>
      match σ.letterAt p with
      | Ctx.Letter.child => Ctx.Letter.child
      | Ctx.Letter.ext j v => if j ∈ σ.levels ∧ σ.sideAt j = σ.sideAt N then
          if p = x then Ctx.Letter.ext j (σ.sideAt j)
            else Ctx.Letter.ext (σ.maxima.length + 1) v
          else Ctx.Letter.ext j v) }
    (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
    τ.childPositions = σ.childPositions ∧
    (∀ j ∈ σ.levels, τ.extPositions j =
      if σ.sideAt j = σ.sideAt N then (σ.extPositions j).filter (· = x)
      else σ.extPositions j) ∧
    (τ.sideAt N = σ.sideAt N ∧ x ∈ τ.extPositions N) ∧
    (∀ j ∈ τ.levelsOn (σ.sideAt N) 0, ∀ p ∈ τ.extPositions j, p = x) ∧
    (∀ t : Ctx.Side, σ.sideAt N ≠ t → ∀ top p,
      τ.leftExt t top p = σ.leftExt t top p ∧
        τ.rightExt t top p = σ.rightExt t top p) ∧
    (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧ σ.bound ≤ τ.bound := by
    classical
    let τ : Context := { σ with word := (List.range σ.word.length).map (fun p =>
      match σ.letterAt p with
      | Letter.child => Letter.child
      | Letter.ext j v => if j ∈ σ.levels ∧ σ.sideAt j = σ.sideAt N then
          if p = x then Letter.ext j (σ.sideAt j)
            else Letter.ext (σ.maxima.length + 1) v
          else Letter.ext j v) }
    change (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
      τ.childPositions = σ.childPositions ∧
      (∀ j ∈ σ.levels, τ.extPositions j =
        if σ.sideAt j = σ.sideAt N then (σ.extPositions j).filter (· = x)
        else σ.extPositions j) ∧
      (τ.sideAt N = σ.sideAt N ∧ x ∈ τ.extPositions N) ∧
      (∀ j ∈ τ.levelsOn (σ.sideAt N) 0, ∀ p ∈ τ.extPositions j, p = x) ∧
      (∀ t : Side, σ.sideAt N ≠ t → ∀ top p,
        τ.leftExt t top p = σ.leftExt t top p ∧ τ.rightExt t top p = σ.rightExt t top p) ∧
      (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
      (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ) ∧ σ.bound ≤ τ.bound
    have hLen : τ.word.length = σ.word.length := by simp [τ]
    have hLetter (p : ℕ) (hp : p < σ.word.length) :
        τ.letterAt p = (match σ.letterAt p with
          | Letter.child => Letter.child
          | Letter.ext j v => if j ∈ σ.levels ∧ σ.sideAt j = σ.sideAt N then
              if p = x then Letter.ext j (σ.sideAt j)
                else Letter.ext (σ.maxima.length + 1) v
              else Letter.ext j v) := by
      simp only [τ, letterAt, List.getElem?_map, List.getElem?_range hp,
        Option.map_some, Option.getD_some]
    have hIsChild (p : ℕ) : τ.letterAt p = Letter.child ↔ σ.letterAt p = Letter.child := by
      by_cases hp : p < σ.word.length
      · rw [hLetter p hp]
        cases σ.letterAt p with
        | child => rfl
        | ext i v =>
          by_cases hc : i ∈ σ.levels ∧ σ.sideAt i = σ.sideAt N <;> by_cases hk : p = x <;> simp [hc, hk]
      · rw [letterAt_of_length_le σ (by omega),
          letterAt_of_length_le τ (by rw [hLen]; omega)]
    have hChild : τ.childPositions = σ.childPositions := by
      simp only [childPositions, hLen, hIsChild]
    have hPos : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
      intro p j v hp
      have hpl : p < σ.word.length := by
        by_contra h
        rw [letterAt_of_length_le τ (by rw [hLen]; omega)] at hp
        cases hp
      rw [hLetter p hpl] at hp
      cases he : σ.letterAt p with
      | child => simp only [he] at hp; cases hp
      | ext i z =>
        have hi := hpositive p i z he
        simp only [he] at hp
        split_ifs at hp <;> have hij := (Letter.ext.inj hp).1 <;> omega
    have hDepthBound (j : ℕ) (hj : j ∈ σ.levels) : j ≤ σ.maxima.length := by
      simp only [levels, List.mem_map, List.mem_range] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      omega
    have hExt (j : ℕ) (hj : j ∈ σ.levels) :
        τ.extPositions j = if σ.sideAt j = σ.sideAt N then
          (σ.extPositions j).filter (· = x) else σ.extPositions j := by
      have hDj : σ.maxima.length + 1 ≠ j := by have h := hDepthBound j hj; omega
      by_cases hjs : σ.sideAt j = σ.sideAt N
      · simp only [if_pos hjs, extPositions, hLen, List.filter_filter]
        apply List.filter_congr
        intro p hp
        rw [hLetter p (List.mem_range.mp hp)]
        cases he : σ.letterAt p with
        | child => simp [he]
        | ext i v =>
          by_cases hi : i = j
          · subst i
            by_cases hpx : p = x <;> simp [he, hj, hjs, hpx, hDj]
          · by_cases hc : i ∈ σ.levels ∧ σ.sideAt i = σ.sideAt N <;>
              by_cases hpx : p = x <;> simp [he, hc, hpx, hi, hDj]
      · simp only [if_neg hjs, extPositions, hLen]
        apply List.filter_congr
        intro p hp
        rw [hLetter p (List.mem_range.mp hp)]
        cases he : σ.letterAt p with
        | child => rfl
        | ext i v =>
          by_cases hi : i = j
          · subst i
            simp [he, hj, hjs]
          · by_cases hc : i ∈ σ.levels ∧ σ.sideAt i = σ.sideAt N <;>
              by_cases hpx : p = x <;> simp [he, hc, hpx, hi, hDj]
    have hSubset (j : ℕ) (hj : j ∈ σ.levels) : τ.extPositions j ⊆ σ.extPositions j := by
      rw [hExt j hj]
      split_ifs
      · exact fun _ hp => (List.mem_filter.mp hp).1
      · exact fun _ hp => hp
    have hOtherSide (j : ℕ) (hj : j ∈ σ.levels) (hs : σ.sideAt j ≠ σ.sideAt N) :
        τ.sideAt j = σ.sideAt j := by
      have hExtOther : τ.extPositions j = σ.extPositions j := by
        rw [hExt j hj, if_neg hs]
      simp only [sideAt, hExtOther]
      cases hh : (σ.extPositions j).head? with
      | none => rfl
      | some p =>
        have hp := List.mem_of_mem_head? hh
        have hpl := List.mem_range.mp (List.mem_filter.mp hp).1
        dsimp only
        rw [hLetter p hpl]
        cases he : σ.letterAt p with
        | child => simp [extPositions, he] at hp
        | ext i v =>
          have hi : i = j := by
            have hz := (List.mem_filter.mp hp).2
            simpa only [he, decide_eq_true_eq] using hz
          subst i
          simp [hj, hs]
    have hLiveSide (j : ℕ) (hj : j ∈ σ.levels) (hne : τ.extPositions j ≠ []) :
        τ.sideAt j = σ.sideAt j := by
      by_cases hs : σ.sideAt j = σ.sideAt N
      · let p := (τ.extPositions j).head hne
        have hp : p ∈ τ.extPositions j := List.head_mem hne
        have hp' := hSubset j hj hp
        have hpx : p = x := by
          rw [hExt j hj, if_pos hs] at hp
          exact of_decide_eq_true (List.mem_filter.mp hp).2
        have hpl := List.mem_range.mp (List.mem_filter.mp hp').1
        have he : τ.letterAt p = Letter.ext j (σ.sideAt j) := by
          rw [hLetter p hpl]
          cases hsrc : σ.letterAt p with
          | child => simp [extPositions, hsrc] at hp'
          | ext i v =>
            have hi : i = j := by
              have hz := (List.mem_filter.mp hp').2
              simpa only [hsrc, decide_eq_true_eq] using hz
            subst i
            simp [hj, hs, hpx]
        simp only [sideAt, List.head?_eq_some_head hne]
        change (match τ.letterAt p with | Letter.ext _ v => v | _ => Side.lower) = σ.sideAt j
        rw [he]
      · exact hOtherSide j hj hs
    have hHistory : ∀ j ∈ σ.levels,
        (τ.extPositions j = [] ∧ τ.maximumAt j = 0) ∨
        (τ.sideAt j = σ.sideAt j ∧ τ.extPositions j ⊆ σ.extPositions j ∧
          τ.maximumAt j ≤ σ.maximumAt j) := by
      intro j hj
      by_cases he : τ.extPositions j = []
      · exact Or.inl ⟨he, hzero j hj⟩
      · exact Or.inr ⟨hLiveSide j hj he, hSubset j hj, le_rfl⟩
    have hMono := ctx_bound_mono_of_marker_inclusion_empty_zero_levels σ τ
      hpositive hPos le_rfl le_rfl rfl hLen.symm (fun p => (hIsChild p).symm) rfl hHistory
    have hxτ : x ∈ τ.extPositions N := by
      rw [hExt N hN, if_pos rfl]
      exact List.mem_filter.mpr ⟨hx, by simp⟩
    have hSelected : τ.sideAt N = σ.sideAt N ∧ x ∈ τ.extPositions N :=
      ⟨hLiveSide N hN (List.ne_nil_of_mem hxτ), hxτ⟩
    have hOnly : ∀ j ∈ τ.levelsOn (σ.sideAt N) 0, ∀ p ∈ τ.extPositions j, p = x := by
      intro j hj p hp
      have hjσ : j ∈ σ.levels := (List.mem_filter.mp hj).1
      have htj := (of_decide_eq_true (List.mem_filter.mp hj).2).1
      have hsj := hLiveSide j hjσ (List.ne_nil_of_mem hp)
      have hs : σ.sideAt j = σ.sideAt N := hsj.symm.trans htj
      rw [hExt j hjσ, if_pos hs] at hp
      exact of_decide_eq_true (List.mem_filter.mp hp).2
    have hOpposite (t : Side) (ht : σ.sideAt N ≠ t) (top p : ℕ) :
        τ.leftExt t top p = σ.leftExt t top p ∧ τ.rightExt t top p = σ.rightExt t top p := by
      have hLiveLevels : (σ.levelsOn t top).filter (fun j => σ.extPositions j ≠ []) =
          (τ.levelsOn t top).filter (fun j => τ.extPositions j ≠ []) := by
        simp only [levelsOn, List.filter_filter]
        change σ.levels.filter _ = σ.levels.filter _
        apply List.filter_congr
        intro j hj
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · intro h
          have hs : σ.sideAt j ≠ σ.sideAt N := by rw [h.2.1]; exact Ne.symm ht
          have he : τ.extPositions j = σ.extPositions j := by rw [hExt j hj, if_neg hs]
          exact ⟨by rw [he]; exact h.1, ⟨(hOtherSide j hj hs).trans h.2.1, h.2.2⟩⟩
        · intro h
          have hjt : σ.sideAt j = t := (hLiveSide j hj h.1).symm.trans h.2.1
          have hs : σ.sideAt j ≠ σ.sideAt N := by rw [hjt]; exact Ne.symm ht
          have he : τ.extPositions j = σ.extPositions j := by rw [hExt j hj, if_neg hs]
          exact ⟨by rw [← he]; exact h.1, ⟨hjt, h.2.2⟩⟩
      have hPositions : ∀ j ∈ (σ.levelsOn t top).filter (fun i => σ.extPositions i ≠ []),
          σ.extPositions j = τ.extPositions j := by
        intro j hj
        have hOn := (List.mem_filter.mp hj).1
        have hLevel := (List.mem_filter.mp hOn).1
        have hAxis := (of_decide_eq_true (List.mem_filter.mp hOn).2).1
        have hs : σ.sideAt j ≠ σ.sideAt N := by rw [hAxis]; exact Ne.symm ht
        rw [hExt j hLevel, if_neg hs]
      have hp := ctx_pure_extensions_eq_of_live_axis_history σ τ t top hLiveLevels hPositions p
      exact ⟨hp.1.symm, hp.2.symm⟩
    exact ⟨hPos, hChild, hExt, hSelected, hOnly, hOpposite, hMono⟩

  have ctx_pure_extension_eq_of_visible_axis_history (σ τ : Ctx.Context) (s : Ctx.Side) (top p q : ℕ) (leftward : Bool) :
    let visible := fun (ρ : Ctx.Context) (z j : ℕ) =>
      (ρ.extPositions j).filter (fun r => if leftward then r < z else z < r)
    (σ.levelsOn s top).filter (fun j => visible σ p j ≠ []) =
      (τ.levelsOn s top).filter (fun j => visible τ q j ≠ []) →
    (∀ j ∈ (σ.levelsOn s top).filter (fun i => visible σ p i ≠ []),
      visible σ p j = visible τ q j) →
    (if leftward then σ.leftExt s top p else σ.rightExt s top p) =
      (if leftward then τ.leftExt s top q else τ.rightExt s top q) := by
    classical
    cases leftward
    · let V (ρ : Context) (z j : ℕ) := (ρ.extPositions j).filter (fun r => z < r)
      change (σ.levelsOn s top).filter (fun j => V σ p j ≠ []) =
        (τ.levelsOn s top).filter (fun j => V τ q j ≠ []) →
        (∀ j ∈ (σ.levelsOn s top).filter (fun i => V σ p i ≠ []), V σ p j = V τ q j) →
        σ.rightExt s top p = τ.rightExt s top q
      intro hLevels hPositions
      have hNested (ρ : Context) (j z b : ℕ) (hz : b ≤ z) :
          V ρ z j = (V ρ b j).filter (fun r => z < r) := by
        simp only [V, List.filter_filter]
        apply List.filter_congr
        intro r hr
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      have hStepBound (ρ : Context) (j z c : ℕ) :
          z ≤ (rightStep ρ (z,c) j).1 := by
        cases hh : ((ρ.extPositions j).filter (fun r => z < r)).head? with
        | none => simp only [rightStep, hh]; exact le_rfl
        | some y =>
          have hy := List.mem_of_mem_head? (Option.mem_def.mpr hh)
          have hp := of_decide_eq_true (List.mem_filter.mp hy).2
          simpa only [rightStep, hh] using Nat.le_of_lt hp
      have hLiveFold (ρ : Context) (b : ℕ) : ∀ (ls : List ℕ) (z c : ℕ),
          b ≤ z →
          (ls.filter (fun j => V ρ b j ≠ [])).foldl (rightStep ρ) (z,c) =
            ls.foldl (rightStep ρ) (z,c) := by
        intro ls
        induction ls with
        | nil => intro z c hz; rfl
        | cons j ls ih =>
          intro z c hz
          by_cases hj : V ρ b j ≠ []
          · simp only [List.filter_cons, decide_eq_true hj, if_true, List.foldl_cons]
            exact ih _ _ (hz.trans (hStepBound ρ j z c))
          · have he : V ρ b j = [] := by tauto
            have hzv : V ρ z j = [] := by rw [hNested ρ j z b hz, he]; rfl
            change (ρ.extPositions j).filter (fun r => z < r) = [] at hzv
            have hs : rightStep ρ (z,c) j = (z,c) := by
              simp only [rightStep, hzv, List.head?_nil]
            simp only [List.filter_cons, decide_eq_false hj, Bool.false_eq_true, if_false,
              List.foldl_cons, hs]
            exact ih z c hz
      have hFixed (ρ υ : Context) (a b : ℕ) : ∀ (ls : List ℕ),
          (∀ j ∈ ls, V ρ a j = V υ b j) → ∀ z c,
          a ≤ z → b ≤ z →
          ls.foldl (rightStep ρ) (z,c) = ls.foldl (rightStep υ) (z,c) := by
        intro ls
        induction ls with
        | nil => intro he z c hza hzb; rfl
        | cons j ls ih =>
          intro he z c hza hzb
          have hext : V ρ z j = V υ z j := by
            rw [hNested ρ j z a hza, he j (by simp), ← hNested υ j z b hzb]
          change (ρ.extPositions j).filter (fun r => z < r) =
            (υ.extPositions j).filter (fun r => z < r) at hext
          have hs : rightStep ρ (z,c) j = rightStep υ (z,c) j := by
            simp only [rightStep, hext]
          have ht := ih (fun i hi => he i (List.mem_cons_of_mem _ hi))
            (rightStep ρ (z,c) j).1 (rightStep ρ (z,c) j).2
            (hza.trans (hStepBound ρ j z c)) (hzb.trans (hStepBound ρ j z c))
          simpa only [List.foldl_cons, ← hs] using ht
      have hStart (ρ υ : Context) (a b : ℕ) (ls : List ℕ)
          (hlive : ∀ j ∈ ls, V ρ a j ≠ []) (he : ∀ j ∈ ls, V ρ a j = V υ b j) :
          (ls.foldl (rightStep ρ) (a,0)).2 = (ls.foldl (rightStep υ) (b,0)).2 := by
        cases ls with
        | nil => rfl
        | cons j ls =>
          have hn := hlive j (by simp)
          let y := (V ρ a j).head hn
          have hy : y ∈ V ρ a j := List.head_mem hn
          have hy' : y ∈ V υ b j := by rw [← he j (by simp)]; exact hy
          have hya := of_decide_eq_true (List.mem_filter.mp hy).2
          have hyb := of_decide_eq_true (List.mem_filter.mp hy').2
          have ha : ((ρ.extPositions j).filter (fun r => a < r)).head? = some y :=
            List.head?_eq_some_head hn
          have hb : ((υ.extPositions j).filter (fun r => b < r)).head? = some y := by
            change (V υ b j).head? = some y
            rw [← he j (by simp)]
            exact ha
          have hf := hFixed ρ υ a b ls (fun i hi => he i (List.mem_cons_of_mem _ hi))
            y 1 (Nat.le_of_lt hya) (Nat.le_of_lt hyb)
          simpa only [List.foldl_cons, rightStep, ha, hb] using congrArg Prod.snd hf
      have hCompare (ρ υ : Context) (a b : ℕ)
          (hl : (ρ.levelsOn s top).filter (fun j => V ρ a j ≠ []) =
            (υ.levelsOn s top).filter (fun j => V υ b j ≠ []))
          (he : ∀ j ∈ (ρ.levelsOn s top).filter (fun i => V ρ a i ≠ []),
            V ρ a j = V υ b j) : ρ.rightExt s top a ≤ υ.rightExt s top b := by
        simp only [rightExt_eq]
        apply getD_max?_le_of_forall
        intro value hv
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
        let ks := ls.filter (fun j => V ρ a j ≠ [])
        have hks : ks.Sublist ((ρ.levelsOn s top).filter (fun j => V ρ a j ≠ [])) :=
          (List.mem_sublists.mp hls).filter _
        have hs : ks.Sublist (υ.levelsOn s top) := by
          have h := hks
          rw [hl] at h
          exact h.trans List.filter_sublist
        have hlive : ∀ j ∈ ks, V ρ a j ≠ [] :=
          fun j hj => of_decide_eq_true (List.mem_filter.mp hj).2
        have hext : ∀ j ∈ ks, V ρ a j = V υ b j := fun j hj => he j (hks.subset hj)
        have hCount : (ls.foldl (rightStep ρ) (a,0)).2 =
            (ks.foldl (rightStep υ) (b,0)).2 :=
          (congrArg Prod.snd (hLiveFold ρ a ls a 0 le_rfl)).symm.trans
            (hStart ρ υ a b ks hlive hext)
        exact ⟨_, List.mem_map.mpr ⟨ks, List.mem_sublists.mpr hs, rfl⟩, le_of_eq hCount⟩
      have hστ := hCompare σ τ p q hLevels hPositions
      have hτσ := hCompare τ σ q p hLevels.symm (fun j hj =>
        (hPositions j (by rw [hLevels]; exact hj)).symm)
      exact le_antisymm hστ hτσ
    · let V (ρ : Context) (z j : ℕ) := (ρ.extPositions j).filter (fun r => r < z)
      change (σ.levelsOn s top).filter (fun j => V σ p j ≠ []) =
        (τ.levelsOn s top).filter (fun j => V τ q j ≠ []) →
        (∀ j ∈ (σ.levelsOn s top).filter (fun i => V σ p i ≠ []), V σ p j = V τ q j) →
        σ.leftExt s top p = τ.leftExt s top q
      intro hLevels hPositions
      have hNested (ρ : Context) (j z b : ℕ) (hz : z ≤ b) :
          V ρ z j = (V ρ b j).filter (fun r => r < z) := by
        simp only [V, List.filter_filter]
        apply List.filter_congr
        intro r hr
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      have hStepBound (ρ : Context) (j z c : ℕ) :
          (leftStep ρ (z,c) j).1 ≤ z := by
        cases hh : ((ρ.extPositions j).filter (fun r => r < z)).getLast? with
        | none => simp only [leftStep, hh]; exact le_rfl
        | some y =>
          have hy := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
          have hp := of_decide_eq_true (List.mem_filter.mp hy).2
          simpa only [leftStep, hh] using Nat.le_of_lt hp
      have hLiveFold (ρ : Context) (b : ℕ) : ∀ (ls : List ℕ) (z c : ℕ),
          z ≤ b →
          (ls.filter (fun j => V ρ b j ≠ [])).foldl (leftStep ρ) (z,c) =
            ls.foldl (leftStep ρ) (z,c) := by
        intro ls
        induction ls with
        | nil => intro z c hz; rfl
        | cons j ls ih =>
          intro z c hz
          by_cases hj : V ρ b j ≠ []
          · simp only [List.filter_cons, decide_eq_true hj, if_true, List.foldl_cons]
            exact ih _ _ ((hStepBound ρ j z c).trans hz)
          · have he : V ρ b j = [] := by tauto
            have hzv : V ρ z j = [] := by rw [hNested ρ j z b hz, he]; rfl
            change (ρ.extPositions j).filter (fun r => r < z) = [] at hzv
            have hs : leftStep ρ (z,c) j = (z,c) := by
              simp only [leftStep, hzv, List.getLast?_nil]
            simp only [List.filter_cons, decide_eq_false hj, Bool.false_eq_true, if_false,
              List.foldl_cons, hs]
            exact ih z c hz
      have hFixed (ρ υ : Context) (a b : ℕ) : ∀ (ls : List ℕ),
          (∀ j ∈ ls, V ρ a j = V υ b j) → ∀ z c,
          z ≤ a → z ≤ b →
          ls.foldl (leftStep ρ) (z,c) = ls.foldl (leftStep υ) (z,c) := by
        intro ls
        induction ls with
        | nil => intro he z c hza hzb; rfl
        | cons j ls ih =>
          intro he z c hza hzb
          have hext : V ρ z j = V υ z j := by
            rw [hNested ρ j z a hza, he j (by simp), ← hNested υ j z b hzb]
          change (ρ.extPositions j).filter (fun r => r < z) =
            (υ.extPositions j).filter (fun r => r < z) at hext
          have hs : leftStep ρ (z,c) j = leftStep υ (z,c) j := by
            simp only [leftStep, hext]
          have ht := ih (fun i hi => he i (List.mem_cons_of_mem _ hi))
            (leftStep ρ (z,c) j).1 (leftStep ρ (z,c) j).2
            ((hStepBound ρ j z c).trans hza) ((hStepBound ρ j z c).trans hzb)
          simpa only [List.foldl_cons, ← hs] using ht
      have hStart (ρ υ : Context) (a b : ℕ) (ls : List ℕ)
          (hlive : ∀ j ∈ ls, V ρ a j ≠ []) (he : ∀ j ∈ ls, V ρ a j = V υ b j) :
          (ls.foldl (leftStep ρ) (a,0)).2 = (ls.foldl (leftStep υ) (b,0)).2 := by
        cases ls with
        | nil => rfl
        | cons j ls =>
          have hn := hlive j (by simp)
          let y := (V ρ a j).getLast hn
          have hy : y ∈ V ρ a j := List.getLast_mem hn
          have hy' : y ∈ V υ b j := by rw [← he j (by simp)]; exact hy
          have hya := of_decide_eq_true (List.mem_filter.mp hy).2
          have hyb := of_decide_eq_true (List.mem_filter.mp hy').2
          have ha : ((ρ.extPositions j).filter (fun r => r < a)).getLast? = some y :=
            List.getLast?_eq_some_getLast hn
          have hb : ((υ.extPositions j).filter (fun r => r < b)).getLast? = some y := by
            change (V υ b j).getLast? = some y
            rw [← he j (by simp)]
            exact ha
          have hf := hFixed ρ υ a b ls (fun i hi => he i (List.mem_cons_of_mem _ hi))
            y 1 (Nat.le_of_lt hya) (Nat.le_of_lt hyb)
          simpa only [List.foldl_cons, leftStep, ha, hb] using congrArg Prod.snd hf
      have hCompare (ρ υ : Context) (a b : ℕ)
          (hl : (ρ.levelsOn s top).filter (fun j => V ρ a j ≠ []) =
            (υ.levelsOn s top).filter (fun j => V υ b j ≠ []))
          (he : ∀ j ∈ (ρ.levelsOn s top).filter (fun i => V ρ a i ≠ []),
            V ρ a j = V υ b j) : ρ.leftExt s top a ≤ υ.leftExt s top b := by
        simp only [leftExt_eq]
        apply getD_max?_le_of_forall
        intro value hv
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
        let ks := ls.filter (fun j => V ρ a j ≠ [])
        have hks : ks.Sublist ((ρ.levelsOn s top).filter (fun j => V ρ a j ≠ [])) :=
          (List.mem_sublists.mp hls).filter _
        have hs : ks.Sublist (υ.levelsOn s top) := by
          have h := hks
          rw [hl] at h
          exact h.trans List.filter_sublist
        have hlive : ∀ j ∈ ks, V ρ a j ≠ [] :=
          fun j hj => of_decide_eq_true (List.mem_filter.mp hj).2
        have hext : ∀ j ∈ ks, V ρ a j = V υ b j := fun j hj => he j (hks.subset hj)
        have hCount : (ls.foldl (leftStep ρ) (a,0)).2 =
            (ks.foldl (leftStep υ) (b,0)).2 :=
          (congrArg Prod.snd (hLiveFold ρ a ls a 0 le_rfl)).symm.trans
            (hStart ρ υ a b ks hlive hext)
        exact ⟨_, List.mem_map.mpr ⟨ks, List.mem_sublists.mpr hs, rfl⟩, le_of_eq hCount⟩
      have hστ := hCompare σ τ p q hLevels hPositions
      have hτσ := hCompare τ σ q p hLevels.symm (fun j hj =>
        (hPositions j (by rw [hLevels]; exact hj)).symm)
      exact le_antisymm hστ hτσ

  have ctx_zero_axis_interior_marker_prune_upper_normalize (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (t : Ctx.Side) (l r : ℕ)
    (hzero : ∀ j ∈ σ.levels, σ.sideAt j = t → σ.maximumAt j = 0) :
    let τ : Ctx.Context := { σ with word := (List.range σ.word.length).map (fun p =>
      match σ.letterAt p with
      | Ctx.Letter.child => Ctx.Letter.child
      | Ctx.Letter.ext j v => if j ∈ σ.levels ∧ σ.sideAt j = t then
          if l ≤ p ∧ p ≤ r then Ctx.Letter.ext (σ.maxima.length + 1) v
            else Ctx.Letter.ext j (σ.sideAt j)
          else Ctx.Letter.ext j v) }
    (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
    τ.childPositions = σ.childPositions ∧
    (∀ j ∈ σ.levels, τ.extPositions j =
      if σ.sideAt j = t then (σ.extPositions j).filter (fun p => p < l ∨ r < p)
      else σ.extPositions j) ∧
    (∀ j ∈ σ.levels, τ.extPositions j ≠ [] → τ.sideAt j = σ.sideAt j) ∧
    (∀ s : Ctx.Side, t ≠ s → ∀ top p,
      τ.leftExt s top p = σ.leftExt s top p ∧ τ.rightExt s top p = σ.rightExt s top p) ∧
    (∀ top p, l ≤ p → p ≤ r →
      τ.leftExt t top p = σ.leftExt t top l ∧ τ.rightExt t top p = σ.rightExt t top r) ∧
    (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧ σ.bound ≤ τ.bound := by
    classical
    let τ : Context := { σ with word := (List.range σ.word.length).map (fun p =>
      match σ.letterAt p with
      | Letter.child => Letter.child
      | Letter.ext j v => if j ∈ σ.levels ∧ σ.sideAt j = t then
          if l ≤ p ∧ p ≤ r then Letter.ext (σ.maxima.length + 1) v
            else Letter.ext j (σ.sideAt j)
          else Letter.ext j v) }
    change (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
      τ.childPositions = σ.childPositions ∧
      (∀ j ∈ σ.levels, τ.extPositions j =
        if σ.sideAt j = t then (σ.extPositions j).filter (fun p => p < l ∨ r < p)
        else σ.extPositions j) ∧
      (∀ j ∈ σ.levels, τ.extPositions j ≠ [] → τ.sideAt j = σ.sideAt j) ∧
      (∀ s : Side, t ≠ s → ∀ top p,
        τ.leftExt s top p = σ.leftExt s top p ∧ τ.rightExt s top p = σ.rightExt s top p) ∧
      (∀ top p, l ≤ p → p ≤ r →
        τ.leftExt t top p = σ.leftExt t top l ∧ τ.rightExt t top p = σ.rightExt t top r) ∧
      (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
      (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ) ∧ σ.bound ≤ τ.bound
    have hLen : τ.word.length = σ.word.length := by simp [τ]
    have hLetter (p : ℕ) (hp : p < σ.word.length) :
        τ.letterAt p = (match σ.letterAt p with
          | Letter.child => Letter.child
          | Letter.ext j v => if j ∈ σ.levels ∧ σ.sideAt j = t then
              if l ≤ p ∧ p ≤ r then Letter.ext (σ.maxima.length + 1) v
                else Letter.ext j (σ.sideAt j)
              else Letter.ext j v) := by
      simp only [τ, letterAt, List.getElem?_map, List.getElem?_range hp,
        Option.map_some, Option.getD_some]
    have hIsChild (p : ℕ) : τ.letterAt p = Letter.child ↔ σ.letterAt p = Letter.child := by
      by_cases hp : p < σ.word.length
      · rw [hLetter p hp]
        cases σ.letterAt p with
        | child => rfl
        | ext i v =>
          by_cases hc : i ∈ σ.levels ∧ σ.sideAt i = t <;> by_cases hk : l ≤ p ∧ p ≤ r <;> simp [hc, hk]
      · rw [letterAt_of_length_le σ (by omega),
          letterAt_of_length_le τ (by rw [hLen]; omega)]
    have hChild : τ.childPositions = σ.childPositions := by
      simp only [childPositions, hLen, hIsChild]
    have hPos : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
      intro p j v hp
      have hpl : p < σ.word.length := by
        by_contra h
        rw [letterAt_of_length_le τ (by rw [hLen]; omega)] at hp
        cases hp
      rw [hLetter p hpl] at hp
      cases he : σ.letterAt p with
      | child => simp only [he] at hp; cases hp
      | ext i z =>
        have hi := hpositive p i z he
        simp only [he] at hp
        split_ifs at hp <;> have hij := (Letter.ext.inj hp).1 <;> omega
    have hDepthBound (j : ℕ) (hj : j ∈ σ.levels) : j ≤ σ.maxima.length := by
      simp only [levels, List.mem_map, List.mem_range] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      omega
    have hExt (j : ℕ) (hj : j ∈ σ.levels) :
        τ.extPositions j = if σ.sideAt j = t then
          (σ.extPositions j).filter (fun p => p < l ∨ r < p) else σ.extPositions j := by
      have hDj : σ.maxima.length + 1 ≠ j := by have h := hDepthBound j hj; omega
      by_cases hjs : σ.sideAt j = t
      · simp only [if_pos hjs, extPositions, hLen, List.filter_filter]
        apply List.filter_congr
        intro p hp
        have hkeep : (p < l ∨ r < p) ↔ ¬ (l ≤ p ∧ p ≤ r) := by omega
        rw [hLetter p (List.mem_range.mp hp)]
        cases he : σ.letterAt p with
        | child => simp [he]
        | ext i v =>
          by_cases hi : i = j
          · subst i
            by_cases hpx : l ≤ p ∧ p ≤ r <;> simp [he, hj, hjs, hpx, hDj, hkeep]
          · by_cases hc : i ∈ σ.levels ∧ σ.sideAt i = t <;>
              by_cases hpx : l ≤ p ∧ p ≤ r <;> simp [he, hc, hpx, hi, hDj, hkeep]
      · simp only [if_neg hjs, extPositions, hLen]
        apply List.filter_congr
        intro p hp
        have hkeep : (p < l ∨ r < p) ↔ ¬ (l ≤ p ∧ p ≤ r) := by omega
        rw [hLetter p (List.mem_range.mp hp)]
        cases he : σ.letterAt p with
        | child => rfl
        | ext i v =>
          by_cases hi : i = j
          · subst i
            simp [he, hj, hjs]
          · by_cases hc : i ∈ σ.levels ∧ σ.sideAt i = t <;>
              by_cases hpx : l ≤ p ∧ p ≤ r <;> simp [he, hc, hpx, hi, hDj, hkeep]
    have hSubset (j : ℕ) (hj : j ∈ σ.levels) : τ.extPositions j ⊆ σ.extPositions j := by
      rw [hExt j hj]
      split_ifs
      · exact fun _ hp => (List.mem_filter.mp hp).1
      · exact fun _ hp => hp
    have hOtherSide (j : ℕ) (hj : j ∈ σ.levels) (hs : σ.sideAt j ≠ t) :
        τ.sideAt j = σ.sideAt j := by
      have hExtOther : τ.extPositions j = σ.extPositions j := by
        rw [hExt j hj, if_neg hs]
      simp only [sideAt, hExtOther]
      cases hh : (σ.extPositions j).head? with
      | none => rfl
      | some p =>
        have hp := List.mem_of_mem_head? hh
        have hpl := List.mem_range.mp (List.mem_filter.mp hp).1
        dsimp only
        rw [hLetter p hpl]
        cases he : σ.letterAt p with
        | child => simp [extPositions, he] at hp
        | ext i v =>
          have hi : i = j := by
            have hz := (List.mem_filter.mp hp).2
            simpa only [he, decide_eq_true_eq] using hz
          subst i
          simp [hj, hs]
    have hLiveSide (j : ℕ) (hj : j ∈ σ.levels) (hne : τ.extPositions j ≠ []) :
        τ.sideAt j = σ.sideAt j := by
      by_cases hs : σ.sideAt j = t
      · let p := (τ.extPositions j).head hne
        have hp : p ∈ τ.extPositions j := List.head_mem hne
        have hp' := hSubset j hj hp
        have hpx : p < l ∨ r < p := by
          rw [hExt j hj, if_pos hs] at hp
          exact of_decide_eq_true (List.mem_filter.mp hp).2
        have hnot : ¬ (l ≤ p ∧ p ≤ r) := by omega
        have hpl := List.mem_range.mp (List.mem_filter.mp hp').1
        have he : τ.letterAt p = Letter.ext j (σ.sideAt j) := by
          rw [hLetter p hpl]
          cases hsrc : σ.letterAt p with
          | child => simp [extPositions, hsrc] at hp'
          | ext i v =>
            have hi : i = j := by
              have hz := (List.mem_filter.mp hp').2
              simpa only [hsrc, decide_eq_true_eq] using hz
            subst i
            simp [hj, hs, hnot]
        simp only [sideAt, List.head?_eq_some_head hne]
        change (match τ.letterAt p with | Letter.ext _ v => v | _ => Side.lower) = σ.sideAt j
        rw [he]
      · exact hOtherSide j hj hs
    have hHistory : ∀ j ∈ σ.levels,
        (τ.extPositions j = [] ∧ τ.maximumAt j = 0) ∨
        (τ.sideAt j = σ.sideAt j ∧ τ.extPositions j ⊆ σ.extPositions j ∧
          τ.maximumAt j ≤ σ.maximumAt j) := by
      intro j hj
      by_cases ht : σ.sideAt j = t
      · by_cases he : τ.extPositions j = []
        · exact Or.inl ⟨he, hzero j hj ht⟩
        · exact Or.inr ⟨hLiveSide j hj he, hSubset j hj, le_rfl⟩
      · exact Or.inr ⟨hOtherSide j hj ht, hSubset j hj, le_rfl⟩
    have hMono := ctx_bound_mono_of_marker_inclusion_empty_zero_levels σ τ
      hpositive hPos le_rfl le_rfl rfl hLen.symm (fun p => (hIsChild p).symm) rfl hHistory
    have hOpposite (s : Side) (ht : t ≠ s) (top p : ℕ) :
        τ.leftExt s top p = σ.leftExt s top p ∧ τ.rightExt s top p = σ.rightExt s top p := by
      have hLiveLevels : (σ.levelsOn s top).filter (fun j => σ.extPositions j ≠ []) =
          (τ.levelsOn s top).filter (fun j => τ.extPositions j ≠ []) := by
        simp only [levelsOn, List.filter_filter]
        change σ.levels.filter _ = σ.levels.filter _
        apply List.filter_congr
        intro j hj
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · intro h
          have hs : σ.sideAt j ≠ t := by rw [h.2.1]; exact Ne.symm ht
          have he : τ.extPositions j = σ.extPositions j := by rw [hExt j hj, if_neg hs]
          exact ⟨by rw [he]; exact h.1, ⟨(hOtherSide j hj hs).trans h.2.1, h.2.2⟩⟩
        · intro h
          have hjt : σ.sideAt j = s := (hLiveSide j hj h.1).symm.trans h.2.1
          have hs : σ.sideAt j ≠ t := by rw [hjt]; exact Ne.symm ht
          have he : τ.extPositions j = σ.extPositions j := by rw [hExt j hj, if_neg hs]
          exact ⟨by rw [← he]; exact h.1, ⟨hjt, h.2.2⟩⟩
      have hPositions : ∀ j ∈ (σ.levelsOn s top).filter (fun i => σ.extPositions i ≠ []),
          σ.extPositions j = τ.extPositions j := by
        intro j hj
        have hOn := (List.mem_filter.mp hj).1
        have hLevel := (List.mem_filter.mp hOn).1
        have hAxis := (of_decide_eq_true (List.mem_filter.mp hOn).2).1
        have hs : σ.sideAt j ≠ t := by rw [hAxis]; exact Ne.symm ht
        rw [hExt j hLevel, if_neg hs]
      have hp := ctx_pure_extensions_eq_of_live_axis_history σ τ s top hLiveLevels hPositions p
      exact ⟨hp.1.symm, hp.2.symm⟩
    have hInterior : ∀ top p, l ≤ p → p ≤ r →
        τ.leftExt t top p = σ.leftExt t top l ∧ τ.rightExt t top p = σ.rightExt t top r := by
      intro top p hl hr
      constructor
      · let V (ρ : Context) (b j : ℕ) := (ρ.extPositions j).filter (fun z => z < b)
        have hVis (j : ℕ) (hj : j ∈ σ.levels) (hjt : σ.sideAt j = t) :
            V τ p j = V σ l j := by
          dsimp only [V]
          rw [hExt j hj, if_pos hjt, List.filter_filter]
          apply List.filter_congr
          intro z hz
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
        have hVNonempty (j b : ℕ) (hv : V τ b j ≠ []) : τ.extPositions j ≠ [] := by
          intro he
          apply hv
          simp only [V, he, List.filter_nil]
        have hLiveLevels : (σ.levelsOn t top).filter (fun j => V σ l j ≠ []) =
            (τ.levelsOn t top).filter (fun j => V τ p j ≠ []) := by
          simp only [levelsOn, List.filter_filter]
          change σ.levels.filter _ = σ.levels.filter _
          apply List.filter_congr
          intro j hj
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · intro h
            have he := hVis j hj h.2.1
            have hv : V τ p j ≠ [] := by rw [he]; exact h.1
            have hs := hLiveSide j hj (hVNonempty j p hv)
            exact ⟨hv, ⟨hs.trans h.2.1, h.2.2⟩⟩
          · intro h
            have hs := hLiveSide j hj (hVNonempty j p h.1)
            have hjt : σ.sideAt j = t := hs.symm.trans h.2.1
            have he := hVis j hj hjt
            exact ⟨by rw [← he]; exact h.1, ⟨hjt, h.2.2⟩⟩
        have hPositions : ∀ j ∈ (σ.levelsOn t top).filter (fun i => V σ l i ≠ []),
            V σ l j = V τ p j := by
          intro j hj
          have hOn := (List.mem_filter.mp hj).1
          have hLevel := (List.mem_filter.mp hOn).1
          have hAxis := (of_decide_eq_true (List.mem_filter.mp hOn).2).1
          exact (hVis j hLevel hAxis).symm
        have hTrace := ctx_pure_extension_eq_of_visible_axis_history σ τ t top l p true
          hLiveLevels hPositions
        change σ.leftExt t top l = τ.leftExt t top p at hTrace
        exact hTrace.symm
      · let V (ρ : Context) (b j : ℕ) := (ρ.extPositions j).filter (fun z => b < z)
        have hVis (j : ℕ) (hj : j ∈ σ.levels) (hjt : σ.sideAt j = t) :
            V τ p j = V σ r j := by
          dsimp only [V]
          rw [hExt j hj, if_pos hjt, List.filter_filter]
          apply List.filter_congr
          intro z hz
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
        have hVNonempty (j b : ℕ) (hv : V τ b j ≠ []) : τ.extPositions j ≠ [] := by
          intro he
          apply hv
          simp only [V, he, List.filter_nil]
        have hLiveLevels : (σ.levelsOn t top).filter (fun j => V σ r j ≠ []) =
            (τ.levelsOn t top).filter (fun j => V τ p j ≠ []) := by
          simp only [levelsOn, List.filter_filter]
          change σ.levels.filter _ = σ.levels.filter _
          apply List.filter_congr
          intro j hj
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · intro h
            have he := hVis j hj h.2.1
            have hv : V τ p j ≠ [] := by rw [he]; exact h.1
            have hs := hLiveSide j hj (hVNonempty j p hv)
            exact ⟨hv, ⟨hs.trans h.2.1, h.2.2⟩⟩
          · intro h
            have hs := hLiveSide j hj (hVNonempty j p h.1)
            have hjt : σ.sideAt j = t := hs.symm.trans h.2.1
            have he := hVis j hj hjt
            exact ⟨by rw [← he]; exact h.1, ⟨hjt, h.2.2⟩⟩
        have hPositions : ∀ j ∈ (σ.levelsOn t top).filter (fun i => V σ r i ≠ []),
            V σ r j = V τ p j := by
          intro j hj
          have hOn := (List.mem_filter.mp hj).1
          have hLevel := (List.mem_filter.mp hOn).1
          have hAxis := (of_decide_eq_true (List.mem_filter.mp hOn).2).1
          exact (hVis j hLevel hAxis).symm
        have hTrace := ctx_pure_extension_eq_of_visible_axis_history σ τ t top r p false
          hLiveLevels hPositions
        change σ.rightExt t top r = τ.rightExt t top p at hTrace
        exact hTrace.symm
    exact ⟨hPos, hChild, hExt, hLiveSide, hOpposite, hInterior, hMono⟩

  have ctx_shared_rank_uniform_interval_upper_normalize (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (hzero : ∀ j ∈ σ.levels, σ.maximumAt j = 0)
    (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
    (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
    (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [])
    (hactive : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p) :
    let G := fun (ρ : Ctx.Context) => match (generalizing := false) t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
    let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
      (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    let I := fun (ρ : Ctx.Context) (p : ℕ) =>
      Finset.Icc (ρ.leftExt t 0 p + 1) (G ρ - 1 - ρ.rightExt t 0 p)
    let ranks := fun (ρ : Ctx.Context) => (active ρ).biUnion (I ρ)
    ((active σ).filter (fun p => p < x)).biUnion (I σ) = ranks σ →
    ((active σ).filter (fun p => x < p)).biUnion (I σ) = ranks σ →
    (ranks σ).Nonempty →
    ∃ τ : Ctx.Context,
      τ.a = σ.a ∧ τ.u = σ.u ∧ τ.k = σ.k ∧ τ.maxima = σ.maxima ∧
      τ.childPositions = σ.childPositions ∧
      (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
      N ∈ τ.levels ∧ τ.sideAt N = s ∧ x ∈ τ.extPositions N ∧
      (∀ j ∈ τ.levelsOn s N, τ.extPositions j = []) ∧
      (∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p) ∧
      (∀ p ∈ τ.childPositions, I τ p = ranks σ) ∧
      (∀ j ∈ τ.levelsOn t 0, ∀ z ∈ τ.extPositions j,
        ∀ p ∈ τ.childPositions, ∀ q ∈ τ.childPositions, z < min p q ∨ max p q < z) ∧
      ranks τ = ranks σ ∧
      (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧ σ.bound ≤ τ.bound := by
    classical
    let G := fun (ρ : Context) => match t with | Side.lower => ρ.u | Side.upper => ρ.a
    let active := fun (ρ : Context) => ρ.childPositions.toFinset.filter
      (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    let I := fun (ρ : Context) (p : ℕ) =>
      Finset.Icc (ρ.leftExt t 0 p + 1) (G ρ - 1 - ρ.rightExt t 0 p)
    let ranks := fun (ρ : Context) => (active ρ).biUnion (I ρ)
    change ((active σ).filter (fun p => p < x)).biUnion (I σ) = ranks σ →
      ((active σ).filter (fun p => x < p)).biUnion (I σ) = ranks σ →
      (ranks σ).Nonempty →
      ∃ τ : Context,
        τ.a = σ.a ∧ τ.u = σ.u ∧ τ.k = σ.k ∧ τ.maxima = σ.maxima ∧
        τ.childPositions = σ.childPositions ∧
        (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
        N ∈ τ.levels ∧ τ.sideAt N = s ∧ x ∈ τ.extPositions N ∧
        (∀ j ∈ τ.levelsOn s N, τ.extPositions j = []) ∧
        (∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p) ∧
        (∀ p ∈ τ.childPositions, I τ p = ranks σ) ∧
        (∀ j ∈ τ.levelsOn t 0, ∀ z ∈ τ.extPositions j,
          ∀ p ∈ τ.childPositions, ∀ q ∈ τ.childPositions, z < min p q ∨ max p q < z) ∧
        ranks τ = ranks σ ∧
        (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ) ∧ σ.bound ≤ τ.bound
    intro hL hR hNonempty
    have hAnchor := ctx_shared_side_rank_unions_anchor_endpoints σ t x hL hR
    have hWitness := ctx_shared_side_rank_unions_full_interval_witnesses σ t x hL hR hNonempty
    obtain ⟨hPivot, ⟨pL, hpL, hpLx, hIL⟩, ⟨pR, hpR, hxpR, hIR⟩⟩ := hWitness
    have hANE : (active σ).Nonempty := ⟨pL, hpL⟩
    let l := (active σ).min' hANE
    let r := (active σ).max' hANE
    have hlA : l ∈ active σ := Finset.min'_mem _ _
    have hrA : r ∈ active σ := Finset.max'_mem _ _
    have hlx : l < x := lt_of_le_of_lt (Finset.min'_le _ pL hpL) hpLx
    have hxr : x < r := lt_of_lt_of_le hxpR (Finset.le_max' _ pR hpR)
    have hLo : σ.leftExt t 0 l + 1 = σ.leftExt t 0 x + 1 := by
      have hh := hAnchor l (List.mem_toFinset.mp (Finset.mem_filter.mp hlA).1)
        (Finset.mem_filter.mp hlA).2
      simpa only [if_pos hlx] using hh
    have hHi : G σ - 1 - σ.rightExt t 0 r = G σ - 1 - σ.rightExt t 0 x := by
      have hh := hAnchor r (List.mem_toFinset.mp (Finset.mem_filter.mp hrA).1)
        (Finset.mem_filter.mp hrA).2
      simpa only [if_neg (show ¬ r < x by omega)] using hh
    have hBounds (p : ℕ) (hp : p ∈ σ.childPositions) : l ≤ p ∧ p ≤ r := by
      have ha : p ∈ active σ := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hp, hactive p hp⟩
      exact ⟨Finset.min'_le _ p ha, Finset.le_max' _ p ha⟩
    let τ : Context := { σ with word := (List.range σ.word.length).map (fun p =>
      match σ.letterAt p with
      | Letter.child => Letter.child
      | Letter.ext j v => if j ∈ σ.levels ∧ σ.sideAt j = t then
          if l ≤ p ∧ p ≤ r then Letter.ext (σ.maxima.length + 1) v
            else Letter.ext j (σ.sideAt j)
          else Letter.ext j v) }
    have hn := ctx_zero_axis_interior_marker_prune_upper_normalize σ hpositive t l r
      (fun j hj _ => hzero j hj)
    obtain ⟨hPos, hChild, hExt, hLive, hOpp, hInterior, hLimits, hFuel, hBound⟩ := hn
    change τ.childPositions = σ.childPositions at hChild
    have hNt : σ.sideAt N ≠ t := by rw [hNs]; exact hne
    have hExtN : τ.extPositions N = σ.extPositions N := by
      rw [hExt N hN, if_neg hNt]
    have hxτ : x ∈ τ.extPositions N := by rw [hExtN]; exact hx
    have hNsτ : τ.sideAt N = s := (hLive N hN (List.ne_nil_of_mem hxτ)).trans hNs
    have hNτ : N ∈ τ.levels := hN
    have hYoungτ : ∀ j ∈ τ.levelsOn s N, τ.extPositions j = [] := by
      intro j hj
      by_cases he : τ.extPositions j = []
      · exact he
      have hjσ : j ∈ σ.levels := (List.mem_filter.mp hj).1
      have hc : τ.sideAt j = s ∧ (N = 0 ∨ j < N) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      have hjs : σ.sideAt j = s := (hLive j hjσ he).symm.trans hc.1
      have hjOn : j ∈ σ.levelsOn s N := List.mem_filter.mpr ⟨hjσ, decide_eq_true ⟨hjs, hc.2⟩⟩
      have hjt : σ.sideAt j ≠ t := by rw [hjs]; exact hne
      have hEq : τ.extPositions j = σ.extPositions j := by rw [hExt j hjσ, if_neg hjt]
      exact hEq.trans (hyoung j hjOn)
    have hAllτ : ∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := by
      intro p hp
      have hpσ : p ∈ σ.childPositions := by rw [← hChild]; exact hp
      have ha := hactive p hpσ
      have hh := hLimits p p
      exact ⟨lt_of_lt_of_le ha.1 hh.1, lt_of_lt_of_le ha.2 hh.2⟩
    have hUniform (p : ℕ) (hp : p ∈ τ.childPositions) : I τ p = ranks σ := by
      have hpσ : p ∈ σ.childPositions := by rw [← hChild]; exact hp
      have hb := hBounds p hpσ
      have hh := hInterior 0 p hb.1 hb.2
      have hG : G τ = G σ := rfl
      dsimp only [I]
      rw [hG, hh.1, hh.2, hLo, hHi]
      exact hPivot.symm
    have hOutside : ∀ j ∈ τ.levelsOn t 0, ∀ z ∈ τ.extPositions j,
        ∀ p ∈ τ.childPositions, ∀ q ∈ τ.childPositions, z < min p q ∨ max p q < z := by
      intro j hj z hz p hp q hq
      have hjσ : j ∈ σ.levels := (List.mem_filter.mp hj).1
      have hjt : τ.sideAt j = t := by simpa using (List.mem_filter.mp hj).2
      have hjs : σ.sideAt j = t := (hLive j hjσ (List.ne_nil_of_mem hz)).symm.trans hjt
      have he := hExt j hjσ
      rw [if_pos hjs] at he
      rw [he] at hz
      have hz' : z < l ∨ r < z := of_decide_eq_true (List.mem_filter.mp hz).2
      have hpσ : p ∈ σ.childPositions := by rw [← hChild]; exact hp
      have hqσ : q ∈ σ.childPositions := by rw [← hChild]; exact hq
      have hbp := hBounds p hpσ
      have hbq := hBounds q hqσ
      omega
    have hActive : active τ = active σ := by
      ext p
      simp only [active, Finset.mem_filter, List.mem_toFinset, hChild]
      constructor
      · intro hp
        exact ⟨hp.1, hactive p hp.1⟩
      · intro hp
        have hpτ : p ∈ τ.childPositions := by rw [hChild]; exact hp.1
        exact ⟨hp.1, hAllτ p hpτ⟩
    have hRanks : ranks τ = ranks σ := by
      ext z
      constructor
      · intro hz
        obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
        have hc := List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
        rw [hUniform p hc] at hz
        exact hz
      · intro hz
        have hp : pL ∈ active τ := by rw [hActive]; exact hpL
        have hc := List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
        apply Finset.mem_biUnion.mpr
        refine ⟨pL, hp, ?_⟩
        rw [hUniform pL hc]
        exact hz
    exact ⟨τ, rfl, rfl, rfl, rfl, hChild, hPos, hNτ, hNsτ, hxτ,
      hYoungτ, hAllτ, hUniform, hOutside, hRanks, hFuel, hBound⟩

  have ctx_shared_rank_single_marker_upper_normalize (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (hzero : ∀ j ∈ σ.levels, σ.maximumAt j = 0)
    (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
    (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
    (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [])
    (hactive : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p) :
    let G := fun (ρ : Ctx.Context) => match (generalizing := false) t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
    let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
      (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    let I := fun (ρ : Ctx.Context) (p : ℕ) =>
      Finset.Icc (ρ.leftExt t 0 p + 1) (G ρ - 1 - ρ.rightExt t 0 p)
    let ranks := fun (ρ : Ctx.Context) => (active ρ).biUnion (I ρ)
    ((active σ).filter (fun p => p < x)).biUnion (I σ) = ranks σ →
    ((active σ).filter (fun p => x < p)).biUnion (I σ) = ranks σ →
    (ranks σ).Nonempty →
    ∃ τ : Ctx.Context,
      τ.a = σ.a ∧ τ.u = σ.u ∧ τ.k = σ.k ∧ τ.maxima = σ.maxima ∧
      τ.childPositions = σ.childPositions ∧
      (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
      N ∈ τ.levels ∧ τ.sideAt N = s ∧ x ∈ τ.extPositions N ∧
      (∀ j ∈ τ.levelsOn s N, τ.extPositions j = []) ∧
      (∀ j ∈ τ.levelsOn s 0, ∀ p ∈ τ.extPositions j, p = x) ∧
      (∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p) ∧
      (∀ p ∈ τ.childPositions, I τ p = ranks σ) ∧
      (∀ j ∈ τ.levelsOn t 0, ∀ z ∈ τ.extPositions j,
        ∀ p ∈ τ.childPositions, ∀ q ∈ τ.childPositions, z < min p q ∨ max p q < z) ∧
      ranks τ = ranks σ ∧
      (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧ σ.bound ≤ τ.bound := by
    classical
    let G := fun (ρ : Context) => match t with | Side.lower => ρ.u | Side.upper => ρ.a
    let active := fun (ρ : Context) => ρ.childPositions.toFinset.filter
      (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    let I := fun (ρ : Context) (p : ℕ) =>
      Finset.Icc (ρ.leftExt t 0 p + 1) (G ρ - 1 - ρ.rightExt t 0 p)
    let ranks := fun (ρ : Context) => (active ρ).biUnion (I ρ)
    change ((active σ).filter (fun p => p < x)).biUnion (I σ) = ranks σ →
      ((active σ).filter (fun p => x < p)).biUnion (I σ) = ranks σ →
      (ranks σ).Nonempty →
      ∃ τ : Context,
        τ.a = σ.a ∧ τ.u = σ.u ∧ τ.k = σ.k ∧ τ.maxima = σ.maxima ∧
        τ.childPositions = σ.childPositions ∧
        (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
        N ∈ τ.levels ∧ τ.sideAt N = s ∧ x ∈ τ.extPositions N ∧
        (∀ j ∈ τ.levelsOn s N, τ.extPositions j = []) ∧
        (∀ j ∈ τ.levelsOn s 0, ∀ p ∈ τ.extPositions j, p = x) ∧
        (∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p) ∧
        (∀ p ∈ τ.childPositions, I τ p = ranks σ) ∧
        (∀ j ∈ τ.levelsOn t 0, ∀ z ∈ τ.extPositions j,
          ∀ p ∈ τ.childPositions, ∀ q ∈ τ.childPositions, z < min p q ∨ max p q < z) ∧
        ranks τ = ranks σ ∧
        (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ) ∧ σ.bound ≤ τ.bound
    intro hL hR hNonempty
    obtain ⟨ρ, hAρ, hUρ, hKρ, hMaxρ, hChildρ, hPosρ, hNρ, hNsρ, hxρ,
        hYoungρ, hAllρ, hUniformρ, hOutsideρ, hRanksρ, hFuelρ, hBoundρ⟩ :=
      ctx_shared_rank_uniform_interval_upper_normalize σ hpositive hzero s t hne N x
        hN hNs hx hyoung hactive hL hR hNonempty
    have hZeroρ : ∀ j ∈ ρ.levels, ρ.maximumAt j = 0 := by
      intro j hj
      have hjσ : j ∈ σ.levels := by simpa only [levels, hMaxρ] using hj
      simpa only [maximumAt, hMaxρ] using hzero j hjσ
    let τ : Context := { ρ with word := (List.range ρ.word.length).map (fun p =>
      match ρ.letterAt p with
      | Letter.child => Letter.child
      | Letter.ext j v => if j ∈ ρ.levels ∧ ρ.sideAt j = ρ.sideAt N then
          if p = x then Letter.ext j (ρ.sideAt j)
            else Letter.ext (ρ.maxima.length + 1) v
          else Letter.ext j v) }
    have hn := ctx_zero_maxima_single_axis_marker_upper_normalize ρ hPosρ hZeroρ N x hNρ hxρ
    obtain ⟨hPosτ, hChildτρ, hExt, ⟨hSideN, hxτ⟩, hOnly, hOpp, hLimits, hFuelτρ, hBoundτρ⟩ := hn
    change τ.childPositions = ρ.childPositions at hChildτρ
    change τ.sideAt N = ρ.sideAt N at hSideN
    change x ∈ τ.extPositions N at hxτ
    change (∀ j ∈ τ.levelsOn (ρ.sideAt N) 0, ∀ p ∈ τ.extPositions j, p = x) at hOnly
    have hChildτ : τ.childPositions = σ.childPositions := hChildτρ.trans hChildρ
    have hNsτ : τ.sideAt N = s := hSideN.trans hNsρ
    have hNτ : N ∈ τ.levels := hNρ
    have hOnlyτ : ∀ j ∈ τ.levelsOn s 0, ∀ p ∈ τ.extPositions j, p = x := by
      simpa only [hNsρ] using hOnly
    have hNpos : 0 < N := by
      obtain ⟨i, hi, he⟩ := List.mem_map.mp hNτ
      omega
    have hYoungτ : ∀ j ∈ τ.levelsOn s N, τ.extPositions j = [] := by
      intro j hj
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro p hp
      have hc : τ.sideAt j = s ∧ (N = 0 ∨ j < N) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      have hj0 : j ∈ τ.levelsOn s 0 := List.mem_filter.mpr
        ⟨(List.mem_filter.mp hj).1, decide_eq_true ⟨hc.1, Or.inl rfl⟩⟩
      have hpx := hOnlyτ j hj0 p hp
      subst p
      have hjx := (List.mem_filter.mp hp).2
      have hNx := (List.mem_filter.mp hxτ).2
      have hjN : j = N := by
        cases he : τ.letterAt x with
        | child => simp [he] at hjx
        | ext l v =>
          have hl : l = j := by simpa only [he, decide_eq_true_eq] using hjx
          have hlN : l = N := by simpa only [he, decide_eq_true_eq] using hNx
          exact hl.symm.trans hlN
      omega
    have hAllτ : ∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := by
      intro p hp
      have hpρ : p ∈ ρ.childPositions := by rw [← hChildτρ]; exact hp
      have ha := hAllρ p hpρ
      have hh := hLimits p p
      exact ⟨lt_of_lt_of_le ha.1 hh.1, lt_of_lt_of_le ha.2 hh.2⟩
    have hOpposite : ρ.sideAt N ≠ t := by rw [hNsρ]; exact hne
    have hI (p : ℕ) : I τ p = I ρ p := by
      have hh := hOpp t hOpposite 0 p
      have hG : G τ = G ρ := rfl
      dsimp only [I]
      rw [hG, hh.1, hh.2]
    have hUniformτ (p : ℕ) (hp : p ∈ τ.childPositions) : I τ p = ranks σ := by
      have hpρ : p ∈ ρ.childPositions := by rw [← hChildτρ]; exact hp
      exact (hI p).trans (hUniformρ p hpρ)
    have hOutsideτ : ∀ j ∈ τ.levelsOn t 0, ∀ z ∈ τ.extPositions j,
        ∀ p ∈ τ.childPositions, ∀ q ∈ τ.childPositions, z < min p q ∨ max p q < z := by
      intro j hj z hz p hp q hq
      have hjρ : j ∈ ρ.levels := (List.mem_filter.mp hj).1
      have hjt : τ.sideAt j = t := by simpa using (List.mem_filter.mp hj).2
      have he := hExt j hjρ
      by_cases hchosen : ρ.sideAt j = ρ.sideAt N
      · rw [if_pos hchosen] at he
        have hz' : z ∈ (ρ.extPositions j).filter (· = x) := by rw [← he]; exact hz
        have hzx : z = x := of_decide_eq_true (List.mem_filter.mp hz').2
        subst z
        have hjx := (List.mem_filter.mp hz).2
        have hNx := (List.mem_filter.mp hxτ).2
        have hjN : j = N := by
          cases hc : τ.letterAt x with
          | child => simp [hc] at hjx
          | ext l v =>
            have hl : l = j := by simpa only [hc, decide_eq_true_eq] using hjx
            have hlN : l = N := by simpa only [hc, decide_eq_true_eq] using hNx
            exact hl.symm.trans hlN
        have hst : s = t := hNsτ.symm.trans (hjN ▸ hjt)
        exact False.elim (hne hst)
      · rw [if_neg hchosen] at he
        have hzρ : z ∈ ρ.extPositions j := by rw [← he]; exact hz
        have hjs : ρ.sideAt j ≠ s := by simpa only [hNsρ] using hchosen
        have hSideRule : ∀ a b c : Side, a ≠ b → b ≠ c → a = c := by
          intro a b c
          cases a <;> cases b <;> cases c <;> simp
        have hOppSide : ρ.sideAt j = t := hSideRule _ _ _ hjs hne
        have hjOn : j ∈ ρ.levelsOn t 0 :=
          List.mem_filter.mpr ⟨hjρ, decide_eq_true ⟨hOppSide, Or.inl rfl⟩⟩
        have hpρ : p ∈ ρ.childPositions := by rw [← hChildτρ]; exact hp
        have hqρ : q ∈ ρ.childPositions := by rw [← hChildτρ]; exact hq
        exact hOutsideρ j hjOn z hzρ p hpρ q hqρ
    have hActive : active τ = active ρ := by
      ext p
      simp only [active, Finset.mem_filter, List.mem_toFinset, hChildτρ]
      constructor
      · intro hp
        exact ⟨hp.1, hAllρ p hp.1⟩
      · intro hp
        have hpτ : p ∈ τ.childPositions := by rw [hChildτρ]; exact hp.1
        exact ⟨hp.1, hAllτ p hpτ⟩
    have hRanksτ : ranks τ = ranks σ := by
      have hh : ranks τ = ranks ρ := by
        dsimp only [ranks]
        rw [hActive]
        apply Finset.biUnion_congr rfl
        intro p hp
        exact hI p
      exact hh.trans hRanksρ
    exact ⟨τ, hAρ, hUρ, hKρ, hMaxρ, hChildτ, hPosτ, hNτ, hNsτ, hxτ,
      hYoungτ, hOnlyτ, hAllτ, hUniformτ, hOutsideτ, hRanksτ,
      fun fuel => (hFuelρ fuel).trans (hFuelτρ fuel), hBoundρ.trans hBoundτρ⟩

  have ctx_pure_extensions_eq_of_position_history (σ τ : Ctx.Context) (s t : Ctx.Side) (top bottom : ℕ)
    (hhistory : ((σ.levelsOn s top).filter (fun j => σ.extPositions j ≠ [])).map σ.extPositions =
      ((τ.levelsOn t bottom).filter (fun j => τ.extPositions j ≠ [])).map τ.extPositions) :
    ∀ p, σ.leftExt s top p = τ.leftExt t bottom p ∧
      σ.rightExt s top p = τ.rightExt t bottom p := by
    classical
    let lstep : ℕ × ℕ → List ℕ → ℕ × ℕ := fun z positions =>
      match (positions.filter (· < z.1)).getLast? with
      | some x => (x, z.2 + 1)
      | none => z
    let rstep : ℕ × ℕ → List ℕ → ℕ × ℕ := fun z positions =>
      match (positions.filter (z.1 < ·)).head? with
      | some x => (x, z.2 + 1)
      | none => z
    have hLiveFold (υ : Context) : ∀ (ls : List ℕ) (z : ℕ × ℕ),
        ((ls.filter (fun j => υ.extPositions j ≠ [])).foldl (leftStep υ) z = ls.foldl (leftStep υ) z) ∧
        ((ls.filter (fun j => υ.extPositions j ≠ [])).foldl (rightStep υ) z = ls.foldl (rightStep υ) z) := by
      intro ls
      induction ls with
      | nil => intro z; exact ⟨rfl, rfl⟩
      | cons j ls ih =>
        intro z
        by_cases hj : υ.extPositions j ≠ []
        · simp only [List.filter_cons, decide_eq_true hj, if_true, List.foldl_cons]
          exact ⟨(ih _).1, (ih _).2⟩
        · have he : υ.extPositions j = [] := by tauto
          simp only [List.filter_cons, decide_eq_false hj, if_false, List.foldl_cons,
            leftStep, rightStep, he, List.filter_nil, List.getLast?_nil, List.head?_nil]
          exact ih z
    have hMapFold (υ : Context) : ∀ (ls : List ℕ) (z : ℕ × ℕ),
        (ls.map υ.extPositions).foldl lstep z = ls.foldl (leftStep υ) z ∧
        (ls.map υ.extPositions).foldl rstep z = ls.foldl (rightStep υ) z := by
      intro ls
      induction ls with
      | nil => intro z; exact ⟨rfl, rfl⟩
      | cons j ls ih =>
        intro z
        simp only [List.map_cons, List.foldl_cons]
        exact ⟨(ih _).1, (ih _).2⟩
    have hFolds (ρ υ : Context) (ls ks : List ℕ)
        (he : ls.map ρ.extPositions = ks.map υ.extPositions) (z : ℕ × ℕ) :
        ls.foldl (leftStep ρ) z = ks.foldl (leftStep υ) z ∧
        ls.foldl (rightStep ρ) z = ks.foldl (rightStep υ) z := by
      constructor
      · rw [← (hMapFold ρ ls z).1, ← (hMapFold υ ks z).1, he]
      · rw [← (hMapFold ρ ls z).2, ← (hMapFold υ ks z).2, he]
    have hCompare (ρ υ : Context) (v w : Side) (a b p : ℕ)
        (he : ((ρ.levelsOn v a).filter (fun j => ρ.extPositions j ≠ [])).map ρ.extPositions =
          ((υ.levelsOn w b).filter (fun j => υ.extPositions j ≠ [])).map υ.extPositions) :
        ρ.leftExt v a p ≤ υ.leftExt w b p ∧
        ρ.rightExt v a p ≤ υ.rightExt w b p := by
      have hWitness (ls : List ℕ) (hls : ls.Sublist (ρ.levelsOn v a)) :
          ∃ ks : List ℕ, ks.Sublist (υ.levelsOn w b) ∧
            (ls.filter (fun j => ρ.extPositions j ≠ [])).map ρ.extPositions = ks.map υ.extPositions := by
        have hs := (hls.filter (fun j => decide (ρ.extPositions j ≠ []))).map ρ.extPositions
        rw [he] at hs
        obtain ⟨ks, hks, hEq⟩ := List.sublist_map_iff.mp hs
        exact ⟨ks, hks.trans List.filter_sublist, hEq⟩
      constructor
      · simp only [leftExt_eq]
        apply getD_max?_le_of_forall
        intro value hv
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
        obtain ⟨ks, hsub, hEq⟩ := hWitness ls (List.mem_sublists.mp hls)
        have hCount : (ls.foldl (leftStep ρ) (p,0)).2 =
            (ks.foldl (leftStep υ) (p,0)).2 :=
          (congrArg Prod.snd (hLiveFold ρ ls (p,0)).1).symm.trans
            (congrArg Prod.snd (hFolds ρ υ _ ks hEq (p,0)).1)
        exact ⟨_, List.mem_map.mpr ⟨ks, List.mem_sublists.mpr hsub, rfl⟩, le_of_eq hCount⟩
      · simp only [rightExt_eq]
        apply getD_max?_le_of_forall
        intro value hv
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
        obtain ⟨ks, hsub, hEq⟩ := hWitness ls (List.mem_sublists.mp hls)
        have hCount : (ls.foldl (rightStep ρ) (p,0)).2 =
            (ks.foldl (rightStep υ) (p,0)).2 :=
          (congrArg Prod.snd (hLiveFold ρ ls (p,0)).2).symm.trans
            (congrArg Prod.snd (hFolds ρ υ _ ks hEq (p,0)).2)
        exact ⟨_, List.mem_map.mpr ⟨ks, List.mem_sublists.mpr hsub, rfl⟩, le_of_eq hCount⟩
    intro p
    have hστ := hCompare σ τ s t top bottom p hhistory
    have hτσ := hCompare τ σ t s bottom top p hhistory.symm
    exact ⟨le_antisymm hστ.1 hτσ.1, le_antisymm hστ.2 hτσ.2⟩

  have ctx_interval_descendant_limits_normalize (σ : Ctx.Context) (b N : ℕ)
    (houtside : ∀ j ∈ σ.levels, ∀ x ∈ σ.extPositions j, x < b ∨ b + N ≤ x)
    (π : Ctx.Context) (D : ℕ)
    (hπ : π.a = σ.a ∧ π.u = σ.u ∧ π.k = σ.k ∧
      π.maxima.length = D + σ.maxima.length ∧
      (∀ l, 1 ≤ l → π.extPositions (l + D) = σ.extPositions l) ∧
      (∀ l, 1 ≤ l → π.sideAt (l + D) = σ.sideAt l) ∧
      (∀ l, 1 ≤ l → π.maximumAt (l + D) = σ.maximumAt l))
    (hnew : ∀ l x, 1 ≤ l → l ≤ D → x ∈ π.extPositions l → x ∈ List.range' b N)
    (p q : ℕ) (hp : p ∈ List.range' b N) (hq : q ∈ List.range' b N) :
    let τ : Ctx.Context := { π with a := σ.capLimit b b + 1, u := σ.cupLimit b b + 1, maxima := π.maxima.take D }
    π.cupLimit p q = τ.cupLimit p q ∧ π.capLimit p q = τ.capLimit p q := by
    classical
    dsimp only
    let τ : Context := { π with a := σ.capLimit b b + 1, u := σ.cupLimit b b + 1, maxima := π.maxima.take D }
    change π.cupLimit p q = τ.cupLimit p q ∧ π.capLimit p q = τ.capLimit p q
    obtain ⟨ha, hu, hk, hlen, hext, hside, hmaximum⟩ := hπ
    let rootLength := N
    let region := List.range' b N
    have hchild : ∀ p, p ∈ region ↔ b ≤ p ∧ p < b + rootLength := by
      intro p
      exact List.mem_range'_1
    have hextOutside : ∀ j ∈ σ.levels, ∀ x ∈ σ.extPositions j,
        x < b ∨ b + rootLength ≤ x := houtside
    have hfilters : ∀ p q, p ∈ region → q ∈ region → ∀ j, j ∈ σ.levels →
        (σ.extPositions j).filter (· < p) = (σ.extPositions j).filter (· < q) ∧
        (σ.extPositions j).filter (p < ·) = (σ.extPositions j).filter (q < ·) := by
      intro p q hp hq j hj
      have hp' := (hchild p).1 hp
      have hq' := (hchild q).1 hq
      constructor <;> apply List.filter_congr <;> intro x hx
      · have := hextOutside j hj x hx
        simp only [decide_eq_decide]
        omega
      · have := hextOutside j hj x hx
        simp only [decide_eq_decide]
        omega
    have hfoldLeft : ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ σ.levels) → ∀ p q c,
        p ∈ region → q ∈ region →
        (ls.foldl (leftStep σ) (p, c)).2 = (ls.foldl (leftStep σ) (q, c)).2 := by
      intro ls
      induction ls with
      | nil => intros; rfl
      | cons j ls ih =>
        intro hls p q c hp hq
        have ht : ∀ i ∈ ls, i ∈ σ.levels := fun i hi => hls i (List.mem_cons_of_mem _ hi)
        simp only [List.foldl_cons, leftStep]
        rw [(hfilters p q hp hq j (hls j (List.mem_cons_self ..))).1]
        split
        · rfl
        · exact ih ht p q c hp hq
    have hfoldRight : ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ σ.levels) → ∀ p q c,
        p ∈ region → q ∈ region →
        (ls.foldl (rightStep σ) (p, c)).2 = (ls.foldl (rightStep σ) (q, c)).2 := by
      intro ls
      induction ls with
      | nil => intros; rfl
      | cons j ls ih =>
        intro hls p q c hp hq
        have ht : ∀ i ∈ ls, i ∈ σ.levels := fun i hi => hls i (List.mem_cons_of_mem _ hi)
        simp only [List.foldl_cons, rightStep]
        rw [(hfilters p q hp hq j (hls j (List.mem_cons_self ..))).2]
        split
        · rfl
        · exact ih ht p q c hp hq
    have hleftEq : ∀ s top p q, p ∈ region → q ∈ region →
        σ.leftExt s top p = σ.leftExt s top q := by
      intro s top p q hp hq
      simp only [leftExt_eq]
      congr 2
      apply List.map_congr_left
      intro ls hls
      exact hfoldLeft ls (fun j hj =>
        (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) p q 0 hp hq
    have hrightEq : ∀ s top p q, p ∈ region → q ∈ region →
        σ.rightExt s top p = σ.rightExt s top q := by
      intro s top p q hp hq
      simp only [rightExt_eq]
      congr 2
      apply List.map_congr_left
      intro ls hls
      exact hfoldRight ls (fun j hj =>
        (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) p q 0 hp hq
    have hmaxWitness : ∀ (L : List ℕ) (f : List ℕ → ℕ),
        ∃ ls ∈ L.sublists, ((L.sublists.map f).max?).getD 0 = f ls := by
      intro L f
      have hmem : f [] ∈ L.sublists.map f := List.mem_map.2 ⟨[], by simp, rfl⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (List.isSome_max?_of_mem hmem)
      obtain ⟨ls, hls, hval⟩ := List.mem_map.1 (List.max?_mem hv)
      exact ⟨ls, hls, by simp [hv, hval]⟩
    have hb : b ∈ region := by
      have hp' := (hchild p).1 hp
      apply (hchild b).2
      omega
    have hτlen : τ.maxima.length = D := by
      simp only [τ, List.length_take, hlen]
      omega
    have hτext : ∀ l, τ.extPositions l = π.extPositions l := fun _ => rfl
    have hτside : ∀ l, τ.sideAt l = π.sideAt l := fun _ => rfl
    have hτleftStep : leftStep τ = leftStep π := rfl
    have hτrightStep : rightStep τ = rightStep π := rfl
    have hτmaximum : ∀ l, 1 ≤ l → l ≤ D → τ.maximumAt l = π.maximumAt l := by
      intro l hl hD
      simp only [maximumAt, τ, List.getElem?_take_of_lt (by omega : l - 1 < D)]
    have hτprefix (s : Side) : τ.levelsOn s 0 =
        ((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s) := by
      simp [levelsOn, levels, hτlen, hτside]
    have hτmem : ∀ s top l, l ∈ τ.levelsOn s top → 1 ≤ l ∧ l ≤ D := by
      intro s top l hl
      obtain ⟨hm, _⟩ := List.mem_filter.mp hl
      change l ∈ (List.range τ.maxima.length).map (· + 1) at hm
      rw [hτlen] at hm
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
      have := List.mem_range.mp hi
      omega
    have hnewFoldLeft : ∀ (ls : List ℕ), (∀ l ∈ ls, 1 ≤ l ∧ l ≤ D) →
        ∀ z c, z ∈ region → (ls.foldl (leftStep π) (z, c)).1 ∈ region := by
      intro ls
      induction ls with
      | nil => intro _ z c hz; exact hz
      | cons l ls ih =>
        intro hls z c hz
        have hl := hls l (by simp)
        have htail : ∀ n ∈ ls, 1 ≤ n ∧ n ≤ D := fun n hn => hls n (by simp [hn])
        simp only [List.foldl_cons, leftStep]
        cases hh : ((π.extPositions l).filter (· < z)).getLast? with
        | none => exact ih htail z c hz
        | some x =>
          have hx := (List.mem_filter.mp (List.mem_of_mem_getLast? (Option.mem_def.mpr hh))).1
          exact ih htail x (c + 1) (hnew l x hl.1 hl.2 hx)
    have hnewFoldRight : ∀ (ls : List ℕ), (∀ l ∈ ls, 1 ≤ l ∧ l ≤ D) →
        ∀ z c, z ∈ region → (ls.foldl (rightStep π) (z, c)).1 ∈ region := by
      intro ls
      induction ls with
      | nil => intro _ z c hz; exact hz
      | cons l ls ih =>
        intro hls z c hz
        have hl := hls l (by simp)
        have htail : ∀ n ∈ ls, 1 ≤ n ∧ n ≤ D := fun n hn => hls n (by simp [hn])
        simp only [List.foldl_cons, rightStep]
        cases hh : ((π.extPositions l).filter (z < ·)).head? with
        | none => exact ih htail z c hz
        | some x =>
          have hx := (List.mem_filter.mp (List.mem_of_mem_head? (Option.mem_def.mpr hh))).1
          exact ih htail x (c + 1) (hnew l x hl.1 hl.2 hx)
    have hlevelPrefix (π : Context) (D : ℕ) (hlen : π.maxima.length = D + σ.maxima.length)
        (hside : ∀ N, 1 ≤ N → π.sideAt (N + D) = σ.sideAt N) (s : Side) (N : ℕ) :
        π.levelsOn s (if N = 0 then 0 else N + D) =
          ((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s) ++
            (σ.levelsOn s N).map (· + D) := by
      have hlevels : π.levels = (List.range D).map (· + 1) ++ σ.levels.map (· + D) := by
        simp only [levels, hlen, List.range_add, List.map_append, List.map_map]
        congr 2
        funext i
        simp only [Function.comp_def]
        omega
      unfold levelsOn
      rw [hlevels, List.filter_append]
      congr 1
      · apply List.filter_congr
        intro l hl
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
        have hi' := List.mem_range.mp hi
        by_cases hN : N = 0
        · simp [hN]
        · simp [hN]
          omega
      · rw [List.filter_map]
        congr 1
        apply List.filter_congr
        intro l hl
        have hl1 := one_le_of_mem_levels hl
        simp only [Function.comp_def, hside l hl1, decide_eq_decide]
        by_cases hN : N = 0 <;> simp [hN]
    have hfoldOldLeft (π : Context) (D : ℕ)
        (hext : ∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N)
        (ls : List ℕ) (hls : ∀ N ∈ ls, 1 ≤ N) (st : ℕ × ℕ) :
        ((ls.map (· + D)).foldl (leftStep π) st) = ls.foldl (leftStep σ) st := by
      induction ls generalizing st with
      | nil => rfl
      | cons N ls ih =>
        simp only [List.map_cons, List.foldl_cons]
        have hstep : leftStep π st (N + D) = leftStep σ st N := by
          rcases st with ⟨p, c⟩
          simp only [leftStep, hext N (hls N (by simp))]
        rw [hstep]
        exact ih (fun N hN => hls N (by simp [hN])) _
    have hfoldOldRight (π : Context) (D : ℕ)
        (hext : ∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N)
        (ls : List ℕ) (hls : ∀ N ∈ ls, 1 ≤ N) (st : ℕ × ℕ) :
        ((ls.map (· + D)).foldl (rightStep π) st) = ls.foldl (rightStep σ) st := by
      induction ls generalizing st with
      | nil => rfl
      | cons N ls ih =>
        simp only [List.map_cons, List.foldl_cons]
        have hstep : rightStep π st (N + D) = rightStep σ st N := by
          rcases st with ⟨p, c⟩
          simp only [rightStep, hext N (hls N (by simp))]
        rw [hstep]
        exact ih (fun N hN => hls N (by simp [hN])) _
    have hsplitLevels (s : Side) (top : ℕ) :
        π.levelsOn s (if top = 0 then 0 else top + D) =
          τ.levelsOn s 0 ++ (σ.levelsOn s top).map (· + D) := by
      rw [hlevelPrefix π D hlen hside, hτprefix]
    have hleftExact (s : Side) (top z : ℕ) (hz : z ∈ region) :
        π.leftExt s (if top = 0 then 0 else top + D) z =
          τ.leftExt s 0 z + σ.leftExt s top b := by
      have hsum (A B : List ℕ) (hA : A.Sublist (τ.levelsOn s 0))
          (hB : B.Sublist (σ.levelsOn s top)) :
          ((A ++ B.map (· + D)).foldl (leftStep π) (z, 0)).2 =
            (A.foldl (leftStep τ) (z, 0)).2 + (B.foldl (leftStep σ) (b, 0)).2 := by
        have hr := hnewFoldLeft A (fun l hl => hτmem s 0 l (hA.subset hl)) z 0 hz
        rw [List.foldl_append, hfoldOldLeft π D hext B
          (fun l hl => (one_le_of_mem_levelsOn (hB.subset hl)).1)]
        let st := A.foldl (leftStep π) (z, 0)
        change (B.foldl (leftStep σ) (st.1, st.2)).2 = st.2 + (B.foldl (leftStep σ) (b, 0)).2
        rw [foldl_leftStep_count, hfoldLeft B (fun j hj => (List.mem_filter.mp (hB.subset hj)).1) st.1 b 0 hr hb]
      apply le_antisymm
      · rw [leftExt_eq]
        apply getD_max?_le
        intro v hv
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
        have hsub := List.mem_sublists.mp hls
        rw [hsplitLevels] at hsub
        obtain ⟨A, B', rfl, hA, hB'⟩ := List.sublist_append_iff.mp hsub
        obtain ⟨B, hB, rfl⟩ := List.sublist_map_iff.mp hB'
        rw [hsum A B hA hB]
        exact Nat.add_le_add
          (le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
            (fun ls => (ls.foldl (leftStep τ) (z, 0)).2))
            (List.mem_map.mpr ⟨A, List.mem_sublists.mpr hA, rfl⟩))
          (le_getD_max?_of_mem (L := (σ.levelsOn s top).sublists.map
            (fun ls => (ls.foldl (leftStep σ) (b, 0)).2))
            (List.mem_map.mpr ⟨B, List.mem_sublists.mpr hB, rfl⟩))
      · obtain ⟨A, hA, hAval⟩ := hmaxWitness (τ.levelsOn s 0)
          (fun ls => (ls.foldl (leftStep τ) (z, 0)).2)
        obtain ⟨B, hB, hBval⟩ := hmaxWitness (σ.levelsOn s top)
          (fun ls => (ls.foldl (leftStep σ) (b, 0)).2)
        have hsub : (A ++ B.map (· + D)).Sublist
            (π.levelsOn s (if top = 0 then 0 else top + D)) := by
          rw [hsplitLevels]
          exact (List.mem_sublists.mp hA).append ((List.mem_sublists.mp hB).map _)
        have hv := le_getD_max?_of_mem (L :=
          (π.levelsOn s (if top = 0 then 0 else top + D)).sublists.map
            (fun ls => (ls.foldl (leftStep π) (z, 0)).2))
            (List.mem_map.mpr ⟨A ++ B.map (· + D), List.mem_sublists.mpr hsub, rfl⟩)
        rw [hsum A B (List.mem_sublists.mp hA) (List.mem_sublists.mp hB)] at hv
        change τ.leftExt s 0 z + σ.leftExt s top b ≤ π.leftExt s (if top = 0 then 0 else top + D) z
        rw [leftExt_eq τ, leftExt_eq σ, hAval, hBval]
        exact hv
    have hrightExact (s : Side) (top z : ℕ) (hz : z ∈ region) :
        π.rightExt s (if top = 0 then 0 else top + D) z =
          τ.rightExt s 0 z + σ.rightExt s top b := by
      have hsum (A B : List ℕ) (hA : A.Sublist (τ.levelsOn s 0))
          (hB : B.Sublist (σ.levelsOn s top)) :
          ((A ++ B.map (· + D)).foldl (rightStep π) (z, 0)).2 =
            (A.foldl (rightStep τ) (z, 0)).2 + (B.foldl (rightStep σ) (b, 0)).2 := by
        have hr := hnewFoldRight A (fun l hl => hτmem s 0 l (hA.subset hl)) z 0 hz
        rw [List.foldl_append, hfoldOldRight π D hext B
          (fun l hl => (one_le_of_mem_levelsOn (hB.subset hl)).1)]
        let st := A.foldl (rightStep π) (z, 0)
        change (B.foldl (rightStep σ) (st.1, st.2)).2 = st.2 + (B.foldl (rightStep σ) (b, 0)).2
        rw [foldl_rightStep_count, hfoldRight B (fun j hj => (List.mem_filter.mp (hB.subset hj)).1) st.1 b 0 hr hb]
      apply le_antisymm
      · rw [rightExt_eq]
        apply getD_max?_le
        intro v hv
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
        have hsub := List.mem_sublists.mp hls
        rw [hsplitLevels] at hsub
        obtain ⟨A, B', rfl, hA, hB'⟩ := List.sublist_append_iff.mp hsub
        obtain ⟨B, hB, rfl⟩ := List.sublist_map_iff.mp hB'
        rw [hsum A B hA hB]
        exact Nat.add_le_add
          (le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
            (fun ls => (ls.foldl (rightStep τ) (z, 0)).2))
            (List.mem_map.mpr ⟨A, List.mem_sublists.mpr hA, rfl⟩))
          (le_getD_max?_of_mem (L := (σ.levelsOn s top).sublists.map
            (fun ls => (ls.foldl (rightStep σ) (b, 0)).2))
            (List.mem_map.mpr ⟨B, List.mem_sublists.mpr hB, rfl⟩))
      · obtain ⟨A, hA, hAval⟩ := hmaxWitness (τ.levelsOn s 0)
          (fun ls => (ls.foldl (rightStep τ) (z, 0)).2)
        obtain ⟨B, hB, hBval⟩ := hmaxWitness (σ.levelsOn s top)
          (fun ls => (ls.foldl (rightStep σ) (b, 0)).2)
        have hsub : (A ++ B.map (· + D)).Sublist
            (π.levelsOn s (if top = 0 then 0 else top + D)) := by
          rw [hsplitLevels]
          exact (List.mem_sublists.mp hA).append ((List.mem_sublists.mp hB).map _)
        have hv := le_getD_max?_of_mem (L :=
          (π.levelsOn s (if top = 0 then 0 else top + D)).sublists.map
            (fun ls => (ls.foldl (rightStep π) (z, 0)).2))
            (List.mem_map.mpr ⟨A ++ B.map (· + D), List.mem_sublists.mpr hsub, rfl⟩)
        rw [hsum A B (List.mem_sublists.mp hA) (List.mem_sublists.mp hB)] at hv
        change τ.rightExt s 0 z + σ.rightExt s top b ≤ π.rightExt s (if top = 0 then 0 else top + D) z
        rw [rightExt_eq τ, rightExt_eq σ, hAval, hBval]
        exact hv
    have hlevels : π.levels = τ.levels ++ σ.levels.map (· + D) := by
      simp only [levels, hlen, hτlen, List.range_add, List.map_append, List.map_map]
      congr 2
      funext i
      simp only [Function.comp_def]
      omega
    have hsmallLevels (s : Side) (l : ℕ) (hl : 1 ≤ l) (hlD : l ≤ D) :
        π.levelsOn s l = τ.levelsOn s l := by
      unfold levelsOn
      rw [hlevels, List.filter_append]
      have hempty : (σ.levels.map (· + D)).filter
          (fun n => π.sideAt n = s ∧ (l = 0 ∨ n < l)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro n hn
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
        have hi1 := one_le_of_mem_levels hi
        simp only [decide_eq_true_eq]
        omega
      rw [hempty, List.append_nil]
      apply List.filter_congr
      intro n _
      rw [hτside]
    have hsmallLeft (s : Side) (l z : ℕ) (hl : 1 ≤ l) (hlD : l ≤ D) :
        π.leftExt s l z = τ.leftExt s l z := by
      rw [leftExt_eq, leftExt_eq, hsmallLevels s l hl hlD]
      rfl
    have hsmallRight (s : Side) (l z : ℕ) (hl : 1 ≤ l) (hlD : l ≤ D) :
        π.rightExt s l z = τ.rightExt s l z := by
      rw [rightExt_eq, rightExt_eq, hsmallLevels s l hl hlD]
      rfl
    have hchainExact (s : Side) :
        π.chainExt s p q = σ.chainExt s b b + τ.chainExt s p q := by
      have hL : π.leftExt s 0 p = τ.leftExt s 0 p + σ.leftExt s 0 b := hleftExact s 0 p hp
      have hR : π.rightExt s 0 q = τ.rightExt s 0 q + σ.rightExt s 0 b := hrightExact s 0 q hq
      unfold chainExt
      rw [hL, hR]
      omega
    have hjoinExact (s : Side) :
        π.joinExt s p q = max (σ.joinExt s b b + τ.chainExt s p q) (τ.joinExt s p q) := by
      have hdom : π.levelsOn s 0 = τ.levelsOn s 0 ++ (σ.levelsOn s 0).map (· + D) := by
        simpa only [if_pos rfl] using hsplitLevels s 0
      have hOldTerm (l : ℕ) (hl : l ∈ σ.levelsOn s 0) :
          σ.leftExt s l b + σ.rightExt s l b + σ.maximumAt l + τ.chainExt s p q ≤ π.joinExt s p q := by
        have hl1 := (one_le_of_mem_levelsOn hl).1
        have hmem : l + D ∈ π.levelsOn s 0 := by
          rw [hdom]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
        have hv := le_joinExt_of_mem_levelsOn hmem p q
        have hL := hleftExact s l p hp
        have hR := hrightExact s l q hq
        simp only [if_neg (by omega : l ≠ 0)] at hL hR
        rw [hL, hR, hmaximum l hl1] at hv
        unfold chainExt
        omega
      have hNewTerm (l : ℕ) (hl : l ∈ τ.levelsOn s 0) :
          τ.leftExt s l p + τ.rightExt s l q + τ.maximumAt l ≤ π.joinExt s p q := by
        have hlD := hτmem s 0 l hl
        have hmem : l ∈ π.levelsOn s 0 := by rw [hdom]; exact List.mem_append_left _ hl
        have hv := le_joinExt_of_mem_levelsOn hmem p q
        rw [hsmallLeft s l p hlD.1 hlD.2, hsmallRight s l q hlD.1 hlD.2,
          ← hτmaximum l hlD.1 hlD.2] at hv
        exact hv
      have hChainLe := π.chainExt_le_joinExt s p q
      have hTLe : τ.chainExt s p q ≤ π.joinExt s p q := by rw [hchainExact] at hChainLe; omega
      have hOldLe : σ.joinExt s b b + τ.chainExt s p q ≤ π.joinExt s p q := by
        let oldVals := (σ.levelsOn s 0).map
          (fun l => σ.leftExt s l b + σ.rightExt s l b + σ.maximumAt l)
        have hMaxOld : (oldVals.max?).getD 0 + τ.chainExt s p q ≤ π.joinExt s p q := by
          cases he : oldVals.max? with
          | none => simpa only [Option.getD_none, Nat.zero_add] using hTLe
          | some v =>
            obtain ⟨l, hl, heq⟩ := List.mem_map.mp (List.max?_mem he)
            have hv := hOldTerm l hl
            simp only [Option.getD_some]
            omega
        change max (σ.chainExt s b b) ((oldVals.max?).getD 0) + τ.chainExt s p q ≤ _
        rw [hchainExact] at hChainLe
        omega
      have hNewLe : τ.joinExt s p q ≤ π.joinExt s p q := by
        change max (τ.chainExt s p q) _ ≤ _
        apply max_le hTLe
        apply getD_max?_le
        intro v hv
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
        exact hNewTerm l hl
      apply le_antisymm
      · change max (π.chainExt s p q) _ ≤ _
        apply max_le
        · have hc := σ.chainExt_le_joinExt s b b
          rw [hchainExact]
          omega
        · apply getD_max?_le
          intro v hv
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
          rw [hdom] at hl
          rcases List.mem_append.mp hl with hl | hl
          · have hlD := hτmem s 0 l hl
            rw [hsmallLeft s l p hlD.1 hlD.2, hsmallRight s l q hlD.1 hlD.2,
              ← hτmaximum l hlD.1 hlD.2]
            exact (le_joinExt_of_mem_levelsOn hl p q).trans (le_max_right _ _)
          · obtain ⟨oldLevel, hOldLevel, rfl⟩ := List.mem_map.mp hl
            have hOld1 := (one_le_of_mem_levelsOn hOldLevel).1
            have hL := hleftExact s oldLevel p hp
            have hR := hrightExact s oldLevel q hq
            simp only [if_neg (by omega : oldLevel ≠ 0)] at hL hR
            rw [hL, hR, hmaximum oldLevel hOld1]
            have hv := le_joinExt_of_mem_levelsOn hOldLevel b b
            have hMax : σ.joinExt s b b + τ.chainExt s p q ≤
                max (σ.joinExt s b b + τ.chainExt s p q) (τ.joinExt s p q) := le_max_left _ _
            have hT : τ.chainExt s p q = τ.leftExt s 0 p + τ.rightExt s 0 q := rfl
            omega
      · exact max_le hOldLe hNewLe
    constructor
    · change min (π.u - 1 - π.chainExt Side.lower p q) (π.k - 1 - π.joinExt Side.lower p q) =
        min (σ.cupLimit b b - τ.chainExt Side.lower p q) (π.k - 1 - τ.joinExt Side.lower p q)
      rw [hu, hk, hchainExact, hjoinExact]
      have hC : σ.cupLimit b b = min (σ.u - 1 - σ.chainExt Side.lower b b)
          (σ.k - 1 - σ.joinExt Side.lower b b) := rfl
      rw [hC]
      omega
    · change min (π.a - 1 - π.chainExt Side.upper p q) (π.k - 1 - π.joinExt Side.upper p q) =
        min (σ.capLimit b b - τ.chainExt Side.upper p q) (π.k - 1 - τ.joinExt Side.upper p q)
      rw [ha, hk, hchainExact, hjoinExact]
      have hP : σ.capLimit b b = min (σ.a - 1 - σ.chainExt Side.upper b b)
          (σ.k - 1 - σ.joinExt Side.upper b b) := rfl
      rw [hP]
      omega

  have ctx_interval_descendant_bound_normalize (σ : Ctx.Context) (b N : ℕ)
    (houtside : ∀ j ∈ σ.levels, ∀ x ∈ σ.extPositions j, x < b ∨ b + N ≤ x)
    (π : Ctx.Context) (D : ℕ)
    (hπ : π.a = σ.a ∧ π.u = σ.u ∧ π.k = σ.k ∧
      π.maxima.length = D + σ.maxima.length ∧
      (∀ l, 1 ≤ l → π.extPositions (l + D) = σ.extPositions l) ∧
      (∀ l, 1 ≤ l → π.sideAt (l + D) = σ.sideAt l) ∧
      (∀ l, 1 ≤ l → π.maximumAt (l + D) = σ.maximumAt l))
    (hnew : ∀ l x, 1 ≤ l → l ≤ D → x ∈ π.extPositions l → x ∈ List.range' b N)
    (hchild : ∀ x ∈ π.childPositions, x ∈ List.range' b N)
    (hpositive : ∀ x l s, π.letterAt x = Ctx.Letter.ext l s → 1 ≤ l) :
    let τ : Ctx.Context := { π with a := σ.capLimit b b + 1, u := σ.cupLimit b b + 1, maxima := π.maxima.take D }
    (∀ fuel : ℕ, Ctx.Context.boundFuel fuel π = Ctx.Context.boundFuel fuel τ) ∧ π.bound = τ.bound := by
    classical
    dsimp only
    let norm (ρ : Context) (E : ℕ) : Context :=
      { ρ with a := σ.capLimit b b + 1, u := σ.cupLimit b b + 1, maxima := ρ.maxima.take E }
    let Hist (ρ : Context) (E : ℕ) : Prop :=
      ρ.a = σ.a ∧ ρ.u = σ.u ∧ ρ.k = σ.k ∧
        ρ.maxima.length = E + σ.maxima.length ∧
        (∀ l, 1 ≤ l → ρ.extPositions (l + E) = σ.extPositions l) ∧
        (∀ l, 1 ≤ l → ρ.sideAt (l + E) = σ.sideAt l) ∧
        (∀ l, 1 ≤ l → ρ.maximumAt (l + E) = σ.maximumAt l)
    change (∀ fuel, boundFuel fuel π = boundFuel fuel (norm π D)) ∧ π.bound = (norm π D).bound
    have hNormPart (ρ : Context) (E : ℕ) (keep : List ℕ) (s : Side) (m : ℕ) :
        norm (ρ.part keep s m) (E + 1) = (norm ρ E).part keep s m := by
      rfl
    have hHistPart (ρ : Context) (E : ℕ) (hH : Hist ρ E)
        (keep : List ℕ) (s : Side) (m : ℕ) : Hist (ρ.part keep s m) (E + 1) := by
      obtain ⟨ha, hu, hk, hlen, hext, hside, hmaximum⟩ := hH
      refine ⟨ha, hu, hk, ?_, ?_, ?_, ?_⟩
      · change (m :: ρ.maxima).length = E + 1 + σ.maxima.length
        simp only [List.length_cons, hlen]
        omega
      · intro l hl
        rw [show l + (E + 1) = (l + E) + 1 by omega,
          part_extPositions_succ ρ keep s m (by omega : 1 ≤ l + E), hext l hl]
      · intro l hl
        rw [show l + (E + 1) = (l + E) + 1 by omega,
          part_sideAt_succ ρ keep s m (by omega : 1 ≤ l + E), hside l hl]
      · intro l hl
        rw [show l + (E + 1) = (l + E) + 1 by omega,
          part_maximumAt_succ ρ keep s m (by omega : 1 ≤ l + E), hmaximum l hl]
    have hChildPart (ρ : Context) (hC : ∀ x ∈ ρ.childPositions, x ∈ List.range' b N)
        (keep : List ℕ) (s : Side) (m : ℕ) :
        ∀ x ∈ (ρ.part keep s m).childPositions, x ∈ List.range' b N := by
      intro x hx
      rw [part_childPositions] at hx
      exact hC x (List.mem_filter.mp hx).1
    have hPositivePart (ρ : Context) (keep : List ℕ) (s : Side) (m : ℕ) :
        ∀ x l t, (ρ.part keep s m).letterAt x = Letter.ext l t → 1 ≤ l := by
      intro x l t hx
      have hxl : x < ρ.word.length := by
        by_contra h
        have hn := letterAt_of_length_le (ρ.part keep s m)
          (show (ρ.part keep s m).word.length ≤ x by rw [part_word_length]; omega)
        rw [hn] at hx
        cases hx
      cases he : ρ.letterAt x with
      | child =>
        rw [part_letterAt_of_child ρ keep s m hxl he] at hx
        split at hx
        · cases hx
        · cases hx
          omega
      | ext oldLevel oldSide =>
        rw [part_letterAt_of_ext ρ keep s m hxl he] at hx
        cases hx
        omega
    have hNewPart (ρ : Context) (E : ℕ)
        (hNew : ∀ l x, 1 ≤ l → l ≤ E → x ∈ ρ.extPositions l → x ∈ List.range' b N)
        (hC : ∀ x ∈ ρ.childPositions, x ∈ List.range' b N)
        (hPos : ∀ x l s, ρ.letterAt x = Letter.ext l s → 1 ≤ l)
        (keep : List ℕ) (s : Side) (m : ℕ) :
        ∀ l x, 1 ≤ l → l ≤ E + 1 → x ∈ (ρ.part keep s m).extPositions l → x ∈ List.range' b N := by
      intro l x hl hlE hx
      by_cases hOne : l = 1
      · subst l
        rw [part_extPositions_one hPos keep s m] at hx
        exact hC x (List.mem_filter.mp hx).1
      · have hOld : 1 ≤ l - 1 := by omega
        rw [show l = (l - 1) + 1 by omega, part_extPositions_succ ρ keep s m hOld] at hx
        exact hNew (l - 1) x hOld (by omega) hx
    have hBase (ρ : Context) (E : ℕ) (hH : Hist ρ E)
        (hNew : ∀ l x, 1 ≤ l → l ≤ E → x ∈ ρ.extPositions l → x ∈ List.range' b N)
        (hC : ∀ x ∈ ρ.childPositions, x ∈ List.range' b N) : ρ.base = (norm ρ E).base := by
      rw [base_eq_baseOf, base_eq_baseOf]
      have hps : (norm ρ E).childPositions = ρ.childPositions := rfl
      rw [hps]
      cases hh : ρ.childPositions.head? with
      | none => rfl
      | some p =>
        have hp := hC p (List.mem_of_mem_head? (Option.mem_def.mpr hh))
        have hLimits := ctx_interval_descendant_limits_normalize σ b N houtside ρ E hH hNew p p hp hp
        change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k =
          baseOf ((norm ρ E).cupLimit p p) ((norm ρ E).capLimit p p) (norm ρ E).k
        rw [hLimits.1, hLimits.2]
    have hFuel : ∀ fuel (ρ : Context) (E : ℕ), Hist ρ E →
        (∀ l x, 1 ≤ l → l ≤ E → x ∈ ρ.extPositions l → x ∈ List.range' b N) →
        (∀ x ∈ ρ.childPositions, x ∈ List.range' b N) →
        (∀ x l s, ρ.letterAt x = Letter.ext l s → 1 ≤ l) →
        boundFuel fuel ρ = boundFuel fuel (norm ρ E) := by
      intro fuel
      induction fuel with
      | zero => intro ρ E _ _ _ _; rfl
      | succ fuel ih =>
        intro ρ E hH hNew hC hPos
        have hParts : ∀ keep s m,
            boundFuel fuel (ρ.part keep s m) = boundFuel fuel ((norm ρ E).part keep s m) := by
          intro keep s m
          have hv := ih (ρ.part keep s m) (E + 1) (hHistPart ρ E hH keep s m)
            (hNewPart ρ E hNew hC hPos keep s m) (hChildPart ρ hC keep s m)
            (hPositivePart ρ keep s m)
          rw [hNormPart] at hv
          exact hv
        simp only [boundFuel]
        have hruns : (norm ρ E).numRuns = ρ.numRuns := rfl
        rw [hruns]
        split_ifs with hr
        · exact hBase ρ E hH hNew hC
        · have hps : (norm ρ E).childPositions = ρ.childPositions := rfl
          have hblocks : (norm ρ E).blocks = ρ.blocks := rfl
          have hk : (norm ρ E).k = ρ.k := rfl
          rw [hps, hblocks, hk]
          apply congrArg (fun xs : List ℕ => (xs.max?).getD 0)
          apply List.flatMap_congr
          intro block _
          apply List.flatMap_congr
          intro d _
          simp only [hParts]
    have hAll : ∀ fuel, boundFuel fuel π = boundFuel fuel (norm π D) :=
      fun fuel => hFuel fuel π D hπ hnew hchild hpositive
    refine ⟨hAll, ?_⟩
    unfold bound
    have hps : (norm π D).childPositions = π.childPositions := rfl
    rw [hps]
    exact hAll _

  have ctx_limits_eq_of_axis_history (σ τ : Ctx.Context)
    (ha : σ.a = τ.a) (hu : σ.u = τ.u) (hk : σ.k = τ.k)
    (hhistory : ∀ s : Ctx.Side,
      (σ.levelsOn s 0).map (fun j => (σ.extPositions j, σ.maximumAt j)) =
      (τ.levelsOn s 0).map (fun j => (τ.extPositions j, τ.maximumAt j))) :
    (∀ s p, σ.leftExt s 0 p = τ.leftExt s 0 p ∧ σ.rightExt s 0 p = τ.rightExt s 0 p) ∧
    (∀ s p q, σ.joinExt s p q = τ.joinExt s p q) ∧
    (∀ p q, σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q) := by
    classical
    let entry (ρ : Context) (j : ℕ) := (ρ.extPositions j, ρ.maximumAt j)
    have hPrefix : ∀ (A B : List ℕ) (f g : ℕ → List ℕ × ℕ),
        A.Pairwise (· < ·) → B.Pairwise (· < ·) → A.map f = B.map g →
        ∀ n ∈ A, ∃ m ∈ B, f n = g m ∧
          (A.filter (· < n)).map f = (B.filter (· < m)).map g := by
      intro A
      induction A with
      | nil => intro B f g hA hB he n hn; cases hn
      | cons a A ih =>
        intro B f g hA hB he n hn
        cases B with
        | nil => simp at he
        | cons b B =>
          have hAs := List.pairwise_cons.mp hA
          have hBs := List.pairwise_cons.mp hB
          have hh := List.cons.inj (show f a :: A.map f = g b :: B.map g from he)
          rcases List.mem_cons.mp hn with hna | hn
          · subst n
            have hAf : A.filter (· < a) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro z hz
              have hz' := hAs.1 z hz
              intro hbad
              have hlt : z < a := of_decide_eq_true hbad
              omega
            have hBf : B.filter (· < b) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro z hz
              have hz' := hBs.1 z hz
              intro hbad
              have hlt : z < b := of_decide_eq_true hbad
              omega
            refine ⟨b, List.mem_cons_self .., hh.1, ?_⟩
            simp [hAf, hBf]
          · obtain ⟨m, hm, hfm, hpre⟩ := ih B f g hAs.2 hBs.2 hh.2 n hn
            have han := hAs.1 n hn
            have hbm := hBs.1 m hm
            refine ⟨m, List.mem_cons_of_mem _ hm, hfm, ?_⟩
            simp only [List.filter_cons, decide_eq_true han, decide_eq_true hbm,
              if_true, List.map_cons, hh.1, hpre]
    have hSorted (ρ : Context) (s : Side) : (ρ.levelsOn s 0).Pairwise (· < ·) := by
      apply List.Pairwise.filter
      unfold levels
      exact List.pairwise_lt_range.map (fun x => x + 1) (fun a b h => Nat.add_lt_add_right h 1)
    have hBelow (ρ : Context) (s : Side) (n : ℕ) (hn : 0 < n) :
        ρ.levelsOn s n = (ρ.levelsOn s 0).filter (· < n) := by
      simp only [levelsOn, List.filter_filter]
      apply List.filter_congr
      intro j hj
      simp [show n ≠ 0 by omega, Bool.and_comm, and_comm]
    have hPure (ρ υ : Context) (s : Side) (a b : ℕ)
        (he : (ρ.levelsOn s a).map (entry ρ) = (υ.levelsOn s b).map (entry υ)) :
        ∀ p, ρ.leftExt s a p = υ.leftExt s b p ∧ ρ.rightExt s a p = υ.rightExt s b p := by
      have hh := congrArg (fun H : List (List ℕ × ℕ) =>
        (H.map Prod.fst).filter (fun positions => positions ≠ [])) he
      have hpositions : ((ρ.levelsOn s a).filter (fun j => ρ.extPositions j ≠ [])).map ρ.extPositions =
          ((υ.levelsOn s b).filter (fun j => υ.extPositions j ≠ [])).map υ.extPositions := by
        simpa only [List.map_map, List.filter_map, Function.comp_def, entry] using hh
      exact ctx_pure_extensions_eq_of_position_history ρ υ s s a b hpositions
    have hJoinLe (ρ υ : Context)
        (he : ∀ s, (ρ.levelsOn s 0).map (entry ρ) = (υ.levelsOn s 0).map (entry υ))
        (s : Side) (p q : ℕ) : ρ.joinExt s p q ≤ υ.joinExt s p q := by
      have hChain : ρ.chainExt s p q = υ.chainExt s p q := by
        simp only [chainExt, (hPure ρ υ s 0 0 (he s) p).1, (hPure ρ υ s 0 0 (he s) q).2]
      unfold joinExt
      apply max_le
      · exact hChain.le.trans (le_max_left _ _)
      · apply getD_max?_le
        intro value hv
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hv
        obtain ⟨m, hm, hentry, hprefix⟩ :=
          hPrefix (ρ.levelsOn s 0) (υ.levelsOn s 0) (entry ρ) (entry υ)
            (hSorted ρ s) (hSorted υ s) (he s) n hn
        have hnpos : 0 < n := by have := one_le_of_mem_levels (List.mem_filter.mp hn).1; omega
        have hmpos : 0 < m := by have := one_le_of_mem_levels (List.mem_filter.mp hm).1; omega
        rw [← hBelow ρ s n hnpos, ← hBelow υ s m hmpos] at hprefix
        have hmax : ρ.maximumAt n = υ.maximumAt m := congrArg Prod.snd hentry
        rw [(hPure ρ υ s n m hprefix p).1, (hPure ρ υ s n m hprefix q).2, hmax]
        exact (le_getD_max?_of_mem (L := (υ.levelsOn s 0).map
          (fun j => υ.leftExt s j p + υ.rightExt s j q + υ.maximumAt j))
          (List.mem_map.mpr ⟨m, hm, rfl⟩)).trans (le_max_right _ _)
    have hJoin : ∀ s p q, σ.joinExt s p q = τ.joinExt s p q := by
      intro s p q
      exact le_antisymm (hJoinLe σ τ hhistory s p q)
        (hJoinLe τ σ (fun s => (hhistory s).symm) s p q)
    have hFull : ∀ s p, σ.leftExt s 0 p = τ.leftExt s 0 p ∧ σ.rightExt s 0 p = τ.rightExt s 0 p :=
      fun s => hPure σ τ s 0 0 (hhistory s)
    refine ⟨hFull, hJoin, ?_⟩
    intro p q
    have hChain (s : Side) : σ.chainExt s p q = τ.chainExt s p q := by
      simp only [chainExt, (hFull s p).1, (hFull s q).2]
    simp [cupLimit, capLimit, ha, hu, hk, hChain, hJoin]

  have ctx_bound_eq_of_axis_history (σ τ : Ctx.Context)
    (ha : σ.a = τ.a) (hu : σ.u = τ.u) (hk : σ.k = τ.k)
    (hword : σ.word.length = τ.word.length)
    (hchild : ∀ p, σ.letterAt p = Ctx.Letter.child ↔ τ.letterAt p = Ctx.Letter.child)
    (hhistory : ∀ s : Ctx.Side,
      (σ.levelsOn s 0).map (fun j => (σ.extPositions j, σ.maximumAt j)) =
      (τ.levelsOn s 0).map (fun j => (τ.extPositions j, τ.maximumAt j)))
    (hσpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (hτpositive : ∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) :
    (∀ fuel, Ctx.Context.boundFuel fuel σ = Ctx.Context.boundFuel fuel τ) ∧ σ.bound = τ.bound := by
    classical
    let entry (ρ : Context) (j : ℕ) := (ρ.extPositions j, ρ.maximumAt j)
    let profile (ρ : Context) (s : Side) := (ρ.levelsOn s 0).map (entry ρ)
    let Sim (ρ υ : Context) : Prop :=
      ρ.a = υ.a ∧ ρ.u = υ.u ∧ ρ.k = υ.k ∧ ρ.word.length = υ.word.length ∧
      (∀ p, ρ.letterAt p = Letter.child ↔ υ.letterAt p = Letter.child) ∧
      (∀ s, profile ρ s = profile υ s) ∧
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
      (∀ p j v, υ.letterAt p = Letter.ext j v → 1 ≤ j)
    have hInitial : Sim σ τ := ⟨ha, hu, hk, hword, hchild, hhistory, hσpositive, hτpositive⟩
    have hK {ρ υ : Context} (h : Sim ρ υ) : υ.k = ρ.k := h.2.2.1.symm
    have hChild {ρ υ : Context} (h : Sim ρ υ) : υ.childPositions = ρ.childPositions := by
      rcases h with ⟨_, _, _, hlen, hletters, _⟩
      simp only [childPositions, hlen, hletters]
    have hRuns {ρ υ : Context} (h : Sim ρ υ) : υ.numRuns = ρ.numRuns := by
      rcases h with ⟨_, _, _, hlen, hletters, _⟩
      simp only [numRuns, hlen, ne_eq, hletters]
    have hBlocks {ρ υ : Context} (h : Sim ρ υ) : υ.blocks = ρ.blocks := by
      simp only [blocks, hChild h]
    have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
        ∀ p j s, (ρ.part keep v m).letterAt p = Letter.ext j s → 1 ≤ j := by
      intro p j s hp
      have hpl : p < ρ.word.length := by
        by_contra h
        have hn := letterAt_of_length_le (ρ.part keep v m)
          (show (ρ.part keep v m).word.length ≤ p by rw [part_word_length]; omega)
        rw [hn] at hp
        cases hp
      cases he : ρ.letterAt p with
      | child =>
        rw [part_letterAt_of_child ρ keep v m hpl he] at hp
        split at hp
        · cases hp
        · cases hp
          omega
      | ext oldLevel oldSide =>
        rw [part_letterAt_of_ext ρ keep v m hpl he] at hp
        cases hp
        omega
    have hPartChildAt {ρ υ : Context} (h : Sim ρ υ) (keep : List ℕ) (v : Side) (m p : ℕ) :
        (ρ.part keep v m).letterAt p = Letter.child ↔
          (υ.part keep v m).letterAt p = Letter.child := by
      rcases h with ⟨_, _, _, hlen, hletters, _⟩
      by_cases hpl : p < ρ.word.length
      · have hpu : p < υ.word.length := by omega
        cases hr : ρ.letterAt p with
        | child =>
          have hs : υ.letterAt p = Letter.child := (hletters p).mp hr
          rw [part_letterAt_of_child ρ keep v m hpl hr, part_letterAt_of_child υ keep v m hpu hs]
        | ext j s =>
          have hs : υ.letterAt p ≠ Letter.child := by
            intro hc
            have he := (hletters p).mpr hc
            rw [hr] at he
            cases he
          cases ht : υ.letterAt p with
          | child => exact False.elim (hs ht)
          | ext i t =>
            rw [part_letterAt_of_ext ρ keep v m hpl hr, part_letterAt_of_ext υ keep v m hpu ht]
            simp
      · have hpρ : (ρ.part keep v m).word.length ≤ p := by rw [part_word_length]; omega
        have hpυ : (υ.part keep v m).word.length ≤ p := by rw [part_word_length]; omega
        rw [letterAt_of_length_le (ρ.part keep v m) hpρ, letterAt_of_length_le (υ.part keep v m) hpυ]
    have hOnPart (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) (s : Side) :
        (ρ.part keep v m).levelsOn s 0 =
          (if (ρ.part keep v m).sideAt 1 = s then [1] else []) ++
            (ρ.levelsOn s 0).map (· + 1) := by
      have hPred : ρ.levels.filter (fun j => (ρ.part keep v m).sideAt (j + 1) = s) =
          ρ.levels.filter (fun j => ρ.sideAt j = s) := by
        apply List.filter_congr
        intro j hj
        rw [part_sideAt_succ ρ keep v m (one_le_of_mem_levels hj)]
      simp only [levelsOn, part_levels, eq_self_iff_true, true_or, and_true, List.filter_cons,
        List.filter_map, Function.comp_def, hPred, decide_eq_true_eq]
      split_ifs <;> rfl
    have hProfilePart (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) (s : Side) :
        profile (ρ.part keep v m) s =
          (if (ρ.part keep v m).sideAt 1 = s then
            [((ρ.part keep v m).extPositions 1, m)] else []) ++ profile ρ s := by
      have hOld : (ρ.levelsOn s 0).map (fun j => entry (ρ.part keep v m) (j + 1)) =
          (ρ.levelsOn s 0).map (entry ρ) := by
        apply List.map_congr_left
        intro j hj
        have hjpos := one_le_of_mem_levels (List.mem_filter.mp hj).1
        simp only [entry, part_extPositions_succ ρ keep v m hjpos,
          part_maximumAt_succ ρ keep v m hjpos]
      dsimp only [profile]
      rw [hOnPart, List.map_append, List.map_map]
      simp only [Function.comp_def, hOld]
      split_ifs <;> simp only [List.map_singleton, List.map_nil, entry, part_maximumAt_one]
    have hPart {ρ υ : Context} (h : Sim ρ υ) (keep : List ℕ) (v : Side) (m : ℕ) :
        Sim (ρ.part keep v m) (υ.part keep v m) := by
      have hsaved := h
      obtain ⟨ha, hu, hk, hlen, hletters, hhist, hρpos, hυpos⟩ := h
      have hExt : (ρ.part keep v m).extPositions 1 = (υ.part keep v m).extPositions 1 := by
        rw [part_extPositions_one hρpos, part_extPositions_one hυpos, hChild hsaved]
      have hSide : (ρ.part keep v m).sideAt 1 = (υ.part keep v m).sideAt 1 := by
        by_cases he : (ρ.part keep v m).extPositions 1 = []
        · have he' : (υ.part keep v m).extPositions 1 = [] := hExt.symm.trans he
          simp only [sideAt, he, he', List.head?_nil]
        · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ he
          have hp' : p ∈ (υ.part keep v m).extPositions 1 := by rw [← hExt]; exact hp
          exact (part_sideAt_one_of_mem hρpos keep v m hp).trans
            (part_sideAt_one_of_mem hυpos keep v m hp').symm
      refine ⟨ha, hu, hk, ?_, fun p => hPartChildAt hsaved keep v m p, ?_,
        hPartPositive ρ keep v m, hPartPositive υ keep v m⟩
      · simpa only [part_word_length] using hlen
      · intro s
        rw [hProfilePart, hProfilePart, hSide, hExt, hhist s]
    have hBase {ρ υ : Context} (h : Sim ρ υ) : ρ.base = υ.base := by
      have hL := ctx_limits_eq_of_axis_history ρ υ h.1 h.2.1 h.2.2.1 h.2.2.2.2.2.1
      simp only [base, hChild h]
      cases hh : ρ.childPositions.head? with
      | none => rfl
      | some p => simp only [(hL.2.2 p p).1, (hL.2.2 p p).2, hK h]
    have hFuel : ∀ fuel (ρ υ : Context), Sim ρ υ → boundFuel fuel ρ = boundFuel fuel υ := by
      intro fuel
      induction fuel with
      | zero => intro ρ υ h; rfl
      | succ fuel ih =>
        intro ρ υ h
        have hParts : ∀ keep v m,
            boundFuel fuel (ρ.part keep v m) = boundFuel fuel (υ.part keep v m) :=
          fun keep v m => ih _ _ (hPart h keep v m)
        simp only [boundFuel, hRuns h]
        split_ifs
        · exact hBase h
        · rw [hBlocks h, hChild h, hK h]
          apply congrArg (fun xs : List ℕ => (xs.max?).getD 0)
          apply List.flatMap_congr
          intro block hb
          apply List.flatMap_congr
          intro d hd
          simp only [hParts]
    refine ⟨fun fuel => hFuel fuel σ τ hInitial, ?_⟩
    simp only [bound, hChild hInitial]
    exact hFuel _ σ τ hInitial

  have ctx_axis_order_reindex_bound_eq (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (order : List ℕ) (horder : order.Perm σ.levels)
    (haxes : ∀ s : Ctx.Side, order.filter (fun j => σ.sideAt j = s) = σ.levelsOn s 0) :
    let reindex := fun j => order.idxOf j + 1
    let τ : Ctx.Context := { σ with
      maxima := order.map σ.maximumAt
      word := (List.range σ.word.length).map (fun p =>
        match σ.letterAt p with
        | Ctx.Letter.child => Ctx.Letter.child
        | Ctx.Letter.ext j v => if j ∈ σ.levels then Ctx.Letter.ext (reindex j) (σ.sideAt j)
            else Ctx.Letter.ext (order.length + 1) v) }
    τ.word.length = σ.word.length ∧ τ.childPositions = σ.childPositions ∧
    τ.maxima.length = σ.maxima.length ∧ order.map reindex = τ.levels ∧
    (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
    (∀ j ∈ σ.levels, reindex j ∈ τ.levels ∧ τ.extPositions (reindex j) = σ.extPositions j ∧
      τ.sideAt (reindex j) = σ.sideAt j ∧ τ.maximumAt (reindex j) = σ.maximumAt j) ∧
    (∀ s : Ctx.Side, (τ.levelsOn s 0).map (fun j => (τ.extPositions j, τ.maximumAt j)) =
      (σ.levelsOn s 0).map (fun j => (σ.extPositions j, σ.maximumAt j))) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ = Ctx.Context.boundFuel fuel τ) ∧ σ.bound = τ.bound := by
    classical
    let reindex := fun j => order.idxOf j + 1
    let τ : Context := { σ with
      maxima := order.map σ.maximumAt
      word := (List.range σ.word.length).map (fun p =>
        match σ.letterAt p with
        | Letter.child => Letter.child
        | Letter.ext j v => if j ∈ σ.levels then Letter.ext (reindex j) (σ.sideAt j)
            else Letter.ext (order.length + 1) v) }
    change τ.word.length = σ.word.length ∧ τ.childPositions = σ.childPositions ∧
      τ.maxima.length = σ.maxima.length ∧ order.map reindex = τ.levels ∧
      (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
      (∀ j ∈ σ.levels, reindex j ∈ τ.levels ∧ τ.extPositions (reindex j) = σ.extPositions j ∧
        τ.sideAt (reindex j) = σ.sideAt j ∧ τ.maximumAt (reindex j) = σ.maximumAt j) ∧
      (∀ s : Side, (τ.levelsOn s 0).map (fun j => (τ.extPositions j, τ.maximumAt j)) =
        (σ.levelsOn s 0).map (fun j => (σ.extPositions j, σ.maximumAt j))) ∧
      (∀ fuel, boundFuel fuel σ = boundFuel fuel τ) ∧ σ.bound = τ.bound
    have hMem (j : ℕ) : j ∈ order ↔ j ∈ σ.levels := horder.mem_iff
    have hOrderLength : order.length = σ.maxima.length := by
      simpa only [levels, List.length_map, List.length_range] using horder.length_eq
    have hOrderNodup : order.Nodup := by
      apply horder.symm.nodup
      unfold levels
      exact (List.nodup_range (n := σ.maxima.length)).map (fun x y h => Nat.add_right_cancel h)
    have hIdxRange : ∀ L : List ℕ, L.Nodup → L.map (fun j => L.idxOf j) = List.range L.length := by
      intro L
      induction L with
      | nil => intro h; rfl
      | cons a L ih =>
        intro h
        have hn := List.nodup_cons.mp h
        have hTail : L.map (fun j => (a :: L).idxOf j) = (L.map (fun j => L.idxOf j)).map (· + 1) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro j hj
          have haj : a ≠ j := by intro he; subst j; exact hn.1 hj
          simp [List.idxOf_cons, haj, Function.comp_def]
        simp only [List.map_cons, List.idxOf_cons_self, List.length_cons,
          List.range_succ_eq_map, hTail, ih hn.2]
    have hReindexBound (j : ℕ) (hj : j ∈ σ.levels) : reindex j ≤ order.length := by
      have hh := List.idxOf_lt_length_iff.mpr ((hMem j).mpr hj)
      dsimp only [reindex]
      omega
    have hReindexInj (i j : ℕ) (hi : i ∈ σ.levels) : reindex i = reindex j ↔ i = j := by
      dsimp only [reindex]
      rw [Nat.add_right_cancel_iff, List.idxOf_inj ((hMem i).mpr hi)]
    have hLen : τ.word.length = σ.word.length := by simp [τ]
    have hDepth : τ.maxima.length = σ.maxima.length := by simp only [τ, List.length_map, hOrderLength]
    have hReindexLevels : order.map reindex = τ.levels := by
      calc
        order.map reindex = (order.map (fun j => order.idxOf j)).map (· + 1) := by
          rw [List.map_map]
          rfl
        _ = (List.range order.length).map (· + 1) := by rw [hIdxRange order hOrderNodup]
        _ = τ.levels := by simp only [levels, τ, List.length_map]
    have hIndexed (j : ℕ) (hj : j ∈ σ.levels) : reindex j ∈ τ.levels := by
      rw [← hReindexLevels]
      exact List.mem_map.mpr ⟨j, (hMem j).mpr hj, rfl⟩
    have hLetter (p : ℕ) (hp : p < σ.word.length) :
        τ.letterAt p = (match σ.letterAt p with
          | Letter.child => Letter.child
          | Letter.ext j v => if j ∈ σ.levels then Letter.ext (reindex j) (σ.sideAt j)
              else Letter.ext (order.length + 1) v) := by
      simp only [τ, letterAt, List.getElem?_map, List.getElem?_range hp,
        Option.map_some, Option.getD_some]
    have hIsChild (p : ℕ) : τ.letterAt p = Letter.child ↔ σ.letterAt p = Letter.child := by
      by_cases hp : p < σ.word.length
      · rw [hLetter p hp]
        cases he : σ.letterAt p with
        | child => simp [he]
        | ext j v => by_cases hj : j ∈ σ.levels <;> simp [he, hj]
      · rw [letterAt_of_length_le σ (by omega), letterAt_of_length_le τ (by rw [hLen]; omega)]
    have hChild : τ.childPositions = σ.childPositions := by
      simp only [childPositions, hLen, hIsChild]
    have hPos : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
      intro p j v hp
      have hpl : p < σ.word.length := by
        by_contra h
        rw [letterAt_of_length_le τ (by rw [hLen]; omega)] at hp
        cases hp
      rw [hLetter p hpl] at hp
      cases he : σ.letterAt p with
      | child => simp only [he] at hp; cases hp
      | ext i z =>
        simp only [he] at hp
        split_ifs at hp
        · have hij := (Letter.ext.inj hp).1
          dsimp only [reindex] at hij
          omega
        · have hij := (Letter.ext.inj hp).1
          omega
    have hExt (j : ℕ) (hj : j ∈ σ.levels) : τ.extPositions (reindex j) = σ.extPositions j := by
      have hFresh : order.length + 1 ≠ reindex j := by have := hReindexBound j hj; omega
      simp only [extPositions, hLen]
      apply List.filter_congr
      intro p hp
      rw [hLetter p (List.mem_range.mp hp)]
      cases he : σ.letterAt p with
      | child => rfl
      | ext i v =>
        by_cases hi : i ∈ σ.levels
        · simp only [if_pos hi, hReindexInj i j hi]
        · have hij : i ≠ j := by intro h; subst i; exact hi hj
          simp [hi, hFresh, hij]
    have hIndexedLetter (j : ℕ) (hj : j ∈ σ.levels) (p : ℕ) (hp : p ∈ σ.extPositions j) :
        τ.letterAt p = Letter.ext (reindex j) (σ.sideAt j) := by
      have hpl := List.mem_range.mp (List.mem_filter.mp hp).1
      rw [hLetter p hpl]
      cases he : σ.letterAt p with
      | child => simp [extPositions, he] at hp
      | ext i v =>
        have hi : i = j := by
          have hh := (List.mem_filter.mp hp).2
          simpa only [he, decide_eq_true_eq] using hh
        subst i
        simp only [if_pos hj]
    have hSide (j : ℕ) (hj : j ∈ σ.levels) : τ.sideAt (reindex j) = σ.sideAt j := by
      by_cases he : σ.extPositions j = []
      · have heτ : τ.extPositions (reindex j) = [] := (hExt j hj).trans he
        simp only [sideAt, heτ, he, List.head?_nil]
      · let p := (σ.extPositions j).head he
        have hp : p ∈ σ.extPositions j := List.head_mem he
        have hh : (τ.extPositions (reindex j)).head? = some p := by
          rw [hExt j hj]
          exact List.head?_eq_some_head he
        simp only [sideAt, hh]
        change (match τ.letterAt p with | Letter.ext _ v => v | _ => Side.lower) = σ.sideAt j
        rw [hIndexedLetter j hj p hp]
    have hMax (j : ℕ) (hj : j ∈ σ.levels) : τ.maximumAt (reindex j) = σ.maximumAt j := by
      simp only [maximumAt, τ, reindex, Nat.add_sub_cancel, List.getElem?_map,
        List.getElem?_idxOf ((hMem j).mpr hj), Option.map_some, Option.getD_some]
    have hOn (s : Side) : τ.levelsOn s 0 = (σ.levelsOn s 0).map reindex := by
      change τ.levels.filter (fun j => τ.sideAt j = s ∧ (0 = 0 ∨ j < 0)) = _
      simp only [eq_self_iff_true, true_or, and_true]
      rw [← hReindexLevels, List.filter_map]
      have he : order.filter (fun j => τ.sideAt (reindex j) = s) =
          order.filter (fun j => σ.sideAt j = s) := by
        apply List.filter_congr
        intro j hj
        rw [hSide j ((hMem j).mp hj)]
      simpa only [Function.comp_def, he, haxes s]
    have hHistory : ∀ s : Side,
        (τ.levelsOn s 0).map (fun j => (τ.extPositions j, τ.maximumAt j)) =
        (σ.levelsOn s 0).map (fun j => (σ.extPositions j, σ.maximumAt j)) := by
      intro s
      rw [hOn, List.map_map]
      apply List.map_congr_left
      intro j hj
      have hjσ := (List.mem_filter.mp hj).1
      exact Prod.ext (hExt j hjσ) (hMax j hjσ)
    have hBound := ctx_bound_eq_of_axis_history σ τ rfl rfl rfl hLen.symm
      (fun p => (hIsChild p).symm) (fun s => (hHistory s).symm) hpositive hPos
    exact ⟨hLen, hChild, hDepth, hReindexLevels, hPos, fun j hj =>
      ⟨hIndexed j hj, hExt j hj, hSide j hj, hMax j hj⟩, hHistory, hBound.1, hBound.2⟩

  have ctx_chosen_axis_prefix_reindex_bound_eq (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s : Ctx.Side) :
    let chosen := σ.levels.filter (fun j => σ.sideAt j = s)
    let other := σ.levels.filter (fun j => σ.sideAt j ≠ s)
    let order := chosen ++ other
    let D := chosen.length
    let reindex := fun j => order.idxOf j + 1
    let τ : Ctx.Context := { σ with
      maxima := order.map σ.maximumAt
      word := (List.range σ.word.length).map (fun p =>
        match σ.letterAt p with
        | Ctx.Letter.child => Ctx.Letter.child
        | Ctx.Letter.ext j v => if j ∈ σ.levels then Ctx.Letter.ext (reindex j) (σ.sideAt j)
            else Ctx.Letter.ext (order.length + 1) v) }
    τ.word.length = σ.word.length ∧ τ.childPositions = σ.childPositions ∧
    τ.maxima.length = σ.maxima.length ∧ order.map reindex = τ.levels ∧
    (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
    (∀ j ∈ σ.levels, reindex j ∈ τ.levels ∧ τ.extPositions (reindex j) = σ.extPositions j ∧
      τ.sideAt (reindex j) = σ.sideAt j ∧ τ.maximumAt (reindex j) = σ.maximumAt j) ∧
    (∀ s : Ctx.Side, (τ.levelsOn s 0).map (fun j => (τ.extPositions j, τ.maximumAt j)) =
      (σ.levelsOn s 0).map (fun j => (σ.extPositions j, σ.maximumAt j))) ∧
    (∀ j ∈ τ.levels, τ.sideAt j = s ↔ j ≤ D) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ = Ctx.Context.boundFuel fuel τ) ∧ σ.bound = τ.bound := by
    classical
    let chosen := σ.levels.filter (fun j => σ.sideAt j = s)
    let other := σ.levels.filter (fun j => σ.sideAt j ≠ s)
    let order := chosen ++ other
    let D := chosen.length
    let reindex := fun j => order.idxOf j + 1
    let τ : Context := { σ with
      maxima := order.map σ.maximumAt
      word := (List.range σ.word.length).map (fun p =>
        match σ.letterAt p with
        | Letter.child => Letter.child
        | Letter.ext j v => if j ∈ σ.levels then Letter.ext (reindex j) (σ.sideAt j)
            else Letter.ext (order.length + 1) v) }
    change τ.word.length = σ.word.length ∧ τ.childPositions = σ.childPositions ∧
      τ.maxima.length = σ.maxima.length ∧ order.map reindex = τ.levels ∧
      (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
      (∀ j ∈ σ.levels, reindex j ∈ τ.levels ∧ τ.extPositions (reindex j) = σ.extPositions j ∧
        τ.sideAt (reindex j) = σ.sideAt j ∧ τ.maximumAt (reindex j) = σ.maximumAt j) ∧
      (∀ s : Side, (τ.levelsOn s 0).map (fun j => (τ.extPositions j, τ.maximumAt j)) =
        (σ.levelsOn s 0).map (fun j => (σ.extPositions j, σ.maximumAt j))) ∧
      (∀ j ∈ τ.levels, τ.sideAt j = s ↔ j ≤ D) ∧
      (∀ fuel, boundFuel fuel σ = boundFuel fuel τ) ∧ σ.bound = τ.bound
    have horder : order.Perm σ.levels := by
      have hh := List.filter_append_perm (fun j => decide (σ.sideAt j = s)) σ.levels
      have hNeg : σ.levels.filter (fun j => !decide (σ.sideAt j = s)) = other := by
        apply List.filter_congr
        intro j hj
        by_cases hs : σ.sideAt j = s <;> simp [hs]
      rw [hNeg] at hh
      exact hh
    have haxes : ∀ v : Side, order.filter (fun j => σ.sideAt j = v) = σ.levelsOn v 0 := by
      intro v
      by_cases hvs : v = s
      · subst v
        simp [order, chosen, other, levelsOn, List.filter_filter]
      · have hFirst : chosen.filter (fun j => σ.sideAt j = v) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro j hj
          have hjs : σ.sideAt j = s := of_decide_eq_true (List.mem_filter.mp hj).2
          intro hbad
          have hjv : σ.sideAt j = v := of_decide_eq_true hbad
          exact hvs (hjv.symm.trans hjs)
        have hSecond : other.filter (fun j => σ.sideAt j = v) =
            σ.levels.filter (fun j => σ.sideAt j = v) := by
          dsimp only [other]
          rw [List.filter_filter]
          apply List.filter_congr
          intro j hj
          by_cases hjv : σ.sideAt j = v
          · have hjs : σ.sideAt j ≠ s := by rw [hjv]; exact hvs
            simp [hjv, hvs]
          · simp [hjv]
        simp only [order, List.filter_append, hFirst, hSecond, List.nil_append]
        simp only [levelsOn, eq_self_iff_true, true_or, and_true]
    obtain ⟨hLen, hChild, hDepth, hLevels, hPos, hFacts, hHistory, hFuel, hBound⟩ :=
      ctx_axis_order_reindex_bound_eq σ hpositive order horder haxes
    have hIndexChosen (j : ℕ) (hj : j ∈ σ.levels) : σ.sideAt j = s ↔ reindex j ≤ D := by
      by_cases hs : σ.sideAt j = s
      · have hmem : j ∈ chosen := List.mem_filter.mpr ⟨hj, decide_eq_true hs⟩
        have hIdx : order.idxOf j = chosen.idxOf j := List.idxOf_append_of_mem hmem
        have hBound := List.idxOf_lt_length_iff.mpr hmem
        have hle : reindex j ≤ D := by dsimp only [reindex, D]; rw [hIdx]; omega
        exact ⟨fun _ => hle, fun _ => hs⟩
      · have hnot : j ∉ chosen := by
          intro hmem
          exact hs (of_decide_eq_true (List.mem_filter.mp hmem).2)
        have hIdx : order.idxOf j = chosen.length + other.idxOf j := List.idxOf_append_of_notMem hnot
        have hgt : D < reindex j := by dsimp only [reindex, D]; rw [hIdx]; omega
        exact ⟨fun h => False.elim (hs h), fun h => False.elim (by omega)⟩
    have hPrefix : ∀ j ∈ τ.levels, τ.sideAt j = s ↔ j ≤ D := by
      intro j hj
      rw [← hLevels] at hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      have hiσ : i ∈ σ.levels := horder.mem_iff.mp hi
      rw [(hFacts i hiσ).2.2.1]
      exact hIndexChosen i hiσ
    exact ⟨hLen, hChild, hDepth, hLevels, hPos, hFacts, hHistory, hPrefix, hFuel, hBound⟩

  have ctx_interval_tail_bound_normalize (σ : Ctx.Context) (D b N : ℕ) (hD : D ≤ σ.maxima.length)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (hprefix : ∀ j x, 1 ≤ j → j ≤ D → x ∈ σ.extPositions j → x ∈ List.range' b N)
    (htail : ∀ j ∈ σ.levels, D < j → ∀ x ∈ σ.extPositions j, x < b ∨ b + N ≤ x)
    (hchild : ∀ x ∈ σ.childPositions, x ∈ List.range' b N) :
    let old : Ctx.Context := { σ with
      maxima := σ.maxima.drop D
      word := (List.range σ.word.length).map (fun p =>
        match σ.letterAt p with
        | Ctx.Letter.child => Ctx.Letter.child
        | Ctx.Letter.ext j v => if j ≤ D then Ctx.Letter.child else Ctx.Letter.ext (j - D) v) }
    let τ : Ctx.Context := { σ with
      a := old.capLimit b b + 1
      u := old.cupLimit b b + 1
      maxima := σ.maxima.take D }
    (∀ p q, p ∈ List.range' b N → q ∈ List.range' b N →
      σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ = Ctx.Context.boundFuel fuel τ) ∧ σ.bound = τ.bound := by
    classical
    let old : Context := { σ with
      maxima := σ.maxima.drop D
      word := (List.range σ.word.length).map (fun p =>
        match σ.letterAt p with
        | Letter.child => Letter.child
        | Letter.ext j v => if j ≤ D then Letter.child else Letter.ext (j - D) v) }
    let τ : Context := { σ with
      a := old.capLimit b b + 1
      u := old.cupLimit b b + 1
      maxima := σ.maxima.take D }
    change (∀ p q, p ∈ List.range' b N → q ∈ List.range' b N →
        σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q) ∧
      (∀ fuel, boundFuel fuel σ = boundFuel fuel τ) ∧ σ.bound = τ.bound
    have hOldLen : old.word.length = σ.word.length := by simp [old]
    have hOldDepth : old.maxima.length = σ.maxima.length - D := by simp only [old, List.length_drop]
    have hLetter (p : ℕ) (hp : p < σ.word.length) :
        old.letterAt p = (match σ.letterAt p with
          | Letter.child => Letter.child
          | Letter.ext j v => if j ≤ D then Letter.child else Letter.ext (j - D) v) := by
      simp only [old, letterAt, List.getElem?_map, List.getElem?_range hp,
        Option.map_some, Option.getD_some]
    have hExt (j : ℕ) (hj : 1 ≤ j) : old.extPositions j = σ.extPositions (j + D) := by
      simp only [extPositions, hOldLen]
      apply List.filter_congr
      intro p hp
      rw [hLetter p (List.mem_range.mp hp)]
      cases he : σ.letterAt p with
      | child => rfl
      | ext i v =>
        by_cases hi : i ≤ D
        · have hij : i ≠ j + D := by omega
          simp [hi, hij]
        · have heq : i - D = j ↔ i = j + D := by omega
          simp only [if_neg hi, heq]
    have hSide (j : ℕ) (hj : 1 ≤ j) : old.sideAt j = σ.sideAt (j + D) := by
      simp only [sideAt, hExt j hj]
      cases hh : (σ.extPositions (j + D)).head? with
      | none => rfl
      | some p =>
        have hp := List.mem_of_mem_head? hh
        have hpl := List.mem_range.mp (List.mem_filter.mp hp).1
        dsimp only
        rw [hLetter p hpl]
        cases he : σ.letterAt p with
        | child => simp [extPositions, he] at hp
        | ext i v =>
          have hi : i = j + D := by
            have hz := (List.mem_filter.mp hp).2
            simpa only [he, decide_eq_true_eq] using hz
          subst i
          simp only [if_neg (show ¬ j + D ≤ D by omega)]
    have hMax (j : ℕ) (hj : 1 ≤ j) : σ.maximumAt (j + D) = old.maximumAt j := by
      simp only [maximumAt, old, List.getElem?_drop]
      rw [show j + D - 1 = D + (j - 1) by omega]
    have hHistory : σ.a = old.a ∧ σ.u = old.u ∧ σ.k = old.k ∧
        σ.maxima.length = D + old.maxima.length ∧
        (∀ j, 1 ≤ j → σ.extPositions (j + D) = old.extPositions j) ∧
        (∀ j, 1 ≤ j → σ.sideAt (j + D) = old.sideAt j) ∧
        (∀ j, 1 ≤ j → σ.maximumAt (j + D) = old.maximumAt j) := by
      exact ⟨rfl, rfl, rfl, by rw [hOldDepth]; omega,
        fun j hj => (hExt j hj).symm, fun j hj => (hSide j hj).symm, hMax⟩
    have hOutside : ∀ j ∈ old.levels, ∀ x ∈ old.extPositions j, x < b ∨ b + N ≤ x := by
      intro j hj x hx
      have hjpos := one_le_of_mem_levels hj
      have hjle : j ≤ old.maxima.length := by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        have hi' := List.mem_range.mp hi
        omega
      have hjσ : j + D ∈ σ.levels := by
        apply List.mem_map.mpr
        refine ⟨j + D - 1, List.mem_range.mpr ?_, ?_⟩ <;> rw [hOldDepth] at hjle <;> omega
      rw [hExt j hjpos] at hx
      exact htail (j + D) hjσ (by omega) x hx
    have hBound := ctx_interval_descendant_bound_normalize old b N hOutside σ D
      hHistory hprefix hchild hpositive
    refine ⟨?_, hBound.1, hBound.2⟩
    intro p q hp hq
    exact ctx_interval_descendant_limits_normalize old b N hOutside σ D hHistory hprefix p q hp hq

  have ctx_separated_axis_interval_bound_normalize (σ : Ctx.Context) (s : Ctx.Side) (b N : ℕ)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (hinside : ∀ j ∈ σ.levels, σ.sideAt j = s → ∀ x ∈ σ.extPositions j, x ∈ List.range' b N)
    (houtside : ∀ j ∈ σ.levels, σ.sideAt j ≠ s → ∀ x ∈ σ.extPositions j, x < b ∨ b + N ≤ x)
    (hchild : ∀ x ∈ σ.childPositions, x ∈ List.range' b N) :
    let chosen := σ.levels.filter (fun j => σ.sideAt j = s)
    let other := σ.levels.filter (fun j => σ.sideAt j ≠ s)
    let order := chosen ++ other
    let D := chosen.length
    let reindex := fun j => order.idxOf j + 1
    let ρ : Ctx.Context := { σ with
      maxima := order.map σ.maximumAt
      word := (List.range σ.word.length).map (fun p =>
        match σ.letterAt p with
        | Ctx.Letter.child => Ctx.Letter.child
        | Ctx.Letter.ext j v => if j ∈ σ.levels then Ctx.Letter.ext (reindex j) (σ.sideAt j)
            else Ctx.Letter.ext (order.length + 1) v) }
    let old : Ctx.Context := { ρ with
      maxima := ρ.maxima.drop D
      word := (List.range ρ.word.length).map (fun p =>
        match ρ.letterAt p with
        | Ctx.Letter.child => Ctx.Letter.child
        | Ctx.Letter.ext j v => if j ≤ D then Ctx.Letter.child else Ctx.Letter.ext (j - D) v) }
    let τ : Ctx.Context := { ρ with
      a := old.capLimit b b + 1
      u := old.cupLimit b b + 1
      maxima := ρ.maxima.take D }
    τ.word.length = σ.word.length ∧ τ.childPositions = σ.childPositions ∧
    τ.maxima = chosen.map σ.maximumAt ∧
    (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
    (∀ j ∈ τ.levels, τ.sideAt j = s) ∧
    (∀ j ∈ σ.levels, σ.sideAt j = s → reindex j ∈ τ.levels ∧
      τ.extPositions (reindex j) = σ.extPositions j ∧ τ.maximumAt (reindex j) = σ.maximumAt j) ∧
    (∀ j ∈ τ.levels, ∀ p ∈ τ.extPositions j,
      ∃ i ∈ σ.levels, σ.sideAt i = s ∧ p ∈ σ.extPositions i) ∧
    τ.a ≤ max 1 σ.a ∧ τ.u ≤ max 1 σ.u ∧
    τ.a ≤ max 1 σ.k ∧ τ.u ≤ max 1 σ.k ∧
    (∀ p q, p ∈ List.range' b N → q ∈ List.range' b N →
      σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q) ∧
    (∀ t : Ctx.Side, s ≠ t → ∀ p ∈ List.range' b N,
      (match (generalizing := false) t with | Ctx.Side.lower => τ.u | Ctx.Side.upper => τ.a) - 1 =
        (match (generalizing := false) t with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p)) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ = Ctx.Context.boundFuel fuel τ) ∧ σ.bound = τ.bound := by
    classical
    let chosen := σ.levels.filter (fun j => σ.sideAt j = s)
    let other := σ.levels.filter (fun j => σ.sideAt j ≠ s)
    let order := chosen ++ other
    let D := chosen.length
    let reindex := fun j => order.idxOf j + 1
    let ρ : Context := { σ with
      maxima := order.map σ.maximumAt
      word := (List.range σ.word.length).map (fun p =>
        match σ.letterAt p with
        | Letter.child => Letter.child
        | Letter.ext j v => if j ∈ σ.levels then Letter.ext (reindex j) (σ.sideAt j)
            else Letter.ext (order.length + 1) v) }
    let old : Context := { ρ with
      maxima := ρ.maxima.drop D
      word := (List.range ρ.word.length).map (fun p =>
        match ρ.letterAt p with
        | Letter.child => Letter.child
        | Letter.ext j v => if j ≤ D then Letter.child else Letter.ext (j - D) v) }
    let τ : Context := { ρ with
      a := old.capLimit b b + 1
      u := old.cupLimit b b + 1
      maxima := ρ.maxima.take D }
    change τ.word.length = σ.word.length ∧ τ.childPositions = σ.childPositions ∧
      τ.maxima = chosen.map σ.maximumAt ∧
      (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
      (∀ j ∈ τ.levels, τ.sideAt j = s) ∧
      (∀ j ∈ σ.levels, σ.sideAt j = s → reindex j ∈ τ.levels ∧
        τ.extPositions (reindex j) = σ.extPositions j ∧ τ.maximumAt (reindex j) = σ.maximumAt j) ∧
      (∀ j ∈ τ.levels, ∀ p ∈ τ.extPositions j,
        ∃ i ∈ σ.levels, σ.sideAt i = s ∧ p ∈ σ.extPositions i) ∧
      τ.a ≤ max 1 σ.a ∧ τ.u ≤ max 1 σ.u ∧
      τ.a ≤ max 1 σ.k ∧ τ.u ≤ max 1 σ.k ∧
      (∀ p q, p ∈ List.range' b N → q ∈ List.range' b N →
        σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q) ∧
      (∀ t : Side, s ≠ t → ∀ p ∈ List.range' b N,
        (match t with | Side.lower => τ.u | Side.upper => τ.a) - 1 =
          (match t with | Side.lower => σ.cupLimit p p | Side.upper => σ.capLimit p p)) ∧
      (∀ fuel, boundFuel fuel σ = boundFuel fuel τ) ∧ σ.bound = τ.bound
    obtain ⟨hLenρ, hChildρ, hDepthρ, hLevelsρ, hPosρ, hFacts, hHistory, hPrefix, hFuelρ, hBoundρ⟩ :=
      ctx_chosen_axis_prefix_reindex_bound_eq σ hpositive s
    have hD : D ≤ ρ.maxima.length := by
      have hh : chosen.length ≤ σ.levels.length := List.length_filter_le _ _
      simp only [levels, List.length_map, List.length_range] at hh
      rw [hDepthρ]
      exact hh
    have hOrderSub (i : ℕ) (hi : i ∈ order) : i ∈ σ.levels := by
      rcases List.mem_append.mp hi with hi | hi <;> exact (List.mem_filter.mp hi).1
    have hAt (j : ℕ) (hj : j ∈ ρ.levels) :
        ∃ i ∈ σ.levels, ρ.extPositions j = σ.extPositions i ∧ ρ.sideAt j = σ.sideAt i := by
      rw [← hLevelsρ] at hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      have hiσ := hOrderSub i hi
      exact ⟨i, hiσ, (hFacts i hiσ).2.1, (hFacts i hiσ).2.2.1⟩
    have hMemρ (j : ℕ) (hpos : 1 ≤ j) (hjD : j ≤ D) : j ∈ ρ.levels := by
      apply List.mem_map.mpr
      exact ⟨j - 1, List.mem_range.mpr (by omega), by omega⟩
    have hInsideρ : ∀ j x, 1 ≤ j → j ≤ D → x ∈ ρ.extPositions j → x ∈ List.range' b N := by
      intro j x hjpos hjD hx
      have hj := hMemρ j hjpos hjD
      obtain ⟨i, hi, he, hs⟩ := hAt j hj
      have his : σ.sideAt i = s := hs.symm.trans ((hPrefix j hj).mpr hjD)
      exact hinside i hi his x (by rw [← he]; exact hx)
    have hOutsideρ : ∀ j ∈ ρ.levels, D < j → ∀ x ∈ ρ.extPositions j, x < b ∨ b + N ≤ x := by
      intro j hj hDj x hx
      obtain ⟨i, hi, he, hs⟩ := hAt j hj
      have his : σ.sideAt i ≠ s := by
        intro his
        have hh := (hPrefix j hj).mp (hs.trans his)
        change j ≤ D at hh
        omega
      exact houtside i hi his x (by rw [← he]; exact hx)
    have hChildInsideρ : ∀ x ∈ ρ.childPositions, x ∈ List.range' b N := by
      intro x hx
      rw [hChildρ] at hx
      exact hchild x hx
    have hn := ctx_interval_tail_bound_normalize ρ D b N hD hPosρ hInsideρ hOutsideρ hChildInsideρ
    have hMaxima : τ.maxima = chosen.map σ.maximumAt := by
      change ((chosen ++ other).map σ.maximumAt).take chosen.length = chosen.map σ.maximumAt
      rw [List.map_append]
      exact List.take_left' (by simp only [List.length_map])
    have hDepthτ : τ.maxima.length = D := by
      change (ρ.maxima.take D).length = D
      simp only [List.length_take, Nat.min_eq_left hD]
    have hAllChosen : ∀ j ∈ τ.levels, τ.sideAt j = s := by
      intro j hj
      have hjpos := one_le_of_mem_levels hj
      have hjD : j ≤ D := by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        have hh := List.mem_range.mp hi
        rw [hDepthτ] at hh
        omega
      exact (hPrefix j (hMemρ j hjpos hjD)).mpr hjD
    have hTargetMem (j : ℕ) (hj : j ∈ τ.levels) : j ∈ ρ.levels := by
      have hjpos := one_le_of_mem_levels hj
      have hjD : j ≤ D := by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        have hh := List.mem_range.mp hi
        rw [hDepthτ] at hh
        omega
      exact hMemρ j hjpos hjD
    have hSurviving : ∀ j ∈ σ.levels, σ.sideAt j = s → reindex j ∈ τ.levels ∧
        τ.extPositions (reindex j) = σ.extPositions j ∧ τ.maximumAt (reindex j) = σ.maximumAt j := by
      intro j hj hs
      have hf := hFacts j hj
      have hsmall : reindex j ≤ D := (hPrefix _ hf.1).mp (hf.2.2.1.trans hs)
      have hpos : 1 ≤ reindex j := by dsimp only [reindex]; omega
      have hjτ : reindex j ∈ τ.levels := by
        apply List.mem_map.mpr
        refine ⟨reindex j - 1, List.mem_range.mpr ?_, ?_⟩
        · rw [hDepthτ]
          omega
        · omega
      have hmax : τ.maximumAt (reindex j) = ρ.maximumAt (reindex j) := by
        simp only [maximumAt, τ, List.getElem?_take_of_lt (by omega : reindex j - 1 < D)]
      exact ⟨hjτ, hf.2.1, hmax.trans hf.2.2.2⟩
    have hBack : ∀ j ∈ τ.levels, ∀ p ∈ τ.extPositions j,
        ∃ i ∈ σ.levels, σ.sideAt i = s ∧ p ∈ σ.extPositions i := by
      intro j hj p hp
      obtain ⟨i, hi, he, hs⟩ := hAt j (hTargetMem j hj)
      exact ⟨i, hi, hs.symm.trans (hAllChosen j hj), by rw [← he]; exact hp⟩
    have hA : τ.a ≤ max 1 σ.a := by
      have hh := Nat.min_le_left (old.a - 1 - old.chainExt Side.upper b b)
        (old.k - 1 - old.joinExt Side.upper b b)
      change old.capLimit b b ≤ old.a - 1 - old.chainExt Side.upper b b at hh
      change old.capLimit b b + 1 ≤ max 1 σ.a
      have hOldA : old.a = σ.a := rfl
      rw [hOldA] at hh
      omega
    have hU : τ.u ≤ max 1 σ.u := by
      have hh := Nat.min_le_left (old.u - 1 - old.chainExt Side.lower b b)
        (old.k - 1 - old.joinExt Side.lower b b)
      change old.cupLimit b b ≤ old.u - 1 - old.chainExt Side.lower b b at hh
      change old.cupLimit b b + 1 ≤ max 1 σ.u
      have hOldU : old.u = σ.u := rfl
      rw [hOldU] at hh
      omega
    have hAK : τ.a ≤ max 1 σ.k := by
      have hh := Nat.min_le_right (old.a - 1 - old.chainExt Side.upper b b)
        (old.k - 1 - old.joinExt Side.upper b b)
      change old.capLimit b b ≤ old.k - 1 - old.joinExt Side.upper b b at hh
      change old.capLimit b b + 1 ≤ max 1 σ.k
      have hOldK : old.k = σ.k := rfl
      rw [hOldK] at hh
      omega
    have hUK : τ.u ≤ max 1 σ.k := by
      have hh := Nat.min_le_right (old.u - 1 - old.chainExt Side.lower b b)
        (old.k - 1 - old.joinExt Side.lower b b)
      change old.cupLimit b b ≤ old.k - 1 - old.joinExt Side.lower b b at hh
      change old.cupLimit b b + 1 ≤ max 1 σ.k
      have hOldK : old.k = σ.k := rfl
      rw [hOldK] at hh
      omega
    have hSourceLimits := ctx_limits_eq_of_axis_history σ ρ rfl rfl rfl
      (fun v => (hHistory v).symm)
    have hLimits : ∀ p q, p ∈ List.range' b N → q ∈ List.range' b N →
        σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q := by
      intro p q hp hq
      exact ⟨(hSourceLimits.2.2 p q).1.trans (hn.1 p q hp hq).1,
        (hSourceLimits.2.2 p q).2.trans (hn.1 p q hp hq).2⟩
    have hClear (t : Side) (hst : s ≠ t) (p q : ℕ) :
        τ.chainExt t p q = 0 ∧ τ.joinExt t p q = 0 := by
      have he : τ.levelsOn t 0 = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro j hj
        have hh := hAllChosen j hj
        intro hbad
        have h : τ.sideAt j = t ∧ (0 = 0 ∨ j < 0) := of_decide_eq_true hbad
        exact hst (hh.symm.trans h.1)
      simp [chainExt, leftExt, rightExt, joinExt, he]
    have hOppositeGlobal : ∀ t : Side, s ≠ t → ∀ p ∈ List.range' b N,
        (match t with | Side.lower => τ.u | Side.upper => τ.a) - 1 =
          (match t with | Side.lower => σ.cupLimit p p | Side.upper => σ.capLimit p p) := by
      intro t hst p hp
      have hL := hLimits p p hp hp
      have hC := hClear t hst p p
      cases t with
      | lower =>
        rw [hL.1]
        simp only [cupLimit, hC.1, hC.2, Nat.sub_zero]
        change τ.u - 1 = min (τ.u - 1) (σ.k - 1)
        omega
      | upper =>
        rw [hL.2]
        simp only [capLimit, hC.1, hC.2, Nat.sub_zero]
        change τ.a - 1 = min (τ.a - 1) (σ.k - 1)
        omega
    exact ⟨hLenρ, hChildρ, hMaxima, hPosρ, hAllChosen, hSurviving, hBack,
      hA, hU, hAK, hUK, hLimits, hOppositeGlobal,
      fun fuel => (hFuelρ fuel).trans (hn.2.1 fuel), hBoundρ.trans hn.2.2⟩

  classical
  let G := fun (ρ : Context) => match t with | Side.lower => ρ.u | Side.upper => ρ.a
  let active := fun (ρ : Context) => ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let I := fun (ρ : Context) (p : ℕ) =>
    Finset.Icc (ρ.leftExt t 0 p + 1) (G ρ - 1 - ρ.rightExt t 0 p)
  let ranks := fun (ρ : Context) => (active ρ).biUnion (I ρ)
  change ((active σ).filter (fun p => p < x)).biUnion (I σ) = ranks σ →
    ((active σ).filter (fun p => x < p)).biUnion (I σ) = ranks σ →
    (ranks σ).Nonempty →
    ∃ (τ : Context) (J : ℕ),
      τ.k = σ.k ∧ τ.childPositions = σ.childPositions ∧
      (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
      (∀ j ∈ τ.levels, τ.maximumAt j = 0) ∧
      (∀ j ∈ τ.levels, τ.sideAt j = s) ∧
      J ∈ τ.levels ∧ x ∈ τ.extPositions J ∧
      (∀ j ∈ τ.levels, ∀ p ∈ τ.extPositions j, p = x) ∧
      (match s with | Side.lower => τ.u | Side.upper => τ.a) ≤ 5 ∧
      G τ - 1 ≤ (ranks σ).card ∧
      (∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p) ∧
      (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ) ∧ σ.bound ≤ τ.bound
  intro hL hR hNonempty
  obtain ⟨ρ, hAρ, hUρ, hKρ, hMaxρ, hChildρ, hPosρ, hNρ, hNsρ, hxρ,
      hYoungρ, hOnlyρ, hAllρ, hUniformρ, hOutsideρ, hRanksρ, hFuelρ, hBoundρ⟩ :=
    ctx_shared_rank_single_marker_upper_normalize σ hpositive hzero s t hne N x
      hN hNs hx hyoung hactive hL hR hNonempty
  have hZeroρ : ∀ j ∈ ρ.levels, ρ.maximumAt j = 0 := by
    intro j hj
    have hjσ : j ∈ σ.levels := by simpa only [levels, hMaxρ] using hj
    simpa only [maximumAt, hMaxρ] using hzero j hjσ
  obtain ⟨_, ⟨pL, hpL, hpLx, _⟩, ⟨pR, hpR, hxpR, _⟩⟩ :=
    ctx_shared_side_rank_unions_full_interval_witnesses σ t x hL hR hNonempty
  have hpLρ : pL ∈ ρ.childPositions := by
    rw [hChildρ]
    exact List.mem_toFinset.mp (Finset.mem_filter.mp hpL).1
  have hpRρ : pR ∈ ρ.childPositions := by
    rw [hChildρ]
    exact List.mem_toFinset.mp (Finset.mem_filter.mp hpR).1
  let children := ρ.childPositions.toFinset
  have hNonemptyChildren : children.Nonempty := ⟨pL, List.mem_toFinset.mpr hpLρ⟩
  let l := children.min' hNonemptyChildren
  let r := children.max' hNonemptyChildren
  let W := r + 1 - l
  have hl : l ∈ ρ.childPositions := List.mem_toFinset.mp (Finset.min'_mem _ _)
  have hr : r ∈ ρ.childPositions := List.mem_toFinset.mp (Finset.max'_mem _ _)
  have hlx : l < x := lt_of_le_of_lt (Finset.min'_le _ pL (List.mem_toFinset.mpr hpLρ)) hpLx
  have hxr : x < r := lt_of_lt_of_le hxpR (Finset.le_max' _ pR (List.mem_toFinset.mpr hpRρ))
  have hBounds (p : ℕ) (hp : p ∈ ρ.childPositions) : l ≤ p ∧ p ≤ r :=
    ⟨Finset.min'_le _ p (List.mem_toFinset.mpr hp),
      Finset.le_max' _ p (List.mem_toFinset.mpr hp)⟩
  have hRange (p : ℕ) : p ∈ List.range' l W ↔ l ≤ p ∧ p ≤ r := by
    rw [List.mem_range']
    constructor
    · rintro ⟨i, hi, he⟩
      simp only [Nat.one_mul] at he
      dsimp only [W] at hi
      omega
    · intro hp
      refine ⟨p - l, ?_, ?_⟩
      · dsimp only [W]
        omega
      · simp only [Nat.one_mul]
        omega
  have hInside : ∀ j ∈ ρ.levels, ρ.sideAt j = s → ∀ p ∈ ρ.extPositions j,
      p ∈ List.range' l W := by
    intro j hj hs p hp
    have hjOn : j ∈ ρ.levelsOn s 0 :=
      List.mem_filter.mpr ⟨hj, decide_eq_true ⟨hs, Or.inl rfl⟩⟩
    have hpx := hOnlyρ j hjOn p hp
    rw [hpx, hRange]
    omega
  have hOutside : ∀ j ∈ ρ.levels, ρ.sideAt j ≠ s → ∀ p ∈ ρ.extPositions j,
      p < l ∨ l + W ≤ p := by
    intro j hj hs p hp
    have hSideRule : ∀ a b c : Side, a ≠ b → b ≠ c → a = c := by
      intro a b c
      cases a <;> cases b <;> cases c <;> simp
    have hjt := hSideRule _ _ _ hs hne
    have hjOn : j ∈ ρ.levelsOn t 0 :=
      List.mem_filter.mpr ⟨hj, decide_eq_true ⟨hjt, Or.inl rfl⟩⟩
    have hh := hOutsideρ j hjOn p hp l hl r hr
    dsimp only [W]
    omega
  have hChildInside : ∀ p ∈ ρ.childPositions, p ∈ List.range' l W := by
    intro p hp
    exact (hRange p).mpr (hBounds p hp)
  let chosen := ρ.levels.filter (fun j => ρ.sideAt j = s)
  let other := ρ.levels.filter (fun j => ρ.sideAt j ≠ s)
  let order := chosen ++ other
  let D := chosen.length
  let reindex := fun j => order.idxOf j + 1
  let η : Context := { ρ with
    maxima := order.map ρ.maximumAt
    word := (List.range ρ.word.length).map (fun p =>
      match ρ.letterAt p with
      | Letter.child => Letter.child
      | Letter.ext j v => if j ∈ ρ.levels then Letter.ext (reindex j) (ρ.sideAt j)
          else Letter.ext (order.length + 1) v) }
  let old : Context := { η with
    maxima := η.maxima.drop D
    word := (List.range η.word.length).map (fun p =>
      match η.letterAt p with
      | Letter.child => Letter.child
      | Letter.ext j v => if j ≤ D then Letter.child else Letter.ext (j - D) v) }
  let τ : Context := { η with
    a := old.capLimit l l + 1
    u := old.cupLimit l l + 1
    maxima := η.maxima.take D }
  obtain ⟨hLenτ, hChildτρ, hMaxτ, hPosτ, hAllChosen, hSurviving, hBack,
      hAτ, hUτ, hAKτ, hUKτ, hLimits, hOpposite, hFuelτρ, hBoundτρ⟩ :=
    ctx_separated_axis_interval_bound_normalize ρ s l W hPosρ hInside hOutside hChildInside
  have hZeroValues : ∀ v ∈ τ.maxima, v = 0 := by
    intro v hv
    rw [hMaxτ] at hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    exact hZeroρ j (List.mem_filter.mp hj).1
  have hZeroτ : ∀ j ∈ τ.levels, τ.maximumAt j = 0 := by
    intro j hj
    cases he : τ.maxima[j - 1]? with
    | none => simp only [maximumAt, he, Option.getD_none]
    | some v =>
      have hv := hZeroValues v (List.mem_of_getElem? he)
      simp only [maximumAt, he, Option.getD_some, hv]
  have hPivot := hSurviving N hNρ hNsρ
  have hxτ : x ∈ τ.extPositions (reindex N) := by rw [hPivot.2.1]; exact hxρ
  have hOnlyτ : ∀ j ∈ τ.levels, ∀ p ∈ τ.extPositions j, p = x := by
    intro j hj p hp
    obtain ⟨i, hi, hs, hpρ⟩ := hBack j hj p hp
    have hiOn : i ∈ ρ.levelsOn s 0 :=
      List.mem_filter.mpr ⟨hi, decide_eq_true ⟨hs, Or.inl rfl⟩⟩
    exact hOnlyρ i hiOn p hpρ
  have hGlobalτ : (match s with | Side.lower => τ.u | Side.upper => τ.a) ≤ 5 := by
    change τ.a ≤ max 1 ρ.a at hAτ
    change τ.u ≤ max 1 ρ.u at hUτ
    rw [hAρ] at hAτ
    rw [hUρ] at hUτ
    cases s <;> simp only at hglobal ⊢ <;> omega
  have hWidth : G τ - 1 ≤ (ranks σ).card := by
    have hG := hOpposite t hne l (hChildInside l hl)
    have hI := hUniformρ l hl
    have hCard : (I ρ l).card = (ranks σ).card := congrArg Finset.card hI
    simp only [I, Nat.card_Icc] at hCard
    have hLimit : (match (generalizing := false) t with | Side.lower => ρ.cupLimit l l | Side.upper => ρ.capLimit l l)
        ≤ (I ρ l).card := by
      cases t <;> simp only [cupLimit, capLimit, chainExt, I, G, Nat.card_Icc] <;> omega
    change G τ - 1 = _ at hG
    rw [hG]
    rw [← congrArg Finset.card hI]
    exact hLimit
  have hAllτ : ∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := by
    intro p hp
    have hpρ : p ∈ ρ.childPositions := by rw [← hChildτρ]; exact hp
    have ha := hAllρ p hpρ
    have hh := hLimits p p (hChildInside p hpρ) (hChildInside p hpρ)
    exact ⟨hh.1 ▸ ha.1, hh.2 ▸ ha.2⟩
  exact ⟨τ, reindex N, hKρ, hChildτρ.trans hChildρ, hPosτ, hZeroτ, hAllChosen,
    hPivot.1, hxτ, hOnlyτ, hGlobalτ, hWidth, hAllτ,
    fun fuel => (hFuelρ fuel).trans (le_of_eq (hFuelτρ fuel)),
    hBoundρ.trans (le_of_eq hBoundτρ)⟩

end ErdosSzekeres
