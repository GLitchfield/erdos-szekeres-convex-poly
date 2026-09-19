import ESBlueprint.B.CtxTwoMarkerMixedCapacityPairOverlapExcessBound

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- In an exact two-marker chosen-global-five context with a capacity-three witness, the canonical high-capacity pruning is bounded, for every fuel and in full, by the cardinality of its exact active opposite-rank pair support. This exports the sharp internal high-group estimate used by the mixed-overlap theorem so later collision classifications can use support cardinalities directly.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_active_boundary_marker_rank_pair_union_bound, ErdosSzekeres.ctx_capacity_three_children_exterior_of_two_levels_global_five, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_high_capacity_pruning_rank_pair_bound_of_high_witness (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y high : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (hhighmem : high ∈ σ.childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit high high | Ctx.Side.upper => σ.capLimit high high)) :
  let capacity : ℕ → ℕ := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p
  let color : ℕ → ℕ := fun p => if capacity p ≤ 2 then 0 else 1
  let support : ℕ → List ℕ := fun c => σ.childPositions.filter (fun p => color p = c)
  let group : ℕ → Ctx.Context := fun c => ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context)
  let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p)
  let interval : ℕ → ℕ → Finset ℕ := fun c p => Finset.Icc ((group c).leftExt t 0 p + 1) (global - 1 - (group c).rightExt t 0 p)
  let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun p => ((interval c p).product (interval c p)).filter (fun z => z.1 ≤ z.2))
  (∀ fuel, Ctx.Context.boundFuel fuel (group 1) ≤ (pairs 1).card) ∧ (group 1).bound ≤ (pairs 1).card := by
  classical
  dsimp only
  let C (p : ℕ) := match s with
    | Ctx.Side.lower => σ.cupLimit p p
    | Ctx.Side.upper => σ.capLimit p p
  let color (p : ℕ) := if C p ≤ 2 then (0 : ℕ) else 1
  let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
  let group (c : ℕ) : Ctx.Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  let G := match t, hne, hchosenGlobal, hhigh with
    | Ctx.Side.lower, _, _, _ => σ.u
    | Ctx.Side.upper, _, _, _ => σ.a
  let active (c : ℕ) := (group c).childPositions.toFinset.filter
    (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p)
  let I (c p : ℕ) := Finset.Icc ((group c).leftExt t 0 p + 1)
    (G - 1 - (group c).rightExt t 0 p)
  let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
  let pairs (c : ℕ) := (active c).biUnion (fun p => Q (I c p))
  change (∀ fuel, Ctx.Context.boundFuel fuel (group 1) ≤ (pairs 1).card) ∧
    (group 1).bound ≤ (pairs 1).card
  have hPos (c : ℕ) : ∀ p j v,
      (group c).letterAt p = Ctx.Letter.ext j v → 1 ≤ j :=
    (ctx_part_pruning_history_transport σ hpositive (support c)
      Ctx.Side.lower 0).1
  have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔
      p ∈ σ.childPositions ∧ color p = c := by
    have hh := (ctx_part_pruning_history_transport σ hpositive (support c)
      Ctx.Side.lower 0).2.1
    change (group c).childPositions = σ.childPositions.filter (· ∈ support c) at hh
    rw [hh]
    simp [support]
  have hHist (c j : ℕ) (hj : j ∈ σ.levels) :
      (group c).extPositions j = σ.extPositions j ∧
        (group c).sideAt j = σ.sideAt j :=
    (ctx_part_pruning_history_transport σ hpositive (support c)
      Ctx.Side.lower 0).2.2.1 j hj
  have hLevels (c : ℕ) (v : Ctx.Side) (top : ℕ) :
      (group c).levelsOn v top = σ.levelsOn v top :=
    (ctx_part_pruning_history_transport σ hpositive (support c)
      Ctx.Side.lower 0).2.2.2.1 v top
  have hAtLevel (j i z : ℕ) (hz : z ∈ σ.extPositions j)
      (hz' : z ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hz).2
    have hi := (List.mem_filter.mp hz').2
    cases he : σ.letterAt z <;> simp [he] at hj hi
    omega
  have hNOn : N ∈ σ.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hNpos : 1 ≤ N := Ctx.Context.one_le_of_mem_levels hN
  have hNgroup : N ∈ (group 1).levels := hN
  have hxgroup : x ∈ (group 1).extPositions N := by
    rw [(hHist 1 N hN).1]
    exact hx
  have hNside : (group 1).sideAt N = s := (hHist 1 N hN).2.trans hNs
  have hChosenGlobalPlain : (match s with
      | Ctx.Side.lower => σ.u
      | Ctx.Side.upper => σ.a) ≤ 5 := by
    cases s <;> exact hchosenGlobal
  have hSmall : min ((match (group 1).sideAt N with
      | Ctx.Side.lower => (group 1).u
      | Ctx.Side.upper => (group 1).a) - 1)
      ((group 1).k - (group 1).maximumAt N) ≤ 4 := by
    apply (Nat.min_le_left _ _).trans
    rw [hNside]
    cases s <;> simp only [group] at hChosenGlobalPlain ⊢ <;> omega
  rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
      σ s N M x y hN hM hNM hNs hMs hx hy hChosenGlobalPlain with horient | horient
  · have hb := ctx_active_boundary_marker_rank_pair_union_bound
        (group 1) (hPos 1) N x hNgroup hxgroup false
        (fun p hp _ => by
          have hpData := (hChild 1 p).mp hp
          have hcap : 3 ≤ C p := by
            have hc := hpData.2
            dsimp only [color] at hc
            by_cases hle : C p ≤ 2
            · simp [hle] at hc
            · omega
          have hout := horient.2 p hpData.1 hcap N hNOn x hx
          simpa using hout)
        (fun j hj z hz => by
          rw [hNside, hLevels 1 s N] at hj
          have hh := List.mem_filter.mp hj
          have hpred := of_decide_eq_true hh.2
          have hjN : j < N := by
            rcases hpred.2 with hzero | hlt
            · omega
            · exact hlt
          have hj0 : j ∈ σ.levelsOn s 0 :=
            List.mem_filter.mpr ⟨hh.1, by simp [hpred.1]⟩
          rw [(hHist 1 j hh.1).1] at hz
          rcases hchosen j hj0 z hz with hzx | hzy
          · have he := hAtLevel j N x (by simpa only [hzx] using hz) hx
            omega
          · simpa only [hzy, if_false] using horient.1)
        t (by rw [hNside]; exact hne) hSmall
    cases t <;> simpa only [pairs, active, Q, I, G] using hb
  · have hb := ctx_active_boundary_marker_rank_pair_union_bound
        (group 1) (hPos 1) N x hNgroup hxgroup true
        (fun p hp _ => by
          have hpData := (hChild 1 p).mp hp
          have hcap : 3 ≤ C p := by
            have hc := hpData.2
            dsimp only [color] at hc
            by_cases hle : C p ≤ 2
            · simp [hle] at hc
            · omega
          have hout := horient.2 p hpData.1 hcap N hNOn x hx
          simpa using hout)
        (fun j hj z hz => by
          rw [hNside, hLevels 1 s N] at hj
          have hh := List.mem_filter.mp hj
          have hpred := of_decide_eq_true hh.2
          have hjN : j < N := by
            rcases hpred.2 with hzero | hlt
            · omega
            · exact hlt
          have hj0 : j ∈ σ.levelsOn s 0 :=
            List.mem_filter.mpr ⟨hh.1, by simp [hpred.1]⟩
          rw [(hHist 1 j hh.1).1] at hz
          rcases hchosen j hj0 z hz with hzx | hzy
          · have he := hAtLevel j N x (by simpa only [hzx] using hz) hx
            omega
          · simpa only [hzy, if_true] using horient.1)
        t (by rw [hNside]; exact hne) hSmall
    cases t <;> simpa only [pairs, active, Q, I, G] using hb

end ErdosSzekeres
