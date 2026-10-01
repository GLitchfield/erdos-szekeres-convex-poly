import ESBlueprint.B.CtxSingletonPartBoundEqThreshold
import ESBlueprint.B.CtxBoundLeSumPointBases

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Full localized singleton-base and complement exchange X for a one-level root when its old chosen global axis is at most two. Two child runs force an actual level-one marker; the indexed-marker zero-capacity argument and part-limit monotonicity make every source singleton cut zero. The original legal side and coupling suffice. Reuses the mathematical proof of R16's closed marker-zero helper without modifying its node; old-chosen-axis-at-least-three residuals remain.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_sum_point_bases, ErdosSzekeres.ctx_singleton_part_bound_eq_threshold, ErdosSzekeres.ctx_part_limits_le
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange
@falsifier ctx_one_level_root_singleton_base_exchange_residuals.py -/
theorem ctx_one_level_root_singleton_base_exchange_chosen_axis_two (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2) (side : Ctx.Side) (hsmall : (match side with | Ctx.Side.lower => u | Ctx.Side.upper => a) ≤ 2) (left right : List Ctx.Letter) (hletters : ∀ x ∈ left ++ right, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) :
  let σ : Ctx.Context := { a := a, u := u, k := k, word := left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right, maxima := [m] }
  let ρ : Ctx.Context := { a := a, u := u, k := k, word := left ++ [Ctx.Letter.child] ++ right, maxima := [m] }
  let opposite : Ctx.Side → Ctx.Side := fun s => match s with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower
  2 ≤ σ.numRuns →
  ∀ p ∈ σ.childPositions, ∀ (s : Ctx.Side) (c : ℕ), 1 ≤ c → c ≤ k - 2 →
    let q := if p ≤ left.length then p else p - 1
    ∃ (t : Ctx.Side) (d : ℕ), 1 ≤ d ∧ d ≤ k - 2 ∧
      decomposableThreshold ((σ.part [p] s c).capLimit p p + 1) ((σ.part [p] s c).cupLimit p p + 1) k +
          (σ.part (σ.childPositions.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)).bound ≤
      decomposableThreshold ((ρ.part [q] t d).capLimit q q + 1) ((ρ.part [q] t d).cupLimit q q + 1) k +
          (ρ.part (ρ.childPositions.filter (fun r => r ≠ q)) (opposite t) (k - 1 - d)).bound := by
  set_option maxHeartbeats 800000 in
    classical
    dsimp only
    intro hruns p hp s c hc hck
    let σ : Context :=
      ⟨a, u, k, left ++ [Letter.child, Letter.child] ++ right, [m]⟩
    change 2 ≤ σ.numRuns at hruns
    change p ∈ σ.childPositions at hp
    let opposite : Side → Side := fun t => match t with
      | .lower => .upper
      | .upper => .lower
    have hMarkerZero (σ : Ctx.Context) (s : Ctx.Side) (N x : ℕ) (hN : N ∈ σ.levels) (hs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 2) : ∀ p ∈ σ.childPositions, baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k = 0 := by
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
      exact hPoint
    have hσletters : ∀ x ∈ σ.word, x = Letter.child ∨ x = Letter.ext 1 side := by
      intro x hx
      by_cases hc : x = Letter.child
      · exact Or.inl hc
      · apply hletters x
        simpa [σ, hc, List.mem_append] using hx
    have hshape : ∀ i l t, σ.letterAt i = Letter.ext l t → l = 1 ∧ t = side := by
      intro i l t hext
      have hi : i < σ.word.length := by
        by_contra hn
        have h := letterAt_of_length_le σ (Nat.le_of_not_gt hn)
        rw [h] at hext
        cases hext
      have hget : σ.word[i] = Letter.ext l t := by
        simpa [letterAt, hi] using hext
      have hmem : Letter.ext l t ∈ σ.word := by
        rw [← hget]
        exact List.getElem_mem _
      rcases hσletters _ hmem with h | h
      · cases h
      · cases h
        exact ⟨rfl, rfl⟩
    have hMarked : ∃ x, x ∈ σ.extPositions 1 := by
      by_contra hno
      have hAllChild : ∀ i, i < σ.word.length → σ.letterAt i = Letter.child := by
        intro i hi
        have hletter : σ.letterAt i = σ.word[i] := by
          simp [letterAt, List.getElem?_eq_getElem hi]
        rcases hσletters _ (List.getElem_mem _) with h | h
        · exact hletter.trans h
        · have hext : σ.letterAt i = Letter.ext 1 side := hletter.trans h
          have himem : i ∈ σ.extPositions 1 := by simp [extPositions, hi, hext]
          exact False.elim (hno ⟨i, himem⟩)
      let starts := (List.range σ.word.length).filter fun i =>
        σ.letterAt i = Letter.child ∧ (i = 0 ∨ σ.letterAt (i - 1) ≠ Letter.child)
      have hSubset : starts.toFinset ⊆ {0} := by
        intro i hi
        obtain ⟨hirange, hpred⟩ := List.mem_filter.mp (List.mem_toFinset.mp hi)
        have hil : i < σ.word.length := List.mem_range.mp hirange
        obtain ⟨_, hstart⟩ := of_decide_eq_true hpred
        have hi0 : i = 0 := by
          rcases hstart with h | h
          · exact h
          · by_contra hn
            exact h (hAllChild (i - 1) (by omega))
        simpa [hi0]
      have hNodup : starts.Nodup := List.nodup_range.filter _
      have hCard : starts.toFinset.card = starts.length :=
        List.toFinset_card_of_nodup hNodup
      have hRunsLe : σ.numRuns ≤ 1 := by
        change starts.length ≤ 1
        simpa only [hCard, Finset.card_singleton] using Finset.card_le_card hSubset
      omega
    obtain ⟨x, hx⟩ := hMarked
    have hN : 1 ∈ σ.levels := by simp [levels, σ]
    have hSide : σ.sideAt 1 = side := by
      cases hh : (σ.extPositions 1).head? with
      | none =>
          have hn := List.head?_eq_none_iff.mp hh
          rw [hn] at hx
          simp at hx
      | some y =>
          have hy := List.mem_of_mem_head? hh
          have hye := (List.mem_filter.mp hy).2
          cases hl : σ.letterAt y with
          | child => simp [hl] at hye
          | ext j v =>
              obtain ⟨rfl, rfl⟩ := hshape y j v hl
              simp [sideAt, hh, hl]
    have hRootPoint : ∀ p ∈ σ.childPositions,
        baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k = 0 :=
      hMarkerZero σ side 1 x hN hSide hx (by
        cases side <;> simpa [σ] using hsmall)
    have hPartZero (keep : List ℕ) (t : Side) (n : ℕ) :
        (σ.part keep t n).bound = 0 := by
      apply Nat.eq_zero_of_le_zero
      have hMap :
          (σ.part keep t n).childPositions.map (fun p =>
            baseOf ((σ.part keep t n).cupLimit p p)
              ((σ.part keep t n).capLimit p p) σ.k) =
          (σ.part keep t n).childPositions.map (fun _ => 0) := by
        apply List.map_congr_left
        intro p hpPart
        have hpRoot : p ∈ σ.childPositions := by
          rw [part_childPositions] at hpPart
          exact (List.mem_filter.mp hpPart).1
        apply Nat.eq_zero_of_le_zero
        have hrel := ctx_part_limits_le σ keep t n p p
        have hmono := baseOf_mono (k := σ.k) hrel.1 hrel.2
        rw [hRootPoint p hpRoot] at hmono
        exact hmono
      simpa only [show (σ.part keep t n).k = σ.k from rfl,
        hMap, List.sum_map_zero] using ctx_bound_le_sum_point_bases (σ.part keep t n)
    refine ⟨s, c, hc, hck, ?_⟩
    rw [← ctx_singleton_part_bound_eq_threshold σ p hp s c,
      hPartZero [p] s c,
      hPartZero (σ.childPositions.filter (fun r => r ≠ p)) (opposite s) (k - 1 - c)]
    exact Nat.zero_le _

end ErdosSzekeres
