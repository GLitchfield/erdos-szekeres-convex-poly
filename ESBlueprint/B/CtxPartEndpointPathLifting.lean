import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxPureExtensionsPositionMonotone

namespace ErdosSzekeres

/-- Any raw context part lifts old pure and join paths by zero, one or two selected outer new-level markers; the new maximum is a join candidate. Positive child chain limits transfer to the parent at the selected endpoints and imply root coupling with the reserved sibling maximum. Explicit new-level side only; no wellformedness, coloring, occupancy or positive maximum hypothesis.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_pure_extensions_position_monotone
@dangling-ok General missing endpoint and coupling bridge for Q4 virtual assigned-slot B constructions and Q3 profile gluing; slot placement, threshold lower leaves and full B induction remain separate, with no finite-instance target or maximum assertion. -/
theorem ctx_part_endpoint_path_lifting (σ : Ctx.Context) (keep : List ℕ) (s : Ctx.Side) (m : ℕ)
(hside : (σ.part keep s m).sideAt 1 = s)
(p q x y : ℕ) (eL eR : Bool)
(hL : if eL then x < p ∧ x ∈ (σ.part keep s m).extPositions 1 else x = p)
(hR : if eR then q < y ∧ y ∈ (σ.part keep s m).extPositions 1 else y = q) :
let g : ℕ := (if eL then 1 else 0) + (if eR then 1 else 0)
g + σ.chainExt s x y ≤ (σ.part keep s m).chainExt s p q ∧
g + σ.joinExt s x y ≤ (σ.part keep s m).joinExt s p q ∧
m ≤ (σ.part keep s m).joinExt s p q ∧
∀ r : ℕ, 0 < r →
  r ≤ (match s with
    | Ctx.Side.lower => (σ.part keep s m).cupLimit p q
    | Ctx.Side.upper => (σ.part keep s m).capLimit p q) →
  r + g ≤ (match s with
    | Ctx.Side.lower => σ.cupLimit x y
    | Ctx.Side.upper => σ.capLimit x y) ∧ r + m ≤ σ.k - 1 := by
  classical
  dsimp only
  let τ := σ.part keep s m
  let gL : ℕ := if eL then 1 else 0
  let gR : ℕ := if eR then 1 else 0
  let g := gL + gR
  have max_witness (L : List ℕ) (f : List ℕ → ℕ) :
      ∃ ls ∈ L.sublists, ((L.sublists.map f).max?).getD 0 = f ls := by
    have hmem : f [] ∈ L.sublists.map f := List.mem_map.mpr ⟨[], by simp, rfl⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (List.isSome_max?_of_mem hmem)
    obtain ⟨ls, hls, hval⟩ := List.mem_map.mp (List.max?_mem hv)
    exact ⟨ls, hls, by simp [hv, hval]⟩
  have positive_sublist (top : ℕ) (ls : List ℕ)
      (hls : ls ∈ (σ.levelsOn s top).sublists) : ∀ N ∈ ls, 1 ≤ N := by
    intro N hN
    exact (Ctx.Context.one_le_of_mem_levelsOn
      ((List.mem_sublists.mp hls).subset hN)).1
  have mapped_skip (top top' : ℕ)
      (hl : τ.levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1))
      (ls : List ℕ) (hls : ls ∈ (σ.levelsOn s top).sublists) :
      ls.map (· + 1) ∈ (τ.levelsOn s top').sublists := by
    rw [hl, List.mem_sublists]
    exact List.sublist_cons_iff.mpr
      (Or.inl ((List.mem_sublists.mp hls).map _))
  have mapped_take (top top' : ℕ)
      (hl : τ.levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1))
      (ls : List ℕ) (hls : ls ∈ (σ.levelsOn s top).sublists) :
      1 :: ls.map (· + 1) ∈ (τ.levelsOn s top').sublists := by
    rw [hl, List.mem_sublists]
    exact List.sublist_cons_iff.mpr
      (Or.inr ⟨_, rfl, (List.mem_sublists.mp hls).map _⟩)
  have left_skip (top top' r : ℕ)
      (hl : τ.levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1)) :
      σ.leftExt s top r ≤ τ.leftExt s top' r := by
    obtain ⟨ls, hls, heq⟩ := max_witness (σ.levelsOn s top)
      (fun ls ↦ (ls.foldl (Ctx.Context.leftStep σ) (r, 0)).2)
    rw [Ctx.Context.leftExt_eq, heq]
    have hle := Ctx.le_getD_max?_of_mem
      (List.mem_map.mpr ⟨ls.map (· + 1), mapped_skip top top' hl ls hls, rfl⟩ :
        ((ls.map (· + 1)).foldl (Ctx.Context.leftStep τ) (r, 0)).2 ∈
          (τ.levelsOn s top').sublists.map
            (fun xs ↦ (xs.foldl (Ctx.Context.leftStep τ) (r, 0)).2))
    rw [Ctx.Context.foldl_leftStep_part_map σ keep s m ls
      (positive_sublist top ls hls)] at hle
    exact hle
  have right_skip (top top' r : ℕ)
      (hl : τ.levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1)) :
      σ.rightExt s top r ≤ τ.rightExt s top' r := by
    obtain ⟨ls, hls, heq⟩ := max_witness (σ.levelsOn s top)
      (fun ls ↦ (ls.foldl (Ctx.Context.rightStep σ) (r, 0)).2)
    rw [Ctx.Context.rightExt_eq, heq]
    have hle := Ctx.le_getD_max?_of_mem
      (List.mem_map.mpr ⟨ls.map (· + 1), mapped_skip top top' hl ls hls, rfl⟩ :
        ((ls.map (· + 1)).foldl (Ctx.Context.rightStep τ) (r, 0)).2 ∈
          (τ.levelsOn s top').sublists.map
            (fun xs ↦ (xs.foldl (Ctx.Context.rightStep τ) (r, 0)).2))
    rw [Ctx.Context.foldl_rightStep_part_map σ keep s m ls
      (positive_sublist top ls hls)] at hle
    exact hle
  have left_gain (top top' p x : ℕ)
      (hl : τ.levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1))
      (hx : x ∈ τ.extPositions 1) (hxp : x < p) :
      1 + σ.leftExt s top x ≤ τ.leftExt s top' p := by
    have hxfilter : x ∈ (τ.extPositions 1).filter (· < p) := by simp [hx, hxp]
    cases hh : ((τ.extPositions 1).filter (· < p)).getLast? with
    | none =>
      have hnil := List.getLast?_eq_none_iff.mp hh
      rw [hnil] at hxfilter
      exact (List.not_mem_nil hxfilter).elim
    | some z =>
      have hlast : ((τ.extPositions 1).filter (· < p)).getLast
          (List.ne_nil_of_mem hxfilter) = z := by
        rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hxfilter)] at hh
        exact Option.some.inj hh
      have hsorted : (τ.extPositions 1).Pairwise (· ≤ ·) :=
        (List.pairwise_lt_range.filter _).imp le_of_lt
      have hxz : x ≤ z := by
        simpa only [hlast] using (hsorted.filter _).rel_getLast hxfilter
      have hmono := (ctx_pure_extensions_position_monotone σ s top x z hxz).1
      obtain ⟨ls, hls, heq⟩ := max_witness (σ.levelsOn s top)
        (fun ls ↦ (ls.foldl (Ctx.Context.leftStep σ) (z, 0)).2)
      have hle := Ctx.le_getD_max?_of_mem
        (List.mem_map.mpr ⟨1 :: ls.map (· + 1),
          mapped_take top top' hl ls hls, rfl⟩ :
          ((1 :: ls.map (· + 1)).foldl (Ctx.Context.leftStep τ) (p, 0)).2 ∈
            (τ.levelsOn s top').sublists.map
              (fun xs ↦ (xs.foldl (Ctx.Context.leftStep τ) (p, 0)).2))
      have hstep : Ctx.Context.leftStep τ (p, 0) 1 = (z, 1) := by
        simp [Ctx.Context.leftStep, hh]
      rw [List.foldl_cons, hstep, Ctx.Context.foldl_leftStep_part_map σ keep s m ls
        (positive_sublist top ls hls), Ctx.Context.foldl_leftStep_count] at hle
      have hmax : σ.leftExt s top z =
          (ls.foldl (Ctx.Context.leftStep σ) (z, 0)).2 := by
        simpa only [Ctx.Context.leftExt_eq] using heq
      rw [← hmax] at hle
      exact (Nat.add_le_add_left hmono 1).trans hle
  have right_gain (top top' q y : ℕ)
      (hl : τ.levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1))
      (hy : y ∈ τ.extPositions 1) (hqy : q < y) :
      1 + σ.rightExt s top y ≤ τ.rightExt s top' q := by
    have hyfilter : y ∈ (τ.extPositions 1).filter (q < ·) := by simp [hy, hqy]
    cases hh : ((τ.extPositions 1).filter (q < ·)).head? with
    | none =>
      have hnil := List.head?_eq_none_iff.mp hh
      rw [hnil] at hyfilter
      exact (List.not_mem_nil hyfilter).elim
    | some z =>
      have hhead : ((τ.extPositions 1).filter (q < ·)).head
          (List.ne_nil_of_mem hyfilter) = z := by
        rw [List.head?_eq_some_head (List.ne_nil_of_mem hyfilter)] at hh
        exact Option.some.inj hh
      have hsorted : (τ.extPositions 1).Pairwise (· ≤ ·) :=
        (List.pairwise_lt_range.filter _).imp le_of_lt
      have hzy : z ≤ y := by
        simpa only [hhead] using (hsorted.filter _).rel_head hyfilter
      have hmono := (ctx_pure_extensions_position_monotone σ s top z y hzy).2
      obtain ⟨ls, hls, heq⟩ := max_witness (σ.levelsOn s top)
        (fun ls ↦ (ls.foldl (Ctx.Context.rightStep σ) (z, 0)).2)
      have hle := Ctx.le_getD_max?_of_mem
        (List.mem_map.mpr ⟨1 :: ls.map (· + 1),
          mapped_take top top' hl ls hls, rfl⟩ :
          ((1 :: ls.map (· + 1)).foldl (Ctx.Context.rightStep τ) (q, 0)).2 ∈
            (τ.levelsOn s top').sublists.map
              (fun xs ↦ (xs.foldl (Ctx.Context.rightStep τ) (q, 0)).2))
      have hstep : Ctx.Context.rightStep τ (q, 0) 1 = (z, 1) := by
        simp [Ctx.Context.rightStep, hh]
      rw [List.foldl_cons, hstep, Ctx.Context.foldl_rightStep_part_map σ keep s m ls
        (positive_sublist top ls hls), Ctx.Context.foldl_rightStep_count] at hle
      have hmax : σ.rightExt s top z =
          (ls.foldl (Ctx.Context.rightStep σ) (z, 0)).2 := by
        simpa only [Ctx.Context.rightExt_eq] using heq
      rw [← hmax] at hle
      exact (Nat.add_le_add_left hmono 1).trans hle
  have both_lift (top top' : ℕ)
      (hl : τ.levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1)) :
      g + σ.leftExt s top x + σ.rightExt s top y ≤
        τ.leftExt s top' p + τ.rightExt s top' q := by
    have hleft : gL + σ.leftExt s top x ≤ τ.leftExt s top' p := by
      cases eL with
      | false =>
        change x = p at hL
        simpa [gL, hL] using left_skip top top' p hl
      | true =>
        change x < p ∧ x ∈ τ.extPositions 1 at hL
        exact left_gain top top' p x hl hL.2 hL.1
    have hright : gR + σ.rightExt s top y ≤ τ.rightExt s top' q := by
      cases eR with
      | false =>
        change y = q at hR
        simpa [gR, hR] using right_skip top top' q hl
      | true =>
        change q < y ∧ y ∈ τ.extPositions 1 at hR
        exact right_gain top top' q y hl hR.2 hR.1
    dsimp only [g]
    omega
  have hlevels0 : τ.levelsOn s 0 = 1 :: (σ.levelsOn s 0).map (· + 1) :=
    Ctx.Context.part_levelsOn_self_zero hside
  have hchain : g + σ.chainExt s x y ≤ τ.chainExt s p q := by
    have h := both_lift 0 0 hlevels0
    simp only [Ctx.Context.chainExt]
    omega
  have hchainJoin : g + σ.chainExt s x y ≤ τ.joinExt s p q :=
    hchain.trans (Ctx.Context.chainExt_le_joinExt τ s p q)
  have hg : g ≤ τ.joinExt s p q := by omega
  have hjoinEach (N : ℕ) (hN : N ∈ σ.levelsOn s 0) :
      g + (σ.leftExt s N x + σ.rightExt s N y + σ.maximumAt N) ≤
        τ.joinExt s p q := by
    have hN1 := (Ctx.Context.one_le_of_mem_levelsOn hN).1
    have hlevels := Ctx.Context.part_levelsOn_self_succ hside hN1
    have hboth := both_lift N (N + 1) hlevels
    have hmem : N + 1 ∈ τ.levelsOn s 0 := by
      rw [hlevels0]
      exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨N, hN, rfl⟩))
    have hjoin := Ctx.Context.le_joinExt_of_mem_levelsOn hmem p q
    have hmax := Ctx.Context.part_maximumAt_succ σ keep s m hN1
    change τ.maximumAt (N + 1) = σ.maximumAt N at hmax
    rw [hmax] at hjoin
    omega
  have hjoin : g + σ.joinExt s x y ≤ τ.joinExt s p q := by
    have hold : σ.joinExt s x y ≤ τ.joinExt s p q - g := by
      change max (σ.chainExt s x y)
        ((((σ.levelsOn s 0).map fun N ↦
          σ.leftExt s N x + σ.rightExt s N y + σ.maximumAt N).max?).getD 0) ≤
        τ.joinExt s p q - g
      apply max_le
      · omega
      · apply Ctx.getD_max?_le
        intro v hv
        obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hv
        have h := hjoinEach N hN
        omega
    omega
  have hm : m ≤ τ.joinExt s p q := by
    have hmem : 1 ∈ τ.levelsOn s 0 := by rw [hlevels0]; simp
    have h := Ctx.Context.le_joinExt_of_mem_levelsOn hmem p q
    have hmax : τ.maximumAt 1 = m := by
      simp [τ, Ctx.Context.maximumAt, Ctx.Context.part_maxima]
    rw [hmax] at h
    omega
  have hlimit (r : ℕ) (hr : 0 < r)
      (h : r ≤ (match s with
        | Ctx.Side.lower => τ.cupLimit p q
        | Ctx.Side.upper => τ.capLimit p q)) :
      r + g ≤ (match s with
        | Ctx.Side.lower => σ.cupLimit x y
        | Ctx.Side.upper => σ.capLimit x y) ∧ r + m ≤ σ.k - 1 := by
    cases s with
    | lower =>
      change r ≤ min (σ.u - 1 - τ.chainExt Ctx.Side.lower p q)
        (σ.k - 1 - τ.joinExt Ctx.Side.lower p q) at h
      change r + g ≤ min (σ.u - 1 - σ.chainExt Ctx.Side.lower x y)
        (σ.k - 1 - σ.joinExt Ctx.Side.lower x y) ∧ r + m ≤ σ.k - 1
      have hc := h.trans (min_le_left _ _)
      have hj := h.trans (min_le_right _ _)
      constructor
      · apply le_min <;> omega
      · omega
    | upper =>
      change r ≤ min (σ.a - 1 - τ.chainExt Ctx.Side.upper p q)
        (σ.k - 1 - τ.joinExt Ctx.Side.upper p q) at h
      change r + g ≤ min (σ.a - 1 - σ.chainExt Ctx.Side.upper x y)
        (σ.k - 1 - σ.joinExt Ctx.Side.upper x y) ∧ r + m ≤ σ.k - 1
      have hc := h.trans (min_le_left _ _)
      have hj := h.trans (min_le_right _ _)
      constructor
      · apply le_min <;> omega
      · omega
  refine ⟨hchain, hjoin, hm, ?_⟩
  intro r hr h
  cases s <;> exact hlimit r hr h


end ErdosSzekeres
