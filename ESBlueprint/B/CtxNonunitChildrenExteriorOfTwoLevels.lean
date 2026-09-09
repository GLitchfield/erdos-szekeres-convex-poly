import ESBlueprint.B.CtxBracketedChildrenUnitBound

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Two actual indexed levels on an axis with global parameter at most four force all nonunit children into one common exterior marker region. For levels N<M witnessed at positions x,y, every child with chosen capacity at least two lies beyond every indexed chosen marker in the direction from x to y. Includes inactive children, arbitrary maxima, unused levels, multiple marker positions at a level, and arbitrary external labels without a positivity premise. Two-step greedy extension witnesses exclude the wrong exterior; one marker on each side excludes the interior. Orients the nonunit rank contribution in the singleton-end sandwich mixed potential.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonunit_children_exterior_of_two_levels (σ : Ctx.Context) (s : Ctx.Side) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) :
  (x < y ∧ ∀ p ∈ σ.childPositions,
    2 ≤ (match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p) →
      ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z < p) ∨
  (y < x ∧ ∀ p ∈ σ.childPositions,
    2 ≤ (match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p) →
      ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, p < z) := by
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
  have hChildNe (p j z : ℕ) (hp : p ∈ σ.childPositions) (hz : z ∈ σ.extPositions j) :
      p ≠ z := by
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hz).2
    intro h
    subst z
    simp [hc] at he
  have hxy : x ≠ y := by
    intro h
    have ha := (List.mem_filter.mp hx).2
    have hb := (List.mem_filter.mp hy).2
    rw [← h] at hb
    cases he : σ.letterAt x with
    | child => simp [he] at ha
    | ext j v =>
      simp only [he, decide_eq_true_eq] at ha hb
      omega
  have hSmallChain (p : ℕ)
      (hp : 2 ≤ (match s with | Side.lower => σ.cupLimit p p | Side.upper => σ.capLimit p p)) :
      σ.chainExt s p p ≤ 1 := by
    cases hs : s <;> simp only [hs] at hglobal hp ⊢
    · simp only [cupLimit] at hp
      omega
    · simp only [capLimit] at hp
      omega
  have hNoBoth (p j k a b : ℕ) (hp : σ.chainExt s p p ≤ 1)
      (hj : j ∈ σ.levelsOn s 0) (hk : k ∈ σ.levelsOn s 0)
      (ha : a ∈ σ.extPositions j) (hb : b ∈ σ.extPositions k)
      (hap : a < p) (hpb : p < b) : False := by
    have hL := hOneLeft σ s j p a hj ha hap
    have hR := hOneRight σ s k p b hk hb hpb
    simp only [chainExt] at hp
    omega
  have hSortN : (σ.extPositions N).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp le_of_lt
  have hTwoRight (p : ℕ) (hpx : p < x) (hxy : x < y) : 2 ≤ σ.rightExt s 0 p := by
    have hm : x ∈ (σ.extPositions N).filter (p < ·) := by simp [hx, hpx]
    have hne := List.ne_nil_of_mem hm
    let w := ((σ.extPositions N).filter (p < ·)).head hne
    have hw : ((σ.extPositions N).filter (p < ·)).head? = some w :=
      List.head?_eq_some_head hne
    have hwx : w ≤ x := (hSortN.filter _).rel_head hm
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
  have hTwoLeft (p : ℕ) (hxp : x < p) (hyx : y < x) : 2 ≤ σ.leftExt s 0 p := by
    have hm : x ∈ (σ.extPositions N).filter (· < p) := by simp [hx, hxp]
    have hne := List.ne_nil_of_mem hm
    let w := ((σ.extPositions N).filter (· < p)).getLast hne
    have hw : ((σ.extPositions N).filter (· < p)).getLast? = some w :=
      List.getLast?_eq_some_getLast hne
    have hxw : x ≤ w := (hSortN.filter _).rel_getLast hm
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
  rcases lt_or_gt_of_ne hxy with hxy | hyx
  · refine Or.inl ⟨hxy, ?_⟩
    intro p hp hnonunit j hj z hz
    have hc := hSmallChain p hnonunit
    have hpxne := hChildNe p N x hp hx
    have hpyne := hChildNe p M y hp hy
    have hxp : x < p := by
      by_contra h
      have hR := hTwoRight p (by omega) hxy
      simp only [chainExt] at hc
      omega
    have hyp : y < p := by
      by_contra h
      exact hNoBoth p N M x y hc hNOn hMOn hx hy hxp (by omega)
    have hpzne := hChildNe p j z hp hz
    by_contra hzp
    exact hNoBoth p M j y z hc hMOn hj hy hz hyp (by omega)
  · refine Or.inr ⟨hyx, ?_⟩
    intro p hp hnonunit j hj z hz
    have hc := hSmallChain p hnonunit
    have hpxne := hChildNe p N x hp hx
    have hpyne := hChildNe p M y hp hy
    have hpx : p < x := by
      by_contra h
      have hL := hTwoLeft p (by omega) hyx
      simp only [chainExt] at hc
      omega
    have hpy : p < y := by
      by_contra h
      exact hNoBoth p M N y x hc hMOn hNOn hy hx (by omega) hpx
    have hpzne := hChildNe p j z hp hz
    by_contra hpz
    exact hNoBoth p j M z y hc hj hMOn hz hy (by omega) hpy

end ErdosSzekeres
