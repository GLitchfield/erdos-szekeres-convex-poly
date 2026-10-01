import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- Every fuel approximation and the full context bound are at most two when one global parameter is at most three and its axis contains an actual indexed external marker. Positive actual external labels suffice for a raw context; no well-formedness, run-count, sibling-maximum or length premise is needed. The small-axis rank-and-region potential is capped by the two exterior active regions. Reusable for near-saturated proper parts and the k=4 boundary of maximal-segment exchange.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_small_global_axis_rank_region_potential
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_bound_le_two_of_small_global_axis_with_indexed_marker (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s : Ctx.Side)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 3)
  (N x : ℕ) (hN : N ∈ σ.levelsOn s 0) (hx : x ∈ σ.extPositions N) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2) ∧ σ.bound ≤ 2 := by
  classical
  let t : Ctx.Side := match s with | .lower => .upper | .upper => .lower
  have hne : s ≠ t := by cases s <;> simp [t]
  let G (ρ : Ctx.Context) := match s with | .lower => ρ.u | .upper => ρ.a
  let B (ρ : Ctx.Context) := match t with | .lower => ρ.u - 1 | .upper => ρ.a - 1
  let marks (ρ : Ctx.Context) : Finset ℕ :=
    (ρ.levelsOn s 0).toFinset.biUnion (fun j => (ρ.extPositions j).toFinset)
  let active (ρ : Ctx.Context) : Finset ℕ := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let ranks (ρ : Ctx.Context) := (active ρ).biUnion
    (fun p => Finset.Icc (ρ.leftExt t 0 p + 1) (B ρ - ρ.rightExt t 0 p))
  let reg (ρ : Ctx.Context) :=
    ((active ρ).image (fun p => ((marks ρ).filter (· < p)).card)).card
  let V (ρ : Ctx.Context) :=
    if marks ρ = ∅ then (ranks ρ).card else min (reg ρ) (ranks ρ).card
  have hActive (ρ : Ctx.Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by
    simp [active]
  have hMark (ρ : Ctx.Context) (p : ℕ) : p ∈ marks ρ ↔
      ∃ j ∈ ρ.levelsOn s 0, p ∈ ρ.extPositions j := by
    simp [marks]
  have hNoMark (ρ : Ctx.Context) (p : ℕ) (hp : p ∈ ρ.childPositions) :
      p ∉ marks ρ := by
    intro hm
    obtain ⟨j, _, hx⟩ := (hMark ρ p).mp hm
    have hc := (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hx).2
    simp only [decide_eq_true_eq] at hc he
    simp [hc] at he
  have hOneLeft (ρ : Ctx.Context) (v : Ctx.Side) (j p y : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hy : y ∈ ρ.extPositions j) (hyp : y < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : y ∈ (ρ.extPositions j).filter (· < p) := by simp [hy, hyp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Ctx.Context) (v : Ctx.Side) (j p y : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hy : y ∈ ρ.extPositions j) (hpy : p < y) :
      1 ≤ ρ.rightExt v 0 p := by
    have hm : y ∈ (ρ.extPositions j).filter (p < ·) := by simp [hy, hpy]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  let lim (ρ : Ctx.Context) (p : ℕ) := match s with
    | .lower => ρ.cupLimit p p
    | .upper => ρ.capLimit p p
  have hOwnPure (ρ : Ctx.Context) (hG : G ρ ≤ 3) (p : ℕ) :
      lim ρ p ≤ 2 - (ρ.leftExt s 0 p + ρ.rightExt s 0 p) := by
    cases s <;> dsimp [lim, G, cupLimit, capLimit, chainExt] at hG ⊢ <;> omega
  have hLimPos (ρ : Ctx.Context) (p : ℕ) (hp : p ∈ active ρ) :
      0 < lim ρ p := by
    have hc := (hActive _ _).mp hp
    cases s <;> dsimp [lim] <;> omega
  have hExterior (ρ : Ctx.Context) (hG : G ρ ≤ 3) (p : ℕ) (hp : p ∈ active ρ) :
      (∀ y ∈ marks ρ, y < p) ∨ (∀ y ∈ marks ρ, p < y) := by
    have hpc := ((hActive _ _).mp hp).1
    have hlim := hOwnPure ρ hG p
    have hpos := hLimPos ρ p hp
    by_cases hr : ∃ y ∈ marks ρ, p < y
    · right
      obtain ⟨y, hy, hpy⟩ := hr
      obtain ⟨j, hj, hyj⟩ := (hMark _ _).mp hy
      have hright := hOneRight ρ s j p y hj hyj hpy
      intro z hz
      have hneq : z ≠ p := by intro h; subst z; exact hNoMark ρ p hpc hz
      by_contra hpz
      obtain ⟨i, hi, hzi⟩ := (hMark _ _).mp hz
      have hleft := hOneLeft ρ s i p z hi hzi (by omega)
      omega
    · left
      intro y hy
      have hneq : y ≠ p := by intro h; subst y; exact hNoMark ρ p hpc hy
      have hn : ¬ p < y := fun h => hr ⟨y, hy, h⟩
      omega
  have hRegTwo (ρ : Ctx.Context) (hG : G ρ ≤ 3) : reg ρ ≤ 2 := by
    have hs : (active ρ).image (fun p => ((marks ρ).filter (· < p)).card) ⊆
        {0, (marks ρ).card} := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      rcases hExterior ρ hG p hp with hl | hr
      · have he := Finset.filter_eq_self.mpr hl
        simp only [he, Finset.mem_insert, Finset.mem_singleton, or_true]
      · have he : (marks ρ).filter (· < p) = ∅ :=
          Finset.filter_eq_empty_iff.mpr (fun y hy => by have := hr y hy; omega)
        simp only [he, Finset.card_empty, Finset.mem_insert, true_or]
    have hcard : ({0, (marks ρ).card} : Finset ℕ).card ≤ 2 := by
      have h := Finset.card_insert_le 0 ({(marks ρ).card} : Finset ℕ)
      simpa only [Finset.card_singleton] using h
    exact (Finset.card_le_card hs).trans hcard
  have hmarks : marks σ ≠ ∅ := by
    have hm : x ∈ marks σ := (hMark σ x).mpr ⟨N, hN, hx⟩
    exact Finset.ne_empty_of_mem hm
  have hV : V σ ≤ 2 := by
    dsimp only [V]
    rw [if_neg hmarks]
    exact (Nat.min_le_left _ _).trans (hRegTwo σ hglobal)
  have hp := ctx_small_global_axis_rank_region_potential σ hpositive s t hne hglobal
  exact ⟨fun fuel => (hp.1 fuel).trans hV, hp.2.1.trans hV⟩

end ErdosSzekeres
