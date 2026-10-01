import ESBlueprint.B.CtxUnitAxisActiveRegionPotential
import ESBlueprint.B.CtxChainOneChildrenExteriorOfTwoLevels

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 6000000
set_option maxRecDepth 15000

/-- An arbitrary raw positive-label context with an actual indexed chosen-axis marker and chosen global at most three has every-fuel and full bound at most two. With a second actual indexed chosen level distinct from the first, every-fuel and full bound are at most one. No WellFormed, one-level, k, global lower, maximum legality, opposite-axis bound, run or end-pattern premise. The actual marker makes every chosen point capacity unit; active marker-prefix ranks occupy at most the two exterior regions, and two-level chain-one geometry puts all active children in one common exterior. Reuses closed unit active-region potential and two-level exterior geometry. Supplies marked-global-three upper estimates and arbitrary-history degenerate companions for N_ends/N_root.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_bound_le_two_and_two_level_le_one_of_indexed_marker_global_three (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s : Ctx.Side) (N x : ℕ) (hN : N ∈ σ.levels) (hs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 3) : (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ ≤ 2) ∧ σ.bound ≤ 2 ∧ (∀ M y : ℕ, M ∈ σ.levels → N ≠ M → σ.sideAt M = s → y ∈ σ.extPositions M → (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ ≤ 1) ∧ σ.bound ≤ 1) := by
  classical
  let marks : Finset ℕ := (σ.levelsOn s 0).toFinset.biUnion
    (fun j => (σ.extPositions j).toFinset)
  let active : Finset ℕ := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let label (p : ℕ) := (marks.filter (· < p)).card
  let regions := (active.image label).card
  have hMark (z : ℕ) :
      z ∈ marks ↔ ∃ j ∈ σ.levelsOn s 0, z ∈ σ.extPositions j := by
    simp [marks]
  have hActive (p : ℕ) : p ∈ active ↔
      p ∈ σ.childPositions ∧ 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p := by
    simp [active]
  have hNoMark (p : ℕ) (hp : p ∈ σ.childPositions) : p ∉ marks := by
    intro hz
    obtain ⟨j,_,hj⟩ := (hMark p).mp hz
    have hc := (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hj).2
    simp only [decide_eq_true_eq] at hc he
    simp [hc] at he
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
  have hxMark : x ∈ marks := (hMark x).mpr ⟨N,hNOn,hx⟩
  have hChain (p : ℕ) (hp : p ∈ σ.childPositions) : 1 ≤ σ.chainExt s p p := by
    have hpx : p ≠ x := by
      intro he
      subst x
      exact hNoMark p hp hxMark
    by_cases h : x < p
    · have hL := hOneLeft σ s N p x hNOn hx h
      unfold chainExt
      omega
    · have hR := hOneRight σ s N p x hNOn hx (by omega)
      unfold chainExt
      omega
  have hUnit : ∀ p ∈ σ.childPositions,
      (match s with | Side.lower => σ.cupLimit p p | Side.upper => σ.capLimit p p) ≤ 1 := by
    intro p hp
    have hc := hChain p hp
    cases s with
    | lower =>
      dsimp only at hglobal ⊢
      simp only [cupLimit]
      omega
    | upper =>
      dsimp only at hglobal ⊢
      simp only [capLimit]
      omega
  have hChainActive (p : ℕ) (hp : p ∈ active) : σ.chainExt s p p ≤ 1 := by
    obtain ⟨_,hcup,hcap⟩ := (hActive p).mp hp
    cases s with
    | lower =>
      dsimp only at hglobal
      simp only [cupLimit] at hcup
      omega
    | upper =>
      dsimp only at hglobal
      simp only [capLimit] at hcap
      omega
  have hLabelLeft (p : ℕ) (hAll : ∀ z ∈ marks, z < p) : label p = marks.card := by
    change (marks.filter (· < p)).card = marks.card
    exact congrArg Finset.card (Finset.filter_eq_self.mpr hAll)
  have hLabelRight (p : ℕ) (hAll : ∀ z ∈ marks, p < z) : label p = 0 := by
    have he : marks.filter (· < p) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro z hz
      have hh := hAll z hz
      omega
    simp only [label,he,Finset.card_empty]
  have hLabelCases (p : ℕ) (hp : p ∈ active) : label p = 0 ∨ label p = marks.card := by
    have hpc := ((hActive p).mp hp).1
    by_cases hleft : ∃ z ∈ marks, z < p
    · right
      apply hLabelLeft
      obtain ⟨z,hz,hzp⟩ := hleft
      obtain ⟨j,hj,hzj⟩ := (hMark z).mp hz
      have hL := hOneLeft σ s j p z hj hzj hzp
      intro q hq
      by_contra hqp
      have hpq : p ≠ q := by
        intro he
        subst q
        exact hNoMark p hpc hq
      have hpq' : p < q := by omega
      obtain ⟨l,hl,hql⟩ := (hMark q).mp hq
      have hR := hOneRight σ s l p q hl hql hpq'
      have hc := hChainActive p hp
      unfold chainExt at hc
      omega
    · left
      apply hLabelRight
      intro z hz
      have hzp : ¬ z < p := by
        intro he
        exact hleft ⟨z,hz,he⟩
      have hpz : p ≠ z := by
        intro he
        subst z
        exact hNoMark p hpc hz
      omega
  have hRegionsTwo : regions ≤ 2 := by
    have hsub : active.image label ⊆ ({0,marks.card} : Finset ℕ) := by
      intro z hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hLabelCases p hp
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hPotential := ctx_unit_axis_active_region_potential σ hpositive s hUnit
  change (∀ fuel, boundFuel fuel σ ≤ regions) ∧
    σ.bound ≤ regions ∧ regions ≤ σ.numRuns at hPotential
  have hUniform (r : ℕ) (hlabels : ∀ p ∈ active, label p = r) : regions ≤ 1 := by
    have hsub : active.image label ⊆ ({r} : Finset ℕ) := by
      intro z hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      simpa only [Finset.mem_singleton] using hlabels p hp
    simpa only [Finset.card_singleton] using Finset.card_le_card hsub
  have hTwo (J L v w : ℕ) (hJ : J ∈ σ.levels) (hL : L ∈ σ.levels) (hJL : J < L)
      (hJs : σ.sideAt J = s) (hLs : σ.sideAt L = s)
      (hv : v ∈ σ.extPositions J) (hw : w ∈ σ.extPositions L) : regions ≤ 1 := by
    rcases ctx_chain_one_children_exterior_of_two_levels σ s J L v w
      hJ hL hJL hJs hLs hv hw with hl | hr
    · apply hUniform marks.card
      intro p hp
      apply hLabelLeft
      intro z hz
      obtain ⟨j,hj,hzj⟩ := (hMark z).mp hz
      exact hl.2 p ((hActive p).mp hp).1 (hChainActive p hp) j hj z hzj
    · apply hUniform 0
      intro p hp
      apply hLabelRight
      intro z hz
      obtain ⟨j,hj,hzj⟩ := (hMark z).mp hz
      exact hr.2 p ((hActive p).mp hp).1 (hChainActive p hp) j hj z hzj
  refine ⟨fun fuel => (hPotential.1 fuel).trans hRegionsTwo,
    hPotential.2.1.trans hRegionsTwo,?_⟩
  intro M y hM hNM hMs hy
  have hRegionsOne : regions ≤ 1 := by
    rcases lt_or_gt_of_ne hNM with hlt | hgt
    · exact hTwo N M x y hN hM hlt hs hMs hx hy
    · exact hTwo M N y x hM hN hgt hMs hs hy hx
  exact ⟨fun fuel => (hPotential.1 fuel).trans hRegionsOne,
    hPotential.2.1.trans hRegionsOne⟩

end ErdosSzekeres
