import ESBlueprint.B.CtxAxisRegionLimitsExact

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Exact chosen-capacity profile forced by two nonunit children straddling an actual chosen marker under chosen global at most four. The global parameter equals four, every child in either exterior marker region has chosen capacity exactly two, and every child in the interior region has chosen capacity at most one. Neither opposite activity nor positivity is needed; opposite-axis history, unused levels and maxima remain arbitrary. Combines the unique actual chosen-level reduction with exact limits within a chosen-axis marker region. Eliminates mixed exterior unit/nonunit capacities from the remaining strict rank-pair collision recurrence: the only possible active unit zone is the interior.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonunit_straddling_capacity_profile (σ : Ctx.Context) (s : Ctx.Side) (N x p q : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hp : p ∈ σ.childPositions) (hq : q ∈ σ.childPositions)
  (hpnonunit : 2 ≤ (match s with
    | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p))
  (hqnonunit : 2 ≤ (match s with
    | Ctx.Side.lower => σ.cupLimit q q | Ctx.Side.upper => σ.capLimit q q))
  (hpx : p < x) (hxq : x < q)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) :
  let global := match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let capacity := fun r => match s with
    | Ctx.Side.lower => σ.cupLimit r r | Ctx.Side.upper => σ.capLimit r r
  let markers := (σ.levelsOn s 0).toFinset.biUnion (fun j => (σ.extPositions j).toFinset)
  let label := fun r => if (markers.filter (· < r)).Nonempty then
    if (markers.filter (r < ·)).Nonempty then (1 : ℕ) else 2 else 0
  global = 4 ∧ ∀ r ∈ σ.childPositions,
    ((label r = 0 ∨ label r = 2) → capacity r = 2) ∧
    (label r = 1 → capacity r ≤ 1) := by
  classical
  let G := match s with | Side.lower => σ.u | Side.upper => σ.a
  let C (r : ℕ) := match s with | Side.lower => σ.cupLimit r r | Side.upper => σ.capLimit r r
  let M := (σ.levelsOn s 0).toFinset.biUnion (fun j => (σ.extPositions j).toFinset)
  let label (r : ℕ) := if (M.filter (· < r)).Nonempty then
    if (M.filter (r < ·)).Nonempty then (1 : ℕ) else 2 else 0
  change G = 4 ∧ ∀ r ∈ σ.childPositions,
    ((label r = 0 ∨ label r = 2) → C r = 2) ∧ (label r = 1 → C r ≤ 1)
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
  have hMark (z : ℕ) : z ∈ M ↔ ∃ j ∈ σ.levelsOn s 0, z ∈ σ.extPositions j := by
    simp [M]
  have hChildNe (r j z : ℕ) (hr : r ∈ σ.childPositions) (hz : z ∈ σ.extPositions j) :
      r ≠ z := by
    have hc := of_decide_eq_true (List.mem_filter.mp hr).2
    have he := (List.mem_filter.mp hz).2
    intro h
    subst z
    simp [hc] at he
  have hPext := hOneRight σ s N p x hNOn hx hpx
  have hQext := hOneLeft σ s N q x hNOn hx hxq
  have hG : G = 4 := by
    cases s <;> simp only [G, cupLimit, capLimit, chainExt] at hpnonunit hglobal ⊢ <;> omega
  have hCp : C p = 2 := by
    cases s <;> simp only [C, cupLimit, capLimit, chainExt] at hpnonunit hglobal ⊢ <;> omega
  have hCq : C q = 2 := by
    cases s <;> simp only [C, cupLimit, capLimit, chainExt] at hqnonunit hglobal ⊢ <;> omega
  have hUnique := ctx_nonunit_straddling_unique_axis_level σ s N x p q
    hN hNs hx hp hq hpnonunit hqnonunit hpx hxq hglobal
  refine ⟨hG, ?_⟩
  intro r hr
  constructor
  · intro he
    rcases he with he | he
    · have hNoLeft : ¬ (M.filter (· < r)).Nonempty := by
        intro hyes
        dsimp only [label] at he
        rw [if_pos hyes] at he
        split at he <;> omega
      have hBefore (j : ℕ) (hj : j ∈ σ.levelsOn s 0) (z : ℕ) (hz : z ∈ σ.extPositions j) : r < z := by
        have hn := hChildNe r j z hr hz
        by_contra h
        have hzr : z < r := by omega
        exact hNoLeft ⟨z, Finset.mem_filter.mpr ⟨(hMark z).mpr ⟨j, hj, hz⟩, hzr⟩⟩
      have hEq := ctx_axis_region_limits_exact σ s r p (by
        intro j hj z hz
        have ha := hBefore j hj z hz
        have hb := (hUnique j hj z hz).2.1
        exact ⟨by simp [not_lt_of_gt ha, not_lt_of_gt hb], by simp [ha, hb]⟩)
      have hh : C r = C p := by cases s <;> simpa only [C] using hEq.2.2.2
      exact hh.trans hCp
    · have hNoRight : ¬ (M.filter (r < ·)).Nonempty := by
        intro hyes
        dsimp only [label] at he
        split at he <;> omega
      have hAfter (j : ℕ) (hj : j ∈ σ.levelsOn s 0) (z : ℕ) (hz : z ∈ σ.extPositions j) : z < r := by
        have hn := hChildNe r j z hr hz
        by_contra h
        have hrz : r < z := by omega
        exact hNoRight ⟨z, Finset.mem_filter.mpr ⟨(hMark z).mpr ⟨j, hj, hz⟩, hrz⟩⟩
      have hEq := ctx_axis_region_limits_exact σ s r q (by
        intro j hj z hz
        have ha := hAfter j hj z hz
        have hb := (hUnique j hj z hz).2.2
        exact ⟨by simp [ha, hb], by simp [not_lt_of_gt ha, not_lt_of_gt hb]⟩)
      have hh : C r = C q := by cases s <;> simpa only [C] using hEq.2.2.2
      exact hh.trans hCq
  · intro he
    have hb : (M.filter (· < r)).Nonempty ∧ (M.filter (r < ·)).Nonempty := by
      by_cases hl : (M.filter (· < r)).Nonempty
      · by_cases hh : (M.filter (r < ·)).Nonempty
        · exact ⟨hl, hh⟩
        · simp [label, hl, hh] at he
      · simp [label, hl] at he
    obtain ⟨a, ha⟩ := hb.1
    obtain ⟨b, hb⟩ := hb.2
    obtain ⟨haM, har⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbM, hrb⟩ := Finset.mem_filter.mp hb
    obtain ⟨j, hj, hja⟩ := (hMark a).mp haM
    obtain ⟨l, hl, hlb⟩ := (hMark b).mp hbM
    have hL := hOneLeft σ s j r a hj hja har
    have hR := hOneRight σ s l r b hl hlb hrb
    cases s <;> simp only [C, cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega

end ErdosSzekeres
