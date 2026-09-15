import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Three ordered actual markers on one axis force every active child in the exterior region beyond the oldest marker to share a singleton opposite rank, so the full recursive bound is at most one when that axis global is at most five. Both reflected orders, arbitrary histories, inactive children, maxima, and k remain explicit. This standalone theorem replaces a repeated local argument in younger-surrounded complement estimates; exact search found no registered equivalent.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_one_of_common_singleton_rank
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_three_ordered_markers_exterior_unit_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s : Ctx.Side) (J N M a x y : ℕ) (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hJN : J < N) (hNM : N < M) (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (ha : a ∈ σ.extPositions J) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (horder : (a < x ∧ x < y ∧ ∀ p ∈ σ.childPositions, p < a) ∨ (y < x ∧ x < a ∧ ∀ p ∈ σ.childPositions, a < p)) : σ.bound ≤ 1 := by
  classical
  have hTrip (ρ : Context) (A B D a b d : ℕ)
      (hA : A ∈ ρ.levels) (hB : B ∈ ρ.levels) (hD : D ∈ ρ.levels)
      (hAB : A < B) (hBD : B < D)
      (hAs : ρ.sideAt A = s) (hBs : ρ.sideAt B = s) (hDs : ρ.sideAt D = s)
      (ha : a ∈ ρ.extPositions A) (hb : b ∈ ρ.extPositions B)
      (hd : d ∈ ρ.extPositions D) :
      (∀ p, p < a → a < b → b < d → 3 ≤ ρ.rightExt s 0 p) ∧
      (∀ p, a < p → b < a → d < b → 3 ≤ ρ.leftExt s 0 p) := by
    have hAOn : A ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hA, by simp [hAs]⟩
    have hBOn : B ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hB, by simp [hBs]⟩
    have hDOn : D ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hD, by simp [hDs]⟩
    have hSorted : (ρ.levelsOn s 0).Pairwise (· < ·) := by
      apply List.Pairwise.filter
      exact List.pairwise_lt_range.map (fun i => i + 1)
        (fun i j h => by dsimp; omega)
    have hThree : [A, B, D].Sublist (ρ.levelsOn s 0) := by
      have hs : [A, B, D].Pairwise (· < ·) := by simp; omega
      have hsub : [A, B, D] ⊆ ρ.levelsOn s 0 := by
        intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hAOn
        · exact hBOn
        · exact hDOn
      have he : (ρ.levelsOn s 0).filter (· ∈ [A, B, D]) = [A, B, D] := by
        apply (hSorted.filter _).eq_of_mem_iff hs
        intro j
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨And.right, fun hj => ⟨hsub hj, hj⟩⟩
      rw [← he]
      exact List.filter_sublist
    have hSort (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
      (List.pairwise_lt_range.filter _).imp le_of_lt
    constructor
    · intro p hpa hab hbd
      have hmA : a ∈ (ρ.extPositions A).filter (p < ·) := by simp [ha, hpa]
      have hneA := List.ne_nil_of_mem hmA
      let u := ((ρ.extPositions A).filter (p < ·)).head hneA
      have hu : ((ρ.extPositions A).filter (p < ·)).head? = some u :=
        List.head?_eq_some_head hneA
      have hua : u ≤ a := ((hSort A).filter _).rel_head hmA
      have hmB : b ∈ (ρ.extPositions B).filter (u < ·) := by simp [hb]; omega
      have hneB := List.ne_nil_of_mem hmB
      let v := ((ρ.extPositions B).filter (u < ·)).head hneB
      have hv : ((ρ.extPositions B).filter (u < ·)).head? = some v :=
        List.head?_eq_some_head hneB
      have hvb : v ≤ b := ((hSort B).filter _).rel_head hmB
      have hmD : d ∈ (ρ.extPositions D).filter (v < ·) := by simp [hd]; omega
      have hneD := List.ne_nil_of_mem hmD
      have hh := le_getD_max?_of_mem (L := (ρ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
        (List.mem_map.mpr ⟨[A, B, D], List.mem_sublists.mpr hThree, rfl⟩)
      change _ ≤ ρ.rightExt s 0 p at hh
      simpa only [List.foldl_cons, List.foldl_nil, rightStep, hu, hv,
        List.head?_eq_some_head hneD] using hh
    · intro p hap hba hdb
      have hmA : a ∈ (ρ.extPositions A).filter (· < p) := by simp [ha, hap]
      have hneA := List.ne_nil_of_mem hmA
      let u := ((ρ.extPositions A).filter (· < p)).getLast hneA
      have hu : ((ρ.extPositions A).filter (· < p)).getLast? = some u :=
        List.getLast?_eq_some_getLast hneA
      have hau : a ≤ u := ((hSort A).filter _).rel_getLast hmA
      have hmB : b ∈ (ρ.extPositions B).filter (· < u) := by simp [hb]; omega
      have hneB := List.ne_nil_of_mem hmB
      let v := ((ρ.extPositions B).filter (· < u)).getLast hneB
      have hv : ((ρ.extPositions B).filter (· < u)).getLast? = some v :=
        List.getLast?_eq_some_getLast hneB
      have hbv : b ≤ v := ((hSort B).filter _).rel_getLast hmB
      have hmD : d ∈ (ρ.extPositions D).filter (· < v) := by simp [hd]; omega
      have hneD := List.ne_nil_of_mem hmD
      have hh := le_getD_max?_of_mem (L := (ρ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
        (List.mem_map.mpr ⟨[A, B, D], List.mem_sublists.mpr hThree, rfl⟩)
      change _ ≤ ρ.leftExt s 0 p at hh
      simpa only [List.foldl_cons, List.foldl_nil, leftStep, hu, hv,
        List.getLast?_eq_some_getLast hneD] using hh
  rcases horder with ⟨hax, hxy, hChildren⟩ | ⟨hyx, hxa, hChildren⟩
  · have hRank : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p →
        0 < σ.capLimit p p → σ.leftExt s 0 p + 1 = 1 ∧
        1 + σ.rightExt s 0 p =
          (match (generalizing := false) s with
            | Side.lower => σ.u - 1
            | Side.upper => σ.a - 1) := by
      intro p hp hcup hcap
      have ht := (hTrip σ J N M a x y hJ hN hM hJN hNM hJs hNs hMs ha hx hy).1
        p (hChildren p hp) hax hxy
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal hcup hcap ⊢ <;>
        omega
    exact (ctx_bound_le_one_of_common_singleton_rank σ hpositive s 1 hRank).2.1
  · have hRank : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p →
        0 < σ.capLimit p p → σ.leftExt s 0 p + 1 = 4 ∧
        4 + σ.rightExt s 0 p =
          (match (generalizing := false) s with
            | Side.lower => σ.u - 1
            | Side.upper => σ.a - 1) := by
      intro p hp hcup hcap
      have ht := (hTrip σ J N M a x y hJ hN hM hJN hNM hJs hNs hMs ha hx hy).2
        p (hChildren p hp) hxa hyx
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal hcup hcap ⊢ <;>
        omega
    exact (ctx_bound_le_one_of_common_singleton_rank σ hpositive s 4 hRank).2.1

end ErdosSzekeres
