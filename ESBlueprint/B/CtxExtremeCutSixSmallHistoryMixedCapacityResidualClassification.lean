import ESBlueprint.B.CtxExtremeCutSixElevenOfSmallChosenMaximaCapacityTwo
import ESBlueprint.B.CtxAllActiveCapacityThreeTwoMarkerTriangleBound
import ESBlueprint.B.CtxMixedCapacityChildrenSeparatedByOlderMarkerGlobalFive

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- At k six in the all-small chosen-history extreme, the cut total is at most eleven unless the companion has both an active chosen-capacity-three child and an active chosen-capacity-at-most-two child. In the residual, the older actual marker separates the low and high witnesses with the orientation forced by the two chosen markers. This isolates the sole mixed-support obstruction after the low-only and high-only companion bounds.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_extreme_cut_six_eleven_of_small_chosen_maxima_capacity_two, ErdosSzekeres.ctx_all_active_capacity_three_two_marker_triangle_bound, ErdosSzekeres.ctx_mixed_capacity_children_separated_by_older_marker_global_five, ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_extreme_cut_six_small_history_mixed_capacity_residual_classification (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hoppositeLower : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (hmax : ∀ j ∈ σ.levelsOn s 0, σ.maximumAt j ≤ 1) (keep : List ℕ) (m n p : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hm : m + 2 = σ.k) (hk : σ.k = 6) : let A := σ.part keep s m; let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; ((∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 11) ∧ A.bound + B.bound ≤ 11) ∨ ∃ high ∈ B.childPositions, 0 < B.cupLimit high high ∧ 0 < B.capLimit high high ∧ 3 ≤ (match s with | Ctx.Side.lower => B.cupLimit high high | Ctx.Side.upper => B.capLimit high high) ∧ ∃ low ∈ B.childPositions, 0 < B.cupLimit low low ∧ 0 < B.capLimit low low ∧ (match s with | Ctx.Side.lower => B.cupLimit low low | Ctx.Side.upper => B.capLimit low low) ≤ 2 ∧ ((x < y ∧ low < y ∧ y < high) ∨ (y < x ∧ high < y ∧ y < low)) := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let A := σ.part keep s m
  let B := σ.part rest t n
  change ((∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 11) ∧
      A.bound + B.bound ≤ 11) ∨
    ∃ high ∈ B.childPositions, 0 < B.cupLimit high high ∧
      0 < B.capLimit high high ∧
      3 ≤ (match s with
        | Ctx.Side.lower => B.cupLimit high high
        | Ctx.Side.upper => B.capLimit high high) ∧
      ∃ low ∈ B.childPositions, 0 < B.cupLimit low low ∧
        0 < B.capLimit low low ∧
        (match s with
          | Ctx.Side.lower => B.cupLimit low low
          | Ctx.Side.upper => B.capLimit low low) ≤ 2 ∧
        ((x < y ∧ low < y ∧ y < high) ∨ (y < x ∧ high < y ∧ y < low))
  have hpa : p ∈ σ.childPositions ∧ p ∈ keep := by
    simpa only [Ctx.Context.part_childPositions, List.mem_filter, decide_eq_true_eq] using hp
  have hpB : p ∈ B.extPositions 1 := by
    change p ∈ (σ.part rest t n).extPositions 1
    rw [Ctx.Context.part_extPositions_one hpositive]
    exact List.mem_filter.mpr ⟨hpa.1, by simp [rest, hpa.2]⟩
  have hBsideOne : B.sideAt 1 = t :=
    Ctx.Context.part_sideAt_one_of_mem hpositive rest t n hpB
  have hNpos := Ctx.Context.one_le_of_mem_levels hN
  have hMpos := Ctx.Context.one_le_of_mem_levels hM
  have hNB : N + 1 ∈ B.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hMB : M + 1 ∈ B.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hNsB : B.sideAt (N + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest t n hNpos).trans hNs
  have hMsB : B.sideAt (M + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest t n hMpos).trans hMs
  have hxB : x ∈ B.extPositions (N + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ rest t n hNpos]
    exact hx
  have hyB : y ∈ B.extPositions (M + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ rest t n hMpos]
    exact hy
  have hChosenB : ∀ j ∈ B.levelsOn s 0, ∀ z ∈ B.extPositions j,
      z = x ∨ z = y := by
    have hs : B.sideAt 1 ≠ s := by rw [hBsideOne]; exact Ne.symm hne
    intro j hj z hz
    rw [Ctx.Context.part_levelsOn_other_zero hs] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [Ctx.Context.part_extPositions_succ σ rest t n
      (Ctx.Context.one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hz
    exact hchosen i hi z hz
  have hAtLevelB (j i z : ℕ) (hz : z ∈ B.extPositions j)
      (hz' : z ∈ B.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hz).2
    have hi := (List.mem_filter.mp hz').2
    cases he : B.letterAt z <;> simp [he] at hj hi
    omega
  have hYoungB : ∀ j ∈ B.levelsOn s (N + 1), B.extPositions j = [] := by
    intro j hj
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z hz
    have hh := List.mem_filter.mp hj
    have hpred := of_decide_eq_true hh.2
    have hOn : j ∈ B.levelsOn s 0 :=
      List.mem_filter.mpr ⟨hh.1, by simp [hpred.1]⟩
    rcases hChosenB j hOn z hz with hzx | hzy
    · have he := hAtLevelB j (N + 1) x (by simpa only [hzx] using hz) hxB
      omega
    · have he := hAtLevelB j (M + 1) y (by simpa only [hzy] using hz) hyB
      omega
  have hPosB := ctx_part_positive_letters σ rest t n
  have hGlobalB : (match s with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) ≤ 5 := by
    cases s <;> exact hchosenGlobal
  by_cases hsmall : ∀ q ∈ B.childPositions, 0 < B.cupLimit q q →
      0 < B.capLimit q q →
      (match s with
        | Ctx.Side.lower => B.cupLimit q q
        | Ctx.Side.upper => B.capLimit q q) ≤ 2
  · left
    exact ctx_extreme_cut_six_eleven_of_small_chosen_maxima_capacity_two σ hpositive
      s t hne hchosenGlobal hoppositeLower hopposite hmax keep m n p hp hm hk hsmall
  · push Not at hsmall
    obtain ⟨high, hhighmem, hhighcup, hhighcap, hhighnot⟩ := hsmall
    have hhigh : 3 ≤ (match s with
        | Ctx.Side.lower => B.cupLimit high high
        | Ctx.Side.upper => B.capLimit high high) := by
      cases s <;> simp only at hhighnot ⊢ <;> omega
    by_cases hallHigh : ∀ q ∈ B.childPositions, 0 < B.cupLimit q q →
        0 < B.capLimit q q →
        3 ≤ (match s with
          | Ctx.Side.lower => B.cupLimit q q
          | Ctx.Side.upper => B.capLimit q q)
    · left
      have hPosA := ctx_part_positive_letters σ keep s m
      have hAlevel : 1 ∈ A.levels := by simp [A, Ctx.Context.part_levels]
      have hAlarge : A.k - 2 ≤ A.maximumAt 1 := by
        rw [Ctx.Context.part_maximumAt_one]
        change σ.k - 2 ≤ m
        omega
      have hA := ctx_bound_le_one_of_large_sibling_maximum A hPosA 1 hAlevel hAlarge
      have hB := ctx_all_active_capacity_three_two_marker_triangle_bound B hPosB s t hne
        (N + 1) (M + 1) x y hNB hMB (by omega) hNsB hMsB hxB hyB hYoungB
        hGlobalB hallHigh
      have hChoose : (match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a).choose 2 ≤ 10 := by
        have hc := Nat.choose_le_choose 2 hopposite
        cases t <;> norm_num at hc ⊢ <;> exact hc
      exact ⟨fun f g => (Nat.add_le_add (hA.1 f) ((hB.1 g).trans hChoose)).trans (by omega),
        (Nat.add_le_add hA.2 (hB.2.trans hChoose)).trans (by omega)⟩
    · push Not at hallHigh
      obtain ⟨low, hlowmem, hlowcup, hlowcap, hlownot⟩ := hallHigh
      have hlow : (match s with
          | Ctx.Side.lower => B.cupLimit low low
          | Ctx.Side.upper => B.capLimit low low) ≤ 2 := by
        cases s <;> simp only at hlownot ⊢ <;> omega
      have hsep := ctx_mixed_capacity_children_separated_by_older_marker_global_five
        B s (N + 1) (M + 1) x y high low hNB hMB (by omega) hNsB hMsB
        hxB hyB hGlobalB hChosenB hhighmem hlowmem hhigh hlow
      exact Or.inr ⟨high, hhighmem, hhighcup, hhighcap, hhigh, low, hlowmem,
        hlowcup, hlowcap, hlow, hsep⟩

end ErdosSzekeres
