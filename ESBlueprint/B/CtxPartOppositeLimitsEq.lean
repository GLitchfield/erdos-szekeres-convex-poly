import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Taking a part preserves the opposite-side capacity exactly: an upper insertion preserves every cup limit, and a lower insertion preserves every cap limit, provided at least one child is removed. Uniform in positions, the kept set, and the inserted maximum. The nonempty removal identifies the new level side. Supplies the unchanged-coordinate comparison for mixed-side strip exchanges.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_attained_by_end_cut -/
theorem ctx_part_opposite_limits_eq (σ : Ctx.Context) (hwf : σ.WellFormed) (keep : List ℕ)
  (hremoved : ∃ r ∈ σ.childPositions, r ∉ keep) (m p q : ℕ) :
  (σ.part keep Ctx.Side.upper m).cupLimit p q = σ.cupLimit p q ∧
  (σ.part keep Ctx.Side.lower m).capLimit p q = σ.capLimit p q := by
  have hside (s : Side) : (σ.part keep s m).sideAt 1 = s := by
    obtain ⟨r, hr, hrkeep⟩ := hremoved
    apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) keep s m (q := r)
    rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1)]
    simp [hr, hrkeep]
  have hext (s t : Side) (hst : s ≠ t) :
      (σ.part keep s m).chainExt t p q = σ.chainExt t p q ∧
      (σ.part keep s m).joinExt t p q = σ.joinExt t p q := by
    let τ := σ.part keep s m
    have hlevels (N : ℕ) :
        τ.levelsOn t (if N = 0 then 0 else N + 1) = (σ.levelsOn t N).map (· + 1) := by
      unfold levelsOn
      change (σ.part keep s m).levels.filter _ = _
      rw [part_levels, List.filter_cons, List.filter_map]
      have heq : σ.levels.filter (fun l => decide ((σ.part keep s m).sideAt (l + 1) = t ∧
          ((if N = 0 then 0 else N + 1) = 0 ∨ l + 1 < (if N = 0 then 0 else N + 1)))) =
          σ.levels.filter (fun l => decide (σ.sideAt l = t ∧ (N = 0 ∨ l < N))) := by
        apply List.filter_congr
        intro l hl
        have hl1 := one_le_of_mem_levels hl
        by_cases hN : N = 0 <;> simp [hN, part_sideAt_succ σ keep s m hl1]
      simp only [Function.comp_def]
      rw [heq]
      have hτside : τ.sideAt 1 = s := hside s
      simp [hτside, hst]
    have hleft (N x : ℕ) :
        τ.leftExt t (if N = 0 then 0 else N + 1) x = σ.leftExt t N x := by
      simp only [leftExt_eq, hlevels, List.sublists_map, List.map_map]
      apply congrArg (fun ns : List ℕ => ns.max?.getD 0)
      apply List.map_congr_left
      intro ls hls
      have hpos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
        (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hl)).1
      exact congrArg Prod.snd (foldl_leftStep_part_map σ keep s m ls hpos (x, 0))
    have hright (N x : ℕ) :
        τ.rightExt t (if N = 0 then 0 else N + 1) x = σ.rightExt t N x := by
      simp only [rightExt_eq, hlevels, List.sublists_map, List.map_map]
      apply congrArg (fun ns : List ℕ => ns.max?.getD 0)
      apply List.map_congr_left
      intro ls hls
      have hpos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
        (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hl)).1
      exact congrArg Prod.snd (foldl_rightStep_part_map σ keep s m ls hpos (x, 0))
    have hchain : τ.chainExt t p q = σ.chainExt t p q := by
      have hL0 : τ.leftExt t 0 p = σ.leftExt t 0 p := by simpa using hleft 0 p
      have hR0 : τ.rightExt t 0 q = σ.rightExt t 0 q := by simpa using hright 0 q
      simp only [chainExt, hL0, hR0]
    refine ⟨hchain, ?_⟩
    unfold joinExt
    rw [hchain]
    congr 1
    rw [show τ.levelsOn t 0 = (σ.levelsOn t 0).map (· + 1) by simpa using hlevels 0,
      List.map_map]
    apply congrArg (fun ns : List ℕ => ns.max?.getD 0)
    apply List.map_congr_left
    intro N hN
    have hN1 := (one_le_of_mem_levelsOn hN).1
    have hL := hleft N p
    have hR := hright N q
    simp only [if_neg (by omega : N ≠ 0)] at hL hR
    change τ.leftExt t (N + 1) p + τ.rightExt t (N + 1) q + τ.maximumAt (N + 1) = _
    rw [hL, hR]
    change _ + (σ.part keep s m).maximumAt (N + 1) = _
    rw [part_maximumAt_succ σ keep s m hN1]
  have hlow := hext Side.upper Side.lower (by decide)
  have hupp := hext Side.lower Side.upper (by decide)
  simp only [cupLimit, capLimit, hlow.1, hlow.2, hupp.1, hupp.2]
  exact ⟨rfl, rfl⟩

end ErdosSzekeres
