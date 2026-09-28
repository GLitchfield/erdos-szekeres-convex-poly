import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

/-- Taking a part can only decrease its cup and cap limits at every pair of positions. The result is unconditional: shifted old levels preserve every old extension witness and every old sibling join, so the new level can only add restrictions. This supplies capacity transport for recursive pointwise upper bounds and cut comparisons.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_part_limits_le (σ : Ctx.Context) (keep : List ℕ) (s : Ctx.Side) (m p q : ℕ) :
  (σ.part keep s m).cupLimit p q ≤ σ.cupLimit p q ∧
  (σ.part keep s m).capLimit p q ≤ σ.capLimit p q := by
  let τ := σ.part keep s m
  have hlevels (t : Ctx.Side) (N : ℕ) :
      List.Sublist ((σ.levelsOn t N).map (· + 1)) (τ.levelsOn t (if N = 0 then 0 else N + 1)) := by
    unfold Ctx.Context.levelsOn
    change List.Sublist _ ((σ.part keep s m).levels.filter _)
    rw [Ctx.Context.part_levels, List.filter_cons, List.filter_map]
    have heq : σ.levels.filter (fun l => decide ((σ.part keep s m).sideAt (l + 1) = t ∧
        ((if N = 0 then 0 else N + 1) = 0 ∨ l + 1 < (if N = 0 then 0 else N + 1)))) =
        σ.levels.filter (fun l => decide (σ.sideAt l = t ∧ (N = 0 ∨ l < N))) := by
      apply List.filter_congr
      intro l hl
      have hl1 := Ctx.Context.one_le_of_mem_levels hl
      by_cases hN : N = 0 <;>
        simp [hN, Ctx.Context.part_sideAt_succ σ keep s m hl1]
    simp only [Function.comp_def]
    rw [heq]
    split_ifs <;> simp_all
  have hleft (t : Ctx.Side) (N p : ℕ) :
      σ.leftExt t N p ≤ τ.leftExt t (if N = 0 then 0 else N + 1) p := by
    simp only [Ctx.Context.leftExt_eq]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    have hsub := List.mem_sublists.mp hls
    have hpos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
      (Ctx.Context.one_le_of_mem_levelsOn (hsub.subset hl)).1
    refine ⟨((ls.map (· + 1)).foldl (Ctx.Context.leftStep τ) (p, 0)).2,
      List.mem_map.mpr ⟨_, List.mem_sublists.mpr ((hsub.map _).trans (hlevels t N)), rfl⟩, ?_⟩
    exact le_of_eq (congrArg Prod.snd (Ctx.Context.foldl_leftStep_part_map σ keep s m ls hpos (p, 0))).symm
  have hright (t : Ctx.Side) (N p : ℕ) :
      σ.rightExt t N p ≤ τ.rightExt t (if N = 0 then 0 else N + 1) p := by
    simp only [Ctx.Context.rightExt_eq]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    have hsub := List.mem_sublists.mp hls
    have hpos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
      (Ctx.Context.one_le_of_mem_levelsOn (hsub.subset hl)).1
    refine ⟨((ls.map (· + 1)).foldl (Ctx.Context.rightStep τ) (p, 0)).2,
      List.mem_map.mpr ⟨_, List.mem_sublists.mpr ((hsub.map _).trans (hlevels t N)), rfl⟩, ?_⟩
    exact le_of_eq (congrArg Prod.snd (Ctx.Context.foldl_rightStep_part_map σ keep s m ls hpos (p, 0))).symm
  have hchain (t : Ctx.Side) : σ.chainExt t p q ≤ τ.chainExt t p q := by
    simpa only [Ctx.Context.chainExt, if_pos rfl] using Nat.add_le_add (hleft t 0 p) (hright t 0 q)
  have hjoin (t : Ctx.Side) : σ.joinExt t p q ≤ τ.joinExt t p q := by
    unfold Ctx.Context.joinExt
    apply max_le_max (hchain t)
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hx
    have hN1 := (Ctx.Context.one_le_of_mem_levelsOn hN).1
    have hmem : N + 1 ∈ τ.levelsOn t 0 := by
      simpa only [if_pos rfl] using (hlevels t 0).subset (List.mem_map.mpr ⟨N, hN, rfl⟩)
    refine ⟨_, List.mem_map.mpr ⟨N + 1, hmem, rfl⟩, ?_⟩
    have hL := hleft t N p
    have hR := hright t N q
    have hM := Ctx.Context.part_maximumAt_succ σ keep s m hN1
    simp only [if_neg (by omega : N ≠ 0)] at hL hR
    change _ ≤ _ + τ.maximumAt (N + 1)
    change τ.maximumAt (N + 1) = _ at hM
    rw [hM]
    exact Nat.add_le_add_right (Nat.add_le_add hL hR) _
  have hcl := hchain Ctx.Side.lower
  have hcu := hchain Ctx.Side.upper
  have hjl := hjoin Ctx.Side.lower
  have hju := hjoin Ctx.Side.upper
  change τ.cupLimit p q ≤ _ ∧ τ.capLimit p q ≤ _
  simp only [Ctx.Context.cupLimit, Ctx.Context.capLimit]
  have ha : τ.a = σ.a := rfl
  have hu : τ.u = σ.u := rfl
  have hk : τ.k = σ.k := rfl
  rw [ha, hu, hk]
  omega

end ErdosSzekeres
