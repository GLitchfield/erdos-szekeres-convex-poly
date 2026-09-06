import ErdosSzekeres.DecomposableContextLemmas
import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

namespace Ctx
namespace Context

/-! ### Fuel monotonicity -/

theorem boundFuel_le_succ : ∀ (fuel : ℕ) (σ : Context), boundFuel fuel σ ≤ boundFuel (fuel + 1) σ := by
  intro fuel
  induction fuel with
  | zero => intro σ; exact Nat.zero_le _
  | succ fuel ih =>
    intro σ
    rw [boundFuel.eq_2 σ fuel, boundFuel.eq_2 σ (fuel + 1)]
    split_ifs with hruns
    · exact le_rfl
    · dsimp only
      apply getD_max?_le_of_forall
      intro x hx
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      obtain ⟨block, hb, d', hd', hx⟩ := hx
      rcases hx with rfl | rfl
      · refine ⟨_, ⟨block, hb, d', hd', Or.inl rfl⟩, ?_⟩
        exact Nat.add_le_add (ih _) (ih _)
      · refine ⟨_, ⟨block, hb, d', hd', Or.inr rfl⟩, ?_⟩
        exact Nat.add_le_add (ih _) (ih _)

theorem boundFuel_mono {f f' : ℕ} (h : f ≤ f') (σ : Context) : boundFuel f σ ≤ boundFuel f' σ := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (boundFuel_le_succ _ σ)

/-- With at least the child count plus one as fuel, the recursion is `bound`. -/
theorem bound_le_boundFuel (σ : Context) {f : ℕ} (hf : σ.childPositions.length + 1 ≤ f) :
    σ.bound ≤ boundFuel f σ :=
  boundFuel_mono hf σ

/-! ### Blocks -/

theorem mem_blocks {σ : Context} {block : List ℕ} (hb : block ∈ σ.blocks) :
    block.length < σ.childPositions.length ∧ block ≠ [] ∧ ∀ p ∈ block, p ∈ σ.childPositions := by
  unfold Context.blocks at hb
  simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map, decide_eq_true_eq] at hb
  obtain ⟨⟨i, hi, l, hl, rfl⟩, hlen⟩ := hb
  refine ⟨hlen, ?_, fun p hp => List.mem_of_mem_drop (List.mem_of_mem_take hp)⟩
  intro hnil
  rw [List.take_eq_nil_iff, List.drop_eq_nil_iff] at hnil
  omega

theorem length_filter_mem_le {ps block : List ℕ} (hps : ps.Nodup) :
    (ps.filter (· ∈ block)).length ≤ block.length :=
  ((hps.filter _).subperm fun p hp => by simpa using (List.mem_filter.1 hp).2).length_le

theorem length_filter_not_mem_lt {ps block : List ℕ} (hbne : block ≠ [])
    (hbsub : ∀ p ∈ block, p ∈ ps) : (ps.filter (· ∉ block)).length < ps.length := by
  have hsub := List.filter_sublist (p := fun p => decide (p ∉ block)) (l := ps)
  rcases lt_or_eq_of_le hsub.length_le with h | h
  · exact h
  · exfalso
    have heq := hsub.eq_of_length h
    rcases block with _ | ⟨b, rest⟩
    · exact hbne rfl
    · have hb : b ∈ ps.filter (fun p => decide (p ∉ b :: rest)) := by
        rw [heq]
        exact hbsub b (List.mem_cons_self ..)
      simp at hb

end Context
end Ctx

/-- Every interval cut of a context with at least two runs is dominated by its bound: the recursion takes the maximum over exactly these cuts, and the recursion is monotone in its fuel, so the parts (which have fewer child letters) are evaluated with enough fuel. This is the definitional half of additivity (experiment 0122).
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_bound_cut_le (σ : Ctx.Context) (hruns : 2 ≤ σ.numRuns) (block : List ℕ) (hb : block ∈ σ.blocks) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (σ.part block Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part block Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.lower d).bound ≤ σ.bound := by
  obtain ⟨hblen, hbne, hbsub⟩ := Ctx.Context.mem_blocks hb
  have hnodup := Ctx.Context.childPositions_nodup σ
  have hd' : d - 1 < σ.k - 2 := by omega
  have hdd : d - 1 + 1 = d := Nat.sub_add_cancel hd
  -- the parts have fewer child letters than `σ`
  have hfuelB : ∀ s m, (σ.part block s m).childPositions.length + 1 ≤ σ.childPositions.length := by
    intro s m
    rw [Ctx.Context.part_childPositions]
    have := Ctx.Context.length_filter_mem_le (block := block) hnodup
    omega
  have hfuelR : ∀ s m, (σ.part (σ.childPositions.filter (fun p => p ∉ block)) s m).childPositions.length + 1 ≤
      σ.childPositions.length := by
    intro s m
    rw [Ctx.Context.part_childPositions]
    have heq : σ.childPositions.filter (· ∈ σ.childPositions.filter (fun p => p ∉ block)) =
        σ.childPositions.filter (· ∉ block) := by
      apply List.filter_congr
      intro p hp
      simp [hp]
    rw [heq]
    have := Ctx.Context.length_filter_not_mem_lt hbne hbsub
    omega
  -- the two cut terms are members of the recursion's maximum
  have hcut : ∀ x, (x = Ctx.Context.boundFuel σ.childPositions.length (σ.part block Ctx.Side.lower (d - 1 + 1)) +
        Ctx.Context.boundFuel σ.childPositions.length
          (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.upper (σ.k - 1 - (d - 1 + 1))) ∨
      x = Ctx.Context.boundFuel σ.childPositions.length (σ.part block Ctx.Side.upper (σ.k - 1 - (d - 1 + 1))) +
        Ctx.Context.boundFuel σ.childPositions.length
          (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.lower (d - 1 + 1))) →
      x ≤ σ.bound := by
    intro x hx
    unfold Ctx.Context.bound
    rw [Ctx.Context.boundFuel.eq_2, if_neg (by omega)]
    dsimp only
    apply Ctx.le_getD_max?_of_mem
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨block, hb, d - 1, hd', hx⟩
  rw [hdd] at hcut
  constructor
  · exact (Nat.add_le_add (Ctx.Context.bound_le_boundFuel _ (hfuelB _ _))
      (Ctx.Context.bound_le_boundFuel _ (hfuelR _ _))).trans (hcut _ (Or.inl rfl))
  · exact (Nat.add_le_add (Ctx.Context.bound_le_boundFuel _ (hfuelB _ _))
      (Ctx.Context.bound_le_boundFuel _ (hfuelR _ _))).trans (hcut _ (Or.inr rfl))


end ErdosSzekeres
