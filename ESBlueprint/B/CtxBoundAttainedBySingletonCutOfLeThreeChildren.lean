import ESBlueprint.B.CtxBoundAttainedByEndCut

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Exact singleton-cut attainment for arbitrary raw contexts with at least two runs, k at least three and at most three children. Every proper interval block then has a singleton on one side; take a maximum recurrence witness, use fuel stability, and exchange the roles of complementary parts if necessary. No endpoint restriction or well-formedness assumption, and no use of the refuted general end-cut normal form. Supplies the small-arity base of the missing singleton reduction in the one-level-root run-contraction exchange route.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root -/
theorem ctx_bound_attained_by_singleton_cut_of_le_three_children (σ : Ctx.Context) (hk : 3 ≤ σ.k) (hruns : 2 ≤ σ.numRuns) (hlen : σ.childPositions.length ≤ 3) : ∃ p ∈ σ.childPositions, ∃ d, 1 ≤ d ∧ d ≤ σ.k - 2 ∧ (σ.bound = (σ.part [p] Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k - 1 - d)).bound ∨ σ.bound = (σ.part [p] Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d).bound) := by
  classical
  have hclass : ∀ block ∈ σ.blocks, ∃ p ∈ σ.childPositions,
      (∀ q ∈ σ.childPositions, q ∈ block ↔ q = p) ∨
      (∀ q ∈ σ.childPositions, q ∈ block ↔ q ≠ p) := by
    intro block hb
    have hn : 2 ≤ σ.childPositions.length := hruns.trans (numRuns_le_length σ)
    have hd := childPositions_nodup σ
    have hsize : σ.childPositions.length = 2 ∨ σ.childPositions.length = 3 := by omega
    rcases hsize with h2 | h3
    · obtain ⟨a, b, hps⟩ := List.length_eq_two.mp h2
      simp [hps] at hd
      simp only [blocks, hps] at hb
      change block ∈ [[a], [b]] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · refine ⟨a, ?_, Or.inl ?_⟩ <;> simp_all
      · refine ⟨b, ?_, Or.inl ?_⟩ <;> simp_all
    · obtain ⟨a, b, c, hps⟩ := List.length_eq_three.mp h3
      simp [hps] at hd
      have hba : b ≠ a := Ne.symm hd.1.1
      have hca : c ≠ a := Ne.symm hd.1.2
      have hcb : c ≠ b := Ne.symm hd.2
      simp only [blocks, hps] at hb
      change block ∈ [[a], [a, b], [b], [b, c], [c]] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · refine ⟨a, ?_, Or.inl ?_⟩ <;> simp_all
      · refine ⟨c, ?_, Or.inr ?_⟩ <;> simp_all
      · refine ⟨b, ?_, Or.inl ?_⟩ <;> simp_all
      · refine ⟨a, ?_, Or.inr ?_⟩ <;> simp_all
      · refine ⟨c, ?_, Or.inl ?_⟩ <;> simp_all
  have hlen2 : 2 ≤ σ.childPositions.length := hruns.trans (numRuns_le_length σ)
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, σ.childPositions.head? = some p₀ := by
    cases h : σ.childPositions with
    | nil => rw [h] at hlen2; simp at hlen2
    | cons x xs => exact ⟨x, rfl⟩
  have hb₀ : [p₀] ∈ σ.blocks := by
    unfold blocks
    simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map, decide_eq_true_eq]
    refine ⟨⟨0, by omega, 0, by omega, ?_⟩, by simp; omega⟩
    cases h : σ.childPositions with
    | nil => rw [h] at hp₀; simp at hp₀
    | cons x xs => rw [h] at hp₀; simp at hp₀; simp [hp₀]
  let cuts : List ℕ := σ.blocks.flatMap fun block =>
    (List.range (σ.k - 2)).flatMap fun d' =>
      [boundFuel σ.childPositions.length (σ.part block Side.lower (d' + 1)) +
        boundFuel σ.childPositions.length
          (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Side.upper (σ.k - 1 - (d' + 1))),
       boundFuel σ.childPositions.length (σ.part block Side.upper (σ.k - 1 - (d' + 1))) +
        boundFuel σ.childPositions.length
          (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Side.lower (d' + 1))]
  have hbound : σ.bound = (cuts.max?).getD 0 := by
    simp only [bound, boundFuel.eq_2, if_neg (by omega : ¬ σ.numRuns ≤ 1)]
    rfl
  have hne : cuts ≠ [] := by
    dsimp only [cuts]
    refine List.ne_nil_of_mem (List.mem_flatMap.2
      ⟨[p₀], hb₀, List.mem_flatMap.2 ⟨0, ?_, List.mem_cons_self ..⟩⟩)
    exact List.mem_range.2 (by omega)
  obtain ⟨value, hval, hmax⟩ := exists_mem_eq_getD_max? cuts hne
  have heq : σ.bound = value := hbound.trans hmax
  dsimp only [cuts] at hval
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hval
  obtain ⟨block, hb, d', hd', hval⟩ := hval
  have hfB : ∀ s m, (σ.part block s m).childPositions.length + 1 ≤ σ.childPositions.length :=
    fun s m => part_childPositions_length_lt_of_mem_blocks hb s m
  have hfR : ∀ s m, (σ.part (σ.childPositions.filter (fun p => p ∉ block)) s m).childPositions.length + 1 ≤
      σ.childPositions.length := fun s m => part_rest_childPositions_length_lt_of_mem_blocks hb s m
  have hdk : d' + 1 ≤ σ.k - 2 := by omega
  have hv : value = (σ.part block Side.lower (d' + 1)).bound +
      (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Side.upper (σ.k - 1 - (d' + 1))).bound ∨
      value = (σ.part block Side.upper (σ.k - 1 - (d' + 1))).bound +
      (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Side.lower (d' + 1)).bound := by
    rcases hval with rfl | rfl
    · left
      rw [boundFuel_eq_bound _ (hfB _ _), boundFuel_eq_bound _ (hfR _ _)]
    · right
      rw [boundFuel_eq_bound _ (hfB _ _), boundFuel_eq_bound _ (hfR _ _)]
  obtain ⟨p, hp, hsame | hcompl⟩ := hclass block hb
  · have h1 : ∀ s m, σ.part block s m = σ.part [p] s m := fun s m =>
      part_congr σ s m fun q hq => by simp [hsame q hq]
    have h2 : ∀ s m, σ.part (σ.childPositions.filter (fun q => q ∉ block)) s m =
        σ.part (σ.childPositions.filter (fun q => q ≠ p)) s m := fun s m =>
      part_congr σ s m fun q hq => by simp [List.mem_filter, hq, hsame q hq]
    refine ⟨p, hp, d' + 1, by omega, hdk, ?_⟩
    rcases hv with h | h
    · left
      rw [h1, h2] at h
      exact heq.trans h
    · right
      rw [h1, h2] at h
      exact heq.trans h
  · have h1 : ∀ s m, σ.part block s m =
        σ.part (σ.childPositions.filter (fun q => q ≠ p)) s m := fun s m =>
      part_congr σ s m fun q hq => by simp [List.mem_filter, hq, hcompl q hq]
    have h2 : ∀ s m, σ.part (σ.childPositions.filter (fun q => q ∉ block)) s m =
        σ.part [p] s m := fun s m =>
      part_congr σ s m fun q hq => by simp [List.mem_filter, hq, hcompl q hq]
    refine ⟨p, hp, d' + 1, by omega, hdk, ?_⟩
    rcases hv with h | h
    · right
      rw [h1, h2] at h
      exact heq.trans (h.trans (Nat.add_comm _ _))
    · left
      rw [h1, h2] at h
      exact heq.trans (h.trans (Nat.add_comm _ _))


end ErdosSzekeres
