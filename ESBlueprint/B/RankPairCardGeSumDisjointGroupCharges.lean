import ESBlueprint.B.CtxBoundLeSumRunGroupPrunings

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- For finitely many pairwise disjoint natural-rank groups, a pair set containing every rank diagonal and the successor pair starting at every nonmaximal group rank has cardinality at least the sum of twice each group size minus one. Empty groups contribute zero. Supplies an explicit disjoint reservation matching the doubled-rank bound of each original-history pruned context.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem rank_pair_card_ge_sum_disjoint_group_charges (colors : Finset ℕ) (ranks : ℕ → Finset ℕ) (pairs : Finset (ℕ × ℕ))
  (hdisjoint : ∀ c ∈ colors, ∀ d ∈ colors, c ≠ d → Disjoint (ranks c) (ranks d))
  (hdiag : ∀ c ∈ colors, ∀ a ∈ ranks c, (a, a) ∈ pairs)
  (hedge : ∀ c ∈ colors, ∀ a ∈ ranks c, (∃ b ∈ ranks c, a < b) → (a, a + 1) ∈ pairs) :
  colors.sum (fun c => 2 * (ranks c).card - 1) ≤ pairs.card := by
  classical
  let top (c : ℕ) := if h : (ranks c).Nonempty then (ranks c).max' h else 0
  let smaller (c : ℕ) := (ranks c).erase (top c)
  let diag (c : ℕ) := (ranks c).image (fun a => (a, a))
  let edges (c : ℕ) := (smaller c).image (fun a => (a, a + 1))
  let charge (c : ℕ) := diag c ∪ edges c
  have hDiagInj : Function.Injective (fun a : ℕ => (a, a)) := by
    intro a b h
    exact congrArg Prod.fst h
  have hNextInj : Function.Injective (fun a : ℕ => (a, a + 1)) := by
    intro a b h
    exact congrArg Prod.fst h
  have hSeparated (c : ℕ) : Disjoint (diag c) (edges c) := by
    apply Finset.disjoint_left.mpr
    intro z hz hd
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hz
    obtain ⟨b, hb, hf⟩ := Finset.mem_image.mp hd
    have h1 := congrArg Prod.fst (he.trans hf.symm)
    have h2 := congrArg Prod.snd (he.trans hf.symm)
    simp only [Prod.fst, Prod.snd] at h1 h2
    omega
  have hCard (c : ℕ) : (charge c).card = 2 * (ranks c).card - 1 := by
    by_cases hn : (ranks c).Nonempty
    · have ht : top c ∈ ranks c := by
        simpa only [top, dif_pos hn] using (ranks c).max'_mem hn
      change (diag c ∪ edges c).card = _
      rw [Finset.card_union_of_disjoint (hSeparated c)]
      simp only [diag, edges, Finset.card_image_of_injective _ hDiagInj,
        Finset.card_image_of_injective _ hNextInj, smaller, Finset.card_erase_of_mem ht]
      have hc : 0 < (ranks c).card := Finset.card_pos.mpr hn
      omega
    · have he := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [charge, diag, edges, smaller, he]
  have hFirst (c : ℕ) (z : ℕ × ℕ) (hz : z ∈ charge c) : z.1 ∈ ranks c := by
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact ha
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_of_mem_erase ha
  have hPairwise : (↑colors : Set ℕ).PairwiseDisjoint charge := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro z hz hd'
    exact Finset.disjoint_left.mp (hdisjoint c hc d hd hcd) (hFirst c z hz) (hFirst d z hd')
  have hSubset : colors.biUnion charge ⊆ pairs := by
    intro z hz
    obtain ⟨c, hc, hz⟩ := Finset.mem_biUnion.mp hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact hdiag c hc a ha
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      have har : a ∈ ranks c := Finset.mem_of_mem_erase ha
      have hn : (ranks c).Nonempty := ⟨a, har⟩
      have ht : top c = (ranks c).max' hn := by simp only [top, dif_pos hn]
      have ham : a ∈ (ranks c).erase ((ranks c).max' hn) := by simpa only [smaller, ht] using ha
      exact hedge c hc a har ⟨(ranks c).max' hn, (ranks c).max'_mem hn,
        (ranks c).lt_max'_of_mem_erase_max' hn ham⟩
  calc
    colors.sum (fun c => 2 * (ranks c).card - 1) = colors.sum (fun c => (charge c).card) :=
      Finset.sum_congr rfl (fun c _ => (hCard c).symm)
    _ = (colors.biUnion charge).card := (Finset.card_biUnion hPairwise).symm
    _ ≤ pairs.card := Finset.card_le_card hSubset

end ErdosSzekeres
