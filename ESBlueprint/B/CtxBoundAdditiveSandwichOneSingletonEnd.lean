import ESBlueprint.B.CtxBoundAdditiveSandwichSingletonEnds
import ESBlueprint.B.CtxBoundAdditiveSingleRun

namespace ErdosSzekeres

/-- Sandwich additivity for a contiguous child run split into three nonempty blocks, with at least one outer block a singleton. Includes both orientations, reflection, arbitrary middle and other outer block lengths, and every admissible coupling. The statement is the approved intermediate goal beyond the proved singleton-ended case; it remains open until the unbounded outer-run comparison is established.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_bound_additive_sandwich_one_singleton_end (σ : Ctx.Context) (hwf : σ.WellFormed)
  (b l m r : ℕ) (hpos : σ.childPositions = List.range' b (l + m + r))
  (hl : 0 < l) (hm : 0 < m) (hr : 0 < r) (hend : l = 1 ∨ r = 1)
  (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) :
  (σ.part (List.range' b l ++ List.range' (b + l + m) r) Ctx.Side.lower d).bound +
      (σ.part (List.range' (b + l) m) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧
  (σ.part (List.range' b l ++ List.range' (b + l + m) r) Ctx.Side.upper (σ.k - 1 - d)).bound +
      (σ.part (List.range' (b + l) m) Ctx.Side.lower d).bound ≤ σ.bound := by
  classical
  have hruns : σ.numRuns ≤ 1 := by
    let starts := (List.range σ.word.length).filter fun p ↦
      σ.letterAt p = Ctx.Letter.child ∧ (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child)
    have hsubset : starts.toFinset ⊆ ({b} : Finset ℕ) := by
      intro p hp
      have hstart : p < σ.word.length ∧ σ.letterAt p = Ctx.Letter.child ∧
          (p = 0 ∨ σ.letterAt (p - 1) ≠ Ctx.Letter.child) := by simpa [starts] using hp
      have hp' : b ≤ p ∧ p < b + (l + m + r) := by
        have hpchild : p ∈ σ.childPositions := by simp [Ctx.Context.childPositions, hstart]
        simpa [hpos, List.mem_range'_1] using hpchild
      simp only [Finset.mem_singleton]
      by_contra hpb
      have hprev : p - 1 ∈ σ.childPositions := by rw [hpos, List.mem_range'_1]; omega
      have hprev' : σ.letterAt (p - 1) = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hprev).2
      rcases hstart.2.2 with hz | hnot
      · omega
      · exact hnot hprev'
    calc
      σ.numRuns = starts.toFinset.card :=
        (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
      _ ≤ ({b} : Finset ℕ).card := Finset.card_le_card hsubset
      _ = 1 := by simp
  let keep := List.range' b l ++ List.range' (b + l + m) r
  have hkeep : ∀ p ∈ keep, p ∈ σ.childPositions := by
    intro p hp
    simp only [keep, List.mem_append, List.mem_range'_1] at hp
    rw [hpos, List.mem_range'_1]
    omega
  have hne : keep ≠ [] := by
    intro heq
    have hlen := congrArg List.length heq
    simp only [keep, List.length_append, List.length_range', List.length_nil] at hlen
    omega
  have hall : keep.length < σ.childPositions.length := by
    simp only [keep, hpos, List.length_append, List.length_range']
    omega
  have hcomplement : σ.childPositions.filter (fun p ↦ p ∉ keep) =
      List.range' (b + l) m := by
    rw [hpos]
    apply ((List.pairwise_lt_range' 1 (by omega)).filter _).eq_of_mem_iff
      (List.pairwise_lt_range' 1 (by omega))
    intro p
    simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq, keep, List.mem_append]
    omega
  simpa only [hcomplement] using
    ctx_bound_additive_single_run σ hwf hruns keep hkeep hne hall d hd hdk

end ErdosSzekeres
