import ESBlueprint.B.CtxPartPruningHistoryTransport
import ESBlueprint.B.CtxBoundMonoOfMarkerInclusion
import ESBlueprint.B.CtxAxisCapacityIntervalLowerBound

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Pruning a context part to a tracked group is dominated by taking the same part after pruning the source group, provided the group has a removed child. Preserves the sibling maximum and proves endpoint capacity, every-fuel and full-bound comparisons. The witness fixes the side of the new level; the proof uses indexed marker inclusion, since removed children outside the group contribute extra source markers. Supplies recursive cut projection for a proposed sum of bounds over groups constant on child runs; no sum theorem is asserted here.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_prune_part_projection_of_removed_witness (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (support keep : List ℕ) (v : Ctx.Side) (m q : ℕ)
  (hq : q ∈ σ.childPositions) (hqSupport : q ∈ support) (hqRemoved : q ∉ keep) :
  let prune := fun (ρ : Ctx.Context) => { ρ with
    word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
      | Ctx.Letter.child => if p ∈ support then Ctx.Letter.child
          else Ctx.Letter.ext (ρ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j s => Ctx.Letter.ext j s) }
  let A := prune (σ.part keep v m)
  let B := (prune σ).part keep v m
  (∀ p q, A.cupLimit p q ≤ B.cupLimit p q ∧ A.capLimit p q ≤ B.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel A ≤ Ctx.Context.boundFuel fuel B) ∧ A.bound ≤ B.bound := by
  classical
  let prune (ρ : Context) (support : List ℕ) : Context := { ρ with
    word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
      | Letter.child => if p ∈ support then Letter.child
          else Letter.ext (ρ.maxima.length + 1) Side.lower
      | Letter.ext j s => Letter.ext j s) }
  let T := prune σ support
  let A := prune (σ.part keep v m) support
  let B := T.part keep v m
  change (∀ p q, A.cupLimit p q ≤ B.cupLimit p q ∧ A.capLimit p q ≤ B.capLimit p q) ∧
    (∀ fuel, boundFuel fuel A ≤ boundFuel fuel B) ∧ A.bound ≤ B.bound
  have hPLen (ρ : Context) (ks : List ℕ) : (prune ρ ks).word.length = ρ.word.length := by
    simp [prune]
  have hPartPos (ρ : Context) (ks : List ℕ) (w : Side) (c : ℕ) :
      ∀ r j u, (ρ.part ks w c).letterAt r = Letter.ext j u → 1 ≤ j := by
    intro r j u hr
    have hrl : r < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part ks w c)
        (show (ρ.part ks w c).word.length ≤ r by rw [part_word_length]; omega)
      rw [hn] at hr
      cases hr
    cases he : ρ.letterAt r with
    | child =>
      rw [part_letterAt_of_child ρ ks w c hrl he] at hr
      split at hr
      · cases hr
      · cases hr; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ ks w c hrl he] at hr
      cases hr; omega
  obtain ⟨hTPos, hTChild, hTHist, hTLevels, hTExt, hTLimits, hTActive, hTFuel, hTBound⟩ :=
    ctx_part_pruning_history_transport σ hpositive support Side.lower 0
  obtain ⟨hAPos, hAChild, hAHist, hALevels, hAExt, hALimits, hAActive, hAFuel, hABound⟩ :=
    ctx_part_pruning_history_transport (σ.part keep v m) (hPartPos σ keep v m)
      support Side.lower 0
  change (∀ r j u, T.letterAt r = Letter.ext j u → 1 ≤ j) at hTPos
  change T.childPositions = σ.childPositions.filter (· ∈ support) at hTChild
  change (∀ j ∈ σ.levels, T.extPositions j = σ.extPositions j ∧ T.sideAt j = σ.sideAt j) at hTHist
  change A.childPositions = (σ.part keep v m).childPositions.filter (· ∈ support) at hAChild
  change (∀ j ∈ (σ.part keep v m).levels, A.extPositions j = (σ.part keep v m).extPositions j ∧
    A.sideAt j = (σ.part keep v m).sideAt j) at hAHist
  have hBPos := hPartPos T keep v m
  have hword : A.word.length = B.word.length := by
    simp only [A, B, T, hPLen, part_word_length]
  have hChildren : A.childPositions = B.childPositions := by
    change A.childPositions = (T.part keep v m).childPositions
    rw [hAChild, part_childPositions, part_childPositions, hTChild]
    simp only [List.filter_filter]
    apply List.filter_congr
    intro r _
    simp [Bool.and_comm]
  have hLetterChildren (r : ℕ) : A.letterAt r = Letter.child ↔ B.letterAt r = Letter.child := by
    by_cases hr : r < A.word.length
    · have hrB : r < B.word.length := by omega
      have hA : r ∈ A.childPositions ↔ A.letterAt r = Letter.child := by
        simp [childPositions, hr]
      have hB : r ∈ B.childPositions ↔ B.letterAt r = Letter.child := by
        simp [childPositions, hrB]
      rw [← hA, ← hB, hChildren]
    · have hrA : A.word.length ≤ r := by omega
      have hrB : B.word.length ≤ r := by omega
      rw [letterAt_of_length_le A hrA, letterAt_of_length_le B hrB]
  have hSourceOne : 1 ∈ (σ.part keep v m).levels := by simp [part_levels]
  have hRemovedSource : q ∈ (σ.part keep v m).extPositions 1 := by
    rw [part_extPositions_one hpositive]
    exact List.mem_filter.mpr ⟨hq, by simp [hqRemoved]⟩
  have hRemovedTarget : q ∈ T.childPositions := by
    rw [hTChild]
    exact List.mem_filter.mpr ⟨hq, by simp [hqSupport]⟩
  have hTargetNew : q ∈ B.extPositions 1 := by
    change q ∈ (T.part keep v m).extPositions 1
    rw [part_extPositions_one hTPos]
    exact List.mem_filter.mpr ⟨hRemovedTarget, by simp [hqRemoved]⟩
  have hSourceSide : (σ.part keep v m).sideAt 1 = v :=
    part_sideAt_one_of_mem hpositive keep v m hRemovedSource
  have hTargetSide : B.sideAt 1 = v :=
    part_sideAt_one_of_mem hTPos keep v m hTargetNew
  have hHistory (j : ℕ) (hj : j ∈ A.levels) :
      B.sideAt j = A.sideAt j ∧ B.extPositions j ⊆ A.extPositions j ∧
        B.maximumAt j ≤ A.maximumAt j := by
    have hjPart : j ∈ (σ.part keep v m).levels := hj
    have hAHistory := hAHist j hjPart
    have hMax : B.maximumAt j = A.maximumAt j := rfl
    refine ⟨?_, ?_, hMax.le⟩
    · change (T.part keep v m).sideAt j = A.sideAt j
      by_cases hj1 : j = 1
      · subst j
        exact hTargetSide.trans (hAHistory.2.trans hSourceSide).symm
      · have hjPos := one_le_of_mem_levels hjPart
        have hold : 1 ≤ j - 1 := by omega
        have hjEq : j = (j - 1) + 1 := by omega
        have hjOld : j - 1 ∈ σ.levels := by
          rw [part_levels] at hjPart
          rcases List.mem_cons.mp hjPart with h | h
          · exact False.elim (hj1 h)
          · obtain ⟨l, hl, he⟩ := List.mem_map.mp h
            have : l = j - 1 := by omega
            simpa only [this] using hl
        rw [hAHistory.2, hjEq, part_sideAt_succ T keep v m hold,
          part_sideAt_succ σ keep v m hold]
        exact (hTHist (j - 1) hjOld).2
    · change (T.part keep v m).extPositions j ⊆ A.extPositions j
      by_cases hj1 : j = 1
      · subst j
        rw [hAHistory.1, part_extPositions_one hTPos, part_extPositions_one hpositive]
        intro r hr
        obtain ⟨hrT, hrNot⟩ := List.mem_filter.mp hr
        rw [hTChild] at hrT
        exact List.mem_filter.mpr ⟨(List.mem_filter.mp hrT).1, hrNot⟩
      · have hjPos := one_le_of_mem_levels hjPart
        have hold : 1 ≤ j - 1 := by omega
        have hjEq : j = (j - 1) + 1 := by omega
        have hjOld : j - 1 ∈ σ.levels := by
          rw [part_levels] at hjPart
          rcases List.mem_cons.mp hjPart with h | h
          · exact False.elim (hj1 h)
          · obtain ⟨l, hl, he⟩ := List.mem_map.mp h
            have : l = j - 1 := by omega
            simpa only [this] using hl
        rw [hAHistory.1, hjEq, part_extPositions_succ T keep v m hold,
          part_extPositions_succ σ keep v m hold, (hTHist (j - 1) hjOld).1]
        exact fun _ hp => hp
  exact ctx_bound_mono_of_marker_inclusion A B hAPos hBPos le_rfl le_rfl rfl
    hword hLetterChildren rfl hHistory

end ErdosSzekeres
