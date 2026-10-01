import ESBlueprint.B.CtxPartBoundLeTwoOfNearSaturatedOldAndFreshMaxima
import ESBlueprint.B.CtxPositivePartForcesUnsaturatedSameSideHistory

namespace ErdosSzekeres

/-- At k=4 a legal nonempty proper child partition with paired value greater than two, in either orientation, forces every declared source sibling maximum to equal one. Positive actual external labels and positive declared source maxima suffice for arbitrary raw contexts, keep lists, histories and global widths. Near-saturated old and fresh maxima bound each proper part by two, so both opposite-axis parts must be positive; their necessary unsaturated-history ceilings then force every source maximum to one. A necessary reduction of the critical value-three maximal-segment exchange case, without a flip lower witness or a sufficiency converse.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_bound_le_two_of_near_saturated_old_and_fresh_maxima, ErdosSzekeres.ctx_positive_part_forces_unsaturated_same_side_history
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_k_four_critical_partition_forces_unit_sibling_maxima (σ : Ctx.Context)
  (hpositive : ∀ x j v, σ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j)
  (hk : σ.k = 4) (hmaxima : ∀ N ∈ σ.levels, 1 ≤ σ.maximumAt N)
  (keep : List ℕ) (p r : ℕ)
  (hp : p ∈ σ.childPositions) (hkept : p ∈ keep)
  (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep)
  (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) :
  (2 < (σ.part keep Ctx.Side.lower d).bound +
    (σ.part (σ.childPositions.filter (· ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound →
    ∀ N ∈ σ.levels, σ.maximumAt N = 1) ∧
  (2 < (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound +
    (σ.part (σ.childPositions.filter (· ∉ keep)) Ctx.Side.lower d).bound →
    ∀ N ∈ σ.levels, σ.maximumAt N = 1) := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  have hpnotrest : p ∉ rest := by simp [rest, hkept]
  have hkThree : 3 ≤ σ.k := by omega
  have hdNear : σ.k - 3 ≤ d := by omega
  have hoNear : σ.k - 3 ≤ σ.k - 1 - d := by omega
  have hUnit (K L : List ℕ) (x y : ℕ)
      (hx : x ∈ σ.childPositions) (hxremoved : x ∉ K)
      (hy : y ∈ σ.childPositions) (hyremoved : y ∉ L)
      (m n : ℕ) (hm : σ.k - 3 ≤ m) (hn : σ.k - 3 ≤ n)
      (hcritical : 2 < (σ.part K .lower m).bound + (σ.part L .upper n).bound) :
      ∀ N ∈ σ.levels, σ.maximumAt N = 1 := by
    intro N hN
    have hPositive := hmaxima N hN
    have hNear : σ.k - 3 ≤ σ.maximumAt N := by omega
    have hLower := (ctx_part_bound_le_two_of_near_saturated_old_and_fresh_maxima
      σ hpositive N hN hNear K .lower m x hm hx hxremoved).2
    have hUpper := (ctx_part_bound_le_two_of_near_saturated_old_and_fresh_maxima
      σ hpositive N hN hNear L .upper n y hn hy hyremoved).2
    have hLowerPositive : 0 < (σ.part K .lower m).bound := by omega
    have hUpperPositive : 0 < (σ.part L .upper n).bound := by omega
    cases hs : σ.sideAt N
    · have hOn : N ∈ σ.levelsOn .lower 0 :=
        List.mem_filter.mpr ⟨hN, by simp [hs]⟩
      have hCeiling := ctx_positive_part_forces_unsaturated_same_side_history
        σ hpositive hkThree K .lower m x hx hxremoved hLowerPositive N hOn
      omega
    · have hOn : N ∈ σ.levelsOn .upper 0 :=
        List.mem_filter.mpr ⟨hN, by simp [hs]⟩
      have hCeiling := ctx_positive_part_forces_unsaturated_same_side_history
        σ hpositive hkThree L .upper n y hy hyremoved hUpperPositive N hOn
      omega
  change (2 < (σ.part keep Ctx.Side.lower d).bound +
      (σ.part rest Ctx.Side.upper (σ.k - 1 - d)).bound →
      ∀ N ∈ σ.levels, σ.maximumAt N = 1) ∧
    (2 < (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound +
      (σ.part rest Ctx.Side.lower d).bound →
      ∀ N ∈ σ.levels, σ.maximumAt N = 1)
  constructor
  · intro hcritical
    exact hUnit keep rest r p hr hremoved hp hpnotrest
      d (σ.k - 1 - d) hdNear hoNear hcritical
  · intro hcritical
    have hcritical' : 2 < (σ.part rest .lower d).bound +
        (σ.part keep .upper (σ.k - 1 - d)).bound := by omega
    exact hUnit rest keep p r hp hpnotrest hr hremoved
      d (σ.k - 1 - d) hdNear hoNear hcritical'

end ErdosSzekeres
