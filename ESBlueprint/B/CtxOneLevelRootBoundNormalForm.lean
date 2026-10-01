import ErdosSzekeres.DecomposableContextLemmas
import ESBlueprint.B.CtxBoundZeroOfUnitGlobalAxis
import ESBlueprint.B.CtxBoundLeIffAllIntervalCutsLe

namespace ErdosSzekeres

/-- ROOT-NF: a one-level root over child and ext 1 side has the bound of a word retaining the presence of both end markers, with one child per run and run count clamped at three on a global axis two, and at two otherwise. The axis-two exception preserves the diagnostic two-to-three-run drop. This alternate route implies C1r independently of N_root and X; no normal-form equality is assumed in its proof.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root
@falsifier ctx_one_level_root_normal_form.py
@measure number of child positions -/
theorem ctx_one_level_root_bound_normal_form (a u k m : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k)
    (hu : 1 ≤ u) (huk : u ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k - 2)
    (side : Ctx.Side) (word : List Ctx.Letter)
    (hletters : ∀ x ∈ word, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) :
    let σ : Ctx.Context := {a := a, u := u, k := k, word := word, maxima := [m]}
    let r := min σ.numRuns (if a = 2 ∨ u = 2 then 3 else 2)
    let marker := Ctx.Letter.ext 1 side
    let normalWord :=
      (if word.head? = some marker then [marker] else []) ++
      (List.replicate r Ctx.Letter.child).intersperse marker ++
      (if word.getLast? = some marker then [marker] else [])
    σ.bound = ({σ with word := normalWord} : Ctx.Context).bound := by
  classical
  let P (n : ℕ) : Prop :=
    ∀ (a u k m : ℕ), 3 ≤ k → 1 ≤ a → a ≤ k → 1 ≤ u → u ≤ k →
      1 ≤ m → m ≤ k - 2 → ∀ (side : Ctx.Side) (word : List Ctx.Letter),
      (∀ x ∈ word, x = Ctx.Letter.child ∨ x = Ctx.Letter.ext 1 side) →
      ({a := a, u := u, k := k, word := word, maxima := [m]} : Ctx.Context).childPositions.length = n →
      let σ : Ctx.Context := {a := a, u := u, k := k, word := word, maxima := [m]}
      let r := min σ.numRuns (if a = 2 ∨ u = 2 then 3 else 2)
      let marker := Ctx.Letter.ext 1 side
      let normalWord :=
        (if word.head? = some marker then [marker] else []) ++
        (List.replicate r Ctx.Letter.child).intersperse marker ++
        (if word.getLast? = some marker then [marker] else [])
      σ.bound = ({σ with word := normalWord} : Ctx.Context).bound
  have hemptyBound (ρ : Ctx.Context) (hρ : ρ.childPositions = []) : ρ.bound = 0 := by
    have hr : ρ.numRuns ≤ 1 := by
      have h := Ctx.numRuns_le_length ρ
      rw [hρ] at h
      simp only [List.length_nil] at h
      omega
    simp only [Ctx.Context.bound, hρ, List.length_nil, Nat.zero_add]
    rw [Ctx.Context.boundFuel.eq_2, if_pos hr]
    simp [Ctx.Context.base, hρ]
  have hmain : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [P]
      intro a u k m hk ha hak hu huk hm hmk side word hletters hcount
      let σ : Ctx.Context := {a := a, u := u, k := k, word := word, maxima := [m]}
      let marker := Ctx.Letter.ext 1 side
      let normalWord :=
        (if word.head? = some marker then [marker] else []) ++
        (List.replicate (min σ.numRuns (if a = 2 ∨ u = 2 then 3 else 2))
          Ctx.Letter.child).intersperse marker ++
        (if word.getLast? = some marker then [marker] else [])
      let τ : Ctx.Context := {σ with word := normalWord}
      change σ.bound = τ.bound
      by_cases hzero : a ≤ 1 ∨ u ≤ 1
      · exact (ctx_bound_zero_of_unit_global_axis σ hzero).2.trans
          (ctx_bound_zero_of_unit_global_axis τ hzero).2.symm
      by_cases hempty : σ.childPositions = []
      · have hruns : σ.numRuns = 0 := by
          have h := Ctx.numRuns_le_length σ
          rw [hempty] at h
          simp only [List.length_nil] at h
          omega
        have hτ : τ.childPositions = [] := by
          by_cases hleft : word.head? = some marker <;>
            by_cases hright : word.getLast? = some marker <;>
            simp [τ, normalWord, hruns, hleft, hright,
              Ctx.Context.childPositions, Ctx.Context.letterAt, marker] <;>
            intro p hp <;> interval_cases p <;> simp
        rw [hemptyBound σ hempty, hemptyBound τ hτ]
      have hsourceCount : σ.childPositions.length = n := hcount
      apply Nat.le_antisymm
      · by_cases hruns : 2 ≤ σ.numRuns
        · apply (ctx_bound_le_iff_all_interval_cuts_le σ hruns τ.bound).mpr
          intro block hb d hd hdk
          have hblockSmall (s : Ctx.Side) (c : ℕ) :
              (σ.part block s c).childPositions.length < n := by
            have h := Ctx.Context.part_childPositions_length_lt_of_mem_blocks hb s c
            rw [hsourceCount] at h
            omega
          have hrestSmall (s : Ctx.Side) (c : ℕ) :
              (σ.part (σ.childPositions.filter (fun p ↦ p ∉ block)) s c).childPositions.length < n := by
            have h := Ctx.Context.part_rest_childPositions_length_lt_of_mem_blocks hb s c
            rw [hsourceCount] at h
            omega
          have hNFblock := ih _ (hblockSmall Ctx.Side.lower d)
          have hNFrest := ih _ (hrestSmall Ctx.Side.upper (σ.k - 1 - d))
          -- These are full smaller ROOT-NF hypotheses P j, not assertions about
          -- the two-level parts themselves. A sound transport is still required.
          constructor
          · trace_state
            sorry
          · trace_state
            sorry
        · have hsingle : σ.numRuns ≤ 1 := by omega
          -- Single-run base equality is separate from the multi-run upper step.
          trace_state
          sorry
      · -- Construct cuts witnessing the lower inequality, allowing inner run ends.
        trace_state
        sorry
  exact hmain _ a u k m hk ha hak hu huk hm hmk side word hletters rfl

end ErdosSzekeres
