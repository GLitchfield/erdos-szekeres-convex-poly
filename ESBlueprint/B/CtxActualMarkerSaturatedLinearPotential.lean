import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxEraseLevelBoundMono
import ESBlueprint.B.CtxSingleLevelSaturatedLinearBound

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Extend the saturated linear bound 2*k-4 to every positive context with chosen global at most four, opposite global at most k, and an actual chosen marker. Arbitrary indexed levels other than the retained marker are erased using the checked bound monotonicity theorem; physical external barriers remain. The depth induction ends at the checked one-level saturated theorem. Positive physical labels, distinct axes, chosen global at most four, opposite global at most k and k at least four. At least one actual indexed chosen marker is required. Arbitrary history on both axes, repeated occurrences, maxima, inactive children and unindexed physical barriers are allowed. No one-level, youngest-marker, empty-history, recursive-potential or cut-bound premise.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_actual_marker_saturated_linear_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hk : 4 ≤ σ.k) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2*σ.k-4) ∧ σ.bound ≤ 2*σ.k-4 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
  let letter (D L : ℕ) : Letter → Letter := fun x => match x with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext (idx D L j) v
  let norm (ρ : Context) (L : ℕ) : Context :=
    { ρ with word := ρ.word.map (letter ρ.maxima.length L), maxima := ρ.maxima.eraseIdx (L-1) }
  let up (L j : ℕ) := if j < L then j else j+1
  have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
    simp only [levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro hj; exact ⟨j-1, by omega, by omega⟩
  have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
    unfold levels
    exact List.pairwise_lt_range.map (fun x => x+1) (fun a b h => Nat.add_lt_add_right h 1)
  have hLen (ρ : Context) (L : ℕ) : (norm ρ L).word.length = ρ.word.length := by
    simp only [norm, List.length_map]
  have hLetter (ρ : Context) (L p : ℕ) :
      (norm ρ L).letterAt p = letter ρ.maxima.length L (ρ.letterAt p) := by
    simp only [norm, letterAt, List.getElem?_map]
    cases ρ.word[p]? <;> rfl
  have hIsChild (ρ : Context) (L p : ℕ) :
      (norm ρ L).letterAt p = Letter.child ↔ ρ.letterAt p = Letter.child := by
    rw [hLetter]
    cases ρ.letterAt p <;> simp [letter]
  have hChild (ρ : Context) (L : ℕ) : (norm ρ L).childPositions = ρ.childPositions := by
    simp only [childPositions, hLen, hIsChild]
  have hRuns (ρ : Context) (L : ℕ) : (norm ρ L).numRuns = ρ.numRuns := by
    simp only [numRuns, hLen, ne_eq, hIsChild]
  have hBlocks (ρ : Context) (L : ℕ) : (norm ρ L).blocks = ρ.blocks := by
    simp only [blocks, hChild]
  have hK (ρ : Context) (L : ℕ) : (norm ρ L).k = ρ.k := rfl
  have hDepth (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      (norm ρ L).maxima.length = ρ.maxima.length-1 := by
    have hh := (hLevelMem ρ L).mp hL
    exact List.length_eraseIdx_of_lt (by omega)
  have hLive (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) :
      1 ≤ j ∧ j < ρ.maxima.length ∧ up L j ∈ ρ.levels := by
    have hh := (hLevelMem ρ L).mp hL
    have hj' := (hLevelMem (norm ρ L) j).mp hj
    rw [hDepth ρ L hL] at hj'
    refine ⟨hj'.1, by omega, ?_⟩
    apply (hLevelMem ρ _).mpr
    dsimp [up]
    split_ifs <;> omega
  have hIndex (D L i j : ℕ) (hL : 1 ≤ L) (hLD : L ≤ D)
      (hj : 1 ≤ j) (hjD : j < D) : idx D L i = j ↔ i = up L j := by
    dsimp [idx, up]
    split_ifs <;> omega
  have hExt (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) :
      (norm ρ L).extPositions j = ρ.extPositions (up L j) := by
    have hLj := (hLevelMem ρ L).mp hL
    have hj' := hLive ρ L j hL hj
    simp only [extPositions, hLen, hLetter]
    apply List.filter_congr
    intro p _
    cases ρ.letterAt p with
    | child => rfl
    | ext i v => simp only [letter, hIndex _ _ i j hLj.1 hLj.2 hj'.1 hj'.2.1]
  have hSide (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) : (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
    simp only [sideAt, hExt ρ L j hL hj]
    cases hh : (ρ.extPositions (up L j)).head? with
    | none => rfl
    | some p =>
      dsimp only
      rw [hLetter]
      cases ρ.letterAt p <;> rfl
  have hPositive (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) :
      ∀ p j v, (norm ρ L).letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hj
    rw [hLetter] at hj
    have hLB := (hLevelMem ρ L).mp hL
    cases he : ρ.letterAt p with
    | child => simp only [he, letter] at hj; cases hj
    | ext i z =>
      rw [he] at hj
      have hi := hPos p i z he
      have hnew : 1 ≤ idx ρ.maxima.length L i := by
        dsimp only [idx]
        split_ifs <;> omega
      change Letter.ext (idx ρ.maxima.length L i) z = Letter.ext j v at hj
      cases hj
      exact hnew
  have hMain : ∀ d (ρ : Context), ρ.maxima.length=d →
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      ∀ N x, N ∈ ρ.levels → ρ.sideAt N=s → x ∈ ρ.extPositions N →
      G ρ s ≤ 4 → G ρ t ≤ ρ.k → 4 ≤ ρ.k → ρ.bound ≤ 2*ρ.k-4 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro ρ hd hPos N x hN hNs hx hGs hGt hk
      have hNB := (hLevelMem ρ N).mp hN
      by_cases hOne : ρ.maxima.length=1
      · have hN1 : N=1 := by omega
        subst N
        exact (ctx_single_level_saturated_linear_bound ρ hPos hOne s t hne x hNs hx hGs hGt hk).2
      let L := if N=1 then 2 else 1
      have hLB : 1 ≤ L ∧ L ≤ ρ.maxima.length ∧ L≠N := by
        dsimp only [L]
        split_ifs <;> omega
      have hL : L ∈ ρ.levels := (hLevelMem ρ L).mpr ⟨hLB.1, hLB.2.1⟩
      let N' := if N<L then N else N-1
      have hN' : N' ∈ (norm ρ L).levels := by
        apply (hLevelMem (norm ρ L) N').mpr
        rw [hDepth ρ L hL]
        dsimp only [N']
        split_ifs <;> omega
      have hRecover : up L N'=N := by
        dsimp only [up, N']
        split_ifs <;> omega
      have hNs' : (norm ρ L).sideAt N'=s := by
        rw [hSide ρ L N' hL hN', hRecover]
        exact hNs
      have hx' : x ∈ (norm ρ L).extPositions N' := by
        rw [hExt ρ L N' hL hN', hRecover]
        exact hx
      have hD : (norm ρ L).maxima.length<d := by rw [hDepth ρ L hL]; omega
      have hBound := ih (norm ρ L).maxima.length hD (norm ρ L) rfl
        (hPositive ρ L hL hPos) N' x hN' hNs' hx' hGs hGt hk
      have hMono : ρ.bound ≤ (norm ρ L).bound := (ctx_erase_level_bound_mono ρ L hL).2.2
      exact hMono.trans hBound
  have hBound := hMain σ.maxima.length σ rfl hpositive N x hN hNs hx hglobal hopposite hk
  have hFuelFull (fuel : ℕ) : boundFuel fuel σ ≤ σ.bound := by
    by_cases hf : σ.childPositions.length+1 ≤ fuel
    · exact (boundFuel_eq_bound σ hf).le
    · exact boundFuel_mono (by omega : fuel ≤ σ.childPositions.length+1) σ
  exact ⟨fun fuel => (hFuelFull fuel).trans hBound, hBound⟩


end ErdosSzekeres
