import ESBlueprint.B.CtxBareTwoMarkerSharpPotential
import ESBlueprint.B.CtxEraseLevelBoundMono
import ESBlueprint.B.CtxSingleLevelOccurrencePruneBoundMono
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Prove the sharp triangular-linear two-marker potential with arbitrary history on both axes. Erase every indexed level except the selected actual pair using the checked arbitrary-level bound monotonicity theorem. At depth two, prune repeated occurrences while retaining physical barriers and apply the bare sharp potential. No history-empty or occurrence-count premise remains. Positive physical labels, distinct axes, chosen global at most five and opposite width at least two. Two distinct actual indexed chosen levels are required; arbitrary additional chosen and opposite history, repeated occurrences, maxima, inactive children and unindexed barriers are allowed. No empty-history, youngest-marker, occurrence-count, recursive-potential or cut-bound premise.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_actual_marker_sharp_potential_arbitrary_history (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (w + 1).choose 2 + w - 1) ∧
    σ.bound ≤ (w + 1).choose 2 + w - 1 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let P (w : ℕ) := (w+1).choose 2+w-1
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
  have hBase (σ : Context)
      (hpositive : ∀ p j v, σ.letterAt p = Letter.ext j v → 1 ≤ j)
      (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N<M)
      (hNs : σ.sideAt N=s) (hMs : σ.sideAt M=s)
      (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
      (hglobal : G σ s ≤ 5) (hwidth : 2 ≤ G σ t-1)
      (hDepth : σ.maxima.length=2) : σ.bound ≤ P (G σ t-1) := by
    have hNB := (hLevelMem σ N).mp hN
    have hMB := (hLevelMem σ M).mp hM
    have hN1 : N=1 := by omega
    have hM2 : M=2 := by omega
    have hlevels : σ.levels=[N,M] := by
      rw [hN1,hM2]
      unfold levels
      rw [hDepth]
      rfl
    have hchosen : ∀ j ∈ σ.levelsOn s 0, j≠N → j≠M → σ.extPositions j=[] := by
      intro j hj hjN hjM
      have hh : j=N ∨ j=M := by simpa [hlevels] using (List.mem_filter.mp hj).1
      omega
    let prune (ρ : Context) (L z : ℕ) : Context := {ρ with
      word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
        | Letter.child => Letter.child
        | Letter.ext j v => if j = L then
            if p ∈ [z] then Letter.ext L (ρ.sideAt L)
            else Letter.ext (ρ.maxima.length+1) v
          else Letter.ext j v) }
    let τ := prune σ N x
    let ν := prune τ M y
    have hFirst := ctx_single_level_occurrence_prune_bound_mono σ hpositive N hN [x] x hx (by simp)
    have hτPos : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := hFirst.1
    have hτHistory : ∀ j ∈ σ.levels, τ.sideAt j = σ.sideAt j ∧ τ.maximumAt j = σ.maximumAt j ∧
        τ.extPositions j = if j = N then (σ.extPositions j).filter (· ∈ [x]) else σ.extPositions j :=
      hFirst.2.2.1
    have hMNne : M ≠ N := by omega
    have hNMne : N ≠ M := by omega
    have hExtτM : τ.extPositions M = σ.extPositions M := by
      simpa only [if_neg hMNne] using (hτHistory M hM).2.2
    have hyτ : y ∈ τ.extPositions M := by rw [hExtτM]; exact hy
    have hSecond := ctx_single_level_occurrence_prune_bound_mono τ hτPos M hM [y] y hyτ (by simp)
    have hνPos : ∀ p j v, ν.letterAt p = Letter.ext j v → 1 ≤ j := hSecond.1
    have hνHistory : ∀ j ∈ σ.levels, ν.sideAt j = τ.sideAt j ∧ ν.maximumAt j = τ.maximumAt j ∧
        ν.extPositions j = if j = M then (τ.extPositions j).filter (· ∈ [y]) else τ.extPositions j :=
      hSecond.2.2.1
    have hνSide (j : ℕ) (hj : j ∈ σ.levels) : ν.sideAt j = σ.sideAt j :=
      (hνHistory j hj).1.trans (hτHistory j hj).1
    have hνExt (j : ℕ) (hj : j ∈ σ.levels) : ν.extPositions j =
        if j = M then (σ.extPositions j).filter (· ∈ [y])
        else if j = N then (σ.extPositions j).filter (· ∈ [x]) else σ.extPositions j := by
      rw [(hνHistory j hj).2.2, (hτHistory j hj).2.2]
      by_cases hjM : j = M
      · subst j
        simp only [if_pos rfl, if_neg hMNne]
      · simp only [if_neg hjM]
    have hxν : x ∈ ν.extPositions N := by
      rw [hνExt N hN]
      simp [hNMne, hx]
    have hyν : y ∈ ν.extPositions M := by
      rw [hνExt M hM]
      simp [hy]
    have hνChosen : ∀ j ∈ ν.levelsOn s 0, ∀ p ∈ ν.extPositions j, p = x ∨ p = y := by
      intro j hj p hp
      have hlevel : j ∈ σ.levels := (List.mem_filter.mp hj).1
      have hsideν := (of_decide_eq_true (List.mem_filter.mp hj).2).1
      have hsideσ : σ.sideAt j = s := (hνSide j hlevel).symm.trans hsideν
      have hjpos := (one_le_of_mem_levelsOn hj).1
      have hOn : j ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hlevel, by simp [hsideσ]⟩
      rw [hνExt j hlevel] at hp
      by_cases hjM : j = M
      · rw [if_pos hjM] at hp
        exact Or.inr (List.mem_singleton.mp (of_decide_eq_true (List.mem_filter.mp hp).2))
      · rw [if_neg hjM] at hp
        by_cases hjN : j = N
        · rw [if_pos hjN] at hp
          exact Or.inl (List.mem_singleton.mp (of_decide_eq_true (List.mem_filter.mp hp).2))
        · rw [if_neg hjN, hchosen j hOn hjN hjM] at hp
          exact False.elim (List.not_mem_nil hp)
    have hclear : ν.levelsOn t 0=[] := by
      unfold levelsOn
      change σ.levels.filter _=[]
      rw [hlevels]
      simp [hνSide N hN, hνSide M hM, hNs, hMs, hne]
    have hνBound := (ctx_bare_two_marker_sharp_potential ν hνPos s t hne N M x y
      hN hM hNM ((hνSide N hN).trans hNs) ((hνSide M hM).trans hMs)
      hxν hyν hglobal hclear hνChosen hwidth).2
    have hToτ : σ.bound ≤ τ.bound := hFirst.2.2.2.2.2.2
    have hToν : τ.bound ≤ ν.bound := hSecond.2.2.2.2.2.2
    exact hToτ.trans (hToν.trans hνBound)
  have hMain : ∀ d (ρ : Context), ρ.maxima.length=d →
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      ∀ N M x y, N ∈ ρ.levels → M ∈ ρ.levels → N<M →
      ρ.sideAt N=s → ρ.sideAt M=s → x ∈ ρ.extPositions N → y ∈ ρ.extPositions M →
      G ρ s ≤ 5 → 2 ≤ G ρ t-1 → ρ.bound ≤ P (G ρ t-1) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro ρ hd hPos N M x y hN hM hNM hNs hMs hx hy hGs hW
      have hNB := (hLevelMem ρ N).mp hN
      have hMB := (hLevelMem ρ M).mp hM
      by_cases hTwo : ρ.maxima.length=2
      · exact hBase ρ hPos N M x y hN hM hNM hNs hMs hx hy hGs hW hTwo
      let L := if N=1 then if M=2 then 3 else 2 else 1
      have hLB : 1 ≤ L ∧ L ≤ ρ.maxima.length ∧ L≠N ∧ L≠M := by
        dsimp only [L]
        split_ifs <;> omega
      have hL : L ∈ ρ.levels := (hLevelMem ρ L).mpr ⟨hLB.1,hLB.2.1⟩
      let N' := if N<L then N else N-1
      let M' := if M<L then M else M-1
      have hN' : N' ∈ (norm ρ L).levels := by
        apply (hLevelMem (norm ρ L) N').mpr
        rw [hDepth ρ L hL]
        dsimp only [N']
        split_ifs <;> omega
      have hM' : M' ∈ (norm ρ L).levels := by
        apply (hLevelMem (norm ρ L) M').mpr
        rw [hDepth ρ L hL]
        dsimp only [M']
        split_ifs <;> omega
      have hNM' : N'<M' := by
        dsimp only [N',M']
        split_ifs <;> omega
      have hRecoverN : up L N'=N := by
        dsimp only [up,N']
        split_ifs <;> omega
      have hRecoverM : up L M'=M := by
        dsimp only [up,M']
        split_ifs <;> omega
      have hNs' : (norm ρ L).sideAt N'=s := by
        rw [hSide ρ L N' hL hN',hRecoverN]
        exact hNs
      have hMs' : (norm ρ L).sideAt M'=s := by
        rw [hSide ρ L M' hL hM',hRecoverM]
        exact hMs
      have hx' : x ∈ (norm ρ L).extPositions N' := by
        rw [hExt ρ L N' hL hN',hRecoverN]
        exact hx
      have hy' : y ∈ (norm ρ L).extPositions M' := by
        rw [hExt ρ L M' hL hM',hRecoverM]
        exact hy
      have hD : (norm ρ L).maxima.length<d := by rw [hDepth ρ L hL]; omega
      have hBound := ih (norm ρ L).maxima.length hD (norm ρ L) rfl
        (hPositive ρ L hL hPos) N' M' x y hN' hM' hNM' hNs' hMs' hx' hy' hGs hW
      have hMono : ρ.bound ≤ (norm ρ L).bound := (ctx_erase_level_bound_mono ρ L hL).2.2
      exact hMono.trans hBound
  have hBound := hMain σ.maxima.length σ rfl hpositive N M x y hN hM hNM
    hNs hMs hx hy hglobal hwidth
  have hFuelFull (fuel : ℕ) : boundFuel fuel σ ≤ σ.bound := by
    by_cases hf : σ.childPositions.length+1 ≤ fuel
    · exact (boundFuel_eq_bound σ hf).le
    · exact boundFuel_mono (by omega : fuel ≤ σ.childPositions.length+1) σ
  exact ⟨fun fuel => (hFuelFull fuel).trans hBound,hBound⟩

end ErdosSzekeres
