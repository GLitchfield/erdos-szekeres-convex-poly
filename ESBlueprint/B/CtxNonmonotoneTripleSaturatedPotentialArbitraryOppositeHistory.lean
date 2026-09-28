import ESBlueprint.B.CtxNonmonotoneTripleSaturatedPotential
import ESBlueprint.B.CtxEraseLevelBoundMono

namespace ErdosSzekeres

/-- Remove the empty opposite indexed-history restriction from the nonmonotone-triple saturated potential. Retain three actual chosen markers in nonmonotone age/spatial order and a chosen maximum at least k-4 while erasing opposite levels using checked bound monotonicity; the clear-history endpoint is the existing saturated potential. Positive physical labels, distinct axes, chosen global at most five, opposite global at most k, and k at least five remain explicit. Top and next bounds are 3k-8 and 3k-9 for all fuel and the full bound. All additional chosen and opposite history, maxima, inactive children, and positive unindexed barriers are allowed. The large chosen maximum and nonmonotone geometry remain substantive assumptions; this does not close the general parent. Search evidence: runs/sol-trial-20260913/search-arbitrary-opposite.json.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonmonotone_triple_saturated_potential_arbitrary_opposite_history (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (J N M z x y : ℕ)
  (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels)
  (hJN : J < N) (hNM : N < M)
  (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hz : z ∈ σ.extPositions J) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hgeometry : (z < x ∧ y < x) ∨ (x < z ∧ x < y))
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hk : 5 ≤ σ.k) (R : ℕ) (hR : R ∈ σ.levels) (hRs : σ.sideAt R = s)
  (hmaximum : σ.k-4 ≤ σ.maximumAt R) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 3*σ.k-8) ∧ σ.bound ≤ 3*σ.k-8 ∧
    ((match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k-1 →
      (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 3*σ.k-9) ∧ σ.bound ≤ 3*σ.k-9) := by
  classical
  let G (ρ : Ctx.Context) (v : Ctx.Side) :=
    match v with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
  let letter (D L : ℕ) : Ctx.Letter → Ctx.Letter := fun w => match w with
    | Ctx.Letter.child => Ctx.Letter.child
    | Ctx.Letter.ext j v => Ctx.Letter.ext (idx D L j) v
  let norm (ρ : Ctx.Context) (L : ℕ) : Ctx.Context :=
    { ρ with word := ρ.word.map (letter ρ.maxima.length L), maxima := ρ.maxima.eraseIdx (L - 1) }
  let up (L j : ℕ) := if j < L then j else j + 1
  let down (L j : ℕ) := if j < L then j else j - 1
  have hLevelMem (ρ : Ctx.Context) (j : ℕ) :
      j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
    simp only [Ctx.Context.levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · intro hj
      exact ⟨j - 1, by omega, by omega⟩
  have hLen (ρ : Ctx.Context) (L : ℕ) :
      (norm ρ L).word.length = ρ.word.length := by
    simp only [norm, List.length_map]
  have hLetter (ρ : Ctx.Context) (L p : ℕ) :
      (norm ρ L).letterAt p = letter ρ.maxima.length L (ρ.letterAt p) := by
    simp only [norm, Ctx.Context.letterAt, List.getElem?_map]
    cases ρ.word[p]? <;> rfl
  have hDepth (ρ : Ctx.Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      (norm ρ L).maxima.length = ρ.maxima.length - 1 := by
    have hLB := (hLevelMem ρ L).mp hL
    exact List.length_eraseIdx_of_lt (by omega)
  have hLive (ρ : Ctx.Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) :
      1 ≤ j ∧ j < ρ.maxima.length ∧ up L j ∈ ρ.levels := by
    have hLB := (hLevelMem ρ L).mp hL
    have hj' := (hLevelMem (norm ρ L) j).mp hj
    rw [hDepth ρ L hL] at hj'
    refine ⟨hj'.1, by omega, ?_⟩
    apply (hLevelMem ρ _).mpr
    dsimp only [up]
    split_ifs <;> omega
  have hIndex (D L i j : ℕ) (hL : 1 ≤ L) (hLD : L ≤ D)
      (hj : 1 ≤ j) (hjD : j < D) : idx D L i = j ↔ i = up L j := by
    dsimp only [idx, up]
    split_ifs <;> omega
  have hExt (ρ : Ctx.Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) :
      (norm ρ L).extPositions j = ρ.extPositions (up L j) := by
    have hLB := (hLevelMem ρ L).mp hL
    have hj' := hLive ρ L j hL hj
    simp only [Ctx.Context.extPositions, hLen, hLetter]
    apply List.filter_congr
    intro p _
    cases ρ.letterAt p with
    | child => rfl
    | ext i v =>
        simp only [letter, hIndex _ _ i j hLB.1 hLB.2 hj'.1 hj'.2.1]
  have hSide (ρ : Ctx.Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) :
      (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
    simp only [Ctx.Context.sideAt, hExt ρ L j hL hj]
    cases hh : (ρ.extPositions (up L j)).head? with
    | none => rfl
    | some p =>
        dsimp only
        rw [hLetter]
        cases ρ.letterAt p <;> rfl
  have hMaximum (ρ : Ctx.Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) :
      (norm ρ L).maximumAt j = ρ.maximumAt (up L j) := by
    have hLB := (hLevelMem ρ L).mp hL
    have hj' := (hLive ρ L j hL hj).1
    simp only [Ctx.Context.maximumAt, norm, List.getElem?_eraseIdx]
    by_cases h : j < L
    · simp [up, h, show j - 1 < L - 1 by omega]
    · simp [up, h, show ¬j - 1 < L - 1 by omega, show j - 1 + 1 = j by omega]
  have hPositive (ρ : Ctx.Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (hPos : ∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) :
      ∀ p j v, (norm ρ L).letterAt p = Ctx.Letter.ext j v → 1 ≤ j := by
    intro p j v hj
    rw [hLetter] at hj
    have hLB := (hLevelMem ρ L).mp hL
    cases he : ρ.letterAt p with
    | child =>
        simp only [he, letter] at hj
        cases hj
    | ext i w =>
        rw [he] at hj
        have hi := hPos p i w he
        have hnew : 1 ≤ idx ρ.maxima.length L i := by
          dsimp only [idx]
          split_ifs <;> omega
        change Ctx.Letter.ext (idx ρ.maxima.length L i) w = Ctx.Letter.ext j v at hj
        cases hj
        exact hnew
  have hDownMem (ρ : Ctx.Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ ρ.levels) (hjL : j ≠ L) : down L j ∈ (norm ρ L).levels := by
    have hLB := (hLevelMem ρ L).mp hL
    have hjB := (hLevelMem ρ j).mp hj
    apply (hLevelMem (norm ρ L) _).mpr
    rw [hDepth ρ L hL]
    dsimp only [down]
    split_ifs <;> omega
  have hRecover (ρ : Ctx.Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ ρ.levels) (hjL : j ≠ L) : up L (down L j) = j := by
    have hLB := (hLevelMem ρ L).mp hL
    have hjB := (hLevelMem ρ j).mp hj
    dsimp only [up, down]
    split_ifs <;> omega
  have hDownMono (L i j : ℕ) (hiL : i ≠ L) (hjL : j ≠ L) (hij : i < j) :
      down L i < down L j := by
    dsimp only [down]
    split_ifs <;> omega
  have hMain : ∀ d (ρ : Ctx.Context), ρ.maxima.length = d →
      (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
      ∀ J N M z x y,
      J ∈ ρ.levels → N ∈ ρ.levels → M ∈ ρ.levels → J < N → N < M →
      ρ.sideAt J = s → ρ.sideAt N = s → ρ.sideAt M = s →
      z ∈ ρ.extPositions J → x ∈ ρ.extPositions N → y ∈ ρ.extPositions M →
      ((z < x ∧ y < x) ∨ (x < z ∧ x < y)) →
      G ρ s ≤ 5 → G ρ t ≤ ρ.k → 5 ≤ ρ.k →
      ∀ R, R ∈ ρ.levels → ρ.sideAt R = s → ρ.k - 4 ≤ ρ.maximumAt R →
      ρ.bound ≤ 3 * ρ.k - 8 ∧
        (G ρ t ≤ ρ.k - 1 → ρ.bound ≤ 3 * ρ.k - 9) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro ρ hd hPos J N M z x y hJ hN hM hJN hNM hJs hNs hMs
        hz hx hy hGeom hGs hGt hk R hR hRs hMax
      by_cases hClear : ρ.levelsOn t 0 = []
      · have hb := ctx_nonmonotone_triple_saturated_potential ρ hPos s t hne
          J N M z x y hJ hN hM hJN hNM hJs hNs hMs hz hx hy hGeom
          hGs hClear hGt hk R hR hRs hMax
        exact ⟨hb.2.1, fun hnext => (hb.2.2 hnext).2⟩
      · obtain ⟨L, hLOn⟩ := List.exists_mem_of_ne_nil _ hClear
        have hL : L ∈ ρ.levels := (List.mem_filter.mp hLOn).1
        have hLBounds : 1 ≤ L ∧ L ≤ ρ.maxima.length := (hLevelMem ρ L).mp hL
        have hLt : ρ.sideAt L = t :=
          (of_decide_eq_true (List.mem_filter.mp hLOn).2).1
        have hLJ : L ≠ J := by
          intro he
          subst J
          exact hne (hJs.symm.trans hLt)
        have hLN : L ≠ N := by
          intro he
          subst N
          exact hne (hNs.symm.trans hLt)
        have hLM : L ≠ M := by
          intro he
          subst M
          exact hne (hMs.symm.trans hLt)
        have hLR : L ≠ R := by
          intro he
          subst R
          exact hne (hRs.symm.trans hLt)
        let J' := down L J
        let N' := down L N
        let M' := down L M
        let R' := down L R
        have hJ' : J' ∈ (norm ρ L).levels := hDownMem ρ L J hL hJ hLJ.symm
        have hN' : N' ∈ (norm ρ L).levels := hDownMem ρ L N hL hN hLN.symm
        have hM' : M' ∈ (norm ρ L).levels := hDownMem ρ L M hL hM hLM.symm
        have hR' : R' ∈ (norm ρ L).levels := hDownMem ρ L R hL hR hLR.symm
        have hJRecover : up L J' = J := hRecover ρ L J hL hJ hLJ.symm
        have hNRecover : up L N' = N := hRecover ρ L N hL hN hLN.symm
        have hMRecover : up L M' = M := hRecover ρ L M hL hM hLM.symm
        have hRRecover : up L R' = R := hRecover ρ L R hL hR hLR.symm
        have hJN' : J' < N' := hDownMono L J N hLJ.symm hLN.symm hJN
        have hNM' : N' < M' := hDownMono L N M hLN.symm hLM.symm hNM
        have hJs' : (norm ρ L).sideAt J' = s := by
          rw [hSide ρ L J' hL hJ', hJRecover]
          exact hJs
        have hNs' : (norm ρ L).sideAt N' = s := by
          rw [hSide ρ L N' hL hN', hNRecover]
          exact hNs
        have hMs' : (norm ρ L).sideAt M' = s := by
          rw [hSide ρ L M' hL hM', hMRecover]
          exact hMs
        have hRs' : (norm ρ L).sideAt R' = s := by
          rw [hSide ρ L R' hL hR', hRRecover]
          exact hRs
        have hz' : z ∈ (norm ρ L).extPositions J' := by
          rw [hExt ρ L J' hL hJ', hJRecover]
          exact hz
        have hx' : x ∈ (norm ρ L).extPositions N' := by
          rw [hExt ρ L N' hL hN', hNRecover]
          exact hx
        have hy' : y ∈ (norm ρ L).extPositions M' := by
          rw [hExt ρ L M' hL hM', hMRecover]
          exact hy
        have hMax' : (norm ρ L).k - 4 ≤ (norm ρ L).maximumAt R' := by
          rw [hMaximum ρ L R' hL hR', hRRecover]
          exact hMax
        have hD : (norm ρ L).maxima.length < d := by
          rw [hDepth ρ L hL, hd]
          omega
        have hRec := ih (norm ρ L).maxima.length hD (norm ρ L) rfl
          (hPositive ρ L hL hPos) J' N' M' z x y hJ' hN' hM' hJN' hNM'
          hJs' hNs' hMs' hz' hx' hy' hGeom hGs hGt hk R' hR' hRs' hMax'
        have hMono : ρ.bound ≤ (norm ρ L).bound :=
          (ctx_erase_level_bound_mono ρ L hL).2.2
        exact ⟨hMono.trans hRec.1, fun hnext => hMono.trans (hRec.2 hnext)⟩
  have hBounds := hMain σ.maxima.length σ rfl hpositive J N M z x y
    hJ hN hM hJN hNM hJs hNs hMs hz hx hy hgeometry hglobal hopposite hk
    R hR hRs hmaximum
  have hFuelFull (fuel : ℕ) : Ctx.Context.boundFuel fuel σ ≤ σ.bound := by
    by_cases hf : σ.childPositions.length + 1 ≤ fuel
    · exact (Ctx.Context.boundFuel_eq_bound σ hf).le
    · exact Ctx.Context.boundFuel_mono
        (by omega : fuel ≤ σ.childPositions.length + 1) σ
  refine ⟨fun fuel => (hFuelFull fuel).trans hBounds.1, hBounds.1, ?_⟩
  intro hnext
  exact ⟨fun fuel => (hFuelFull fuel).trans (hBounds.2 hnext), hBounds.2 hnext⟩


end ErdosSzekeres
