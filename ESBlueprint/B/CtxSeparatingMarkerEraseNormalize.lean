import ESBlueprint.B.CtxEraseLevelBoundMono
import ESBlueprint.B.CtxBoundaryMarkerEraseNormalize
import ESBlueprint.B.CtxActiveTwoBoundaryMarkerRankUnionBound

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Erase a chosen indexed marker level that separates all children and younger same-axis positions from all older same-axis positions, reducing only its global parameter by one. Every child-endpoint limit and every recursive fuel/full bound can only increase. All other history, including older chosen markers and arbitrary opposite history, is retained. Exact child positions, depth reduction, surviving indexed-level data and opposite pure extension traces and positive labels are exposed for reuse. Both directions and axes, positive labels and arbitrary maxima are allowed. The pure-chain argument inserts the selected level between younger and older subsequences. This permits a global-five exterior to retain an older marker after reduction to global four. No k-minus-maximum cap is asserted: that stronger variant has a concrete finite counterexample.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_separating_marker_erase_normalize (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N)
  (rightward : Bool)
  (hchildren : ∀ p ∈ σ.childPositions, if rightward then p < x else x < p)
  (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
    if rightward then p < x else x < p)
  (holder : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, N < j →
    ∀ p ∈ σ.extPositions j, if rightward then x < p else p < x) :
  let ρ : Ctx.Context := { σ with
    word := σ.word.map (fun z => match z with
      | Ctx.Letter.child => Ctx.Letter.child
      | Ctx.Letter.ext j v => Ctx.Letter.ext
          (if j = N then σ.maxima.length else if N < j then j - 1 else j) v)
    maxima := σ.maxima.eraseIdx (N - 1) }
  let τ : Ctx.Context := match σ.sideAt N with
    | Ctx.Side.lower => { ρ with u := σ.u - 1 }
    | Ctx.Side.upper => { ρ with a := σ.a - 1 }
  τ.childPositions = σ.childPositions ∧ τ.maxima.length = σ.maxima.length - 1 ∧
    (∀ j ∈ τ.levels,
      let i := if j < N then j else j + 1
      i ∈ σ.levels ∧ i ≠ N ∧ τ.extPositions j = σ.extPositions i ∧
        τ.sideAt j = σ.sideAt i ∧ τ.maximumAt j = σ.maximumAt i) ∧
    (∀ t : Ctx.Side, σ.sideAt N ≠ t → ∀ p,
      τ.leftExt t 0 p = σ.leftExt t 0 p ∧ τ.rightExt t 0 p = σ.rightExt t 0 p) ∧
    (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
  (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
    σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧
    σ.bound ≤ τ.bound := by
  classical
  let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
  let letter (D L : ℕ) : Letter → Letter := fun x => match x with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext (idx D L j) v
  let erase (ρ : Context) (L : ℕ) : Context :=
    { ρ with word := ρ.word.map (letter ρ.maxima.length L), maxima := ρ.maxima.eraseIdx (L-1) }
  let up (L j : ℕ) := if j < L then j else j+1
  let norm (ρ : Context) (L : ℕ) : Context := match ρ.sideAt L with
    | Side.lower => { erase ρ L with u := ρ.u - 1 }
    | Side.upper => { erase ρ L with a := ρ.a - 1 }
  change (norm σ N).childPositions = σ.childPositions ∧
    (norm σ N).maxima.length = σ.maxima.length - 1 ∧
    (∀ j ∈ (norm σ N).levels,
      up N j ∈ σ.levels ∧ up N j ≠ N ∧
        (norm σ N).extPositions j = σ.extPositions (up N j) ∧
        (norm σ N).sideAt j = σ.sideAt (up N j) ∧
        (norm σ N).maximumAt j = σ.maximumAt (up N j)) ∧
    (∀ t : Side, σ.sideAt N ≠ t → ∀ p,
      (norm σ N).leftExt t 0 p = σ.leftExt t 0 p ∧
        (norm σ N).rightExt t 0 p = σ.rightExt t 0 p) ∧
    (∀ p j v, (norm σ N).letterAt p = Letter.ext j v → 1 ≤ j) ∧
    (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
    σ.cupLimit p q ≤ (norm σ N).cupLimit p q ∧ σ.capLimit p q ≤ (norm σ N).capLimit p q) ∧
    (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel (norm σ N)) ∧ σ.bound ≤ (norm σ N).bound
  have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
    simp only [levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro hj; exact ⟨j-1, by omega, by omega⟩
  have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
    unfold levels
    exact List.pairwise_lt_range.map (fun x => x+1) (fun a b h => Nat.add_lt_add_right h 1)
  have hLen (ρ : Context) (L : ℕ) : (erase ρ L).word.length = ρ.word.length := by
    simp only [erase, List.length_map]
  have hLetter (ρ : Context) (L p : ℕ) :
      (erase ρ L).letterAt p = letter ρ.maxima.length L (ρ.letterAt p) := by
    simp only [erase, letterAt, List.getElem?_map]
    cases ρ.word[p]? <;> rfl
  have hIsChild (ρ : Context) (L p : ℕ) :
      (erase ρ L).letterAt p = Letter.child ↔ ρ.letterAt p = Letter.child := by
    rw [hLetter]
    cases ρ.letterAt p <;> simp [letter]
  have hChild (ρ : Context) (L : ℕ) : (erase ρ L).childPositions = ρ.childPositions := by
    simp only [childPositions, hLen, hIsChild]
  have hRuns (ρ : Context) (L : ℕ) : (erase ρ L).numRuns = ρ.numRuns := by
    simp only [numRuns, hLen, ne_eq, hIsChild]
  have hBlocks (ρ : Context) (L : ℕ) : (erase ρ L).blocks = ρ.blocks := by
    simp only [blocks, hChild]
  have hK (ρ : Context) (L : ℕ) : (erase ρ L).k = ρ.k := rfl
  have hDepth (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      (erase ρ L).maxima.length = ρ.maxima.length-1 := by
    have hh := (hLevelMem ρ L).mp hL
    exact List.length_eraseIdx_of_lt (by omega)
  have hLive (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (erase ρ L).levels) :
      1 ≤ j ∧ j < ρ.maxima.length ∧ up L j ∈ ρ.levels := by
    have hh := (hLevelMem ρ L).mp hL
    have hj' := (hLevelMem (erase ρ L) j).mp hj
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
      (hj : j ∈ (erase ρ L).levels) :
      (erase ρ L).extPositions j = ρ.extPositions (up L j) := by
    have hLj := (hLevelMem ρ L).mp hL
    have hj' := hLive ρ L j hL hj
    simp only [extPositions, hLen, hLetter]
    apply List.filter_congr
    intro p _
    cases ρ.letterAt p with
    | child => rfl
    | ext i v => simp only [letter, hIndex _ _ i j hLj.1 hLj.2 hj'.1 hj'.2.1]
  have hSide (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (erase ρ L).levels) : (erase ρ L).sideAt j = ρ.sideAt (up L j) := by
    simp only [sideAt, hExt ρ L j hL hj]
    cases hh : (ρ.extPositions (up L j)).head? with
    | none => rfl
    | some p =>
      dsimp only
      rw [hLetter]
      cases ρ.letterAt p <;> rfl
  have hMaximum (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (erase ρ L).levels) : (erase ρ L).maximumAt j = ρ.maximumAt (up L j) := by
    have hh := (hLevelMem ρ L).mp hL
    have hj' := (hLive ρ L j hL hj).1
    simp only [maximumAt, erase, List.getElem?_eraseIdx]
    by_cases h : j < L
    · simp [up, h, show j-1 < L-1 by omega]
    · simp [up, h, show ¬j-1 < L-1 by omega, show j-1+1 = j by omega]
  have hUpMono (L i j : ℕ) (h : i < j) : up L i < up L j := by
    dsimp [up]; split_ifs <;> omega
  have hUpZero (L : ℕ) (hL : 1 ≤ L) : up L 0 = 0 := by simp [up, show 0 < L by omega]
  have hSub (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side) (top : ℕ) :
      (((erase ρ L).levelsOn v top).map (up L)).Sublist (ρ.levelsOn v (up L top)) := by
    have hs : (((erase ρ L).levelsOn v top).map (up L)).Pairwise (· < ·) :=
      ((hSorted (erase ρ L)).filter _).map (up L) (fun i j hij => hUpMono L i j hij)
    have ho : (ρ.levelsOn v (up L top)).Pairwise (· < ·) := (hSorted ρ).filter _
    have hsubset : (((erase ρ L).levelsOn v top).map (up L)) ⊆ ρ.levelsOn v (up L top) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      have hjl := (List.mem_filter.mp hj).1
      have hjc : (erase ρ L).sideAt j = v ∧ (top = 0 ∨ j < top) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      apply List.mem_filter.mpr
      refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
      apply decide_eq_true
      refine ⟨?_, ?_⟩
      · rw [← hSide ρ L j hL hjl]; exact hjc.1
      · rcases hjc.2 with rfl | hlt
        · exact Or.inl (hUpZero L (one_le_of_mem_levels hL))
        · exact Or.inr (hUpMono L j top hlt)
    have he : (ρ.levelsOn v (up L top)).filter
        (· ∈ (((erase ρ L).levelsOn v top).map (up L))) =
        (((erase ρ L).levelsOn v top).map (up L)) := by
      apply (ho.filter _).eq_of_mem_iff hs
      intro x
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun hx => ⟨hsubset hx, hx⟩⟩
    rw [← he]
    exact List.filter_sublist
  have hFoldLeft (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (erase ρ L).levels) → ∀ z,
      ls.foldl (leftStep (erase ρ L)) z = (ls.map (up L)).foldl (leftStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ z; rfl
    | cons j ls ih =>
      intro hj z
      simp only [List.foldl_cons, List.map_cons, leftStep, hExt ρ L j hL (hj j (by simp))]
      exact ih (fun i hi => hj i (by simp [hi])) _
  have hFoldRight (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (erase ρ L).levels) → ∀ z,
      ls.foldl (rightStep (erase ρ L)) z = (ls.map (up L)).foldl (rightStep ρ) z := by
    intro ls
    induction ls with
    | nil => intro _ z; rfl
    | cons j ls ih =>
      intro hj z
      simp only [List.foldl_cons, List.map_cons, rightStep, hExt ρ L j hL (hj j (by simp))]
      exact ih (fun i hi => hj i (by simp [hi])) _
  have hLeftLe (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side) (top p : ℕ) :
      (erase ρ L).leftExt v top p ≤ ρ.leftExt v (up L top) p := by
    simp only [leftExt_eq]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    have hsub := List.mem_sublists.mp hls
    have hl : ∀ j ∈ ls, j ∈ (erase ρ L).levels :=
      fun j hj => (List.mem_filter.mp (hsub.subset hj)).1
    refine ⟨_, List.mem_map.mpr ⟨ls.map (up L),
      List.mem_sublists.mpr ((hsub.map _).trans (hSub ρ L hL v top)), rfl⟩, ?_⟩
    exact le_of_eq (congrArg Prod.snd (hFoldLeft ρ L hL ls hl (p,0)))
  have hRightLe (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) (v : Side) (top p : ℕ) :
      (erase ρ L).rightExt v top p ≤ ρ.rightExt v (up L top) p := by
    simp only [rightExt_eq]
    apply Ctx.getD_max?_le_of_forall
    intro x hx
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
    have hsub := List.mem_sublists.mp hls
    have hl : ∀ j ∈ ls, j ∈ (erase ρ L).levels :=
      fun j hj => (List.mem_filter.mp (hsub.subset hj)).1
    refine ⟨_, List.mem_map.mpr ⟨ls.map (up L),
      List.mem_sublists.mpr ((hsub.map _).trans (hSub ρ L hL v top)), rfl⟩, ?_⟩
    exact le_of_eq (congrArg Prod.snd (hFoldRight ρ L hL ls hl (p,0)))
  have hNormChild (ρ : Context) (L : ℕ) : (norm ρ L).childPositions = ρ.childPositions := by
    cases hs : ρ.sideAt L <;> simpa only [norm, hs] using hChild ρ L
  have hNormRuns (ρ : Context) (L : ℕ) : (norm ρ L).numRuns = ρ.numRuns := by
    cases hs : ρ.sideAt L <;> simpa only [norm, hs] using hRuns ρ L
  have hNormBlocks (ρ : Context) (L : ℕ) : (norm ρ L).blocks = ρ.blocks := by
    simp only [blocks, hNormChild]
  have hNormK (ρ : Context) (L : ℕ) : (norm ρ L).k = ρ.k := by
    cases hs : ρ.sideAt L <;> simp only [norm, hs] <;> rfl
  have hOppLevels (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (v : Side) (hne : ρ.sideAt L ≠ v) :
      ((erase ρ L).levelsOn v 0).map (up L) = ρ.levelsOn v 0 := by
    have hs : (((erase ρ L).levelsOn v 0).map (up L)).Pairwise (· < ·) :=
      ((hSorted (erase ρ L)).filter _).map (up L) (fun i j hij => hUpMono L i j hij)
    apply hs.eq_of_mem_iff ((hSorted ρ).filter _)
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hjl := (List.mem_filter.mp hj).1
      have hjc : (erase ρ L).sideAt j = v ∧ (0 = 0 ∨ j < 0) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      apply List.mem_filter.mpr
      refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
      rw [hSide ρ L j hL hjl] at hjc
      apply decide_eq_true
      exact ⟨hjc.1, Or.inl rfl⟩
    · intro hi
      have hil := (hLevelMem ρ i).mp (List.mem_filter.mp hi).1
      have hic : ρ.sideAt i = v ∧ (0 = 0 ∨ i < 0) :=
        of_decide_eq_true (List.mem_filter.mp hi).2
      have hiL : i ≠ L := by intro h; subst i; exact hne hic.1
      have hLL := (hLevelMem ρ L).mp hL
      let j := if i < L then i else i-1
      have hup : up L j = i := by dsimp [up, j]; split_ifs <;> omega
      have hjl : j ∈ (erase ρ L).levels := by
        apply (hLevelMem (erase ρ L) j).mpr
        rw [hDepth ρ L hL]
        dsimp [j]
        split_ifs <;> omega
      apply List.mem_map.mpr
      refine ⟨j, ?_, hup⟩
      apply List.mem_filter.mpr
      refine ⟨hjl, ?_⟩
      apply decide_eq_true
      rw [hSide ρ L j hL hjl, hup]
      exact ⟨hic.1, Or.inl rfl⟩
  have hEraseLeft (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (v : Side) (hne : ρ.sideAt L ≠ v) (p : ℕ) :
      (erase ρ L).leftExt v 0 p = ρ.leftExt v 0 p := by
    rw [leftExt_eq, leftExt_eq, ← hOppLevels ρ L hL v hne, List.sublists_map, List.map_map]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    have hl : ∀ j ∈ ls, j ∈ (erase ρ L).levels :=
      fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1
    exact congrArg Prod.snd (hFoldLeft ρ L hL ls hl (p,0))
  have hEraseRight (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (v : Side) (hne : ρ.sideAt L ≠ v) (p : ℕ) :
      (erase ρ L).rightExt v 0 p = ρ.rightExt v 0 p := by
    rw [rightExt_eq, rightExt_eq, ← hOppLevels ρ L hL v hne, List.sublists_map, List.map_map]
    apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
    apply List.map_congr_left
    intro ls hls
    have hl : ∀ j ∈ ls, j ∈ (erase ρ L).levels :=
      fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1
    exact congrArg Prod.snd (hFoldRight ρ L hL ls hl (p,0))
  have hErasePositive (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) :
      ∀ p j v, (erase ρ L).letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    rw [hLetter] at hp
    have hL1 := one_le_of_mem_levels hL
    have hDepthPos : 1 ≤ ρ.maxima.length := by
      have h := (hLevelMem ρ L).mp hL
      omega
    cases he : ρ.letterAt p with
    | child =>
      simp only [he, letter] at hp
      cases hp
    | ext i w =>
      have hi := hPos p i w he
      simp only [he, letter] at hp
      have hij := (Letter.ext.inj hp).1
      dsimp only [idx] at hij
      split_ifs at hij <;> omega
  have hEndRight (ρ : Context) (x : ℕ) : ∀ (ls : List ℕ),
      (∀ j ∈ ls, ∀ y ∈ ρ.extPositions j, y < x) → ∀ z : ℕ × ℕ,
      z.1 < x → (ls.foldl (rightStep ρ) z).1 < x := by
    intro ls
    induction ls with
    | nil => intro _ z hz; exact hz
    | cons j ls ih =>
      intro hy z hz
      have ht : ∀ i ∈ ls, ∀ y ∈ ρ.extPositions i, y < x :=
        fun i hi y hiy => hy i (by simp [hi]) y hiy
      cases hh : ((ρ.extPositions j).filter (z.1 < ·)).head? with
      | none => simpa only [List.foldl_cons, rightStep, hh] using ih ht z hz
      | some y =>
        have hm := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
        simpa only [List.foldl_cons, rightStep, hh] using ih ht (y,z.2+1) hyx
  have hEndLeft (ρ : Context) (x : ℕ) : ∀ (ls : List ℕ),
      (∀ j ∈ ls, ∀ y ∈ ρ.extPositions j, x < y) → ∀ z : ℕ × ℕ,
      x < z.1 → x < (ls.foldl (leftStep ρ) z).1 := by
    intro ls
    induction ls with
    | nil => intro _ z hz; exact hz
    | cons j ls ih =>
      intro hy z hz
      have ht : ∀ i ∈ ls, ∀ y ∈ ρ.extPositions i, x < y :=
        fun i hi y hiy => hy i (by simp [hi]) y hiy
      cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? with
      | none => simpa only [List.foldl_cons, leftStep, hh] using ih ht z hz
      | some y =>
        have hm := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
        have hxy := hy j (by simp) y (List.mem_filter.mp hm).1
        simpa only [List.foldl_cons, leftStep, hh] using ih ht (y,z.2+1) hxy
  let Near (dir : Bool) (p x : ℕ) : Prop := if dir then p < x else x < p
  let NearEq (dir : Bool) (p x : ℕ) : Prop := if dir then p ≤ x else x ≤ p
  let Step (ρ : Context) (dir : Bool) : ℕ × ℕ → ℕ → ℕ × ℕ :=
    if dir then rightStep ρ else leftStep ρ
  let Shift (z : ℕ × ℕ) (c : ℕ) := (z.1, z.2 + c)
  have hStepShift (ρ : Context) (dir : Bool) (j : ℕ) (z : ℕ × ℕ) (c : ℕ) :
      Step ρ dir (Shift z c) j = Shift (Step ρ dir z j) c := by
    rcases z with ⟨p, n⟩
    cases dir
    · cases h : ((ρ.extPositions j).filter (· < p)).getLast? <;>
        simp only [Step, Bool.false_eq_true, if_false, Shift, leftStep, h] <;>
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · cases h : ((ρ.extPositions j).filter (p < ·)).head? <;>
        simp only [Step, if_true, Shift, rightStep, h] <;>
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hFoldShift (ρ : Context) (dir : Bool) (ls : List ℕ) (z : ℕ × ℕ) (c : ℕ) :
      ls.foldl (Step ρ dir) (Shift z c) = Shift (ls.foldl (Step ρ dir) z) c := by
    induction ls generalizing z with
    | nil => rfl
    | cons j ls ih =>
      simp only [List.foldl_cons, hStepShift]
      exact ih _
  have hFarFold (ρ : Context) (dir : Bool) (x : ℕ) : ∀ ls : List ℕ,
      (∀ j ∈ ls, ∀ z ∈ ρ.extPositions j, Near dir x z) → ∀ p q c : ℕ,
      NearEq dir p x → NearEq dir q x →
      (ls.foldl (Step ρ dir) (p, c)).2 = (ls.foldl (Step ρ dir) (q, c)).2 := by
    intro ls
    induction ls with
    | nil => intro _ p q c _ _; rfl
    | cons j ls ih =>
      intro hf p q c hp hq
      have ht : ∀ i ∈ ls, ∀ z ∈ ρ.extPositions i, Near dir x z :=
        fun i hi z hz => hf i (by simp [hi]) z hz
      cases dir
      · have hfp : (ρ.extPositions j).filter (· < p) = ρ.extPositions j := by
          apply List.filter_eq_self.mpr
          intro z hz
          have hh := hf j (by simp) z hz
          simp only [Near, NearEq, Bool.false_eq_true, if_false] at hh hp
          exact decide_eq_true (by omega)
        have hfq : (ρ.extPositions j).filter (· < q) = ρ.extPositions j := by
          apply List.filter_eq_self.mpr
          intro z hz
          have hh := hf j (by simp) z hz
          simp only [Near, NearEq, Bool.false_eq_true, if_false] at hh hq
          exact decide_eq_true (by omega)
        cases hh : (ρ.extPositions j).getLast? with
        | none =>
          simpa only [List.foldl_cons, Step, Bool.false_eq_true, if_false, leftStep,
            hfp, hfq, hh] using ih ht p q c hp hq
        | some z =>
          simp only [List.foldl_cons, Step, Bool.false_eq_true, if_false, leftStep,
            hfp, hfq, hh]
      · have hfp : (ρ.extPositions j).filter (p < ·) = ρ.extPositions j := by
          apply List.filter_eq_self.mpr
          intro z hz
          have hh := hf j (by simp) z hz
          simp only [Near, NearEq, if_true] at hh hp
          exact decide_eq_true (by omega)
        have hfq : (ρ.extPositions j).filter (q < ·) = ρ.extPositions j := by
          apply List.filter_eq_self.mpr
          intro z hz
          have hh := hf j (by simp) z hz
          simp only [Near, NearEq, if_true] at hh hq
          exact decide_eq_true (by omega)
        cases hh : (ρ.extPositions j).head? with
        | none =>
          simpa only [List.foldl_cons, Step, if_true, rightStep, hfp, hfq, hh]
            using ih ht p q c hp hq
        | some z =>
          simp only [List.foldl_cons, Step, if_true, rightStep, hfp, hfq, hh]
  have hHit (ρ : Context) (dir : Bool) (L x : ℕ) (hx : x ∈ ρ.extPositions L)
      (z : ℕ × ℕ) (hz : Near dir z.1 x) :
      NearEq dir (Step ρ dir z L).1 x ∧ (Step ρ dir z L).2 = z.2 + 1 := by
    have hs : (ρ.extPositions L).Pairwise (· ≤ ·) := by
      apply List.Pairwise.filter
      exact List.pairwise_lt_range.imp (fun hab => Nat.le_of_lt hab)
    cases dir
    · have hm : x ∈ (ρ.extPositions L).filter (· < z.1) := by
        simpa only [List.mem_filter, decide_eq_true_eq, Near, Bool.false_eq_true, if_false]
          using And.intro hx hz
      have hn := List.ne_nil_of_mem hm
      have hle := (hs.filter (· < z.1)).rel_getLast hm
      simp only [Step, Bool.false_eq_true, if_false, leftStep,
        List.getLast?_eq_some_getLast hn, NearEq]
      exact ⟨hle, True.intro⟩
    · have hm : x ∈ (ρ.extPositions L).filter (z.1 < ·) := by
        simpa only [List.mem_filter, decide_eq_true_eq, Near, if_true] using And.intro hx hz
      have hn := List.ne_nil_of_mem hm
      have hle := (hs.filter (z.1 < ·)).rel_head hm
      simp only [Step, if_true, rightStep, List.head?_eq_some_head hn, NearEq]
      exact ⟨hle, True.intro⟩
  have hSplit (L : ℕ) : ∀ ls : List ℕ, ls.Pairwise (· < ·) →
      (∀ j ∈ ls, j ≠ L) → ls.filter (· < L) ++ ls.filter (L < ·) = ls := by
    intro ls
    induction ls with
    | nil => intro _ _; simp
    | cons j ls ih =>
      intro hs hskip
      have ht := (List.pairwise_cons.mp hs).2
      have htSkip : ∀ i ∈ ls, i ≠ L := fun i hi => hskip i (by simp [hi])
      by_cases hj : j < L
      · simpa only [List.filter_cons, decide_eq_true hj, if_true, Bool.false_eq_true,
          decide_eq_false (show ¬ L < j by omega), if_false, List.cons_append]
          using congrArg (List.cons j) (ih ht htSkip)
      · have hLj : L < j := by have := hskip j (by simp); omega
        have hAll : ∀ i ∈ ls, L < i := by
          intro i hi
          have := (List.pairwise_cons.mp hs).1 i hi
          omega
        have hlt : ls.filter (· < L) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro i hi
          simp only [decide_eq_true_eq]
          have := hAll i hi
          omega
        have hgt : ls.filter (L < ·) = ls := by
          apply List.filter_eq_self.mpr
          intro i hi
          exact decide_eq_true (hAll i hi)
        simp only [List.filter_cons, decide_eq_false hj, Bool.false_eq_true, if_false,
          decide_eq_true hLj, if_true, hlt, hgt, List.nil_append]
  have hNearFold (ρ : Context) (dir : Bool) (x : ℕ) (ls : List ℕ)
      (hy : ∀ j ∈ ls, ∀ p ∈ ρ.extPositions j, Near dir p x)
      (z : ℕ × ℕ) (hz : Near dir z.1 x) :
      Near dir (ls.foldl (Step ρ dir) z).1 x := by
    cases dir
    · exact hEndLeft ρ x ls hy z hz
    · exact hEndRight ρ x ls hy z hz
  have hInsert (ρ : Context) (dir : Bool) (L x : ℕ)
      (hL : L ∈ ρ.levels) (hx : x ∈ ρ.extPositions L)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, Near dir p x)
      (ho : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, L < j →
        ∀ p ∈ ρ.extPositions j, Near dir x p)
      (ls : List ℕ) (hls : ls.Sublist (ρ.levelsOn (ρ.sideAt L) 0))
      (hskip : ∀ j ∈ ls, j ≠ L) (p : ℕ) (hp : Near dir p x) :
      ∃ ws : List ℕ, ws.Sublist (ρ.levelsOn (ρ.sideAt L) 0) ∧
        (ws.foldl (Step ρ dir) (p,0)).2 = (ls.foldl (Step ρ dir) (p,0)).2 + 1 := by
    let Y := ls.filter (· < L)
    let O := ls.filter (L < ·)
    have hs : ls.Pairwise (· < ·) := ((hSorted ρ).filter _).sublist hls
    have hY (j : ℕ) (hj : j ∈ Y) : j ∈ ls ∧ j < L := by
      simpa only [Y, List.mem_filter, decide_eq_true_eq] using hj
    have hO (j : ℕ) (hj : j ∈ O) : j ∈ ls ∧ L < j := by
      simpa only [O, List.mem_filter, decide_eq_true_eq] using hj
    have hYOn (j : ℕ) (hj : j ∈ Y) : j ∈ ρ.levelsOn (ρ.sideAt L) L := by
      have hmem := hls.subset (hY j hj).1
      have hside := (of_decide_eq_true (List.mem_filter.mp hmem).2).1
      exact List.mem_filter.mpr ⟨(List.mem_filter.mp hmem).1,
        by apply decide_eq_true; exact ⟨hside, Or.inr (hY j hj).2⟩⟩
    have hYPositions : ∀ j ∈ Y, ∀ z ∈ ρ.extPositions j, Near dir z x :=
      fun j hj z hz => hy j (hYOn j hj) z hz
    have hOPositions : ∀ j ∈ O, ∀ z ∈ ρ.extPositions j, Near dir x z :=
      fun j hj z hz => ho j (hls.subset (hO j hj).1) (hO j hj).2 z hz
    have hLOn : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by simp [levelsOn, hL]
    have hMid : (L :: O).Pairwise (· < ·) :=
      List.pairwise_cons.mpr ⟨fun j hj => (hO j hj).2, hs.filter _⟩
    have hCand : (Y ++ L :: O).Pairwise (· < ·) := by
      apply List.pairwise_append.mpr
      refine ⟨hs.filter _, hMid, ?_⟩
      intro i hi j hj
      have hiL := (hY i hi).2
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hiL
      · have hjL := (hO j hj).2
        omega
    have hSubset : Y ++ L :: O ⊆ ρ.levelsOn (ρ.sideAt L) 0 := by
      intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact hls.subset (hY j hj).1
      · rcases List.mem_cons.mp hj with rfl | hj
        · exact hLOn
        · exact hls.subset (hO j hj).1
    have hEq : (ρ.levelsOn (ρ.sideAt L) 0).filter (· ∈ Y ++ L :: O) = Y ++ L :: O := by
      apply (((hSorted ρ).filter _).filter _).eq_of_mem_iff hCand
      intro j
      exact ⟨fun hj => of_decide_eq_true (List.mem_filter.mp hj).2,
        fun hj => List.mem_filter.mpr ⟨hSubset hj, decide_eq_true hj⟩⟩
    have hSub : (Y ++ L :: O).Sublist (ρ.levelsOn (ρ.sideAt L) 0) := by
      rw [← hEq]
      exact List.filter_sublist
    let z := Y.foldl (Step ρ dir) (p,0)
    let w := Step ρ dir z L
    have hz : Near dir z.1 x := hNearFold ρ dir x Y hYPositions (p,0) hp
    have hw := hHit ρ dir L x hx z hz
    change NearEq dir w.1 x ∧ w.2 = z.2 + 1 at hw
    have hze : NearEq dir z.1 x := by
      cases dir <;> simp only [Near, NearEq, Bool.false_eq_true, if_false, if_true] at hz ⊢ <;> omega
    have hwEq : w = Shift (w.1, z.2) 1 := by
      apply Prod.ext
      · rfl
      · exact hw.2
    have hCounts : (O.foldl (Step ρ dir) w).2 = (O.foldl (Step ρ dir) z).2 + 1 := by
      rw [hwEq, hFoldShift]
      change (O.foldl (Step ρ dir) (w.1,z.2)).2 + 1 = _
      have hh := hFarFold ρ dir x O hOPositions w.1 z.1 z.2 hw.1 hze
      exact congrArg (fun n : ℕ => n + 1) hh
    refine ⟨Y ++ L :: O, hSub, ?_⟩
    have hsplit : Y ++ O = ls := hSplit L ls hs hskip
    rw [← hsplit, List.foldl_append, List.foldl_append, List.foldl_cons]
    exact hCounts
  let Pure (ρ : Context) (dir : Bool) (v : Side) (p : ℕ) :=
    if dir then ρ.rightExt v 0 p else ρ.leftExt v 0 p
  have hPureEq (ρ : Context) (dir : Bool) (v : Side) (p : ℕ) :
      Pure ρ dir v p = ((ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (Step ρ dir) (p,0)).2)).max?.getD 0 := by
    cases dir <;> simp only [Pure, Step, Bool.false_eq_true, if_false, if_true,
      leftExt_eq, rightExt_eq]
  have hPureGain (ρ : Context) (dir : Bool) (L x : ℕ)
      (hL : L ∈ ρ.levels) (hx : x ∈ ρ.extPositions L)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ z ∈ ρ.extPositions j, Near dir z x)
      (ho : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, L < j →
        ∀ z ∈ ρ.extPositions j, Near dir x z)
      (p : ℕ) (hp : Near dir p x) :
      Pure (erase ρ L) dir (ρ.sideAt L) p + 1 ≤ Pure ρ dir (ρ.sideAt L) p := by
    have hL1 := one_le_of_mem_levels hL
    have hEach (ls : List ℕ) (hls : ls.Sublist ((erase ρ L).levelsOn (ρ.sideAt L) 0)) :
        (ls.foldl (Step (erase ρ L) dir) (p,0)).2 + 1 ≤ Pure ρ dir (ρ.sideAt L) p := by
      have hmapped : (ls.map (up L)).Sublist (ρ.levelsOn (ρ.sideAt L) 0) := by
        have hh := (hls.map (up L)).trans (hSub ρ L hL (ρ.sideAt L) 0)
        simpa only [hUpZero L hL1] using hh
      have hskip : ∀ j ∈ ls.map (up L), j ≠ L := by
        intro j hj
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        dsimp only [up]
        split_ifs <;> omega
      obtain ⟨ws, hws, hcount⟩ := hInsert ρ dir L x hL hx hy ho
        (ls.map (up L)) hmapped hskip p hp
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn (ρ.sideAt L) 0).sublists.map
        (fun ls => (ls.foldl (Step ρ dir) (p,0)).2))
        (List.mem_map.mpr ⟨ws, List.mem_sublists.mpr hws, rfl⟩)
      rw [← hPureEq, hcount] at hv
      have hlevels : ∀ j ∈ ls, j ∈ (erase ρ L).levels :=
        fun j hj => (List.mem_filter.mp (hls.subset hj)).1
      have heq : ls.foldl (Step (erase ρ L) dir) (p,0) =
          (ls.map (up L)).foldl (Step ρ dir) (p,0) := by
        cases dir
        · exact hFoldLeft ρ L hL ls hlevels (p,0)
        · exact hFoldRight ρ L hL ls hlevels (p,0)
      simpa only [heq] using hv
    have hOne : 1 ≤ Pure ρ dir (ρ.sideAt L) p := by
      simpa only [List.foldl_nil, Nat.zero_add] using hEach [] (List.nil_sublist _)
    have hLe : Pure (erase ρ L) dir (ρ.sideAt L) p ≤ Pure ρ dir (ρ.sideAt L) p - 1 := by
      rw [hPureEq]
      apply getD_max?_le
      intro n hn
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hn
      have hh := hEach ls (List.mem_sublists.mp hls)
      omega
    omega
  have hChainGain (ρ : Context) (dir : Bool) (L x : ℕ)
      (hL : L ∈ ρ.levels) (hx : x ∈ ρ.extPositions L)
      (hc : ∀ p ∈ ρ.childPositions, Near dir p x)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ z ∈ ρ.extPositions j, Near dir z x)
      (ho : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, L < j →
        ∀ z ∈ ρ.extPositions j, Near dir x z)
      (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
      (erase ρ L).chainExt (ρ.sideAt L) p q + 1 ≤ ρ.chainExt (ρ.sideAt L) p q := by
    have hL1 := one_le_of_mem_levels hL
    cases dir
    · have hl := hPureGain ρ false L x hL hx hy ho p (hc p hp)
      have hr := hRightLe ρ L hL (ρ.sideAt L) 0 q
      simp only [Pure, Bool.false_eq_true, if_false, hUpZero L hL1] at hl hr
      dsimp only [chainExt]
      omega
    · have hr := hPureGain ρ true L x hL hx hy ho q (hc q hq)
      have hl := hLeftLe ρ L hL (ρ.sideAt L) 0 p
      simp only [Pure, if_true, hUpZero L hL1] at hl hr
      dsimp only [chainExt]
      omega
  have hCaps (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (L x : ℕ) (hL : L ∈ ρ.levels) (hx : x ∈ ρ.extPositions L)
      (dir : Bool) (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p)
      (ho : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, L < j →
        ∀ p ∈ ρ.extPositions j, if dir then x < p else p < x)
      (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
      ρ.cupLimit p q ≤ (norm ρ L).cupLimit p q ∧
      ρ.capLimit p q ≤ (norm ρ L).capLimit p q := by
    have hGain := hChainGain ρ dir L x hL hx hc hy ho p q hp hq
    have hE := (ctx_erase_level_bound_mono ρ L hL).1 p q
    change ρ.cupLimit p q ≤ (erase ρ L).cupLimit p q ∧
      ρ.capLimit p q ≤ (erase ρ L).capLimit p q at hE
    cases hs : ρ.sideAt L with
    | lower =>
      rw [hs] at hGain
      simp only [norm, hs]
      constructor
      · have hOwn := hE.1
        change ρ.cupLimit p q ≤ min (ρ.u - 1 - (erase ρ L).chainExt Side.lower p q)
          (ρ.k - 1 - (erase ρ L).joinExt Side.lower p q) at hOwn
        change min (ρ.u - 1 - ρ.chainExt Side.lower p q) (ρ.k - 1 - ρ.joinExt Side.lower p q) ≤
          min ((ρ.u - 1) - 1 - (erase ρ L).chainExt Side.lower p q)
            (ρ.k - 1 - (erase ρ L).joinExt Side.lower p q)
        dsimp only [cupLimit] at hOwn
        omega
      · simpa only [norm, hs] using hE.2
    | upper =>
      rw [hs] at hGain
      simp only [norm, hs]
      constructor
      · simpa only [norm, hs] using hE.1
      · have hOwn := hE.2
        change ρ.capLimit p q ≤ min (ρ.a - 1 - (erase ρ L).chainExt Side.upper p q)
          (ρ.k - 1 - (erase ρ L).joinExt Side.upper p q) at hOwn
        change min (ρ.a - 1 - ρ.chainExt Side.upper p q) (ρ.k - 1 - ρ.joinExt Side.upper p q) ≤
          min ((ρ.a - 1) - 1 - (erase ρ L).chainExt Side.upper p q)
            (ρ.k - 1 - (erase ρ L).joinExt Side.upper p q)
        dsimp only [capLimit] at hOwn
        omega
  have hErasePart (ρ : Context) (keep : List ℕ) (v : Side) (m L : ℕ) (hL : 1 ≤ L) :
      erase (ρ.part keep v m) (L+1) = (erase ρ L).part keep v m := by
    have hi (j : ℕ) : idx (ρ.maxima.length+1) (L+1) (j+1) = idx ρ.maxima.length L j + 1 := by
      dsimp [idx]; split_ifs <;> omega
    have hnew : idx (ρ.maxima.length+1) (L+1) 1 = 1 := by simp [idx]; omega
    have hm : (m :: ρ.maxima).eraseIdx (L+1-1) = m :: ρ.maxima.eraseIdx (L-1) := by
      rw [show L+1-1 = (L-1)+1 by omega, List.eraseIdx_cons_succ]
    have hw : (erase (ρ.part keep v m) (L+1)).word = ((erase ρ L).part keep v m).word := by
      change ((ρ.part keep v m).word.map (letter (m :: ρ.maxima).length (L+1))) =
        (List.range (erase ρ L).word.length).map (fun p => match (erase ρ L).letterAt p with
          | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 v
          | Letter.ext j w => Letter.ext (j+1) w)
      rw [hLen]
      simp only [part, List.map_map, List.length_cons, Function.comp_def]
      apply List.map_congr_left
      intro p _
      rw [hLetter]
      cases ρ.letterAt p with
      | child => by_cases hp : p ∈ keep <;> simp [hp, letter, hnew]
      | ext j w => simp only [letter, hi]
    change Context.mk ρ.a ρ.u ρ.k _ ((m :: ρ.maxima).eraseIdx (L+1-1)) =
      Context.mk ρ.a ρ.u ρ.k _ (m :: ρ.maxima.eraseIdx (L-1))
    rw [hm]
    exact congrArg (fun w => Context.mk ρ.a ρ.u ρ.k w (m :: ρ.maxima.eraseIdx (L-1))) hw
  have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ x j w, (ρ.part keep v m).letterAt x = Letter.ext j w → 1 ≤ j := by
    intro x j w hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep v m)
        (show (ρ.part keep v m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep v m hxl he] at hx
      split at hx
      · cases hx
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep v m hxl he] at hx
      cases hx
      omega
  have hNextBoundary (ρ : Context)
      (hPos : ∀ p j w, ρ.letterAt p = Letter.ext j w → 1 ≤ j)
      (L x : ℕ) (hL : L ∈ ρ.levels) (dir : Bool)
      (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p)
      (keep : List ℕ) (v : Side) (m : ℕ) :
      (∀ p ∈ (ρ.part keep v m).childPositions, if dir then p < x else x < p) ∧
      (∀ j ∈ (ρ.part keep v m).levelsOn ((ρ.part keep v m).sideAt (L+1)) (L+1),
        ∀ p ∈ (ρ.part keep v m).extPositions j, if dir then p < x else x < p) := by
    have hL1 := one_le_of_mem_levels hL
    constructor
    · intro p hp
      rw [part_childPositions] at hp
      exact hc p (List.mem_filter.mp hp).1
    · intro j hj p hp
      have hj1 := (one_le_of_mem_levelsOn hj).1
      by_cases he : j = 1
      · subst j
        rw [part_extPositions_one hPos keep v m] at hp
        exact hc p (List.mem_filter.mp hp).1
      · let i := j-1
        have hi : 1 ≤ i := by dsimp [i]; omega
        have he : j = i+1 := by dsimp [i]; omega
        rw [he] at hj hp
        have hjLevel : i+1 ∈ (ρ.part keep v m).levels := (List.mem_filter.mp hj).1
        rw [part_levels] at hjLevel
        have hiLevel : i ∈ ρ.levels := by
          rcases List.mem_cons.mp hjLevel with h | h
          · omega
          · obtain ⟨z, hz, hzi⟩ := List.mem_map.mp h
            have hz' : z = i := by omega
            simpa only [hz'] using hz
        have hjc : (ρ.part keep v m).sideAt (i+1) = (ρ.part keep v m).sideAt (L+1) ∧
            (L+1 = 0 ∨ i+1 < L+1) := of_decide_eq_true (List.mem_filter.mp hj).2
        rw [part_sideAt_succ ρ keep v m hi, part_sideAt_succ ρ keep v m hL1] at hjc
        have hiOn : i ∈ ρ.levelsOn (ρ.sideAt L) L := by
          apply List.mem_filter.mpr
          refine ⟨hiLevel, ?_⟩
          apply decide_eq_true
          exact ⟨hjc.1, Or.inr (by omega)⟩
        rw [part_extPositions_succ ρ keep v m hi] at hp
        exact hy i hiOn p hp
  have hNormPart (ρ : Context) (keep : List ℕ) (v : Side) (m L : ℕ) (hL : 1 ≤ L) :
      norm (ρ.part keep v m) (L+1) = (norm ρ L).part keep v m := by
    have hs := part_sideAt_succ ρ keep v m hL
    have he := hErasePart ρ keep v m L hL
    simp only [norm, hs, he]
    cases hh : ρ.sideAt L <;> rfl
  have hNextOlder (ρ : Context) (L x : ℕ) (hL : L ∈ ρ.levels) (dir : Bool)
      (ho : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, L < j →
        ∀ p ∈ ρ.extPositions j, if dir then x < p else p < x)
      (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ j ∈ (ρ.part keep v m).levelsOn ((ρ.part keep v m).sideAt (L+1)) 0,
        L+1 < j → ∀ p ∈ (ρ.part keep v m).extPositions j,
          if dir then x < p else p < x := by
    intro j hj hLj p hp
    have hL1 := one_le_of_mem_levels hL
    let i := j-1
    have hi : 1 ≤ i := by dsimp [i]; omega
    have he : j = i+1 := by dsimp [i]; omega
    rw [he] at hj hp hLj
    have hjLevel : i+1 ∈ (ρ.part keep v m).levels := (List.mem_filter.mp hj).1
    rw [part_levels] at hjLevel
    have hiLevel : i ∈ ρ.levels := by
      rcases List.mem_cons.mp hjLevel with h | h
      · omega
      · obtain ⟨z, hz, hzi⟩ := List.mem_map.mp h
        have hz' : z = i := by omega
        simpa only [hz'] using hz
    have hjc : (ρ.part keep v m).sideAt (i+1) = (ρ.part keep v m).sideAt (L+1) ∧
        (0 = 0 ∨ i+1 < 0) := of_decide_eq_true (List.mem_filter.mp hj).2
    rw [part_sideAt_succ ρ keep v m hi, part_sideAt_succ ρ keep v m hL1] at hjc
    have hiOn : i ∈ ρ.levelsOn (ρ.sideAt L) 0 :=
      List.mem_filter.mpr ⟨hiLevel, by simp [hjc.1]⟩
    rw [part_extPositions_succ ρ keep v m hi] at hp
    exact ho i hiOn (by omega) p hp
  have hBase (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (L x : ℕ) (hL : L ∈ ρ.levels) (hx : x ∈ ρ.extPositions L)
      (dir : Bool) (hc : ∀ p ∈ ρ.childPositions, if dir then p < x else x < p)
      (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p)
      (ho : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, L < j →
        ∀ p ∈ ρ.extPositions j, if dir then x < p else p < x) : ρ.base ≤ (norm ρ L).base := by
    rw [base_eq_baseOf, base_eq_baseOf, hNormChild]
    cases hh : ρ.childPositions.head? with
    | none => exact le_rfl
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      have h := hCaps ρ hPos L x hL hx dir hc hy ho p p hp hp
      simpa only [hNormK] using baseOf_mono (k := ρ.k) h.1 h.2
  have hFuel : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      ∀ (L x : ℕ), L ∈ ρ.levels → x ∈ ρ.extPositions L → ∀ dir : Bool,
      (∀ p ∈ ρ.childPositions, if dir then p < x else x < p) →
      (∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j,
        if dir then p < x else x < p) →
      (∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, L < j →
        ∀ p ∈ ρ.extPositions j, if dir then x < p else p < x) →
      boundFuel fuel ρ ≤ boundFuel fuel (norm ρ L) := by
    intro fuel
    induction fuel with
    | zero => intro ρ hPos L x hL hx dir hc hy ho; exact le_rfl
    | succ fuel ih =>
      intro ρ hPos L x hL hx dir hc hy ho
      have hL1 := one_le_of_mem_levels hL
      have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
          boundFuel fuel (ρ.part keep v m) ≤ boundFuel fuel ((norm ρ L).part keep v m) := by
        have hn : L+1 ∈ (ρ.part keep v m).levels := by
          rw [part_levels]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L,hL,rfl⟩)
        have hx' : x ∈ (ρ.part keep v m).extPositions (L+1) := by
          rw [part_extPositions_succ ρ keep v m hL1]
          exact hx
        have hd := hNextBoundary ρ hPos L x hL dir hc hy keep v m
        have h := ih (ρ.part keep v m) (hPartPositive ρ keep v m) (L+1) x hn hx' dir hd.1 hd.2
          (hNextOlder ρ L x hL dir ho keep v m)
        rw [hNormPart ρ keep v m L hL1] at h
        exact h
      simp only [boundFuel, hNormRuns, hNormChild, hNormBlocks, hNormK]
      split_ifs
      · exact hBase ρ hPos L x hL hx dir hc hy ho
      · apply Ctx.getD_max?_le_of_forall
        intro x hx
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨keep, hkeep, d, hd, hx⟩ := hx
        rcases hx with rfl | rfl
        · refine ⟨_, ?_, Nat.add_le_add (hParts _ _ _) (hParts _ _ _)⟩
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
          exact ⟨keep, hkeep, d, hd, Or.inl rfl⟩
        · refine ⟨_, ?_, Nat.add_le_add (hParts _ _ _) (hParts _ _ _)⟩
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
          exact ⟨keep, hkeep, d, hd, Or.inr rfl⟩
  have hResult :
      (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
        σ.cupLimit p q ≤ (norm σ N).cupLimit p q ∧ σ.capLimit p q ≤ (norm σ N).capLimit p q) ∧
      (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel (norm σ N)) ∧ σ.bound ≤ (norm σ N).bound := by
    refine ⟨fun p hp q hq => hCaps σ hpositive N x hN hx rightward hchildren hyounger holder p q hp hq,
      fun fuel => hFuel fuel σ hpositive N x hN hx rightward hchildren hyounger holder, ?_⟩
    simpa only [bound, hNormChild] using
      hFuel (σ.childPositions.length+1) σ hpositive N x hN hx rightward hchildren hyounger holder

  have hDepthNorm : (norm σ N).maxima.length = σ.maxima.length - 1 := by
    cases hs : σ.sideAt N <;> simpa only [norm, hs] using hDepth σ N hN
  have hTransport : ∀ j ∈ (norm σ N).levels,
      up N j ∈ σ.levels ∧ up N j ≠ N ∧
        (norm σ N).extPositions j = σ.extPositions (up N j) ∧
        (norm σ N).sideAt j = σ.sideAt (up N j) ∧
        (norm σ N).maximumAt j = σ.maximumAt (up N j) := by
    intro j hj
    have he : j ∈ (erase σ N).levels := by
      cases hs : σ.sideAt N <;> simpa only [norm, hs] using hj
    have hne : up N j ≠ N := by dsimp only [up]; split_ifs <;> omega
    refine ⟨(hLive σ N j hN he).2.2, hne, ?_, ?_, ?_⟩
    · cases hs : σ.sideAt N <;> simpa only [norm, hs] using hExt σ N j hN he
    · cases hs : σ.sideAt N <;> simpa only [norm, hs] using hSide σ N j hN he
    · cases hs : σ.sideAt N <;> simpa only [norm, hs] using hMaximum σ N j hN he
  have hOpposite : ∀ t : Side, σ.sideAt N ≠ t → ∀ p,
      (norm σ N).leftExt t 0 p = σ.leftExt t 0 p ∧
        (norm σ N).rightExt t 0 p = σ.rightExt t 0 p := by
    intro t ht p
    constructor
    · cases hs : σ.sideAt N <;> simpa only [norm, hs] using hEraseLeft σ N hN t ht p
    · cases hs : σ.sideAt N <;> simpa only [norm, hs] using hEraseRight σ N hN t ht p
  have hPositiveNorm : ∀ p j v, (norm σ N).letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    have he : (erase σ N).letterAt p = Letter.ext j v := by
      cases hs : σ.sideAt N <;> simpa only [norm, hs] using hp
    exact hErasePositive σ N hN hpositive p j v he
  exact ⟨hNormChild σ N, hDepthNorm, hTransport, hOpposite, hPositiveNorm, hResult⟩

end ErdosSzekeres
