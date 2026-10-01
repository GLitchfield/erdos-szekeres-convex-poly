import ESBlueprint.B.CtxBoundaryMarkerUpperNormalize
import ESBlueprint.B.CtxSingletonPartBoundEqThreshold
import ESBlueprint.B.CtxBoundLeMergeSameSideLevels
import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank
import ESBlueprint.B.CtxBoundZeroOfUnitGlobalAxis
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential
import ESBlueprint.B.CtxBoundReverse

set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

namespace ErdosSzekeres

open Ctx Ctx.Context MergeLevels

/-- The first global child singleton attains the recursive bound of every legal uniform neither-marked one-level root whose opposite global is exactly three and marker global is at least three. Arbitrary run lengths/marker multiplicities and either marker side; actual old marker, child at both word ends and at least two runs. Explicit opposite singleton maximum k-2, selected complement maximum one, and raw decomposable threshold leaf. Source absorbed-marker upper is H-1 for H=min(G,k-m); exposed leaf is one; complementary prefix merge retains G and has maximum m+1 and marked-first/exposed-last word. The reflected unrestricted legal-root lower supplies H-2 when H>=3, while H=2 needs only nonnegative complement. Uses no run-contraction or singleton-exchange conjecture. Supplies a new neither-marked N_ends subcase; larger opposite globals and the degenerate global-two class remain open.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_one_level_root_first_singleton_cut_attains_of_neither_marked_opposite_global_three (G k m : ℕ) (hk : 3 ≤ k) (hG : 3 ≤ G) (hGk : G ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k-2) (side : Ctx.Side) (word : List Ctx.Letter) (hletters : ∀ z ∈ word, z = Ctx.Letter.child ∨ z = Ctx.Letter.ext 1 side) (hmarker : Ctx.Letter.ext 1 side ∈ word) (hfirst : word.head? = some Ctx.Letter.child) (hlast : word.getLast? = some Ctx.Letter.child) (hchild : Ctx.Letter.child ∈ word) : let σ : Ctx.Context := { a := match side with | Ctx.Side.lower => 3 | Ctx.Side.upper => G, u := match side with | Ctx.Side.lower => G | Ctx.Side.upper => 3, k := k, word := word, maxima := [m] }; 2 ≤ σ.numRuns → ∃ p : ℕ, σ.childPositions.head? = some p ∧ 1 ≤ k-2 ∧ k-2 ≤ k-2 ∧ σ.bound ≤ decomposableThreshold ((σ.part [p] (match side with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower) (k-2)).capLimit p p+1) ((σ.part [p] (match side with | Ctx.Side.lower => Ctx.Side.upper | Ctx.Side.upper => Ctx.Side.lower) (k-2)).cupLimit p p+1) k + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) side (k-1-(k-2))).bound := by
  classical
  let A : ℕ := 3
  have hA : 3 ≤ A := by rfl
  have hAk : A ≤ k := hk
  have hAbsorb (σ : Ctx.Context)
      (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
      (N x : ℕ) (hpair : MergeLevels.Inv σ N)
      (hsole : σ.extPositions N = [x])
      (hbefore : ∃ y ∈ σ.extPositions (N + 1), y < x)
      (hchildren : ∀ p ∈ σ.childPositions, x < p)
      (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j, x < p)
      (holdest : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, j ≤ N + 1)
      (hglobal : (match σ.sideAt N with
        | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k) :
      let τ : Ctx.Context :=
        { σ with
          a := match σ.sideAt N with
            | Ctx.Side.lower => σ.a | Ctx.Side.upper => σ.a - 1
          u := match σ.sideAt N with
            | Ctx.Side.lower => σ.u - 1 | Ctx.Side.upper => σ.u
          word := σ.word.map (fun z => match z with
            | Ctx.Letter.child => Ctx.Letter.child
            | Ctx.Letter.ext j v => if j ≤ N then Ctx.Letter.ext j v
                else Ctx.Letter.ext (j - 1) v)
          maxima := σ.maxima.take (N - 1) ++
            [max (σ.maximumAt N) (σ.maximumAt (N + 1) + 1)] ++
            σ.maxima.drop (N + 1) }
      (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
        σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q) ∧
      (∀ fuel, Ctx.Context.boundFuel fuel σ = Ctx.Context.boundFuel fuel τ) ∧
      σ.bound = τ.bound := by
    classical
    let letter (L : ℕ) : Letter → Letter := fun x => match x with
      | Letter.child => Letter.child
      | Letter.ext j s => if j ≤ L then Letter.ext j s else Letter.ext (j - 1) s
    let norm (ρ : Context) (L : ℕ) : Context :=
      { ρ with
        a := match ρ.sideAt L with | Side.lower => ρ.a | Side.upper => ρ.a - 1
        u := match ρ.sideAt L with | Side.lower => ρ.u - 1 | Side.upper => ρ.u
        word := ρ.word.map (letter L)
        maxima := ρ.maxima.take (L - 1) ++ [max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)] ++
          ρ.maxima.drop (L + 1) }
    let lv (ρ : Context) (i : ℕ) : ℕ → Bool := fun p => match ρ.letterAt p with
      | Letter.ext j _ => decide (j = i)
      | Letter.child => false
    let up (L j : ℕ) := if j < L then j else j + 1
    let upTop (L t : ℕ) := if t ≤ L then t else t + 1
    let img (L j x : ℕ) : Prop := (j < L ∧ x = j) ∨ (j = L ∧ (x = L ∨ x = L + 1)) ∨ (L < j ∧ x = j + 1)
    change (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
        σ.cupLimit p q = (norm σ N).cupLimit p q ∧
        σ.capLimit p q = (norm σ N).capLimit p q) ∧
      (∀ fuel, boundFuel fuel σ = boundFuel fuel (norm σ N)) ∧
        σ.bound = (norm σ N).bound
    -- basic transport ----------------------------------------------------------
    have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
      simp only [levels, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; omega
      · intro hj; exact ⟨j - 1, by omega, by omega⟩
    have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
      unfold levels
      exact List.pairwise_lt_range.map (fun x => x + 1) (fun a b h => Nat.add_lt_add_right h 1)
    have hLen (ρ : Context) (L : ℕ) : (norm ρ L).word.length = ρ.word.length := by
      simp only [norm, List.length_map]
    have hLetter (ρ : Context) (L p : ℕ) : (norm ρ L).letterAt p = letter L (ρ.letterAt p) := by
      simp only [norm, letterAt, List.getElem?_map]
      cases ρ.word[p]? <;> rfl
    have hIsChild (ρ : Context) (L p : ℕ) :
        (norm ρ L).letterAt p = Letter.child ↔ ρ.letterAt p = Letter.child := by
      rw [hLetter]
      cases ρ.letterAt p with
      | child => simp [letter]
      | ext j v => by_cases hj : j ≤ L <;> simp [letter, hj]
    have hChild (ρ : Context) (L : ℕ) : (norm ρ L).childPositions = ρ.childPositions := by
      simp only [childPositions, hLen, hIsChild]
    have hRuns (ρ : Context) (L : ℕ) : (norm ρ L).numRuns = ρ.numRuns := by
      simp only [numRuns, hLen, ne_eq, hIsChild]
    have hBlocks (ρ : Context) (L : ℕ) : (norm ρ L).blocks = ρ.blocks := by
      simp only [blocks, hChild]
    have hK (ρ : Context) (L : ℕ) : (norm ρ L).k = ρ.k := rfl
    have hDepth (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        (norm ρ L).maxima.length = ρ.maxima.length - 1 := by
      obtain ⟨h1, h2, -, -⟩ := hL
      simp only [norm, List.length_append, List.length_take, List.length_singleton, List.length_drop]
      omega
    have hNormLevel (ρ : Context) (L : ℕ) (hL : Inv ρ L) (j : ℕ) (hj : j ∈ (norm ρ L).levels) :
        1 ≤ j ∧ j + 1 ≤ ρ.maxima.length := by
      have h := (hLevelMem (norm ρ L) j).mp hj
      rw [hDepth ρ L hL] at h
      omega
    -- levels and letters ---------------------------------------------------------
    have hExtLv (ρ : Context) (i : ℕ) : ρ.extPositions i = (List.range ρ.word.length).filter (lv ρ i) := by
      unfold extPositions
      apply List.filter_congr
      intro p _
      cases h : ρ.letterAt p with
      | child => simp [lv, h]
      | ext j v => simp [lv, h]
    have hExtMerged (ρ : Context) (L : ℕ) :
        (norm ρ L).extPositions L =
          (List.range ρ.word.length).filter (fun p => lv ρ L p || lv ρ (L + 1) p) := by
      unfold extPositions
      rw [hLen]
      apply List.filter_congr
      intro p _
      rw [hLetter]
      cases h : ρ.letterAt p with
      | child => simp [lv, h, letter]
      | ext j v =>
        by_cases hj : j ≤ L
        · simp only [letter, hj, if_true, lv, h]
          by_cases hjL : j = L <;> simp [hjL] <;> omega
        · simp only [letter, hj, if_false, lv, h]
          by_cases hjL : j = L + 1 <;> simp [hjL] <;> omega
    have hExtNe (ρ : Context) (L j : ℕ) (hj1 : 1 ≤ j) (hjL : j ≠ L) :
        (norm ρ L).extPositions j = ρ.extPositions (up L j) := by
      unfold extPositions
      rw [hLen]
      apply List.filter_congr
      intro p _
      rw [hLetter]
      cases h : ρ.letterAt p with
      | child => simp [letter]
      | ext i v =>
        by_cases hi : i ≤ L <;> by_cases hjl : j < L <;> simp [letter, hi, hjl, up] <;> omega
    have hMemMerged (ρ : Context) (L p : ℕ) (hp : p ∈ ρ.extPositions L) :
        p ∈ (norm ρ L).extPositions L := by
      rw [hExtMerged, List.mem_filter]
      rw [hExtLv, List.mem_filter] at hp
      exact ⟨hp.1, by simp [hp.2]⟩
    have hSideL (ρ : Context) (L : ℕ) (hL : Inv ρ L) : (norm ρ L).sideAt L = ρ.sideAt L := by
      obtain ⟨-, -, h3, -⟩ := hL
      rcases hh : ((norm ρ L).extPositions L).head? with _ | p
      · have hρ : (ρ.extPositions L).head? = none := by
          cases hh2 : (ρ.extPositions L).head? with
          | none => rfl
          | some q =>
            exfalso
            have hq := hMemMerged ρ L q (List.mem_of_mem_head? (Option.mem_def.mpr hh2))
            rw [List.head?_eq_none_iff] at hh
            rw [hh] at hq
            exact List.not_mem_nil hq
        simp only [sideAt, hh, hρ]
      · have hp : p ∈ (norm ρ L).extPositions L := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        rw [hExtMerged, List.mem_filter] at hp
        cases hlet : ρ.letterAt p with
        | child => simp [lv, hlet] at hp
        | ext j v =>
          have hj : j = L ∨ j = L + 1 := by
            have := hp.2
            simp only [lv, hlet, Bool.or_eq_true, decide_eq_true_eq] at this
            exact this
          have hv := h3 p j v hlet hj
          rw [← hv]
          simp only [sideAt, hh, hLetter, hlet]
          by_cases hjL : j ≤ L <;> simp [letter, hjL]
    have hSideNe (ρ : Context) (L j : ℕ) (hj1 : 1 ≤ j) (hjL : j ≠ L) :
        (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
      unfold sideAt
      rw [hExtNe ρ L j hj1 hjL]
      cases hh : (ρ.extPositions (up L j)).head? with
      | none => rfl
      | some p =>
        dsimp only
        rw [hLetter]
        cases ρ.letterAt p with
        | child => rfl
        | ext i v => by_cases hi : i ≤ L <;> simp [letter, hi]
    have hMax (ρ : Context) (L : ℕ) (hL : Inv ρ L) (j : ℕ) (hj1 : 1 ≤ j) :
        (norm ρ L).maximumAt j =
          if j < L then ρ.maximumAt j else if j = L then max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)
          else ρ.maximumAt (j + 1) := by
      obtain ⟨h1, h2, -, -⟩ := hL
      simp only [maximumAt, norm]
      rw [getElem?_merge ρ.maxima L (j - 1) _ h1 h2]
      by_cases hjl : j < L
      · simp [hjl, show j - 1 < L - 1 by omega]
      · by_cases hjL : j = L
        · subst hjL; simp
        · simp [hjl, hjL, show ¬ j - 1 < L - 1 by omega, show j - 1 ≠ L - 1 by omega,
            show j - 1 + 1 = j by omega]
    have hUpMono (L i j : ℕ) (h : i < j) : up L i < up L j := by
      dsimp [up]
      split_ifs <;> omega
    have hUpZero (L : ℕ) (hL : 1 ≤ L) : up L 0 = 0 := by
      simp [up, show 0 < L by omega]
    have hLive (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
        (hj : j ∈ (norm ρ L).levels) :
        1 ≤ j ∧ j < ρ.maxima.length ∧ up L j ∈ ρ.levels := by
      have hh := hNormLevel ρ L hL j hj
      refine ⟨hh.1, by omega, ?_⟩
      apply (hLevelMem ρ _).mpr
      dsimp [up]
      split_ifs <;> omega
    have hSide (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
        (hj : j ∈ (norm ρ L).levels) :
        (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
      have hj1 := (hNormLevel ρ L hL j hj).1
      by_cases he : j = L
      · subst j
        rw [hSideL ρ L hL]
        simpa only [up, lt_self_iff_false, if_false] using hL.2.2.2
      · exact hSideNe ρ L j hj1 he
    have hNoMerged (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (v : Side) (hv : v ≠ ρ.sideAt L) (top j : ℕ)
        (hj : j ∈ (norm ρ L).levelsOn v top) : j ≠ L := by
      intro he
      subst j
      have hc : (norm ρ L).sideAt L = v ∧ (top = 0 ∨ L < top) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      rw [hSideL ρ L hL] at hc
      exact hv hc.1.symm
    have hMaximum (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
        (hj : j ∈ (norm ρ L).levels) (hne : j ≠ L) :
        (norm ρ L).maximumAt j = ρ.maximumAt (up L j) := by
      rw [hMax ρ L hL j ((hNormLevel ρ L hL j hj).1)]
      by_cases hjl : j < L <;> simp [hjl, hne, up]
    have hOppLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
        (hv : v ≠ ρ.sideAt L) (top : ℕ) :
        (((norm ρ L).levelsOn v top).map (up L)) = ρ.levelsOn v (up L top) := by
      have hs : (((norm ρ L).levelsOn v top).map (up L)).Pairwise (· < ·) :=
        ((hSorted (norm ρ L)).filter _).map (up L) (fun i j hij => hUpMono L i j hij)
      apply hs.eq_of_mem_iff ((hSorted ρ).filter _)
      intro i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        have hjl := (List.mem_filter.mp hj).1
        have hjc : (norm ρ L).sideAt j = v ∧ (top = 0 ∨ j < top) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        apply List.mem_filter.mpr
        refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
        apply decide_eq_true
        refine ⟨?_, ?_⟩
        · rw [← hSide ρ L j hL hjl]
          exact hjc.1
        · rcases hjc.2 with rfl | hlt
          · exact Or.inl (hUpZero L hL.1)
          · exact Or.inr (hUpMono L j top hlt)
      · intro hi
        have hil := (List.mem_filter.mp hi).1
        have hic : ρ.sideAt i = v ∧ (up L top = 0 ∨ i < up L top) :=
          of_decide_eq_true (List.mem_filter.mp hi).2
        have hiL : i ≠ L := by
          intro he
          subst i
          exact hv hic.1.symm
        let j := if i < L then i else i-1
        have hLr : 1 ≤ L ∧ L ≤ ρ.maxima.length := ⟨hL.1, by omega⟩
        have hir := (hLevelMem ρ i).mp hil
        have hjr : 1 ≤ j ∧ j < ρ.maxima.length ∧ up L j = i := by
          dsimp [j, up]
          split_ifs <;> omega
        have hjl : j ∈ (norm ρ L).levels := by
          apply (hLevelMem (norm ρ L) j).mpr
          rw [hDepth ρ L hL]
          omega
        apply List.mem_map.mpr
        refine ⟨j, ?_, hjr.2.2⟩
        apply List.mem_filter.mpr
        refine ⟨hjl, ?_⟩
        apply decide_eq_true
        refine ⟨?_, ?_⟩
        · rw [hSide ρ L j hL hjl, hjr.2.2]
          exact hic.1
        · rcases hic.2 with hzero | hlt
          · left
            by_contra hne
            have h := hUpMono L 0 top (by omega)
            rw [hUpZero L hLr.1, hzero] at h
            omega
          · right
            by_contra hn
            have hm : up L top ≤ up L j := by
              rcases lt_or_eq_of_le (show top ≤ j by omega) with hm | he
              · exact (hUpMono L top j hm).le
              · rw [he]
            rw [hjr.2.2] at hm
            omega
    have hFoldNormLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (norm ρ L).levels ∧ j ≠ L) → ∀ z,
        ls.foldl (leftStep (norm ρ L)) z =
          (ls.map (up L)).foldl (leftStep ρ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; rfl
      | cons j ls ih =>
        intro hj z
        simp only [List.foldl_cons, List.map_cons, leftStep,
          hExtNe ρ L j ((hLevelMem (norm ρ L) j).mp (hj j (by simp)).1).1
            (hj j (by simp)).2]
        exact ih (fun i hi => hj i (by simp [hi])) _
    have hFoldNormRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (norm ρ L).levels ∧ j ≠ L) → ∀ z,
        ls.foldl (rightStep (norm ρ L)) z =
          (ls.map (up L)).foldl (rightStep ρ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; rfl
      | cons j ls ih =>
        intro hj z
        simp only [List.foldl_cons, List.map_cons, rightStep,
          hExtNe ρ L j ((hLevelMem (norm ρ L) j).mp (hj j (by simp)).1).1
            (hj j (by simp)).2]
        exact ih (fun i hi => hj i (by simp [hi])) _
    have hOppLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
        (hv : v ≠ ρ.sideAt L) (top p : ℕ) :
        (norm ρ L).leftExt v top p = ρ.leftExt v (up L top) p := by
      rw [leftExt_eq, leftExt_eq, ← hOppLevels ρ L hL v hv top,
        List.sublists_map, List.map_map]
      apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
      apply List.map_congr_left
      intro ls hls
      exact congrArg Prod.snd (hFoldNormLeft ρ L hL ls
        (fun j hj => ⟨(List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1,
          hNoMerged ρ L hL v hv top j ((List.mem_sublists.mp hls).subset hj)⟩) (p,0))
    have hOppRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
        (hv : v ≠ ρ.sideAt L) (top p : ℕ) :
        (norm ρ L).rightExt v top p = ρ.rightExt v (up L top) p := by
      rw [rightExt_eq, rightExt_eq, ← hOppLevels ρ L hL v hv top,
        List.sublists_map, List.map_map]
      apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
      apply List.map_congr_left
      intro ls hls
      exact congrArg Prod.snd (hFoldNormRight ρ L hL ls
        (fun j hj => ⟨(List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1,
          hNoMerged ρ L hL v hv top j ((List.mem_sublists.mp hls).subset hj)⟩) (p,0))
    have hOppChain (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
        (hv : v ≠ ρ.sideAt L) (p q : ℕ) :
        (norm ρ L).chainExt v p q = ρ.chainExt v p q := by
      simp only [chainExt, hOppLeft ρ L hL v hv, hOppRight ρ L hL v hv,
        hUpZero L hL.1]
    have hOppJoin (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
        (hv : v ≠ ρ.sideAt L) (p q : ℕ) :
        (norm ρ L).joinExt v p q = ρ.joinExt v p q := by
      have hl : (((norm ρ L).levelsOn v 0).map (up L)) = ρ.levelsOn v 0 := by
        simpa only [hUpZero L hL.1] using hOppLevels ρ L hL v hv 0
      rw [joinExt, joinExt, hOppChain ρ L hL v hv, ← hl, List.map_map]
      congr 1
      apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
      apply List.map_congr_left
      intro j hj
      rw [hOppLeft ρ L hL v hv, hOppRight ρ L hL v hv,
        hMaximum ρ L j hL (List.mem_filter.mp hj).1
          (hNoMerged ρ L hL v hv 0 j hj)]
      rfl
    have hYoungLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        (norm ρ L).levelsOn (ρ.sideAt L) L = ρ.levelsOn (ρ.sideAt L) L := by
      apply ((hSorted (norm ρ L)).filter _).eq_of_mem_iff ((hSorted ρ).filter _)
      intro j
      constructor
      · intro hj
        have hjl := (List.mem_filter.mp hj).1
        have hjc : (norm ρ L).sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        have hjlt : j < L := by omega
        have hj1 := (hNormLevel ρ L hL j hjl).1
        have hs := hSideNe ρ L j hj1 (by omega)
        have hu : up L j = j := by simp [up, hjlt]
        rw [hu] at hs
        exact List.mem_filter.mpr ⟨by
          have hh := (hLive ρ L j hL hjl).2.2
          simpa only [hu] using hh,
          by apply decide_eq_true; exact ⟨hs.symm.trans hjc.1, Or.inr hjlt⟩⟩
      · intro hj
        have hjl := (List.mem_filter.mp hj).1
        have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        have hjlt : j < L := by omega
        have hj1 := ((hLevelMem ρ j).mp hjl).1
        have hjn : j ∈ (norm ρ L).levels := by
          apply (hLevelMem (norm ρ L) j).mpr
          rw [hDepth ρ L hL]
          omega
        have hs := hSideNe ρ L j hj1 (by omega)
        have hu : up L j = j := by simp [up, hjlt]
        rw [hu] at hs
        exact List.mem_filter.mpr ⟨hjn,
          by apply decide_eq_true; exact ⟨hs.trans hjc.1, Or.inr hjlt⟩⟩
    have hSourcePairLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
        ρ.levelsOn (ρ.sideAt L) 0 = ρ.levelsOn (ρ.sideAt L) L ++ [L, L + 1] := by
      have hLs : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
        apply List.mem_filter.mpr
        exact ⟨(hLevelMem ρ L).mpr ⟨hL.1, by omega⟩, by simp⟩
      have hL1s : L + 1 ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
        apply List.mem_filter.mpr
        exact ⟨(hLevelMem ρ (L + 1)).mpr ⟨by omega, hL.2.1⟩,
          by apply decide_eq_true; exact ⟨hL.2.2.2.symm, Or.inl rfl⟩⟩
      have hs : (ρ.levelsOn (ρ.sideAt L) L ++ [L, L + 1]).Pairwise (· < ·) := by
        apply List.pairwise_append.mpr
        refine ⟨(hSorted ρ).filter _, by simp, ?_⟩
        intro i hi j hj
        have hc : ρ.sideAt i = ρ.sideAt L ∧ (L = 0 ∨ i < L) :=
          of_decide_eq_true (List.mem_filter.mp hi).2
        have hiL : i < L := by omega
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> omega
      apply ((hSorted ρ).filter _).eq_of_mem_iff hs
      intro j
      constructor
      · intro hj
        have hjL := ht j hj
        by_cases he : j = L
        · simp [he]
        by_cases he1 : j = L + 1
        · simp [he1]
        apply List.mem_append.mpr
        left
        apply List.mem_filter.mpr
        refine ⟨(List.mem_filter.mp hj).1, ?_⟩
        apply decide_eq_true
        have hc : ρ.sideAt j = ρ.sideAt L ∧ (0 = 0 ∨ j < 0) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        exact ⟨hc.1, Or.inr (by omega)⟩
      · intro hj
        rcases List.mem_append.mp hj with hj | hj
        · apply List.mem_filter.mpr
          refine ⟨(List.mem_filter.mp hj).1, ?_⟩
          apply decide_eq_true
          have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          exact ⟨hc.1, Or.inl rfl⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl
          · exact hLs
          · exact hL1s
    have hSourceOwnLevels (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) :
        ρ.levelsOn (ρ.sideAt L) 0 = ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
      have hLs : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by simp [levelsOn, hL]
      have hs : (ρ.levelsOn (ρ.sideAt L) L ++ [L]).Pairwise (· < ·) := by
        apply List.pairwise_append.mpr
        refine ⟨(hSorted ρ).filter _, by simp, ?_⟩
        intro i hi j hj
        have he : j = L := by simpa using hj
        subst j
        have hc : ρ.sideAt i = ρ.sideAt L ∧ (L = 0 ∨ i < L) :=
          of_decide_eq_true (List.mem_filter.mp hi).2
        have hL1 := one_le_of_mem_levels hL
        omega
      apply ((hSorted ρ).filter _).eq_of_mem_iff hs
      intro j
      constructor
      · intro hj
        have hjL := ht j hj
        by_cases he : j = L
        · simp [he]
        · apply List.mem_append.mpr
          left
          apply List.mem_filter.mpr
          refine ⟨(List.mem_filter.mp hj).1, ?_⟩
          apply decide_eq_true
          have hc : ρ.sideAt j = ρ.sideAt L ∧ (0 = 0 ∨ j < 0) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          exact ⟨hc.1, Or.inr (by omega)⟩
      · intro hj
        rcases List.mem_append.mp hj with hj | hj
        · apply List.mem_filter.mpr
          refine ⟨(List.mem_filter.mp hj).1, ?_⟩
          apply decide_eq_true
          have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          exact ⟨hc.1, Or.inl rfl⟩
        · have he : j = L := by simpa using hj
          simpa [levelsOn, he] using hLs
    have hNormOwnLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
        (norm ρ L).levelsOn (ρ.sideAt L) 0 =
          ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
      have hNL : L ∈ (norm ρ L).levels := by
        apply (hLevelMem (norm ρ L) L).mpr
        rw [hDepth ρ L hL]
        omega
      have hAll : ∀ j ∈ (norm ρ L).levelsOn ((norm ρ L).sideAt L) 0, j ≤ L := by
        intro j hj
        have hjl := (List.mem_filter.mp hj).1
        have hjc : (norm ρ L).sideAt j = (norm ρ L).sideAt L ∧ (0 = 0 ∨ j < 0) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        have hh : up L j ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
          apply List.mem_filter.mpr
          refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
          apply decide_eq_true
          rw [← hSide ρ L j hL hjl, ← hSideL ρ L hL]
          exact ⟨hjc.1, Or.inl rfl⟩
        have hm := ht (up L j) hh
        dsimp [up] at hm
        split_ifs at hm <;> omega
      have hh := hSourceOwnLevels (norm ρ L) L hNL hAll
      rw [hSideL ρ L hL, hYoungLevels ρ L hL] at hh
      exact hh
    have hYoungFoldLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        ∀ (ls : List ℕ), ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists → ∀ (z : ℕ × ℕ),
        ls.foldl (leftStep (norm ρ L)) z = ls.foldl (leftStep ρ) z := by
      intro ls
      have hGeneral : ∀ (ls : List ℕ),
          (∀ j ∈ ls, j ∈ ρ.levelsOn (ρ.sideAt L) L) → ∀ (z : ℕ × ℕ),
          ls.foldl (leftStep (norm ρ L)) z = ls.foldl (leftStep ρ) z := by
        intro ls
        induction ls with
        | nil => intro _ z; rfl
        | cons j ls ih =>
          intro hj z
          have hjl := (List.mem_filter.mp (hj j (by simp))).1
          have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp (hj j (by simp))).2
          have hjlt : j < L := by omega
          have hj1 := ((hLevelMem ρ j).mp hjl).1
          have he := hExtNe ρ L j hj1 (by omega)
          rw [show up L j = j by simp [up, hjlt]] at he
          simp only [List.foldl_cons, leftStep, he]
          exact ih (fun i hi => hj i (by simp [hi])) _
      intro hls z
      exact hGeneral ls (fun j hj => (List.mem_sublists.mp hls).subset hj) z
    have hDecomposeSublists (Y T ls : List ℕ) (hls : ls ∈ (Y ++ T).sublists) :
        ∃ ys ∈ Y.sublists, ∃ ts ∈ T.sublists, ls = ys ++ ts := by
      rw [List.sublists_append, List.bind_eq_flatMap] at hls
      obtain ⟨ts, hts, hh⟩ := List.mem_flatMap.mp hls
      obtain ⟨ys, hys, he⟩ := List.mem_map.mp hh
      exact ⟨ys, hys, ts, hts, he.symm⟩
    have hFoldCountLeft (ρ : Context) : ∀ (ls : List ℕ) (z : ℕ × ℕ),
        (ls.foldl (leftStep ρ) z).2 ≤ z.2 + ls.length := by
      intro ls
      induction ls with
      | nil => intro z; simp
      | cons j ls ih =>
        intro z
        have hstep : (leftStep ρ z j).2 ≤ z.2 + 1 := by
          cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? <;>
            simp [leftStep, hh]
        have hh := ih (leftStep ρ z j)
        simp only [List.foldl_cons, List.length_cons]
        omega
    have hLeftStepAdd (ρ : Context) (j e c : ℕ)
        (hex : ∃ y ∈ ρ.extPositions j, y < e) :
        (leftStep ρ (e,c) j).2 = c + 1 := by
      cases hh : ((ρ.extPositions j).filter (· < e)).getLast? with
      | some y => simp [leftStep, hh]
      | none =>
        obtain ⟨y, hy, hye⟩ := hex
        have hm : y ∈ (ρ.extPositions j).filter (· < e) := by simp [hy, hye]
        rw [List.getLast?_eq_none_iff] at hh
        rw [hh] at hm
        exact False.elim (List.not_mem_nil hm)
    have hFoldBoundary (ρ : Context) (x : ℕ) (dir : Bool) :
        ∀ (ls : List ℕ),
        (∀ j ∈ ls, ∀ y ∈ ρ.extPositions j, if dir then y < x else x < y) →
        ∀ z : ℕ × ℕ, (if dir then z.1 < x else x < z.1) →
        (if dir then (ls.foldl (leftStep ρ) z).1 < x
          else x < (ls.foldl (leftStep ρ) z).1) ∧
        (if dir then (ls.foldl (rightStep ρ) z).1 < x
          else x < (ls.foldl (rightStep ρ) z).1) := by
      intro ls
      induction ls with
      | nil => intro _ z hz; exact ⟨hz,hz⟩
      | cons j ls ih =>
        intro hy z hz
        have ht := fun i hi y hiy => hy i (List.mem_cons_of_mem j hi) y hiy
        constructor
        · cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? with
          | none => simpa only [List.foldl_cons, leftStep, hh] using (ih ht z hz).1
          | some y =>
            have hm := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
            have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
            simpa only [List.foldl_cons, leftStep, hh] using (ih ht (y,z.2+1) hyx).1
        · cases hh : ((ρ.extPositions j).filter (z.1 < ·)).head? with
          | none => simpa only [List.foldl_cons, rightStep, hh] using (ih ht z hz).2
          | some y =>
            have hm := List.mem_of_mem_head? (Option.mem_def.mpr hh)
            have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
            simpa only [List.foldl_cons, rightStep, hh] using (ih ht (y,z.2+1) hyx).2
    have hSourceLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hbefore : ∃ y ∈ ρ.extPositions (L + 1), y < x)
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p : ℕ) (hp : p ∈ ρ.childPositions) :
        ρ.leftExt (ρ.sideAt L) 0 p = ρ.leftExt (ρ.sideAt L) L p + 2 := by
      let Y := ρ.levelsOn (ρ.sideAt L) L
      have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          ((ys ++ [L, L + 1]).foldl (leftStep ρ) (p,0)).2 =
            (ys.foldl (leftStep ρ) (p,0)).2 + 2 := by
        let z := ys.foldl (leftStep ρ) (p,0)
        have hz := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).1
        change x < z.1 at hz
        have hs : leftStep ρ z L = (x, z.2 + 1) := by
          simp [leftStep, hsingle, hz]
        rw [List.foldl_append]
        change (leftStep ρ (leftStep ρ z L) (L + 1)).2 = z.2 + 2
        rw [hs, hLeftStepAdd ρ (L + 1) x (z.2 + 1) hbefore]
      have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          (ys.foldl (leftStep ρ) (p,0)).2 + 2 ≤ ρ.leftExt (ρ.sideAt L) 0 p := by
        have hsub : ys ++ [L, L + 1] ∈ (ρ.levelsOn (ρ.sideAt L) 0).sublists := by
          rw [hSourcePairLevels ρ L hL ht]
          exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
        have hh : ((ys ++ [L, L + 1]).foldl (leftStep ρ) (p,0)).2 ≤
            ρ.leftExt (ρ.sideAt L) 0 p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L, L + 1], hsub, rfl⟩)
        rwa [hAdd ys hys] at hh
      apply le_antisymm
      · rw [leftExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
        rw [hSourcePairLevels ρ L hL ht] at hls
        obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L, L + 1] ls hls
        have hcount := hFoldCountLeft ρ ts (ys.foldl (leftStep ρ) (p,0))
        have hlen : ts.length ≤ 2 := by
          simpa using (List.mem_sublists.mp hts).length_le
        have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
            ρ.leftExt (ρ.sideAt L) L p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
        rw [List.foldl_append]
        omega
      · have h2 : 2 ≤ ρ.leftExt (ρ.sideAt L) 0 p := by
          simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
        have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤ ρ.leftExt (ρ.sideAt L) 0 p - 2 := by
          rw [leftExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
          have hh := hLe ys hys
          omega
        omega
    have hNormLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p : ℕ) (hp : p ∈ ρ.childPositions) :
        (norm ρ L).leftExt (ρ.sideAt L) 0 p = ρ.leftExt (ρ.sideAt L) L p + 1 := by
      let Y := ρ.levelsOn (ρ.sideAt L) L
      have hx : x ∈ (norm ρ L).extPositions L :=
        hMemMerged ρ L x (by simp [hsingle])
      have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          ((ys ++ [L]).foldl (leftStep (norm ρ L)) (p,0)).2 =
            (ys.foldl (leftStep ρ) (p,0)).2 + 1 := by
        let z := ys.foldl (leftStep ρ) (p,0)
        have hz := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).1
        change x < z.1 at hz
        rw [List.foldl_append, hYoungFoldLeft ρ L hL ys hys]
        change (leftStep (norm ρ L) z L).2 = z.2 + 1
        exact hLeftStepAdd (norm ρ L) L z.1 z.2 ⟨x, hx, hz⟩
      have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          (ys.foldl (leftStep ρ) (p,0)).2 + 1 ≤
            (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
        have hsub : ys ++ [L] ∈ ((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists := by
          rw [hNormOwnLevels ρ L hL ht]
          exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
        have hh : ((ys ++ [L]).foldl (leftStep (norm ρ L)) (p,0)).2 ≤
            (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L], hsub, rfl⟩)
        rwa [hAdd ys hys] at hh
      apply le_antisymm
      · rw [leftExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
        rw [hNormOwnLevels ρ L hL ht] at hls
        obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
        have hcount := hFoldCountLeft (norm ρ L) ts
          (ys.foldl (leftStep (norm ρ L)) (p,0))
        rw [hYoungFoldLeft ρ L hL ys hys] at hcount
        have hlen : ts.length ≤ 1 := by
          simpa using (List.mem_sublists.mp hts).length_le
        have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
            ρ.leftExt (ρ.sideAt L) L p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
        rw [List.foldl_append, hYoungFoldLeft ρ L hL ys hys]
        omega
      · have h1 : 1 ≤ (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
          simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
        have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤
            (norm ρ L).leftExt (ρ.sideAt L) 0 p - 1 := by
          rw [leftExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
          have hh := hLe ys hys
          omega
        omega
    have hYoungFoldRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        ∀ (ls : List ℕ), ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists → ∀ (z : ℕ × ℕ),
        ls.foldl (rightStep (norm ρ L)) z = ls.foldl (rightStep ρ) z := by
      intro ls
      have hGeneral : ∀ (ls : List ℕ),
          (∀ j ∈ ls, j ∈ ρ.levelsOn (ρ.sideAt L) L) → ∀ (z : ℕ × ℕ),
          ls.foldl (rightStep (norm ρ L)) z = ls.foldl (rightStep ρ) z := by
        intro ls
        induction ls with
        | nil => intro _ z; rfl
        | cons j ls ih =>
          intro hj z
          have hjl := (List.mem_filter.mp (hj j (by simp))).1
          have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp (hj j (by simp))).2
          have hjlt : j < L := by omega
          have hj1 := ((hLevelMem ρ j).mp hjl).1
          have he := hExtNe ρ L j hj1 (by omega)
          rw [show up L j = j by simp [up, hjlt]] at he
          simp only [List.foldl_cons, rightStep, he]
          exact ih (fun i hi => hj i (by simp [hi])) _
      intro hls z
      exact hGeneral ls (fun j hj => (List.mem_sublists.mp hls).subset hj) z
    have hMergedRightStep (ρ : Context) (L x : ℕ)
        (hsingle : ρ.extPositions L = [x]) (z : ℕ × ℕ) (hx : x < z.1) :
        rightStep (norm ρ L) z L = rightStep ρ z (L + 1) := by
      have he : ((norm ρ L).extPositions L).filter (z.1 < ·) =
          (ρ.extPositions (L + 1)).filter (z.1 < ·) := by
        have hs₁ : ((norm ρ L).extPositions L).Pairwise (· < ·) :=
          List.pairwise_lt_range.filter _
        have hs₂ : (ρ.extPositions (L + 1)).Pairwise (· < ·) :=
          List.pairwise_lt_range.filter _
        apply (hs₁.filter _).eq_of_mem_iff (hs₂.filter _)
        intro p
        rw [hExtMerged, hExtLv]
        simp only [List.mem_filter, Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨hp, hpL | hpO⟩, hzp⟩
          · have hm : p ∈ ρ.extPositions L := by
              rw [hExtLv]
              exact List.mem_filter.mpr ⟨hp, hpL⟩
            have hpx : p = x := by simpa [hsingle] using hm
            omega
          · exact ⟨⟨hp, hpO⟩, hzp⟩
        · rintro ⟨⟨hp, hpO⟩, hzp⟩
          exact ⟨⟨hp, Or.inr hpO⟩, hzp⟩
      simp only [rightStep, he]
    have hNewRightStep (ρ : Context) (L x : ℕ)
        (hsingle : ρ.extPositions L = [x]) (z : ℕ × ℕ) (hx : x < z.1) :
        rightStep ρ z L = z := by
      rcases z with ⟨e,c⟩
      simp only at hx
      simp [rightStep, hsingle, show ¬ e < x by omega]
    have hOwnRight (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p : ℕ) (hp : p ∈ ρ.childPositions) :
        ρ.rightExt (ρ.sideAt L) 0 p = (norm ρ L).rightExt (ρ.sideAt L) 0 p := by
      let Y := ρ.levelsOn (ρ.sideAt L) L
      have hTail (ys ts : List ℕ) (hys : ys ∈ Y.sublists)
          (hts : ts ∈ [L, L + 1].sublists) :
          ∃ us ∈ [L].sublists,
            (ys ++ ts).foldl (rightStep ρ) (p,0) =
              (ys ++ us).foldl (rightStep (norm ρ L)) (p,0) := by
        let z := ys.foldl (rightStep ρ) (p,0)
        have hz := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).2
        change x < z.1 at hz
        have hcases : ts = [] ∨ ts = [L] ∨ ts = [L + 1] ∨ ts = [L, L + 1] := by
          simpa [List.sublists_cons] using hts
        rcases hcases with rfl | rfl | rfl | rfl
        · refine ⟨[], by simp, ?_⟩
          simpa only [List.append_nil] using (hYoungFoldRight ρ L hL ys hys (p,0)).symm
        · refine ⟨[], by simp, ?_⟩
          rw [List.foldl_append, List.append_nil, hYoungFoldRight ρ L hL ys hys]
          change rightStep ρ z L = z
          exact hNewRightStep ρ L x hsingle z hz
        · refine ⟨[L], by simp [List.sublists_cons], ?_⟩
          rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
          change rightStep ρ z (L + 1) = rightStep (norm ρ L) z L
          exact (hMergedRightStep ρ L x hsingle z hz).symm
        · refine ⟨[L], by simp [List.sublists_cons], ?_⟩
          rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
          change rightStep ρ (rightStep ρ z L) (L + 1) = rightStep (norm ρ L) z L
          rw [hNewRightStep ρ L x hsingle z hz]
          exact (hMergedRightStep ρ L x hsingle z hz).symm
      have hBack (ys us : List ℕ) (hys : ys ∈ Y.sublists)
          (hus : us ∈ [L].sublists) :
          ∃ ts ∈ [L, L + 1].sublists,
            (ys ++ us).foldl (rightStep (norm ρ L)) (p,0) =
              (ys ++ ts).foldl (rightStep ρ) (p,0) := by
        let z := ys.foldl (rightStep ρ) (p,0)
        have hz := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).2
        change x < z.1 at hz
        have hcases : us = [] ∨ us = [L] := by simpa [List.sublists_cons] using hus
        rcases hcases with rfl | rfl
        · refine ⟨[], by simp, ?_⟩
          simpa only [List.append_nil] using hYoungFoldRight ρ L hL ys hys (p,0)
        · refine ⟨[L + 1], by simp [List.sublists_cons], ?_⟩
          rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
          change rightStep (norm ρ L) z L = rightStep ρ z (L + 1)
          exact hMergedRightStep ρ L x hsingle z hz
      apply le_antisymm
      · rw [rightExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
        rw [hSourcePairLevels ρ L hL ht] at hls
        obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L, L + 1] ls hls
        obtain ⟨us, hus, he⟩ := hTail ys ts hys hts
        have hsub : ys ++ us ∈ ((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists := by
          rw [hNormOwnLevels ρ L hL ht]
          exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.mem_sublists.mp hus))
        rw [he, rightExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ us, hsub, rfl⟩)
      · rw [rightExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
        rw [hNormOwnLevels ρ L hL ht] at hls
        obtain ⟨ys, hys, us, hus, rfl⟩ := hDecomposeSublists Y [L] ls hls
        obtain ⟨ts, hts, he⟩ := hBack ys us hys hus
        have hsub : ys ++ ts ∈ (ρ.levelsOn (ρ.sideAt L) 0).sublists := by
          rw [hSourcePairLevels ρ L hL ht]
          exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.mem_sublists.mp hts))
        rw [he, rightExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ ts, hsub, rfl⟩)
    have hTopFilter (ρ : Context) (v : Side) (top : ℕ) (htop : 1 ≤ top) :
        ρ.levelsOn v top = (ρ.levelsOn v 0).filter (· < top) := by
      simp only [levelsOn, List.filter_filter]
      apply List.filter_congr
      intro j _
      simp [show top ≠ 0 by omega, Bool.and_comm]
    have hLevelsAtTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) :
        (norm ρ L).levelsOn (ρ.sideAt L) top = ρ.levelsOn (ρ.sideAt L) top := by
      rw [hTopFilter (norm ρ L) (ρ.sideAt L) top htop, hNormOwnLevels ρ L hL ht,
        hTopFilter ρ (ρ.sideAt L) top htop, hSourcePairLevels ρ L hL ht,
        List.filter_append, List.filter_append]
      simp [show ¬ L < top by omega, show ¬ L + 1 < top by omega]
    have hMidLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
        ρ.levelsOn (ρ.sideAt L) (L + 1) = ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
      rw [hTopFilter ρ (ρ.sideAt L) (L + 1) (by omega),
        hSourcePairLevels ρ L hL ht, List.filter_append]
      have hf : (ρ.levelsOn (ρ.sideAt L) L).filter (· < L + 1) =
          ρ.levelsOn (ρ.sideAt L) L := by
        apply List.filter_eq_self.mpr
        intro j hj
        apply decide_eq_true
        have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        omega
      rw [hf]
      simp
    have hYoungLeftTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) (p : ℕ) :
        (norm ρ L).leftExt (ρ.sideAt L) top p = ρ.leftExt (ρ.sideAt L) top p := by
      rw [leftExt_eq, leftExt_eq, hLevelsAtTop ρ L hL ht top htop htL]
      apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
      apply List.map_congr_left
      intro ls hls
      have hs : ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists :=
        List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans
          (levelsOn_sublist_of_le ρ (ρ.sideAt L) htop htL))
      exact congrArg Prod.snd (hYoungFoldLeft ρ L hL ls hs (p,0))
    have hYoungRightTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) (p : ℕ) :
        (norm ρ L).rightExt (ρ.sideAt L) top p = ρ.rightExt (ρ.sideAt L) top p := by
      rw [rightExt_eq, rightExt_eq, hLevelsAtTop ρ L hL ht top htop htL]
      apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
      apply List.map_congr_left
      intro ls hls
      have hs : ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists :=
        List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans
          (levelsOn_sublist_of_le ρ (ρ.sideAt L) htop htL))
      exact congrArg Prod.snd (hYoungFoldRight ρ L hL ls hs (p,0))
    have hMidLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p : ℕ) (hp : p ∈ ρ.childPositions) :
        ρ.leftExt (ρ.sideAt L) (L + 1) p = ρ.leftExt (ρ.sideAt L) L p + 1 := by
      let Y := ρ.levelsOn (ρ.sideAt L) L
      have hx : x ∈ ρ.extPositions L := by simp [hsingle]
      have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          ((ys ++ [L]).foldl (leftStep ρ) (p,0)).2 =
            (ys.foldl (leftStep ρ) (p,0)).2 + 1 := by
        let z := ys.foldl (leftStep ρ) (p,0)
        have hz := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).1
        change x < z.1 at hz
        rw [List.foldl_append]
        change (leftStep ρ z L).2 = z.2 + 1
        exact hLeftStepAdd ρ L z.1 z.2 ⟨x, hx, hz⟩
      have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          (ys.foldl (leftStep ρ) (p,0)).2 + 1 ≤
            ρ.leftExt (ρ.sideAt L) (L + 1) p := by
        have hsub : ys ++ [L] ∈ (ρ.levelsOn (ρ.sideAt L) (L + 1)).sublists := by
          rw [hMidLevels ρ L hL ht]
          exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
        have hh : ((ys ++ [L]).foldl (leftStep ρ) (p,0)).2 ≤
            ρ.leftExt (ρ.sideAt L) (L + 1) p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L], hsub, rfl⟩)
        rwa [hAdd ys hys] at hh
      apply le_antisymm
      · rw [leftExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
        rw [hMidLevels ρ L hL ht] at hls
        obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
        have hcount := hFoldCountLeft ρ ts
          (ys.foldl (leftStep ρ) (p,0))
        have hlen : ts.length ≤ 1 := by
          simpa using (List.mem_sublists.mp hts).length_le
        have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
            ρ.leftExt (ρ.sideAt L) L p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
        rw [List.foldl_append]
        omega
      · have h1 : 1 ≤ ρ.leftExt (ρ.sideAt L) (L + 1) p := by
          simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
        have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤
            ρ.leftExt (ρ.sideAt L) (L + 1) p - 1 := by
          rw [leftExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
          have hh := hLe ys hys
          omega
        omega
    have hMidRight (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p : ℕ) (hp : p ∈ ρ.childPositions) :
        ρ.rightExt (ρ.sideAt L) (L + 1) p = ρ.rightExt (ρ.sideAt L) L p := by
      let Y := ρ.levelsOn (ρ.sideAt L) L
      apply le_antisymm
      · rw [rightExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
        rw [hMidLevels ρ L hL ht] at hls
        obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
        have hboundary := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).2
        change x < (ys.foldl (rightStep ρ) (p,0)).1 at hboundary
        have hcases : ts = [] ∨ ts = [L] := by simpa [List.sublists_cons] using hts
        have hprefix : (ys.foldl (rightStep ρ) (p,0)).2 ≤
            ρ.rightExt (ρ.sideAt L) L p := by
          rw [rightExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
        rcases hcases with rfl | rfl
        · simpa only [List.append_nil] using hprefix
        · rw [List.foldl_append]
          change (rightStep ρ (ys.foldl (rightStep ρ) (p,0)) L).2 ≤ _
          rw [hNewRightStep ρ L x hsingle _ hboundary]
          exact hprefix
      · rw [rightExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
        have hsub : ys ∈ (ρ.levelsOn (ρ.sideAt L) (L + 1)).sublists := by
          rw [hMidLevels ρ L hL ht]
          exact List.mem_sublists.mpr (by
            simpa only [List.append_nil] using
              ((List.mem_sublists.mp hys).append (List.nil_sublist [L])))
        rw [rightExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hsub, rfl⟩)
    have hOwnChain (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hbefore : ∃ y ∈ ρ.extPositions (L + 1), y < x)
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
        ρ.chainExt (ρ.sideAt L) p q = (norm ρ L).chainExt (ρ.sideAt L) p q + 1 := by
      have hl := hSourceLeft ρ L x hL hsingle hbefore hc hy ht p hp
      have hn := hNormLeft ρ L x hL hsingle hc hy ht p hp
      have hr := hOwnRight ρ L x hL hsingle hc hy ht q hq
      unfold chainExt
      omega
    have hMaxAppend (A B : List ℕ) :
        ((A ++ B).max?).getD 0 = max (A.max?.getD 0) (B.max?.getD 0) := by
      apply le_antisymm
      · apply getD_max?_le
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact (le_getD_max?_of_mem hz).trans (le_max_left _ _)
        · exact (le_getD_max?_of_mem hz).trans (le_max_right _ _)
      · apply max_le
        · apply getD_max?_le_of_forall
          intro z hz
          exact ⟨z, List.mem_append_left _ hz, le_rfl⟩
        · apply getD_max?_le_of_forall
          intro z hz
          exact ⟨z, List.mem_append_right _ hz, le_rfl⟩
    have hMaxSingle (z : ℕ) : ([z].max?).getD 0 = z := by simp
    have hMaxPair (z w : ℕ) : ([z,w].max?).getD 0 = max z w := by
      simpa only [List.singleton_append, hMaxSingle] using hMaxAppend [z] [w]
    have hOwnJoin (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hbefore : ∃ y ∈ ρ.extPositions (L + 1), y < x)
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
        ρ.joinExt (ρ.sideAt L) p q =
          max ((norm ρ L).chainExt (ρ.sideAt L) p q + 1)
            ((norm ρ L).joinExt (ρ.sideAt L) p q) := by
      let f := fun j => ρ.leftExt (ρ.sideAt L) j p +
        ρ.rightExt (ρ.sideAt L) j q + ρ.maximumAt j
      let g := fun j => (norm ρ L).leftExt (ρ.sideAt L) j p +
        (norm ρ L).rightExt (ρ.sideAt L) j q + (norm ρ L).maximumAt j
      have hYoungMap :
          (ρ.levelsOn (ρ.sideAt L) L).map g =
            (ρ.levelsOn (ρ.sideAt L) L).map f := by
        apply List.map_congr_left
        intro j hj
        have hj1 := one_le_of_mem_levels (List.mem_filter.mp hj).1
        have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        have hjL : j < L := by have := hL.1; omega
        dsimp [f,g]
        rw [hYoungLeftTop ρ L hL ht j hj1 (by omega) p,
          hYoungRightTop ρ L hL ht j hj1 (by omega) q,
          hMax ρ L hL j hj1]
        simp only [hjL, if_true]
      have hMergedValue : g L = max (f L) (f (L + 1)) := by
        dsimp [f,g]
        rw [hYoungLeftTop ρ L hL ht L hL.1 le_rfl p,
          hYoungRightTop ρ L hL ht L hL.1 le_rfl q,
          hMax ρ L hL L hL.1,
          hMidLeft ρ L x hL hsingle hc hy ht p hp,
          hMidRight ρ L x hL hsingle hc hy ht q hq]
        simp only [lt_self_iff_false, if_false, if_true]
        omega
      change max (ρ.chainExt (ρ.sideAt L) p q)
          (((ρ.levelsOn (ρ.sideAt L) 0).map f).max?.getD 0) =
        max ((norm ρ L).chainExt (ρ.sideAt L) p q + 1)
          (max ((norm ρ L).chainExt (ρ.sideAt L) p q)
            ((((norm ρ L).levelsOn (ρ.sideAt L) 0).map g).max?.getD 0))
      rw [hOwnChain ρ L x hL hsingle hbefore hc hy ht p q hp hq,
        hSourcePairLevels ρ L hL ht, hNormOwnLevels ρ L hL ht,
        List.map_append, List.map_append, hMaxAppend, hMaxAppend, hYoungMap]
      simp only [List.map_cons, List.map_nil, hMaxPair, hMaxSingle]
      rw [← hMergedValue]
      omega
    have hCaps (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hbefore : ∃ y ∈ ρ.extPositions (L + 1), y < x)
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (hG : (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k)
        (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
        ρ.cupLimit p q = (norm ρ L).cupLimit p q ∧
        ρ.capLimit p q = (norm ρ L).capLimit p q := by
      have hc' := hOwnChain ρ L x hL hsingle hbefore hc hy ht p q hp hq
      have hj' := hOwnJoin ρ L x hL hsingle hbefore hc hy ht p q hp hq
      cases hs : ρ.sideAt L with
      | lower =>
        rw [hs] at hc' hj' hG
        change ρ.u ≤ ρ.k at hG
        have hOC := hOppChain ρ L hL Side.upper (by simp [hs]) p q
        have hOJ := hOppJoin ρ L hL Side.upper (by simp [hs]) p q
        have ha : (norm ρ L).a = ρ.a := by simp only [norm, hs]
        have hu : (norm ρ L).u = ρ.u - 1 := by simp only [norm, hs]
        unfold cupLimit capLimit
        rw [ha, hu, hK, hc', hj', hOC, hOJ]
        constructor
        · omega
        · rfl
      | upper =>
        rw [hs] at hc' hj' hG
        change ρ.a ≤ ρ.k at hG
        have hOC := hOppChain ρ L hL Side.lower (by simp [hs]) p q
        have hOJ := hOppJoin ρ L hL Side.lower (by simp [hs]) p q
        have ha : (norm ρ L).a = ρ.a - 1 := by simp only [norm, hs]
        have hu : (norm ρ L).u = ρ.u := by simp only [norm, hs]
        unfold cupLimit capLimit
        rw [ha, hu, hK, hc', hj', hOC, hOJ]
        constructor
        · rfl
        · omega
    have hNormPart (ρ : Context) (keep : List ℕ) (v : Side) (m L : ℕ) (hL1 : 1 ≤ L) :
        norm (ρ.part keep v m) (L + 1) = (norm ρ L).part keep v m := by
      have hw : (norm (ρ.part keep v m) (L + 1)).word = ((norm ρ L).part keep v m).word := by
        change ((ρ.part keep v m).word.map (letter (L + 1))) =
          (List.range (norm ρ L).word.length).map (fun p => match (norm ρ L).letterAt p with
            | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 v
            | Letter.ext j w => Letter.ext (j + 1) w)
        rw [hLen]
        simp only [part, List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro p _
        rw [hLetter]
        cases ρ.letterAt p with
        | child => by_cases hp : p ∈ keep <;> simp [hp, letter]
        | ext j w =>
          by_cases hj : j ≤ L
          · simp [letter, hj]
          · simp [letter, hj, show j - 1 + 1 = j by omega]
      have e1 : (m :: ρ.maxima).take (L + 1 - 1) = m :: ρ.maxima.take (L - 1) := by
        rw [show L + 1 - 1 = (L - 1) + 1 by omega, List.take_succ_cons]
      have e2 : (m :: ρ.maxima).drop (L + 1 + 1) = ρ.maxima.drop (L + 1) := by
        rw [List.drop_succ_cons]
      have e3 : (ρ.part keep v m).maximumAt (L + 1) = ρ.maximumAt L := by
        simp only [maximumAt, part_maxima]
        rw [show L + 1 - 1 = (L - 1) + 1 by omega, List.getElem?_cons_succ]
      have e4 : (ρ.part keep v m).maximumAt (L + 1 + 1) = ρ.maximumAt (L + 1) := by
        simp only [maximumAt, part_maxima]
        rw [show L + 1 + 1 - 1 = (L + 1 - 1) + 1 by omega, List.getElem?_cons_succ]
      have hmx : (norm (ρ.part keep v m) (L + 1)).maxima = ((norm ρ L).part keep v m).maxima := by
        show (m :: ρ.maxima).take (L + 1 - 1) ++
            [max ((ρ.part keep v m).maximumAt (L + 1)) ((ρ.part keep v m).maximumAt (L + 1 + 1) + 1)] ++
            (m :: ρ.maxima).drop (L + 1 + 1) =
          m :: (ρ.maxima.take (L - 1) ++ [max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)] ++ ρ.maxima.drop (L + 1))
        rw [e1, e2, e3, e4]
        rfl
      have ha : (norm (ρ.part keep v m) (L + 1)).a = ((norm ρ L).part keep v m).a := by
        change (match (ρ.part keep v m).sideAt (L + 1) with
            | Side.lower => ρ.a | Side.upper => ρ.a - 1) =
          (match ρ.sideAt L with | Side.lower => ρ.a | Side.upper => ρ.a - 1)
        rw [part_sideAt_succ ρ keep v m hL1]
      have hu : (norm (ρ.part keep v m) (L + 1)).u = ((norm ρ L).part keep v m).u := by
        change (match (ρ.part keep v m).sideAt (L + 1) with
            | Side.lower => ρ.u - 1 | Side.upper => ρ.u) =
          (match ρ.sideAt L with | Side.lower => ρ.u - 1 | Side.upper => ρ.u)
        rw [part_sideAt_succ ρ keep v m hL1]
      exact ctx_ext ha hu rfl hw hmx
    have hInvPart (ρ : Context) (L : ℕ) (hL : Inv ρ L) (keep : List ℕ) (v : Side) (m : ℕ) :
        Inv (ρ.part keep v m) (L + 1) := by
      obtain ⟨h1, h2, h3, h4⟩ := hL
      refine ⟨by omega, by simp only [part_maxima, List.length_cons]; omega, ?_, ?_⟩
      · intro p j w hp hj
        rw [part_sideAt_succ ρ keep v m h1]
        by_cases hplen : p < ρ.word.length
        · cases hlet : ρ.letterAt p with
          | child =>
            rw [part_letterAt_of_child ρ keep v m hplen hlet] at hp
            by_cases hk : p ∈ keep
            · simp [hk] at hp
            · simp only [hk, if_false, Letter.ext.injEq] at hp
              obtain ⟨hj1, -⟩ := hp
              omega
          | ext i u =>
            rw [part_letterAt_of_ext ρ keep v m hplen hlet, Letter.ext.injEq] at hp
            obtain ⟨rfl, rfl⟩ := hp
            exact h3 p i u hlet (by omega)
        · rw [letterAt_of_length_le _ (by rw [part_word_length]; omega)] at hp
          cases hp
      · rw [part_sideAt_succ ρ keep v m h1, part_sideAt_succ ρ keep v m (by omega : 1 ≤ L + 1)]
        exact h4
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
    have hNextTerminal (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (keep : List ℕ) (v : Side) (m : ℕ) :
        ∀ j ∈ (ρ.part keep v m).levelsOn ((ρ.part keep v m).sideAt (L+1)) 0, j ≤ L+1+1 := by
      intro j hj
      have hj1 := (one_le_of_mem_levelsOn hj).1
      have hL1 := one_le_of_mem_levels hL
      by_cases he : j = 1
      · omega
      · let i := j-1
        have hi : 1 ≤ i := by dsimp [i]; omega
        have he : j = i+1 := by dsimp [i]; omega
        rw [he] at hj ⊢
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
        have := ht i hiOn
        omega
    have hBase (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hbefore : ∃ y ∈ ρ.extPositions (L + 1), y < x)
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (hG : (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k) :
        ρ.base = (norm ρ L).base := by
      rw [base_eq_baseOf, base_eq_baseOf, hChild]
      cases hh : ρ.childPositions.head? with
      | none => rfl
      | some p =>
        have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        have h := hCaps ρ L x hL hsingle hbefore hc hy ht hG p p hp hp
        simp only [baseOf, h.1, h.2, hK]
    have hFuel : ∀ fuel (ρ : Context),
        (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
        ∀ (L x : ℕ), Inv ρ L → ρ.extPositions L = [x] →
        (∃ y ∈ ρ.extPositions (L + 1), y < x) →
        (∀ p ∈ ρ.childPositions, x < p) →
        (∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p) →
        (∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) →
        (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k →
        boundFuel fuel ρ = boundFuel fuel (norm ρ L) := by
      intro fuel
      induction fuel with
      | zero => intro ρ hPos L x hL hsingle hbefore hc hy ht hG; rfl
      | succ fuel ih =>
        intro ρ hPos L x hL hsingle hbefore hc hy ht hG
        have hL1 := hL.1
        have hLn : L ∈ ρ.levels :=
          (hLevelMem ρ L).mpr ⟨hL1, by have := hL.2.1; omega⟩
        have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
            boundFuel fuel (ρ.part keep v m) =
              boundFuel fuel ((norm ρ L).part keep v m) := by
          have hs' : (ρ.part keep v m).extPositions (L + 1) = [x] := by
            rw [part_extPositions_succ ρ keep v m hL1, hsingle]
          have hb' : ∃ y ∈ (ρ.part keep v m).extPositions (L + 1 + 1), y < x := by
            rw [part_extPositions_succ ρ keep v m (by omega : 1 ≤ L + 1)]
            exact hbefore
          have hd := hNextBoundary ρ hPos L x hLn false hc hy keep v m
          have hg' : (match (ρ.part keep v m).sideAt (L + 1) with
              | Side.lower => (ρ.part keep v m).u
              | Side.upper => (ρ.part keep v m).a) ≤ (ρ.part keep v m).k := by
            rw [part_sideAt_succ ρ keep v m hL1]
            exact hG
          have h := ih (ρ.part keep v m) (hPartPositive ρ keep v m)
            (L + 1) x (hInvPart ρ L hL keep v m) hs' hb' hd.1 hd.2
            (hNextTerminal ρ L hLn ht keep v m) hg'
          rw [hNormPart ρ keep v m L hL1] at h
          exact h
        simp only [boundFuel, hRuns, hChild, hBlocks, hK]
        split_ifs
        · exact hBase ρ L x hL hsingle hbefore hc hy ht hG
        · congr 1
          apply congrArg List.max?
          apply List.flatMap_congr
          intro keep _
          apply List.flatMap_congr
          intro m _
          simp only [hParts]
    refine ⟨fun p hp q hq =>
      hCaps σ N x hpair hsole hbefore hchildren hyounger holdest hglobal p q hp hq,
      fun fuel => hFuel fuel σ hpositive N x hpair hsole hbefore hchildren hyounger holdest hglobal,
      ?_⟩
    simpa only [bound, hChild] using
      hFuel (σ.childPositions.length + 1) σ hpositive N x hpair hsole hbefore
        hchildren hyounger holdest hglobal
  have hPascal (a u k : ℕ) (ha : 3 ≤ a) (hak : a ≤ k) (hu : 2 ≤ u) (huk : u ≤ k) :
    decomposableThreshold a u k = decomposableThreshold (a - 1) u k +
      decomposableThreshold a (min (u - 1) (k - a + 2)) k := by
    classical
    have hSplit (lo hi : ℕ) (h : lo ≤ hi) (f : ℕ → ℕ) :
        (∑ j ∈ Finset.Icc lo hi, f j) =
          f lo + ∑ j ∈ Finset.Icc (lo + 1) hi, f j := by
      have hI : Finset.Icc lo hi = insert lo (Finset.Icc (lo + 1) hi) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hI, Finset.sum_insert (by simp [Finset.mem_Icc])]
    have hBoundary (x y : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
        (hxk : x ≤ k) (hyk : y ≤ k) (hxy : x + y = k + 3) :
        decomposableThreshold x y k = decomposableBinomialWindow x y k := by
      rw [decomposableThreshold_eq_choose hx hy (by omega)]
      have htop : x + y - 4 = k - 1 := by omega
      have hsym : Nat.choose (k - 1) (x - 2) =
          Nat.choose (k - 1) (k - x + 1) :=
        Nat.choose_symm_of_eq_add (by omega)
      have hrow : k - 1 = (k - 2) + 1 := by omega
      have hcol : k - x + 1 = (k - x) + 1 := by omega
      have hhi : y - 2 = (k - x) + 1 := by omega
      rw [htop, hsym, hrow, hcol, Nat.choose_succ_succ']
      unfold decomposableBinomialWindow
      rw [hSplit (k - x) (y - 2) (by omega), hhi]
      simp
    by_cases hu2 : u = 2
    · subst u
      have hmin : min (2 - 1) (k - a + 2) = 1 := by omega
      rw [hmin, decomposableThreshold_one_right]
      rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega),
        decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
      simp
    · have hu3 : 3 ≤ u := by omega
      by_cases hbase : a + u ≤ k + 3
      · have hmin : min (u - 1) (k - a + 2) = u - 1 := by omega
        rw [hmin, decomposableThreshold_eq_choose (by omega) hu hbase,
          decomposableThreshold_eq_choose (by omega) hu (by omega),
          decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
        have htop : a + u - 4 = (a + u - 5) + 1 := by omega
        have hidx : a - 2 = (a - 3) + 1 := by omega
        rw [htop, hidx, Nat.choose_succ_succ']
        congr 1 <;> congr 1 <;> omega
      · have hactive : k + 4 ≤ a + u := by omega
        have hmin : min (u - 1) (k - a + 2) = k - a + 2 := by omega
        have hLeaf : decomposableThreshold (a - 1) u k =
            decomposableBinomialWindow (a - 1) u k := by
          by_cases hmore : k + 4 ≤ (a - 1) + u
          · exact decomposableThreshold_eq_window (by omega) hu hmore
          · exact hBoundary (a - 1) u (by omega) hu (by omega) huk (by omega)
        have hSecond : decomposableThreshold a (k - a + 2) k =
            Nat.choose (k - 2) (k - a) := by
          rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
          have htop : a + (k - a + 2) - 4 = k - 2 := by omega
          rw [htop]
          exact Nat.choose_symm_of_eq_add (by omega)
        rw [hmin, decomposableThreshold_eq_window (by omega) hu hactive,
          hLeaf, hSecond]
        unfold decomposableBinomialWindow
        have hlo : k - (a - 1) = (k - a) + 1 := by omega
        rw [hlo, hSplit (k - a) (u - 2) (by omega)]
        omega
  have hWindowComm
      {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
      decomposableBinomialWindow a u k =
        decomposableBinomialWindow u a k := by
    unfold decomposableBinomialWindow
    apply Finset.sum_nbij' (fun j ↦ k - 2 - j) (fun j ↦ k - 2 - j)
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      exact (Nat.choose_symm (by omega)).symm
  have hThresholdComm
      {a u k : ℕ} (ha : 2 ≤ a) (hu : 2 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
      decomposableThreshold a u k = decomposableThreshold u a k := by
    rw [decomposableThreshold, decomposableThreshold]
    simp only [show ¬(a = 1 ∨ u = 1) by omega,
      show ¬(u = 1 ∨ a = 1) by omega, ↓reduceIte]
    by_cases hbase : a + u ≤ k + 3
    · rw [if_pos hbase, if_pos (by omega)]
      simpa [add_comm] using Nat.choose_symm_of_eq_add
        (n := a + u - 4) (a := a - 2) (b := u - 2) (by omega)
    · rw [if_neg hbase, if_neg (by omega)]
      exact hWindowComm ha hu hak huk
  have hSingleLeft (ρ : Context) (v : Side) (L p : ℕ)
      (hls : ρ.levelsOn v 0 = [L])
      (hx : ∃ x ∈ ρ.extPositions L, x < p) : ρ.leftExt v 0 p = 1 := by
    cases he : ((ρ.extPositions L).filter (· < p)).getLast? with
    | none =>
      obtain ⟨x,hx,hxp⟩ := hx
      have hm : x ∈ (ρ.extPositions L).filter (· < p) := by simp [hx,hxp]
      have hn := List.getLast?_eq_none_iff.mp he
      rw [hn] at hm
      exact False.elim (List.not_mem_nil hm)
    | some x =>
      simp [leftExt_eq,hls,List.sublists_cons,leftStep,he]
  have hSingleRight (ρ : Context) (v : Side) (L p : ℕ)
      (hls : ρ.levelsOn v 0 = [L])
      (hx : ∃ x ∈ ρ.extPositions L, p < x) : ρ.rightExt v 0 p = 1 := by
    cases he : ((ρ.extPositions L).filter (p < ·)).head? with
    | none =>
      obtain ⟨x,hx,hpx⟩ := hx
      have hm : x ∈ (ρ.extPositions L).filter (p < ·) := by simp [hx,hpx]
      have hn := List.head?_eq_none_iff.mp he
      rw [hn] at hm
      exact False.elim (List.not_mem_nil hm)
    | some x =>
      simp [rightExt_eq,hls,List.sublists_cons,rightStep,he]
  have hSingleLeftZero (ρ : Context) (v : Side) (L p : ℕ)
      (hls : ρ.levelsOn v 0 = [L])
      (hx : ∀ x ∈ ρ.extPositions L, ¬ x < p) : ρ.leftExt v 0 p = 0 := by
    have hf : (ρ.extPositions L).filter (· < p) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx'
      simp [hx x hx']
    simp [leftExt_eq,hls,List.sublists_cons,leftStep,hf]
  have hTopFilter (ρ : Context) (v : Side) (top : ℕ) (htop : 1 ≤ top) :
      ρ.levelsOn v top = (ρ.levelsOn v 0).filter (· < top) := by
    simp only [levelsOn,List.filter_filter]
    apply List.filter_congr
    intro j _
    simp [show top ≠ 0 by omega,Bool.and_comm]
  have hSingleJoin (ρ : Context) (v : Side) (L p q : ℕ)
      (hL : 1 ≤ L) (hls : ρ.levelsOn v 0 = [L]) :
      ρ.joinExt v p q = max (ρ.chainExt v p q) (ρ.maximumAt L) := by
    have ht : ρ.levelsOn v L = [] := by
      rw [hTopFilter ρ v L hL,hls]
      simp
    have hl : ρ.leftExt v L p = 0 := by simp [leftExt_eq,ht]
    have hr : ρ.rightExt v L q = 0 := by simp [rightExt_eq,ht]
    simp [joinExt,hls,hl,hr]
  have hEmptyAxis (ρ : Context) (v : Side) (p q : ℕ)
      (hls : ρ.levelsOn v 0 = []) :
      ρ.chainExt v p q = 0 ∧ ρ.joinExt v p q = 0 := by
    have hl : ρ.leftExt v 0 p = 0 := by simp [leftExt_eq,hls]
    have hr : ρ.rightExt v 0 q = 0 := by simp [rightExt_eq,hls]
    simp [chainExt,joinExt,hls,hl,hr]
  have hChildMem (ρ : Context) (p : ℕ) (hp : p ∈ ρ.childPositions) :
      p < ρ.word.length ∧ ρ.letterAt p = Letter.child := by
    simpa only [childPositions,List.mem_filter,List.mem_range,decide_eq_true_eq] using hp
  have hShape (ρ : Context) (v : Side)
      (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v) :
      ∀ p j w, ρ.letterAt p = Letter.ext j w → j = 1 ∧ w = v := by
    intro p j w hext
    have hp : p < ρ.word.length := by
      by_contra hn
      have h := letterAt_of_length_le ρ (Nat.le_of_not_gt hn)
      rw [h] at hext
      cases hext
    have hget : ρ.word[p] = Letter.ext j w := by
      simpa [letterAt,hp] using hext
    have hmem : Letter.ext j w ∈ ρ.word := by
      rw [← hget]
      exact List.getElem_mem _
    rcases hw _ hmem with h | h
    · cases h
    · cases h
      exact ⟨rfl,rfl⟩
  have hEnds (ρ : Context) (v : Side)
      (hf : ρ.word.head? = some (Letter.ext 1 v))
      (hl : ρ.word.getLast? = some (Letter.ext 1 v)) :
      ∃ y, 0 ∈ ρ.extPositions 1 ∧ y ∈ ρ.extPositions 1 ∧
        (∀ p ∈ ρ.childPositions, 0 < p ∧ p < y) := by
    have hlen : 1 ≤ ρ.word.length := by
      obtain ⟨ws,hws⟩ := List.head?_eq_some_iff.mp hf
      simp only [hws,List.length_cons]
      omega
    have hzero : ρ.letterAt 0 = Letter.ext 1 v := by
      unfold letterAt
      rw [← List.head?_eq_getElem?,hf]
      rfl
    have hlast : ρ.letterAt (ρ.word.length-1) = Letter.ext 1 v := by
      unfold letterAt
      rw [← List.getLast?_eq_getElem?,hl]
      rfl
    refine ⟨ρ.word.length-1,?_,?_,?_⟩
    · simp [extPositions,hzero,show 0 < ρ.word.length by omega]
    · simp [extPositions,hlast,show ρ.word.length-1 < ρ.word.length by omega]
    · intro p hp
      have hc := hChildMem ρ p hp
      have hn0 : p ≠ 0 := by intro he; subst p; rw [hzero] at hc; cases hc.2
      have hnlast : p ≠ ρ.word.length-1 := by
        intro he
        rw [he,hlast] at hc
        cases hc.2
      omega
  have hSideOne (ρ : Context) (v : Side)
      (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v)
      (hx : ∃ x, x ∈ ρ.extPositions 1) : ρ.sideAt 1 = v := by
    cases hh : (ρ.extPositions 1).head? with
    | none =>
      obtain ⟨x,hx⟩ := hx
      have hn := List.head?_eq_none_iff.mp hh
      rw [hn] at hx
      exact False.elim (List.not_mem_nil hx)
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      cases he : ρ.letterAt p with
      | child => simp [extPositions,he] at hp
      | ext j w =>
        have hs := (hShape ρ v hw p j w he).2
        simp [sideAt,hh,he,hs]
  have hChildExists (ρ : Context) (hc : Letter.child ∈ ρ.word) :
      ∃ p, p ∈ ρ.childPositions := by
    obtain ⟨p,hp⟩ := List.mem_iff_getElem?.mp hc
    have hlt := (List.getElem?_eq_some_iff.mp hp).1
    have hget := (List.getElem?_eq_some_iff.mp hp).2
    refine ⟨p,?_⟩
    simp [childPositions,hlt,letterAt,hget]
  have hRootLevels (ρ : Context) (v : Side) (m : ℕ)
      (hmx : ρ.maxima = [m]) (hs : ρ.sideAt 1 = v) :
      ρ.levelsOn v 0 = [1] := by
    simp [levelsOn,levels,hmx,hs]
  have hOtherLevels (ρ : Context) (v w : Side) (m : ℕ)
      (hmx : ρ.maxima = [m]) (hs : ρ.sideAt 1 = v) (hw : w ≠ v) :
      ρ.levelsOn w 0 = [] := by
    simp [levelsOn,levels,hmx,hs,hw.symm]
  let mkRoot (B H K M : ℕ) (v : Side) (w : List Letter) : Context :=
    { a := match v with | Side.lower => B | Side.upper => H
      u := match v with | Side.lower => H | Side.upper => B
      k := K, word := w, maxima := [M] }
  let opp : Side → Side := fun v => match v with
    | Side.lower => Side.upper | Side.upper => Side.lower
  let ownLimit (ρ : Context) (v : Side) (p q : ℕ) : ℕ :=
    match v with
    | Side.lower => ρ.cupLimit p q
    | Side.upper => ρ.capLimit p q
  let otherLimit (ρ : Context) (v : Side) (p q : ℕ) : ℕ :=
    match v with
    | Side.lower => ρ.capLimit p q
    | Side.upper => ρ.cupLimit p q
  have hRootPoint (B H K M : ℕ) (hB : 3 ≤ B) (hBK : B ≤ K)
      (hH : 4 ≤ H) (hHK : H ≤ K) (hM : 1 ≤ M) (hMK : M ≤ K-2)
      (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some (Letter.ext 1 v))
      (hl : w.getLast? = some (Letter.ext 1 v))
      (p : ℕ) (hp : p ∈ (mkRoot B H K M v w).childPositions) :
      let ρ := mkRoot B H K M v w
      ownLimit ρ v p p = min (H-2) (K-M) - 1 ∧
      otherLimit ρ v p p = B-1 := by
    let ρ := mkRoot B H K M v w
    change
      ownLimit ρ v p p = min (H-2) (K-M) - 1 ∧
      otherLimit ρ v p p = B-1
    obtain ⟨y,hzero,hy,hbracket⟩ := hEnds ρ v hf hl
    have hs := hSideOne ρ v hw ⟨0,hzero⟩
    have hls := hRootLevels ρ v M rfl hs
    have hleft := hSingleLeft ρ v 1 p hls ⟨0,hzero,(hbracket p hp).1⟩
    have hright := hSingleRight ρ v 1 p hls ⟨y,hy,(hbracket p hp).2⟩
    have hOwnC : ρ.chainExt v p p = 2 := by simp [chainExt,hleft,hright]
    have hOwnJ : ρ.joinExt v p p = max 2 M := by
      rw [hSingleJoin ρ v 1 p p (by omega) hls,hOwnC]
      simp [maximumAt,ρ,mkRoot]
    have hother : opp v ≠ v := by cases v <;> simp [opp]
    have hOtherLs := hOtherLevels ρ v (opp v) M rfl hs hother
    have hOC := hEmptyAxis ρ (opp v) p p hOtherLs
    cases v with
    | lower =>
      change
        min (H-1-ρ.chainExt Side.lower p p) (K-1-ρ.joinExt Side.lower p p) =
          min (H-2) (K-M)-1 ∧
        min (B-1-ρ.chainExt Side.upper p p) (K-1-ρ.joinExt Side.upper p p) = B-1
      rw [hOwnC,hOwnJ,hOC.1,hOC.2]
      constructor <;> omega
    | upper =>
      change
        min (H-1-ρ.chainExt Side.upper p p) (K-1-ρ.joinExt Side.upper p p) =
          min (H-2) (K-M)-1 ∧
        min (B-1-ρ.chainExt Side.lower p p) (K-1-ρ.joinExt Side.lower p p) = B-1
      rw [hOwnC,hOwnJ,hOC.1,hOC.2]
      constructor <;> omega
  have hBaseValue : ∀ cl pl k : ℕ, cl ≤ k - 1 → pl ≤ k - 1 →
      baseOf cl pl k = decomposableThreshold (pl + 1) (cl + 1) k := by
    intro cl pl k hc hpl
    by_cases hz : cl = 0 ∨ pl = 0
    · rcases hz with rfl | rfl <;> simp [baseOf]
    unfold baseOf
    rw [if_neg hz]
    by_cases hunit : cl = 1 ∨ pl = 1
    · rw [if_pos hunit]
      rcases hunit with rfl | rfl
      · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
        have hrow : pl + 1 + (1 + 1) - 4 = pl + 1 - 2 := by omega
        rw [hrow, Nat.choose_self]
      · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
        simp
    · rw [if_neg hunit]
  have hRootBase (B H K M : ℕ) (hB : 3 ≤ B) (hBK : B ≤ K)
      (hH : 4 ≤ H) (hHK : H ≤ K) (hM : 1 ≤ M) (hMK : M ≤ K-2)
      (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some (Letter.ext 1 v))
      (hl : w.getLast? = some (Letter.ext 1 v))
      (p : ℕ) (hhead : (mkRoot B H K M v w).childPositions.head? = some p) :
      (mkRoot B H K M v w).base = decomposableThreshold B (min (H-2) (K-M)) K := by
    let ρ := mkRoot B H K M v w
    let V := min (H-2) (K-M)
    have hV2 : 2 ≤ V := by dsimp [V]; omega
    have hVk : V ≤ K := by dsimp [V]; omega
    have hp : p ∈ ρ.childPositions :=
      List.mem_of_mem_head? (Option.mem_def.mpr hhead)
    have hLimits :
      ownLimit ρ v p p = V-1 ∧ otherLimit ρ v p p = B-1 :=
      hRootPoint B H K M hB hBK hH hHK hM hMK v w hw hf hl p hp
    have hc : ρ.cupLimit p p ≤ K-1 := by
      change min (ρ.u-1-ρ.chainExt Side.lower p p) (K-1-ρ.joinExt Side.lower p p) ≤ K-1
      omega
    have hpl : ρ.capLimit p p ≤ K-1 := by
      change min (ρ.a-1-ρ.chainExt Side.upper p p) (K-1-ρ.joinExt Side.upper p p) ≤ K-1
      omega
    change ρ.base = decomposableThreshold B V K
    rw [base_eq_baseOf,hhead]
    change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) K = decomposableThreshold B V K
    rw [hBaseValue _ _ _ hc hpl]
    have hbe : B-1+1 = B := by omega
    have hve : V-1+1 = V := by omega
    cases v with
    | lower =>
      dsimp only [ownLimit,otherLimit] at hLimits
      rw [hLimits.1,hLimits.2,hbe,hve]
    | upper =>
      dsimp only [ownLimit,otherLimit] at hLimits
      rw [hLimits.1,hLimits.2,hbe,hve]
      exact hThresholdComm hV2 (by omega) hVk hBK
  have hRootPositive (ρ : Context) (v : Side)
      (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v) :
      ∀ p j w, ρ.letterAt p = Letter.ext j w → 1 ≤ j := by
    intro p j w he
    have hj := (hShape ρ v hw p j w he).1
    omega
  have hFirstTail (ρ : Context) (p : ℕ) (ps : List ℕ)
      (hcp : ρ.childPositions = p :: ps) : ∀ q ∈ ps, p < q := by
    have h := childPositions_pairwise ρ
    rw [hcp] at h
    exact (List.pairwise_cons.mp h).1
  have hLeaf (B H K M : ℕ) (hB : 3 ≤ B) (hBK : B ≤ K)
      (hH : 4 ≤ H) (hHK : H ≤ K) (hM : 1 ≤ M) (hMK : M ≤ K-2)
      (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some (Letter.ext 1 v))
      (hl : w.getLast? = some (Letter.ext 1 v))
      (p : ℕ) (ps : List ℕ)
      (hcp : (mkRoot B H K M v w).childPositions = p :: ps) (hne : ps ≠ []) :
      ((mkRoot B H K M v w).part [p] (opp v) (K-B+1)).bound =
        decomposableThreshold (B-1) (min (H-2) (K-M)) K := by
    let ρ := mkRoot B H K M v w
    let c := K-B+1
    let V := min (H-2) (K-M)
    let leaf := ρ.part [p] (opp v) c
    have hcp : ρ.childPositions = p :: ps := hcp
    have hp : p ∈ ρ.childPositions := by simp [hcp]
    have hlt := hFirstTail ρ p ps hcp
    obtain ⟨q,hq⟩ := List.exists_mem_of_ne_nil ps hne
    have hqρ : q ∈ ρ.childPositions := by simp [hcp,hq]
    have hqp : p < q := hlt q hq
    have hpos := hRootPositive ρ v hw
    have hExt : leaf.extPositions 1 = ρ.childPositions.filter (· ∉ [p]) :=
      part_extPositions_one hpos [p] (opp v) c
    have hFresh : q ∈ leaf.extPositions 1 := by
      rw [hExt]
      simp [hqρ,show q ≠ p by omega]
    have hSide : leaf.sideAt 1 = opp v :=
      part_sideAt_one_of_mem hpos [p] (opp v) c hFresh
    obtain ⟨y,hzero,hy,hbracket⟩ := hEnds ρ v hf hl
    have hOldSide := hSideOne ρ v hw ⟨0,hzero⟩
    have hOldOther := hOtherLevels ρ v (opp v) M rfl hOldSide
      (by cases v <;> simp [opp])
    have hLevels : leaf.levelsOn (opp v) 0 = [1] := by
      rw [part_levelsOn_self_zero hSide,hOldOther]
      rfl
    have hNoLeft : ∀ x ∈ leaf.extPositions 1, ¬ x < p := by
      intro x hx
      rw [hExt] at hx
      have hxρ := (List.mem_filter.mp hx).1
      have hxn : x ≠ p := by simpa using (List.mem_filter.mp hx).2
      rw [hcp] at hxρ
      rcases List.mem_cons.mp hxρ with he | ht
      · exact False.elim (hxn he)
      · have hpx := hlt x ht
        omega
    have hLeft := hSingleLeftZero leaf (opp v) 1 p hLevels hNoLeft
    have hRight := hSingleRight leaf (opp v) 1 p hLevels ⟨q,hFresh,hqp⟩
    have hOC : leaf.chainExt (opp v) p p = 1 := by
      simp [chainExt,hLeft,hRight]
    have hNewMax : leaf.maximumAt 1 = c := by simp [maximumAt,leaf,part]
    have hc1 : 1 ≤ c := by dsimp [c]; omega
    have hOJ : leaf.joinExt (opp v) p p = c := by
      rw [hSingleJoin leaf (opp v) 1 p p (by omega) hLevels,hOC,hNewMax]
      omega
    have hSideNe : leaf.sideAt 1 ≠ v := by
      rw [hSide]
      cases v <;> simp [opp]
    have hOwnC := chainExt_part_other (σ := ρ) (keep := [p])
      (s := opp v) (m := c) hSideNe p p
    have hOwnJ := joinExt_part_other (σ := ρ) (keep := [p])
      (s := opp v) (m := c) hSideNe p p
    have hRP := hRootPoint B H K M hB hBK hH hHK hM hMK v w hw hf hl p hp
    have hOwn : ownLimit leaf v p p = V-1 := by
      cases v with
      | lower =>
        dsimp only [ownLimit] at hRP ⊢
        change min (H-1-leaf.chainExt Side.lower p p)
          (K-1-leaf.joinExt Side.lower p p) = V-1
        rw [hOwnC,hOwnJ]
        exact hRP.1
      | upper =>
        dsimp only [ownLimit] at hRP ⊢
        change min (H-1-leaf.chainExt Side.upper p p)
          (K-1-leaf.joinExt Side.upper p p) = V-1
        rw [hOwnC,hOwnJ]
        exact hRP.1
    have hOther : otherLimit leaf v p p = B-2 := by
      cases v with
      | lower =>
        change min (B-1-leaf.chainExt Side.upper p p)
          (K-1-leaf.joinExt Side.upper p p) = B-2
        change leaf.chainExt Side.upper p p = 1 at hOC
        change leaf.joinExt Side.upper p p = c at hOJ
        rw [hOC,hOJ]
        dsimp [c]
        omega
      | upper =>
        change min (B-1-leaf.chainExt Side.lower p p)
          (K-1-leaf.joinExt Side.lower p p) = B-2
        change leaf.chainExt Side.lower p p = 1 at hOC
        change leaf.joinExt Side.lower p p = c at hOJ
        rw [hOC,hOJ]
        dsimp [c]
        omega
    change leaf.bound = decomposableThreshold (B-1) V K
    rw [ctx_singleton_part_bound_eq_threshold ρ p hp (opp v) c]
    have hV2 : 2 ≤ V := by dsimp [V]; omega
    have hVk : V ≤ K := by dsimp [V]; omega
    have hbe : B-2+1 = B-1 := by omega
    have hve : V-1+1 = V := by omega
    cases v with
    | lower =>
      dsimp only [ownLimit,otherLimit] at hOwn hOther
      rw [hOwn,hOther,hbe,hve]
    | upper =>
      dsimp only [ownLimit,otherLimit] at hOwn hOther
      rw [hOwn,hOther,hbe,hve]
      simpa only [ρ,mkRoot] using
        hThresholdComm (a := V) (u := B-1) (k := K) hV2 (by omega) hVk (by omega)
  have hPartShape (ρ : Context) (v : Side)
      (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v)
      (keep : List ℕ) (s : Side) (n : ℕ) :
      ∀ x j t, (ρ.part keep s n).letterAt x = Letter.ext j t →
        (j = 1 ∧ t = s) ∨ (j = 2 ∧ t = v) := by
    intro x j t hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep s n)
        (show (ρ.part keep s n).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep s n hxl he] at hx
      by_cases hm : x ∈ keep
      · simp [hm] at hx
      · simp only [hm,if_false,Letter.ext.injEq] at hx
        obtain ⟨rfl,rfl⟩ := hx
        exact Or.inl ⟨rfl,rfl⟩
    | ext oldLevel oldSide =>
      have hs := hShape ρ v hw x oldLevel oldSide he
      obtain ⟨rfl,rfl⟩ := hs
      rw [part_letterAt_of_ext ρ keep s n hxl he] at hx
      cases hx
      exact Or.inr ⟨rfl,rfl⟩
  let mergeLetter : Letter → Letter := fun z => match z with
    | Letter.child => Letter.child
    | Letter.ext j v => if j ≤ 1 then Letter.ext j v else Letter.ext (j-1) v
  let mergeFirst (ρ : Context) : Context :=
    { ρ with
      a := match ρ.sideAt 1 with | Side.lower => ρ.a | Side.upper => ρ.a-1
      u := match ρ.sideAt 1 with | Side.lower => ρ.u-1 | Side.upper => ρ.u
      word := ρ.word.map mergeLetter
      maxima := [max (ρ.maximumAt 1) (ρ.maximumAt 2 + 1)] ++ ρ.maxima.drop 2 }
  have hMergeLength (ρ : Context) :
      (mergeFirst ρ).word.length = ρ.word.length := by simp [mergeFirst]
  have hMergeLetter (ρ : Context) (x : ℕ) :
      (mergeFirst ρ).letterAt x = mergeLetter (ρ.letterAt x) := by
    simp only [mergeFirst,letterAt,List.getElem?_map]
    cases ρ.word[x]? <;> rfl
  have hComplement (B H K M : ℕ) (hHk : H ≤ K)
      (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some (Letter.ext 1 v))
      (hl : w.getLast? = some (Letter.ext 1 v))
      (p : ℕ) (ps : List ℕ)
      (hcp : (mkRoot B H K M v w).childPositions = p :: ps) (hne : ps ≠ []) :
      ∃ w' : List Letter,
        (∀ z ∈ w', z = Letter.child ∨ z = Letter.ext 1 v) ∧
        w'.head? = some (Letter.ext 1 v) ∧
        w'.getLast? = some (Letter.ext 1 v) ∧
        Letter.child ∈ w' ∧
        ((mkRoot B H K M v w).part ps v (B-2)).bound =
          (mkRoot B (H-1) K (max (B-2) (M+1)) v w').bound := by
    let ρ := mkRoot B H K M v w
    let δ := ρ.part ps v (B-2)
    let τ := mergeFirst δ
    have hcp : ρ.childPositions = p :: ps := hcp
    have hlt := hFirstTail ρ p ps hcp
    have hnot : p ∉ ps := by
      intro hp
      have h := hlt p hp
      omega
    have hpos := hRootPositive ρ v hw
    have hShapeδ := hPartShape ρ v hw ps v (B-2)
    have hδpos : ∀ x j t, δ.letterAt x = Letter.ext j t → 1 ≤ j := by
      intro x j t hx
      rcases hShapeδ x j t hx with h | h <;> omega
    have hsole : δ.extPositions 1 = [p] := by
      rw [part_extPositions_one hpos,hcp]
      simp [hnot]
    have hside : δ.sideAt 1 = v :=
      part_sideAt_one_of_mem hpos ps v (B-2) (q := p) (by rw [hsole]; simp)
    obtain ⟨y,hzero,hy,hbracket⟩ := hEnds ρ v hf hl
    have hsideρ := hSideOne ρ v hw ⟨0,hzero⟩
    have hside2 : δ.sideAt 2 = v := by
      rw [part_sideAt_succ ρ ps v (B-2) (by omega : 1 ≤ 1),hsideρ]
    have hInv : Inv δ 1 := by
      refine ⟨by omega,?_,?_,?_⟩
      · simp [δ,part,ρ,mkRoot]
      · intro x j t hx _
        rcases hShapeδ x j t hx with h | h <;> simpa [hside] using h.2
      · rw [hside,hside2]
    have hbefore : ∃ y ∈ δ.extPositions 2, y < p := by
      refine ⟨0,?_,(hbracket p (by simp [hcp])).1⟩
      rw [part_extPositions_succ ρ ps v (B-2) (by omega : 1 ≤ 1)]
      exact hzero
    have hchildren : ∀ q ∈ δ.childPositions, p < q := by
      intro q hq
      rw [part_childPositions] at hq
      have hqps : q ∈ ps := of_decide_eq_true (List.mem_filter.mp hq).2
      exact hlt q hqps
    have hyounger : ∀ j ∈ δ.levelsOn (δ.sideAt 1) 1,
        ∀ q ∈ δ.extPositions j, p < q := by
      simp [levelsOn_one]
    have holdest : ∀ j ∈ δ.levelsOn (δ.sideAt 1) 0, j ≤ 2 := by
      intro j hj
      have hj' : j ∈ δ.levels := (List.mem_filter.mp hj).1
      simp [levels,δ,part,ρ,mkRoot] at hj'
      omega
    have hglobal :
        (match δ.sideAt 1 with | Side.lower => δ.u | Side.upper => δ.a) ≤ δ.k := by
      rw [hside]
      cases v <;> simpa [δ,part,ρ,mkRoot] using hHk
    have hEq := (hAbsorb δ hδpos 1 p hInv hsole hbefore hchildren hyounger holdest hglobal).2.2
    change δ.bound = τ.bound at hEq
    have hFields : τ = mkRoot B (H-1) K (max (B-2) (M+1)) v τ.word := by
      apply MergeLevels.ctx_ext
      · dsimp only [τ,mergeFirst]
        rw [hside]
        cases v <;> rfl
      · dsimp only [τ,mergeFirst]
        rw [hside]
        cases v <;> rfl
      · rfl
      · rfl
      · simp [τ,mergeFirst,maximumAt,δ,part,ρ,mkRoot]
    have hUniform : ∀ z ∈ τ.word, z = Letter.child ∨ z = Letter.ext 1 v := by
      intro z hz
      obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hz
      obtain ⟨x,hx⟩ := List.mem_iff_getElem?.mp hold
      have hOld : δ.letterAt x = old := by simp [letterAt,hx]
      cases old with
      | child => exact Or.inl rfl
      | ext j t =>
        rcases hShapeδ x j t hOld with h | h
        · obtain ⟨rfl,rfl⟩ := h
          exact Or.inr rfl
        · obtain ⟨rfl,rfl⟩ := h
          exact Or.inr rfl
    have hp0 := (hbracket p (by simp [hcp])).1
    have hlen : 1 ≤ ρ.word.length := by
      have h := hChildMem ρ p (by simp [hcp])
      omega
    have hδzero : δ.letterAt 0 = Letter.ext 2 v := by
      apply part_letterAt_of_ext ρ ps v (B-2) (by omega)
      have h : ρ.letterAt 0 = Letter.ext 1 v := by
        unfold letterAt
        rw [← List.head?_eq_getElem?,hf]
        rfl
      exact h
    have hδlast : δ.letterAt (δ.word.length-1) = Letter.ext 2 v := by
      rw [part_word_length]
      apply part_letterAt_of_ext ρ ps v (B-2) (by omega)
      unfold letterAt
      rw [← List.getLast?_eq_getElem?,hl]
      rfl
    have hτzero : τ.letterAt 0 = Letter.ext 1 v := by
      rw [hMergeLetter,hδzero]
      rfl
    have hτlast : τ.letterAt (τ.word.length-1) = Letter.ext 1 v := by
      rw [hMergeLength,hMergeLetter,hδlast]
      rfl
    have hτlen : 1 ≤ τ.word.length := by
      rw [hMergeLength,part_word_length]
      exact hlen
    have hFirst : τ.word.head? = some (Letter.ext 1 v) := by
      rw [List.head?_eq_getElem?]
      apply List.getElem?_eq_some_iff.mpr
      refine ⟨by omega,?_⟩
      simpa [letterAt,show 0 < τ.word.length by omega] using hτzero
    have hLast : τ.word.getLast? = some (Letter.ext 1 v) := by
      rw [List.getLast?_eq_getElem?]
      apply List.getElem?_eq_some_iff.mpr
      refine ⟨by omega,?_⟩
      simpa [letterAt,show τ.word.length-1 < τ.word.length by omega] using hτlast
    obtain ⟨q,hq⟩ := List.exists_mem_of_ne_nil ps hne
    have hqρ : q ∈ ρ.childPositions := by simp [hcp,hq]
    have hqmem := hChildMem ρ q hqρ
    have hδq : δ.letterAt q = Letter.child := by
      rw [part_letterAt_of_child ρ ps v (B-2) hqmem.1 hqmem.2,if_pos hq]
    have hτq : τ.letterAt q = Letter.child := by
      rw [hMergeLetter,hδq]
    have hqlen : q < τ.word.length := by
      rw [hMergeLength,part_word_length]
      exact hqmem.1
    have hChild : Letter.child ∈ τ.word := by
      have hget : τ.word[q] = Letter.child := by simpa [letterAt,hqlen] using hτq
      rw [← hget]
      exact List.getElem_mem _
    exact ⟨τ.word,hUniform,hFirst,hLast,hChild,hEq.trans (congrArg Context.bound hFields)⟩
  have hFirstBlock (ρ : Context) (p : ℕ) (ps : List ℕ)
      (hcp : ρ.childPositions = p :: ps) (hne : ps ≠ []) :
      [p] ∈ ρ.blocks ∧ ρ.childPositions.filter (· ∉ [p]) = ps := by
    have hlt := hFirstTail ρ p ps hcp
    have hlen : 1 ≤ ps.length := by
      by_contra h
      exact hne (List.length_eq_zero_iff.mp (by omega))
    have hblockLen : [p].length < ρ.childPositions.length := by
      rw [hcp]
      simp only [List.length_cons,List.length_nil]
      omega
    have hzero : 0 ∈ List.range ρ.childPositions.length := by
      simp only [List.mem_range,hcp,List.length_cons]
      omega
    have hzero' : 0 ∈ List.range (ρ.childPositions.length-0) := by simpa using hzero
    constructor
    · unfold blocks
      apply List.mem_filter.mpr
      refine ⟨?_,by simpa using hblockLen⟩
      apply List.mem_flatMap.mpr
      refine ⟨0,hzero,?_⟩
      apply List.mem_map.mpr
      refine ⟨0,hzero',?_⟩
      rw [hcp]
      rfl
    · have hf : ps.filter (· ∉ [p]) = ps := by
        apply List.filter_eq_self.mpr
        intro q hq
        have hpq := hlt q hq
        simp [show q ≠ p by omega]
      simpa [hcp] using hf
  have hLowerAll : ∀ H : ℕ, 4 ≤ H → H ≤ k →
      ∀ M : ℕ, 1 ≤ M → M ≤ k-2 →
      ∀ (v : Side) (w : List Letter),
      (∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v) →
      w.head? = some (Letter.ext 1 v) →
      w.getLast? = some (Letter.ext 1 v) →
      Letter.child ∈ w →
      decomposableThreshold A (min (H-2) (k-M)) k ≤ (mkRoot A H k M v w).bound := by
    intro H
    induction H using Nat.strong_induction_on with
    | h H ih =>
      intro hH hHk M hM hMk v w hw hf hl hc
      let ρ := mkRoot A H k M v w
      change decomposableThreshold A (min (H-2) (k-M)) k ≤ ρ.bound
      have hExist := hChildExists ρ hc
      cases hcp : ρ.childPositions with
      | nil =>
        obtain ⟨p,hp⟩ := hExist
        rw [hcp] at hp
        cases hp
      | cons p ps =>
        have hhead : ρ.childPositions.head? = some p := by rw [hcp]; rfl
        by_cases hr : ρ.numRuns ≤ 1
        · have hb : ρ.base = decomposableThreshold A (min (H-2) (k-M)) k :=
            hRootBase A H k M hA hAk hH hHk hM hMk v w hw hf hl p hhead
          rw [bound,boundFuel.eq_2,if_pos hr,hb]
        · have hRuns : 2 ≤ ρ.numRuns := by omega
          have hlen := numRuns_le_length ρ
          have hne : ps ≠ [] := by
            intro he
            rw [hcp,he] at hlen
            simp only [List.length_cons,List.length_nil] at hlen
            omega
          obtain ⟨hBlock,hRest⟩ := hFirstBlock ρ p ps hcp hne
          let V := min (H-2) (k-M)
          let W := min (H-1-2) (k-max (A-2) (M+1))
          have hV2 : 2 ≤ V := by dsimp [V]; omega
          have hVk : V ≤ k := by dsimp [V]; omega
          have hW : W = min (V-1) (k-A+2) := by dsimp [W,V]; omega
          obtain ⟨w',hw',hf',hl',hc',hCompEq⟩ :=
            hComplement A H k M hHk v w hw hf hl p ps hcp hne
          have hComp : decomposableThreshold A W k ≤ (ρ.part ps v (A-2)).bound := by
            rw [hCompEq]
            by_cases hW2 : 2 ≤ W
            · have hHpred : 4 ≤ H-1 := by dsimp [W] at hW2; omega
              have hMpred : max (A-2) (M+1) ≤ k-2 := by dsimp [W] at hW2; omega
              exact ih (H-1) (by omega) hHpred (by omega)
                (max (A-2) (M+1)) (by omega) hMpred v w' hw' hf' hl' hc'
            · have hW1 : W = 1 := by dsimp [W]; omega
              rw [hW1,decomposableThreshold_one_right]
              exact Nat.zero_le _
          have hLeafEq :
              (ρ.part [p] (opp v) (k-A+1)).bound = decomposableThreshold (A-1) V k :=
            hLeaf A H k M hA hAk hH hHk hM hMk v w hw hf hl p ps hcp hne
          have hcut :
              (ρ.part [p] (opp v) (k-A+1)).bound +
                (ρ.part ps v (A-2)).bound ≤ ρ.bound := by
            cases v with
            | lower =>
              have h := (ctx_bound_cut_le ρ hRuns [p] hBlock (A-2)
                (by omega) (by change A-2 ≤ k-2; omega)).2
              have he : ρ.k-1-(A-2) = k-A+1 := by change k-1-(A-2) = k-A+1; omega
              rw [hRest,he] at h
              exact h
            | upper =>
              have h := (ctx_bound_cut_le ρ hRuns [p] hBlock (k-A+1)
                (by omega) (by change k-A+1 ≤ k-2; omega)).1
              have he : ρ.k-1-(k-A+1) = A-2 := by change k-1-(k-A+1) = A-2; omega
              rw [hRest,he] at h
              exact h
          calc
            decomposableThreshold A V k =
                decomposableThreshold (A-1) V k + decomposableThreshold A W k := by
              rw [hW]
              exact hPascal A V k hA hAk hV2 hVk
            _ ≤ (ρ.part [p] (opp v) (k-A+1)).bound +
                (ρ.part ps v (A-2)).bound :=
              Nat.add_le_add hLeafEq.symm.le hComp
            _ ≤ ρ.bound := hcut
  have hPrefixMerge (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (N x : ℕ) (hpair : MergeLevels.Inv σ N)
    (hsole : σ.extPositions N = [x])
    (hafter : ∀ y ∈ σ.extPositions (N+1), x < y)
    (hchildren : ∀ p ∈ σ.childPositions, x < p)
    (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j, x < p)
    (holdest : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, j ≤ N+1)
    (hglobal : (match σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k) :
    let τ : Ctx.Context :=
      { σ with
        word := σ.word.map (fun z => match z with
          | Ctx.Letter.child => Ctx.Letter.child
          | Ctx.Letter.ext j v => if j ≤ N then Ctx.Letter.ext j v else Ctx.Letter.ext (j-1) v)
        maxima := σ.maxima.take (N-1) ++
          [max (σ.maximumAt N) (σ.maximumAt (N+1)+1)] ++ σ.maxima.drop (N+1) }
    (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
      σ.cupLimit p q = τ.cupLimit p q ∧ σ.capLimit p q = τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ = Ctx.Context.boundFuel fuel τ) ∧ σ.bound = τ.bound := by
    classical
    let letter (L : ℕ) : Letter → Letter := fun x => match x with
      | Letter.child => Letter.child
      | Letter.ext j s => if j ≤ L then Letter.ext j s else Letter.ext (j - 1) s
    let norm (ρ : Context) (L : ℕ) : Context :=
      { ρ with
        word := ρ.word.map (letter L)
        maxima := ρ.maxima.take (L - 1) ++ [max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)] ++
          ρ.maxima.drop (L + 1) }
    let lv (ρ : Context) (i : ℕ) : ℕ → Bool := fun p => match ρ.letterAt p with
      | Letter.ext j _ => decide (j = i)
      | Letter.child => false
    let up (L j : ℕ) := if j < L then j else j + 1
    let upTop (L t : ℕ) := if t ≤ L then t else t + 1
    let img (L j x : ℕ) : Prop := (j < L ∧ x = j) ∨ (j = L ∧ (x = L ∨ x = L + 1)) ∨ (L < j ∧ x = j + 1)
    change (∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
        σ.cupLimit p q = (norm σ N).cupLimit p q ∧
        σ.capLimit p q = (norm σ N).capLimit p q) ∧
      (∀ fuel, boundFuel fuel σ = boundFuel fuel (norm σ N)) ∧
        σ.bound = (norm σ N).bound
    -- basic transport ----------------------------------------------------------
    have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
      simp only [levels, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; omega
      · intro hj; exact ⟨j - 1, by omega, by omega⟩
    have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
      unfold levels
      exact List.pairwise_lt_range.map (fun x => x + 1) (fun a b h => Nat.add_lt_add_right h 1)
    have hLen (ρ : Context) (L : ℕ) : (norm ρ L).word.length = ρ.word.length := by
      simp only [norm, List.length_map]
    have hLetter (ρ : Context) (L p : ℕ) : (norm ρ L).letterAt p = letter L (ρ.letterAt p) := by
      simp only [norm, letterAt, List.getElem?_map]
      cases ρ.word[p]? <;> rfl
    have hIsChild (ρ : Context) (L p : ℕ) :
        (norm ρ L).letterAt p = Letter.child ↔ ρ.letterAt p = Letter.child := by
      rw [hLetter]
      cases ρ.letterAt p with
      | child => simp [letter]
      | ext j v => by_cases hj : j ≤ L <;> simp [letter, hj]
    have hChild (ρ : Context) (L : ℕ) : (norm ρ L).childPositions = ρ.childPositions := by
      simp only [childPositions, hLen, hIsChild]
    have hRuns (ρ : Context) (L : ℕ) : (norm ρ L).numRuns = ρ.numRuns := by
      simp only [numRuns, hLen, ne_eq, hIsChild]
    have hBlocks (ρ : Context) (L : ℕ) : (norm ρ L).blocks = ρ.blocks := by
      simp only [blocks, hChild]
    have hK (ρ : Context) (L : ℕ) : (norm ρ L).k = ρ.k := rfl
    have hDepth (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        (norm ρ L).maxima.length = ρ.maxima.length - 1 := by
      obtain ⟨h1, h2, -, -⟩ := hL
      simp only [norm, List.length_append, List.length_take, List.length_singleton, List.length_drop]
      omega
    have hNormLevel (ρ : Context) (L : ℕ) (hL : Inv ρ L) (j : ℕ) (hj : j ∈ (norm ρ L).levels) :
        1 ≤ j ∧ j + 1 ≤ ρ.maxima.length := by
      have h := (hLevelMem (norm ρ L) j).mp hj
      rw [hDepth ρ L hL] at h
      omega
    -- levels and letters ---------------------------------------------------------
    have hExtLv (ρ : Context) (i : ℕ) : ρ.extPositions i = (List.range ρ.word.length).filter (lv ρ i) := by
      unfold extPositions
      apply List.filter_congr
      intro p _
      cases h : ρ.letterAt p with
      | child => simp [lv, h]
      | ext j v => simp [lv, h]
    have hExtMerged (ρ : Context) (L : ℕ) :
        (norm ρ L).extPositions L =
          (List.range ρ.word.length).filter (fun p => lv ρ L p || lv ρ (L + 1) p) := by
      unfold extPositions
      rw [hLen]
      apply List.filter_congr
      intro p _
      rw [hLetter]
      cases h : ρ.letterAt p with
      | child => simp [lv, h, letter]
      | ext j v =>
        by_cases hj : j ≤ L
        · simp only [letter, hj, if_true, lv, h]
          by_cases hjL : j = L <;> simp [hjL] <;> omega
        · simp only [letter, hj, if_false, lv, h]
          by_cases hjL : j = L + 1 <;> simp [hjL] <;> omega
    have hExtNe (ρ : Context) (L j : ℕ) (hj1 : 1 ≤ j) (hjL : j ≠ L) :
        (norm ρ L).extPositions j = ρ.extPositions (up L j) := by
      unfold extPositions
      rw [hLen]
      apply List.filter_congr
      intro p _
      rw [hLetter]
      cases h : ρ.letterAt p with
      | child => simp [letter]
      | ext i v =>
        by_cases hi : i ≤ L <;> by_cases hjl : j < L <;> simp [letter, hi, hjl, up] <;> omega
    have hMemMerged (ρ : Context) (L p : ℕ) (hp : p ∈ ρ.extPositions L) :
        p ∈ (norm ρ L).extPositions L := by
      rw [hExtMerged, List.mem_filter]
      rw [hExtLv, List.mem_filter] at hp
      exact ⟨hp.1, by simp [hp.2]⟩
    have hSideL (ρ : Context) (L : ℕ) (hL : Inv ρ L) : (norm ρ L).sideAt L = ρ.sideAt L := by
      obtain ⟨-, -, h3, -⟩ := hL
      rcases hh : ((norm ρ L).extPositions L).head? with _ | p
      · have hρ : (ρ.extPositions L).head? = none := by
          cases hh2 : (ρ.extPositions L).head? with
          | none => rfl
          | some q =>
            exfalso
            have hq := hMemMerged ρ L q (List.mem_of_mem_head? (Option.mem_def.mpr hh2))
            rw [List.head?_eq_none_iff] at hh
            rw [hh] at hq
            exact List.not_mem_nil hq
        simp only [sideAt, hh, hρ]
      · have hp : p ∈ (norm ρ L).extPositions L := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        rw [hExtMerged, List.mem_filter] at hp
        cases hlet : ρ.letterAt p with
        | child => simp [lv, hlet] at hp
        | ext j v =>
          have hj : j = L ∨ j = L + 1 := by
            have := hp.2
            simp only [lv, hlet, Bool.or_eq_true, decide_eq_true_eq] at this
            exact this
          have hv := h3 p j v hlet hj
          rw [← hv]
          simp only [sideAt, hh, hLetter, hlet]
          by_cases hjL : j ≤ L <;> simp [letter, hjL]
    have hSideNe (ρ : Context) (L j : ℕ) (hj1 : 1 ≤ j) (hjL : j ≠ L) :
        (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
      unfold sideAt
      rw [hExtNe ρ L j hj1 hjL]
      cases hh : (ρ.extPositions (up L j)).head? with
      | none => rfl
      | some p =>
        dsimp only
        rw [hLetter]
        cases ρ.letterAt p with
        | child => rfl
        | ext i v => by_cases hi : i ≤ L <;> simp [letter, hi]
    have hMax (ρ : Context) (L : ℕ) (hL : Inv ρ L) (j : ℕ) (hj1 : 1 ≤ j) :
        (norm ρ L).maximumAt j =
          if j < L then ρ.maximumAt j else if j = L then max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)
          else ρ.maximumAt (j + 1) := by
      obtain ⟨h1, h2, -, -⟩ := hL
      simp only [maximumAt, norm]
      rw [getElem?_merge ρ.maxima L (j - 1) _ h1 h2]
      by_cases hjl : j < L
      · simp [hjl, show j - 1 < L - 1 by omega]
      · by_cases hjL : j = L
        · subst hjL; simp
        · simp [hjl, hjL, show ¬ j - 1 < L - 1 by omega, show j - 1 ≠ L - 1 by omega,
            show j - 1 + 1 = j by omega]
    have hUpMono (L i j : ℕ) (h : i < j) : up L i < up L j := by
      dsimp [up]
      split_ifs <;> omega
    have hUpZero (L : ℕ) (hL : 1 ≤ L) : up L 0 = 0 := by
      simp [up, show 0 < L by omega]
    have hLive (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
        (hj : j ∈ (norm ρ L).levels) :
        1 ≤ j ∧ j < ρ.maxima.length ∧ up L j ∈ ρ.levels := by
      have hh := hNormLevel ρ L hL j hj
      refine ⟨hh.1, by omega, ?_⟩
      apply (hLevelMem ρ _).mpr
      dsimp [up]
      split_ifs <;> omega
    have hSide (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
        (hj : j ∈ (norm ρ L).levels) :
        (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
      have hj1 := (hNormLevel ρ L hL j hj).1
      by_cases he : j = L
      · subst j
        rw [hSideL ρ L hL]
        simpa only [up, lt_self_iff_false, if_false] using hL.2.2.2
      · exact hSideNe ρ L j hj1 he
    have hNoMerged (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (v : Side) (hv : v ≠ ρ.sideAt L) (top j : ℕ)
        (hj : j ∈ (norm ρ L).levelsOn v top) : j ≠ L := by
      intro he
      subst j
      have hc : (norm ρ L).sideAt L = v ∧ (top = 0 ∨ L < top) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      rw [hSideL ρ L hL] at hc
      exact hv hc.1.symm
    have hMaximum (ρ : Context) (L j : ℕ) (hL : Inv ρ L)
        (hj : j ∈ (norm ρ L).levels) (hne : j ≠ L) :
        (norm ρ L).maximumAt j = ρ.maximumAt (up L j) := by
      rw [hMax ρ L hL j ((hNormLevel ρ L hL j hj).1)]
      by_cases hjl : j < L <;> simp [hjl, hne, up]
    have hOppLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
        (hv : v ≠ ρ.sideAt L) (top : ℕ) :
        (((norm ρ L).levelsOn v top).map (up L)) = ρ.levelsOn v (up L top) := by
      have hs : (((norm ρ L).levelsOn v top).map (up L)).Pairwise (· < ·) :=
        ((hSorted (norm ρ L)).filter _).map (up L) (fun i j hij => hUpMono L i j hij)
      apply hs.eq_of_mem_iff ((hSorted ρ).filter _)
      intro i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        have hjl := (List.mem_filter.mp hj).1
        have hjc : (norm ρ L).sideAt j = v ∧ (top = 0 ∨ j < top) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        apply List.mem_filter.mpr
        refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
        apply decide_eq_true
        refine ⟨?_, ?_⟩
        · rw [← hSide ρ L j hL hjl]
          exact hjc.1
        · rcases hjc.2 with rfl | hlt
          · exact Or.inl (hUpZero L hL.1)
          · exact Or.inr (hUpMono L j top hlt)
      · intro hi
        have hil := (List.mem_filter.mp hi).1
        have hic : ρ.sideAt i = v ∧ (up L top = 0 ∨ i < up L top) :=
          of_decide_eq_true (List.mem_filter.mp hi).2
        have hiL : i ≠ L := by
          intro he
          subst i
          exact hv hic.1.symm
        let j := if i < L then i else i-1
        have hLr : 1 ≤ L ∧ L ≤ ρ.maxima.length := ⟨hL.1, by omega⟩
        have hir := (hLevelMem ρ i).mp hil
        have hjr : 1 ≤ j ∧ j < ρ.maxima.length ∧ up L j = i := by
          dsimp [j, up]
          split_ifs <;> omega
        have hjl : j ∈ (norm ρ L).levels := by
          apply (hLevelMem (norm ρ L) j).mpr
          rw [hDepth ρ L hL]
          omega
        apply List.mem_map.mpr
        refine ⟨j, ?_, hjr.2.2⟩
        apply List.mem_filter.mpr
        refine ⟨hjl, ?_⟩
        apply decide_eq_true
        refine ⟨?_, ?_⟩
        · rw [hSide ρ L j hL hjl, hjr.2.2]
          exact hic.1
        · rcases hic.2 with hzero | hlt
          · left
            by_contra hne
            have h := hUpMono L 0 top (by omega)
            rw [hUpZero L hLr.1, hzero] at h
            omega
          · right
            by_contra hn
            have hm : up L top ≤ up L j := by
              rcases lt_or_eq_of_le (show top ≤ j by omega) with hm | he
              · exact (hUpMono L top j hm).le
              · rw [he]
            rw [hjr.2.2] at hm
            omega
    have hFoldNormLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (norm ρ L).levels ∧ j ≠ L) → ∀ z,
        ls.foldl (leftStep (norm ρ L)) z =
          (ls.map (up L)).foldl (leftStep ρ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; rfl
      | cons j ls ih =>
        intro hj z
        simp only [List.foldl_cons, List.map_cons, leftStep,
          hExtNe ρ L j ((hLevelMem (norm ρ L) j).mp (hj j (by simp)).1).1
            (hj j (by simp)).2]
        exact ih (fun i hi => hj i (by simp [hi])) _
    have hFoldNormRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (norm ρ L).levels ∧ j ≠ L) → ∀ z,
        ls.foldl (rightStep (norm ρ L)) z =
          (ls.map (up L)).foldl (rightStep ρ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; rfl
      | cons j ls ih =>
        intro hj z
        simp only [List.foldl_cons, List.map_cons, rightStep,
          hExtNe ρ L j ((hLevelMem (norm ρ L) j).mp (hj j (by simp)).1).1
            (hj j (by simp)).2]
        exact ih (fun i hi => hj i (by simp [hi])) _
    have hOppLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
        (hv : v ≠ ρ.sideAt L) (top p : ℕ) :
        (norm ρ L).leftExt v top p = ρ.leftExt v (up L top) p := by
      rw [leftExt_eq, leftExt_eq, ← hOppLevels ρ L hL v hv top,
        List.sublists_map, List.map_map]
      apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
      apply List.map_congr_left
      intro ls hls
      exact congrArg Prod.snd (hFoldNormLeft ρ L hL ls
        (fun j hj => ⟨(List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1,
          hNoMerged ρ L hL v hv top j ((List.mem_sublists.mp hls).subset hj)⟩) (p,0))
    have hOppRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
        (hv : v ≠ ρ.sideAt L) (top p : ℕ) :
        (norm ρ L).rightExt v top p = ρ.rightExt v (up L top) p := by
      rw [rightExt_eq, rightExt_eq, ← hOppLevels ρ L hL v hv top,
        List.sublists_map, List.map_map]
      apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
      apply List.map_congr_left
      intro ls hls
      exact congrArg Prod.snd (hFoldNormRight ρ L hL ls
        (fun j hj => ⟨(List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1,
          hNoMerged ρ L hL v hv top j ((List.mem_sublists.mp hls).subset hj)⟩) (p,0))
    have hOppChain (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
        (hv : v ≠ ρ.sideAt L) (p q : ℕ) :
        (norm ρ L).chainExt v p q = ρ.chainExt v p q := by
      simp only [chainExt, hOppLeft ρ L hL v hv, hOppRight ρ L hL v hv,
        hUpZero L hL.1]
    have hOppJoin (ρ : Context) (L : ℕ) (hL : Inv ρ L) (v : Side)
        (hv : v ≠ ρ.sideAt L) (p q : ℕ) :
        (norm ρ L).joinExt v p q = ρ.joinExt v p q := by
      have hl : (((norm ρ L).levelsOn v 0).map (up L)) = ρ.levelsOn v 0 := by
        simpa only [hUpZero L hL.1] using hOppLevels ρ L hL v hv 0
      rw [joinExt, joinExt, hOppChain ρ L hL v hv, ← hl, List.map_map]
      congr 1
      apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
      apply List.map_congr_left
      intro j hj
      rw [hOppLeft ρ L hL v hv, hOppRight ρ L hL v hv,
        hMaximum ρ L j hL (List.mem_filter.mp hj).1
          (hNoMerged ρ L hL v hv 0 j hj)]
      rfl
    have hYoungLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        (norm ρ L).levelsOn (ρ.sideAt L) L = ρ.levelsOn (ρ.sideAt L) L := by
      apply ((hSorted (norm ρ L)).filter _).eq_of_mem_iff ((hSorted ρ).filter _)
      intro j
      constructor
      · intro hj
        have hjl := (List.mem_filter.mp hj).1
        have hjc : (norm ρ L).sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        have hjlt : j < L := by omega
        have hj1 := (hNormLevel ρ L hL j hjl).1
        have hs := hSideNe ρ L j hj1 (by omega)
        have hu : up L j = j := by simp [up, hjlt]
        rw [hu] at hs
        exact List.mem_filter.mpr ⟨by
          have hh := (hLive ρ L j hL hjl).2.2
          simpa only [hu] using hh,
          by apply decide_eq_true; exact ⟨hs.symm.trans hjc.1, Or.inr hjlt⟩⟩
      · intro hj
        have hjl := (List.mem_filter.mp hj).1
        have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        have hjlt : j < L := by omega
        have hj1 := ((hLevelMem ρ j).mp hjl).1
        have hjn : j ∈ (norm ρ L).levels := by
          apply (hLevelMem (norm ρ L) j).mpr
          rw [hDepth ρ L hL]
          omega
        have hs := hSideNe ρ L j hj1 (by omega)
        have hu : up L j = j := by simp [up, hjlt]
        rw [hu] at hs
        exact List.mem_filter.mpr ⟨hjn,
          by apply decide_eq_true; exact ⟨hs.trans hjc.1, Or.inr hjlt⟩⟩
    have hSourcePairLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
        ρ.levelsOn (ρ.sideAt L) 0 = ρ.levelsOn (ρ.sideAt L) L ++ [L, L + 1] := by
      have hLs : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
        apply List.mem_filter.mpr
        exact ⟨(hLevelMem ρ L).mpr ⟨hL.1, by omega⟩, by simp⟩
      have hL1s : L + 1 ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
        apply List.mem_filter.mpr
        exact ⟨(hLevelMem ρ (L + 1)).mpr ⟨by omega, hL.2.1⟩,
          by apply decide_eq_true; exact ⟨hL.2.2.2.symm, Or.inl rfl⟩⟩
      have hs : (ρ.levelsOn (ρ.sideAt L) L ++ [L, L + 1]).Pairwise (· < ·) := by
        apply List.pairwise_append.mpr
        refine ⟨(hSorted ρ).filter _, by simp, ?_⟩
        intro i hi j hj
        have hc : ρ.sideAt i = ρ.sideAt L ∧ (L = 0 ∨ i < L) :=
          of_decide_eq_true (List.mem_filter.mp hi).2
        have hiL : i < L := by omega
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> omega
      apply ((hSorted ρ).filter _).eq_of_mem_iff hs
      intro j
      constructor
      · intro hj
        have hjL := ht j hj
        by_cases he : j = L
        · simp [he]
        by_cases he1 : j = L + 1
        · simp [he1]
        apply List.mem_append.mpr
        left
        apply List.mem_filter.mpr
        refine ⟨(List.mem_filter.mp hj).1, ?_⟩
        apply decide_eq_true
        have hc : ρ.sideAt j = ρ.sideAt L ∧ (0 = 0 ∨ j < 0) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        exact ⟨hc.1, Or.inr (by omega)⟩
      · intro hj
        rcases List.mem_append.mp hj with hj | hj
        · apply List.mem_filter.mpr
          refine ⟨(List.mem_filter.mp hj).1, ?_⟩
          apply decide_eq_true
          have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          exact ⟨hc.1, Or.inl rfl⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl
          · exact hLs
          · exact hL1s
    have hSourceOwnLevels (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L) :
        ρ.levelsOn (ρ.sideAt L) 0 = ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
      have hLs : L ∈ ρ.levelsOn (ρ.sideAt L) 0 := by simp [levelsOn, hL]
      have hs : (ρ.levelsOn (ρ.sideAt L) L ++ [L]).Pairwise (· < ·) := by
        apply List.pairwise_append.mpr
        refine ⟨(hSorted ρ).filter _, by simp, ?_⟩
        intro i hi j hj
        have he : j = L := by simpa using hj
        subst j
        have hc : ρ.sideAt i = ρ.sideAt L ∧ (L = 0 ∨ i < L) :=
          of_decide_eq_true (List.mem_filter.mp hi).2
        have hL1 := one_le_of_mem_levels hL
        omega
      apply ((hSorted ρ).filter _).eq_of_mem_iff hs
      intro j
      constructor
      · intro hj
        have hjL := ht j hj
        by_cases he : j = L
        · simp [he]
        · apply List.mem_append.mpr
          left
          apply List.mem_filter.mpr
          refine ⟨(List.mem_filter.mp hj).1, ?_⟩
          apply decide_eq_true
          have hc : ρ.sideAt j = ρ.sideAt L ∧ (0 = 0 ∨ j < 0) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          exact ⟨hc.1, Or.inr (by omega)⟩
      · intro hj
        rcases List.mem_append.mp hj with hj | hj
        · apply List.mem_filter.mpr
          refine ⟨(List.mem_filter.mp hj).1, ?_⟩
          apply decide_eq_true
          have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp hj).2
          exact ⟨hc.1, Or.inl rfl⟩
        · have he : j = L := by simpa using hj
          simpa [levelsOn, he] using hLs
    have hNormOwnLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
        (norm ρ L).levelsOn (ρ.sideAt L) 0 =
          ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
      have hNL : L ∈ (norm ρ L).levels := by
        apply (hLevelMem (norm ρ L) L).mpr
        rw [hDepth ρ L hL]
        omega
      have hAll : ∀ j ∈ (norm ρ L).levelsOn ((norm ρ L).sideAt L) 0, j ≤ L := by
        intro j hj
        have hjl := (List.mem_filter.mp hj).1
        have hjc : (norm ρ L).sideAt j = (norm ρ L).sideAt L ∧ (0 = 0 ∨ j < 0) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        have hh : up L j ∈ ρ.levelsOn (ρ.sideAt L) 0 := by
          apply List.mem_filter.mpr
          refine ⟨(hLive ρ L j hL hjl).2.2, ?_⟩
          apply decide_eq_true
          rw [← hSide ρ L j hL hjl, ← hSideL ρ L hL]
          exact ⟨hjc.1, Or.inl rfl⟩
        have hm := ht (up L j) hh
        dsimp [up] at hm
        split_ifs at hm <;> omega
      have hh := hSourceOwnLevels (norm ρ L) L hNL hAll
      rw [hSideL ρ L hL, hYoungLevels ρ L hL] at hh
      exact hh
    have hYoungFoldLeft (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        ∀ (ls : List ℕ), ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists → ∀ (z : ℕ × ℕ),
        ls.foldl (leftStep (norm ρ L)) z = ls.foldl (leftStep ρ) z := by
      intro ls
      have hGeneral : ∀ (ls : List ℕ),
          (∀ j ∈ ls, j ∈ ρ.levelsOn (ρ.sideAt L) L) → ∀ (z : ℕ × ℕ),
          ls.foldl (leftStep (norm ρ L)) z = ls.foldl (leftStep ρ) z := by
        intro ls
        induction ls with
        | nil => intro _ z; rfl
        | cons j ls ih =>
          intro hj z
          have hjl := (List.mem_filter.mp (hj j (by simp))).1
          have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp (hj j (by simp))).2
          have hjlt : j < L := by omega
          have hj1 := ((hLevelMem ρ j).mp hjl).1
          have he := hExtNe ρ L j hj1 (by omega)
          rw [show up L j = j by simp [up, hjlt]] at he
          simp only [List.foldl_cons, leftStep, he]
          exact ih (fun i hi => hj i (by simp [hi])) _
      intro hls z
      exact hGeneral ls (fun j hj => (List.mem_sublists.mp hls).subset hj) z
    have hDecomposeSublists (Y T ls : List ℕ) (hls : ls ∈ (Y ++ T).sublists) :
        ∃ ys ∈ Y.sublists, ∃ ts ∈ T.sublists, ls = ys ++ ts := by
      rw [List.sublists_append, List.bind_eq_flatMap] at hls
      obtain ⟨ts, hts, hh⟩ := List.mem_flatMap.mp hls
      obtain ⟨ys, hys, he⟩ := List.mem_map.mp hh
      exact ⟨ys, hys, ts, hts, he.symm⟩
    have hFoldCountLeft (ρ : Context) : ∀ (ls : List ℕ) (z : ℕ × ℕ),
        (ls.foldl (leftStep ρ) z).2 ≤ z.2 + ls.length := by
      intro ls
      induction ls with
      | nil => intro z; simp
      | cons j ls ih =>
        intro z
        have hstep : (leftStep ρ z j).2 ≤ z.2 + 1 := by
          cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? <;>
            simp [leftStep, hh]
        have hh := ih (leftStep ρ z j)
        simp only [List.foldl_cons, List.length_cons]
        omega
    have hLeftStepAdd (ρ : Context) (j e c : ℕ)
        (hex : ∃ y ∈ ρ.extPositions j, y < e) :
        (leftStep ρ (e,c) j).2 = c + 1 := by
      cases hh : ((ρ.extPositions j).filter (· < e)).getLast? with
      | some y => simp [leftStep, hh]
      | none =>
        obtain ⟨y, hy, hye⟩ := hex
        have hm : y ∈ (ρ.extPositions j).filter (· < e) := by simp [hy, hye]
        rw [List.getLast?_eq_none_iff] at hh
        rw [hh] at hm
        exact False.elim (List.not_mem_nil hm)
    have hFoldBoundary (ρ : Context) (x : ℕ) (dir : Bool) :
        ∀ (ls : List ℕ),
        (∀ j ∈ ls, ∀ y ∈ ρ.extPositions j, if dir then y < x else x < y) →
        ∀ z : ℕ × ℕ, (if dir then z.1 < x else x < z.1) →
        (if dir then (ls.foldl (leftStep ρ) z).1 < x
          else x < (ls.foldl (leftStep ρ) z).1) ∧
        (if dir then (ls.foldl (rightStep ρ) z).1 < x
          else x < (ls.foldl (rightStep ρ) z).1) := by
      intro ls
      induction ls with
      | nil => intro _ z hz; exact ⟨hz,hz⟩
      | cons j ls ih =>
        intro hy z hz
        have ht := fun i hi y hiy => hy i (List.mem_cons_of_mem j hi) y hiy
        constructor
        · cases hh : ((ρ.extPositions j).filter (· < z.1)).getLast? with
          | none => simpa only [List.foldl_cons, leftStep, hh] using (ih ht z hz).1
          | some y =>
            have hm := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
            have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
            simpa only [List.foldl_cons, leftStep, hh] using (ih ht (y,z.2+1) hyx).1
        · cases hh : ((ρ.extPositions j).filter (z.1 < ·)).head? with
          | none => simpa only [List.foldl_cons, rightStep, hh] using (ih ht z hz).2
          | some y =>
            have hm := List.mem_of_mem_head? (Option.mem_def.mpr hh)
            have hyx := hy j (by simp) y (List.mem_filter.mp hm).1
            simpa only [List.foldl_cons, rightStep, hh] using (ih ht (y,z.2+1) hyx).2
    have hSourceLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hafter : ∀ y ∈ ρ.extPositions (L+1), x < y)
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L+1)
        (p : ℕ) (hp : p ∈ ρ.childPositions) :
        ρ.leftExt (ρ.sideAt L) 0 p = ρ.leftExt (ρ.sideAt L) L p + 1 := by
      let Y := ρ.levelsOn (ρ.sideAt L) L
      have hnil : (ρ.extPositions (L+1)).filter (· < x) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simp [show ¬ y < x by have := hafter y hy; omega]
      have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          ((ys ++ [L,L+1]).foldl (leftStep ρ) (p,0)).2 =
            (ys.foldl (leftStep ρ) (p,0)).2 + 1 := by
        let z := ys.foldl (leftStep ρ) (p,0)
        have hz := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).1
        change x < z.1 at hz
        have hs : leftStep ρ z L = (x,z.2+1) := by
          simp [leftStep,hsingle,hz]
        rw [List.foldl_append]
        change (leftStep ρ (leftStep ρ z L) (L+1)).2 = z.2+1
        rw [hs]
        simp [leftStep,hnil]
      have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          (ys.foldl (leftStep ρ) (p,0)).2 + 1 ≤ ρ.leftExt (ρ.sideAt L) 0 p := by
        have hsub : ys ++ [L,L+1] ∈ (ρ.levelsOn (ρ.sideAt L) 0).sublists := by
          rw [hSourcePairLevels ρ L hL ht]
          exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
        have hh : ((ys ++ [L,L+1]).foldl (leftStep ρ) (p,0)).2 ≤
            ρ.leftExt (ρ.sideAt L) 0 p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L,L+1],hsub,rfl⟩)
        rwa [hAdd ys hys] at hh
      apply le_antisymm
      · rw [leftExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls,hls,rfl⟩ := List.mem_map.mp hz
        rw [hSourcePairLevels ρ L hL ht] at hls
        obtain ⟨ys,hys,ts,hts,rfl⟩ := hDecomposeSublists Y [L,L+1] ls hls
        have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
            ρ.leftExt (ρ.sideAt L) L p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys,hys,rfl⟩)
        have htail : (ts.foldl (leftStep ρ) (ys.foldl (leftStep ρ) (p,0))).2 ≤
            (ys.foldl (leftStep ρ) (p,0)).2+1 := by
          change ts ∈ [[],[L],[L+1],[L,L+1]] at hts
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hts
          rcases hts with rfl | rfl | rfl | rfl
          · simp
          · simpa using hFoldCountLeft ρ [L] (ys.foldl (leftStep ρ) (p,0))
          · simpa using hFoldCountLeft ρ [L+1] (ys.foldl (leftStep ρ) (p,0))
          · have he := hAdd ys hys
            rw [List.foldl_append] at he
            exact he.le
        rw [List.foldl_append]
        exact htail.trans (Nat.add_le_add_right hprefix 1)
      · have h1 : 1 ≤ ρ.leftExt (ρ.sideAt L) 0 p := by
          simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
        have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤ ρ.leftExt (ρ.sideAt L) 0 p-1 := by
          rw [leftExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ys,hys,rfl⟩ := List.mem_map.mp hz
          have hh := hLe ys hys
          omega
        omega
    have hNormLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p : ℕ) (hp : p ∈ ρ.childPositions) :
        (norm ρ L).leftExt (ρ.sideAt L) 0 p = ρ.leftExt (ρ.sideAt L) L p + 1 := by
      let Y := ρ.levelsOn (ρ.sideAt L) L
      have hx : x ∈ (norm ρ L).extPositions L :=
        hMemMerged ρ L x (by simp [hsingle])
      have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          ((ys ++ [L]).foldl (leftStep (norm ρ L)) (p,0)).2 =
            (ys.foldl (leftStep ρ) (p,0)).2 + 1 := by
        let z := ys.foldl (leftStep ρ) (p,0)
        have hz := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).1
        change x < z.1 at hz
        rw [List.foldl_append, hYoungFoldLeft ρ L hL ys hys]
        change (leftStep (norm ρ L) z L).2 = z.2 + 1
        exact hLeftStepAdd (norm ρ L) L z.1 z.2 ⟨x, hx, hz⟩
      have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          (ys.foldl (leftStep ρ) (p,0)).2 + 1 ≤
            (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
        have hsub : ys ++ [L] ∈ ((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists := by
          rw [hNormOwnLevels ρ L hL ht]
          exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
        have hh : ((ys ++ [L]).foldl (leftStep (norm ρ L)) (p,0)).2 ≤
            (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L], hsub, rfl⟩)
        rwa [hAdd ys hys] at hh
      apply le_antisymm
      · rw [leftExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
        rw [hNormOwnLevels ρ L hL ht] at hls
        obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
        have hcount := hFoldCountLeft (norm ρ L) ts
          (ys.foldl (leftStep (norm ρ L)) (p,0))
        rw [hYoungFoldLeft ρ L hL ys hys] at hcount
        have hlen : ts.length ≤ 1 := by
          simpa using (List.mem_sublists.mp hts).length_le
        have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
            ρ.leftExt (ρ.sideAt L) L p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
        rw [List.foldl_append, hYoungFoldLeft ρ L hL ys hys]
        omega
      · have h1 : 1 ≤ (norm ρ L).leftExt (ρ.sideAt L) 0 p := by
          simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
        have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤
            (norm ρ L).leftExt (ρ.sideAt L) 0 p - 1 := by
          rw [leftExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
          have hh := hLe ys hys
          omega
        omega
    have hYoungFoldRight (ρ : Context) (L : ℕ) (hL : Inv ρ L) :
        ∀ (ls : List ℕ), ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists → ∀ (z : ℕ × ℕ),
        ls.foldl (rightStep (norm ρ L)) z = ls.foldl (rightStep ρ) z := by
      intro ls
      have hGeneral : ∀ (ls : List ℕ),
          (∀ j ∈ ls, j ∈ ρ.levelsOn (ρ.sideAt L) L) → ∀ (z : ℕ × ℕ),
          ls.foldl (rightStep (norm ρ L)) z = ls.foldl (rightStep ρ) z := by
        intro ls
        induction ls with
        | nil => intro _ z; rfl
        | cons j ls ih =>
          intro hj z
          have hjl := (List.mem_filter.mp (hj j (by simp))).1
          have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
            of_decide_eq_true (List.mem_filter.mp (hj j (by simp))).2
          have hjlt : j < L := by omega
          have hj1 := ((hLevelMem ρ j).mp hjl).1
          have he := hExtNe ρ L j hj1 (by omega)
          rw [show up L j = j by simp [up, hjlt]] at he
          simp only [List.foldl_cons, rightStep, he]
          exact ih (fun i hi => hj i (by simp [hi])) _
      intro hls z
      exact hGeneral ls (fun j hj => (List.mem_sublists.mp hls).subset hj) z
    have hMergedRightStep (ρ : Context) (L x : ℕ)
        (hsingle : ρ.extPositions L = [x]) (z : ℕ × ℕ) (hx : x < z.1) :
        rightStep (norm ρ L) z L = rightStep ρ z (L + 1) := by
      have he : ((norm ρ L).extPositions L).filter (z.1 < ·) =
          (ρ.extPositions (L + 1)).filter (z.1 < ·) := by
        have hs₁ : ((norm ρ L).extPositions L).Pairwise (· < ·) :=
          List.pairwise_lt_range.filter _
        have hs₂ : (ρ.extPositions (L + 1)).Pairwise (· < ·) :=
          List.pairwise_lt_range.filter _
        apply (hs₁.filter _).eq_of_mem_iff (hs₂.filter _)
        intro p
        rw [hExtMerged, hExtLv]
        simp only [List.mem_filter, Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨hp, hpL | hpO⟩, hzp⟩
          · have hm : p ∈ ρ.extPositions L := by
              rw [hExtLv]
              exact List.mem_filter.mpr ⟨hp, hpL⟩
            have hpx : p = x := by simpa [hsingle] using hm
            omega
          · exact ⟨⟨hp, hpO⟩, hzp⟩
        · rintro ⟨⟨hp, hpO⟩, hzp⟩
          exact ⟨⟨hp, Or.inr hpO⟩, hzp⟩
      simp only [rightStep, he]
    have hNewRightStep (ρ : Context) (L x : ℕ)
        (hsingle : ρ.extPositions L = [x]) (z : ℕ × ℕ) (hx : x < z.1) :
        rightStep ρ z L = z := by
      rcases z with ⟨e,c⟩
      simp only at hx
      simp [rightStep, hsingle, show ¬ e < x by omega]
    have hOwnRight (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p : ℕ) (hp : p ∈ ρ.childPositions) :
        ρ.rightExt (ρ.sideAt L) 0 p = (norm ρ L).rightExt (ρ.sideAt L) 0 p := by
      let Y := ρ.levelsOn (ρ.sideAt L) L
      have hTail (ys ts : List ℕ) (hys : ys ∈ Y.sublists)
          (hts : ts ∈ [L, L + 1].sublists) :
          ∃ us ∈ [L].sublists,
            (ys ++ ts).foldl (rightStep ρ) (p,0) =
              (ys ++ us).foldl (rightStep (norm ρ L)) (p,0) := by
        let z := ys.foldl (rightStep ρ) (p,0)
        have hz := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).2
        change x < z.1 at hz
        have hcases : ts = [] ∨ ts = [L] ∨ ts = [L + 1] ∨ ts = [L, L + 1] := by
          simpa [List.sublists_cons] using hts
        rcases hcases with rfl | rfl | rfl | rfl
        · refine ⟨[], by simp, ?_⟩
          simpa only [List.append_nil] using (hYoungFoldRight ρ L hL ys hys (p,0)).symm
        · refine ⟨[], by simp, ?_⟩
          rw [List.foldl_append, List.append_nil, hYoungFoldRight ρ L hL ys hys]
          change rightStep ρ z L = z
          exact hNewRightStep ρ L x hsingle z hz
        · refine ⟨[L], by simp [List.sublists_cons], ?_⟩
          rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
          change rightStep ρ z (L + 1) = rightStep (norm ρ L) z L
          exact (hMergedRightStep ρ L x hsingle z hz).symm
        · refine ⟨[L], by simp [List.sublists_cons], ?_⟩
          rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
          change rightStep ρ (rightStep ρ z L) (L + 1) = rightStep (norm ρ L) z L
          rw [hNewRightStep ρ L x hsingle z hz]
          exact (hMergedRightStep ρ L x hsingle z hz).symm
      have hBack (ys us : List ℕ) (hys : ys ∈ Y.sublists)
          (hus : us ∈ [L].sublists) :
          ∃ ts ∈ [L, L + 1].sublists,
            (ys ++ us).foldl (rightStep (norm ρ L)) (p,0) =
              (ys ++ ts).foldl (rightStep ρ) (p,0) := by
        let z := ys.foldl (rightStep ρ) (p,0)
        have hz := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).2
        change x < z.1 at hz
        have hcases : us = [] ∨ us = [L] := by simpa [List.sublists_cons] using hus
        rcases hcases with rfl | rfl
        · refine ⟨[], by simp, ?_⟩
          simpa only [List.append_nil] using hYoungFoldRight ρ L hL ys hys (p,0)
        · refine ⟨[L + 1], by simp [List.sublists_cons], ?_⟩
          rw [List.foldl_append, List.foldl_append, hYoungFoldRight ρ L hL ys hys]
          change rightStep (norm ρ L) z L = rightStep ρ z (L + 1)
          exact hMergedRightStep ρ L x hsingle z hz
      apply le_antisymm
      · rw [rightExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
        rw [hSourcePairLevels ρ L hL ht] at hls
        obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L, L + 1] ls hls
        obtain ⟨us, hus, he⟩ := hTail ys ts hys hts
        have hsub : ys ++ us ∈ ((norm ρ L).levelsOn (ρ.sideAt L) 0).sublists := by
          rw [hNormOwnLevels ρ L hL ht]
          exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.mem_sublists.mp hus))
        rw [he, rightExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ us, hsub, rfl⟩)
      · rw [rightExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
        rw [hNormOwnLevels ρ L hL ht] at hls
        obtain ⟨ys, hys, us, hus, rfl⟩ := hDecomposeSublists Y [L] ls hls
        obtain ⟨ts, hts, he⟩ := hBack ys us hys hus
        have hsub : ys ++ ts ∈ (ρ.levelsOn (ρ.sideAt L) 0).sublists := by
          rw [hSourcePairLevels ρ L hL ht]
          exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.mem_sublists.mp hts))
        rw [he, rightExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ ts, hsub, rfl⟩)
    have hTopFilter (ρ : Context) (v : Side) (top : ℕ) (htop : 1 ≤ top) :
        ρ.levelsOn v top = (ρ.levelsOn v 0).filter (· < top) := by
      simp only [levelsOn, List.filter_filter]
      apply List.filter_congr
      intro j _
      simp [show top ≠ 0 by omega, Bool.and_comm]
    have hLevelsAtTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) :
        (norm ρ L).levelsOn (ρ.sideAt L) top = ρ.levelsOn (ρ.sideAt L) top := by
      rw [hTopFilter (norm ρ L) (ρ.sideAt L) top htop, hNormOwnLevels ρ L hL ht,
        hTopFilter ρ (ρ.sideAt L) top htop, hSourcePairLevels ρ L hL ht,
        List.filter_append, List.filter_append]
      simp [show ¬ L < top by omega, show ¬ L + 1 < top by omega]
    have hMidLevels (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) :
        ρ.levelsOn (ρ.sideAt L) (L + 1) = ρ.levelsOn (ρ.sideAt L) L ++ [L] := by
      rw [hTopFilter ρ (ρ.sideAt L) (L + 1) (by omega),
        hSourcePairLevels ρ L hL ht, List.filter_append]
      have hf : (ρ.levelsOn (ρ.sideAt L) L).filter (· < L + 1) =
          ρ.levelsOn (ρ.sideAt L) L := by
        apply List.filter_eq_self.mpr
        intro j hj
        apply decide_eq_true
        have hc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        omega
      rw [hf]
      simp
    have hYoungLeftTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) (p : ℕ) :
        (norm ρ L).leftExt (ρ.sideAt L) top p = ρ.leftExt (ρ.sideAt L) top p := by
      rw [leftExt_eq, leftExt_eq, hLevelsAtTop ρ L hL ht top htop htL]
      apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
      apply List.map_congr_left
      intro ls hls
      have hs : ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists :=
        List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans
          (levelsOn_sublist_of_le ρ (ρ.sideAt L) htop htL))
      exact congrArg Prod.snd (hYoungFoldLeft ρ L hL ls hs (p,0))
    have hYoungRightTop (ρ : Context) (L : ℕ) (hL : Inv ρ L)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (top : ℕ) (htop : 1 ≤ top) (htL : top ≤ L) (p : ℕ) :
        (norm ρ L).rightExt (ρ.sideAt L) top p = ρ.rightExt (ρ.sideAt L) top p := by
      rw [rightExt_eq, rightExt_eq, hLevelsAtTop ρ L hL ht top htop htL]
      apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
      apply List.map_congr_left
      intro ls hls
      have hs : ls ∈ (ρ.levelsOn (ρ.sideAt L) L).sublists :=
        List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans
          (levelsOn_sublist_of_le ρ (ρ.sideAt L) htop htL))
      exact congrArg Prod.snd (hYoungFoldRight ρ L hL ls hs (p,0))
    have hMidLeft (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p : ℕ) (hp : p ∈ ρ.childPositions) :
        ρ.leftExt (ρ.sideAt L) (L + 1) p = ρ.leftExt (ρ.sideAt L) L p + 1 := by
      let Y := ρ.levelsOn (ρ.sideAt L) L
      have hx : x ∈ ρ.extPositions L := by simp [hsingle]
      have hAdd (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          ((ys ++ [L]).foldl (leftStep ρ) (p,0)).2 =
            (ys.foldl (leftStep ρ) (p,0)).2 + 1 := by
        let z := ys.foldl (leftStep ρ) (p,0)
        have hz := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).1
        change x < z.1 at hz
        rw [List.foldl_append]
        change (leftStep ρ z L).2 = z.2 + 1
        exact hLeftStepAdd ρ L z.1 z.2 ⟨x, hx, hz⟩
      have hLe (ys : List ℕ) (hys : ys ∈ Y.sublists) :
          (ys.foldl (leftStep ρ) (p,0)).2 + 1 ≤
            ρ.leftExt (ρ.sideAt L) (L + 1) p := by
        have hsub : ys ++ [L] ∈ (ρ.levelsOn (ρ.sideAt L) (L + 1)).sublists := by
          rw [hMidLevels ρ L hL ht]
          exact List.mem_sublists.mpr ((List.mem_sublists.mp hys).append (List.Sublist.refl _))
        have hh : ((ys ++ [L]).foldl (leftStep ρ) (p,0)).2 ≤
            ρ.leftExt (ρ.sideAt L) (L + 1) p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys ++ [L], hsub, rfl⟩)
        rwa [hAdd ys hys] at hh
      apply le_antisymm
      · rw [leftExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
        rw [hMidLevels ρ L hL ht] at hls
        obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
        have hcount := hFoldCountLeft ρ ts
          (ys.foldl (leftStep ρ) (p,0))
        have hlen : ts.length ≤ 1 := by
          simpa using (List.mem_sublists.mp hts).length_le
        have hprefix : (ys.foldl (leftStep ρ) (p,0)).2 ≤
            ρ.leftExt (ρ.sideAt L) L p := by
          rw [leftExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
        rw [List.foldl_append]
        omega
      · have h1 : 1 ≤ ρ.leftExt (ρ.sideAt L) (L + 1) p := by
          simpa using hLe [] (List.mem_sublists.mpr (List.nil_sublist _))
        have hyoung : ρ.leftExt (ρ.sideAt L) L p ≤
            ρ.leftExt (ρ.sideAt L) (L + 1) p - 1 := by
          rw [leftExt_eq]
          apply getD_max?_le
          intro z hz
          obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
          have hh := hLe ys hys
          omega
        omega
    have hMidRight (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p : ℕ) (hp : p ∈ ρ.childPositions) :
        ρ.rightExt (ρ.sideAt L) (L + 1) p = ρ.rightExt (ρ.sideAt L) L p := by
      let Y := ρ.levelsOn (ρ.sideAt L) L
      apply le_antisymm
      · rw [rightExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hz
        rw [hMidLevels ρ L hL ht] at hls
        obtain ⟨ys, hys, ts, hts, rfl⟩ := hDecomposeSublists Y [L] ls hls
        have hboundary := (hFoldBoundary ρ x false ys
          (fun j hj y hiy => hy j ((List.mem_sublists.mp hys).subset hj) y hiy)
          (p,0) (hc p hp)).2
        change x < (ys.foldl (rightStep ρ) (p,0)).1 at hboundary
        have hcases : ts = [] ∨ ts = [L] := by simpa [List.sublists_cons] using hts
        have hprefix : (ys.foldl (rightStep ρ) (p,0)).2 ≤
            ρ.rightExt (ρ.sideAt L) L p := by
          rw [rightExt_eq]
          exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hys, rfl⟩)
        rcases hcases with rfl | rfl
        · simpa only [List.append_nil] using hprefix
        · rw [List.foldl_append]
          change (rightStep ρ (ys.foldl (rightStep ρ) (p,0)) L).2 ≤ _
          rw [hNewRightStep ρ L x hsingle _ hboundary]
          exact hprefix
      · rw [rightExt_eq]
        apply getD_max?_le
        intro z hz
        obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hz
        have hsub : ys ∈ (ρ.levelsOn (ρ.sideAt L) (L + 1)).sublists := by
          rw [hMidLevels ρ L hL ht]
          exact List.mem_sublists.mpr (by
            simpa only [List.append_nil] using
              ((List.mem_sublists.mp hys).append (List.nil_sublist [L])))
        rw [rightExt_eq]
        exact le_getD_max?_of_mem (List.mem_map.mpr ⟨ys, hsub, rfl⟩)
    have hOwnChain (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
        ρ.chainExt (ρ.sideAt L) p q = (norm ρ L).chainExt (ρ.sideAt L) p q := by
      have hl := hSourceLeft ρ L x hL hsingle hafter hc hy ht p hp
      have hn := hNormLeft ρ L x hL hsingle hc hy ht p hp
      have hr := hOwnRight ρ L x hL hsingle hc hy ht q hq
      unfold chainExt
      omega
    have hMaxAppend (A B : List ℕ) :
        ((A ++ B).max?).getD 0 = max (A.max?.getD 0) (B.max?.getD 0) := by
      apply le_antisymm
      · apply getD_max?_le
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact (le_getD_max?_of_mem hz).trans (le_max_left _ _)
        · exact (le_getD_max?_of_mem hz).trans (le_max_right _ _)
      · apply max_le
        · apply getD_max?_le_of_forall
          intro z hz
          exact ⟨z, List.mem_append_left _ hz, le_rfl⟩
        · apply getD_max?_le_of_forall
          intro z hz
          exact ⟨z, List.mem_append_right _ hz, le_rfl⟩
    have hMaxSingle (z : ℕ) : ([z].max?).getD 0 = z := by simp
    have hMaxPair (z w : ℕ) : ([z,w].max?).getD 0 = max z w := by
      simpa only [List.singleton_append, hMaxSingle] using hMaxAppend [z] [w]
    have hOwnJoin (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
        ρ.joinExt (ρ.sideAt L) p q =
          (norm ρ L).joinExt (ρ.sideAt L) p q := by
      let f := fun j => ρ.leftExt (ρ.sideAt L) j p +
        ρ.rightExt (ρ.sideAt L) j q + ρ.maximumAt j
      let g := fun j => (norm ρ L).leftExt (ρ.sideAt L) j p +
        (norm ρ L).rightExt (ρ.sideAt L) j q + (norm ρ L).maximumAt j
      have hYoungMap :
          (ρ.levelsOn (ρ.sideAt L) L).map g =
            (ρ.levelsOn (ρ.sideAt L) L).map f := by
        apply List.map_congr_left
        intro j hj
        have hj1 := one_le_of_mem_levels (List.mem_filter.mp hj).1
        have hjc : ρ.sideAt j = ρ.sideAt L ∧ (L = 0 ∨ j < L) :=
          of_decide_eq_true (List.mem_filter.mp hj).2
        have hjL : j < L := by have := hL.1; omega
        dsimp [f,g]
        rw [hYoungLeftTop ρ L hL ht j hj1 (by omega) p,
          hYoungRightTop ρ L hL ht j hj1 (by omega) q,
          hMax ρ L hL j hj1]
        simp only [hjL, if_true]
      have hMergedValue : g L = max (f L) (f (L + 1)) := by
        dsimp [f,g]
        rw [hYoungLeftTop ρ L hL ht L hL.1 le_rfl p,
          hYoungRightTop ρ L hL ht L hL.1 le_rfl q,
          hMax ρ L hL L hL.1,
          hMidLeft ρ L x hL hsingle hc hy ht p hp,
          hMidRight ρ L x hL hsingle hc hy ht q hq]
        simp only [lt_self_iff_false, if_false, if_true]
        omega
      change max (ρ.chainExt (ρ.sideAt L) p q)
          (((ρ.levelsOn (ρ.sideAt L) 0).map f).max?.getD 0) =
        max ((norm ρ L).chainExt (ρ.sideAt L) p q)
          ((((norm ρ L).levelsOn (ρ.sideAt L) 0).map g).max?.getD 0)
      rw [hOwnChain ρ L x hL hsingle hafter hc hy ht p q hp hq,
        hSourcePairLevels ρ L hL ht, hNormOwnLevels ρ L hL ht,
        List.map_append, List.map_append, hMaxAppend, hMaxAppend, hYoungMap]
      simp only [List.map_cons, List.map_nil, hMaxPair, hMaxSingle]
      rw [← hMergedValue]
    have hCaps (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (hG : (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k)
        (p q : ℕ) (hp : p ∈ ρ.childPositions) (hq : q ∈ ρ.childPositions) :
        ρ.cupLimit p q = (norm ρ L).cupLimit p q ∧
        ρ.capLimit p q = (norm ρ L).capLimit p q := by
      have hc' := hOwnChain ρ L x hL hsingle hafter hc hy ht p q hp hq
      have hj' := hOwnJoin ρ L x hL hsingle hafter hc hy ht p q hp hq
      cases hs : ρ.sideAt L with
      | lower =>
        rw [hs] at hc' hj' hG
        change ρ.u ≤ ρ.k at hG
        have hOC := hOppChain ρ L hL Side.upper (by simp [hs]) p q
        have hOJ := hOppJoin ρ L hL Side.upper (by simp [hs]) p q
        have ha : (norm ρ L).a = ρ.a := rfl
        have hu : (norm ρ L).u = ρ.u := rfl
        unfold cupLimit capLimit
        rw [ha, hu, hK, hc', hj', hOC, hOJ]
        exact ⟨rfl,rfl⟩
      | upper =>
        rw [hs] at hc' hj' hG
        change ρ.a ≤ ρ.k at hG
        have hOC := hOppChain ρ L hL Side.lower (by simp [hs]) p q
        have hOJ := hOppJoin ρ L hL Side.lower (by simp [hs]) p q
        have ha : (norm ρ L).a = ρ.a := rfl
        have hu : (norm ρ L).u = ρ.u := rfl
        unfold cupLimit capLimit
        rw [ha, hu, hK, hc', hj', hOC, hOJ]
        exact ⟨rfl,rfl⟩
    have hNormPart (ρ : Context) (keep : List ℕ) (v : Side) (m L : ℕ) (hL1 : 1 ≤ L) :
        norm (ρ.part keep v m) (L + 1) = (norm ρ L).part keep v m := by
      have hw : (norm (ρ.part keep v m) (L + 1)).word = ((norm ρ L).part keep v m).word := by
        change ((ρ.part keep v m).word.map (letter (L + 1))) =
          (List.range (norm ρ L).word.length).map (fun p => match (norm ρ L).letterAt p with
            | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 v
            | Letter.ext j w => Letter.ext (j + 1) w)
        rw [hLen]
        simp only [part, List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro p _
        rw [hLetter]
        cases ρ.letterAt p with
        | child => by_cases hp : p ∈ keep <;> simp [hp, letter]
        | ext j w =>
          by_cases hj : j ≤ L
          · simp [letter, hj]
          · simp [letter, hj, show j - 1 + 1 = j by omega]
      have e1 : (m :: ρ.maxima).take (L + 1 - 1) = m :: ρ.maxima.take (L - 1) := by
        rw [show L + 1 - 1 = (L - 1) + 1 by omega, List.take_succ_cons]
      have e2 : (m :: ρ.maxima).drop (L + 1 + 1) = ρ.maxima.drop (L + 1) := by
        rw [List.drop_succ_cons]
      have e3 : (ρ.part keep v m).maximumAt (L + 1) = ρ.maximumAt L := by
        simp only [maximumAt, part_maxima]
        rw [show L + 1 - 1 = (L - 1) + 1 by omega, List.getElem?_cons_succ]
      have e4 : (ρ.part keep v m).maximumAt (L + 1 + 1) = ρ.maximumAt (L + 1) := by
        simp only [maximumAt, part_maxima]
        rw [show L + 1 + 1 - 1 = (L + 1 - 1) + 1 by omega, List.getElem?_cons_succ]
      have hmx : (norm (ρ.part keep v m) (L + 1)).maxima = ((norm ρ L).part keep v m).maxima := by
        show (m :: ρ.maxima).take (L + 1 - 1) ++
            [max ((ρ.part keep v m).maximumAt (L + 1)) ((ρ.part keep v m).maximumAt (L + 1 + 1) + 1)] ++
            (m :: ρ.maxima).drop (L + 1 + 1) =
          m :: (ρ.maxima.take (L - 1) ++ [max (ρ.maximumAt L) (ρ.maximumAt (L + 1) + 1)] ++ ρ.maxima.drop (L + 1))
        rw [e1, e2, e3, e4]
        rfl
      have ha : (norm (ρ.part keep v m) (L+1)).a = ((norm ρ L).part keep v m).a := rfl
      have hu : (norm (ρ.part keep v m) (L+1)).u = ((norm ρ L).part keep v m).u := rfl
      exact ctx_ext ha hu rfl hw hmx
    have hInvPart (ρ : Context) (L : ℕ) (hL : Inv ρ L) (keep : List ℕ) (v : Side) (m : ℕ) :
        Inv (ρ.part keep v m) (L + 1) := by
      obtain ⟨h1, h2, h3, h4⟩ := hL
      refine ⟨by omega, by simp only [part_maxima, List.length_cons]; omega, ?_, ?_⟩
      · intro p j w hp hj
        rw [part_sideAt_succ ρ keep v m h1]
        by_cases hplen : p < ρ.word.length
        · cases hlet : ρ.letterAt p with
          | child =>
            rw [part_letterAt_of_child ρ keep v m hplen hlet] at hp
            by_cases hk : p ∈ keep
            · simp [hk] at hp
            · simp only [hk, if_false, Letter.ext.injEq] at hp
              obtain ⟨hj1, -⟩ := hp
              omega
          | ext i u =>
            rw [part_letterAt_of_ext ρ keep v m hplen hlet, Letter.ext.injEq] at hp
            obtain ⟨rfl, rfl⟩ := hp
            exact h3 p i u hlet (by omega)
        · rw [letterAt_of_length_le _ (by rw [part_word_length]; omega)] at hp
          cases hp
      · rw [part_sideAt_succ ρ keep v m h1, part_sideAt_succ ρ keep v m (by omega : 1 ≤ L + 1)]
        exact h4
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
    have hNextTerminal (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (keep : List ℕ) (v : Side) (m : ℕ) :
        ∀ j ∈ (ρ.part keep v m).levelsOn ((ρ.part keep v m).sideAt (L+1)) 0, j ≤ L+1+1 := by
      intro j hj
      have hj1 := (one_le_of_mem_levelsOn hj).1
      have hL1 := one_le_of_mem_levels hL
      by_cases he : j = 1
      · omega
      · let i := j-1
        have hi : 1 ≤ i := by dsimp [i]; omega
        have he : j = i+1 := by dsimp [i]; omega
        rw [he] at hj ⊢
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
        have := ht i hiOn
        omega
    have hBase (ρ : Context) (L x : ℕ) (hL : Inv ρ L)
        (hsingle : ρ.extPositions L = [x])
        (hafter : ∀ y ∈ ρ.extPositions (L + 1), x < y)
        (hc : ∀ p ∈ ρ.childPositions, x < p)
        (hy : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p)
        (ht : ∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1)
        (hG : (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k) :
        ρ.base = (norm ρ L).base := by
      rw [base_eq_baseOf, base_eq_baseOf, hChild]
      cases hh : ρ.childPositions.head? with
      | none => rfl
      | some p =>
        have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        have h := hCaps ρ L x hL hsingle hafter hc hy ht hG p p hp hp
        simp only [baseOf, h.1, h.2, hK]
    have hFuel : ∀ fuel (ρ : Context),
        (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
        ∀ (L x : ℕ), Inv ρ L → ρ.extPositions L = [x] →
        (∀ y ∈ ρ.extPositions (L + 1), x < y) →
        (∀ p ∈ ρ.childPositions, x < p) →
        (∀ j ∈ ρ.levelsOn (ρ.sideAt L) L, ∀ p ∈ ρ.extPositions j, x < p) →
        (∀ j ∈ ρ.levelsOn (ρ.sideAt L) 0, j ≤ L + 1) →
        (match ρ.sideAt L with | Side.lower => ρ.u | Side.upper => ρ.a) ≤ ρ.k →
        boundFuel fuel ρ = boundFuel fuel (norm ρ L) := by
      intro fuel
      induction fuel with
      | zero => intro ρ hPos L x hL hsingle hafter hc hy ht hG; rfl
      | succ fuel ih =>
        intro ρ hPos L x hL hsingle hafter hc hy ht hG
        have hL1 := hL.1
        have hLn : L ∈ ρ.levels :=
          (hLevelMem ρ L).mpr ⟨hL1, by have := hL.2.1; omega⟩
        have hParts (keep : List ℕ) (v : Side) (m : ℕ) :
            boundFuel fuel (ρ.part keep v m) =
              boundFuel fuel ((norm ρ L).part keep v m) := by
          have hs' : (ρ.part keep v m).extPositions (L + 1) = [x] := by
            rw [part_extPositions_succ ρ keep v m hL1, hsingle]
          have hb' : ∀ y ∈ (ρ.part keep v m).extPositions (L + 1 + 1), x < y := by
            rw [part_extPositions_succ ρ keep v m (by omega : 1 ≤ L + 1)]
            exact hafter
          have hd := hNextBoundary ρ hPos L x hLn false hc hy keep v m
          have hg' : (match (ρ.part keep v m).sideAt (L + 1) with
              | Side.lower => (ρ.part keep v m).u
              | Side.upper => (ρ.part keep v m).a) ≤ (ρ.part keep v m).k := by
            rw [part_sideAt_succ ρ keep v m hL1]
            exact hG
          have h := ih (ρ.part keep v m) (hPartPositive ρ keep v m)
            (L + 1) x (hInvPart ρ L hL keep v m) hs' hb' hd.1 hd.2
            (hNextTerminal ρ L hLn ht keep v m) hg'
          rw [hNormPart ρ keep v m L hL1] at h
          exact h
        simp only [boundFuel, hRuns, hChild, hBlocks, hK]
        split_ifs
        · exact hBase ρ L x hL hsingle hafter hc hy ht hG
        · congr 1
          apply congrArg List.max?
          apply List.flatMap_congr
          intro keep _
          apply List.flatMap_congr
          intro m _
          simp only [hParts]
    refine ⟨fun p hp q hq =>
      hCaps σ N x hpair hsole hafter hchildren hyounger holdest hglobal p q hp hq,
      fun fuel => hFuel fuel σ hpositive N x hpair hsole hafter hchildren hyounger holdest hglobal,
      ?_⟩
    simpa only [bound, hChild] using
      hFuel (σ.childPositions.length + 1) σ hpositive N x hpair hsole hafter
        hchildren hyounger holdest hglobal

  have hChildZero (ρ : Context) (hf : ρ.word.head? = some Letter.child) :
      0 < ρ.word.length ∧ ρ.letterAt 0 = Letter.child ∧ 0 ∈ ρ.childPositions := by
    have hlen : 0 < ρ.word.length := by
      obtain ⟨ws,hws⟩ := List.head?_eq_some_iff.mp hf
      simp [hws]
    have hz : ρ.letterAt 0 = Letter.child := by
      unfold letterAt
      rw [← List.head?_eq_getElem?,hf]
      rfl
    exact ⟨hlen,hz,by simp [childPositions,hlen,hz]⟩
  have hLastFacts (ρ : Context) (v : Side)
      (hf : ρ.word.head? = some Letter.child)
      (hl : ρ.word.getLast? = some (Letter.ext 1 v)) :
      ∃ y, y ∈ ρ.extPositions 1 ∧ (∀ p ∈ ρ.childPositions, p < y) := by
    have hlen := (hChildZero ρ hf).1
    have he : ρ.letterAt (ρ.word.length-1) = Letter.ext 1 v := by
      unfold letterAt
      rw [← List.getLast?_eq_getElem?,hl]
      rfl
    refine ⟨ρ.word.length-1,?_,?_⟩
    · simp [extPositions,he,show ρ.word.length-1 < ρ.word.length by omega]
    · intro p hp
      have hc := hChildMem ρ p hp
      have hn : p ≠ ρ.word.length-1 := by
        intro heq
        rw [heq,he] at hc
        cases hc.2
      omega
  have hFirstIsZero (ρ : Context) (hf : ρ.word.head? = some Letter.child)
      (p : ℕ) (ps : List ℕ) (hcp : ρ.childPositions = p :: ps) : p = 0 := by
    have hz := (hChildZero ρ hf).2.2
    rw [hcp] at hz
    rcases List.mem_cons.mp hz with h | h
    · exact h.symm
    · have hh := hFirstTail ρ p ps hcp 0 h
      omega
  have hOldAfterZero (ρ : Context) (hf : ρ.word.head? = some Letter.child) :
      ∀ y ∈ ρ.extPositions 1, 0 < y := by
    intro y hy
    have hz := (hChildZero ρ hf).2.1
    by_contra hn
    have hy0 : y = 0 := by omega
    subst y
    simp [extPositions,hz] at hy
  have hExposedPoint (B H K M : ℕ) (hB : 3 ≤ B) (hBK : B ≤ K)
      (hH : 3 ≤ H) (hHK : H ≤ K) (hM : 1 ≤ M) (hMK : M ≤ K-2)
      (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some Letter.child)
      (hl : w.getLast? = some (Letter.ext 1 v)) :
      ownLimit (mkRoot B H K M v w) v 0 0 = min (H-1) (K-M)-1 ∧
      otherLimit (mkRoot B H K M v w) v 0 0 = B-1 := by
    let ρ := mkRoot B H K M v w
    obtain ⟨y,hy,hbracket⟩ := hLastFacts ρ v hf hl
    have hs := hSideOne ρ v hw ⟨y,hy⟩
    have hls := hRootLevels ρ v M rfl hs
    have hleft := hSingleLeftZero ρ v 1 0 hls (fun x _ => by omega)
    have hright := hSingleRight ρ v 1 0 hls
      ⟨y,hy,hbracket 0 (hChildZero ρ hf).2.2⟩
    have hOwnC : ρ.chainExt v 0 0 = 1 := by simp [chainExt,hleft,hright]
    have hOwnJ : ρ.joinExt v 0 0 = M := by
      rw [hSingleJoin ρ v 1 0 0 (by omega) hls,hOwnC]
      simp [maximumAt,ρ,mkRoot,show 1 ≤ M from hM]
    have hOtherLs := hOtherLevels ρ v (opp v) M rfl hs
      (by cases v <;> simp [opp])
    have hOC := hEmptyAxis ρ (opp v) 0 0 hOtherLs
    cases v with
    | lower =>
      change
        min (H-1-ρ.chainExt Side.lower 0 0) (K-1-ρ.joinExt Side.lower 0 0) =
          min (H-1) (K-M)-1 ∧
        min (B-1-ρ.chainExt Side.upper 0 0) (K-1-ρ.joinExt Side.upper 0 0) = B-1
      rw [hOwnC,hOwnJ,hOC.1,hOC.2]
      constructor <;> omega
    | upper =>
      change
        min (H-1-ρ.chainExt Side.upper 0 0) (K-1-ρ.joinExt Side.upper 0 0) =
          min (H-1) (K-M)-1 ∧
        min (B-1-ρ.chainExt Side.lower 0 0) (K-1-ρ.joinExt Side.lower 0 0) = B-1
      rw [hOwnC,hOwnJ,hOC.1,hOC.2]
      constructor <;> omega

  have hLeafExposed (B H K M : ℕ) (hB : 3 ≤ B) (hBK : B ≤ K)
      (hH : 3 ≤ H) (hHK : H ≤ K) (hM : 1 ≤ M) (hMK : M ≤ K-2)
      (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some Letter.child)
      (hl : w.getLast? = some (Letter.ext 1 v))
      (p : ℕ) (ps : List ℕ)
      (hcp : (mkRoot B H K M v w).childPositions = p :: ps) (hne : ps ≠ []) :
      ((mkRoot B H K M v w).part [p] (opp v) (K-B+1)).bound =
        decomposableThreshold (B-1) (min (H-1) (K-M)) K := by
    let ρ := mkRoot B H K M v w
    let c := K-B+1
    let V := min (H-1) (K-M)
    let leaf := ρ.part [p] (opp v) c
    have hcp : ρ.childPositions = p :: ps := hcp
    have hpzero := hFirstIsZero ρ hf p ps hcp
    have hp : p ∈ ρ.childPositions := by simp [hcp]
    have hlt := hFirstTail ρ p ps hcp
    obtain ⟨q,hq⟩ := List.exists_mem_of_ne_nil ps hne
    have hqρ : q ∈ ρ.childPositions := by simp [hcp,hq]
    have hqp : p < q := hlt q hq
    have hpos := hRootPositive ρ v hw
    have hExt : leaf.extPositions 1 = ρ.childPositions.filter (· ∉ [p]) :=
      part_extPositions_one hpos [p] (opp v) c
    have hFresh : q ∈ leaf.extPositions 1 := by
      rw [hExt]
      simp [hqρ,show q ≠ p by omega]
    have hSide : leaf.sideAt 1 = opp v :=
      part_sideAt_one_of_mem hpos [p] (opp v) c hFresh
    obtain ⟨y,hy,hbracket⟩ := hLastFacts ρ v hf hl
    have hOldSide := hSideOne ρ v hw ⟨y,hy⟩
    have hOldOther := hOtherLevels ρ v (opp v) M rfl hOldSide
      (by cases v <;> simp [opp])
    have hLevels : leaf.levelsOn (opp v) 0 = [1] := by
      rw [part_levelsOn_self_zero hSide,hOldOther]
      rfl
    have hNoLeft : ∀ x ∈ leaf.extPositions 1, ¬ x < p := by
      intro x hx
      rw [hExt] at hx
      have hxρ := (List.mem_filter.mp hx).1
      have hxn : x ≠ p := by simpa using (List.mem_filter.mp hx).2
      rw [hcp] at hxρ
      rcases List.mem_cons.mp hxρ with he | ht
      · exact False.elim (hxn he)
      · have hpx := hlt x ht
        omega
    have hLeft := hSingleLeftZero leaf (opp v) 1 p hLevels hNoLeft
    have hRight := hSingleRight leaf (opp v) 1 p hLevels ⟨q,hFresh,hqp⟩
    have hOC : leaf.chainExt (opp v) p p = 1 := by
      simp [chainExt,hLeft,hRight]
    have hNewMax : leaf.maximumAt 1 = c := by simp [maximumAt,leaf,part]
    have hc1 : 1 ≤ c := by dsimp [c]; omega
    have hOJ : leaf.joinExt (opp v) p p = c := by
      rw [hSingleJoin leaf (opp v) 1 p p (by omega) hLevels,hOC,hNewMax]
      omega
    have hSideNe : leaf.sideAt 1 ≠ v := by
      rw [hSide]
      cases v <;> simp [opp]
    have hOwnC := chainExt_part_other (σ := ρ) (keep := [p])
      (s := opp v) (m := c) hSideNe p p
    have hOwnJ := joinExt_part_other (σ := ρ) (keep := [p])
      (s := opp v) (m := c) hSideNe p p
    have hRP : ownLimit ρ v p p = V-1 ∧ otherLimit ρ v p p = B-1 := by
      simpa only [hpzero] using hExposedPoint B H K M hB hBK hH hHK hM hMK v w hw hf hl
    have hOwn : ownLimit leaf v p p = V-1 := by
      cases v with
      | lower =>
        dsimp only [ownLimit] at hRP ⊢
        change min (H-1-leaf.chainExt Side.lower p p)
          (K-1-leaf.joinExt Side.lower p p) = V-1
        rw [hOwnC,hOwnJ]
        exact hRP.1
      | upper =>
        dsimp only [ownLimit] at hRP ⊢
        change min (H-1-leaf.chainExt Side.upper p p)
          (K-1-leaf.joinExt Side.upper p p) = V-1
        rw [hOwnC,hOwnJ]
        exact hRP.1
    have hOther : otherLimit leaf v p p = B-2 := by
      cases v with
      | lower =>
        change min (B-1-leaf.chainExt Side.upper p p)
          (K-1-leaf.joinExt Side.upper p p) = B-2
        change leaf.chainExt Side.upper p p = 1 at hOC
        change leaf.joinExt Side.upper p p = c at hOJ
        rw [hOC,hOJ]
        dsimp [c]
        omega
      | upper =>
        change min (B-1-leaf.chainExt Side.lower p p)
          (K-1-leaf.joinExt Side.lower p p) = B-2
        change leaf.chainExt Side.lower p p = 1 at hOC
        change leaf.joinExt Side.lower p p = c at hOJ
        rw [hOC,hOJ]
        dsimp [c]
        omega
    change leaf.bound = decomposableThreshold (B-1) V K
    rw [ctx_singleton_part_bound_eq_threshold ρ p hp (opp v) c]
    have hV2 : 2 ≤ V := by dsimp [V]; omega
    have hVk : V ≤ K := by dsimp [V]; omega
    have hbe : B-2+1 = B-1 := by omega
    have hve : V-1+1 = V := by omega
    cases v with
    | lower =>
      dsimp only [ownLimit,otherLimit] at hOwn hOther
      rw [hOwn,hOther,hbe,hve]
    | upper =>
      dsimp only [ownLimit,otherLimit] at hOwn hOther
      rw [hOwn,hOther,hbe,hve]
      simpa only [ρ,mkRoot] using
        hThresholdComm (a := V) (u := B-1) (k := K) hV2 (by omega) hVk (by omega)
  let mergePrefix (ρ : Context) : Context :=
    { ρ with
      word := ρ.word.map mergeLetter
      maxima := [max (ρ.maximumAt 1) (ρ.maximumAt 2+1)] ++ ρ.maxima.drop 2 }
  have hMergePrefixLength (ρ : Context) :
      (mergePrefix ρ).word.length = ρ.word.length := by simp [mergePrefix]
  have hMergePrefixLetter (ρ : Context) (x : ℕ) :
      (mergePrefix ρ).letterAt x = mergeLetter (ρ.letterAt x) := by
    simp only [mergePrefix,letterAt,List.getElem?_map]
    cases ρ.word[x]? <;> rfl

  have hComplementPrefix (B H K M : ℕ) (hHk : H ≤ K)
      (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some Letter.child)
      (hl : w.getLast? = some (Letter.ext 1 v))
      (p : ℕ) (ps : List ℕ)
      (hcp : (mkRoot B H K M v w).childPositions = p :: ps) (hne : ps ≠ []) :
      ∃ w' : List Letter,
        (∀ z ∈ w', z = Letter.child ∨ z = Letter.ext 1 v) ∧
        w'.head? = some (Letter.ext 1 v) ∧
        w'.getLast? = some (Letter.ext 1 v) ∧
        Letter.child ∈ w' ∧
        ((mkRoot B H K M v w).part ps v (B-2)).bound =
          (mkRoot B H K (max (B-2) (M+1)) v w').bound := by
    let ρ := mkRoot B H K M v w
    let δ := ρ.part ps v (B-2)
    let τ := mergePrefix δ
    have hcp : ρ.childPositions = p :: ps := hcp
    have hpzero := hFirstIsZero ρ hf p ps hcp
    have hlt := hFirstTail ρ p ps hcp
    have hnot : p ∉ ps := by
      intro hp
      have h := hlt p hp
      omega
    have hpos := hRootPositive ρ v hw
    have hShapeδ := hPartShape ρ v hw ps v (B-2)
    have hδpos : ∀ x j t, δ.letterAt x = Letter.ext j t → 1 ≤ j := by
      intro x j t hx
      rcases hShapeδ x j t hx with h | h <;> omega
    have hsole : δ.extPositions 1 = [p] := by
      rw [part_extPositions_one hpos,hcp]
      simp [hnot]
    have hside : δ.sideAt 1 = v :=
      part_sideAt_one_of_mem hpos ps v (B-2) (q := p) (by rw [hsole]; simp)
    obtain ⟨y,hy,hbracket⟩ := hLastFacts ρ v hf hl
    have hsideρ := hSideOne ρ v hw ⟨y,hy⟩
    have hside2 : δ.sideAt 2 = v := by
      rw [part_sideAt_succ ρ ps v (B-2) (by omega : 1 ≤ 1),hsideρ]
    have hInv : Inv δ 1 := by
      refine ⟨by omega,?_,?_,?_⟩
      · simp [δ,part,ρ,mkRoot]
      · intro x j t hx _
        rcases hShapeδ x j t hx with h | h <;> simpa [hside] using h.2
      · rw [hside,hside2]
    have hafter : ∀ y ∈ δ.extPositions 2, p < y := by
      intro y hy
      rw [part_extPositions_succ ρ ps v (B-2) (by omega : 1 ≤ 1)] at hy
      have hh := hOldAfterZero ρ hf y hy
      omega
    have hchildren : ∀ q ∈ δ.childPositions, p < q := by
      intro q hq
      rw [part_childPositions] at hq
      have hqps : q ∈ ps := of_decide_eq_true (List.mem_filter.mp hq).2
      exact hlt q hqps
    have hyounger : ∀ j ∈ δ.levelsOn (δ.sideAt 1) 1,
        ∀ q ∈ δ.extPositions j, p < q := by
      simp [levelsOn_one]
    have holdest : ∀ j ∈ δ.levelsOn (δ.sideAt 1) 0, j ≤ 2 := by
      intro j hj
      have hj' : j ∈ δ.levels := (List.mem_filter.mp hj).1
      simp [levels,δ,part,ρ,mkRoot] at hj'
      omega
    have hglobal :
        (match δ.sideAt 1 with | Side.lower => δ.u | Side.upper => δ.a) ≤ δ.k := by
      rw [hside]
      cases v <;> simpa [δ,part,ρ,mkRoot] using hHk
    have hEq := (hPrefixMerge δ hδpos 1 p hInv hsole hafter hchildren hyounger holdest hglobal).2.2
    change δ.bound = τ.bound at hEq
    have hFields : τ = mkRoot B H K (max (B-2) (M+1)) v τ.word := by
      apply MergeLevels.ctx_ext
      · rfl
      · rfl
      · rfl
      · rfl
      · simp [τ,mergePrefix,maximumAt,δ,part,ρ,mkRoot]
    have hUniform : ∀ z ∈ τ.word, z = Letter.child ∨ z = Letter.ext 1 v := by
      intro z hz
      obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hz
      obtain ⟨x,hx⟩ := List.mem_iff_getElem?.mp hold
      have hOld : δ.letterAt x = old := by simp [letterAt,hx]
      cases old with
      | child => exact Or.inl rfl
      | ext j t =>
        rcases hShapeδ x j t hOld with h | h
        · obtain ⟨rfl,rfl⟩ := h
          exact Or.inr rfl
        · obtain ⟨rfl,rfl⟩ := h
          exact Or.inr rfl
    have hlen : 1 ≤ ρ.word.length := by
      have hh := (hChildZero ρ hf).1
      omega
    have hδzero : δ.letterAt 0 = Letter.ext 1 v := by
      have hnot0 : 0 ∉ ps := by simpa only [hpzero] using hnot
      rw [part_letterAt_of_child ρ ps v (B-2)
        (hChildZero ρ hf).1 (hChildZero ρ hf).2.1,if_neg hnot0]

    have hδlast : δ.letterAt (δ.word.length-1) = Letter.ext 2 v := by
      rw [part_word_length]
      apply part_letterAt_of_ext ρ ps v (B-2) (by omega)
      unfold letterAt
      rw [← List.getLast?_eq_getElem?,hl]
      rfl
    have hτzero : τ.letterAt 0 = Letter.ext 1 v := by
      rw [hMergePrefixLetter,hδzero]
      rfl
    have hτlast : τ.letterAt (τ.word.length-1) = Letter.ext 1 v := by
      rw [hMergePrefixLength,hMergePrefixLetter,hδlast]
      rfl
    have hτlen : 1 ≤ τ.word.length := by
      rw [hMergePrefixLength,part_word_length]
      exact hlen
    have hFirst : τ.word.head? = some (Letter.ext 1 v) := by
      rw [List.head?_eq_getElem?]
      apply List.getElem?_eq_some_iff.mpr
      refine ⟨by omega,?_⟩
      simpa [letterAt,show 0 < τ.word.length by omega] using hτzero
    have hLast : τ.word.getLast? = some (Letter.ext 1 v) := by
      rw [List.getLast?_eq_getElem?]
      apply List.getElem?_eq_some_iff.mpr
      refine ⟨by omega,?_⟩
      simpa [letterAt,show τ.word.length-1 < τ.word.length by omega] using hτlast
    obtain ⟨q,hq⟩ := List.exists_mem_of_ne_nil ps hne
    have hqρ : q ∈ ρ.childPositions := by simp [hcp,hq]
    have hqmem := hChildMem ρ q hqρ
    have hδq : δ.letterAt q = Letter.child := by
      rw [part_letterAt_of_child ρ ps v (B-2) hqmem.1 hqmem.2,if_pos hq]
    have hτq : τ.letterAt q = Letter.child := by
      rw [hMergePrefixLetter,hδq]
    have hqlen : q < τ.word.length := by
      rw [hMergePrefixLength,part_word_length]
      exact hqmem.1
    have hChild : Letter.child ∈ τ.word := by
      have hget : τ.word[q] = Letter.child := by simpa [letterAt,hqlen] using hτq
      rw [← hget]
      exact List.getElem_mem _
    exact ⟨τ.word,hUniform,hFirst,hLast,hChild,hEq.trans (congrArg Context.bound hFields)⟩

  have hExposedLower (H M : ℕ) (hH : 3 ≤ H) (hHk : H ≤ k)
      (hM : 1 ≤ M) (hMk : M ≤ k-2) (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some Letter.child)
      (hl : w.getLast? = some (Letter.ext 1 v))
      (hc : Letter.child ∈ w) :
      decomposableThreshold A (min (H-1) (k-M)) k ≤ (mkRoot A H k M v w).bound := by
    let ρ := mkRoot A H k M v w
    let V := min (H-1) (k-M)
    have hV2 : 2 ≤ V := by dsimp [V]; omega
    have hVk : V ≤ k := by dsimp [V]; omega
    change decomposableThreshold A V k ≤ ρ.bound
    have hExist := hChildExists ρ hc
    cases hcp : ρ.childPositions with
    | nil =>
      obtain ⟨p,hp⟩ := hExist
      rw [hcp] at hp
      cases hp
    | cons p ps =>
      have hhead : ρ.childPositions.head? = some p := by rw [hcp]; rfl
      have hpzero := hFirstIsZero ρ hf p ps hcp
      have hBase : ρ.base = decomposableThreshold A V k := by
        have hLimits :
            ownLimit ρ v 0 0 = V-1 ∧ otherLimit ρ v 0 0 = A-1 :=
          hExposedPoint A H k M hA hAk hH hHk hM hMk v w hw hf hl
        have hcK : ρ.cupLimit 0 0 ≤ k-1 := by
          change min (ρ.u-1-ρ.chainExt Side.lower 0 0)
            (k-1-ρ.joinExt Side.lower 0 0) ≤ k-1
          omega
        have hplK : ρ.capLimit 0 0 ≤ k-1 := by
          change min (ρ.a-1-ρ.chainExt Side.upper 0 0)
            (k-1-ρ.joinExt Side.upper 0 0) ≤ k-1
          omega
        rw [base_eq_baseOf,hhead]
        change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) k =
          decomposableThreshold A V k
        rw [hpzero,hBaseValue _ _ _ hcK hplK]
        have hAe : A-1+1 = A := by omega
        have hVe : V-1+1 = V := by omega
        cases v with
        | lower =>
          dsimp only [ownLimit,otherLimit] at hLimits
          rw [hLimits.1,hLimits.2,hAe,hVe]
        | upper =>
          dsimp only [ownLimit,otherLimit] at hLimits
          rw [hLimits.1,hLimits.2,hAe,hVe]
          exact hThresholdComm hV2 (by omega) hVk hAk
      by_cases hr : ρ.numRuns ≤ 1
      · rw [bound,boundFuel.eq_2,if_pos hr,hBase]
      · have hRuns : 2 ≤ ρ.numRuns := by omega
        have hlen := numRuns_le_length ρ
        have hne : ps ≠ [] := by
          intro he
          rw [hcp,he] at hlen
          simp only [List.length_cons,List.length_nil] at hlen
          omega
        obtain ⟨hBlock,hRest⟩ := hFirstBlock ρ p ps hcp hne
        let W := min (H-2) (k-max (A-2) (M+1))
        have hW : W = min (V-1) (k-A+2) := by dsimp [W,V]; omega
        obtain ⟨w',hw',hf',hl',hc',hCompEq⟩ :=
          hComplementPrefix A H k M hHk v w hw hf hl p ps hcp hne
        have hComp : decomposableThreshold A W k ≤ (ρ.part ps v (A-2)).bound := by
          rw [hCompEq]
          by_cases hW2 : 2 ≤ W
          · have hGpred : 4 ≤ H := by dsimp [W] at hW2; omega
            have hMpred : max (A-2) (M+1) ≤ k-2 := by dsimp [W] at hW2; omega
            exact hLowerAll H hGpred (by omega)
              (max (A-2) (M+1)) (by omega) hMpred v w' hw' hf' hl' hc'
          · have hW1 : W = 1 := by dsimp [W]; omega
            rw [hW1,decomposableThreshold_one_right]
            exact Nat.zero_le _
        have hLeafEq :
            (ρ.part [p] (opp v) (k-A+1)).bound = decomposableThreshold (A-1) V k :=
          hLeafExposed A H k M hA hAk hH hHk hM hMk v w hw hf hl p ps hcp hne
        have hLower :
            decomposableThreshold A V k ≤
              (ρ.part [p] (opp v) (k-A+1)).bound + (ρ.part ps v (A-2)).bound := by
          calc
            decomposableThreshold A V k =
                decomposableThreshold (A-1) V k + decomposableThreshold A W k := by
              rw [hW]
              exact hPascal A V k hA hAk hV2 hVk
            _ ≤ _ := Nat.add_le_add hLeafEq.symm.le hComp
        have hCut :
            (ρ.part [p] (opp v) (k-A+1)).bound + (ρ.part ps v (A-2)).bound ≤ ρ.bound := by
          cases v with
          | lower =>
            have hcut := (ctx_bound_cut_le ρ hRuns [p] hBlock (A-2)
              (by omega) (by change A-2 ≤ k-2; omega)).2
            have he : k-1-(A-2) = k-A+1 := by omega
            simpa only [opp,show ρ.k = k from rfl,he,hRest] using hcut
          | upper =>
            have hcut := (ctx_bound_cut_le ρ hRuns [p] hBlock (k-A+1)
              (by omega) (by change k-A+1 ≤ k-2; omega)).1
            have he : k-1-(k-A+1) = A-2 := by omega
            simpa only [opp,show ρ.k = k from rfl,he,hRest] using hcut
        exact hLower.trans hCut
  have hRootWF (M : ℕ) (hM : 1 ≤ M) (hMk : M ≤ k-2)
      (a u : ℕ) (ha2 : 2 ≤ a) (hu2 : 2 ≤ u)
      (hak : a ≤ k) (huk : u ≤ k) (v : Side) (w : List Letter)
      (hw : ∀ x ∈ w, x = Letter.child ∨ x = Letter.ext 1 v) :
      ({a := a, u := u, k := k, word := w, maxima := [M]} : Context).WellFormed := by
    let τ : Context := {a := a, u := u, k := k, word := w, maxima := [M]}
    have hshape : ∀ p l t, τ.letterAt p = Letter.ext l t → l = 1 ∧ t = v := by
      intro p l t hext
      have hp : p < τ.word.length := by
        by_contra hn
        have h := letterAt_of_length_le τ (Nat.le_of_not_gt hn)
        rw [h] at hext
        cases hext
      have hmem : Letter.ext l t ∈ w := by
        have hget : τ.word[p] = Letter.ext l t := by
          simpa [letterAt, hp] using hext
        rw [← hget]
        exact List.getElem_mem _
      rcases hw _ hmem with h | h
      · cases h
      · cases h
        exact ⟨rfl, rfl⟩
    refine ⟨ha2, hu2, hak, huk, ?_, ?_⟩
    · intro n hn
      simp only [List.mem_singleton] at hn
      subst n
      exact ⟨hM, hMk⟩
    · intro p l t hext
      change τ.letterAt p = Letter.ext l t at hext
      obtain ⟨rfl, rfl⟩ := hshape p l t hext
      refine ⟨by omega, by simp, ?_⟩
      have hpExt : p ∈ τ.extPositions 1 := by
        have hp : p < τ.word.length := by
          by_contra hn
          have h := letterAt_of_length_le τ (Nat.le_of_not_gt hn)
          rw [h] at hext
          cases hext
        simp [extPositions, hp, hext]
      cases hh : (τ.extPositions 1).head? with
      | none =>
        have hn := List.head?_eq_none_iff.mp hh
        rw [hn] at hpExt
        simp at hpExt
      | some q =>
        have hq := List.mem_of_mem_head? hh
        have hqe := (List.mem_filter.mp hq).2
        cases hl : τ.letterAt q with
        | child => simp [hl] at hqe
        | ext j v =>
          obtain ⟨rfl, rfl⟩ := hshape q j v hl
          change v = τ.sideAt 1
          simp [sideAt, hh, hl]

  have hMarkedLower (H M : ℕ) (hH : 3 ≤ H) (hHk : H ≤ k)
      (hM : 1 ≤ M) (hMk : M ≤ k-2) (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some (Letter.ext 1 v))
      (hl : w.getLast? = some Letter.child)
      (hc : Letter.child ∈ w) :
      decomposableThreshold A (min (H-1) (k-M)) k ≤ (mkRoot A H k M v w).bound := by
    let σ := mkRoot A H k M v w
    have hσwf : σ.WellFormed := by
      cases v with
      | lower =>
        exact hRootWF M hM hMk A H (by omega) (by omega) hAk hHk Side.lower w hw
      | upper =>
        exact hRootWF M hM hMk H A (by omega) (by omega) hHk hAk Side.upper w hw
    have hwrev : ∀ z ∈ w.reverse, z = Letter.child ∨ z = Letter.ext 1 v := by
      intro z hz
      exact hw z (List.mem_reverse.mp hz)
    have hfrev : w.reverse.head? = some Letter.child := by simpa using hl
    have hlrev : w.reverse.getLast? = some (Letter.ext 1 v) := by simpa using hf
    have hcrev : Letter.child ∈ w.reverse := List.mem_reverse.mpr hc
    have hLower := hExposedLower H M hH hHk hM hMk v w.reverse hwrev hfrev hlrev hcrev
    have hEq : (mkRoot A H k M v w.reverse).bound = σ.bound :=
      ctx_bound_reverse σ hσwf
    rw [hEq] at hLower
    exact hLower
  have hMarkerExists (ρ : Context) (v : Side)
      (hmark : Letter.ext 1 v ∈ ρ.word) : ∃ x, x ∈ ρ.extPositions 1 := by
    obtain ⟨x,hx⟩ := List.mem_iff_getElem?.mp hmark
    have hxl : x < ρ.word.length := (List.getElem?_eq_some_iff.mp hx).1
    have hletter : ρ.letterAt x = Letter.ext 1 v := by simp [letterAt,hx]
    exact ⟨x,by simp [extPositions,hxl,hletter]⟩
  have hAnyExposedPoint (B H K M : ℕ) (hB : 3 ≤ B) (hBK : B ≤ K)
      (hH : 3 ≤ H) (hHK : H ≤ K) (hM : 1 ≤ M) (hMK : M ≤ K-2)
      (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some Letter.child)
      (hmark : Letter.ext 1 v ∈ w) :
      ownLimit (mkRoot B H K M v w) v 0 0 = min (H-1) (K-M)-1 ∧
      otherLimit (mkRoot B H K M v w) v 0 0 = B-1 := by
    let ρ := mkRoot B H K M v w
    obtain ⟨y,hy⟩ := hMarkerExists ρ v hmark
    have hypos := hOldAfterZero ρ hf y hy
    have hs := hSideOne ρ v hw ⟨y,hy⟩
    have hls := hRootLevels ρ v M rfl hs
    have hleft := hSingleLeftZero ρ v 1 0 hls (fun x _ => by omega)
    have hright := hSingleRight ρ v 1 0 hls
      ⟨y,hy,hypos⟩
    have hOwnC : ρ.chainExt v 0 0 = 1 := by simp [chainExt,hleft,hright]
    have hOwnJ : ρ.joinExt v 0 0 = M := by
      rw [hSingleJoin ρ v 1 0 0 (by omega) hls,hOwnC]
      simp [maximumAt,ρ,mkRoot,show 1 ≤ M from hM]
    have hOtherLs := hOtherLevels ρ v (opp v) M rfl hs
      (by cases v <;> simp [opp])
    have hOC := hEmptyAxis ρ (opp v) 0 0 hOtherLs
    cases v with
    | lower =>
      change
        min (H-1-ρ.chainExt Side.lower 0 0) (K-1-ρ.joinExt Side.lower 0 0) =
          min (H-1) (K-M)-1 ∧
        min (B-1-ρ.chainExt Side.upper 0 0) (K-1-ρ.joinExt Side.upper 0 0) = B-1
      rw [hOwnC,hOwnJ,hOC.1,hOC.2]
      constructor <;> omega
    | upper =>
      change
        min (H-1-ρ.chainExt Side.upper 0 0) (K-1-ρ.joinExt Side.upper 0 0) =
          min (H-1) (K-M)-1 ∧
        min (B-1-ρ.chainExt Side.lower 0 0) (K-1-ρ.joinExt Side.lower 0 0) = B-1
      rw [hOwnC,hOwnJ,hOC.1,hOC.2]
      constructor <;> omega
  have hLeafAnyExposed (B H K M : ℕ) (hB : 3 ≤ B) (hBK : B ≤ K)
      (hH : 3 ≤ H) (hHK : H ≤ K) (hM : 1 ≤ M) (hMK : M ≤ K-2)
      (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some Letter.child)
      (hmark : Letter.ext 1 v ∈ w)
      (p : ℕ) (ps : List ℕ)
      (hcp : (mkRoot B H K M v w).childPositions = p :: ps) (hne : ps ≠ []) :
      ((mkRoot B H K M v w).part [p] (opp v) (K-B+1)).bound =
        decomposableThreshold (B-1) (min (H-1) (K-M)) K := by
    let ρ := mkRoot B H K M v w
    let c := K-B+1
    let V := min (H-1) (K-M)
    let leaf := ρ.part [p] (opp v) c
    have hcp : ρ.childPositions = p :: ps := hcp
    have hpzero := hFirstIsZero ρ hf p ps hcp
    have hp : p ∈ ρ.childPositions := by simp [hcp]
    have hlt := hFirstTail ρ p ps hcp
    obtain ⟨q,hq⟩ := List.exists_mem_of_ne_nil ps hne
    have hqρ : q ∈ ρ.childPositions := by simp [hcp,hq]
    have hqp : p < q := hlt q hq
    have hpos := hRootPositive ρ v hw
    have hExt : leaf.extPositions 1 = ρ.childPositions.filter (· ∉ [p]) :=
      part_extPositions_one hpos [p] (opp v) c
    have hFresh : q ∈ leaf.extPositions 1 := by
      rw [hExt]
      simp [hqρ,show q ≠ p by omega]
    have hSide : leaf.sideAt 1 = opp v :=
      part_sideAt_one_of_mem hpos [p] (opp v) c hFresh
    obtain ⟨y,hy⟩ := hMarkerExists ρ v hmark
    have hOldSide := hSideOne ρ v hw ⟨y,hy⟩
    have hOldOther := hOtherLevels ρ v (opp v) M rfl hOldSide
      (by cases v <;> simp [opp])
    have hLevels : leaf.levelsOn (opp v) 0 = [1] := by
      rw [part_levelsOn_self_zero hSide,hOldOther]
      rfl
    have hNoLeft : ∀ x ∈ leaf.extPositions 1, ¬ x < p := by
      intro x hx
      rw [hExt] at hx
      have hxρ := (List.mem_filter.mp hx).1
      have hxn : x ≠ p := by simpa using (List.mem_filter.mp hx).2
      rw [hcp] at hxρ
      rcases List.mem_cons.mp hxρ with he | ht
      · exact False.elim (hxn he)
      · have hpx := hlt x ht
        omega
    have hLeft := hSingleLeftZero leaf (opp v) 1 p hLevels hNoLeft
    have hRight := hSingleRight leaf (opp v) 1 p hLevels ⟨q,hFresh,hqp⟩
    have hOC : leaf.chainExt (opp v) p p = 1 := by
      simp [chainExt,hLeft,hRight]
    have hNewMax : leaf.maximumAt 1 = c := by simp [maximumAt,leaf,part]
    have hc1 : 1 ≤ c := by dsimp [c]; omega
    have hOJ : leaf.joinExt (opp v) p p = c := by
      rw [hSingleJoin leaf (opp v) 1 p p (by omega) hLevels,hOC,hNewMax]
      omega
    have hSideNe : leaf.sideAt 1 ≠ v := by
      rw [hSide]
      cases v <;> simp [opp]
    have hOwnC := chainExt_part_other (σ := ρ) (keep := [p])
      (s := opp v) (m := c) hSideNe p p
    have hOwnJ := joinExt_part_other (σ := ρ) (keep := [p])
      (s := opp v) (m := c) hSideNe p p
    have hRP : ownLimit ρ v p p = V-1 ∧ otherLimit ρ v p p = B-1 := by
      simpa only [hpzero] using hAnyExposedPoint B H K M hB hBK hH hHK hM hMK v w hw hf hmark
    have hOwn : ownLimit leaf v p p = V-1 := by
      cases v with
      | lower =>
        dsimp only [ownLimit] at hRP ⊢
        change min (H-1-leaf.chainExt Side.lower p p)
          (K-1-leaf.joinExt Side.lower p p) = V-1
        rw [hOwnC,hOwnJ]
        exact hRP.1
      | upper =>
        dsimp only [ownLimit] at hRP ⊢
        change min (H-1-leaf.chainExt Side.upper p p)
          (K-1-leaf.joinExt Side.upper p p) = V-1
        rw [hOwnC,hOwnJ]
        exact hRP.1
    have hOther : otherLimit leaf v p p = B-2 := by
      cases v with
      | lower =>
        change min (B-1-leaf.chainExt Side.upper p p)
          (K-1-leaf.joinExt Side.upper p p) = B-2
        change leaf.chainExt Side.upper p p = 1 at hOC
        change leaf.joinExt Side.upper p p = c at hOJ
        rw [hOC,hOJ]
        dsimp [c]
        omega
      | upper =>
        change min (B-1-leaf.chainExt Side.lower p p)
          (K-1-leaf.joinExt Side.lower p p) = B-2
        change leaf.chainExt Side.lower p p = 1 at hOC
        change leaf.joinExt Side.lower p p = c at hOJ
        rw [hOC,hOJ]
        dsimp [c]
        omega
    change leaf.bound = decomposableThreshold (B-1) V K
    rw [ctx_singleton_part_bound_eq_threshold ρ p hp (opp v) c]
    have hV2 : 2 ≤ V := by dsimp [V]; omega
    have hVk : V ≤ K := by dsimp [V]; omega
    have hbe : B-2+1 = B-1 := by omega
    have hve : V-1+1 = V := by omega
    cases v with
    | lower =>
      dsimp only [ownLimit,otherLimit] at hOwn hOther
      rw [hOwn,hOther,hbe,hve]
    | upper =>
      dsimp only [ownLimit,otherLimit] at hOwn hOther
      rw [hOwn,hOther,hbe,hve]
      simpa only [ρ,mkRoot] using
        hThresholdComm (a := V) (u := B-1) (k := K) hV2 (by omega) hVk (by omega)
  have hComplementNeither (B H K M : ℕ) (hHk : H ≤ K)
      (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hf : w.head? = some Letter.child)
      (hl : w.getLast? = some Letter.child)
      (hmark : Letter.ext 1 v ∈ w)
      (p : ℕ) (ps : List ℕ)
      (hcp : (mkRoot B H K M v w).childPositions = p :: ps) (hne : ps ≠ []) :
      ∃ w' : List Letter,
        (∀ z ∈ w', z = Letter.child ∨ z = Letter.ext 1 v) ∧
        w'.head? = some (Letter.ext 1 v) ∧
        w'.getLast? = some Letter.child ∧
        Letter.child ∈ w' ∧
        ((mkRoot B H K M v w).part ps v (B-2)).bound =
          (mkRoot B H K (max (B-2) (M+1)) v w').bound := by
    let ρ := mkRoot B H K M v w
    let δ := ρ.part ps v (B-2)
    let τ := mergePrefix δ
    have hcp : ρ.childPositions = p :: ps := hcp
    have hpzero := hFirstIsZero ρ hf p ps hcp
    have hlt := hFirstTail ρ p ps hcp
    have hnot : p ∉ ps := by
      intro hp
      have h := hlt p hp
      omega
    have hpos := hRootPositive ρ v hw
    have hShapeδ := hPartShape ρ v hw ps v (B-2)
    have hδpos : ∀ x j t, δ.letterAt x = Letter.ext j t → 1 ≤ j := by
      intro x j t hx
      rcases hShapeδ x j t hx with h | h <;> omega
    have hsole : δ.extPositions 1 = [p] := by
      rw [part_extPositions_one hpos,hcp]
      simp [hnot]
    have hside : δ.sideAt 1 = v :=
      part_sideAt_one_of_mem hpos ps v (B-2) (q := p) (by rw [hsole]; simp)
    obtain ⟨y,hy⟩ := hMarkerExists ρ v hmark
    have hsideρ := hSideOne ρ v hw ⟨y,hy⟩
    have hside2 : δ.sideAt 2 = v := by
      rw [part_sideAt_succ ρ ps v (B-2) (by omega : 1 ≤ 1),hsideρ]
    have hInv : Inv δ 1 := by
      refine ⟨by omega,?_,?_,?_⟩
      · simp [δ,part,ρ,mkRoot]
      · intro x j t hx _
        rcases hShapeδ x j t hx with h | h <;> simpa [hside] using h.2
      · rw [hside,hside2]
    have hafter : ∀ y ∈ δ.extPositions 2, p < y := by
      intro y hy
      rw [part_extPositions_succ ρ ps v (B-2) (by omega : 1 ≤ 1)] at hy
      have hh := hOldAfterZero ρ hf y hy
      omega
    have hchildren : ∀ q ∈ δ.childPositions, p < q := by
      intro q hq
      rw [part_childPositions] at hq
      have hqps : q ∈ ps := of_decide_eq_true (List.mem_filter.mp hq).2
      exact hlt q hqps
    have hyounger : ∀ j ∈ δ.levelsOn (δ.sideAt 1) 1,
        ∀ q ∈ δ.extPositions j, p < q := by
      simp [levelsOn_one]
    have holdest : ∀ j ∈ δ.levelsOn (δ.sideAt 1) 0, j ≤ 2 := by
      intro j hj
      have hj' : j ∈ δ.levels := (List.mem_filter.mp hj).1
      simp [levels,δ,part,ρ,mkRoot] at hj'
      omega
    have hglobal :
        (match δ.sideAt 1 with | Side.lower => δ.u | Side.upper => δ.a) ≤ δ.k := by
      rw [hside]
      cases v <;> simpa [δ,part,ρ,mkRoot] using hHk
    have hEq := (hPrefixMerge δ hδpos 1 p hInv hsole hafter hchildren hyounger holdest hglobal).2.2
    change δ.bound = τ.bound at hEq
    have hFields : τ = mkRoot B H K (max (B-2) (M+1)) v τ.word := by
      apply MergeLevels.ctx_ext
      · rfl
      · rfl
      · rfl
      · rfl
      · simp [τ,mergePrefix,maximumAt,δ,part,ρ,mkRoot]
    have hUniform : ∀ z ∈ τ.word, z = Letter.child ∨ z = Letter.ext 1 v := by
      intro z hz
      obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hz
      obtain ⟨x,hx⟩ := List.mem_iff_getElem?.mp hold
      have hOld : δ.letterAt x = old := by simp [letterAt,hx]
      cases old with
      | child => exact Or.inl rfl
      | ext j t =>
        rcases hShapeδ x j t hOld with h | h
        · obtain ⟨rfl,rfl⟩ := h
          exact Or.inr rfl
        · obtain ⟨rfl,rfl⟩ := h
          exact Or.inr rfl
    have hlen : 1 ≤ ρ.word.length := by
      have hh := (hChildZero ρ hf).1
      omega
    have hδzero : δ.letterAt 0 = Letter.ext 1 v := by
      have hnot0 : 0 ∉ ps := by simpa only [hpzero] using hnot
      rw [part_letterAt_of_child ρ ps v (B-2)
        (hChildZero ρ hf).1 (hChildZero ρ hf).2.1,if_neg hnot0]

    obtain ⟨q0,hq0⟩ := List.exists_mem_of_ne_nil ps hne
    have hq0ρ : q0 ∈ ρ.childPositions := by simp [hcp,hq0]
    have hq0len := (hChildMem ρ q0 hq0ρ).1
    have hpq0 := hlt q0 hq0
    have hlen2 : 2 ≤ ρ.word.length := by omega
    have hOriginalLast : ρ.letterAt (ρ.word.length-1) = Letter.child := by
      unfold letterAt
      rw [← List.getLast?_eq_getElem?,hl]
      rfl
    have hLastMem : ρ.word.length-1 ∈ ρ.childPositions := by
      simp [childPositions,show ρ.word.length-1 < ρ.word.length by omega,hOriginalLast]
    have hLastPS : ρ.word.length-1 ∈ ps := by
      rw [hcp] at hLastMem
      rcases List.mem_cons.mp hLastMem with he | ht
      · omega
      · exact ht
    have hδlast : δ.letterAt (δ.word.length-1) = Letter.child := by
      rw [part_word_length]
      rw [part_letterAt_of_child ρ ps v (B-2)
        (by omega) hOriginalLast,if_pos hLastPS]
    have hτzero : τ.letterAt 0 = Letter.ext 1 v := by
      rw [hMergePrefixLetter,hδzero]
      rfl
    have hτlast : τ.letterAt (τ.word.length-1) = Letter.child := by
      rw [hMergePrefixLength,hMergePrefixLetter,hδlast]
    have hτlen : 1 ≤ τ.word.length := by
      rw [hMergePrefixLength,part_word_length]
      exact hlen
    have hFirst : τ.word.head? = some (Letter.ext 1 v) := by
      rw [List.head?_eq_getElem?]
      apply List.getElem?_eq_some_iff.mpr
      refine ⟨by omega,?_⟩
      simpa [letterAt,show 0 < τ.word.length by omega] using hτzero
    have hLast : τ.word.getLast? = some Letter.child := by
      rw [List.getLast?_eq_getElem?]
      apply List.getElem?_eq_some_iff.mpr
      refine ⟨by omega,?_⟩
      simpa [letterAt,show τ.word.length-1 < τ.word.length by omega] using hτlast
    obtain ⟨q,hq⟩ := List.exists_mem_of_ne_nil ps hne
    have hqρ : q ∈ ρ.childPositions := by simp [hcp,hq]
    have hqmem := hChildMem ρ q hqρ
    have hδq : δ.letterAt q = Letter.child := by
      rw [part_letterAt_of_child ρ ps v (B-2) hqmem.1 hqmem.2,if_pos hq]
    have hτq : τ.letterAt q = Letter.child := by
      rw [hMergePrefixLetter,hδq]
    have hqlen : q < τ.word.length := by
      rw [hMergePrefixLength,part_word_length]
      exact hqmem.1
    have hChild : Letter.child ∈ τ.word := by
      have hget : τ.word[q] = Letter.child := by simpa [letterAt,hqlen] using hτq
      rw [← hget]
      exact List.getElem_mem _
    exact ⟨τ.word,hUniform,hFirst,hLast,hChild,hEq.trans (congrArg Context.bound hFields)⟩

  have hUpper (A G k m : ℕ) (hA : A ≤ 3) (side : Ctx.Side) (word : List Ctx.Letter) (hletters : ∀ z ∈ word, z = Ctx.Letter.child ∨ z = Ctx.Letter.ext 1 side) (hmarker : Ctx.Letter.ext 1 side ∈ word) : let σ : Ctx.Context := { a := match side with | Ctx.Side.lower => A | Ctx.Side.upper => G, u := match side with | Ctx.Side.lower => G | Ctx.Side.upper => A, k := k, word := word, maxima := [m] }; (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ ≤ min G (k-m)-1) ∧ σ.bound ≤ min G (k-m)-1 := by
    classical
    have hShape (ρ : Context) (v : Side)
        (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v) :
        ∀ p j w, ρ.letterAt p = Letter.ext j w → j = 1 ∧ w = v := by
      intro p j w hext
      have hp : p < ρ.word.length := by
        by_contra hn
        have h := letterAt_of_length_le ρ (Nat.le_of_not_gt hn)
        rw [h] at hext
        cases hext
      have hget : ρ.word[p] = Letter.ext j w := by
        simpa [letterAt,hp] using hext
      have hmem : Letter.ext j w ∈ ρ.word := by
        rw [← hget]
        exact List.getElem_mem _
      rcases hw _ hmem with h | h
      · cases h
      · cases h
        exact ⟨rfl,rfl⟩
    have hSideOne (ρ : Context) (v : Side)
        (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v)
        (hx : ∃ x, x ∈ ρ.extPositions 1) : ρ.sideAt 1 = v := by
      cases hh : (ρ.extPositions 1).head? with
      | none =>
        obtain ⟨x,hx⟩ := hx
        have hn := List.head?_eq_none_iff.mp hh
        rw [hn] at hx
        exact False.elim (List.not_mem_nil hx)
      | some p =>
        have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        cases he : ρ.letterAt p with
        | child => simp [extPositions,he] at hp
        | ext j w =>
          have hs := (hShape ρ v hw p j w he).2
          simp [sideAt,hh,he,hs]
    have hRootPositive (ρ : Context) (v : Side)
        (hw : ∀ z ∈ ρ.word, z = Letter.child ∨ z = Letter.ext 1 v) :
        ∀ p j w, ρ.letterAt p = Letter.ext j w → 1 ≤ j := by
      intro p j w he
      have hj := (hShape ρ v hw p j w he).1
      omega
    let ρ : Context :=
      { a := match side with | Side.lower => A | Side.upper => G
        u := match side with | Side.lower => G | Side.upper => A
        k := k, word := word, maxima := [m] }
    let H := min G (k-m)
    let τ : Context :=
      { ρ with
        a := match side with | Side.lower => A | Side.upper => H
        u := match side with | Side.lower => H | Side.upper => A
        maxima := [] }
    let opp : Side → Side := fun v => match v with
      | Side.lower => Side.upper | Side.upper => Side.lower
    change (∀ fuel, boundFuel fuel ρ ≤ H-1) ∧ ρ.bound ≤ H-1
    obtain ⟨x,hx⟩ := List.mem_iff_getElem?.mp hmarker
    have hxl : x < ρ.word.length := (List.getElem?_eq_some_iff.mp hx).1
    have hletter : ρ.letterAt x = Letter.ext 1 side := by
      simp [letterAt,ρ,hx]
    have hExt : x ∈ ρ.extPositions 1 := by
      simp [extPositions,hxl,hletter]
    have hSide : ρ.sideAt 1 = side := hSideOne ρ side hletters ⟨x,hExt⟩
    have hN : 1 ∈ ρ.levels := by simp [levels,ρ]
    have hNorm :
        (∀ fuel, boundFuel fuel ρ ≤ boundFuel fuel τ) ∧ ρ.bound ≤ τ.bound := by
      have h := (ctx_sibling_maximum_upper_normalize ρ 1 hN).2
      cases side <;> simpa [hSide,ρ,τ,H,maximumAt] using h
    have hPositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j :=
      hRootPositive τ side hletters
    have hNe : opp side ≠ side := by cases side <;> simp [opp]
    have hSmall :
        (match opp side with | Side.lower => τ.u | Side.upper => τ.a) ≤ 3 := by
      cases side <;> simpa [opp,τ] using hA
    have hRanks := ctx_small_global_axis_rank_region_potential τ hPositive
      (opp side) side hNe hSmall
    have hFuel (fuel : ℕ) : boundFuel fuel τ ≤ H-1 := by
      cases side <;> exact (hRanks.1 fuel).trans hRanks.2.2.1
    have hBound : τ.bound ≤ H-1 := by
      cases side <;> exact hRanks.2.1.trans hRanks.2.2.1
    exact ⟨fun fuel => (hNorm.1 fuel).trans (hFuel fuel),hNorm.2.trans hBound⟩
  have hAttains (v : Side) (w : List Letter)
      (hw : ∀ z ∈ w, z = Letter.child ∨ z = Letter.ext 1 v)
      (hmark : Letter.ext 1 v ∈ w)
      (hf : w.head? = some Letter.child)
      (hl : w.getLast? = some Letter.child)
      (hc : Letter.child ∈ w) :
      let ρ := mkRoot A G k m v w
      2 ≤ ρ.numRuns →
      ∃ p : ℕ, ρ.childPositions.head? = some p ∧
        1 ≤ k-2 ∧ k-2 ≤ k-2 ∧
        ρ.bound ≤
          decomposableThreshold ((ρ.part [p] (opp v) (k-2)).capLimit p p+1)
            ((ρ.part [p] (opp v) (k-2)).cupLimit p p+1) k +
          (ρ.part (ρ.childPositions.filter (fun q => q ≠ p)) v (k-1-(k-2))).bound := by
    let ρ := mkRoot A G k m v w
    change 2 ≤ ρ.numRuns → _
    intro hRuns
    let H := min G (k-m)
    let V := min (G-1) (k-m)
    have hH2 : 2 ≤ H := by dsimp [H]; omega
    have hV2 : 2 ≤ V := by dsimp [V]; omega
    have hVk : V ≤ k := by dsimp [V]; omega
    have hSource : ρ.bound ≤ H-1 := by
      have h := (hUpper A G k m (by rfl) v w hw hmark).2
      cases v <;> exact h
    have hExist := hChildExists ρ hc
    cases hcp : ρ.childPositions with
    | nil =>
      obtain ⟨p,hp⟩ := hExist
      rw [hcp] at hp
      cases hp
    | cons p ps =>
      have hhead : ρ.childPositions.head? = some p := by rw [hcp]; rfl
      have hp : p ∈ ρ.childPositions := by simp [hcp]
      have hlen := numRuns_le_length ρ
      have hne : ps ≠ [] := by
        intro he
        rw [hcp,he] at hlen
        simp only [List.length_cons,List.length_nil] at hlen
        omega
      obtain ⟨hBlock,hRest⟩ := hFirstBlock ρ p ps hcp hne
      have hec : k-A+1 = k-2 := by dsimp [A]; omega
      have hLeafEq : (ρ.part [p] (opp v) (k-2)).bound = 1 := by
        have h := hLeafAnyExposed A G k m hA hAk hG hGk hm hmk
          v w hw hf hmark p ps hcp hne
        rw [hec,show A-1 = 2 from rfl] at h
        rw [decomposableThreshold_eq_choose (by omega) hV2 (by omega)] at h
        simpa using h
      obtain ⟨w',hw',hf',hl',hc',hCompEq⟩ :=
        hComplementNeither A G k m hGk v w hw hf hl hmark p ps hcp hne
      have hM : max (A-2) (m+1) = m+1 := by dsimp [A]; omega
      rw [hM] at hCompEq
      have hComp : H-2 ≤ (ρ.part ps v (A-2)).bound := by
        by_cases hH3 : 3 ≤ H
        · have hMk : m+1 ≤ k-2 := by dsimp [H] at hH3; omega
          have hLower := hMarkedLower G (m+1) hG hGk (by omega) hMk
            v w' hw' hf' hl' hc'
          have hW : min (G-1) (k-(m+1)) = H-1 := by dsimp [H]; omega
          rw [hW] at hLower
          have hThreshold : decomposableThreshold A (H-1) k = H-2 := by
            change decomposableThreshold 3 (H-1) k = H-2
            rw [decomposableThreshold_eq_choose (by omega) (by omega)
              (by dsimp [H]; omega)]
            simp only [show 3+(H-1)-4 = H-2 by omega,
              show 3-2 = 1 from rfl,Nat.choose_one_right]
          rw [hThreshold] at hLower
          rw [hCompEq]
          exact hLower
        · have hHz : H-2 = 0 := by omega
          rw [hHz]
          exact Nat.zero_le _
      have hValue :
          ρ.bound ≤ (ρ.part [p] (opp v) (k-2)).bound +
            (ρ.part ps v (A-2)).bound := by
        rw [hLeafEq]
        omega
      have hRaw := ctx_singleton_part_bound_eq_threshold ρ p hp (opp v) (k-2)
      rw [hRaw] at hValue
      have hFilter : ρ.childPositions.filter (fun q => q ≠ p) = ps := by
        simpa only [List.mem_singleton] using hRest
      have hFilterCons : (p :: ps).filter (fun q => q ≠ p) = ps := by
        simpa only [hcp] using hFilter
      refine ⟨p,?_,by omega,le_rfl,?_⟩
      · rfl
      · simpa only [hFilterCons,show ρ.k = k from rfl,
          show k-1-(k-2) = 1 by omega,show A-2 = 1 from rfl] using hValue
  cases side with
  | lower =>
    exact hAttains Side.lower word hletters hmarker hfirst hlast hchild
  | upper =>
    exact hAttains Side.upper word hletters hmarker hfirst hlast hchild

end ErdosSzekeres
