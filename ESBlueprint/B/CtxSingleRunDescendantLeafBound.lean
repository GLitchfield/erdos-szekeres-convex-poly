import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A descendant single run is bounded by the ancestor run capacities minus explicit left and right extension counts, capped by explicit new-level join witnesses. The ancestor run has arbitrary positive length; old external positions, sides and maxima are transported through an arbitrary finite prefix. This isolates the geometric capacity transport used in sandwich allocation proofs.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_112 -/
theorem ctx_single_run_descendant_leaf_bound (σ : Ctx.Context) (b N : ℕ) (hpos : σ.childPositions = List.range' b N) (hN : 0 < N)
  (π : Ctx.Context) (D p n : ℕ) (hπ : π.a = σ.a ∧ π.u = σ.u ∧ π.k = σ.k ∧ π.maxima.length = D + σ.maxima.length ∧
      (∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N) ∧
      (∀ N, 1 ≤ N → π.sideAt (N + D) = σ.sideAt N) ∧
      (∀ N, 1 ≤ N → π.maximumAt (N + D) = σ.maximumAt N))
      (hp : p ∈ σ.childPositions) (hn : 0 < n) (hps : π.childPositions = List.range' p n)
      (L₀ R₀ L₁ R₁ : List ℕ)
      (hL₀ : L₀.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = Ctx.Side.lower)))
      (hR₀ : R₀.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = Ctx.Side.lower)))
      (hL₁ : L₁.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = Ctx.Side.upper)))
      (hR₁ : R₁.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = Ctx.Side.upper)))
      (l₀ r₀ l₁ r₁ c₀ d₀ c₁ d₁ : ℕ)
      (hl₀ : l₀ ∈ σ.childPositions) (hr₀ : r₀ ∈ σ.childPositions)
      (hl₁ : l₁ ∈ σ.childPositions) (hr₁ : r₁ ∈ σ.childPositions)
      (hfL₀ : L₀.foldl (Ctx.Context.leftStep π) (p, 0) = (l₀, c₀))
      (hfR₀ : R₀.foldl (Ctx.Context.rightStep π) (p, 0) = (r₀, d₀))
      (hfL₁ : L₁.foldl (Ctx.Context.leftStep π) (p, 0) = (l₁, c₁))
      (hfR₁ : R₁.foldl (Ctx.Context.rightStep π) (p, 0) = (r₁, d₁))
      (J₀ J₁ : ℕ) (hj₀ : J₀ ≤ π.joinExt Ctx.Side.lower p p) (hj₁ : J₁ ≤ π.joinExt Ctx.Side.upper p p) :
      π.bound ≤ Ctx.Context.baseOf
        (min (σ.cupLimit b b - (c₀ + d₀)) (σ.k - 1 - J₀))
        (min (σ.capLimit b b - (c₁ + d₁)) (σ.k - 1 - J₁)) σ.k := by
  let rootLength := N
  have hrunBound : ∀ (τ : Context) (a n : ℕ), 0 < n →
      τ.childPositions = List.range' a n →
      τ.bound = baseOf (τ.cupLimit a a) (τ.capLimit a a) τ.k := by
    intro τ a n hn hps
    have hmem : ∀ p, p ∈ τ.childPositions ↔ a ≤ p ∧ p < a + n := by
      intro p
      rw [hps, List.mem_range'_1]
    let starts := (List.range τ.word.length).filter fun p ↦
      τ.letterAt p = Letter.child ∧ (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child)
    have hsubset : starts.toFinset ⊆ ({a} : Finset ℕ) := by
      intro p hp
      have hstart : p < τ.word.length ∧ τ.letterAt p = Letter.child ∧
          (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child) := by
        simpa [starts] using hp
      have hp' := (hmem p).1
        (by simpa [childPositions] using And.intro hstart.1 hstart.2.1)
      simp only [Finset.mem_singleton]
      by_contra hpa
      have hprev : p - 1 ∈ τ.childPositions := (hmem (p - 1)).2 ⟨by omega, by omega⟩
      have hprev' : τ.letterAt (p - 1) = Letter.child :=
        (List.mem_filter.1 hprev).2 |> of_decide_eq_true
      rcases hstart.2.2 with hz | hnot
      · omega
      · exact hnot hprev'
    have hruns : τ.numRuns ≤ 1 := by
      calc
        τ.numRuns = starts.toFinset.card :=
          (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
        _ ≤ ({a} : Finset ℕ).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    simp [bound, boundFuel, hruns, base_eq_baseOf, hps, List.head?_range', Nat.ne_of_gt hn]
  have hchild : ∀ p, p ∈ σ.childPositions ↔ b ≤ p ∧ p < b + rootLength := by
    intro p
    rw [hpos, List.mem_range'_1]
  -- Every old external position lies outside the run. Moving the starting child
  -- within the run therefore leaves both extension folds unchanged.
  have hextOutside : ∀ N p, p ∈ σ.extPositions N → p < b ∨ b + rootLength ≤ p := by
    intro N p hp
    by_contra hout
    have hc := (hchild p).2 ⟨by omega, by omega⟩
    have hlet : σ.letterAt p = Letter.child := of_decide_eq_true (List.mem_filter.1 hc).2
    simp [extPositions, hlet] at hp
  have hfilters : ∀ p q, p ∈ σ.childPositions → q ∈ σ.childPositions → ∀ N,
      (σ.extPositions N).filter (· < p) = (σ.extPositions N).filter (· < q) ∧
      (σ.extPositions N).filter (p < ·) = (σ.extPositions N).filter (q < ·) := by
    intro p q hp hq N
    have hp' := (hchild p).1 hp
    have hq' := (hchild q).1 hq
    constructor <;> apply List.filter_congr <;> intro x hx
    · have := hextOutside N x hx
      simp only [decide_eq_decide]
      omega
    · have := hextOutside N x hx
      simp only [decide_eq_decide]
      omega
  have hfoldLeft : ∀ (ls : List ℕ) p q c, p ∈ σ.childPositions → q ∈ σ.childPositions →
      (ls.foldl (leftStep σ) (p, c)).2 = (ls.foldl (leftStep σ) (q, c)).2 := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons N ls ih =>
      intro p q c hp hq
      simp only [List.foldl_cons, leftStep]
      rw [(hfilters p q hp hq N).1]
      split
      · rfl
      · exact ih p q c hp hq
  have hfoldRight : ∀ (ls : List ℕ) p q c, p ∈ σ.childPositions → q ∈ σ.childPositions →
      (ls.foldl (rightStep σ) (p, c)).2 = (ls.foldl (rightStep σ) (q, c)).2 := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons N ls ih =>
      intro p q c hp hq
      simp only [List.foldl_cons, rightStep]
      rw [(hfilters p q hp hq N).2]
      split
      · rfl
      · exact ih p q c hp hq
  have hleftEq : ∀ s top p q, p ∈ σ.childPositions → q ∈ σ.childPositions →
      σ.leftExt s top p = σ.leftExt s top q := by
    intro s top p q hp hq
    simp only [leftExt_eq]
    congr 2
    apply List.map_congr_left
    intro ls _
    exact hfoldLeft ls p q 0 hp hq
  have hrightEq : ∀ s top p q, p ∈ σ.childPositions → q ∈ σ.childPositions →
      σ.rightExt s top p = σ.rightExt s top q := by
    intro s top p q hp hq
    simp only [rightExt_eq]
    congr 2
    apply List.map_congr_left
    intro ls _
    exact hfoldRight ls p q 0 hp hq
  have hchainEq : ∀ s p q, p ∈ σ.childPositions → q ∈ σ.childPositions →
      σ.chainExt s p p = σ.chainExt s q q := by
    intro s p q hp hq
    simp only [chainExt, hleftEq s 0 p q hp hq, hrightEq s 0 p q hp hq]
  have hjoinEq : ∀ s p q, p ∈ σ.childPositions → q ∈ σ.childPositions →
      σ.joinExt s p p = σ.joinExt s q q := by
    intro s p q hp hq
    simp only [joinExt, hchainEq s p q hp hq, hleftEq s _ p q hp hq,
      hrightEq s _ p q hp hq]
  have hmaxWitness : ∀ (L : List ℕ) (f : List ℕ → ℕ),
      ∃ ls ∈ L.sublists, ((L.sublists.map f).max?).getD 0 = f ls := by
    intro L f
    have hmem : f [] ∈ L.sublists.map f := List.mem_map.2 ⟨[], by simp, rfl⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (List.isSome_max?_of_mem hmem)
    obtain ⟨ls, hls, hval⟩ := List.mem_map.1 (List.max?_mem hv)
    exact ⟨ls, hls, by simp [hv, hval]⟩
  -- New levels form a finite prefix; every old level follows them unchanged.
  have hlevelPrefix (π : Context) (D : ℕ) (hlen : π.maxima.length = D + σ.maxima.length)
      (hside : ∀ N, 1 ≤ N → π.sideAt (N + D) = σ.sideAt N) (s : Side) (N : ℕ) :
      π.levelsOn s (if N = 0 then 0 else N + D) =
        ((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s) ++
          (σ.levelsOn s N).map (· + D) := by
    have hlevels : π.levels = (List.range D).map (· + 1) ++ σ.levels.map (· + D) := by
      simp only [levels, hlen, List.range_add, List.map_append, List.map_map]
      congr 2
      funext i
      simp only [Function.comp_def]
      omega
    unfold levelsOn
    rw [hlevels, List.filter_append]
    congr 1
    · apply List.filter_congr
      intro l hl
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
      have hi' := List.mem_range.mp hi
      by_cases hN : N = 0 <;> simp [hN] <;> omega
    · rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro l hl
      have hl1 := one_le_of_mem_levels hl
      simp only [Function.comp_def, hside l hl1, decide_eq_decide]
      by_cases hN : N = 0 <;> simp [hN] <;> omega
  have hfoldOldLeft (π : Context) (D : ℕ)
      (hext : ∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N)
      (ls : List ℕ) (hls : ∀ N ∈ ls, 1 ≤ N) (st : ℕ × ℕ) :
      ((ls.map (· + D)).foldl (leftStep π) st) = ls.foldl (leftStep σ) st := by
    induction ls generalizing st with
    | nil => rfl
    | cons N ls ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hstep : leftStep π st (N + D) = leftStep σ st N := by
        rcases st with ⟨p, c⟩
        simp only [leftStep, hext N (hls N (by simp))]
      rw [hstep]
      exact ih (fun N hN => hls N (by simp [hN])) _
  have hfoldOldRight (π : Context) (D : ℕ)
      (hext : ∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N)
      (ls : List ℕ) (hls : ∀ N ∈ ls, 1 ≤ N) (st : ℕ × ℕ) :
      ((ls.map (· + D)).foldl (rightStep π) st) = ls.foldl (rightStep σ) st := by
    induction ls generalizing st with
    | nil => rfl
    | cons N ls ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hstep : rightStep π st (N + D) = rightStep σ st N := by
        rcases st with ⟨p, c⟩
        simp only [rightStep, hext N (hls N (by simp))]
      rw [hstep]
      exact ih (fun N hN => hls N (by simp [hN])) _
  have htransfer (π : Context) (D : ℕ)
      (hlen : π.maxima.length = D + σ.maxima.length)
      (hside : ∀ N, 1 ≤ N → π.sideAt (N + D) = σ.sideAt N)
      (hext : ∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N)
      (hmaximum : ∀ N, 1 ≤ N → π.maximumAt (N + D) = σ.maximumAt N)
      (s : Side) (p : ℕ) (hp : p ∈ σ.childPositions) (L R : List ℕ)
      (hL : L.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s)))
      (hR : R.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s)))
      (l r lc rc : ℕ) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
      (hleft : L.foldl (leftStep π) (p, 0) = (l, lc))
      (hright : R.foldl (rightStep π) (p, 0) = (r, rc)) :
      σ.chainExt s p p + (lc + rc) ≤ π.chainExt s p p ∧
      σ.joinExt s p p + (lc + rc) ≤ π.joinExt s p p := by
    have hleftGrow (N : ℕ) : σ.leftExt s N p + lc ≤ π.leftExt s (if N = 0 then 0 else N + D) p := by
      rw [hleftEq s N p l hp hl]
      obtain ⟨ls, hls, hval⟩ := hmaxWitness (σ.levelsOn s N)
        (fun ls => (ls.foldl (leftStep σ) (l, 0)).2)
      have hsub : (L ++ ls.map (· + D)).Sublist (π.levelsOn s (if N = 0 then 0 else N + D)) := by
        rw [hlevelPrefix π D hlen hside s N]
        exact hL.append ((List.mem_sublists.mp hls).map _)
      have hv := le_getD_max?_of_mem (List.mem_map.mpr ⟨_, List.mem_sublists.mpr hsub, rfl⟩ :
        ((L ++ ls.map (· + D)).foldl (leftStep π) (p, 0)).2 ∈
          (π.levelsOn s (if N = 0 then 0 else N + D)).sublists.map
            (fun ls => (ls.foldl (leftStep π) (p, 0)).2))
      rw [List.foldl_append, hleft, hfoldOldLeft π D hext ls
        (fun N hN => (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hN)).1),
        foldl_leftStep_count σ ls l lc] at hv
      change _ ≤ π.leftExt s (if N = 0 then 0 else N + D) p at hv
      rw [leftExt_eq, hval]
      omega
    have hrightGrow (N : ℕ) : σ.rightExt s N p + rc ≤ π.rightExt s (if N = 0 then 0 else N + D) p := by
      rw [hrightEq s N p r hp hr]
      obtain ⟨ls, hls, hval⟩ := hmaxWitness (σ.levelsOn s N)
        (fun ls => (ls.foldl (rightStep σ) (r, 0)).2)
      have hsub : (R ++ ls.map (· + D)).Sublist (π.levelsOn s (if N = 0 then 0 else N + D)) := by
        rw [hlevelPrefix π D hlen hside s N]
        exact hR.append ((List.mem_sublists.mp hls).map _)
      have hv := le_getD_max?_of_mem (List.mem_map.mpr ⟨_, List.mem_sublists.mpr hsub, rfl⟩ :
        ((R ++ ls.map (· + D)).foldl (rightStep π) (p, 0)).2 ∈
          (π.levelsOn s (if N = 0 then 0 else N + D)).sublists.map
            (fun ls => (ls.foldl (rightStep π) (p, 0)).2))
      rw [List.foldl_append, hright, hfoldOldRight π D hext ls
        (fun N hN => (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hN)).1),
        foldl_rightStep_count σ ls r rc] at hv
      change _ ≤ π.rightExt s (if N = 0 then 0 else N + D) p at hv
      rw [rightExt_eq, hval]
      omega
    have hchain : σ.chainExt s p p + (lc + rc) ≤ π.chainExt s p p := by
      have hL : σ.leftExt s 0 p + lc ≤ π.leftExt s 0 p := by simpa using hleftGrow 0
      have hR : σ.rightExt s 0 p + rc ≤ π.rightExt s 0 p := by simpa using hrightGrow 0
      unfold chainExt
      omega
    refine ⟨hchain, ?_⟩
    have hmax : (((σ.levelsOn s 0).map (fun N => σ.leftExt s N p + σ.rightExt s N p + σ.maximumAt N)).max?).getD 0 + (lc + rc) ≤ π.joinExt s p p := by
      cases hh : ((σ.levelsOn s 0).map (fun N => σ.leftExt s N p + σ.rightExt s N p + σ.maximumAt N)).max? with
      | none =>
        simp only [Option.getD_none, Nat.zero_add]
        exact (by omega : lc + rc ≤ π.chainExt s p p).trans (π.chainExt_le_joinExt s p p)
      | some val =>
        obtain ⟨N, hN, heq⟩ := List.mem_map.mp (List.max?_mem hh)
        have hN1 := (one_le_of_mem_levelsOn hN).1
        have hL := hleftGrow N
        have hR := hrightGrow N
        simp only [if_neg (by omega : N ≠ 0)] at hL hR
        have hmem : N + D ∈ π.levelsOn s 0 := by
          rw [show 0 = (if (0 : ℕ) = 0 then 0 else 0 + D) by simp,
            hlevelPrefix π D hlen hside s 0]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
        have hv := le_joinExt_of_mem_levelsOn hmem p p
        rw [hmaximum N hN1] at hv
        simp only [Option.getD_some]
        omega
    have hc := hchain.trans (π.chainExt_le_joinExt s p p)
    change max _ _ + (lc + rc) ≤ _
    omega
  obtain ⟨ha, hu, hk, hlen, hext, hside, hmaximum⟩ := hπ
  have h₀ := htransfer π D hlen hside hext hmaximum Side.lower p hp L₀ R₀ hL₀ hR₀
    l₀ r₀ c₀ d₀ hl₀ hr₀ hfL₀ hfR₀
  have h₁ := htransfer π D hlen hside hext hmaximum Side.upper p hp L₁ R₁ hL₁ hR₁
    l₁ r₁ c₁ d₁ hl₁ hr₁ hfL₁ hfR₁
  have hb : b ∈ σ.childPositions := by rw [hpos]; simpa using hN
  have hcEq : σ.cupLimit p p = σ.cupLimit b b := by
    simp only [cupLimit, hchainEq Side.lower p b hp hb, hjoinEq Side.lower p b hp hb]
  have hpEq : σ.capLimit p p = σ.capLimit b b := by
    simp only [capLimit, hchainEq Side.upper p b hp hb, hjoinEq Side.upper p b hp hb]
  rw [hrunBound π p n hn hps, hk]
  apply baseOf_mono
  · rw [← hcEq]
    unfold cupLimit
    rw [hu, hk]
    omega
  · rw [← hpEq]
    unfold capLimit
    rw [ha, hk]
    omega

end ErdosSzekeres
