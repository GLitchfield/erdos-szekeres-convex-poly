import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Exact same-side capacity update for an arbitrary part of a single child run. The old cup or cap limit loses one unit for each side containing removed children, then is capped by the new sibling maximum. Retains arbitrary old external levels and unused maxima, and permits any new maximum. Supplies explicit capacity arithmetic for the unbounded outer-block sandwich comparison.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_single_run_part_limits_exact (σ : Ctx.Context) (hwf : σ.WellFormed) (b N : ℕ)
  (hpos : σ.childPositions = List.range' b N)
  (keep : List ℕ) (hremoved : ∃ r ∈ σ.childPositions, r ∉ keep)
  (p q : ℕ) (hp : p ∈ σ.childPositions) (hq : q ∈ σ.childPositions) (m : ℕ) :
  let removed := σ.childPositions.filter (· ∉ keep)
  let cost := (if (removed.filter (· < p)).isEmpty then 0 else 1) +
    (if (removed.filter (q < ·)).isEmpty then 0 else 1)
  (σ.part keep Ctx.Side.lower m).cupLimit p q =
      min (σ.cupLimit p q - cost) (σ.k - 1 - m) ∧
  (σ.part keep Ctx.Side.upper m).capLimit p q =
      min (σ.capLimit p q - cost) (σ.k - 1 - m) := by
  classical
  dsimp only
  let removed := σ.childPositions.filter (· ∉ keep)
  let leftCost (z : ℕ) := if (removed.filter (· < z)).isEmpty then 0 else 1
  let rightCost (z : ℕ) := if (removed.filter (z < ·)).isEmpty then 0 else 1
  let cost := leftCost p + rightCost q
  change (σ.part keep Side.lower m).cupLimit p q =
      min (σ.cupLimit p q - cost) (σ.k - 1 - m) ∧
    (σ.part keep Side.upper m).capLimit p q =
      min (σ.capLimit p q - cost) (σ.k - 1 - m)
  let rootLength := N
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
  have hmaxWitness : ∀ (L : List ℕ) (f : List ℕ → ℕ),
      ∃ ls ∈ L.sublists, ((L.sublists.map f).max?).getD 0 = f ls := by
    intro L f
    have hmem : f [] ∈ L.sublists.map f := List.mem_map.2 ⟨[], by simp, rfl⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (List.isSome_max?_of_mem hmem)
    obtain ⟨ls, hls, hval⟩ := List.mem_map.1 (List.max?_mem hv)
    exact ⟨ls, hls, by simp [hv, hval]⟩
  have hlet : ∀ z l s, σ.letterAt z = Letter.ext l s → 1 ≤ l :=
    fun z l s h ↦ (hwf.2.2.2.2.2 z l s h).1
  have hext (s : Side) : (σ.part keep s m).extPositions 1 = removed :=
    part_extPositions_one hlet keep s m
  have hside (s : Side) : (σ.part keep s m).sideAt 1 = s := by
    obtain ⟨r, hr, hnot⟩ := hremoved
    apply part_sideAt_one_of_mem hlet keep s m (q := r)
    rw [hext]
    simp [removed, hr, hnot]
  have hremovedChild : ∀ x ∈ removed, x ∈ σ.childPositions := by
    intro x hx
    exact (List.mem_filter.mp hx).1
  have hleftCost : ∀ z x, x ∈ removed → x < z → leftCost z = 1 := by
    intro z x hx hlt
    have hn : removed.filter (· < z) ≠ [] :=
      List.ne_nil_of_mem (by simp [hx, hlt] : x ∈ removed.filter (· < z))
    dsimp only [leftCost]
    rw [List.isEmpty_eq_false_iff.mpr hn]
    simp
  have hrightCost : ∀ z x, x ∈ removed → z < x → rightCost z = 1 := by
    intro z x hx hlt
    have hn : removed.filter (z < ·) ≠ [] :=
      List.ne_nil_of_mem (by simp [hx, hlt] : x ∈ removed.filter (z < ·))
    dsimp only [rightCost]
    rw [List.isEmpty_eq_false_iff.mpr hn]
    simp
  -- The existing fold bounds give the upper inequality. A maximizing old sublist,
  -- preceded by the new level, attains that inequality even when its first step is empty.
  have hpartLeft : ∀ (s : Side) (top top' z : ℕ), z ∈ σ.childPositions →
      (σ.part keep s m).levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1) →
      (σ.part keep s m).leftExt s top' z = σ.leftExt s top z + leftCost z := by
    intro s top top' z hz hlevels
    have hpositive : ∀ l ∈ σ.levelsOn s top, 1 ≤ l := by
      intro l hl
      exact (one_le_of_mem_levelsOn hl).1
    apply le_antisymm
    · rw [leftExt_eq]
      apply getD_max?_le
      intro value hvalue
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hvalue
      rw [hlevels] at hls
      have hbound := foldl_leftStep_part_le (σ := σ) (keep := keep) (s := s) (m := m)
        hpositive z hls
      rcases hbound with hbound | ⟨x, hx, hxz, hbound⟩
      · change _ ≤ σ.leftExt s top z at hbound
        omega
      · rw [hext] at hx
        have hxchild := hremovedChild x hx
        have hc := hleftCost z x hx hxz
        change _ ≤ 1 + σ.leftExt s top x at hbound
        rw [hleftEq s top x z hxchild hz] at hbound
        omega
    · obtain ⟨ls, hls, hval⟩ := hmaxWitness (σ.levelsOn s top)
        (fun ls ↦ (ls.foldl (leftStep σ) (z, 0)).2)
      change σ.leftExt s top z = _ at hval
      have hlspos : ∀ l ∈ ls, 1 ≤ l := fun l hl ↦
        hpositive l ((List.mem_sublists.mp hls).subset hl)
      have hsub : 1 :: ls.map (· + 1) ∈ ((σ.part keep s m).levelsOn s top').sublists := by
        rw [hlevels, List.mem_sublists]
        exact List.Sublist.cons₂ 1 ((List.mem_sublists.mp hls).map _)
      have hwitness := le_getD_max?_of_mem
        (List.mem_map.mpr ⟨1 :: ls.map (· + 1), hsub, rfl⟩ :
          ((1 :: ls.map (· + 1)).foldl (leftStep (σ.part keep s m)) (z, 0)).2 ∈
            ((σ.part keep s m).levelsOn s top').sublists.map
              (fun xs ↦ (xs.foldl (leftStep (σ.part keep s m)) (z, 0)).2))
      change _ ≤ (σ.part keep s m).leftExt s top' z at hwitness
      have hstep : leftStep (σ.part keep s m) (z, 0) 1 =
          match (removed.filter (· < z)).getLast? with
          | some x => (x, 1)
          | none => (z, 0) := by
        simp only [leftStep, hext]
        rfl
      rw [List.foldl_cons, hstep] at hwitness
      cases hh : (removed.filter (· < z)).getLast? with
      | none =>
        have hnil := List.getLast?_eq_none_iff.mp hh
        have hc : leftCost z = 0 := by
          dsimp only [leftCost]
          rw [hnil]
          simp
        simp only [hh] at hwitness
        rw [foldl_leftStep_part_map σ keep s m ls hlspos] at hwitness
        rw [hc, Nat.add_zero, hval]
        exact hwitness
      | some x =>
        have hx := List.mem_of_mem_getLast? (Option.mem_def.mpr hh)
        have hxremoved := (List.mem_filter.mp hx).1
        have hxz := of_decide_eq_true (List.mem_filter.mp hx).2
        have hxchild := hremovedChild x hxremoved
        have hc := hleftCost z x hxremoved hxz
        simp only [hh] at hwitness
        rw [foldl_leftStep_part_map σ keep s m ls hlspos,
          foldl_leftStep_count σ ls x 1,
          hfoldLeft ls x z 0 hxchild hz] at hwitness
        rw [hc, hval]
        omega
  have hpartRight : ∀ (s : Side) (top top' z : ℕ), z ∈ σ.childPositions →
      (σ.part keep s m).levelsOn s top' = 1 :: (σ.levelsOn s top).map (· + 1) →
      (σ.part keep s m).rightExt s top' z = σ.rightExt s top z + rightCost z := by
    intro s top top' z hz hlevels
    have hpositive : ∀ l ∈ σ.levelsOn s top, 1 ≤ l := by
      intro l hl
      exact (one_le_of_mem_levelsOn hl).1
    apply le_antisymm
    · rw [rightExt_eq]
      apply getD_max?_le
      intro value hvalue
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hvalue
      rw [hlevels] at hls
      have hbound := foldl_rightStep_part_le (σ := σ) (keep := keep) (s := s) (m := m)
        hpositive z hls
      rcases hbound with hbound | ⟨x, hx, hxz, hbound⟩
      · change _ ≤ σ.rightExt s top z at hbound
        omega
      · rw [hext] at hx
        have hxchild := hremovedChild x hx
        have hc := hrightCost z x hx hxz
        change _ ≤ 1 + σ.rightExt s top x at hbound
        rw [hrightEq s top x z hxchild hz] at hbound
        omega
    · obtain ⟨ls, hls, hval⟩ := hmaxWitness (σ.levelsOn s top)
        (fun ls ↦ (ls.foldl (rightStep σ) (z, 0)).2)
      change σ.rightExt s top z = _ at hval
      have hlspos : ∀ l ∈ ls, 1 ≤ l := fun l hl ↦
        hpositive l ((List.mem_sublists.mp hls).subset hl)
      have hsub : 1 :: ls.map (· + 1) ∈ ((σ.part keep s m).levelsOn s top').sublists := by
        rw [hlevels, List.mem_sublists]
        exact List.Sublist.cons₂ 1 ((List.mem_sublists.mp hls).map _)
      have hwitness := le_getD_max?_of_mem
        (List.mem_map.mpr ⟨1 :: ls.map (· + 1), hsub, rfl⟩ :
          ((1 :: ls.map (· + 1)).foldl (rightStep (σ.part keep s m)) (z, 0)).2 ∈
            ((σ.part keep s m).levelsOn s top').sublists.map
              (fun xs ↦ (xs.foldl (rightStep (σ.part keep s m)) (z, 0)).2))
      change _ ≤ (σ.part keep s m).rightExt s top' z at hwitness
      have hstep : rightStep (σ.part keep s m) (z, 0) 1 =
          match (removed.filter (z < ·)).head? with
          | some x => (x, 1)
          | none => (z, 0) := by
        simp only [rightStep, hext]
        rfl
      rw [List.foldl_cons, hstep] at hwitness
      cases hh : (removed.filter (z < ·)).head? with
      | none =>
        have hnil := List.head?_eq_none_iff.mp hh
        have hc : rightCost z = 0 := by
          dsimp only [rightCost]
          rw [hnil]
          simp
        simp only [hh] at hwitness
        rw [foldl_rightStep_part_map σ keep s m ls hlspos] at hwitness
        rw [hc, Nat.add_zero, hval]
        exact hwitness
      | some x =>
        have hx := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        have hxremoved := (List.mem_filter.mp hx).1
        have hxz := of_decide_eq_true (List.mem_filter.mp hx).2
        have hxchild := hremovedChild x hxremoved
        have hc := hrightCost z x hxremoved hxz
        simp only [hh] at hwitness
        rw [foldl_rightStep_part_map σ keep s m ls hlspos,
          foldl_rightStep_count σ ls x 1,
          hfoldRight ls x z 0 hxchild hz] at hwitness
        rw [hc, hval]
        omega
  have hchain (s : Side) :
      (σ.part keep s m).chainExt s p q = σ.chainExt s p q + cost := by
    have hl := hpartLeft s 0 0 p hp (part_levelsOn_self_zero (hside s))
    have hr := hpartRight s 0 0 q hq (part_levelsOn_self_zero (hside s))
    unfold chainExt
    rw [hl, hr]
    dsimp [cost]
    omega
  have hbelowOne : ∀ (τ : Context) (s : Side) (z : ℕ),
      τ.leftExt s 1 z = 0 ∧ τ.rightExt s 1 z = 0 := by
    intro τ s z
    have hlevels : τ.levelsOn s 1 = [] := by
      unfold levelsOn
      apply List.filter_eq_nil_iff.mpr
      intro l hl
      have h1 := one_le_of_mem_levels hl
      simp only [decide_eq_true_eq]
      omega
    simp [leftExt_eq, rightExt_eq, hlevels]
  have hterm (s : Side) (l : ℕ) (hl : 1 ≤ l) :
      (σ.part keep s m).leftExt s (l + 1) p +
        (σ.part keep s m).rightExt s (l + 1) q +
        (σ.part keep s m).maximumAt (l + 1) =
      σ.leftExt s l p + σ.rightExt s l q + σ.maximumAt l + cost := by
    rw [hpartLeft s l (l + 1) p hp (part_levelsOn_self_succ (hside s) hl),
      hpartRight s l (l + 1) q hq (part_levelsOn_self_succ (hside s) hl),
      part_maximumAt_succ σ keep s m hl]
    dsimp [cost]
    omega
  have hjoin (s : Side) :
      (σ.part keep s m).joinExt s p q = max (σ.joinExt s p q + cost) m := by
    let τ := σ.part keep s m
    have hnew : τ.leftExt s 1 p + τ.rightExt s 1 q + τ.maximumAt 1 = m := by
      rw [(hbelowOne τ s p).1, (hbelowOne τ s q).2]
      simpa only [Nat.zero_add] using part_maximumAt_one σ keep s m
    have hlevels : τ.levelsOn s 0 = 1 :: (σ.levelsOn s 0).map (· + 1) :=
      part_levelsOn_self_zero (hside s)
    have hleTerm : ∀ l ∈ τ.levelsOn s 0,
        τ.leftExt s l p + τ.rightExt s l q + τ.maximumAt l ≤ τ.joinExt s p q := by
      intro l hl
      have hv : τ.leftExt s l p + τ.rightExt s l q + τ.maximumAt l ≤
          (((τ.levelsOn s 0).map (fun j ↦
            τ.leftExt s j p + τ.rightExt s j q + τ.maximumAt j)).max?).getD 0 :=
        le_getD_max?_of_mem (List.mem_map.mpr ⟨l, hl, rfl⟩)
      exact hv.trans (Nat.le_max_right _ _)
    have hchainBound : σ.chainExt s p q + cost ≤ τ.joinExt s p q := by
      rw [← hchain]
      exact Nat.le_max_left _ _
    have hm : m ≤ τ.joinExt s p q := by
      rw [← hnew]
      exact hleTerm 1 (by rw [hlevels]; exact List.mem_cons_self)
    have holdTerm : ∀ l ∈ σ.levelsOn s 0,
        σ.leftExt s l p + σ.rightExt s l q + σ.maximumAt l + cost ≤ τ.joinExt s p q := by
      intro l hl
      rw [← hterm s l (one_le_of_mem_levelsOn hl).1]
      apply hleTerm
      rw [hlevels]
      exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨l, hl, rfl⟩))
    apply le_antisymm
    · change max (τ.chainExt s p q)
        ((((τ.levelsOn s 0).map (fun l ↦
          τ.leftExt s l p + τ.rightExt s l q + τ.maximumAt l)).max?).getD 0) ≤ _
      apply max_le
      · change (σ.part keep s m).chainExt s p q ≤ _
        rw [hchain]
        have hold : σ.chainExt s p q ≤ σ.joinExt s p q := Nat.le_max_left _ _
        omega
      · apply getD_max?_le
        intro value hvalue
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hvalue
        rw [hlevels, List.mem_cons] at hl
        rcases hl with rfl | hl
        · rw [hnew]
          exact Nat.le_max_right _ _
        · obtain ⟨oldLevel, hOldLevel, hLevelEq⟩ := List.mem_map.mp hl
          subst l
          change (σ.part keep s m).leftExt s (oldLevel + 1) p +
            (σ.part keep s m).rightExt s (oldLevel + 1) q +
            (σ.part keep s m).maximumAt (oldLevel + 1) ≤ _
          rw [hterm s oldLevel (one_le_of_mem_levelsOn hOldLevel).1]
          have hold : σ.leftExt s oldLevel p + σ.rightExt s oldLevel q + σ.maximumAt oldLevel ≤
              σ.joinExt s p q :=
            le_trans (le_getD_max?_of_mem
              (L := (σ.levelsOn s 0).map (fun j ↦
                σ.leftExt s j p + σ.rightExt s j q + σ.maximumAt j))
              (List.mem_map.mpr ⟨oldLevel, hOldLevel, rfl⟩)) (Nat.le_max_right _ _)
          omega
    · apply max_le ?_ hm
      have hc : cost ≤ τ.joinExt s p q := by omega
      have hmax : (((σ.levelsOn s 0).map (fun l ↦
          σ.leftExt s l p + σ.rightExt s l q + σ.maximumAt l)).max?).getD 0 ≤
          τ.joinExt s p q - cost := by
        apply getD_max?_le
        intro value hvalue
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hvalue
        have h := holdTerm l hl
        omega
      change max (σ.chainExt s p q)
        ((((σ.levelsOn s 0).map (fun l ↦
          σ.leftExt s l p + σ.rightExt s l q + σ.maximumAt l)).max?).getD 0) + cost ≤
          τ.joinExt s p q
      omega
  constructor
  · unfold cupLimit
    change min (σ.u - 1 - (σ.part keep Side.lower m).chainExt Side.lower p q)
      (σ.k - 1 - (σ.part keep Side.lower m).joinExt Side.lower p q) = _
    rw [hchain, hjoin]
    omega
  · unfold capLimit
    change min (σ.a - 1 - (σ.part keep Side.upper m).chainExt Side.upper p q)
      (σ.k - 1 - (σ.part keep Side.upper m).joinExt Side.upper p q) = _
    rw [hchain, hjoin]
    omega

end ErdosSzekeres
