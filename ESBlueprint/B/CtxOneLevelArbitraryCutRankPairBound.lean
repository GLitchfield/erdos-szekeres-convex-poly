import ESBlueprint.B.CtxOneLevelArbitraryCutRankBound

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- For positive history labels, an actual chosen-side marker and chosen global at most four, both parts of any chosen/opposite cut have total bound at most the source active opposite-rank-pair union cardinality. Covers interleaved kept sets, empty sides, arbitrary sibling maxima and independent fuel values. Missing-successor-pair colors are inherited by each part. Mixed groups use the arbitrary-cut doubled-rank estimate after pruning projection; groups wholly in one part use original-history pruning domination. Disjoint diagonal and successor charges bound the sum. Supplies a support-sensitive cut potential without the source-single-run or rank-band separation restrictions toward the remaining singleton-end sandwich.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_one_level_arbitrary_cut_rank_pair_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (keep : List ℕ) (m n : ℕ) :
  let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let interval := fun p => Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p)
  let pairs := active.biUnion (fun p => ((interval p).product (interval p)).filter (fun z => z.1 ≤ z.2))
  let own := σ.part keep s m
  let other := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  (∀ ownFuel otherFuel, Ctx.Context.boundFuel ownFuel own +
    Ctx.Context.boundFuel otherFuel other ≤ pairs.card) ∧ own.bound + other.bound ≤ pairs.card := by
  classical
  have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls ↦ (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls ↦ (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p ↦ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let I (ρ : Context) (r : ℕ) :=
    Finset.Icc (ρ.leftExt t 0 r + 1) (G ρ t - 1 - ρ.rightExt t 0 r)
  let Tri (r : ℕ) := ((I σ r).product (I σ r)).filter (fun z ↦ z.1 ≤ z.2)
  let S := (active σ).biUnion Tri
  let P := G σ t - 1
  let gaps := (Finset.range P).filter (fun z ↦ (z, z + 1) ∉ S)
  let key := fun z ↦ (gaps.filter (· < z)).card
  let color := fun r ↦ key (σ.leftExt t 0 r + 1)
  let colors := Finset.range (gaps.card + 1)
  let ranks (c : ℕ) := ((active σ).filter (fun p ↦ color p = c)).biUnion (I σ)
  let support (c : ℕ) := σ.childPositions.filter (fun p ↦ color p = c)
  let group (c : ℕ) : Context := { σ with
    word := (List.range σ.word.length).map (fun p ↦ match σ.letterAt p with
      | Letter.child => if p ∈ support c then Letter.child
          else Letter.ext (σ.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  let A := σ.part keep s m
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  change (∀ ownFuel otherFuel, boundFuel ownFuel A + boundFuel otherFuel B ≤ S.card) ∧
    A.bound + B.bound ≤ S.card
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hSmall (r : ℕ) (hr : r ∈ σ.childPositions) : min (σ.cupLimit r r) (σ.capLimit r r) ≤ 2 := by
    have hrx : r ≠ x := by
      intro he
      subst x
      have hc := of_decide_eq_true (List.mem_filter.mp hr).2
      have he := (List.mem_filter.mp hx).2
      simp [hc] at he
    by_cases h : r < x
    · have he := hOneRight σ s N r x hNOn hx h
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
    · have he := hOneLeft σ s N r x hNOn hx (by omega)
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
  have hPair (r : ℕ) (hr : r ∈ active σ) (a b : ℕ)
      (ha : a ∈ I σ r) (hb : b ∈ I σ r) (hab : a ≤ b) : (a, b) ∈ S := by
    apply Finset.mem_biUnion.mpr
    exact ⟨r, hr, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩⟩
  have hKey (r : ℕ) (hr : r ∈ active σ) (z : ℕ) (hz : z ∈ I σ r) :
      key z = color r := by
    have hzi := Finset.mem_Icc.mp hz
    have he : gaps.filter (· < z) = gaps.filter (· < σ.leftExt t 0 r + 1) := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ha, haz⟩
        refine ⟨ha, ?_⟩
        by_contra hn
        have haI : a ∈ I σ r := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have ha1I : a + 1 ∈ I σ r := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        exact (Finset.mem_filter.mp ha).2 (hPair r hr a (a + 1) haI ha1I (by omega))
      · rintro ⟨ha, hal⟩
        exact ⟨ha, by omega⟩
    exact congrArg Finset.card he
  have hCover : ∀ r ∈ σ.childPositions, color r ∈ colors := by
    intro r _
    have hc : (gaps.filter (· < σ.leftExt t 0 r + 1)).card ≤ gaps.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    change (gaps.filter (· < σ.leftExt t 0 r + 1)).card ∈ Finset.range (gaps.card + 1)
    exact Finset.mem_range.mpr (by omega)
  have hColor : ∀ a ∈ σ.childPositions, ∀ b ∈ σ.childPositions, a ≤ b →
      (∀ r, a ≤ r → r ≤ b → r ∈ σ.childPositions) → color a = color b := by
    intro a ha b hb hab hbetween
    have hRegion : ∀ j ∈ σ.levelsOn t 0, ∀ z ∈ σ.extPositions j,
        (z < a ↔ z < b) ∧ (a < z ↔ b < z) := by
      intro j hj z hz
      have hOutside : z < a ∨ b < z := by
        by_contra h
        have hzc := hbetween z (by omega) (by omega)
        have hc := of_decide_eq_true (List.mem_filter.mp hzc).2
        have he := (List.mem_filter.mp hz).2
        simp [hc] at he
      omega
    have he := (ctx_axis_region_limits_exact σ t a b hRegion).1 0
    simp only [color, he.1]
  have hRankColor (c z : ℕ) (hz : z ∈ ranks c) : key z = c := by
    obtain ⟨r, hr, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hrA, hc⟩ := Finset.mem_filter.mp hr
    exact (hKey r hrA z hz).trans hc
  have hRankBound (c z : ℕ) (hz : z ∈ ranks c) : z ≤ P := by
    obtain ⟨r, hr, hz⟩ := Finset.mem_biUnion.mp hz
    have hzi := (Finset.mem_Icc.mp hz).2
    dsimp only [P]
    exact hzi.trans (Nat.sub_le _ _)
  have hDisjoint : ∀ c ∈ colors, ∀ d ∈ colors, c ≠ d → Disjoint (ranks c) (ranks d) := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro z hz hd'
    exact hcd ((hRankColor c z hz).symm.trans (hRankColor d z hd'))
  have hDiag : ∀ c ∈ colors, ∀ a ∈ ranks c, (a, a) ∈ S := by
    intro c hc a ha
    obtain ⟨r, hr, ha⟩ := Finset.mem_biUnion.mp ha
    exact hPair r (Finset.mem_filter.mp hr).1 a a ha ha le_rfl
  have hEdge : ∀ c ∈ colors, ∀ a ∈ ranks c,
      (∃ b ∈ ranks c, a < b) → (a, a + 1) ∈ S := by
    intro c hc a ha hb
    obtain ⟨b, hb, hab⟩ := hb
    have hbP := hRankBound c b hb
    have hEq : key a = key b := (hRankColor c a ha).trans (hRankColor c b hb).symm
    by_contra hn
    have hag : a ∈ gaps := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn⟩
    have hsub : gaps.filter (· < a) ⊆ gaps.filter (· < b) := by
      intro z hz
      obtain ⟨hz, hza⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz, by omega⟩
    have he : gaps.filter (· < a) = gaps.filter (· < b) :=
      Finset.eq_of_subset_of_card_le hsub hEq.symm.le
    have hm : a ∈ gaps.filter (· < b) := Finset.mem_filter.mpr ⟨hag, hab⟩
    rw [← he] at hm
    have haa := (Finset.mem_filter.mp hm).2
    omega
  have hCharges := rank_pair_card_ge_sum_disjoint_group_charges colors ranks S hDisjoint hDiag hEdge
  have hPos (c : ℕ) : ∀ p j v, (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).1
  have hChild (c r : ℕ) : r ∈ (group c).childPositions ↔ r ∈ σ.childPositions ∧ color r = c := by
    have hh : (group c).childPositions = σ.childPositions.filter (· ∈ support c) :=
      (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.1
    rw [hh]
    simp [support, and_assoc]
  have hLimits (c p q : ℕ) : (group c).cupLimit p q = σ.cupLimit p q ∧
      (group c).capLimit p q = σ.capLimit p q :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.2.2.1 p q
  have hHist (c j : ℕ) (hj : j ∈ σ.levels) :
      (group c).extPositions j = σ.extPositions j ∧ (group c).sideAt j = σ.sideAt j :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.1 j hj
  have hLevels (c : ℕ) (v : Side) (top : ℕ) : (group c).levelsOn v top = σ.levelsOn v top :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.1 v top
  have hPure (c : ℕ) (v : Side) (top p : ℕ) :
      (group c).leftExt v top p = σ.leftExt v top p ∧
      (group c).rightExt v top p = σ.rightExt v top p :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.2.1 v top p
  have hActive (c r : ℕ) : r ∈ active (group c) ↔ r ∈ active σ ∧ color r = c := by
    simp only [active, Finset.mem_filter, List.mem_toFinset, hChild, (hLimits c r r).1,
      (hLimits c r r).2]
    tauto
  have hI (c r : ℕ) : I (group c) r = I σ r := by
    simp only [I, (hPure c t 0 r).1, (hPure c t 0 r).2]
    rfl
  have hRanks (c : ℕ) : (active (group c)).biUnion (I (group c)) = ranks c := by
    ext z
    simp only [ranks, Finset.mem_biUnion, Finset.mem_filter, hActive, hI]
  have hNSide (c : ℕ) : (group c).sideAt N = s := (hHist c N hN).2.trans hNs
  have hX (c : ℕ) : x ∈ (group c).extPositions N := by rw [(hHist c N hN).1]; exact hx
  have hGroupBound (c : ℕ) : (group c).bound ≤ 2 * (ranks c).card - 1 := by
    have hh := ctx_one_level_refined_potential_bound (group c) (hPos c) s t hne N x
      hN (hNSide c) (hX c) hglobal
    have hb := hh.2.1.trans (Nat.min_le_right _ _)
    change (group c).bound ≤ 2 * ((active (group c)).biUnion (I (group c))).card - 1 at hb
    rw [hRanks c] at hb
    exact hb
  let prune (ρ : Context) (ks : List ℕ) : Context := { ρ with
    word := (List.range ρ.word.length).map (fun p ↦ match ρ.letterAt p with
      | Letter.child => if p ∈ ks then Letter.child else Letter.ext (ρ.maxima.length + 1) Side.lower
      | Letter.ext j s => Letter.ext j s) }
  let supportG (ρ : Context) (c : ℕ) := ρ.childPositions.filter (fun p ↦ color p = c)
  let groupG (ρ : Context) (c : ℕ) := prune ρ (supportG ρ c)
  let total (ρ : Context) := colors.sum (fun c ↦ (groupG ρ c).bound)
  let Cover (ρ : Context) := ∀ p ∈ ρ.childPositions, color p ∈ colors
  let Small (ρ : Context) := ∀ p ∈ ρ.childPositions, min (ρ.cupLimit p p) (ρ.capLimit p p) ≤ 2
  let RunColor (ρ : Context) := ∀ p ∈ ρ.childPositions, ∀ q ∈ ρ.childPositions, p ≤ q →
    (∀ r, p ≤ r → r ≤ q → r ∈ ρ.childPositions) → color p = color q
  have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ p j s, (ρ.part keep v m).letterAt p = Letter.ext j s → 1 ≤ j := by
    intro p j s hp
    have hpl : p < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep v m)
        (show (ρ.part keep v m).word.length ≤ p by rw [part_word_length]; omega)
      rw [hn] at hp
      cases hp
    cases he : ρ.letterAt p with
    | child =>
      rw [part_letterAt_of_child ρ keep v m hpl he] at hp
      split at hp
      · cases hp
      · cases hp
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep v m hpl he] at hp
      cases hp
      omega
  have hPLen (ρ : Context) (ks : List ℕ) : (prune ρ ks).word.length = ρ.word.length := by
    simp [prune]
  have hPLetter (ρ : Context) (ks : List ℕ) (p : ℕ) (hp : p < ρ.word.length) :
      (prune ρ ks).letterAt p = (match ρ.letterAt p with
        | Letter.child => if p ∈ ks then Letter.child
            else Letter.ext (ρ.maxima.length + 1) Side.lower
        | Letter.ext j s => Letter.ext j s) := by
    simp only [prune, letterAt, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some]
  have hPChild (ρ : Context) (ks : List ℕ) :
      (prune ρ ks).childPositions = ρ.childPositions.filter (· ∈ ks) := by
    simp only [childPositions, hPLen, List.filter_filter]
    apply List.filter_congr
    intro p hp
    rw [hPLetter ρ ks p (List.mem_range.mp hp)]
    cases ρ.letterAt p <;> simp
  have hGroupChild (ρ : Context) (c : ℕ) : (groupG ρ c).childPositions = supportG ρ c := by
    change (prune ρ (supportG ρ c)).childPositions = supportG ρ c
    rw [hPChild]
    apply List.filter_congr
    intro p hp
    simp [supportG, hp]
  have hGroupMem (ρ : Context) (c : ℕ) (p : ℕ) :
      p ∈ (groupG ρ c).childPositions ↔ p ∈ ρ.childPositions ∧ color p = c := by
    rw [hGroupChild]
    simp [supportG]
  have hGroupPos (ρ : Context)
      (hpos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) (c : ℕ) :
      ∀ p j v, (groupG ρ c).letterAt p = Letter.ext j v → 1 ≤ j :=
    (ctx_part_pruning_history_transport ρ hpos (supportG ρ c) Side.lower 0).1
  have hGroupLimits (ρ : Context)
      (hpos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) (c : ℕ) (p q : ℕ) :
      (groupG ρ c).cupLimit p q = ρ.cupLimit p q ∧
      (groupG ρ c).capLimit p q = ρ.capLimit p q :=
    (ctx_part_pruning_history_transport ρ hpos (supportG ρ c) Side.lower 0).2.2.2.2.2.1 p q
  have hPCongr (ρ : Context) (ks ls : List ℕ)
      (he : ∀ p ∈ ρ.childPositions, p ∈ ks ↔ p ∈ ls) : prune ρ ks = prune ρ ls := by
    unfold prune
    congr 1
    apply List.map_congr_left
    intro p hp
    cases hc : ρ.letterAt p with
    | child =>
      have hm : p ∈ ρ.childPositions := by
        exact List.mem_filter.mpr ⟨hp, by simp [hc]⟩
      simp only [he p hm]
    | ext j v => rfl
  have hPartSub (ρ : Context) (ks : List ℕ) (v : Side) (m : ℕ) :
      (ρ.part ks v m).childPositions ⊆ ρ.childPositions := by
    rw [part_childPositions]
    intro p hp
    exact (List.mem_filter.mp hp).1
  have hGroupPart (ρ : Context) (c : ℕ) (ks : List ℕ) (v : Side) (m : ℕ) :
      groupG (ρ.part ks v m) c = prune (ρ.part ks v m) (supportG ρ c) := by
    apply hPCongr
    intro p hp
    have hs := hPartSub ρ ks v m hp
    simp [supportG, hp, hs]
  have hSmallPart (ρ : Context) (hs : Small ρ) (ks : List ℕ) (v : Side) (m : ℕ) :
      Small (ρ.part ks v m) := by
    intro p hp
    have h := hs p (hPartSub ρ ks v m hp)
    have hl := ctx_part_limits_le ρ ks v m p p
    exact (min_le_min hl.1 hl.2).trans h
  have hColorPart (ρ : Context) (hc : RunColor ρ) (ks : List ℕ) (v : Side) (m : ℕ) :
      RunColor (ρ.part ks v m) := by
    intro p hp q hq hpq hbetween
    exact hc p (hPartSub ρ ks v m hp) q (hPartSub ρ ks v m hq) hpq
      (fun r hpr hrq ↦ hPartSub ρ ks v m (hbetween r hpr hrq))
  have hEmptyGroup (ρ : Context) (c : ℕ)
      (hn : ∀ p ∈ ρ.childPositions, color p ≠ c) : (groupG ρ c).bound = 0 := by
    have he : (groupG ρ c).childPositions = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro p hp
      have hh := (hGroupMem ρ c p).mp hp
      exact hn p hh.1 hh.2
    apply Nat.eq_zero_of_le_zero
    simpa only [he, List.map_nil, List.sum_nil] using (ctx_bound_le_sum_point_bases (groupG ρ c))
  have hCutGroup (ρ : Context)
      (hpos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (c : ℕ) (block : List ℕ) (s t : Side) (m n : ℕ)
      (budget : ℕ) (hBase : (groupG ρ c).bound ≤ budget)
      (hTarget : (∃ p ∈ (groupG ρ c).childPositions, p ∈ block) →
        (∃ p ∈ (groupG ρ c).childPositions, p ∉ block) →
        ((groupG ρ c).part block s m).bound +
          ((groupG ρ c).part (ρ.childPositions.filter (· ∉ block)) t n).bound ≤ budget) :
      (groupG (ρ.part block s m) c).bound +
        (groupG (ρ.part (ρ.childPositions.filter (· ∉ block)) t n) c).bound ≤ budget := by
    let rest := ρ.childPositions.filter (· ∉ block)
    by_cases hSome : ∃ p ∈ (groupG ρ c).childPositions, p ∈ block
    · by_cases hOther : ∃ p ∈ (groupG ρ c).childPositions, p ∉ block
      · obtain ⟨q, hq, hqn⟩ := hOther
        obtain ⟨p, hp, hpb⟩ := hSome
        have hqρ := ((hGroupMem ρ c q).mp hq).1
        have hpρ := ((hGroupMem ρ c p).mp hp).1
        have hqs : q ∈ supportG ρ c := by rw [← hGroupChild]; exact hq
        have hps : p ∈ supportG ρ c := by rw [← hGroupChild]; exact hp
        have hpn : p ∉ rest := by simp [rest, hpb]
        have ha := (ctx_prune_part_projection_of_removed_witness ρ hpos
          (supportG ρ c) block s m q hqρ hqs hqn).2.2
        have hb := (ctx_prune_part_projection_of_removed_witness ρ hpos
          (supportG ρ c) rest t n p hpρ hps hpn).2.2
        rw [hGroupPart, hGroupPart]
        exact (Nat.add_le_add ha hb).trans (hTarget ⟨p, hp, hpb⟩ ⟨q, hq, hqn⟩)
      · have hall : ∀ p ∈ ρ.childPositions, p ∈ supportG ρ c → p ∈ block := by
          intro p hp hps
          have hg : p ∈ (groupG ρ c).childPositions := by rw [hGroupChild]; exact hps
          by_contra hn
          exact hOther ⟨p, hg, hn⟩
        have hz : (groupG (ρ.part rest t n) c).bound = 0 := by
          apply hEmptyGroup
          intro p hp hc
          rw [part_childPositions] at hp
          obtain ⟨hpρ, hpr⟩ := List.mem_filter.mp hp
          have hnot : p ∉ block := (of_decide_eq_true (List.mem_filter.mp
            (of_decide_eq_true hpr)).2)
          exact hOther ⟨p, (hGroupMem ρ c p).mpr ⟨hpρ, hc⟩, hnot⟩
        have ha := (ctx_prune_part_bound_of_all_tracked_retained ρ hpos
          (supportG ρ c) block s m hall).2
        change (groupG (ρ.part block s m) c).bound + (groupG (ρ.part rest t n) c).bound ≤ _
        rw [hz, Nat.add_zero, hGroupPart]
        exact ha.trans hBase
    · have hall : ∀ p ∈ ρ.childPositions, p ∈ supportG ρ c → p ∈ rest := by
        intro p hp hps
        have hg : p ∈ (groupG ρ c).childPositions := by rw [hGroupChild]; exact hps
        have hn : p ∉ block := fun h ↦ hSome ⟨p, hg, h⟩
        simp [rest, hp, hn]
      have hz : (groupG (ρ.part block s m) c).bound = 0 := by
        apply hEmptyGroup
        intro p hp hc
        rw [part_childPositions] at hp
        obtain ⟨hpρ, hpb⟩ := List.mem_filter.mp hp
        exact hSome ⟨p, (hGroupMem ρ c p).mpr ⟨hpρ, hc⟩, of_decide_eq_true hpb⟩
      have hb := (ctx_prune_part_bound_of_all_tracked_retained ρ hpos
        (supportG ρ c) rest t n hall).2
      change (groupG (ρ.part block s m) c).bound + (groupG (ρ.part rest t n) c).bound ≤ _
      rw [hz, Nat.zero_add, hGroupPart]
      exact hb.trans hBase
  have hTarget (c : ℕ)
      (hSome : ∃ p ∈ (group c).childPositions, p ∈ keep)
      (hOther : ∃ p ∈ (group c).childPositions, p ∉ keep) :
      ((group c).part keep s m).bound +
        ((group c).part (σ.childPositions.filter (· ∉ keep)) t n).bound ≤
          2 * (ranks c).card - 1 := by
    obtain ⟨p, hp, hpk⟩ := hSome
    obtain ⟨q, hq, hqk⟩ := hOther
    have hh := (ctx_one_level_arbitrary_cut_rank_bound (group c) (hPos c) s t hne
      N x hN (hNSide c) (hX c) hglobal keep m n p q hp hpk hq hqk).2
    change ((group c).part keep s m).bound +
      ((group c).part ((group c).childPositions.filter (· ∉ keep)) t n).bound ≤
        2 * ((active (group c)).biUnion (I (group c))).card - 1 at hh
    rw [hRanks c] at hh
    have hRest : (group c).part ((group c).childPositions.filter (· ∉ keep)) t n =
        (group c).part (σ.childPositions.filter (· ∉ keep)) t n := by
      apply part_congr
      intro r hr
      have hrσ := ((hChild c r).mp hr).1
      simp [hr, hrσ]
    simpa only [hRest] using hh
  have hPerColor (c : ℕ) : (groupG A c).bound + (groupG B c).bound ≤
      2 * (ranks c).card - 1 :=
    hCutGroup σ hpositive c keep s t m n (2 * (ranks c).card - 1)
      (hGroupBound c) (hTarget c)
  have hOwn (ks : List ℕ) (v : Side) (maximum : ℕ) :
      (∀ fuel, boundFuel fuel (σ.part ks v maximum) ≤ total (σ.part ks v maximum)) ∧
        (σ.part ks v maximum).bound ≤ total (σ.part ks v maximum) := by
    exact ctx_bound_le_sum_run_group_prunings (σ.part ks v maximum)
      (hPartPositive σ ks v maximum) color colors
      (fun r hr ↦ hCover r (hPartSub σ ks v maximum hr))
      (hSmallPart σ hSmall ks v maximum) (hColorPart σ hColor ks v maximum)
  have hTotal : total A + total B ≤ S.card := by
    dsimp only [total]
    rw [← Finset.sum_add_distrib]
    exact (Finset.sum_le_sum (fun c _ ↦ hPerColor c)).trans hCharges
  have hA := hOwn keep s m
  have hB := hOwn (σ.childPositions.filter (· ∉ keep)) t n
  exact ⟨fun f g ↦ (Nat.add_le_add (hA.1 f) (hB.1 g)).trans hTotal,
    (Nat.add_le_add hA.2 hB.2).trans hTotal⟩

end ErdosSzekeres
