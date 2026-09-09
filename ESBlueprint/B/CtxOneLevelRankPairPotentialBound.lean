import ESBlueprint.B.CtxOneLevelRefinedPotentialBound
import ESBlueprint.B.RankPairCardGeSumDisjointGroupCharges

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- For any positive-label context with an actual chosen-side marker and chosen global at most four, every-fuel and full context bounds are at most the cardinality of the union of ordered opposite-rank pairs available at active children. Color children by the number of missing successor pairs below their lower opposite-rank endpoint. Interval ranks share the color and colors are constant on physical child runs. Finite pruning decomposition and the general one-level doubled-rank bound then match disjoint diagonal/successor pair reservations. Allows inactive children, multiple markers and levels, varying middle histories and arbitrary maxima; no band-separation or exact-projection premises.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_one_level_rank_pair_potential_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) :
  let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let interval := fun p => Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p)
  let pairs := active.biUnion (fun p => ((interval p).product (interval p)).filter (fun z => z.1 ≤ z.2))
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ pairs.card) ∧ σ.bound ≤ pairs.card := by
  classical
  have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
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
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let I (ρ : Context) (r : ℕ) :=
    Finset.Icc (ρ.leftExt t 0 r + 1) (G ρ t - 1 - ρ.rightExt t 0 r)
  let Tri (r : ℕ) := ((I σ r).product (I σ r)).filter (fun z => z.1 ≤ z.2)
  let S := (active σ).biUnion Tri
  let P := G σ t - 1
  let gaps := (Finset.range P).filter (fun z => (z, z + 1) ∉ S)
  let key := fun z => (gaps.filter (· < z)).card
  let color := fun r => key (σ.leftExt t 0 r + 1)
  let colors := Finset.range (gaps.card + 1)
  let ranks (c : ℕ) := ((active σ).filter (fun p => color p = c)).biUnion (I σ)
  let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
  let group (c : ℕ) : Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Letter.child => if p ∈ support c then Letter.child
          else Letter.ext (σ.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  change (∀ fuel, boundFuel fuel σ ≤ S.card) ∧ σ.bound ≤ S.card
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
  have hDecomp := ctx_bound_le_sum_run_group_prunings σ hpositive color colors hCover hSmall hColor
  change (∀ fuel, boundFuel fuel σ ≤ colors.sum (fun c => (group c).bound)) ∧
    σ.bound ≤ colors.sum (fun c => (group c).bound) at hDecomp
  have hBudget : colors.sum (fun c => (group c).bound) ≤ S.card :=
    (Finset.sum_le_sum (fun c _ => hGroupBound c)).trans hCharges
  exact ⟨fun fuel => (hDecomp.1 fuel).trans hBudget, hDecomp.2.trans hBudget⟩

end ErdosSzekeres
