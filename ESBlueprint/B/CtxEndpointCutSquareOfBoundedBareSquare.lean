import ESBlueprint.B.CtxSeparatingMarkerRetainedLevelDoubledRankBound
import ESBlueprint.B.CtxBoundLeInactivePruneCapacityThree
import ESBlueprint.B.CtxYoungestMarkerRankSquareBoundOfBoundedBareSquare
import ESBlueprint.B.CtxInternalIntervalCutSquareOfEmptyOppositeHistory

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- An actual endpoint-cut square estimate for either spatial direction. The chosen global is at most five, the opposite indexed history is empty, and every actual chosen indexed occurrence equals a youngest chosen pivot. Both parts are nonempty and the opposite width is at least two. The explicit bare-marker square premise is restricted to widths at most w-1. The new maxima and fuel values of the two parts are independent. The proof derives either a 2w-1 chosen charge plus a smaller-width square or complementary triangular charges. Inactive children and arbitrary original maxima are permitted. The active separator pruning argument is a local helper, not a separately exported node. This supports width induction; the bare-square premise and internal chosen-complement case are not established here.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_endpoint_cut_square_of_bounded_bare_square (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [])
  (hclear : σ.levelsOn t 0 = [])
  (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x)
  (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
  (keep : List ℕ) (q₀ r₀ m n : ℕ) (rightward : Bool)
  (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
  (hr₀ : r₀ ∈ σ.childPositions) (hrnot : r₀ ∉ keep)
  (hendpoint : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep →
    if rightward then p < q else q < p) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ (ρ : Ctx.Context) (J y : ℕ),
    (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
    (∀ j ∈ ρ.levels, ρ.maximumAt j = 0) →
    (∀ j ∈ ρ.levels, ρ.sideAt j = s) →
    J ∈ ρ.levels → y ∈ ρ.extPositions J →
    (∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = y) →
    (match s with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) ≤ 5 →
    (∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) →
    ((match t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1) ≤ w - 1 →
    ρ.bound ≤ ((match t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1) ^ 2) →
  (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) +
    Ctx.Context.boundFuel g (σ.part rest t n) ≤ w ^ 2) ∧
    (σ.part keep s m).bound + (σ.part rest t n).bound ≤ w ^ 2 := by
  classical
  have ctx_active_separating_marker_retained_level_doubled_rank_bound (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N)
    (rightward : Bool)
    (hchildren : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p →
      if rightward then p < x else x < p)
    (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
      if rightward then p < x else x < p)
    (holder : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, N < j →
      ∀ p ∈ σ.extPositions j, if rightward then x < p else p < x)
    (I y : ℕ) (hI : I ∈ σ.levels) (hNI : I ≠ N)
    (hIs : σ.sideAt I = σ.sideAt N) (hy : y ∈ σ.extPositions I)
    (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
    (hglobal : (match (generalizing := false) σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) :
    let budget := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    let active := σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let ranks := active.biUnion
      (fun p => Finset.Icc (σ.leftExt t 0 p + 1) (budget - σ.rightExt t 0 p))
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 2 * ranks.card - 1) ∧ σ.bound ≤ 2 * ranks.card - 1 := by
    classical
    let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
    let active (ρ : Context) := ρ.childPositions.toFinset.filter
      (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    let ranks (ρ : Context) := (active ρ).biUnion
      (fun p => Finset.Icc (ρ.leftExt t 0 p + 1) (G ρ t - 1 - ρ.rightExt t 0 p))
    let keep := σ.childPositions.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let τ : Context := { σ with
      word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
        | Letter.child => if p ∈ keep then Letter.child else Letter.ext (σ.maxima.length + 1) Side.lower
        | Letter.ext j v => Letter.ext j v) }
    change (∀ fuel, boundFuel fuel σ ≤ 2 * (ranks σ).card - 1) ∧ σ.bound ≤ 2 * (ranks σ).card - 1
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
    have hNOn : N ∈ σ.levelsOn (σ.sideAt N) 0 := List.mem_filter.mpr ⟨hN, by simp⟩
    have hSmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3 := by
      intro p hp
      by_cases ha : 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p
      · have hc := hchildren p hp ha
        have he : 1 ≤ σ.leftExt (σ.sideAt N) 0 p ∨ 1 ≤ σ.rightExt (σ.sideAt N) 0 p := by
          cases rightward with
          | false => exact Or.inl (hOneLeft σ (σ.sideAt N) N p x hNOn hx hc)
          | true => exact Or.inr (hOneRight σ (σ.sideAt N) N p x hNOn hx hc)
        cases hs : σ.sideAt N <;>
          simp only [hs, cupLimit, capLimit, chainExt] at hglobal he ⊢ <;> omega
      · omega
    have ht := ctx_part_pruning_history_transport σ hpositive keep Side.lower 0
    have hPos : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := ht.1
    have hChild : τ.childPositions = σ.childPositions.filter (· ∈ keep) := ht.2.1
    have hHist : ∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧
        τ.sideAt j = σ.sideAt j := ht.2.2.1
    have hLevels : ∀ v top, τ.levelsOn v top = σ.levelsOn v top := ht.2.2.2.1
    have hPure : ∀ v top p, τ.leftExt v top p = σ.leftExt v top p ∧
        τ.rightExt v top p = σ.rightExt v top p := ht.2.2.2.2.1
    have hLimits : ∀ p q, τ.cupLimit p q = σ.cupLimit p q ∧
        τ.capLimit p q = σ.capLimit p q := ht.2.2.2.2.2.1
    have hMem (p : ℕ) : p ∈ τ.childPositions ↔ p ∈ σ.childPositions ∧
        0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p := by
      rw [hChild]
      simp only [keep, List.mem_filter, decide_eq_true_eq]
      tauto
    have hAllActive : ∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := by
      intro p hp
      rw [(hLimits p p).1, (hLimits p p).2]
      exact ((hMem p).mp hp).2
    have hChildren : ∀ p ∈ τ.childPositions, if rightward then p < x else x < p := by
      intro p hp
      obtain ⟨hc, ha⟩ := (hMem p).mp hp
      exact hchildren p hc ha
    have hYoung : ∀ j ∈ τ.levelsOn (τ.sideAt N) N, ∀ p ∈ τ.extPositions j,
        if rightward then p < x else x < p := by
      intro j hj p hp
      rw [(hHist N hN).2, hLevels] at hj
      rw [(hHist j (List.mem_filter.mp hj).1).1] at hp
      exact hyounger j hj p hp
    have hOld : ∀ j ∈ τ.levelsOn (τ.sideAt N) 0, N < j → ∀ p ∈ τ.extPositions j,
        if rightward then x < p else p < x := by
      intro j hj hNj p hp
      rw [(hHist N hN).2, hLevels] at hj
      rw [(hHist j (List.mem_filter.mp hj).1).1] at hp
      exact holder j hj hNj p hp
    have hX : x ∈ τ.extPositions N := by rw [(hHist N hN).1]; exact hx
    have hY : y ∈ τ.extPositions I := by rw [(hHist I hI).1]; exact hy
    have hISide : τ.sideAt I = τ.sideAt N := by rw [(hHist I hI).2, (hHist N hN).2, hIs]
    have hGlobal : G τ (τ.sideAt N) ≤ 5 := by
      rw [(hHist N hN).2]
      exact hglobal
    have hOpp : τ.sideAt N ≠ t := by rw [(hHist N hN).2]; exact hne
    have hd := ctx_separating_marker_retained_level_doubled_rank_bound τ hPos N x hN hX
      rightward hChildren hYoung hOld I y hI hNI hISide hY hAllActive t hOpp hGlobal
    change (∀ fuel, boundFuel fuel τ ≤ 2 * (ranks τ).card - 1) ∧
      τ.bound ≤ 2 * (ranks τ).card - 1 at hd
    have hActive : active τ = active σ := by
      ext p
      simp only [active, Finset.mem_filter, List.mem_toFinset, hMem,
        (hLimits p p).1, (hLimits p p).2]
      tauto
    have hRanks : ranks τ = ranks σ := by
      simp only [ranks, hActive, (hPure t 0 _).1, (hPure t 0 _).2]
      rfl
    rw [hRanks] at hd
    have hm := ctx_bound_le_inactive_prune_capacity_three σ hpositive hSmall
    change (∀ fuel, boundFuel fuel σ ≤ τ.bound) ∧ σ.bound ≤ τ.bound at hm
    exact ⟨fun fuel => (hm.1 fuel).trans hd.2, hm.2.trans hd.2⟩

  classical
  dsimp only
  intro hBare
  let w := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part keep s m
  let β := σ.part rest t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ w ^ 2) ∧ α.bound + β.bound ≤ w ^ 2
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [α, part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hChildβ (p : ℕ) : p ∈ β.childPositions ↔ p ∈ rest := by
    simp only [β, part_childPositions, rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔ p ∈ rest := by
    rw [part_extPositions_one hpositive]
  have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hRα : r₀ ∈ α.extPositions 1 := (hExtα r₀).mpr ((hRest r₀).mpr ⟨hr₀, hrnot⟩)
  have hQβ : q₀ ∈ β.extPositions 1 := (hExtβ q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
  have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive keep s m hRα
  have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive rest t n hQβ
  have hPositivePart (ks : List ℕ) (v : Side) (a : ℕ) :
      ∀ p j z, (σ.part ks v a).letterAt p = Letter.ext j z → 1 ≤ j := by
    intro p j z hp
    have hpl : p < σ.word.length := by
      by_contra h
      have hh := letterAt_of_length_le (σ.part ks v a)
        (show (σ.part ks v a).word.length ≤ p by rw [part_word_length]; omega)
      rw [hh] at hp
      cases hp
    cases he : σ.letterAt p with
    | child =>
      rw [part_letterAt_of_child σ ks v a hpl he] at hp
      split at hp
      · cases hp
      · cases hp; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ ks v a hpl he] at hp
      cases hp; omega
  have hPosα := hPositivePart keep s m
  have hPosβ := hPositivePart rest t n
  have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
  have hNpos := one_le_of_mem_levels hN
  have hNα : N + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNβ : N + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNsα : α.sideAt (N + 1) = s := (part_sideAt_succ σ keep s m hNpos).trans hNs
  have hNsβ : β.sideAt (N + 1) = s := (part_sideAt_succ σ rest t n hNpos).trans hNs
  have hXα : x ∈ α.extPositions (N + 1) := by rw [part_extPositions_succ σ keep s m hNpos]; exact hx
  have hXβ : x ∈ β.extPositions (N + 1) := by rw [part_extPositions_succ σ rest t n hNpos]; exact hx
  have hYoungβ : ∀ j ∈ β.levelsOn s (N + 1), β.extPositions j = [] := by
    have hs : β.sideAt 1 ≠ s := by rw [hSideβ]; exact Ne.symm hne
    have he := part_levelsOn_other_succ hs hNpos
    intro j hj
    rw [he] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [part_extPositions_succ σ rest t n (one_le_of_mem_levels (List.mem_filter.mp hi).1), hyoung i hi]
  have hLevelsβ : β.levelsOn t 0 = [1] := by
    rw [part_levelsOn_self_zero hSideβ, hclear]
    rfl
  have hw : 2 ≤ w := hwidth
  let active := β.childPositions.toFinset.filter
    (fun p => 0 < β.cupLimit p p ∧ 0 < β.capLimit p p)
  let I (p : ℕ) := Finset.Icc (β.leftExt t 0 p + 1) (w - β.rightExt t 0 p)
  let L := Finset.Icc 1 (w - 1)
  let R := Finset.Icc 2 w
  have hActive (p : ℕ) (hp : p ∈ active) : p ∈ rest :=
    (hChildβ p).mp (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
  have hLeftRank (p : ℕ) (hp : ∀ q ∈ keep, p < q) : I p = L := by
    have hEmpty : (β.extPositions 1).filter (· < p) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq hbad
      have hqp : q < p := of_decide_eq_true hbad
      have hpq := hp q ((hExtβ q).mp hq).2
      omega
    have hMem : q₀ ∈ (β.extPositions 1).filter (p < ·) := by simp [hQβ, hp q₀ hq₀]
    have hNE := List.ne_nil_of_mem hMem
    have hLeft : β.leftExt t 0 p = 0 := by simp [leftExt, hLevelsβ, hEmpty, -List.getLast?_filter]
    have hRight : β.rightExt t 0 p = 1 := by
      unfold rightExt
      rw [hLevelsβ]
      change ([0, (match ((β.extPositions 1).filter (p < ·)).head? with
        | some q => (q, 1) | none => (p, 0)).2].max?).getD 0 = 1
      rw [List.head?_eq_some_head hNE]
      rfl
    simp only [I, L, hLeft, hRight, Nat.zero_add]
  have hRightRank (p : ℕ) (hp : ∀ q ∈ keep, q < p) : I p = R := by
    have hEmpty : (β.extPositions 1).filter (p < ·) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro q hq hbad
      have hpq : p < q := of_decide_eq_true hbad
      have hqp := hp q ((hExtβ q).mp hq).2
      omega
    have hMem : q₀ ∈ (β.extPositions 1).filter (· < p) := by simp [hQβ, hp q₀ hq₀]
    have hNE := List.ne_nil_of_mem hMem
    have hLeft : β.leftExt t 0 p = 1 := by
      unfold leftExt
      rw [hLevelsβ]
      change ([0, (match ((β.extPositions 1).filter (· < p)).getLast? with
        | some q => (q, 1) | none => (p, 0)).2].max?).getD 0 = 1
      rw [List.getLast?_eq_some_getLast hNE]
      rfl
    have hRight : β.rightExt t 0 p = 0 := by simp [rightExt, hLevelsβ, hEmpty, -List.head?_filter]
    simp only [I, R, hLeft, hRight, Nat.sub_zero]
  let J := if rightward then R else L
  let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
  let ranksβ := active.biUnion I
  let pairsβ := active.biUnion (fun p => Q (I p))
  have hInterval (p : ℕ) (hp : p ∈ β.childPositions) : I p = J := by
    have hr := (hRest p).mp ((hChildβ p).mp hp)
    cases rightward with
    | false =>
      exact hLeftRank p (fun q hq => hendpoint q hq p hr.1 hr.2)
    | true =>
      exact hRightRank p (fun q hq => hendpoint q hq p hr.1 hr.2)
  have hJCard : J.card = w - 1 := by
    cases rightward <;> simp only [J, Bool.false_eq_true, if_false, if_true, R, L, Nat.card_Icc] <;> omega
  have hRanksβSub : ranksβ ⊆ J := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    rw [hInterval p (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)] at hz
    exact hz
  have hRanksβCard : ranksβ.card ≤ w - 1 := by
    rw [← hJCard]
    exact Finset.card_le_card hRanksβSub
  have hPairsβSub : pairsβ ⊆ Q J := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    rw [hInterval p (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)] at hz
    exact hz
  have hCardPairs (T : Finset ℕ) : (Q T).card = (T.card + 1).choose 2 := by
    rw [← Finset.card_sym2]
    apply Finset.card_bij (fun z _ => Sym2.mk z.1 z.2)
    · intro z hz
      exact Finset.mk_mem_sym2_iff.mpr (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
    · intro p hp q hq he
      have hpl := (Finset.mem_filter.mp hp).2
      have hql := (Finset.mem_filter.mp hq).2
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · apply Prod.ext <;> omega
    · intro z hz
      induction z using Sym2.ind with
      | h a b =>
        obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hz
        by_cases hab : a ≤ b
        · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
        · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩,
            Sym2.eq_swap⟩
  have hPairsβCard : pairsβ.card ≤ w.choose 2 := by
    have hh := Finset.card_le_card hPairsβSub
    rw [hCardPairs, hJCard, Nat.sub_add_cancel (show 1 ≤ w by omega)] at hh
    exact hh
  have hSquareβ : (∀ fuel, boundFuel fuel β ≤ (w - 1) ^ 2) ∧ β.bound ≤ (w - 1) ^ 2 := by
    have hh := ctx_youngest_marker_rank_square_bound_of_bounded_bare_square β hPosβ s t hne
      (N + 1) x hNβ hNsβ hXβ hglobal hYoungβ
    have hBound : (∀ fuel, boundFuel fuel β ≤ ranksβ.card ^ 2) ∧ β.bound ≤ ranksβ.card ^ 2 := by
      apply hh
      intro ρ K y hpos hzero hs hK hy hactual hg ha hwidthρ
      exact hBare ρ K y hpos hzero hs hK hy hactual hg ha (hwidthρ.trans hRanksβCard)
    have hsquare : ranksβ.card ^ 2 ≤ (w - 1) ^ 2 := by nlinarith [hRanksβCard]
    exact ⟨fun fuel => (hBound.1 fuel).trans hsquare, hBound.2.trans hsquare⟩
  let ownActive := α.childPositions.toFinset.filter
    (fun p => 0 < α.cupLimit p p ∧ 0 < α.capLimit p p)
  let ownI (p : ℕ) := Finset.Icc (α.leftExt t 0 p + 1) (w - α.rightExt t 0 p)
  let ownRanks := ownActive.biUnion ownI
  let ownPairs := ownActive.biUnion (fun p => Q (ownI p))
  have hCard : (Finset.Icc 1 w).card = w := by simp only [Nat.card_Icc]; omega
  have hOwnInterval (p : ℕ) : ownI p ⊆ Finset.Icc 1 w := by
    intro z hz
    have hh := Finset.mem_Icc.mp hz
    apply Finset.mem_Icc.mpr
    omega
  have hOwnSub : ownRanks ⊆ Finset.Icc 1 w := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    exact hOwnInterval p hz
  have hOwnCard : ownRanks.card ≤ w := by
    rw [← hCard]
    exact Finset.card_le_card hOwnSub
  have hOwnPairsSub : ownPairs ⊆ Q (Finset.Icc 1 w) := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hz, ho⟩ := Finset.mem_filter.mp hz
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hOwnInterval p h1, hOwnInterval p h2⟩, ho⟩
  have hOwnPairsCard : ownPairs.card ≤ (w + 1).choose 2 := by
    have hh := Finset.card_le_card hOwnPairsSub
    rw [hCardPairs, hCard] at hh
    exact hh
  have hGlobalα : (match α.sideAt 1 with | Side.lower => α.u | Side.upper => α.a) ≤ 5 := by
    rw [hSideα]
    exact hglobal
  have hPairSmallα : min ((match α.sideAt 1 with | Side.lower => α.u | Side.upper => α.a) - 1)
      (α.k - α.maximumAt 1) ≤ 4 := by omega
  have hOwnPairBound : (∀ fuel, boundFuel fuel α ≤ (w + 1).choose 2) ∧
      α.bound ≤ (w + 1).choose 2 := by
    have hh := ctx_active_boundary_marker_rank_pair_union_bound α hPosα 1 r₀ hOneα hRα
      rightward (by
        intro p hp ha
        exact hendpoint p ((hChildα p).mp hp).2 r₀ hr₀ hrnot)
      (by simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true])
      t (by rw [hSideα]; exact hne) hPairSmallα
    change (∀ fuel, boundFuel fuel α ≤ ownPairs.card) ∧ α.bound ≤ ownPairs.card at hh
    exact ⟨fun fuel => (hh.1 fuel).trans hOwnPairsCard, hh.2.trans hOwnPairsCard⟩
  have hLinearα (a : ℕ) (ha : a ∈ rest)
      (hsep : if rightward then a < x else x < a) :
      (∀ fuel, boundFuel fuel α ≤ 2 * w - 1) ∧ α.bound ≤ 2 * w - 1 := by
    have hA : a ∈ α.extPositions 1 := (hExtα a).mpr ha
    have hLevelsα : α.levelsOn s 0 = 1 :: (σ.levelsOn s 0).map (· + 1) :=
      part_levelsOn_self_zero hSideα
    have hOld : ∀ j ∈ α.levelsOn (α.sideAt 1) 0, 1 < j → ∀ p ∈ α.extPositions j,
        if rightward then a < p else p < a := by
      intro j hj hj1 p hp
      rw [hSideα, hLevelsα] at hj
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        rw [part_extPositions_succ σ keep s m (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
        have he := hchosen i hi p hp
        subst p
        exact hsep
    have hh := ctx_active_separating_marker_retained_level_doubled_rank_bound α hPosα 1 a
      hOneα hA rightward (by
        intro p hp hact
        have hr := (hRest a).mp ha
        exact hendpoint p ((hChildα p).mp hp).2 a hr.1 hr.2)
      (by simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true])
      hOld (N + 1) x hNα (by omega) (by rw [hNsα, hSideα]) hXα
      t (by rw [hSideα]; exact hne) hGlobalα
    change (∀ fuel, boundFuel fuel α ≤ 2 * ownRanks.card - 1) ∧
      α.bound ≤ 2 * ownRanks.card - 1 at hh
    have hle : 2 * ownRanks.card - 1 ≤ 2 * w - 1 := by omega
    exact ⟨fun fuel => (hh.1 fuel).trans hle, hh.2.trans hle⟩
  by_cases hSep : ∃ p ∈ rest, if rightward then p < x else x < p
  · obtain ⟨p, hp, hsep⟩ := hSep
    have hOwn := hLinearα p hp hsep
    have hIdentity : 2 * w - 1 + (w - 1) ^ 2 = w ^ 2 := by
      have hw1 : w - 1 + 1 = w := by omega
      have hw2 : 2 * w - 1 + 1 = 2 * w := by omega
      nlinarith
    constructor
    · intro f g
      exact (Nat.add_le_add (hOwn.1 f) (hSquareβ.1 g)).trans_eq hIdentity
    · exact (Nat.add_le_add hOwn.2 hSquareβ.2).trans_eq hIdentity
  have hNe (p : ℕ) (hp : p ∈ rest) : p ≠ x := by
    intro he
    subst p
    have hc := of_decide_eq_true (List.mem_filter.mp ((hRest x).mp hp).1).2
    have he := (List.mem_filter.mp hx).2
    simp [hc] at he
  have hBoundaryβ : ∀ p ∈ β.childPositions,
      0 < β.cupLimit p p ∧ 0 < β.capLimit p p →
      if !rightward then p < x else x < p := by
    intro p hp hact
    have hr := (hChildβ p).mp hp
    have hn := hNe p hr
    have hnot : ¬ (if rightward then p < x else x < p) := by
      intro hh
      exact hSep ⟨p, hr, hh⟩
    cases rightward <;> simp only [Bool.not_false, Bool.not_true, if_true, if_false,
      Bool.false_eq_true] at hnot ⊢ <;> omega
  have hPairSmallβ : min ((match β.sideAt (N + 1) with | Side.lower => β.u | Side.upper => β.a) - 1)
      (β.k - β.maximumAt (N + 1)) ≤ 4 := by
    rw [hNsβ]
    change min ((match s with | Side.lower => σ.u | Side.upper => σ.a) - 1) _ ≤ 4
    omega
  have hPairBoundβ : (∀ fuel, boundFuel fuel β ≤ w.choose 2) ∧ β.bound ≤ w.choose 2 := by
    have hh := ctx_active_boundary_marker_rank_pair_union_bound β hPosβ (N + 1) x hNβ hXβ
      (!rightward) hBoundaryβ (by
        intro j hj p hp
        rw [hNsβ] at hj
        rw [hYoungβ j hj] at hp
        exact False.elim (List.not_mem_nil hp))
      t (by rw [hNsβ]; exact hne) hPairSmallβ
    change (∀ fuel, boundFuel fuel β ≤ pairsβ.card) ∧ β.bound ≤ pairsβ.card at hh
    exact ⟨fun fuel => (hh.1 fuel).trans hPairsβCard, hh.2.trans hPairsβCard⟩
  have hTwoChoose (n : ℕ) : 2 * (n + 1).choose 2 = n * n + n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith
  have hTriangles : (w + 1).choose 2 + w.choose 2 = w ^ 2 := by
    have h1 := hTwoChoose w
    have h2 := hTwoChoose (w - 1)
    have hw1 : w - 1 + 1 = w := by omega
    rw [hw1] at h2
    nlinarith
  constructor
  · intro f g
    exact (Nat.add_le_add (hOwnPairBound.1 f) (hPairBoundβ.1 g)).trans_eq hTriangles
  · exact (Nat.add_le_add hOwnPairBound.2 hPairBoundβ.2).trans_eq hTriangles

end ErdosSzekeres
