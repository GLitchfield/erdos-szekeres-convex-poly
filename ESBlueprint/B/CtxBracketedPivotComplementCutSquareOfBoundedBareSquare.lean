import ESBlueprint.B.CtxSeparatingMarkerRetainedBoundaryRankUnionBound
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsCapacityThree
import ESBlueprint.B.CtxEndpointCutSquareOfBoundedBareSquare

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- An actual internal chosen-complement cut square estimate when the opposite middle block contains child witnesses on both sides of a youngest chosen pivot. The chosen global is at most five, the source opposite indexed history is empty, and every actual chosen indexed occurrence is at the pivot. The explicit bare-square premise is restricted to widths at most w-2. Inactive children, arbitrary original maxima, independent new maxima and independent fuel values are allowed. Exact run-group pruning and a local active retained-boundary argument bound the two outer pieces by w each; the middle loses two ranks. This closes the bracketed-pivot internal orientation while the pivot-exterior one-unit saving remains open.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bracketed_pivot_complement_cut_square_of_bounded_bare_square (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [])
  (hclear : σ.levelsOn t 0 = [])
  (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x)
  (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
  (keep : List ℕ) (a b l r m n : ℕ)
  (ha : a ∈ keep) (hb : b ∈ keep) (hax : a < x) (hxb : x < b)
  (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
  (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
  (hlnot : l ∉ keep) (hrnot : r ∉ keep)
  (hinside : ∀ p ∈ keep, l < p ∧ p < r)
  (hconvex : ∀ p ∈ keep, ∀ q ∈ keep, ∀ z ∈ σ.childPositions,
    p ≤ z → z ≤ q → z ∈ keep) :
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
    ((match t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1) ≤ w - 2 →
    ρ.bound ≤ ((match t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1) ^ 2) →
  (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) +
    Ctx.Context.boundFuel g (σ.part keep t n) ≤ w ^ 2) ∧
    (σ.part rest s m).bound + (σ.part keep t n).bound ≤ w ^ 2 := by
  classical
  have ctx_active_separating_marker_retained_boundary_rank_union_bound (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (N x : ℕ) (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N)
    (rightward : Bool)
    (hchildren : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p →
      if rightward then p < x else x < p)
    (hyounger : ∀ j ∈ σ.levelsOn (σ.sideAt N) N, ∀ p ∈ σ.extPositions j,
      if rightward then p < x else x < p)
    (holder : ∀ j ∈ σ.levelsOn (σ.sideAt N) 0, N < j →
      ∀ p ∈ σ.extPositions j, if rightward then x < p else p < x)
    (I y : ℕ) (hI : I ∈ σ.levels) (hNI : N < I)
    (hIs : σ.sideAt I = σ.sideAt N) (hy : y ∈ σ.extPositions I)
    (hretained : ∀ j ∈ σ.levelsOn (σ.sideAt N) I, j ≠ N →
      ∀ p ∈ σ.extPositions j, if rightward then p < y else y < p)
    (t : Ctx.Side) (hne : σ.sideAt N ≠ t)
    (hglobal : (match (generalizing := false) σ.sideAt N with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) :
    let budget := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    let active := σ.childPositions.toFinset.filter
      (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let ranks := active.biUnion
      (fun p => Finset.Icc (σ.leftExt t 0 p + 1) (budget - σ.rightExt t 0 p))
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ ranks.card) ∧ σ.bound ≤ ranks.card := by
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
    change (∀ fuel, boundFuel fuel σ ≤ (ranks σ).card) ∧ σ.bound ≤ (ranks σ).card
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
    have hRetained : ∀ j ∈ τ.levelsOn (τ.sideAt N) I, j ≠ N → ∀ p ∈ τ.extPositions j,
        if rightward then p < y else y < p := by
      intro j hj hjN p hp
      rw [(hHist N hN).2, hLevels] at hj
      rw [(hHist j (List.mem_filter.mp hj).1).1] at hp
      exact hretained j hj hjN p hp
    have hX : x ∈ τ.extPositions N := by rw [(hHist N hN).1]; exact hx
    have hY : y ∈ τ.extPositions I := by rw [(hHist I hI).1]; exact hy
    have hISide : τ.sideAt I = τ.sideAt N := by rw [(hHist I hI).2, (hHist N hN).2, hIs]
    have hGlobal : G τ (τ.sideAt N) ≤ 5 := by
      rw [(hHist N hN).2]
      exact hglobal
    have hOpp : τ.sideAt N ≠ t := by rw [(hHist N hN).2]; exact hne
    have hd := ctx_separating_marker_retained_boundary_rank_union_bound τ hPos N x hN hX
      rightward hChildren hYoung hOld I y hI hNI hISide hY hRetained hAllActive t hOpp hGlobal
    change (∀ fuel, boundFuel fuel τ ≤ (ranks τ).card) ∧
      τ.bound ≤ (ranks τ).card at hd
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
  let α := σ.part rest s m
  let β := σ.part keep t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ w ^ 2) ∧ α.bound + β.bound ≤ w ^ 2
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ rest := by
    simp only [α, part_childPositions, rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hChildβ (p : ℕ) : p ∈ β.childPositions ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    simp only [β, part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ rest := by
    rw [part_extPositions_one hpositive]
  have hAα : a ∈ α.extPositions 1 := (hExtα a).mpr ⟨hkeep a ha, ha⟩
  have hBα : b ∈ α.extPositions 1 := (hExtα b).mpr ⟨hkeep b hb, hb⟩
  have hLβ : l ∈ β.extPositions 1 := (hExtβ l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
  have hRβ : r ∈ β.extPositions 1 := (hExtβ r).mpr ((hRest r).mpr ⟨hr, hrnot⟩)
  have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive rest s m hAα
  have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t n hLβ
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
  have hPosα := hPositivePart rest s m
  have hPosβ := hPositivePart keep t n
  have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
  have hNpos := one_le_of_mem_levels hN
  have hNα : N + 1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNβ : N + 1 ∈ β.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNsα : α.sideAt (N + 1) = s := (part_sideAt_succ σ rest s m hNpos).trans hNs
  have hNsβ : β.sideAt (N + 1) = s := (part_sideAt_succ σ keep t n hNpos).trans hNs
  have hXα : x ∈ α.extPositions (N + 1) := by rw [part_extPositions_succ σ rest s m hNpos]; exact hx
  have hXβ : x ∈ β.extPositions (N + 1) := by rw [part_extPositions_succ σ keep t n hNpos]; exact hx
  have hYoungβ : ∀ j ∈ β.levelsOn s (N + 1), β.extPositions j = [] := by
    have hs : β.sideAt 1 ≠ s := by rw [hSideβ]; exact Ne.symm hne
    have he := part_levelsOn_other_succ hs hNpos
    intro j hj
    rw [he] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [part_extPositions_succ σ keep t n (one_le_of_mem_levels (List.mem_filter.mp hi).1), hyoung i hi]
  have hLevelsβ : β.levelsOn t 0 = [1] := by
    rw [part_levelsOn_self_zero hSideβ, hclear]
    rfl
  have hw : 2 ≤ w := hwidth
  have hOutside (p : ℕ) (hp : p ∈ rest) :
      (∀ q ∈ keep, p < q) ∨ (∀ q ∈ keep, q < p) := by
    obtain ⟨hpσ, hpnot⟩ := (hRest p).mp hp
    have hpne : p ≠ a := by intro he; exact hpnot (he ▸ ha)
    by_cases hpq : p < a
    · left
      intro q hq
      by_contra h
      exact hpnot (hconvex q hq a ha p hpσ (by omega) (by omega))
    · right
      intro q hq
      by_contra h
      exact hpnot (hconvex a ha q hq p hpσ (by omega) (by omega))
  let activeβ := β.childPositions.toFinset.filter
    (fun p => 0 < β.cupLimit p p ∧ 0 < β.capLimit p p)
  let Iβ (p : ℕ) := Finset.Icc (β.leftExt t 0 p + 1) (w - β.rightExt t 0 p)
  let ranksβ := activeβ.biUnion Iβ
  let J := Finset.Icc 2 (w - 1)
  have hIntervalβ (p : ℕ) (hp : p ∈ β.childPositions) : Iβ p = J := by
    have hpk := ((hChildβ p).mp hp).2
    have hpl := (hinside p hpk).1
    have hpr := (hinside p hpk).2
    have hMemL : l ∈ (β.extPositions 1).filter (· < p) := by simp [hLβ, hpl]
    have hMemR : r ∈ (β.extPositions 1).filter (p < ·) := by simp [hRβ, hpr]
    have hNEL := List.ne_nil_of_mem hMemL
    have hNER := List.ne_nil_of_mem hMemR
    have hLeft : β.leftExt t 0 p = 1 := by
      unfold leftExt
      rw [hLevelsβ]
      change ([0, (match ((β.extPositions 1).filter (· < p)).getLast? with
        | some q => (q, 1) | none => (p, 0)).2].max?).getD 0 = 1
      rw [List.getLast?_eq_some_getLast hNEL]
      rfl
    have hRight : β.rightExt t 0 p = 1 := by
      unfold rightExt
      rw [hLevelsβ]
      change ([0, (match ((β.extPositions 1).filter (p < ·)).head? with
        | some q => (q, 1) | none => (p, 0)).2].max?).getD 0 = 1
      rw [List.head?_eq_some_head hNER]
      rfl
    simp only [Iβ, J, hLeft, hRight]
  have hJCard : J.card = w - 2 := by simp only [J, Nat.card_Icc]; omega
  have hRanksβSub : ranksβ ⊆ J := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    rw [hIntervalβ p (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)] at hz
    exact hz
  have hRanksβCard : ranksβ.card ≤ w - 2 := by
    rw [← hJCard]
    exact Finset.card_le_card hRanksβSub
  have hSquareβ : (∀ fuel, boundFuel fuel β ≤ (w - 2) ^ 2) ∧ β.bound ≤ (w - 2) ^ 2 := by
    have hh := ctx_youngest_marker_rank_square_bound_of_bounded_bare_square β hPosβ s t hne
      (N + 1) x hNβ hNsβ hXβ hglobal hYoungβ
    have hBound : (∀ fuel, boundFuel fuel β ≤ ranksβ.card ^ 2) ∧ β.bound ≤ ranksβ.card ^ 2 := by
      apply hh
      intro ρ K y hpos hzero hs hK hy hactual hg hact hwidthρ
      exact hBare ρ K y hpos hzero hs hK hy hactual hg hact (hwidthρ.trans hRanksβCard)
    have hsquare : ranksβ.card ^ 2 ≤ (w - 2) ^ 2 := by nlinarith [hRanksβCard]
    exact ⟨fun fuel => (hBound.1 fuel).trans hsquare, hBound.2.trans hsquare⟩
  have hOldα : ∀ j ∈ α.levelsOn s 0, 1 < j → ∀ p ∈ α.extPositions j, p = x := by
    intro j hj hj1 p hp
    rw [part_levelsOn_self_zero hSideα] at hj
    rcases List.mem_cons.mp hj with rfl | hj
    · omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      rw [part_extPositions_succ σ rest s m (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
      exact hchosen i hi p hp
  have hRetainedα : ∀ j ∈ α.levelsOn s (N + 1), j ≠ 1 → α.extPositions j = [] := by
    intro j hj hj1
    rw [part_levelsOn_self_succ hSideα hNpos] at hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact False.elim (hj1 rfl)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      rw [part_extPositions_succ σ rest s m (one_le_of_mem_levels (List.mem_filter.mp hi).1)]
      exact hyoung i hi
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
  let color (p : ℕ) := if p < x then (0 : ℕ) else 1
  let support (c : ℕ) := α.childPositions.filter (fun p => color p = c)
  let group (c : ℕ) : Context := { α with
    word := (List.range α.word.length).map (fun p => match α.letterAt p with
      | Letter.child => if p ∈ support c then Letter.child else Letter.ext (α.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let I (ρ : Context) (p : ℕ) := Finset.Icc (ρ.leftExt t 0 p + 1) (w - ρ.rightExt t 0 p)
  let ranks (ρ : Context) := (active ρ).biUnion (I ρ)
  have hNe (p : ℕ) (hp : p ∈ α.childPositions) : p ≠ x := by
    intro he
    subst p
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hXα).2
    simp [hc] at he
  have hNOn : N + 1 ∈ α.levelsOn s 0 := List.mem_filter.mpr ⟨hNα, by simp [hNsα]⟩
  have hSmall : ∀ p ∈ α.childPositions, min (α.cupLimit p p) (α.capLimit p p) ≤ 3 := by
    intro p hp
    have hn := hNe p hp
    have hg : (match s with | Side.lower => α.u | Side.upper => α.a) ≤ 5 := hglobal
    by_cases hpx : p < x
    · have he := hOneRight α s (N + 1) p x hNOn hXα hpx
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hg ⊢ <;> omega
    · have he := hOneLeft α s (N + 1) p x hNOn hXα (by omega)
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hg ⊢ <;> omega
  have hCover : ∀ p ∈ α.childPositions, color p ∈ ({0, 1} : Finset ℕ) := by
    intro p hp
    dsimp only [color]
    split_ifs <;> simp
  have hColor : ∀ p ∈ α.childPositions, ∀ q ∈ α.childPositions, p ≤ q →
      (∀ z, p ≤ z → z ≤ q → z ∈ α.childPositions) → color p = color q := by
    intro p hp q hq hpq hbetween
    have hside : (p < x) = (q < x) := by
      apply propext
      constructor
      · intro hpx
        by_contra hqx
        have hxc := hbetween x (by omega) (by omega)
        exact hNe x hxc rfl
      · omega
    simp only [color, hside]
  have hPos (c : ℕ) : ∀ p j v, (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
    (ctx_part_pruning_history_transport α hPosα (support c) Side.lower 0).1
  have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔ p ∈ α.childPositions ∧ color p = c := by
    have hh : (group c).childPositions = α.childPositions.filter (· ∈ support c) :=
      (ctx_part_pruning_history_transport α hPosα (support c) Side.lower 0).2.1
    rw [hh]
    simp [support, and_assoc]
  have hHist (c j : ℕ) (hj : j ∈ α.levels) :
      (group c).extPositions j = α.extPositions j ∧ (group c).sideAt j = α.sideAt j :=
    (ctx_part_pruning_history_transport α hPosα (support c) Side.lower 0).2.2.1 j hj
  have hLevels (c : ℕ) (v : Side) (top : ℕ) : (group c).levelsOn v top = α.levelsOn v top :=
    (ctx_part_pruning_history_transport α hPosα (support c) Side.lower 0).2.2.2.1 v top
  have hOneSide (c : ℕ) : (group c).sideAt 1 = s := (hHist c 1 hOneα).2.trans hSideα
  have hRankCard (c : ℕ) : (ranks (group c)).card ≤ w := by
    have hSub : ranks (group c) ⊆ Finset.Icc 1 w := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hh := Finset.mem_Icc.mp hz
      apply Finset.mem_Icc.mpr
      omega
    have hc : (Finset.Icc 1 w).card = w := by simp only [Nat.card_Icc]; omega
    rw [← hc]
    exact Finset.card_le_card hSub
  have hLinearGroup (c : ℕ) (direction : Bool) (z : ℕ) (hz : z ∈ α.extPositions 1)
      (hsep : if direction then z < x else x < z)
      (hchildren : ∀ p ∈ (group c).childPositions, if direction then p < z else z < p) :
      (group c).bound ≤ w := by
    have hZ : z ∈ (group c).extPositions 1 := by rw [(hHist c 1 hOneα).1]; exact hz
    have hX : x ∈ (group c).extPositions (N + 1) := by
      rw [(hHist c (N + 1) hNα).1]
      exact hXα
    have hOld : ∀ j ∈ (group c).levelsOn ((group c).sideAt 1) 0,
        1 < j → ∀ p ∈ (group c).extPositions j, if direction then z < p else p < z := by
      intro j hj hj1 p hp
      rw [hOneSide c, hLevels c s 0] at hj
      rw [(hHist c j (List.mem_filter.mp hj).1).1] at hp
      have he := hOldα j hj hj1 p hp
      subst p
      exact hsep
    have hRetained : ∀ j ∈ (group c).levelsOn ((group c).sideAt 1) (N + 1),
        j ≠ 1 → ∀ p ∈ (group c).extPositions j, if direction then p < x else x < p := by
      intro j hj hj1 p hp
      rw [hOneSide c, hLevels c s (N + 1)] at hj
      rw [(hHist c j (List.mem_filter.mp hj).1).1, hRetainedα j hj hj1] at hp
      exact False.elim (List.not_mem_nil hp)
    have hGlobal : (match (group c).sideAt 1 with
        | Side.lower => (group c).u | Side.upper => (group c).a) ≤ 5 := by
      rw [hOneSide c]
      exact hglobal
    have hISide : (group c).sideAt (N + 1) = (group c).sideAt 1 := by
      rw [(hHist c (N + 1) hNα).2, hNsα, hOneSide c]
    have hh := ctx_active_separating_marker_retained_boundary_rank_union_bound (group c) (hPos c)
      1 z hOneα hZ direction (by intro p hp hact; exact hchildren p hp)
      (by simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true])
      hOld (N + 1) x hNα (by omega) hISide hX hRetained
      t (by rw [hOneSide c]; exact hne) hGlobal
    have hBound : (group c).bound ≤ (ranks (group c)).card := hh.2
    exact hBound.trans (hRankCard c)
  have hB0 : (group 0).bound ≤ w := by
    apply hLinearGroup 0 true a hAα hax
    intro p hp
    have hc := (hChild 0 p).mp hp
    have hpx : p < x := by
      have hh := hc.2
      dsimp only [color] at hh
      split_ifs at hh <;> omega
    rcases hOutside p ((hChildα p).mp hc.1) with h | h
    · exact h a ha
    · have hh := h b hb
      omega
  have hB1 : (group 1).bound ≤ w := by
    apply hLinearGroup 1 false b hBα hxb
    intro p hp
    have hc := (hChild 1 p).mp hp
    have hn := hNe p hc.1
    have hxp : x < p := by
      have hh := hc.2
      dsimp only [color] at hh
      split_ifs at hh <;> omega
    rcases hOutside p ((hChildα p).mp hc.1) with h | h
    · have hh := h a ha
      omega
    · exact h b hb
  have hOwn : (∀ fuel, boundFuel fuel α ≤ 2 * w) ∧ α.bound ≤ 2 * w := by
    have hd := ctx_bound_le_sum_run_group_prunings_capacity_three α hPosα color {0, 1}
      hCover hSmall hColor
    change (∀ fuel, boundFuel fuel α ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
      α.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hd
    have hSum : ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) =
        (group 0).bound + (group 1).bound := by simp
    rw [hSum] at hd
    constructor
    · intro fuel
      have hh := hd.1 fuel
      omega
    · have hh := hd.2
      omega
  have hBudget : 2 * w + (w - 2) ^ 2 ≤ w ^ 2 := by
    have hw2 : w - 2 + 2 = w := by omega
    nlinarith
  constructor
  · intro f g
    exact (Nat.add_le_add (hOwn.1 f) (hSquareβ.1 g)).trans hBudget
  · exact (Nat.add_le_add hOwn.2 hSquareβ.2).trans hBudget

end ErdosSzekeres
