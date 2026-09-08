import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential
import ESBlueprint.B.CtxSingleRunDescendantBoundNormalize
import ESBlueprint.B.CtxUnitAxisActiveRegionPotential

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Additivity for arbitrary disjoint kept sets in a nonempty single ancestor child run when either ancestor cup or cap capacity is at most two. Covers both opposite-side orientations, arbitrary new maxima, empty parts and non-covering sets, assuming only positive external labels. Normalizes old external history into ancestor capacities, then combines the small-global-axis rank-region potential with the unit-axis region inequality. Removes all block-length and orientation restrictions from the sandwich obstruction in this capacity range.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_disjoint_single_run_small_axis (σ : Ctx.Context)
  (hpositive : ∀ x j v, σ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j)
  (b N : ℕ) (hpos : σ.childPositions = List.range' b N) (hN : 0 < N)
  (hsmall : min (σ.cupLimit b b) (σ.capLimit b b) ≤ 2)
  (keep rest : List ℕ) (s t : Ctx.Side) (hne : s ≠ t) (m n : ℕ)
  (hdis : ∀ p ∈ σ.childPositions, p ∈ keep → p ∉ rest) :
  (σ.part keep s m).bound + (σ.part rest t n).bound ≤ σ.bound := by
  classical
  let C := σ.cupLimit b b
  let P := σ.capLimit b b
  let τ : Context := { σ with a := P + 1, u := C + 1, maxima := [] }
  let cap (v : Side) := match v with | Side.lower => C | Side.upper => P
  let lim (v : Side) (ρ : Context) (p : ℕ) := match v with
    | Side.lower => ρ.cupLimit p p
    | Side.upper => ρ.capLimit p p
  let marks (v : Side) (ρ : Context) : Finset ℕ :=
    (ρ.levelsOn v 0).toFinset.biUnion (fun j => (ρ.extPositions j).toFinset)
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let reg (v : Side) (ρ : Context) :=
    ((active ρ).image (fun p => ((marks v ρ).filter (· < p)).card)).card
  let G (v : Side) (ρ : Context) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let budget (w : Side) (ρ : Context) := match w with
    | Side.lower => ρ.u - 1
    | Side.upper => ρ.a - 1
  let ranks (w : Side) (ρ : Context) := (active ρ).biUnion
    (fun p => Finset.Icc (ρ.leftExt w 0 p + 1) (budget w ρ - ρ.rightExt w 0 p))
  let V (v w : Side) (ρ : Context) :=
    if marks v ρ = ∅ then (ranks w ρ).card else min (reg v ρ) (ranks w ρ).card
  have hCk : C ≤ σ.k - 1 := by dsimp only [C, cupLimit]; omega
  have hPk : P ≤ σ.k - 1 := by dsimp only [P, capLimit]; omega
  have hτpos : ∀ x j v, τ.letterAt x = Letter.ext j v → 1 ≤ j := hpositive
  have hτchildren : τ.childPositions = σ.childPositions := rfl
  have hτlimits (p : ℕ) : τ.cupLimit p p = C ∧ τ.capLimit p p = P := by
    constructor
    · simp [τ, cupLimit, chainExt, joinExt, leftExt, rightExt, levelsOn, levels,
        Nat.min_eq_left hCk]
    · simp [τ, capLimit, chainExt, joinExt, leftExt, rightExt, levelsOn, levels,
        Nat.min_eq_left hPk]
  have hτlim (v : Side) (p : ℕ) : lim v τ p = cap v := by
    cases v
    · exact (hτlimits p).1
    · exact (hτlimits p).2
  have hτG (v : Side) : G v τ = cap v + 1 := by cases v <;> rfl
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
  have hNormalize (keep : List ℕ) (v : Side) (m : ℕ) :
      (σ.part keep v m).bound = (τ.part keep v m).bound := by
    let π := σ.part keep v m
    have hHist : π.a = σ.a ∧ π.u = σ.u ∧ π.k = σ.k ∧
        π.maxima.length = 1 + σ.maxima.length ∧
        (∀ j, 1 ≤ j → π.extPositions (j + 1) = σ.extPositions j) ∧
        (∀ j, 1 ≤ j → π.sideAt (j + 1) = σ.sideAt j) ∧
        (∀ j, 1 ≤ j → π.maximumAt (j + 1) = σ.maximumAt j) := by
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · change (m :: σ.maxima).length = 1 + σ.maxima.length
        simp only [List.length_cons]
        omega
      · intro j hj
        exact part_extPositions_succ σ keep v m hj
      · intro j hj
        exact part_sideAt_succ σ keep v m hj
      · intro j hj
        exact part_maximumAt_succ σ keep v m hj
    have hNew : ∀ j x, 1 ≤ j → j ≤ 1 → x ∈ π.extPositions j → x ∈ σ.childPositions := by
      intro j x hj hj1 hx
      have he : j = 1 := by omega
      subst j
      change x ∈ (σ.part keep v m).extPositions 1 at hx
      rw [part_extPositions_one hpositive keep v m] at hx
      exact (List.mem_filter.mp hx).1
    have hChild : ∀ x ∈ π.childPositions, x ∈ σ.childPositions := by
      intro x hx
      change x ∈ (σ.part keep v m).childPositions at hx
      rw [part_childPositions] at hx
      exact (List.mem_filter.mp hx).1
    have h := (ctx_single_run_descendant_bound_normalize σ b N hpos π 1 hHist hNew hChild
      (hPartPositive σ keep v m)).2
    exact h
  have hrunBound : ∀ (ρ : Context) (a n : ℕ), 0 < n →
      ρ.childPositions = List.range' a n →
      ρ.bound = baseOf (ρ.cupLimit a a) (ρ.capLimit a a) ρ.k := by
    intro ρ a n hn hps
    have hmem : ∀ p, p ∈ ρ.childPositions ↔ a ≤ p ∧ p < a + n := by
      intro p
      rw [hps, List.mem_range'_1]
    let starts := (List.range ρ.word.length).filter fun p =>
      ρ.letterAt p = Letter.child ∧ (p = 0 ∨ ρ.letterAt (p - 1) ≠ Letter.child)
    have hsubset : starts.toFinset ⊆ ({a} : Finset ℕ) := by
      intro p hp
      have hstart : p < ρ.word.length ∧ ρ.letterAt p = Letter.child ∧
          (p = 0 ∨ ρ.letterAt (p - 1) ≠ Letter.child) := by
        simpa [starts] using hp
      have hp' := (hmem p).mp
        (by simpa [childPositions] using And.intro hstart.1 hstart.2.1)
      simp only [Finset.mem_singleton]
      by_contra hpa
      have hprev : p - 1 ∈ ρ.childPositions := (hmem (p - 1)).mpr ⟨by omega, by omega⟩
      have hprev' : ρ.letterAt (p - 1) = Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hprev).2
      rcases hstart.2.2 with hz | hnot
      · omega
      · exact hnot hprev'
    have hruns : ρ.numRuns ≤ 1 := by
      calc
        ρ.numRuns = starts.toFinset.card :=
          (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
        _ ≤ ({a} : Finset ℕ).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    simp [bound, boundFuel, hruns, base_eq_baseOf, hps, List.head?_range', Nat.ne_of_gt hn]
  have hroot : σ.bound = baseOf C P σ.k := hrunBound σ b N hN hpos
  have hτMarks (v : Side) : marks v τ = ∅ := by simp [marks, τ, levelsOn, levels]
  have hRegOne (v : Side) : reg v τ ≤ 1 := by
    have hs : (active τ).image (fun p => ((marks v τ).filter (· < p)).card) ⊆ {0} := by
      intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      simp only [hτMarks, Finset.filter_empty, Finset.card_empty, Finset.mem_singleton]
    simpa only [Finset.card_singleton] using Finset.card_le_card hs
  have hRegBase (v : Side) (hv : cap v ≤ 1) : reg v τ ≤ baseOf C P σ.k := by
    by_cases hz : C = 0 ∨ P = 0
    · have he : active τ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hh : 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := (Finset.mem_filter.mp hp).2
        rw [(hτlimits p).1, (hτlimits p).2] at hh
        omega
      have hg : reg v τ = 0 := by simp [reg, he]
      rw [hg]
      exact Nat.zero_le _
    · have ho : C = 1 ∨ P = 1 := by cases v <;> dsimp only [cap] at hv <;> omega
      simpa only [baseOf, if_neg hz, if_pos ho] using hRegOne v
  have hPartUnit (v w : Side) (hv : cap v ≤ 1) (keep : List ℕ) (m : ℕ) :
      ∀ p ∈ (τ.part keep w m).childPositions, lim v (τ.part keep w m) p ≤ 1 := by
    intro p _
    have hp := hτlim v p
    have hl := ctx_part_limits_le τ keep w m p p
    cases v <;> dsimp only [lim, cap] at hp hv ⊢ <;> omega
  have hUnitBound (v w : Side) (hv : cap v ≤ 1) (keep : List ℕ) (m : ℕ) :
      (τ.part keep w m).bound ≤ reg v (τ.part keep w m) := by
    exact (ctx_unit_axis_active_region_potential (τ.part keep w m)
      (hPartPositive τ keep w m) v (hPartUnit v w hv keep m)).2.1
  have hUnitCut (v w : Side) (hv : cap v ≤ 1) (keep rest : List ℕ) (m n : ℕ)
      (hd : ∀ p ∈ τ.childPositions, p ∈ keep → p ∉ rest) :
      (τ.part keep v m).bound + (τ.part rest w n).bound ≤ baseOf C P σ.k := by
    have hu : ∀ p ∈ τ.childPositions, lim v τ p ≤ 1 := by
      intro p _
      rw [hτlim]
      exact hv
    have hc := ctx_unit_axis_region_potential_additive τ hτpos v hu keep rest w m n hd
    change reg v (τ.part keep v m) + reg v (τ.part rest w n) ≤ reg v τ at hc
    exact ((Nat.add_le_add (hUnitBound v v hv keep m) (hUnitBound v w hv rest n)).trans hc).trans
      (hRegBase v hv)
  have hTwoLeft (p k : ℕ) (hp : p ≤ k - 1) : baseOf 2 p k = p := by
    by_cases hz : p = 0
    · simp [baseOf, hz]
    by_cases ho : p = 1
    · simp [baseOf, ho]
    unfold baseOf
    rw [if_neg (by omega), if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hrow : p + 1 + (2 + 1) - 4 = p := by omega
    have hcol : p + 1 - 2 = p - 1 := by omega
    rw [hrow, hcol, Nat.choose_symm (show 1 ≤ p by omega)]
    simp
  have hTwoRight (c k : ℕ) (hc : c ≤ k - 1) : baseOf c 2 k = c := by
    by_cases hz : c = 0
    · simp [baseOf, hz]
    by_cases ho : c = 1
    · simp [baseOf, ho]
    unfold baseOf
    rw [if_neg (by omega), if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hrow : 2 + 1 + (c + 1) - 4 = c := by omega
    rw [hrow]
    simp
  have hBaseTwo (v w : Side) (hvw : v ≠ w) (hv : cap v = 2) : baseOf C P σ.k = cap w := by
    cases v <;> cases w
    · exact False.elim (hvw rfl)
    · change C = 2 at hv
      change baseOf C P σ.k = P
      rw [hv]
      exact hTwoLeft P σ.k hPk
    · change P = 2 at hv
      change baseOf C P σ.k = C
      rw [hv]
      exact hTwoRight C σ.k hCk
    · exact False.elim (hvw rfl)
  have hτBudget (w : Side) : budget w τ = cap w := by cases w <;> simp [budget, τ, cap]
  have hPotential (ρ : Context) (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (v w : Side) (hvw : v ≠ w) (hG : G v ρ ≤ 3) :
      ρ.bound ≤ V v w ρ ∧ V v w ρ ≤ budget w ρ ∧
      (∀ (keep rest : List ℕ) (m n : ℕ),
        (∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) →
        V v w (ρ.part keep v m) + V v w (ρ.part rest w n) ≤ V v w ρ) := by
    exact (ctx_small_global_axis_rank_region_potential ρ hPos v w hvw hG).2
  have hTwoCut (v w : Side) (hvw : v ≠ w) (hv : cap v = 2) (keep rest : List ℕ) (m n : ℕ)
      (hd : ∀ p ∈ τ.childPositions, p ∈ keep → p ∉ rest) :
      (τ.part keep v m).bound + (τ.part rest w n).bound ≤ baseOf C P σ.k := by
    have hG : G v τ ≤ 3 := by rw [hτG, hv]
    have hGpart (keep : List ℕ) (z : Side) (m : ℕ) : G v (τ.part keep z m) ≤ 3 := by
      have he : G v (τ.part keep z m) = G v τ := by cases v <;> rfl
      rw [he]
      exact hG
    have ha := (hPotential (τ.part keep v m) (hPartPositive τ keep v m) v w hvw (hGpart keep v m)).1
    have hb := (hPotential (τ.part rest w n) (hPartPositive τ rest w n) v w hvw (hGpart rest w n)).1
    have hp := hPotential τ hτpos v w hvw hG
    calc
      (τ.part keep v m).bound + (τ.part rest w n).bound ≤
          V v w (τ.part keep v m) + V v w (τ.part rest w n) := Nat.add_le_add ha hb
      _ ≤ V v w τ := hp.2.2 keep rest m n hd
      _ ≤ budget w τ := hp.2.1
      _ = cap w := hτBudget w
      _ = baseOf C P σ.k := (hBaseTwo v w hvw hv).symm
  have hSmallCut (v w : Side) (hvw : v ≠ w) (hv : cap v ≤ 2) (keep rest : List ℕ) (m n : ℕ)
      (hd : ∀ p ∈ τ.childPositions, p ∈ keep → p ∉ rest) :
      (τ.part keep v m).bound + (τ.part rest w n).bound ≤ baseOf C P σ.k := by
    by_cases hu : cap v ≤ 1
    · exact hUnitCut v w hu keep rest m n hd
    · exact hTwoCut v w hvw (by omega) keep rest m n hd
  have hchoice : cap s ≤ 2 ∨ cap t ≤ 2 := by
    change min C P ≤ 2 at hsmall
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · dsimp only [cap]
      omega
    · dsimp only [cap]
      omega
    · exact False.elim (hne rfl)
  rw [hNormalize keep s m, hNormalize rest t n, hroot]
  have hd : ∀ p ∈ τ.childPositions, p ∈ keep → p ∉ rest := hdis
  rcases hchoice with hs | ht
  · exact hSmallCut s t hne hs keep rest m n hd
  · have hr : ∀ p ∈ τ.childPositions, p ∈ rest → p ∉ keep := by
      intro p hp hr hk
      exact hd p hp hk hr
    simpa only [Nat.add_comm] using hSmallCut t s (Ne.symm hne) ht rest keep n m hr

end ErdosSzekeres
