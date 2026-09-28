import ESBlueprint.B.CtxBoundAttainedByEndCut
import ESBlueprint.B.CtxSandwich112LeafCases02
import ESBlueprint.B.CtxSandwich112LeafCases03
import ESBlueprint.B.CtxSandwich112LeafCases12
import ESBlueprint.B.CtxSandwich112LeafCases13
import ESBlueprint.B.CtxSandwich112LeafCasesThree

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000

/-- Sandwich additivity for four consecutive child positions split into outer blocks of lengths one and two and a singleton middle block. Uniform in the well-formed external context, parameters, and admissible coupling, with both orientations. Together with checked middle-block contraction this gives the (1,m,2) sandwich family.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_sandwich_112 (σ : Ctx.Context) (hwf : σ.WellFormed) (b : ℕ)
  (hpos : σ.childPositions = List.range' b 4)
  (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) :
  (σ.part [b, b + 2, b + 3] Ctx.Side.lower d).bound +
      (σ.part [b + 1] Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧
  (σ.part [b, b + 2, b + 3] Ctx.Side.upper (σ.k - 1 - d)).bound +
      (σ.part [b + 1] Ctx.Side.lower d).bound ≤ σ.bound := by
  obtain ⟨hquad_0200, hquad_0201, hquad_0210, hquad_0211⟩ :=
    ctx_sandwich_112_leaf_cases_02 σ hwf b hpos
  obtain ⟨hquad_0300, hquad_0301, hquad_0310, hquad_0311⟩ :=
    ctx_sandwich_112_leaf_cases_03 σ hwf b hpos
  obtain ⟨hquad_1200, hquad_1201, hquad_1210, hquad_1211⟩ :=
    ctx_sandwich_112_leaf_cases_12 σ hwf b hpos
  obtain ⟨hquad_1300, hquad_1301, hquad_1310, hquad_1311⟩ :=
    ctx_sandwich_112_leaf_cases_13 σ hwf b hpos
  obtain ⟨hquad_0000, hquad_0010, hquad_1000, hquad_1010⟩ :=
    ctx_sandwich_112_leaf_cases_three σ hwf b hpos
  have two_child_bound_of_singleton_cuts :
      ∀ (τ : Ctx.Context) (p q B : ℕ),
        τ.childPositions = [p, q] →
        p ≠ q →
        2 ≤ τ.numRuns →
        (∀ d, 1 ≤ d → d ≤ τ.k - 2 →
          (τ.part [p] Ctx.Side.lower d).bound +
                (τ.part [q] Ctx.Side.upper (τ.k - 1 - d)).bound ≤ B ∧
            (τ.part [p] Ctx.Side.upper (τ.k - 1 - d)).bound +
                (τ.part [q] Ctx.Side.lower d).bound ≤ B) →
        τ.bound ≤ B := by
    intro τ p q B hpos hpq hruns hcut
    clear * - τ p q B hpos hpq hruns hcut
    have hqp : q ≠ p := Ne.symm hpq
    have hblocks : τ.blocks = [[p], [q]] := by
      simp [Ctx.Context.blocks, hpos, List.range_succ]
    have hrestP : τ.childPositions.filter (fun x ↦ x ∉ [p]) = [q] := by
      rw [hpos]
      simp [hpq, hqp]
    have hrestQ : τ.childPositions.filter (fun x ↦ x ∉ [q]) = [p] := by
      rw [hpos]
      simp [hpq, hqp]
    have hpartP : ∀ s m, (τ.part [p] s m).childPositions = [p] := by
      intro s m
      rw [Ctx.Context.part_childPositions, hpos]
      simp [hpq, hqp]
    have hpartQ : ∀ s m, (τ.part [q] s m).childPositions = [q] := by
      intro s m
      rw [Ctx.Context.part_childPositions, hpos]
      simp [hpq, hqp]
    have hfuelP : ∀ s m,
        Ctx.Context.boundFuel 2 (τ.part [p] s m) = (τ.part [p] s m).bound := by
      intro s m
      unfold Ctx.Context.bound
      rw [hpartP]
      rfl
    have hfuelQ : ∀ s m,
        Ctx.Context.boundFuel 2 (τ.part [q] s m) = (τ.part [q] s m).bound := by
      intro s m
      unfold Ctx.Context.bound
      rw [hpartQ]
      rfl
    unfold Ctx.Context.bound
    rw [hpos]
    change Ctx.Context.boundFuel 3 τ ≤ B
    rw [Ctx.Context.boundFuel.eq_2, if_neg (by omega)]
    dsimp only
    apply Ctx.getD_max?_le
    intro x hx
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    obtain ⟨block, hblock, d', hd', hx⟩ := hx
    rw [hblocks] at hblock
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hblock
    have hc := hcut (d' + 1) (by omega) (by omega)
    rcases hblock with rfl | rfl
    · rw [hrestP] at hx
      rcases hx with rfl | rfl
      · rw [hfuelP Side.lower (d' + 1),
          hfuelQ Side.upper (τ.k - 1 - (d' + 1))]
        exact hc.1
      · rw [hfuelP Side.upper (τ.k - 1 - (d' + 1)),
          hfuelQ Side.lower (d' + 1)]
        exact hc.2
    · rw [hrestQ] at hx
      rcases hx with rfl | rfl
      · rw [hfuelQ Side.lower (d' + 1),
          hfuelP Side.upper (τ.k - 1 - (d' + 1))]
        simpa only [Nat.add_comm] using hc.2
      · rw [hfuelQ Side.upper (τ.k - 1 - (d' + 1)),
          hfuelP Side.lower (d' + 1)]
        simpa only [Nat.add_comm] using hc.1
  have hthreeCuts (τ : Context) (p q r B : ℕ) (hpq : p < q) (hqr : q < r)
      (hps : τ.childPositions = [p, q, r]) (hruns : 2 ≤ τ.numRuns)
      (hcuts : ∀ x ∈ [p, q, r], ∀ d, 1 ≤ d → d ≤ τ.k - 2 →
        (τ.part [x] Side.lower d).bound +
            (τ.part (τ.childPositions.filter (· ∉ [x])) Side.upper (τ.k - 1 - d)).bound ≤ B ∧
        (τ.part [x] Side.upper (τ.k - 1 - d)).bound +
            (τ.part (τ.childPositions.filter (· ∉ [x])) Side.lower d).bound ≤ B) :
      τ.bound ≤ B := by
    clear * - τ p q r B hpq hqr hps hruns hcuts
    have hne : p ≠ q ∧ p ≠ r ∧ q ≠ r := by omega
    have hblocks : τ.blocks = [[p], [p, q], [q], [q, r], [r]] := by
      simp [blocks, hps, List.range_succ]
    have hfuel (K : List ℕ) (hK : K.length ≤ 2) (s : Side) (m : ℕ) :
        boundFuel 3 (τ.part K s m) = (τ.part K s m).bound := by
      apply boundFuel_eq_bound
      have hlen := length_filter_mem_le (block := K) (show τ.childPositions.Nodup by simp [hps, hne.1, hne.2.1, hne.2.2])
      rw [part_childPositions]
      omega
    have hcomps : τ.childPositions.filter (· ∉ [p]) = [q, r] ∧
        τ.childPositions.filter (· ∉ [q]) = [p, r] ∧
        τ.childPositions.filter (· ∉ [r]) = [p, q] ∧
        τ.childPositions.filter (· ∉ [p, q]) = [r] ∧
        τ.childPositions.filter (· ∉ [q, r]) = [p] := by
      simp [hps, hne.1, hne.2.1, hne.2.2, Ne.symm hne.1, Ne.symm hne.2.1, Ne.symm hne.2.2]
    unfold bound
    rw [hps]
    change boundFuel 4 τ ≤ B
    rw [boundFuel.eq_2, if_neg (by omega)]
    dsimp only
    apply getD_max?_le
    intro x hx
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨K, hK, d, hd, hx⟩ := hx
    have hP := hcuts p (by simp) (d + 1) (by omega) (by omega)
    have hQ := hcuts q (by simp) (d + 1) (by omega) (by omega)
    have hR := hcuts r (by simp) (d + 1) (by omega) (by omega)
    rw [hcomps.1] at hP
    rw [hcomps.2.1] at hQ
    rw [hcomps.2.2.1] at hR
    rw [hblocks] at hK
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
    rcases hK with rfl | rfl | rfl | rfl | rfl
    · rw [hcomps.1] at hx
      rcases hx with rfl | rfl
      · rw [hfuel [p] (by simp), hfuel [q, r] (by simp)]
        exact hP.1
      · rw [hfuel [p] (by simp), hfuel [q, r] (by simp)]
        exact hP.2
    · rw [hcomps.2.2.2.1] at hx
      rcases hx with rfl | rfl
      · rw [hfuel [p, q] (by simp), hfuel [r] (by simp)]
        simpa only [Nat.add_comm] using hR.2
      · rw [hfuel [p, q] (by simp), hfuel [r] (by simp)]
        simpa only [Nat.add_comm] using hR.1
    · rw [hcomps.2.1] at hx
      rcases hx with rfl | rfl
      · rw [hfuel [q] (by simp), hfuel [p, r] (by simp)]
        exact hQ.1
      · rw [hfuel [q] (by simp), hfuel [p, r] (by simp)]
        exact hQ.2
    · rw [hcomps.2.2.2.2] at hx
      rcases hx with rfl | rfl
      · rw [hfuel [q, r] (by simp), hfuel [p] (by simp)]
        simpa only [Nat.add_comm] using hP.2
      · rw [hfuel [q, r] (by simp), hfuel [p] (by simp)]
        simpa only [Nat.add_comm] using hP.1
    · rw [hcomps.2.2.1] at hx
      rcases hx with rfl | rfl
      · rw [hfuel [r] (by simp), hfuel [p, q] (by simp)]
        exact hR.1
      · rw [hfuel [r] (by simp), hfuel [p, q] (by simp)]
        exact hR.2
  have htwoStarts (τ : Context) (p q : ℕ) (hp : p ∈ τ.childPositions)
      (hq : q ∈ τ.childPositions) (hpq : p ≠ q)
      (hpp : p = 0 ∨ p - 1 ∉ τ.childPositions)
      (hqp : q = 0 ∨ q - 1 ∉ τ.childPositions) : 2 ≤ τ.numRuns := by
    clear * - τ p q hp hq hpq hpp hqp
    let starts := (List.range τ.word.length).filter fun x =>
      τ.letterAt x = Letter.child ∧ (x = 0 ∨ τ.letterAt (x - 1) ≠ Letter.child)
    have hstart (x : ℕ) (hx : x ∈ τ.childPositions)
        (hprev : x = 0 ∨ x - 1 ∉ τ.childPositions) : x ∈ starts := by
      have hxl : x < τ.word.length := List.mem_range.mp (List.mem_filter.mp hx).1
      have hxc : τ.letterAt x = Letter.child := of_decide_eq_true (List.mem_filter.mp hx).2
      have hprev' : x = 0 ∨ τ.letterAt (x - 1) ≠ Letter.child := by
        rcases hprev with hz | hn
        · exact Or.inl hz
        · by_cases hz : x = 0
          · exact Or.inl hz
          · right
            intro hc
            apply hn
            exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simpa using hc⟩
      simpa only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq] using
        And.intro hxl (And.intro hxc hprev')
    have hsub : ({p, q} : Finset ℕ) ⊆ starts.toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · subst x
        exact List.mem_toFinset.mpr (hstart p hp hpp)
      · subst x
        exact List.mem_toFinset.mpr (hstart q hq hqp)
    have h := Finset.card_le_card hsub
    rw [Finset.card_pair hpq, List.toFinset_card_of_nodup (List.nodup_range.filter _)] at h
    exact h
  have hremove2 (A B X Y T : ℕ) (h : A + B + X + Y ≤ T) : X + Y ≤ T - A - B := by
    clear * - A B X Y T h
    omega
  have hremove1 (A X Y T : ℕ) (h : A + X + Y ≤ T) : X + Y ≤ T - A := by
    clear * - A X Y T h
    omega
  have hfinish2 (A B R X Y T : ℕ) (h : A + B + X + Y ≤ T) (hr : R ≤ T - A - B) : A + B + R ≤ T := by
    clear * - A B R X Y T h hr
    omega
  have hfinish1 (A R X Y T : ℕ) (h : A + X + Y ≤ T) (hr : R ≤ T - A) : A + R ≤ T := by
    clear * - A R X Y T h hr
    omega
  have hpair_020 (od e : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) :
      let O := σ.part [b, b + 2, b + 3] Side.lower (od)
      let M := σ.part [b + 1] Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Side.lower (e)
      let R := O.part [b, b + 3] Side.upper (σ.k - 1 - e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    clear * - σ b hpos od e hod hodk he hek hquad_0200 hquad_0201 htwoStarts two_child_bound_of_singleton_cuts hremove2 hfinish2
    dsimp only
    let O := σ.part [b, b + 2, b + 3] Side.lower (od)
    let M := σ.part [b + 1] Side.upper (σ.k - 1 - od)
    let Q := O.part [(b + 2)] Side.lower (e)
    let R := O.part [b, b + 3] Side.upper (σ.k - 1 - e)
    have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by simpa [List.range'_succ, Nat.add_assoc] using hpos
    have hOc : O.childPositions = [b, b + 2, b + 3] := by
      change (σ.part _ _ _).childPositions = _
      rw [part_childPositions, hCP4]
      simp [Nat.add_assoc]
    have hRc : R.childPositions = [b, b + 3] := by
      change (O.part _ _ _).childPositions = _
      rw [part_childPositions, hOc]
      simp [Nat.add_assoc]
    have hRruns : 2 ≤ R.numRuns := htwoStarts R b (b + 3)
      (by rw [hRc]; simp) (by rw [hRc]; simp) (by omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have hRbound : R.bound ≤ σ.bound - M.bound - Q.bound := by
      apply two_child_bound_of_singleton_cuts R b (b + 3) _ hRc (by omega) hRruns
      intro f hf hfk
      change f ≤ σ.k - 2 at hfk
      have h0 := hquad_0200 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.lower (f)).bound +
        (R.part [b + 3] Side.upper (σ.k - 1 - f)).bound ≤ σ.bound at h0
      have h1 := hquad_0201 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.upper (σ.k - 1 - f)).bound +
        (R.part [b + 3] Side.lower (f)).bound ≤ σ.bound at h1
      exact ⟨hremove2 _ _ _ _ _ h0, hremove2 _ _ _ _ _ h1⟩
    have hknown := hquad_0200 od e 1 hod hodk he hek (by decide) (by omega)
    change M.bound + Q.bound + (R.part [b] Side.lower 1).bound +
      (R.part [b + 3] Side.upper (σ.k - 1 - 1)).bound ≤ σ.bound at hknown
    change M.bound + Q.bound + R.bound ≤ _
    exact hfinish2 _ _ _ _ _ _ hknown hRbound
  have hpair_021 (od e : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) :
      let O := σ.part [b, b + 2, b + 3] Side.lower (od)
      let M := σ.part [b + 1] Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Side.upper (σ.k - 1 - e)
      let R := O.part [b, b + 3] Side.lower (e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    clear * - σ b hpos od e hod hodk he hek hquad_0210 hquad_0211 htwoStarts two_child_bound_of_singleton_cuts hremove2 hfinish2
    dsimp only
    let O := σ.part [b, b + 2, b + 3] Side.lower (od)
    let M := σ.part [b + 1] Side.upper (σ.k - 1 - od)
    let Q := O.part [(b + 2)] Side.upper (σ.k - 1 - e)
    let R := O.part [b, b + 3] Side.lower (e)
    have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by simpa [List.range'_succ, Nat.add_assoc] using hpos
    have hOc : O.childPositions = [b, b + 2, b + 3] := by
      change (σ.part _ _ _).childPositions = _
      rw [part_childPositions, hCP4]
      simp [Nat.add_assoc]
    have hRc : R.childPositions = [b, b + 3] := by
      change (O.part _ _ _).childPositions = _
      rw [part_childPositions, hOc]
      simp [Nat.add_assoc]
    have hRruns : 2 ≤ R.numRuns := htwoStarts R b (b + 3)
      (by rw [hRc]; simp) (by rw [hRc]; simp) (by omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have hRbound : R.bound ≤ σ.bound - M.bound - Q.bound := by
      apply two_child_bound_of_singleton_cuts R b (b + 3) _ hRc (by omega) hRruns
      intro f hf hfk
      change f ≤ σ.k - 2 at hfk
      have h0 := hquad_0210 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.lower (f)).bound +
        (R.part [b + 3] Side.upper (σ.k - 1 - f)).bound ≤ σ.bound at h0
      have h1 := hquad_0211 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.upper (σ.k - 1 - f)).bound +
        (R.part [b + 3] Side.lower (f)).bound ≤ σ.bound at h1
      exact ⟨hremove2 _ _ _ _ _ h0, hremove2 _ _ _ _ _ h1⟩
    have hknown := hquad_0210 od e 1 hod hodk he hek (by decide) (by omega)
    change M.bound + Q.bound + (R.part [b] Side.lower 1).bound +
      (R.part [b + 3] Side.upper (σ.k - 1 - 1)).bound ≤ σ.bound at hknown
    change M.bound + Q.bound + R.bound ≤ _
    exact hfinish2 _ _ _ _ _ _ hknown hRbound
  have hpair_030 (od e : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) :
      let O := σ.part [b, b + 2, b + 3] Side.lower (od)
      let M := σ.part [b + 1] Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 3)] Side.lower (e)
      let R := O.part [b, b + 2] Side.upper (σ.k - 1 - e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    clear * - σ b hpos od e hod hodk he hek hquad_0300 hquad_0301 htwoStarts two_child_bound_of_singleton_cuts hremove2 hfinish2
    dsimp only
    let O := σ.part [b, b + 2, b + 3] Side.lower (od)
    let M := σ.part [b + 1] Side.upper (σ.k - 1 - od)
    let Q := O.part [(b + 3)] Side.lower (e)
    let R := O.part [b, b + 2] Side.upper (σ.k - 1 - e)
    have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by simpa [List.range'_succ, Nat.add_assoc] using hpos
    have hOc : O.childPositions = [b, b + 2, b + 3] := by
      change (σ.part _ _ _).childPositions = _
      rw [part_childPositions, hCP4]
      simp [Nat.add_assoc]
    have hRc : R.childPositions = [b, b + 2] := by
      change (O.part _ _ _).childPositions = _
      rw [part_childPositions, hOc]
      simp [Nat.add_assoc]
    have hRruns : 2 ≤ R.numRuns := htwoStarts R b (b + 2)
      (by rw [hRc]; simp) (by rw [hRc]; simp) (by omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have hRbound : R.bound ≤ σ.bound - M.bound - Q.bound := by
      apply two_child_bound_of_singleton_cuts R b (b + 2) _ hRc (by omega) hRruns
      intro f hf hfk
      change f ≤ σ.k - 2 at hfk
      have h0 := hquad_0300 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.lower (f)).bound +
        (R.part [b + 2] Side.upper (σ.k - 1 - f)).bound ≤ σ.bound at h0
      have h1 := hquad_0301 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.upper (σ.k - 1 - f)).bound +
        (R.part [b + 2] Side.lower (f)).bound ≤ σ.bound at h1
      exact ⟨hremove2 _ _ _ _ _ h0, hremove2 _ _ _ _ _ h1⟩
    have hknown := hquad_0300 od e 1 hod hodk he hek (by decide) (by omega)
    change M.bound + Q.bound + (R.part [b] Side.lower 1).bound +
      (R.part [b + 2] Side.upper (σ.k - 1 - 1)).bound ≤ σ.bound at hknown
    change M.bound + Q.bound + R.bound ≤ _
    exact hfinish2 _ _ _ _ _ _ hknown hRbound
  have hpair_031 (od e : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) :
      let O := σ.part [b, b + 2, b + 3] Side.lower (od)
      let M := σ.part [b + 1] Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 3)] Side.upper (σ.k - 1 - e)
      let R := O.part [b, b + 2] Side.lower (e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    clear * - σ b hpos od e hod hodk he hek hquad_0310 hquad_0311 htwoStarts two_child_bound_of_singleton_cuts hremove2 hfinish2
    dsimp only
    let O := σ.part [b, b + 2, b + 3] Side.lower (od)
    let M := σ.part [b + 1] Side.upper (σ.k - 1 - od)
    let Q := O.part [(b + 3)] Side.upper (σ.k - 1 - e)
    let R := O.part [b, b + 2] Side.lower (e)
    have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by simpa [List.range'_succ, Nat.add_assoc] using hpos
    have hOc : O.childPositions = [b, b + 2, b + 3] := by
      change (σ.part _ _ _).childPositions = _
      rw [part_childPositions, hCP4]
      simp [Nat.add_assoc]
    have hRc : R.childPositions = [b, b + 2] := by
      change (O.part _ _ _).childPositions = _
      rw [part_childPositions, hOc]
      simp [Nat.add_assoc]
    have hRruns : 2 ≤ R.numRuns := htwoStarts R b (b + 2)
      (by rw [hRc]; simp) (by rw [hRc]; simp) (by omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have hRbound : R.bound ≤ σ.bound - M.bound - Q.bound := by
      apply two_child_bound_of_singleton_cuts R b (b + 2) _ hRc (by omega) hRruns
      intro f hf hfk
      change f ≤ σ.k - 2 at hfk
      have h0 := hquad_0310 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.lower (f)).bound +
        (R.part [b + 2] Side.upper (σ.k - 1 - f)).bound ≤ σ.bound at h0
      have h1 := hquad_0311 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.upper (σ.k - 1 - f)).bound +
        (R.part [b + 2] Side.lower (f)).bound ≤ σ.bound at h1
      exact ⟨hremove2 _ _ _ _ _ h0, hremove2 _ _ _ _ _ h1⟩
    have hknown := hquad_0310 od e 1 hod hodk he hek (by decide) (by omega)
    change M.bound + Q.bound + (R.part [b] Side.lower 1).bound +
      (R.part [b + 2] Side.upper (σ.k - 1 - 1)).bound ≤ σ.bound at hknown
    change M.bound + Q.bound + R.bound ≤ _
    exact hfinish2 _ _ _ _ _ _ hknown hRbound
  have hpair_120 (od e : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) :
      let O := σ.part [b, b + 2, b + 3] Side.upper (od)
      let M := σ.part [b + 1] Side.lower (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Side.lower (e)
      let R := O.part [b, b + 3] Side.upper (σ.k - 1 - e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    clear * - σ b hpos od e hod hodk he hek hquad_1200 hquad_1201 htwoStarts two_child_bound_of_singleton_cuts hremove2 hfinish2
    dsimp only
    let O := σ.part [b, b + 2, b + 3] Side.upper (od)
    let M := σ.part [b + 1] Side.lower (σ.k - 1 - od)
    let Q := O.part [(b + 2)] Side.lower (e)
    let R := O.part [b, b + 3] Side.upper (σ.k - 1 - e)
    have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by simpa [List.range'_succ, Nat.add_assoc] using hpos
    have hOc : O.childPositions = [b, b + 2, b + 3] := by
      change (σ.part _ _ _).childPositions = _
      rw [part_childPositions, hCP4]
      simp [Nat.add_assoc]
    have hRc : R.childPositions = [b, b + 3] := by
      change (O.part _ _ _).childPositions = _
      rw [part_childPositions, hOc]
      simp [Nat.add_assoc]
    have hRruns : 2 ≤ R.numRuns := htwoStarts R b (b + 3)
      (by rw [hRc]; simp) (by rw [hRc]; simp) (by omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have hRbound : R.bound ≤ σ.bound - M.bound - Q.bound := by
      apply two_child_bound_of_singleton_cuts R b (b + 3) _ hRc (by omega) hRruns
      intro f hf hfk
      change f ≤ σ.k - 2 at hfk
      have h0 := hquad_1200 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.lower (f)).bound +
        (R.part [b + 3] Side.upper (σ.k - 1 - f)).bound ≤ σ.bound at h0
      have h1 := hquad_1201 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.upper (σ.k - 1 - f)).bound +
        (R.part [b + 3] Side.lower (f)).bound ≤ σ.bound at h1
      exact ⟨hremove2 _ _ _ _ _ h0, hremove2 _ _ _ _ _ h1⟩
    have hknown := hquad_1200 od e 1 hod hodk he hek (by decide) (by omega)
    change M.bound + Q.bound + (R.part [b] Side.lower 1).bound +
      (R.part [b + 3] Side.upper (σ.k - 1 - 1)).bound ≤ σ.bound at hknown
    change M.bound + Q.bound + R.bound ≤ _
    exact hfinish2 _ _ _ _ _ _ hknown hRbound
  have hpair_121 (od e : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) :
      let O := σ.part [b, b + 2, b + 3] Side.upper (od)
      let M := σ.part [b + 1] Side.lower (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Side.upper (σ.k - 1 - e)
      let R := O.part [b, b + 3] Side.lower (e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    clear * - σ b hpos od e hod hodk he hek hquad_1210 hquad_1211 htwoStarts two_child_bound_of_singleton_cuts hremove2 hfinish2
    dsimp only
    let O := σ.part [b, b + 2, b + 3] Side.upper (od)
    let M := σ.part [b + 1] Side.lower (σ.k - 1 - od)
    let Q := O.part [(b + 2)] Side.upper (σ.k - 1 - e)
    let R := O.part [b, b + 3] Side.lower (e)
    have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by simpa [List.range'_succ, Nat.add_assoc] using hpos
    have hOc : O.childPositions = [b, b + 2, b + 3] := by
      change (σ.part _ _ _).childPositions = _
      rw [part_childPositions, hCP4]
      simp [Nat.add_assoc]
    have hRc : R.childPositions = [b, b + 3] := by
      change (O.part _ _ _).childPositions = _
      rw [part_childPositions, hOc]
      simp [Nat.add_assoc]
    have hRruns : 2 ≤ R.numRuns := htwoStarts R b (b + 3)
      (by rw [hRc]; simp) (by rw [hRc]; simp) (by omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have hRbound : R.bound ≤ σ.bound - M.bound - Q.bound := by
      apply two_child_bound_of_singleton_cuts R b (b + 3) _ hRc (by omega) hRruns
      intro f hf hfk
      change f ≤ σ.k - 2 at hfk
      have h0 := hquad_1210 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.lower (f)).bound +
        (R.part [b + 3] Side.upper (σ.k - 1 - f)).bound ≤ σ.bound at h0
      have h1 := hquad_1211 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.upper (σ.k - 1 - f)).bound +
        (R.part [b + 3] Side.lower (f)).bound ≤ σ.bound at h1
      exact ⟨hremove2 _ _ _ _ _ h0, hremove2 _ _ _ _ _ h1⟩
    have hknown := hquad_1210 od e 1 hod hodk he hek (by decide) (by omega)
    change M.bound + Q.bound + (R.part [b] Side.lower 1).bound +
      (R.part [b + 3] Side.upper (σ.k - 1 - 1)).bound ≤ σ.bound at hknown
    change M.bound + Q.bound + R.bound ≤ _
    exact hfinish2 _ _ _ _ _ _ hknown hRbound
  have hpair_130 (od e : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) :
      let O := σ.part [b, b + 2, b + 3] Side.upper (od)
      let M := σ.part [b + 1] Side.lower (σ.k - 1 - od)
      let Q := O.part [(b + 3)] Side.lower (e)
      let R := O.part [b, b + 2] Side.upper (σ.k - 1 - e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    clear * - σ b hpos od e hod hodk he hek hquad_1300 hquad_1301 htwoStarts two_child_bound_of_singleton_cuts hremove2 hfinish2
    dsimp only
    let O := σ.part [b, b + 2, b + 3] Side.upper (od)
    let M := σ.part [b + 1] Side.lower (σ.k - 1 - od)
    let Q := O.part [(b + 3)] Side.lower (e)
    let R := O.part [b, b + 2] Side.upper (σ.k - 1 - e)
    have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by simpa [List.range'_succ, Nat.add_assoc] using hpos
    have hOc : O.childPositions = [b, b + 2, b + 3] := by
      change (σ.part _ _ _).childPositions = _
      rw [part_childPositions, hCP4]
      simp [Nat.add_assoc]
    have hRc : R.childPositions = [b, b + 2] := by
      change (O.part _ _ _).childPositions = _
      rw [part_childPositions, hOc]
      simp [Nat.add_assoc]
    have hRruns : 2 ≤ R.numRuns := htwoStarts R b (b + 2)
      (by rw [hRc]; simp) (by rw [hRc]; simp) (by omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have hRbound : R.bound ≤ σ.bound - M.bound - Q.bound := by
      apply two_child_bound_of_singleton_cuts R b (b + 2) _ hRc (by omega) hRruns
      intro f hf hfk
      change f ≤ σ.k - 2 at hfk
      have h0 := hquad_1300 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.lower (f)).bound +
        (R.part [b + 2] Side.upper (σ.k - 1 - f)).bound ≤ σ.bound at h0
      have h1 := hquad_1301 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.upper (σ.k - 1 - f)).bound +
        (R.part [b + 2] Side.lower (f)).bound ≤ σ.bound at h1
      exact ⟨hremove2 _ _ _ _ _ h0, hremove2 _ _ _ _ _ h1⟩
    have hknown := hquad_1300 od e 1 hod hodk he hek (by decide) (by omega)
    change M.bound + Q.bound + (R.part [b] Side.lower 1).bound +
      (R.part [b + 2] Side.upper (σ.k - 1 - 1)).bound ≤ σ.bound at hknown
    change M.bound + Q.bound + R.bound ≤ _
    exact hfinish2 _ _ _ _ _ _ hknown hRbound
  have hpair_131 (od e : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) :
      let O := σ.part [b, b + 2, b + 3] Side.upper (od)
      let M := σ.part [b + 1] Side.lower (σ.k - 1 - od)
      let Q := O.part [(b + 3)] Side.upper (σ.k - 1 - e)
      let R := O.part [b, b + 2] Side.lower (e)
      M.bound + Q.bound + R.bound ≤ σ.bound := by
    clear * - σ b hpos od e hod hodk he hek hquad_1310 hquad_1311 htwoStarts two_child_bound_of_singleton_cuts hremove2 hfinish2
    dsimp only
    let O := σ.part [b, b + 2, b + 3] Side.upper (od)
    let M := σ.part [b + 1] Side.lower (σ.k - 1 - od)
    let Q := O.part [(b + 3)] Side.upper (σ.k - 1 - e)
    let R := O.part [b, b + 2] Side.lower (e)
    have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by simpa [List.range'_succ, Nat.add_assoc] using hpos
    have hOc : O.childPositions = [b, b + 2, b + 3] := by
      change (σ.part _ _ _).childPositions = _
      rw [part_childPositions, hCP4]
      simp [Nat.add_assoc]
    have hRc : R.childPositions = [b, b + 2] := by
      change (O.part _ _ _).childPositions = _
      rw [part_childPositions, hOc]
      simp [Nat.add_assoc]
    have hRruns : 2 ≤ R.numRuns := htwoStarts R b (b + 2)
      (by rw [hRc]; simp) (by rw [hRc]; simp) (by omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by rw [hRc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have hRbound : R.bound ≤ σ.bound - M.bound - Q.bound := by
      apply two_child_bound_of_singleton_cuts R b (b + 2) _ hRc (by omega) hRruns
      intro f hf hfk
      change f ≤ σ.k - 2 at hfk
      have h0 := hquad_1310 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.lower (f)).bound +
        (R.part [b + 2] Side.upper (σ.k - 1 - f)).bound ≤ σ.bound at h0
      have h1 := hquad_1311 od e f hod hodk he hek hf hfk
      change M.bound + Q.bound + (R.part [b] Side.upper (σ.k - 1 - f)).bound +
        (R.part [b + 2] Side.lower (f)).bound ≤ σ.bound at h1
      exact ⟨hremove2 _ _ _ _ _ h0, hremove2 _ _ _ _ _ h1⟩
    have hknown := hquad_1310 od e 1 hod hodk he hek (by decide) (by omega)
    change M.bound + Q.bound + (R.part [b] Side.lower 1).bound +
      (R.part [b + 2] Side.upper (σ.k - 1 - 1)).bound ≤ σ.bound at hknown
    change M.bound + Q.bound + R.bound ≤ _
    exact hfinish2 _ _ _ _ _ _ hknown hRbound
  have hfinal0 (od : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2) :
      (σ.part [b + 1] Side.upper (σ.k - 1 - od)).bound +
        (σ.part [b, b + 2, b + 3] Side.lower od).bound ≤ σ.bound := by
    clear * - σ b hpos od hod hodk htwoStarts hthreeCuts hremove1 hfinish1 hquad_0000 hquad_0010 hpair_020 hpair_021 hpair_030 hpair_031
    let O := σ.part [b, b + 2, b + 3] Side.lower od
    let M := σ.part [b + 1] Side.upper (σ.k - 1 - od)
    have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by simpa [List.range'_succ, Nat.add_assoc] using hpos
    have hOc : O.childPositions = [b, b + 2, b + 3] := by
      change (σ.part _ _ _).childPositions = _
      rw [part_childPositions, hCP4]
      simp [Nat.add_assoc]
    have hOruns : 2 ≤ O.numRuns := htwoStarts O b (b + 2)
      (by rw [hOc]; simp) (by rw [hOc]; simp) (by omega)
      (by rw [hOc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by rw [hOc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have hcuts (x : ℕ) (hx : x ∈ [b, b + 2, b + 3]) (e : ℕ)
        (he : 1 ≤ e) (hek : e ≤ O.k - 2) :
        (O.part [x] Side.lower e).bound + (O.part (O.childPositions.filter (· ∉ [x])) Side.upper (O.k - 1 - e)).bound ≤ σ.bound - M.bound ∧
        (O.part [x] Side.upper (O.k - 1 - e)).bound + (O.part (O.childPositions.filter (· ∉ [x])) Side.lower e).bound ≤ σ.bound - M.bound := by
      change e ≤ σ.k - 2 at hek
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx
      · subst x
        have hrest : O.childPositions.filter (· ∉ [b]) = [b + 2, b + 3] := by rw [hOc]; simp [Nat.add_assoc]
        rw [hrest]
        have h0 := hquad_0000 od e 1 hod hodk he hek (by decide) (by omega)
        change M.bound + (O.part [b] Side.lower e).bound +
          (O.part [b + 2, b + 3] Side.upper (σ.k - 1 - e)).bound ≤ σ.bound at h0
        have h1 := hquad_0010 od e 1 hod hodk he hek (by decide) (by omega)
        change M.bound + (O.part [b] Side.upper (σ.k - 1 - e)).bound +
          (O.part [b + 2, b + 3] Side.lower e).bound ≤ σ.bound at h1
        exact ⟨hremove1 _ _ _ _ h0, hremove1 _ _ _ _ h1⟩
      · subst x
        have hrest : O.childPositions.filter (· ∉ [(b + 2)]) = [b, b + 3] := by rw [hOc]; simp [Nat.add_assoc]
        rw [hrest]
        have h0 := hpair_020 od e hod hodk he hek
        change M.bound + (O.part [(b + 2)] Side.lower e).bound +
          (O.part [b, b + 3] Side.upper (σ.k - 1 - e)).bound ≤ σ.bound at h0
        have h1 := hpair_021 od e hod hodk he hek
        change M.bound + (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).bound +
          (O.part [b, b + 3] Side.lower e).bound ≤ σ.bound at h1
        exact ⟨hremove1 _ _ _ _ h0, hremove1 _ _ _ _ h1⟩
      · subst x
        have hrest : O.childPositions.filter (· ∉ [(b + 3)]) = [b, b + 2] := by rw [hOc]; simp [Nat.add_assoc]
        rw [hrest]
        have h0 := hpair_030 od e hod hodk he hek
        change M.bound + (O.part [(b + 3)] Side.lower e).bound +
          (O.part [b, b + 2] Side.upper (σ.k - 1 - e)).bound ≤ σ.bound at h0
        have h1 := hpair_031 od e hod hodk he hek
        change M.bound + (O.part [(b + 3)] Side.upper (σ.k - 1 - e)).bound +
          (O.part [b, b + 2] Side.lower e).bound ≤ σ.bound at h1
        exact ⟨hremove1 _ _ _ _ h0, hremove1 _ _ _ _ h1⟩
    have hOb := hthreeCuts O b (b + 2) (b + 3) (σ.bound - M.bound) (by omega) (by omega) hOc hOruns hcuts
    have hMknown := hquad_0000 od 1 1 hod hodk (by decide) (by omega) (by decide) (by omega)
    change M.bound + (O.part [b] Side.lower 1).bound +
      (O.part [b + 2, b + 3] Side.upper (σ.k - 1 - 1)).bound ≤ σ.bound at hMknown
    change M.bound + O.bound ≤ _
    exact hfinish1 _ _ _ _ _ hMknown hOb
  have hfinal1 (od : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2) :
      (σ.part [b + 1] Side.lower (σ.k - 1 - od)).bound +
        (σ.part [b, b + 2, b + 3] Side.upper od).bound ≤ σ.bound := by
    clear * - σ b hpos od hod hodk htwoStarts hthreeCuts hremove1 hfinish1 hquad_1000 hquad_1010 hpair_120 hpair_121 hpair_130 hpair_131
    let O := σ.part [b, b + 2, b + 3] Side.upper od
    let M := σ.part [b + 1] Side.lower (σ.k - 1 - od)
    have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by simpa [List.range'_succ, Nat.add_assoc] using hpos
    have hOc : O.childPositions = [b, b + 2, b + 3] := by
      change (σ.part _ _ _).childPositions = _
      rw [part_childPositions, hCP4]
      simp [Nat.add_assoc]
    have hOruns : 2 ≤ O.numRuns := htwoStarts O b (b + 2)
      (by rw [hOc]; simp) (by rw [hOc]; simp) (by omega)
      (by rw [hOc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by rw [hOc]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have hcuts (x : ℕ) (hx : x ∈ [b, b + 2, b + 3]) (e : ℕ)
        (he : 1 ≤ e) (hek : e ≤ O.k - 2) :
        (O.part [x] Side.lower e).bound + (O.part (O.childPositions.filter (· ∉ [x])) Side.upper (O.k - 1 - e)).bound ≤ σ.bound - M.bound ∧
        (O.part [x] Side.upper (O.k - 1 - e)).bound + (O.part (O.childPositions.filter (· ∉ [x])) Side.lower e).bound ≤ σ.bound - M.bound := by
      change e ≤ σ.k - 2 at hek
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx
      · subst x
        have hrest : O.childPositions.filter (· ∉ [b]) = [b + 2, b + 3] := by rw [hOc]; simp [Nat.add_assoc]
        rw [hrest]
        have h0 := hquad_1000 od e 1 hod hodk he hek (by decide) (by omega)
        change M.bound + (O.part [b] Side.lower e).bound +
          (O.part [b + 2, b + 3] Side.upper (σ.k - 1 - e)).bound ≤ σ.bound at h0
        have h1 := hquad_1010 od e 1 hod hodk he hek (by decide) (by omega)
        change M.bound + (O.part [b] Side.upper (σ.k - 1 - e)).bound +
          (O.part [b + 2, b + 3] Side.lower e).bound ≤ σ.bound at h1
        exact ⟨hremove1 _ _ _ _ h0, hremove1 _ _ _ _ h1⟩
      · subst x
        have hrest : O.childPositions.filter (· ∉ [(b + 2)]) = [b, b + 3] := by rw [hOc]; simp [Nat.add_assoc]
        rw [hrest]
        have h0 := hpair_120 od e hod hodk he hek
        change M.bound + (O.part [(b + 2)] Side.lower e).bound +
          (O.part [b, b + 3] Side.upper (σ.k - 1 - e)).bound ≤ σ.bound at h0
        have h1 := hpair_121 od e hod hodk he hek
        change M.bound + (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).bound +
          (O.part [b, b + 3] Side.lower e).bound ≤ σ.bound at h1
        exact ⟨hremove1 _ _ _ _ h0, hremove1 _ _ _ _ h1⟩
      · subst x
        have hrest : O.childPositions.filter (· ∉ [(b + 3)]) = [b, b + 2] := by rw [hOc]; simp [Nat.add_assoc]
        rw [hrest]
        have h0 := hpair_130 od e hod hodk he hek
        change M.bound + (O.part [(b + 3)] Side.lower e).bound +
          (O.part [b, b + 2] Side.upper (σ.k - 1 - e)).bound ≤ σ.bound at h0
        have h1 := hpair_131 od e hod hodk he hek
        change M.bound + (O.part [(b + 3)] Side.upper (σ.k - 1 - e)).bound +
          (O.part [b, b + 2] Side.lower e).bound ≤ σ.bound at h1
        exact ⟨hremove1 _ _ _ _ h0, hremove1 _ _ _ _ h1⟩
    have hOb := hthreeCuts O b (b + 2) (b + 3) (σ.bound - M.bound) (by omega) (by omega) hOc hOruns hcuts
    have hMknown := hquad_1000 od 1 1 hod hodk (by decide) (by omega) (by decide) (by omega)
    change M.bound + (O.part [b] Side.lower 1).bound +
      (O.part [b + 2, b + 3] Side.upper (σ.k - 1 - 1)).bound ≤ σ.bound at hMknown
    change M.bound + O.bound ≤ _
    exact hfinish1 _ _ _ _ _ hMknown hOb
  have hlo := hfinal0 d hd hdk
  have hup := hfinal1 (σ.k - 1 - d) (by clear * - hd hdk; omega) (by clear * - hd hdk; omega)
  have hcomp : σ.k - 1 - (σ.k - 1 - d) = d := by clear * - hd hdk; omega
  rw [hcomp] at hup
  constructor
  · simpa only [Nat.add_comm] using hlo
  · simpa only [Nat.add_comm] using hup

end ErdosSzekeres
