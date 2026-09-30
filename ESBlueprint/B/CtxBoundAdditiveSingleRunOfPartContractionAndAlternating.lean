import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxBoundExternalLetterContraction
import ESBlueprint.B.CtxBaseChildLetterContraction
import Mathlib.Data.List.Chain
import Mathlib.Data.List.GetD
import ESBlueprint.B.CtxBoundAttainedByEndCut

namespace ErdosSzekeres
open Ctx Ctx.Context
set_option maxHeartbeats 8000000

/-- Single-run additivity from run contraction on parts of single-run contexts (hpart, C1p) and alternating additivity (halternating, C3): the closed R6 glue with its general-C1 hypothesis narrowed to what it uses (R7/R11).
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_external_letter_contraction, ErdosSzekeres.ctx_base_child_letter_contraction
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_bound_additive_single_run_of_part_contraction_and_alternating (hpart : ∀ (τ : Ctx.Context), τ.WellFormed → τ.numRuns ≤ 1 → ∀ (keep : List ℕ) (s : Ctx.Side) (m : ℕ), 1 ≤ m → m ≤ τ.k - 2 → ∀ (left right : List Ctx.Letter), (τ.part keep s m).word = left ++ [Ctx.Letter.child, Ctx.Letter.child] ++ right → (τ.part keep s m).bound = ({ τ.part keep s m with word := left ++ [Ctx.Letter.child] ++ right } : Ctx.Context).bound) (halternating : ∀ (τ : Ctx.Context), τ.WellFormed → τ.numRuns ≤ 1 → 2 ≤ τ.childPositions.length → ∀ (r : ℕ), r < 2 → ∀ (d : ℕ), 1 ≤ d → d ≤ τ.k - 2 → let keep := ((List.range τ.childPositions.length).filter (fun i => i % 2 = r)).map (fun i => τ.childPositions.getD i 0); (τ.part keep Ctx.Side.lower d).bound + (τ.part (τ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (τ.k - 1 - d)).bound ≤ τ.bound ∧ (τ.part keep Ctx.Side.upper (τ.k - 1 - d)).bound + (τ.part (τ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ τ.bound) (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : σ.numRuns ≤ 1) (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) : (σ.part keep Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧ (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun p => p ∉ keep)) Ctx.Side.lower d).bound ≤ σ.bound := by
  classical
  have hCtxEq : ∀ (τ ρ : Context), τ.a = ρ.a → τ.u = ρ.u → τ.k = ρ.k →
      τ.word = ρ.word → τ.maxima = ρ.maxima → τ = ρ := by
    intro τ ρ ha hu hk hw hm
    cases τ
    cases ρ
    cases ha
    cases hu
    cases hk
    cases hw
    cases hm
    rfl
  have hInterval (ρ : Context) (hruns : ρ.numRuns ≤ 1) (hchildNe : ρ.childPositions ≠ []) :
      ∃ b, ρ.childPositions = List.range' b ρ.childPositions.length := by
    obtain ⟨b, tail, hcons⟩ := List.exists_cons_of_ne_nil hchildNe
    have hb : b ∈ ρ.childPositions := by
      rw [hcons]
      exact List.mem_cons_self
    have hordered : ρ.childPositions.Pairwise (· ≤ ·) :=
      (Ctx.Context.childPositions_pairwise ρ).imp le_of_lt
    have hmin : ∀ p ∈ ρ.childPositions, b ≤ p := by
      intro p hp
      have h := hordered.rel_head hp
      simpa [hcons] using h
    let starts := (List.range ρ.word.length).filter fun p ↦
      ρ.letterAt p = Ctx.Letter.child ∧
        (p = 0 ∨ ρ.letterAt (p - 1) ≠ Ctx.Letter.child)
    have hstartsLen : starts.length ≤ 1 := by
      simpa [starts, Ctx.Context.numRuns] using hruns
    have hstartsNodup : starts.Nodup := by
      exact List.nodup_range.filter _
    have hbRange : b < ρ.word.length := by
      exact List.mem_range.1 (List.mem_filter.1 hb).1
    have hbLetter : ρ.letterAt b = Ctx.Letter.child :=
      of_decide_eq_true (List.mem_filter.1 hb).2
    have hbStartCondition :
        b = 0 ∨ ρ.letterAt (b - 1) ≠ Ctx.Letter.child := by
      by_cases hb0 : b = 0
      · exact Or.inl hb0
      · right
        intro hprev
        have hprevMem : b - 1 ∈ ρ.childPositions := by
          apply List.mem_filter.2
          exact ⟨List.mem_range.2 (by omega), by simpa using hprev⟩
        have := hmin (b - 1) hprevMem
        omega
    have hbStart : b ∈ starts := by
      simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hbRange, hbLetter, hbStartCondition⟩
    have hstartUnique : ∀ p ∈ starts, p = b := by
      intro p hp
      by_contra hpb
      have hsubset : ({b, p} : Finset ℕ) ⊆ starts.toFinset := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact List.mem_toFinset.2 hbStart
        · exact List.mem_toFinset.2 hp
      have hcard := Finset.card_le_card hsubset
      rw [List.toFinset_card_of_nodup hstartsNodup] at hcard
      have htwo : ({b, p} : Finset ℕ).card = 2 := by
        simp [Ne.symm hpb]
      rw [htwo] at hcard
      omega
    have hpred : ∀ p ∈ ρ.childPositions, p ≠ b → p - 1 ∈ ρ.childPositions := by
      intro p hp hpb
      have hpRange : p < ρ.word.length :=
        List.mem_range.1 (List.mem_filter.1 hp).1
      have hpLetter : ρ.letterAt p = Ctx.Letter.child :=
        of_decide_eq_true (List.mem_filter.1 hp).2
      have hpPositive : 0 < p := by
        have := hmin p hp
        omega
      by_contra hprevMem
      have hprevLetter : ρ.letterAt (p - 1) ≠ Ctx.Letter.child := by
        intro hletter
        apply hprevMem
        apply List.mem_filter.2
        exact ⟨List.mem_range.2 (by omega), by simpa using hletter⟩
      have hpStart : p ∈ starts := by
        simp only [starts, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hpRange, hpLetter, Or.inr hprevLetter⟩
      exact hpb (hstartUnique p hpStart)
    have hfill : ∀ p ∈ ρ.childPositions, ∀ q, b ≤ q → q ≤ p →
        q ∈ ρ.childPositions := by
      intro p
      induction p using Nat.strong_induction_on with
      | h p ih =>
        intro hp q hbq hqp
        by_cases hpb : p = b
        · have : q = b := by omega
          simpa [this] using hb
        by_cases hqp' : q = p
        · simpa [hqp'] using hp
        exact ih (p - 1) (by omega) (hpred p hp hpb) q hbq (by omega)
    let e := ρ.childPositions.getLast hchildNe
    have he : e ∈ ρ.childPositions := by
      dsimp [e]
      exact List.getLast_mem _
    have hmax : ∀ p ∈ ρ.childPositions, p ≤ e := by
      intro p hp
      simpa [e] using hordered.rel_getLast hp
    have hbe : b ≤ e := hmin e he
    have hmemRange : ∀ p, p ∈ ρ.childPositions ↔
        p ∈ List.range' b (e + 1 - b) := by
      intro p
      simp only [List.mem_range'_1]
      constructor
      · intro hp
        exact ⟨hmin p hp, by have := hmax p hp; omega⟩
      · rintro ⟨hbp, hp⟩
        exact hfill e he p hbp (by omega)
    have hperm : ρ.childPositions.Perm (List.range' b (e + 1 - b)) :=
      (List.perm_ext_iff_of_nodup (Ctx.Context.childPositions_nodup ρ)
        List.nodup_range').2 hmemRange
    have hrange : ρ.childPositions = List.range' b (e + 1 - b) :=
      List.Perm.eq_of_pairwise' (r := (· ≤ ·)) hordered List.pairwise_le_range' hperm
    have hlen : ρ.childPositions.length = e + 1 - b := by
      rw [hrange]
      simp
    have hinterval : ρ.childPositions = List.range' b ρ.childPositions.length := by
      rw [hlen]
      exact hrange
    exact ⟨b, hinterval⟩
  have hExtMem : ∀ (τ : Context) (N : ℕ) (s : Side),
      Letter.ext N s ∈ τ.word ↔ ∃ p, τ.letterAt p = Letter.ext N s := by
    intro τ N s
    constructor
    · intro h
      obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp h
      exact ⟨p, by simp [Context.letterAt, hp]⟩
    · rintro ⟨p, hp⟩
      unfold Context.letterAt at hp
      cases he : τ.word[p]? with
      | none => simp [he] at hp
      | some x =>
        simp only [he, Option.getD_some] at hp
        exact List.mem_iff_getElem?.mpr ⟨p, hp ▸ he⟩
  have hWF : ∀ (τ : Context) (W : List Letter), τ.WellFormed →
      (∀ N s, Letter.ext N s ∈ W → Letter.ext N s ∈ τ.word) →
      ({ τ with word := W } : Context).WellFormed := by
    intro τ W hτ hsub
    obtain ⟨ha, hu, hak, huk, hmax, hlet⟩ := hτ
    refine ⟨ha, hu, hak, huk, hmax, ?_⟩
    intro p N s hp
    let ρ : Context := { τ with word := W }
    have hmem : Letter.ext N s ∈ W := (hExtMem ρ N s).mpr ⟨p, hp⟩
    obtain ⟨q, hq⟩ := (hExtMem τ N s).mp (hsub N s hmem)
    obtain ⟨hN, hlen, hs⟩ := hlet q N s hq
    refine ⟨hN, hlen, ?_⟩
    have hplen : p < W.length := by
      by_contra h
      have := letterAt_of_length_le ρ (show ρ.word.length ≤ p by simpa [ρ] using Nat.le_of_not_gt h)
      rw [this] at hp
      cases hp
    have hpN : p ∈ ρ.extPositions N := by
      simp [Context.extPositions, ρ, hplen, hp]
    obtain ⟨q', hq'⟩ : ∃ q', (ρ.extPositions N).head? = some q' := by
      cases he : ρ.extPositions N with
      | nil => simp [he] at hpN
      | cons q' qs => exact ⟨q', rfl⟩
    have hq'mem := List.mem_of_mem_head? (Option.mem_def.mpr hq')
    have hq'ext := (List.mem_filter.mp hq'mem).2
    cases hletter : ρ.letterAt q' with
    | child => simp [hletter] at hq'ext
    | ext N' s' =>
      have heq : N' = N := by simpa [hletter] using hq'ext
      subst N'
      have hx := (hExtMem ρ N s').mpr ⟨q', hletter⟩
      obtain ⟨q'', hq''⟩ := (hExtMem τ N s').mp (hsub N s' hx)
      have hs' := (hlet q'' N s' hq'').2.2
      change s = ρ.sideAt N
      unfold Context.sideAt
      simp only [hq', hletter]
      exact hs.trans hs'.symm
  -- A word with one uninterrupted child block has exactly the corresponding interval of positions.
  have hPositions : ∀ (τ : Context) (L R : List Letter) (n : ℕ),
      (∀ x ∈ L ++ R, x ≠ Letter.child) →
      τ.word = L ++ List.replicate n Letter.child ++ R →
      τ.childPositions = List.range' L.length n := by
    intro τ L R n hext hw
    apply (childPositions_pairwise τ).eq_of_mem_iff (List.pairwise_lt_range' _ (by omega))
    intro p
    simp only [Context.childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq,
      List.mem_range'_1]
    have hsize : τ.word.length = L.length + n + R.length := by simp [hw, Nat.add_assoc]
    by_cases hpL : p < L.length
    · have hn : τ.letterAt p ≠ Letter.child := by
        have hx := hext L[p] (List.mem_append_left _ (List.getElem_mem hpL))
        simpa [Context.letterAt, hw, List.append_assoc, List.getElem?_append_left hpL,
          List.getElem?_eq_getElem hpL] using hx
      constructor
      · rintro ⟨_, h⟩; exact (hn h).elim
      · omega
    · by_cases hpN : p < L.length + n
      · have hrel : p - L.length < n := by omega
        have hp : p < τ.word.length := by omega
        have hs : τ.letterAt p = Letter.child := by
          simp [Context.letterAt, hw, List.append_assoc,
            List.getElem?_append_right (Nat.le_of_not_gt hpL),
            List.getElem?_append_left (show p - L.length <
              (List.replicate n Letter.child).length by simpa using hrel), hrel]
        exact ⟨fun _ ↦ ⟨by omega, hpN⟩, fun _ ↦ ⟨hp, hs⟩⟩
      · constructor
        · rintro ⟨hp, hs⟩
          have hrel : p - L.length - n < R.length := by omega
          have hx := hext R[p - L.length - n]
            (List.mem_append_right _ (List.getElem_mem hrel))
          have he : τ.letterAt p = R[p - L.length - n] := by
            simp [Context.letterAt, hw, List.append_assoc,
              List.getElem?_append_right (Nat.le_of_not_gt hpL),
              List.getElem?_append_right (show (List.replicate n Letter.child).length ≤
                p - L.length by simp; omega), List.getElem?_eq_getElem hrel]
          exact (hx (he.symm.trans hs)).elim
        · omega
  have hRunCount : ∀ (τ : Context) (a n : ℕ),
      τ.childPositions = List.range' a n → τ.numRuns ≤ 1 := by
    intro τ a n hps
    let starts := (List.range τ.word.length).filter fun p ↦
      τ.letterAt p = Letter.child ∧ (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child)
    have hsubset : starts.toFinset ⊆ ({a} : Finset ℕ) := by
      intro p hp
      have hstart : p < τ.word.length ∧ τ.letterAt p = Letter.child ∧
          (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child) := by simpa [starts] using hp
      have hp' : a ≤ p ∧ p < a + n := by
        have hm : p ∈ τ.childPositions := by simp [Context.childPositions, hstart]
        simpa [hps, List.mem_range'_1] using hm
      simp only [Finset.mem_singleton]
      by_contra hpa
      have hprev : p - 1 ∈ τ.childPositions := by rw [hps, List.mem_range'_1]; omega
      have hprev' : τ.letterAt (p - 1) = Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hprev).2
      rcases hstart.2.2 with hz | hnot
      · omega
      · exact hnot hprev'
    have hruns : τ.numRuns ≤ 1 := by
      calc
        τ.numRuns = starts.toFinset.card :=
          (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
        _ ≤ ({a} : Finset ℕ).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    exact hruns
  have hRunBase : ∀ (τ : Context) (a n : ℕ),
      τ.childPositions = List.range' a n → τ.bound = τ.base := by
    intro τ a n hps
    have hruns := hRunCount τ a n hps
    simp [Context.bound, Context.boundFuel, hruns]
  -- Repeated use of the proved base transport contracts any nonempty child block.
  have hBaseRun : ∀ (τ : Context) (L R : List Letter) (n : ℕ), 0 < n →
      τ.word = L ++ List.replicate n Letter.child ++ R →
      τ.base = ({ τ with word := L ++ [Letter.child] ++ R } : Context).base := by
    intro τ L R n hn hw
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    induction j generalizing τ with
    | zero =>
      apply congrArg Context.base
      exact hCtxEq _ _ rfl rfl rfl (by simpa using hw) rfl
    | succ j ih =>
      let ρ : Context := { τ with word := L ++ List.replicate (j + 1) Letter.child ++ R }
      have hstep := ctx_base_child_letter_contraction τ L
        (List.replicate j Letter.child ++ R)
        (by simpa [List.replicate_succ, List.append_assoc] using hw)
      have he : τ.base = ρ.base := by simpa [ρ, List.replicate_succ, List.append_assoc] using hstep
      exact he.trans (by simpa [ρ] using ih ρ (by omega) rfl)
  let shift : Letter → Letter
    | .child => .child
    | .ext N s => .ext (N + 1) s
  let replace (keep : List ℕ) (s : Side) (p : ℕ) : Letter → Letter
    | .child => if p ∈ keep then .child else .ext 1 s
    | .ext N t => .ext (N + 1) t
  have hPartMap : ∀ (τ : Context) keep s n,
      (τ.part keep s n).word = τ.word.mapIdx (replace keep s) := by
    intro τ keep s n
    apply List.ext_getElem (by simp [Context.part])
    intro i hi hj
    simp only [Context.part, List.getElem_map, List.getElem_range, List.getElem_mapIdx]
    have hi' : i < τ.word.length := by simpa [Context.part] using hi
    simp [Context.letterAt, List.getElem?_eq_getElem hi', replace]
    rfl
  have hMapExt : ∀ (L : List Letter) keep s off,
      (∀ x ∈ L, x ≠ Letter.child) →
      L.mapIdx (fun i x ↦ replace keep s (i + off) x) = L.map shift := by
    intro L keep s off hL
    apply List.ext_getElem (by simp)
    intro i hi hj
    have hi' : i < L.length := by simpa using hi
    have hx := hL L[i] (List.getElem_mem hi')
    simp only [List.getElem_mapIdx, List.getElem_map]
    cases he : L[i] with
    | child => exact (hx he).elim
    | ext N t => simp [replace, shift]
  let keepOf (off : ℕ) (bs : List Bool) :=
    ((List.range bs.length).filter (fun i ↦ bs.getD i false)).map (fun i ↦ i + off)
  let paint (s : Side) (bs : List Bool) :=
    bs.map (fun b ↦ if b then Letter.child else Letter.ext 1 s)
  have hKeepMem : ∀ (off : ℕ) (bs : List Bool) (i : ℕ) (hi : i < bs.length),
      i + off ∈ keepOf off bs ↔ bs[i] = true := by
    intro off bs i hi
    constructor
    · intro h
      obtain ⟨j, hj, he⟩ := List.mem_map.mp h
      have hji : j = i := Nat.add_right_cancel he
      subst j
      have ht := (List.mem_filter.mp hj).2
      change bs.getD i false = true at ht
      rw [List.getD_eq_getElem bs false hi] at ht
      exact ht
    · intro h
      apply List.mem_map.mpr
      refine ⟨i, List.mem_filter.mpr ⟨List.mem_range.mpr hi, ?_⟩, rfl⟩
      change bs.getD i false = true
      rw [List.getD_eq_getElem bs false hi]
      exact h
  have hPartPaint : ∀ (τ : Context) (L R : List Letter) (bs : List Bool) s m,
      (∀ x ∈ L ++ R, x ≠ Letter.child) →
      τ.word = L ++ List.replicate bs.length Letter.child ++ R →
      (τ.part (keepOf L.length bs) s m).word =
        L.map shift ++ paint s bs ++ R.map shift := by
    intro τ L R bs s m hout hw
    rw [hPartMap, hw]
    simp only [List.mapIdx_append, List.length_append, List.length_replicate]
    have hL := hMapExt L (keepOf L.length bs) s 0
      (fun x hx ↦ hout x (List.mem_append_left _ hx))
    simp only [Nat.add_zero] at hL
    rw [hL, hMapExt R (keepOf L.length bs) s _
      (fun x hx ↦ hout x (List.mem_append_right _ hx))]
    have hmid : (List.replicate bs.length Letter.child).mapIdx
        (fun i x ↦ replace (keepOf L.length bs) s (i + L.length) x) = paint s bs := by
      apply List.ext_getElem (by simp [paint])
      intro i hi hj
      have hib : i < bs.length := by simpa using hi
      simp only [List.getElem_mapIdx, List.getElem_replicate, paint, List.getElem_map,
        replace, hKeepMem L.length bs i hib]
    rw [hmid]
  have hComplement : ∀ (off : ℕ) (bs : List Bool),
      (List.range' off bs.length).filter (fun p ↦ p ∉ keepOf off bs) =
        keepOf off (bs.map Bool.not) := by
    intro off bs
    rw [List.range'_eq_map_range, List.filter_map]
    have hm : (fun i ↦ off + i) = (fun i ↦ i + off) := by
      funext i
      omega
    rw [hm]
    conv_rhs =>
      unfold keepOf
      rw [List.length_map]
    change ((List.range bs.length).filter
      (fun i ↦ decide (i + off ∉ keepOf off bs))).map (fun i ↦ i + off) =
        ((List.range bs.length).filter (fun i ↦ (bs.map Bool.not).getD i false)).map
          (fun i ↦ i + off)
    congr 1
    apply List.filter_congr
    intro i hi
    have hib : i < bs.length := List.mem_range.mp hi
    have hin : i < (bs.map Bool.not).length := by simpa using hib
    rw [List.getD_eq_getElem _ false hin]
    simp only [List.getElem_map]
    cases he : bs[i] <;> simp [hKeepMem off bs i hib, he]
  have hParityKeep : ∀ (τ : Context) (off : ℕ) (bs : List Bool) (r : ℕ),
      τ.childPositions = List.range' off bs.length →
      (∀ i (hi : i < bs.length), bs[i] = decide (i % 2 = r)) →
      keepOf off bs =
        ((List.range τ.childPositions.length).filter (fun i ↦ i % 2 = r)).map
          (fun i ↦ τ.childPositions.getD i 0) := by
    intro τ off bs r hp hb
    rw [hp, List.length_range']
    unfold keepOf
    have hf : (List.range bs.length).filter (fun i ↦ bs.getD i false) =
        (List.range bs.length).filter (fun i ↦ i % 2 = r) := by
      apply List.filter_congr
      intro i hi
      rw [List.getD_eq_getElem bs false (List.mem_range.mp hi), hb i (List.mem_range.mp hi)]
    rw [hf]
    apply List.map_congr_left
    intro i hi
    have hin : i < (List.range' off bs.length).length := by
      simpa using List.mem_range.mp (List.mem_filter.mp hi).1
    rw [List.getD_eq_getElem _ 0 hin]
    simp only [List.getElem_range']
    omega
  have hReconstruct : ∀ (τ : Context) (b n : ℕ), 0 < n →
      τ.childPositions = List.range' b n →
      ∃ L R : List Letter, L.length = b ∧
        τ.word = L ++ List.replicate n Letter.child ++ R ∧
        (∀ x ∈ L ++ R, x ≠ Letter.child) := by
    intro τ b n hn hp
    have hmem : ∀ p, p ∈ τ.childPositions ↔ b ≤ p ∧ p < b + n := by
      intro p
      rw [hp, List.mem_range'_1]
    have hlen : b + n ≤ τ.word.length := by
      have hh : b + n - 1 ∈ τ.childPositions := (hmem _).mpr ⟨by omega, by omega⟩
      have := List.mem_range.mp (List.mem_filter.mp hh).1
      omega
    let L := τ.word.take b
    let R := τ.word.drop (b + n)
    have hLlen : L.length = b := by
      simp [L, Nat.min_eq_left (show b ≤ τ.word.length by omega)]
    have hmid : (τ.word.drop b).take n = List.replicate n Letter.child := by
      apply List.ext_getElem (by simp; omega)
      intro i hi hj
      have hi' : i < n := by simpa using hj
      have hib : b + i < τ.word.length := by omega
      have hchild : b + i ∈ τ.childPositions := (hmem _).mpr ⟨by omega, by omega⟩
      have hc : τ.letterAt (b + i) = Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hchild).2
      simp only [List.getElem_take, List.getElem_drop, List.getElem_replicate]
      simpa [Context.letterAt, List.getElem?_eq_getElem hib] using hc
    have hw : τ.word = L ++ List.replicate n Letter.child ++ R := by
      rw [← hmid]
      dsimp [L, R]
      rw [← List.take_add, List.take_append_drop]
    refine ⟨L, R, hLlen, hw, ?_⟩
    intro x hx hc
    subst x
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
      have hib : i < b := by simpa [hLlen] using hi
      have hiw : i < τ.word.length := by omega
      have hl : τ.letterAt i = Letter.child := by
        simpa [L, Context.letterAt, List.getElem?_eq_getElem hiw] using he
      have hm : i ∈ τ.childPositions := by simp [Context.childPositions, hiw, hl]
      have := (hmem i).mp hm
      omega
    · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
      have hiw : b + n + i < τ.word.length := by
        simp only [R, List.length_drop] at hi
        omega
      have hl : τ.letterAt (b + n + i) = Letter.child := by
        simpa [R, Context.letterAt, List.getElem?_eq_getElem hiw] using he
      have hm : b + n + i ∈ τ.childPositions := by
        simp [Context.childPositions, hiw, hl]
      have := (hmem _).mp hm
      omega
  have hDichotomy : ∀ (bs : List Bool),
      (∃ (pre : List Bool) (b : Bool) (post : List Bool), bs = pre ++ b :: b :: post) ∨
        (∃ r : ℕ, r < 2 ∧ ∀ i (hi : i < bs.length), bs[i] = decide (i % 2 = r)) := by
    intro bs
    classical
    by_cases hc : bs.IsChain (· ≠ ·)
    · right
      cases bs with
      | nil => exact ⟨0, by omega, by simp⟩
      | cons b tl =>
        refine ⟨if b then 0 else 1, by cases b <;> simp, ?_⟩
        intro i
        induction i with
        | zero => intro hi; cases b <;> simp
        | succ i ih =>
          intro hi
          have hprev : i < (b :: tl).length := by omega
          have hne := (List.isChain_iff_getElem.mp hc) i hi
          rw [ih hprev] at hne
          have hmod : (i + 1) % 2 = 1 - i % 2 := by omega
          have hlt : i % 2 < 2 := Nat.mod_lt i (by omega)
          cases he : (b :: tl)[i + 1] <;> cases b <;> simp [he] at hne ⊢ <;> omega
    · left
      have hn := List.isChain_iff_forall_rel_of_append_cons_cons.not.mp hc
      push Not at hn
      obtain ⟨a, b, pre, post, heq, hab⟩ := hn
      have he : a = b := by simpa using hab
      subst b
      exact ⟨pre, a, post, heq⟩
  have hPaintContract : ∀ (τ : Context) (L R : List Letter) (pre post : List Bool)
      (b : Bool) (s : Side) (m : ℕ), τ.WellFormed →
      (∀ x ∈ L ++ R, x ≠ Letter.child) →
      τ.word = L ++ List.replicate (pre ++ b :: b :: post).length Letter.child ++ R →
      1 ≤ m → m ≤ τ.k - 2 →
      (τ.part (keepOf L.length (pre ++ b :: b :: post)) s m).bound =
        (({ τ with word := L ++ List.replicate (pre ++ b :: post).length Letter.child ++ R }
          : Context).part (keepOf L.length (pre ++ b :: post)) s m).bound := by
    intro τ L R pre post b s m hwf hout hw hm1 hmk
    let big := τ.part (keepOf L.length (pre ++ b :: b :: post)) s m
    let ρ : Context :=
      { τ with word := L ++ List.replicate (pre ++ b :: post).length Letter.child ++ R }
    let small := ρ.part (keepOf L.length (pre ++ b :: post)) s m
    let A := L.map shift ++ paint s pre
    let B := paint s post ++ R.map shift
    let x := if b then Letter.child else Letter.ext 1 s
    have hbw : big.word = A ++ [x, x] ++ B := by
      rw [hPartPaint τ L R (pre ++ b :: b :: post) s m hout hw]
      simp [A, B, x, paint, List.map_append, List.append_assoc]
    have hsw : small.word = A ++ [x] ++ B := by
      rw [hPartPaint ρ L R (pre ++ b :: post) s m hout rfl]
      simp [A, B, x, paint, List.map_append, List.append_assoc]
    have hbwF : big.WellFormed := hwf.part _ s hm1 hmk
    have hdel : big.bound = ({ big with word := A ++ [x] ++ B } : Context).bound := by
      cases b with
      | false =>
        exact ctx_bound_external_letter_contraction big hbwF A B 1 s hbw
      | true =>
        have hrun : τ.numRuns ≤ 1 :=
          hRunCount τ L.length _ (hPositions τ L R _ hout hw)
        exact hpart τ hwf hrun
          (keepOf L.length (pre ++ true :: true :: post)) s m hm1 hmk A B hbw
    have heq : ({ big with word := A ++ [x] ++ B } : Context) = small :=
      hCtxEq _ _ rfl rfl rfl hsw.symm rfl
    exact hdel.trans (congrArg Context.bound heq)
  have hAll : ∀ n : ℕ, ∀ (bs : List Bool), bs.length = n →
      ∀ (τ : Context) (L R : List Letter), τ.WellFormed →
      (∀ x ∈ L ++ R, x ≠ Letter.child) →
      τ.word = L ++ List.replicate bs.length Letter.child ++ R →
      true ∈ bs → false ∈ bs → ∀ (d : ℕ), 1 ≤ d → d ≤ τ.k - 2 →
      (τ.part (keepOf L.length bs) Side.lower d).bound +
          (τ.part (keepOf L.length (bs.map Bool.not)) Side.upper (τ.k - 1 - d)).bound
            ≤ τ.bound ∧
        (τ.part (keepOf L.length bs) Side.upper (τ.k - 1 - d)).bound +
          (τ.part (keepOf L.length (bs.map Bool.not)) Side.lower d).bound ≤ τ.bound := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro bs hn τ L R hwf hout hw ht hf d hd hdk
      have hpos := hPositions τ L R bs.length hout hw
      rcases hDichotomy bs with hdup | halt
      · obtain ⟨pre, b, post, rfl⟩ := hdup
        let short := pre ++ b :: post
        let ρ : Context := { τ with word := L ++ List.replicate short.length Letter.child ++ R }
        have hshort : short.length < n := by
          simp only [List.length_append, List.length_cons] at hn
          simp only [short, List.length_append, List.length_cons]
          omega
        have ht' : true ∈ short := by simpa [short, List.mem_append] using ht
        have hf' : false ∈ short := by simpa [short, List.mem_append] using hf
        have hρwf : ρ.WellFormed := hWF τ _ hwf (by
          intro N s hx
          simpa [ρ, hw, List.mem_append, List.mem_replicate] using hx)
        have hρpos := hPositions ρ L R short.length hout rfl
        have hparent : τ.bound = ρ.bound := by
          rw [hRunBase τ L.length _ hpos, hRunBase ρ L.length _ hρpos]
          have hp := hBaseRun τ L R (pre ++ b :: b :: post).length (by simp) hw
          have hs := hBaseRun ρ L R short.length (by simp [short]) rfl
          exact hp.trans (by simpa [ρ] using hs.symm)
        have hkeepEq (s : Side) (m : ℕ) (hm1 : 1 ≤ m) (hmk : m ≤ τ.k - 2) :
            (τ.part (keepOf L.length (pre ++ b :: b :: post)) s m).bound =
              (ρ.part (keepOf L.length short) s m).bound :=
          hPaintContract τ L R pre post b s m hwf hout hw hm1 hmk
        have hrestEq (s : Side) (m : ℕ) (hm1 : 1 ≤ m) (hmk : m ≤ τ.k - 2) :
            (τ.part (keepOf L.length ((pre ++ b :: b :: post).map Bool.not)) s m).bound =
              (ρ.part (keepOf L.length (short.map Bool.not)) s m).bound := by
          have hp := hPaintContract τ L R (pre.map Bool.not) (post.map Bool.not)
            (!b) s m hwf hout (by simpa using hw) hm1 hmk
          simpa [ρ, short, List.map_append] using hp
        have hc1 : 1 ≤ τ.k - 1 - d := by omega
        have hck : τ.k - 1 - d ≤ τ.k - 2 := by omega
        rw [hkeepEq Side.lower d hd hdk, hrestEq Side.upper _ hc1 hck,
          hkeepEq Side.upper _ hc1 hck, hrestEq Side.lower d hd hdk, hparent]
        exact ih short.length hshort short rfl ρ L R hρwf hout rfl ht' hf' d hd hdk
      · obtain ⟨r, hr, hb⟩ := halt
        have htwo : 2 ≤ bs.length := by
          have hnd : ([true, false] : List Bool).Nodup := by simp
          have hsub : ([true, false] : List Bool) ⊆ bs := by simpa using And.intro ht hf
          have hc := Finset.card_le_card (show ([true, false] : List Bool).toFinset ⊆
              bs.toFinset from fun x hx ↦
                List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp hx)))
          rw [List.toFinset_card_of_nodup hnd] at hc
          exact (show 2 ≤ bs.toFinset.card by simpa using hc).trans (List.toFinset_card_le bs)
        have hrun := hRunCount τ L.length bs.length hpos
        have htwop : 2 ≤ τ.childPositions.length := by simpa [hpos] using htwo
        have ha := halternating τ hwf hrun htwop r hr d hd hdk
        have hk := hParityKeep τ L.length bs r hpos hb
        have hrest := hComplement L.length bs
        rw [← hk] at ha
        dsimp only at ha
        rw [hpos, hrest] at ha
        exact ha
  have hchildNe : σ.childPositions ≠ [] := by
    obtain ⟨p, ps, he⟩ := List.exists_cons_of_ne_nil hne
    have hp := hkeep p (by simp [he])
    intro hempty
    simpa [hempty] using hp
  obtain ⟨off, hpos⟩ := hInterval σ hruns hchildNe
  have hn : 0 < σ.childPositions.length := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hchildNe (List.length_eq_zero_iff.mp hz)
  obtain ⟨L, R, hL, hword, hout⟩ := hReconstruct σ off σ.childPositions.length hn hpos
  let bs : List Bool := (List.range σ.childPositions.length).map
    (fun i ↦ decide (i + off ∈ keep))
  have hbslen : bs.length = σ.childPositions.length := by simp [bs]
  have hbs (i : ℕ) (hi : i < bs.length) : bs[i] = decide (i + off ∈ keep) := by
    simp [bs, List.getElem_map, List.getElem_range]
  have hmember (p : ℕ) (hp : p ∈ σ.childPositions) :
      p ∈ keepOf L.length bs ↔ p ∈ keep := by
    have hpr : off ≤ p ∧ p < off + σ.childPositions.length := by
      rw [hpos, List.mem_range'_1] at hp
      exact hp
    have hi : p - off < bs.length := by rw [hbslen]; omega
    have he : p = (p - off) + L.length := by omega
    rw [he, hKeepMem L.length bs (p - off) hi, hbs _ hi]
    simp [hL]
  have ht : true ∈ bs := by
    obtain ⟨p, ps, he⟩ := List.exists_cons_of_ne_nil hne
    have hp : p ∈ keep := by simp [he]
    have hpc := hkeep p hp
    have hpr : off ≤ p ∧ p < off + σ.childPositions.length := by
      rw [hpos, List.mem_range'_1] at hpc
      exact hpc
    have hi : p - off < bs.length := by rw [hbslen]; omega
    have hv : bs[p - off] = true := by rw [hbs _ hi]; simpa [Nat.sub_add_cancel hpr.1] using hp
    exact hv ▸ List.getElem_mem hi
  have hf : false ∈ bs := by
    by_contra hno
    have hsub : σ.childPositions ⊆ keep := by
      intro p hp
      have hpr : off ≤ p ∧ p < off + σ.childPositions.length := by
        rw [hpos, List.mem_range'_1] at hp
        exact hp
      have hi : p - off < bs.length := by rw [hbslen]; omega
      have hnot : bs[p - off] ≠ false := fun he ↦ hno (he ▸ List.getElem_mem hi)
      have he : bs[p - off] = true := by
        cases hx : bs[p - off] with
        | false => exact (hnot hx).elim
        | true => rfl
      rw [hbs _ hi, decide_eq_true_eq] at he
      simpa [Nat.sub_add_cancel hpr.1] using he
    have hc := Finset.card_le_card (show σ.childPositions.toFinset ⊆ keep.toFinset from
      fun p hp ↦ List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp hp)))
    rw [List.toFinset_card_of_nodup (childPositions_nodup σ)] at hc
    have hlen : σ.childPositions.length ≤ keep.length := hc.trans (List.toFinset_card_le keep)
    omega
  have hw : σ.word = L ++ List.replicate bs.length Letter.child ++ R := by
    simpa [hbslen] using hword
  have hpbs : σ.childPositions = List.range' L.length bs.length := by
    simpa [hL, hbslen] using hpos
  have ha := hAll bs.length bs rfl σ L R hwf hout hw ht hf d hd hdk
  have hkc (s : Side) (m : ℕ) : σ.part (keepOf L.length bs) s m = σ.part keep s m :=
    part_congr σ s m hmember
  have hrc (s : Side) (m : ℕ) :
      σ.part (keepOf L.length (bs.map Bool.not)) s m =
        σ.part (σ.childPositions.filter (fun p ↦ p ∉ keep)) s m := by
    rw [← hComplement L.length bs, ← hpbs]
    apply part_congr
    intro p hp
    simp [hmember p hp]
  simpa [hkc, hrc] using ha

end ErdosSzekeres
