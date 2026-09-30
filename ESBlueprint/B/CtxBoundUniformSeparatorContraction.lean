import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit
import ESBlueprint.B.CtxBoundPartRunContractionOfOneLevelRoot
import ESBlueprint.B.CtxBoundChildRunContractionOneLevelRoot
import Mathlib.Data.List.GetD

namespace ErdosSzekeres

/-- A context with two nonempty child runs separated entirely by copies of one level-one external letter has the same bound after shortening both child runs to singletons, provided all older external letters lie outside the two runs. Parameters, sibling maxima, and separator multiplicity stay fixed. This restricted conjecture is a proposed reduction for single-run sandwich additivity; unrestricted child contraction is false.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive_single_run
@falsifier ctx_approved_uniform.py -/
theorem ctx_bound_uniform_separator_contraction (σ : Ctx.Context) (hwf : σ.WellFormed)
  (left right : List Ctx.Letter) (r m t : ℕ) (side : Ctx.Side)
  (hr : 0 < r) (hm : 0 < m) (ht : 0 < t)
  (houter : ∀ x ∈ left ++ right, ∃ l s, 2 ≤ l ∧ x = Ctx.Letter.ext l s)
  (hword : σ.word = left ++ List.replicate r Ctx.Letter.child ++
    List.replicate m (Ctx.Letter.ext 1 side) ++ List.replicate t Ctx.Letter.child ++ right) :
  σ.bound = ({ σ with
    word := left ++ [Ctx.Letter.child] ++ List.replicate m (Ctx.Letter.ext 1 side) ++
      [Ctx.Letter.child] ++ right } : Ctx.Context).bound := by
  classical
  have hExtMem : ∀ (τ : Ctx.Context) (N : ℕ) (s : Ctx.Side),
      Ctx.Letter.ext N s ∈ τ.word ↔ ∃ p, τ.letterAt p = Ctx.Letter.ext N s := by
    intro τ N s
    constructor
    · intro h
      obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp h
      exact ⟨p, by simp [Ctx.Context.letterAt, hp]⟩
    · rintro ⟨p, hp⟩
      unfold Ctx.Context.letterAt at hp
      cases he : τ.word[p]? with
      | none => simp [he] at hp
      | some x =>
        simp only [he, Option.getD_some] at hp
        exact List.mem_iff_getElem?.mpr ⟨p, hp ▸ he⟩
  let down : Ctx.Letter → Ctx.Letter
    | .child => .child
    | .ext N s => .ext (N - 1) s
  have hOldMem : ∀ x ∈ left ++ right, x ∈ σ.word := by
    intro x hx
    simp only [List.mem_append] at hx
    simp only [hword, List.mem_append]
    tauto
  have hLowerMem : ∀ x ∈ left.map down ++ right.map down,
      ∃ N s, 1 ≤ N ∧ x = Ctx.Letter.ext N s ∧ Ctx.Letter.ext (N + 1) s ∈ σ.word := by
    intro x hx
    rw [← List.map_append] at hx
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
    obtain ⟨N, s, hN, rfl⟩ := houter y hy
    refine ⟨N - 1, s, by omega, ?_, ?_⟩
    · simpa [down] using hxy.symm
    · have hpred : N - 1 + 1 = N := by omega
      rw [hpred]
      exact hOldMem _ hy
  let hat (n : ℕ) : Ctx.Context :=
    { σ with
      word := left.map down ++ List.replicate n Ctx.Letter.child ++ right.map down
      maxima := σ.maxima.tail }
  have hOuterMem : ∀ n N s, Ctx.Letter.ext N s ∈ (hat n).word →
      Ctx.Letter.ext N s ∈ left.map down ++ right.map down := by
    intro n N s hx
    simpa [hat, List.mem_append] using hx
  have hLabels : ∀ n N s, Ctx.Letter.ext N s ∈ (hat n).word →
      1 ≤ N ∧ N ≤ (hat n).maxima.length ∧ s = σ.sideAt (N + 1) := by
    intro n N s hx
    obtain ⟨N', s', hN, he, hold⟩ := hLowerMem _ (hOuterMem n N s hx)
    obtain ⟨rfl, rfl⟩ := Ctx.Letter.ext.inj he
    obtain ⟨q, hq⟩ := (hExtMem σ (N + 1) s).mp hold
    obtain ⟨_, hlen, hs⟩ := hwf.2.2.2.2.2 q (N + 1) s hq
    refine ⟨hN, ?_, hs⟩
    simp only [hat, List.length_tail]
    omega
  have hWF : ∀ n, (hat n).WellFormed := by
    intro n
    obtain ⟨ha, hu, hak, huk, hmax, hlet⟩ := hwf
    refine ⟨ha, hu, hak, huk, ?_, ?_⟩
    · intro M hM
      exact hmax M (List.mem_of_mem_tail hM)
    · intro p N s hp
      have hmem := (hExtMem (hat n) N s).mpr ⟨p, hp⟩
      obtain ⟨hN, hlen, hs⟩ := hLabels n N s hmem
      refine ⟨hN, hlen, ?_⟩
      have hplen : p < (hat n).word.length := by
        by_contra h
        have he := Ctx.Context.letterAt_of_length_le (hat n) (Nat.le_of_not_gt h)
        rw [he] at hp
        cases hp
      have hpN : p ∈ (hat n).extPositions N := by
        simp [Ctx.Context.extPositions, hplen, hp]
      cases hh : ((hat n).extPositions N).head? with
      | none =>
        have hnil := List.head?_eq_none_iff.mp hh
        rw [hnil] at hpN
        simp at hpN
      | some q =>
        have hqmem := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        have hqext := (List.mem_filter.mp hqmem).2
        cases he : (hat n).letterAt q with
        | child => simp [he] at hqext
        | ext N' s' =>
          have heq : N' = N := by simpa [he] using hqext
          subst N'
          have hs' := (hLabels n N s'
            ((hExtMem (hat n) N s').mpr ⟨q, he⟩)).2.2
          change s = (hat n).sideAt N
          unfold Ctx.Context.sideAt
          simp only [hh, he]
          exact hs.trans hs'.symm
  have hCtxEq : ∀ (τ ρ : Ctx.Context), τ.a = ρ.a → τ.u = ρ.u → τ.k = ρ.k →
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
  have hPositions : ∀ (τ : Ctx.Context) (L R : List Ctx.Letter) (n : ℕ),
      (∀ x ∈ L ++ R, x ≠ Ctx.Letter.child) →
      τ.word = L ++ List.replicate n Ctx.Letter.child ++ R →
      τ.childPositions = List.range' L.length n := by
    intro τ L R n hext hw
    apply (Ctx.Context.childPositions_pairwise τ).eq_of_mem_iff
      (List.pairwise_lt_range' _ (by omega))
    intro p
    simp only [Ctx.Context.childPositions, List.mem_filter, List.mem_range, decide_eq_true_eq,
      List.mem_range'_1]
    have hsize : τ.word.length = L.length + n + R.length := by simp [hw, Nat.add_assoc]
    by_cases hpL : p < L.length
    · have hn : τ.letterAt p ≠ Ctx.Letter.child := by
        have hx := hext L[p] (List.mem_append_left _ (List.getElem_mem hpL))
        simpa [Ctx.Context.letterAt, hw, List.append_assoc, List.getElem?_append_left hpL,
          List.getElem?_eq_getElem hpL] using hx
      constructor
      · rintro ⟨_, h⟩; exact (hn h).elim
      · omega
    · by_cases hpN : p < L.length + n
      · have hrel : p - L.length < n := by omega
        have hp : p < τ.word.length := by omega
        have hs : τ.letterAt p = Ctx.Letter.child := by
          simp [Ctx.Context.letterAt, hw, List.append_assoc,
            List.getElem?_append_right (Nat.le_of_not_gt hpL),
            List.getElem?_append_left (show p - L.length <
              (List.replicate n Ctx.Letter.child).length by simpa using hrel), hrel]
        exact ⟨fun _ ↦ ⟨by omega, hpN⟩, fun _ ↦ ⟨hp, hs⟩⟩
      · constructor
        · rintro ⟨hp, hs⟩
          have hrel : p - L.length - n < R.length := by omega
          have hx := hext R[p - L.length - n]
            (List.mem_append_right _ (List.getElem_mem hrel))
          have he : τ.letterAt p = R[p - L.length - n] := by
            simp [Ctx.Context.letterAt, hw, List.append_assoc,
              List.getElem?_append_right (Nat.le_of_not_gt hpL),
              List.getElem?_append_right (show (List.replicate n Ctx.Letter.child).length ≤
                p - L.length by simp; omega), List.getElem?_eq_getElem hrel]
          exact (hx (he.symm.trans hs)).elim
        · omega
  have hRunCount : ∀ (τ : Ctx.Context) (a n : ℕ),
      τ.childPositions = List.range' a n → τ.numRuns ≤ 1 := by
    intro τ a n hps
    let starts := (List.range τ.word.length).filter fun p ↦
      τ.letterAt p = Ctx.Letter.child ∧ (p = 0 ∨ τ.letterAt (p - 1) ≠ Ctx.Letter.child)
    have hsubset : starts.toFinset ⊆ ({a} : Finset ℕ) := by
      intro p hp
      have hstart : p < τ.word.length ∧ τ.letterAt p = Ctx.Letter.child ∧
          (p = 0 ∨ τ.letterAt (p - 1) ≠ Ctx.Letter.child) := by simpa [starts] using hp
      have hp' : a ≤ p ∧ p < a + n := by
        have hm : p ∈ τ.childPositions := by simp [Ctx.Context.childPositions, hstart]
        simpa [hps, List.mem_range'_1] using hm
      simp only [Finset.mem_singleton]
      by_contra hpa
      have hprev : p - 1 ∈ τ.childPositions := by rw [hps, List.mem_range'_1]; omega
      have hprev' : τ.letterAt (p - 1) = Ctx.Letter.child :=
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
  let shift : Ctx.Letter → Ctx.Letter
    | .child => .child
    | .ext N s => .ext (N + 1) s
  let replace (keep : List ℕ) (s : Ctx.Side) (p : ℕ) : Ctx.Letter → Ctx.Letter
    | .child => if p ∈ keep then .child else .ext 1 s
    | .ext N t => .ext (N + 1) t
  have hPartMap : ∀ (τ : Ctx.Context) keep s n,
      (τ.part keep s n).word = τ.word.mapIdx (replace keep s) := by
    intro τ keep s n
    apply List.ext_getElem (by simp [Ctx.Context.part])
    intro i hi hj
    simp only [Ctx.Context.part, List.getElem_map, List.getElem_range, List.getElem_mapIdx]
    have hi' : i < τ.word.length := by simpa [Ctx.Context.part] using hi
    simp [Ctx.Context.letterAt, List.getElem?_eq_getElem hi', replace]
    rfl
  have hMapExt : ∀ (L : List Ctx.Letter) keep s off,
      (∀ x ∈ L, x ≠ Ctx.Letter.child) →
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
  let paint (s : Ctx.Side) (bs : List Bool) :=
    bs.map (fun b ↦ if b then Ctx.Letter.child else Ctx.Letter.ext 1 s)
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
  have hPartPaint : ∀ (τ : Ctx.Context) (L R : List Ctx.Letter) (bs : List Bool) s m,
      (∀ x ∈ L ++ R, x ≠ Ctx.Letter.child) →
      τ.word = L ++ List.replicate bs.length Ctx.Letter.child ++ R →
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
    have hmid : (List.replicate bs.length Ctx.Letter.child).mapIdx
        (fun i x ↦ replace (keepOf L.length bs) s (i + L.length) x) = paint s bs := by
      apply List.ext_getElem (by simp [paint])
      intro i hi hj
      have hib : i < bs.length := by simpa using hi
      simp only [List.getElem_mapIdx, List.getElem_replicate, paint, List.getElem_map,
        replace, hKeepMem L.length bs i hib]
    rw [hmid]
  have hOutside : ∀ x ∈ left.map down ++ right.map down, x ≠ Ctx.Letter.child := by
    intro x hx
    obtain ⟨N, s, _, he, _⟩ := hLowerMem x hx
    rw [he]
    simp
  have hRuns : ∀ n, (hat n).numRuns ≤ 1 := by
    intro n
    exact hRunCount (hat n) _ n
      (hPositions (hat n) (left.map down) (right.map down) n hOutside rfl)
  have hInv : ∀ (W : List Ctx.Letter), (∀ x ∈ W, x ∈ left ++ right) →
      (W.map down).map shift = W := by
    intro W hW
    rw [List.map_map]
    calc
      W.map (shift ∘ down) = W.map (fun x ↦ x) := by
        apply List.map_congr_left
        intro x hx
        obtain ⟨N, s, hN, rfl⟩ := houter x (hW x hx)
        simp [down, shift, Nat.sub_add_cancel (show 1 ≤ N by omega)]
      _ = W := List.map_id' W
  have hMaxNe : σ.maxima ≠ [] := by
    have hsep : Ctx.Letter.ext 1 side ∈ σ.word := by
      simp [hword, List.mem_replicate, show m ≠ 0 by omega]
    obtain ⟨p, hp⟩ := (hExtMem σ 1 side).mp hsep
    have hlen := (hwf.2.2.2.2.2 p 1 side hp).2.1
    intro he
    simp [he] at hlen
  obtain ⟨M, ms, hms⟩ := List.exists_cons_of_ne_nil hMaxNe
  have hM : 1 ≤ M ∧ M ≤ σ.k - 2 := hwf.2.2.2.2.1 M (by rw [hms]; simp)
  let family (bs : List Bool) : Ctx.Context := { σ with word := left ++ paint side bs ++ right }
  have hPartFamily : ∀ bs,
      (hat bs.length).part (keepOf left.length bs) side M = family bs := by
    intro bs
    have hw := hPartPaint (hat bs.length) (left.map down) (right.map down) bs
      side M hOutside rfl
    simp only [List.length_map] at hw
    rw [hInv left (fun x hx ↦ List.mem_append_left _ hx),
      hInv right (fun x hx ↦ List.mem_append_right _ hx)] at hw
    apply hCtxEq ((hat bs.length).part (keepOf left.length bs) side M)
      (family bs) rfl rfl rfl hw
    change M :: σ.maxima.tail = σ.maxima
    rw [hms]
    rfl
  have hContract : ∀ (pre post : List Bool),
      (family (pre ++ true :: true :: post)).bound =
        (family (pre ++ true :: post)).bound := by
    intro pre post
    let bs := pre ++ true :: true :: post
    let A := left ++ paint side pre
    let B := paint side post ++ right
    have hw : ((hat bs.length).part (keepOf left.length bs) side M).word =
        A ++ [Ctx.Letter.child, Ctx.Letter.child] ++ B := by
      rw [hPartFamily]
      simp [family, bs, A, B, paint, List.map_append, List.append_assoc]
    have he := ctx_bound_part_run_contraction_of_one_level_root
      ctx_bound_child_run_contraction_one_level_root (hat bs.length) (hWF _) (hRuns _)
      (keepOf left.length bs) side M hM.1 hM.2 A B hw
    rw [hPartFamily bs] at he
    have hsmall : ({ family bs with word := A ++ [Ctx.Letter.child] ++ B } : Ctx.Context) =
        family (pre ++ true :: post) := by
      apply hCtxEq ({ family bs with word := A ++ [Ctx.Letter.child] ++ B } : Ctx.Context)
        (family (pre ++ true :: post)) rfl rfl rfl
      · simp [family, A, B, paint, List.map_append, List.append_assoc]
      · rfl
    exact he.trans (congrArg Ctx.Context.bound hsmall)
  have hLeft : ∀ n t,
      (family (List.replicate (n + 1) true ++ List.replicate m false ++
        List.replicate t true)).bound =
      (family ([true] ++ List.replicate m false ++ List.replicate t true)).bound := by
    intro n
    induction n with
    | zero => intro t; rfl
    | succ n ih =>
      intro t
      have he := hContract [] (List.replicate n true ++ List.replicate m false ++
        List.replicate t true)
      have hs :
          (family (List.replicate (n + 1 + 1) true ++ List.replicate m false ++
            List.replicate t true)).bound =
          (family (List.replicate (n + 1) true ++ List.replicate m false ++
            List.replicate t true)).bound := by
        simpa only [List.replicate_succ, List.nil_append, List.cons_append] using he
      exact hs.trans (ih t)
  have hRight : ∀ n,
      (family ([true] ++ List.replicate m false ++ List.replicate (n + 1) true)).bound =
      (family ([true] ++ List.replicate m false ++ [true])).bound := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have he := hContract ([true] ++ List.replicate m false) (List.replicate n true)
      have hs :
          (family ([true] ++ List.replicate m false ++
            List.replicate (n + 1 + 1) true)).bound =
          (family ([true] ++ List.replicate m false ++
            List.replicate (n + 1) true)).bound := by
        simpa only [List.replicate_succ, List.append_assoc, List.cons_append,
          List.nil_append] using he
      exact hs.trans ih
  let bs := List.replicate r true ++ List.replicate m false ++ List.replicate t true
  have hOriginal : σ = family bs := by
    apply hCtxEq σ (family bs) rfl rfl rfl
    · simpa [family, bs, paint, List.map_append, List.map_replicate, List.append_assoc]
        using hword
    · rfl
  have hTarget : family ([true] ++ List.replicate m false ++ [true]) =
      ({ σ with word := left ++ [Ctx.Letter.child] ++ List.replicate m (Ctx.Letter.ext 1 side) ++
        [Ctx.Letter.child] ++ right } : Ctx.Context) := by
    apply hCtxEq (family ([true] ++ List.replicate m false ++ [true]))
      ({ σ with word := left ++ [Ctx.Letter.child] ++ List.replicate m (Ctx.Letter.ext 1 side) ++
        [Ctx.Letter.child] ++ right } : Ctx.Context) rfl rfl rfl
    · simp [family, paint, List.map_append, List.map_replicate, List.append_assoc]
    · rfl
  have hleft := hLeft (r - 1) t
  rw [show r - 1 + 1 = r by omega] at hleft
  have hright := hRight (t - 1)
  rw [show t - 1 + 1 = t by omega] at hright
  calc
    σ.bound = (family bs).bound := congrArg Ctx.Context.bound hOriginal
    _ = (family ([true] ++ List.replicate m false ++ List.replicate t true)).bound := hleft
    _ = (family ([true] ++ List.replicate m false ++ [true])).bound := hright
    _ = _ := congrArg Ctx.Context.bound hTarget

end ErdosSzekeres
