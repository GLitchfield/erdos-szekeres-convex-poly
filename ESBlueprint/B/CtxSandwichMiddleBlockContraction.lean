import ESBlueprint.B.CtxBoundAdditiveThreeBlocksOfUniformContraction

namespace ErdosSzekeres

open Ctx Ctx.Context

set_option maxHeartbeats 4000000

/-- Exact middle-block contraction for a three-block partition of a contiguous child run. Replacing the nonempty middle child block by a singleton preserves the parent bound and each part bound, in either orientation at every admissible sibling maximum. The resulting context is well formed with the expected child positions. This reduces the one-singleton-end sandwich family (1,m,r) to (1,1,r), and also applies to arbitrary positive outer block lengths; no child-bound contraction conjecture is used.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_external_letter_contraction, ErdosSzekeres.ctx_base_child_letter_contraction
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_sandwich_middle_block_contraction (σ : Ctx.Context) (hwf : σ.WellFormed)
  (b l m r : ℕ) (hpos : σ.childPositions = List.range' b (l + m + r))
  (hl : 0 < l) (hm : 0 < m) (hr : 0 < r) :
  let τ : Ctx.Context := { σ with word := (σ.word.take b ++
    List.replicate (l + 1 + r) Ctx.Letter.child ++ σ.word.drop (b + (l + m + r))) }
  τ.WellFormed ∧ τ.childPositions = List.range' b (l + 1 + r) ∧ σ.bound = τ.bound ∧
    (∀ (s : Ctx.Side) (q : ℕ), 1 ≤ q → q ≤ σ.k - 2 →
      (σ.part (List.range' b l ++ List.range' (b + l + m) r) s q).bound =
        (τ.part (List.range' b l ++ List.range' (b + l + 1) r) s q).bound ∧
      (σ.part (List.range' (b + l) m) s q).bound = (τ.part [b + l] s q).bound) := by
  classical
  -- Membership, rather than a particular position, is enough to transport well-formedness.
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
        simpa [Context.letterAt, hw, List.append_assoc, List.getElem?_append_left hpL, List.getElem?_eq_getElem hpL] using hx
      constructor
      · rintro ⟨_, h⟩; exact (hn h).elim
      · omega
    · by_cases hpN : p < L.length + n
      · have hrel : p - L.length < n := by omega
        have hp : p < τ.word.length := by omega
        have hs : τ.letterAt p = Letter.child := by
          simp [Context.letterAt, hw, List.append_assoc,
            List.getElem?_append_right (Nat.le_of_not_gt hpL),
            List.getElem?_append_left (show p - L.length < (List.replicate n Letter.child).length by simpa using hrel), List.getElem?_replicate, hrel]
        exact ⟨fun _ ↦ ⟨by omega, hpN⟩, fun _ ↦ ⟨hp, hs⟩⟩
      · constructor
        · rintro ⟨hp, hs⟩
          have hrel : p - L.length - n < R.length := by omega
          have hx := hext R[p - L.length - n]
            (List.mem_append_right _ (List.getElem_mem hrel))
          have he : τ.letterAt p = R[p - L.length - n] := by
            simp [Context.letterAt, hw, List.append_assoc,
              List.getElem?_append_right (Nat.le_of_not_gt hpL),
              List.getElem?_append_right (show (List.replicate n Letter.child).length ≤ p - L.length by simp; omega), List.getElem?_eq_getElem hrel]
          exact (hx (he.symm.trans hs)).elim
        · omega
  have hRunBase : ∀ (τ : Context) (a n : ℕ),
      τ.childPositions = List.range' a n → τ.bound = τ.base := by
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
    simp [Context.bound, Context.boundFuel, hruns]
  -- Repeated use of the proved base transport contracts any nonempty child block.
  have hBaseRun : ∀ (τ : Context) (L R : List Letter) (n : ℕ), 0 < n →
      τ.word = L ++ List.replicate n Letter.child ++ R →
      τ.base = ({ τ with word := L ++ [Letter.child] ++ R } : Context).base := by
    intro τ L R n hn hw
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    induction j generalizing τ with
    | zero => simpa using congrArg Context.base (show τ = { τ with word := L ++ [Letter.child] ++ R } by cases τ; simp_all)
    | succ j ih =>
      let ρ : Context := { τ with word := L ++ List.replicate (j + 1) Letter.child ++ R }
      have hstep := ctx_base_child_letter_contraction τ L
        (List.replicate j Letter.child ++ R) (by simpa [List.replicate_succ, List.append_assoc] using hw)
      have he : τ.base = ρ.base := by simpa [ρ, List.replicate_succ, List.append_assoc] using hstep
      exact he.trans (by simpa [ρ] using ih ρ (by omega) rfl)
  -- Repeated external-letter contraction is valid under the transported well-formedness proof.
  have hExternalRun : ∀ (τ : Context) (L R : List Letter) (n N : ℕ) (s : Side),
      τ.WellFormed → 0 < n → τ.word = L ++ List.replicate n (Letter.ext N s) ++ R →
      τ.bound = ({ τ with word := L ++ [Letter.ext N s] ++ R } : Context).bound := by
    intro τ L R n N s hτ hn hw
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    induction j generalizing τ with
    | zero => simpa using congrArg Context.bound (show τ = { τ with word := L ++ [Letter.ext N s] ++ R } by cases τ; simp_all)
    | succ j ih =>
      let ρ : Context := { τ with word := L ++ List.replicate (j + 1) (Letter.ext N s) ++ R }
      have hstep := ctx_bound_external_letter_contraction τ hτ L
        (List.replicate j (Letter.ext N s) ++ R) N s
        (by simpa [List.replicate_succ, List.append_assoc] using hw)
      have he : τ.bound = ρ.bound := by simpa [ρ, List.replicate_succ, List.append_assoc] using hstep
      have hρ : ρ.WellFormed := hWF τ _ hτ (by
        intro M t hx
        simpa [hw, ρ, List.mem_append, List.mem_replicate, Nat.succ_ne_zero] using hx)
      exact he.trans (by simpa [ρ] using ih ρ hρ (by omega) rfl)
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
    | ext N t => simp [replace, shift, he]
  have hMapRun : ∀ (n off : ℕ) keep s (x : Letter),
      (∀ i, i < n → (if i + off ∈ keep then Letter.child else Letter.ext 1 s) = x) →
      (List.replicate n Letter.child).mapIdx (fun i y ↦ replace keep s (i + off) y) =
        List.replicate n x := by
    intro n off keep s x h
    have hh : (List.replicate n Letter.child).mapIdx (fun i y ↦ replace keep s (i + off) y) =
        List.replicate (List.replicate n Letter.child).length x := by
      rw [List.mapIdx_eq_replicate_iff]
      intro i hi
      simpa [replace] using h i (by simpa using hi)
    simpa using hh
  have hPartThree : ∀ (τ : Context) (L R : List Letter) (x y z : ℕ) keep s n
      (A B C : Letter),
      (∀ t ∈ L ++ R, t ≠ Letter.child) →
      τ.word = L ++ List.replicate x Letter.child ++ List.replicate y Letter.child ++
        List.replicate z Letter.child ++ R →
      (∀ i, i < x → (if i + L.length ∈ keep then Letter.child else Letter.ext 1 s) = A) →
      (∀ i, i < y → (if i + (L.length + x) ∈ keep then Letter.child else Letter.ext 1 s) = B) →
      (∀ i, i < z → (if i + (L.length + x + y) ∈ keep then Letter.child else Letter.ext 1 s) = C) →
      (τ.part keep s n).word = L.map shift ++ List.replicate x A ++
        List.replicate y B ++ List.replicate z C ++ R.map shift := by
    intro τ L R x y z keep s n A B C hext hw hA hB hC
    rw [hPartMap, hw]
    simp only [List.mapIdx_append, List.length_append, List.length_replicate]
    have hL := hMapExt L keep s 0 (fun t ht ↦ hext t (List.mem_append_left _ ht))
    simp only [Nat.add_zero] at hL
    rw [hL, hMapExt R keep s _ (fun t ht ↦ hext t (List.mem_append_right _ ht)),
      hMapRun x L.length keep s A hA, hMapRun y (L.length + x) keep s B hB,
      hMapRun z (L.length + x + y) keep s C hC]
  -- Reconstruct the surrounding external words from the interval of child positions.
  have hmem : ∀ p, p ∈ σ.childPositions ↔ b ≤ p ∧ p < b + (l + m + r) := by
    intro p; rw [hpos, List.mem_range'_1]
  have hlen : b + (l + m + r) ≤ σ.word.length := by
    have hp : b + (l + m + r) - 1 ∈ σ.childPositions := (hmem _).mpr ⟨by omega, by omega⟩
    have := List.mem_range.mp (List.mem_filter.mp hp).1
    omega
  let L := σ.word.take b
  let R := σ.word.drop (b + (l + m + r))
  have hLlen : L.length = b := by simp [L, Nat.min_eq_left (show b ≤ σ.word.length by omega)]
  have hmid : (σ.word.drop b).take (l + m + r) = List.replicate (l + m + r) Letter.child := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp; omega, ?_⟩
    intro x hx
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < l + m + r := by simp only [List.length_take, List.length_drop] at hi; omega
    have hp : b + i ∈ σ.childPositions := (hmem _).mpr ⟨by omega, by omega⟩
    have hc : σ.letterAt (b + i) = Letter.child := of_decide_eq_true (List.mem_filter.mp hp).2
    simp only [List.getElem_take, List.getElem_drop] at he
    simpa [Context.letterAt, List.getElem?_eq_getElem (show b + i < σ.word.length by omega), he] using hc
  have hword : σ.word = L ++ List.replicate (l + m + r) Letter.child ++ R := by
    rw [← hmid]
    dsimp [L, R]
    rw [← List.take_add, List.take_append_drop]
  have houter : ∀ x ∈ L ++ R, x ≠ Letter.child := by
    intro x hx hc
    subst x
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
      have hib : i < b := by simpa [hLlen] using hi
      have hiw : i < σ.word.length := by omega
      have hlet : σ.letterAt i = Letter.child := by
        simpa [L, Context.letterAt, List.getElem?_eq_getElem hiw] using he
      have hp : i ∈ σ.childPositions := by simp [Context.childPositions, hiw, hlet]
      have := (hmem i).mp hp
      omega
    · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
      have hiw : b + (l + m + r) + i < σ.word.length := by
        simp only [R, List.length_drop] at hi; omega
      have hlet : σ.letterAt (b + (l + m + r) + i) = Letter.child := by
        simpa [R, Context.letterAt, List.getElem?_eq_getElem hiw] using he
      have hp : b + (l + m + r) + i ∈ σ.childPositions := by
        simp [Context.childPositions, hiw, hlet]
      have := (hmem _).mp hp
      omega
  let τ : Context := { σ with word := L ++ List.replicate (l + 1 + r) Letter.child ++ R }
  have hτwf : τ.WellFormed := hWF σ _ hwf (by
    intro N s hx
    simpa [τ, hword, List.mem_append, List.mem_replicate] using hx)
  have hτpos : τ.childPositions = List.range' b (l + 1 + r) := by
    simpa [hLlen] using hPositions τ L R (l + 1 + r) houter rfl
  have hparent : σ.bound = τ.bound := by
    rw [hRunBase σ b (l + m + r) hpos, hRunBase τ b (l + 1 + r) hτpos]
    exact (hBaseRun σ L R (l + m + r) (by omega) hword).trans
      (by simpa [τ] using (hBaseRun τ L R (l + 1 + r) (by omega) rfl).symm)
  have hWords : ∀ (ρ : Context) (x y z : ℕ),
      ρ.word = L ++ List.replicate x Letter.child ++ List.replicate y Letter.child ++
        List.replicate z Letter.child ++ R → ∀ s q,
      (ρ.part (List.range' b x ++ List.range' (b + x + y) z) s q).word =
        L.map shift ++ List.replicate x Letter.child ++ List.replicate y (Letter.ext 1 s) ++
          List.replicate z Letter.child ++ R.map shift ∧
      (ρ.part (List.range' (b + x) y) s q).word =
        L.map shift ++ List.replicate x (Letter.ext 1 s) ++ List.replicate y Letter.child ++
          List.replicate z (Letter.ext 1 s) ++ R.map shift := by
    intro ρ x y z hw s q
    constructor
    · apply hPartThree ρ L R x y z _ s q _ _ _ houter hw
      · intro i hi
        have hp : i + L.length ∈ List.range' b x ++ List.range' (b + x + y) z := by
          simp only [List.mem_append, List.mem_range'_1, hLlen]; omega
        simp [hp]
      · intro i hi
        have hp : i + (L.length + x) ∉ List.range' b x ++ List.range' (b + x + y) z := by
          simp only [List.mem_append, List.mem_range'_1, hLlen]; omega
        simp [hp]
      · intro i hi
        have hp : i + (L.length + x + y) ∈ List.range' b x ++ List.range' (b + x + y) z := by
          simp only [List.mem_append, List.mem_range'_1, hLlen]; omega
        simp [hp]
    · apply hPartThree ρ L R x y z _ s q _ _ _ houter hw
      · intro i hi
        have hp : i + L.length ∉ List.range' (b + x) y := by
          simp only [List.mem_range'_1, hLlen]; omega
        simp [hp]
      · intro i hi
        have hp : i + (L.length + x) ∈ List.range' (b + x) y := by
          simp only [List.mem_range'_1, hLlen]; omega
        simp [hp]
      · intro i hi
        have hp : i + (L.length + x + y) ∉ List.range' (b + x) y := by
          simp only [List.mem_range'_1, hLlen]; omega
        simp [hp]
  have hσwords := hWords σ l m r (by
    simpa only [List.replicate_add, List.append_assoc] using hword)
  have hτwords := hWords τ l 1 r (by
    dsimp [τ]
    simp only [List.replicate_add, List.replicate_one, List.append_assoc])
  have holder : ∀ x ∈ L.map shift ++ R.map shift, ∃ N s, 2 ≤ N ∧ x = Letter.ext N s := by
    intro x hx
    rw [← List.map_append] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hyc := houter y hy
    cases y with
    | child => exact (hyc rfl).elim
    | ext N s =>
      have hσmem : Letter.ext N s ∈ σ.word := by
        rw [hword]
        rcases List.mem_append.mp hy with hy | hy
        · simp [hy]
        · simp [hy]
      obtain ⟨p, hp⟩ := (hExtMem σ N s).mp hσmem
      have hN := (hwf.2.2.2.2.2 p N s hp).1
      exact ⟨N + 1, s, by omega, rfl⟩
  have hOuter : ∀ s q, 1 ≤ q → q ≤ σ.k - 2 →
      (σ.part (List.range' b l ++ List.range' (b + l + m) r) s q).bound =
        (τ.part (List.range' b l ++ List.range' (b + l + 1) r) s q).bound := by
    intro s q hq hqk
    let π := σ.part (List.range' b l ++ List.range' (b + l + m) r) s q
    have hc := hExternalRun π (L.map shift ++ List.replicate l Letter.child)
      (List.replicate r Letter.child ++ R.map shift) m 1 s (hwf.part _ s hq hqk) hm
      (by simpa only [List.append_assoc] using (hσwords s q).1)
    refine hc.trans ?_
    congr 1
    change _ = { π with word :=
      (τ.part (List.range' b l ++ List.range' (b + l + 1) r) s q).word }
    rw [(hτwords s q).1]
    simp only [List.replicate_one, List.append_assoc]
  have hMiddle : ∀ s q,
      (σ.part (List.range' (b + l) m) s q).bound = (τ.part [b + l] s q).bound := by
    intro s q
    let π := σ.part (List.range' (b + l) m) s q
    let υ := τ.part [b + l] s q
    let A := L.map shift ++ List.replicate l (Letter.ext 1 s)
    let B := List.replicate r (Letter.ext 1 s) ++ R.map shift
    have hab : ∀ x ∈ A ++ B, x ≠ Letter.child := by
      intro x hx
      have hx' : (x ∈ L.map shift ∨ (l ≠ 0 ∧ x = Letter.ext 1 s)) ∨
          ((r ≠ 0 ∧ x = Letter.ext 1 s) ∨ x ∈ R.map shift) := by
        simpa only [A, B, List.mem_append, List.mem_replicate] using hx
      rcases hx' with (hL | hx) | (hx | hR)
      · obtain ⟨N, t, _, rfl⟩ := holder x (List.mem_append_left _ hL)
        simp
      · rw [hx.2]; simp
      · rw [hx.2]; simp
      · obtain ⟨N, t, _, rfl⟩ := holder x (List.mem_append_right _ hR)
        simp
    have hπword : π.word = A ++ List.replicate m Letter.child ++ B := by
      simpa only [π, A, B, List.append_assoc] using (hσwords s q).2
    have hυword : υ.word = A ++ [Letter.child] ++ B := by
      simpa only [υ, A, B, List.range'_succ, List.range'_zero, List.replicate_one,
        List.append_assoc] using (hτwords s q).2
    have hπpos := hPositions π A B m hab hπword
    have hυpos := hPositions υ A B 1 hab (by simpa using hυword)
    rw [hRunBase π A.length m hπpos, hRunBase υ A.length 1 hυpos]
    have hc := hBaseRun π A B m hm hπword
    refine hc.trans ?_
    congr 1
    change _ = { π with word := υ.word }
    rw [hυword]
  change τ.WellFormed ∧ τ.childPositions = List.range' b (l + 1 + r) ∧
    σ.bound = τ.bound ∧ _
  exact ⟨hτwf, hτpos, hparent, fun s q hq hqk ↦ ⟨hOuter s q hq hqk, hMiddle s q⟩⟩

end ErdosSzekeres
