import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

/-- Exterior padding by external letters above the indexed history depth preserves every translated child endpoint limit, every fuel bound and the full recursive bound, without WellFormed or legality premises. Child positions shift by the prefix length. The constant order embedding transports all indexed extension walks and recursive cuts; padding remains unindexed after each part. Supplies literal erasure of the retained raw prefix in the R19 oldest-flank normalization explanation, without asserting feasible singleton selection or deleting internal separators.
@node
@ws B
@kind formalization
@dangling-ok Removes R19 retained-unindexed-exterior-padding obstruction in exact oldest-flank normalization; standalone transport is reusable without WellFormed. -/
theorem ctx_bound_eq_unindexed_padding : ∀ (σ : Ctx.Context) (left right : List Ctx.Letter),
  (∀ z ∈ left ++ right, ∃ N s, σ.maxima.length < N ∧ z = Ctx.Letter.ext N s) →
  let τ : Ctx.Context := { σ with word := left ++ σ.word ++ right }
  τ.childPositions = σ.childPositions.map (fun p => left.length + p) ∧
  (∀ p q, τ.cupLimit (left.length + p) (left.length + q) = σ.cupLimit p q ∧
    τ.capLimit (left.length + p) (left.length + q) = σ.capLimit p q) ∧
  (∀ fuel, Ctx.Context.boundFuel fuel τ = Ctx.Context.boundFuel fuel σ) ∧
  τ.bound = σ.bound := by
  classical
  let pad (σ : Ctx.Context) (L R : List Ctx.Letter) : Ctx.Context :=
    { σ with word := L ++ σ.word ++ R }
  have hRangeFilter : ∀ (a b c : ℕ) (P Q : ℕ → Bool),
      (∀ i, i < a → P i = false) →
      (∀ i, i < b → P (a + i) = Q i) →
      (∀ i, i < c → P (a + b + i) = false) →
      (List.range (a + b + c)).filter P =
        ((List.range b).filter Q).map (fun i => a + i) := by
    intro a b c P Q hL hM hR
    have hleft : (List.range a).filter P = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro i hi
      rw [hL i (List.mem_range.mp hi)]
      simp
    have hmiddle : ((List.range b).map (fun i => a + i)).filter P =
        ((List.range b).filter Q).map (fun i => a + i) := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro i hi
      exact hM i (List.mem_range.mp hi)
    have hright0 : (List.range c).filter (fun i => P (a + b + i)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro i hi
      rw [hR i (List.mem_range.mp hi)]
      simp
    have hright : ((List.range c).map (fun i => a + b + i)).filter P = [] := by
      simpa only [List.filter_map, Function.comp_def, hright0, List.map_nil]
    rw [List.range_add, List.filter_append, List.range_add, List.filter_append,
      hleft, hmiddle, hright]
    simp
  have hLeftLetter (σ : Ctx.Context) (L R : List Ctx.Letter) (i : ℕ)
      (hi : i < L.length) :
      (pad σ L R).letterAt i = (L[i]?).getD Ctx.Letter.child := by
    simp only [pad, Ctx.Context.letterAt, List.append_assoc]
    rw [List.getElem?_append_left hi]
  have hMiddleLetter (σ : Ctx.Context) (L R : List Ctx.Letter) (i : ℕ)
      (hi : i < σ.word.length) :
      (pad σ L R).letterAt (L.length + i) = σ.letterAt i := by
    simp only [pad, Ctx.Context.letterAt, List.append_assoc]
    rw [List.getElem?_append_right (show L.length ≤ L.length + i by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left hi]
  have hRightLetter (σ : Ctx.Context) (L R : List Ctx.Letter) (i : ℕ)
      (hi : i < R.length) :
      (pad σ L R).letterAt (L.length + σ.word.length + i) =
        (R[i]?).getD Ctx.Letter.child := by
    simp only [pad, Ctx.Context.letterAt]
    rw [List.getElem?_append_right
      (show (L ++ σ.word).length ≤ L.length + σ.word.length + i by
        simp only [List.length_append]; omega)]
    simp only [List.length_append, Nat.add_sub_cancel_left]
  have hPaddingLetters (σ : Ctx.Context) (L R : List Ctx.Letter)
      (hpad : ∀ z ∈ L ++ R, ∃ N s, σ.maxima.length < N ∧ z = Ctx.Letter.ext N s) :
      (∀ i, i < L.length → ∃ N s, σ.maxima.length < N ∧
        (pad σ L R).letterAt i = Ctx.Letter.ext N s) ∧
      (∀ i, i < R.length → ∃ N s, σ.maxima.length < N ∧
        (pad σ L R).letterAt (L.length + σ.word.length + i) = Ctx.Letter.ext N s) := by
    constructor
    · intro i hi
      have hm : (L[i]?).getD Ctx.Letter.child ∈ L := by
        rw [List.getElem?_eq_getElem hi, Option.getD_some]
        exact List.getElem_mem ..
      obtain ⟨N, s, hN, hz⟩ := hpad _ (List.mem_append_left R hm)
      exact ⟨N, s, hN, (hLeftLetter σ L R i hi).trans hz⟩
    · intro i hi
      have hm : (R[i]?).getD Ctx.Letter.child ∈ R := by
        rw [List.getElem?_eq_getElem hi, Option.getD_some]
        exact List.getElem_mem ..
      obtain ⟨N, s, hN, hz⟩ := hpad _ (List.mem_append_right L hm)
      exact ⟨N, s, hN, (hRightLetter σ L R i hi).trans hz⟩
  have hGeometry : ∀ (σ : Ctx.Context) (L R : List Ctx.Letter),
      (∀ z ∈ L ++ R, ∃ N s, σ.maxima.length < N ∧ z = Ctx.Letter.ext N s) →
      (pad σ L R).childPositions = σ.childPositions.map (fun i => L.length + i) ∧
      (∀ N, N ≤ σ.maxima.length → (pad σ L R).extPositions N =
        (σ.extPositions N).map (fun i => L.length + i)) ∧
      (pad σ L R).numRuns = σ.numRuns ∧
      (∀ N, N ≤ σ.maxima.length → (pad σ L R).sideAt N = σ.sideAt N) := by
    intro σ L R hpad
    have hlen : (pad σ L R).word.length = L.length + σ.word.length + R.length := by
      simp [pad, Nat.add_assoc]
    obtain ⟨hL, hR⟩ := hPaddingLetters σ L R hpad
    have hc : (pad σ L R).childPositions = σ.childPositions.map (fun i => L.length + i) := by
      unfold Ctx.Context.childPositions
      rw [hlen]
      apply hRangeFilter
      · intro i hi
        obtain ⟨N, s, _, hz⟩ := hL i hi
        simp [hz]
      · intro i hi
        rw [hMiddleLetter σ L R i hi]
      · intro i hi
        obtain ⟨N, s, _, hz⟩ := hR i hi
        simp [hz]
    have hext : ∀ N, N ≤ σ.maxima.length → (pad σ L R).extPositions N =
        (σ.extPositions N).map (fun i => L.length + i) := by
      intro N hN
      unfold Ctx.Context.extPositions
      rw [hlen]
      apply hRangeFilter
      · intro i hi
        obtain ⟨j, s, hj, hz⟩ := hL i hi
        have hjN : j ≠ N := by omega
        simp [hz, hjN]
      · intro i hi
        rw [hMiddleLetter σ L R i hi]
      · intro i hi
        obtain ⟨j, s, hj, hz⟩ := hR i hi
        have hjN : j ≠ N := by omega
        simp [hz, hjN]
    have hruns : (pad σ L R).numRuns = σ.numRuns := by
      unfold Ctx.Context.numRuns
      rw [hlen]
      have hflags : (List.range (L.length + σ.word.length + R.length)).filter
          (fun i => decide ((pad σ L R).letterAt i = Ctx.Letter.child ∧
            (i = 0 ∨ (pad σ L R).letterAt (i - 1) ≠ Ctx.Letter.child))) =
          ((List.range σ.word.length).filter (fun i => decide
            (σ.letterAt i = Ctx.Letter.child ∧
              (i = 0 ∨ σ.letterAt (i - 1) ≠ Ctx.Letter.child)))).map
            (fun i => L.length + i) := by
        apply hRangeFilter
        · intro i hi
          obtain ⟨N, s, _, hz⟩ := hL i hi
          simp [hz]
        · intro i hi
          rw [hMiddleLetter σ L R i hi]
          by_cases hi0 : i = 0
          · subst i
            by_cases hL0 : L.length = 0
            · simp [hL0]
            · have hprev : L.length - 1 < L.length := by omega
              obtain ⟨N, s, _, hz⟩ := hL (L.length - 1) hprev
              simp [hz]
          · have hip : i - 1 < σ.word.length := by omega
            have heq : L.length + i - 1 = L.length + (i - 1) := by omega
            have hne : L.length + i ≠ 0 := by omega
            rw [heq, hMiddleLetter σ L R (i - 1) hip]
            simp [hi0, hne]
        · intro i hi
          obtain ⟨N, s, _, hz⟩ := hR i hi
          simp [hz]
      rw [hflags, List.length_map]
    have hsides : ∀ N, N ≤ σ.maxima.length → (pad σ L R).sideAt N = σ.sideAt N := by
      intro N hN
      unfold Ctx.Context.sideAt
      rw [hext N hN, List.head?_map]
      cases hh : (σ.extPositions N).head? with
      | none => rfl
      | some p =>
        simp only [Option.map_some]
        have hp : p < σ.word.length :=
          List.mem_range.mp (List.mem_filter.mp (List.mem_of_mem_head? hh)).1
        rw [hMiddleLetter σ L R p hp]
    exact ⟨hc, hext, hruns, hsides⟩
  have hLevelBound (σ : Ctx.Context) (N : ℕ) (hN : N ∈ σ.levels) :
      N ≤ σ.maxima.length := by
    unfold Ctx.Context.levels at hN
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hN
    have hi' := List.mem_range.mp hi
    omega
  have hLimits : ∀ (σ : Ctx.Context) (L R : List Ctx.Letter),
      (∀ z ∈ L ++ R, ∃ N s, σ.maxima.length < N ∧ z = Ctx.Letter.ext N s) →
      ∀ p q, (pad σ L R).cupLimit (L.length + p) (L.length + q) = σ.cupLimit p q ∧
        (pad σ L R).capLimit (L.length + p) (L.length + q) = σ.capLimit p q := by
    intro σ L R hpad
    have hg := hGeometry σ L R hpad
    have hext := hg.2.1
    have hside := hg.2.2.2
    have hOn (s : Ctx.Side) (top : ℕ) :
        (pad σ L R).levelsOn s top = σ.levelsOn s top := by
      unfold Ctx.Context.levelsOn
      have hl : (pad σ L R).levels = σ.levels := rfl
      rw [hl]
      apply List.filter_congr
      intro N hN
      rw [hside N (hLevelBound σ N hN)]
    have hSteps (e c N : ℕ) (hN : N ≤ σ.maxima.length) :
        Ctx.Context.leftStep (pad σ L R) (L.length + e, c) N =
          (L.length + (Ctx.Context.leftStep σ (e, c) N).1,
            (Ctx.Context.leftStep σ (e, c) N).2) ∧
        Ctx.Context.rightStep (pad σ L R) (L.length + e, c) N =
          (L.length + (Ctx.Context.rightStep σ (e, c) N).1,
            (Ctx.Context.rightStep σ (e, c) N).2) := by
      constructor
      · unfold Ctx.Context.leftStep
        dsimp only
        rw [hext N hN, List.filter_map]
        simp only [Function.comp_def, Nat.add_lt_add_iff_left]
        rw [List.getLast?_map]
        cases h : ((σ.extPositions N).filter (fun i => decide (i < e))).getLast? <;>
          simp [h]
      · unfold Ctx.Context.rightStep
        dsimp only
        rw [hext N hN, List.filter_map]
        simp only [Function.comp_def, Nat.add_lt_add_iff_left]
        rw [List.head?_map]
        cases h : ((σ.extPositions N).filter (fun i => decide (e < i))).head? <;>
          simp [h]
    have hFolds : ∀ ls : List ℕ, (∀ N ∈ ls, N ≤ σ.maxima.length) → ∀ e c,
        ls.foldl (Ctx.Context.leftStep (pad σ L R)) (L.length + e, c) =
          (L.length + (ls.foldl (Ctx.Context.leftStep σ) (e, c)).1,
            (ls.foldl (Ctx.Context.leftStep σ) (e, c)).2) ∧
        ls.foldl (Ctx.Context.rightStep (pad σ L R)) (L.length + e, c) =
          (L.length + (ls.foldl (Ctx.Context.rightStep σ) (e, c)).1,
            (ls.foldl (Ctx.Context.rightStep σ) (e, c)).2) := by
      intro ls
      induction ls with
      | nil => intro _ e c; exact ⟨rfl, rfl⟩
      | cons N ls ih =>
        intro hNs e c
        have hN := hNs N (List.mem_cons_self ..)
        have htail : ∀ j ∈ ls, j ≤ σ.maxima.length :=
          fun j hj => hNs j (List.mem_cons_of_mem _ hj)
        constructor
        · rw [List.foldl_cons, (hSteps e c N hN).1]
          exact (ih htail (Ctx.Context.leftStep σ (e, c) N).1
            (Ctx.Context.leftStep σ (e, c) N).2).1
        · rw [List.foldl_cons, (hSteps e c N hN).2]
          exact (ih htail (Ctx.Context.rightStep σ (e, c) N).1
            (Ctx.Context.rightStep σ (e, c) N).2).2
    have hExt (s : Ctx.Side) (top p : ℕ) :
        (pad σ L R).leftExt s top (L.length + p) = σ.leftExt s top p ∧
        (pad σ L R).rightExt s top (L.length + p) = σ.rightExt s top p := by
      have hmaps : ∀ ls ∈ (σ.levelsOn s top).sublists,
          (ls.foldl (Ctx.Context.leftStep (pad σ L R)) (L.length + p, 0)).2 =
            (ls.foldl (Ctx.Context.leftStep σ) (p, 0)).2 ∧
          (ls.foldl (Ctx.Context.rightStep (pad σ L R)) (L.length + p, 0)).2 =
            (ls.foldl (Ctx.Context.rightStep σ) (p, 0)).2 := by
        intro ls hls
        have hsub := List.mem_sublists.mp hls
        have hb : ∀ N ∈ ls, N ≤ σ.maxima.length := by
          intro N hN
          exact hLevelBound σ N (List.mem_filter.mp (hsub.subset hN)).1
        have hf := hFolds ls hb p 0
        have hl := congrArg (fun st : ℕ × ℕ => st.2) hf.1
        have hr := congrArg (fun st : ℕ × ℕ => st.2) hf.2
        exact ⟨hl, hr⟩
      constructor
      · rw [Ctx.Context.leftExt_eq, Ctx.Context.leftExt_eq, hOn]
        congr 2
        exact List.map_congr_left (fun ls hls => (hmaps ls hls).1)
      · rw [Ctx.Context.rightExt_eq, Ctx.Context.rightExt_eq, hOn]
        congr 2
        exact List.map_congr_left (fun ls hls => (hmaps ls hls).2)
    have hChain (s : Ctx.Side) (p q : ℕ) :
        (pad σ L R).chainExt s (L.length + p) (L.length + q) = σ.chainExt s p q := by
      unfold Ctx.Context.chainExt
      rw [(hExt s 0 p).1, (hExt s 0 q).2]
    have hJoin (s : Ctx.Side) (p q : ℕ) :
        (pad σ L R).joinExt s (L.length + p) (L.length + q) = σ.joinExt s p q := by
      unfold Ctx.Context.joinExt
      rw [hChain, hOn]
      congr 3
      apply List.map_congr_left
      intro N hN
      rw [(hExt s N p).1, (hExt s N q).2]
      rfl
    intro p q
    constructor
    · simp only [Ctx.Context.cupLimit, hChain, hJoin]
      rfl
    · simp only [Ctx.Context.capLimit, hChain, hJoin]
      rfl
  let bump : Ctx.Letter → Ctx.Letter := fun z => match z with
    | Ctx.Letter.child => Ctx.Letter.child
    | Ctx.Letter.ext N s => Ctx.Letter.ext (N + 1) s
  have hMapMem (c : ℕ) (A : List ℕ) (i : ℕ) :
      c + i ∈ A.map (fun j => c + j) ↔ i ∈ A := by
    constructor
    · intro h
      obtain ⟨j, hj, heq⟩ := List.mem_map.mp h
      have hji : j = i := Nat.add_left_cancel heq
      simpa [hji] using hj
    · exact List.mem_map_of_mem
  have hLookupMap (A : List Ctx.Letter) (f : Ctx.Letter → Ctx.Letter) :
      (List.range A.length).map (fun i => f ((A[i]?).getD Ctx.Letter.child)) = A.map f := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hin : i < A.length := by simpa using hi
      simp only [List.getElem_map, List.getElem_range, List.getElem?_eq_getElem hin,
        Option.getD_some]
  have hPart : ∀ (σ : Ctx.Context) (L R : List Ctx.Letter),
      (∀ z ∈ L ++ R, ∃ N s, σ.maxima.length < N ∧ z = Ctx.Letter.ext N s) →
      ∀ (A : List ℕ) (t : Ctx.Side) (m : ℕ),
      (pad σ L R).part (A.map (fun i => L.length + i)) t m =
        pad (σ.part A t m) (L.map bump) (R.map bump) := by
    intro σ L R hpad A t m
    obtain ⟨hL, hR⟩ := hPaddingLetters σ L R hpad
    let f : ℕ → Ctx.Letter := fun i => match (pad σ L R).letterAt i with
      | Ctx.Letter.child => if i ∈ A.map (fun j => L.length + j) then Ctx.Letter.child
          else Ctx.Letter.ext 1 t
      | Ctx.Letter.ext N s => Ctx.Letter.ext (N + 1) s
    let g : ℕ → Ctx.Letter := fun i => match σ.letterAt i with
      | Ctx.Letter.child => if i ∈ A then Ctx.Letter.child else Ctx.Letter.ext 1 t
      | Ctx.Letter.ext N s => Ctx.Letter.ext (N + 1) s
    have hleft : (List.range L.length).map f = L.map bump := by
      calc
        _ = (List.range L.length).map (fun i => bump ((L[i]?).getD Ctx.Letter.child)) := by
          apply List.map_congr_left
          intro i hi
          have hin := List.mem_range.mp hi
          obtain ⟨N, s, _, hz⟩ := hL i hin
          rw [← hLeftLetter σ L R i hin]
          simp only [f, hz, bump]
        _ = _ := hLookupMap L bump
    have hmiddle : ((List.range σ.word.length).map (fun i => L.length + i)).map f =
        (σ.part A t m).word := by
      rw [List.map_map]
      change (List.range σ.word.length).map (fun i => f (L.length + i)) =
        (List.range σ.word.length).map g
      apply List.map_congr_left
      intro i hi
      dsimp only [f, g]
      rw [hMiddleLetter σ L R i (List.mem_range.mp hi)]
      cases h : σ.letterAt i <;> simp only [h, hMapMem]
    have hright : ((List.range R.length).map (fun i => L.length + σ.word.length + i)).map f =
        R.map bump := by
      rw [List.map_map]
      calc
        _ = (List.range R.length).map (fun i => bump ((R[i]?).getD Ctx.Letter.child)) := by
          apply List.map_congr_left
          intro i hi
          have hin := List.mem_range.mp hi
          obtain ⟨N, s, _, hz⟩ := hR i hin
          rw [← hRightLetter σ L R i hin]
          simp only [Function.comp_def, f, hz, bump]
        _ = _ := hLookupMap R bump
    have hword : ((pad σ L R).part (A.map (fun i => L.length + i)) t m).word =
        L.map bump ++ (σ.part A t m).word ++ R.map bump := by
      change (List.range (pad σ L R).word.length).map f = _
      have hlen : (pad σ L R).word.length = L.length + σ.word.length + R.length := by
        simp [pad, Nat.add_assoc]
      rw [hlen, List.range_add, List.map_append, List.range_add, List.map_append,
        hleft, hmiddle, hright]
    have hctx := congrArg (fun w : List Ctx.Letter =>
      Ctx.Context.mk σ.a σ.u σ.k w (m :: σ.maxima)) hword
    exact hctx
  have hPaddingPart (σ : Ctx.Context) (L R : List Ctx.Letter)
      (hpad : ∀ z ∈ L ++ R, ∃ N s, σ.maxima.length < N ∧ z = Ctx.Letter.ext N s)
      (A : List ℕ) (t : Ctx.Side) (m : ℕ) :
      ∀ z ∈ L.map bump ++ R.map bump,
        ∃ N s, (σ.part A t m).maxima.length < N ∧ z = Ctx.Letter.ext N s := by
    intro z hz
    rw [← List.map_append] at hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    obtain ⟨N, s, hN, rfl⟩ := hpad y hy
    refine ⟨N + 1, s, ?_, rfl⟩
    simpa only [Ctx.Context.part_maxima, List.length_cons] using Nat.add_lt_add_right hN 1
  have hBase (σ : Ctx.Context) (L R : List Ctx.Letter)
      (hpad : ∀ z ∈ L ++ R, ∃ N s, σ.maxima.length < N ∧ z = Ctx.Letter.ext N s) :
      (pad σ L R).base = σ.base := by
    unfold Ctx.Context.base
    rw [(hGeometry σ L R hpad).1, List.head?_map]
    cases hh : σ.childPositions.head? with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [(hLimits σ L R hpad p p).1, (hLimits σ L R hpad p p).2] <;> rfl
  have hRest (c : ℕ) (A B : List ℕ) :
      (A.map (fun i => c + i)).filter (fun i => decide (i ∉ B.map (fun j => c + j))) =
        (A.filter (fun i => decide (i ∉ B))).map (fun i => c + i) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro i hi
    change decide (c + i ∉ B.map (fun j => c + j)) = decide (i ∉ B)
    simp only [hMapMem]
  have hBlocks (σ : Ctx.Context) (L R : List Ctx.Letter)
      (hpad : ∀ z ∈ L ++ R, ∃ N s, σ.maxima.length < N ∧ z = Ctx.Letter.ext N s) :
      (pad σ L R).blocks = σ.blocks.map (fun A => A.map (fun i => L.length + i)) := by
    simp only [Ctx.Context.blocks, (hGeometry σ L R hpad).1, List.length_map]
    have hraw : ((List.range σ.childPositions.length).flatMap fun i =>
          (List.range (σ.childPositions.length - i)).map fun len =>
            ((σ.childPositions.map (fun j => L.length + j)).drop i).take (len + 1)) =
        ((List.range σ.childPositions.length).flatMap fun i =>
          (List.range (σ.childPositions.length - i)).map fun len =>
            (σ.childPositions.drop i).take (len + 1)).map
              (fun A => A.map (fun i => L.length + i)) := by
      rw [List.map_flatMap]
      apply List.flatMap_congr
      intro i hi
      rw [List.map_map]
      apply List.map_congr_left
      intro len hlen
      simp [Function.comp_def, List.map_take, List.map_drop]
    rw [hraw, List.filter_map]
    congr 1
    apply List.filter_congr
    intro A hA
    simp [Function.comp_def]
  have hFuel : ∀ fuel (σ : Ctx.Context) (L R : List Ctx.Letter),
      (∀ z ∈ L ++ R, ∃ N s, σ.maxima.length < N ∧ z = Ctx.Letter.ext N s) →
      Ctx.Context.boundFuel fuel (pad σ L R) = Ctx.Context.boundFuel fuel σ := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro σ L R hpad
      have hg := hGeometry σ L R hpad
      have hparts : ∀ (A : List ℕ) (t : Ctx.Side) (m : ℕ),
          Ctx.Context.boundFuel fuel ((pad σ L R).part (A.map (fun i => L.length + i)) t m) =
            Ctx.Context.boundFuel fuel (σ.part A t m) := by
        intro A t m
        rw [hPart σ L R hpad A t m]
        exact ih (σ.part A t m) (L.map bump) (R.map bump) (hPaddingPart σ L R hpad A t m)
      rw [Ctx.Context.boundFuel.eq_2, Ctx.Context.boundFuel.eq_2, hg.2.2.1]
      by_cases hrun : σ.numRuns ≤ 1
      · simp only [if_pos hrun]
        exact hBase σ L R hpad
      · simp only [if_neg hrun]
        have hk : (pad σ L R).k = σ.k := rfl
        rw [hg.1, hBlocks σ L R hpad, hk, List.flatMap_map]
        congr 2
        apply List.flatMap_congr
        intro A hA
        rw [hRest]
        apply List.flatMap_congr
        intro d hd
        rw [hparts A Ctx.Side.lower (d + 1),
          hparts (σ.childPositions.filter (fun i => decide (i ∉ A))) Ctx.Side.upper
            (σ.k - 1 - (d + 1)),
          hparts A Ctx.Side.upper (σ.k - 1 - (d + 1)),
          hparts (σ.childPositions.filter (fun i => decide (i ∉ A))) Ctx.Side.lower (d + 1)]
  intro σ left right hpad
  refine ⟨(hGeometry σ left right hpad).1, hLimits σ left right hpad,
    fun fuel => hFuel fuel σ left right hpad, ?_⟩
  unfold Ctx.Context.bound
  rw [(hGeometry σ left right hpad).1, List.length_map]
  exact hFuel (σ.childPositions.length + 1) σ left right hpad

end ErdosSzekeres
