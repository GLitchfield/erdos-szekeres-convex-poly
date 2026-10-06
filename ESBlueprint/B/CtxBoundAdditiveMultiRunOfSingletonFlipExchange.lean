import ESBlueprint.B.CtxBoundIntervalOrComplementLe

namespace ErdosSzekeres

/-- Conditional multi-run additivity from an explicit singleton-flip exchange hypothesis for the fixed context. Strong induction on the number of maximal membership segments in child order reduces an interior singleton by two segments or an end singleton by one; partitions with at most three segments have an interval side and are bounded by ctx_bound_cut_le. No proof of the exchange is assumed as a theorem. This conditional remains logically separate from the R15 singleton-existence obstruction at eight children.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_cut_le, ErdosSzekeres.ctx_bound_interval_or_complement_le
@consumer ErdosSzekeres.ctx_bound_additive_multi_run
@measure number of maximal membership segments in child order -/
theorem ctx_bound_additive_multi_run_of_singleton_flip_exchange (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns)
    (hflip : ∀ (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
    (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length)
    (hinter : σ.childPositions.filter (fun p ↦ p ∈ keep) ∉ σ.blocks)
    (hco : σ.childPositions.filter (fun p ↦ p ∉ keep) ∉ σ.blocks)
    (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) (o : Bool),
    let value := fun (K : List ℕ) (e : ℕ) (b : Bool) ↦
      if b then
        (σ.part K Ctx.Side.upper (σ.k - 1 - e)).bound +
          (σ.part (σ.childPositions.filter (fun p ↦ p ∉ K)) Ctx.Side.lower e).bound
      else
        (σ.part K Ctx.Side.lower e).bound +
          (σ.part (σ.childPositions.filter (fun p ↦ p ∉ K))
            Ctx.Side.upper (σ.k - 1 - e)).bound
    ∃ i : Fin σ.childPositions.length,
      (∀ j : Fin σ.childPositions.length,
        j.val + 1 = i.val ∨ i.val + 1 = j.val →
          (σ.childPositions[j] ∈ keep ↔ σ.childPositions[i] ∉ keep)) ∧
      ∃ e : ℕ, 1 ≤ e ∧ e ≤ σ.k - 2 ∧ ∃ b : Bool,
        value keep d o ≤ value
          (σ.childPositions.filter (fun p ↦
            (p ∈ keep ∧ p ≠ σ.childPositions[i]) ∨
              (p ∉ keep ∧ p = σ.childPositions[i]))) e b)
    (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
    (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length)
    (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) :
    (σ.part keep Ctx.Side.lower d).bound +
        (σ.part (σ.childPositions.filter (fun p ↦ p ∉ keep))
          Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧
      (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound +
        (σ.part (σ.childPositions.filter (fun p ↦ p ∉ keep))
          Ctx.Side.lower d).bound ≤ σ.bound := by
  classical
  let changes : List Bool → ℕ := fun xs ↦
    (List.zipWith (fun a b ↦ a != b) xs xs.tail).countP id
  let transitionsFrom : Bool → List Bool → ℕ := fun b xs ↦ changes (b :: xs)
  have hstep : ∀ (a b : Bool) (xs : List Bool),
      transitionsFrom a (b :: xs) = transitionsFrom b xs + if a = b then 0 else 1 := by
    intro a b xs
    cases a <;> cases b <;> simp [transitionsFrom, changes]
  have hcons : ∀ (a b : Bool) (xs : List Bool),
      changes (a :: b :: xs) = changes (b :: xs) + if a = b then 0 else 1 := by
    intro a b xs
    exact hstep a b xs
  have hhead : ∀ (xs : List Bool) (b : Bool),
      xs.head? = some b → changes xs = transitionsFrom b xs := by
    intro xs b hh
    cases xs with
    | nil => simp at hh
    | cons c xs =>
      have hcb : c = b := by simpa using hh
      subst b
      change transitionsFrom c xs = transitionsFrom c (c :: xs)
      rw [hstep]
      simp
  have hzero : ∀ (f : ℕ → Bool) (ps : List ℕ) (b : Bool),
      transitionsFrom b (ps.map f) = 0 ↔ ∀ q ∈ ps, f q = b := by
    intro f ps
    induction ps with
    | nil => intro b; simp [transitionsFrom, changes]
    | cons p ps ih =>
      intro b
      rw [List.map_cons, hstep]
      by_cases h : b = f p
      · rw [if_pos h, Nat.add_zero, ih]
        constructor
        · intro hall q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact h.symm
          · exact (hall q hq).trans h.symm
        · intro hall q hq
          exact (hall q (by simp [hq])).trans h
      · rw [if_neg h]
        constructor
        · intro hz; omega
        · intro hall
          exact (h (hall p (by simp)).symm).elim
  have hone : ∀ (f : ℕ → Bool) (ps : List ℕ) (b : Bool),
      transitionsFrom b (ps.map f) ≤ 1 →
      ∃ L R : List ℕ, ps = L ++ R ∧
        (∀ q ∈ L, f q = b) ∧ (∀ q ∈ R, f q = !b) := by
    intro f ps
    induction ps with
    | nil => intro b hc; exact ⟨[], [], rfl, by simp, by simp⟩
    | cons p ps ih =>
      intro b hc
      by_cases h : b = f p
      · rw [List.map_cons, hstep, if_pos h, Nat.add_zero] at hc
        rcases ih (f p) hc with ⟨L, R, heq, hL, hR⟩
        refine ⟨p :: L, R, by simp [heq], ?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact h.symm
          · exact (hL q hq).trans h.symm
        · intro q hq
          simpa [h] using hR q hq
      · rw [List.map_cons, hstep, if_neg h] at hc
        have hz : transitionsFrom (f p) (ps.map f) = 0 := by omega
        have hopp : f p = !b := by
          cases hb : b <;> cases hp : f p
          · exact (h (hb.trans hp.symm)).elim
          · rfl
          · rfl
          · exact (h (hb.trans hp.symm)).elim
        refine ⟨[], p :: ps, by simp, by simp, ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hopp
        · exact ((hzero f ps (f p)).1 hz q hq).trans hopp
  have htwo : ∀ (f : ℕ → Bool) (ps : List ℕ) (b : Bool),
      transitionsFrom b (ps.map f) ≤ 2 →
      ∃ L B R : List ℕ, ps = L ++ B ++ R ∧
        (∀ q ∈ L, f q = b) ∧ (∀ q ∈ B, f q = !b) ∧ (∀ q ∈ R, f q = b) := by
    intro f ps
    induction ps with
    | nil => intro b hc; exact ⟨[], [], [], rfl, by simp, by simp, by simp⟩
    | cons p ps ih =>
      intro b hc
      by_cases h : b = f p
      · rw [List.map_cons, hstep, if_pos h, Nat.add_zero] at hc
        rcases ih (f p) hc with ⟨L, B, R, heq, hL, hB, hR⟩
        refine ⟨p :: L, B, R, by simp [heq], ?_, ?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact h.symm
          · exact (hL q hq).trans h.symm
        · intro q hq; simpa [h] using hB q hq
        · intro q hq; exact (hR q hq).trans h.symm
      · rw [List.map_cons, hstep, if_neg h] at hc
        have hc' : transitionsFrom (f p) (ps.map f) ≤ 1 := by omega
        have hopp : f p = !b := by
          cases hb : b <;> cases hp : f p
          · exact (h (hb.trans hp.symm)).elim
          · rfl
          · rfl
          · exact (h (hb.trans hp.symm)).elim
        rcases hone f ps (f p) hc' with ⟨B, R, heq, hB, hR⟩
        refine ⟨[], p :: B, R, by simp [heq], by simp, ?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hopp
          · exact (hB q hq).trans hopp
        · intro q hq; simpa [hopp] using hR q hq
  have hsingle : ∀ (L R : List Bool) (b : Bool),
      (∀ c, L.getLast? = some c → c = !b) →
      (∀ c, R.head? = some c → c = !b) → (L ≠ [] ∨ R ≠ []) →
      changes (L ++ (!b) :: R) + 1 ≤ changes (L ++ b :: R) ∧
        changes (L ++ b :: R) ≤ changes (L ++ (!b) :: R) + 2 := by
    intro L
    induction L with
    | nil =>
      intro R b hL hR hne
      cases R with
      | nil => simp at hne
      | cons c R =>
        have hcb : c = !b := hR c rfl
        subst c
        cases b <;> simp [changes] <;> omega
    | cons a L ih =>
      intro R b hL hR hne
      cases L with
      | nil =>
        have hab : a = !b := hL a rfl
        subst a
        cases R with
        | nil => cases b <;> simp [changes]
        | cons c R =>
          have hcb : c = !b := hR c rfl
          subst c
          cases b <;> simp [changes] <;> omega
      | cons c L =>
        have hL' : ∀ x, (c :: L).getLast? = some x → x = !b := by
          intro x hx
          apply hL x
          simpa using hx
        have ht := ih R b hL' hR (Or.inl (by simp))
        simp only [List.cons_append, hcons] at ht ⊢
        omega
  have hblock : ∀ (L B R : List ℕ), σ.childPositions = L ++ B ++ R →
      B ≠ [] → B.length < σ.childPositions.length → B ∈ σ.blocks := by
    intro L B R heq hne hlt
    have hpos : 0 < B.length := List.length_pos_iff.mpr hne
    have hlen : σ.childPositions.length = L.length + B.length + R.length := by
      simp [heq, Nat.add_assoc]
    have hadd : B.length - 1 + 1 = B.length := by omega
    unfold Ctx.Context.blocks
    simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
      decide_eq_true_eq]
    refine ⟨⟨L.length, by omega, B.length - 1, by omega, ?_⟩, hlt⟩
    simp [heq, List.append_assoc, hadd]
  have hpart : ∀ (K L : List ℕ),
      (∀ p ∈ σ.childPositions, p ∈ K ↔ p ∈ L) →
      ∀ s m, σ.part K s m = σ.part L s m := by
    intro K L h s m
    unfold Ctx.Context.part
    congr 1
    apply List.map_congr_left
    intro p hp
    rcases hletter : σ.letterAt p with _ | ⟨level, side⟩
    · have hpchild : p ∈ σ.childPositions := by
        simp [Ctx.Context.childPositions, List.mem_range.1 hp, hletter]
      simp [h p hpchild]
    · simp
  have hconstant : ∀ (f : ℕ → Bool) (ps : List ℕ) (b : Bool),
      (∀ q ∈ ps, f q = b) → changes (ps.map f) = 0 := by
    intro f ps b hall
    cases ps with
    | nil => simp [changes]
    | cons p ps =>
      have hp : f p = b := hall p (by simp)
      rw [hhead ((p :: ps).map f) (f p) (by simp), hp]
      exact (hzero f (p :: ps) b).2 hall
  have hcanonical : ∀ (P : ℕ → Bool),
      σ.childPositions.filter (fun p ↦ p ∈ σ.childPositions.filter P) =
        σ.childPositions.filter P := by
    intro P
    apply List.filter_congr
    intro p hp
    simp [hp]
  have hproper : ∀ (K : List ℕ),
      0 < changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) →
      σ.childPositions.filter (fun p ↦ p ∈ K) ≠ [] ∧
        (σ.childPositions.filter (fun p ↦ p ∈ K)).length < σ.childPositions.length := by
    intro K hc
    constructor
    · intro hnil
      have hz := hconstant (fun p ↦ decide (p ∈ K)) σ.childPositions false (by
        intro p hp
        have h := (List.filter_eq_nil_iff.1 hnil) p hp
        simpa using h)
      omega
    · have hle : (σ.childPositions.filter (fun p ↦ p ∈ K)).length ≤
          σ.childPositions.length := List.length_filter_le _ _
      by_contra hnot
      have heq : (σ.childPositions.filter (fun p ↦ p ∈ K)).length =
          σ.childPositions.length := by omega
      have hz := hconstant (fun p ↦ decide (p ∈ K)) σ.childPositions true (by
        intro p hp
        exact (List.length_filter_eq_length_iff.1 heq) p hp)
      omega
  have hpartition : ∀ (K : List ℕ),
      (∀ p ∈ K, p ∈ σ.childPositions) → K ≠ [] → K.length < σ.childPositions.length →
      σ.childPositions.filter (fun p ↦ p ∈ K) ≠ [] ∧
      (σ.childPositions.filter (fun p ↦ p ∈ K)).length < σ.childPositions.length ∧
      σ.childPositions.filter (fun p ↦ p ∉ K) ≠ [] ∧
      (σ.childPositions.filter (fun p ↦ p ∉ K)).length < σ.childPositions.length := by
    intro K hK hne hlt
    have hkn : σ.childPositions.filter (fun p ↦ p ∈ K) ≠ [] := by
      intro hnil
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil K hne
      have hmem : p ∈ σ.childPositions.filter (fun p ↦ p ∈ K) := by
        simp [hK p hp, hp]
      simpa [hnil] using hmem
    have hkl : (σ.childPositions.filter (fun p ↦ p ∈ K)).length <
        σ.childPositions.length :=
      (Ctx.Context.length_filter_mem_le (Ctx.Context.childPositions_nodup σ)).trans_lt hlt
    have hcn : σ.childPositions.filter (fun p ↦ p ∉ K) ≠ [] := by
      intro hnil
      have hall : ∀ p ∈ σ.childPositions, p ∈ K := by
        intro p hp
        have h := (List.filter_eq_nil_iff.1 hnil) p hp
        simpa using h
      have heq : σ.childPositions.filter (fun p ↦ p ∈ K) = σ.childPositions :=
        List.filter_eq_self.2 (by simpa using hall)
      rw [heq] at hkl
      omega
    exact ⟨hkn, hkl, hcn, Ctx.Context.length_filter_not_mem_lt hne hK⟩
  have hbase : ∀ (K : List ℕ),
      (∀ p ∈ K, p ∈ σ.childPositions) → K ≠ [] → K.length < σ.childPositions.length →
      changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) ≤ 2 →
      σ.childPositions.filter (fun p ↦ p ∈ K) ∈ σ.blocks ∨
        σ.childPositions.filter (fun p ↦ p ∉ K) ∈ σ.blocks := by
    intro K hK hne hlt hc
    obtain ⟨hkn, hkl, hcn, hcl⟩ := hpartition K hK hne hlt
    let f : ℕ → Bool := fun p ↦ decide (p ∈ K)
    cases hps : σ.childPositions with
    | nil => simp [hps] at hkn
    | cons p ps =>
      have hh : (σ.childPositions.map f).head? = some (f p) := by simp [hps]
      have hc' : transitionsFrom (f p) (σ.childPositions.map f) ≤ 2 := by
        rw [← hhead _ _ hh]
        exact hc
      obtain ⟨L, B, R, heq, hL, hB, hR⟩ := htwo f σ.childPositions (f p) hc'
      have hfiltered : σ.childPositions.filter (fun q ↦ f q != f p) = B := by
        have hLf : L.filter (fun q ↦ f q != f p) = [] :=
          List.filter_eq_nil_iff.2 (by
            intro q hq
            simp [hL q hq])
        have hRf : R.filter (fun q ↦ f q != f p) = [] :=
          List.filter_eq_nil_iff.2 (by
            intro q hq
            simp [hR q hq])
        have hBf : B.filter (fun q ↦ f q != f p) = B :=
          List.filter_eq_self.2 (by
            intro q hq
            cases hb : f p <;> simp [hB q hq, hb])
        rw [heq, List.filter_append, List.filter_append, hLf, hBf, hRf]
        simp
      cases hb : f p with
      | false =>
        have hKB : σ.childPositions.filter (fun q ↦ q ∈ K) = B := by
          rw [← hfiltered]
          apply List.filter_congr
          intro q hq
          rw [hb]
          simp [f]
        left
        rw [← hps, hKB]
        exact hblock L B R heq (by simpa only [hKB] using hkn)
          (by simpa only [hKB] using hkl)
      | true =>
        have hCB : σ.childPositions.filter (fun q ↦ q ∉ K) = B := by
          rw [← hfiltered]
          apply List.filter_congr
          intro q hq
          rw [hb]
          simp [f]
        right
        rw [← hps, hCB]
        exact hblock L B R heq (by simpa only [hCB] using hcn)
          (by simpa only [hCB] using hcl)
  have htoggle : ∀ (K : List ℕ) (i : Fin σ.childPositions.length),
      (∀ j : Fin σ.childPositions.length,
        j.val + 1 = i.val ∨ i.val + 1 = j.val →
          (σ.childPositions[j] ∈ K ↔ σ.childPositions[i] ∉ K)) →
      3 ≤ changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) →
      let newK := σ.childPositions.filter (fun p ↦
        (p ∈ K ∧ p ≠ σ.childPositions[i]) ∨ (p ∉ K ∧ p = σ.childPositions[i]))
      changes (σ.childPositions.map (fun p ↦ decide (p ∈ newK))) + 1 ≤
        changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) ∧
      changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) ≤
        changes (σ.childPositions.map (fun p ↦ decide (p ∈ newK))) + 2 := by
    intro K i hadj hc
    let p := σ.childPositions[i]
    let L := σ.childPositions.take i.val
    let R := σ.childPositions.drop (i.val + 1)
    let newK := σ.childPositions.filter (fun q ↦
      (q ∈ K ∧ q ≠ p) ∨ (q ∉ K ∧ q = p))
    let f : ℕ → Bool := fun q ↦ decide (q ∈ K)
    change changes (σ.childPositions.map (fun q ↦ decide (q ∈ newK))) + 1 ≤
        changes (σ.childPositions.map f) ∧
      changes (σ.childPositions.map f) ≤
        changes (σ.childPositions.map (fun q ↦ decide (q ∈ newK))) + 2
    have hp : p ∈ σ.childPositions := List.getElem_mem i.isLt
    have heq : σ.childPositions = L ++ p :: R := by
      calc
        σ.childPositions = σ.childPositions.take i.val ++ σ.childPositions.drop i.val :=
          (List.take_append_drop _ _).symm
        _ = L ++ p :: R := by
          rw [List.drop_eq_getElem_cons i.isLt]
          rfl
    have hnd : (L ++ p :: R).Nodup := heq ▸ Ctx.Context.childPositions_nodup σ
    have hpL : p ∉ L := by
      intro hm
      exact (List.disjoint_left.1 (List.nodup_append'.1 hnd).2.2) hm (by simp)
    have hpR : p ∉ R := (List.nodup_cons.1 (List.nodup_append'.1 hnd).2.1).1
    have hlabel : ∀ q ∈ σ.childPositions,
        decide (q ∈ newK) = if q = p then !f q else f q := by
      intro q hq
      by_cases he : q = p <;> by_cases hm : q ∈ K <;>
        simp [newK, hq, hp, he, hm, f]
    have hmapL : L.map (fun q ↦ decide (q ∈ newK)) = L.map f := by
      apply List.map_congr_left
      intro q hq
      have he : q ≠ p := by intro he; subst q; exact hpL hq
      have hchild : q ∈ σ.childPositions := List.mem_of_mem_take hq
      simpa [he] using hlabel q hchild
    have hmapR : R.map (fun q ↦ decide (q ∈ newK)) = R.map f := by
      apply List.map_congr_left
      intro q hq
      have he : q ≠ p := by intro he; subst q; exact hpR hq
      have hchild : q ∈ σ.childPositions := List.mem_of_mem_drop hq
      simpa [he] using hlabel q hchild
    have hlabelp : decide (p ∈ newK) = !f p := by simpa using hlabel p hp
    have hold : σ.childPositions.map f = L.map f ++ f p :: R.map f := by
      calc
        _ = (L ++ p :: R).map f := congrArg (List.map f) heq
        _ = _ := by simp
    have hnew : σ.childPositions.map (fun q ↦ decide (q ∈ newK)) =
        L.map f ++ (!f p) :: R.map f := by
      calc
        _ = (L ++ p :: R).map (fun q ↦ decide (q ∈ newK)) :=
          congrArg (List.map (fun q ↦ decide (q ∈ newK))) heq
        _ = _ := by simp only [List.map_append, List.map_cons, hmapL, hmapR, hlabelp]
    have hlogic : ∀ q, (q ∈ K ↔ p ∉ K) → f q = !f p := by
      intro q h
      change decide (q ∈ K) = !decide (p ∈ K)
      by_cases hq : q ∈ K <;> by_cases hp : p ∈ K <;> simp [hq, hp] at h ⊢
    have hlast : ∀ q, L.getLast? = some q → f q = !f p := by
      intro q hq
      by_cases hz : i.val = 0
      · simp [L, hz] at hq
      · have hi : i.val - 1 < σ.childPositions.length := by omega
        have hget : L.getLast? = some σ.childPositions[i.val - 1] := by
          dsimp only [L]
          rw [List.getLast?_take, if_neg hz, List.getElem?_eq_getElem hi]
          rfl
        have he : σ.childPositions[i.val - 1] = q :=
          Option.some.inj (hget.symm.trans hq)
        have h := hadj ⟨i.val - 1, hi⟩ (Or.inl (by change i.val - 1 + 1 = i.val; omega))
        change (σ.childPositions[i.val - 1] ∈ K ↔ p ∉ K) at h
        rw [he] at h
        exact hlogic q h
    have hfirst : ∀ q, R.head? = some q → f q = !f p := by
      intro q hq
      dsimp only [R] at hq
      rw [List.head?_drop] at hq
      obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.1 hq
      have h := hadj ⟨i.val + 1, hi⟩ (Or.inr rfl)
      change (σ.childPositions[i.val + 1] ∈ K ↔ p ∉ K) at h
      rw [he] at h
      exact hlogic q h
    have hlast' : ∀ c, (L.map f).getLast? = some c → c = !f p := by
      intro c hc
      rw [List.getLast?_map] at hc
      cases hq : L.getLast? with
      | none => simp [hq] at hc
      | some q =>
        have he : f q = c := by simpa [hq] using hc
        rw [← he]
        exact hlast q hq
    have hfirst' : ∀ c, (R.map f).head? = some c → c = !f p := by
      intro c hc
      rw [List.head?_map] at hc
      cases hq : R.head? with
      | none => simp [hq] at hc
      | some q =>
        have he : f q = c := by simpa [hq] using hc
        rw [← he]
        exact hfirst q hq
    have hLR : L ≠ [] ∨ R ≠ [] := by
      by_contra h
      have hnil : L = [] ∧ R = [] := by simpa only [not_or, not_not] using h
      have hc' := hc
      change 3 ≤ changes (σ.childPositions.map f) at hc'
      rw [hold, hnil.1, hnil.2] at hc'
      simp [changes] at hc'
    have ht := hsingle (L.map f) (R.map f) (f p) hlast' hfirst'
      (by simpa using hLR)
    rw [← hold, ← hnew] at ht
    exact ht
  let value := fun (K : List ℕ) (e : ℕ) (b : Bool) ↦
    if b then
      (σ.part K Ctx.Side.upper (σ.k - 1 - e)).bound +
        (σ.part (σ.childPositions.filter (fun p ↦ p ∉ K)) Ctx.Side.lower e).bound
    else
      (σ.part K Ctx.Side.lower e).bound +
        (σ.part (σ.childPositions.filter (fun p ↦ p ∉ K))
          Ctx.Side.upper (σ.k - 1 - e)).bound
  let segments := fun K : List ℕ ↦
    changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) + 1
  have hcutbound : ∀ (K : List ℕ),
      (σ.childPositions.filter (fun p ↦ p ∈ K) ∈ σ.blocks ∨
        σ.childPositions.filter (fun p ↦ p ∉ K) ∈ σ.blocks) →
      ∀ e, 1 ≤ e → e ≤ σ.k - 2 → ∀ b, value K e b ≤ σ.bound := by
    intro K hcut e he hek b
    let KC := σ.childPositions.filter (fun p ↦ p ∈ K)
    have hmem : ∀ p ∈ σ.childPositions, p ∈ K ↔ p ∈ KC := by
      intro p hp
      simp [KC, hp]
    have hparts := hpart K KC hmem
    have hcoeq : σ.childPositions.filter (fun p ↦ p ∉ KC) =
        σ.childPositions.filter (fun p ↦ p ∉ K) := by
      apply List.filter_congr
      intro p hp
      simp [KC, hp]
    have hcut' : KC ∈ σ.blocks ∨ σ.childPositions.filter (fun p ↦ p ∉ KC) ∈ σ.blocks := by
      simpa only [KC, hcoeq] using hcut
    have h := ctx_bound_interval_or_complement_le σ hruns KC hcut' e he hek
    rw [hcoeq, ← hparts Ctx.Side.lower e,
      ← hparts Ctx.Side.upper (σ.k - 1 - e)] at h
    cases b with
    | false => exact h.1
    | true => exact h.2
  have hbound : ∀ n, ∀ (K : List ℕ), segments K = n →
      (∀ p ∈ K, p ∈ σ.childPositions) → K ≠ [] → K.length < σ.childPositions.length →
      ∀ e, 1 ≤ e → e ≤ σ.k - 2 → ∀ b, value K e b ≤ σ.bound := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hn hK hne hlt e he hek b
      by_cases hcut : σ.childPositions.filter (fun p ↦ p ∈ K) ∈ σ.blocks ∨
          σ.childPositions.filter (fun p ↦ p ∉ K) ∈ σ.blocks
      · exact hcutbound K hcut e he hek b
      have hc : 3 ≤ changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) := by
        by_contra hnot
        have hs : changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) ≤ 2 := by omega
        exact hcut (hbase K hK hne hlt hs)
      have hinter : σ.childPositions.filter (fun p ↦ p ∈ K) ∉ σ.blocks :=
        fun h ↦ hcut (Or.inl h)
      have hco : σ.childPositions.filter (fun p ↦ p ∉ K) ∉ σ.blocks :=
        fun h ↦ hcut (Or.inr h)
      obtain ⟨i, hsi, e', he', hek', b', hdom⟩ := hflip K hK hne hlt hinter hco e he hek b
      let newK := σ.childPositions.filter (fun p ↦
        (p ∈ K ∧ p ≠ σ.childPositions[i]) ∨ (p ∉ K ∧ p = σ.childPositions[i]))
      have hcounts := htoggle K i hsi hc
      change changes (σ.childPositions.map (fun p ↦ decide (p ∈ newK))) + 1 ≤
          changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) ∧
        changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) ≤
          changes (σ.childPositions.map (fun p ↦ decide (p ∈ newK))) + 2 at hcounts
      have hpositive : 0 < changes (σ.childPositions.map (fun p ↦ decide (p ∈ newK))) := by
        omega
      have hnewproper := hproper newK hpositive
      have hnewcanonical : σ.childPositions.filter (fun p ↦ p ∈ newK) = newK :=
        hcanonical (fun p ↦ decide (
          (p ∈ K ∧ p ≠ σ.childPositions[i]) ∨ (p ∉ K ∧ p = σ.childPositions[i])))
      rw [hnewcanonical] at hnewproper
      have hnewkeep : ∀ p ∈ newK, p ∈ σ.childPositions := by
        intro p hp
        exact (List.mem_filter.1 hp).1
      have hless : segments newK < n := by
        rw [← hn]
        dsimp only [segments]
        omega
      have hfinal := ih (segments newK) hless newK rfl hnewkeep hnewproper.1
        hnewproper.2 e' he' hek' b'
      change value K e b ≤ value newK e' b' at hdom
      exact hdom.trans hfinal
  constructor
  · exact hbound (segments keep) keep rfl hkeep hne hall d hd hdk false
  · exact hbound (segments keep) keep rfl hkeep hne hall d hd hdk true

end ErdosSzekeres
