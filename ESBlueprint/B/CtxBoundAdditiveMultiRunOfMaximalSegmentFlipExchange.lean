import ESBlueprint.B.CtxBoundIntervalOrComplementLe

namespace ErdosSzekeres

/-- Multi-run partition bounds from an explicit maximal homogeneous-segment exchange assumed only for positive original partition values. Strong induction on child membership segment count reduces to interval or complement cuts; zero values are bounded by Nat nonnegativity. The assumption may freely reoptimize coupling and orientation after a whole maximal segment is flipped.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_interval_or_complement_le, ErdosSzekeres.ctx_bound_cut_le
@consumer ErdosSzekeres.ctx_bound_additive_multi_run
@measure membership segment count: adjacent Boolean transitions plus one -/
theorem ctx_bound_additive_multi_run_of_maximal_segment_flip_exchange (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns)
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
    0 < value keep d o →
    ∃ L S R : List ℕ, σ.childPositions = L ++ S ++ R ∧ S ≠ [] ∧
      ∃ c : Bool, (∀ p ∈ S, decide (p ∈ keep) = c) ∧
        (∀ p, L.getLast? = some p → decide (p ∈ keep) = !c) ∧
        (∀ p, R.head? = some p → decide (p ∈ keep) = !c) ∧
        ∃ e : ℕ, 1 ≤ e ∧ e ≤ σ.k - 2 ∧ ∃ b : Bool,
          value keep d o ≤ value
            (σ.childPositions.filter (fun p ↦
              (p ∈ keep ∧ p ∉ S) ∨ (p ∉ keep ∧ p ∈ S))) e b)
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
  have hdup : ∀ (L R : List Bool) (b : Bool),
      changes (L ++ b :: b :: R) = changes (L ++ b :: R) := by
    intro L
    induction L with
    | nil => intro R b; simp only [List.nil_append, hcons, ite_true, Nat.add_zero]
    | cons a L ih =>
      intro R b
      cases L with
      | nil => simp only [List.cons_append, List.nil_append, hcons, ite_true,
          Nat.add_zero]
      | cons c L =>
        have hih := ih R b
        simp only [List.cons_append] at hih
        simp only [List.cons_append, hcons]
        rw [hih]
  have hcompress : ∀ (B L R : List Bool) (b : Bool), B ≠ [] →
      (∀ c ∈ B, c = b) →
      changes (L ++ B ++ R) = changes (L ++ b :: R) := by
    intro B
    induction B with
    | nil => intro L R b hne hB; exact (hne rfl).elim
    | cons a B ih =>
      intro L R b hne hB
      have hab : a = b := hB a (by simp)
      subst a
      cases B with
      | nil => simp
      | cons c B =>
        have hcb : c = b := hB c (by simp)
        subst c
        have htail : ∀ c ∈ b :: B, c = b := by
          intro c hc
          exact hB c (by simp [hc])
        calc
          changes (L ++ (b :: b :: B) ++ R) =
              changes (L ++ (b :: B) ++ R) := by
            simpa only [List.cons_append, List.append_assoc] using hdup L (B ++ R) b
          _ = changes (L ++ b :: R) := ih L R b (by simp) htail
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
  have htoggle : ∀ (K L S R : List ℕ) (c : Bool),
      σ.childPositions = L ++ S ++ R → S ≠ [] →
      (∀ p ∈ S, decide (p ∈ K) = c) →
      (∀ p, L.getLast? = some p → decide (p ∈ K) = !c) →
      (∀ p, R.head? = some p → decide (p ∈ K) = !c) →
      3 ≤ changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) →
      let newK := σ.childPositions.filter (fun p ↦
        (p ∈ K ∧ p ∉ S) ∨ (p ∉ K ∧ p ∈ S))
      changes (σ.childPositions.map (fun p ↦ decide (p ∈ newK))) + 1 ≤
        changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) ∧
      changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) ≤
        changes (σ.childPositions.map (fun p ↦ decide (p ∈ newK))) + 2 := by
    intro K L S R c heq hne hmono hlast hfirst hc
    let newK := σ.childPositions.filter (fun p ↦
      (p ∈ K ∧ p ∉ S) ∨ (p ∉ K ∧ p ∈ S))
    let f : ℕ → Bool := fun p ↦ decide (p ∈ K)
    let g : ℕ → Bool := fun p ↦ decide (p ∈ newK)
    change changes (σ.childPositions.map g) + 1 ≤ changes (σ.childPositions.map f) ∧
      changes (σ.childPositions.map f) ≤ changes (σ.childPositions.map g) + 2
    have hnd : (L ++ (S ++ R)).Nodup := by
      rw [← List.append_assoc, ← heq]
      exact Ctx.Context.childPositions_nodup σ
    have hLdis := (List.nodup_append'.1 hnd).2.2
    have hSRdis := (List.nodup_append'.1 (List.nodup_append'.1 hnd).2.1).2.2
    have hlabel : ∀ p ∈ σ.childPositions, g p = if p ∈ S then !f p else f p := by
      intro p hp
      by_cases hs : p ∈ S <;> by_cases hk : p ∈ K <;>
        simp [g, f, newK, hp, hs, hk]
    have hmapL : L.map g = L.map f := by
      apply List.map_congr_left
      intro p hp
      have hs : p ∉ S := by
        intro hs
        exact (List.disjoint_left.1 hLdis) hp (by simp [hs])
      have hchild : p ∈ σ.childPositions := by rw [heq]; simp [hp]
      simpa [hs] using hlabel p hchild
    have hmapR : R.map g = R.map f := by
      apply List.map_congr_left
      intro p hp
      have hs : p ∉ S := by
        intro hs
        exact (List.disjoint_left.1 hSRdis) hs hp
      have hchild : p ∈ σ.childPositions := by rw [heq]; simp [hp]
      simpa [hs] using hlabel p hchild
    have hnewmono : ∀ p ∈ S, g p = !c := by
      intro p hp
      have hchild : p ∈ σ.childPositions := by rw [heq]; simp [hp]
      have hfc : f p = c := hmono p hp
      simpa only [if_pos hp, hfc] using hlabel p hchild
    have hold : changes (σ.childPositions.map f) =
        changes (L.map f ++ c :: R.map f) := by
      rw [heq, List.map_append, List.map_append]
      apply hcompress (S.map f) (L.map f) (R.map f) c (by simpa using hne)
      intro b hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
      exact hmono p hp
    have hnew : changes (σ.childPositions.map g) =
        changes (L.map f ++ (!c) :: R.map f) := by
      rw [heq, List.map_append, List.map_append, hmapL, hmapR]
      apply hcompress (S.map g) (L.map f) (R.map f) (!c) (by simpa using hne)
      intro b hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
      exact hnewmono p hp
    have hlast' : ∀ b, (L.map f).getLast? = some b → b = !c := by
      intro b hb
      rw [List.getLast?_map] at hb
      cases hp : L.getLast? with
      | none => simp [hp] at hb
      | some p =>
        have he : f p = b := by simpa [hp] using hb
        rw [← he]
        exact hlast p hp
    have hfirst' : ∀ b, (R.map f).head? = some b → b = !c := by
      intro b hb
      rw [List.head?_map] at hb
      cases hp : R.head? with
      | none => simp [hp] at hb
      | some p =>
        have he : f p = b := by simpa [hp] using hb
        rw [← he]
        exact hfirst p hp
    have hLR : L ≠ [] ∨ R ≠ [] := by
      by_contra h
      have hnil : L = [] ∧ R = [] := by simpa only [not_or, not_not] using h
      have hc' := hc
      change 3 ≤ changes (σ.childPositions.map f) at hc'
      rw [hold, hnil.1, hnil.2] at hc'
      simp [changes] at hc'
    have ht := hsingle (L.map f) (R.map f) c hlast' hfirst' (by simpa using hLR)
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
      by_cases hz : value K e b = 0
      · rw [hz]
        exact Nat.zero_le _
      have hvaluepos : 0 < value K e b := Nat.pos_of_ne_zero hz
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
      obtain ⟨L, S, R, heq, hSne, c, hmono, hlast, hfirst, e', he', hek', b', hdom⟩ :=
        hflip K hK hne hlt hinter hco e he hek b hvaluepos
      let newK := σ.childPositions.filter (fun p ↦
        (p ∈ K ∧ p ∉ S) ∨ (p ∉ K ∧ p ∈ S))
      have hcounts := htoggle K L S R c heq hSne hmono hlast hfirst hc
      change changes (σ.childPositions.map (fun p ↦ decide (p ∈ newK))) + 1 ≤
          changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) ∧
        changes (σ.childPositions.map (fun p ↦ decide (p ∈ K))) ≤
          changes (σ.childPositions.map (fun p ↦ decide (p ∈ newK))) + 2 at hcounts
      have hpositive : 0 < changes (σ.childPositions.map (fun p ↦ decide (p ∈ newK))) := by
        omega
      have hnewproper := hproper newK hpositive
      have hnewcanonical : σ.childPositions.filter (fun p ↦ p ∈ newK) = newK :=
        hcanonical (fun p ↦ decide (
          (p ∈ K ∧ p ∉ S) ∨ (p ∉ K ∧ p ∈ S)))
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
