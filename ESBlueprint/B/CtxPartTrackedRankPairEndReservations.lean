import ESBlueprint.B.CtxPartTrackedRankPairReservation

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Row and column rank-pair reservations for source-active removed witnesses lying on the left and right of a tracked active part. Each left witness reserves every ordered pair joining its lower endpoint to one of its available ranks; each right witness reserves the dual upper-endpoint column. Their union lies in the source pair potential and is excluded from the part pair potential, with exact cardinal charge and separate charges by the left and right rank-union cardinalities. If the tracked part is nonempty, monotonicity of pure extension endpoints forces the row and column unions to overlap in at most one pair, giving a combined rank charge with at most one extra unit. Arbitrary global parameters, positive histories, maxima and disconnected rank unions are allowed. Supplies the end-block charges and isolates the possible one-pair overlap in the prospective higher-capacity quadratic argument.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_part_tracked_rank_pair_end_reservations (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s : Ctx.Side) (keep : List ℕ) (m : ℕ) (F Q L R : Finset ℕ)
  (hF : ∀ p ∈ F, p ∈ σ.childPositions ∧ 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  (hQ : ∀ q ∈ Q, q ∈ (σ.part keep s m).childPositions ∧
    0 < (σ.part keep s m).cupLimit q q ∧ 0 < (σ.part keep s m).capLimit q q)
  (hQF : Q ⊆ F)
  (hL : ∀ p ∈ L, p ∈ F ∧ p ∉ keep) (hR : ∀ p ∈ R, p ∈ F ∧ p ∉ keep)
  (hleft : ∀ p ∈ L, ∀ q ∈ Q, p < q) (hright : ∀ p ∈ R, ∀ q ∈ Q, q < p) :
  let global := fun (ρ : Ctx.Context) (v : Ctx.Side) =>
    match v with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let interval := fun (ρ : Ctx.Context) (p : ℕ) =>
    Finset.Icc (ρ.leftExt s 0 p + 1) (global ρ s - 1 - ρ.rightExt s 0 p)
  let pairs := fun (ρ : Ctx.Context) (p : ℕ) =>
    ((interval ρ p).product (interval ρ p)).filter (fun z => z.1 ≤ z.2)
  let sourcePairs := F.biUnion (pairs σ)
  let partPairs := Q.biUnion (pairs (σ.part keep s m))
  let rows := L.biUnion (fun p => ({σ.leftExt s 0 p + 1} : Finset ℕ).product (interval σ p))
  let columns := R.biUnion (fun p => (interval σ p).product
    ({global σ s - 1 - σ.rightExt s 0 p} : Finset ℕ))
  let reserved := rows ∪ columns
  let leftRanks := L.biUnion (interval σ)
  let rightRanks := R.biUnion (interval σ)
  reserved ⊆ sourcePairs ∧ partPairs ⊆ sourcePairs \ reserved ∧
    partPairs.card + reserved.card ≤ sourcePairs.card ∧
    partPairs.card + leftRanks.card ≤ sourcePairs.card ∧
    partPairs.card + rightRanks.card ≤ sourcePairs.card ∧
    (Q.Nonempty → (rows ∩ columns).card ≤ 1 ∧
      partPairs.card + leftRanks.card + rightRanks.card ≤ sourcePairs.card + 1) := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let lo (p : ℕ) := σ.leftExt s 0 p + 1
  let hi (p : ℕ) := G σ s - 1 - σ.rightExt s 0 p
  let I (ρ : Context) (p : ℕ) :=
    Finset.Icc (ρ.leftExt s 0 p + 1) (G ρ s - 1 - ρ.rightExt s 0 p)
  let Tri (ρ : Context) (p : ℕ) := ((I ρ p).product (I ρ p)).filter (fun z => z.1 ≤ z.2)
  let τ := σ.part keep s m
  let S := F.biUnion (Tri σ)
  let T := Q.biUnion (Tri τ)
  let Rows := L.biUnion (fun p => ({lo p} : Finset ℕ).product (I σ p))
  let Cols := R.biUnion (fun p => (I σ p).product ({hi p} : Finset ℕ))
  let E := Rows ∪ Cols
  let LR := L.biUnion (I σ)
  let RR := R.biUnion (I σ)
  let D := (L.image lo) ∪ (R.image hi)
  change E ⊆ S ∧ T ⊆ S \ E ∧ T.card + E.card ≤ S.card ∧
    T.card + LR.card ≤ S.card ∧ T.card + RR.card ≤ S.card ∧
    (Q.Nonempty → (Rows ∩ Cols).card ≤ 1 ∧ T.card + LR.card + RR.card ≤ S.card + 1)
  have hSort (ρ : Context) (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp le_of_lt
  have hStepLeft (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : c ≤ d) :
      (leftStep ρ (p, c) j).1 ≤ (leftStep ρ (q, d) j).1 ∧
      (leftStep ρ (p, c) j).2 ≤ (leftStep ρ (q, d) j).2 := by
    cases ha : ((ρ.extPositions j).filter (· < p)).getLast? with
    | none =>
      have hnil := List.getLast?_eq_none_iff.mp ha
      cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
      | none => simpa only [leftStep, ha, hb] using And.intro hpq hcd
      | some y =>
        have hy := List.mem_of_mem_getLast? (Option.mem_def.mpr hb)
        have hpy : p ≤ y := by
          by_contra h
          have hx : y ∈ (ρ.extPositions j).filter (· < p) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hx
          exact List.not_mem_nil hx
        simpa only [leftStep, ha, hb] using And.intro hpy (show c ≤ d + 1 by omega)
    | some x =>
      have hx := List.mem_of_mem_getLast? (Option.mem_def.mpr ha)
      have hxq : x ∈ (ρ.extPositions j).filter (· < q) := by
        have hxp : x < p := of_decide_eq_true (List.mem_filter.mp hx).2
        exact List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
      cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
      | none =>
        have hnil := List.getLast?_eq_none_iff.mp hb
        rw [hnil] at hxq
        exact False.elim (List.not_mem_nil hxq)
      | some y =>
        have hlast : ((ρ.extPositions j).filter (· < q)).getLast (List.ne_nil_of_mem hxq) = y := by
          rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hxq)] at hb
          exact Option.some.inj hb
        have hxy : x ≤ y := by
          simpa only [hlast] using ((hSort ρ j).filter _).rel_getLast hxq
        simpa only [leftStep, ha, hb] using And.intro hxy (show c + 1 ≤ d + 1 by omega)
  have hStepRight (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : d ≤ c) :
      (rightStep ρ (p, c) j).1 ≤ (rightStep ρ (q, d) j).1 ∧
      (rightStep ρ (q, d) j).2 ≤ (rightStep ρ (p, c) j).2 := by
    cases ha : ((ρ.extPositions j).filter (p < ·)).head? with
    | none =>
      have hnil := List.head?_eq_none_iff.mp ha
      cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
      | none => simpa only [rightStep, ha, hb] using And.intro hpq hcd
      | some y =>
        have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
        have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
        have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
          List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
        rw [hnil] at hyp
        exact False.elim (List.not_mem_nil hyp)
    | some x =>
      have hx := List.mem_of_mem_head? (Option.mem_def.mpr ha)
      cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
      | none =>
        have hnil := List.head?_eq_none_iff.mp hb
        have hxq : x ≤ q := by
          by_contra h
          have hmem : x ∈ (ρ.extPositions j).filter (q < ·) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hmem
          exact List.not_mem_nil hmem
        simpa only [rightStep, ha, hb] using And.intro hxq (show d ≤ c + 1 by omega)
      | some y =>
        have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
        have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
        have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
          List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
        have hhead : ((ρ.extPositions j).filter (p < ·)).head (List.ne_nil_of_mem hyp) = x := by
          rw [List.head?_eq_some_head (List.ne_nil_of_mem hyp)] at ha
          exact Option.some.inj ha
        have hxy : x ≤ y := by
          simpa only [hhead] using ((hSort ρ j).filter _).rel_head hyp
        simpa only [rightStep, ha, hb] using And.intro hxy (show d + 1 ≤ c + 1 by omega)
  have hFoldLeft (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → c ≤ d →
      (ls.foldl (leftStep ρ) (p, c)).1 ≤ (ls.foldl (leftStep ρ) (q, d)).1 ∧
      (ls.foldl (leftStep ρ) (p, c)).2 ≤ (ls.foldl (leftStep ρ) (q, d)).2 := by
    intro ls
    induction ls with
    | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
    | cons j ls ih =>
      intro p q c d hpq hcd
      have h := hStepLeft ρ j p q c d hpq hcd
      simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
  have hFoldRight (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → d ≤ c →
      (ls.foldl (rightStep ρ) (p, c)).1 ≤ (ls.foldl (rightStep ρ) (q, d)).1 ∧
      (ls.foldl (rightStep ρ) (q, d)).2 ≤ (ls.foldl (rightStep ρ) (p, c)).2 := by
    intro ls
    induction ls with
    | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
    | cons j ls ih =>
      intro p q c d hpq hcd
      have h := hStepRight ρ j p q c d hpq hcd
      simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
  have hLeftMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
      ρ.leftExt v top p ≤ ρ.leftExt v top q := by
    simp only [leftExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldLeft ρ ls p q 0 0 hpq le_rfl).2⟩
  have hRightMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
      ρ.rightExt v top q ≤ ρ.rightExt v top p := by
    simp only [rightExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldRight ρ ls p q 0 0 hpq le_rfl).2⟩
  have hTri (ρ : Context) (p : ℕ) (z : ℕ × ℕ) :
      z ∈ Tri ρ p ↔ z.1 ∈ I ρ p ∧ z.2 ∈ I ρ p ∧ z.1 ≤ z.2 := by
    simp [Tri, and_assoc]
  have hWidth (p : ℕ) (hp : p ∈ F) : lo p ≤ hi p := by
    have hc := (hF p hp).2.1
    have ha := (hF p hp).2.2
    cases s <;> simp only [lo, hi, G, cupLimit, capLimit, chainExt] at hc ha ⊢ <;> omega
  have hTS : T ⊆ S := by
    have hh := ctx_part_tracked_rank_pair_reservation σ hpositive s keep m F Q ∅ hF hQ hQF
      (by simp)
    simpa only [Finset.image_empty, Finset.sdiff_empty] using hh.2.1
  have htrack := ctx_part_tracked_rank_reservation σ hpositive s keep m F Q L R
    hF hQ hQF hL hR hleft hright
  have hAvoid (q : ℕ) (hq : q ∈ Q) (z : ℕ) (hz : z ∈ I τ q) : z ∉ D := by
    have hh := htrack.2.1 (Finset.mem_biUnion.mpr ⟨q, hq, hz⟩)
    exact (Finset.mem_sdiff.mp hh).2
  have hRowsS : Rows ⊆ S := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    have hpF := (hL p hp).1
    obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hz
    have he := Finset.mem_singleton.mp hza
    have hw := hWidth p hpF
    refine Finset.mem_biUnion.mpr ⟨p, hpF, (hTri σ p z).mpr ⟨?_, hzb, ?_⟩⟩
    · rw [he]
      exact Finset.mem_Icc.mpr ⟨le_rfl, hw⟩
    · rw [he]
      exact (Finset.mem_Icc.mp hzb).1
  have hColsS : Cols ⊆ S := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    have hpF := (hR p hp).1
    obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hz
    have he := Finset.mem_singleton.mp hzb
    have hw := hWidth p hpF
    refine Finset.mem_biUnion.mpr ⟨p, hpF, (hTri σ p z).mpr ⟨hza, ?_, ?_⟩⟩
    · rw [he]
      exact Finset.mem_Icc.mpr ⟨hw, le_rfl⟩
    · rw [he]
      exact (Finset.mem_Icc.mp hza).2
  have hES : E ⊆ S := Finset.union_subset hRowsS hColsS
  have hTE : Disjoint T E := by
    apply Finset.disjoint_left.mpr
    intro z hz he
    obtain ⟨q, hq, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hza, hzb, _⟩ := (hTri τ q z).mp hz
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨p, hp, hpz⟩ := Finset.mem_biUnion.mp he
      have heq := Finset.mem_singleton.mp (Finset.mem_product.mp hpz).1
      exact hAvoid q hq z.1 hza
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, heq.symm⟩))
    · obtain ⟨p, hp, hpz⟩ := Finset.mem_biUnion.mp he
      have heq := Finset.mem_singleton.mp (Finset.mem_product.mp hpz).2
      exact hAvoid q hq z.2 hzb
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, heq.symm⟩))
  have hsub : T ⊆ S \ E := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨hTS hz, fun he => Finset.disjoint_left.mp hTE hz he⟩
  have hcard : T.card + E.card ≤ S.card := by
    have hh := Finset.card_le_card (Finset.union_subset hTS hES)
    rw [Finset.card_union_of_disjoint hTE] at hh
    exact hh
  have hLR : LR.card ≤ Rows.card := by
    have him : LR ⊆ Rows.image Prod.snd := by
      intro r hr
      obtain ⟨p, hp, hr⟩ := Finset.mem_biUnion.mp hr
      refine Finset.mem_image.mpr ⟨(lo p, r), Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩, rfl⟩
      exact Finset.mem_product.mpr ⟨by simp, hr⟩
    exact (Finset.card_le_card him).trans Finset.card_image_le
  have hRR : RR.card ≤ Cols.card := by
    have him : RR ⊆ Cols.image Prod.fst := by
      intro r hr
      obtain ⟨p, hp, hr⟩ := Finset.mem_biUnion.mp hr
      refine Finset.mem_image.mpr ⟨(r, hi p), Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩, rfl⟩
      exact Finset.mem_product.mpr ⟨hr, by simp⟩
    exact (Finset.card_le_card him).trans Finset.card_image_le
  have hleftCharge : T.card + LR.card ≤ S.card := by
    have hh : Rows.card ≤ E.card := Finset.card_le_card Finset.subset_union_left
    omega
  have hrightCharge : T.card + RR.card ≤ S.card := by
    have hh : Cols.card ≤ E.card := Finset.card_le_card Finset.subset_union_right
    omega
  refine ⟨hES, hsub, hcard, hleftCharge, hrightCharge, ?_⟩
  intro hnonempty
  obtain ⟨q, hq⟩ := hnonempty
  have hCrossLo (p : ℕ) (hp : p ∈ L) (r : ℕ) (hr : r ∈ R) : lo p ≤ lo r := by
    have hh := hLeftMono σ s 0 p r (le_of_lt ((hleft p hp q hq).trans (hright r hr q hq)))
    dsimp only [lo]
    omega
  have hCrossHi (p : ℕ) (hp : p ∈ L) (r : ℕ) (hr : r ∈ R) : hi p ≤ hi r := by
    have hh := hRightMono σ s 0 p r (le_of_lt ((hleft p hp q hq).trans (hright r hr q hq)))
    dsimp only [hi]
    omega
  have hCorner (z : ℕ × ℕ) (hz : z ∈ Rows ∩ Cols) :
      ∃ p ∈ L, ∃ r ∈ R, lo p = z.1 ∧ lo r = z.1 ∧ hi p = z.2 ∧ hi r = z.2 := by
    obtain ⟨hpz, hrz⟩ := Finset.mem_inter.mp hz
    obtain ⟨p, hp, hpz⟩ := Finset.mem_biUnion.mp hpz
    obtain ⟨r, hr, hrz⟩ := Finset.mem_biUnion.mp hrz
    obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hpz
    obtain ⟨hra, hrb⟩ := Finset.mem_product.mp hrz
    have he₁ := Finset.mem_singleton.mp hpa
    have he₂ := Finset.mem_singleton.mp hrb
    have hpI := Finset.mem_Icc.mp hpb
    have hrI := Finset.mem_Icc.mp hra
    have hc₁ := hCrossLo p hp r hr
    have hc₂ := hCrossHi p hp r hr
    change lo p ≤ z.2 ∧ z.2 ≤ hi p at hpI
    change lo r ≤ z.1 ∧ z.1 ≤ hi r at hrI
    refine ⟨p, hp, r, hr, he₁.symm, ?_, ?_, he₂.symm⟩ <;> omega
  have hcollision : (Rows ∩ Cols).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    obtain ⟨p, hp, r, hr, hpa, hra, hpb, hrb⟩ := hCorner z hz
    obtain ⟨p', hp', r', hr', hpa', hra', hpb', hrb'⟩ := hCorner w hw
    have hl₁ := hCrossLo p hp r' hr'
    have hl₂ := hCrossLo p' hp' r hr
    have hu₁ := hCrossHi p hp r' hr'
    have hu₂ := hCrossHi p' hp' r hr
    apply Prod.ext <;> omega
  refine ⟨hcollision, ?_⟩
  have hunion := Finset.card_union_add_card_inter Rows Cols
  change E.card + (Rows ∩ Cols).card = Rows.card + Cols.card at hunion
  omega

end ErdosSzekeres
