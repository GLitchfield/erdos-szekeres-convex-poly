import ESBlueprint.B.CtxPartTrackedRankPairEndReservations

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Localize a coincident left/right rank-pair reservation. Removed source-active witnesses on opposite sides of a tracked active part have equal source rank-interval endpoints. Every tracked source interval then equals that common interval, while the corresponding part interval lies strictly inside it. The part rank union has cardinal at most the common width minus two, and nonempty tracked activity forces the common interval to contain at least three ranks. Allows arbitrary positive histories, global parameters, kept sets and new maxima. Describes the unique row-column overlap regime of the rank-pair reservation approach and excludes narrow collision intervals from the remaining recursive overlap-saving obstruction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_part_equal_endpoint_interior_ranks (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s : Ctx.Side) (keep : List ℕ) (m : ℕ) (F Q : Finset ℕ) (p q : ℕ)
  (hF : ∀ r ∈ F, r ∈ σ.childPositions ∧ 0 < σ.cupLimit r r ∧ 0 < σ.capLimit r r)
  (hQ : ∀ r ∈ Q, r ∈ (σ.part keep s m).childPositions ∧
    0 < (σ.part keep s m).cupLimit r r ∧ 0 < (σ.part keep s m).capLimit r r)
  (hQF : Q ⊆ F) (hp : p ∈ F) (hq : q ∈ F) (hpnot : p ∉ keep) (hqnot : q ∉ keep)
  (hleft : ∀ r ∈ Q, p < r) (hright : ∀ r ∈ Q, r < q)
  (hlo : σ.leftExt s 0 p = σ.leftExt s 0 q)
  (hhi : (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s - 1 - σ.rightExt s 0 p =
    (fun v : Ctx.Side => match v with
      | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s - 1 - σ.rightExt s 0 q) :
  let global := fun (ρ : Ctx.Context) (v : Ctx.Side) =>
    match v with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let interval := fun (ρ : Ctx.Context) (r : ℕ) =>
    Finset.Icc (ρ.leftExt s 0 r + 1) (global ρ s - 1 - ρ.rightExt s 0 r)
  let lo := σ.leftExt s 0 p + 1
  let hi := global σ s - 1 - σ.rightExt s 0 p
  let interior := Finset.Icc (lo + 1) (hi - 1)
  let partRanks := Q.biUnion (interval (σ.part keep s m))
  (∀ r ∈ Q, interval σ r = interval σ p ∧
    interval (σ.part keep s m) r ⊆ interior) ∧
    partRanks ⊆ interior ∧ partRanks.card ≤ hi - lo - 1 ∧
    (Q.Nonempty → lo + 2 ≤ hi) := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let I (ρ : Context) (r : ℕ) :=
    Finset.Icc (ρ.leftExt s 0 r + 1) (G ρ s - 1 - ρ.rightExt s 0 r)
  let τ := σ.part keep s m
  let lo := σ.leftExt s 0 p + 1
  let hi := G σ s - 1 - σ.rightExt s 0 p
  let J := Finset.Icc (lo + 1) (hi - 1)
  let T := Q.biUnion (I τ)
  change (∀ r ∈ Q, I σ r = I σ p ∧ I τ r ⊆ J) ∧
    T ⊆ J ∧ T.card ≤ hi - lo - 1 ∧ (Q.Nonempty → lo + 2 ≤ hi)
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
  have hWidth (ρ : Context) (r : ℕ)
      (hc : 0 < ρ.cupLimit r r) (ha : 0 < ρ.capLimit r r) :
      ρ.leftExt s 0 r + 1 ≤ G ρ s - 1 - ρ.rightExt s 0 r := by
    cases s <;> simp only [G, cupLimit, capLimit, chainExt] at hc ha ⊢ <;> omega
  have hCommon (r : ℕ) (hr : r ∈ Q) : I σ r = I σ p := by
    have hl₁ := hLeftMono σ s 0 p r (le_of_lt (hleft r hr))
    have hl₂ := hLeftMono σ s 0 r q (le_of_lt (hright r hr))
    have hu₁ := hRightMono σ s 0 p r (le_of_lt (hleft r hr))
    have hu₂ := hRightMono σ s 0 r q (le_of_lt (hright r hr))
    have hle : σ.leftExt s 0 r = σ.leftExt s 0 p := by omega
    have hue : G σ s - 1 - σ.rightExt s 0 r = G σ s - 1 - σ.rightExt s 0 p := by
      change G σ s - 1 - σ.rightExt s 0 p = G σ s - 1 - σ.rightExt s 0 q at hhi
      omega
    dsimp only [I]
    rw [hle, hue]
  have hInherit (r : ℕ) (hr : r ∈ Q) : I τ r ⊆ I σ r := by
    have hh := ctx_part_tracked_rank_reservation σ hpositive s keep m {r} {r} ∅ ∅
      (by intro a ha; simpa only [Finset.mem_singleton.mp ha] using hF r (hQF hr))
      (by intro a ha; simpa only [Finset.mem_singleton.mp ha] using hQ r hr)
      (by intro a ha; exact ha) (by simp) (by simp) (by simp) (by simp)
    simpa only [Finset.singleton_biUnion, Finset.image_empty,
      Finset.empty_union, Finset.sdiff_empty] using hh.2.1
  have htrack := ctx_part_tracked_rank_reservation σ hpositive s keep m F Q {p} {q}
    hF hQ hQF
    (by intro a ha; have he := Finset.mem_singleton.mp ha; subst a; exact ⟨hp, hpnot⟩)
    (by intro a ha; have he := Finset.mem_singleton.mp ha; subst a; exact ⟨hq, hqnot⟩)
    (by intro a ha r hr; simpa only [Finset.mem_singleton.mp ha] using hleft r hr)
    (by intro a ha r hr; simpa only [Finset.mem_singleton.mp ha] using hright r hr)
  have hInterior (r : ℕ) (hr : r ∈ Q) : I τ r ⊆ J := by
    intro z hz
    have hsrc := hInherit r hr hz
    rw [hCommon r hr] at hsrc
    have hb := Finset.mem_Icc.mp hsrc
    have hx := (Finset.mem_sdiff.mp (htrack.2.1 (Finset.mem_biUnion.mpr ⟨r, hr, hz⟩))).2
    have hnlo : z ≠ lo := by
      intro he
      apply hx
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨p, by simp, he.symm⟩
    have hnhi : z ≠ hi := by
      intro he
      apply hx
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨q, by simp, ?_⟩
      change G σ s - 1 - σ.rightExt s 0 q = z
      change G σ s - 1 - σ.rightExt s 0 p = G σ s - 1 - σ.rightExt s 0 q at hhi
      exact hhi.symm.trans he.symm
    change lo ≤ z ∧ z ≤ hi at hb
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsub : T ⊆ J := by
    intro z hz
    obtain ⟨r, hr, hz⟩ := Finset.mem_biUnion.mp hz
    exact hInterior r hr hz
  have hcard : T.card ≤ hi - lo - 1 := by
    have hh := Finset.card_le_card hsub
    have hlo1 : 1 ≤ lo := by dsimp only [lo]; omega
    simp only [J, Nat.card_Icc] at hh
    omega
  refine ⟨fun r hr => ⟨hCommon r hr, hInterior r hr⟩, hsub, hcard, ?_⟩
  rintro ⟨r, hr⟩
  have hw := hWidth τ r (hQ r hr).2.1 (hQ r hr).2.2
  have hz : τ.leftExt s 0 r + 1 ∈ I τ r := Finset.mem_Icc.mpr ⟨le_rfl, hw⟩
  have hh := Finset.mem_Icc.mp (hInterior r hr hz)
  change lo + 1 ≤ τ.leftExt s 0 r + 1 ∧ τ.leftExt s 0 r + 1 ≤ hi - 1 at hh
  omega

end ErdosSzekeres
