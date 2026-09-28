import ESBlueprint.B.RankRowColumnUnionCardEqGroupCharges
import ESBlueprint.B.RankTripleFaceIntervalUnionCardSq

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Exact grouped cardinality of ordered-triple faces for interval endpoints ordered around a common pivot. Left faces fix the lower endpoint; right faces fix the upper endpoint. Group by those endpoints and merge the two pivot groups precisely when the face unions meet. Ordinary groups contribute their ordered-pair rank counts; the merged pivot contributes the square of its rank-union cardinality. Empty intervals and extra empty colors are allowed. This extends the checked row/column grouping to the finite counting component of a proposed higher-capacity triple-face potential, without assuming its recursive context inequality.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem rank_triple_face_union_card_eq_group_charges (L R : Finset ℕ) (lo hi : ℕ → ℕ) (a b : ℕ)
  (hL : ∀ p ∈ L, lo p ≤ a ∧ hi p ≤ b)
  (hR : ∀ p ∈ R, a ≤ lo p ∧ b ≤ hi p)
  (colors : Finset ℕ) :
  let I := fun p => Finset.Icc (lo p) (hi p)
  let pairs := fun S : Finset ℕ => (S.product S).filter (fun z => z.1 ≤ z.2)
  let rows := L.biUnion (fun p => ({lo p} : Finset ℕ).product (pairs (I p)))
  let columns := R.biUnion (fun p => (pairs (I p)).image (fun z => (z.1, z.2, hi p)))
  let merge := ¬ Disjoint rows columns
  let leftColor := fun p => if merge ∧ lo p = a then 0 else 2 * lo p + 1
  let rightColor := fun p => if merge ∧ hi p = b then 0 else 2 * hi p + 2
  let ranks := fun c => ((L.filter (fun p => leftColor p = c)).biUnion I) ∪
    ((R.filter (fun p => rightColor p = c)).biUnion I)
  (∀ p ∈ L, leftColor p ∈ colors) → (∀ p ∈ R, rightColor p ∈ colors) →
  (rows ∪ columns).card =
    colors.sum (fun c => if c = 0 then (ranks c).card ^ 2 else (pairs (ranks c)).card) := by
  classical
  let I (p : ℕ) := Finset.Icc (lo p) (hi p)
  let pairs (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
  let row (p : ℕ) := ({lo p} : Finset ℕ).product (pairs (I p))
  let col (p : ℕ) := (pairs (I p)).image (fun z => (z.1, z.2, hi p))
  let rows := L.biUnion row
  let cols := R.biUnion col
  let merge := ¬ Disjoint rows cols
  let lc (p : ℕ) := if merge ∧ lo p = a then 0 else 2 * lo p + 1
  let rc (p : ℕ) := if merge ∧ hi p = b then 0 else 2 * hi p + 2
  let LP (c : ℕ) := L.filter (fun p => lc p = c)
  let RP (c : ℕ) := R.filter (fun p => rc p = c)
  let LK (c : ℕ) := (LP c).biUnion I
  let RK (c : ℕ) := (RP c).biUnion I
  let U (c : ℕ) := (LP c).biUnion row
  let V (c : ℕ) := (RP c).biUnion col
  let W (c : ℕ) := U c ∪ V c
  let K (c : ℕ) := LK c ∪ RK c
  change (∀ p ∈ L, lc p ∈ colors) → (∀ p ∈ R, rc p ∈ colors) →
    (rows ∪ cols).card = colors.sum (fun c => if c = 0 then (K c).card ^ 2 else (pairs (K c)).card)
  intro hcolorsL hcolorsR
  have hLP (c p : ℕ) : p ∈ LP c ↔ p ∈ L ∧ lc p = c := by simp [LP]
  have hRP (c p : ℕ) : p ∈ RP c ↔ p ∈ R ∧ rc p = c := by simp [RP]
  have hRowMem (p : ℕ) (z : ℕ × ℕ × ℕ) :
      z ∈ row p ↔ z.1 = lo p ∧ z.2.1 ∈ I p ∧ z.2.2 ∈ I p ∧ z.2.1 ≤ z.2.2 := by
    simp only [row, pairs, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_filter, and_assoc]
  have hColMem (p : ℕ) (z : ℕ × ℕ × ℕ) :
      z ∈ col p ↔ z.1 ∈ I p ∧ z.2.1 ∈ I p ∧ z.1 ≤ z.2.1 ∧ z.2.2 = hi p := by
    constructor
    · intro hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      have hq' := Finset.mem_filter.mp hq
      have hp := Finset.mem_product.mp hq'.1
      exact ⟨hp.1, hp.2, hq'.2, rfl⟩
    · intro hz
      refine Finset.mem_image.mpr ⟨(z.1, z.2.1), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz.1, hz.2.1⟩, hz.2.2.1⟩
      · exact Prod.ext rfl (Prod.ext rfl hz.2.2.2.symm)
  have hColInj (v : ℕ) : Function.Injective (fun z : ℕ × ℕ => (z.1, z.2, v)) := by
    intro p q h
    exact Prod.ext (congrArg (fun z : ℕ × ℕ × ℕ => z.1) h) (congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) h)
  have hCross (p q : ℕ) (hp : p ∈ L) (hq : q ∈ R) (z : ℕ × ℕ × ℕ)
      (hzr : z ∈ row p) (hzc : z ∈ col q) :
      lo p = a ∧ hi p = b ∧ lo q = a ∧ hi q = b ∧ merge := by
    have hpv := hL p hp
    have hqv := hR q hq
    have hr := (hRowMem p z).mp hzr
    have hc := (hColMem q z).mp hzc
    have hrLast := Finset.mem_Icc.mp hr.2.2.1
    have hcFirst := Finset.mem_Icc.mp hc.1
    have hm : merge := by
      intro hd
      exact Finset.disjoint_left.mp hd
        (Finset.mem_biUnion.mpr ⟨p, hp, hzr⟩)
        (Finset.mem_biUnion.mpr ⟨q, hq, hzc⟩)
    exact ⟨by omega, by omega, by omega, by omega, hm⟩
  have hLsame (p q : ℕ) (hc : lc p = lc q) (hn : lc p ≠ 0) : lo p = lo q := by
    dsimp [lc] at hc hn
    split_ifs at hc hn <;> omega
  have hRsame (p q : ℕ) (hc : rc p = rc q) (hn : rc p ≠ 0) : hi p = hi q := by
    dsimp [rc] at hc hn
    split_ifs at hc hn <;> omega
  have hDifferent (p q : ℕ) (hc : lc p = rc q) (hn : lc p ≠ 0) : False := by
    dsimp [lc, rc] at hc hn
    split_ifs at hc hn <;> omega
  have hUProd (c v : ℕ) (hv : ∀ p ∈ LP c, lo p = v) :
      U c = ({v} : Finset ℕ).product (pairs (LK c)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hr := (hRowMem p z).mp hz
      refine Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr (hr.1.trans (hv p hp)), ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_biUnion.mpr ⟨p, hp, hr.2.1⟩,
          Finset.mem_biUnion.mpr ⟨p, hp, hr.2.2.1⟩⟩, hr.2.2.2⟩
    · intro hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz
      have hFirst := Finset.mem_singleton.mp hz1
      obtain ⟨hz2, horder⟩ := Finset.mem_filter.mp hz2
      obtain ⟨hmid, hlast⟩ := Finset.mem_product.mp hz2
      obtain ⟨p, hp, hlast⟩ := Finset.mem_biUnion.mp hlast
      obtain ⟨q, hq, hmid⟩ := Finset.mem_biUnion.mp hmid
      have hqlo := hv q hq
      have hplo := hv p hp
      have hm := Finset.mem_Icc.mp hmid
      have he := Finset.mem_Icc.mp hlast
      refine Finset.mem_biUnion.mpr ⟨p, hp, (hRowMem p z).mpr ?_⟩
      exact ⟨hFirst.trans hplo.symm, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hlast, horder⟩
  have hVProd (c v : ℕ) (hv : ∀ p ∈ RP c, hi p = v) :
      V c = (pairs (RK c)).image (fun z => (z.1, z.2, v)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hr := (hColMem p z).mp hz
      refine Finset.mem_image.mpr ⟨(z.1, z.2.1), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_biUnion.mpr ⟨p, hp, hr.1⟩,
            Finset.mem_biUnion.mpr ⟨p, hp, hr.2.1⟩⟩, hr.2.2.1⟩
      · exact Prod.ext rfl (Prod.ext rfl ((hv p hp).symm.trans hr.2.2.2.symm))
    · intro hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hq, horder⟩ := Finset.mem_filter.mp hq
      obtain ⟨hfirst, hmid⟩ := Finset.mem_product.mp hq
      obtain ⟨p, hp, hfirst⟩ := Finset.mem_biUnion.mp hfirst
      obtain ⟨r, hr, hmid⟩ := Finset.mem_biUnion.mp hmid
      have hrhi := hv r hr
      have hphi := hv p hp
      have hm := Finset.mem_Icc.mp hmid
      have he := Finset.mem_Icc.mp hfirst
      refine Finset.mem_biUnion.mpr ⟨p, hp, (hColMem p _).mpr ?_⟩
      have hmidp : q.2 ∈ I p := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      exact ⟨hfirst, hmidp, horder, hphi.symm⟩
  have hDisjoint : (colors : Set ℕ).PairwiseDisjoint W := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro z hzc hzd
    rcases Finset.mem_union.mp hzc with hzc | hzc <;>
      rcases Finset.mem_union.mp hzd with hzd | hzd
    · obtain ⟨p, hp, hzp⟩ := Finset.mem_biUnion.mp hzc
      obtain ⟨q, hq, hzq⟩ := Finset.mem_biUnion.mp hzd
      have he : lo p = lo q := by
        have hp1 := ((hRowMem p z).mp hzp).1
        have hq1 := ((hRowMem q z).mp hzq).1
        exact hp1.symm.trans hq1
      have hh : lc p = lc q := by simp only [lc, he]
      exact hcd (((hLP c p).mp hp).2.symm.trans (hh.trans ((hLP d q).mp hq).2))
    · obtain ⟨p, hp, hzp⟩ := Finset.mem_biUnion.mp hzc
      obtain ⟨q, hq, hzq⟩ := Finset.mem_biUnion.mp hzd
      have hh := hCross p q ((hLP c p).mp hp).1 ((hRP d q).mp hq).1 z hzp hzq
      have he : lc p = rc q := by simp [lc, rc, hh.1, hh.2.2.2.1, hh.2.2.2.2]
      exact hcd (((hLP c p).mp hp).2.symm.trans (he.trans ((hRP d q).mp hq).2))
    · obtain ⟨p, hp, hzp⟩ := Finset.mem_biUnion.mp hzc
      obtain ⟨q, hq, hzq⟩ := Finset.mem_biUnion.mp hzd
      have hh := hCross q p ((hLP d q).mp hq).1 ((hRP c p).mp hp).1 z hzq hzp
      have he : rc p = lc q := by simp [lc, rc, hh.1, hh.2.2.2.1, hh.2.2.2.2]
      exact hcd (((hRP c p).mp hp).2.symm.trans (he.trans ((hLP d q).mp hq).2))
    · obtain ⟨p, hp, hzp⟩ := Finset.mem_biUnion.mp hzc
      obtain ⟨q, hq, hzq⟩ := Finset.mem_biUnion.mp hzd
      have he : hi p = hi q := by
        have hp2 := ((hColMem p z).mp hzp).2.2.2
        have hq2 := ((hColMem q z).mp hzq).2.2.2
        exact hp2.symm.trans hq2
      have hh : rc p = rc q := by simp only [rc, he]
      exact hcd (((hRP c p).mp hp).2.symm.trans (hh.trans ((hRP d q).mp hq).2))
  have hUnion : colors.biUnion W = rows ∪ cols := by
    ext z
    constructor
    · intro hz
      obtain ⟨c, hc, hz⟩ := Finset.mem_biUnion.mp hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p, ((hLP c p).mp hp).1, hz⟩)
      · obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, ((hRP c p).mp hp).1, hz⟩)
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
        exact Finset.mem_biUnion.mpr ⟨lc p, hcolorsL p hp,
          Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p, (hLP _ p).mpr ⟨hp, rfl⟩, hz⟩)⟩
      · obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
        exact Finset.mem_biUnion.mpr ⟨rc p, hcolorsR p hp,
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, (hRP _ p).mpr ⟨hp, rfl⟩, hz⟩)⟩
  have hOrdinary (c : ℕ) (hc : c ≠ 0) : (W c).card = (pairs (K c)).card := by
    by_cases hl : (LP c).Nonempty
    · obtain ⟨p, hp⟩ := hl
      have hpcol := ((hLP c p).mp hp).2
      have hr : RP c = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        exact hDifferent p q (hpcol.trans ((hRP c q).mp hq).2.symm) (by omega)
      have hu := hUProd c (lo p) (by
        intro q hq
        have hqc := ((hLP c q).mp hq).2
        exact hLsame q p (hqc.trans hpcol.symm) (by omega))
      simp only [W, K, V, RK, hr, Finset.biUnion_empty, Finset.union_empty, hu,
        Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, one_mul]
    · have hl' := Finset.not_nonempty_iff_eq_empty.mp hl
      by_cases hr : (RP c).Nonempty
      · obtain ⟨p, hp⟩ := hr
        have hpcol := ((hRP c p).mp hp).2
        have hv := hVProd c (hi p) (by
          intro q hq
          have hqc := ((hRP c q).mp hq).2
          exact hRsame q p (hqc.trans hpcol.symm) (by omega))
        simp only [W, K, U, LK, hl', Finset.biUnion_empty, Finset.empty_union, hv,
          Finset.product_eq_sprod, Finset.card_image_of_injective _ (hColInj _)]
      · have hr' := Finset.not_nonempty_iff_eq_empty.mp hr
        simp [W, K, U, V, LK, RK, pairs, hl', hr']
  have hCentral : (W 0).card = (K 0).card ^ 2 := by
    by_cases hm : merge
    · obtain ⟨z, hzr, hzc⟩ := Finset.not_disjoint_iff.mp hm
      obtain ⟨p, hp, hzp⟩ := Finset.mem_biUnion.mp hzr
      obtain ⟨q, hq, hzq⟩ := Finset.mem_biUnion.mp hzc
      have hh := hCross p q hp hq z hzp hzq
      have hab : a ≤ b := by
        have hi' := Finset.mem_Icc.mp ((hRowMem p z).mp hzp).2.2.1
        omega
      have hL0 (r : ℕ) : r ∈ LP 0 ↔ r ∈ L ∧ lo r = a := by
        rw [hLP]
        by_cases he : lo r = a <;> simp [lc, hm, he]
      have hR0 (r : ℕ) : r ∈ RP 0 ↔ r ∈ R ∧ hi r = b := by
        rw [hRP]
        by_cases he : hi r = b <;> simp [rc, hm, he]
      have hlk : LK 0 = Finset.Icc a b := by
        apply Finset.Subset.antisymm
        · intro v hv
          obtain ⟨r, hr, hv⟩ := Finset.mem_biUnion.mp hv
          have hr' := (hL0 r).mp hr
          have hb := (hL r hr'.1).2
          have hv' := Finset.mem_Icc.mp hv
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · intro v hv
          refine Finset.mem_biUnion.mpr ⟨p, (hL0 p).mpr ⟨hp, hh.1⟩, ?_⟩
          simpa only [I, hh.1, hh.2.1] using hv
      have hrk : RK 0 = Finset.Icc a b := by
        apply Finset.Subset.antisymm
        · intro v hv
          obtain ⟨r, hr, hv⟩ := Finset.mem_biUnion.mp hv
          have hr' := (hR0 r).mp hr
          have ha := (hR r hr'.1).1
          have hv' := Finset.mem_Icc.mp hv
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · intro v hv
          refine Finset.mem_biUnion.mpr ⟨q, (hR0 q).mpr ⟨hq, hh.2.2.2.1⟩, ?_⟩
          simpa only [I, hh.2.2.1, hh.2.2.2.1] using hv
      have hu := hUProd 0 a (by intro r hr; exact ((hL0 r).mp hr).2)
      have hv := hVProd 0 b (by intro r hr; exact ((hR0 r).mp hr).2)
      have hk : K 0 = Finset.Icc a b := by simp only [K, hlk, hrk, Finset.union_self]
      dsimp only [W]
      rw [hu, hv, hlk, hrk, hk]
      exact rank_triple_face_interval_union_card_sq a b
    · have hl : LP 0 = ∅ := by
        ext p
        simp [LP, lc, hm]
      have hr : RP 0 = ∅ := by
        ext p
        simp [RP, rc, hm]
      simp [W, K, U, V, LK, RK, pairs, hl, hr]
  rw [← hUnion, Finset.card_biUnion hDisjoint]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hz : c = 0
  · subst c
    simpa only [if_pos rfl] using hCentral
  · simpa only [if_neg hz] using hOrdinary c hz

end ErdosSzekeres
