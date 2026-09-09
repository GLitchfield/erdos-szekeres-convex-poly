import ESBlueprint.B.CtxOneLevelArbitraryCutRankPairBound

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Exact finite row-and-column reservation count for interval endpoints ordered around a common pivot. Left intervals have both endpoints below the pivot coordinates; right intervals have both endpoints above them. Group left rows by their lower endpoint and right columns by their upper endpoint, merging the two pivot groups precisely when the row and column unions intersect. Every ordinary group contributes its rank-union cardinality; the merged group contributes twice its rank-union cardinality minus one. Empty intervals and extra empty colors are allowed. This supplies the finite counting step for a youngest-marker context reservation potential and a subsequent no-marker rank-pair induction, without extending the run-group decomposition to capacity three.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem rank_row_column_union_card_eq_group_charges (L R : Finset ℕ) (lo hi : ℕ → ℕ) (a b : ℕ)
  (hL : ∀ p ∈ L, lo p ≤ a ∧ hi p ≤ b)
  (hR : ∀ p ∈ R, a ≤ lo p ∧ b ≤ hi p)
  (colors : Finset ℕ) :
  let I := fun p => Finset.Icc (lo p) (hi p)
  let rows := L.biUnion (fun p => ({lo p} : Finset ℕ).product (I p))
  let columns := R.biUnion (fun p => (I p).product ({hi p} : Finset ℕ))
  let merge := ¬ Disjoint rows columns
  let leftColor := fun p => if merge ∧ lo p = a then 0 else 2 * lo p + 1
  let rightColor := fun p => if merge ∧ hi p = b then 0 else 2 * hi p + 2
  let ranks := fun c => ((L.filter (fun p => leftColor p = c)).biUnion I) ∪
    ((R.filter (fun p => rightColor p = c)).biUnion I)
  (∀ p ∈ L, leftColor p ∈ colors) → (∀ p ∈ R, rightColor p ∈ colors) →
  (rows ∪ columns).card =
    colors.sum (fun c => if c = 0 then 2 * (ranks c).card - 1 else (ranks c).card) := by
  classical
  let I (p : ℕ) := Finset.Icc (lo p) (hi p)
  let row (p : ℕ) := ({lo p} : Finset ℕ).product (I p)
  let col (p : ℕ) := (I p).product ({hi p} : Finset ℕ)
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
    (rows ∪ cols).card = colors.sum (fun c => if c = 0 then 2 * (K c).card - 1 else (K c).card)
  intro hcolorsL hcolorsR
  have hLP (c p : ℕ) : p ∈ LP c ↔ p ∈ L ∧ lc p = c := by simp [LP]
  have hRP (c p : ℕ) : p ∈ RP c ↔ p ∈ R ∧ rc p = c := by simp [RP]
  have hCross (p q : ℕ) (hp : p ∈ L) (hq : q ∈ R) (z : ℕ × ℕ)
      (hzr : z ∈ row p) (hzc : z ∈ col q) :
      lo p = a ∧ hi p = b ∧ lo q = a ∧ hi q = b ∧ merge := by
    have hpv := hL p hp
    have hqv := hR q hq
    have hzr' : z.1 = lo p ∧ lo p ≤ z.2 ∧ z.2 ≤ hi p := by
      simpa only [row, I, Finset.product_eq_sprod, Finset.mem_product,
        Finset.mem_singleton, Finset.mem_Icc] using hzr
    have hzc' : (lo q ≤ z.1 ∧ z.1 ≤ hi q) ∧ z.2 = hi q := by
      simpa only [col, I, Finset.product_eq_sprod, Finset.mem_product,
        Finset.mem_singleton, Finset.mem_Icc] using hzc
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
      U c = ({v} : Finset ℕ).product (LK c) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_biUnion.mpr ⟨p, hp, hz2⟩⟩
      simpa only [hv p hp] using hz1
    · intro hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz
      obtain ⟨p, hp, hz2⟩ := Finset.mem_biUnion.mp hz2
      refine Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_product.mpr ⟨?_, hz2⟩⟩
      simpa only [hv p hp] using hz1
  have hVProd (c v : ℕ) (hv : ∀ p ∈ RP c, hi p = v) :
      V c = (RK c).product ({v} : Finset ℕ) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz
      refine Finset.mem_product.mpr ⟨Finset.mem_biUnion.mpr ⟨p, hp, hz1⟩, ?_⟩
      simpa only [hv p hp] using hz2
    · intro hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz
      obtain ⟨p, hp, hz1⟩ := Finset.mem_biUnion.mp hz1
      refine Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_product.mpr ⟨hz1, ?_⟩⟩
      simpa only [hv p hp] using hz2
  have hDisjoint : (colors : Set ℕ).PairwiseDisjoint W := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro z hzc hzd
    rcases Finset.mem_union.mp hzc with hzc | hzc <;>
      rcases Finset.mem_union.mp hzd with hzd | hzd
    · obtain ⟨p, hp, hzp⟩ := Finset.mem_biUnion.mp hzc
      obtain ⟨q, hq, hzq⟩ := Finset.mem_biUnion.mp hzd
      have he : lo p = lo q := by
        have hp1 := Finset.mem_singleton.mp (Finset.mem_product.mp hzp).1
        have hq1 := Finset.mem_singleton.mp (Finset.mem_product.mp hzq).1
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
        have hp2 := Finset.mem_singleton.mp (Finset.mem_product.mp hzp).2
        have hq2 := Finset.mem_singleton.mp (Finset.mem_product.mp hzq).2
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
  have hOrdinary (c : ℕ) (hc : c ≠ 0) : (W c).card = (K c).card := by
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
          Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, mul_one]
      · have hr' := Finset.not_nonempty_iff_eq_empty.mp hr
        simp [W, K, U, V, LK, RK, hl', hr']
  have hCentral : (W 0).card = 2 * (K 0).card - 1 := by
    by_cases hm : merge
    · obtain ⟨z, hzr, hzc⟩ := Finset.not_disjoint_iff.mp hm
      obtain ⟨p, hp, hzp⟩ := Finset.mem_biUnion.mp hzr
      obtain ⟨q, hq, hzq⟩ := Finset.mem_biUnion.mp hzc
      have hh := hCross p q hp hq z hzp hzq
      have hab : a ≤ b := by
        have hi' := Finset.mem_Icc.mp (Finset.mem_product.mp hzp).2
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
      have hinter : U 0 ∩ V 0 = {(a, b)} := by
        rw [hu, hv, hlk, hrk]
        ext z
        simp only [Finset.mem_inter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton,
          Finset.mem_Icc]
        constructor
        · intro hz
          exact Prod.ext hz.1.1 hz.2.2
        · intro hz
          cases hz
          exact ⟨⟨rfl, hab, le_rfl⟩, ⟨⟨le_rfl, hab⟩, rfl⟩⟩
      have huCard : (U 0).card = (Finset.Icc a b).card := by simp [hu, hlk]
      have hvCard : (V 0).card = (Finset.Icc a b).card := by simp [hv, hrk]
      have hk : K 0 = Finset.Icc a b := by simp only [K, hlk, hrk, Finset.union_self]
      have he := Finset.card_union_add_card_inter (U 0) (V 0)
      rw [hinter, Finset.card_singleton, huCard, hvCard] at he
      dsimp only [W]
      rw [hk]
      omega
    · have hl : LP 0 = ∅ := by
        ext p
        simp [LP, lc, hm]
      have hr : RP 0 = ∅ := by
        ext p
        simp [RP, rc, hm]
      simp [W, K, U, V, LK, RK, hl, hr]
  rw [← hUnion, Finset.card_biUnion hDisjoint]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hz : c = 0
  · subst c
    simpa only [if_pos rfl] using hCentral
  · simpa only [if_neg hz] using hOrdinary c hz

end ErdosSzekeres
