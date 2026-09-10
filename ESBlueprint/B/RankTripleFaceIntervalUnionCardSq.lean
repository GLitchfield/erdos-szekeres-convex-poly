import ESBlueprint.B.CtxSmallGlobalOppositeMaximumBinomialBound
import ESBlueprint.B.CtxSeparatingMarkerRetainedBoundaryRankUnionBound

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Exact square cardinality of the union of the two ordered-triple faces anchored at the endpoints of a finite natural-number interval. Left faces fix the first coordinate to the lower endpoint; right faces fix the last to the upper endpoint. Their intersection has one triple for each middle rank, so the union has the square of the interval cardinality. Empty intervals are included. Supplies the finite pivot charge for a prospective higher-capacity context reservation potential; no recursive context estimate is assumed.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem rank_triple_face_interval_union_card_sq (a b : ℕ) :
  let I := Finset.Icc a b
  let pairs := (I.product I).filter (fun z => z.1 ≤ z.2)
  let rows := ({a} : Finset ℕ).product pairs
  let columns := pairs.image (fun z => (z.1, z.2, b))
  (rows ∪ columns).card = I.card ^ 2 := by
  classical
  let I := Finset.Icc a b
  let Q := (I.product I).filter (fun z => z.1 ≤ z.2)
  let rows := ({a} : Finset ℕ).product Q
  let columns := Q.image (fun z => (z.1, z.2, b))
  let D := I.image (fun v => (a, v, b))
  change (rows ∪ columns).card = I.card ^ 2
  have hRowMem (z : ℕ × ℕ × ℕ) :
      z ∈ rows ↔ z.1 = a ∧ z.2.1 ∈ I ∧ z.2.2 ∈ I ∧ z.2.1 ≤ z.2.2 := by
    simp only [rows, Q, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_filter, and_assoc]
  have hColMem (z : ℕ × ℕ × ℕ) :
      z ∈ columns ↔ z.1 ∈ I ∧ z.2.1 ∈ I ∧ z.1 ≤ z.2.1 ∧ z.2.2 = b := by
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
  have hInter : rows ∩ columns = D := by
    ext z
    simp only [Finset.mem_inter, hRowMem, hColMem, D, Finset.mem_image]
    constructor
    · intro hz
      exact ⟨z.2.1, hz.1.2.1, Prod.ext hz.1.1.symm (Prod.ext rfl hz.2.2.2.2.symm)⟩
    · rintro ⟨v, hv, rfl⟩
      have hv' := Finset.mem_Icc.mp hv
      have hab : a ≤ b := le_trans hv'.1 hv'.2
      have ha : a ∈ I := Finset.mem_Icc.mpr ⟨le_rfl, hab⟩
      have hb : b ∈ I := Finset.mem_Icc.mpr ⟨hab, le_rfl⟩
      exact ⟨⟨rfl, hv, hb, hv'.2⟩, ⟨ha, hv, hv'.1, rfl⟩⟩
  have hColInj : Function.Injective (fun z : ℕ × ℕ => (z.1, z.2, b)) := by
    intro p q h
    exact Prod.ext (congrArg (fun z : ℕ × ℕ × ℕ => z.1) h) (congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) h)
  have hDiagInj : Function.Injective (fun v : ℕ => (a, v, b)) := by
    intro p q h
    exact congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) h
  have hRowCard : rows.card = Q.card := by
    simp only [rows, Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, one_mul]
  have hColCard : columns.card = Q.card := Finset.card_image_of_injective Q hColInj
  have hDiagCard : D.card = I.card := Finset.card_image_of_injective I hDiagInj
  have hCardPairs (T : Finset ℕ) :
      ((T.product T).filter (fun z => z.1 ≤ z.2)).card = (T.card + 1).choose 2 := by
    rw [← Finset.card_sym2]
    apply Finset.card_bij (fun z _ => Sym2.mk z.1 z.2)
    · intro z hz
      exact Finset.mk_mem_sym2_iff.mpr (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
    · intro p hp q hq he
      have hpl := (Finset.mem_filter.mp hp).2
      have hql := (Finset.mem_filter.mp hq).2
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · apply Prod.ext <;> omega
    · intro z hz
      induction z using Sym2.ind with
      | h a b =>
        obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hz
        by_cases hab : a ≤ b
        · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
        · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩,
            Sym2.eq_swap⟩
  have hTwoChoose (n : ℕ) : 2 * (n + 1).choose 2 = n * n + n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith
  have hQCard : Q.card = (I.card + 1).choose 2 := hCardPairs I
  have hCount := Finset.card_union_add_card_inter rows columns
  rw [hInter, hDiagCard, hRowCard, hColCard, hQCard] at hCount
  have hTwice := hTwoChoose I.card
  nlinarith [hTwice]

end ErdosSzekeres
