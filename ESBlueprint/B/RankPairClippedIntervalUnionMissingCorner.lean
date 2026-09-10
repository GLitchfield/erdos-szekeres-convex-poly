import ESBlueprint.B.RankTripleFaceIntervalUnionCardSq

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Exact ordered-pair saving for two endpoint-clipped overlapping integer intervals. For a<b, the union of ordered pairs from [a,b-1] and [a+1,b] is the ordered-pair set of [a,b] with exactly its extreme corner (a,b) erased. Consequently adding the left triangular charge to this union charge gives the full interval-cardinality square minus one, expressed without subtraction as an equality after adding one. This is the precise one-unit counting saving proposed for an internal interval cut whose complement straddles the chosen pivot. The contextual cut classification remains a separate proof task.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem rank_pair_clipped_interval_union_missing_corner (a b : ℕ) (hab : a < b) :
  let I := Finset.Icc a b
  let L := Finset.Icc a (b - 1)
  let R := Finset.Icc (a + 1) b
  let pairs := fun (S : Finset ℕ) => (S.product S).filter (fun z => z.1 ≤ z.2)
  pairs L ∪ pairs R = (pairs I).erase (a, b) ∧
    (pairs L).card + (pairs L ∪ pairs R).card + 1 = I.card ^ 2 := by
  classical
  let I := Finset.Icc a b
  let L := Finset.Icc a (b - 1)
  let R := Finset.Icc (a + 1) b
  let pairs := fun (S : Finset ℕ) => (S.product S).filter (fun z => z.1 ≤ z.2)
  change pairs L ∪ pairs R = (pairs I).erase (a, b) ∧
    (pairs L).card + (pairs L ∪ pairs R).card + 1 = I.card ^ 2
  have hUnion : pairs L ∪ pairs R = (pairs I).erase (a, b) := by
    apply Finset.ext
    intro z
    rcases z with ⟨p, q⟩
    simp only [pairs, I, L, R, Finset.product_eq_sprod, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc, Finset.mem_erase, ne_eq, Prod.mk.injEq]
    omega
  have hCorner : (a, b) ∈ pairs I := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩,
        Finset.mem_Icc.mpr ⟨le_of_lt hab, le_rfl⟩⟩, le_of_lt hab⟩
  have hErase : (pairs L ∪ pairs R).card + 1 = (pairs I).card := by
    rw [hUnion]
    exact Finset.card_erase_add_one hCorner
  have hLength : L.card + 1 = I.card := by
    simp only [L, I, Nat.card_Icc]
    omega
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
  have hLeftCard : (pairs L).card = I.card.choose 2 := by
    rw [hCardPairs L, hLength]
  have hTotalCard : (pairs I).card = (I.card + 1).choose 2 := hCardPairs I
  have hChoose : (I.card + 1).choose 2 = I.card.choose 2 + I.card := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    change I.card + I.card.choose 2 = I.card.choose 2 + I.card
    exact Nat.add_comm _ _
  have hTwice := hTwoChoose I.card
  refine ⟨hUnion, ?_⟩
  rw [hTotalCard] at hErase
  rw [hLeftCard]
  nlinarith

end ErdosSzekeres
