import ESBlueprint.B.CtxSmallGlobalAxisRankPairPotential

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At chosen global at most four, every fuel approximation and the full context are bounded by the complete ordered-pair triangle on the opposite pure ranks. Positive labels and distinct axes suffice; histories, maxima, inactive children, and empty support are arbitrary. This exports the finite triangle consequence previously repeated as local proof code and enables sibling-maximum normalization at the final maximum-two sandwich residual.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_small_global_axis_rank_pair_potential
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_small_global_axis_opposite_binomial_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) : let oppositeGlobal := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ oppositeGlobal.choose 2) ∧ σ.bound ≤ oppositeGlobal.choose 2 := by
  classical
  let G (v : Side) := match v with
    | Side.lower => σ.u
    | Side.upper => σ.a
  let B := G t
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let I (p : ℕ) :=
    Finset.Icc (σ.leftExt t 0 p + 1) (B - 1 - σ.rightExt t 0 p)
  let pairs := active.biUnion
    (fun p => ((I p).product (I p)).filter (fun z => z.1 ≤ z.2))
  let T := Finset.Icc 1 (B - 1)
  let triangle := (T.product T).filter (fun z => z.1 ≤ z.2)
  change (∀ fuel, boundFuel fuel σ ≤ B.choose 2) ∧
    σ.bound ≤ B.choose 2
  have hPairBound :=
    ctx_small_global_axis_rank_pair_potential σ hpositive s t hne hglobal
  change (∀ fuel, boundFuel fuel σ ≤ pairs.card) ∧
    σ.bound ≤ pairs.card at hPairBound
  have hInside (p : ℕ) : I p ⊆ T := by
    intro z hz
    have hzi := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hSubset : pairs ⊆ triangle := by
    intro z hz
    obtain ⟨p, _, hz⟩ := Finset.mem_biUnion.mp hz
    have hz' := Finset.mem_filter.mp hz
    obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hz'.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hInside p hza, hInside p hzb⟩, hz'.2⟩
  have hCardPairs (S : Finset ℕ) :
      ((S.product S).filter (fun z => z.1 ≤ z.2)).card =
        (S.card + 1).choose 2 := by
    rw [← Finset.card_sym2]
    apply Finset.card_bij (fun z _ => Sym2.mk z.1 z.2)
    · intro z hz
      exact Finset.mk_mem_sym2_iff.mpr
        (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
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
        · exact ⟨(a, b), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
        · exact ⟨(b, a), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩, Sym2.eq_swap⟩
  have hTriangle : triangle.card = B.choose 2 := by
    change ((T.product T).filter (fun z => z.1 ≤ z.2)).card = B.choose 2
    rw [hCardPairs]
    by_cases hzero : B = 0
    · norm_num [T, hzero]
    · have hcard : T.card + 1 = B := by
        simp only [T, Nat.card_Icc]
        omega
      rw [hcard]
  have hCount : pairs.card ≤ B.choose 2 :=
    (Finset.card_le_card hSubset).trans_eq hTriangle
  exact ⟨fun fuel => (hPairBound.1 fuel).trans hCount,
    hPairBound.2.trans hCount⟩

end ErdosSzekeres
