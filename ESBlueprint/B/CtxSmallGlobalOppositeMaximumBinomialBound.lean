import ESBlueprint.B.CtxOldestAxisMaximumEraseNormalize
import ESBlueprint.B.CtxSmallGlobalAxisRankPairPotential

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- A triangular bound controlled by an indexed opposite-axis sibling maximum when the chosen global is at most four. If the selected opposite level is oldest on its axis, every-fuel and full context bounds are at most choose(min(oppositeGlobal,k-maximumAt N),2). Positive labels suffice, with no actual chosen marker, boundary geometry, depth-one or nonempty active-set premise. Reuses oldest-axis maximum erasure, preserves positive labels and the small chosen global, and applies the unrestricted active rank-pair potential inside the normalized global rank interval. Supplies the missing saturated outer-part estimate for interval/complement additivity when the middle ancestor capacity is at most three.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_small_global_opposite_maximum_binomial_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (N : ℕ) (hN : N ∈ σ.levels) (hside : σ.sideAt N = t)
  (hterminal : ∀ j ∈ σ.levelsOn t 0, j ≤ N) :
  let oppositeGlobal := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let normalizedGlobal := min oppositeGlobal (σ.k - σ.maximumAt N)
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ normalizedGlobal.choose 2) ∧
    σ.bound ≤ normalizedGlobal.choose 2 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let B := min (G σ t) (σ.k - σ.maximumAt N)
  let f : Letter → Letter := fun z => match z with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext
        (if j = N then σ.maxima.length else if N < j then j - 1 else j) v
  let E : Context := { σ with word := σ.word.map f, maxima := σ.maxima.eraseIdx (N - 1) }
  let ν : Context := match σ.sideAt N with
    | Side.lower => { E with u := min σ.u (σ.k - σ.maximumAt N) }
    | Side.upper => { E with a := min σ.a (σ.k - σ.maximumAt N) }
  let active := ν.childPositions.toFinset.filter
    (fun p => 0 < ν.cupLimit p p ∧ 0 < ν.capLimit p p)
  let I (p : ℕ) := Finset.Icc (ν.leftExt t 0 p + 1) (G ν t - 1 - ν.rightExt t 0 p)
  let pairs := active.biUnion (fun p => ((I p).product (I p)).filter (fun z => z.1 ≤ z.2))
  let T := Finset.Icc 1 (B - 1)
  let triangle := (T.product T).filter (fun z => z.1 ≤ z.2)
  change (∀ fuel, boundFuel fuel σ ≤ B.choose 2) ∧ σ.bound ≤ B.choose 2
  have hn := ctx_oldest_axis_maximum_erase_normalize σ N hN
    (by simpa only [hside] using hterminal)
  have hνFuel : ∀ fuel, boundFuel fuel σ ≤ boundFuel fuel ν := hn.2.2.2.2.1
  have hνBound : σ.bound ≤ ν.bound := hn.2.2.2.2.2
  have hNpos : 1 ≤ N := one_le_of_mem_levels hN
  have hD : 1 ≤ σ.maxima.length := by
    have hp := List.length_pos_iff.mpr (List.ne_nil_of_mem hN)
    simp only [levels, List.length_map, List.length_range] at hp
    omega
  have hνWord : ν.word = σ.word.map f := by cases hs : σ.sideAt N <;> simp [ν, hs, E]
  have hνLetter (r : ℕ) : ν.letterAt r = f (σ.letterAt r) := by
    simp only [letterAt, hνWord, List.getElem?_map]
    cases σ.word[r]? <;> rfl
  have hνPos : ∀ r j v, ν.letterAt r = Letter.ext j v → 1 ≤ j := by
    intro r j v hj
    rw [hνLetter] at hj
    cases he : σ.letterAt r with
    | child =>
      simp only [he, f] at hj
      cases hj
    | ext i z =>
      rw [he] at hj
      have hi := hpositive r i z he
      have hnew : 1 ≤ (if i = N then σ.maxima.length else if N < i then i - 1 else i) := by
        split_ifs <;> omega
      change Letter.ext (if i = N then σ.maxima.length else if N < i then i - 1 else i) z =
        Letter.ext j v at hj
      cases hj
      exact hnew
  have hνChosen : G ν s = G σ s := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · simp only [G, ν, hside]
      rfl
    · simp only [G, ν, hside]
      rfl
    · exact False.elim (hne rfl)
  have hνGlobal : G ν s ≤ 4 := by rw [hνChosen]; exact hglobal
  have hνOpposite : G ν t = B := by cases t <;> simp only [G, ν, hside, B]
  have hInside (p : ℕ) : I p ⊆ T := by
    intro z hz
    have hz' := Finset.mem_Icc.mp hz
    change ν.leftExt t 0 p + 1 ≤ z ∧ z ≤ G ν t - 1 - ν.rightExt t 0 p at hz'
    rw [hνOpposite] at hz'
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hPairSub : pairs ⊆ triangle := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hz, horder⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hInside p hz1, hInside p hz2⟩, horder⟩
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
  have hTriangle : triangle.card = B.choose 2 := by
    change ((T.product T).filter (fun z => z.1 ≤ z.2)).card = B.choose 2
    rw [hCardPairs]
    by_cases hz : B = 0
    · norm_num [T, hz]
    · have hc : T.card + 1 = B := by
        simp only [T, Nat.card_Icc]
        omega
      rw [hc]
  have hcharge : pairs.card ≤ B.choose 2 := (Finset.card_le_card hPairSub).trans hTriangle.le
  have hb := ctx_small_global_axis_rank_pair_potential ν hνPos s t hne hνGlobal
  change (∀ fuel, boundFuel fuel ν ≤ pairs.card) ∧ ν.bound ≤ pairs.card at hb
  exact ⟨fun fuel => (hνFuel fuel).trans ((hb.1 fuel).trans hcharge),
    hνBound.trans (hb.2.trans hcharge)⟩

end ErdosSzekeres
