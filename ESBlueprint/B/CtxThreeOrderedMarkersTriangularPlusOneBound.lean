import ESBlueprint.B.CtxActiveBoundaryMarkerRankPairUnionBound
import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsCapacityThree

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Three ordered actual markers on one axis, with no younger history below the oldest marker, bound every fuel approximation and the full recursive context by the opposite triangular potential plus one. Splitting physical child runs at the oldest marker makes the exterior arm share a singleton rank forced by the three-marker chain, while the other arm is controlled by the complete rank-pair triangle; capacity-three recombination adds the two charges. Both monotone marker orientations, arbitrary opposite history, maxima, inactive children, and k remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_active_boundary_marker_rank_pair_union_bound, ErdosSzekeres.ctx_bound_le_one_of_common_singleton_rank, ErdosSzekeres.ctx_bound_le_sum_run_group_prunings_capacity_three, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_three_ordered_markers_triangular_plus_one_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (J N M x y z : ℕ) (hJ : J ∈ σ.levels) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hJN : J < N) (hNM : N < M) (hJs : σ.sideAt J = s) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions J) (hy : y ∈ σ.extPositions N) (hz : z ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hyoung : ∀ j ∈ σ.levelsOn s J, σ.extPositions j = []) (horder : (x < y ∧ y < z) ∨ (z < y ∧ y < x)) : let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1; (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (w + 1).choose 2 + 1) ∧ σ.bound ≤ (w + 1).choose 2 + 1 := by
  classical
  have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hTrip (ρ : Context) (A B D a b d : ℕ)
      (hA : A ∈ ρ.levels) (hB : B ∈ ρ.levels) (hD : D ∈ ρ.levels)
      (hAB : A < B) (hBD : B < D)
      (hAs : ρ.sideAt A = s) (hBs : ρ.sideAt B = s) (hDs : ρ.sideAt D = s)
      (ha : a ∈ ρ.extPositions A) (hb : b ∈ ρ.extPositions B)
      (hd : d ∈ ρ.extPositions D) :
      (∀ p, p < a → a < b → b < d → 3 ≤ ρ.rightExt s 0 p) ∧
      (∀ p, a < p → b < a → d < b → 3 ≤ ρ.leftExt s 0 p) := by
    have hAOn : A ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hA, by simp [hAs]⟩
    have hBOn : B ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hB, by simp [hBs]⟩
    have hDOn : D ∈ ρ.levelsOn s 0 := List.mem_filter.mpr ⟨hD, by simp [hDs]⟩
    have hSorted : (ρ.levelsOn s 0).Pairwise (· < ·) := by
      apply List.Pairwise.filter
      exact List.pairwise_lt_range.map (fun i => i + 1)
        (fun i j h => by dsimp; omega)
    have hThree : [A, B, D].Sublist (ρ.levelsOn s 0) := by
      have hs : [A, B, D].Pairwise (· < ·) := by simp; omega
      have hsub : [A, B, D] ⊆ ρ.levelsOn s 0 := by
        intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hAOn
        · exact hBOn
        · exact hDOn
      have he : (ρ.levelsOn s 0).filter (· ∈ [A, B, D]) = [A, B, D] := by
        apply (hSorted.filter _).eq_of_mem_iff hs
        intro j
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨And.right, fun hj => ⟨hsub hj, hj⟩⟩
      rw [← he]
      exact List.filter_sublist
    have hSort (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
      (List.pairwise_lt_range.filter _).imp le_of_lt
    constructor
    · intro p hpa hab hbd
      have hmA : a ∈ (ρ.extPositions A).filter (p < ·) := by simp [ha, hpa]
      have hneA := List.ne_nil_of_mem hmA
      let u := ((ρ.extPositions A).filter (p < ·)).head hneA
      have hu : ((ρ.extPositions A).filter (p < ·)).head? = some u :=
        List.head?_eq_some_head hneA
      have hua : u ≤ a := ((hSort A).filter _).rel_head hmA
      have hmB : b ∈ (ρ.extPositions B).filter (u < ·) := by simp [hb]; omega
      have hneB := List.ne_nil_of_mem hmB
      let v := ((ρ.extPositions B).filter (u < ·)).head hneB
      have hv : ((ρ.extPositions B).filter (u < ·)).head? = some v :=
        List.head?_eq_some_head hneB
      have hvb : v ≤ b := ((hSort B).filter _).rel_head hmB
      have hmD : d ∈ (ρ.extPositions D).filter (v < ·) := by simp [hd]; omega
      have hneD := List.ne_nil_of_mem hmD
      have hh := le_getD_max?_of_mem (L := (ρ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
        (List.mem_map.mpr ⟨[A, B, D], List.mem_sublists.mpr hThree, rfl⟩)
      change _ ≤ ρ.rightExt s 0 p at hh
      simpa only [List.foldl_cons, List.foldl_nil, rightStep, hu, hv,
        List.head?_eq_some_head hneD] using hh
    · intro p hap hba hdb
      have hmA : a ∈ (ρ.extPositions A).filter (· < p) := by simp [ha, hap]
      have hneA := List.ne_nil_of_mem hmA
      let u := ((ρ.extPositions A).filter (· < p)).getLast hneA
      have hu : ((ρ.extPositions A).filter (· < p)).getLast? = some u :=
        List.getLast?_eq_some_getLast hneA
      have hau : a ≤ u := ((hSort A).filter _).rel_getLast hmA
      have hmB : b ∈ (ρ.extPositions B).filter (· < u) := by simp [hb]; omega
      have hneB := List.ne_nil_of_mem hmB
      let v := ((ρ.extPositions B).filter (· < u)).getLast hneB
      have hv : ((ρ.extPositions B).filter (· < u)).getLast? = some v :=
        List.getLast?_eq_some_getLast hneB
      have hbv : b ≤ v := ((hSort B).filter _).rel_getLast hmB
      have hmD : d ∈ (ρ.extPositions D).filter (· < v) := by simp [hd]; omega
      have hneD := List.ne_nil_of_mem hmD
      have hh := le_getD_max?_of_mem (L := (ρ.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
        (List.mem_map.mpr ⟨[A, B, D], List.mem_sublists.mpr hThree, rfl⟩)
      change _ ≤ ρ.leftExt s 0 p at hh
      simpa only [List.foldl_cons, List.foldl_nil, leftStep, hu, hv,
        List.getLast?_eq_some_getLast hneD] using hh
  let w := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let color (p : ℕ) := if p < x then (0 : ℕ) else 1
  let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
  let group (c : ℕ) : Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Letter.child => if p ∈ support c then Letter.child
          else Letter.ext (σ.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let I (ρ : Context) (p : ℕ) :=
    Finset.Icc (ρ.leftExt t 0 p + 1) (w - ρ.rightExt t 0 p)
  let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
  let pairs (ρ : Context) := (active ρ).biUnion (fun p => Q (I ρ p))
  change (∀ fuel, boundFuel fuel σ ≤ (w + 1).choose 2 + 1) ∧
    σ.bound ≤ (w + 1).choose 2 + 1
  have hNe (p : ℕ) (hp : p ∈ σ.childPositions) : p ≠ x := by
    intro he
    subst p
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hx).2
    simp [hc] at he
  have hJOn : J ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hJ, by simp [hJs]⟩
  have hSmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3 := by
    intro p hp
    have hn := hNe p hp
    by_cases hpx : p < x
    · have he := hOneRight σ s J p x hJOn hx hpx
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
    · have he := hOneLeft σ s J p x hJOn hx (by omega)
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
  have hCover : ∀ p ∈ σ.childPositions, color p ∈ ({0, 1} : Finset ℕ) := by
    intro p hp
    dsimp only [color]
    split_ifs <;> simp
  have hColor : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions, p ≤ q →
      (∀ z, p ≤ z → z ≤ q → z ∈ σ.childPositions) → color p = color q := by
    intro p hp q hq hpq hbetween
    have hside : (p < x) = (q < x) := by
      apply propext
      constructor
      · intro hpx
        by_contra hqx
        have hxc := hbetween x (by omega) (by omega)
        exact hNe x hxc rfl
      · omega
    simp only [color, hside]
  have hPos (c : ℕ) : ∀ p j v, (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).1
  have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔
      p ∈ σ.childPositions ∧ color p = c := by
    have hh : (group c).childPositions = σ.childPositions.filter (· ∈ support c) :=
      (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.1
    rw [hh]
    simp [support]
  have hHist (c j : ℕ) (hj : j ∈ σ.levels) :
      (group c).extPositions j = σ.extPositions j ∧
        (group c).sideAt j = σ.sideAt j :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.1 j hj
  have hLevels (c : ℕ) (v : Side) (top : ℕ) :
      (group c).levelsOn v top = σ.levelsOn v top :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.1 v top
  have hX (c : ℕ) : x ∈ (group c).extPositions J := by
    rw [(hHist c J hJ).1]
    exact hx
  have hY (c : ℕ) : y ∈ (group c).extPositions N := by
    rw [(hHist c N hN).1]
    exact hy
  have hZ (c : ℕ) : z ∈ (group c).extPositions M := by
    rw [(hHist c M hM).1]
    exact hz
  have hSide (c : ℕ) : (group c).sideAt J = s := (hHist c J hJ).2.trans hJs
  have h0 (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < x := by
    have hh := ((hChild 0 p).mp hp).2
    dsimp only [color] at hh
    split_ifs at hh <;> omega
  have h1 (p : ℕ) (hp : p ∈ (group 1).childPositions) : x < p := by
    have hh := ((hChild 1 p).mp hp).2
    have hn := hNe p ((hChild 1 p).mp hp).1
    dsimp only [color] at hh
    split_ifs at hh <;> omega
  have hCardPairs (T : Finset ℕ) : (Q T).card = (T.card + 1).choose 2 := by
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
  have hPair (c : ℕ) (direction : Bool)
      (hboundary : ∀ p ∈ (group c).childPositions,
        if direction then p < x else x < p) :
      (group c).bound ≤ (w + 1).choose 2 := by
    have hSmallG : min ((match (group c).sideAt J with
        | Side.lower => (group c).u | Side.upper => (group c).a) - 1)
        ((group c).k - (group c).maximumAt J) ≤ 4 := by
      rw [hSide c]
      change min ((match s with | Side.lower => σ.u | Side.upper => σ.a) - 1) _ ≤ 4
      omega
    have hh := ctx_active_boundary_marker_rank_pair_union_bound
      (group c) (hPos c) J x hJ (hX c) direction
      (by intro p hp hact; exact hboundary p hp)
      (by
        intro j hj p hp
        rw [hSide c, hLevels c s J] at hj
        rw [(hHist c j (List.mem_filter.mp hj).1).1, hyoung j hj] at hp
        exact False.elim (List.not_mem_nil hp))
      t (by rw [hSide c]; exact hne) hSmallG
    have hbound : (group c).bound ≤ (pairs (group c)).card := hh.2
    have hSub : pairs (group c) ⊆ Q (Finset.Icc 1 w) := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hz' := Finset.mem_filter.mp hz
      obtain ⟨hza, hzb⟩ := Finset.mem_product.mp hz'.1
      have hza' := Finset.mem_Icc.mp hza
      have hzb' := Finset.mem_Icc.mp hzb
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, hz'.2⟩
    have hcard : (Q (Finset.Icc 1 w)).card = (w + 1).choose 2 := by
      rw [hCardPairs]
      have hh : (Finset.Icc 1 w).card = w := by
        simp only [Nat.card_Icc]
        omega
      rw [hh]
    exact hbound.trans ((Finset.card_le_card hSub).trans_eq hcard)
  have hUnit0 (hxy : x < y) (hyz : y < z) : (group 0).bound ≤ 1 := by
    have hRank : ∀ p ∈ (group 0).childPositions, 0 < (group 0).cupLimit p p →
        0 < (group 0).capLimit p p → (group 0).leftExt s 0 p + 1 = 1 ∧
        1 + (group 0).rightExt s 0 p =
          (match (generalizing := false) s with
            | Side.lower => (group 0).u - 1 | Side.upper => (group 0).a - 1) := by
      intro p hp hcup hcap
      have ht := (hTrip (group 0) J N M x y z hJ hN hM hJN hNM (hSide 0)
        ((hHist 0 N hN).2.trans hNs) ((hHist 0 M hM).2.trans hMs)
        (hX 0) (hY 0) (hZ 0)).1 p (h0 p hp) hxy hyz
      have hg : (match s with
        | Side.lower => (group 0).u | Side.upper => (group 0).a) ≤ 5 := hglobal
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hg hcup hcap ⊢ <;> omega
    exact (ctx_bound_le_one_of_common_singleton_rank
      (group 0) (hPos 0) s 1 hRank).2.1
  have hUnit1 (hzy : z < y) (hyx : y < x) : (group 1).bound ≤ 1 := by
    have hRank : ∀ p ∈ (group 1).childPositions, 0 < (group 1).cupLimit p p →
        0 < (group 1).capLimit p p → (group 1).leftExt s 0 p + 1 = 4 ∧
        4 + (group 1).rightExt s 0 p =
          (match (generalizing := false) s with
            | Side.lower => (group 1).u - 1 | Side.upper => (group 1).a - 1) := by
      intro p hp hcup hcap
      have ht := (hTrip (group 1) J N M x y z hJ hN hM hJN hNM (hSide 1)
        ((hHist 1 N hN).2.trans hNs) ((hHist 1 M hM).2.trans hMs)
        (hX 1) (hY 1) (hZ 1)).2 p (h1 p hp) hyx hzy
      have hg : (match s with
        | Side.lower => (group 1).u | Side.upper => (group 1).a) ≤ 5 := hglobal
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hg hcup hcap ⊢ <;> omega
    exact (ctx_bound_le_one_of_common_singleton_rank
      (group 1) (hPos 1) s 4 hRank).2.1
  have hSum : (group 0).bound + (group 1).bound ≤ (w + 1).choose 2 + 1 := by
    rcases horder with ⟨hxy, hyz⟩ | ⟨hzy, hyx⟩
    · have ha := hUnit0 hxy hyz
      have hb := hPair 1 false h1
      omega
    · have ha := hPair 0 true h0
      have hb := hUnit1 hzy hyx
      omega
  have hDecomp := ctx_bound_le_sum_run_group_prunings_capacity_three σ hpositive
    color ({0, 1} : Finset ℕ) hCover hSmall hColor
  change (∀ fuel, boundFuel fuel σ ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
    σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hDecomp
  have hBudget : ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) ≤
      (w + 1).choose 2 + 1 := by
    simpa using hSum
  exact ⟨fun fuel => (hDecomp.1 fuel).trans hBudget, hDecomp.2.trans hBudget⟩

end ErdosSzekeres
