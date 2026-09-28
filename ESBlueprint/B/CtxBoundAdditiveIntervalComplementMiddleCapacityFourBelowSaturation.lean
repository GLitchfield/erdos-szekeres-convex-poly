import ESBlueprint.B.CtxSmallGlobalAxisRankTriplePotential
import ESBlueprint.B.CtxBracketedChildrenUnitBound
import ESBlueprint.B.CtxPartTrackedRankPairReservation
import ESBlueprint.B.CtxBoundAdditiveDisjointSingleRunSmallAxis
import ESBlueprint.B.CtxSingleRunDescendantBoundNormalize
import ESBlueprint.B.CtxSmallGlobalAxisRankPairPotential
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Prove reverse-orientation interval-complement additivity below saturation with both new maxima arbitrary. Normalize old history into ancestor capacities; middle capacity four uses the exact cubic cut potential, middle capacity three combines a bracketed unit part with a reserved source rank pair, and smaller capacities use the checked disjoint small-axis theorem.
Positive labels and one contiguous ancestor child run split into three nonempty blocks; distinct outer and middle axes.
Middle ancestor capacity at most four and outer ancestor capacity at most k-3.
Both new maxima, old history and block lengths are arbitrary; no maximum positivity, sibling coupling, singleton-end, or recursive-potential premise. The top two outer-capacity bands remain outside this theorem.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_interval_complement_middle_capacity_four_below_saturation (σ : Ctx.Context)
  (hpositive : ∀ x j v, σ.letterAt x=Ctx.Letter.ext j v → 1≤j)
  (b l m r : ℕ) (hpos : σ.childPositions=List.range' b (l+m+r))
  (hl : 0<l) (hm : 0<m) (hr : 0<r)
  (outerSide middleSide : Ctx.Side) (hne : outerSide≠middleSide)
  (outerMax middleMax : ℕ)
  (hchosen : (match middleSide with | Ctx.Side.lower => σ.cupLimit b b | Ctx.Side.upper => σ.capLimit b b)≤4)
  (hopposite : (match outerSide with | Ctx.Side.lower => σ.cupLimit b b | Ctx.Side.upper => σ.capLimit b b)≤σ.k-3) :
  (σ.part (List.range' b l ++ List.range' (b+l+m) r) outerSide outerMax).bound+
    (σ.part (List.range' (b+l) m) middleSide middleMax).bound≤σ.bound := by
  classical
  let C := σ.cupLimit b b
  let P := σ.capLimit b b
  let τ : Context := { σ with a := P + 1, u := C + 1, maxima := [] }
  let O := List.range' b l ++ List.range' (b + l + m) r
  let M := List.range' (b + l) m
  have hdis : ∀ p ∈ σ.childPositions, p ∈ O → p ∉ M := by
    intro p _ hp
    simp only [O, M, List.mem_append, List.mem_range'_1] at hp ⊢
    omega
  by_cases hsmall : min C P ≤ 2
  · exact ctx_bound_additive_disjoint_single_run_small_axis σ hpositive b (l+m+r)
      hpos (by omega) hsmall O M outerSide middleSide hne outerMax middleMax hdis
  have hC : 3 ≤ C := by omega
  have hP : 3 ≤ P := by omega
  have hCk : C ≤ σ.k - 1 := by dsimp only [C, cupLimit]; omega
  have hPk : P ≤ σ.k - 1 := by dsimp only [P, capLimit]; omega
  have hτpos : ∀ x j v, τ.letterAt x = Letter.ext j v → 1 ≤ j := hpositive
  have hτchildren : τ.childPositions = σ.childPositions := rfl
  have hτlimits (p : ℕ) : τ.cupLimit p p = C ∧ τ.capLimit p p = P := by
    constructor
    · simp [τ, cupLimit, chainExt, joinExt, leftExt, rightExt, levelsOn, levels,
        Nat.min_eq_left hCk]
    · simp [τ, capLimit, chainExt, joinExt, leftExt, rightExt, levelsOn, levels,
        Nat.min_eq_left hPk]
  have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ x j w, (ρ.part keep v m).letterAt x = Letter.ext j w → 1 ≤ j := by
    intro x j w hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep v m)
        (show (ρ.part keep v m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep v m hxl he] at hx
      split at hx
      · cases hx
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep v m hxl he] at hx
      cases hx
      omega
  have hNormalize (keep : List ℕ) (v : Side) (newMax : ℕ) :
      (σ.part keep v newMax).bound = (τ.part keep v newMax).bound := by
    let π := σ.part keep v newMax
    have hHist : π.a = σ.a ∧ π.u = σ.u ∧ π.k = σ.k ∧
        π.maxima.length = 1 + σ.maxima.length ∧
        (∀ j, 1 ≤ j → π.extPositions (j + 1) = σ.extPositions j) ∧
        (∀ j, 1 ≤ j → π.sideAt (j + 1) = σ.sideAt j) ∧
        (∀ j, 1 ≤ j → π.maximumAt (j + 1) = σ.maximumAt j) := by
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · change (newMax :: σ.maxima).length = 1 + σ.maxima.length
        simp only [List.length_cons]
        omega
      · intro j hj
        exact part_extPositions_succ σ keep v newMax hj
      · intro j hj
        exact part_sideAt_succ σ keep v newMax hj
      · intro j hj
        exact part_maximumAt_succ σ keep v newMax hj
    have hNew : ∀ j x, 1 ≤ j → j ≤ 1 → x ∈ π.extPositions j → x ∈ σ.childPositions := by
      intro j x hj hj1 hx
      have he : j = 1 := by omega
      subst j
      change x ∈ (σ.part keep v newMax).extPositions 1 at hx
      rw [part_extPositions_one hpositive keep v newMax] at hx
      exact (List.mem_filter.mp hx).1
    have hChild : ∀ x ∈ π.childPositions, x ∈ σ.childPositions := by
      intro x hx
      change x ∈ (σ.part keep v newMax).childPositions at hx
      rw [part_childPositions] at hx
      exact (List.mem_filter.mp hx).1
    have h := (ctx_single_run_descendant_bound_normalize σ b (l+m+r) hpos π 1 hHist hNew hChild
      (hPartPositive σ keep v newMax)).2
    exact h
  have hrunBound : ∀ (ρ : Context) (a n : ℕ), 0 < n →
      ρ.childPositions = List.range' a n →
      ρ.bound = baseOf (ρ.cupLimit a a) (ρ.capLimit a a) ρ.k := by
    intro ρ a n hn hps
    have hmem : ∀ p, p ∈ ρ.childPositions ↔ a ≤ p ∧ p < a + n := by
      intro p
      rw [hps, List.mem_range'_1]
    let starts := (List.range ρ.word.length).filter fun p =>
      ρ.letterAt p = Letter.child ∧ (p = 0 ∨ ρ.letterAt (p - 1) ≠ Letter.child)
    have hsubset : starts.toFinset ⊆ ({a} : Finset ℕ) := by
      intro p hp
      have hstart : p < ρ.word.length ∧ ρ.letterAt p = Letter.child ∧
          (p = 0 ∨ ρ.letterAt (p - 1) ≠ Letter.child) := by
        simpa [starts] using hp
      have hp' := (hmem p).mp
        (by simpa [childPositions] using And.intro hstart.1 hstart.2.1)
      simp only [Finset.mem_singleton]
      by_contra hpa
      have hprev : p - 1 ∈ ρ.childPositions := (hmem (p - 1)).mpr ⟨by omega, by omega⟩
      have hprev' : ρ.letterAt (p - 1) = Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hprev).2
      rcases hstart.2.2 with hz | hnot
      · omega
      · exact hnot hprev'
    have hruns : ρ.numRuns ≤ 1 := by
      calc
        ρ.numRuns = starts.toFinset.card :=
          (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
        _ ≤ ({a} : Finset ℕ).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    simp [bound, boundFuel, hruns, base_eq_baseOf, hps, List.head?_range', Nat.ne_of_gt hn]
  have hroot : σ.bound = baseOf C P σ.k :=
    hrunBound σ b (l+m+r) (by omega) hpos
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
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
  have hThreeCut (v u : Side) (hne' : v≠u) (hg : G τ v≤4) :
      (τ.part O u outerMax).bound+(τ.part M v middleMax).bound≤(G τ u).choose 2 := by
    let A := τ.part M v middleMax
    let B := τ.part O u outerMax
    let active (ρ : Context) := ρ.childPositions.toFinset.filter
      (fun p => 0<ρ.cupLimit p p ∧ 0<ρ.capLimit p p)
    let I (ρ : Context) (p : ℕ) := Finset.Icc (ρ.leftExt u 0 p+1)
      (G ρ u-1-ρ.rightExt u 0 p)
    let Pair (ρ : Context) (p : ℕ) := ((I ρ p).product (I ρ p)).filter (fun z => z.1≤z.2)
    let F := active τ
    let Q := active B
    let H : Finset ℕ := {b+l}
    let S := F.biUnion (Pair τ)
    let T := Q.biUnion (Pair B)
    let R := H.image (fun p => (τ.leftExt u 0 p+1,G τ u-1-τ.rightExt u 0 p))
    have hActive (ρ : Context) (p : ℕ) : p∈active ρ ↔
        p∈ρ.childPositions ∧ 0<ρ.cupLimit p p ∧ 0<ρ.capLimit p p := by simp [active]
    have hChild (p : ℕ) : p∈τ.childPositions ↔ b≤p ∧ p<b+(l+m+r) := by
      rw [hτchildren,hpos,List.mem_range'_1]
    have hF : ∀ p∈F, p∈τ.childPositions ∧ 0<τ.cupLimit p p ∧ 0<τ.capLimit p p := by
      intro p hp; exact (hActive τ p).mp hp
    have hQ : ∀ p∈Q, p∈B.childPositions ∧ 0<B.cupLimit p p ∧ 0<B.capLimit p p := by
      intro p hp; exact (hActive B p).mp hp
    have hQF : Q⊆F := by
      intro p hp
      obtain ⟨hc,hcup,hcap⟩ := hQ p hp
      rw [part_childPositions] at hc
      have hh := ctx_part_limits_le τ O u outerMax p p
      exact (hActive τ p).mpr ⟨(List.mem_filter.mp hc).1,
        lt_of_lt_of_le hcup hh.1,lt_of_lt_of_le hcap hh.2⟩
    have hH : ∀ p∈H, p∈F ∧ p∉O := by
      intro p hp
      have he : p=b+l := Finset.mem_singleton.mp hp
      subst p
      constructor
      · exact (hActive τ _).mpr ⟨(hChild _).mpr ⟨by omega,by omega⟩,
          by rw [(hτlimits _).1]; omega,by rw [(hτlimits _).2]; omega⟩
      · simp only [O,List.mem_append,List.mem_range'_1]
        omega
    have hh := ctx_part_tracked_rank_pair_reservation τ hτpos u O outerMax F Q H hF hQ hQF hH
    have hc := hh.2.2.1
    change T.card+R.card≤S.card at hc
    have hR : R.card=1 := by simp [R,H]
    rw [hR] at hc
    have hBg : G B v≤4 := by cases v <;> exact hg
    have hb := (ctx_small_global_axis_rank_pair_potential B (hPartPositive τ O u outerMax)
      v u hne' hBg).2
    change B.bound≤T.card at hb
    let W := Finset.Icc 1 (G τ u-1)
    let triangle := (W.product W).filter (fun z => z.1≤z.2)
    have hInside (p : ℕ) : I τ p⊆W := by
      intro z hz
      have he := Finset.mem_Icc.mp hz
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    have hSub : S⊆triangle := by
      intro z hz
      obtain ⟨p,_,hz⟩ := Finset.mem_biUnion.mp hz
      have hf := Finset.mem_filter.mp hz
      have hp := Finset.mem_product.mp hf.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hInside p hp.1,hInside p hp.2⟩,hf.2⟩
    have hWG : W.card+1=G τ u := by
      have hposG : 1≤G τ u := by cases u <;> simp only [G,τ] <;> omega
      simp only [W,Nat.card_Icc]
      omega
    have hTriangle : triangle.card=(G τ u).choose 2 := by
      change ((W.product W).filter (fun z => z.1≤z.2)).card=(G τ u).choose 2
      rw [hCardPairs,hWG]
    have hS : S.card≤(G τ u).choose 2 := (Finset.card_le_card hSub).trans_eq hTriangle
    have hOne : 1∈A.levels := by simp [A,part_levels]
    have hMark (p : ℕ) (hp : p∈τ.childPositions) (hn : p∉M) : p∈A.extPositions 1 := by
      rw [part_extPositions_one hτpos]
      exact List.mem_filter.mpr ⟨hp,by simp [hn]⟩
    have hL : b∈A.extPositions 1 := hMark b ((hChild b).mpr ⟨le_rfl,by omega⟩)
      (by simp only [M,List.mem_range'_1]; omega)
    have hRMark : b+l+m∈A.extPositions 1 := hMark (b+l+m)
      ((hChild _).mpr ⟨by omega,by omega⟩) (by simp only [M,List.mem_range'_1]; omega)
    have hs : A.sideAt 1=v := part_sideAt_one_of_mem hτpos M v middleMax hL
    have hAg : G A v≤4 := by cases v <;> exact hg
    have hInsideA : ∀ p∈A.childPositions, b<p ∧ p<b+l+m := by
      intro p hp
      rw [part_childPositions] at hp
      have hm' : p∈M := of_decide_eq_true (List.mem_filter.mp hp).2
      have he := List.mem_range'_1.mp hm'
      omega
    have ha := ((ctx_bracketed_children_unit_bound A (hPartPositive τ M v middleMax)
      v 1 1 b (b+l+m) hOne hOne hs hs hL hRMark hAg).2 hInsideA).2
    change B.bound+A.bound≤(G τ u).choose 2
    omega
  have hThreeLeft (p k : ℕ) (hp : 3≤p) (hpk : p≤k-3) :
      baseOf 3 p k=(p+1).choose 2 := by
    unfold baseOf
    rw [if_neg (by omega),if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    rw [show p+1+(3+1)-4=p+1 by omega]
    exact Nat.choose_symm (show 2≤p+1 by omega)
  have hThreeRight (p k : ℕ) (hp : 3≤p) (hpk : p≤k-3) :
      baseOf p 3 k=(p+1).choose 2 := by
    unfold baseOf
    rw [if_neg (by omega),if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    rw [show 3+1+(p+1)-4=p+1 by omega]
  have hMBlock : M ∈ τ.blocks := by
    unfold blocks
    simp only [List.mem_filter,List.mem_flatMap,List.mem_map,List.mem_range,decide_eq_true_eq]
    refine ⟨⟨l,?_,m-1,?_,?_⟩,?_⟩
    · rw [hτchildren,hpos,List.length_range']; omega
    · rw [hτchildren,hpos,List.length_range']; omega
    · rw [show m-1+1=m by omega,hτchildren,hpos,List.drop_range',Nat.mul_one,
        List.take_range'_of_length_ge (by omega)]
    · simp only [M,List.length_range',hτchildren,hpos]
      omega
  have hComplement (v : Side) (q : ℕ) :
      τ.part (τ.childPositions.filter (· ∉ M)) v q=τ.part O v q := by
    apply part_congr
    intro p hp
    have hb : b≤p ∧ p<b+(l+m+r) := by
      simpa only [hτchildren,hpos,List.mem_range'_1] using hp
    simp only [List.mem_filter,decide_eq_true_eq,hp,true_and,M,O,List.mem_append,List.mem_range'_1]
    omega
  have hCut (v u : Side) (hne' : v≠u) (hg : G τ v≤5) :
      (τ.part O u outerMax).bound+(τ.part M v middleMax).bound≤(G τ u-1+2).choose 3 := by
    have hh := ctx_small_global_axis_rank_triple_potential τ hτpos v u hne' hg
    have hc := (hh.2.2.2 M hMBlock middleMax outerMax).1
    rw [hComplement] at hc
    have hb := hc.trans hh.2.2.1
    simpa only [Nat.add_comm] using hb
  have hFourLeft (p k : ℕ) (hp : 3≤p) (hpk : p≤k-3) :
      baseOf 4 p k=(p+2).choose 3 := by
    unfold baseOf
    rw [if_neg (by omega),if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    rw [show p+1+(4+1)-4=p+2 by omega]
    have hh := Nat.choose_symm (show 3≤p+2 by omega)
    simpa only [show p+2-3=p+1-2 by omega] using hh
  have hFourRight (p k : ℕ) (hp : 3≤p) (hpk : p≤k-3) :
      baseOf p 4 k=(p+2).choose 3 := by
    unfold baseOf
    rw [if_neg (by omega),if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    rw [show 4+1+(p+1)-4=p+2 by omega]
  change (σ.part O outerSide outerMax).bound+(σ.part M middleSide middleMax).bound≤σ.bound
  rw [hNormalize,hNormalize,hroot]
  cases outerSide <;> cases middleSide
  · exact False.elim (hne rfl)
  · change P≤4 at hchosen
    change C≤σ.k-3 at hopposite
    by_cases hP3 : P≤3
    · have he : P=3 := by omega
      rw [he,hThreeRight C σ.k hC hopposite]
      have hh := hThreeCut Side.upper Side.lower (by decide) (by change P+1≤4; omega)
      exact hh
    · have he : P=4 := by omega
      rw [he,hFourRight C σ.k hC hopposite]
      have hh := hCut Side.upper Side.lower (by decide) (by change P+1≤5; omega)
      simpa only [G,τ,Nat.add_sub_cancel] using hh
  · change C≤4 at hchosen
    change P≤σ.k-3 at hopposite
    by_cases hC3 : C≤3
    · have he : C=3 := by omega
      rw [he,hThreeLeft P σ.k hP hopposite]
      have hh := hThreeCut Side.lower Side.upper (by decide) (by change C+1≤4; omega)
      exact hh
    · have he : C=4 := by omega
      rw [he,hFourLeft P σ.k hP hopposite]
      have hh := hCut Side.lower Side.upper (by decide) (by change C+1≤5; omega)
      simpa only [G,τ,Nat.add_sub_cancel] using hh
  · exact False.elim (hne rfl)

end ErdosSzekeres
