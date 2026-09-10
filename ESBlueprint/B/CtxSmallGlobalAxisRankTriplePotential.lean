import ESBlueprint.B.CtxSmallGlobalAxisRankPairPotential
import ESBlueprint.B.CtxYoungestMarkerTripleFacePotential
import ESBlueprint.B.CtxActiveTwoBoundaryMarkerRankUnionBound
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Bound every fuel and the full context recurrence by the exact union of ordered opposite-rank triples when the chosen global is at most five, and bound that union by choose(opposite width+2,3). Positive labels and distinct axes are the only other hypotheses; indexed histories, sibling maxima, inactive children and unindexed barriers are arbitrary. Fuel induction uses the checked youngest-marker triple faces for endpoint cuts, and the checked two-boundary rank-union bound for internally bracketed chosen intervals. Existing pair reservations exclude the endpoint pairs of the corresponding reserved triples; all finite counting and lifting arguments remain local. Removes the actual-marker requirement from the global-five polynomial potential. It is an ordinary cubic estimate, not the unresolved saturated quadratic saving.

Also expose both orientations of every proper interval cut, with arbitrary sibling maxima and no source run-count premise. Additional search: `global-five-rank-triple-cut-potential-search.json` returned no hits.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_small_global_axis_rank_triple_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let interval := fun p => Finset.Icc (σ.leftExt t 0 p+1) (w-σ.rightExt t 0 p)
  let triples := active.biUnion (fun p =>
    ((interval p).product ((interval p).product (interval p))).filter
      (fun z => z.1 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2))
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ triples.card) ∧
    σ.bound ≤ triples.card ∧ triples.card ≤ (w+2).choose 3 ∧
    (∀ keep ∈ σ.blocks, ∀ m n,
      (σ.part keep s m).bound + (σ.part (σ.childPositions.filter (· ∉ keep)) t n).bound ≤ triples.card ∧
      (σ.part (σ.childPositions.filter (· ∉ keep)) s m).bound + (σ.part keep t n).bound ≤ triples.card) := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let C (ρ : Context) (v : Side) (p : ℕ) := match v with
    | Side.lower => ρ.cupLimit p p | Side.upper => ρ.capLimit p p
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let I (ρ : Context) (p : ℕ) :=
    Finset.Icc (ρ.leftExt t 0 p+1) (G ρ t-1-ρ.rightExt t 0 p)
  let Pairs (T : Finset ℕ) := (T.product T).filter (fun z => z.1 ≤ z.2)
  let Triples (T : Finset ℕ) := (T.product (T.product T)).filter
    (fun z => z.1 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2)
  let Tri (ρ : Context) (p : ℕ) := Triples (I ρ p)
  let Pair (ρ : Context) (p : ℕ) := Pairs (I ρ p)
  let Rows (ρ : Context) (F : Finset ℕ) :=
    F.biUnion (fun p => ({ρ.leftExt t 0 p+1} : Finset ℕ).product (Pairs (I ρ p)))
  let Cols (ρ : Context) (F : Finset ℕ) :=
    F.biUnion (fun p => (Pairs (I ρ p)).image (fun z => (z.1,z.2,G ρ t-1-ρ.rightExt t 0 p)))
  let S (ρ : Context) := (active ρ).biUnion (Tri ρ)
  let Convex (ρ : Context) (ks : List ℕ) := ∀ a ∈ ks, ∀ b ∈ ks,
    ∀ z ∈ ρ.childPositions, a ≤ z → z ≤ b → z ∈ ks
  change (∀ fuel, boundFuel fuel σ ≤ (S σ).card) ∧ σ.bound ≤ (S σ).card ∧
    (S σ).card ≤ (G σ t-1+2).choose 3 ∧
    (∀ keep ∈ σ.blocks, ∀ m n,
      (σ.part keep s m).bound + (σ.part (σ.childPositions.filter (· ∉ keep)) t n).bound ≤ (S σ).card ∧
      (σ.part (σ.childPositions.filter (· ∉ keep)) s m).bound + (σ.part keep t n).bound ≤ (S σ).card)
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by
    simp [active]
  have hPositivePart (ρ : Context) (keep : List ℕ) (t : Side) (m : ℕ) :
      ∀ x j v, (ρ.part keep t m).letterAt x = Letter.ext j v → 1 ≤ j := by
    intro x j v hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep t m)
        (show (ρ.part keep t m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep t m hxl he] at hx
      split at hx
      · cases hx
      · cases hx; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep t m hxl he] at hx
      cases hx; omega
  have hGPart (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) (w : Side) :
      G (ρ.part keep v m) w = G ρ w := by cases w <;> rfl
  have hPartActive (ρ : Context) (keep : List ℕ) (t : Side) (m p : ℕ)
      (hp : p ∈ active (ρ.part keep t m)) : p ∈ active ρ ∧ p ∈ keep := by
    obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
    rw [part_childPositions] at hc
    obtain ⟨hc, hk⟩ := List.mem_filter.mp hc
    simp only [decide_eq_true_eq] at hk
    have hle := ctx_part_limits_le ρ keep t m p p
    exact ⟨(hActive _ _).mpr ⟨hc, by omega, by omega⟩, hk⟩
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
  have hTriple (T : Finset ℕ) (z : ℕ × ℕ × ℕ) : z ∈ Triples T ↔
      z.1 ∈ T ∧ z.2.1 ∈ T ∧ z.2.2 ∈ T ∧ z.1 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2 := by
    constructor
    · intro hz
      have hf := Finset.mem_filter.mp hz
      have hp := Finset.mem_product.mp hf.1
      have hq := Finset.mem_product.mp hp.2
      exact ⟨hp.1,hq.1,hq.2,hf.2⟩
    · intro hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hz.1,Finset.mem_product.mpr ⟨hz.2.1,hz.2.2.1⟩⟩,hz.2.2.2⟩
  have hCardTriples (T : Finset ℕ) : (Triples T).card = (T.card+2).choose 3 := by
    induction T using Finset.induction_on_max with
    | empty => norm_num [Triples]
    | insert a T hmax ih =>
      have ha : a ∉ T := by intro h; have hh := hmax a h; omega
      let V := (Pairs (insert a T)).image (fun z => (z.1,z.2,a))
      have hsplit : Triples (insert a T) = Triples T ∪ V := by
        ext z
        constructor
        · intro hz
          have hh := (hTriple _ z).mp hz
          by_cases hc : z.2.2=a
          · apply Finset.mem_union_right
            refine Finset.mem_image.mpr ⟨(z.1,z.2.1), ?_, ?_⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hh.1,hh.2.1⟩,hh.2.2.2.1⟩
            · exact Prod.ext rfl (Prod.ext rfl hc.symm)
          · have hcT : z.2.2 ∈ T := (Finset.mem_insert.mp hh.2.2.1).resolve_left hc
            have hca := hmax _ hcT
            have hla : z.1 ≠ a := by omega
            have hba : z.2.1 ≠ a := by omega
            exact Finset.mem_union_left _ ((hTriple _ z).mpr
              ⟨(Finset.mem_insert.mp hh.1).resolve_left hla,
               (Finset.mem_insert.mp hh.2.1).resolve_left hba,hcT,hh.2.2.2⟩)
        · intro hz
          rcases Finset.mem_union.mp hz with hz | hz
          · have hh := (hTriple _ z).mp hz
            exact (hTriple _ z).mpr ⟨Finset.mem_insert_of_mem hh.1,
              Finset.mem_insert_of_mem hh.2.1,Finset.mem_insert_of_mem hh.2.2.1,hh.2.2.2⟩
          · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
            have hh := Finset.mem_filter.mp hp
            have hab : p.2 ≤ a := by
              rcases Finset.mem_insert.mp (Finset.mem_product.mp hh.1).2 with he | he
              · exact he.le
              · exact (hmax _ he).le
            exact (hTriple _ _).mpr ⟨(Finset.mem_product.mp hh.1).1,
              (Finset.mem_product.mp hh.1).2,by simp,hh.2,hab⟩
      have hdis : Disjoint (Triples T) V := by
        apply Finset.disjoint_left.mpr
        intro z hz hv
        obtain ⟨p,_,he⟩ := Finset.mem_image.mp hv
        have hc := (hTriple _ z).mp hz
        have hec : a=z.2.2 := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) he
        exact ha (hec.symm ▸ hc.2.2.1)
      have hV : V.card = (T.card+2).choose 2 := by
        rw [Finset.card_image_of_injective]
        · simpa only [Pairs,Finset.card_insert_of_notMem ha] using hCardPairs (insert a T)
        · intro p q he
          exact Prod.ext (congrArg (fun z : ℕ × ℕ × ℕ => z.1) he)
            (congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) he)
      rw [hsplit,Finset.card_union_of_disjoint hdis,ih,hV,Finset.card_insert_of_notMem ha]
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (Nat.choose_succ_succ (T.card+2) 2).symm
  have hBaseFour (p k : ℕ) (hp : p ≤ k-1) : baseOf 4 p k ≤ (p+2).choose 3 := by
    by_cases hp0 : p=0
    · subst p; simp [baseOf]
    by_cases hp1 : p=1
    · subst p; norm_num [baseOf]
    have hp2 : 2 ≤ p := by omega
    simp only [baseOf,if_neg (show ¬(4=0 ∨ p=0) by omega),
      if_neg (show ¬(4=1 ∨ p=1) by omega)]
    by_cases hclass : p+3 ≤ k
    · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
      have hr : p+1+(4+1)-4=p+2 := by omega
      rw [hr]
      have hh := Nat.choose_symm (show 3 ≤ p+2 by omega)
      simpa only [show p+2-3=p+1-2 by omega] using hh.le
    have hk : k=p+1 ∨ k=p+2 := by omega
    rcases hk with rfl | rfl
    · rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
      have hw : decomposableBinomialWindow (p+1) (4+1) (p+1) =
          1+(p-1)+(p-1).choose 2+(p-1).choose 3 := by
        norm_num [decomposableBinomialWindow,Finset.sum_Icc_succ_top,
          show p+1-2=p-1 by omega]
      rw [hw]
      have hA := Nat.choose_succ_succ (p-1) 2
      have hB := Nat.choose_succ_succ p 2
      have hC := Nat.choose_succ_succ (p+1) 2
      have hD := Nat.choose_succ_succ (p-1) 1
      have hE := Nat.choose_succ_succ p 1
      simp only [Nat.choose_one_right,Nat.succ_eq_add_one,Nat.add_assoc,Nat.reduceAdd,show p-1+1=p by omega] at hA hB hC hD hE
      omega
    · rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
      have hw : decomposableBinomialWindow (p+1) (4+1) (p+2) =
          p+p.choose 2+p.choose 3 := by
        norm_num [decomposableBinomialWindow,Finset.sum_Icc_succ_top,
          show p+2-(p+1)=1 by omega]
      rw [hw]
      have hA := Nat.choose_succ_succ p 2
      have hB := Nat.choose_succ_succ (p+1) 2
      have hC := Nat.choose_succ_succ p 1
      simp only [Nat.choose_one_right,Nat.succ_eq_add_one,Nat.add_assoc,Nat.reduceAdd] at hA hB hC
      omega
  have hBaseLower (c p k : ℕ) (hc : c ≤ 4) (hp : p ≤ k-1) :
      baseOf c p k ≤ (p+2).choose 3 := (baseOf_mono hc le_rfl).trans (hBaseFour p k hp)
  have hBaseSwap (x y k : ℕ) (hx : x ≤ k - 1) (hy : y ≤ k - 1) :
      baseOf x y k = baseOf y x k := by
    have hz (r : ℕ) : baseOf 0 r k = 0 := by simp [baseOf]
    have hz' (r : ℕ) : baseOf r 0 k = 0 := by simp [baseOf]
    apply Nat.le_antisymm
    · have hh := ctx_base_cross_axis_transfer 0 y x x k le_rfl hx (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
    · have hh := ctx_base_cross_axis_transfer 0 x y y k le_rfl hy (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
  have hBaseUpper (c p k : ℕ) (hp : p ≤ 4) (hc : c ≤ k-1) (hpk : p ≤ k-1) :
      baseOf c p k ≤ (c+2).choose 3 := by
    rw [hBaseSwap c p k hc hpk]
    exact hBaseLower p c k hp hc
  have hWidth (ρ : Context) (p : ℕ) : C ρ t p ≤ (I ρ p).card := by
    simp only [I, Nat.card_Icc]
    cases t <;> simp only [G, C, cupLimit, capLimit, chainExt] <;> omega
  have hBase (ρ : Context) (hg : G ρ s ≤ 5) : ρ.base ≤ (S ρ).card := by
    rw [base_eq_baseOf]
    cases he : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ (S ρ).card
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr he)
      by_cases hz : ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0
      · simp [baseOf, hz]
      have hpos : 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by omega
      have hc : C ρ s p ≤ 4 := by
        cases s <;> simp only [C, G, cupLimit, capLimit] at hg ⊢ <;> omega
      have hcupk : ρ.cupLimit p p ≤ ρ.k - 1 := by dsimp only [cupLimit]; omega
      have hcapk : ρ.capLimit p p ≤ ρ.k - 1 := by dsimp only [capLimit]; omega
      have hleaf : baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ (C ρ t p + 2).choose 3 := by
        cases s <;> cases t
        · exact False.elim (hne rfl)
        · exact hBaseLower _ _ _ hc hcapk
        · exact hBaseUpper _ _ _ hc hcupk hcapk
        · exact False.elim (hne rfl)
      have hsub : Tri ρ p ⊆ S ρ := fun z hz =>
        Finset.mem_biUnion.mpr ⟨p, (hActive ρ p).mpr ⟨hp, hpos⟩, hz⟩
      have hcard : (Tri ρ p).card = ((I ρ p).card + 2).choose 3 := hCardTriples (I ρ p)
      exact hleaf.trans ((Nat.choose_le_choose 3 (Nat.add_le_add_right (hWidth ρ p) 2)).trans
        (hcard.symm.le.trans (Finset.card_le_card hsub)))
  have hBlockConvex (ρ : Context) (ks : List ℕ) (hk : ks ∈ ρ.blocks) : Convex ρ ks := by
    obtain ⟨i, l, _, _, hwindow⟩ := exists_take_drop_of_mem_blocks hk
    have hinfix : ks <:+: ρ.childPositions := by
      refine ⟨ρ.childPositions.take i, (ρ.childPositions.drop i).drop (l+1), ?_⟩
      rw [hwindow, List.append_assoc, List.take_append_drop, List.take_append_drop]
    obtain ⟨pre, post, he⟩ := hinfix
    have he' : pre ++ (ks ++ post) = ρ.childPositions := by simpa only [List.append_assoc] using he
    have hs : (pre ++ (ks ++ post)).Pairwise (· < ·) := by
      rw [he']
      exact childPositions_pairwise ρ
    have hbefore : ∀ a ∈ pre, ∀ b ∈ ks, a < b := by
      intro a ha b hb
      exact (List.pairwise_append.mp hs).2.2 a ha b (List.mem_append_left post hb)
    have hafter : ∀ a ∈ ks, ∀ b ∈ post, a < b :=
      (List.pairwise_append.mp (List.pairwise_append.mp hs).2.1).2.2
    intro a ha b hb z hz haz hzb
    rw [← he'] at hz
    rcases List.mem_append.mp hz with hz | hz
    · have hh := hbefore z hz a ha
      omega
    · rcases List.mem_append.mp hz with hz | hz
      · exact hz
      · have hh := hafter b hb z hz
        omega
  have hOutside (ρ : Context) (ks : List ℕ) (hconv : Convex ρ ks)
      (a b z : ℕ) (ha : a ∈ ks) (hb : b ∈ ks) (hz : z ∈ ρ.childPositions) (hzn : z ∉ ks) :
      z < min a b ∨ max a b < z := by
    by_contra h
    by_cases hab : a ≤ b
    · exact hzn (hconv a ha b hb z hz (by omega) (by omega))
    · exact hzn (hconv b hb a ha z hz (by omega) (by omega))
  have hPairMem (ρ : Context) (p : ℕ) (z : ℕ × ℕ) : z ∈ Pair ρ p ↔
      z.1 ∈ I ρ p ∧ z.2 ∈ I ρ p ∧ z.1 ≤ z.2 := by
    constructor
    · intro hz
      have hf := Finset.mem_filter.mp hz
      have hp := Finset.mem_product.mp hf.1
      exact ⟨hp.1,hp.2,hf.2⟩
    · intro hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz.1,hz.2.1⟩,hz.2.2⟩
  have hEnds (ρ : Context) (F : Finset ℕ) (z : ℕ × ℕ × ℕ)
      (hz : z ∈ F.biUnion (Tri ρ)) : (z.1,z.2.2) ∈ F.biUnion (Pair ρ) ∧
        z.1 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2 := by
    obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
    have hh := (hTriple _ z).mp hz
    exact ⟨Finset.mem_biUnion.mpr ⟨p,hp,(hPairMem _ _ _).mpr
      ⟨hh.1,hh.2.2.1,by omega⟩⟩,hh.2.2.2⟩
  have hLift (ρ : Context) (F : Finset ℕ) (z : ℕ × ℕ × ℕ)
      (horder : z.1 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2)
      (hz : (z.1,z.2.2) ∈ F.biUnion (Pair ρ)) : z ∈ F.biUnion (Tri ρ) := by
    obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
    have hh := (hPairMem _ _ _).mp hz
    have hL := Finset.mem_Icc.mp hh.1
    have hR := Finset.mem_Icc.mp hh.2.1
    exact Finset.mem_biUnion.mpr ⟨p,hp,(hTriple _ z).mpr
      ⟨hh.1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hh.2.1,horder⟩⟩
  have hLiftSubset (ρ υ : Context) (F Q : Finset ℕ)
      (hsub : Q.biUnion (Pair υ) ⊆ F.biUnion (Pair ρ)) :
      Q.biUnion (Tri υ) ⊆ F.biUnion (Tri ρ) := by
    intro z hz
    have hh := hEnds υ Q z hz
    exact hLift ρ F z hh.2 (hsub hh.1)
  have hCut (fuel : ℕ) (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hg : G ρ s ≤ 5)
      (ih : ∀ υ : Context, (∀ p j v, υ.letterAt p = Letter.ext j v → 1 ≤ j) →
        G υ s ≤ 5 → boundFuel fuel υ ≤ (S υ).card)
      (ks js : List ℕ)
      (hpartition : ∀ p ∈ ρ.childPositions, p ∈ ks ↔ p ∉ js)
      (p0 x0 : ℕ) (hp0 : p0 ∈ ρ.childPositions) (hp0k : p0 ∈ ks)
      (hx0 : x0 ∈ ρ.childPositions) (hx0j : x0 ∈ js)
      (hconv : Convex ρ ks ∨ Convex ρ js) (m n : ℕ) :
      boundFuel fuel (ρ.part ks s m) + boundFuel fuel (ρ.part js t n) ≤ (S ρ).card := by
    let A := ρ.part ks s m
    let B := ρ.part js t n
    let F := active ρ
    let Q := active B
    let E (x : ℕ) := Rows ρ ((active A).filter (fun p => p < x)) ∪
      Cols ρ ((active A).filter (fun p => x < p))
    change boundFuel fuel A + boundFuel fuel B ≤ (S ρ).card
    have hAchild (p : ℕ) : p ∈ A.childPositions ↔ p ∈ ρ.childPositions ∧ p ∈ ks := by
      simp only [A, part_childPositions, List.mem_filter, decide_eq_true_eq]
    have hBchild (p : ℕ) : p ∈ B.childPositions ↔ p ∈ ρ.childPositions ∧ p ∈ js := by
      simp only [B, part_childPositions, List.mem_filter, decide_eq_true_eq]
    have hp0A : p0 ∈ A.childPositions := (hAchild p0).mpr ⟨hp0, hp0k⟩
    have hx0B : x0 ∈ B.childPositions := (hBchild x0).mpr ⟨hx0, hx0j⟩
    have hANotJ (p : ℕ) (hp : p ∈ A.childPositions) : p ∉ js := by
      have hp' := (hAchild p).mp hp
      exact (hpartition p hp'.1).mp hp'.2
    have hBNotK (p : ℕ) (hp : p ∈ B.childPositions) : p ∉ ks := by
      have hp' := (hBchild p).mp hp
      intro hk
      exact (hpartition p hp'.1).mp hk hp'.2
    have hNeAB (p q : ℕ) (hp : p ∈ A.childPositions) (hq : q ∈ B.childPositions) : p ≠ q := by
      intro he
      subst q
      exact hANotJ p hp ((hBchild p).mp hq).2
    have hAPos : ∀ p j v, A.letterAt p = Letter.ext j v → 1 ≤ j := hPositivePart ρ ks s m
    have hBPos : ∀ p j v, B.letterAt p = Letter.ext j v → 1 ≤ j := hPositivePart ρ js t n
    have hgA : G A s ≤ 5 := by simpa only [A, hGPart] using hg
    have hgB : G B s ≤ 5 := by simpa only [B, hGPart] using hg
    have hIA : boundFuel fuel A ≤ (S A).card := ih A hAPos hgA
    have hIB : boundFuel fuel B ≤ (S B).card := ih B hBPos hgB
    have hF : ∀ p ∈ F, p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by
      intro p hp
      exact (hActive ρ p).mp hp
    have hQ : ∀ p ∈ Q, p ∈ B.childPositions ∧ 0 < B.cupLimit p p ∧ 0 < B.capLimit p p := by
      intro p hp
      exact (hActive B p).mp hp
    have hQF : Q ⊆ F := by
      intro p hp
      exact (hPartActive ρ js t n p hp).1
    have hMarkA (x : ℕ) (hx : x ∈ B.childPositions) : x ∈ A.extPositions 1 := by
      rw [part_extPositions_one hPos ks s m]
      exact List.mem_filter.mpr ⟨((hBchild x).mp hx).1, by simpa using hBNotK x hx⟩
    have hASide : A.sideAt 1 = s := part_sideAt_one_of_mem hPos ks s m (hMarkA x0 hx0B)
    have hALevel : 1 ∈ A.levels := by
      simp only [levels, List.mem_map, List.mem_range]
      exact ⟨0, by simp [A, part], rfl⟩
    have hAOn : 1 ∈ A.levelsOn s 0 := by simp [levelsOn, hALevel, hASide]
    have hPureL (p : ℕ) : A.leftExt t 0 p = ρ.leftExt t 0 p :=
      (leftExt_part_other (show A.sideAt 1 ≠ t by rw [hASide]; exact hne) p).1
    have hPureR (p : ℕ) : A.rightExt t 0 p = ρ.rightExt t 0 p :=
      (rightExt_part_other (show A.sideAt 1 ≠ t by rw [hASide]; exact hne) p).1
    have hGAt : G A t = G ρ t := by cases t <;> rfl
    have hIeq (p : ℕ) : I A p = I ρ p := by simp only [I, hPureL, hPureR, hGAt]
    have hRowsEq (H : Finset ℕ) : Rows A H = Rows ρ H := by simp only [Rows, hPureL, hIeq]
    have hColsEq (H : Finset ℕ) : Cols A H = Cols ρ H := by simp only [Cols, hPureR, hIeq, hGAt]
    have hRowA (x : ℕ) (hx : x ∈ B.childPositions) : boundFuel fuel A ≤ (E x).card := by
      have hh := ctx_youngest_marker_triple_face_potential A hAPos s t hne 1 x
        hALevel hASide (hMarkA x hx) hgA (by simp [levelsOn_one])
      have hb := hh.1 fuel
      change boundFuel fuel A ≤ (Rows A ((active A).filter (fun p => p < x)) ∪
        Cols A ((active A).filter (fun p => x < p))).card at hb
      rw [hRowsEq, hColsEq] at hb
      exact hb
    have hOuter (x : ℕ) (hx : x ∈ B.childPositions)
        (hsep : ∀ p ∈ A.childPositions, ∀ q ∈ B.childPositions,
          (p < x → p < q) ∧ (x < p → q < p)) :
        boundFuel fuel A + boundFuel fuel B ≤ (S ρ).card := by
      let L := (active A).filter (fun p => p < x)
      let R := (active A).filter (fun p => x < p)
      have hL : ∀ p ∈ L, p ∈ F ∧ p ∉ js := by
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).1
        exact ⟨(hPartActive ρ ks s m p hp').1, hANotJ p ((hActive A p).mp hp').1⟩
      have hR : ∀ p ∈ R, p ∈ F ∧ p ∉ js := by
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).1
        exact ⟨(hPartActive ρ ks s m p hp').1, hANotJ p ((hActive A p).mp hp').1⟩
      have hleft : ∀ p ∈ L, ∀ q ∈ Q, p < q := by
        intro p hp q hq
        have hp' := Finset.mem_filter.mp hp
        exact (hsep p ((hActive A p).mp hp'.1).1 q (hQ q hq).1).1 hp'.2
      have hright : ∀ p ∈ R, ∀ q ∈ Q, q < p := by
        intro p hp q hq
        have hp' := Finset.mem_filter.mp hp
        exact (hsep p ((hActive A p).mp hp'.1).1 q (hQ q hq).1).2 hp'.2
      have hh := ctx_part_tracked_rank_pair_end_reservations ρ hPos t js n F Q L R
        hF hQ hQF hL hR hleft hright
      let RP := L.biUnion (fun p => ({ρ.leftExt t 0 p+1} : Finset ℕ).product (I ρ p))
      let CP := R.biUnion (fun p => (I ρ p).product ({G ρ t-1-ρ.rightExt t 0 p} : Finset ℕ))
      have hFace : ∀ z ∈ E x, (z.1,z.2.2) ∈ RP ∪ CP ∧
          z.1 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2 := by
        intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
          have hprod := Finset.mem_product.mp hz
          have he := Finset.mem_singleton.mp hprod.1
          have hpair := Finset.mem_filter.mp hprod.2
          have hr := Finset.mem_product.mp hpair.1
          have hL := Finset.mem_Icc.mp hr.1
          refine ⟨Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p,hp,?_⟩),by omega,hpair.2⟩
          exact Finset.mem_product.mpr ⟨hprod.1,hr.2⟩
        · obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
          obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
          have hpair := Finset.mem_filter.mp hq
          have hr := Finset.mem_product.mp hpair.1
          have hR := Finset.mem_Icc.mp hr.2
          refine ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,hp,?_⟩),hpair.2,hR.2⟩
          exact Finset.mem_product.mpr ⟨hr.1,by simp⟩
      have hBsub : S B ⊆ S ρ := hLiftSubset ρ B F Q
        (fun z hz => (Finset.mem_sdiff.mp (hh.2.1 hz)).1)
      have hEsub : E x ⊆ S ρ := by
        intro z hz
        have he := hFace z hz
        exact hLift ρ F z he.2 (hh.1 he.1)
      have hDis : Disjoint (S B) (E x) := by
        apply Finset.disjoint_left.mpr
        intro z hz he
        have hb := hEnds B Q z hz
        exact (Finset.mem_sdiff.mp (hh.2.1 hb.1)).2 (hFace z he).1
      have hc : (S B).card+(E x).card ≤ (S ρ).card := by
        rw [← Finset.card_union_of_disjoint hDis]
        exact Finset.card_le_card (Finset.union_subset hBsub hEsub)
      have ha := hRowA x hx
      omega
    by_cases ha : (active A).Nonempty
    · obtain ⟨pa, hpa⟩ := ha
      have hUnit (hconvK : Convex ρ ks) (l r : ℕ)
          (hl : l ∈ B.childPositions) (hr : r ∈ B.childPositions)
          (hleft : ∀ p ∈ A.childPositions, l < p)
          (hright : ∀ p ∈ A.childPositions, p < r) :
          boundFuel fuel A + boundFuel fuel B ≤ (S ρ).card := by
        have hsmall : min ((match A.sideAt 1 with | Side.lower => A.u | Side.upper => A.a)-2)
            (A.k-A.maximumAt 1) ≤ 3 := by
          rw [hASide]
          apply (Nat.min_le_left _ _).trans
          change G A s-2 ≤ 3
          omega
        have hLinear := ctx_active_two_boundary_marker_rank_union_bound A hAPos 1 l r
          hALevel (hMarkA l hl) (hMarkA r hr)
          (fun p hp _ => ⟨hleft p hp,hright p hp⟩)
          (by simp [levelsOn_one]) t (by rw [hASide]; exact hne) hsmall
        let ranks := (active A).biUnion (I ρ)
        have hAlinear : boundFuel fuel A ≤ ranks.card := by
          have hb := hLinear.1 fuel
          change boundFuel fuel A ≤ ((active A).biUnion (I A)).card at hb
          have he : I A = I ρ := funext hIeq
          rw [he] at hb
          exact hb
        have hP : ∀ p ∈ active A, p ∈ F ∧ p ∉ js := by
          intro p hp
          exact ⟨(hPartActive ρ ks s m p hp).1,hANotJ p ((hActive A p).mp hp).1⟩
        have hh := ctx_part_tracked_rank_pair_reservation ρ hPos t js n F Q (active A) hF hQ hQF hP
        let V := (active A).biUnion (fun p => (I ρ p).image
          (fun z => (ρ.leftExt t 0 p+1,z,G ρ t-1-ρ.rightExt t 0 p)))
        let reserved := (active A).image (fun p => (ρ.leftExt t 0 p+1,G ρ t-1-ρ.rightExt t 0 p))
        have hVdata : ∀ z ∈ V, (z.1,z.2.2) ∈ reserved ∧
            z.1 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2 := by
          intro z hz
          obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
          obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
          exact ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,Finset.mem_Icc.mp hq⟩
        have hVsub : V ⊆ S ρ := by
          intro z hz
          have hv := hVdata z hz
          exact hLift ρ F z hv.2 (hh.1 hv.1)
        have hBsub : S B ⊆ S ρ := hLiftSubset ρ B F Q
          (fun z hz => (Finset.mem_sdiff.mp (hh.2.1 hz)).1)
        have hDis : Disjoint (S B) V := by
          apply Finset.disjoint_left.mpr
          intro z hz hv
          have hb := hEnds B Q z hz
          exact (Finset.mem_sdiff.mp (hh.2.1 hb.1)).2 (hVdata z hv).1
        have hImage : V.image (fun z => z.2.1) = ranks := by
          ext z
          constructor
          · intro hz
            obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hz
            obtain ⟨p,hp,hv⟩ := Finset.mem_biUnion.mp hv
            obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hv
            have hqz : q=z := (congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) he).trans hvz
            exact Finset.mem_biUnion.mpr ⟨p,hp,hqz ▸ hq⟩
          · intro hz
            obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
            exact Finset.mem_image.mpr ⟨(ρ.leftExt t 0 p+1,z,G ρ t-1-ρ.rightExt t 0 p),
              Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩,rfl⟩
        have hRankCard : ranks.card ≤ V.card := by
          rw [← hImage]
          exact Finset.card_image_le
        have hc : (S B).card+V.card ≤ (S ρ).card := by
          rw [← Finset.card_union_of_disjoint hDis]
          exact Finset.card_le_card (Finset.union_subset hBsub hVsub)
        omega
      rcases hconv with hconvK | hconvJ
      · by_cases hleft : ∃ l ∈ B.childPositions, l < p0
        · obtain ⟨l, hl, hlp⟩ := hleft
          by_cases hright : ∃ r ∈ B.childPositions, p0 < r
          · obtain ⟨r, hr, hpr⟩ := hright
            apply hUnit hconvK l r hl hr
            · intro p hp
              have hh := hOutside ρ ks hconvK p0 p l hp0k ((hAchild p).mp hp).2
                ((hBchild l).mp hl).1 (hBNotK l hl)
              omega
            · intro p hp
              have hh := hOutside ρ ks hconvK p0 p r hp0k ((hAchild p).mp hp).2
                ((hBchild r).mp hr).1 (hBNotK r hr)
              omega
          · have hbefore : ∀ q ∈ B.childPositions, ∀ p ∈ A.childPositions, q < p := by
              intro q hq p hp
              have hn : ¬p0 < q := by intro h; exact hright ⟨q, hq, h⟩
              have hne' := hNeAB p0 q hp0A hq
              have hh := hOutside ρ ks hconvK p0 p q hp0k ((hAchild p).mp hp).2
                ((hBchild q).mp hq).1 (hBNotK q hq)
              omega
            apply hOuter x0 hx0B
            intro p hp q hq
            have hx := hbefore x0 hx0B p hp
            have hq' := hbefore q hq p hp
            omega
        · have hafter : ∀ p ∈ A.childPositions, ∀ q ∈ B.childPositions, p < q := by
            intro p hp q hq
            have hn : ¬q < p0 := by intro h; exact hleft ⟨q, hq, h⟩
            have hne' := hNeAB p0 q hp0A hq
            have hh := hOutside ρ ks hconvK p0 p q hp0k ((hAchild p).mp hp).2
              ((hBchild q).mp hq).1 (hBNotK q hq)
            omega
          apply hOuter x0 hx0B
          intro p hp q hq
          have hx := hafter p hp x0 hx0B
          have hq' := hafter p hp q hq
          omega
      · apply hOuter x0 hx0B
        intro p hp q hq
        have hh := hOutside ρ js hconvJ x0 q p hx0j ((hBchild q).mp hq).2
          ((hAchild p).mp hp).1 (hANotJ p hp)
        omega
    · have he := Finset.not_nonempty_iff_eq_empty.mp ha
      have hz : (S A).card = 0 := by simp [S, he]
      have hA0 : boundFuel fuel A = 0 := by omega
      have hh := ctx_part_tracked_rank_pair_reservation ρ hPos t js n F Q ∅ hF hQ hQF (by simp)
      have hBsub : S B ⊆ S ρ := hLiftSubset ρ B F Q
        (fun z hz => (Finset.mem_sdiff.mp (hh.2.1 hz)).1)
      have hc := Finset.card_le_card hBsub
      omega
  have hFuel : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      G ρ s ≤ 5 → boundFuel fuel ρ ≤ (S ρ).card := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hPos hg
      rw [boundFuel]
      split
      · exact hBase ρ hg
      · apply Ctx.getD_max?_le
        intro z hz
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hz
        obtain ⟨keep, hkeep, d, _, hz⟩ := hz
        obtain ⟨hkl, hkne, hksub⟩ := mem_blocks hkeep
        obtain ⟨p, hpk⟩ := List.exists_mem_of_ne_nil _ hkne
        have hp : p ∈ ρ.childPositions := hksub p hpk
        have hremoved : ∃ q ∈ ρ.childPositions, q ∉ keep := by
          by_contra h
          push Not at h
          have hlen := ((childPositions_nodup ρ).subperm h).length_le
          omega
        obtain ⟨q, hq, hqk⟩ := hremoved
        let rest := ρ.childPositions.filter (· ∉ keep)
        have hqrest : q ∈ rest := by simp [rest, hq, hqk]
        have hforward (a b : ℕ) : boundFuel fuel (ρ.part keep s a) +
            boundFuel fuel (ρ.part rest t b) ≤ (S ρ).card :=
          hCut fuel ρ hPos hg ih keep rest
            (by intro r hr; simp [rest, hr]) p q hp hpk hq hqrest
            (Or.inl (hBlockConvex ρ keep hkeep)) a b
        have hbackward (a b : ℕ) : boundFuel fuel (ρ.part rest s a) +
            boundFuel fuel (ρ.part keep t b) ≤ (S ρ).card :=
          hCut fuel ρ hPos hg ih rest keep
            (by intro r hr; simp [rest, hr]) q p hq hqrest hp hpk
            (Or.inr (hBlockConvex ρ keep hkeep)) a b
        have hboth (a b : ℕ) :
            (boundFuel fuel (ρ.part keep Side.lower a) +
              boundFuel fuel (ρ.part rest Side.upper b) ≤ (S ρ).card) ∧
            (boundFuel fuel (ρ.part keep Side.upper b) +
              boundFuel fuel (ρ.part rest Side.lower a) ≤ (S ρ).card) := by
          cases s <;> cases t
          · exact False.elim (hne rfl)
          · exact ⟨hforward a b, by simpa only [Nat.add_comm] using hbackward a b⟩
          · exact ⟨by simpa only [Nat.add_comm] using hbackward b a, hforward b a⟩
          · exact False.elim (hne rfl)
        rcases hz with rfl | rfl
        · exact (hboth (d + 1) (ρ.k - 1 - (d + 1))).1
        · exact (hboth (d + 1) (ρ.k - 1 - (d + 1))).2
  let T := Finset.Icc 1 (G σ t-1)
  have hRanks (p : ℕ) : I σ p ⊆ T := by
    intro z hz
    have hh := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hSub : S σ ⊆ Triples T := by
    intro z hz
    obtain ⟨p,_,hz⟩ := Finset.mem_biUnion.mp hz
    have hh := (hTriple _ z).mp hz
    exact (hTriple _ z).mpr ⟨hRanks p hh.1,hRanks p hh.2.1,hRanks p hh.2.2.1,hh.2.2.2⟩
  have hCard : (S σ).card ≤ (G σ t-1+2).choose 3 := by
    have hh := (Finset.card_le_card hSub).trans (hCardTriples T).le
    simpa only [T,Nat.card_Icc,Nat.add_sub_cancel] using hh
  refine ⟨fun fuel => hFuel fuel σ hpositive hglobal,
    hFuel (σ.childPositions.length+1) σ hpositive hglobal,hCard,?_⟩
  intro keep hkeep m n
  obtain ⟨hkl,hkne,hksub⟩ := mem_blocks hkeep
  obtain ⟨p,hpk⟩ := List.exists_mem_of_ne_nil _ hkne
  have hp : p ∈ σ.childPositions := hksub p hpk
  have hremoved : ∃ q ∈ σ.childPositions, q ∉ keep := by
    by_contra h
    push Not at h
    have hlen := ((childPositions_nodup σ).subperm h).length_le
    omega
  obtain ⟨q,hq,hqk⟩ := hremoved
  let rest := σ.childPositions.filter (· ∉ keep)
  have hqrest : q ∈ rest := by simp [rest,hq,hqk]
  have hFullPart (ks : List ℕ) (v : Side) (M : ℕ) :
      boundFuel (σ.childPositions.length+1) (σ.part ks v M) = (σ.part ks v M).bound := by
    apply boundFuel_eq_bound
    rw [part_childPositions]
    exact Nat.add_le_add_right (List.length_filter_le _ _) 1
  have hForward := hCut (σ.childPositions.length+1) σ hpositive hglobal
    (fun ρ hPos hg => hFuel (σ.childPositions.length+1) ρ hPos hg) keep rest
    (by intro r hr; simp [rest,hr]) p q hp hpk hq hqrest
    (Or.inl (hBlockConvex σ keep hkeep)) m n
  have hBackward := hCut (σ.childPositions.length+1) σ hpositive hglobal
    (fun ρ hPos hg => hFuel (σ.childPositions.length+1) ρ hPos hg) rest keep
    (by intro r hr; simp [rest,hr]) q p hq hqrest hp hpk
    (Or.inr (hBlockConvex σ keep hkeep)) m n
  exact ⟨by simpa only [hFullPart] using hForward,by simpa only [hFullPart] using hBackward⟩

end ErdosSzekeres
