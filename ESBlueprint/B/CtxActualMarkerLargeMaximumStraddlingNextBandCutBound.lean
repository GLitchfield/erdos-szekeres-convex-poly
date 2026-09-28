import ESBlueprint.B.CtxYoungestMarkerTripleFacePotential
import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum
import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit
import ESBlueprint.B.CtxEraseLevelBoundMono
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Remove the youngest-marker and empty-opposite-history restrictions from the straddling extreme cut. Erase all other source levels, using checked erasure monotonicity and local part commutation, then pay the retained unit part and two fixed companion triangular faces. No recursive quadratic or experimental width-product premise. Positive labels, distinct axes, chosen global at most five, and any actual indexed chosen marker at N. Additional chosen and opposite history, repeated markers, maxima and positive unindexed barriers are arbitrary. Opposite global at most k-1; no lower bound on k or opposite width. The chosen kept list is convex in child order and contains source children strictly on both sides of the marker. Chosen new maximum at least k-2; opposite new maximum is arbitrary. No youngest-marker, empty-history, exact-depth, sibling-coupling, singleton-end or recursive-potential premise. Top-band and nonstraddling extreme cuts remain outside this theorem.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_actual_marker_large_maximum_straddling_next_band_cut_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p=Ctx.Letter.ext j v → 1≤j)
  (s t : Ctx.Side) (hne : s≠t) (N x : ℕ)
  (hN : N∈σ.levels) (hNs : σ.sideAt N=s) (hx : x∈σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)≤5)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)≤σ.k-1)
  (keep : List ℕ) (hkeep : ∀ p∈keep, p∈σ.childPositions)
  (hconvex : ∀ a∈keep, ∀ b∈keep, ∀ p∈σ.childPositions, a<p → p<b → p∈keep)
  (l r : ℕ) (hl : l∈keep) (hr : r∈keep) (hlx : l<x) (hxr : x<r)
  (m n : ℕ) (hmaximum : σ.k-2≤m) :
  let A := σ.part keep s m
  let B := σ.part (σ.childPositions.filter (·∉keep)) t n
  (∀ f g, Ctx.Context.boundFuel f A+Ctx.Context.boundFuel g B≤(σ.k-2)^2-(σ.k-2)+1) ∧
    A.bound+B.bound≤(σ.k-2)^2-(σ.k-2)+1 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
  let letter (D L : ℕ) : Letter → Letter := fun x => match x with
    | Letter.child => Letter.child
    | Letter.ext j v => Letter.ext (idx D L j) v
  let norm (ρ : Context) (L : ℕ) : Context :=
    { ρ with word := ρ.word.map (letter ρ.maxima.length L), maxima := ρ.maxima.eraseIdx (L-1) }
  let up (L j : ℕ) := if j < L then j else j+1
  have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1 ≤ j ∧ j ≤ ρ.maxima.length := by
    simp only [levels, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro hj; exact ⟨j-1, by omega, by omega⟩
  have hSorted (ρ : Context) : ρ.levels.Pairwise (· < ·) := by
    unfold levels
    exact List.pairwise_lt_range.map (fun x => x+1) (fun a b h => Nat.add_lt_add_right h 1)
  have hLen (ρ : Context) (L : ℕ) : (norm ρ L).word.length = ρ.word.length := by
    simp only [norm, List.length_map]
  have hLetter (ρ : Context) (L p : ℕ) :
      (norm ρ L).letterAt p = letter ρ.maxima.length L (ρ.letterAt p) := by
    simp only [norm, letterAt, List.getElem?_map]
    cases ρ.word[p]? <;> rfl
  have hIsChild (ρ : Context) (L p : ℕ) :
      (norm ρ L).letterAt p = Letter.child ↔ ρ.letterAt p = Letter.child := by
    rw [hLetter]
    cases ρ.letterAt p <;> simp [letter]
  have hChild (ρ : Context) (L : ℕ) : (norm ρ L).childPositions = ρ.childPositions := by
    simp only [childPositions, hLen, hIsChild]
  have hRuns (ρ : Context) (L : ℕ) : (norm ρ L).numRuns = ρ.numRuns := by
    simp only [numRuns, hLen, ne_eq, hIsChild]
  have hBlocks (ρ : Context) (L : ℕ) : (norm ρ L).blocks = ρ.blocks := by
    simp only [blocks, hChild]
  have hK (ρ : Context) (L : ℕ) : (norm ρ L).k = ρ.k := rfl
  have hDepth (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels) :
      (norm ρ L).maxima.length = ρ.maxima.length-1 := by
    have hh := (hLevelMem ρ L).mp hL
    exact List.length_eraseIdx_of_lt (by omega)
  have hLive (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) :
      1 ≤ j ∧ j < ρ.maxima.length ∧ up L j ∈ ρ.levels := by
    have hh := (hLevelMem ρ L).mp hL
    have hj' := (hLevelMem (norm ρ L) j).mp hj
    rw [hDepth ρ L hL] at hj'
    refine ⟨hj'.1, by omega, ?_⟩
    apply (hLevelMem ρ _).mpr
    dsimp [up]
    split_ifs <;> omega
  have hIndex (D L i j : ℕ) (hL : 1 ≤ L) (hLD : L ≤ D)
      (hj : 1 ≤ j) (hjD : j < D) : idx D L i = j ↔ i = up L j := by
    dsimp [idx, up]
    split_ifs <;> omega
  have hExt (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) :
      (norm ρ L).extPositions j = ρ.extPositions (up L j) := by
    have hLj := (hLevelMem ρ L).mp hL
    have hj' := hLive ρ L j hL hj
    simp only [extPositions, hLen, hLetter]
    apply List.filter_congr
    intro p _
    cases ρ.letterAt p with
    | child => rfl
    | ext i v => simp only [letter, hIndex _ _ i j hLj.1 hLj.2 hj'.1 hj'.2.1]
  have hSide (ρ : Context) (L j : ℕ) (hL : L ∈ ρ.levels)
      (hj : j ∈ (norm ρ L).levels) : (norm ρ L).sideAt j = ρ.sideAt (up L j) := by
    simp only [sideAt, hExt ρ L j hL hj]
    cases hh : (ρ.extPositions (up L j)).head? with
    | none => rfl
    | some p =>
      dsimp only
      rw [hLetter]
      cases ρ.letterAt p <;> rfl
  have hPositive (ρ : Context) (L : ℕ) (hL : L ∈ ρ.levels)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) :
      ∀ p j v, (norm ρ L).letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hj
    rw [hLetter] at hj
    have hLB := (hLevelMem ρ L).mp hL
    cases he : ρ.letterAt p with
    | child => simp only [he, letter] at hj; cases hj
    | ext i z =>
      rw [he] at hj
      have hi := hPos p i z he
      have hnew : 1 ≤ idx ρ.maxima.length L i := by
        dsimp only [idx]
        split_ifs <;> omega
      change Letter.ext (idx ρ.maxima.length L i) z = Letter.ext j v at hj
      cases hj
      exact hnew
  have hNormPart (ρ : Context) (keep : List ℕ) (v : Side) (m L : ℕ) (hL : 1 ≤ L) :
      norm (ρ.part keep v m) (L+1) = (norm ρ L).part keep v m := by
    have hi (j : ℕ) : idx (ρ.maxima.length+1) (L+1) (j+1) = idx ρ.maxima.length L j + 1 := by
      dsimp [idx]; split_ifs <;> omega
    have hnew : idx (ρ.maxima.length+1) (L+1) 1 = 1 := by simp [idx]; omega
    have hm : (m :: ρ.maxima).eraseIdx (L+1-1) = m :: ρ.maxima.eraseIdx (L-1) := by
      rw [show L+1-1 = (L-1)+1 by omega, List.eraseIdx_cons_succ]
    have hw : (norm (ρ.part keep v m) (L+1)).word = ((norm ρ L).part keep v m).word := by
      change ((ρ.part keep v m).word.map (letter (m :: ρ.maxima).length (L+1))) =
        (List.range (norm ρ L).word.length).map (fun p => match (norm ρ L).letterAt p with
          | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 v
          | Letter.ext j w => Letter.ext (j+1) w)
      rw [hLen]
      simp only [part, List.map_map, List.length_cons, Function.comp_def]
      apply List.map_congr_left
      intro p _
      rw [hLetter]
      cases ρ.letterAt p with
      | child => by_cases hp : p ∈ keep <;> simp [hp, letter, hnew]
      | ext j w => simp only [letter, hi]
    change Context.mk ρ.a ρ.u ρ.k _ ((m :: ρ.maxima).eraseIdx (L+1-1)) =
      Context.mk ρ.a ρ.u ρ.k _ (m :: ρ.maxima.eraseIdx (L-1))
    rw [hm]
    exact congrArg (fun w => Context.mk ρ.a ρ.u ρ.k w (m :: ρ.maxima.eraseIdx (L-1))) hw
  have hBase (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p=Ctx.Letter.ext j v → 1≤j)
  (s t : Ctx.Side) (hne : s≠t) (N x : ℕ)
  (hN : N∈σ.levels) (hNs : σ.sideAt N=s) (hx : x∈σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)≤5)
  (hclear : σ.levelsOn t 0=[])
  (hyoung : ∀ j∈σ.levelsOn s N, σ.extPositions j=[])
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)≤σ.k-1)
  (keep : List ℕ) (hkeep : ∀ p∈keep, p∈σ.childPositions)
  (hconvex : ∀ a∈keep, ∀ b∈keep, ∀ p∈σ.childPositions, a<p → p<b → p∈keep)
  (l r : ℕ) (hl : l∈keep) (hr : r∈keep) (hlx : l<x) (hxr : x<r)
  (m n : ℕ) (hmaximum : σ.k-2≤m) :
  let A := σ.part keep s m
  let B := σ.part (σ.childPositions.filter (·∉keep)) t n
  (∀ f g, Ctx.Context.boundFuel f A+Ctx.Context.boundFuel g B≤(σ.k-2)^2-(σ.k-2)+1) ∧
    A.bound+B.bound≤(σ.k-2)^2-(σ.k-2)+1 := by
    classical
    let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
    let rest := σ.childPositions.filter (· ∉ keep)
    let A := σ.part keep s m
    let B := σ.part rest t n
    let w := G σ t-1
    let target := (σ.k-2)^2-(σ.k-2)+1
    change (∀ f g, boundFuel f A+boundFuel g B≤target) ∧ A.bound+B.bound≤target
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
    have hPosA := hPartPositive σ keep s m
    have hPosB := hPartPositive σ rest t n
    have hAlevel : 1∈A.levels := by simp [A,part_levels]
    have hAmax : A.maximumAt 1=m := part_maximumAt_one σ keep s m
    have hA := ctx_bound_le_one_of_large_sibling_maximum A hPosA 1 hAlevel
      (by rw [hAmax]; exact hmaximum)
    have hBChild (p : ℕ) : p∈B.childPositions ↔ p∈σ.childPositions ∧ p∉keep := by
      simp [B,rest,part_childPositions]
    have hNew (p : ℕ) (hp : p∈keep) : p∈B.extPositions 1 := by
      rw [part_extPositions_one hpositive rest t n]
      exact List.mem_filter.mpr ⟨hkeep p hp,by simp [rest,hp]⟩
    have hNewKeep (p : ℕ) (hp : p∈B.extPositions 1) : p∈keep := by
      rw [part_extPositions_one hpositive rest t n] at hp
      have hs := (List.mem_filter.mp hp).1
      have hn : p∉rest := of_decide_eq_true (List.mem_filter.mp hp).2
      by_contra hnot
      exact hn (List.mem_filter.mpr ⟨hs,by simp [hnot]⟩)
    have hBL := hNew l hl
    have hBR := hNew r hr
    have hBside : B.sideAt 1=t := part_sideAt_one_of_mem hpositive rest t n hBL
    have hOn : B.levelsOn t 0=[1] := by
      rw [part_levelsOn_self_zero hBside,hclear]
      rfl
    have hNpos : 1≤N := one_le_of_mem_levels hN
    have hBN : N+1∈B.levels := by
      rw [part_levels]
      exact List.mem_cons_of_mem 1 (List.mem_map.mpr ⟨N,hN,rfl⟩)
    have hBNside : B.sideAt (N+1)=s := (part_sideAt_succ σ rest t n hNpos).trans hNs
    have hxB : x∈B.extPositions (N+1) := by
      rw [part_extPositions_succ σ rest t n hNpos]
      exact hx
    have hBYoung : ∀ j∈B.levelsOn s (N+1), B.extPositions j=[] := by
      intro j hj
      rw [part_levelsOn_other_succ (show B.sideAt 1≠s by rw [hBside]; exact Ne.symm hne) hNpos] at hj
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hj
      rw [part_extPositions_succ σ rest t n (one_le_of_mem_levelsOn hi).1]
      exact hyoung i hi
    have hBGlobal : G B s≤5 := by cases s <;> exact hglobal
    have hOpp : G B t=G σ t := by cases t <;> rfl
    have hwk : w≤σ.k-2 := by change G σ t≤σ.k-1 at hopposite; dsimp only [w]; omega
    have hLeftOrder (p : ℕ) (hp : p∈B.childPositions) (hpx : p<x) :
        ∀ q∈B.extPositions 1, p<q := by
      intro q hq
      have hp' := (hBChild p).mp hp
      have hq' := hNewKeep q hq
      by_contra hnot
      by_cases he : q=p
      · subst q
        exact hp'.2 hq'
      have hqp : q<p := by omega
      exact hp'.2 (hconvex q hq' r hr p hp'.1 hqp (by omega))
    have hRightOrder (p : ℕ) (hp : p∈B.childPositions) (hxp : x<p) :
        ∀ q∈B.extPositions 1, q<p := by
      intro q hq
      have hp' := (hBChild p).mp hp
      have hq' := hNewKeep q hq
      by_contra hnot
      by_cases he : q=p
      · subst q
        exact hp'.2 hq'
      have hpq : p<q := by omega
      exact hp'.2 (hconvex l hl q hq' p hp'.1 (by omega) hpq)
    have hLeftTrace (p : ℕ) (hp : p∈B.childPositions) (hpx : p<x) :
        B.leftExt t 0 p=0 ∧ B.rightExt t 0 p=1 := by
      have hnil : (B.extPositions 1).filter (·<p)=[] := by
        apply List.filter_eq_nil_iff.mpr
        intro q hq
        have h := hLeftOrder p hp hpx q hq
        simp only [decide_eq_true_eq]
        omega
      have hmem : r∈(B.extPositions 1).filter (p<·) := by
        simp only [List.mem_filter,decide_eq_true_eq]
        exact ⟨hBR,by omega⟩
      have hnonempty := List.ne_nil_of_mem hmem
      constructor
      · simp [leftExt_eq,hOn,leftStep,hnil]
      · have hstep : (rightStep B (p,0) 1).2=1 := by
          simp only [rightStep,List.head?_eq_some_head hnonempty]
        simp [rightExt_eq,hOn,hstep]
    have hRightTrace (p : ℕ) (hp : p∈B.childPositions) (hxp : x<p) :
        B.leftExt t 0 p=1 ∧ B.rightExt t 0 p=0 := by
      have hnil : (B.extPositions 1).filter (p<·)=[] := by
        apply List.filter_eq_nil_iff.mpr
        intro q hq
        have h := hRightOrder p hp hxp q hq
        simp only [decide_eq_true_eq]
        omega
      have hmem : l∈(B.extPositions 1).filter (·<p) := by
        simp only [List.mem_filter,decide_eq_true_eq]
        exact ⟨hBL,by omega⟩
      have hnonempty := List.ne_nil_of_mem hmem
      constructor
      · have hstep : (leftStep B (p,0) 1).2=1 := by
          simp only [leftStep,List.getLast?_eq_some_getLast hnonempty]
        simp [leftExt_eq,hOn,hstep]
      · simp [rightExt_eq,hOn,rightStep,hnil]
    let active := B.childPositions.toFinset.filter (fun p => 0<B.cupLimit p p ∧ 0<B.capLimit p p)
    let I (p : ℕ) := Finset.Icc (B.leftExt t 0 p+1) (w-B.rightExt t 0 p)
    let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1≤z.2)
    let rows := (active.filter (fun p => p<x)).biUnion
      (fun p => ({B.leftExt t 0 p+1} : Finset ℕ).product (Q (I p)))
    let columns := (active.filter (fun p => x<p)).biUnion
      (fun p => (Q (I p)).image (fun z => (z.1,z.2,w-B.rightExt t 0 p)))
    have hFaces := ctx_youngest_marker_triple_face_potential B hPosB s t hne (N+1) x
      hBN hBNside hxB hBGlobal hBYoung
    change (∀ fuel, boundFuel fuel B≤(rows∪columns).card) ∧ B.bound≤(rows∪columns).card at hFaces
    let L := Finset.Icc 1 (w-1)
    let R := Finset.Icc 2 w
    have hActive (p : ℕ) (hp : p∈active) : p∈B.childPositions :=
      List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hRows : rows ⊆ ({1} : Finset ℕ).product (Q L) := by
      intro z hz
      obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
      have hh := Finset.mem_filter.mp hp
      have ht := hLeftTrace p (hActive p hh.1) hh.2
      simpa only [I,L,ht.1,ht.2,Nat.zero_add] using hz
    have hColumns : columns ⊆ (Q R).image (fun z => (z.1,z.2,w)) := by
      intro z hz
      obtain ⟨p,hp,hz⟩ := Finset.mem_biUnion.mp hz
      have hh := Finset.mem_filter.mp hp
      have ht := hRightTrace p (hActive p hh.1) hh.2
      simpa only [I,R,ht.1,ht.2,Nat.sub_zero,Nat.reduceAdd] using hz
    have hCardPairs (T : Finset ℕ) : (Q T).card = (T.card + 1).choose 2 := by
      rw [← Finset.card_sym2]
      apply Finset.card_bij (fun z _ ↦ Sym2.mk z.1 z.2)
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
          · exact ⟨(b, a), Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩, Sym2.eq_swap⟩
    have hLCard : L.card=w-1 := by simp [L]
    have hRCard : R.card=w-1 := by simp only [R,Nat.card_Icc]; omega
    have hPairL : (Q L).card=w.choose 2 := by
      by_cases hw0 : w=0
      · simp [Q,L,hw0]
      · rw [hCardPairs,hLCard,show w-1+1=w by omega]
    have hPairR : (Q R).card=w.choose 2 := by
      by_cases hw0 : w=0
      · simp [Q,R,hw0]
      · rw [hCardPairs,hRCard,show w-1+1=w by omega]
    have hRowCard : rows.card≤w.choose 2 := by
      have hproduct : (({1} : Finset ℕ).product (Q L)).card =
          ({1} : Finset ℕ).card*(Q L).card := Finset.card_product _ _
      have htarget : (({1} : Finset ℕ).product (Q L)).card=w.choose 2 := by
        rw [hproduct,Finset.card_singleton,Nat.one_mul,hPairL]
      exact (Finset.card_le_card hRows).trans_eq htarget
    have hColumnCard : columns.card≤w.choose 2 := by
      have himage : ((Q R).image (fun z => (z.1,z.2,w))).card≤(Q R).card := Finset.card_image_le
      exact (Finset.card_le_card hColumns).trans (himage.trans_eq hPairR)
    have hFaceCard : (rows∪columns).card≤2*(σ.k-2).choose 2 := by
      have hu := Finset.card_union_le rows columns
      have hm := Nat.choose_le_choose 2 hwk
      omega
    have hNumeric : 1+2*(σ.k-2).choose 2=target := by
      let z := σ.k-2
      have hh := Nat.choose_succ_right_eq z 1
      simp only [Nat.reduceAdd,Nat.choose_one_right] at hh
      have hprod : z*(z-1)=z^2-z := by simp [Nat.mul_sub_left_distrib,pow_two]
      rw [hprod] at hh
      change 1+2*z.choose 2=z^2-z+1
      omega
    have hBFuel (fuel : ℕ) : boundFuel fuel B≤2*(σ.k-2).choose 2 := (hFaces.1 fuel).trans hFaceCard
    have hBBound : B.bound≤2*(σ.k-2).choose 2 := hFaces.2.trans hFaceCard
    exact ⟨fun f g => (Nat.add_le_add (hA.1 f) (hBFuel g)).trans_eq hNumeric,
      (Nat.add_le_add hA.2 hBBound).trans_eq hNumeric⟩
  have hPartMono (ρ : Context) (L : ℕ) (hL : L∈ρ.levels)
      (keep : List ℕ) (v : Side) (m : ℕ) :
      (ρ.part keep v m).bound≤((norm ρ L).part keep v m).bound := by
    have hnext : L+1∈(ρ.part keep v m).levels := by
      rw [part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L,hL,rfl⟩)
    have hh := (ctx_erase_level_bound_mono (ρ.part keep v m) (L+1) hnext).2.2
    change (ρ.part keep v m).bound≤(norm (ρ.part keep v m) (L+1)).bound at hh
    rw [hNormPart ρ keep v m L (one_le_of_mem_levels hL)] at hh
    exact hh
  have hMain : ∀ d (ρ : Context), ρ.maxima.length=d →
      (∀ p j v, ρ.letterAt p=Letter.ext j v → 1≤j) →
      ∀ N x, N∈ρ.levels → ρ.sideAt N=s → x∈ρ.extPositions N →
      G ρ s≤5 → G ρ t≤ρ.k-1 →
      ∀ keep : List ℕ, (∀ p∈keep, p∈ρ.childPositions) →
      (∀ a∈keep, ∀ b∈keep, ∀ p∈ρ.childPositions, a<p → p<b → p∈keep) →
      ∀ l r, l∈keep → r∈keep → l<x → x<r →
      ∀ m n, ρ.k-2≤m →
      (ρ.part keep s m).bound+(ρ.part (ρ.childPositions.filter (·∉keep)) t n).bound≤
        (ρ.k-2)^2-(ρ.k-2)+1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro ρ hd hPos N x hN hNs hx hGs hGt keep hKeep hConvex l r hl hr hlx hxr m n hMax
      have hNB := (hLevelMem ρ N).mp hN
      by_cases hOne : ρ.maxima.length=1
      · have hN1 : N=1 := by omega
        have hlevels : ρ.levels=[N] := by rw [hN1]; simp [levels,hOne]
        have hclear : ρ.levelsOn t 0=[] := by
          simp [levelsOn,hlevels,hNs,hne]
        have hyoung : ∀ j∈ρ.levelsOn s N, ρ.extPositions j=[] := by
          rw [hN1,levelsOn_one]
          simp
        exact (hBase ρ hPos s t hne N x hN hNs hx (by cases s <;> exact hGs) hclear hyoung
          (by cases t <;> exact hGt)
          keep hKeep hConvex l r hl hr hlx hxr m n hMax).2
      let L := if N=1 then 2 else 1
      have hLB : 1≤L ∧ L≤ρ.maxima.length ∧ L≠N := by
        dsimp only [L]
        split_ifs <;> omega
      have hL : L∈ρ.levels := (hLevelMem ρ L).mpr ⟨hLB.1,hLB.2.1⟩
      let N' := if N<L then N else N-1
      have hN' : N'∈(norm ρ L).levels := by
        apply (hLevelMem (norm ρ L) N').mpr
        rw [hDepth ρ L hL]
        dsimp only [N']
        split_ifs <;> omega
      have hRecoverN : up L N'=N := by
        dsimp only [up,N']
        split_ifs <;> omega
      have hNs' : (norm ρ L).sideAt N'=s := by
        rw [hSide ρ L N' hL hN',hRecoverN]
        exact hNs
      have hx' : x∈(norm ρ L).extPositions N' := by
        rw [hExt ρ L N' hL hN',hRecoverN]
        exact hx
      have hD : (norm ρ L).maxima.length<d := by rw [hDepth ρ L hL]; omega
      have hBound := ih (norm ρ L).maxima.length hD (norm ρ L) rfl
        (hPositive ρ L hL hPos) N' x hN' hNs' hx' hGs hGt keep
        (by simpa only [hChild] using hKeep)
        (by simpa only [hChild] using hConvex) l r hl hr hlx hxr m n hMax
      rw [hChild] at hBound
      exact (Nat.add_le_add (hPartMono ρ L hL keep s m)
        (hPartMono ρ L hL (ρ.childPositions.filter (·∉keep)) t n)).trans hBound
  have hBound := hMain σ.maxima.length σ rfl hpositive N x hN hNs hx hglobal hopposite
    keep hkeep hconvex l r hl hr hlx hxr m n hmaximum
  have hFuelFull (ρ : Context) (fuel : ℕ) : boundFuel fuel ρ≤ρ.bound := by
    by_cases hf : ρ.childPositions.length+1≤fuel
    · exact (boundFuel_eq_bound ρ hf).le
    · exact boundFuel_mono (by omega : fuel≤ρ.childPositions.length+1) ρ
  exact ⟨fun f g => (Nat.add_le_add (hFuelFull _ f) (hFuelFull _ g)).trans hBound,hBound⟩

end ErdosSzekeres
