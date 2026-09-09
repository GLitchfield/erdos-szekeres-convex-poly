import Mathlib.Data.Finset.Sym
import ESBlueprint.B.CtxBaseCrossAxisTransfer
import ESBlueprint.B.CtxYoungestMarkerRowColumnPotentialBound

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every-fuel and full recursive context bound by the union of ordered opposite-rank pairs available at active children whenever the chosen global is at most four. Positive labels suffice; no actual chosen marker is required. Allows empty active sets, arbitrary opposite global, older histories, maxima, unused indexed levels and positive unindexed markers. Removes the actual-marker hypothesis from the existing rank-pair potential theorem and covers chosen pointwise capacity three. Fuel induction uses the old theorem in the marker-present branch; the absent-marker branch pays outer cut parts by youngest-marker endpoint rows/columns and straddled middle parts by one reserved endpoint pair. The base is bounded by the triangular pair count. Supplies the unrestricted small-global quadratic support potential toward the remaining singleton-end sandwich additivity cases.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_small_global_axis_rank_pair_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) :
  let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let interval := fun p => Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p)
  let pairs := active.biUnion
    (fun p => ((interval p).product (interval p)).filter (fun z => z.1 ≤ z.2))
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ pairs.card) ∧ σ.bound ≤ pairs.card := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let C (ρ : Context) (v : Side) (p : ℕ) := match v with
    | Side.lower => ρ.cupLimit p p | Side.upper => ρ.capLimit p p
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let I (ρ : Context) (p : ℕ) :=
    Finset.Icc (ρ.leftExt t 0 p + 1) (G ρ t - 1 - ρ.rightExt t 0 p)
  let Tri (ρ : Context) (p : ℕ) := ((I ρ p).product (I ρ p)).filter (fun z => z.1 ≤ z.2)
  let Rows (ρ : Context) (F : Finset ℕ) :=
    F.biUnion (fun p => ({ρ.leftExt t 0 p + 1} : Finset ℕ).product (I ρ p))
  let Cols (ρ : Context) (F : Finset ℕ) :=
    F.biUnion (fun p => (I ρ p).product ({G ρ t - 1 - ρ.rightExt t 0 p} : Finset ℕ))
  let S (ρ : Context) := (active ρ).biUnion (Tri ρ)
  let Good (ρ : Context) := ∃ N x, N ∈ ρ.levels ∧ ρ.sideAt N = s ∧ x ∈ ρ.extPositions N
  let marks (ρ : Context) := (ρ.levelsOn s 0).toFinset.biUnion (fun j => (ρ.extPositions j).toFinset)
  let Convex (ρ : Context) (ks : List ℕ) := ∀ a ∈ ks, ∀ b ∈ ks,
    ∀ z ∈ ρ.childPositions, a ≤ z → z ≤ b → z ∈ ks
  change (∀ fuel, boundFuel fuel σ ≤ (S σ).card) ∧ σ.bound ≤ (S σ).card
  have hMark (ρ : Context) (x : ℕ) :
      x ∈ marks ρ ↔ ∃ l ∈ ρ.levelsOn s 0, x ∈ ρ.extPositions l := by
    simp [marks]
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by
    simp [active]
  have hNoMark (ρ : Context) (p : ℕ) (hp : p ∈ ρ.childPositions) : p ∉ marks ρ := by
    intro hm
    obtain ⟨l, _, hx⟩ := (hMark ρ p).mp hm
    have hc := (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hx).2
    simp only [decide_eq_true_eq] at hc he
    simp [hc] at he
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
  have hPartMarks (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (keep : List ℕ) (t : Side) (m x : ℕ) (hx : x ∈ marks (ρ.part keep t m)) :
      x ∈ marks ρ ∨ (t = s ∧ x ∈ ρ.childPositions ∧ x ∉ keep) := by
    obtain ⟨l, hl, hx⟩ := (hMark _ _).mp hx
    have hl' := List.mem_filter.mp hl
    have hs : (ρ.part keep t m).sideAt l = s := by simpa using hl'.2
    rw [part_levels] at hl'
    rcases List.mem_cons.mp hl'.1 with rfl | hold
    · right
      have hside := part_sideAt_one_of_mem hPos keep t m hx
      rw [part_extPositions_one hPos keep t m] at hx
      have hr := List.mem_filter.mp hx
      exact ⟨hside.symm.trans hs, hr.1, by simpa using hr.2⟩
    · left
      obtain ⟨j, hj, hjl⟩ := List.mem_map.mp hold
      subst l
      have h1 := one_le_of_mem_levels hj
      rw [part_extPositions_succ ρ keep t m h1] at hx
      rw [part_sideAt_succ ρ keep t m h1] at hs
      exact (hMark ρ x).mpr ⟨j, by simp [Context.levelsOn, hj, hs], hx⟩
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
  have hBaseThree (p k : ℕ) (hp : p ≤ k - 1) : baseOf 3 p k ≤ (p + 1).choose 2 := by
    by_cases hp0 : p = 0
    · subst p
      simp [baseOf]
    by_cases hp1 : p = 1
    · subst p
      norm_num [baseOf]
    have hp2 : 2 ≤ p := by omega
    simp only [baseOf, if_neg (show ¬(3 = 0 ∨ p = 0) by omega),
      if_neg (show ¬(3 = 1 ∨ p = 1) by omega)]
    by_cases hpk : p + 2 ≤ k
    · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
      have hrow : p + 1 + (3 + 1) - 4 = p + 1 := by omega
      have hcol : p + 1 - 2 = (p + 1) - 2 := rfl
      rw [hrow]
      exact (Nat.choose_symm (show 2 ≤ p + 1 by omega)).le
    · have hk : k = p + 1 := by omega
      subst k
      rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
      have hwindow : decomposableBinomialWindow (p + 1) (3 + 1) (p + 1) =
          1 + (p - 1) + (p - 1).choose 2 := by
        have hr : p + 1 - 2 = p - 1 := by omega
        norm_num [decomposableBinomialWindow, hr, Finset.sum_Icc_succ_top]
      rw [hwindow]
      have hp' : p = (p - 1) + 1 := by omega
      have hpascal : (p + 1).choose 2 = (p - 1).choose 2 + (p - 1) + p := by
        calc
          (p + 1).choose 2 = p + p.choose 2 := by simp [Nat.choose_succ_succ']
          _ = (p - 1).choose 2 + (p - 1) + p := by
            conv_lhs => arg 2; rw [hp']
            simp [Nat.choose_succ_succ']
            omega
      omega
  have hBaseLower (c p k : ℕ) (hc : c ≤ 3) (hp : p ≤ k - 1) :
      baseOf c p k ≤ (p + 1).choose 2 :=
    (baseOf_mono hc le_rfl).trans (hBaseThree p k hp)
  have hBaseSwap (x y k : ℕ) (hx : x ≤ k - 1) (hy : y ≤ k - 1) :
      baseOf x y k = baseOf y x k := by
    have hz (r : ℕ) : baseOf 0 r k = 0 := by simp [baseOf]
    have hz' (r : ℕ) : baseOf r 0 k = 0 := by simp [baseOf]
    apply Nat.le_antisymm
    · have hh := ctx_base_cross_axis_transfer 0 y x x k le_rfl hx (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
    · have hh := ctx_base_cross_axis_transfer 0 x y y k le_rfl hy (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
  have hBaseUpper (c p k : ℕ) (hp : p ≤ 3) (hc : c ≤ k - 1) (hpk : p ≤ k - 1) :
      baseOf c p k ≤ (c + 1).choose 2 := by
    rw [hBaseSwap c p k hc hpk]
    exact hBaseLower p c k hp hc
  have hWidth (ρ : Context) (p : ℕ) : C ρ t p ≤ (I ρ p).card := by
    simp only [I, Nat.card_Icc]
    cases t <;> simp only [G, C, cupLimit, capLimit, chainExt] <;> omega
  have hBase (ρ : Context) (hg : G ρ s ≤ 4) : ρ.base ≤ (S ρ).card := by
    rw [base_eq_baseOf]
    cases he : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr he)
      by_cases hz : ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0
      · simp [baseOf, hz]
      have hpos : 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by omega
      have hc : C ρ s p ≤ 3 := by
        cases s <;> simp only [C, G, cupLimit, capLimit] at hg ⊢ <;> omega
      have hcupk : ρ.cupLimit p p ≤ ρ.k - 1 := by dsimp only [cupLimit]; omega
      have hcapk : ρ.capLimit p p ≤ ρ.k - 1 := by dsimp only [capLimit]; omega
      have hleaf : baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ (C ρ t p + 1).choose 2 := by
        cases s <;> cases t
        · exact False.elim (hne rfl)
        · exact hBaseLower _ _ _ hc hcapk
        · exact hBaseUpper _ _ _ hc hcupk hcapk
        · exact False.elim (hne rfl)
      have hsub : Tri ρ p ⊆ S ρ := fun z hz =>
        Finset.mem_biUnion.mpr ⟨p, (hActive ρ p).mpr ⟨hp, hpos⟩, hz⟩
      have hcard : (Tri ρ p).card = ((I ρ p).card + 1).choose 2 := hCardPairs (I ρ p)
      exact hleaf.trans ((Nat.choose_le_choose 2 (Nat.add_le_add_right (hWidth ρ p) 1)).trans
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
  have hNoOld (ρ : Context) (hgood : ¬ Good ρ) (p : ℕ) : p ∉ marks ρ := by
    intro hp
    obtain ⟨j, hj, hp⟩ := (hMark ρ p).mp hp
    have hh := List.mem_filter.mp hj
    have hside : ρ.sideAt j = s := by simpa using hh.2
    exact hgood ⟨j, p, hh.1, hside, hp⟩
  have hCut (fuel : ℕ) (ρ : Context)
      (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
      (hg : G ρ s ≤ 4) (hgood : ¬ Good ρ)
      (ih : ∀ υ : Context, (∀ p j v, υ.letterAt p = Letter.ext j v → 1 ≤ j) →
        G υ s ≤ 4 → boundFuel fuel υ ≤ (S υ).card)
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
    have hgA : G A s ≤ 4 := by simpa only [A, hGPart] using hg
    have hgB : G B s ≤ 4 := by simpa only [B, hGPart] using hg
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
      have hh := ctx_youngest_marker_row_column_potential_bound A hAPos s t hne 1 x
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
      have hc := hh.2.2.1
      change (S B).card + (E x).card ≤ (S ρ).card at hc
      have ha := hRowA x hx
      omega
    by_cases ha : (active A).Nonempty
    · obtain ⟨pa, hpa⟩ := ha
      have hUnit (hconvK : Convex ρ ks) (l r : ℕ)
          (hl : l ∈ B.childPositions) (hr : r ∈ B.childPositions)
          (hleft : ∀ p ∈ A.childPositions, l < p)
          (hright : ∀ p ∈ A.childPositions, p < r) :
          boundFuel fuel A + boundFuel fuel B ≤ (S ρ).card := by
        have hunit : ∀ p ∈ A.childPositions, C A s p ≤ 1 := by
          intro p hp
          have hL := hOneLeft A s 1 p l hAOn (hMarkA l hl) (hleft p hp)
          have hR := hOneRight A s 1 p r hAOn (hMarkA r hr) (hright p hp)
          cases s <;> simp only [C, G, cupLimit, capLimit, chainExt] at hgA ⊢ <;> omega
        have hclear : ∀ p ∈ A.childPositions, ∀ q ∈ A.childPositions,
            ∀ j ∈ A.levelsOn s 0, ∀ z ∈ A.extPositions j, z < min p q ∨ max p q < z := by
          intro p hp q hq j hj z hz
          have hzm := (hMark A z).mpr ⟨j, hj, hz⟩
          rcases hPartMarks ρ hPos ks s m z hzm with hold | hnew
          · exact False.elim (hNoOld ρ hgood z hold)
          · exact hOutside ρ ks hconvK p q z ((hAchild p).mp hp).2 ((hAchild q).mp hq).2
              hnew.2.1 hnew.2.2
        have hOne := (ctx_bound_le_one_of_clear_unit_axis A hAPos s hunit hclear).1 fuel
        have hP : ∀ p ∈ ({pa} : Finset ℕ), p ∈ F ∧ p ∉ js := by
          intro p hp
          have he := Finset.mem_singleton.mp hp
          subst p
          exact ⟨(hPartActive ρ ks s m pa hpa).1, hANotJ pa ((hActive A pa).mp hpa).1⟩
        have hh := ctx_part_tracked_rank_pair_reservation ρ hPos t js n F Q {pa} hF hQ hQF hP
        have hc : (S B).card + 1 ≤ (S ρ).card := by
          simpa only [Finset.image_singleton, Finset.card_singleton] using hh.2.2.1
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
      have hc : (S B).card ≤ (S ρ).card := by
        simpa only [Finset.image_empty, Finset.card_empty, Nat.add_zero] using hh.2.2.1
      omega
  have hFuel : ∀ fuel (ρ : Context),
      (∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j) →
      G ρ s ≤ 4 → boundFuel fuel ρ ≤ (S ρ).card := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hPos hg
      by_cases hgood : Good ρ
      · obtain ⟨N, x, hN, hNs, hx⟩ := hgood
        exact (ctx_one_level_rank_pair_potential_bound ρ hPos s t hne N x hN hNs hx hg).1 (fuel + 1)
      · rw [boundFuel]
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
            hCut fuel ρ hPos hg hgood ih keep rest
              (by intro r hr; simp [rest, hr]) p q hp hpk hq hqrest
              (Or.inl (hBlockConvex ρ keep hkeep)) a b
          have hbackward (a b : ℕ) : boundFuel fuel (ρ.part rest s a) +
              boundFuel fuel (ρ.part keep t b) ≤ (S ρ).card :=
            hCut fuel ρ hPos hg hgood ih rest keep
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
  exact ⟨fun fuel => hFuel fuel σ hpositive hglobal,
    hFuel (σ.childPositions.length + 1) σ hpositive hglobal⟩

end ErdosSzekeres
