import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.DeepSplitProfileGluingExists
import ESBlueprint.B.DeepSplitFiniteEndpointConstraintsIff
import ESBlueprint.B.DecomposableColoringPushforwardExists
import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit
import ErdosSzekeres.StructuralChargingNextState578SpanCounterexample
import Mathlib.Order.Interval.Finset.Fin

namespace ErdosSzekeres

/-- Every admissible two-full-cap core at p>=5 extends exactly to three actual upper singleton ancestors, preserving decomposition, realization and ranks, and satisfying the literal S^p 1L3L2L S^p context with maxima111.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.decomposable_coloring_pushforward_exists, ErdosSzekeres.deepSplit_profile_gluing_exists, ErdosSzekeres.deepSplit_finite_endpoint_constraints_iff, ErdosSzekeres.ctx_satisfies_of_deepBelowSplit, ErdosSzekeres.IsDecomposable.isSweepRealizable
@dangling-ok General actual-reach interface for the persistent Q4 two-cap interval-root obstruction; any admissible core is retained, with no finite-instance node or B/backend-equivalence assertion. -/
theorem two_full_cap_blocks_context_history_extension (p : ℕ) (hp : 5 ≤ p) (χ : TripleColoring (2 * p))
(hdec : IsDecomposable χ)
(hfirst : IsCapSet χ (Finset.univ.filter fun i : Fin (2 * p) ↦ i.val < p))
(hlast : IsCapSet χ (Finset.univ.filter fun i : Fin (2 * p) ↦ p ≤ i.val))
(hcup : ∀ T : Finset (Fin (2 * p)), IsCupSet χ T → T.card ≤ 4)
(hcap : ∀ T : Finset (Fin (2 * p)), IsCapSet χ T → T.card ≤ p)
(hno : ¬ ContainsStrongPolygonSet χ Finset.univ (p + 1)) :
let σ : Ctx.Context :=
  ⟨p + 1, 5, p + 1,
    List.replicate p Ctx.Letter.child ++
      [Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
       Ctx.Letter.ext 2 Ctx.Side.lower] ++ List.replicate p Ctx.Letter.child,
    [1, 1, 1]⟩
σ.WellFormed ∧
∃ f : Fin (2 * p) ↪o Fin (2 * p + 3),
  (∀ i : Fin (2 * p), (f i).val = if i.val < p then i.val else i.val + 3) ∧
  ∃ ψ : TripleColoring (2 * p + 3),
    ψ.restrict f = χ ∧ IsDecomposable ψ ∧ IsSweepRealizable ψ ∧
    (∀ T : Finset (Fin (2 * p + 3)), IsCupSet ψ T → T.card ≤ 4) ∧
    (∀ T : Finset (Fin (2 * p + 3)), IsCapSet ψ T → T.card ≤ p) ∧
    (¬ ContainsStrongPolygonSet ψ Finset.univ (p + 1)) ∧
    Ctx.Satisfies ψ (Finset.univ.image f) σ ∧
    ∃ a b c : Fin (2 * p + 3),
      a.val = p ∧ b.val = p + 1 ∧ c.val = p + 2 ∧
      HasDeepBelowSplit ψ (Finset.univ.image f) {a} ∧
      HasDeepBelowSplit ψ (insert a (Finset.univ.image f)) {c} ∧
      HasDeepBelowSplit ψ (insert c (insert a (Finset.univ.image f))) {b} := by
  classical
  dsimp only
  have cup_agree {n : ℕ} {κ η : TripleColoring n} {S T : Finset (Fin n)}
      (hTS : T ⊆ S) (h : κ.AgreeOnTriples η S) :
      IsCupSet κ T ↔ IsCupSet η T := by
    constructor <;> intro hT t hi hj hk
    · exact (h t (hTS hi) (hTS hj) (hTS hk)).symm.trans (hT t hi hj hk)
    · exact (h t (hTS hi) (hTS hj) (hTS hk)).trans (hT t hi hj hk)
  have cap_agree {n : ℕ} {κ η : TripleColoring n} {S T : Finset (Fin n)}
      (hTS : T ⊆ S) (h : κ.AgreeOnTriples η S) :
      IsCapSet κ T ↔ IsCapSet η T := by
    constructor <;> intro hT t hi hj hk
    · exact (h t (hTS hi) (hTS hj) (hTS hk)).symm.trans (hT t hi hj hk)
    · exact (h t (hTS hi) (hTS hj) (hTS hk)).trans (hT t hi hj hk)
  have card_split {n : ℕ} (T L U : Finset (Fin n)) (hT : T ⊆ L ∪ U) :
      T.card ≤ (T ∩ L).card + (T ∩ U).card := by
    have heq : (T ∩ L) ∪ (T ∩ U) = T := by
      ext z
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
      · intro hz
        rcases Finset.mem_union.mp (hT hz) with hL | hU
        · exact Or.inl ⟨hz, hL⟩
        · exact Or.inr ⟨hz, hU⟩
    simpa only [heq] using Finset.card_union_le (T ∩ L) (T ∩ U)
  have noStrong_card {n : ℕ} (κ : TripleColoring n) (S : Finset (Fin n))
      (hS : S.card ≤ p) : ¬ ContainsStrongPolygonSet κ S (p + 1) := by
    rintro ⟨T, hTS, hcard, _⟩
    have := Finset.card_le_card hTS
    omega
  have add_point {n : ℕ} (κ : TripleColoring n) (S : Finset (Fin n))
      (q : Fin n) (hq : q ∉ S) (hSd : IsDecomposableOn κ S)
      (hC : ∀ T, T ⊆ S → IsCupSet κ T → T.card ≤ 4)
      (hA : ∀ T, T ⊆ S → IsCapSet κ T → T.card ≤ p)
      (hN : ¬ ContainsStrongPolygonSet κ S (p + 1))
      (hSpan : ∀ T, T ⊆ S → IsCupSet κ T → T.card = 4 →
        ∃ x ∈ T, ∃ y ∈ T, x < q ∧ q < y) :
      ∃ η : TripleColoring n, η.AgreeOnTriples κ S ∧
        HasDeepBelowSplit η S {q} ∧ IsDecomposableOn η (insert q S) ∧
        (¬ ContainsStrongPolygonSet η (insert q S) (p + 1)) ∧
        (∀ T, T ⊆ insert q S → IsCupSet η T → T.card ≤ 4) ∧
        (∀ T, T ⊆ insert q S → IsCapSet η T → T.card ≤ p) := by
    have hdis : Disjoint S {q} := by simp [hq]
    have hsingle (T : Finset (Fin n)) (hT : T ⊆ {q}) : T.card ≤ 1 := by
      simpa using Finset.card_le_card hT
    obtain ⟨η, hL, _, hd, hdec, hno, _⟩ :=
      deepSplit_profile_gluing_exists κ κ hdis hSd (.singleton q) hN
        (noStrong_card κ {q} (by simp; omega))
        (fun _ ↦ True) (fun _ ↦ True)
        (by intros; trivial) (by intros; trivial)
        (by intros; trivial) (by intros; trivial)
        (by
          intro C D hCS hDQ hCup _
          have := hC C hCS hCup
          have := hsingle D hDQ
          omega)
    have hBounds :
        (∀ T, T ⊆ S ∪ {q} → IsCupSet η T → T.card ≤ 4) ∧
        (∀ T, T ⊆ S ∪ {q} → IsCapSet η T → T.card ≤ p) := by
      apply (deepSplit_finite_endpoint_constraints_iff hd
        (fun T ↦ T.card ≤ 4) (fun T ↦ T.card ≤ p)).mpr
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
      · intro T hTS hT
        exact hC T hTS ((cup_agree hTS hL).mp hT)
      · intro T hTQ _
        have := hsingle T hTQ
        omega
      · intro C hCS hCup x hx hend
        have hxq : x = q := Finset.mem_singleton.mp hx
        subst x
        have hCupOld := (cup_agree hCS hL).mp hCup
        have hsize := hC C hCS hCupOld
        by_cases hsmall : C.card ≤ 3
        · have := Finset.card_insert_le q C
          omega
        have hfour : C.card = 4 := by omega
        obtain ⟨x, hx, y, hy, hxq, hqy⟩ := hSpan C hCS hCupOld hfour
        rcases hend with hleft | hright
        · have := hleft x hx
          omega
        · have := hright y hy
          omega
      · intro C hCS hCup x y hx hy hxy _ _
        have hxq := Finset.mem_singleton.mp hx
        have hyq := Finset.mem_singleton.mp hy
        subst x
        subst y
        exact (lt_irrefl q hxy).elim
      · intro T hTQ _
        have := hsingle T hTQ
        omega
      · intro T hTS hT
        exact hA T hTS ((cap_agree hTS hL).mp hT)
      · intro C hCQ _ x _ _
        have := hsingle C hCQ
        have := Finset.card_insert_le x C
        omega
      · intro C hCQ _ x y _ _ _ _ _
        have := hsingle C hCQ
        have := Finset.card_insert_le y C
        have := Finset.card_insert_le x (insert y C)
        omega
    refine ⟨η, hL, hd, ?_, ?_, ?_, ?_⟩
    · simpa only [Finset.union_singleton] using hdec
    · simpa only [Finset.union_singleton] using hno
    · simpa only [Finset.union_singleton] using hBounds.1
    · simpa only [Finset.union_singleton] using hBounds.2
  let f : Fin (2 * p) ↪o Fin (2 * p + 3) := OrderEmbedding.ofStrictMono
    (fun i ↦ (⟨if i.val < p then i.val else i.val + 3, by
      split <;> have := i.isLt <;> omega⟩ : Fin (2 * p + 3)))
    (by
      intro i j hij
      change i.val < j.val at hij
      change (if i.val < p then i.val else i.val + 3) <
        (if j.val < p then j.val else j.val + 3)
      split <;> split <;> omega)
  let a : Fin (2 * p + 3) := ⟨p, by omega⟩
  let b : Fin (2 * p + 3) := ⟨p + 1, by omega⟩
  let c : Fin (2 * p + 3) := ⟨p + 2, by omega⟩
  let S : Finset (Fin (2 * p + 3)) := Finset.univ.image f
  let A := (Finset.univ.filter fun i : Fin (2 * p) ↦ i.val < p).image f
  let B := (Finset.univ.filter fun i : Fin (2 * p) ↦ p ≤ i.val).image f
  have hAB : A ∪ B = S := by
    rw [← Finset.image_union]
    congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    omega
  have hAval (z : Fin (2 * p + 3)) (hz : z ∈ A) : z.val < p := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hi' : i.val < p := (Finset.mem_filter.mp hi).2
    simpa [f, hi'] using hi'
  have hBval (z : Fin (2 * p + 3)) (hz : z ∈ B) : p + 3 ≤ z.val := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hi' : p ≤ i.val := (Finset.mem_filter.mp hi).2
    have hi'' : ¬ i.val < p := by omega
    simp [f, hi'']
    omega
  have hSval (z : Fin (2 * p + 3)) (hz : z ∈ S) :
      z.val < p ∨ p + 3 ≤ z.val := by
    rw [← hAB] at hz
    rcases Finset.mem_union.mp hz with hA | hB
    · exact Or.inl (hAval z hA)
    · exact Or.inr (hBval z hB)
  have haS : a ∉ S := by intro hz; have := hSval a hz; dsimp [a] at this; omega
  have hbS : b ∉ S := by intro hz; have := hSval b hz; dsimp [b] at this; omega
  have hcS : c ∉ S := by intro hz; have := hSval c hz; dsimp [c] at this; omega
  have hab : a < b := by change p < p + 1; omega
  have hbc : b < c := by change p + 1 < p + 2; omega
  have hac : a < c := hab.trans hbc
  let S1 := insert a S
  let S2 := insert c S1
  have hcS1 : c ∉ S1 := by simp [S1, hcS, ne_of_gt hac]
  have hbS2 : b ∉ S2 := by simp [S2, S1, hbS, ne_of_lt hbc, ne_of_gt hab]
  have hS3 : insert b S2 = Finset.univ := by
    ext z
    simp only [Finset.mem_univ, iff_true]
    by_cases hz : z.val < p
    · have hi : z.val < 2 * p := by omega
      have hmem : z ∈ S := by
        refine Finset.mem_image.mpr ⟨⟨z.val, hi⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        simp [f, hz]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem hmem))
    by_cases hz' : p + 3 ≤ z.val
    · let i : Fin (2 * p) := ⟨z.val - 3, by have := z.isLt; omega⟩
      have hi : ¬ i.val < p := by dsimp [i]; omega
      have hmem : z ∈ S := by
        refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        simp [f, hi, i]
        omega
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem hmem))
    have hzA : z = a ∨ z = b ∨ z = c := by
      have hvals : z.val = p ∨ z.val = p + 1 ∨ z.val = p + 2 := by omega
      rcases hvals with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases hzA with rfl | rfl | rfl <;> simp [S2, S1]
  obtain ⟨κ0, hrestrict, hDecImage, hCupImage, hCapImage, hStrongImage, _⟩ :=
    decomposable_coloring_pushforward_exists χ f
  have hA0 : IsCapSet κ0 A := (hCapImage _).mp hfirst
  have hB0 : IsCapSet κ0 B := (hCapImage _).mp hlast
  have hCup0 (T : Finset (Fin (2 * p + 3))) (hTS : T ⊆ S)
      (hT : IsCupSet κ0 T) : T.card ≤ 4 := by
    obtain ⟨D, _, hDT⟩ := Finset.subset_image_iff.mp hTS
    have := hcup D ((hCupImage D).mpr (by simpa [hDT] using hT))
    rw [← hDT, Finset.card_image_of_injective _ f.injective]
    exact this
  have hCap0 (T : Finset (Fin (2 * p + 3))) (hTS : T ⊆ S)
      (hT : IsCapSet κ0 T) : T.card ≤ p := by
    obtain ⟨D, _, hDT⟩ := Finset.subset_image_iff.mp hTS
    have := hcap D ((hCapImage D).mpr (by simpa [hDT] using hT))
    rw [← hDT, Finset.card_image_of_injective _ f.injective]
    exact this
  have hNo0 : ¬ ContainsStrongPolygonSet κ0 S (p + 1) := by
    intro h
    exact hno ((hStrongImage Finset.univ (p + 1)).mpr h)
  have core_span (κ : TripleColoring (2 * p + 3))
      (hκ : κ.AgreeOnTriples κ0 S) (T : Finset (Fin (2 * p + 3)))
      (hTS : T ⊆ S) (hT : IsCupSet κ T) (hcard : 3 ≤ T.card)
      (q : Fin (2 * p + 3)) (hq0 : p ≤ q.val) (hq1 : q.val < p + 3) :
      ∃ x ∈ T, ∃ y ∈ T, x < q ∧ q < y := by
    have hAk : IsCapSet κ A :=
      (cap_agree (by rw [← hAB]; exact Finset.subset_union_left) hκ).mpr hA0
    have hBk : IsCapSet κ B :=
      (cap_agree (by rw [← hAB]; exact Finset.subset_union_right) hκ).mpr hB0
    have hcardA : (T ∩ A).card ≤ 2 := by
      simpa only [Finset.inter_comm] using inter_card_le_two_of_cup_cap hT hAk
    have hcardB : (T ∩ B).card ≤ 2 := by
      simpa only [Finset.inter_comm] using inter_card_le_two_of_cup_cap hT hBk
    have hsum := card_split T A B (by simpa only [hAB] using hTS)
    have hposA : 0 < (T ∩ A).card := by omega
    have hposB : 0 < (T ∩ B).card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hposA
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hposB
    have hxv := hAval x (Finset.mem_inter.mp hx).2
    have hyv := hBval y (Finset.mem_inter.mp hy).2
    refine ⟨x, (Finset.mem_inter.mp hx).1, y, (Finset.mem_inter.mp hy).1, ?_, ?_⟩
    · change x.val < q.val
      omega
    · change q.val < y.val
      omega
  have hSpan0 : ∀ T, T ⊆ S → IsCupSet κ0 T → T.card = 4 →
      ∃ x ∈ T, ∃ y ∈ T, x < a ∧ a < y := by
    intro T hTS hT hcard
    exact core_span κ0 (by intro t hi hj hk; rfl) T hTS hT (by omega) a
      (by rfl) (by dsimp [a]; omega)
  obtain ⟨κ1, h10, hd1, hdec1, hno1, hcup1, hcap1⟩ :=
    add_point κ0 S a haS (hDecImage Finset.univ hdec) hCup0 hCap0 hNo0 hSpan0
  have four_core (T : Finset (Fin (2 * p + 3))) (hTS : T ⊆ S1)
      (hT : IsCupSet κ1 T) (hcard : T.card = 4) : T ⊆ S := by
    by_cases haT : a ∈ T
    · let C := T ∩ S
      have hsum := card_split T S {a} (by simpa only [Finset.union_singleton] using hTS)
      have hsingle : (T ∩ {a}).card ≤ 1 := by
        simpa using Finset.card_le_card (Finset.inter_subset_right : T ∩ {a} ⊆ {a})
      have hCcard : 3 ≤ C.card := by dsimp [C]; omega
      have hCcup : IsCupSet κ1 C := FinsetPolygon.IsCupSet.mono hT Finset.inter_subset_left
      obtain ⟨x, hx, y, hy, hxa, hay⟩ := core_span κ1 h10 C
        Finset.inter_subset_right hCcup hCcard a (by rfl) (by dsimp [a]; omega)
      have hmeet : (T ∩ S).Nonempty := Finset.card_pos.mp (by dsimp [C] at hCcard; omega)
      have hend := hd1.upper_mem_cup_isSweepEndpoint
        (by simpa only [Finset.union_singleton] using hTS) hT hmeet haT (by simp)
      rcases hend with hleft | hright
      · have := hleft x (Finset.mem_inter.mp hx).1
        omega
      · have := hright y (Finset.mem_inter.mp hy).1
        omega
    · intro z hz
      rcases Finset.mem_insert.mp (hTS hz) with hza | hzS
      · exact (haT (hza ▸ hz)).elim
      · exact hzS
  have hSpan1 : ∀ T, T ⊆ S1 → IsCupSet κ1 T → T.card = 4 →
      ∃ x ∈ T, ∃ y ∈ T, x < c ∧ c < y := by
    intro T hTS hT hcard
    exact core_span κ1 h10 T (four_core T hTS hT hcard) hT (by omega) c
      (by dsimp [c]; omega) (by dsimp [c]; omega)
  obtain ⟨κ2, h21, hd2, hdec2, hno2, hcup2, hcap2⟩ :=
    add_point κ1 S1 c hcS1 hdec1 hcup1 hcap1 hno1 hSpan1
  have h20 : κ2.AgreeOnTriples κ0 S := by
    intro t hi hj hk
    exact (h21 t (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj)
      (Finset.mem_insert_of_mem hk)).trans (h10 t hi hj hk)
  have hSpan2 : ∀ T, T ⊆ S2 → IsCupSet κ2 T → T.card = 4 →
      ∃ x ∈ T, ∃ y ∈ T, x < b ∧ b < y := by
    intro T hTS hT hcard
    by_cases hcT : c ∈ T
    · let C := T ∩ S1
      have hCS1 : C ⊆ S1 := Finset.inter_subset_right
      have hCT : C ⊆ T := Finset.inter_subset_left
      have hsum := card_split T S1 {c}
        (by simpa only [Finset.union_singleton] using hTS)
      have hsingle : (T ∩ {c}).card ≤ 1 := by
        simpa using Finset.card_le_card (Finset.inter_subset_right : T ∩ {c} ⊆ {c})
      have hCcard : 3 ≤ C.card := by dsimp [C]; omega
      have hCcup : IsCupSet κ2 C := FinsetPolygon.IsCupSet.mono hT hCT
      have hmeet : (T ∩ S1).Nonempty := Finset.card_pos.mp (by dsimp [C] at hCcard; omega)
      have hend := hd2.upper_mem_cup_isSweepEndpoint
        (by simpa only [Finset.union_singleton] using hTS) hT hmeet hcT (by simp)
      have haC : a ∈ C := by
        by_contra haC
        have hCS : C ⊆ S := by
          intro z hz
          rcases Finset.mem_insert.mp (hCS1 hz) with hza | hzS
          · exact (haC (hza ▸ hz)).elim
          · exact hzS
        obtain ⟨x, hx, y, hy, hxc, hcy⟩ := core_span κ2 h20 C hCS hCcup hCcard c
          (by dsimp [c]; omega) (by dsimp [c]; omega)
        rcases hend with hleft | hright
        · have := hleft x (hCT hx)
          omega
        · have := hright y (hCT hy)
          omega
      have hright : ∀ z ∈ T, z ≤ c := by
        rcases hend with hleft | hright
        · have := hleft a (hCT haC)
          omega
        · exact hright
      have hsumC := card_split C S {a}
        (by simpa only [Finset.union_singleton] using hCS1)
      have hsingleC : (C ∩ {a}).card ≤ 1 := by
        simpa using Finset.card_le_card (Finset.inter_subset_right : C ∩ {a} ⊆ {a})
      have hpos : 0 < (C ∩ S).card := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      have hxT := hCT (Finset.mem_inter.mp hx).1
      have hxv := hSval x (Finset.mem_inter.mp hx).2
      have hxc := hright x hxT
      refine ⟨x, hxT, c, hcT, ?_, hbc⟩
      change x.val < b.val
      change x.val ≤ c.val at hxc
      dsimp [b, c] at *
      omega
    · have hTS1 : T ⊆ S1 := by
        intro z hz
        rcases Finset.mem_insert.mp (hTS hz) with hzc | hzS1
        · exact (hcT (hzc ▸ hz)).elim
        · exact hzS1
      have hCup1 := (cup_agree hTS1 h21).mp hT
      exact core_span κ2 h20 T (four_core T hTS1 hCup1 hcard) hT (by omega) b
        (by dsimp [b]; omega) (by dsimp [b]; omega)
  obtain ⟨ψ, h32, hd3, hdec3, hno3, hcup3, hcap3⟩ :=
    add_point κ2 S2 b hbS2 hdec2 hcup2 hcap2 hno2 hSpan2
  have h31 : ψ.AgreeOnTriples κ1 S1 := by
    intro t hi hj hk
    exact (h32 t (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj)
      (Finset.mem_insert_of_mem hk)).trans (h21 t hi hj hk)
  have h30 : ψ.AgreeOnTriples κ0 S := by
    intro t hi hj hk
    exact (h31 t (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj)
      (Finset.mem_insert_of_mem hk)).trans (h10 t hi hj hk)
  have hDeep1 : HasDeepBelowSplit ψ S {a} :=
    hd1.of_agreeOnTriples (by
      simpa only [Finset.union_singleton] using
        (show κ1.AgreeOnTriples ψ S1 from fun t hi hj hk ↦ (h31 t hi hj hk).symm))
  have hDeep2 : HasDeepBelowSplit ψ S1 {c} :=
    hd2.of_agreeOnTriples (by
      simpa only [Finset.union_singleton] using
        (show κ2.AgreeOnTriples ψ S2 from fun t hi hj hk ↦ (h32 t hi hj hk).symm))
  have hDecFinal : IsDecomposable ψ := by
    simpa only [IsDecomposable, hS3] using hdec3
  have hNoFinal : ¬ ContainsStrongPolygonSet ψ Finset.univ (p + 1) := by
    simpa only [hS3] using hno3
  have hCupFinal (T : Finset (Fin (2 * p + 3))) (hT : IsCupSet ψ T) : T.card ≤ 4 :=
    hcup3 T (by rw [hS3]; exact Finset.subset_univ T) hT
  have hCapFinal (T : Finset (Fin (2 * p + 3))) (hT : IsCapSet ψ T) : T.card ≤ p :=
    hcap3 T (by rw [hS3]; exact Finset.subset_univ T) hT
  have hRestrictFinal : ψ.restrict f = χ := by
    funext t
    change ψ (t.map f) = χ t
    rw [h30 (t.map f) (Finset.mem_image.mpr ⟨t.i, Finset.mem_univ _, rfl⟩)
      (Finset.mem_image.mpr ⟨t.j, Finset.mem_univ _, rfl⟩)
      (Finset.mem_image.mpr ⟨t.k, Finset.mem_univ _, rfl⟩)]
    exact congrFun hrestrict t
  let θ0 := Ctx.Context.root (p + 1) 5 (p + 1) (2 * p + 3)
  let K0 := θ0.positionsOf (Finset.univ : Finset (Fin (2 * p + 3))) S2
  let θ1 := θ0.part K0 Ctx.Side.lower 1
  let K1 := θ1.positionsOf S2 S1
  let θ2 := θ1.part K1 Ctx.Side.lower 1
  let K2 := θ2.positionsOf S1 S
  let θ3 := θ2.part K2 Ctx.Side.lower 1
  let σ : Ctx.Context :=
    ⟨p + 1, 5, p + 1,
      List.replicate p Ctx.Letter.child ++
        [Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
         Ctx.Letter.ext 2 Ctx.Side.lower] ++ List.replicate p Ctx.Letter.child,
      [1, 1, 1]⟩
  have hword0 : θ0.word.length = 2 * p + 3 := by simp [θ0, Ctx.Context.root]
  have hword1 : θ1.word.length = 2 * p + 3 := by
    simpa only [θ1, Ctx.Context.part_word_length] using hword0
  have hword2 : θ2.word.length = 2 * p + 3 := by
    simpa only [θ2, Ctx.Context.part_word_length] using hword1
  have hword3 : θ3.word.length = 2 * p + 3 := by
    simpa only [θ3, Ctx.Context.part_word_length] using hword2
  have hlet0 (i : ℕ) : θ0.letterAt i = Ctx.Letter.child := by
    simp only [θ0, Ctx.Context.root, Ctx.Context.letterAt, List.getElem?_replicate]
    split <;> rfl
  have hpositions0 : θ0.childPositions = List.range (2 * p + 3) := by
    simp [Ctx.Context.childPositions, hlet0, hword0]
  have hwf0 : θ0.WellFormed := by
    refine ⟨by change 2 ≤ p + 1; omega, by change 2 ≤ (5 : ℕ); decide,
      by change p + 1 ≤ p + 1; rfl, by change 5 ≤ p + 1; omega, ?_, ?_⟩
    · simp [θ0, Ctx.Context.root]
    · intro i l side hi
      rw [hlet0] at hi
      cases hi
  have hrootCup (i j : ℕ) : θ0.cupLimit i j = 4 := by
    change min 4 p = 4
    exact Nat.min_eq_left (by omega)
  have hrootCap (i j : ℕ) : θ0.capLimit i j = p := by
    change min p p = p
    exact Nat.min_self p
  have hStrongFinal (T : Finset (Fin (2 * p + 3)))
      (hT : IsStrongPolygonSet ψ T) : T.card ≤ p := by
    by_contra hcard
    obtain ⟨D, hDT, hDcard⟩ := Finset.exists_subset_card_eq
      (show p + 1 ≤ T.card by omega)
    exact hNoFinal ⟨D, Finset.subset_univ D, hDcard,
      FinsetPolygon.IsStrongPolygonSet.mono hT hDT⟩
  have hs0 : Ctx.Satisfies ψ (Finset.univ : Finset (Fin (2 * p + 3))) θ0 := by
    refine ⟨?_, ?_⟩
    · simp [hpositions0]
    · intro T hTS hne
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · rw [hrootCup]
        exact hCupFinal T
      · rw [hrootCap]
        exact hCapFinal T
      · change IsStrongPolygonSet ψ T → T.card ≤ p
        exact hStrongFinal T
  have hsingle (v : Fin (2 * p + 3)) : Ctx.chainMax ψ {v} false = 1 := by
    apply le_antisymm
    · apply Ctx.chainMax_le_iff.mpr
      intro T hT _
      simpa using Finset.card_le_card hT
    · exact Ctx.one_le_chainMax (Finset.singleton_nonempty v) false
  have hSne : S.Nonempty := by
    let i : Fin (2 * p) := ⟨0, by omega⟩
    exact ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hS1ne : S1.Nonempty := Finset.insert_nonempty _ _
  have hS2ne : S2.Nonempty := Finset.insert_nonempty _ _
  have hs1 : Ctx.Satisfies ψ S2 θ1 := by
    have h := (ctx_satisfies_of_deepBelowSplit θ0 hwf0 hs0 hd3
      (by simpa only [Finset.union_singleton] using hS3)
      hS2ne (Finset.singleton_nonempty b)).1
    rw [hsingle b] at h
    exact h
  have hwf1 : θ1.WellFormed :=
    hwf0.part K0 Ctx.Side.lower (by rfl) (by change 1 ≤ p + 1 - 2; omega)
  have hs2 : Ctx.Satisfies ψ S1 θ2 := by
    have h := (ctx_satisfies_of_deepBelowSplit θ1 hwf1 hs1 hDeep2
      (by simp only [Finset.union_singleton, S2])
      hS1ne (Finset.singleton_nonempty c)).1
    rw [hsingle c] at h
    exact h
  have hwf2 : θ2.WellFormed :=
    hwf1.part K1 Ctx.Side.lower (by rfl) (by change 1 ≤ p + 1 - 2; omega)
  have hs3 : Ctx.Satisfies ψ S θ3 := by
    have h := (ctx_satisfies_of_deepBelowSplit θ2 hwf2 hs2 hDeep1
      (by simp only [Finset.union_singleton, S1])
      hSne (Finset.singleton_nonempty a)).1
    rw [hsingle a] at h
    exact h
  have hwf3 : θ3.WellFormed :=
    hwf2.part K2 Ctx.Side.lower (by rfl) (by change 1 ≤ p + 1 - 2; omega)
  have hpos0 (v : Fin (2 * p + 3)) :
      (θ0.childPositions[((Finset.univ : Finset (Fin (2 * p + 3))).filter
        (· < v)).card]?).getD 0 = v.val := by
    have heq : (Finset.univ.filter (fun w : Fin (2 * p + 3) ↦ w < v)) =
        Finset.Iio v := by ext w; simp
    rw [hpositions0, heq, Fin.card_Iio, List.getElem?_range v.isLt]
    rfl
  have hpos1 (v : Fin (2 * p + 3)) (hv : v ∈ S2) :
      (θ1.childPositions[(S2.filter (· < v)).card]?).getD 0 = v.val :=
    (Ctx.Context.pos_part_eq hs0.1 (Finset.subset_univ S2)
      Ctx.Side.lower 1 hv).trans (hpos0 v)
  have hpos2 (v : Fin (2 * p + 3)) (hv : v ∈ S1) :
      (θ2.childPositions[(S1.filter (· < v)).card]?).getD 0 = v.val :=
    (Ctx.Context.pos_part_eq hs1.1 (Finset.subset_insert c S1)
      Ctx.Side.lower 1 hv).trans (hpos1 v (Finset.mem_insert_of_mem hv))
  have hK0 (v : Fin (2 * p + 3)) : v.val ∈ K0 ↔ v ∈ S2 := by
    constructor
    · intro hv
      obtain ⟨w, hw, hpos⟩ := (Ctx.Context.mem_positionsOf θ0).mp hv
      rw [hpos0 w] at hpos
      simpa only [Fin.ext hpos] using hw
    · intro hv
      exact (Ctx.Context.mem_positionsOf θ0).mpr ⟨v, hv, hpos0 v⟩
  have hK1 (v : Fin (2 * p + 3)) : v.val ∈ K1 ↔ v ∈ S1 := by
    constructor
    · intro hv
      obtain ⟨w, hw, hpos⟩ := (Ctx.Context.mem_positionsOf θ1).mp hv
      rw [hpos1 w (Finset.mem_insert_of_mem hw)] at hpos
      simpa only [Fin.ext hpos] using hw
    · intro hv
      exact (Ctx.Context.mem_positionsOf θ1).mpr
        ⟨v, hv, hpos1 v (Finset.mem_insert_of_mem hv)⟩
  have hK2 (v : Fin (2 * p + 3)) : v.val ∈ K2 ↔ v ∈ S := by
    constructor
    · intro hv
      obtain ⟨w, hw, hpos⟩ := (Ctx.Context.mem_positionsOf θ2).mp hv
      rw [hpos2 w (Finset.mem_insert_of_mem hw)] at hpos
      simpa only [Fin.ext hpos] using hw
    · intro hv
      exact (Ctx.Context.mem_positionsOf θ2).mpr
        ⟨v, hv, hpos2 v (Finset.mem_insert_of_mem hv)⟩
  have hlet1 (v : Fin (2 * p + 3)) : θ1.letterAt v.val =
      if v ∈ S2 then Ctx.Letter.child else Ctx.Letter.ext 1 Ctx.Side.lower := by
    rw [Ctx.Context.part_letterAt_of_child θ0 K0 Ctx.Side.lower 1
      (by rw [hword0]; exact v.isLt) (hlet0 v.val)]
    simp only [hK0]
  have hlet2child (v : Fin (2 * p + 3)) (hv : v ∈ S1) :
      θ2.letterAt v.val = Ctx.Letter.child := by
    have h1 : θ1.letterAt v.val = Ctx.Letter.child := by
      have hvS2 : v ∈ S2 := Finset.mem_insert_of_mem hv
      simp only [hlet1, hvS2, if_true]
    rw [Ctx.Context.part_letterAt_of_child θ1 K1 Ctx.Side.lower 1
      (by rw [hword1]; exact v.isLt) h1]
    simp only [hK1, hv, if_true]
  have hlet3 (v : Fin (2 * p + 3)) : θ3.letterAt v.val =
      if v = a then Ctx.Letter.ext 1 Ctx.Side.lower
      else if v = b then Ctx.Letter.ext 3 Ctx.Side.lower
      else if v = c then Ctx.Letter.ext 2 Ctx.Side.lower else Ctx.Letter.child := by
    by_cases hva : v = a
    · subst v
      have h2 := hlet2child a (Finset.mem_insert_self _ _)
      rw [Ctx.Context.part_letterAt_of_child θ2 K2 Ctx.Side.lower 1
        (by rw [hword2]; exact a.isLt) h2]
      simp [hK2, haS]
    by_cases hvb : v = b
    · subst v
      have h1 : θ1.letterAt b.val = Ctx.Letter.ext 1 Ctx.Side.lower := by
        simp only [hlet1, hbS2, if_false]
      have h2 : θ2.letterAt b.val = Ctx.Letter.ext 2 Ctx.Side.lower :=
        Ctx.Context.part_letterAt_of_ext θ1 K1 Ctx.Side.lower 1
          (by rw [hword1]; exact b.isLt) h1
      rw [Ctx.Context.part_letterAt_of_ext θ2 K2 Ctx.Side.lower 1
        (by rw [hword2]; exact b.isLt) h2]
      simp [hva]
    by_cases hvc : v = c
    · subst v
      have h1 : θ1.letterAt c.val = Ctx.Letter.child := by
        simp [hlet1, S2]
      have h2 : θ2.letterAt c.val = Ctx.Letter.ext 1 Ctx.Side.lower := by
        rw [Ctx.Context.part_letterAt_of_child θ1 K1 Ctx.Side.lower 1
          (by rw [hword1]; exact c.isLt) h1]
        simp only [hK1, hcS1, if_false]
      rw [Ctx.Context.part_letterAt_of_ext θ2 K2 Ctx.Side.lower 1
        (by rw [hword2]; exact c.isLt) h2]
      simp [hva, hvb]
    have hvS : v ∈ S := by
      have hv : v ∈ insert b S2 := by rw [hS3]; exact Finset.mem_univ _
      simp only [S2, S1, Finset.mem_insert] at hv
      rcases hv with h | h | h | hvS
      · exact (hvb h).elim
      · exact (hvc h).elim
      · exact (hva h).elim
      · exact hvS
    have h2 := hlet2child v (Finset.mem_insert_of_mem hvS)
    rw [Ctx.Context.part_letterAt_of_child θ2 K2 Ctx.Side.lower 1
      (by rw [hword2]; exact v.isLt) h2]
    simp only [hK2, hvS, if_true, hva, hvb, hvc, if_false]
  have hσlet (v : Fin (2 * p + 3)) : σ.letterAt v.val =
      if v.val = p then Ctx.Letter.ext 1 Ctx.Side.lower
      else if v.val = p + 1 then Ctx.Letter.ext 3 Ctx.Side.lower
      else if v.val = p + 2 then Ctx.Letter.ext 2 Ctx.Side.lower else Ctx.Letter.child := by
    by_cases hva : v.val = p
    · simp [σ, Ctx.Context.letterAt, List.getElem?_append, List.getElem?_replicate,
        hva, show p < p + 3 by omega]
    by_cases hvb : v.val = p + 1
    · simp [σ, Ctx.Context.letterAt, List.getElem?_append, List.getElem?_replicate,
        hvb, show ¬ (p + 1 < p) by omega, show p + 1 < p + 3 by omega]
    by_cases hvc : v.val = p + 2
    · simp [σ, Ctx.Context.letterAt, List.getElem?_append, List.getElem?_replicate,
        hvc, show ¬ (p + 2 < p) by omega, show p + 2 < p + 3 by omega]
    by_cases hleft : v.val < p
    · have hleft' : v.val < p + 3 := by omega
      simp [σ, Ctx.Context.letterAt, List.getElem?_append, List.getElem?_replicate,
        hleft, hleft', hva, hvb, hvc]
    have htail : p + 3 ≤ v.val := by omega
    have hnot0 : ¬ (v.val < p + 3) := by omega
    have hnot1 : ¬ (v.val - p < 3) := by omega
    have htail0 : v.val - (p + 3) < p := by have := v.isLt; omega
    have htail1 : v.val - p - 3 < p := by have := v.isLt; omega
    have hn0 : v.val - p ≠ 0 := by omega
    have hn1 : v.val - p - 1 ≠ 0 := by omega
    have hn2 : v.val - p - 1 - 1 ≠ 0 := by omega
    have htail2 : v.val - p - 1 - 1 - 1 < p := by have := v.isLt; omega
    simp [σ, Ctx.Context.letterAt, List.getElem?_append, List.getElem?_replicate,
      List.getElem?_cons, hleft, hnot0, hnot1, htail0, htail1, htail2,
      hn0, hn1, hn2, hva, hvb, hvc]
  have hctx : θ3 = σ := by
    have hword : θ3.word = σ.word := by
      apply List.ext_getElem
      · rw [hword3]
        simp [σ] <;> omega
      · intro i hi hi'
        let v : Fin (2 * p + 3) := ⟨i, by rw [hword3] at hi; exact hi⟩
        have hletter : θ3.letterAt i = σ.letterAt i := by
          rw [hlet3 v, hσlet v]
          simp only [Fin.ext_iff]
          rfl
        simpa only [Ctx.Context.letterAt, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hi', Option.getD_some] using hletter
    change (⟨p + 1, 5, p + 1, θ3.word, [1, 1, 1]⟩ : Ctx.Context) = σ
    rw [hword]
  refine ⟨?_, f, ?_, ψ, hRestrictFinal, hDecFinal, hDecFinal.isSweepRealizable,
    hCupFinal, hCapFinal, hNoFinal, ?_, a, b, c, rfl, rfl, rfl,
    hDeep1, hDeep2, hd3⟩
  · simpa only [hctx] using hwf3
  · intro i
    rfl
  · simpa only [hctx] using hs3


end ErdosSzekeres
