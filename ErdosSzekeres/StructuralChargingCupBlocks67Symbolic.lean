module

public import ErdosSzekeres.StructuralChargingCupBlocks67

@[expose] public section

/-!
# Symbolic proof of the ordered `6+7` cup-block gate

This file proves the normalized thirteen-vertex gate by a short explicit
case analysis, then transports it to the arbitrary finite-set contract.
-/

namespace ErdosSzekeres

def emb0123456Eight : Fin 7 ↪o Fin 8 :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ ⟨i.val, lt_trans i.isLt (by decide)⟩) (by
      intro i j hij
      exact hij)

def emb1234567Eight : Fin 7 ↪o Fin 8 :=
  OrderEmbedding.ofStrictMono (fun i ↦ ⟨i.val + 1, by omega⟩) (by
    intro i j hij
    change i.val + 1 < j.val + 1
    omega)

set_option maxHeartbeats 1000000 in
/-- Six equal consecutive turns determine all fifty-six turns on an
eight-chain satisfying the one-change law. -/
theorem isMonochromaticChain_finEight_of_consecutive
    {n : ℕ} {χ : TripleColoring n} {c : Turn} (f : Fin 8 ↪o Fin n)
    (hone : OneChangeOn χ (Finset.univ.image f))
    (h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = c)
    (h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = c)
    (h234 : χ ⟨f 2, f 3, f 4, by simp, by simp⟩ = c)
    (h345 : χ ⟨f 3, f 4, f 5, by simp, by simp⟩ = c)
    (h456 : χ ⟨f 4, f 5, f 6, by simp, by simp⟩ = c)
    (h567 : χ ⟨f 5, f 6, f 7, by simp, by simp⟩ = c) :
    IsMonochromaticChain χ c f := by
  let first : Fin 7 ↪o Fin n := emb0123456Eight.trans f
  let last : Fin 7 ↪o Fin n := emb1234567Eight.trans f
  have hfirst := isMonochromaticChain_finSeven_of_consecutive first
    (hone.mono (by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨i, rfl⟩ := hx
      exact ⟨emb0123456Eight i, rfl⟩))
    (by simpa [first, emb0123456Eight] using h012)
    (by simpa [first, emb0123456Eight] using h123)
    (by simpa [first, emb0123456Eight] using h234)
    (by simpa [first, emb0123456Eight] using h345)
    (by simpa [first, emb0123456Eight] using h456)
  have hlast := isMonochromaticChain_finSeven_of_consecutive last
    (hone.mono (by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨i, rfl⟩ := hx
      exact ⟨emb1234567Eight i, rfl⟩))
    (by simpa [last, emb1234567Eight] using h123)
    (by simpa [last, emb1234567Eight] using h234)
    (by simpa [last, emb1234567Eight] using h345)
    (by simpa [last, emb1234567Eight] using h456)
    (by simpa [last, emb1234567Eight] using h567)
  have hcrossAux (j : Fin 8) (hj0 : 0 < j) (hj6 : j < 6) :
      χ ⟨f 0, f j, f 7, f.strictMono hj0,
        f.strictMono (hj6.trans (by decide))⟩ = c := by
    have hallow := hone (i := f 0) (j := f j) (k := f 6) (l := f 7)
      (f.strictMono hj0) (f.strictMono hj6) (f.strictMono (by decide))
      (by simp) (by simp) (by simp) (by simp)
    have hleft : χ ⟨f 0, f j, f 6, f.strictMono hj0,
        f.strictMono hj6⟩ = c := by
      fin_cases j
      · norm_num at hj0
      · simpa [first, emb0123456Eight] using
          hfirst.2 (i := (0 : Fin 7)) (j := 1) (l := 6)
            (by decide) (by decide)
      · simpa [first, emb0123456Eight] using
          hfirst.2 (i := (0 : Fin 7)) (j := 2) (l := 6)
            (by decide) (by decide)
      · simpa [first, emb0123456Eight] using
          hfirst.2 (i := (0 : Fin 7)) (j := 3) (l := 6)
            (by decide) (by decide)
      · simpa [first, emb0123456Eight] using
          hfirst.2 (i := (0 : Fin 7)) (j := 4) (l := 6)
            (by decide) (by decide)
      · simpa [first, emb0123456Eight] using
          hfirst.2 (i := (0 : Fin 7)) (j := 5) (l := 6)
            (by decide) (by decide)
      · simp at hj6
      · simp at hj6
    have hright : χ ⟨f j, f 6, f 7, f.strictMono hj6,
        f.strictMono (by decide)⟩ = c := by
      fin_cases j
      · norm_num at hj0
      · simpa [last, emb1234567Eight] using
          hlast.2 (i := (0 : Fin 7)) (j := 5) (l := 6)
            (by decide) (by decide)
      · simpa [last, emb1234567Eight] using
          hlast.2 (i := (1 : Fin 7)) (j := 5) (l := 6)
            (by decide) (by decide)
      · simpa [last, emb1234567Eight] using
          hlast.2 (i := (2 : Fin 7)) (j := 5) (l := 6)
            (by decide) (by decide)
      · simpa [last, emb1234567Eight] using
          hlast.2 (i := (3 : Fin 7)) (j := 5) (l := 6)
            (by decide) (by decide)
      · simpa [last, emb1234567Eight] using
          hlast.2 (i := (4 : Fin 7)) (j := 5) (l := 6)
            (by decide) (by decide)
      · simp at hj6
      · simp at hj6
    exact (hallow.all_eq_of_outer_eq (hleft.trans hright.symm)).1.symm.trans hleft
  have h067 : χ ⟨f 0, f 6, f 7, f.strictMono (by decide),
      f.strictMono (by decide)⟩ = c := by
    have hallow := hone (i := f 0) (j := f 1) (k := f 6) (l := f 7)
      (f.strictMono (by decide)) (f.strictMono (by decide))
      (f.strictMono (by decide)) (by simp) (by simp) (by simp) (by simp)
    have h016 : χ ⟨f 0, f 1, f 6, by simp, by simp⟩ = c := by
      simpa [first, emb0123456Eight] using
        hfirst.2 (i := (0 : Fin 7)) (j := 1) (l := 6) (by decide) (by decide)
    have h167 : χ ⟨f 1, f 6, f 7, by simp, by simp⟩ = c := by
      simpa [last, emb1234567Eight] using
        hlast.2 (i := (0 : Fin 7)) (j := 5) (l := 6) (by decide) (by decide)
    exact (hallow.all_eq_of_outer_eq (h016.trans h167.symm)).2.2.trans h167
  refine ⟨f.strictMono, ?_⟩
  intro i j k hij hjk
  by_cases hk : k < 7
  · let i' : Fin 7 := ⟨i.val, by omega⟩
    let j' : Fin 7 := ⟨j.val, by omega⟩
    let k' : Fin 7 := ⟨k.val, by omega⟩
    have hi : emb0123456Eight i' = i := by
      apply Fin.ext
      rfl
    have hj : emb0123456Eight j' = j := by
      apply Fin.ext
      rfl
    have hk' : emb0123456Eight k' = k := by
      apply Fin.ext
      rfl
    simpa [first, hi, hj, hk'] using
      hfirst.2 (i := i') (j := j') (l := k') (by omega) (by omega)
  · have hk7 : k = 7 := by omega
    subst k
    by_cases hi0 : 0 < i
    · let i' : Fin 7 := ⟨i.val - 1, by omega⟩
      let j' : Fin 7 := ⟨j.val - 1, by omega⟩
      let k' : Fin 7 := 6
      have hi : emb1234567Eight i' = i := by
        apply Fin.ext
        simp [emb1234567Eight, i']
        omega
      have hj : emb1234567Eight j' = j := by
        apply Fin.ext
        simp [emb1234567Eight, j']
        omega
      have hk' : emb1234567Eight k' = (7 : Fin 8) := by decide
      have hij' : i' < j' := by
        change i.val - 1 < j.val - 1
        omega
      have hjk' : j' < k' := by
        change j.val - 1 < 6
        omega
      simpa [last, hi, hj, hk'] using
        hlast.2 (i := i') (j := j') (l := k') hij' hjk'
    · have hi : i = 0 := by omega
      subst i
      by_cases hj6 : j < 6
      · exact hcrossAux j (by omega) hj6
      · have hj : j = 6 := by omega
        subst j
        exact h067

def finEightFirstToThirteen (i : Fin 8) : Fin 13 :=
  ⟨i.val, lt_trans i.isLt (by decide)⟩

def emb01234567Thirteen : Fin 8 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono finEightFirstToThirteen (by
    intro i j hij
    exact hij)

def finEightLastToThirteen (i : Fin 8) : Fin 13 :=
  ⟨i.val + 5, by omega⟩

def emb56789101112Thirteen : Fin 8 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono finEightLastToThirteen (by
    intro i j hij
    change i.val + 5 < j.val + 5
    omega)

set_option maxHeartbeats 1000000 in
/-- Two seven-cups sharing their first six vertices, with a right fan through
the two remaining vertices, form a strong eight-set. -/
theorem strong01234567_of_overlapping_cups
    (χ : TripleColoring 13)
    (hfirst : IsCupSet χ {0, 1, 2, 3, 4, 5, 6})
    (hsecond : IsCupSet χ {0, 1, 2, 3, 4, 5, 7})
    (hfan : ∀ i : Fin 8, ∀ hi : i < 6,
      χ ⟨finEightFirstToThirteen i, 6, 7, by
        change i.val < 6
        exact hi, by decide⟩ = Turn.right) :
    IsStrongPolygonOn χ emb01234567Thirteen := by
  have hmemFirst (r : Fin 8) (hr : r < 7) :
      finEightFirstToThirteen r ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 13)) := by
    fin_cases r <;> simp_all [finEightFirstToThirteen]
  have hmemSecond (r : Fin 8) (hr : r < 6 ∨ r = 7) :
      finEightFirstToThirteen r ∈ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 13)) := by
    fin_cases r <;> simp_all [finEightFirstToThirteen]
  have hleftTriple (i j k : Fin 8) (hij : i < j) (hjk : j < k)
      (hnotFan : ¬(j = 6 ∧ k = 7)) :
      χ ⟨emb01234567Thirteen i, emb01234567Thirteen j,
        emb01234567Thirteen k, emb01234567Thirteen.strictMono hij,
        emb01234567Thirteen.strictMono hjk⟩ = Turn.left := by
    by_cases hk : k = 7
    · subst k
      have hj6 : j < 6 := by omega
      exact hsecond _ (hmemSecond i (Or.inl (by omega)))
        (hmemSecond j (Or.inl hj6)) (hmemSecond 7 (Or.inr rfl))
    · have hk7 : k < 7 := by omega
      exact hfirst _ (hmemFirst i (by omega)) (hmemFirst j (by omega))
        (hmemFirst k hk7)
  intro i j k l hij hjk hkl
  constructor
  · exact (hleftTriple i j k hij hjk (by omega)).trans
      (hleftTriple i j l hij (hjk.trans hkl) (by omega)).symm
  · by_cases hlast : k = 6 ∧ l = 7
    · rcases hlast with ⟨rfl, rfl⟩
      have hi := hfan i (by omega)
      have hj := hfan j (by omega)
      simpa [emb01234567Thirteen, finEightFirstToThirteen] using
        hi.trans hj.symm
    · exact (hleftTriple i k l (hij.trans hjk) hkl hlast).trans
        (hleftTriple j k l hjk hkl hlast).symm

set_option maxHeartbeats 1000000 in
/-- Two seven-cups omitting alternate first vertices, with a right fan over
the first pair, form the terminal strong eight-set. -/
theorem strong56789101112_of_split_cups
    (χ : TripleColoring 13)
    (hright : IsCupSet χ {6, 7, 8, 9, 10, 11, 12})
    (hskip : IsCupSet χ {5, 7, 8, 9, 10, 11, 12})
    (hfan : ∀ k : Fin 8, ∀ hk : 1 < k,
      χ ⟨5, 6, finEightLastToThirteen k, by decide, by
        change 6 < k.val + 5
        omega⟩ = Turn.right) :
    IsStrongPolygonOn χ emb56789101112Thirteen := by
  have hmemRight (r : Fin 8) (hr : 0 < r) :
      finEightLastToThirteen r ∈ ({6, 7, 8, 9, 10, 11, 12} : Finset (Fin 13)) := by
    fin_cases r <;> simp_all [finEightLastToThirteen]
  have hmemSkip (r : Fin 8) (hr : r = 0 ∨ 1 < r) :
      finEightLastToThirteen r ∈ ({5, 7, 8, 9, 10, 11, 12} : Finset (Fin 13)) := by
    fin_cases r <;> simp_all [finEightLastToThirteen]
  have hleftTriple (i j k : Fin 8) (hij : i < j) (hjk : j < k)
      (hnotFan : ¬(i = 0 ∧ j = 1)) :
      χ ⟨emb56789101112Thirteen i, emb56789101112Thirteen j,
        emb56789101112Thirteen k, emb56789101112Thirteen.strictMono hij,
        emb56789101112Thirteen.strictMono hjk⟩ = Turn.left := by
    by_cases hi : i = 0
    · subst i
      have hj1 : 1 < j := by omega
      exact hskip _ (hmemSkip 0 (Or.inl rfl))
        (hmemSkip j (Or.inr hj1)) (hmemSkip k (Or.inr (by omega)))
    · have hi0 : 0 < i := by omega
      exact hright _ (hmemRight i hi0) (hmemRight j (by omega))
        (hmemRight k (by omega))
  intro i j k l hij hjk hkl
  constructor
  · by_cases hfirst : i = 0 ∧ j = 1
    · rcases hfirst with ⟨rfl, rfl⟩
      have hk := hfan k (by omega)
      have hl := hfan l (by omega)
      simpa [emb56789101112Thirteen, finEightLastToThirteen] using
        hk.trans hl.symm
    · exact (hleftTriple i j k hij hjk hfirst).trans
        (hleftTriple i j l hij (hjk.trans hkl) hfirst).symm
  · exact (hleftTriple i k l (hij.trans hjk) hkl (by omega)).trans
      (hleftTriple j k l hjk hkl (by omega)).symm

/-- An explicit eight-cup supplies the corresponding ambient witness. -/
theorem containsCupSet_univ_of_finEight
    {n : ℕ} {χ : TripleColoring n} {f : Fin 8 ↪o Fin n}
    (h : IsCup χ f) : ContainsCupSet χ Finset.univ 8 := by
  refine ⟨Finset.univ.image f, by simp, ?_, FinsetPolygon.IsCup.image h⟩
  simpa using Finset.card_image_of_injective Finset.univ f.injective

/-- An explicit strong eight-set supplies the corresponding ambient witness. -/
theorem containsStrongPolygonSet_univ_of_finEight
    {n : ℕ} {χ : TripleColoring n} {f : Fin 8 ↪o Fin n}
    (h : IsStrongPolygonOn χ f) :
    ContainsStrongPolygonSet χ Finset.univ 8 := by
  refine ⟨Finset.univ.image f, by simp, ?_,
    FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image h⟩
  simpa using Finset.card_image_of_injective Finset.univ f.injective

/-- Package the consecutive-turn extension theorem as an eight-cup witness. -/
theorem containsCupSet_univ_eight_of_consecutive
    {n : ℕ} {χ : TripleColoring n} (f : Fin 8 ↪o Fin n)
    (hone : OneChangeOn χ (Finset.univ.image f))
    (h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = Turn.left)
    (h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = Turn.left)
    (h234 : χ ⟨f 2, f 3, f 4, by simp, by simp⟩ = Turn.left)
    (h345 : χ ⟨f 3, f 4, f 5, by simp, by simp⟩ = Turn.left)
    (h456 : χ ⟨f 4, f 5, f 6, by simp, by simp⟩ = Turn.left)
    (h567 : χ ⟨f 5, f 6, f 7, by simp, by simp⟩ = Turn.left) :
    ContainsCupSet χ Finset.univ 8 := by
  apply containsCupSet_univ_of_finEight
  exact isMonochromaticChain_finEight_of_consecutive f hone
    h012 h123 h234 h345 h456 h567

def finSixToThirteen (i : Fin 6) : Fin 13 :=
  ⟨i.val, lt_trans i.isLt (by decide)⟩

def leftRightSevenTriple (i : Fin 6) : OrderedTriple 13 :=
  ⟨finSixToThirteen i, 6, 7, by
    change i.val < 6
    exact i.isLt, by decide⟩

def embLeftRightSeven (i : Fin 6) : Fin 8 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono
    ![finSixToThirteen i, 6, 7, 8, 9, 10, 11, 12] (by
      have hi6 : finSixToThirteen i < (6 : Fin 13) := by
        change i.val < 6
        exact i.isLt
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
      all_goals exact lt_trans hi6 (by decide))

def emb4567Thirteen : Fin 4 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono ![4, 5, 6, 7] (by decide)

def emb4578Thirteen : Fin 4 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono ![4, 5, 7, 8] (by decide)

def emb0123456Thirteen : Fin 7 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 5, 6] (by decide)

def emb0123457Thirteen : Fin 7 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 5, 7] (by decide)

def emb5789101112Thirteen : Fin 7 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono ![5, 7, 8, 9, 10, 11, 12] (by decide)

def emb45689101112Thirteen : Fin 8 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono ![4, 5, 6, 8, 9, 10, 11, 12] (by decide)

def emb34569101112Thirteen : Fin 8 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10, 11, 12] (by decide)

def emb23456101112Thirteen : Fin 8 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono ![2, 3, 4, 5, 6, 10, 11, 12] (by decide)

def emb1234561112Thirteen : Fin 8 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono ![1, 2, 3, 4, 5, 6, 11, 12] (by decide)

def emb012345612Thirteen : Fin 8 ↪o Fin 13 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 5, 6, 12] (by decide)

/-- Normalized thirteen-vertex form of the ordered `6+7` cup-block gate. -/
def CupBlocks67FinThirteen : Prop :=
  ∀ χ : TripleColoring 13,
    IsCupSet χ {0, 1, 2, 3, 4, 5} →
      IsCupSet χ {6, 7, 8, 9, 10, 11, 12} →
        OneChangeOn χ Finset.univ →
          ContainsCapSet χ Finset.univ 4 ∨
            ContainsCupSet χ Finset.univ 8 ∨
              ContainsStrongPolygonSet χ Finset.univ 8

set_option maxHeartbeats 2000000 in
/-- The normalized ordered `6+7` cup-block gate, proved by the explicit
fan/cap/extension case analysis. -/
theorem cupBlocks67FinThirteen : CupBlocks67FinThirteen := by
  intro χ hleft hright hone
  by_contra hout
  have hnoCap : ¬ContainsCapSet χ Finset.univ 4 :=
    fun hcap ↦ hout (Or.inl hcap)
  have hnoCup : ¬ContainsCupSet χ Finset.univ 8 :=
    fun hcup ↦ hout (Or.inr (Or.inl hcup))
  have hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 8 :=
    fun hstrong ↦ hout (Or.inr (Or.inr hstrong))
  have h678 : χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
    simpa using hright ⟨6, 7, 8, by decide, by decide⟩
      (by simp) (by simp) (by simp)
  have h789 : χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
    simpa using hright ⟨7, 8, 9, by decide, by decide⟩
      (by simp) (by simp) (by simp)
  have h8910 : χ ⟨8, 9, 10, by decide, by decide⟩ = Turn.left := by
    simpa using hright ⟨8, 9, 10, by decide, by decide⟩
      (by simp) (by simp) (by simp)
  have h91011 : χ ⟨9, 10, 11, by decide, by decide⟩ = Turn.left := by
    simpa using hright ⟨9, 10, 11, by decide, by decide⟩
      (by simp) (by simp) (by simp)
  have h101112 : χ ⟨10, 11, 12, by decide, by decide⟩ = Turn.left := by
    simpa using hright ⟨10, 11, 12, by decide, by decide⟩
      (by simp) (by simp) (by simp)
  have hfan (i : Fin 6) : χ (leftRightSevenTriple i) = Turn.right := by
    by_cases hcross : χ (leftRightSevenTriple i) = Turn.left
    · exfalso
      apply hnoCup
      apply containsCupSet_univ_eight_of_consecutive (embLeftRightSeven i)
        (hone.mono (by simp))
      · simpa [embLeftRightSeven, leftRightSevenTriple] using hcross
      · simpa [embLeftRightSeven] using h678
      · simpa [embLeftRightSeven] using h789
      · simpa [embLeftRightSeven] using h8910
      · simpa [embLeftRightSeven] using h91011
      · simpa [embLeftRightSeven] using h101112
    · cases hturn : χ (leftRightSevenTriple i) <;> simp_all
  have h567r : χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right := by
    simpa [leftRightSevenTriple, finSixToThirteen] using hfan 5
  have h012 : χ ⟨0, 1, 2, by decide, by decide⟩ = Turn.left := by
    simpa using hleft ⟨0, 1, 2, by decide, by decide⟩
      (by simp) (by simp) (by simp)
  have h123 : χ ⟨1, 2, 3, by decide, by decide⟩ = Turn.left := by
    simpa using hleft ⟨1, 2, 3, by decide, by decide⟩
      (by simp) (by simp) (by simp)
  have h234 : χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left := by
    simpa using hleft ⟨2, 3, 4, by decide, by decide⟩
      (by simp) (by simp) (by simp)
  have h345 : χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left := by
    simpa using hleft ⟨3, 4, 5, by decide, by decide⟩
      (by simp) (by simp) (by simp)
  have h456 : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left := by
    by_cases h : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left
    · exact h
    · have hr : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right := by
        cases hturn : χ ⟨4, 5, 6, by decide, by decide⟩ <;> simp_all
      exfalso
      apply hnoCap
      apply containsCapSet_univ_of_finFour
      apply isMonochromaticChain_finFour_of_outer_eq emb4567Thirteen
        (hone.mono (by simp))
      · simpa [emb4567Thirteen] using hr
      · simpa [emb4567Thirteen] using h567r
  have hcupFirst : IsCupSet χ {0, 1, 2, 3, 4, 5, 6} := by
    have hchain : IsCup χ emb0123456Thirteen := by
      apply isMonochromaticChain_finSeven_of_consecutive emb0123456Thirteen
        (hone.mono (by simp))
      · simpa [emb0123456Thirteen] using h012
      · simpa [emb0123456Thirteen] using h123
      · simpa [emb0123456Thirteen] using h234
      · simpa [emb0123456Thirteen] using h345
      · simpa [emb0123456Thirteen] using h456
    simpa [emb0123456Thirteen] using FinsetPolygon.IsCup.image hchain
  by_cases h457 : χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.left
  · have hcupSecond : IsCupSet χ {0, 1, 2, 3, 4, 5, 7} := by
      have hchain : IsCup χ emb0123457Thirteen := by
        apply isMonochromaticChain_finSeven_of_consecutive emb0123457Thirteen
          (hone.mono (by simp))
        · simpa [emb0123457Thirteen] using h012
        · simpa [emb0123457Thirteen] using h123
        · simpa [emb0123457Thirteen] using h234
        · simpa [emb0123457Thirteen] using h345
        · simpa [emb0123457Thirteen] using h457
      simpa [emb0123457Thirteen] using FinsetPolygon.IsCup.image hchain
    apply hnoStrong
    apply containsStrongPolygonSet_univ_of_finEight
    apply strong01234567_of_overlapping_cups χ hcupFirst hcupSecond
    intro i hi
    let r : Fin 6 := ⟨i.val, by omega⟩
    simpa [r, leftRightSevenTriple, finSixToThirteen,
      finEightFirstToThirteen] using hfan r
  · have h457r : χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right := by
      cases hturn : χ ⟨4, 5, 7, by decide, by decide⟩ <;> simp_all
    have h578 : χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left := by
      by_cases h : χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left
      · exact h
      · have hr : χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right := by
          cases hturn : χ ⟨5, 7, 8, by decide, by decide⟩ <;> simp_all
        exfalso
        apply hnoCap
        apply containsCapSet_univ_of_finFour
        apply isMonochromaticChain_finFour_of_outer_eq emb4578Thirteen
          (hone.mono (by simp))
        · simpa [emb4578Thirteen] using h457r
        · simpa [emb4578Thirteen] using hr
    have hcupSkip : IsCupSet χ {5, 7, 8, 9, 10, 11, 12} := by
      have hchain : IsCup χ emb5789101112Thirteen := by
        apply isMonochromaticChain_finSeven_of_consecutive
          emb5789101112Thirteen (hone.mono (by simp))
        · simpa [emb5789101112Thirteen] using h578
        · simpa [emb5789101112Thirteen] using h789
        · simpa [emb5789101112Thirteen] using h8910
        · simpa [emb5789101112Thirteen] using h91011
        · simpa [emb5789101112Thirteen] using h101112
      simpa [emb5789101112Thirteen] using FinsetPolygon.IsCup.image hchain
    by_cases h568 : χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left
    · apply hnoCup
      apply containsCupSet_univ_eight_of_consecutive emb45689101112Thirteen
        (hone.mono (by simp))
      · simpa [emb45689101112Thirteen] using h456
      · simpa [emb45689101112Thirteen] using h568
      · simpa [emb45689101112Thirteen] using hright
          ⟨6, 8, 9, by decide, by decide⟩ (by simp) (by simp) (by simp)
      · simpa [emb45689101112Thirteen] using h8910
      · simpa [emb45689101112Thirteen] using h91011
      · simpa [emb45689101112Thirteen] using h101112
    · have h568r : χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
        cases hturn : χ ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
      by_cases h569 : χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left
      · apply hnoCup
        apply containsCupSet_univ_eight_of_consecutive emb34569101112Thirteen
          (hone.mono (by simp))
        · simpa [emb34569101112Thirteen] using h345
        · simpa [emb34569101112Thirteen] using h456
        · simpa [emb34569101112Thirteen] using h569
        · simpa [emb34569101112Thirteen] using hright
            ⟨6, 9, 10, by decide, by decide⟩ (by simp) (by simp) (by simp)
        · simpa [emb34569101112Thirteen] using h91011
        · simpa [emb34569101112Thirteen] using h101112
      · have h569r : χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
          cases hturn : χ ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
        by_cases h5610 : χ ⟨5, 6, 10, by decide, by decide⟩ = Turn.left
        · apply hnoCup
          apply containsCupSet_univ_eight_of_consecutive
            emb23456101112Thirteen (hone.mono (by simp))
          · simpa [emb23456101112Thirteen] using h234
          · simpa [emb23456101112Thirteen] using h345
          · simpa [emb23456101112Thirteen] using h456
          · simpa [emb23456101112Thirteen] using h5610
          · simpa [emb23456101112Thirteen] using hright
              ⟨6, 10, 11, by decide, by decide⟩ (by simp) (by simp) (by simp)
          · simpa [emb23456101112Thirteen] using h101112
        · have h5610r : χ ⟨5, 6, 10, by decide, by decide⟩ = Turn.right := by
            cases hturn : χ ⟨5, 6, 10, by decide, by decide⟩ <;> simp_all
          by_cases h5611 : χ ⟨5, 6, 11, by decide, by decide⟩ = Turn.left
          · apply hnoCup
            apply containsCupSet_univ_eight_of_consecutive
              emb1234561112Thirteen (hone.mono (by simp))
            · simpa [emb1234561112Thirteen] using h123
            · simpa [emb1234561112Thirteen] using h234
            · simpa [emb1234561112Thirteen] using h345
            · simpa [emb1234561112Thirteen] using h456
            · simpa [emb1234561112Thirteen] using h5611
            · simpa [emb1234561112Thirteen] using hright
                ⟨6, 11, 12, by decide, by decide⟩ (by simp) (by simp) (by simp)
          · have h5611r : χ ⟨5, 6, 11, by decide, by decide⟩ = Turn.right := by
              cases hturn : χ ⟨5, 6, 11, by decide, by decide⟩ <;> simp_all
            by_cases h5612 : χ ⟨5, 6, 12, by decide, by decide⟩ = Turn.left
            · apply hnoCup
              apply containsCupSet_univ_eight_of_consecutive
                emb012345612Thirteen (hone.mono (by simp))
              · simpa [emb012345612Thirteen] using h012
              · simpa [emb012345612Thirteen] using h123
              · simpa [emb012345612Thirteen] using h234
              · simpa [emb012345612Thirteen] using h345
              · simpa [emb012345612Thirteen] using h456
              · simpa [emb012345612Thirteen] using h5612
            · have h5612r : χ ⟨5, 6, 12, by decide, by decide⟩ = Turn.right := by
                cases hturn : χ ⟨5, 6, 12, by decide, by decide⟩ <;> simp_all
              apply hnoStrong
              apply containsStrongPolygonSet_univ_of_finEight
              apply strong56789101112_of_split_cups χ hright hcupSkip
              intro k hk
              fin_cases k
              · simp at hk
              · simp at hk
              · simpa [finEightLastToThirteen] using h567r
              · simpa [finEightLastToThirteen] using h568r
              · simpa [finEightLastToThirteen] using h569r
              · simpa [finEightLastToThirteen] using h5610r
              · simpa [finEightLastToThirteen] using h5611r
              · simpa [finEightLastToThirteen] using h5612r

/-- Reversal derives the normalized `7+6` orientation from `6+7`. -/
theorem cupBlocks76_finThirteen_of_cupBlocks67
    (hnormalized : CupBlocks67FinThirteen)
    (χ : TripleColoring 13)
    (hleft : IsCupSet χ {0, 1, 2, 3, 4, 5, 6})
    (hright : IsCupSet χ {7, 8, 9, 10, 11, 12})
    (hone : OneChangeOn χ Finset.univ) :
    ContainsCapSet χ Finset.univ 4 ∨
      ContainsCupSet χ Finset.univ 8 ∨
        ContainsStrongPolygonSet χ Finset.univ 8 := by
  let ψ := reverseColor χ
  have hrevFirst : ∀ i : Fin 13,
      i ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 13)) →
        i.rev ∈ ({7, 8, 9, 10, 11, 12} : Finset (Fin 13)) := by
    intro i hi
    fin_cases i <;> simp_all
  have hrevLast : ∀ i : Fin 13,
      i ∈ ({6, 7, 8, 9, 10, 11, 12} : Finset (Fin 13)) →
        i.rev ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 13)) := by
    intro i hi
    fin_cases i <;> simp_all
  have hψLeft : IsCupSet ψ {0, 1, 2, 3, 4, 5} := by
    intro t hi hj hk
    exact hright (reverseOrderedTriple t)
      (hrevFirst t.k hk) (hrevFirst t.j hj) (hrevFirst t.i hi)
  have hψRight : IsCupSet ψ {6, 7, 8, 9, 10, 11, 12} := by
    intro t hi hj hk
    exact hleft (reverseOrderedTriple t)
      (hrevLast t.k hk) (hrevLast t.j hj) (hrevLast t.i hi)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    have horig := hone (i := l.rev) (j := k.rev) (k := j.rev) (l := i.rev)
      (by simpa using hkl) (by simpa using hjk) (by simpa using hij)
      (by simp) (by simp) (by simp) (by simp)
    simpa [ψ, reverseColor, reverseOrderedTriple] using horig.reversed
  rcases hnormalized ψ hψLeft hψRight hψOne with hcap | hcup | hstrong
  · exact Or.inl (containsCapSet_of_reverseColor hcap)
  · exact Or.inr (Or.inl (containsCupSet_of_reverseColor hcup))
  · exact Or.inr (Or.inr (containsStrongPolygonSet_of_reverseColor hstrong))

set_option maxHeartbeats 1000000 in
/-- Transport the normalized theorem to arbitrary ordered `6+7` blocks. -/
theorem cupBlocks67Force488_six_seven_of_finThirteen
    (hnormalized : CupBlocks67FinThirteen)
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleftCard : left.card = 6) (hrightCard : right.card = 7)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right)) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsCupSet χ (left ∪ right) 8 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 8 := by
  let le : Fin 6 ↪o Fin n := left.orderEmbOfFin hleftCard
  let re : Fin 7 ↪o Fin n := right.orderEmbOfFin hrightCard
  let f : Fin 13 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![le 0, le 1, le 2, le 3, le 4, le 5,
      re 0, re 1, re 2, re 3, re 4, re 5, re 6] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact re.strictMono (by decide)
        | exact horder _ (left.orderEmbOfFin_mem hleftCard _)
            _ (right.orderEmbOfFin_mem hrightCard _))
  let ψ : TripleColoring 13 := χ.restrict f
  have hfmem : ∀ i : Fin 13, f i ∈ left ∪ right := by
    intro i
    fin_cases i <;>
      simp [f, le, re, left.orderEmbOfFin_mem hleftCard,
        right.orderEmbOfFin_mem hrightCard]
  have hfirst : ∀ i : Fin 13,
      i ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 13)) → f i ∈ left := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact left.orderEmbOfFin_mem hleftCard _
  have hlast : ∀ i : Fin 13,
      i ∈ ({6, 7, 8, 9, 10, 11, 12} : Finset (Fin 13)) → f i ∈ right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact right.orderEmbOfFin_mem hrightCard _
  have hψLeft : IsCupSet ψ {0, 1, 2, 3, 4, 5} := by
    intro t hi hj hk
    exact hleft (t.map f) (hfirst t.i hi) (hfirst t.j hj) (hfirst t.k hk)
  have hψRight : IsCupSet ψ {6, 7, 8, 9, 10, 11, 12} := by
    intro t hi hj hk
    exact hright (t.map f) (hlast t.i hi) (hlast t.j hj) (hlast t.k hk)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
      (hfmem i) (hfmem j) (hfmem k) (hfmem l)
  have hout := hnormalized ψ hψLeft hψRight hψOne
  have himage : Finset.univ.image f = left ∪ right := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfmem i
    · have himageCard : (Finset.univ.image f).card = 13 := by
        simpa using Finset.card_image_of_injective Finset.univ f.injective
      rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard,
        himageCard]
  rcases hout with hcap | hcup | hstrong
  · exact Or.inl (by simpa [himage] using containsCapSet_map_restrict f hcap)
  · exact Or.inr (Or.inl (by
      simpa [himage] using containsCupSet_map_restrict f hcup))
  · exact Or.inr (Or.inr (by
      simpa [himage] using containsStrongPolygonSet_map_restrict f hstrong))

set_option maxHeartbeats 1000000 in
/-- Transport the reversed normalized theorem to arbitrary ordered `7+6`
blocks. -/
theorem cupBlocks67Force488_seven_six_of_finThirteen
    (hnormalized : CupBlocks67FinThirteen)
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleftCard : left.card = 7) (hrightCard : right.card = 6)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right)) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsCupSet χ (left ∪ right) 8 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 8 := by
  let le : Fin 7 ↪o Fin n := left.orderEmbOfFin hleftCard
  let re : Fin 6 ↪o Fin n := right.orderEmbOfFin hrightCard
  let f : Fin 13 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![le 0, le 1, le 2, le 3, le 4, le 5, le 6,
      re 0, re 1, re 2, re 3, re 4, re 5] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact re.strictMono (by decide)
        | exact horder _ (left.orderEmbOfFin_mem hleftCard _)
            _ (right.orderEmbOfFin_mem hrightCard _))
  let ψ : TripleColoring 13 := χ.restrict f
  have hfmem : ∀ i : Fin 13, f i ∈ left ∪ right := by
    intro i
    fin_cases i <;>
      simp [f, le, re, left.orderEmbOfFin_mem hleftCard,
        right.orderEmbOfFin_mem hrightCard]
  have hfirst : ∀ i : Fin 13,
      i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 13)) → f i ∈ left := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact left.orderEmbOfFin_mem hleftCard _
  have hlast : ∀ i : Fin 13,
      i ∈ ({7, 8, 9, 10, 11, 12} : Finset (Fin 13)) → f i ∈ right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact right.orderEmbOfFin_mem hrightCard _
  have hψLeft : IsCupSet ψ {0, 1, 2, 3, 4, 5, 6} := by
    intro t hi hj hk
    exact hleft (t.map f) (hfirst t.i hi) (hfirst t.j hj) (hfirst t.k hk)
  have hψRight : IsCupSet ψ {7, 8, 9, 10, 11, 12} := by
    intro t hi hj hk
    exact hright (t.map f) (hlast t.i hi) (hlast t.j hj) (hlast t.k hk)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
      (hfmem i) (hfmem j) (hfmem k) (hfmem l)
  have hout := cupBlocks76_finThirteen_of_cupBlocks67
    hnormalized ψ hψLeft hψRight hψOne
  have himage : Finset.univ.image f = left ∪ right := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfmem i
    · have himageCard : (Finset.univ.image f).card = 13 := by
        simpa using Finset.card_image_of_injective Finset.univ f.injective
      rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard,
        himageCard]
  rcases hout with hcap | hcup | hstrong
  · exact Or.inl (by simpa [himage] using containsCapSet_map_restrict f hcap)
  · exact Or.inr (Or.inl (by
      simpa [himage] using containsCupSet_map_restrict f hcup))
  · exact Or.inr (Or.inr (by
      simpa [himage] using containsStrongPolygonSet_map_restrict f hstrong))

/-- The normalized symbolic proof closes the full ordered-block contract. -/
theorem cupBlocks67Force488 : CupBlocks67Force488 := by
  intro n χ left right hdisjoint horder hcards hleft hright hone
  rcases hcards with ⟨hleftCard, hrightCard⟩ | ⟨hleftCard, hrightCard⟩
  · exact cupBlocks67Force488_six_seven_of_finThirteen
      cupBlocks67FinThirteen hdisjoint horder hleftCard hrightCard
      hleft hright hone
  · exact cupBlocks67Force488_seven_six_of_finThirteen
      cupBlocks67FinThirteen hdisjoint horder hleftCard hrightCard
      hleft hright hone

/-- The proved cup-block gate removes every open `(4,8,8)` root with a
nonempty lower child and at least thirteen upper vertices. -/
theorem upper_card_le_twelve_at_open_488
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty)
    (hupper : IsDecomposableOn χ upper)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 8)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 8) :
    upper.card ≤ 12 := by
  exact upper_card_le_twelve_of_cupBlocks67 cupBlocks67Force488
    hlower hupper hdeep hnoCap hnoCup hnoStrong

/-- In particular, the formerly open `10+13` critical-root boundary is
impossible. -/
theorem no_open_488_ten_thirteen
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hlowerCard : lower.card = 10)
    (hupperCard : upper.card = 13)
    (hupper : IsDecomposableOn χ upper)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 8)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 8) : False := by
  have hlower : lower.Nonempty := Finset.card_pos.mp (by omega)
  have hbound := upper_card_le_twelve_at_open_488 hlower hupper hdeep
    hnoCap hnoCup hnoStrong
  omega

/-- After removing the `10+13` boundary, every open critical `(4,8,8)` root
of total size twenty-three lies in the residual child-cardinality window
`11 ≤ lower.card` and `upper.card ≤ 12`. -/
theorem open_488_critical_child_window
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty)
    (hupper : IsDecomposableOn χ upper)
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hcritical : (lower ∪ upper).card = 23)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 8)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 8) :
    11 ≤ lower.card ∧ upper.card ≤ 12 := by
  have hupperBound := upper_card_le_twelve_at_open_488 hlower hupper hdeep
    hnoCap hnoCup hnoStrong
  have hsum : lower.card + upper.card = 23 := by
    rw [← Finset.card_union_of_disjoint hdeep.disjoint, hcritical]
  omega

end ErdosSzekeres

end
