module

public import ErdosSzekeres.StructuralChargingCupBlocks45

@[expose] public section

/-!
# The proposed normalized `5+6` cup-block gate

This file freezes the exact next local contract at `(4,7,7,3,3)` and proves
its quantitative consequence.  It does not assume the contract is true: the
normalized symbolic proof and its transport remain the next proof target.
-/

namespace ErdosSzekeres

def emb012345Seven : Fin 6 ↪o Fin 7 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 5] (by decide)

def emb123456Seven : Fin 6 ↪o Fin 7 :=
  OrderEmbedding.ofStrictMono ![1, 2, 3, 4, 5, 6] (by decide)

set_option maxHeartbeats 800000 in
/-- Five equal consecutive turns determine all thirty-five turns on a
seven-chain. This is the reusable extension mechanism behind the immediate
seven-cup branches of the normalized `5+6` proof. -/
theorem isMonochromaticChain_finSeven_of_consecutive
    {n : ℕ} {χ : TripleColoring n} {c : Turn} (f : Fin 7 ↪o Fin n)
    (hone : OneChangeOn χ (Finset.univ.image f))
    (h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = c)
    (h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = c)
    (h234 : χ ⟨f 2, f 3, f 4, by simp, by simp⟩ = c)
    (h345 : χ ⟨f 3, f 4, f 5, by simp, by simp⟩ = c)
    (h456 : χ ⟨f 4, f 5, f 6, by simp, by simp⟩ = c) :
    IsMonochromaticChain χ c f := by
  let first : Fin 6 ↪o Fin n := emb012345Seven.trans f
  let last : Fin 6 ↪o Fin n := emb123456Seven.trans f
  have hfirst := isMonochromaticChain_finSix_of_consecutive first
    (hone.mono (by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨i, rfl⟩ := hx
      exact ⟨emb012345Seven i, rfl⟩))
    (by simpa [first, emb012345Seven] using h012)
    (by simpa [first, emb012345Seven] using h123)
    (by simpa [first, emb012345Seven] using h234)
    (by simpa [first, emb012345Seven] using h345)
  have hlast := isMonochromaticChain_finSix_of_consecutive last
    (hone.mono (by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨i, rfl⟩ := hx
      exact ⟨emb123456Seven i, rfl⟩))
    (by simpa [last, emb123456Seven] using h123)
    (by simpa [last, emb123456Seven] using h234)
    (by simpa [last, emb123456Seven] using h345)
    (by simpa [last, emb123456Seven] using h456)
  have h056 : χ ⟨f 0, f 5, f 6, by simp, by simp⟩ = c := by
    have hallow := hone (i := f 0) (j := f 1) (k := f 5) (l := f 6)
      (f.strictMono (by decide)) (f.strictMono (by decide))
      (f.strictMono (by decide)) (by simp) (by simp) (by simp) (by simp)
    have h015 : χ ⟨f 0, f 1, f 5, by simp, by simp⟩ = c := by
      simpa [first, emb012345Seven] using
        hfirst.2 (i := (0 : Fin 6)) (j := 1) (l := 5) (by decide) (by decide)
    have h156 : χ ⟨f 1, f 5, f 6, by simp, by simp⟩ = c := by
      simpa [last, emb123456Seven] using
        hlast.2 (i := (0 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
    have houter : χ ⟨f 0, f 1, f 5, by simp, by simp⟩ =
        χ ⟨f 1, f 5, f 6, by simp, by simp⟩ := h015.trans h156.symm
    exact (hallow.all_eq_of_outer_eq houter).2.2.trans h156
  have hcrossAux (j' : Fin 7) (hj0 : 0 < j') (hj5 : j' < 5)
      (hleft : χ ⟨f 0, f j', f 5, f.strictMono hj0,
        f.strictMono hj5⟩ = c)
      (hright : χ ⟨f j', f 5, f 6, f.strictMono hj5,
        f.strictMono (by decide)⟩ = c) :
      χ ⟨f 0, f j', f 6, f.strictMono hj0,
        f.strictMono (lt_trans hj5 (by decide))⟩ = c := by
    have hallow := hone (i := f 0) (j := f j') (k := f 5) (l := f 6)
      (f.strictMono hj0) (f.strictMono hj5) (f.strictMono (by decide))
      (by simp) (by simp) (by simp) (by simp)
    have houter : χ ⟨f 0, f j', f 5, f.strictMono hj0,
        f.strictMono hj5⟩ =
        χ ⟨f j', f 5, f 6, f.strictMono hj5,
          f.strictMono (by decide)⟩ := hleft.trans hright.symm
    exact (hallow.all_eq_of_outer_eq houter).1.symm.trans hleft
  have hcross (j : Fin 4) :
      χ ⟨f 0, f (⟨j.val + 1, by omega⟩ : Fin 7), f 6,
        f.strictMono (by
          change 0 < j.val + 1
          exact Nat.zero_lt_succ _),
        f.strictMono (by
          change j.val + 1 < 6
          omega)⟩ = c := by
    fin_cases j
    · exact hcrossAux 1 (by decide) (by decide)
        (by simpa [first, emb012345Seven] using
          hfirst.2 (i := (0 : Fin 6)) (j := 1) (l := 5) (by decide) (by decide))
        (by simpa [last, emb123456Seven] using
          hlast.2 (i := (0 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide))
    · exact hcrossAux 2 (by decide) (by decide)
        (by simpa [first, emb012345Seven] using
          hfirst.2 (i := (0 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide))
        (by simpa [last, emb123456Seven] using
          hlast.2 (i := (1 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide))
    · exact hcrossAux 3 (by decide) (by decide)
        (by simpa [first, emb012345Seven] using
          hfirst.2 (i := (0 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide))
        (by simpa [last, emb123456Seven] using
          hlast.2 (i := (2 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide))
    · exact hcrossAux 4 (by decide) (by decide)
        (by simpa [first, emb012345Seven] using
          hfirst.2 (i := (0 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide))
        (by simpa [last, emb123456Seven] using
          hlast.2 (i := (3 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide))
  refine ⟨f.strictMono, ?_⟩
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals (try norm_num at hij)
  all_goals (try norm_num at hjk)
  all_goals first
    | simpa using hcross 0
    | simpa using hcross 1
    | simpa using hcross 2
    | simpa using hcross 3
    | simpa using h056
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (0 : Fin 6)) (j := 1) (l := 2) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (0 : Fin 6)) (j := 1) (l := 3) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (0 : Fin 6)) (j := 1) (l := 4) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (0 : Fin 6)) (j := 1) (l := 5) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (0 : Fin 6)) (j := 2) (l := 3) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (0 : Fin 6)) (j := 2) (l := 4) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (0 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (0 : Fin 6)) (j := 3) (l := 4) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (0 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (0 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (1 : Fin 6)) (j := 2) (l := 3) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (1 : Fin 6)) (j := 2) (l := 4) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (1 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (1 : Fin 6)) (j := 3) (l := 4) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (1 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (1 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (2 : Fin 6)) (j := 3) (l := 4) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (2 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (2 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
    | simpa [first, emb012345Seven] using
        hfirst.2 (i := (3 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
    | simpa [last, emb123456Seven] using
        hlast.2 (i := (0 : Fin 6)) (j := 1) (l := 5) (by decide) (by decide)
    | simpa [last, emb123456Seven] using
        hlast.2 (i := (0 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide)
    | simpa [last, emb123456Seven] using
        hlast.2 (i := (0 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
    | simpa [last, emb123456Seven] using
        hlast.2 (i := (0 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
    | simpa [last, emb123456Seven] using
        hlast.2 (i := (1 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide)
    | simpa [last, emb123456Seven] using
        hlast.2 (i := (1 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
    | simpa [last, emb123456Seven] using
        hlast.2 (i := (1 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
    | simpa [last, emb123456Seven] using
        hlast.2 (i := (2 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
    | simpa [last, emb123456Seven] using
        hlast.2 (i := (2 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
    | simpa [last, emb123456Seven] using
        hlast.2 (i := (3 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)

def finFiveToEleven (i : Fin 5) : Fin 11 :=
  ⟨i.val, lt_trans i.isLt (by decide)⟩

def frontFanTriple (i : Fin 5) : OrderedTriple 11 :=
  ⟨finFiveToEleven i, 5, 6, by
    change i.val < 5
    exact i.isLt, by decide⟩

def embFrontTailSix (i : Fin 5) : Fin 7 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono
    ![finFiveToEleven i, 5, 6, 7, 8, 9, 10] (by
      have hi5 : finFiveToEleven i < (5 : Fin 11) := by
        change i.val < 5
        exact i.isLt
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
      all_goals exact lt_trans hi5 (by decide))

/-- A selected seven-cup gives the corresponding ambient finite-set witness. -/
theorem containsCupSet_univ_of_finSeven {n : ℕ} {χ : TripleColoring n}
    {f : Fin 7 ↪o Fin n} (h : IsCup χ f) :
    ContainsCupSet χ Finset.univ 7 := by
  refine ⟨Finset.univ.image f, by simp, ?_, FinsetPolygon.IsCup.image h⟩
  simpa using Finset.card_image_of_injective Finset.univ f.injective

theorem containsStrongPolygonSet_univ_of_finSeven
    {n : ℕ} {χ : TripleColoring n} {f : Fin 7 ↪o Fin n}
    (h : IsStrongPolygonOn χ f) :
    ContainsStrongPolygonSet χ Finset.univ 7 := by
  refine ⟨Finset.univ.image f, by simp, ?_,
    FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image h⟩
  simpa using Finset.card_image_of_injective Finset.univ f.injective

/-- The five immediate branches of the normalized `5+6` gate. A left turn
from any first-block vertex through the first two tail vertices extends the
six-vertex tail cup to a seven-cup. Otherwise the whole five-turn fan points
right. -/
theorem cupBlocks56_containsCupSeven_or_rightFan
    (χ : TripleColoring 11)
    (hright : IsCupSet χ {5, 6, 7, 8, 9, 10})
    (hone : OneChangeOn χ Finset.univ) :
    ContainsCupSet χ Finset.univ 7 ∨
      ∀ i : Fin 5,
        χ (frontFanTriple i) = Turn.right := by
  have hcupOfCross (i : Fin 5)
      (hcross : χ (frontFanTriple i) = Turn.left) :
      ContainsCupSet χ Finset.univ 7 := by
    apply containsCupSet_univ_of_finSeven
    apply isMonochromaticChain_finSeven_of_consecutive (embFrontTailSix i)
      (hone.mono (by simp))
      (by simpa [frontFanTriple, embFrontTailSix] using hcross)
    · simpa [embFrontTailSix] using hright
        ⟨5, 6, 7, by decide, by decide⟩ (by simp) (by simp) (by simp)
    · simpa [embFrontTailSix] using hright
        ⟨6, 7, 8, by decide, by decide⟩ (by simp) (by simp) (by simp)
    · simpa [embFrontTailSix] using hright
        ⟨7, 8, 9, by decide, by decide⟩ (by simp) (by simp) (by simp)
    · simpa [embFrontTailSix] using hright
        ⟨8, 9, 10, by decide, by decide⟩ (by simp) (by simp) (by simp)
  by_cases h0 : χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left
  · exact Or.inl (hcupOfCross 0 (by simpa [embFrontTailSix] using h0))
  have h0r : χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases h : χ ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  by_cases h1 : χ ⟨1, 5, 6, by decide, by decide⟩ = Turn.left
  · exact Or.inl (hcupOfCross 1 (by simpa [embFrontTailSix] using h1))
  have h1r : χ ⟨1, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases h : χ ⟨1, 5, 6, by decide, by decide⟩ <;> simp_all
  by_cases h2 : χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left
  · exact Or.inl (hcupOfCross 2 (by simpa [embFrontTailSix] using h2))
  have h2r : χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases h : χ ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  by_cases h3 : χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left
  · exact Or.inl (hcupOfCross 3 (by simpa [embFrontTailSix] using h3))
  have h3r : χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases h : χ ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  by_cases h4 : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left
  · exact Or.inl (hcupOfCross 4 (by simpa [embFrontTailSix] using h4))
  have h4r : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases h : χ ⟨4, 5, 6, by decide, by decide⟩ <;> simp_all
  right
  intro i
  fin_cases i
  · simpa [frontFanTriple, finFiveToEleven] using h0r
  · simpa [frontFanTriple, finFiveToEleven] using h1r
  · simpa [frontFanTriple, finFiveToEleven] using h2r
  · simpa [frontFanTriple, finFiveToEleven] using h3r
  · simpa [frontFanTriple, finFiveToEleven] using h4r

def emb01235910 : Fin 7 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5, 9, 10] (by decide)

/-- One residual branch closes conceptually: the two left bridge turns
`235` and `359` join the left and right cup blocks into the explicit
seven-cup `{0,1,2,3,5,9,10}`. -/
theorem cupBlocks56_containsCupSeven_of_bridge_turns
    (χ : TripleColoring 11)
    (hleft : IsCupSet χ {0, 1, 2, 3, 4})
    (hright : IsCupSet χ {5, 6, 7, 8, 9, 10})
    (hone : OneChangeOn χ Finset.univ)
    (h235 : χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left)
    (h359 : χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) :
    ContainsCupSet χ Finset.univ 7 := by
  apply containsCupSet_univ_of_finSeven
  apply isMonochromaticChain_finSeven_of_consecutive emb01235910
    (hone.mono (by simp))
  · simpa [emb01235910] using hleft
      ⟨0, 1, 2, by decide, by decide⟩ (by simp) (by simp) (by simp)
  · simpa [emb01235910] using hleft
      ⟨1, 2, 3, by decide, by decide⟩ (by simp) (by simp) (by simp)
  · simpa [emb01235910] using h235
  · simpa [emb01235910] using h359
  · simpa [emb01235910] using hright
      ⟨5, 9, 10, by decide, by decide⟩ (by simp) (by simp) (by simp)

def emb012345Eleven : Fin 6 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 5] (by decide)

def emb012346Eleven : Fin 6 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 6] (by decide)

def finSevenToEleven (i : Fin 7) : Fin 11 :=
  ⟨i.val, lt_trans i.isLt (by decide)⟩

def emb0123456Eleven : Fin 7 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono finSevenToEleven (by
    intro a b hab
    change a.val < b.val
    exact hab)

set_option maxHeartbeats 1000000 in
/-- Two six-cups sharing their first five vertices, with right turns through
the two remaining vertices, form a strong seven-set. -/
theorem strong0123456_of_overlapping_cups
    (χ : TripleColoring 11)
    (hfirst : IsCup χ emb012345Eleven)
    (hsecond : IsCup χ emb012346Eleven)
    (h056 : χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right)
    (h156 : χ ⟨1, 5, 6, by decide, by decide⟩ = Turn.right)
    (h256 : χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right)
    (h356 : χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right)
    (h456 : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right) :
    IsStrongPolygonOn χ emb0123456Eleven := by
  rcases hfirst with ⟨_, hfirst⟩
  rcases hsecond with ⟨_, hsecond⟩
  have hleftTriple (i j k : Fin 7) (hij : i < j) (hjk : j < k)
      (hnotFan : ¬(j = 5 ∧ k = 6)) :
      χ ⟨emb0123456Eleven i, emb0123456Eleven j, emb0123456Eleven k,
        emb0123456Eleven.strictMono hij, emb0123456Eleven.strictMono hjk⟩ = Turn.left := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals (try norm_num at hij)
    all_goals (try norm_num at hjk)
    all_goals (try simp at hnotFan)
    all_goals first
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (0 : Fin 6)) (j := 1) (l := 2) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (0 : Fin 6)) (j := 1) (l := 3) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (0 : Fin 6)) (j := 1) (l := 4) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (0 : Fin 6)) (j := 1) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012346Eleven] using
          hsecond (i := (0 : Fin 6)) (j := 1) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (0 : Fin 6)) (j := 2) (l := 3) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (0 : Fin 6)) (j := 2) (l := 4) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (0 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012346Eleven] using
          hsecond (i := (0 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (0 : Fin 6)) (j := 3) (l := 4) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (0 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012346Eleven] using
          hsecond (i := (0 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (0 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012346Eleven] using
          hsecond (i := (0 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (1 : Fin 6)) (j := 2) (l := 3) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (1 : Fin 6)) (j := 2) (l := 4) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (1 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012346Eleven] using
          hsecond (i := (1 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (1 : Fin 6)) (j := 3) (l := 4) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (1 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012346Eleven] using
          hsecond (i := (1 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (1 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012346Eleven] using
          hsecond (i := (1 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (2 : Fin 6)) (j := 3) (l := 4) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (2 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012346Eleven] using
          hsecond (i := (2 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (2 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012346Eleven] using
          hsecond (i := (2 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012345Eleven] using
          hfirst (i := (3 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
      | simpa [emb0123456Eleven, emb012346Eleven] using
          hsecond (i := (3 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
  have hfanColor (i : Fin 7) (hi : i < 5) :
      χ ⟨emb0123456Eleven i, 5, 6, by
        change (emb0123456Eleven i).val < 5
        simpa [emb0123456Eleven, finSevenToEleven] using hi, by decide⟩ = Turn.right := by
    change i.val < 5 at hi
    fin_cases i
    · simpa [emb0123456Eleven, finSevenToEleven] using h056
    · simpa [emb0123456Eleven, finSevenToEleven] using h156
    · simpa [emb0123456Eleven, finSevenToEleven] using h256
    · simpa [emb0123456Eleven, finSevenToEleven] using h356
    · simpa [emb0123456Eleven, finSevenToEleven] using h456
    · norm_num at hi
    · norm_num at hi
  intro i j k l hij hjk hkl
  constructor
  · exact (hleftTriple i j k hij hjk (by omega)).trans
      (hleftTriple i j l hij (hjk.trans hkl) (by omega)).symm
  · by_cases hlast : k = 5 ∧ l = 6
    · rcases hlast with ⟨rfl, rfl⟩
      exact (hfanColor i (by omega)).trans (hfanColor j (by omega)).symm
    · exact (hleftTriple i k l (hij.trans hjk) hkl hlast).trans
        (hleftTriple j k l hjk hkl hlast).symm

/-- The left `346` branch of residual A has the explicit strong-seven witness
`{0,1,2,3,4,5,6}`. -/
theorem cupBlocks56_residualA_strong_of_346_left
    (χ : TripleColoring 11)
    (hleft : IsCupSet χ {0, 1, 2, 3, 4})
    (hone : OneChangeOn χ Finset.univ)
    (hfan : ∀ i : Fin 5, χ (frontFanTriple i) = Turn.right)
    (h345 : χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left)
    (h346 : χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) :
    ContainsStrongPolygonSet χ Finset.univ 7 := by
  have hfirst : IsCup χ emb012345Eleven := by
    apply isMonochromaticChain_finSix_of_consecutive emb012345Eleven
      (hone.mono (by simp))
    · simpa [emb012345Eleven] using
        hleft ⟨0, 1, 2, by decide, by decide⟩ (by simp) (by simp) (by simp)
    · simpa [emb012345Eleven] using
        hleft ⟨1, 2, 3, by decide, by decide⟩ (by simp) (by simp) (by simp)
    · simpa [emb012345Eleven] using
        hleft ⟨2, 3, 4, by decide, by decide⟩ (by simp) (by simp) (by simp)
    · simpa [emb012345Eleven] using h345
  have hsecond : IsCup χ emb012346Eleven := by
    apply isMonochromaticChain_finSix_of_consecutive emb012346Eleven
      (hone.mono (by simp))
    · simpa [emb012346Eleven] using
        hleft ⟨0, 1, 2, by decide, by decide⟩ (by simp) (by simp) (by simp)
    · simpa [emb012346Eleven] using
        hleft ⟨1, 2, 3, by decide, by decide⟩ (by simp) (by simp) (by simp)
    · simpa [emb012346Eleven] using
        hleft ⟨2, 3, 4, by decide, by decide⟩ (by simp) (by simp) (by simp)
    · simpa [emb012346Eleven] using h346
  apply containsStrongPolygonSet_univ_of_finSeven
  apply strong0123456_of_overlapping_cups χ hfirst hsecond
  · simpa [frontFanTriple, finFiveToEleven] using hfan 0
  · simpa [frontFanTriple, finFiveToEleven] using hfan 1
  · simpa [frontFanTriple, finFiveToEleven] using hfan 2
  · simpa [frontFanTriple, finFiveToEleven] using hfan 3
  · simpa [frontFanTriple, finFiveToEleven] using hfan 4

def emb01234510Eleven : Fin 7 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 5, 10] (by decide)

def emb3467Eleven : Fin 4 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![3, 4, 6, 7] (by decide)

def emb4678910Eleven : Fin 6 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![4, 6, 7, 8, 9, 10] (by decide)

def emb5678910Eleven : Fin 6 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![5, 6, 7, 8, 9, 10] (by decide)

def emb45678910Eleven : Fin 7 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![4, 5, 6, 7, 8, 9, 10] (by decide)

set_option maxHeartbeats 1000000 in
/-- A six-cup on the tail and a six-cup skipping the second vertex, together
with a right fan over the first pair, form a strong seven-set. -/
theorem strong45678910_of_split_cups
    (χ : TripleColoring 11)
    (htail : IsCup χ emb5678910Eleven)
    (hskip : IsCup χ emb4678910Eleven)
    (h456 : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right)
    (h457 : χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right)
    (h458 : χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right)
    (h459 : χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.right)
    (h4510 : χ ⟨4, 5, 10, by decide, by decide⟩ = Turn.right) :
    IsStrongPolygonOn χ emb45678910Eleven := by
  rcases htail with ⟨_, htail⟩
  rcases hskip with ⟨_, hskip⟩
  have h567 := htail (i := (0 : Fin 6)) (j := 1) (l := 2) (by decide) (by decide)
  have h568 := htail (i := (0 : Fin 6)) (j := 1) (l := 3) (by decide) (by decide)
  have h569 := htail (i := (0 : Fin 6)) (j := 1) (l := 4) (by decide) (by decide)
  have h5610 := htail (i := (0 : Fin 6)) (j := 1) (l := 5) (by decide) (by decide)
  have h578 := htail (i := (0 : Fin 6)) (j := 2) (l := 3) (by decide) (by decide)
  have h579 := htail (i := (0 : Fin 6)) (j := 2) (l := 4) (by decide) (by decide)
  have h5710 := htail (i := (0 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide)
  have h589 := htail (i := (0 : Fin 6)) (j := 3) (l := 4) (by decide) (by decide)
  have h5810 := htail (i := (0 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
  have h5910 := htail (i := (0 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
  have h678 := htail (i := (1 : Fin 6)) (j := 2) (l := 3) (by decide) (by decide)
  have h679 := htail (i := (1 : Fin 6)) (j := 2) (l := 4) (by decide) (by decide)
  have h6710 := htail (i := (1 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide)
  have h689 := htail (i := (1 : Fin 6)) (j := 3) (l := 4) (by decide) (by decide)
  have h6810 := htail (i := (1 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
  have h6910 := htail (i := (1 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
  have h789 := htail (i := (2 : Fin 6)) (j := 3) (l := 4) (by decide) (by decide)
  have h7810 := htail (i := (2 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
  have h7910 := htail (i := (2 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
  have h8910 := htail (i := (3 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
  have h467 := hskip (i := (0 : Fin 6)) (j := 1) (l := 2) (by decide) (by decide)
  have h468 := hskip (i := (0 : Fin 6)) (j := 1) (l := 3) (by decide) (by decide)
  have h469 := hskip (i := (0 : Fin 6)) (j := 1) (l := 4) (by decide) (by decide)
  have h4610 := hskip (i := (0 : Fin 6)) (j := 1) (l := 5) (by decide) (by decide)
  have h478 := hskip (i := (0 : Fin 6)) (j := 2) (l := 3) (by decide) (by decide)
  have h479 := hskip (i := (0 : Fin 6)) (j := 2) (l := 4) (by decide) (by decide)
  have h4710 := hskip (i := (0 : Fin 6)) (j := 2) (l := 5) (by decide) (by decide)
  have h489 := hskip (i := (0 : Fin 6)) (j := 3) (l := 4) (by decide) (by decide)
  have h4810 := hskip (i := (0 : Fin 6)) (j := 3) (l := 5) (by decide) (by decide)
  have h4910 := hskip (i := (0 : Fin 6)) (j := 4) (l := 5) (by decide) (by decide)
  intro i j k l hij hjk hkl
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
  all_goals (try norm_num at hij)
  all_goals (try norm_num at hjk)
  all_goals (try norm_num at hkl)
  all_goals simp_all [emb45678910Eleven, emb5678910Eleven,
    emb4678910Eleven, TripleColoring.restrict, OrderedTriple.map]

/-- Normalized eleven-vertex form of the next cup-block target. -/
def CupBlocks56FinEleven : Prop :=
  ∀ χ : TripleColoring 11,
    IsCupSet χ {0, 1, 2, 3, 4} → IsCupSet χ {5, 6, 7, 8, 9, 10} →
      OneChangeOn χ Finset.univ →
      ContainsCapSet χ Finset.univ 4 ∨
        ContainsCupSet χ Finset.univ 7 ∨
        ContainsStrongPolygonSet χ Finset.univ 7

/-- First remaining residual leaf after the fan, cap, and bridge-cup branches
are removed. -/
def CupBlocks56ResidualA : Prop :=
  ∀ χ : TripleColoring 11,
    IsCupSet χ {0, 1, 2, 3, 4} → IsCupSet χ {5, 6, 7, 8, 9, 10} →
      OneChangeOn χ Finset.univ →
      (∀ i : Fin 5,
        χ (frontFanTriple i) = Turn.right) →
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left →
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left →
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left →
      ContainsCapSet χ Finset.univ 4 ∨
        ContainsCupSet χ Finset.univ 7 ∨
        ContainsStrongPolygonSet χ Finset.univ 7

/-- The genuinely remaining half of residual A. The complementary left turn
at `346` already gives the explicit strong seven-set `{0,1,2,3,4,5,6}`. -/
def CupBlocks56ResidualARight346 : Prop :=
  ∀ χ : TripleColoring 11,
    IsCupSet χ {0, 1, 2, 3, 4} → IsCupSet χ {5, 6, 7, 8, 9, 10} →
      OneChangeOn χ Finset.univ →
      (∀ i : Fin 5, χ (frontFanTriple i) = Turn.right) →
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left →
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left →
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left →
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right →
      ContainsCapSet χ Finset.univ 4 ∨
        ContainsCupSet χ Finset.univ 7 ∨
        ContainsStrongPolygonSet χ Finset.univ 7

set_option maxHeartbeats 1200000 in
/-- The right-`346` residual closes by a cup/cap split. If both immediate
witnesses are avoided, the tail supplies two six-cups and the one-change law
forces the right fan needed for the strong seven-set `{4,5,6,7,8,9,10}`. -/
theorem cupBlocks56ResidualARight346 : CupBlocks56ResidualARight346 := by
  intro χ hleft hright hone hfan _h235 _h236 h345 h346
  cases h4510 : χ ⟨4, 5, 10, by decide, by decide⟩ with
  | left =>
      right
      left
      apply containsCupSet_univ_of_finSeven
      apply isMonochromaticChain_finSeven_of_consecutive emb01234510Eleven
        (hone.mono (by simp))
      · simpa [emb01234510Eleven] using
          hleft ⟨0, 1, 2, by decide, by decide⟩ (by simp) (by simp) (by simp)
      · simpa [emb01234510Eleven] using
          hleft ⟨1, 2, 3, by decide, by decide⟩ (by simp) (by simp) (by simp)
      · simpa [emb01234510Eleven] using
          hleft ⟨2, 3, 4, by decide, by decide⟩ (by simp) (by simp) (by simp)
      · simpa [emb01234510Eleven] using h345
      · simpa [emb01234510Eleven] using h4510
  | right =>
      cases h467 : χ ⟨4, 6, 7, by decide, by decide⟩ with
      | right =>
          left
          apply containsCapSet_univ_of_finFour
          apply isMonochromaticChain_finFour_of_outer_eq emb3467Eleven
            (hone.mono (by simp))
          · simpa [emb3467Eleven] using h346
          · simpa [emb3467Eleven] using h467
      | left =>
          have h567 : χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left := by
            simpa using hright ⟨5, 6, 7, by decide, by decide⟩
              (by simp) (by simp) (by simp)
          have h678 : χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
            simpa using hright ⟨6, 7, 8, by decide, by decide⟩
              (by simp) (by simp) (by simp)
          have h789 : χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
            simpa using hright ⟨7, 8, 9, by decide, by decide⟩
              (by simp) (by simp) (by simp)
          have h8910 : χ ⟨8, 9, 10, by decide, by decide⟩ = Turn.left := by
            simpa using hright ⟨8, 9, 10, by decide, by decide⟩
              (by simp) (by simp) (by simp)
          have htail : IsCup χ emb5678910Eleven := by
            apply isMonochromaticChain_finSix_of_consecutive emb5678910Eleven
              (hone.mono (by simp))
            · simpa [emb5678910Eleven] using h567
            · simpa [emb5678910Eleven] using h678
            · simpa [emb5678910Eleven] using h789
            · simpa [emb5678910Eleven] using h8910
          have hskip : IsCup χ emb4678910Eleven := by
            apply isMonochromaticChain_finSix_of_consecutive emb4678910Eleven
              (hone.mono (by simp))
            · simpa [emb4678910Eleven] using h467
            · simpa [emb4678910Eleven] using h678
            · simpa [emb4678910Eleven] using h789
            · simpa [emb4678910Eleven] using h8910
          have hfront (k : Fin 11) (hk5 : (5 : Fin 11) < k) (hk10 : k < 10)
              (h5k10 : χ ⟨5, k, 10, hk5, hk10⟩ = Turn.left) :
              χ ⟨4, 5, k, by omega, hk5⟩ = Turn.right := by
            have hallow := hone (i := (4 : Fin 11)) (j := 5) (k := k) (l := 10)
              (by decide) hk5 hk10 (by simp) (by simp) (by simp) (by simp)
            have heq := hallow.first_eq_second_of_second_ne_fourth
              (by simp [h4510, h5k10])
            exact heq.trans h4510
          have h457 : χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right := by
            apply hfront 7 (by decide) (by decide)
            simpa using hright ⟨5, 7, 10, by decide, by decide⟩
              (by simp) (by simp) (by simp)
          have h458 : χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right := by
            apply hfront 8 (by decide) (by decide)
            simpa using hright ⟨5, 8, 10, by decide, by decide⟩
              (by simp) (by simp) (by simp)
          have h459 : χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.right := by
            apply hfront 9 (by decide) (by decide)
            simpa using hright ⟨5, 9, 10, by decide, by decide⟩
              (by simp) (by simp) (by simp)
          have h456 : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right := by
            simpa [frontFanTriple, finFiveToEleven] using hfan 4
          right
          right
          apply containsStrongPolygonSet_univ_of_finSeven
          exact strong45678910_of_split_cups χ htail hskip h456 h457 h458 h459 h4510

/-- Closing the right-`346` refinement suffices to close all of residual A. -/
theorem cupBlocks56ResidualA_of_right346
    (hA : CupBlocks56ResidualARight346) : CupBlocks56ResidualA := by
  intro χ hleft hright hone hfan h235 h236 h345
  by_cases h346 : χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left
  · exact Or.inr (Or.inr
      (cupBlocks56_residualA_strong_of_346_left χ hleft hone hfan h345 h346))
  · have h346r : χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right := by
      cases h : χ ⟨3, 4, 6, by decide, by decide⟩ <;> simp_all
    exact hA χ hleft hright hone hfan h235 h236 h345 h346r

/-- Residual A is closed by the two explicit `346` branches. -/
theorem cupBlocks56ResidualA : CupBlocks56ResidualA :=
  cupBlocks56ResidualA_of_right346 cupBlocks56ResidualARight346

/-- Second remaining residual leaf after the fan, cap, and bridge-cup branches
are removed. -/
def CupBlocks56ResidualC : Prop :=
  ∀ χ : TripleColoring 11,
    IsCupSet χ {0, 1, 2, 3, 4} → IsCupSet χ {5, 6, 7, 8, 9, 10} →
      OneChangeOn χ Finset.univ →
      (∀ i : Fin 5,
        χ (frontFanTriple i) = Turn.right) →
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left →
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right →
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left →
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right →
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left →
      ContainsCapSet χ Finset.univ 4 ∨
        ContainsCupSet χ Finset.univ 7 ∨
        ContainsStrongPolygonSet χ Finset.univ 7

set_option maxHeartbeats 1200000 in
/-- Residual C closes by forcing `459` right and `467` left. A left turn at
`4510` gives a seven-cup; a right turn completes the split-cup strong-seven
configuration on `{4,5,6,7,8,9,10}`. -/
theorem cupBlocks56ResidualC : CupBlocks56ResidualC := by
  intro χ hleft hright hone hfan _h235 h236 h367 h359 h345
  have h459 : χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.right := by
    have hallow := hone (i := (3 : Fin 11)) (j := 4) (k := 5) (l := 9)
      (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    have heq := hallow.third_eq_fourth_of_first_ne_third
      (by simp [h345, h359])
    exact heq.symm.trans h359
  have h346 : χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right := by
    have h234 : χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left := by
      simpa using hleft ⟨2, 3, 4, by decide, by decide⟩
        (by simp) (by simp) (by simp)
    have hallow := hone (i := (2 : Fin 11)) (j := 3) (k := 4) (l := 6)
      (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    cases h246 : χ ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases h346' : χ ⟨3, 4, 6, by decide, by decide⟩ <;>
      simp_all [TurnSequenceAllowed]
  have h467 : χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.left := by
    have hallow := hone (i := (3 : Fin 11)) (j := 4) (k := 6) (l := 7)
      (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    have heq := hallow.third_eq_fourth_of_first_ne_third
      (by simp [h346, h367])
    exact heq.symm.trans h367
  cases h4510 : χ ⟨4, 5, 10, by decide, by decide⟩ with
  | left =>
      right
      left
      apply containsCupSet_univ_of_finSeven
      apply isMonochromaticChain_finSeven_of_consecutive emb01234510Eleven
        (hone.mono (by simp))
      · simpa [emb01234510Eleven] using
          hleft ⟨0, 1, 2, by decide, by decide⟩ (by simp) (by simp) (by simp)
      · simpa [emb01234510Eleven] using
          hleft ⟨1, 2, 3, by decide, by decide⟩ (by simp) (by simp) (by simp)
      · simpa [emb01234510Eleven] using
          hleft ⟨2, 3, 4, by decide, by decide⟩ (by simp) (by simp) (by simp)
      · simpa [emb01234510Eleven] using h345
      · simpa [emb01234510Eleven] using h4510
  | right =>
      have h567 : χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left := by
        simpa using hright ⟨5, 6, 7, by decide, by decide⟩
          (by simp) (by simp) (by simp)
      have h678 : χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
        simpa using hright ⟨6, 7, 8, by decide, by decide⟩
          (by simp) (by simp) (by simp)
      have h789 : χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
        simpa using hright ⟨7, 8, 9, by decide, by decide⟩
          (by simp) (by simp) (by simp)
      have h8910 : χ ⟨8, 9, 10, by decide, by decide⟩ = Turn.left := by
        simpa using hright ⟨8, 9, 10, by decide, by decide⟩
          (by simp) (by simp) (by simp)
      have htail : IsCup χ emb5678910Eleven := by
        apply isMonochromaticChain_finSix_of_consecutive emb5678910Eleven
          (hone.mono (by simp))
        · simpa [emb5678910Eleven] using h567
        · simpa [emb5678910Eleven] using h678
        · simpa [emb5678910Eleven] using h789
        · simpa [emb5678910Eleven] using h8910
      have hskip : IsCup χ emb4678910Eleven := by
        apply isMonochromaticChain_finSix_of_consecutive emb4678910Eleven
          (hone.mono (by simp))
        · simpa [emb4678910Eleven] using h467
        · simpa [emb4678910Eleven] using h678
        · simpa [emb4678910Eleven] using h789
        · simpa [emb4678910Eleven] using h8910
      have hfront (k : Fin 11) (hk5 : (5 : Fin 11) < k) (hk9 : k < 9)
          (h5k9 : χ ⟨5, k, 9, hk5, hk9⟩ = Turn.left) :
          χ ⟨4, 5, k, by omega, hk5⟩ = Turn.right := by
        have hallow := hone (i := (4 : Fin 11)) (j := 5) (k := k) (l := 9)
          (by decide) hk5 hk9 (by simp) (by simp) (by simp) (by simp)
        have heq := hallow.first_eq_second_of_second_ne_fourth
          (by simp [h459, h5k9])
        exact heq.trans h459
      have h457 : χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right := by
        apply hfront 7 (by decide) (by decide)
        simpa using hright ⟨5, 7, 9, by decide, by decide⟩
          (by simp) (by simp) (by simp)
      have h458 : χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right := by
        apply hfront 8 (by decide) (by decide)
        simpa using hright ⟨5, 8, 9, by decide, by decide⟩
          (by simp) (by simp) (by simp)
      have h456 : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right := by
        simpa [frontFanTriple, finFiveToEleven] using hfan 4
      right
      right
      apply containsStrongPolygonSet_univ_of_finSeven
      exact strong45678910_of_split_cups χ htail hskip h456 h457 h458 h459 h4510

/-- Arbitrary ordered-block form of the proposed `(4,7,7)` local gate. -/
def CupBlocks56Force477 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ((left.card = 5 ∧ right.card = 6) ∨
        (left.card = 6 ∧ right.card = 5)) →
      IsCupSet χ left → IsCupSet χ right → OneChangeOn χ (left ∪ right) →
      ContainsCapSet χ (left ∪ right) 4 ∨
        ContainsCupSet χ (left ∪ right) 7 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 7

def emb2356Eleven : Fin 4 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![2, 3, 5, 6] (by decide)

def emb3456Eleven : Fin 4 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![3, 4, 5, 6] (by decide)

def emb2367Eleven : Fin 4 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![2, 3, 6, 7] (by decide)

/-- The normalized `5+6` theorem reduces to the two explicitly named residual
leaves. All other branches have concrete cap or cup witnesses. -/
theorem cupBlocks56FinEleven_of_residuals
    (hA : CupBlocks56ResidualA) (hC : CupBlocks56ResidualC) :
    CupBlocks56FinEleven := by
  intro χ hleft hright hone
  rcases cupBlocks56_containsCupSeven_or_rightFan χ hright hone with hcup | hfan
  · exact Or.inr (Or.inl hcup)
  have h356 : χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    simpa [frontFanTriple, finFiveToEleven] using hfan 3
  have h456 : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right := by
    simpa [frontFanTriple, finFiveToEleven] using hfan 4
  have hcapOfOuter (f : Fin 4 ↪o Fin 11)
      (h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = Turn.right)
      (h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = Turn.right) :
      ContainsCapSet χ Finset.univ 4 := by
    apply containsCapSet_univ_of_finFour
    exact isMonochromaticChain_finFour_of_outer_eq f
      (hone.mono (by simp)) h012 h123
  by_cases h345 : χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left
  · by_cases h235 : χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left
    · by_cases h236 : χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left
      · exact hA χ hleft hright hone hfan h235 h236 h345
      · have h236r : χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
          cases h : χ ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
        by_cases h367 : χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left
        · by_cases h359 : χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left
          · exact Or.inr (Or.inl
              (cupBlocks56_containsCupSeven_of_bridge_turns
                χ hleft hright hone h235 h359))
          · have h359r : χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
              cases h : χ ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
            exact hC χ hleft hright hone hfan h235 h236r h367 h359r h345
        · have h367r : χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right := by
            cases h : χ ⟨3, 6, 7, by decide, by decide⟩ <;> simp_all
          exact Or.inl (hcapOfOuter emb2367Eleven
            (by simpa [emb2367Eleven] using h236r)
            (by simpa [emb2367Eleven] using h367r))
    · have h235r : χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
        cases h : χ ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
      exact Or.inl (hcapOfOuter emb2356Eleven
        (by simpa [emb2356Eleven] using h235r)
        (by simpa [emb2356Eleven] using h356))
  · have h345r : χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.right := by
      cases h : χ ⟨3, 4, 5, by decide, by decide⟩ <;> simp_all
    exact Or.inl (hcapOfOuter emb3456Eleven
      (by simpa [emb3456Eleven] using h345r)
      (by simpa [emb3456Eleven] using h456))

/-- The normalized eleven-vertex `5+6` cup-block gate. -/
theorem cupBlocks56FinEleven : CupBlocks56FinEleven :=
  cupBlocks56FinEleven_of_residuals cupBlocks56ResidualA cupBlocks56ResidualC

/-- Reversal derives the normalized `6+5` orientation from the proposed
normalized `5+6` theorem. -/
theorem cupBlocks65_finEleven_of_cupBlocks56
    (hnormalized : CupBlocks56FinEleven)
    (χ : TripleColoring 11)
    (hleft : IsCupSet χ {0, 1, 2, 3, 4, 5})
    (hright : IsCupSet χ {6, 7, 8, 9, 10})
    (hone : OneChangeOn χ Finset.univ) :
    ContainsCapSet χ Finset.univ 4 ∨
      ContainsCupSet χ Finset.univ 7 ∨
      ContainsStrongPolygonSet χ Finset.univ 7 := by
  let ψ := reverseColor χ
  have hrevFirst : ∀ i : Fin 11,
      i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 11)) →
        i.rev ∈ ({6, 7, 8, 9, 10} : Finset (Fin 11)) := by
    intro i hi
    fin_cases i <;> simp_all
  have hrevLast : ∀ i : Fin 11,
      i ∈ ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)) →
        i.rev ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)) := by
    intro i hi
    fin_cases i <;> simp_all
  have hψLeft : IsCupSet ψ {0, 1, 2, 3, 4} := by
    intro t hi hj hk
    exact hright (reverseOrderedTriple t)
      (hrevFirst t.k hk) (hrevFirst t.j hj) (hrevFirst t.i hi)
  have hψRight : IsCupSet ψ {5, 6, 7, 8, 9, 10} := by
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
/-- Transport the proposed normalized `5+6` theorem to arbitrary ordered
blocks of the same sizes. -/
theorem cupBlocks56Force477_five_six_of_finEleven
    (hnormalized : CupBlocks56FinEleven)
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleftCard : left.card = 5) (hrightCard : right.card = 6)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right)) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsCupSet χ (left ∪ right) 7 ∨
      ContainsStrongPolygonSet χ (left ∪ right) 7 := by
  let le : Fin 5 ↪o Fin n := left.orderEmbOfFin hleftCard
  let re : Fin 6 ↪o Fin n := right.orderEmbOfFin hrightCard
  let f : Fin 11 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![le 0, le 1, le 2, le 3, le 4, re 0, re 1, re 2, re 3, re 4, re 5] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact re.strictMono (by decide)
        | exact horder _ (left.orderEmbOfFin_mem hleftCard _)
            _ (right.orderEmbOfFin_mem hrightCard _))
  let ψ : TripleColoring 11 := χ.restrict f
  have hfmem : ∀ i : Fin 11, f i ∈ left ∪ right := by
    intro i
    fin_cases i <;>
      simp [f, le, re, left.orderEmbOfFin_mem hleftCard,
        right.orderEmbOfFin_mem hrightCard]
  have hfirst : ∀ i : Fin 11,
      i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 11)) → f i ∈ left := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      exact left.orderEmbOfFin_mem hleftCard _
  have hlast : ∀ i : Fin 11,
      i ∈ ({5, 6, 7, 8, 9, 10} : Finset (Fin 11)) → f i ∈ right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact right.orderEmbOfFin_mem hrightCard _
  have hψLeft : IsCupSet ψ {0, 1, 2, 3, 4} := by
    intro t hi hj hk
    exact hleft (t.map f) (hfirst t.i hi) (hfirst t.j hj) (hfirst t.k hk)
  have hψRight : IsCupSet ψ {5, 6, 7, 8, 9, 10} := by
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
    · have himageCard : (Finset.univ.image f).card = 11 := by
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
/-- Transport the reversed normalized theorem to arbitrary ordered `6+5`
blocks. -/
theorem cupBlocks56Force477_six_five_of_finEleven
    (hnormalized : CupBlocks56FinEleven)
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleftCard : left.card = 6) (hrightCard : right.card = 5)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right)) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsCupSet χ (left ∪ right) 7 ∨
      ContainsStrongPolygonSet χ (left ∪ right) 7 := by
  let le : Fin 6 ↪o Fin n := left.orderEmbOfFin hleftCard
  let re : Fin 5 ↪o Fin n := right.orderEmbOfFin hrightCard
  let f : Fin 11 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![le 0, le 1, le 2, le 3, le 4, le 5, re 0, re 1, re 2, re 3, re 4] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact re.strictMono (by decide)
        | exact horder _ (left.orderEmbOfFin_mem hleftCard _)
            _ (right.orderEmbOfFin_mem hrightCard _))
  let ψ : TripleColoring 11 := χ.restrict f
  have hfmem : ∀ i : Fin 11, f i ∈ left ∪ right := by
    intro i
    fin_cases i <;>
      simp [f, le, re, left.orderEmbOfFin_mem hleftCard,
        right.orderEmbOfFin_mem hrightCard]
  have hfirst : ∀ i : Fin 11,
      i ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)) → f i ∈ left := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact left.orderEmbOfFin_mem hleftCard _
  have hlast : ∀ i : Fin 11,
      i ∈ ({6, 7, 8, 9, 10} : Finset (Fin 11)) → f i ∈ right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      exact right.orderEmbOfFin_mem hrightCard _
  have hψLeft : IsCupSet ψ {0, 1, 2, 3, 4, 5} := by
    intro t hi hj hk
    exact hleft (t.map f) (hfirst t.i hi) (hfirst t.j hj) (hfirst t.k hk)
  have hψRight : IsCupSet ψ {6, 7, 8, 9, 10} := by
    intro t hi hj hk
    exact hright (t.map f) (hlast t.i hi) (hlast t.j hj) (hlast t.k hk)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
      (hfmem i) (hfmem j) (hfmem k) (hfmem l)
  have hout := cupBlocks65_finEleven_of_cupBlocks56
    hnormalized ψ hψLeft hψRight hψOne
  have himage : Finset.univ.image f = left ∪ right := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfmem i
    · have himageCard : (Finset.univ.image f).card = 11 := by
        simpa using Finset.card_image_of_injective Finset.univ f.injective
      rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard,
        himageCard]
  rcases hout with hcap | hcup | hstrong
  · exact Or.inl (by simpa [himage] using containsCapSet_map_restrict f hcap)
  · exact Or.inr (Or.inl (by
      simpa [himage] using containsCupSet_map_restrict f hcup))
  · exact Or.inr (Or.inr (by
      simpa [himage] using containsStrongPolygonSet_map_restrict f hstrong))

/-- The normalized target alone suffices for the full ordered-block contract. -/
theorem cupBlocks56Force477_of_finEleven
    (hnormalized : CupBlocks56FinEleven) : CupBlocks56Force477 := by
  intro n χ left right hdisjoint horder hcards hleft hright hone
  rcases hcards with ⟨hleftCard, hrightCard⟩ | ⟨hleftCard, hrightCard⟩
  · exact cupBlocks56Force477_five_six_of_finEleven hnormalized
      hdisjoint horder hleftCard hrightCard hleft hright hone
  · exact cupBlocks56Force477_six_five_of_finEleven hnormalized
      hdisjoint horder hleftCard hrightCard hleft hright hone

/-- The full ordered `5+6/6+5` cup-block gate. -/
theorem cupBlocks56Force477 : CupBlocks56Force477 :=
  cupBlocks56Force477_of_finEleven cupBlocks56FinEleven

/-- The proposed `5+6/6+5` gate has exactly the required quantitative payoff:
two ordered cup blocks avoiding all `(4,7,7)` outcomes contain at most ten
vertices in total. -/
theorem cup_block_card_add_le_ten_of_cupBlocks56
    (hblocks : CupBlocks56Force477) {n : ℕ} {χ : TripleColoring n}
    {left right : Finset (Fin n)} (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoCap : ¬ContainsCapSet χ (left ∪ right) 4)
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) 7) :
    left.card + right.card ≤ 10 := by
  have hleftCard : left.card ≤ 6 := by
    by_contra hcard
    have hseven : 7 ≤ left.card := by omega
    obtain ⟨seven, hsevenSub, hsevenCard⟩ := Finset.exists_subset_card_eq hseven
    apply hnoCup
    exact ⟨seven, hsevenSub.trans Finset.subset_union_left, hsevenCard,
      FinsetPolygon.IsCupSet.mono hleft hsevenSub⟩
  have hrightCard : right.card ≤ 6 := by
    by_contra hcard
    have hseven : 7 ≤ right.card := by omega
    obtain ⟨seven, hsevenSub, hsevenCard⟩ := Finset.exists_subset_card_eq hseven
    apply hnoCup
    exact ⟨seven, hsevenSub.trans Finset.subset_union_right, hsevenCard,
      FinsetPolygon.IsCupSet.mono hright hsevenSub⟩
  by_contra hsum
  have hsizes : (5 ≤ left.card ∧ 6 ≤ right.card) ∨
      (6 ≤ left.card ∧ 5 ≤ right.card) := by
    omega
  rcases hsizes with hsizes | hsizes
  · obtain ⟨left', hleftSub, hleftCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.1
    obtain ⟨right', hrightSub, hrightCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.2
    have hout := hblocks (hdisjoint.mono hleftSub hrightSub)
      (fun x hx y hy ↦ horder x (hleftSub hx) y (hrightSub hy))
      (Or.inl ⟨hleftCard', hrightCard'⟩)
      (FinsetPolygon.IsCupSet.mono hleft hleftSub)
      (FinsetPolygon.IsCupSet.mono hright hrightSub)
      (hone.mono (Finset.union_subset_union hleftSub hrightSub))
    have hsub : left' ∪ right' ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    rcases hout with hcap | hcup | hstrong
    · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hsub)
    · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hsub)
    · exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hsub)
  · obtain ⟨left', hleftSub, hleftCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.1
    obtain ⟨right', hrightSub, hrightCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.2
    have hout := hblocks (hdisjoint.mono hleftSub hrightSub)
      (fun x hx y hy ↦ horder x (hleftSub hx) y (hrightSub hy))
      (Or.inr ⟨hleftCard', hrightCard'⟩)
      (FinsetPolygon.IsCupSet.mono hleft hleftSub)
      (FinsetPolygon.IsCupSet.mono hright hrightSub)
      (hone.mono (Finset.union_subset_union hleftSub hrightSub))
    have hsub : left' ∪ right' ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    rcases hout with hcap | hcup | hstrong
    · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hsub)
    · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hsub)
    · exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hsub)

end ErdosSzekeres

end
