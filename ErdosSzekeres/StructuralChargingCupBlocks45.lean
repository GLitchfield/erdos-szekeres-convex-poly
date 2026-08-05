module

public import ErdosSzekeres.StructuralChargingIntervals

@[expose] public section

/-!
# The normalized `4+5` cup-block core

This file proves the first `k = 6` coupled cup-block gate by a fixed nine-leaf
symbolic argument.  It uses only the rank-three one-change law.
-/

namespace ErdosSzekeres

def emb045678 : Fin 6 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![0, 4, 5, 6, 7, 8] (by decide)

def emb145678 : Fin 6 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![1, 4, 5, 6, 7, 8] (by decide)

def emb245678 : Fin 6 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![2, 4, 5, 6, 7, 8] (by decide)

def emb345678 : Fin 6 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 8] (by decide)

def emb012345 : Fin 6 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 5] (by decide)

def emb012348 : Fin 6 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4, 8] (by decide)

def emb2345Nine : Fin 4 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![2, 3, 4, 5] (by decide)

def emb2356Nine : Fin 4 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![2, 3, 5, 6] (by decide)

def emb01234Nine : Fin 5 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4] (by decide)

def emb01235Nine : Fin 5 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 5] (by decide)

def emb45678Nine : Fin 5 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![4, 5, 6, 7, 8] (by decide)

def emb35678Nine : Fin 5 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono ![3, 5, 6, 7, 8] (by decide)

def emb01234Six : Fin 5 ↪o Fin 6 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4] (by decide)

def emb12345Six : Fin 5 ↪o Fin 6 :=
  OrderEmbedding.ofStrictMono ![1, 2, 3, 4, 5] (by decide)

theorem containsCupSet_univ_of_finSix {n : ℕ} {χ : TripleColoring n}
    {f : Fin 6 ↪o Fin n} (h : IsCup χ f) :
    ContainsCupSet χ Finset.univ 6 := by
  refine ⟨Finset.univ.image f, by simp, ?_, FinsetPolygon.IsCup.image h⟩
  simpa using Finset.card_image_of_injective Finset.univ f.injective

theorem containsStrongPolygonSet_univ_of_finSix
    {n : ℕ} {χ : TripleColoring n} {f : Fin 6 ↪o Fin n}
    (h : IsStrongPolygonOn χ f) :
    ContainsStrongPolygonSet χ Finset.univ 6 := by
  refine ⟨Finset.univ.image f, by simp, ?_,
    FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image h⟩
  simpa using Finset.card_image_of_injective Finset.univ f.injective

set_option maxHeartbeats 800000 in
/-- Four equal consecutive turns determine all twenty turns on a six-chain. -/
theorem isMonochromaticChain_finSix_of_consecutive
    {n : ℕ} {χ : TripleColoring n} {c : Turn} (f : Fin 6 ↪o Fin n)
    (hone : OneChangeOn χ (Finset.univ.image f))
    (h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = c)
    (h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = c)
    (h234 : χ ⟨f 2, f 3, f 4, by simp, by simp⟩ = c)
    (h345 : χ ⟨f 3, f 4, f 5, by simp, by simp⟩ = c) :
    IsMonochromaticChain χ c f := by
  let first : Fin 5 ↪o Fin n := emb01234Six.trans f
  let last : Fin 5 ↪o Fin n := emb12345Six.trans f
  have hfirst := isMonochromaticChain_finFive_of_consecutive first
    (hone.mono (by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨i, rfl⟩ := hx
      exact ⟨emb01234Six i, rfl⟩)) (by simpa [first, emb01234Six] using h012)
      (by simpa [first] using h123) (by simpa [first] using h234)
  have hlast := isMonochromaticChain_finFive_of_consecutive last
    (hone.mono (by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨i, rfl⟩ := hx
      exact ⟨emb12345Six i, rfl⟩)) (by simpa [last, emb12345Six] using h123)
      (by simpa [last] using h234) (by simpa [last] using h345)
  have hallow0145 := hone (i := f 0) (j := f 1) (k := f 4) (l := f 5)
    (f.strictMono (by decide)) (f.strictMono (by decide))
    (f.strictMono (by decide)) (by simp) (by simp) (by simp) (by simp)
  have h014 : χ ⟨f 0, f 1, f 4, by simp, by simp⟩ = c := by
    simpa [first, emb01234Six] using
      hfirst.2 (i := (0 : Fin 5)) (j := 1) (l := 4) (by decide) (by decide)
  have h145' : χ ⟨f 1, f 4, f 5, by simp, by simp⟩ = c := by
    simpa [last, emb12345Six] using
      hlast.2 (i := (0 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  have houter0145 :
      χ ⟨f 0, f 1, f 4, by simp, by simp⟩ =
        χ ⟨f 1, f 4, f 5, by simp, by simp⟩ := h014.trans h145'.symm
  have heq0145 := hallow0145.all_eq_of_outer_eq houter0145
  have h015 : χ ⟨f 0, f 1, f 5, by simp, by simp⟩ = c := by
    exact heq0145.1.symm.trans h014
  have hallow0245 := hone (i := f 0) (j := f 2) (k := f 4) (l := f 5)
    (f.strictMono (by decide)) (f.strictMono (by decide))
    (f.strictMono (by decide)) (by simp) (by simp) (by simp) (by simp)
  have h024 : χ ⟨f 0, f 2, f 4, by simp, by simp⟩ = c := by
    simpa [first, emb01234Six] using
      hfirst.2 (i := (0 : Fin 5)) (j := 2) (l := 4) (by decide) (by decide)
  have h245 : χ ⟨f 2, f 4, f 5, by simp, by simp⟩ = c := by
    simpa [last, emb12345Six] using
      hlast.2 (i := (1 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  have houter0245 :
      χ ⟨f 0, f 2, f 4, by simp, by simp⟩ =
        χ ⟨f 2, f 4, f 5, by simp, by simp⟩ := h024.trans h245.symm
  have heq0245 := hallow0245.all_eq_of_outer_eq houter0245
  have h025 : χ ⟨f 0, f 2, f 5, by simp, by simp⟩ = c := by
    exact heq0245.1.symm.trans h024
  have hallow0345 := hone (i := f 0) (j := f 3) (k := f 4) (l := f 5)
    (f.strictMono (by decide)) (f.strictMono (by decide))
    (f.strictMono (by decide)) (by simp) (by simp) (by simp) (by simp)
  have h034 : χ ⟨f 0, f 3, f 4, by simp, by simp⟩ = c := by
    simpa [first, emb01234Six] using
      hfirst.2 (i := (0 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  have h345' : χ ⟨f 3, f 4, f 5, by simp, by simp⟩ = c := h345
  have houter0345 :
      χ ⟨f 0, f 3, f 4, by simp, by simp⟩ =
        χ ⟨f 3, f 4, f 5, by simp, by simp⟩ := h034.trans h345'.symm
  have heq0345 := hallow0345.all_eq_of_outer_eq houter0345
  have h035 : χ ⟨f 0, f 3, f 5, by simp, by simp⟩ = c := by
    exact heq0345.1.symm.trans h034
  have h045 : χ ⟨f 0, f 4, f 5, by simp, by simp⟩ = c := by
    exact heq0345.2.2.trans h345'
  refine ⟨f.strictMono, ?_⟩
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals (try norm_num at hij)
  all_goals (try norm_num at hjk)
  all_goals first
    | simpa [first] using hfirst.2 (i := (0 : Fin 5)) (j := 1) (l := 2)
        (by decide) (by decide)
    | simpa [first] using hfirst.2 (i := (0 : Fin 5)) (j := 1) (l := 3)
        (by decide) (by decide)
    | simpa [first] using hfirst.2 (i := (0 : Fin 5)) (j := 1) (l := 4)
        (by decide) (by decide)
    | exact h015
    | simpa [first] using hfirst.2 (i := (0 : Fin 5)) (j := 2) (l := 3)
        (by decide) (by decide)
    | simpa [first] using hfirst.2 (i := (0 : Fin 5)) (j := 2) (l := 4)
        (by decide) (by decide)
    | exact h025
    | simpa [first] using hfirst.2 (i := (0 : Fin 5)) (j := 3) (l := 4)
        (by decide) (by decide)
    | exact h035
    | exact h045
    | simpa [last] using hlast.2 (i := (0 : Fin 5)) (j := 1) (l := 2)
        (by decide) (by decide)
    | simpa [last] using hlast.2 (i := (0 : Fin 5)) (j := 1) (l := 3)
        (by decide) (by decide)
    | simpa [last] using hlast.2 (i := (0 : Fin 5)) (j := 1) (l := 4)
        (by decide) (by decide)
    | simpa [last] using hlast.2 (i := (0 : Fin 5)) (j := 2) (l := 3)
        (by decide) (by decide)
    | simpa [last] using hlast.2 (i := (0 : Fin 5)) (j := 2) (l := 4)
        (by decide) (by decide)
    | simpa [last] using hlast.2 (i := (0 : Fin 5)) (j := 3) (l := 4)
        (by decide) (by decide)
    | simpa [last] using hlast.2 (i := (1 : Fin 5)) (j := 2) (l := 3)
        (by decide) (by decide)
    | simpa [last] using hlast.2 (i := (1 : Fin 5)) (j := 2) (l := 4)
        (by decide) (by decide)
    | simpa [last] using hlast.2 (i := (1 : Fin 5)) (j := 3) (l := 4)
        (by decide) (by decide)
    | simpa [last] using hlast.2 (i := (2 : Fin 5)) (j := 3) (l := 4)
        (by decide) (by decide)

/-- Two cups sharing their first four vertices, with right turns through the
two remaining vertices, form a strong six-set. -/
theorem strong012345_of_overlapping_cups (χ : TripleColoring 9)
    (hfirst : IsCup χ emb01234Nine) (hsecond : IsCup χ emb01235Nine)
    (h045 : χ ⟨0, 4, 5, by decide, by decide⟩ = Turn.right)
    (h145 : χ ⟨1, 4, 5, by decide, by decide⟩ = Turn.right)
    (h245 : χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.right)
    (h345 : χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.right) :
    IsStrongPolygonOn χ emb012345 := by
  rw [isStrongPolygonOn_finSix_iff]
  rcases hfirst with ⟨_, hfirst⟩
  rcases hsecond with ⟨_, hsecond⟩
  have hf012 := hfirst (i := (0 : Fin 5)) (j := 1) (l := 2) (by decide) (by decide)
  have hf013 := hfirst (i := (0 : Fin 5)) (j := 1) (l := 3) (by decide) (by decide)
  have hf014 := hfirst (i := (0 : Fin 5)) (j := 1) (l := 4) (by decide) (by decide)
  have hf023 := hfirst (i := (0 : Fin 5)) (j := 2) (l := 3) (by decide) (by decide)
  have hf024 := hfirst (i := (0 : Fin 5)) (j := 2) (l := 4) (by decide) (by decide)
  have hf034 := hfirst (i := (0 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  have hf123 := hfirst (i := (1 : Fin 5)) (j := 2) (l := 3) (by decide) (by decide)
  have hf124 := hfirst (i := (1 : Fin 5)) (j := 2) (l := 4) (by decide) (by decide)
  have hf134 := hfirst (i := (1 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  have hf234 := hfirst (i := (2 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  have hs015 := hsecond (i := (0 : Fin 5)) (j := 1) (l := 4) (by decide) (by decide)
  have hs025 := hsecond (i := (0 : Fin 5)) (j := 2) (l := 4) (by decide) (by decide)
  have hs035 := hsecond (i := (0 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  have hs125 := hsecond (i := (1 : Fin 5)) (j := 2) (l := 4) (by decide) (by decide)
  have hs135 := hsecond (i := (1 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  have hs235 := hsecond (i := (2 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  simp only [StrongSixValues, emb012345]
  simp_all [emb01234Nine, emb01235Nine]

/-- Two cups sharing their last four vertices, with right turns through the
two remaining vertices, form a strong six-set. -/
theorem strong345678_of_overlapping_cups (χ : TripleColoring 9)
    (hfirst : IsCup χ emb45678Nine) (hsecond : IsCup χ emb35678Nine)
    (h345 : χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.right)
    (h346 : χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right)
    (h347 : χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.right)
    (h348 : χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.right) :
    IsStrongPolygonOn χ emb345678 := by
  rw [isStrongPolygonOn_finSix_iff]
  rcases hfirst with ⟨_, hfirst⟩
  rcases hsecond with ⟨_, hsecond⟩
  have hf456 := hfirst (i := (0 : Fin 5)) (j := 1) (l := 2) (by decide) (by decide)
  have hf457 := hfirst (i := (0 : Fin 5)) (j := 1) (l := 3) (by decide) (by decide)
  have hf458 := hfirst (i := (0 : Fin 5)) (j := 1) (l := 4) (by decide) (by decide)
  have hf467 := hfirst (i := (0 : Fin 5)) (j := 2) (l := 3) (by decide) (by decide)
  have hf468 := hfirst (i := (0 : Fin 5)) (j := 2) (l := 4) (by decide) (by decide)
  have hf478 := hfirst (i := (0 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  have hf567 := hfirst (i := (1 : Fin 5)) (j := 2) (l := 3) (by decide) (by decide)
  have hf568 := hfirst (i := (1 : Fin 5)) (j := 2) (l := 4) (by decide) (by decide)
  have hf578 := hfirst (i := (1 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  have hf678 := hfirst (i := (2 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  have hs356 := hsecond (i := (0 : Fin 5)) (j := 1) (l := 2) (by decide) (by decide)
  have hs357 := hsecond (i := (0 : Fin 5)) (j := 1) (l := 3) (by decide) (by decide)
  have hs358 := hsecond (i := (0 : Fin 5)) (j := 1) (l := 4) (by decide) (by decide)
  have hs367 := hsecond (i := (0 : Fin 5)) (j := 2) (l := 3) (by decide) (by decide)
  have hs368 := hsecond (i := (0 : Fin 5)) (j := 2) (l := 4) (by decide) (by decide)
  have hs378 := hsecond (i := (0 : Fin 5)) (j := 3) (l := 4) (by decide) (by decide)
  simp only [StrongSixValues, emb345678]
  simp_all [emb45678Nine, emb35678Nine]

/-- The normalized `4+5` cup-block gate, proved by nine fixed witnesses. -/
theorem cupBlocks45_finNine : CupBlocks45FinNine := by
  intro χ hleft hright hone
  have h012 : χ ⟨0, 1, 2, by decide, by decide⟩ = Turn.left :=
    hleft _ (by simp) (by simp) (by simp)
  have h123 : χ ⟨1, 2, 3, by decide, by decide⟩ = Turn.left :=
    hleft _ (by simp) (by simp) (by simp)
  have h456 : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left :=
    hright _ (by simp) (by simp) (by simp)
  have h468 : χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left :=
    hright _ (by simp) (by simp) (by simp)
  have h478 : χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left :=
    hright _ (by simp) (by simp) (by simp)
  have h567 : χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left :=
    hright _ (by simp) (by simp) (by simp)
  have h678 : χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left :=
    hright _ (by simp) (by simp) (by simp)
  cases h045 : χ ⟨0, 4, 5, by decide, by decide⟩ with
  | left =>
      right; left
      apply containsCupSet_univ_of_finSix
      apply isMonochromaticChain_finSix_of_consecutive emb045678
        (hone.mono (by simp))
      · simpa [emb045678] using h045
      · simpa [emb045678] using h456
      · simpa [emb045678] using h567
      · simpa [emb045678] using h678
  | right =>
    cases h145 : χ ⟨1, 4, 5, by decide, by decide⟩ with
    | left =>
        right; left
        apply containsCupSet_univ_of_finSix
        apply isMonochromaticChain_finSix_of_consecutive emb145678
          (hone.mono (by simp))
        · simpa [emb145678] using h145
        · simpa [emb145678] using h456
        · simpa [emb145678] using h567
        · simpa [emb145678] using h678
    | right =>
      cases h245 : χ ⟨2, 4, 5, by decide, by decide⟩ with
      | left =>
          right; left
          apply containsCupSet_univ_of_finSix
          apply isMonochromaticChain_finSix_of_consecutive emb245678
            (hone.mono (by simp))
          · simpa [emb245678] using h245
          · simpa [emb245678] using h456
          · simpa [emb245678] using h567
          · simpa [emb245678] using h678
      | right =>
        cases h345 : χ ⟨3, 4, 5, by decide, by decide⟩ with
        | left =>
            right; left
            apply containsCupSet_univ_of_finSix
            apply isMonochromaticChain_finSix_of_consecutive emb345678
              (hone.mono (by simp))
            · simpa [emb345678] using h345
            · simpa [emb345678] using h456
            · simpa [emb345678] using h567
            · simpa [emb345678] using h678
        | right =>
          cases h234 : χ ⟨2, 3, 4, by decide, by decide⟩ with
          | right =>
              left
              apply containsCapSet_univ_of_finFour
              apply isMonochromaticChain_finFour_of_outer_eq emb2345Nine
                (hone.mono (by simp))
              · simpa [emb2345Nine] using h234
              · simpa [emb2345Nine] using h345
          | left =>
            cases h235 : χ ⟨2, 3, 5, by decide, by decide⟩ with
            | left =>
                right; right
                apply containsStrongPolygonSet_univ_of_finSix
                apply strong012345_of_overlapping_cups χ
                · apply isMonochromaticChain_finFive_of_consecutive emb01234Nine
                    (hone.mono (by simp))
                  · simpa [emb01234Nine] using h012
                  · simpa [emb01234Nine] using h123
                  · simpa [emb01234Nine] using h234
                · apply isMonochromaticChain_finFive_of_consecutive emb01235Nine
                    (hone.mono (by simp))
                  · simpa [emb01235Nine] using h012
                  · simpa [emb01235Nine] using h123
                  · simpa [emb01235Nine] using h235
                · exact h045
                · exact h145
                · exact h245
                · exact h345
            | right =>
              cases h356 : χ ⟨3, 5, 6, by decide, by decide⟩ with
              | right =>
                  left
                  apply containsCapSet_univ_of_finFour
                  apply isMonochromaticChain_finFour_of_outer_eq emb2356Nine
                    (hone.mono (by simp))
                  · simpa [emb2356Nine] using h235
                  · simpa [emb2356Nine] using h356
              | left =>
                cases h348 : χ ⟨3, 4, 8, by decide, by decide⟩ with
                | left =>
                    right; left
                    apply containsCupSet_univ_of_finSix
                    apply isMonochromaticChain_finSix_of_consecutive emb012348
                      (hone.mono (by simp))
                    · simpa [emb012348] using h012
                    · simpa [emb012348] using h123
                    · simpa [emb012348] using h234
                    · simpa [emb012348] using h348
                | right =>
                  have hallow3468 := hone (i := (3 : Fin 9)) (j := 4) (k := 6) (l := 8)
                    (by decide) (by decide) (by decide)
                    (by simp) (by simp) (by simp) (by simp)
                  have h346 : χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right := by
                    have heq := hallow3468.first_eq_second_of_second_ne_fourth
                      (by simp [h348, h468])
                    exact heq.trans h348
                  have hallow3478 := hone (i := (3 : Fin 9)) (j := 4) (k := 7) (l := 8)
                    (by decide) (by decide) (by decide)
                    (by simp) (by simp) (by simp) (by simp)
                  have h347 : χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.right := by
                    have heq := hallow3478.first_eq_second_of_second_ne_fourth
                      (by simp [h348, h478])
                    exact heq.trans h348
                  right; right
                  apply containsStrongPolygonSet_univ_of_finSix
                  apply strong345678_of_overlapping_cups χ
                  · apply isMonochromaticChain_finFive_of_consecutive emb45678Nine
                      (hone.mono (by simp))
                    · simpa [emb45678Nine] using h456
                    · simpa [emb45678Nine] using h567
                    · simpa [emb45678Nine] using h678
                  · apply isMonochromaticChain_finFive_of_consecutive emb35678Nine
                      (hone.mono (by simp))
                    · simpa [emb35678Nine] using h356
                    · simpa [emb35678Nine] using h567
                    · simpa [emb35678Nine] using h678
                  · exact h345
                  · exact h346
                  · exact h347
                  · exact h348

/-- The reversed normalized `5+4` cup-block gate. -/
theorem cupBlocks54_finNine
    (χ : TripleColoring 9)
    (hleft : IsCupSet χ {0, 1, 2, 3, 4})
    (hright : IsCupSet χ {5, 6, 7, 8})
    (hone : OneChangeOn χ Finset.univ) :
    ContainsCapSet χ Finset.univ 4 ∨
      ContainsCupSet χ Finset.univ 6 ∨
      ContainsStrongPolygonSet χ Finset.univ 6 := by
  let ψ := reverseColor χ
  have hrevFirst : ∀ i : Fin 9,
      i ∈ ({0, 1, 2, 3} : Finset (Fin 9)) →
        i.rev ∈ ({5, 6, 7, 8} : Finset (Fin 9)) := by
    intro i hi
    fin_cases i <;> simp_all
  have hrevLast : ∀ i : Fin 9,
      i ∈ ({4, 5, 6, 7, 8} : Finset (Fin 9)) →
        i.rev ∈ ({0, 1, 2, 3, 4} : Finset (Fin 9)) := by
    intro i hi
    fin_cases i <;> simp_all
  have hψLeft : IsCupSet ψ {0, 1, 2, 3} := by
    intro t hi hj hk
    exact hright (reverseOrderedTriple t)
      (hrevFirst t.k hk) (hrevFirst t.j hj) (hrevFirst t.i hi)
  have hψRight : IsCupSet ψ {4, 5, 6, 7, 8} := by
    intro t hi hj hk
    exact hleft (reverseOrderedTriple t)
      (hrevLast t.k hk) (hrevLast t.j hj) (hrevLast t.i hi)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    have horig := hone (i := l.rev) (j := k.rev) (k := j.rev) (l := i.rev)
      (by simpa using hkl) (by simpa using hjk) (by simpa using hij)
      (by simp) (by simp) (by simp) (by simp)
    simpa [ψ, reverseColor, reverseOrderedTriple] using horig.reversed
  rcases cupBlocks45_finNine ψ hψLeft hψRight hψOne with hcap | hcup | hstrong
  · exact Or.inl (containsCapSet_of_reverseColor hcap)
  · exact Or.inr (Or.inl (containsCupSet_of_reverseColor hcup))
  · exact Or.inr (Or.inr (containsStrongPolygonSet_of_reverseColor hstrong))

/-- Transport of the normalized `4+5` theorem to arbitrary ordered blocks. -/
theorem cupBlocks45Force466_four_five {n : ℕ} {χ : TripleColoring n}
    {left right : Finset (Fin n)} (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleftCard : left.card = 4) (hrightCard : right.card = 5)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right)) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsCupSet χ (left ∪ right) 6 ∨
      ContainsStrongPolygonSet χ (left ∪ right) 6 := by
  let le : Fin 4 ↪o Fin n := left.orderEmbOfFin hleftCard
  let re : Fin 5 ↪o Fin n := right.orderEmbOfFin hrightCard
  let f : Fin 9 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![le 0, le 1, le 2, le 3, re 0, re 1, re 2, re 3, re 4] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact re.strictMono (by decide)
        | exact horder _ (left.orderEmbOfFin_mem hleftCard _)
            _ (right.orderEmbOfFin_mem hrightCard _))
  let ψ : TripleColoring 9 := χ.restrict f
  have hfmem : ∀ i : Fin 9, f i ∈ left ∪ right := by
    intro i
    fin_cases i <;>
      simp [f, le, re, left.orderEmbOfFin_mem hleftCard,
        right.orderEmbOfFin_mem hrightCard]
  have hfirst : ∀ i : Fin 9,
      i ∈ ({0, 1, 2, 3} : Finset (Fin 9)) → f i ∈ left := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact left.orderEmbOfFin_mem hleftCard _
  have hlast : ∀ i : Fin 9,
      i ∈ ({4, 5, 6, 7, 8} : Finset (Fin 9)) → f i ∈ right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      exact right.orderEmbOfFin_mem hrightCard _
  have hψLeft : IsCupSet ψ {0, 1, 2, 3} := by
    intro t hi hj hk
    exact hleft (t.map f) (hfirst t.i hi) (hfirst t.j hj) (hfirst t.k hk)
  have hψRight : IsCupSet ψ {4, 5, 6, 7, 8} := by
    intro t hi hj hk
    exact hright (t.map f) (hlast t.i hi) (hlast t.j hj) (hlast t.k hk)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
      (hfmem i) (hfmem j) (hfmem k) (hfmem l)
  have hout := cupBlocks45_finNine ψ hψLeft hψRight hψOne
  have himage : Finset.univ.image f = left ∪ right := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfmem i
    · have himageCard : (Finset.univ.image f).card = 9 := by
        simpa using Finset.card_image_of_injective Finset.univ f.injective
      rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard,
        himageCard]
  rcases hout with hcap | hcup | hstrong
  · left
    simpa [himage] using containsCapSet_map_restrict f hcap
  · right
    left
    simpa [himage] using containsCupSet_map_restrict f hcup
  · right
    right
    simpa [himage] using containsStrongPolygonSet_map_restrict f hstrong

/-- Transport of the reversed normalized `5+4` theorem to arbitrary ordered
blocks. -/
theorem cupBlocks45Force466_five_four {n : ℕ} {χ : TripleColoring n}
    {left right : Finset (Fin n)} (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleftCard : left.card = 5) (hrightCard : right.card = 4)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right)) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsCupSet χ (left ∪ right) 6 ∨
      ContainsStrongPolygonSet χ (left ∪ right) 6 := by
  let le : Fin 5 ↪o Fin n := left.orderEmbOfFin hleftCard
  let re : Fin 4 ↪o Fin n := right.orderEmbOfFin hrightCard
  let f : Fin 9 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![le 0, le 1, le 2, le 3, le 4, re 0, re 1, re 2, re 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact re.strictMono (by decide)
        | exact horder _ (left.orderEmbOfFin_mem hleftCard _)
            _ (right.orderEmbOfFin_mem hrightCard _))
  let ψ : TripleColoring 9 := χ.restrict f
  have hfmem : ∀ i : Fin 9, f i ∈ left ∪ right := by
    intro i
    fin_cases i <;>
      simp [f, le, re, left.orderEmbOfFin_mem hleftCard,
        right.orderEmbOfFin_mem hrightCard]
  have hfirst : ∀ i : Fin 9,
      i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 9)) → f i ∈ left := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      exact left.orderEmbOfFin_mem hleftCard _
  have hlast : ∀ i : Fin 9,
      i ∈ ({5, 6, 7, 8} : Finset (Fin 9)) → f i ∈ right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact right.orderEmbOfFin_mem hrightCard _
  have hψLeft : IsCupSet ψ {0, 1, 2, 3, 4} := by
    intro t hi hj hk
    exact hleft (t.map f) (hfirst t.i hi) (hfirst t.j hj) (hfirst t.k hk)
  have hψRight : IsCupSet ψ {5, 6, 7, 8} := by
    intro t hi hj hk
    exact hright (t.map f) (hlast t.i hi) (hlast t.j hj) (hlast t.k hk)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
      (hfmem i) (hfmem j) (hfmem k) (hfmem l)
  have hout := cupBlocks54_finNine ψ hψLeft hψRight hψOne
  have himage : Finset.univ.image f = left ∪ right := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfmem i
    · have himageCard : (Finset.univ.image f).card = 9 := by
        simpa using Finset.card_image_of_injective Finset.univ f.injective
      rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard,
        himageCard]
  rcases hout with hcap | hcup | hstrong
  · left
    simpa [himage] using containsCapSet_map_restrict f hcap
  · right
    left
    simpa [himage] using containsCupSet_map_restrict f hcup
  · right
    right
    simpa [himage] using containsStrongPolygonSet_map_restrict f hstrong

/-- The normalized symbolic proof, reversal, and order-embedding transport
close the arbitrary `4+5`/`5+4` cup-block gate. -/
theorem cupBlocks45Force466 : CupBlocks45Force466 := by
  intro n χ left right hdisjoint horder hcards hleft hright hone
  rcases hcards with ⟨hleftCard, hrightCard⟩ | ⟨hleftCard, hrightCard⟩
  · exact cupBlocks45Force466_four_five hdisjoint horder hleftCard hrightCard
      hleft hright hone
  · exact cupBlocks45Force466_five_four hdisjoint horder hleftCard hrightCard
      hleft hright hone

/-- Two ordered cup blocks avoiding all `(4,6,6)` outcomes have total
cardinality at most eight. -/
theorem cup_block_card_add_le_eight {n : ℕ} {χ : TripleColoring n}
    {left right : Finset (Fin n)} (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoCap : ¬ContainsCapSet χ (left ∪ right) 4)
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) 6) :
    left.card + right.card ≤ 8 :=
  cup_block_card_add_le_eight_of_cupBlocks45 cupBlocks45Force466
    hdisjoint horder hleft hright hone hnoCap hnoCup hnoStrong

end ErdosSzekeres

end
