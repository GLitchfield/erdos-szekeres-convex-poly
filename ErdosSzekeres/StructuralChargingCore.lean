module

public import ErdosSzekeres.StructuralCharging

@[expose] public section

/-!
# The seven-vertex structural charging core

This file proves the normalized `3+4` cup-block lemma selected by the
structural-charging route review.  The proof is a seven-branch symbolic
argument from the rank-three one-change law; it does not enumerate colorings
or import a generated certificate.
-/

namespace ErdosSzekeres

theorem TurnSequenceAllowed.all_eq_of_outer_eq {a b c d : Turn}
    (h : TurnSequenceAllowed a b c d) (had : a = d) :
    a = b ∧ b = c ∧ c = d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [TurnSequenceAllowed]

theorem TurnSequenceAllowed.third_eq_fourth_of_first_ne_third
    {a b c d : Turn} (h : TurnSequenceAllowed a b c d) (hac : a ≠ c) :
    c = d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [TurnSequenceAllowed]

theorem TurnSequenceAllowed.first_eq_second_of_second_ne_fourth
    {a b c d : Turn} (h : TurnSequenceAllowed a b c d) (hbd : b ≠ d) :
    a = b := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [TurnSequenceAllowed]

/-- Once the first two colors differ, the one-change law forces both
remaining colors to equal the second. -/
theorem TurnSequenceAllowed.tail_eq_of_first_ne_second {a b c d : Turn}
    (h : TurnSequenceAllowed a b c d) (hab : a ≠ b) :
    b = c ∧ c = d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [TurnSequenceAllowed]

/-- If the color through a fixed ordered pair changes between two later
vertices, both turns through that later pair equal the new probe color. -/
theorem OneChangeOn.probe_transition_forces_pair_colors
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) {p q y z : Fin n}
    (hpq : p < q) (hqy : q < y) (hyz : y < z)
    (hp : p ∈ s) (hq : q ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    (hne : χ ⟨p, q, y, hpq, hqy⟩ ≠
      χ ⟨p, q, z, hpq, hqy.trans hyz⟩) :
    χ ⟨p, y, z, hpq.trans hqy, hyz⟩ =
        χ ⟨p, q, z, hpq, hqy.trans hyz⟩ ∧
      χ ⟨q, y, z, hqy, hyz⟩ =
        χ ⟨p, q, z, hpq, hqy.trans hyz⟩ := by
  have htail :=
    (hone hpq hqy hyz hp hq hy hz).tail_eq_of_first_ne_second hne
  exact ⟨htail.1.symm, htail.2.symm.trans htail.1.symm⟩

def emb01234 : Fin 5 ↪o Fin 7 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 4] (by decide)

def emb23456 : Fin 5 ↪o Fin 7 :=
  OrderEmbedding.ofStrictMono ![2, 3, 4, 5, 6] (by decide)

def emb01356 : Fin 5 ↪o Fin 7 :=
  OrderEmbedding.ofStrictMono ![0, 1, 3, 5, 6] (by decide)

def emb03456 : Fin 5 ↪o Fin 7 :=
  OrderEmbedding.ofStrictMono ![0, 3, 4, 5, 6] (by decide)

def emb01236 : Fin 5 ↪o Fin 7 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3, 6] (by decide)

def emb1234 : Fin 4 ↪o Fin 7 :=
  OrderEmbedding.ofStrictMono ![1, 2, 3, 4] (by decide)

def emb1245 : Fin 4 ↪o Fin 7 :=
  OrderEmbedding.ofStrictMono ![1, 2, 4, 5] (by decide)

theorem OneChangeOn.mono {n : ℕ} {χ : TripleColoring n}
    {s t : Finset (Fin n)} (h : OneChangeOn χ s) (hts : t ⊆ s) :
    OneChangeOn χ t := by
  intro i j k l hij hjk hkl hi hj hk hl
  exact h hij hjk hkl (hts hi) (hts hj) (hts hk) (hts hl)

theorem isMonochromaticChain_finFive_of_consecutive
    {n : ℕ} {χ : TripleColoring n} {c : Turn} (f : Fin 5 ↪o Fin n)
    (hone : OneChangeOn χ (Finset.univ.image f))
    (h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = c)
    (h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = c)
    (h234 : χ ⟨f 2, f 3, f 4, by simp, by simp⟩ = c) :
    IsMonochromaticChain χ c f := by
  have hallow0123 := hone (i := f 0) (j := f 1) (k := f 2) (l := f 3)
    (f.strictMono (by decide)) (f.strictMono (by decide))
    (f.strictMono (by decide)) (by simp) (by simp) (by simp) (by simp)
  have houter0123 :
      χ ⟨f 0, f 1, f 2, by simp, by simp⟩ =
        χ ⟨f 1, f 2, f 3, by simp, by simp⟩ := h012.trans h123.symm
  have heq0123 := hallow0123.all_eq_of_outer_eq houter0123
  have h013 : χ ⟨f 0, f 1, f 3, by simp, by simp⟩ = c :=
    heq0123.1.symm.trans h012
  have h023 : χ ⟨f 0, f 2, f 3, by simp, by simp⟩ = c :=
    heq0123.2.1.symm.trans h013
  have hallow1234 := hone (i := f 1) (j := f 2) (k := f 3) (l := f 4)
    (f.strictMono (by decide)) (f.strictMono (by decide))
    (f.strictMono (by decide)) (by simp) (by simp) (by simp) (by simp)
  have houter1234 :
      χ ⟨f 1, f 2, f 3, by simp, by simp⟩ =
        χ ⟨f 2, f 3, f 4, by simp, by simp⟩ := h123.trans h234.symm
  have heq1234 := hallow1234.all_eq_of_outer_eq houter1234
  have h124 : χ ⟨f 1, f 2, f 4, by simp, by simp⟩ = c :=
    heq1234.1.symm.trans h123
  have h134 : χ ⟨f 1, f 3, f 4, by simp, by simp⟩ = c :=
    heq1234.2.1.symm.trans h124
  have hallow0124 := hone (i := f 0) (j := f 1) (k := f 2) (l := f 4)
    (f.strictMono (by decide)) (f.strictMono (by decide))
    (f.strictMono (by decide)) (by simp) (by simp) (by simp) (by simp)
  have houter0124 :
      χ ⟨f 0, f 1, f 2, by simp, by simp⟩ =
        χ ⟨f 1, f 2, f 4, by simp, by simp⟩ := h012.trans h124.symm
  have heq0124 := hallow0124.all_eq_of_outer_eq houter0124
  have h014 : χ ⟨f 0, f 1, f 4, by simp, by simp⟩ = c :=
    heq0124.1.symm.trans h012
  have h024 : χ ⟨f 0, f 2, f 4, by simp, by simp⟩ = c :=
    heq0124.2.1.symm.trans h014
  have hallow0234 := hone (i := f 0) (j := f 2) (k := f 3) (l := f 4)
    (f.strictMono (by decide)) (f.strictMono (by decide))
    (f.strictMono (by decide)) (by simp) (by simp) (by simp) (by simp)
  have houter0234 :
      χ ⟨f 0, f 2, f 3, by simp, by simp⟩ =
        χ ⟨f 2, f 3, f 4, by simp, by simp⟩ := h023.trans h234.symm
  have heq0234 := hallow0234.all_eq_of_outer_eq houter0234
  have h034 : χ ⟨f 0, f 3, f 4, by simp, by simp⟩ = c :=
    heq0234.2.2.trans h234
  refine ⟨f.strictMono, ?_⟩
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals (try norm_num at hij)
  all_goals (try norm_num at hjk)
  all_goals first
    | exact h012
    | exact h013
    | exact h014
    | exact h023
    | exact h024
    | exact h034
    | exact h123
    | exact h124
    | exact h134
    | exact h234

theorem isMonochromaticChain_finFour_of_outer_eq
    {n : ℕ} {χ : TripleColoring n} {c : Turn} (f : Fin 4 ↪o Fin n)
    (hone : OneChangeOn χ (Finset.univ.image f))
    (h012 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ = c)
    (h123 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ = c) :
    IsMonochromaticChain χ c f := by
  have hallow := hone (i := f 0) (j := f 1) (k := f 2) (l := f 3)
    (f.strictMono (by decide)) (f.strictMono (by decide))
    (f.strictMono (by decide)) (by simp) (by simp) (by simp) (by simp)
  have houter :
      χ ⟨f 0, f 1, f 2, by simp, by simp⟩ =
        χ ⟨f 1, f 2, f 3, by simp, by simp⟩ := h012.trans h123.symm
  have heq := hallow.all_eq_of_outer_eq houter
  have h013 : χ ⟨f 0, f 1, f 3, by simp, by simp⟩ = c :=
    heq.1.symm.trans h012
  have h023 : χ ⟨f 0, f 2, f 3, by simp, by simp⟩ = c :=
    heq.2.2.trans h123
  refine ⟨f.strictMono, ?_⟩
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals (try norm_num at hij)
  all_goals (try norm_num at hjk)
  all_goals first
    | exact h012
    | exact h013
    | exact h023
    | exact h123

theorem containsCupSet_univ_of_finFive {n : ℕ} {χ : TripleColoring n}
    {f : Fin 5 ↪o Fin n} (h : IsCup χ f) :
    ContainsCupSet χ Finset.univ 5 := by
  refine ⟨Finset.univ.image f, by simp, ?_, FinsetPolygon.IsCup.image h⟩
  simpa using Finset.card_image_of_injective Finset.univ f.injective

theorem containsCapSet_univ_of_finFour {n : ℕ} {χ : TripleColoring n}
    {f : Fin 4 ↪o Fin n} (h : IsCap χ f) :
    ContainsCapSet χ Finset.univ 4 := by
  refine ⟨Finset.univ.image f, by simp, ?_, FinsetPolygon.IsCap.image h⟩
  simpa using Finset.card_image_of_injective Finset.univ f.injective

theorem containsStrongPolygonSet_univ_of_finFive
    {n : ℕ} {χ : TripleColoring n} {f : Fin 5 ↪o Fin n}
    (h : IsStrongPolygonOn χ f) :
    ContainsStrongPolygonSet χ Finset.univ 5 := by
  refine ⟨Finset.univ.image f, by simp, ?_,
    FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image h⟩
  simpa using Finset.card_image_of_injective Finset.univ f.injective

theorem isStrongPolygonOn_finFive_of_quad_consistency
    {n : ℕ} {χ : TripleColoring n} (f : Fin 5 ↪o Fin n)
    (h012_013 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ =
      χ ⟨f 0, f 1, f 3, by simp, by simp⟩)
    (h023_123 : χ ⟨f 0, f 2, f 3, by simp, by simp⟩ =
      χ ⟨f 1, f 2, f 3, by simp, by simp⟩)
    (h012_014 : χ ⟨f 0, f 1, f 2, by simp, by simp⟩ =
      χ ⟨f 0, f 1, f 4, by simp, by simp⟩)
    (h024_124 : χ ⟨f 0, f 2, f 4, by simp, by simp⟩ =
      χ ⟨f 1, f 2, f 4, by simp, by simp⟩)
    (h013_014 : χ ⟨f 0, f 1, f 3, by simp, by simp⟩ =
      χ ⟨f 0, f 1, f 4, by simp, by simp⟩)
    (h034_134 : χ ⟨f 0, f 3, f 4, by simp, by simp⟩ =
      χ ⟨f 1, f 3, f 4, by simp, by simp⟩)
    (h023_024 : χ ⟨f 0, f 2, f 3, by simp, by simp⟩ =
      χ ⟨f 0, f 2, f 4, by simp, by simp⟩)
    (h034_234 : χ ⟨f 0, f 3, f 4, by simp, by simp⟩ =
      χ ⟨f 2, f 3, f 4, by simp, by simp⟩)
    (h123_124 : χ ⟨f 1, f 2, f 3, by simp, by simp⟩ =
      χ ⟨f 1, f 2, f 4, by simp, by simp⟩)
    (h134_234 : χ ⟨f 1, f 3, f 4, by simp, by simp⟩ =
      χ ⟨f 2, f 3, f 4, by simp, by simp⟩) :
    IsStrongPolygonOn χ f := by
  intro i j k l hij hjk hkl
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
  all_goals (try norm_num at hij)
  all_goals (try norm_num at hjk)
  all_goals (try norm_num at hkl)
  all_goals constructor
  all_goals first
    | exact h012_013
    | exact h023_123
    | exact h012_014
    | exact h024_124
    | exact h013_014
    | exact h034_134
    | exact h023_024
    | exact h034_234
    | exact h123_124
    | exact h134_234

/-- The normalized `3+4` cup-block core.  This proof branches on seven
specific turns and uses only the one-change propagation law. -/
theorem cupBlocks34_finSeven
    (χ : TripleColoring 7)
    (hleft : IsCupSet χ {0, 1, 2})
    (hright : IsCupSet χ {3, 4, 5, 6})
    (hone : OneChangeOn χ Finset.univ) :
    ContainsCapSet χ Finset.univ 4 ∨
      ContainsCupSet χ Finset.univ 5 ∨
      ContainsStrongPolygonSet χ Finset.univ 5 := by
  have h012 : χ ⟨0, 1, 2, by decide, by decide⟩ = Turn.left :=
    hleft _ (by simp) (by simp) (by simp)
  have h345 : χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left :=
    hright _ (by simp) (by simp) (by simp)
  have h346 : χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left :=
    hright _ (by simp) (by simp) (by simp)
  have h356 : χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left :=
    hright _ (by simp) (by simp) (by simp)
  have h456 : χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left :=
    hright _ (by simp) (by simp) (by simp)
  have hone23456 : OneChangeOn χ (Finset.univ.image emb23456) :=
    hone.mono (by simp)
  cases h234 : χ ⟨2, 3, 4, by decide, by decide⟩ with
  | left =>
      right
      left
      apply containsCupSet_univ_of_finFive
      apply isMonochromaticChain_finFive_of_consecutive emb23456 hone23456
      · simpa [emb23456] using h234
      · simpa [emb23456] using h345
      · simpa [emb23456] using h456
  | right =>
    cases h123 : χ ⟨1, 2, 3, by decide, by decide⟩ with
    | right =>
        left
        apply containsCapSet_univ_of_finFour
        apply isMonochromaticChain_finFour_of_outer_eq emb1234
          (hone.mono (by simp))
        · simpa [emb1234] using h123
        · simpa [emb1234] using h234
    | left =>
      have hallow0123 := hone (i := (0 : Fin 7)) (j := 1) (k := 2) (l := 3)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
      have heq0123 := hallow0123.all_eq_of_outer_eq (h012.trans h123.symm)
      have h013 : χ ⟨0, 1, 3, by decide, by decide⟩ = Turn.left :=
        heq0123.1.symm.trans h012
      have h023 : χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left :=
        heq0123.2.1.symm.trans h013
      cases h135 : χ ⟨1, 3, 5, by decide, by decide⟩ with
      | left =>
          right
          left
          apply containsCupSet_univ_of_finFive
          apply isMonochromaticChain_finFive_of_consecutive emb01356
            (hone.mono (by simp))
          · simpa [emb01356] using h013
          · simpa [emb01356] using h135
          · simpa [emb01356] using h356
      | right =>
        cases h034 : χ ⟨0, 3, 4, by decide, by decide⟩ with
        | left =>
            right
            left
            apply containsCupSet_univ_of_finFive
            apply isMonochromaticChain_finFive_of_consecutive emb03456
              (hone.mono (by simp))
            · simpa [emb03456] using h034
            · simpa [emb03456] using h345
            · simpa [emb03456] using h456
        | right =>
          cases h124 : χ ⟨1, 2, 4, by decide, by decide⟩ with
          | left =>
            have hallow0124 := hone (i := (0 : Fin 7)) (j := 1) (k := 2) (l := 4)
              (by decide) (by decide) (by decide)
              (by simp) (by simp) (by simp) (by simp)
            have heq0124 := hallow0124.all_eq_of_outer_eq (h012.trans h124.symm)
            have h014 : χ ⟨0, 1, 4, by decide, by decide⟩ = Turn.left :=
              heq0124.1.symm.trans h012
            have h024 : χ ⟨0, 2, 4, by decide, by decide⟩ = Turn.left :=
              heq0124.2.1.symm.trans h014
            have hallow1345 := hone (i := (1 : Fin 7)) (j := 3) (k := 4) (l := 5)
              (by decide) (by decide) (by decide)
              (by simp) (by simp) (by simp) (by simp)
            have h134 : χ ⟨1, 3, 4, by decide, by decide⟩ = Turn.right := by
              have heq := hallow1345.first_eq_second_of_second_ne_fourth
                (by simp [h135, h345])
              exact heq.trans h135
            right
            right
            apply containsStrongPolygonSet_univ_of_finFive
            apply isStrongPolygonOn_finFive_of_quad_consistency emb01234
            · simpa [emb01234] using h012.trans h013.symm
            · simpa [emb01234] using h023.trans h123.symm
            · simpa [emb01234] using h012.trans h014.symm
            · simpa [emb01234] using h024.trans h124.symm
            · simpa [emb01234] using h013.trans h014.symm
            · simpa [emb01234] using h034.trans h134.symm
            · simpa [emb01234] using h023.trans h024.symm
            · simpa [emb01234] using h034.trans h234.symm
            · simpa [emb01234] using h123.trans h124.symm
            · simpa [emb01234] using h134.trans h234.symm
          | right =>
            cases h245 : χ ⟨2, 4, 5, by decide, by decide⟩ with
            | right =>
                left
                apply containsCapSet_univ_of_finFour
                apply isMonochromaticChain_finFour_of_outer_eq emb1245
                  (hone.mono (by simp))
                · simpa [emb1245] using h124
                · simpa [emb1245] using h245
            | left =>
              have hallow2456 := hone (i := (2 : Fin 7)) (j := 4) (k := 5) (l := 6)
                (by decide) (by decide) (by decide)
                (by simp) (by simp) (by simp) (by simp)
              have heq2456 := hallow2456.all_eq_of_outer_eq (h245.trans h456.symm)
              have h246 : χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left :=
                heq2456.1.symm.trans h245
              have h256 : χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left :=
                heq2456.2.1.symm.trans h246
              have hallow1235 := hone (i := (1 : Fin 7)) (j := 2) (k := 3) (l := 5)
                (by decide) (by decide) (by decide)
                (by simp) (by simp) (by simp) (by simp)
              have h235 : χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
                have heq := hallow1235.third_eq_fourth_of_first_ne_third
                  (by simp [h123, h135])
                exact heq.symm.trans h135
              cases h236 : χ ⟨2, 3, 6, by decide, by decide⟩ with
              | left =>
                  right
                  left
                  apply containsCupSet_univ_of_finFive
                  apply isMonochromaticChain_finFive_of_consecutive emb01236
                    (hone.mono (by simp))
                  · simpa [emb01236] using h012
                  · simpa [emb01236] using h123
                  · simpa [emb01236] using h236
              | right =>
                  right
                  right
                  apply containsStrongPolygonSet_univ_of_finFive
                  apply isStrongPolygonOn_finFive_of_quad_consistency emb23456
                  · simpa [emb23456] using h234.trans h235.symm
                  · simpa [emb23456] using h245.trans h345.symm
                  · simpa [emb23456] using h234.trans h236.symm
                  · simpa [emb23456] using h246.trans h346.symm
                  · simpa [emb23456] using h235.trans h236.symm
                  · simpa [emb23456] using h256.trans h356.symm
                  · simpa [emb23456] using h245.trans h246.symm
                  · simpa [emb23456] using h256.trans h456.symm
                  · simpa [emb23456] using h345.trans h346.symm
                  · simpa [emb23456] using h356.trans h456.symm

end ErdosSzekeres
