import ESBlueprint.B.MarkerCupEndpointsNoCapThreeOnOneSide

namespace ErdosSzekeres

/-- Audited marker Lemma 7 at the level of eight points and their turns. Opposing cup endpoints, saturation turns, marker-forbidden bridge cups and blocked cap extensions force a four-point sequence with two changes. The contradiction is independent of endpoint-cap cardinalities.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_six_pred_pred_of_seven_le -/
theorem marker_straddle_turn_core {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {p e f r c₁ c₂ d₂ d₃ : Fin n}
(hone : OneChangeOn χ s)
(hp : p ∈ s) (he : e ∈ s) (hf : f ∈ s) (hr : r ∈ s)
(hc₁ : c₁ ∈ s) (hc₂ : c₂ ∈ s) (hd₂ : d₂ ∈ s) (hd₃ : d₃ ∈ s)
(hpe : p < e) (hef : e < f) (hfr : f < r)
(hc12 : c₁ < c₂) (hc2f : c₂ < f) (hed2 : e < d₂)
(hd23 : d₂ < d₃) (hc2d2 : c₂ < d₂)
(hD : χ ⟨e, d₂, d₃, hed2, hd23⟩ = Turn.left)
(hC : χ ⟨c₁, c₂, f, hc12, hc2f⟩ = Turn.left)
(hS1left : ∀ x ∈ s, ∀ hxe : x < e, χ ⟨x, e, d₂, hxe, hed2⟩ = Turn.right)
(hS1right : ∀ y ∈ s, ∀ hfy : f < y, χ ⟨c₂, f, y, hc2f, hfy⟩ = Turn.right)
(hS4left : ∀ hc2e : c₂ < e, χ ⟨c₁, c₂, e, hc12, hc2e⟩ = Turn.right)
(hS4right : ∀ hfd2 : f < d₂, χ ⟨f, d₂, d₃, hfd2, hd23⟩ = Turn.right)
(hS4both : ¬(χ ⟨c₁, c₂, d₂, hc12, hc2d2⟩ = Turn.left ∧
  χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ = Turn.left))
(hblockLeft : ∀ hec2 : e < c₂, χ ⟨p, e, c₂, hpe, hec2⟩ ≠ Turn.right)
(hblockRight : ∀ hd2f : d₂ < f, χ ⟨d₂, f, r, hd2f, hfr⟩ ≠ Turn.right) : False := by
  have hX (hec2 : e < c₂)
      (hcap : χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ = Turn.right) : False := by
    have hseq := hone hec2 hc2d2 hd23 he hc₂ hd₂ hd₃
    have hne : χ ⟨e, d₂, d₃, hed2, hd23⟩ ≠
        χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ := by
      rw [hD, hcap]
      decide
    have hhead := hseq.head_eq_of_third_ne_fourth hne
    have hec2d2 : χ ⟨e, c₂, d₂, hec2, hc2d2⟩ = Turn.left :=
      hhead.1.trans (hhead.2.trans hD)
    have hseq2 := hone hpe hec2 hc2d2 hp he hc₂ hd₂
    have hpcap := hS1left p hp hpe
    have hne2 : χ ⟨p, e, d₂, hpe, hed2⟩ ≠
        χ ⟨e, c₂, d₂, hec2, hc2d2⟩ := by
      rw [hpcap, hec2d2]
      decide
    have hpec2 : χ ⟨p, e, c₂, hpe, hec2⟩ = Turn.right :=
      (hseq2.first_eq_second_of_second_ne_fourth hne2).trans hpcap
    exact hblockLeft hec2 hpec2
  have hXprime (hd2f : d₂ < f)
      (hcap : χ ⟨c₁, c₂, d₂, hc12, hc2d2⟩ = Turn.right) : False := by
    have hseq := hone hc12 hc2d2 hd2f hc₁ hc₂ hd₂ hf
    have hne : χ ⟨c₁, c₂, d₂, hc12, hc2d2⟩ ≠
        χ ⟨c₁, c₂, f, hc12, hc2f⟩ := by
      rw [hcap, hC]
      decide
    have htail := hseq.tail_eq_of_first_ne_second hne
    have hc2d2f : χ ⟨c₂, d₂, f, hc2d2, hd2f⟩ = Turn.left :=
      htail.2.symm.trans (htail.1.symm.trans hC)
    have hseq2 := hone hc2d2 hd2f hfr hc₂ hd₂ hf hr
    have hrcap := hS1right r hr hfr
    have hne2 : χ ⟨c₂, d₂, f, hc2d2, hd2f⟩ ≠
        χ ⟨c₂, f, r, hc2f, hfr⟩ := by
      rw [hc2d2f, hrcap]
      decide
    have hd2fr : χ ⟨d₂, f, r, hd2f, hfr⟩ = Turn.right :=
      (hseq2.third_eq_fourth_of_first_ne_third hne2).symm.trans hrcap
    exact hblockRight hd2f hd2fr
  have hcaseLeft (hfirst : χ ⟨c₁, c₂, d₂, hc12, hc2d2⟩ = Turn.left)
      (hlast : χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ = Turn.right) : False := by
    have heNe : e ≠ c₂ := by
      intro heq
      have hcup : χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ = Turn.left := by
        simpa only [heq] using hD
      rw [hlast] at hcup
      cases hcup
    by_cases hec2 : e < c₂
    · exact hX hec2 hlast
    have hc2e : c₂ < e := by omega
    have hcap := hS1left c₂ hc₂ hc2e
    have hseq := hone hc12 hc2e hed2 hc₁ hc₂ he hd₂
    have hne : χ ⟨c₁, c₂, d₂, hc12, hc2d2⟩ ≠
        χ ⟨c₂, e, d₂, hc2e, hed2⟩ := by
      rw [hfirst, hcap]
      decide
    have hc1c2e : χ ⟨c₁, c₂, e, hc12, hc2e⟩ = Turn.left :=
      (hseq.first_eq_second_of_second_ne_fourth hne).trans hfirst
    have hwrong := hS4left hc2e
    rw [hc1c2e] at hwrong
    cases hwrong
  have hcaseRight (hfirst : χ ⟨c₁, c₂, d₂, hc12, hc2d2⟩ = Turn.right)
      (hlast : χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ = Turn.left) : False := by
    have hdNe : d₂ ≠ f := by
      intro heq
      have hfd3 : f < d₃ := by omega
      have hcup : χ ⟨c₂, f, d₃, hc2f, hfd3⟩ = Turn.left := by
        simpa only [heq] using hlast
      rw [hS1right d₃ hd₃ hfd3] at hcup
      cases hcup
    by_cases hd2f : d₂ < f
    · exact hXprime hd2f hfirst
    have hfd2 : f < d₂ := by omega
    have hcap := hS1right d₂ hd₂ hfd2
    have hseq := hone hc2f hfd2 hd23 hc₂ hf hd₂ hd₃
    have hne : χ ⟨c₂, f, d₂, hc2f, hfd2⟩ ≠
        χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ := by
      rw [hcap, hlast]
      decide
    have hfd23 : χ ⟨f, d₂, d₃, hfd2, hd23⟩ = Turn.left :=
      (hseq.third_eq_fourth_of_first_ne_third hne).symm.trans hlast
    have hwrong := hS4right hfd2
    rw [hfd23] at hwrong
    cases hwrong
  have hcaseCaps (hfirst : χ ⟨c₁, c₂, d₂, hc12, hc2d2⟩ = Turn.right)
      (hlast : χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ = Turn.right) : False := by
    have heNe : e ≠ c₂ := by
      intro heq
      have hcup : χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ = Turn.left := by
        simpa only [heq] using hD
      rw [hlast] at hcup
      cases hcup
    have hdNe : d₂ ≠ f := by
      intro heq
      have hcap : χ ⟨c₁, c₂, f, hc12, hc2f⟩ = Turn.right := by
        simpa only [heq] using hfirst
      rw [hC] at hcap
      cases hcap
    have hc2e : c₂ < e := by
      by_contra h
      have hec2 : e < c₂ := by omega
      exact hX hec2 hlast
    have hfd2 : f < d₂ := by
      by_contra h
      have hd2f : d₂ < f := by omega
      exact hXprime hd2f hfirst
    have hc1c2e := hS4left hc2e
    have hseq := hone hc12 hc2e hef hc₁ hc₂ he hf
    have hne : χ ⟨c₁, c₂, e, hc12, hc2e⟩ ≠
        χ ⟨c₁, c₂, f, hc12, hc2f⟩ := by
      rw [hc1c2e, hC]
      decide
    have htail := hseq.tail_eq_of_first_ne_second hne
    have hc2ef : χ ⟨c₂, e, f, hc2e, hef⟩ = Turn.left :=
      htail.2.symm.trans (htail.1.symm.trans hC)
    have hc2fd2 := hS1right d₂ hd₂ hfd2
    have hfd23 := hS4right hfd2
    have hseq2 := hone hef hfd2 hd23 he hf hd₂ hd₃
    have hne2 : χ ⟨e, d₂, d₃, hed2, hd23⟩ ≠
        χ ⟨f, d₂, d₃, hfd2, hd23⟩ := by
      rw [hD, hfd23]
      decide
    have hhead := hseq2.head_eq_of_third_ne_fourth hne2
    have hefd2 : χ ⟨e, f, d₂, hef, hfd2⟩ = Turn.left :=
      hhead.1.trans (hhead.2.trans hD)
    have hseq3 := hone hc2e hef hfd2 hc₂ he hf hd₂
    have hall := hseq3.all_eq_of_outer_eq (hc2ef.trans hefd2.symm)
    have hwrong := hall.2.2
    rw [hc2fd2, hefd2] at hwrong
    cases hwrong
  cases hfirst : χ ⟨c₁, c₂, d₂, hc12, hc2d2⟩ with
  | left =>
    cases hlast : χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ with
    | left => exact hS4both ⟨hfirst, hlast⟩
    | right => exact hcaseLeft hfirst hlast
  | right =>
    cases hlast : χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ with
    | left => exact hcaseRight hfirst hlast
    | right => exact hcaseCaps hfirst hlast


end ErdosSzekeres
