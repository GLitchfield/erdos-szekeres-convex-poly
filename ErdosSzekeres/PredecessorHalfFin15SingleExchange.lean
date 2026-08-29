module

public import ErdosSzekeres.PredecessorHalfFin15Obstruction

@[expose] public section

/-!
# The single-exchange branch at fifteen points

This file isolates the exact obstruction created by replacing one point in a
maximum seven-point predecessor-free support with two exterior points.  It
does not weaken the frozen single-exchange endpoint: the lemmas below expose
the witnesses which a proof of that endpoint must make incompatible.
-/

namespace ErdosSzekeres

/-- A maximum seven-point predecessor-free support rules out the desired
half-support conclusion.  Consequently, the frozen single-exchange endpoint
must derive a contradiction from its overlap and strong-extension data; it
cannot obtain the conclusion by reusing maximality alone. -/
theorem fin15_no_half_of_maximum_support_card_seven
    (chi : TripleColoring 15) {support : Finset (Fin 15)}
    (hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (hsupportCard : support.card = 7) :
    ¬∃ half : Finset (Fin 15),
      ¬ContainsStrongPolygonSet chi half 5 ∧ 15 ≤ 2 * half.card := by
  rintro ⟨half, hhalfFree, hhalfCard⟩
  have hle := hmaximum.2 half hhalfFree
  omega

/-- Removing one support point and adjoining two distinct exterior points
produces an eight-point set. -/
theorem fin15_singleExchange_candidate_card
    {support : Finset (Fin 15)} {q r c : Fin 15}
    (hsupportCard : support.card = 7)
    (hqOutside : q ∈ Finset.univ \ support)
    (hrOutside : r ∈ Finset.univ \ support)
    (hqr : q ≠ r) (hc : c ∈ support) :
    (insert q (insert r (support.erase c))).card = 8 := by
  have hqNotSupport : q ∉ support := (Finset.mem_sdiff.mp hqOutside).2
  have hrNotSupport : r ∉ support := (Finset.mem_sdiff.mp hrOutside).2
  have hqNotErase : q ∉ support.erase c := fun hq ↦
    hqNotSupport (Finset.mem_erase.mp hq).2
  have hrNotErase : r ∉ support.erase c := fun hr ↦
    hrNotSupport (Finset.mem_erase.mp hr).2
  have hqNotInsert : q ∉ insert r (support.erase c) := by
    simp [hqr, hqNotErase]
  rw [Finset.card_insert_of_notMem hqNotInsert,
    Finset.card_insert_of_notMem hrNotErase,
    Finset.card_erase_of_mem hc, hsupportCard]

/-- Maximality forces a strong five-set in every single-exchange candidate,
and support-freeness forces that witness to use at least one exterior point. -/
theorem fin15_singleExchange_candidate_has_exterior_witness
    (chi : TripleColoring 15)
    {support : Finset (Fin 15)} {q r c : Fin 15}
    (hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (hsupportCard : support.card = 7)
    (hqOutside : q ∈ Finset.univ \ support)
    (hrOutside : r ∈ Finset.univ \ support)
    (hqr : q ≠ r) (hc : c ∈ support) :
    ∃ polygon : Finset (Fin 15),
      polygon ⊆ insert q (insert r (support.erase c)) ∧
        polygon.card = 5 ∧ IsStrongPolygonSet chi polygon ∧
          (q ∈ polygon ∨ r ∈ polygon) := by
  let candidate := insert q (insert r (support.erase c))
  have hcandidateCard : candidate.card = 8 := by
    exact fin15_singleExchange_candidate_card hsupportCard hqOutside
      hrOutside hqr hc
  have hcontains : ContainsStrongPolygonSet chi candidate 5 := by
    by_contra hfree
    have hle := hmaximum.2 candidate hfree
    omega
  obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hcontains
  refine ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong, ?_⟩
  by_contra hneither
  push Not at hneither
  apply hmaximum.1
  refine ⟨polygon, ?_, hpolygonCard, hpolygonStrong⟩
  intro x hx
  have hxCandidate := hpolygonSub hx
  simp only [candidate, Finset.mem_insert] at hxCandidate
  rcases hxCandidate with rfl | rfl | hxSupport
  · exact (hneither.1 hx).elim
  · exact (hneither.2 hx).elim
  · exact (Finset.mem_erase.mp hxSupport).2

/-- Every forced witness has one of three exact forms: it uses both exterior
points and three surviving support points, or it uses exactly one exterior
point and four surviving support points. -/
theorem fin15_singleExchange_candidate_anchor_trichotomy
    (chi : TripleColoring 15)
    {support : Finset (Fin 15)} {q r c : Fin 15}
    (hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (hsupportCard : support.card = 7)
    (hqOutside : q ∈ Finset.univ \ support)
    (hrOutside : r ∈ Finset.univ \ support)
    (hqr : q ≠ r) (hc : c ∈ support) :
    (∃ residue : Finset (Fin 15),
      residue ⊆ support.erase c ∧ residue.card = 3 ∧
        IsStrongPolygonSet chi (insert q (insert r residue))) ∨
    (∃ anchor : Finset (Fin 15),
      anchor ⊆ support.erase c ∧ anchor.card = 4 ∧
        IsStrongPolygonSet chi (insert q anchor)) ∨
    ∃ anchor : Finset (Fin 15),
      anchor ⊆ support.erase c ∧ anchor.card = 4 ∧
        IsStrongPolygonSet chi (insert r anchor) := by
  obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong, hexterior⟩ :=
    fin15_singleExchange_candidate_has_exterior_witness chi hmaximum
      hsupportCard hqOutside hrOutside hqr hc
  by_cases hqPolygon : q ∈ polygon
  · by_cases hrPolygon : r ∈ polygon
    · apply Or.inl
      let residue := (polygon.erase q).erase r
      have hrEraseQ : r ∈ polygon.erase q := by
        exact Finset.mem_erase.mpr ⟨hqr.symm, hrPolygon⟩
      have hresidueSub : residue ⊆ support.erase c := by
        intro x hx
        have hxData := Finset.mem_erase.mp hx
        have hxEraseQ := Finset.mem_erase.mp hxData.2
        have hxCandidate := hpolygonSub hxEraseQ.2
        simp only [Finset.mem_insert] at hxCandidate
        rcases hxCandidate with hxq | hxr | hxSupport
        · exact (hxEraseQ.1 hxq).elim
        · exact (hxData.1 hxr).elim
        · exact hxSupport
      have hresidueCard : residue.card = 3 := by
        simp only [residue]
        rw [Finset.card_erase_of_mem hrEraseQ,
          Finset.card_erase_of_mem hqPolygon, hpolygonCard]
      have hinsertResidue : insert q (insert r residue) = polygon := by
        simp only [residue]
        rw [Finset.insert_erase hrEraseQ, Finset.insert_erase hqPolygon]
      exact ⟨residue, hresidueSub, hresidueCard,
        hinsertResidue.symm ▸ hpolygonStrong⟩
    · apply Or.inr
      apply Or.inl
      let anchor := polygon.erase q
      have hanchorSub : anchor ⊆ support.erase c := by
        intro x hx
        have hxData := Finset.mem_erase.mp hx
        have hxCandidate := hpolygonSub hxData.2
        simp only [Finset.mem_insert] at hxCandidate
        rcases hxCandidate with hxq | hxr | hxSupport
        · exact (hxData.1 hxq).elim
        · subst x
          exact (hrPolygon hxData.2).elim
        · exact hxSupport
      have hanchorCard : anchor.card = 4 := by
        simp only [anchor]
        rw [Finset.card_erase_of_mem hqPolygon, hpolygonCard]
      have hinsertAnchor : insert q anchor = polygon := by
        exact Finset.insert_erase hqPolygon
      exact ⟨anchor, hanchorSub, hanchorCard,
        hinsertAnchor.symm ▸ hpolygonStrong⟩
  · have hrPolygon : r ∈ polygon := hexterior.resolve_left hqPolygon
    apply Or.inr
    apply Or.inr
    let anchor := polygon.erase r
    have hanchorSub : anchor ⊆ support.erase c := by
      intro x hx
      have hxData := Finset.mem_erase.mp hx
      have hxCandidate := hpolygonSub hxData.2
      simp only [Finset.mem_insert] at hxCandidate
      rcases hxCandidate with hxq | hxr | hxSupport
      · subst x
        exact (hqPolygon hxData.2).elim
      · exact (hxData.1 hxr).elim
      · exact hxSupport
    have hanchorCard : anchor.card = 4 := by
      simp only [anchor]
      rw [Finset.card_erase_of_mem hrPolygon, hpolygonCard]
    have hinsertAnchor : insert r anchor = polygon := by
      exact Finset.insert_erase hrPolygon
    exact ⟨anchor, hanchorSub, hanchorCard,
      hinsertAnchor.symm ▸ hpolygonStrong⟩

/-- Every one of the three common blocker points produces the exact witness
trichotomy above. -/
theorem fin15_singleExchange_common_point_anchor_trichotomy
    (chi : TripleColoring 15)
    {support a b : Finset (Fin 15)} {q r c : Fin 15}
    (hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (hsupportCard : support.card = 7)
    (hqOutside : q ∈ Finset.univ \ support)
    (hrOutside : r ∈ Finset.univ \ support)
    (hqr : q ≠ r) (haSub : a ⊆ support) (hc : c ∈ a ∩ b) :
    (∃ residue : Finset (Fin 15),
      residue ⊆ support.erase c ∧ residue.card = 3 ∧
        IsStrongPolygonSet chi (insert q (insert r residue))) ∨
    (∃ anchor : Finset (Fin 15),
      anchor ⊆ support.erase c ∧ anchor.card = 4 ∧
        IsStrongPolygonSet chi (insert q anchor)) ∨
    ∃ anchor : Finset (Fin 15),
      anchor ⊆ support.erase c ∧ anchor.card = 4 ∧
        IsStrongPolygonSet chi (insert r anchor) := by
  exact fin15_singleExchange_candidate_anchor_trichotomy chi hmaximum
    hsupportCard hqOutside hrOutside hqr (haSub (Finset.mem_inter.mp hc).1)

end ErdosSzekeres

end
