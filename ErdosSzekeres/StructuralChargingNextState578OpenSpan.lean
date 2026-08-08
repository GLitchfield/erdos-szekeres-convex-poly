module

public import ErdosSzekeres.StructuralChargingNextState578Threshold

@[expose] public section

/-!
# Terminal-span and lowest-split reductions at state `(5,7,8)`

The density-and-common-cut strict-span recurrence is false without the target
avoidance hypotheses.  This file instead extracts a terminal cap, bounds its
open span and outer tails, and allocates it to the lowest tree split.  The
resulting `1+3`/`2+2` alternative is the selected local reduction.  A direct
avoidance-aware strict-descent proposition remains below only as a diagnostic
sufficient condition; it is not claimed or selected as the next theorem.
-/

namespace ErdosSzekeres

/-- Vertices of `support` lying strictly between the two sweep endpoints of a
nonempty witness. -/
def openSweepSpanVertices {n : ℕ} (support witness : Finset (Fin n))
    (hwitness : witness.Nonempty) : Finset (Fin n) :=
  support.filter fun x ↦ witness.min' hwitness < x ∧
    x < witness.max' hwitness

/-- A nonempty set contained in a witness's open sweep span has a strictly
smaller sweep interval. -/
theorem finsetSweepInterval_strictlyInside_of_subset_openSweepSpan
    {n : ℕ} {support outer inner : Finset (Fin n)}
    (houter : outer.Nonempty) (hinner : inner.Nonempty)
    (hsub : inner ⊆ openSweepSpanVertices support outer houter) :
    (finsetSweepInterval inner hinner).StrictlyInside
      (finsetSweepInterval outer houter) := by
  have hminInterior := hsub (inner.min'_mem hinner)
  have hmaxInterior := hsub (inner.max'_mem hinner)
  have hminBounds := (Finset.mem_filter.mp hminInterior).2
  have hmaxBounds := (Finset.mem_filter.mp hmaxInterior).2
  change (outer.min' houter).val ≤ (inner.min' hinner).val ∧
    (inner.max' hinner).val ≤ (outer.max' houter).val ∧
    ((outer.min' houter).val < (inner.min' hinner).val ∨
      (inner.max' hinner).val < (outer.max' houter).val)
  omega

/-- Twenty-three vertices strictly between a cap's endpoints contain a
four-cap with strictly smaller sweep span. -/
theorem exists_strictlyInside_fourCap_of_openSweepSpan_card_ge_23
    {n : ℕ} {χ : TripleColoring n}
    {support cap : Finset (Fin n)}
    (hcap : cap ∈ capWitnesses χ support 4)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hinterior : 23 ≤
      (openSweepSpanVertices support cap
        (capWitness_nonempty_of_mem (by omega) hcap)).card) :
    ∃ inner, ∃ hinner : inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)) := by
  let hcapNonempty := capWitness_nonempty_of_mem (by omega) hcap
  let interior := openSweepSpanVertices support cap hcapNonempty
  obtain ⟨subset, hsubsetInterior, hsubsetCard⟩ :=
    Finset.exists_subset_card_eq hinterior
  have hinteriorSub : interior ⊆ support := by
    unfold interior openSweepSpanVertices
    exact Finset.filter_subset _ _
  have hsubsetSupport : subset ⊆ support :=
    hsubsetInterior.trans hinteriorSub
  obtain ⟨inner, hinnerSub, hinnerCard, hinnerSet⟩ :=
    hdense subset hsubsetSupport hsubsetCard
  have hinner : inner ∈ capWitnesses χ support 4 :=
    mem_capWitnesses.mpr
      ⟨hinnerSub.trans hsubsetSupport, hinnerCard, hinnerSet⟩
  let hinnerNonempty := capWitness_nonempty_of_mem (by omega) hinner
  have hinnerMinInterior : inner.min' hinnerNonempty ∈ interior :=
    hsubsetInterior (hinnerSub (inner.min'_mem hinnerNonempty))
  have hinnerMaxInterior : inner.max' hinnerNonempty ∈ interior :=
    hsubsetInterior (hinnerSub (inner.max'_mem hinnerNonempty))
  have hminBounds :=
    (Finset.mem_filter.mp hinnerMinInterior).2
  have hmaxBounds :=
    (Finset.mem_filter.mp hinnerMaxInterior).2
  refine ⟨inner, hinner, ?_⟩
  change (cap.min' hcapNonempty).val ≤
      (inner.min' hinnerNonempty).val ∧
    (inner.max' hinnerNonempty).val ≤
      (cap.max' hcapNonempty).val ∧
    ((cap.min' hcapNonempty).val <
        (inner.min' hinnerNonempty).val ∨
      (inner.max' hinnerNonempty).val <
        (cap.max' hcapNonempty).val)
  omega

/-- A four-cap with no strictly inner four-cap has at most 22 support vertices
strictly between its endpoints. -/
theorem openSweepSpanVertices_card_le_22_of_terminal_fourCap
    {n : ℕ} {χ : TripleColoring n}
    {support cap : Finset (Fin n)}
    (hcap : cap ∈ capWitnesses χ support 4)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hterminal : ¬∃ inner, ∃ hinner :
      inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap))) :
    (openSweepSpanVertices support cap
      (capWitness_nonempty_of_mem (by omega) hcap)).card ≤ 22 := by
  by_contra hnot
  have hinterior : 23 ≤
      (openSweepSpanVertices support cap
        (capWitness_nonempty_of_mem (by omega) hcap)).card := by
    omega
  exact hterminal
    (exists_strictlyInside_fourCap_of_openSweepSpan_card_ge_23
      hcap hdense hinterior)

/-- In an open state, the terminal-cap interior improves from the density-only
bound 22 to 21: it is four-cap-free by terminality and seven-cup-free by
inheritance, so the compiled `(4,7)` one-change threshold applies. -/
theorem openSweepSpanVertices_card_le_21_of_terminal_fourCap
    {n : ℕ} {χ : TripleColoring n}
    {support cap : Finset (Fin n)}
    (hsupport : IsDecomposableOn χ support)
    (hcap : cap ∈ capWitnesses χ support 4)
    (hterminal : ¬∃ inner, ∃ hinner :
      inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)))
    (hnoCup : ¬ContainsCupSet χ support 7) :
    (openSweepSpanVertices support cap
      (capWitness_nonempty_of_mem (by omega) hcap)).card ≤ 21 := by
  let hcapNonempty := capWitness_nonempty_of_mem (by omega) hcap
  let interior := openSweepSpanVertices support cap hcapNonempty
  have hinteriorSub : interior ⊆ support := by
    unfold interior openSweepSpanVertices
    exact Finset.filter_subset _ _
  have hone : OneChangeOn χ interior := by
    intro i j k l hij hjk hkl hi hj hk hl
    exact hsupport.turnSequenceAllowed hij hjk hkl
      (hinteriorSub hi) (hinteriorSub hj)
      (hinteriorSub hk) (hinteriorSub hl)
  have hnoInteriorCap : ¬ContainsCapSet χ interior 4 := by
    rintro ⟨inner, hinnerSub, hinnerCard, hinnerSet⟩
    have hinner : inner ∈ capWitnesses χ support 4 :=
      mem_capWitnesses.mpr
        ⟨hinnerSub.trans hinteriorSub, hinnerCard, hinnerSet⟩
    apply hterminal
    refine ⟨inner, hinner, ?_⟩
    exact finsetSweepInterval_strictlyInside_of_subset_openSweepSpan
      hcapNonempty (capWitness_nonempty_of_mem (by omega) hinner)
      hinnerSub
  have hnoInteriorCup : ¬ContainsCupSet χ interior 7 := fun hcup ↦
    hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hinteriorSub)
  exact card_le_twentyOne_of_oneChange_no_capFour_no_cupSeven
    hone hnoInteriorCap hnoInteriorCup

/-- At the exact 32-vertex reservoir, every terminal four-cap leaves at least
ten support vertices outside its strict endpoint span. -/
theorem ten_le_exterior_card_of_terminal_fourCap_at_32_23
    {n : ℕ} {χ : TripleColoring n}
    {support cap : Finset (Fin n)}
    (hsupportCard : support.card = 32)
    (hcap : cap ∈ capWitnesses χ support 4)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hterminal : ¬∃ inner, ∃ hinner :
      inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap))) :
    10 ≤ (support \ openSweepSpanVertices support cap
      (capWitness_nonempty_of_mem (by omega) hcap)).card := by
  have hinterior := openSweepSpanVertices_card_le_22_of_terminal_fourCap
    hcap hdense hterminal
  have hinteriorSub :
      openSweepSpanVertices support cap
        (capWitness_nonempty_of_mem (by decide) hcap) ⊆ support := by
    unfold openSweepSpanVertices
    exact Finset.filter_subset _ _
  rw [Finset.card_sdiff_of_subset hinteriorSub]
  omega

/-- A support vertex outside both a witness and its open endpoint span lies
strictly before the witness minimum or strictly after its maximum. -/
theorem outer_of_mem_exterior_sdiff_witness
    {n : ℕ} {support witness : Finset (Fin n)}
    (hwitness : witness.Nonempty) {x : Fin n}
    (hx : x ∈ (support \ openSweepSpanVertices support witness hwitness) \
      witness) :
    x < witness.min' hwitness ∨ witness.max' hwitness < x := by
  have hxExterior := (Finset.mem_sdiff.mp hx).1
  have hxSupport := (Finset.mem_sdiff.mp hxExterior).1
  have hxNotInterior := (Finset.mem_sdiff.mp hxExterior).2
  have hxNotWitness := (Finset.mem_sdiff.mp hx).2
  rcases lt_trichotomy x (witness.min' hwitness) with hbefore | heqMin | hafterMin
  · exact Or.inl hbefore
  · exact (hxNotWitness (heqMin ▸ witness.min'_mem hwitness)).elim
  rcases lt_trichotomy x (witness.max' hwitness) with hbeforeMax | heqMax | hafter
  · exfalso
    apply hxNotInterior
    exact Finset.mem_filter.mpr ⟨hxSupport, hafterMin, hbeforeMax⟩
  · exact (hxNotWitness (heqMax ▸ witness.max'_mem hwitness)).elim
  · exact Or.inr hafter

/-- At most the two witness endpoints can belong both to the witness and to
the complement of its open sweep span. -/
theorem witness_inter_exterior_card_le_two
    {n : ℕ} {support witness : Finset (Fin n)}
    (hwitness : witness.Nonempty) :
    (witness ∩
      (support \ openSweepSpanVertices support witness hwitness)).card ≤ 2 := by
  let exterior := support \ openSweepSpanVertices support witness hwitness
  have hsub : witness ∩ exterior ⊆
      {witness.min' hwitness, witness.max' hwitness} := by
    intro x hx
    have hxWitness := (Finset.mem_inter.mp hx).1
    have hxExterior := Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2
    have hminLe : witness.min' hwitness ≤ x :=
      Finset.min'_le witness x hxWitness
    have hleMax : x ≤ witness.max' hwitness :=
      Finset.le_max' witness x hxWitness
    rcases eq_or_lt_of_le hminLe with hminEq | hminLt
    · simp [hminEq]
    rcases eq_or_lt_of_le hleMax with hmaxEq | hmaxLt
    · simp [hmaxEq]
    · exfalso
      exact hxExterior.2
        (Finset.mem_filter.mpr ⟨hxExterior.1, hminLt, hmaxLt⟩)
  have hcard := Finset.card_le_card hsub
  exact hcard.trans (by
    simpa using Finset.card_insert_le
      (witness.min' hwitness)
      ({witness.max' hwitness} : Finset (Fin n)))

/-- In a 32/23 dense reservoir, deleting a terminal four-cap from the
vertices outside its open span leaves at least eight genuine outer-tail
vertices. -/
theorem eight_le_outerTail_card_of_terminal_fourCap_at_32_23
    {n : ℕ} {χ : TripleColoring n}
    {support cap : Finset (Fin n)}
    (hsupportCard : support.card = 32)
    (hcap : cap ∈ capWitnesses χ support 4)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hterminal : ¬∃ inner, ∃ hinner :
      inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap))) :
    8 ≤ ((support \ openSweepSpanVertices support cap
      (capWitness_nonempty_of_mem (by omega) hcap)) \ cap).card := by
  let hcapNonempty := capWitness_nonempty_of_mem (by omega) hcap
  let exterior := support \ openSweepSpanVertices support cap hcapNonempty
  have hexterior : 10 ≤ exterior.card := by
    exact ten_le_exterior_card_of_terminal_fourCap_at_32_23
      hsupportCard hcap hdense hterminal
  have hcapExteriorLe : (cap ∩ exterior).card ≤ 2 :=
    witness_inter_exterior_card_le_two hcapNonempty
  change 8 ≤ (exterior \ cap).card
  rw [Finset.card_sdiff]
  omega

/-- Seven-cup avoidance improves the density-only exterior reserve: at least
eleven of the 32 support vertices lie outside a terminal cap's open span. -/
theorem eleven_le_exterior_card_of_open_terminal_fourCap_at_578
    {n : ℕ} {χ : TripleColoring n}
    {support cap : Finset (Fin n)}
    (hsupport : IsDecomposableOn χ support)
    (hsupportCard : support.card = 32)
    (hcap : cap ∈ capWitnesses χ support 4)
    (hterminal : ¬∃ inner, ∃ hinner :
      inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)))
    (hnoCup : ¬ContainsCupSet χ support 7) :
    11 ≤ (support \ openSweepSpanVertices support cap
      (capWitness_nonempty_of_mem (by omega) hcap)).card := by
  have hinterior := openSweepSpanVertices_card_le_21_of_terminal_fourCap
    hsupport hcap hterminal hnoCup
  have hinteriorSub :
      openSweepSpanVertices support cap
        (capWitness_nonempty_of_mem (by decide) hcap) ⊆ support := by
    unfold openSweepSpanVertices
    exact Finset.filter_subset _ _
  rw [Finset.card_sdiff_of_subset hinteriorSub]
  omega

/-- Removing the cap endpoints leaves at least nine genuine outer-tail
vertices in an open 32-vertex terminal-cap reservoir. -/
theorem nine_le_outerTail_card_of_open_terminal_fourCap_at_578
    {n : ℕ} {χ : TripleColoring n}
    {support cap : Finset (Fin n)}
    (hsupport : IsDecomposableOn χ support)
    (hsupportCard : support.card = 32)
    (hcap : cap ∈ capWitnesses χ support 4)
    (hterminal : ¬∃ inner, ∃ hinner :
      inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)))
    (hnoCup : ¬ContainsCupSet χ support 7) :
    9 ≤ ((support \ openSweepSpanVertices support cap
      (capWitness_nonempty_of_mem (by omega) hcap)) \ cap).card := by
  let hcapNonempty := capWitness_nonempty_of_mem (by omega) hcap
  let exterior := support \ openSweepSpanVertices support cap hcapNonempty
  have hexterior : 11 ≤ exterior.card := by
    exact eleven_le_exterior_card_of_open_terminal_fourCap_at_578
      hsupport hsupportCard hcap hterminal hnoCup
  have hcapExteriorLe : (cap ∩ exterior).card ≤ 2 :=
    witness_inter_exterior_card_le_two hcapNonempty
  change 9 ≤ (exterior \ cap).card
  rw [Finset.card_sdiff]
  omega

/-- Every nonempty finite family of four-cap witnesses has a member with no
strictly inner four-cap witness. -/
theorem exists_terminal_fourCap_of_nonempty
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (hexists : ∃ cap, cap ∈ capWitnesses χ support 4) :
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ support 4,
      ¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ support 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap)) := by
  let spanWidth (cap : Finset (Fin n))
      (hcap : cap ∈ capWitnesses χ support 4) : ℕ :=
    (finsetSweepInterval cap
      (capWitness_nonempty_of_mem (by omega) hcap)).width
  let WidthOccurs (width : ℕ) : Prop :=
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ support 4,
      spanWidth cap hcap = width
  obtain ⟨cap₀, hcap₀⟩ := hexists
  have hex : ∃ width, WidthOccurs width :=
    ⟨spanWidth cap₀ hcap₀, cap₀, hcap₀, rfl⟩
  obtain ⟨cap, hcap, hwidth⟩ := Nat.find_spec hex
  refine ⟨cap, hcap, ?_⟩
  rintro ⟨inner, hinner, hinside⟩
  have hwidthLt : spanWidth inner hinner < spanWidth cap hcap := by
    apply SweepInterval.width_lt_of_strictlyInside
    · exact finsetSweepInterval_lower_le_upper
        (capWitness_nonempty_of_mem (by omega) hinner)
    · exact finsetSweepInterval_lower_le_upper
        (capWitness_nonempty_of_mem (by omega) hcap)
    · exact hinside
  have hmin : Nat.find hex ≤ spanWidth inner hinner :=
    Nat.find_min' hex ⟨inner, hinner, rfl⟩
  rw [hwidth] at hwidthLt
  omega

/-- The concrete surviving output of minimum-span selection in an open
32/23 reservoir: a terminal four-cap, at least ten vertices outside its open
span, and a realized cap-extension failure signature for every vertex outside
the cap. -/
theorem exists_terminal_fourCap_exterior_failureCharge_at_32_23
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (tree : DecompositionTree χ support)
    (hsupportCard : support.card = 32)
    (hnoCap : ¬ContainsCapSet χ support 5)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4) :
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ support 4,
      (¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ support 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap))) ∧
      10 ≤ (support \ openSweepSpanVertices support cap
        (capWitness_nonempty_of_mem (by omega) hcap)).card ∧
      ∃ charge : Fin n → CapFourFailureSignature,
        IsCapFourFailureCharge χ support cap
          (mem_capWitnesses.mp hcap).2.1 charge := by
  have hsubsetCard : 23 ≤ support.card := by omega
  obtain ⟨subset, hsubset, hcard⟩ :=
    Finset.exists_subset_card_eq hsubsetCard
  obtain ⟨cap₀, hcap₀Sub, hcap₀Card, hcap₀Set⟩ :=
    hdense subset hsubset hcard
  have hcap₀ : cap₀ ∈ capWitnesses χ support 4 :=
    mem_capWitnesses.mpr
      ⟨hcap₀Sub.trans hsubset, hcap₀Card, hcap₀Set⟩
  obtain ⟨cap, hcap, hterminal⟩ :=
    exists_terminal_fourCap_of_nonempty ⟨cap₀, hcap₀⟩
  have hexterior := ten_le_exterior_card_of_terminal_fourCap_at_32_23
    hsupportCard hcap hdense hterminal
  have hone : OneChangeOn χ support := by
    intro i j k l hij hjk hkl hi hj hk hl
    exact tree.toIsDecomposableOn.turnSequenceAllowed
      hij hjk hkl hi hj hk hl
  have hcapData := mem_capWitnesses.mp hcap
  obtain ⟨charge, hcharge⟩ := exists_capFourFailureCharge
    hcapData.1 hcapData.2.1 hcapData.2.2 hone hnoCap
  exact ⟨cap, hcap, hterminal, hexterior, charge, hcharge⟩

/-- Minimum-span selection collapses the nine generic cap-extension failure
classes to the two outer endpoint classes on at least eight vertices. -/
theorem exists_terminal_fourCap_twoTailBridge_at_32_23
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (tree : DecompositionTree χ support)
    (hsupportCard : support.card = 32)
    (hnoCap : ¬ContainsCapSet χ support 5)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4) :
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ support 4,
      (¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ support 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap))) ∧
      8 ≤ ((support \ openSweepSpanVertices support cap
        (capWitness_nonempty_of_mem (by omega) hcap)) \ cap).card ∧
      ∀ x ∈ (support \ openSweepSpanVertices support cap
          (capWitness_nonempty_of_mem (by omega) hcap)) \ cap,
        RealizesCapFourFailureSignature χ cap
            (mem_capWitnesses.mp hcap).2.1 x .before ∨
          RealizesCapFourFailureSignature χ cap
            (mem_capWitnesses.mp hcap).2.1 x .after := by
  have hsubsetCard : 23 ≤ support.card := by omega
  obtain ⟨subset, hsubset, hcard⟩ :=
    Finset.exists_subset_card_eq hsubsetCard
  obtain ⟨cap₀, hcap₀Sub, hcap₀Card, hcap₀Set⟩ :=
    hdense subset hsubset hcard
  have hcap₀ : cap₀ ∈ capWitnesses χ support 4 :=
    mem_capWitnesses.mpr
      ⟨hcap₀Sub.trans hsubset, hcap₀Card, hcap₀Set⟩
  obtain ⟨cap, hcap, hterminal⟩ :=
    exists_terminal_fourCap_of_nonempty ⟨cap₀, hcap₀⟩
  have htail := eight_le_outerTail_card_of_terminal_fourCap_at_32_23
    hsupportCard hcap hdense hterminal
  have hone : OneChangeOn χ support := by
    intro i j k l hij hjk hkl hi hj hk hl
    exact tree.toIsDecomposableOn.turnSequenceAllowed
      hij hjk hkl hi hj hk hl
  have hcapData := mem_capWitnesses.mp hcap
  let hcapNonempty := capWitness_nonempty_of_mem (by omega) hcap
  refine ⟨cap, hcap, hterminal, htail, ?_⟩
  intro x hx
  rcases outer_of_mem_exterior_sdiff_witness hcapNonempty hx with
    hbefore | hafter
  · have horder : ∀ y ∈ cap, x < y := by
      intro y hy
      exact hbefore.trans_le (Finset.min'_le cap y hy)
    refine Or.inl ⟨horder _
      (cap.orderEmbOfFin_mem hcapData.2.1 0), ?_⟩
    exact capFour_forces_left_bridge_before_of_no_capFive
      hcapData.1 hcapData.2.1 hcapData.2.2
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
      horder hone hnoCap
  · have horder : ∀ y ∈ cap, y < x := by
      intro y hy
      exact (Finset.le_max' cap y hy).trans_lt hafter
    refine Or.inr ⟨horder _
      (cap.orderEmbOfFin_mem hcapData.2.1 3), ?_⟩
    exact capFour_forces_left_bridge_after_of_no_capFive
      hcapData.1 hcapData.2.1 hcapData.2.2
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
      horder hone hnoCap

/-- In the actual open singleton-lower state, minimum-span selection produces
a straddling cap with at least nine genuine outer-tail vertices, each carrying
one of only the two endpoint bridge failures. -/
theorem exists_terminal_straddling_fourCap_nineTailBridge_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hupperCard : upper.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8) :
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ upper 4,
      (¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ upper 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap))) ∧
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)).StraddlesCut q.val ∧
      9 ≤ ((upper \ openSweepSpanVertices upper cap
        (capWitness_nonempty_of_mem (by omega) hcap)) \ cap).card ∧
      ∀ x ∈ (upper \ openSweepSpanVertices upper cap
          (capWitness_nonempty_of_mem (by omega) hcap)) \ cap,
        RealizesCapFourFailureSignature χ cap
            (mem_capWitnesses.mp hcap).2.1 x .before ∨
          RealizesCapFourFailureSignature χ cap
            (mem_capWitnesses.mp hcap).2.1 x .after := by
  obtain ⟨tree⟩ := DecompositionTree.exists_of_isDecomposableOn hupper
  have hreservoir := dense_straddling_cap_reservoir_at_578
    hupper hroot hnoCap hnoCup hnoStrong
  have hnoCapUpper : ¬ContainsCapSet χ upper 5 := fun hcap ↦
    hnoCap (FinsetPolygon.ContainsCapSet.mono hcap
      Finset.subset_union_right)
  have hnoCupUpper : ¬ContainsCupSet χ upper 7 := fun hcup ↦
    hnoCup (FinsetPolygon.ContainsCupSet.mono hcup
      Finset.subset_union_right)
  obtain ⟨cap, hcap, hterminal, _htailEight, hbridge⟩ :=
    exists_terminal_fourCap_twoTailBridge_at_32_23
      tree hupperCard hnoCapUpper hreservoir.1
  have htailNine := nine_le_outerTail_card_of_open_terminal_fourCap_at_578
    hupper hupperCard hcap hterminal hnoCupUpper
  exact ⟨cap, hcap, hterminal, hreservoir.2 cap hcap,
    htailNine, hbridge⟩

/-- Exact terminal-cap reduction for a hypothetical open singleton-lower
`(5,7,8)` state.  The chosen cap straddles the omitted root cut, has at least
ten upper vertices outside its open span, and every outside-cap vertex carries
one of the nine compiled consecutive extension-failure signatures. -/
theorem exists_terminal_straddling_fourCap_exterior_failureCharge_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hupperCard : upper.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8) :
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ upper 4,
      (¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ upper 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap))) ∧
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)).StraddlesCut q.val ∧
      10 ≤ (upper \ openSweepSpanVertices upper cap
        (capWitness_nonempty_of_mem (by omega) hcap)).card ∧
      ∃ charge : Fin n → CapFourFailureSignature,
        IsCapFourFailureCharge χ upper cap
          (mem_capWitnesses.mp hcap).2.1 charge := by
  obtain ⟨tree⟩ := DecompositionTree.exists_of_isDecomposableOn hupper
  have hreservoir := dense_straddling_cap_reservoir_at_578
    hupper hroot hnoCap hnoCup hnoStrong
  have hnoCapUpper : ¬ContainsCapSet χ upper 5 := fun hcap ↦
    hnoCap (FinsetPolygon.ContainsCapSet.mono hcap
      Finset.subset_union_right)
  obtain ⟨cap, hcap, hterminal, hexterior, charge, hcharge⟩ :=
    exists_terminal_fourCap_exterior_failureCharge_at_32_23
      tree hupperCard hnoCapUpper hreservoir.1
  exact ⟨cap, hcap, hterminal, hreservoir.2 cap hcap,
    hexterior, charge, hcharge⟩

/-- At the lowest tree split separating any four-cap, the cap has child
profile `1+3` or `2+2`.  Strong-eight avoidance then forbids respectively a
five-cup or six-cup in the lower child.  This is the tree-local alternative
that survives the failure of global strict span descent. -/
theorem fourCap_lowestSplit_openAlternative
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    (tree : DecompositionTree χ support)
    (hcap : cap ∈ capWitnesses χ support 4)
    (hnoStrong : ¬ContainsStrongPolygonSet χ support 8) :
    ∃ path node,
      tree.splitAtPath path = some node ∧
      DecompositionTree.IsLowestSeparatingPath cap tree path ∧
      (((cap ∩ node.lower).card = 1 ∧
          (cap ∩ node.upper).card = 3 ∧
          ¬ContainsCupSet χ node.lower 5) ∨
        ((cap ∩ node.lower).card = 2 ∧
          (cap ∩ node.upper).card = 2 ∧
          ¬ContainsCupSet χ node.lower 6)) := by
  have hcapData := mem_capWitnesses.mp hcap
  have hcapCardTwo : 2 ≤ cap.card := by omega
  let path := tree.lowestSeparatingPath hcapData.1 hcapCardTwo
  have hpath :
      DecompositionTree.IsLowestSeparatingPath cap tree path := by
    exact tree.lowestSeparatingPath_isLowest hcapData.1 hcapCardTwo
  obtain ⟨node, hlookup, hnodeSub, hnotLower, hnotUpper⟩ :=
    tree.lowestSeparatingPath_spec hcapData.1 hcapCardTwo
  have hnodeSupportSub : node.lower ∪ node.upper ⊆ support :=
    tree.splitAtPath_support_subset hlookup
  obtain ⟨u, huCap, huNotLower⟩ := Finset.not_subset.mp hnotLower
  have huUpper : u ∈ node.upper :=
    (Finset.mem_union.mp (hnodeSub huCap)).resolve_left huNotLower
  have hcapUpperNonempty : (cap ∩ node.upper).Nonempty :=
    ⟨u, Finset.mem_inter.mpr ⟨huCap, huUpper⟩⟩
  obtain ⟨l, hlCap, hlNotUpper⟩ := Finset.not_subset.mp hnotUpper
  have hlLower : l ∈ node.lower :=
    (Finset.mem_union.mp (hnodeSub hlCap)).resolve_right hlNotUpper
  have hcapLowerNonempty : (cap ∩ node.lower).Nonempty :=
    ⟨l, Finset.mem_inter.mpr ⟨hlCap, hlLower⟩⟩
  have hcapInterDisjoint :
      Disjoint (cap ∩ node.lower) (cap ∩ node.upper) :=
    node.deep.disjoint.mono Finset.inter_subset_right
      Finset.inter_subset_right
  have hpartition :
      (cap ∩ node.lower) ∪ (cap ∩ node.upper) = cap := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).1
      · exact (Finset.mem_inter.mp hx).1
    · intro hx
      rcases Finset.mem_union.mp (hnodeSub hx) with hxLower | hxUpper
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxLower⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxUpper⟩)
  have hcount : cap.card = (cap ∩ node.lower).card +
      (cap ∩ node.upper).card := by
    calc
      cap.card = ((cap ∩ node.lower) ∪ (cap ∩ node.upper)).card :=
        congrArg Finset.card hpartition.symm
      _ = (cap ∩ node.lower).card + (cap ∩ node.upper).card :=
        Finset.card_union_of_disjoint hcapInterDisjoint
  have hlowerLe : (cap ∩ node.lower).card ≤ 2 :=
    node.deep.cap_inter_lower_card_le_two
      hnodeSub hcapData.2.2 hcapUpperNonempty
  have hlowerPos : 0 < (cap ∩ node.lower).card :=
    hcapLowerNonempty.card_pos
  have hupperPos : 0 < (cap ∩ node.upper).card :=
    hcapUpperNonempty.card_pos
  have hcapUpperSet : IsCapSet χ (cap ∩ node.upper) :=
    FinsetPolygon.IsCapSet.mono hcapData.2.2 Finset.inter_subset_left
  have hprofile :
      ((cap ∩ node.lower).card = 1 ∧
        (cap ∩ node.upper).card = 3) ∨
      ((cap ∩ node.lower).card = 2 ∧
        (cap ∩ node.upper).card = 2) := by
    omega
  refine ⟨path, node, hlookup, hpath, ?_⟩
  rcases hprofile with hprofile | hprofile
  · refine Or.inl ⟨hprofile.1, hprofile.2, ?_⟩
    intro hcup
    obtain ⟨cup, hcupSub, hcupCard, hcupSet⟩ := hcup
    apply hnoStrong
    apply FinsetPolygon.ContainsStrongPolygonSet.mono
      (node.deep.containsStrongPolygonSet_of_cup_cap
        hcupSub Finset.inter_subset_right hcupSet hcapUpperSet
        (k := 8) (by omega))
    exact hnodeSupportSub
  · refine Or.inr ⟨hprofile.1, hprofile.2, ?_⟩
    intro hcup
    obtain ⟨cup, hcupSub, hcupCard, hcupSet⟩ := hcup
    apply hnoStrong
    apply FinsetPolygon.ContainsStrongPolygonSet.mono
      (node.deep.containsStrongPolygonSet_of_cup_cap
        hcupSub Finset.inter_subset_right hcupSet hcapUpperSet
        (k := 8) (by omega))
    exact hnodeSupportSub

/-- The already-assumed strict predecessor `(5,5,8)` bounds the lower child
by 20 in the `1+3` branch of the lowest-split alternative. -/
theorem fourCap_lowestSplit_openAlternative_of_state_558
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    (tree : DecompositionTree χ support)
    (hcap : cap ∈ capWitnesses χ support 4)
    (hstate558 : DecomposableStateUpper 5 5 8)
    (hnoCap : ¬ContainsCapSet χ support 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ support 8) :
    ∃ path node,
      tree.splitAtPath path = some node ∧
      DecompositionTree.IsLowestSeparatingPath cap tree path ∧
      (((cap ∩ node.lower).card = 1 ∧
          (cap ∩ node.upper).card = 3 ∧
          ¬ContainsCupSet χ node.lower 5 ∧ node.lower.card ≤ 20) ∨
        ((cap ∩ node.lower).card = 2 ∧
          (cap ∩ node.upper).card = 2 ∧
          ¬ContainsCupSet χ node.lower 6)) := by
  obtain ⟨path, node, hlookup, hallocated, halternative⟩ :=
    fourCap_lowestSplit_openAlternative tree hcap hnoStrong
  refine ⟨path, node, hlookup, hallocated, ?_⟩
  rcases halternative with hprofile | hprofile
  · refine Or.inl ⟨hprofile.1, hprofile.2.1, hprofile.2.2, ?_⟩
    have hnodeSub : node.lower ∪ node.upper ⊆ support :=
      tree.splitAtPath_support_subset hlookup
    have hlowerSub : node.lower ⊆ support :=
      Finset.subset_union_left.trans hnodeSub
    have hlowerNonempty : node.lower.Nonempty := by
      have hinterNonempty : (cap ∩ node.lower).Nonempty := by
        rw [← Finset.card_pos, hprofile.1]
        decide
      obtain ⟨x, hx⟩ := hinterNonempty
      exact ⟨x, (Finset.mem_inter.mp hx).2⟩
    have hnodeDecomposable :
        IsDecomposableOn χ (node.lower ∪ node.upper) :=
      tree.splitAtPath_isDecomposableOn hlookup
    have hlowerDecomposable : IsDecomposableOn χ node.lower :=
      hnodeDecomposable.subset Finset.subset_union_left hlowerNonempty
    have hthreshold : decomposableThreshold 5 5 8 = 20 := by
      norm_num [decomposableThreshold, Nat.choose]
    by_contra hcard
    have hlarge : decomposableThreshold 5 5 8 < node.lower.card := by
      omega
    rcases hstate558 hlowerDecomposable hlarge with
      hlowerCap | hlowerCup | hlowerStrong
    · exact hnoCap
        (FinsetPolygon.ContainsCapSet.mono hlowerCap hlowerSub)
    · exact hprofile.2.2 hlowerCup
    · exact hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hlowerStrong hlowerSub)
  · exact Or.inr hprofile

/-- The actual singleton-lower state supplies a terminal straddling cap whose
lowest separating tree split satisfies the `1+3`/`2+2` cup-avoidance
alternative. -/
theorem exists_terminalFourCap_lowestSplit_openAlternative_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hupperCard : upper.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8) :
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ upper 4,
      (¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ upper 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap))) ∧
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)).StraddlesCut q.val ∧
      ∃ tree : DecompositionTree χ upper,
        ∃ path : List Bool, ∃ node : DecompositionSplit χ,
        tree.splitAtPath path = some node ∧
        DecompositionTree.IsLowestSeparatingPath cap tree path ∧
        (((cap ∩ node.lower).card = 1 ∧
            (cap ∩ node.upper).card = 3 ∧
            ¬ContainsCupSet χ node.lower 5) ∨
          ((cap ∩ node.lower).card = 2 ∧
            (cap ∩ node.upper).card = 2 ∧
            ¬ContainsCupSet χ node.lower 6)) := by
  obtain ⟨cap, hcap, hterminal, hstraddles, _hexterior,
      _charge, _hcharge⟩ :=
    exists_terminal_straddling_fourCap_exterior_failureCharge_at_578
      hupper hroot hupperCard hnoCap hnoCup hnoStrong
  obtain ⟨tree⟩ := DecompositionTree.exists_of_isDecomposableOn hupper
  have hnoStrongUpper : ¬ContainsStrongPolygonSet χ upper 8 := fun hstrong ↦
    hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
      Finset.subset_union_right)
  obtain ⟨path, node, hlookup, hallocated, halternative⟩ :=
    fourCap_lowestSplit_openAlternative tree hcap hnoStrongUpper
  exact ⟨cap, hcap, hterminal, hstraddles, tree, path, node,
    hlookup, hallocated, halternative⟩

/-- Diagnostic avoidance-aware strict-span recurrence.  Unlike
`DenseFourCapStrictSpanDescent32_23`, it keeps all three hereditary target
avoidance hypotheses.  The tree-local lowest-split alternative above is the
selected reduction; no proof of this global descent proposition is claimed. -/
def OpenDenseFourCapStrictSpanDescent32_23 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {q : Fin n}
      {upper : Finset (Fin n)} (_tree : DecompositionTree χ upper),
    upper.card = 32 →
    ¬ContainsCapSet χ upper 5 →
    ¬ContainsCupSet χ upper 7 →
    ¬ContainsStrongPolygonSet χ upper 8 →
    (∀ subset : Finset (Fin n), subset ⊆ upper →
      subset.card = 23 → ContainsCapSet χ subset 4) →
    (∀ cap, (hcap : cap ∈ capWitnesses χ upper 4) →
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)).StraddlesCut q.val) →
    ∀ cap, (hcap : cap ∈ capWitnesses χ upper 4) →
      ∃ inner, ∃ hinner : inner ∈ capWitnesses χ upper 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap))

/-- Any nonempty finite cap-witness family contradicts strict descent of its
sweep-span width.  This is the route-independent well-founded consumer for
span recurrence proposals. -/
theorem false_of_nonempty_fourCapStrictSpanDescent
    {n : ℕ} {χ : TripleColoring n} {upper : Finset (Fin n)}
    (hexists : ∃ cap, cap ∈ capWitnesses χ upper 4)
    (hdescent : ∀ cap, (hcap : cap ∈ capWitnesses χ upper 4) →
      ∃ inner, ∃ hinner : inner ∈ capWitnesses χ upper 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap))) :
    False := by
  let spanWidth (cap : Finset (Fin n))
      (hcap : cap ∈ capWitnesses χ upper 4) : ℕ :=
    (finsetSweepInterval cap
      (capWitness_nonempty_of_mem (by omega) hcap)).width
  let WidthOccurs (width : ℕ) : Prop :=
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ upper 4,
      spanWidth cap hcap = width
  obtain ⟨cap₀, hcap₀⟩ := hexists
  have hex : ∃ width, WidthOccurs width :=
    ⟨spanWidth cap₀ hcap₀, cap₀, hcap₀, rfl⟩
  obtain ⟨cap, hcap, hwidth⟩ := Nat.find_spec hex
  obtain ⟨inner, hinner, hinside⟩ := hdescent cap hcap
  have hwidthLt : spanWidth inner hinner < spanWidth cap hcap := by
    apply SweepInterval.width_lt_of_strictlyInside
    · exact finsetSweepInterval_lower_le_upper
        (capWitness_nonempty_of_mem (by omega) hinner)
    · exact finsetSweepInterval_lower_le_upper
        (capWitness_nonempty_of_mem (by omega) hcap)
    · exact hinside
  have hmin : Nat.find hex ≤ spanWidth inner hinner :=
    Nat.find_min' hex ⟨inner, hinner, rfl⟩
  rw [hwidth] at hwidthLt
  omega

/-- The corrected recurrence is sufficient to rule out any open dense
32-vertex reservoir carrying the stated common cut. -/
theorem false_of_openDenseFourCapStrictSpanDescent32_23
    (hdescent : OpenDenseFourCapStrictSpanDescent32_23)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)} (tree : DecompositionTree χ upper)
    (hupperCard : upper.card = 32)
    (hnoCap : ¬ContainsCapSet χ upper 5)
    (hnoCup : ¬ContainsCupSet χ upper 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ upper 8)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ upper →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hstraddles : ∀ cap, (hcap : cap ∈ capWitnesses χ upper 4) →
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)).StraddlesCut q.val) :
    False := by
  have hsubsetCard : 23 ≤ upper.card := by omega
  obtain ⟨subset, hsubset, hcard⟩ :=
    Finset.exists_subset_card_eq hsubsetCard
  obtain ⟨cap, hcapSub, hcapCard, hcapSet⟩ :=
    hdense subset hsubset hcard
  have hcap : cap ∈ capWitnesses χ upper 4 :=
    mem_capWitnesses.mpr
      ⟨hcapSub.trans hsubset, hcapCard, hcapSet⟩
  exact false_of_nonempty_fourCapStrictSpanDescent
    ⟨cap, hcap⟩
    (hdescent tree hupperCard hnoCap hnoCup hnoStrong
      hdense hstraddles)

/-- The repaired open-state recurrence closes the exact singleton-lower tail.
This theorem records its role in the state `(5,7,8)` proof without claiming
the recurrence itself. -/
theorem singletonLowerCriticalGate578_of_openDenseFourCapStrictSpanDescent
    (hdescent : OpenDenseFourCapStrictSpanDescent32_23) :
    SingletonLowerCriticalGate578 := by
  intro n χ q upper hupper hroot hupperCard hnoCap hnoCup hnoStrong
  obtain ⟨tree⟩ := DecompositionTree.exists_of_isDecomposableOn hupper
  have hreservoir :=
    dense_straddling_cap_reservoir_at_578
      hupper hroot hnoCap hnoCup hnoStrong
  have hnoCapUpper : ¬ContainsCapSet χ upper 5 := fun hcap ↦
    hnoCap (FinsetPolygon.ContainsCapSet.mono hcap
      Finset.subset_union_right)
  have hnoCupUpper : ¬ContainsCupSet χ upper 7 := fun hcup ↦
    hnoCup (FinsetPolygon.ContainsCupSet.mono hcup
      Finset.subset_union_right)
  have hnoStrongUpper : ¬ContainsStrongPolygonSet χ upper 8 := fun hstrong ↦
    hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
      Finset.subset_union_right)
  exact false_of_openDenseFourCapStrictSpanDescent32_23
    hdescent tree hupperCard hnoCapUpper hnoCupUpper hnoStrongUpper
    hreservoir.1 hreservoir.2

end ErdosSzekeres

end
