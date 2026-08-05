module

public import ErdosSzekeres.StructuralChargingCapFreeSides
public import ErdosSzekeres.StructuralChargingStrongSixSignature
public import ErdosSzekeres.E3State466Certificate
public import ErdosSzekeres.E3State566Certificate

@[expose] public section

/-!
# Witness branches for the `(5,6,7)` two-side gate

This file separates the residual two-side bound into the crossing four-cap
and strong-six witness branches produced by the symbolic cup-block theorem.
The split prevents quantitative claims about one witness type from being
silently used in the other branch.
-/

namespace ErdosSzekeres

/-- Hereditary transport of the kernel-checked twelve-vertex `(4,6,6)`
certificate.  This version only assumes the rank-three one-change law on the
ambient finite set; it does not require a decomposition tree. -/
theorem containsCapFour_or_cupSix_or_strongSix_of_oneChange_card_ge_twelve
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hcard : 12 ≤ s.card) :
    ContainsCapSet χ s 4 ∨ ContainsCupSet χ s 6 ∨
      ContainsStrongPolygonSet χ s 6 := by
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin 12 ↪o Fin n := t.orderEmbOfFin htcard
  let ψ : TripleColoring 12 := χ.restrict e
  have he_mem (i : Fin 12) : e i ∈ s :=
    hts (t.orderEmbOfFin_mem htcard i)
  have hallowed : ∀ (a b c d : Fin 12),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (ψ ⟨a, b, c, hab, hbc⟩)
        (ψ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (ψ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (ψ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    simpa [ψ, TripleColoring.restrict, OrderedTriple.map] using
      hone (e.strictMono hab) (e.strictMono hbc) (e.strictMono hcd)
        (he_mem a) (he_mem b) (he_mem c) (he_mem d)
  rcases exists_cap_four_or_cup_six_or_strong_six ψ hallowed with
      ⟨f, hcap⟩ | ⟨f, hcup⟩ | ⟨f, hstrong⟩
  · let g : Fin 4 ↪o Fin n := f.trans e
    let cap := Finset.univ.image g
    refine Or.inl ⟨cap, ?_, ?_, ?_⟩
    · intro x hx
      simp only [cap, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsCap χ g := by
        simpa [g, ψ, Function.comp_def] using
          IsMonochromaticChain.map_of_restrict_eq e rfl hcap
      exact FinsetPolygon.IsCap.image hmap
  · let g : Fin 6 ↪o Fin n := f.trans e
    let cup := Finset.univ.image g
    refine Or.inr (Or.inl ⟨cup, ?_, ?_, ?_⟩)
    · intro x hx
      simp only [cup, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsCup χ g := by
        simpa [g, ψ, Function.comp_def] using
          IsMonochromaticChain.map_of_restrict_eq e rfl hcup
      exact FinsetPolygon.IsCup.image hmap
  · let g : Fin 6 ↪o Fin n := f.trans e
    let polygon := Finset.univ.image g
    refine Or.inr (Or.inr ⟨polygon, ?_, ?_, ?_⟩)
    · intro x hx
      simp only [polygon, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsStrongPolygonOn χ g := by
        intro i j k l hij hjk hkl
        simpa [g, ψ, IsStrongPolygonOn, TripleColoring.restrict,
          OrderedTriple.map] using hstrong hij hjk hkl
      exact FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hmap

/-- In the no-six-cup/no-strong-six branch, every twelve-point subset already
contains a four-cap.  This is the certificate consequence used by the exact
fifteen-vertex kernel. -/
theorem containsCapFour_of_oneChange_card_ge_twelve_no_cupSix_no_strongSix
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hcard : 12 ≤ s.card)
    (hnoCup : ¬ContainsCupSet χ s 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ s 6) :
    ContainsCapSet χ s 4 := by
  rcases containsCapFour_or_cupSix_or_strongSix_of_oneChange_card_ge_twelve
      hone hcard with hcap | hcup | hstrong
  · exact hcap
  · exact False.elim (hnoCup hcup)
  · exact False.elim (hnoStrong hstrong)

/-- On a four-cap-free set of at least twelve vertices, the checked `(4,6,6)`
state turns six-cup avoidance into an internal strong six-set. -/
theorem containsStrongSix_of_oneChange_no_capFour_no_cupSix_card_ge_twelve
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hcard : 12 ≤ s.card)
    (hnoCap : ¬ContainsCapSet χ s 4)
    (hnoCup : ¬ContainsCupSet χ s 6) :
    ContainsStrongPolygonSet χ s 6 := by
  rcases containsCapFour_or_cupSix_or_strongSix_of_oneChange_card_ge_twelve
      hone hcard with hcap | hcup | hstrong
  · exact False.elim (hnoCap hcap)
  · exact False.elim (hnoCup hcup)
  · exact hstrong

/-- At total size at least twenty-two, either one cap-free side already
contains a strong six-set or the only remaining cardinality pattern is the
balanced `11+11` split. -/
theorem two_cap_free_sides_contains_internal_strongSix_or_eleven_eleven
    {n : ℕ} {χ : TripleColoring n}
    {left right : Finset (Fin n)}
    (hone : OneChangeOn χ (left ∪ right))
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6)
    (hleftBound : left.card ≤ 15) (hrightBound : right.card ≤ 15)
    (htotal : 22 ≤ left.card + right.card) :
    ContainsStrongPolygonSet χ left 6 ∨
      ContainsStrongPolygonSet χ right 6 ∨
      (left.card = 11 ∧ right.card = 11) := by
  by_cases hleftLarge : 12 ≤ left.card
  · exact Or.inl
      (containsStrongSix_of_oneChange_no_capFour_no_cupSix_card_ge_twelve
        (hone.mono Finset.subset_union_left) hleftLarge hleftCap
        (fun hcup ↦ hnoCup
          (FinsetPolygon.ContainsCupSet.mono hcup Finset.subset_union_left)))
  by_cases hrightLarge : 12 ≤ right.card
  · exact Or.inr (Or.inl
      (containsStrongSix_of_oneChange_no_capFour_no_cupSix_card_ge_twelve
        (hone.mono Finset.subset_union_right) hrightLarge hrightCap
        (fun hcup ↦ hnoCup
          (FinsetPolygon.ContainsCupSet.mono hcup Finset.subset_union_right))))
  · exact Or.inr (Or.inr (by omega))

/-- Exact fifteen-vertex deletion form: after deleting any designated three
vertices, a no-six-cup/no-strong-six one-change set still contains a four-cap.
Thus its family of four-caps has transversal number at least four. -/
theorem containsCapFour_avoiding_three_of_card_fifteen
    {n : ℕ} {χ : TripleColoring n} {s deleted : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hsCard : s.card = 15)
    (hdeletedSub : deleted ⊆ s) (hdeletedCard : deleted.card = 3)
    (hnoCup : ¬ContainsCupSet χ s 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ s 6) :
    ContainsCapSet χ (s \ deleted) 4 := by
  have hremainingCard : 12 ≤ (s \ deleted).card := by
    have hcard := Finset.card_sdiff_add_card_eq_card hdeletedSub
    omega
  apply containsCapFour_of_oneChange_card_ge_twelve_no_cupSix_no_strongSix
      (hone.mono (Finset.sdiff_subset)) hremainingCard
  · intro hcup
    exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup Finset.sdiff_subset)
  · intro hstrong
    exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.sdiff_subset)

/-- For two four-cap-free sides totaling fifteen vertices, every deleted
triple misses a crossing four-cap in the no-six-cup/no-strong-six branch. -/
theorem crossingCapFour_avoiding_three_of_two_cap_free_sides_card_fifteen
    {n : ℕ} {χ : TripleColoring n}
    {left right deleted : Finset (Fin n)}
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hone : OneChangeOn χ (left ∪ right))
    (htotalCard : (left ∪ right).card = 15)
    (hdeletedSub : deleted ⊆ left ∪ right)
    (hdeletedCard : deleted.card = 3)
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) 6) :
    ∃ cap : Finset (Fin n),
      cap ⊆ (left ∪ right) \ deleted ∧ cap.card = 4 ∧
      IsCapSet χ cap ∧ (cap ∩ left).Nonempty ∧
        (cap ∩ right).Nonempty := by
  obtain ⟨cap, hcapSub, hcapCard, hcapSet⟩ :=
    containsCapFour_avoiding_three_of_card_fifteen hone htotalCard
      hdeletedSub hdeletedCard hnoCup hnoStrong
  have hcapSubUnion : cap ⊆ left ∪ right :=
    hcapSub.trans Finset.sdiff_subset
  have hleftMeet : (cap ∩ left).Nonempty := by
    by_contra hnot
    have hcapSubRight : cap ⊆ right := by
      intro x hx
      rcases Finset.mem_union.mp (hcapSubUnion hx) with hxLeft | hxRight
      · exact (hnot ⟨x, Finset.mem_inter.mpr ⟨hx, hxLeft⟩⟩).elim
      · exact hxRight
    exact hrightCap ⟨cap, hcapSubRight, hcapCard, hcapSet⟩
  have hrightMeet : (cap ∩ right).Nonempty := by
    by_contra hnot
    have hcapSubLeft : cap ⊆ left := by
      intro x hx
      rcases Finset.mem_union.mp (hcapSubUnion hx) with hxLeft | hxRight
      · exact hxLeft
      · exact (hnot ⟨x, Finset.mem_inter.mpr ⟨hx, hxRight⟩⟩).elim
    exact hleftCap ⟨cap, hcapSubLeft, hcapCard, hcapSet⟩
  exact ⟨cap, hcapSub, hcapCard, hcapSet, hleftMeet, hrightMeet⟩

/-- Hereditary transport of the kernel-checked sixteen-vertex `(5,6,6)`
certificate to an arbitrary finite one-change set. -/
theorem containsCapFive_or_cupSix_or_strongSix_of_oneChange_card_ge_sixteen
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (hcard : 16 ≤ s.card) :
    ContainsCapSet χ s 5 ∨ ContainsCupSet χ s 6 ∨
      ContainsStrongPolygonSet χ s 6 := by
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin 16 ↪o Fin n := t.orderEmbOfFin htcard
  let ψ : TripleColoring 16 := χ.restrict e
  have he_mem (i : Fin 16) : e i ∈ s :=
    hts (t.orderEmbOfFin_mem htcard i)
  have hallowed : ∀ (a b c d : Fin 16),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (ψ ⟨a, b, c, hab, hbc⟩)
        (ψ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (ψ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (ψ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    simpa [ψ, TripleColoring.restrict, OrderedTriple.map] using
      hone (e.strictMono hab) (e.strictMono hbc) (e.strictMono hcd)
        (he_mem a) (he_mem b) (he_mem c) (he_mem d)
  rcases exists_cap_five_or_cup_six_or_strong_six ψ hallowed with
      ⟨f, hcap⟩ | ⟨f, hcup⟩ | ⟨f, hstrong⟩
  · let g : Fin 5 ↪o Fin n := f.trans e
    let cap := Finset.univ.image g
    refine Or.inl ⟨cap, ?_, ?_, ?_⟩
    · intro x hx
      simp only [cap, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsCap χ g := by
        simpa [g, ψ, Function.comp_def] using
          IsMonochromaticChain.map_of_restrict_eq e rfl hcap
      exact FinsetPolygon.IsCap.image hmap
  · let g : Fin 6 ↪o Fin n := f.trans e
    let cup := Finset.univ.image g
    refine Or.inr (Or.inl ⟨cup, ?_, ?_, ?_⟩)
    · intro x hx
      simp only [cup, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsCup χ g := by
        simpa [g, ψ, Function.comp_def] using
          IsMonochromaticChain.map_of_restrict_eq e rfl hcup
      exact FinsetPolygon.IsCup.image hmap
  · let g : Fin 6 ↪o Fin n := f.trans e
    let polygon := Finset.univ.image g
    refine Or.inr (Or.inr ⟨polygon, ?_, ?_, ?_⟩)
    · intro x hx
      simp only [polygon, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsStrongPolygonOn χ g := by
        intro i j k l hij hjk hkl
        simpa [g, ψ, IsStrongPolygonOn, TripleColoring.restrict,
          OrderedTriple.map] using hstrong hij hjk hkl
      exact FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hmap

/-- A strong-six packing condition at the sharp boundary: every six-point
deletion leaves another strong six-set. -/
def StrongSixAvoidsEverySix {n : ℕ} (χ : TripleColoring n)
    (ambient : Finset (Fin n)) : Prop :=
  ∀ deleted : Finset (Fin n), deleted ⊆ ambient → deleted.card = 6 →
    ContainsStrongPolygonSet χ (ambient \ deleted) 6

/-- At total size at least twenty-two, the certified `(5,6,6)` state forces
the strong-six family to avoid every prescribed six-set whenever ambient
five-caps and six-cups are forbidden. -/
theorem strongSixAvoidsEverySix_of_card_ge_twenty_two
    {n : ℕ} {χ : TripleColoring n} {ambient : Finset (Fin n)}
    (hone : OneChangeOn χ ambient) (hcard : 22 ≤ ambient.card)
    (hnoCap : ¬ContainsCapSet χ ambient 5)
    (hnoCup : ¬ContainsCupSet χ ambient 6) :
    StrongSixAvoidsEverySix χ ambient := by
  intro deleted hdeletedSub hdeletedCard
  have hremainingCard : 16 ≤ (ambient \ deleted).card := by
    have hcardSplit := Finset.card_sdiff_add_card_eq_card hdeletedSub
    omega
  rcases containsCapFive_or_cupSix_or_strongSix_of_oneChange_card_ge_sixteen
      (hone.mono Finset.sdiff_subset) hremainingCard with
      hcap | hcup | hstrong
  · exact (hnoCap
      (FinsetPolygon.ContainsCapSet.mono hcap Finset.sdiff_subset)).elim
  · exact (hnoCup
      (FinsetPolygon.ContainsCupSet.mono hcup Finset.sdiff_subset)).elim
  · exact hstrong

/-- In particular, every designated strong six-set at the sharp boundary has
a disjoint strong-six partner. -/
theorem exists_disjoint_strongSix_of_avoidsEverySix
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    (hpacking : StrongSixAvoidsEverySix χ ambient)
    (hpolygonSub : polygon ⊆ ambient) (hpolygonCard : polygon.card = 6) :
    ∃ partner : Finset (Fin n), partner ⊆ ambient ∧ partner.card = 6 ∧
      IsStrongPolygonSet χ partner ∧ Disjoint polygon partner := by
  obtain ⟨partner, hpartnerSub, hpartnerCard, hpartnerStrong⟩ :=
    hpacking polygon hpolygonSub hpolygonCard
  refine ⟨partner, hpartnerSub.trans Finset.sdiff_subset,
    hpartnerCard, hpartnerStrong, ?_⟩
  exact Finset.disjoint_left.mpr (fun x hxPolygon hxPartner ↦
    (Finset.mem_sdiff.mp (hpartnerSub hxPartner)).2 hxPolygon)

/-- Two disjoint strong six-sets are mutually middle-obstructed when every
vertex of either set fails to extend the other to a strong seven-set. -/
def MutuallyMiddleObstructedStrongSixPair {n : ℕ}
    (χ : TripleColoring n) (first second : Finset (Fin n)) : Prop :=
  Disjoint first second ∧ first.card = 6 ∧ second.card = 6 ∧
    IsStrongPolygonSet χ first ∧ IsStrongPolygonSet χ second ∧
    (∀ q ∈ second, HasMiddleExtensionFailure χ first q) ∧
    (∀ q ∈ first, HasMiddleExtensionFailure χ second q)

/-- Every packed strong six-set has a disjoint partner carrying six local
middle failures in each direction when strong seven-sets are forbidden. -/
theorem exists_mutuallyMiddleObstructed_partner
    {n : ℕ} {χ : TripleColoring n} {ambient first : Finset (Fin n)}
    (hpacking : StrongSixAvoidsEverySix χ ambient)
    (hfirstSub : first ⊆ ambient) (hfirstCard : first.card = 6)
    (hfirstStrong : IsStrongPolygonSet χ first)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient 7) :
    ∃ second : Finset (Fin n), second ⊆ ambient ∧
      MutuallyMiddleObstructedStrongSixPair χ first second := by
  obtain ⟨second, hsecondSub, hsecondCard, hsecondStrong, hdisjoint⟩ :=
    exists_disjoint_strongSix_of_avoidsEverySix
      hpacking hfirstSub hfirstCard
  refine ⟨second, hsecondSub, hdisjoint, hfirstCard, hsecondCard,
    hfirstStrong, hsecondStrong, ?_, ?_⟩
  · intro q hqSecond
    exact strongSix_middle_extension_failure_of_no_strongSeven
      hfirstSub hfirstCard hfirstStrong (hsecondSub hqSecond)
      (fun hqFirst ↦ Finset.disjoint_left.mp hdisjoint hqFirst hqSecond)
      hnoStrong
  · intro q hqFirst
    exact strongSix_middle_extension_failure_of_no_strongSeven
      hsecondSub hsecondCard hsecondStrong (hfirstSub hqFirst)
      (fun hqSecond ↦ Finset.disjoint_left.mp hdisjoint hqFirst hqSecond)
      hnoStrong

/-- If a strong six lies in the left side of an ordered cut, every right-side
vertex has a right-endpoint middle failure relative to it. -/
theorem right_side_has_rightEndpoint_failures_from_left_strongSix
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hpolygonSub : polygon ⊆ left) (hpolygonCard : polygon.card = 6)
    (hpolygonStrong : IsStrongPolygonSet χ polygon)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) 7) :
    ∀ q ∈ right,
      HasMiddleExtensionFailureWithRole χ polygon q .rightEndpoint := by
  intro q hqRight
  have hpolygonAmbient : polygon ⊆ left ∪ right :=
    hpolygonSub.trans Finset.subset_union_left
  have hqAmbient : q ∈ left ∪ right := Finset.mem_union_right left hqRight
  have hqPolygon : q ∉ polygon := by
    intro hq
    exact Finset.disjoint_left.mp hdisjoint (hpolygonSub hq) hqRight
  apply middleExtensionFailure_role_right_of_after
  · intro x hx
    exact horder x (hpolygonSub hx) q hqRight
  · exact strongSix_middle_extension_failure_of_no_strongSeven
      hpolygonAmbient hpolygonCard hpolygonStrong hqAmbient hqPolygon
      hnoStrong

/-- The forced endpoint failures on the right normalize to four internally
referenced middle anomalies and one exceptional final-middle fan class. -/
theorem right_side_has_internal_or_final_anomalies_from_left_strongSix
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hpolygonSub : polygon ⊆ left) (hpolygonCard : polygon.card = 6)
    (hpolygonStrong : IsStrongPolygonSet χ polygon)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) 7) :
    ∀ q ∈ right,
      HasInternalRightEndpointMiddleAnomaly χ polygon hpolygonCard q ∨
        HasFinalMiddleFanVariation χ polygon hpolygonCard q := by
  have hfailures :=
    right_side_has_rightEndpoint_failures_from_left_strongSix
      hdisjoint horder hpolygonSub hpolygonCard hpolygonStrong hnoStrong
  intro q hqRight
  exact rightEndpoint_failure_internal_or_final hpolygonCard hpolygonStrong
    (fun x hx ↦ horder x (hpolygonSub hx) q hqRight)
    (hfailures q hqRight)

/-- Symmetrically, if a strong six lies in the right side, every left-side
vertex has a left-endpoint middle failure relative to it. -/
theorem left_side_has_leftEndpoint_failures_from_right_strongSix
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hpolygonSub : polygon ⊆ right) (hpolygonCard : polygon.card = 6)
    (hpolygonStrong : IsStrongPolygonSet χ polygon)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) 7) :
    ∀ q ∈ left,
      HasMiddleExtensionFailureWithRole χ polygon q .leftEndpoint := by
  intro q hqLeft
  have hpolygonAmbient : polygon ⊆ left ∪ right :=
    hpolygonSub.trans Finset.subset_union_right
  have hqAmbient : q ∈ left ∪ right := Finset.mem_union_left right hqLeft
  have hqPolygon : q ∉ polygon := by
    intro hq
    exact Finset.disjoint_left.mp hdisjoint hqLeft (hpolygonSub hq)
  apply middleExtensionFailure_role_left_of_before
  · intro x hx
    exact horder q hqLeft x (hpolygonSub hx)
  · exact strongSix_middle_extension_failure_of_no_strongSeven
      hpolygonAmbient hpolygonCard hpolygonStrong hqAmbient hqPolygon
      hnoStrong

/-- In an eight-vertex four-cap-free one-change set, every designated vertex
can be avoided by some four-cup. This is the first structural distinction
between the sharp `7+7` model and the forbidden `7+8` boundary. -/
theorem containsCupFour_avoiding_vertex_of_card_ge_eight
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {q : Fin n}
    (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4)
    (hq : q ∈ s) (hcard : 8 ≤ s.card) :
    ContainsCupSet χ (s.erase q) 4 := by
  apply containsCupFour_of_oneChange_no_capFour_card_ge_seven
  · exact hone.mono (Finset.erase_subset q s)
  · intro hcap
    exact hnoCap
      (FinsetPolygon.ContainsCapSet.mono hcap (Finset.erase_subset q s))
  · rw [Finset.card_erase_of_mem hq]
    omega

/-- Exact residual theorem contract for the crossing four-cap witness branch. -/
def TwoCapFreeSidesCrossingCapBranch567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right cap : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      7 ≤ left.card → left.card ≤ 15 →
      7 ≤ right.card → right.card ≤ 15 →
      ¬ContainsCapSet χ (left ∪ right) 5 →
      ¬ContainsCupSet χ (left ∪ right) 6 →
      ¬ContainsStrongPolygonSet χ (left ∪ right) 7 →
      cap ⊆ left ∪ right → cap.card = 4 → IsCapSet χ cap →
      (cap ∩ left).Nonempty → (cap ∩ right).Nonempty →
      left.card + right.card ≤ 21

/-- Exact residual theorem contract for the designated strong-six witness
branch recommended by the bounded route review. -/
def TwoCapFreeSidesStrongSixBranch567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right polygon : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      7 ≤ left.card → left.card ≤ 15 →
      7 ≤ right.card → right.card ≤ 15 →
      ¬ContainsCapSet χ (left ∪ right) 5 →
      ¬ContainsCupSet χ (left ∪ right) 6 →
      ¬ContainsStrongPolygonSet χ (left ∪ right) 7 →
      polygon ⊆ left ∪ right → polygon.card = 6 →
      IsStrongPolygonSet χ polygon →
      left.card + right.card ≤ 21

/-- Exact residual theorem contract for the branch containing no ambient
strong six-set. In this branch the cup-block dichotomy necessarily supplies a
crossing four-cap, so cap signatures may be combined with five-cup probes. -/
def TwoCapFreeSidesNoStrongSixBranch567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      7 ≤ left.card → left.card ≤ 15 →
      7 ≤ right.card → right.card ≤ 15 →
      ¬ContainsCapSet χ (left ∪ right) 5 →
      ¬ContainsCupSet χ (left ∪ right) 6 →
      ¬ContainsStrongPolygonSet χ (left ∪ right) 6 →
      left.card + right.card ≤ 21

/-- The already kernel-checked `(5,6,6)` finite state closes the complete
no-strong-six branch.  In fact it proves the stronger total bound fifteen;
the cap-free-side hypotheses are not needed for this branch. -/
theorem twoCapFreeSidesNoStrongSixBranch567 :
    TwoCapFreeSidesNoStrongSixBranch567 := by
  intro n χ left right hdisjoint _horder _hleftCap _hrightCap hone
    _hleftSeven _hleftFifteen _hrightSeven _hrightFifteen
    hnoCap hnoCup hnoStrong
  have hcardUnion : (left ∪ right).card = left.card + right.card :=
    Finset.card_union_of_disjoint hdisjoint
  by_contra hnot
  have hcard : 16 ≤ (left ∪ right).card := by omega
  rcases containsCapFive_or_cupSix_or_strongSix_of_oneChange_card_ge_sixteen
      hone hcard with hcap | hcup | hstrong
  · exact hnoCap hcap
  · exact hnoCup hcup
  · exact hnoStrong hstrong

/-- Refined remaining contract.  A hypothetical 22-vertex counterexample
must have a strong-six family avoiding every prescribed six-set, not merely
one designated strong witness. -/
def TwoCapFreeSidesStrongSixPackingBranch567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      7 ≤ left.card → left.card ≤ 15 →
      7 ≤ right.card → right.card ≤ 15 →
      ¬ContainsCapSet χ (left ∪ right) 5 →
      ¬ContainsCupSet χ (left ∪ right) 6 →
      ¬ContainsStrongPolygonSet χ (left ∪ right) 7 →
      StrongSixAvoidsEverySix χ (left ∪ right) →
      left.card + right.card ≤ 21

/-- Unbalanced sharp-boundary branch: an internal strong six supplies
uniform endpoint-role failures on the opposite ordered side. -/
def TwoCapFreeSidesEndpointObstructedStrongSixBranch567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right polygon : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      7 ≤ left.card → left.card ≤ 15 →
      7 ≤ right.card → right.card ≤ 15 →
      ¬ContainsCapSet χ (left ∪ right) 5 →
      ¬ContainsCupSet χ (left ∪ right) 6 →
      ¬ContainsStrongPolygonSet χ (left ∪ right) 7 →
      polygon.card = 6 → IsStrongPolygonSet χ polygon →
      ((polygon ⊆ left ∧
          ∀ q ∈ right, HasMiddleExtensionFailureWithRole χ polygon q
            .rightEndpoint) ∨
        (polygon ⊆ right ∧
          ∀ q ∈ left, HasMiddleExtensionFailureWithRole χ polygon q
            .leftEndpoint)) →
      left.card + right.card ≤ 21

/-- Balanced sharp-boundary branch left after internal-strong-six extraction.
Its fixed side sizes make this an exact `11+11` obstruction theorem. -/
def TwoCapFreeSidesElevenElevenBranch567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      left.card = 11 → right.card = 11 →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      ContainsCapSet χ (left ∪ right) 5 ∨
        ContainsCupSet χ (left ∪ right) 6 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 7

/-- Sharp fixed-cardinality kernel for the no-strong-six branch. The two
ordered cap-free sides have sizes seven and eight in either orientation. -/
def TwoCapFreeSidesForce566AtFifteen : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ((left.card = 7 ∧ right.card = 8) ∨
        (left.card = 8 ∧ right.card = 7)) →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      ContainsCapSet χ (left ∪ right) 5 ∨
        ContainsCupSet χ (left ∪ right) 6 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 6

/-- The exact `7+8/8+7` forcing kernel bounds every no-strong-six residual
configuration by fourteen vertices, substantially stronger than the bound 21
needed by the parent theorem. -/
theorem twoCapFreeSidesNoStrongSixBranch567_of_forceAtFifteen
    (hforce : TwoCapFreeSidesForce566AtFifteen) :
    TwoCapFreeSidesNoStrongSixBranch567 := by
  intro n χ left right hdisjoint horder hleftCap hrightCap hone
    hleftSeven _hleftFifteen hrightSeven _hrightFifteen
    hnoCap hnoCup hnoStrong
  by_contra hnot
  have htotal : 15 ≤ left.card + right.card := by omega
  by_cases hleftEight : 8 ≤ left.card
  · obtain ⟨left', hleftSub, hleftCard⟩ :=
      Finset.exists_subset_card_eq hleftEight
    obtain ⟨right', hrightSub, hrightCard⟩ :=
      Finset.exists_subset_card_eq hrightSeven
    have hdisjoint' : Disjoint left' right' :=
      hdisjoint.mono hleftSub hrightSub
    have horder' : ∀ x ∈ left', ∀ y ∈ right', x < y := by
      intro x hx y hy
      exact horder x (hleftSub hx) y (hrightSub hy)
    have hunionSub : left' ∪ right' ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    have hleftCap' : ¬ContainsCapSet χ left' 4 := by
      intro hcap
      exact hleftCap (FinsetPolygon.ContainsCapSet.mono hcap hleftSub)
    have hrightCap' : ¬ContainsCapSet χ right' 4 := by
      intro hcap
      exact hrightCap (FinsetPolygon.ContainsCapSet.mono hcap hrightSub)
    rcases hforce hdisjoint' horder'
        (Or.inr ⟨hleftCard, hrightCard⟩)
        hleftCap' hrightCap' (hone.mono hunionSub) with hcap | hcup | hstrong
    · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hunionSub)
    · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hunionSub)
    · exact hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub)
  · have hleftCard : left.card = 7 := by omega
    have hrightEight : 8 ≤ right.card := by omega
    obtain ⟨left', hleftSub, hleftCard'⟩ :=
      Finset.exists_subset_card_eq hleftSeven
    obtain ⟨right', hrightSub, hrightCard⟩ :=
      Finset.exists_subset_card_eq hrightEight
    have hdisjoint' : Disjoint left' right' :=
      hdisjoint.mono hleftSub hrightSub
    have horder' : ∀ x ∈ left', ∀ y ∈ right', x < y := by
      intro x hx y hy
      exact horder x (hleftSub hx) y (hrightSub hy)
    have hunionSub : left' ∪ right' ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    have hleftCap' : ¬ContainsCapSet χ left' 4 := by
      intro hcap
      exact hleftCap (FinsetPolygon.ContainsCapSet.mono hcap hleftSub)
    have hrightCap' : ¬ContainsCapSet χ right' 4 := by
      intro hcap
      exact hrightCap (FinsetPolygon.ContainsCapSet.mono hcap hrightSub)
    rcases hforce hdisjoint' horder'
        (Or.inl ⟨hleftCard', hrightCard⟩)
        hleftCap' hrightCap' (hone.mono hunionSub) with hcap | hcup | hstrong
    · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hunionSub)
    · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hunionSub)
    · exact hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub)

/-- The no-strong-six branch and the designated strong-six branch form an
exhaustive, non-circular reduction of the local two-side bound. -/
theorem twoCapFreeSidesBound567_of_strongSixDichotomy
    (hnoStrongSix : TwoCapFreeSidesNoStrongSixBranch567)
    (hstrongSix : TwoCapFreeSidesStrongSixBranch567) :
    TwoCapFreeSidesBound567 := by
  intro n χ left right hdisjoint horder hleftCap hrightCap hone
    hnoCap hnoCup hnoStrongSeven
  by_contra hnot
  have hlarge : 21 < left.card + right.card := by omega
  have hwindow := two_cap_free_sides_counterexample_card_window
    hone hleftCap hrightCap hnoCup hlarge
  by_cases hstrong : ContainsStrongPolygonSet χ (left ∪ right) 6
  · obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonSet⟩ := hstrong
    have hbound := hstrongSix hdisjoint horder hleftCap hrightCap hone
      hwindow.1 hwindow.2.1 hwindow.2.2.1 hwindow.2.2.2
      hnoCap hnoCup hnoStrongSeven hpolygonSub hpolygonCard hpolygonSet
    omega
  · have hbound := hnoStrongSix hdisjoint horder hleftCap hrightCap hone
      hwindow.1 hwindow.2.1 hwindow.2.2.1 hwindow.2.2.2
      hnoCap hnoCup hstrong
    omega

/-- Consequently the complete local two-side bound has only one remaining
branch: configurations carrying a designated strong six-set. -/
theorem twoCapFreeSidesBound567_of_strongSixBranch
    (hstrongSix : TwoCapFreeSidesStrongSixBranch567) :
    TwoCapFreeSidesBound567 :=
  twoCapFreeSidesBound567_of_strongSixDichotomy
    twoCapFreeSidesNoStrongSixBranch567 hstrongSix

/-- The packing contract is sufficient for the whole local two-side bound:
any counterexample of size at least twenty-two acquires the packing hypothesis
from the certified sixteen-vertex state. -/
theorem twoCapFreeSidesBound567_of_strongSixPackingBranch
    (hpackingBranch : TwoCapFreeSidesStrongSixPackingBranch567) :
    TwoCapFreeSidesBound567 := by
  intro n χ left right hdisjoint horder hleftCap hrightCap hone
    hnoCap hnoCup hnoStrong
  by_contra hnot
  have hlarge : 21 < left.card + right.card := by omega
  have hwindow := two_cap_free_sides_counterexample_card_window
    hone hleftCap hrightCap hnoCup hlarge
  have hcardUnion : (left ∪ right).card = left.card + right.card :=
    Finset.card_union_of_disjoint hdisjoint
  have hpacking : StrongSixAvoidsEverySix χ (left ∪ right) :=
    strongSixAvoidsEverySix_of_card_ge_twenty_two hone (by omega)
      hnoCap hnoCup
  have hbound := hpackingBranch hdisjoint horder hleftCap hrightCap hone
    hwindow.1 hwindow.2.1 hwindow.2.2.1 hwindow.2.2.2
    hnoCap hnoCup hnoStrong hpacking
  omega

/-- The complete two-side bound reduces to two sharply separated targets:
the endpoint-obstructed internal-strong-six branch and the exact balanced
`11+11` branch. -/
theorem twoCapFreeSidesBound567_of_endpointBranch_and_elevenEleven
    (hendpoint : TwoCapFreeSidesEndpointObstructedStrongSixBranch567)
    (hbalanced : TwoCapFreeSidesElevenElevenBranch567) :
    TwoCapFreeSidesBound567 := by
  intro n χ left right hdisjoint horder hleftCap hrightCap hone
    hnoCap hnoCup hnoStrong
  by_contra hnot
  have hlarge : 21 < left.card + right.card := by omega
  have hwindow := two_cap_free_sides_counterexample_card_window
    hone hleftCap hrightCap hnoCup hlarge
  have htotal : 22 ≤ left.card + right.card := by omega
  rcases two_cap_free_sides_contains_internal_strongSix_or_eleven_eleven
      hone hleftCap hrightCap hnoCup hwindow.2.1 hwindow.2.2.2 htotal with
      hleftStrong | hrightStrong | hbalancedCards
  · obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hleftStrong
    have hfailures :=
      right_side_has_rightEndpoint_failures_from_left_strongSix
        hdisjoint horder hpolygonSub hpolygonCard hpolygonStrong hnoStrong
    have hbound := hendpoint hdisjoint horder hleftCap hrightCap hone
      hwindow.1 hwindow.2.1 hwindow.2.2.1 hwindow.2.2.2
      hnoCap hnoCup hnoStrong hpolygonCard hpolygonStrong
      (Or.inl ⟨hpolygonSub, hfailures⟩)
    omega
  · obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hrightStrong
    have hfailures :=
      left_side_has_leftEndpoint_failures_from_right_strongSix
        hdisjoint horder hpolygonSub hpolygonCard hpolygonStrong hnoStrong
    have hbound := hendpoint hdisjoint horder hleftCap hrightCap hone
      hwindow.1 hwindow.2.1 hwindow.2.2.1 hwindow.2.2.2
      hnoCap hnoCup hnoStrong hpolygonCard hpolygonStrong
      (Or.inr ⟨hpolygonSub, hfailures⟩)
    omega
  · rcases hbalanced hdisjoint horder hbalancedCards.1 hbalancedCards.2
      hleftCap hrightCap hone with hcap | hcup | hstrong
    · exact hnoCap hcap
    · exact hnoCup hcup
    · exact hnoStrong hstrong

/-- Closing both witness branches closes the complete local two-side bound. -/
theorem twoCapFreeSidesBound567_of_witnessBranches
    (hcapBranch : TwoCapFreeSidesCrossingCapBranch567)
    (hstrongBranch : TwoCapFreeSidesStrongSixBranch567) :
    TwoCapFreeSidesBound567 := by
  intro n χ left right hdisjoint horder hleftCap hrightCap hone
    hnoCap hnoCup hnoStrong
  by_contra hnot
  have hlarge : 21 < left.card + right.card := by omega
  have hwindow := two_cap_free_sides_counterexample_card_window
    hone hleftCap hrightCap hnoCup hlarge
  have htotal : 22 ≤ left.card + right.card := by omega
  rcases two_cap_free_sides_contains_crossing_capFour_or_strongSix
      hdisjoint horder hone hleftCap hrightCap
      hwindow.1 hwindow.2.2.1 htotal hnoCup with hcap | hstrong
  · obtain ⟨cap, hcapSub, hcapCard, hcapSet, hcapLeft, hcapRight⟩ := hcap
    have hbound := hcapBranch hdisjoint horder hleftCap hrightCap hone
      hwindow.1 hwindow.2.1 hwindow.2.2.1 hwindow.2.2.2
      hnoCap hnoCup hnoStrong hcapSub hcapCard hcapSet hcapLeft hcapRight
    omega
  · obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonSet⟩ := hstrong
    have hbound := hstrongBranch hdisjoint horder hleftCap hrightCap hone
      hwindow.1 hwindow.2.1 hwindow.2.2.1 hwindow.2.2.2
      hnoCap hnoCup hnoStrong hpolygonSub hpolygonCard hpolygonSet
    omega

end ErdosSzekeres
