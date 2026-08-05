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

/-- Adjoining one external vertex to an eleven-vertex four-cap-free side
activates the checked twelve-vertex state.  With ambient six-cups excluded,
the result is either a strong six or a four-cap that necessarily passes
through the adjoined vertex. -/
theorem adjoin_vertex_to_eleven_cap_free_side
    {n : ℕ} {χ : TripleColoring n}
    {ambient side : Finset (Fin n)} {q : Fin n}
    (hsideSub : side ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hqSide : q ∉ side) (hsideCard : side.card = 11)
    (hsideCap : ¬ContainsCapSet χ side 4)
    (hone : OneChangeOn χ ambient)
    (hnoCup : ¬ContainsCupSet χ ambient 6) :
    (∃ cap : Finset (Fin n), cap ⊆ insert q side ∧ cap.card = 4 ∧
      IsCapSet χ cap ∧ q ∈ cap) ∨
      ContainsStrongPolygonSet χ (insert q side) 6 := by
  have hinsertSub : insert q side ⊆ ambient := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hqAmbient
    · exact hsideSub hx
  have hinsertCard : (insert q side).card = 12 := by
    rw [Finset.card_insert_of_notMem hqSide, hsideCard]
  rcases containsCapFour_or_cupSix_or_strongSix_of_oneChange_card_ge_twelve
      (hone.mono hinsertSub) (by omega) with hcap | hcup | hstrong
  · obtain ⟨cap, hcapSub, hcapCard, hcapSet⟩ := hcap
    have hqCap : q ∈ cap := by
      by_contra hqCap
      apply hsideCap
      refine ⟨cap, ?_, hcapCard, hcapSet⟩
      intro x hx
      rcases Finset.mem_insert.mp (hcapSub hx) with hxq | hxSide
      · exact (hqCap (hxq ▸ hx)).elim
      · exact hxSide
    exact Or.inl ⟨cap, hcapSub, hcapCard, hcapSet, hqCap⟩
  · exact (hnoCup
      (FinsetPolygon.ContainsCupSet.mono hcup hinsertSub)).elim
  · exact Or.inr hstrong

/-- Witness-refined form of the eleven-plus-one dichotomy.  A strong six from
the adjoined set either already lies in the eleven-vertex side or uses the
adjoined vertex. -/
theorem adjoin_vertex_to_eleven_cap_free_side_refined
    {n : ℕ} {χ : TripleColoring n}
    {ambient side : Finset (Fin n)} {q : Fin n}
    (hsideSub : side ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hqSide : q ∉ side) (hsideCard : side.card = 11)
    (hsideCap : ¬ContainsCapSet χ side 4)
    (hone : OneChangeOn χ ambient)
    (hnoCup : ¬ContainsCupSet χ ambient 6) :
    (∃ cap : Finset (Fin n), cap ⊆ insert q side ∧ cap.card = 4 ∧
      IsCapSet χ cap ∧ q ∈ cap) ∨
    ContainsStrongPolygonSet χ side 6 ∨
    (∃ polygon : Finset (Fin n), polygon ⊆ insert q side ∧
      polygon.card = 6 ∧ IsStrongPolygonSet χ polygon ∧ q ∈ polygon) := by
  rcases adjoin_vertex_to_eleven_cap_free_side hsideSub hqAmbient hqSide
      hsideCard hsideCap hone hnoCup with hcap | hstrong
  · exact Or.inl hcap
  · obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hstrong
    by_cases hqPolygon : q ∈ polygon
    · exact Or.inr (Or.inr
        ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong, hqPolygon⟩)
    · apply Or.inr (Or.inl ?_)
      refine ⟨polygon, ?_, hpolygonCard, hpolygonStrong⟩
      intro x hx
      rcases Finset.mem_insert.mp (hpolygonSub hx) with hxq | hxSide
      · exact (hqPolygon (hxq ▸ hx)).elim
      · exact hxSide

/-- In the balanced `11+11` branch, every vertex on either side participates
in a crossing four-cap through the opposite side or activates a strong six in
the opposite side plus that vertex. -/
theorem eleven_eleven_vertex_dichotomies
    {n : ℕ} {χ : TripleColoring n}
    {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hleftCard : left.card = 11) (hrightCard : right.card = 11)
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6) :
    (∀ q ∈ right,
      (∃ cap : Finset (Fin n), cap ⊆ insert q left ∧ cap.card = 4 ∧
        IsCapSet χ cap ∧ q ∈ cap) ∨
        ContainsStrongPolygonSet χ (insert q left) 6) ∧
    (∀ q ∈ left,
      (∃ cap : Finset (Fin n), cap ⊆ insert q right ∧ cap.card = 4 ∧
        IsCapSet χ cap ∧ q ∈ cap) ∨
        ContainsStrongPolygonSet χ (insert q right) 6) := by
  constructor
  · intro q hqRight
    apply adjoin_vertex_to_eleven_cap_free_side
      Finset.subset_union_left (Finset.mem_union_right left hqRight)
      (fun hqLeft ↦ Finset.disjoint_left.mp hdisjoint hqLeft hqRight)
      hleftCard hleftCap hone hnoCup
  · intro q hqLeft
    apply adjoin_vertex_to_eleven_cap_free_side
      Finset.subset_union_right (Finset.mem_union_left right hqLeft)
      (fun hqRight ↦ Finset.disjoint_left.mp hdisjoint hqLeft hqRight)
      hrightCard hrightCap hone hnoCup

/-- Every witness in an eleven-plus-one activation genuinely uses the
adjoined vertex. -/
def HasAdjoinedCapOrStrongSixThrough {n : ℕ} (χ : TripleColoring n)
    (side : Finset (Fin n)) (q : Fin n) : Prop :=
  (∃ cap : Finset (Fin n), cap ⊆ insert q side ∧ cap.card = 4 ∧
    IsCapSet χ cap ∧ q ∈ cap) ∨
  (∃ polygon : Finset (Fin n), polygon ⊆ insert q side ∧
    polygon.card = 6 ∧ IsStrongPolygonSet χ polygon ∧ q ∈ polygon)

/-- The three side vertices left after removing the adjoined vertex from a
through four-cap. -/
def HasAdjoinedCapResidue {n : ℕ} (χ : TripleColoring n)
    (side : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ base : Finset (Fin n), base ⊆ side ∧ base.card = 3 ∧
    IsCapSet χ (insert q base)

/-- The five side vertices left after removing the adjoined vertex from a
through strong six-set. -/
def HasAdjoinedStrongSixResidue {n : ℕ} (χ : TripleColoring n)
    (side : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ base : Finset (Fin n), base ⊆ side ∧ base.card = 5 ∧
    IsStrongPolygonSet χ (insert q base)

/-- When the adjoined vertex is external to the side, through-witnesses are
equivalent to exact three- or five-vertex residues contained in that side. -/
theorem hasAdjoinedCapOrStrongSixThrough_iff_residue
    {n : ℕ} {χ : TripleColoring n} {side : Finset (Fin n)} {q : Fin n}
    (hqSide : q ∉ side) :
    HasAdjoinedCapOrStrongSixThrough χ side q ↔
      HasAdjoinedCapResidue χ side q ∨
        HasAdjoinedStrongSixResidue χ side q := by
  constructor
  · rintro (⟨cap, hcapSub, hcapCard, hcapSet, hqCap⟩ |
      ⟨polygon, hpolygonSub, hpolygonCard, hpolygonSet, hqPolygon⟩)
    · apply Or.inl
      refine ⟨cap.erase q, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp
            (hcapSub (Finset.mem_of_mem_erase hx)) with rfl | hxSide
        · exact (Finset.ne_of_mem_erase hx rfl).elim
        · exact hxSide
      · rw [Finset.card_erase_of_mem hqCap, hcapCard]
      · simpa [Finset.insert_erase hqCap] using hcapSet
    · apply Or.inr
      refine ⟨polygon.erase q, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp
            (hpolygonSub (Finset.mem_of_mem_erase hx)) with rfl | hxSide
        · exact (Finset.ne_of_mem_erase hx rfl).elim
        · exact hxSide
      · rw [Finset.card_erase_of_mem hqPolygon, hpolygonCard]
      · simpa [Finset.insert_erase hqPolygon] using hpolygonSet
  · rintro (⟨base, hbaseSub, hbaseCard, hcapSet⟩ |
      ⟨base, hbaseSub, hbaseCard, hpolygonSet⟩)
    · apply Or.inl
      have hqBase : q ∉ base := fun hqBase ↦ hqSide (hbaseSub hqBase)
      exact ⟨insert q base, Finset.insert_subset_insert q hbaseSub,
        by simp [Finset.card_insert_of_notMem hqBase, hbaseCard],
        hcapSet, Finset.mem_insert_self q base⟩
    · apply Or.inr
      have hqBase : q ∉ base := fun hqBase ↦ hqSide (hbaseSub hqBase)
      exact ⟨insert q base, Finset.insert_subset_insert q hbaseSub,
        by simp [Finset.card_insert_of_notMem hqBase, hbaseCard],
        hpolygonSet, Finset.mem_insert_self q base⟩

/-- If neither eleven-vertex side already contains a strong six, every vertex
activates a through-witness on the opposite side. -/
theorem eleven_eleven_has_through_witnesses_of_no_internal_strongSix
    {n : ℕ} {χ : TripleColoring n}
    {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hleftCard : left.card = 11) (hrightCard : right.card = 11)
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6)
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6) :
    (∀ q ∈ right, HasAdjoinedCapOrStrongSixThrough χ left q) ∧
      (∀ q ∈ left, HasAdjoinedCapOrStrongSixThrough χ right q) := by
  constructor
  · intro q hqRight
    rcases adjoin_vertex_to_eleven_cap_free_side_refined
        Finset.subset_union_left (Finset.mem_union_right left hqRight)
        (fun hqLeft ↦ Finset.disjoint_left.mp hdisjoint hqLeft hqRight)
        hleftCard hleftCap hone hnoCup with hcap | hstrong | hthrough
    · exact Or.inl hcap
    · exact (hnoLeftStrong hstrong).elim
    · exact Or.inr hthrough
  · intro q hqLeft
    rcases adjoin_vertex_to_eleven_cap_free_side_refined
        Finset.subset_union_right (Finset.mem_union_left right hqLeft)
        (fun hqRight ↦ Finset.disjoint_left.mp hdisjoint hqLeft hqRight)
        hrightCard hrightCap hone hnoCup with hcap | hstrong | hthrough
    · exact Or.inl hcap
    · exact (hnoRightStrong hstrong).elim
    · exact Or.inr hthrough

/-- Residue form of the balanced activation theorem: every vertex selects
either three or five vertices on the opposite side which, after reinserting
it, form the required cap or strong polygon. -/
theorem eleven_eleven_has_residue_witnesses_of_no_internal_strongSix
    {n : ℕ} {χ : TripleColoring n}
    {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hleftCard : left.card = 11) (hrightCard : right.card = 11)
    (hleftCap : ¬ContainsCapSet χ left 4)
    (hrightCap : ¬ContainsCapSet χ right 4)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6)
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6) :
    (∀ q ∈ right, HasAdjoinedCapResidue χ left q ∨
      HasAdjoinedStrongSixResidue χ left q) ∧
    (∀ q ∈ left, HasAdjoinedCapResidue χ right q ∨
      HasAdjoinedStrongSixResidue χ right q) := by
  have hthrough :=
    eleven_eleven_has_through_witnesses_of_no_internal_strongSix
      hdisjoint hleftCard hrightCard hleftCap hrightCap hone hnoCup
      hnoLeftStrong hnoRightStrong
  constructor
  · intro q hqRight
    exact (hasAdjoinedCapOrStrongSixThrough_iff_residue
      (fun hqLeft ↦ Finset.disjoint_left.mp hdisjoint hqLeft hqRight)).mp
      (hthrough.1 q hqRight)
  · intro q hqLeft
    exact (hasAdjoinedCapOrStrongSixThrough_iff_residue
      (fun hqRight ↦ Finset.disjoint_left.mp hdisjoint hqLeft hqRight)).mp
      (hthrough.2 q hqLeft)

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

/-- Finite-codomain form of the right-side obstruction: each opposite vertex
realizes at least one of the five explicitly indexed anomaly classes. -/
theorem right_side_has_finite_anomaly_classes_from_left_strongSix
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hpolygonSub : polygon ⊆ left) (hpolygonCard : polygon.card = 6)
    (hpolygonStrong : IsStrongPolygonSet χ polygon)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) 7) :
    ∀ q ∈ right, ∃ c : RightEndpointAnomalyClass,
      RealizesRightEndpointAnomalyClass χ polygon hpolygonCard q c := by
  have hfailures :=
    right_side_has_rightEndpoint_failures_from_left_strongSix
      hdisjoint horder hpolygonSub hpolygonCard hpolygonStrong hnoStrong
  intro q hqRight
  exact rightEndpoint_failure_has_finite_class hpolygonCard hpolygonStrong
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

/-- Refined balanced branch after internal strong-six witnesses have been
redirected to the endpoint branch. Every remaining vertex carries a cap-four
or strong-six witness through itself on the opposite eleven-point side. -/
def TwoCapFreeSidesElevenElevenThroughBranch567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      left.card = 11 → right.card = 11 →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      ¬ContainsStrongPolygonSet χ left 6 →
      ¬ContainsStrongPolygonSet χ right 6 →
      (∀ q ∈ right, HasAdjoinedCapOrStrongSixThrough χ left q) →
      (∀ q ∈ left, HasAdjoinedCapOrStrongSixThrough χ right q) →
      ContainsCapSet χ (left ∪ right) 5 ∨
        ContainsCupSet χ (left ∪ right) 6 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 7

/-- Incidence-normalized balanced branch. Each through-cap contributes a
three-subset of the opposite side, and each through-strong-six contributes a
five-subset. -/
def TwoCapFreeSidesElevenElevenResidueBranch567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      left.card = 11 → right.card = 11 →
      ¬ContainsCapSet χ left 4 → ¬ContainsCapSet χ right 4 →
      OneChangeOn χ (left ∪ right) →
      ¬ContainsStrongPolygonSet χ left 6 →
      ¬ContainsStrongPolygonSet χ right 6 →
      (∀ q ∈ right, HasAdjoinedCapResidue χ left q ∨
        HasAdjoinedStrongSixResidue χ left q) →
      (∀ q ∈ left, HasAdjoinedCapResidue χ right q ∨
        HasAdjoinedStrongSixResidue χ right q) →
      ContainsCapSet χ (left ∪ right) 5 ∨
        ContainsCupSet χ (left ∪ right) 6 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 7

/-- The exact residue-incidence branch proves the earlier through-witness
branch. -/
theorem twoCapFreeSidesElevenElevenThroughBranch567_of_residueBranch
    (hresidue : TwoCapFreeSidesElevenElevenResidueBranch567) :
    TwoCapFreeSidesElevenElevenThroughBranch567 := by
  intro n χ left right hdisjoint horder hleftCard hrightCard
    hleftCap hrightCap hone hnoLeftStrong hnoRightStrong
    hleftThrough hrightThrough
  apply hresidue hdisjoint horder hleftCard hrightCard hleftCap hrightCap
    hone hnoLeftStrong hnoRightStrong
  · intro q hqRight
    exact (hasAdjoinedCapOrStrongSixThrough_iff_residue
      (fun hqLeft ↦ Finset.disjoint_left.mp hdisjoint hqLeft hqRight)).mp
      (hleftThrough q hqRight)
  · intro q hqLeft
    exact (hasAdjoinedCapOrStrongSixThrough_iff_residue
      (fun hqRight ↦ Finset.disjoint_left.mp hdisjoint hqLeft hqRight)).mp
      (hrightThrough q hqLeft)

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

/-- The opaque balanced branch follows from the endpoint branch plus the
through-witness refinement. -/
theorem twoCapFreeSidesElevenElevenBranch567_of_endpoint_and_through
    (hendpoint : TwoCapFreeSidesEndpointObstructedStrongSixBranch567)
    (hthrough : TwoCapFreeSidesElevenElevenThroughBranch567) :
    TwoCapFreeSidesElevenElevenBranch567 := by
  intro n χ left right hdisjoint horder hleftCard hrightCard
    hleftCap hrightCap hone
  by_cases hcap : ContainsCapSet χ (left ∪ right) 5
  · exact Or.inl hcap
  by_cases hcup : ContainsCupSet χ (left ∪ right) 6
  · exact Or.inr (Or.inl hcup)
  by_cases hstrongSeven : ContainsStrongPolygonSet χ (left ∪ right) 7
  · exact Or.inr (Or.inr hstrongSeven)
  by_cases hleftStrong : ContainsStrongPolygonSet χ left 6
  · obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hleftStrong
    have hfailures :=
      right_side_has_rightEndpoint_failures_from_left_strongSix
        hdisjoint horder hpolygonSub hpolygonCard hpolygonStrong hstrongSeven
    have hbound := hendpoint hdisjoint horder hleftCap hrightCap hone
      (by omega) (by omega) (by omega) (by omega)
      hcap hcup hstrongSeven hpolygonCard hpolygonStrong
      (Or.inl ⟨hpolygonSub, hfailures⟩)
    omega
  by_cases hrightStrong : ContainsStrongPolygonSet χ right 6
  · obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hrightStrong
    have hfailures :=
      left_side_has_leftEndpoint_failures_from_right_strongSix
        hdisjoint horder hpolygonSub hpolygonCard hpolygonStrong hstrongSeven
    have hbound := hendpoint hdisjoint horder hleftCap hrightCap hone
      (by omega) (by omega) (by omega) (by omega)
      hcap hcup hstrongSeven hpolygonCard hpolygonStrong
      (Or.inr ⟨hpolygonSub, hfailures⟩)
    omega
  have hwitnesses :=
    eleven_eleven_has_through_witnesses_of_no_internal_strongSix
      hdisjoint hleftCard hrightCard hleftCap hrightCap hone hcup
      hleftStrong hrightStrong
  exact hthrough hdisjoint horder hleftCard hrightCard hleftCap hrightCap
    hone hleftStrong hrightStrong hwitnesses.1 hwitnesses.2

/-- Final current reduction: proving the endpoint-obstructed branch and the
balanced through-witness branch proves the complete local `(5,6,7)` bound. -/
theorem twoCapFreeSidesBound567_of_endpointBranch_and_throughBranch
    (hendpoint : TwoCapFreeSidesEndpointObstructedStrongSixBranch567)
    (hthrough : TwoCapFreeSidesElevenElevenThroughBranch567) :
    TwoCapFreeSidesBound567 :=
  twoCapFreeSidesBound567_of_endpointBranch_and_elevenEleven hendpoint
    (twoCapFreeSidesElevenElevenBranch567_of_endpoint_and_through
      hendpoint hthrough)

/-- Incidence-normalized final reduction: the endpoint branch plus the exact
three-/five-residue balanced branch proves the complete local bound. -/
theorem twoCapFreeSidesBound567_of_endpointBranch_and_residueBranch
    (hendpoint : TwoCapFreeSidesEndpointObstructedStrongSixBranch567)
    (hresidue : TwoCapFreeSidesElevenElevenResidueBranch567) :
    TwoCapFreeSidesBound567 :=
  twoCapFreeSidesBound567_of_endpointBranch_and_throughBranch hendpoint
    (twoCapFreeSidesElevenElevenThroughBranch567_of_residueBranch hresidue)

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
