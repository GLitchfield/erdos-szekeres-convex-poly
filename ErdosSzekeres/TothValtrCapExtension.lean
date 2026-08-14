module

public import ErdosSzekeres.TothValtrProjective

@[expose] public section

/-!
# Extending a cap through the Tóth--Valtr anchor

The projective normalization orders the remaining points by their rays from
the selected hull vertex.  Algebraically, every increasing pair `p i, p j`
then makes a negative turn with the anchor.  This file isolates the finite
convexity argument showing that a cap gains the anchor as one extra vertex.
-/

namespace ErdosSzekeres

noncomputable section

/-- Four labeled points are in convex position when the four orientations in
their label order are all negative. -/
theorem inConvexPosition_four_of_all_orientation_neg
    (a b c d : Point 2)
    (habc : orientation a b c < 0)
    (habd : orientation a b d < 0)
    (hacd : orientation a c d < 0)
    (hbcd : orientation b c d < 0) :
    InConvexPosition {a, b, c, d} := by
  have hab : a ≠ b := by
    intro h
    subst b
    simp at habc
  have hac : a ≠ c := by
    intro h
    subst c
    simp at habc
  have had : a ≠ d := by
    intro h
    subst d
    simp at habd
  have hbc : b ≠ c := by
    intro h
    subst c
    simp at habc
  have hbd : b ≠ d := by
    intro h
    subst d
    simp at habd
  have hcd : c ≠ d := by
    intro h
    subst d
    simp at hacd
  rw [inConvexPosition_four_iff_no_mem_triangle a b c d
    hab hac had hbc hbd hcd]
  constructor
  · rw [mem_convexHull_triangle_iff_of_orientation_neg b c d a hbcd]
    intro h
    have hdba : 0 < orientation d b a := by
      rw [← orientation_cyclic d b a, orientation_swap]
      linarith
    linarith [h.2.2]
  constructor
  · rw [mem_convexHull_triangle_iff_of_orientation_neg a c d b hacd]
    intro h
    have hacb : 0 < orientation a c b := by
      rw [orientation_swap_last]
      linarith
    linarith [h.1]
  constructor
  · rw [mem_convexHull_triangle_iff_of_orientation_neg a b d c habd]
    intro h
    have hbdc : 0 < orientation b d c := by
      rw [orientation_swap_last]
      linarith
    linarith [h.2.1]
  · rw [mem_convexHull_triangle_iff_of_orientation_neg a b c d habc]
    intro h
    have hcad : 0 < orientation c a d := by
      rw [← orientation_cyclic c a d, orientation_swap_last]
      linarith
    linarith [h.2.2]

/-- If every increasing pair of a swept configuration makes a negative turn
with an external anchor, adjoining that anchor extends every cap by one
convex-position point. -/
theorem SweptConfiguration.inConvexPosition_insert_anchor_of_cap
    {n m : ℕ} (P : SweptConfiguration n) (anchor : Point 2)
    (hanchor : anchor ∉ P.pointFinset)
    (hpair : ∀ ⦃i j : Fin n⦄, i < j →
      orientation (P.point i) (P.point j) anchor < 0)
    (f : Fin m ↪o Fin n)
    (hcap : IsMonochromaticChain P.tripleColoring Turn.right f) :
    InConvexPosition (insert anchor (P.restrict f).pointFinset) := by
  classical
  let Q := P.restrict f
  have hQsubset : Q.pointFinset ⊆ P.pointFinset := by
    intro p hp
    simp only [Q, SweptConfiguration.pointFinset, Finset.mem_image,
      Finset.mem_univ, true_and, SweptConfiguration.restrict_point] at hp ⊢
    obtain ⟨i, rfl⟩ := hp
    exact ⟨f i, rfl⟩
  have hanchorQ : anchor ∉ Q.pointFinset := fun h => hanchor (hQsubset h)
  have hQpair : ∀ ⦃i j : Fin m⦄, i < j →
      orientation (Q.point i) (Q.point j) anchor < 0 := by
    intro i j hij
    exact hpair (f.strictMono hij)
  have hpairNe : ∀ ⦃p⦄, p ∈ Q.pointFinset → ∀ ⦃q⦄, q ∈ Q.pointFinset →
      p ≠ q → orientation p q anchor ≠ 0 := by
    intro p hp q hq hpq
    simp only [Q, SweptConfiguration.pointFinset, Finset.mem_image,
      Finset.mem_univ, true_and] at hp hq
    obtain ⟨i, rfl⟩ := hp
    obtain ⟨j, rfl⟩ := hq
    have hij : i ≠ j := fun h => hpq (congrArg Q.point h)
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact ne_of_lt (hQpair hij)
    · rw [orientation_swap]
      exact neg_ne_zero.mpr (ne_of_lt (hQpair hji))
  have hgeneral : InGeneralPosition (insert anchor Q.pointFinset) := by
    intro x hx y hy z hz hxy hxz hyz
    simp only [Finset.mem_insert] at hx hy hz
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · rcases hz with rfl | hz
        · exact (hxz rfl).elim
        · rw [← orientation_cyclic]
          exact hpairNe hy hz hyz
    · rcases hy with rfl | hy
      · rcases hz with rfl | hz
        · exact (hyz rfl).elim
        · rw [orientation_swap_last]
          exact neg_ne_zero.mpr (hpairNe hx hz hxz)
      · rcases hz with rfl | hz
        · exact hpairNe hx hy hxy
        · exact Q.pointFinset_generalPosition hx hy hz hxy hxz hyz
  have hcapStrong : IsStrongPolygon Q.tripleColoring := by
    rcases hcap with ⟨hf, hall⟩
    intro i j k l hij hjk hkl
    constructor
    · have hijk := hall hij hjk
      have hijl := hall hij (hjk.trans hkl)
      simpa [Q] using hijk.trans hijl.symm
    · have hikl := hall (hij.trans hjk) hkl
      have hjkl := hall hjk hkl
      simpa [Q] using hikl.trans hjkl.symm
  have hcapConvex : InConvexPosition Q.pointFinset :=
    Q.inConvexPosition_pointFinset_iff_isStrongPolygon.mpr hcapStrong
  apply (inConvexPosition_iff_four_subsets
    (insert anchor Q.pointFinset) hgeneral).2
  intro u hu hucard
  by_cases hau : anchor ∈ u
  · let v := u.erase anchor
    have hvsub : v ⊆ Q.pointFinset := by
      intro p hp
      have hpu : p ∈ u := (Finset.mem_erase.mp hp).2
      rcases Finset.mem_insert.mp (hu hpu) with hpa | hpQ
      · exact False.elim ((Finset.mem_erase.mp hp).1 hpa)
      · exact hpQ
    have hvcard : v.card = 3 := by
      rw [Finset.card_erase_of_mem hau]
      omega
    have hvimage : v ⊆ Finset.univ.image Q.point := by
      simpa [SweptConfiguration.pointFinset] using hvsub
    obtain ⟨w, hw⟩ := Finset.subset_univ_image_iff.mp hvimage
    have hwcard : w.card = 3 := by
      calc
        w.card = (w.image Q.point).card :=
          (Finset.card_image_of_injective w Q.point_injective).symm
        _ = v.card := congrArg Finset.card hw
        _ = 3 := hvcard
    let g : Fin 3 ↪o Fin m := w.orderEmbOfFin hwcard
    have h01 : g 0 < g 1 := g.strictMono (by decide)
    have h12 : g 1 < g 2 := g.strictMono (by decide)
    have h02 : g 0 < g 2 := h01.trans h12
    have hpoints : ({Q.point (g 0), Q.point (g 1), Q.point (g 2)} :
        Finset (Point 2)) = v := by
      have hfin3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      calc
        ({Q.point (g 0), Q.point (g 1), Q.point (g 2)} :
            Finset (Point 2)) = Finset.univ.image (Q.point ∘ g) := by
          rw [hfin3]
          simp
        _ = (Finset.univ.image g).image Q.point := by
          rw [Finset.image_image]
        _ = w.image Q.point := by rw [Finset.image_orderEmbOfFin_univ]
        _ = v := hw
    have huEq :
        ({Q.point (g 0), Q.point (g 1), Q.point (g 2), anchor} :
          Finset (Point 2)) = u := by
      rw [show ({Q.point (g 0), Q.point (g 1), Q.point (g 2), anchor} :
        Finset (Point 2)) = insert anchor v by
          rw [← hpoints]
          ext p
          simp [or_comm, or_left_comm]]
      exact Finset.insert_erase hau
    rw [← huEq]
    apply inConvexPosition_four_of_all_orientation_neg
    · have hturn := hcap.2 h01 h12
      exact (Q.turn_eq_right_iff (g 0) (g 1) (g 2) h01 h12).mp <| by
        simpa [Q] using hturn
    · exact hQpair h01
    · exact hQpair h02
    · exact hQpair h12
  · apply hcapConvex.mono
    intro p hp
    rcases Finset.mem_insert.mp (hu hp) with hpa | hpQ
    · exact False.elim (hau (hpa ▸ hp))
    · exact hpQ

end

end ErdosSzekeres

end
