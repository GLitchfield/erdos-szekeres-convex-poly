module

public import ErdosSzekeres.TothValtrNormalization

@[expose] public section

/-!
# Constructing the Tóth--Valtr frame

This file assembles the explicit normalization, the orientation-sign transfer,
and the cap-anchor lemma into `TothValtrFrame`.  It is the geometric producer
used by the final quantitative upper bound.
-/

namespace ErdosSzekeres

noncomputable section

/-- Reindex a configuration by the definitionally required cardinality of its
point finset. -/
def SweptConfiguration.canonicalReindex
    {n : ℕ} (C : SweptConfiguration n) :
    SweptConfiguration C.pointFinset.card :=
  C.restrict (Fin.castOrderIso C.card_pointFinset).toOrderEmbedding

/-- A swept configuration presents its own point finset without an additional
geometric shear. -/
def SweptConfiguration.canonicalPresentation
    {n : ℕ} (C : SweptConfiguration n) : SweptPresentation C.pointFinset := by
  let e : Fin C.pointFinset.card ≃o Fin n := Fin.castOrderIso C.card_pointFinset
  let enumeration : Fin C.pointFinset.card ≃ C.pointFinset := Equiv.ofBijective
    (fun i => ⟨C.point (e i), C.mem_pointFinset (e i)⟩) ⟨by
      intro i j h
      exact e.injective (C.point_injective (congrArg Subtype.val h)), by
      intro p
      have hp := p.property
      simp only [SweptConfiguration.pointFinset, Finset.mem_image,
        Finset.mem_univ, true_and] at hp
      obtain ⟨j, hj⟩ := hp
      obtain ⟨i, hi⟩ := e.surjective j
      refine ⟨i, ?_⟩
      apply Subtype.ext
      change C.point (e i) = (p : Point 2)
      rw [hi]
      exact hj⟩
  exact
    { parameter := 0
      enumeration := enumeration
      configuration := C.canonicalReindex
      point_eq_shear := by
        intro i
        change C.point (e i) = shear 0 (C.point (e i))
        funext j
        fin_cases j <;> simp [shear, sweepCoordinate] }

/-- The canonical presentation retains the original swept configuration
up to the cardinality cast. -/
theorem SweptConfiguration.canonicalPresentation_configuration
    {n : ℕ} (C : SweptConfiguration n) :
    C.canonicalPresentation.configuration = C.canonicalReindex := rfl

/-- Reindexing does not change the underlying point finset. -/
theorem SweptConfiguration.canonicalReindex_pointFinset
    {n : ℕ} (C : SweptConfiguration n) :
    C.canonicalReindex.pointFinset = C.pointFinset := by
  ext p
  constructor
  · intro hp
    simp only [canonicalReindex, SweptConfiguration.pointFinset,
      Finset.mem_image, Finset.mem_univ, true_and,
      SweptConfiguration.restrict_point] at hp ⊢
    obtain ⟨i, rfl⟩ := hp
    exact ⟨(Fin.castOrderIso C.card_pointFinset) i, rfl⟩
  · intro hp
    simp only [canonicalReindex, SweptConfiguration.pointFinset,
      Finset.mem_image, Finset.mem_univ, true_and,
      SweptConfiguration.restrict_point] at hp ⊢
    obtain ⟨j, rfl⟩ := hp
    obtain ⟨i, hi⟩ :=
      (Fin.castOrderIso C.card_pointFinset).surjective j
    exact ⟨i, congrArg C.point hi⟩

/-- Every nonempty finite general-position set has a Tóth--Valtr frame. -/
theorem exists_tothValtrFrame
    (s : Finset (Point 2)) (hs : s.Nonempty)
    (hgp : InGeneralPosition s) : TothValtrFrame s := by
  classical
  let R := Classical.choice (exists_sweptPresentation s hgp)
  let C := R.configuration
  have hn : 0 < s.card := Finset.card_pos.mpr hs
  let D := Classical.choice (C.exists_tothValtrNormalization hn)
  let Q := D.configuration
  let Qc := Q.canonicalReindex
  let z : Fin s.card := ⟨0, hn⟩
  let F : Point 2 → Point 2 := fun p =>
    tothValtrProjective D.delta (tothValtrQuarterTurnAt (C.point z) p)
  have hQsubsetImage : Q.pointFinset ⊆ C.pointFinset.image F := by
    intro p hp
    have hp' : p ∈ (C.pointFinset.erase (C.point z)).image F := by
      rw [← D.pointFinset_eq]
      exact hp
    exact Finset.image_mono F (Finset.erase_subset _ _) hp'
  have hQcPointFinset : Qc.pointFinset = Q.pointFinset := by
    exact Q.canonicalReindex_pointFinset
  have hQcSubsetImage : Qc.pointFinset ⊆ C.pointFinset.image F := by
    rw [hQcPointFinset]
    exact hQsubsetImage
  have hQcAnchorNot : (0 : Point 2) ∉ Qc.pointFinset := by
    rw [hQcPointFinset]
    exact D.anchor_not_mem
  have hQcPair : ∀ ⦃i j : Fin Q.pointFinset.card⦄, i < j →
      orientation (Qc.point i) (Qc.point j) 0 < 0 := by
    intro i j hij
    exact D.anchor_pair_neg <|
      (Fin.castOrderIso Q.card_pointFinset).strictMono hij
  have htransfer : ∀ {m : ℕ} {v : Finset (Point 2)},
      v ⊆ C.pointFinset.image F → v.card = m → InConvexPosition v →
        ContainsConvexSubset s m := by
    intro m v hvSub hvCard hvConvex
    obtain ⟨t, htSub, htImage⟩ := Finset.subset_image_iff.mp hvSub
    have htGp : InGeneralPosition t := C.pointFinset_generalPosition.mono htSub
    have htInj : Set.InjOn F t := by
      exact D.map_injective.mono htSub
    have htSigns : PreservesOrientationSignsOn F t := by
      intro a ha b hb c hc
      exact D.map_preserves_signs (htSub ha) (htSub hb) (htSub hc)
    have htConvex : InConvexPosition t := by
      apply (inConvexPosition_image_iff_of_preservesOrientationSignsOn
        htGp htInj htSigns).mp
      rwa [htImage]
    have htCard : t.card = m := by
      calc
        t.card = (t.image F).card :=
          (Finset.card_image_of_injOn htInj).symm
        _ = v.card := congrArg Finset.card htImage
        _ = m := hvCard
    have htSubShear : t ⊆ s.image (shearLinearEquiv R.parameter) := by
      simpa [C, R.configuration_pointFinset_eq_image_shear] using htSub
    obtain ⟨u, huSub, huImage⟩ := Finset.subset_image_iff.mp htSubShear
    have huCard : u.card = m := by
      calc
        u.card = (u.image (shearLinearEquiv R.parameter)).card :=
          (Finset.card_image_of_injective u
            (shearLinearEquiv R.parameter).injective).symm
        _ = t.card := congrArg Finset.card huImage
        _ = m := htCard
    have huConvex : InConvexPosition u := by
      apply (inConvexPosition_image_linearEquiv_iff
        (shearLinearEquiv R.parameter) u).mp
      rwa [huImage]
    exact ⟨u, huSub, huCard, huConvex⟩
  refine ⟨Q.pointFinset, ?_, Q.canonicalPresentation, ?_, ?_⟩
  · rw [Q.card_pointFinset]
    omega
  · intro m hcup
    obtain ⟨f, hf⟩ := hcup
    let V := Qc.restrict f
    have hstrong : IsStrongPolygon V.tripleColoring := by
      rcases hf with ⟨hfMono, hall⟩
      intro i j k l hij hjk hkl
      constructor
      · have hijk := hall hij hjk
        have hijl := hall hij (hjk.trans hkl)
        simpa [V] using hijk.trans hijl.symm
      · have hikl := hall (hij.trans hjk) hkl
        have hjkl := hall hjk hkl
        simpa [V] using hikl.trans hjkl.symm
    apply htransfer (v := V.pointFinset)
    · exact (by
        intro p hp
        exact hQcSubsetImage <| by
          simp only [V, SweptConfiguration.pointFinset, Finset.mem_image,
            Finset.mem_univ, true_and] at hp ⊢
          obtain ⟨i, rfl⟩ := hp
          exact ⟨f i, rfl⟩)
    · exact V.card_pointFinset
    · exact V.inConvexPosition_pointFinset_iff_isStrongPolygon.mpr hstrong
  · intro m hcap
    obtain ⟨f, hf⟩ := hcap
    let V := Qc.restrict f
    let v : Finset (Point 2) := insert 0 V.pointFinset
    have hvConvex : InConvexPosition v := by
      exact Qc.inConvexPosition_insert_anchor_of_cap 0 hQcAnchorNot
        hQcPair f hf
    have hVsubsetQ : V.pointFinset ⊆ Qc.pointFinset := by
      intro p hp
      simp only [V, SweptConfiguration.pointFinset, Finset.mem_image,
        Finset.mem_univ, true_and] at hp ⊢
      obtain ⟨i, rfl⟩ := hp
      exact ⟨f i, rfl⟩
    have hzeroImage : (0 : Point 2) ∈ C.pointFinset.image F := by
      apply Finset.mem_image.mpr
      refine ⟨C.point z, C.mem_pointFinset z, ?_⟩
      simp [F]
    have hvSub : v ⊆ C.pointFinset.image F := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hzeroImage
      · exact hQcSubsetImage (hVsubsetQ hp)
    have hzeroNotV : (0 : Point 2) ∉ V.pointFinset := fun h =>
      hQcAnchorNot (hVsubsetQ h)
    have hvCard : v.card = m + 1 := by
      rw [Finset.card_insert_of_notMem hzeroNotV, V.card_pointFinset]
    exact htransfer (v := v) hvSub hvCard hvConvex

end

end ErdosSzekeres

end
