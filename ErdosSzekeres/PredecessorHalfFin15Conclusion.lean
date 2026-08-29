module

public import ErdosSzekeres.PredecessorHalfFin15Obstruction
public import ErdosSzekeres.StrongPredecessorBaseSix

@[expose] public section

/-!
# The conditional Fin15 predecessor-half consumer

This file isolates the exact consumer of the complete eight-exterior
compatibility theorem.  The hard compatibility producer remains an explicit
premise until the two global branches compile.
-/

namespace ErdosSzekeres

/-- Incompatibility of every complete seven-support/eight-exterior system
closes the exact eight-point Fin15 endpoint. -/
theorem predecessorFreeEightSubsetAtSixFinFifteen_of_exteriorSystemIncompatible
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hbad : ∀ (support : Finset (Fin 15))
        (anchor : Fin 15 → Finset (Fin 15)),
      IsMaximumPredecessorFreeSupport chi 6 support →
      support.card = 7 →
      (Finset.univ \ support).card = 8 →
      (∀ vertex ∈ Finset.univ \ support,
        anchor vertex ⊆ support ∧
          (anchor vertex).card = 4 ∧
          IsStrongPolygonSet chi (insert vertex (anchor vertex))) →
      False) :
    ∃ support : Finset (Fin 15),
      support.card = 8 ∧
        ¬ContainsStrongPolygonSet chi support 5 := by
  rcases predecessorHalfFin15_or_exactMaximumObstruction
      chi hone hnoStrong with hhalf |
      ⟨support, hmaximum, hsupportCard, houtsideCard, hblockers⟩
  · obtain ⟨large, hlargeFree, hlargeCard⟩ := hhalf
    have heightLe : 8 ≤ large.card := by omega
    obtain ⟨half, hhalfSub, hhalfCard⟩ :=
      Finset.exists_subset_card_eq heightLe
    refine ⟨half, hhalfCard, ?_⟩
    intro hcontains
    exact hlargeFree
      (FinsetPolygon.ContainsStrongPolygonSet.mono hcontains hhalfSub)
  · classical
    let outside : Finset (Fin 15) := Finset.univ \ support
    let anchor : Fin 15 → Finset (Fin 15) := fun vertex ↦
      if hvertex : vertex ∈ outside then
        Classical.choose (hblockers vertex hvertex)
      else ∅
    have hanchorData : ∀ vertex ∈ outside,
        anchor vertex ⊆ support ∧
          (anchor vertex).card = 4 ∧
          IsStrongPolygonSet chi (insert vertex (anchor vertex)) := by
      intro vertex hvertex
      simpa [anchor, hvertex] using
        Classical.choose_spec (hblockers vertex hvertex)
    exact (hbad support anchor hmaximum hsupportCard houtsideCard
      hanchorData).elim

/-- Transport any proof of the exact Fin15 endpoint through an increasing
fifteen-point window. -/
theorem predecessorFreeEightSubsetAtSixFinFifteenWindow_of_endpoint
    (hfin15 : ∀ (chi : TripleColoring 15),
      OneChangeOn chi Finset.univ →
      ¬ContainsStrongPolygonSet chi Finset.univ 6 →
      ∃ support : Finset (Fin 15),
        support.card = 8 ∧
          ¬ContainsStrongPolygonSet chi support 5)
    {n : ℕ} (chi : TripleColoring n) (f : Fin 15 ↪o Fin n)
    (hone : OneChangeOn chi (Finset.univ.image f))
    (hnoStrong :
      ¬ContainsStrongPolygonSet chi (Finset.univ.image f) 6) :
    ∃ support : Finset (Fin n),
      support ⊆ Finset.univ.image f ∧
        support.card = 8 ∧
        ¬ContainsStrongPolygonSet chi support 5 := by
  have honeRestrict : OneChangeOn (chi.restrict f) Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    simpa [TripleColoring.restrict, OrderedTriple.map] using
      hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
        (by simp) (by simp) (by simp) (by simp)
  have hnoStrongRestrict :
      ¬ContainsStrongPolygonSet (chi.restrict f) Finset.univ 6 := by
    intro hstrong
    exact hnoStrong
      ((containsStrongPolygonSet_image_restrict_iff chi f Finset.univ).mp
        hstrong)
  obtain ⟨support, hcard, hfree⟩ :=
    hfin15 (chi.restrict f) honeRestrict hnoStrongRestrict
  refine ⟨support.image f,
    Finset.image_mono f (Finset.subset_univ support), ?_, ?_⟩
  · exact (Finset.card_image_of_injective support f.injective).trans hcard
  · intro hstrong
    exact hfree
      ((containsStrongPolygonSet_image_restrict_iff chi f support).mpr
        hstrong)

/-- The exact Fin15 endpoint, through an arbitrary fifteen-point window,
supplies the complete ambient-cardinality fifteen/sixteen middle producer. -/
theorem predecessorHalfSubsetAtSixMiddle_of_fin15Endpoint
    (hfin15 : ∀ (chi : TripleColoring 15),
      OneChangeOn chi Finset.univ →
      ¬ContainsStrongPolygonSet chi Finset.univ 6 →
      ∃ support : Finset (Fin 15),
        support.card = 8 ∧
          ¬ContainsStrongPolygonSet chi support 5) :
    PredecessorHalfSubsetAtSixMiddle := by
  intro n chi hrealizable hnoStrong hnLower hnUpper
  let f : Fin 15 ↪o Fin n := Fin.castLEOrderEmb hnLower
  have honeWindow :
      OneChangeOn chi (Finset.univ.image f) := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hrealizable.oneChangeOn_univ hij hjk hkl
      (by simp) (by simp) (by simp) (by simp)
  have hnoStrongWindow :
      ¬ContainsStrongPolygonSet chi (Finset.univ.image f) 6 := by
    intro hstrong
    exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
        (Finset.subset_univ _))
  obtain ⟨support, _hsupportSub, hsupportCard, hsupportFree⟩ :=
    predecessorFreeEightSubsetAtSixFinFifteenWindow_of_endpoint
      hfin15 chi f honeWindow hnoStrongWindow
  exact ⟨support, hsupportFree, by omega⟩

end ErdosSzekeres

end
