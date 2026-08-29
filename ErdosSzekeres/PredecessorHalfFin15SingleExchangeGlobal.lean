module

public import ErdosSzekeres.PredecessorHalfFin15SingleExchange

@[expose] public section

/-!
# The complete-system single-exchange obstruction

For an exact one-for-one blocker exchange, maximality supplies a three-way
strong-five witness for every one of the three common blocker points.  The
lemma below packages all three trichotomies together with a third member of
the eight-vertex exterior system.  The frozen raw contradiction still needs a
color bridge from that third extension into one of the trichotomy witnesses.
-/

namespace ErdosSzekeres

/-- The forced witness alternatives after deleting one support point and
adjoining a pair of exterior vertices. -/
def Fin15SingleExchangeCandidateTrichotomy
    (chi : TripleColoring 15) (support : Finset (Fin 15))
    (q r c : Fin 15) : Prop :=
  (∃ residue : Finset (Fin 15),
    residue ⊆ support.erase c ∧ residue.card = 3 ∧
      IsStrongPolygonSet chi (insert q (insert r residue))) ∨
  (∃ base : Finset (Fin 15),
    base ⊆ support.erase c ∧ base.card = 4 ∧
      IsStrongPolygonSet chi (insert q base)) ∨
  ∃ base : Finset (Fin 15),
    base ⊆ support.erase c ∧ base.card = 4 ∧
      IsStrongPolygonSet chi (insert r base)

/-- The exact single-exchange hypotheses expose all three common-point
trichotomies while retaining a third exterior strong extension. -/
theorem fin15ExteriorSystem_singleExchange_third_trichotomies
    (chi : TripleColoring 15)
    (_hone : OneChangeOn chi Finset.univ)
    (_hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    {support : Finset (Fin 15)}
    {anchor : Fin 15 → Finset (Fin 15)}
    (hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (hsupportCard : support.card = 7)
    (houtsideCard : (Finset.univ \ support).card = 8)
    (hanchorData : ∀ vertex ∈ Finset.univ \ support,
      anchor vertex ⊆ support ∧
        (anchor vertex).card = 4 ∧
        IsStrongPolygonSet chi (insert vertex (anchor vertex)))
    {q r : Fin 15}
    (hq : q ∈ Finset.univ \ support)
    (hr : r ∈ Finset.univ \ support)
    (hqr : q ≠ r)
    (hinter : (anchor q ∩ anchor r).card = 3)
    (hqdiff : (anchor q \ anchor r).card = 1)
    (hrdiff : (anchor r \ anchor q).card = 1) :
    ∃ a b : Fin 15,
      a ≠ b ∧
      anchor q = insert a (anchor q ∩ anchor r) ∧
      anchor r = insert b (anchor q ∩ anchor r) ∧
      ∃ s ∈ Finset.univ \ support,
        s ≠ q ∧ s ≠ r ∧
          anchor s ⊆ support ∧
          (anchor s).card = 4 ∧
          IsStrongPolygonSet chi (insert s (anchor s)) ∧
          (anchor q ∩ anchor r).card = 3 ∧
          ∀ c ∈ anchor q ∩ anchor r,
            Fin15SingleExchangeCandidateTrichotomy chi support q r c ∧
            Fin15SingleExchangeCandidateTrichotomy chi support q s c ∧
            Fin15SingleExchangeCandidateTrichotomy chi support r s c := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hqdiff
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hrdiff
  have haMem : a ∈ anchor q \ anchor r := by rw [ha]; simp
  have hbMem : b ∈ anchor r \ anchor q := by rw [hb]; simp
  have haData := Finset.mem_sdiff.mp haMem
  have hbData := Finset.mem_sdiff.mp hbMem
  have hab : a ≠ b := by
    intro hab
    subst b
    exact haData.2 hbData.1
  have hanchorQ : anchor q = insert a (anchor q ∩ anchor r) := by
    calc
      anchor q = (anchor q \ anchor r) ∪ (anchor q ∩ anchor r) :=
        (Finset.sdiff_union_inter _ _).symm
      _ = insert a (anchor q ∩ anchor r) := by simp [ha]
  have hanchorR : anchor r = insert b (anchor q ∩ anchor r) := by
    calc
      anchor r = (anchor r \ anchor q) ∪ (anchor r ∩ anchor q) :=
        (Finset.sdiff_union_inter _ _).symm
      _ = insert b (anchor q ∩ anchor r) := by simp [hb, Finset.inter_comm]
  let outside : Finset (Fin 15) := Finset.univ \ support
  have hrErase : r ∈ outside.erase q := by
    exact Finset.mem_erase.mpr ⟨hqr.symm, by simpa [outside] using hr⟩
  have heraseCard : ((outside.erase q).erase r).card = 6 := by
    rw [Finset.card_erase_of_mem hrErase,
      Finset.card_erase_of_mem (by simpa [outside] using hq)]
    simpa [outside] using houtsideCard
  obtain ⟨s, hs⟩ : ((outside.erase q).erase r).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hsData := Finset.mem_erase.mp hs
  have hsOutsideData := Finset.mem_erase.mp hsData.2
  have hsOutside : s ∈ Finset.univ \ support := by
    simpa [outside] using hsOutsideData.2
  have hqData := hanchorData q hq
  have hsAnchorData := hanchorData s hsOutside
  refine ⟨a, b, hab, hanchorQ, hanchorR, s, hsOutside, hsOutsideData.1, hsData.1,
    hsAnchorData.1, hsAnchorData.2.1, hsAnchorData.2.2, hinter, ?_⟩
  intro c hc
  have hcSupport : c ∈ support := hqData.1 (Finset.mem_inter.mp hc).1
  exact ⟨fin15_singleExchange_common_point_anchor_trichotomy
      chi hmaximum hsupportCard hq hr hqr hqData.1 hc,
    fin15_singleExchange_candidate_anchor_trichotomy
      chi hmaximum hsupportCard hq hsOutside hsOutsideData.1.symm hcSupport,
    fin15_singleExchange_candidate_anchor_trichotomy
      chi hmaximum hsupportCard hr hsOutside hsData.1.symm hcSupport⟩

end ErdosSzekeres

end
