module

public import ErdosSzekeres.StructuralChargingBoundary

@[expose] public section

/-!
# Interval infrastructure for structural charging

This file formalizes the finite interval-Helly step behind separated witness
charges. It records the one-vertex overlap loss explicitly, since separation
by itself does not yet force a cup, cap, or strong polygon.
-/

namespace ErdosSzekeres

/-- The integer endpoints of the open sweep span of a finite witness. -/
structure SweepInterval where
  lower : ℕ
  upper : ℕ
deriving DecidableEq

namespace SweepInterval

/-- A sweep cut lies inside the interval when it is strictly after the lower
endpoint and weakly before the upper endpoint. -/
def StraddlesCut (I : SweepInterval) (cut : ℕ) : Prop :=
  I.lower < cut ∧ cut ≤ I.upper

/-- The first interval is entirely before the second, with a shared boundary
allowed. -/
def WeaklyBefore (earlier later : SweepInterval) : Prop :=
  earlier.upper ≤ later.lower

/-- Finite interval Helly in the form needed by the separated-cap charge: if
a nonempty finite interval family has no common integer sweep cut, two member
intervals are weakly separated. -/
theorem exists_weaklyBefore_of_no_common_cut
    {family : Finset SweepInterval} (hfamily : family.Nonempty)
    (hno : ¬∃ cut : ℕ, ∀ I ∈ family, I.StraddlesCut cut) :
    ∃ earlier ∈ family, ∃ later ∈ family, earlier.WeaklyBefore later := by
  let lowers := family.image SweepInterval.lower
  let uppers := family.image SweepInterval.upper
  have hlowers : lowers.Nonempty := hfamily.image _
  have huppers : uppers.Nonempty := hfamily.image _
  let lowerMax := lowers.max' hlowers
  let upperMin := uppers.min' huppers
  by_cases hseparated : upperMin ≤ lowerMax
  · have hlowerMem : lowerMax ∈ lowers := Finset.max'_mem lowers hlowers
    have hupperMem : upperMin ∈ uppers := Finset.min'_mem uppers huppers
    obtain ⟨later, hlater, hlaterEq⟩ := Finset.mem_image.mp hlowerMem
    obtain ⟨earlier, hearlier, hearlierEq⟩ := Finset.mem_image.mp hupperMem
    refine ⟨earlier, hearlier, later, hlater, ?_⟩
    change earlier.upper ≤ later.lower
    simpa [upperMin, lowerMax, hearlierEq, hlaterEq] using hseparated
  · have hlt : lowerMax < upperMin := lt_of_not_ge hseparated
    exfalso
    apply hno
    refine ⟨lowerMax + 1, ?_⟩
    intro I hI
    constructor
    · have hmem : I.lower ∈ lowers := Finset.mem_image_of_mem _ hI
      have hle : I.lower ≤ lowerMax := Finset.le_max' lowers I.lower hmem
      omega
    · have hmem : I.upper ∈ uppers := Finset.mem_image_of_mem _ hI
      have hle : upperMin ≤ I.upper := Finset.min'_le uppers I.upper hmem
      omega

end SweepInterval

/-- Every vertex of `earlier` precedes every vertex of `later`. -/
def FinsetWeaklyBefore {n : ℕ} (earlier later : Finset (Fin n)) : Prop :=
  ∀ x ∈ earlier, ∀ y ∈ later, x ≤ y

/-- Two weakly separated witnesses can share at most their boundary vertex. -/
theorem FinsetWeaklyBefore.inter_card_le_one {n : ℕ}
    {earlier later : Finset (Fin n)} (h : FinsetWeaklyBefore earlier later) :
    (earlier ∩ later).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  have hx' := Finset.mem_inter.mp hx
  have hy' := Finset.mem_inter.mp hy
  exact le_antisymm (h x hx'.1 y hy'.2) (h y hy'.1 x hx'.2)

/-- Weakly separated witnesses retain their combined cardinality up to the
single boundary vertex that they may share. -/
theorem FinsetWeaklyBefore.card_add_le_union_add_one {n : ℕ}
    {earlier later : Finset (Fin n)} (h : FinsetWeaklyBefore earlier later) :
    earlier.card + later.card ≤ (earlier ∪ later).card + 1 := by
  have hinter := h.inter_card_le_one
  have hcard := Finset.card_union_add_card_inter earlier later
  omega

/-- The sweep interval spanned by a nonempty finite vertex set. -/
def finsetSweepInterval {n : ℕ} (s : Finset (Fin n)) (hs : s.Nonempty) : SweepInterval where
  lower := (s.min' hs).val
  upper := (s.max' hs).val

/-- Separation of witness spans implies pointwise separation of their vertex
sets. -/
theorem finsetWeaklyBefore_of_interval {n : ℕ}
    {earlier later : Finset (Fin n)} (hearlier : earlier.Nonempty)
    (hlater : later.Nonempty)
    (hspan : (finsetSweepInterval earlier hearlier).WeaklyBefore
      (finsetSweepInterval later hlater)) :
    FinsetWeaklyBefore earlier later := by
  intro x hx y hy
  exact (Finset.le_max' earlier x hx).trans
    (hspan.trans (Finset.min'_le later y hy))

/-- Interval Helly lifted from endpoint pairs to a finite family of nonempty
vertex witnesses. -/
theorem exists_finsetWeaklyBefore_of_no_common_cut {n : ℕ}
    {family : Finset (Finset (Fin n))} (hfamily : family.Nonempty)
    (hnonempty : ∀ witness ∈ family, witness.Nonempty)
    (hno : ¬∃ cut : ℕ, ∀ (witness : Finset (Fin n)) (hwitness : witness ∈ family),
      (finsetSweepInterval witness (hnonempty witness hwitness)).StraddlesCut cut) :
    ∃ earlier ∈ family, ∃ later ∈ family, FinsetWeaklyBefore earlier later := by
  classical
  let spans : Finset SweepInterval := family.attach.image fun witness ↦
    finsetSweepInterval witness.1 (hnonempty witness.1 witness.2)
  have hspans : spans.Nonempty := by
    obtain ⟨witness, hwitness⟩ := hfamily
    refine ⟨finsetSweepInterval witness (hnonempty witness hwitness), ?_⟩
    exact Finset.mem_image.mpr ⟨⟨witness, hwitness⟩, by simp⟩
  have hnoSpans : ¬∃ cut : ℕ, ∀ I ∈ spans, I.StraddlesCut cut := by
    rintro ⟨cut, hcut⟩
    apply hno
    refine ⟨cut, ?_⟩
    intro witness hwitness
    apply hcut
    exact Finset.mem_image.mpr ⟨⟨witness, hwitness⟩, by simp⟩
  obtain ⟨earlierI, hearlierI, laterI, hlaterI, hspan⟩ :=
    SweepInterval.exists_weaklyBefore_of_no_common_cut hspans hnoSpans
  obtain ⟨earlier, hearlierEq⟩ := Finset.mem_image.mp hearlierI
  obtain ⟨later, hlaterEq⟩ := Finset.mem_image.mp hlaterI
  refine ⟨earlier.1, earlier.2, later.1, later.2, ?_⟩
  apply finsetWeaklyBefore_of_interval
    (hnonempty earlier.1 earlier.2) (hnonempty later.1 later.2)
  simpa [spans, hearlierEq, hlaterEq] using hspan

/-- All cap witnesses of cardinality `a` contained in `s`. -/
noncomputable def capWitnesses {n : ℕ} (χ : TripleColoring n)
    (s : Finset (Fin n)) (a : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact s.powerset.filter fun cap ↦ cap.card = a ∧ IsCapSet χ cap

@[simp] theorem mem_capWitnesses {n a : ℕ} {χ : TripleColoring n}
    {s cap : Finset (Fin n)} :
    cap ∈ capWitnesses χ s a ↔ cap ⊆ s ∧ cap.card = a ∧ IsCapSet χ cap := by
  classical
  simp [capWitnesses]

/-- The executable witness family is nonempty exactly when a cap of that
cardinality exists. -/
theorem capWitnesses_nonempty_iff {n a : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} :
    (capWitnesses χ s a).Nonempty ↔ ContainsCapSet χ s a := by
  constructor
  · rintro ⟨cap, hcap⟩
    exact ⟨cap, (mem_capWitnesses.mp hcap).1, (mem_capWitnesses.mp hcap).2.1,
      (mem_capWitnesses.mp hcap).2.2⟩
  · rintro ⟨cap, hcapSub, hcapCard, hcap⟩
    exact ⟨cap, mem_capWitnesses.mpr ⟨hcapSub, hcapCard, hcap⟩⟩

/-- Cap-witness specialization of finite interval Helly. If cap witnesses do
not all cross one integer sweep cut, two cap witnesses are weakly separated. -/
theorem exists_separated_capWitnesses_of_no_common_cut {n a : ℕ}
    {χ : TripleColoring n} {s : Finset (Fin n)} (ha : 0 < a)
    (hexists : ContainsCapSet χ s a)
    (hno : ¬∃ cut : ℕ,
      ∀ (cap : Finset (Fin n)) (hcap : cap ∈ capWitnesses χ s a),
        (finsetSweepInterval cap (by
          have hcard := (mem_capWitnesses.mp hcap).2.1
          exact Finset.card_pos.mp (by omega))).StraddlesCut cut) :
    ∃ earlier ∈ capWitnesses χ s a,
      ∃ later ∈ capWitnesses χ s a, FinsetWeaklyBefore earlier later := by
  refine exists_finsetWeaklyBefore_of_no_common_cut
    (family := capWitnesses χ s a) ?_ ?_ ?_
  · exact capWitnesses_nonempty_iff.mpr hexists
  · intro cap hcap
    have hcard := (mem_capWitnesses.mp hcap).2.1
    exact Finset.card_pos.mp (by omega)
  · exact hno

/-- Two weakly separated four-vertex witnesses reserve at least seven ambient
vertices. The loss of one is sharp when they share their boundary vertex. -/
theorem separated_four_witnesses_reserve_seven {n : ℕ}
    {s earlier later : Finset (Fin n)} (hearlier : earlier ⊆ s)
    (hlater : later ⊆ s) (hearlierCard : earlier.card = 4)
    (hlaterCard : later.card = 4)
    (hbefore : FinsetWeaklyBefore earlier later) :
    7 + (s \ (earlier ∪ later)).card ≤ s.card := by
  have hoverlap := hbefore.card_add_le_union_add_one
  have hunionSub : earlier ∪ later ⊆ s :=
    Finset.union_subset hearlier hlater
  have hcard := Finset.card_sdiff_add_card_eq_card hunionSub
  omega

/-- The normalized nine-vertex statement selected for the symbolic `4+5`
proof attempt. Keeping the target as a proposition lets downstream theorems
state their exact dependency without treating computational evidence as a
proof. -/
def CupBlocks45FinNine : Prop :=
  ∀ χ : TripleColoring 9,
    IsCupSet χ {0, 1, 2, 3} → IsCupSet χ {4, 5, 6, 7, 8} →
      OneChangeOn χ Finset.univ →
      ContainsCapSet χ Finset.univ 4 ∨
        ContainsCupSet χ Finset.univ 6 ∨
        ContainsStrongPolygonSet χ Finset.univ 6

/-- The proposed local `(4,6,6)` cup-block gate, stated independently of its
still-open normalized nine-vertex proof and later transport step. -/
def CupBlocks45Force466 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ((left.card = 4 ∧ right.card = 5) ∨
        (left.card = 5 ∧ right.card = 4)) →
      IsCupSet χ left → IsCupSet χ right → OneChangeOn χ (left ∪ right) →
      ContainsCapSet χ (left ∪ right) 4 ∨
        ContainsCupSet χ (left ∪ right) 6 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 6

/-- The exact quantitative payoff of the proposed `4+5` gate: two ordered
cup blocks avoiding the `(4,6,6)` outcomes contain at most eight vertices in
total. -/
theorem cup_block_card_add_le_eight_of_cupBlocks45
    (hblocks : CupBlocks45Force466) {n : ℕ} {χ : TripleColoring n}
    {left right : Finset (Fin n)} (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoCap : ¬ContainsCapSet χ (left ∪ right) 4)
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) 6) :
    left.card + right.card ≤ 8 := by
  have hleftCard : left.card ≤ 5 := by
    by_contra hcard
    have hsix : 6 ≤ left.card := by omega
    obtain ⟨six, hsixSub, hsixCard⟩ := Finset.exists_subset_card_eq hsix
    apply hnoCup
    exact ⟨six, hsixSub.trans Finset.subset_union_left, hsixCard,
      FinsetPolygon.IsCupSet.mono hleft hsixSub⟩
  have hrightCard : right.card ≤ 5 := by
    by_contra hcard
    have hsix : 6 ≤ right.card := by omega
    obtain ⟨six, hsixSub, hsixCard⟩ := Finset.exists_subset_card_eq hsix
    apply hnoCup
    exact ⟨six, hsixSub.trans Finset.subset_union_right, hsixCard,
      FinsetPolygon.IsCupSet.mono hright hsixSub⟩
  by_contra hsum
  have hsizes : (4 ≤ left.card ∧ 5 ≤ right.card) ∨
      (5 ≤ left.card ∧ 4 ≤ right.card) := by
    omega
  rcases hsizes with hsizes | hsizes
  · obtain ⟨left', hleftSub, hleftCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.1
    obtain ⟨right', hrightSub, hrightCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.2
    have hout := hblocks (hdisjoint.mono hleftSub hrightSub)
      (fun x hx y hy ↦ horder x (hleftSub hx) y (hrightSub hy))
      (Or.inl ⟨hleftCard', hrightCard'⟩)
      (FinsetPolygon.IsCupSet.mono hleft hleftSub)
      (FinsetPolygon.IsCupSet.mono hright hrightSub)
      (hone.mono (Finset.union_subset_union hleftSub hrightSub))
    have hsub : left' ∪ right' ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    rcases hout with hcap | hcup | hstrong
    · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hsub)
    · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hsub)
    · exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hsub)
  · obtain ⟨left', hleftSub, hleftCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.1
    obtain ⟨right', hrightSub, hrightCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.2
    have hout := hblocks (hdisjoint.mono hleftSub hrightSub)
      (fun x hx y hy ↦ horder x (hleftSub hx) y (hrightSub hy))
      (Or.inr ⟨hleftCard', hrightCard'⟩)
      (FinsetPolygon.IsCupSet.mono hleft hleftSub)
      (FinsetPolygon.IsCupSet.mono hright hrightSub)
      (hone.mono (Finset.union_subset_union hleftSub hrightSub))
    have hsub : left' ∪ right' ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    rcases hout with hcap | hcup | hstrong
    · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hsub)
    · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hsub)
    · exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hsub)

/-- The sharpened quantitative descent target exposed by the separated-cap
countercontrol. It asks the vertices outside two ordered four-caps to pay at
most eight units, the remaining half of the diagonal row-four budget. -/
def SeparatedCapExteriorBoundAtSix : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {s earlier later : Finset (Fin n)},
    earlier ⊆ s → later ⊆ s → earlier.card = 4 → later.card = 4 →
      IsCapSet χ earlier → IsCapSet χ later →
      FinsetWeaklyBefore earlier later → OneChangeOn χ s →
      ¬ContainsCapSet χ s 5 → ¬ContainsCupSet χ s 6 →
      ¬ContainsStrongPolygonSet χ s 6 →
      (s \ (earlier ∪ later)).card ≤ 8

/-- The exterior bound has exactly the required numerical strength: it lowers
the parent cardinal estimate to the diagonal `k = 6` threshold 16. -/
theorem card_le_sixteen_of_separatedCapExteriorBound
    (hbound : SeparatedCapExteriorBoundAtSix)
    {n : ℕ} {χ : TripleColoring n} {s earlier later : Finset (Fin n)}
    (hearlierSub : earlier ⊆ s) (hlaterSub : later ⊆ s)
    (hearlierCard : earlier.card = 4) (hlaterCard : later.card = 4)
    (hearlierCap : IsCapSet χ earlier) (hlaterCap : IsCapSet χ later)
    (hbefore : FinsetWeaklyBefore earlier later) (hone : OneChangeOn χ s)
    (hnoCap : ¬ContainsCapSet χ s 5)
    (hnoCup : ¬ContainsCupSet χ s 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ s 6) :
    s.card ≤ 16 := by
  have hexterior := hbound hearlierSub hlaterSub hearlierCard hlaterCard
    hearlierCap hlaterCap hbefore hone hnoCap hnoCup hnoStrong
  have hunionSub : earlier ∪ later ⊆ s :=
    Finset.union_subset hearlierSub hlaterSub
  have hunionCard : (earlier ∪ later).card ≤ 8 := by
    calc
      (earlier ∪ later).card ≤ earlier.card + later.card :=
        Finset.card_union_le earlier later
      _ = 8 := by omega
  have hcard := Finset.card_sdiff_add_card_eq_card hunionSub
  omega

/-- Interval Helly and the exterior bound combine mechanically: whenever the
four-cap witness spans have no common cut, the ambient set is at most the
diagonal `k = 6` threshold. -/
theorem card_le_sixteen_of_no_common_four_cap_cut
    (hbound : SeparatedCapExteriorBoundAtSix)
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hexists : ContainsCapSet χ s 4)
    (hnoCut : ¬∃ cut : ℕ,
      ∀ (cap : Finset (Fin n)) (hcap : cap ∈ capWitnesses χ s 4),
        (finsetSweepInterval cap (by
          have hcard := (mem_capWitnesses.mp hcap).2.1
          exact Finset.card_pos.mp (by omega))).StraddlesCut cut)
    (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 5)
    (hnoCup : ¬ContainsCupSet χ s 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ s 6) :
    s.card ≤ 16 := by
  obtain ⟨earlier, hearlier, later, hlater, hbefore⟩ :=
    exists_separated_capWitnesses_of_no_common_cut (by omega) hexists hnoCut
  have hearlierData := mem_capWitnesses.mp hearlier
  have hlaterData := mem_capWitnesses.mp hlater
  exact card_le_sixteen_of_separatedCapExteriorBound hbound
    hearlierData.1 hlaterData.1 hearlierData.2.1 hlaterData.2.1
    hearlierData.2.2 hlaterData.2.2 hbefore hone hnoCap hnoCup hnoStrong

end ErdosSzekeres
