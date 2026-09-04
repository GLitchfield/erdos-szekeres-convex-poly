module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 213. -/

theorem fin15Anchored_clause27264 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4568 chi ∧
      Fin15AnchoredAtom1601 chi ∧
      Fin15AnchoredAtom1603 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1608 chi ∧
      Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1601 Fin15AnchoredAtom1603 Fin15AnchoredAtom1605
    Fin15AnchoredAtom1608 Fin15AnchoredAtom1817 Fin15AnchoredAtom4568 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23568
  ] at hbad
  tauto

theorem fin15Anchored_clause27265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom4570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29712
  ] at hbad
  tauto

theorem fin15Anchored_clause27266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1605 Fin15AnchoredAtom4570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29712
  ] at hbad
  tauto

theorem fin15Anchored_clause27267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1606 Fin15AnchoredAtom4570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29712
  ] at hbad
  tauto

theorem fin15Anchored_clause27268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1610 Fin15AnchoredAtom4570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29712
  ] at hbad
  tauto

theorem fin15Anchored_clause27269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1819 Fin15AnchoredAtom4570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29712
  ] at hbad
  tauto

theorem fin15Anchored_clause27270 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom1605 Fin15AnchoredAtom1606
    Fin15AnchoredAtom1610 Fin15AnchoredAtom1819 Fin15AnchoredAtom4570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29712
  ] at hbad
  tauto

theorem fin15Anchored_clause27271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom4572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00992
  ] at hbad
  tauto

theorem fin15Anchored_clause27272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom4572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00992
  ] at hbad
  tauto

theorem fin15Anchored_clause27273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom4572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00992
  ] at hbad
  tauto

theorem fin15Anchored_clause27274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom4572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00992
  ] at hbad
  tauto

theorem fin15Anchored_clause27275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom4572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00992
  ] at hbad
  tauto

theorem fin15Anchored_clause27276 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4572 chi ∧
      Fin15AnchoredAtom1611 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1618 chi ∧
      Fin15AnchoredAtom1639 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom1612 Fin15AnchoredAtom1618
    Fin15AnchoredAtom1639 Fin15AnchoredAtom1695 Fin15AnchoredAtom4572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00992
  ] at hbad
  tauto

theorem fin15Anchored_clause27277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom4573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01504
  ] at hbad
  tauto

theorem fin15Anchored_clause27278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom4573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01504
  ] at hbad
  tauto

theorem fin15Anchored_clause27279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1619 Fin15AnchoredAtom4573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01504
  ] at hbad
  tauto

theorem fin15Anchored_clause27280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1640 Fin15AnchoredAtom4573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01504
  ] at hbad
  tauto

theorem fin15Anchored_clause27281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom4573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01504
  ] at hbad
  tauto

theorem fin15Anchored_clause27282 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4573 chi ∧
      Fin15AnchoredAtom1611 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1619 chi ∧
      Fin15AnchoredAtom1640 chi ∧
      Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom1613 Fin15AnchoredAtom1619
    Fin15AnchoredAtom1640 Fin15AnchoredAtom1696 Fin15AnchoredAtom4573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01504
  ] at hbad
  tauto

theorem fin15Anchored_clause27283 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom4575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04576
  ] at hbad
  tauto

theorem fin15Anchored_clause27284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom4575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04576
  ] at hbad
  tauto

theorem fin15Anchored_clause27285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1621 Fin15AnchoredAtom4575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04576
  ] at hbad
  tauto

theorem fin15Anchored_clause27286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1642 Fin15AnchoredAtom4575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04576
  ] at hbad
  tauto

theorem fin15Anchored_clause27287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1698 Fin15AnchoredAtom4575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04576
  ] at hbad
  tauto

theorem fin15Anchored_clause27288 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4575 chi ∧
      Fin15AnchoredAtom1611 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1621 chi ∧
      Fin15AnchoredAtom1642 chi ∧
      Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom1615 Fin15AnchoredAtom1621
    Fin15AnchoredAtom1642 Fin15AnchoredAtom1698 Fin15AnchoredAtom4575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04576
  ] at hbad
  tauto

theorem fin15Anchored_clause27289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom4576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08672
  ] at hbad
  tauto

theorem fin15Anchored_clause27290 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom4576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08672
  ] at hbad
  tauto

theorem fin15Anchored_clause27291 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1622 Fin15AnchoredAtom4576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08672
  ] at hbad
  tauto

theorem fin15Anchored_clause27292 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1643 Fin15AnchoredAtom4576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08672
  ] at hbad
  tauto

theorem fin15Anchored_clause27293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1699 Fin15AnchoredAtom4576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08672
  ] at hbad
  tauto

theorem fin15Anchored_clause27294 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4576 chi ∧
      Fin15AnchoredAtom1611 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1622 chi ∧
      Fin15AnchoredAtom1643 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom1616 Fin15AnchoredAtom1622
    Fin15AnchoredAtom1643 Fin15AnchoredAtom1699 Fin15AnchoredAtom4576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08672
  ] at hbad
  tauto

theorem fin15Anchored_clause27295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom4577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16864
  ] at hbad
  tauto

theorem fin15Anchored_clause27296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1617 Fin15AnchoredAtom4577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16864
  ] at hbad
  tauto

theorem fin15Anchored_clause27297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1623 Fin15AnchoredAtom4577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16864
  ] at hbad
  tauto

theorem fin15Anchored_clause27298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1644 Fin15AnchoredAtom4577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16864
  ] at hbad
  tauto

theorem fin15Anchored_clause27299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1700 Fin15AnchoredAtom4577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16864
  ] at hbad
  tauto

theorem fin15Anchored_clause27300 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4577 chi ∧
      Fin15AnchoredAtom1611 chi ∧
      Fin15AnchoredAtom1617 chi ∧
      Fin15AnchoredAtom1623 chi ∧
      Fin15AnchoredAtom1644 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom1617 Fin15AnchoredAtom1623
    Fin15AnchoredAtom1644 Fin15AnchoredAtom1700 Fin15AnchoredAtom4577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16864
  ] at hbad
  tauto

theorem fin15Anchored_clause27301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom4578 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01760
  ] at hbad
  tauto

theorem fin15Anchored_clause27302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom4578 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01760
  ] at hbad
  tauto

theorem fin15Anchored_clause27303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom4578 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01760
  ] at hbad
  tauto

theorem fin15Anchored_clause27304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom4578 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01760
  ] at hbad
  tauto

theorem fin15Anchored_clause27305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom4578 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01760
  ] at hbad
  tauto

theorem fin15Anchored_clause27306 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom1613 Fin15AnchoredAtom1624
    Fin15AnchoredAtom1645 Fin15AnchoredAtom1701 Fin15AnchoredAtom4578 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01760
  ] at hbad
  tauto

theorem fin15Anchored_clause27307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom4579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02784
  ] at hbad
  tauto

theorem fin15Anchored_clause27308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom1625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1625 Fin15AnchoredAtom4579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02784
  ] at hbad
  tauto

theorem fin15Anchored_clause27309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1646 Fin15AnchoredAtom4579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02784
  ] at hbad
  tauto

theorem fin15Anchored_clause27310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1702 Fin15AnchoredAtom4579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02784
  ] at hbad
  tauto

theorem fin15Anchored_clause27311 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4579 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1614 chi ∧
      Fin15AnchoredAtom1625 chi ∧
      Fin15AnchoredAtom1646 chi ∧
      Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom1614 Fin15AnchoredAtom1625
    Fin15AnchoredAtom1646 Fin15AnchoredAtom1702 Fin15AnchoredAtom4579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02784
  ] at hbad
  tauto

theorem fin15Anchored_clause27312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom4580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04832
  ] at hbad
  tauto

theorem fin15Anchored_clause27313 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom4580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04832
  ] at hbad
  tauto

theorem fin15Anchored_clause27314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom4580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04832
  ] at hbad
  tauto

theorem fin15Anchored_clause27315 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom4580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04832
  ] at hbad
  tauto

theorem fin15Anchored_clause27316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom4580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04832
  ] at hbad
  tauto

theorem fin15Anchored_clause27317 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom1615 Fin15AnchoredAtom1626
    Fin15AnchoredAtom1647 Fin15AnchoredAtom1703 Fin15AnchoredAtom4580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04832
  ] at hbad
  tauto

theorem fin15Anchored_clause27318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom4581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08928
  ] at hbad
  tauto

theorem fin15Anchored_clause27319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom4581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08928
  ] at hbad
  tauto

theorem fin15Anchored_clause27320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom4581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08928
  ] at hbad
  tauto

theorem fin15Anchored_clause27321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom4581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08928
  ] at hbad
  tauto

theorem fin15Anchored_clause27322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom4581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08928
  ] at hbad
  tauto

theorem fin15Anchored_clause27323 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4581 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1627 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom1616 Fin15AnchoredAtom1627
    Fin15AnchoredAtom1648 Fin15AnchoredAtom1704 Fin15AnchoredAtom4581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08928
  ] at hbad
  tauto

theorem fin15Anchored_clause27324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom4582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17120
  ] at hbad
  tauto

theorem fin15Anchored_clause27325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1617 Fin15AnchoredAtom4582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17120
  ] at hbad
  tauto

theorem fin15Anchored_clause27326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1628 Fin15AnchoredAtom4582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17120
  ] at hbad
  tauto

theorem fin15Anchored_clause27327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1649 Fin15AnchoredAtom4582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17120
  ] at hbad
  tauto

theorem fin15Anchored_clause27328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1705 Fin15AnchoredAtom4582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17120
  ] at hbad
  tauto

theorem fin15Anchored_clause27329 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4582 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1617 chi ∧
      Fin15AnchoredAtom1628 chi ∧
      Fin15AnchoredAtom1649 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom1617 Fin15AnchoredAtom1628
    Fin15AnchoredAtom1649 Fin15AnchoredAtom1705 Fin15AnchoredAtom4582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17120
  ] at hbad
  tauto

theorem fin15Anchored_clause27330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom4583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03296
  ] at hbad
  tauto

theorem fin15Anchored_clause27331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1614 Fin15AnchoredAtom4583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03296
  ] at hbad
  tauto

theorem fin15Anchored_clause27332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1629 Fin15AnchoredAtom4583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03296
  ] at hbad
  tauto

theorem fin15Anchored_clause27333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1650 Fin15AnchoredAtom4583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03296
  ] at hbad
  tauto

theorem fin15Anchored_clause27334 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1706 Fin15AnchoredAtom4583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03296
  ] at hbad
  tauto

theorem fin15Anchored_clause27335 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4583 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1614 chi ∧
      Fin15AnchoredAtom1629 chi ∧
      Fin15AnchoredAtom1650 chi ∧
      Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom1614 Fin15AnchoredAtom1629
    Fin15AnchoredAtom1650 Fin15AnchoredAtom1706 Fin15AnchoredAtom4583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03296
  ] at hbad
  tauto

theorem fin15Anchored_clause27336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom4584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05344
  ] at hbad
  tauto

theorem fin15Anchored_clause27337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom4584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05344
  ] at hbad
  tauto

theorem fin15Anchored_clause27338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom4584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05344
  ] at hbad
  tauto

theorem fin15Anchored_clause27339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom4584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05344
  ] at hbad
  tauto

theorem fin15Anchored_clause27340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom4584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05344
  ] at hbad
  tauto

theorem fin15Anchored_clause27341 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4584 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom1615 Fin15AnchoredAtom1630
    Fin15AnchoredAtom1651 Fin15AnchoredAtom1707 Fin15AnchoredAtom4584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05344
  ] at hbad
  tauto

theorem fin15Anchored_clause27342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom4585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09440
  ] at hbad
  tauto

theorem fin15Anchored_clause27343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom4585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09440
  ] at hbad
  tauto

theorem fin15Anchored_clause27344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom4585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09440
  ] at hbad
  tauto

theorem fin15Anchored_clause27345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom4585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09440
  ] at hbad
  tauto

theorem fin15Anchored_clause27346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom4585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09440
  ] at hbad
  tauto

theorem fin15Anchored_clause27347 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4585 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom1616 Fin15AnchoredAtom1631
    Fin15AnchoredAtom1652 Fin15AnchoredAtom1708 Fin15AnchoredAtom4585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09440
  ] at hbad
  tauto

theorem fin15Anchored_clause27348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom4586 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17632
  ] at hbad
  tauto

theorem fin15Anchored_clause27349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1617 Fin15AnchoredAtom4586 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17632
  ] at hbad
  tauto

theorem fin15Anchored_clause27350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1632 Fin15AnchoredAtom4586 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17632
  ] at hbad
  tauto

theorem fin15Anchored_clause27351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1653 Fin15AnchoredAtom4586 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17632
  ] at hbad
  tauto

theorem fin15Anchored_clause27352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1709 Fin15AnchoredAtom4586 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17632
  ] at hbad
  tauto

theorem fin15Anchored_clause27353 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4586 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1617 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1653 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom1617 Fin15AnchoredAtom1632
    Fin15AnchoredAtom1653 Fin15AnchoredAtom1709 Fin15AnchoredAtom4586 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17632
  ] at hbad
  tauto

theorem fin15Anchored_clause27354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4587 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom4587 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06368
  ] at hbad
  tauto

theorem fin15Anchored_clause27355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4587 chi ∧
      ¬Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1654 Fin15AnchoredAtom4587 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06368
  ] at hbad
  tauto

theorem fin15Anchored_clause27356 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4587 chi ∧
      Fin15AnchoredAtom1614 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1633 chi ∧
      Fin15AnchoredAtom1654 chi ∧
      Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1614 Fin15AnchoredAtom1615 Fin15AnchoredAtom1633
    Fin15AnchoredAtom1654 Fin15AnchoredAtom1710 Fin15AnchoredAtom4587 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06368
  ] at hbad
  tauto

theorem fin15Anchored_clause27357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4588 chi ∧
      ¬Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1614 Fin15AnchoredAtom4588 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10464
  ] at hbad
  tauto

theorem fin15Anchored_clause27358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4588 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom4588 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10464
  ] at hbad
  tauto

theorem fin15Anchored_clause27359 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4588 chi ∧
      Fin15AnchoredAtom1614 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1634 chi ∧
      Fin15AnchoredAtom1655 chi ∧
      Fin15AnchoredAtom1711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1614 Fin15AnchoredAtom1616 Fin15AnchoredAtom1634
    Fin15AnchoredAtom1655 Fin15AnchoredAtom1711 Fin15AnchoredAtom4588 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10464
  ] at hbad
  tauto

theorem fin15Anchored_clause27360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4589 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1617 Fin15AnchoredAtom4589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18656
  ] at hbad
  tauto

theorem fin15Anchored_clause27361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom4590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12512
  ] at hbad
  tauto

theorem fin15Anchored_clause27362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom4590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12512
  ] at hbad
  tauto

theorem fin15Anchored_clause27363 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom4590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12512
  ] at hbad
  tauto

theorem fin15Anchored_clause27364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom4590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12512
  ] at hbad
  tauto

theorem fin15Anchored_clause27365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom4590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12512
  ] at hbad
  tauto

theorem fin15Anchored_clause27366 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4590 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1657 chi ∧
      Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom1616 Fin15AnchoredAtom1636
    Fin15AnchoredAtom1657 Fin15AnchoredAtom1713 Fin15AnchoredAtom4590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12512
  ] at hbad
  tauto

theorem fin15Anchored_clause27367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom4591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20704
  ] at hbad
  tauto

theorem fin15Anchored_clause27368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1617 Fin15AnchoredAtom4591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20704
  ] at hbad
  tauto

theorem fin15Anchored_clause27369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1637 Fin15AnchoredAtom4591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20704
  ] at hbad
  tauto

theorem fin15Anchored_clause27370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1658 Fin15AnchoredAtom4591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20704
  ] at hbad
  tauto

theorem fin15Anchored_clause27371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1714 Fin15AnchoredAtom4591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20704
  ] at hbad
  tauto

theorem fin15Anchored_clause27372 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4591 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1617 chi ∧
      Fin15AnchoredAtom1637 chi ∧
      Fin15AnchoredAtom1658 chi ∧
      Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom1617 Fin15AnchoredAtom1637
    Fin15AnchoredAtom1658 Fin15AnchoredAtom1714 Fin15AnchoredAtom4591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20704
  ] at hbad
  tauto

theorem fin15Anchored_clause27373 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom4592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24800
  ] at hbad
  tauto

theorem fin15Anchored_clause27374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1617 Fin15AnchoredAtom4592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24800
  ] at hbad
  tauto

theorem fin15Anchored_clause27375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1638 Fin15AnchoredAtom4592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24800
  ] at hbad
  tauto

theorem fin15Anchored_clause27376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1659 Fin15AnchoredAtom4592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24800
  ] at hbad
  tauto

theorem fin15Anchored_clause27377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1715 Fin15AnchoredAtom4592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24800
  ] at hbad
  tauto

theorem fin15Anchored_clause27378 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4592 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1617 chi ∧
      Fin15AnchoredAtom1638 chi ∧
      Fin15AnchoredAtom1659 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom1617 Fin15AnchoredAtom1638
    Fin15AnchoredAtom1659 Fin15AnchoredAtom1715 Fin15AnchoredAtom4592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24800
  ] at hbad
  tauto

theorem fin15Anchored_clause27379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom4593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01888
  ] at hbad
  tauto

theorem fin15Anchored_clause27380 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1619 Fin15AnchoredAtom4593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01888
  ] at hbad
  tauto

theorem fin15Anchored_clause27381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom4593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01888
  ] at hbad
  tauto

theorem fin15Anchored_clause27382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom4593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01888
  ] at hbad
  tauto

theorem fin15Anchored_clause27383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom4593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01888
  ] at hbad
  tauto

theorem fin15Anchored_clause27384 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4593 chi ∧
      Fin15AnchoredAtom1618 chi ∧
      Fin15AnchoredAtom1619 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1660 chi ∧
      Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom1619 Fin15AnchoredAtom1624
    Fin15AnchoredAtom1660 Fin15AnchoredAtom1716 Fin15AnchoredAtom4593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01888
  ] at hbad
  tauto

theorem fin15Anchored_clause27385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom4595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04960
  ] at hbad
  tauto

theorem fin15Anchored_clause27386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1621 Fin15AnchoredAtom4595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04960
  ] at hbad
  tauto

theorem fin15Anchored_clause27387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom4595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04960
  ] at hbad
  tauto

theorem fin15Anchored_clause27388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1662 Fin15AnchoredAtom4595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04960
  ] at hbad
  tauto

theorem fin15Anchored_clause27389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1718 Fin15AnchoredAtom4595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04960
  ] at hbad
  tauto

theorem fin15Anchored_clause27390 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4595 chi ∧
      Fin15AnchoredAtom1618 chi ∧
      Fin15AnchoredAtom1621 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1662 chi ∧
      Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom1621 Fin15AnchoredAtom1626
    Fin15AnchoredAtom1662 Fin15AnchoredAtom1718 Fin15AnchoredAtom4595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04960
  ] at hbad
  tauto

theorem fin15Anchored_clause27391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom4596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09056
  ] at hbad
  tauto

end ErdosSzekeres

end
