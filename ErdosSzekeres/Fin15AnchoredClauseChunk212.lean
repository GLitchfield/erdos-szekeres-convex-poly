module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 212. -/

theorem fin15Anchored_clause27136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom4530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13456
  ] at hbad
  tauto

theorem fin15Anchored_clause27137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom4530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13456
  ] at hbad
  tauto

theorem fin15Anchored_clause27138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom4530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13456
  ] at hbad
  tauto

theorem fin15Anchored_clause27139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom4530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13456
  ] at hbad
  tauto

theorem fin15Anchored_clause27140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom4530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13456
  ] at hbad
  tauto

theorem fin15Anchored_clause27141 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom1568 Fin15AnchoredAtom1573
    Fin15AnchoredAtom1604 Fin15AnchoredAtom1779 Fin15AnchoredAtom4530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13456
  ] at hbad
  tauto

theorem fin15Anchored_clause27142 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom4531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21648
  ] at hbad
  tauto

theorem fin15Anchored_clause27143 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1569 Fin15AnchoredAtom4531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21648
  ] at hbad
  tauto

theorem fin15Anchored_clause27144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1574 Fin15AnchoredAtom4531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21648
  ] at hbad
  tauto

theorem fin15Anchored_clause27145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1605 Fin15AnchoredAtom4531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21648
  ] at hbad
  tauto

theorem fin15Anchored_clause27146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1780 Fin15AnchoredAtom4531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21648
  ] at hbad
  tauto

theorem fin15Anchored_clause27147 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom1569 Fin15AnchoredAtom1574
    Fin15AnchoredAtom1605 Fin15AnchoredAtom1780 Fin15AnchoredAtom4531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21648
  ] at hbad
  tauto

theorem fin15Anchored_clause27148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom4532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25744
  ] at hbad
  tauto

theorem fin15Anchored_clause27149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1569 Fin15AnchoredAtom4532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25744
  ] at hbad
  tauto

theorem fin15Anchored_clause27150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1575 Fin15AnchoredAtom4532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25744
  ] at hbad
  tauto

theorem fin15Anchored_clause27151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1606 Fin15AnchoredAtom4532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25744
  ] at hbad
  tauto

theorem fin15Anchored_clause27152 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1781 Fin15AnchoredAtom4532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25744
  ] at hbad
  tauto

theorem fin15Anchored_clause27153 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom1569 Fin15AnchoredAtom1575
    Fin15AnchoredAtom1606 Fin15AnchoredAtom1781 Fin15AnchoredAtom4532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25744
  ] at hbad
  tauto

theorem fin15Anchored_clause27154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom4533 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14480
  ] at hbad
  tauto

theorem fin15Anchored_clause27155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1607 Fin15AnchoredAtom4533 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14480
  ] at hbad
  tauto

theorem fin15Anchored_clause27156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1782 Fin15AnchoredAtom4533 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14480
  ] at hbad
  tauto

theorem fin15Anchored_clause27157 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4533 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1571 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1607 chi ∧
      Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1570 Fin15AnchoredAtom1571 Fin15AnchoredAtom1573
    Fin15AnchoredAtom1607 Fin15AnchoredAtom1782 Fin15AnchoredAtom4533 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14480
  ] at hbad
  tauto

theorem fin15Anchored_clause27158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4534 chi ∧
      ¬Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1570 Fin15AnchoredAtom4534 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22672
  ] at hbad
  tauto

theorem fin15Anchored_clause27159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4534 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1574 Fin15AnchoredAtom4534 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22672
  ] at hbad
  tauto

theorem fin15Anchored_clause27160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4534 chi ∧
      ¬Fin15AnchoredAtom1608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1608 Fin15AnchoredAtom4534 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22672
  ] at hbad
  tauto

theorem fin15Anchored_clause27161 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4534 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1572 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1608 chi ∧
      Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1570 Fin15AnchoredAtom1572 Fin15AnchoredAtom1574
    Fin15AnchoredAtom1608 Fin15AnchoredAtom1783 Fin15AnchoredAtom4534 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22672
  ] at hbad
  tauto

theorem fin15Anchored_clause27162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom4536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28816
  ] at hbad
  tauto

theorem fin15Anchored_clause27163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1574 Fin15AnchoredAtom4536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28816
  ] at hbad
  tauto

theorem fin15Anchored_clause27164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1575 Fin15AnchoredAtom4536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28816
  ] at hbad
  tauto

theorem fin15Anchored_clause27165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1610 Fin15AnchoredAtom4536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28816
  ] at hbad
  tauto

theorem fin15Anchored_clause27166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1785 Fin15AnchoredAtom4536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28816
  ] at hbad
  tauto

theorem fin15Anchored_clause27167 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4536 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom1574 Fin15AnchoredAtom1575
    Fin15AnchoredAtom1610 Fin15AnchoredAtom1785 Fin15AnchoredAtom4536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28816
  ] at hbad
  tauto

theorem fin15Anchored_clause27168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1576 Fin15AnchoredAtom4538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05904
  ] at hbad
  tauto

theorem fin15Anchored_clause27169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom4538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05904
  ] at hbad
  tauto

theorem fin15Anchored_clause27170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom4538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05904
  ] at hbad
  tauto

theorem fin15Anchored_clause27171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom4538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05904
  ] at hbad
  tauto

theorem fin15Anchored_clause27172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom4538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05904
  ] at hbad
  tauto

theorem fin15Anchored_clause27173 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4538 chi ∧
      Fin15AnchoredAtom1576 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1576 Fin15AnchoredAtom1578 Fin15AnchoredAtom1582
    Fin15AnchoredAtom1592 Fin15AnchoredAtom1787 Fin15AnchoredAtom4538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05904
  ] at hbad
  tauto

theorem fin15Anchored_clause27174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1576 Fin15AnchoredAtom4539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10000
  ] at hbad
  tauto

theorem fin15Anchored_clause27175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1579 Fin15AnchoredAtom4539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10000
  ] at hbad
  tauto

theorem fin15Anchored_clause27176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1583 Fin15AnchoredAtom4539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10000
  ] at hbad
  tauto

theorem fin15Anchored_clause27177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom4539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10000
  ] at hbad
  tauto

theorem fin15Anchored_clause27178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1788 Fin15AnchoredAtom4539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10000
  ] at hbad
  tauto

theorem fin15Anchored_clause27179 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4539 chi ∧
      Fin15AnchoredAtom1576 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1576 Fin15AnchoredAtom1579 Fin15AnchoredAtom1583
    Fin15AnchoredAtom1593 Fin15AnchoredAtom1788 Fin15AnchoredAtom4539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10000
  ] at hbad
  tauto

theorem fin15Anchored_clause27180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1576 Fin15AnchoredAtom4540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18192
  ] at hbad
  tauto

theorem fin15Anchored_clause27181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1580 Fin15AnchoredAtom4540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18192
  ] at hbad
  tauto

theorem fin15Anchored_clause27182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1584 Fin15AnchoredAtom4540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18192
  ] at hbad
  tauto

theorem fin15Anchored_clause27183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1594 Fin15AnchoredAtom4540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18192
  ] at hbad
  tauto

theorem fin15Anchored_clause27184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1789 Fin15AnchoredAtom4540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18192
  ] at hbad
  tauto

theorem fin15Anchored_clause27185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom4544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13072
  ] at hbad
  tauto

theorem fin15Anchored_clause27186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1579 Fin15AnchoredAtom4544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13072
  ] at hbad
  tauto

theorem fin15Anchored_clause27187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1588 Fin15AnchoredAtom4544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13072
  ] at hbad
  tauto

theorem fin15Anchored_clause27188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom4544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13072
  ] at hbad
  tauto

theorem fin15Anchored_clause27189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1793 Fin15AnchoredAtom4544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13072
  ] at hbad
  tauto

theorem fin15Anchored_clause27190 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4544 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom1579 Fin15AnchoredAtom1588
    Fin15AnchoredAtom1598 Fin15AnchoredAtom1793 Fin15AnchoredAtom4544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13072
  ] at hbad
  tauto

theorem fin15Anchored_clause27191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom4545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21264
  ] at hbad
  tauto

theorem fin15Anchored_clause27192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1580 Fin15AnchoredAtom4545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21264
  ] at hbad
  tauto

theorem fin15Anchored_clause27193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1589 Fin15AnchoredAtom4545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21264
  ] at hbad
  tauto

theorem fin15Anchored_clause27194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1599 Fin15AnchoredAtom4545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21264
  ] at hbad
  tauto

theorem fin15Anchored_clause27195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1794 Fin15AnchoredAtom4545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21264
  ] at hbad
  tauto

theorem fin15Anchored_clause27196 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4545 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1580 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom1580 Fin15AnchoredAtom1589
    Fin15AnchoredAtom1599 Fin15AnchoredAtom1794 Fin15AnchoredAtom4545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21264
  ] at hbad
  tauto

theorem fin15Anchored_clause27197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1579 Fin15AnchoredAtom4546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25360
  ] at hbad
  tauto

theorem fin15Anchored_clause27198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1580 Fin15AnchoredAtom4546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25360
  ] at hbad
  tauto

theorem fin15Anchored_clause27199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1590 Fin15AnchoredAtom4546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25360
  ] at hbad
  tauto

theorem fin15Anchored_clause27200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1600 Fin15AnchoredAtom4546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25360
  ] at hbad
  tauto

theorem fin15Anchored_clause27201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1795 Fin15AnchoredAtom4546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25360
  ] at hbad
  tauto

theorem fin15Anchored_clause27202 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4546 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1580 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1579 Fin15AnchoredAtom1580 Fin15AnchoredAtom1590
    Fin15AnchoredAtom1600 Fin15AnchoredAtom1795 Fin15AnchoredAtom4546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25360
  ] at hbad
  tauto

theorem fin15Anchored_clause27203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom4550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13584
  ] at hbad
  tauto

theorem fin15Anchored_clause27204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1583 Fin15AnchoredAtom4550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13584
  ] at hbad
  tauto

theorem fin15Anchored_clause27205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1588 Fin15AnchoredAtom4550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13584
  ] at hbad
  tauto

theorem fin15Anchored_clause27206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom4550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13584
  ] at hbad
  tauto

theorem fin15Anchored_clause27207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1799 Fin15AnchoredAtom4550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13584
  ] at hbad
  tauto

theorem fin15Anchored_clause27208 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom1583 Fin15AnchoredAtom1588
    Fin15AnchoredAtom1604 Fin15AnchoredAtom1799 Fin15AnchoredAtom4550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13584
  ] at hbad
  tauto

theorem fin15Anchored_clause27209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom4551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21776
  ] at hbad
  tauto

theorem fin15Anchored_clause27210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1584 Fin15AnchoredAtom4551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21776
  ] at hbad
  tauto

theorem fin15Anchored_clause27211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1589 Fin15AnchoredAtom4551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21776
  ] at hbad
  tauto

theorem fin15Anchored_clause27212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1605 Fin15AnchoredAtom4551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21776
  ] at hbad
  tauto

theorem fin15Anchored_clause27213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1800 Fin15AnchoredAtom4551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21776
  ] at hbad
  tauto

theorem fin15Anchored_clause27214 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4551 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1584 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom1584 Fin15AnchoredAtom1589
    Fin15AnchoredAtom1605 Fin15AnchoredAtom1800 Fin15AnchoredAtom4551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21776
  ] at hbad
  tauto

theorem fin15Anchored_clause27215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1583 Fin15AnchoredAtom4552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25872
  ] at hbad
  tauto

theorem fin15Anchored_clause27216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1584 Fin15AnchoredAtom4552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25872
  ] at hbad
  tauto

theorem fin15Anchored_clause27217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1590 Fin15AnchoredAtom4552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25872
  ] at hbad
  tauto

theorem fin15Anchored_clause27218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1606 Fin15AnchoredAtom4552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25872
  ] at hbad
  tauto

theorem fin15Anchored_clause27219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1801 Fin15AnchoredAtom4552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25872
  ] at hbad
  tauto

theorem fin15Anchored_clause27220 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4552 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1584 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1583 Fin15AnchoredAtom1584 Fin15AnchoredAtom1590
    Fin15AnchoredAtom1606 Fin15AnchoredAtom1801 Fin15AnchoredAtom4552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25872
  ] at hbad
  tauto

theorem fin15Anchored_clause27221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1588 Fin15AnchoredAtom4556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28944
  ] at hbad
  tauto

theorem fin15Anchored_clause27222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1589 Fin15AnchoredAtom4556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28944
  ] at hbad
  tauto

theorem fin15Anchored_clause27223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1590 Fin15AnchoredAtom4556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28944
  ] at hbad
  tauto

theorem fin15Anchored_clause27224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1610 Fin15AnchoredAtom4556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28944
  ] at hbad
  tauto

theorem fin15Anchored_clause27225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1805 Fin15AnchoredAtom4556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28944
  ] at hbad
  tauto

theorem fin15Anchored_clause27226 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4556 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1588 Fin15AnchoredAtom1589 Fin15AnchoredAtom1590
    Fin15AnchoredAtom1610 Fin15AnchoredAtom1805 Fin15AnchoredAtom4556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28944
  ] at hbad
  tauto

theorem fin15Anchored_clause27227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4557 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom4557 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07696
  ] at hbad
  tauto

theorem fin15Anchored_clause27228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4557 chi ∧
      ¬Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1595 Fin15AnchoredAtom4557 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07696
  ] at hbad
  tauto

theorem fin15Anchored_clause27229 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4557 chi ∧
      ¬Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1601 Fin15AnchoredAtom4557 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07696
  ] at hbad
  tauto

theorem fin15Anchored_clause27230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4558 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom4558 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11792
  ] at hbad
  tauto

theorem fin15Anchored_clause27231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4559 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1594 Fin15AnchoredAtom4559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19984
  ] at hbad
  tauto

theorem fin15Anchored_clause27232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4559 chi ∧
      ¬Fin15AnchoredAtom1597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1597 Fin15AnchoredAtom4559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19984
  ] at hbad
  tauto

theorem fin15Anchored_clause27233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom4560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13840
  ] at hbad
  tauto

theorem fin15Anchored_clause27234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom4560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13840
  ] at hbad
  tauto

theorem fin15Anchored_clause27235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom4560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13840
  ] at hbad
  tauto

theorem fin15Anchored_clause27236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom4560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13840
  ] at hbad
  tauto

theorem fin15Anchored_clause27237 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom4560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13840
  ] at hbad
  tauto

theorem fin15Anchored_clause27238 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom1593 Fin15AnchoredAtom1598
    Fin15AnchoredAtom1604 Fin15AnchoredAtom1809 Fin15AnchoredAtom4560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13840
  ] at hbad
  tauto

theorem fin15Anchored_clause27239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom4561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22032
  ] at hbad
  tauto

theorem fin15Anchored_clause27240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1594 Fin15AnchoredAtom4561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22032
  ] at hbad
  tauto

theorem fin15Anchored_clause27241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1599 Fin15AnchoredAtom4561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22032
  ] at hbad
  tauto

theorem fin15Anchored_clause27242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1605 Fin15AnchoredAtom4561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22032
  ] at hbad
  tauto

theorem fin15Anchored_clause27243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1810 Fin15AnchoredAtom4561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22032
  ] at hbad
  tauto

theorem fin15Anchored_clause27244 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1594 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom1594 Fin15AnchoredAtom1599
    Fin15AnchoredAtom1605 Fin15AnchoredAtom1810 Fin15AnchoredAtom4561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22032
  ] at hbad
  tauto

theorem fin15Anchored_clause27245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom4562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26128
  ] at hbad
  tauto

theorem fin15Anchored_clause27246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1594 Fin15AnchoredAtom4562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26128
  ] at hbad
  tauto

theorem fin15Anchored_clause27247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1600 Fin15AnchoredAtom4562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26128
  ] at hbad
  tauto

theorem fin15Anchored_clause27248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1606 Fin15AnchoredAtom4562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26128
  ] at hbad
  tauto

theorem fin15Anchored_clause27249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1811 Fin15AnchoredAtom4562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26128
  ] at hbad
  tauto

theorem fin15Anchored_clause27250 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4562 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1594 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom1594 Fin15AnchoredAtom1600
    Fin15AnchoredAtom1606 Fin15AnchoredAtom1811 Fin15AnchoredAtom4562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26128
  ] at hbad
  tauto

theorem fin15Anchored_clause27251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4563 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom4563 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14864
  ] at hbad
  tauto

theorem fin15Anchored_clause27252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4564 chi ∧
      ¬Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1595 Fin15AnchoredAtom4564 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23056
  ] at hbad
  tauto

theorem fin15Anchored_clause27253 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4564 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1599 Fin15AnchoredAtom4564 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23056
  ] at hbad
  tauto

theorem fin15Anchored_clause27254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom4566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29200
  ] at hbad
  tauto

theorem fin15Anchored_clause27255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1599 Fin15AnchoredAtom4566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29200
  ] at hbad
  tauto

theorem fin15Anchored_clause27256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1600 Fin15AnchoredAtom4566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29200
  ] at hbad
  tauto

theorem fin15Anchored_clause27257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1610 Fin15AnchoredAtom4566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29200
  ] at hbad
  tauto

theorem fin15Anchored_clause27258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1815 Fin15AnchoredAtom4566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29200
  ] at hbad
  tauto

theorem fin15Anchored_clause27259 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4566 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom1599 Fin15AnchoredAtom1600
    Fin15AnchoredAtom1610 Fin15AnchoredAtom1815 Fin15AnchoredAtom4566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29200
  ] at hbad
  tauto

theorem fin15Anchored_clause27260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4567 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom4567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15376
  ] at hbad
  tauto

theorem fin15Anchored_clause27261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4567 chi ∧
      ¬Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1816 Fin15AnchoredAtom4567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15376
  ] at hbad
  tauto

theorem fin15Anchored_clause27262 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4567 chi ∧
      Fin15AnchoredAtom1601 chi ∧
      Fin15AnchoredAtom1602 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1607 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1601 Fin15AnchoredAtom1602 Fin15AnchoredAtom1604
    Fin15AnchoredAtom1607 Fin15AnchoredAtom1816 Fin15AnchoredAtom4567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15376
  ] at hbad
  tauto

theorem fin15Anchored_clause27263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4568 chi ∧
      ¬Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1817 Fin15AnchoredAtom4568 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23568
  ] at hbad
  tauto

end ErdosSzekeres

end
