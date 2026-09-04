module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 220. -/

theorem fin15Anchored_clause28160 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4799 chi ∧
      Fin15AnchoredAtom1776 chi ∧
      Fin15AnchoredAtom1778 chi ∧
      Fin15AnchoredAtom1780 chi ∧
      Fin15AnchoredAtom1783 chi ∧
      Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1776 Fin15AnchoredAtom1778 Fin15AnchoredAtom1780
    Fin15AnchoredAtom1783 Fin15AnchoredAtom1817 Fin15AnchoredAtom4799 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23680
  ] at hbad
  tauto

theorem fin15Anchored_clause28161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4800 chi ∧
      ¬Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1777 Fin15AnchoredAtom4800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27776
  ] at hbad
  tauto

theorem fin15Anchored_clause28162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4800 chi ∧
      ¬Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1778 Fin15AnchoredAtom4800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27776
  ] at hbad
  tauto

theorem fin15Anchored_clause28163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4800 chi ∧
      ¬Fin15AnchoredAtom1784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1784 Fin15AnchoredAtom4800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27776
  ] at hbad
  tauto

theorem fin15Anchored_clause28164 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4800 chi ∧
      Fin15AnchoredAtom1777 chi ∧
      Fin15AnchoredAtom1778 chi ∧
      Fin15AnchoredAtom1781 chi ∧
      Fin15AnchoredAtom1784 chi ∧
      Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1777 Fin15AnchoredAtom1778 Fin15AnchoredAtom1781
    Fin15AnchoredAtom1784 Fin15AnchoredAtom1818 Fin15AnchoredAtom4800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27776
  ] at hbad
  tauto

theorem fin15Anchored_clause28165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom4801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29824
  ] at hbad
  tauto

theorem fin15Anchored_clause28166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1780 Fin15AnchoredAtom4801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29824
  ] at hbad
  tauto

theorem fin15Anchored_clause28167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1781 Fin15AnchoredAtom4801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29824
  ] at hbad
  tauto

theorem fin15Anchored_clause28168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1785 Fin15AnchoredAtom4801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29824
  ] at hbad
  tauto

theorem fin15Anchored_clause28169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1819 Fin15AnchoredAtom4801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29824
  ] at hbad
  tauto

theorem fin15Anchored_clause28170 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4801 chi ∧
      Fin15AnchoredAtom1779 chi ∧
      Fin15AnchoredAtom1780 chi ∧
      Fin15AnchoredAtom1781 chi ∧
      Fin15AnchoredAtom1785 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom1780 Fin15AnchoredAtom1781
    Fin15AnchoredAtom1785 Fin15AnchoredAtom1819 Fin15AnchoredAtom4801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29824
  ] at hbad
  tauto

theorem fin15Anchored_clause28171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4802 chi ∧
      ¬Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1783 Fin15AnchoredAtom4802 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30848
  ] at hbad
  tauto

theorem fin15Anchored_clause28172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4802 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1785 Fin15AnchoredAtom4802 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30848
  ] at hbad
  tauto

theorem fin15Anchored_clause28173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom4806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14080
  ] at hbad
  tauto

theorem fin15Anchored_clause28174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1788 Fin15AnchoredAtom4806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14080
  ] at hbad
  tauto

theorem fin15Anchored_clause28175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1793 Fin15AnchoredAtom4806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14080
  ] at hbad
  tauto

theorem fin15Anchored_clause28176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1799 Fin15AnchoredAtom4806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14080
  ] at hbad
  tauto

theorem fin15Anchored_clause28177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom4806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14080
  ] at hbad
  tauto

theorem fin15Anchored_clause28178 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4806 chi ∧
      Fin15AnchoredAtom1787 chi ∧
      Fin15AnchoredAtom1788 chi ∧
      Fin15AnchoredAtom1793 chi ∧
      Fin15AnchoredAtom1799 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom1788 Fin15AnchoredAtom1793
    Fin15AnchoredAtom1799 Fin15AnchoredAtom1809 Fin15AnchoredAtom4806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14080
  ] at hbad
  tauto

theorem fin15Anchored_clause28179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom4807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22272
  ] at hbad
  tauto

theorem fin15Anchored_clause28180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1789 Fin15AnchoredAtom4807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22272
  ] at hbad
  tauto

theorem fin15Anchored_clause28181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1800 Fin15AnchoredAtom4807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22272
  ] at hbad
  tauto

theorem fin15Anchored_clause28182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1810 Fin15AnchoredAtom4807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22272
  ] at hbad
  tauto

theorem fin15Anchored_clause28183 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4807 chi ∧
      Fin15AnchoredAtom1787 chi ∧
      Fin15AnchoredAtom1789 chi ∧
      Fin15AnchoredAtom1794 chi ∧
      Fin15AnchoredAtom1800 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom1789 Fin15AnchoredAtom1794
    Fin15AnchoredAtom1800 Fin15AnchoredAtom1810 Fin15AnchoredAtom4807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22272
  ] at hbad
  tauto

theorem fin15Anchored_clause28184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1788 Fin15AnchoredAtom4808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26368
  ] at hbad
  tauto

theorem fin15Anchored_clause28185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1789 Fin15AnchoredAtom4808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26368
  ] at hbad
  tauto

theorem fin15Anchored_clause28186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1801 Fin15AnchoredAtom4808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26368
  ] at hbad
  tauto

theorem fin15Anchored_clause28187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1811 Fin15AnchoredAtom4808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26368
  ] at hbad
  tauto

theorem fin15Anchored_clause28188 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4808 chi ∧
      Fin15AnchoredAtom1788 chi ∧
      Fin15AnchoredAtom1789 chi ∧
      Fin15AnchoredAtom1795 chi ∧
      Fin15AnchoredAtom1801 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1788 Fin15AnchoredAtom1789 Fin15AnchoredAtom1795
    Fin15AnchoredAtom1801 Fin15AnchoredAtom1811 Fin15AnchoredAtom4808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26368
  ] at hbad
  tauto

theorem fin15Anchored_clause28189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1793 Fin15AnchoredAtom4812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29440
  ] at hbad
  tauto

theorem fin15Anchored_clause28190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1794 Fin15AnchoredAtom4812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29440
  ] at hbad
  tauto

theorem fin15Anchored_clause28191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1795 Fin15AnchoredAtom4812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29440
  ] at hbad
  tauto

theorem fin15Anchored_clause28192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1805 Fin15AnchoredAtom4812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29440
  ] at hbad
  tauto

theorem fin15Anchored_clause28193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1815 Fin15AnchoredAtom4812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29440
  ] at hbad
  tauto

theorem fin15Anchored_clause28194 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4812 chi ∧
      Fin15AnchoredAtom1793 chi ∧
      Fin15AnchoredAtom1794 chi ∧
      Fin15AnchoredAtom1795 chi ∧
      Fin15AnchoredAtom1805 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1793 Fin15AnchoredAtom1794 Fin15AnchoredAtom1795
    Fin15AnchoredAtom1805 Fin15AnchoredAtom1815 Fin15AnchoredAtom4812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29440
  ] at hbad
  tauto

theorem fin15Anchored_clause28195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1799 Fin15AnchoredAtom4816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29952
  ] at hbad
  tauto

theorem fin15Anchored_clause28196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1800 Fin15AnchoredAtom4816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29952
  ] at hbad
  tauto

theorem fin15Anchored_clause28197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1801 Fin15AnchoredAtom4816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29952
  ] at hbad
  tauto

theorem fin15Anchored_clause28198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1805 Fin15AnchoredAtom4816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29952
  ] at hbad
  tauto

theorem fin15Anchored_clause28199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1819 Fin15AnchoredAtom4816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29952
  ] at hbad
  tauto

theorem fin15Anchored_clause28200 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4816 chi ∧
      Fin15AnchoredAtom1799 chi ∧
      Fin15AnchoredAtom1800 chi ∧
      Fin15AnchoredAtom1801 chi ∧
      Fin15AnchoredAtom1805 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1799 Fin15AnchoredAtom1800 Fin15AnchoredAtom1801
    Fin15AnchoredAtom1805 Fin15AnchoredAtom1819 Fin15AnchoredAtom4816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29952
  ] at hbad
  tauto

theorem fin15Anchored_clause28201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4818 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom4818 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15872
  ] at hbad
  tauto

theorem fin15Anchored_clause28202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4819 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1810 Fin15AnchoredAtom4819 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24064
  ] at hbad
  tauto

theorem fin15Anchored_clause28203 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4819 chi ∧
      Fin15AnchoredAtom1806 chi ∧
      Fin15AnchoredAtom1808 chi ∧
      Fin15AnchoredAtom1810 chi ∧
      Fin15AnchoredAtom1813 chi ∧
      Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1806 Fin15AnchoredAtom1808 Fin15AnchoredAtom1810
    Fin15AnchoredAtom1813 Fin15AnchoredAtom1817 Fin15AnchoredAtom4819 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24064
  ] at hbad
  tauto

theorem fin15Anchored_clause28204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4820 chi ∧
      ¬Fin15AnchoredAtom1807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1807 Fin15AnchoredAtom4820 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28160
  ] at hbad
  tauto

theorem fin15Anchored_clause28205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4820 chi ∧
      ¬Fin15AnchoredAtom1808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1808 Fin15AnchoredAtom4820 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28160
  ] at hbad
  tauto

theorem fin15Anchored_clause28206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4820 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1811 Fin15AnchoredAtom4820 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28160
  ] at hbad
  tauto

theorem fin15Anchored_clause28207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4820 chi ∧
      ¬Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1818 Fin15AnchoredAtom4820 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28160
  ] at hbad
  tauto

theorem fin15Anchored_clause28208 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4820 chi ∧
      Fin15AnchoredAtom1807 chi ∧
      Fin15AnchoredAtom1808 chi ∧
      Fin15AnchoredAtom1811 chi ∧
      Fin15AnchoredAtom1814 chi ∧
      Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1807 Fin15AnchoredAtom1808 Fin15AnchoredAtom1811
    Fin15AnchoredAtom1814 Fin15AnchoredAtom1818 Fin15AnchoredAtom4820 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28160
  ] at hbad
  tauto

theorem fin15Anchored_clause28209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4821 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom4821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30208
  ] at hbad
  tauto

theorem fin15Anchored_clause28210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4821 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1810 Fin15AnchoredAtom4821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30208
  ] at hbad
  tauto

theorem fin15Anchored_clause28211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4821 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1811 Fin15AnchoredAtom4821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30208
  ] at hbad
  tauto

theorem fin15Anchored_clause28212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4821 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1815 Fin15AnchoredAtom4821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30208
  ] at hbad
  tauto

theorem fin15Anchored_clause28213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4821 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1819 Fin15AnchoredAtom4821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30208
  ] at hbad
  tauto

theorem fin15Anchored_clause28214 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4821 chi ∧
      Fin15AnchoredAtom1809 chi ∧
      Fin15AnchoredAtom1810 chi ∧
      Fin15AnchoredAtom1811 chi ∧
      Fin15AnchoredAtom1815 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom1810 Fin15AnchoredAtom1811
    Fin15AnchoredAtom1815 Fin15AnchoredAtom1819 Fin15AnchoredAtom4821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30208
  ] at hbad
  tauto

theorem fin15Anchored_clause28215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4822 chi ∧
      ¬Fin15AnchoredAtom1812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1812 Fin15AnchoredAtom4822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask31232
  ] at hbad
  tauto

theorem fin15Anchored_clause28216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4822 chi ∧
      ¬Fin15AnchoredAtom1813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1813 Fin15AnchoredAtom4822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask31232
  ] at hbad
  tauto

theorem fin15Anchored_clause28217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4823 chi ∧
      ¬Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1818 Fin15AnchoredAtom4823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask31744
  ] at hbad
  tauto

theorem fin15Anchored_clause28218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4823 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1819 Fin15AnchoredAtom4823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask31744
  ] at hbad
  tauto

theorem fin15Anchored_clause28219 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1832
    Fin15AnchoredAtom1887 Fin15AnchoredAtom2107 Fin15AnchoredAtom2822 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 5}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 4, 5} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 4, 5} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 4, 5}, {0, 2, 3, 4, 5}, {0, 1, 3, 4, 5}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28220 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1833
    Fin15AnchoredAtom1888 Fin15AnchoredAtom2108 Fin15AnchoredAtom2823 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 6}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 4, 6} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 4, 6} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 4, 6}, {0, 2, 3, 4, 6}, {0, 1, 3, 4, 6}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28221 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2824 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1824 Fin15AnchoredAtom1834
    Fin15AnchoredAtom1889 Fin15AnchoredAtom2109 Fin15AnchoredAtom2824 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 4, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 4, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 4, 7}, {0, 2, 3, 4, 7}, {0, 1, 3, 4, 7}, {0, 1, 2, 4, 7}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28222 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1826 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1891 Fin15AnchoredAtom2111 Fin15AnchoredAtom2826 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 4, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 4, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 4, 9}, {0, 2, 3, 4, 9}, {0, 1, 3, 4, 9}, {0, 1, 2, 4, 9}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28223 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2827 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1827 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1892 Fin15AnchoredAtom2112 Fin15AnchoredAtom2827 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 4, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 4, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 4, 10}, {0, 2, 3, 4, 10}, {0, 1, 3, 4, 10}, {0, 1, 2, 4, 10}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28224 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom1838 chi ∧
      Fin15AnchoredAtom1893 chi ∧
      Fin15AnchoredAtom2113 chi ∧
      Fin15AnchoredAtom2828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1828 Fin15AnchoredAtom1838
    Fin15AnchoredAtom1893 Fin15AnchoredAtom2113 Fin15AnchoredAtom2828 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 4, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 4, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 4, 11}, {0, 2, 3, 4, 11}, {0, 1, 3, 4, 11}, {0, 1, 2, 4, 11}, {0, 1, 2, 3, 11}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28225 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1829 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1894 Fin15AnchoredAtom2114 Fin15AnchoredAtom2829 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 4, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 4, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 4, 12}, {0, 2, 3, 4, 12}, {0, 1, 3, 4, 12}, {0, 1, 2, 4, 12}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28226 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1830 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1895 Fin15AnchoredAtom2115 Fin15AnchoredAtom2830 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 4, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 4, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 4, 13}, {0, 2, 3, 4, 13}, {0, 1, 3, 4, 13}, {0, 1, 2, 4, 13}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28227 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1831 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1896 Fin15AnchoredAtom2116 Fin15AnchoredAtom2831 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 4, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 4, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 4, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 4, 14}, {0, 2, 3, 4, 14}, {0, 1, 3, 4, 14}, {0, 1, 2, 4, 14}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28228 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1842
    Fin15AnchoredAtom1897 Fin15AnchoredAtom2117 Fin15AnchoredAtom2832 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 6}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 5, 6} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 5, 6} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 5, 6}, {0, 2, 3, 5, 6}, {0, 1, 3, 5, 6}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28229 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1824 Fin15AnchoredAtom1843
    Fin15AnchoredAtom1898 Fin15AnchoredAtom2118 Fin15AnchoredAtom2833 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 5, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 5, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 5, 7}, {0, 2, 3, 5, 7}, {0, 1, 3, 5, 7}, {0, 1, 2, 5, 7}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28230 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1825 chi ∧
      Fin15AnchoredAtom1844 chi ∧
      Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom2834 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1825 Fin15AnchoredAtom1844
    Fin15AnchoredAtom1899 Fin15AnchoredAtom2119 Fin15AnchoredAtom2834 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 5, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 5, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 5, 8}, {0, 2, 3, 5, 8}, {0, 1, 3, 5, 8}, {0, 1, 2, 5, 8}, {0, 1, 2, 3, 8}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28231 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1826 Fin15AnchoredAtom1845
    Fin15AnchoredAtom1900 Fin15AnchoredAtom2120 Fin15AnchoredAtom2835 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 5, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 5, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 5, 9}, {0, 2, 3, 5, 9}, {0, 1, 3, 5, 9}, {0, 1, 2, 5, 9}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28232 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1827 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1901 Fin15AnchoredAtom2121 Fin15AnchoredAtom2836 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 5, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 5, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 5, 10}, {0, 2, 3, 5, 10}, {0, 1, 3, 5, 10}, {0, 1, 2, 5, 10}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28233 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom1847 chi ∧
      Fin15AnchoredAtom1902 chi ∧
      Fin15AnchoredAtom2122 chi ∧
      Fin15AnchoredAtom2837 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1828 Fin15AnchoredAtom1847
    Fin15AnchoredAtom1902 Fin15AnchoredAtom2122 Fin15AnchoredAtom2837 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 5, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 5, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 5, 11}, {0, 2, 3, 5, 11}, {0, 1, 3, 5, 11}, {0, 1, 2, 5, 11}, {0, 1, 2, 3, 11}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28234 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1829 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1903 Fin15AnchoredAtom2123 Fin15AnchoredAtom2838 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 5, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 5, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 5, 12}, {0, 2, 3, 5, 12}, {0, 1, 3, 5, 12}, {0, 1, 2, 5, 12}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28235 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1830 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1904 Fin15AnchoredAtom2124 Fin15AnchoredAtom2839 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 5, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 5, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 5, 13}, {0, 2, 3, 5, 13}, {0, 1, 3, 5, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28236 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1831 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1905 Fin15AnchoredAtom2125 Fin15AnchoredAtom2840 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 5, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 5, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 5, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 5, 14}, {0, 2, 3, 5, 14}, {0, 1, 3, 5, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28237 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1824 Fin15AnchoredAtom1851
    Fin15AnchoredAtom1906 Fin15AnchoredAtom2126 Fin15AnchoredAtom2841 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 6, 7}, {0, 2, 3, 6, 7}, {0, 1, 3, 6, 7}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28238 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2843 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1826 Fin15AnchoredAtom1853
    Fin15AnchoredAtom1908 Fin15AnchoredAtom2128 Fin15AnchoredAtom2843 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 6, 9}, {0, 2, 3, 6, 9}, {0, 1, 3, 6, 9}, {0, 1, 2, 6, 9}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28239 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1827 Fin15AnchoredAtom1854
    Fin15AnchoredAtom1909 Fin15AnchoredAtom2129 Fin15AnchoredAtom2844 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 6, 10}, {0, 2, 3, 6, 10}, {0, 1, 3, 6, 10}, {0, 1, 2, 6, 10}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28240 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2846 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1829 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1911 Fin15AnchoredAtom2131 Fin15AnchoredAtom2846 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 6, 12}, {0, 2, 3, 6, 12}, {0, 1, 3, 6, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28241 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1830 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1912 Fin15AnchoredAtom2132 Fin15AnchoredAtom2847 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 6, 13}, {0, 2, 3, 6, 13}, {0, 1, 3, 6, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28242 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1823 Fin15AnchoredAtom1831 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1913 Fin15AnchoredAtom2133 Fin15AnchoredAtom2848 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 6, 14}, {0, 2, 3, 6, 14}, {0, 1, 3, 6, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28243 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1825 chi ∧
      Fin15AnchoredAtom1859 chi ∧
      Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom2849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1825 Fin15AnchoredAtom1859
    Fin15AnchoredAtom1914 Fin15AnchoredAtom2134 Fin15AnchoredAtom2849 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 7, 8}, {0, 2, 3, 7, 8}, {0, 1, 3, 7, 8}, {0, 1, 2, 7, 8}, {0, 1, 2, 3, 8}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28244 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1826 Fin15AnchoredAtom1860
    Fin15AnchoredAtom1915 Fin15AnchoredAtom2135 Fin15AnchoredAtom2850 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 7, 9}, {0, 2, 3, 7, 9}, {0, 1, 3, 7, 9}, {0, 1, 2, 7, 9}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28245 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2851 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1827 Fin15AnchoredAtom1861
    Fin15AnchoredAtom1916 Fin15AnchoredAtom2136 Fin15AnchoredAtom2851 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 7, 10}, {0, 2, 3, 7, 10}, {0, 1, 3, 7, 10}, {0, 1, 2, 7, 10}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28246 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1829 Fin15AnchoredAtom1863
    Fin15AnchoredAtom1918 Fin15AnchoredAtom2138 Fin15AnchoredAtom2853 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 7, 12}, {0, 2, 3, 7, 12}, {0, 1, 3, 7, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28247 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1830 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1919 Fin15AnchoredAtom2139 Fin15AnchoredAtom2854 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 7, 13}, {0, 2, 3, 7, 13}, {0, 1, 3, 7, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28248 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1824 Fin15AnchoredAtom1831 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1920 Fin15AnchoredAtom2140 Fin15AnchoredAtom2855 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 7, 14}, {0, 2, 3, 7, 14}, {0, 1, 3, 7, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28249 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1825 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1867 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1825 Fin15AnchoredAtom1827 Fin15AnchoredAtom1867
    Fin15AnchoredAtom1922 Fin15AnchoredAtom2142 Fin15AnchoredAtom2857 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 8, 10}, {0, 2, 3, 8, 10}, {0, 1, 3, 8, 10}, {0, 1, 2, 8, 10}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28250 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1825 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1869 chi ∧
      Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom2144 chi ∧
      Fin15AnchoredAtom2859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1825 Fin15AnchoredAtom1829 Fin15AnchoredAtom1869
    Fin15AnchoredAtom1924 Fin15AnchoredAtom2144 Fin15AnchoredAtom2859 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 8, 12}, {0, 2, 3, 8, 12}, {0, 1, 3, 8, 12}, {0, 1, 2, 8, 12}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28251 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1826 Fin15AnchoredAtom1827 Fin15AnchoredAtom1872
    Fin15AnchoredAtom1927 Fin15AnchoredAtom2147 Fin15AnchoredAtom2862 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 9, 10}, {0, 2, 3, 9, 10}, {0, 1, 3, 9, 10}, {0, 1, 2, 9, 10}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28252 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1826 Fin15AnchoredAtom1829 Fin15AnchoredAtom1874
    Fin15AnchoredAtom1929 Fin15AnchoredAtom2149 Fin15AnchoredAtom2864 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 9, 12}, {0, 2, 3, 9, 12}, {0, 1, 3, 9, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28253 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2865 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1826 Fin15AnchoredAtom1830 Fin15AnchoredAtom1875
    Fin15AnchoredAtom1930 Fin15AnchoredAtom2150 Fin15AnchoredAtom2865 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 9, 13}, {0, 2, 3, 9, 13}, {0, 1, 3, 9, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28254 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2866 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1826 Fin15AnchoredAtom1831 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1931 Fin15AnchoredAtom2151 Fin15AnchoredAtom2866 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 9, 14}, {0, 2, 3, 9, 14}, {0, 1, 3, 9, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28255 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom1877 chi ∧
      Fin15AnchoredAtom1932 chi ∧
      Fin15AnchoredAtom2152 chi ∧
      Fin15AnchoredAtom2867 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1827 Fin15AnchoredAtom1828 Fin15AnchoredAtom1877
    Fin15AnchoredAtom1932 Fin15AnchoredAtom2152 Fin15AnchoredAtom2867 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 10, 11}, {0, 2, 3, 10, 11}, {0, 1, 3, 10, 11}, {0, 1, 2, 10, 11}, {0, 1, 2, 3, 11}, {0, 1, 2, 3, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28256 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2868 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1827 Fin15AnchoredAtom1829 Fin15AnchoredAtom1878
    Fin15AnchoredAtom1933 Fin15AnchoredAtom2153 Fin15AnchoredAtom2868 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 10, 12}, {0, 2, 3, 10, 12}, {0, 1, 3, 10, 12}, {0, 1, 2, 10, 12}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28257 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2869 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1827 Fin15AnchoredAtom1830 Fin15AnchoredAtom1879
    Fin15AnchoredAtom1934 Fin15AnchoredAtom2154 Fin15AnchoredAtom2869 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 10, 13}, {0, 2, 3, 10, 13}, {0, 1, 3, 10, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28258 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2870 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1827 Fin15AnchoredAtom1831 Fin15AnchoredAtom1880
    Fin15AnchoredAtom1935 Fin15AnchoredAtom2155 Fin15AnchoredAtom2870 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 10, 14}, {0, 2, 3, 10, 14}, {0, 1, 3, 10, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28259 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1882 chi ∧
      Fin15AnchoredAtom1937 chi ∧
      Fin15AnchoredAtom2157 chi ∧
      Fin15AnchoredAtom2872 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1828 Fin15AnchoredAtom1830 Fin15AnchoredAtom1882
    Fin15AnchoredAtom1937 Fin15AnchoredAtom2157 Fin15AnchoredAtom2872 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 11, 13}, {0, 2, 3, 11, 13}, {0, 1, 3, 11, 13}, {0, 1, 2, 11, 13}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28260 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1883 chi ∧
      Fin15AnchoredAtom1938 chi ∧
      Fin15AnchoredAtom2158 chi ∧
      Fin15AnchoredAtom2873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1828 Fin15AnchoredAtom1831 Fin15AnchoredAtom1883
    Fin15AnchoredAtom1938 Fin15AnchoredAtom2158 Fin15AnchoredAtom2873 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 11, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 11, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 11, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 11, 14}, {0, 2, 3, 11, 14}, {0, 1, 3, 11, 14}, {0, 1, 2, 11, 14}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28261 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1829 Fin15AnchoredAtom1830 Fin15AnchoredAtom1884
    Fin15AnchoredAtom1939 Fin15AnchoredAtom2159 Fin15AnchoredAtom2874 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 12, 13}, {0, 2, 3, 12, 13}, {0, 1, 3, 12, 13}, {0, 1, 2, 12, 13}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28262 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1829 Fin15AnchoredAtom1831 Fin15AnchoredAtom1885
    Fin15AnchoredAtom1940 Fin15AnchoredAtom2160 Fin15AnchoredAtom2875 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 12, 14}, {0, 2, 3, 12, 14}, {0, 1, 3, 12, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28263 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2876 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1830 Fin15AnchoredAtom1831 Fin15AnchoredAtom1886
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2161 Fin15AnchoredAtom2876 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 3, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 3, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 3, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 3, 13, 14}, {0, 2, 3, 13, 14}, {0, 1, 3, 13, 14}, {0, 1, 2, 13, 14}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28264 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1842
    Fin15AnchoredAtom1942 Fin15AnchoredAtom2162 Fin15AnchoredAtom2877 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 5, 6}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 5, 6} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 5, 6} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 5, 6}, {0, 2, 4, 5, 6}, {0, 1, 4, 5, 6}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28265 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1843
    Fin15AnchoredAtom1943 Fin15AnchoredAtom2163 Fin15AnchoredAtom2878 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 5, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 5, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 5, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 5, 7}, {0, 2, 4, 5, 7}, {0, 1, 4, 5, 7}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28266 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2880 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1836 Fin15AnchoredAtom1845
    Fin15AnchoredAtom1945 Fin15AnchoredAtom2165 Fin15AnchoredAtom2880 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 5, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 5, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 5, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 5, 9}, {0, 2, 4, 5, 9}, {0, 1, 4, 5, 9}, {0, 1, 2, 5, 9}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28267 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2881 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1837 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1946 Fin15AnchoredAtom2166 Fin15AnchoredAtom2881 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 5, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 5, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 5, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 5, 10}, {0, 2, 4, 5, 10}, {0, 1, 4, 5, 10}, {0, 1, 2, 5, 10}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28268 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1839 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1948 Fin15AnchoredAtom2168 Fin15AnchoredAtom2883 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 5, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 5, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 5, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 5, 12}, {0, 2, 4, 5, 12}, {0, 1, 4, 5, 12}, {0, 1, 2, 5, 12}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28269 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1840 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1949 Fin15AnchoredAtom2169 Fin15AnchoredAtom2884 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 5, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 5, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 5, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 5, 13}, {0, 2, 4, 5, 13}, {0, 1, 4, 5, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28270 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1832 Fin15AnchoredAtom1841 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1950 Fin15AnchoredAtom2170 Fin15AnchoredAtom2885 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 5, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 5, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 5, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 5, 14}, {0, 2, 4, 5, 14}, {0, 1, 4, 5, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28271 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1851
    Fin15AnchoredAtom1951 Fin15AnchoredAtom2171 Fin15AnchoredAtom2886 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 6, 7}, {0, 2, 4, 6, 7}, {0, 1, 4, 6, 7}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28272 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1836 Fin15AnchoredAtom1853
    Fin15AnchoredAtom1953 Fin15AnchoredAtom2173 Fin15AnchoredAtom2888 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 6, 9}, {0, 2, 4, 6, 9}, {0, 1, 4, 6, 9}, {0, 1, 2, 6, 9}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28273 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1837 Fin15AnchoredAtom1854
    Fin15AnchoredAtom1954 Fin15AnchoredAtom2174 Fin15AnchoredAtom2889 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 6, 10}, {0, 2, 4, 6, 10}, {0, 1, 4, 6, 10}, {0, 1, 2, 6, 10}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28274 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1839 Fin15AnchoredAtom1856
    Fin15AnchoredAtom1956 Fin15AnchoredAtom2176 Fin15AnchoredAtom2891 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 6, 12}, {0, 2, 4, 6, 12}, {0, 1, 4, 6, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28275 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2892 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1840 Fin15AnchoredAtom1857
    Fin15AnchoredAtom1957 Fin15AnchoredAtom2177 Fin15AnchoredAtom2892 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 6, 13}, {0, 2, 4, 6, 13}, {0, 1, 4, 6, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28276 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1833 Fin15AnchoredAtom1841 Fin15AnchoredAtom1858
    Fin15AnchoredAtom1958 Fin15AnchoredAtom2178 Fin15AnchoredAtom2893 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 6, 14}, {0, 2, 4, 6, 14}, {0, 1, 4, 6, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28277 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1836 Fin15AnchoredAtom1860
    Fin15AnchoredAtom1960 Fin15AnchoredAtom2180 Fin15AnchoredAtom2895 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 7, 9}, {0, 2, 4, 7, 9}, {0, 1, 4, 7, 9}, {0, 1, 2, 7, 9}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28278 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1837 Fin15AnchoredAtom1861
    Fin15AnchoredAtom1961 Fin15AnchoredAtom2181 Fin15AnchoredAtom2896 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 7, 10}, {0, 2, 4, 7, 10}, {0, 1, 4, 7, 10}, {0, 1, 2, 7, 10}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28279 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1839 Fin15AnchoredAtom1863
    Fin15AnchoredAtom1963 Fin15AnchoredAtom2183 Fin15AnchoredAtom2898 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 7, 12}, {0, 2, 4, 7, 12}, {0, 1, 4, 7, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28280 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1840 Fin15AnchoredAtom1864
    Fin15AnchoredAtom1964 Fin15AnchoredAtom2184 Fin15AnchoredAtom2899 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 7, 13}, {0, 2, 4, 7, 13}, {0, 1, 4, 7, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28281 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1834 Fin15AnchoredAtom1841 Fin15AnchoredAtom1865
    Fin15AnchoredAtom1965 Fin15AnchoredAtom2185 Fin15AnchoredAtom2900 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 7, 14}, {0, 2, 4, 7, 14}, {0, 1, 4, 7, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28282 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1835 chi ∧
      Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1866 chi ∧
      Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom2186 chi ∧
      Fin15AnchoredAtom2901 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1835 Fin15AnchoredAtom1836 Fin15AnchoredAtom1866
    Fin15AnchoredAtom1966 Fin15AnchoredAtom2186 Fin15AnchoredAtom2901 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 8, 9}, {0, 2, 4, 8, 9}, {0, 1, 4, 8, 9}, {0, 1, 2, 8, 9}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28283 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1835 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1871 chi ∧
      Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom2191 chi ∧
      Fin15AnchoredAtom2906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1835 Fin15AnchoredAtom1841 Fin15AnchoredAtom1871
    Fin15AnchoredAtom1971 Fin15AnchoredAtom2191 Fin15AnchoredAtom2906 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 8, 14}, {0, 2, 4, 8, 14}, {0, 1, 4, 8, 14}, {0, 1, 2, 8, 14}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28284 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1836 Fin15AnchoredAtom1837 Fin15AnchoredAtom1872
    Fin15AnchoredAtom1972 Fin15AnchoredAtom2192 Fin15AnchoredAtom2907 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 9, 10}, {0, 2, 4, 9, 10}, {0, 1, 4, 9, 10}, {0, 1, 2, 9, 10}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28285 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2909 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1836 Fin15AnchoredAtom1839 Fin15AnchoredAtom1874
    Fin15AnchoredAtom1974 Fin15AnchoredAtom2194 Fin15AnchoredAtom2909 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 9, 12}, {0, 2, 4, 9, 12}, {0, 1, 4, 9, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28286 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1836 Fin15AnchoredAtom1840 Fin15AnchoredAtom1875
    Fin15AnchoredAtom1975 Fin15AnchoredAtom2195 Fin15AnchoredAtom2910 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 9, 13}, {0, 2, 4, 9, 13}, {0, 1, 4, 9, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28287 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1836 Fin15AnchoredAtom1841 Fin15AnchoredAtom1876
    Fin15AnchoredAtom1976 Fin15AnchoredAtom2196 Fin15AnchoredAtom2911 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 1, 2, 4, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 1, 2, 4, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 1, 2, 4, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{1, 2, 4, 9, 14}, {0, 2, 4, 9, 14}, {0, 1, 4, 9, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

end ErdosSzekeres

end
