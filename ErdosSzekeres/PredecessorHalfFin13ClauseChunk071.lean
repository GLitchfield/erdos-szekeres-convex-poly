module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 071. -/

theorem predecessorHalfFin13_clause22172 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom1837 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1116
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22173 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom1837 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1116
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22174 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom1837 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1116
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22175 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom1837 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1116
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22176 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1837 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0690
    PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom1837 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1116
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22177 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom1838 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2140
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22178 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0678 PredecessorHalfFin13Atom1838 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2140
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22179 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0691 PredecessorHalfFin13Atom1838 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2140
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22180 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom1838 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2140
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22181 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom1838 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2140
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22183 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom1839 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22184 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom1839 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22185 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom1839 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22186 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom1839 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22187 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom1839 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22188 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1839 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0804 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom1839 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22189 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom1840 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22190 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom1840 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22191 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom1840 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22192 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom1840 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22193 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom1840 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22194 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1840 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0805 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0693
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom1840 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22195 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom1841 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22196 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom1841 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22197 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom1841 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22198 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom1841 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22199 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom1841 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22200 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1841 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0806 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0694
    PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom1841 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22201 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom1842 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1180
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22202 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom1842 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1180
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22203 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom1842 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1180
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22204 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom1842 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1180
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22205 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom1842 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1180
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22206 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1842 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0807 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0695
    PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom1842 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1180
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22207 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom1843 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22208 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0678 PredecessorHalfFin13Atom1843 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22209 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom1843 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22210 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom1843 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22211 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom1843 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22212 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1843 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0808 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0678 PredecessorHalfFin13Atom0696
    PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom1843 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22213 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom1844 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22214 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom1844 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22215 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom1844 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22216 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom1844 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22217 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom1844 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22218 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1844 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0809 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom1844 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22219 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom1845 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0796
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22220 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom1845 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0796
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22221 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom1845 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0796
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22222 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom1845 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0796
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22223 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom1845 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0796
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22224 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1845 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0810 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0698
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom1845 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0796
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22225 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom1846 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22226 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom1846 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22227 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom1846 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22228 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom1846 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22229 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom1846 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22230 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1846 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0811 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0699
    PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom1846 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22231 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom1847 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2332
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22232 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0678 PredecessorHalfFin13Atom1847 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2332
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22233 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0700 PredecessorHalfFin13Atom1847 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2332
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22234 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom1847 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2332
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22235 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom1847 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2332
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22237 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom1848 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22238 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom1848 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22239 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom1848 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22240 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom1848 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22241 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom1848 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22242 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1848 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0813 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom1848 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22243 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom1849 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1564
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22244 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom1849 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1564
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22245 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom1849 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1564
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22246 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom1849 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1564
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22247 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom1849 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1564
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22248 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1849 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0814 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom1849 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1564
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22249 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom1850 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2588
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22250 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0678 PredecessorHalfFin13Atom1850 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2588
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22251 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0703 PredecessorHalfFin13Atom1850 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2588
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22252 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom1850 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2588
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22253 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom1850 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2588
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22255 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom1851 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22256 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom1851 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22257 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom1851 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22258 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom1851 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22259 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom1851 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22260 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1851 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0816 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom1851 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22261 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom1852 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3100
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22262 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0678 PredecessorHalfFin13Atom1852 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3100
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22263 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0705 PredecessorHalfFin13Atom1852 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3100
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22264 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0733 PredecessorHalfFin13Atom1852 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3100
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22265 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom1852 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3100
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22267 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom1853 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5148
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22268 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom1853 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5148
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22269 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom1853 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5148
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22270 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom1853 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5148
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22271 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom1853 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5148
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22272 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1853 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0818 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom1853 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5148
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22273 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0678 PredecessorHalfFin13Atom1854 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22274 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom1854 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22276 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom0735 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0735 PredecessorHalfFin13Atom1854 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22277 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0819 PredecessorHalfFin13Atom1854 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22279 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom1855 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22280 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom1855 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22281 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom1855 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22282 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom1855 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22283 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom1855 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22284 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1855 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0820 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0687
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom1855 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22285 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom1856 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22286 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom1856 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22287 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom1856 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22288 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom1856 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22289 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom1856 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22290 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1856 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0821 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0688
    PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom1856 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22291 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom1857 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22292 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom1857 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22293 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom1857 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22294 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom1857 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22295 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom1857 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22296 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1857 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0822 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0689
    PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom1857 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22297 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom1858 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1132
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22298 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom1858 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1132
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22299 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom1858 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1132
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22300 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom1858 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1132
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22301 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom1858 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1132
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22302 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1858 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0823 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0690
    PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom1858 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1132
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22303 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom1859 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22304 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom1859 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22305 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0691 PredecessorHalfFin13Atom1859 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2156
  ] at hbad
  tauto

end ErdosSzekeres

end
