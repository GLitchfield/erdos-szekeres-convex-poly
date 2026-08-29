module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 078. -/

theorem predecessorHalfFin13_clause23132 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom1997 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23133 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0756 PredecessorHalfFin13Atom1997 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23134 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom0787 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0787 PredecessorHalfFin13Atom1997 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23135 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0962 PredecessorHalfFin13Atom1997 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23137 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom1998 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23138 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom1998 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23139 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom1998 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23140 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom1998 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23141 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom1998 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23143 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom1999 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23144 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom1999 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23145 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom1999 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23146 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom1999 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23147 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom1999 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23148 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1999 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom1999 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23149 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom2000 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23150 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom2000 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23151 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0756 PredecessorHalfFin13Atom2000 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23152 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0790 PredecessorHalfFin13Atom2000 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23153 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0965 PredecessorHalfFin13Atom2000 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23155 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom2001 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23156 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom2001 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23157 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0756 PredecessorHalfFin13Atom2001 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23158 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom2001 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23159 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom2001 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23161 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom2002 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0964
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23162 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom2002 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0964
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23163 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom2002 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0964
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23164 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom2002 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0964
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23165 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom2002 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0964
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23166 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2002 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0762
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom2002 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0964
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23167 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom2003 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1476
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23168 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom2003 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1476
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23169 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom2003 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1476
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23170 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom2003 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1476
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23171 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom2003 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1476
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23172 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2003 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0763
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom2003 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1476
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23173 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom2004 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2500
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23174 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom2004 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2500
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23175 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0764 PredecessorHalfFin13Atom2004 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2500
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23176 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom2004 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2500
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23177 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom2004 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2500
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23179 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom2005 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4548
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23180 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom2005 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4548
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23181 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom2005 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4548
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23182 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom2005 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4548
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23183 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom2005 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4548
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23184 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2005 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0765
    PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom2005 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4548
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23185 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom2006 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1732
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23186 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom2006 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1732
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23187 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom2006 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1732
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23188 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom2006 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1732
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23189 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom2006 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1732
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23190 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2006 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0766
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom2006 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1732
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23191 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom2007 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2756
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23192 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom2007 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2756
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23193 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom2007 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2756
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23194 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom2007 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2756
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23195 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom2007 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2756
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23197 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom2008 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23198 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom2008 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23199 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom2008 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23200 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom2008 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23201 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom2008 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23202 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2008 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0768
    PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom2008 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23203 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom2009 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23204 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom2009 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23205 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0769 PredecessorHalfFin13Atom2009 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23206 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0779 PredecessorHalfFin13Atom2009 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23207 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom2009 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23208 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2009 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0760 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom0769
    PredecessorHalfFin13Atom0779 PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom2009 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23209 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom2010 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23210 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom2010 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23211 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom2010 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23212 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom2010 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23213 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom2010 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23214 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2010 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom2010 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23215 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2011 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom2011 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6340
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23216 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2011 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom2011 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6340
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23221 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom2012 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1860
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23222 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom2012 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1860
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23223 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom2012 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1860
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23224 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom2012 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1860
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23225 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom2012 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1860
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23226 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2012 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0766
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom2012 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1860
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23227 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom2013 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2884
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23228 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0764 PredecessorHalfFin13Atom2013 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2884
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23229 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom2013 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2884
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23230 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom2013 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2884
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23231 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom2013 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2884
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23233 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom2014 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23234 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom2014 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23235 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom2014 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23236 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom2014 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23237 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom2014 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23238 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2014 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0768
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom2014 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23239 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom2015 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23240 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0764 PredecessorHalfFin13Atom2015 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23241 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0769 PredecessorHalfFin13Atom2015 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23242 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom2015 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23243 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom2015 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23245 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom2016 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23246 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom2016 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23247 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom2016 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23248 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom2016 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23249 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom2016 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23250 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2016 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom2016 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23252 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom2017 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23254 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom0787 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0787 PredecessorHalfFin13Atom2017 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23255 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0982 PredecessorHalfFin13Atom2017 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23257 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom2018 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23258 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom2018 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23259 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0769 PredecessorHalfFin13Atom2018 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23260 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom2018 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23261 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom2018 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23263 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom2019 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23264 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom2019 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23265 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom2019 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23266 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom2019 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23267 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom2019 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23268 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2019 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom2019 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23270 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom2020 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23272 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0790 PredecessorHalfFin13Atom2020 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23273 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0985 PredecessorHalfFin13Atom2020 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23276 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom2021 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23278 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom2021 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23279 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0986 PredecessorHalfFin13Atom2021 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23281 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom2022 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1924
  ] at hbad
  tauto

end ErdosSzekeres

end
