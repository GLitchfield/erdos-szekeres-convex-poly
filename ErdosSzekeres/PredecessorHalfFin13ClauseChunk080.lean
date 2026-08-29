module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 080. -/

theorem predecessorHalfFin13_clause23434 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom2047 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23435 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom2047 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23436 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2047 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom2047 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23437 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom2048 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23438 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom2048 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23439 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom2048 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23440 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom2048 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23441 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom2048 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23442 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2048 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0810
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom2048 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23443 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom2049 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23444 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom2049 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23445 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom2049 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23446 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom2049 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23447 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom2049 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23448 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2049 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0811
    PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom2049 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23449 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom2050 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2360
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23450 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0797 PredecessorHalfFin13Atom2050 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2360
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23451 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom2050 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2360
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23452 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom2050 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2360
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23453 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom2050 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2360
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23455 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom2051 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23456 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom2051 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23457 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom2051 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23458 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom2051 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23459 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom2051 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23460 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2051 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom0813
    PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom2051 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23461 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom2052 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23462 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom2052 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23463 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom2052 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23464 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom2052 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23465 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom2052 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23466 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2052 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0814
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom2052 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23467 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom2053 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2616
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23468 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0797 PredecessorHalfFin13Atom2053 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2616
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23469 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom2053 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2616
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23470 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom2053 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2616
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23471 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom2053 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2616
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23472 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2053 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0892 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0797 PredecessorHalfFin13Atom0815
    PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom2053 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2616
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23473 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom2054 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23474 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom2054 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23475 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom2054 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23476 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom2054 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23477 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom2054 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23478 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2054 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom2054 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23479 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom2055 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3128
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23480 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0797 PredecessorHalfFin13Atom2055 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3128
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23481 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom2055 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3128
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23482 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom2055 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3128
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23483 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom2055 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3128
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23485 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom2056 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5176
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23486 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom2056 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5176
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23487 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom2056 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5176
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23488 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom2056 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5176
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23489 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom2056 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5176
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23490 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2056 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom2056 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5176
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23491 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0797 PredecessorHalfFin13Atom2057 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6200
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23492 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom2057 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6200
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23493 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0819 PredecessorHalfFin13Atom2057 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6200
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23494 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0840 PredecessorHalfFin13Atom2057 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6200
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23495 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom0896 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0896 PredecessorHalfFin13Atom2057 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6200
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23497 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom2058 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23498 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom2058 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23499 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom2058 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23500 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom2058 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23501 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom2058 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23502 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2058 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0805
    PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom2058 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23503 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom2059 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23504 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom2059 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23505 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom2059 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23506 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom2059 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23507 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom2059 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23508 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2059 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0806
    PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom2059 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23509 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom2060 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23510 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom2060 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23511 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom2060 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23512 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom2060 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23513 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom2060 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23514 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2060 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0807
    PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom2060 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23515 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom2061 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23516 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom2061 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23517 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom2061 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23518 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom2061 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23519 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom2061 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23521 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom2062 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23522 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom2062 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23523 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom2062 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23524 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom2062 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23525 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom2062 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23526 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2062 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom2062 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23527 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom2063 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23528 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom2063 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23529 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom2063 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23530 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom2063 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23531 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom2063 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23532 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2063 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0810
    PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom2063 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23533 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom2064 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23534 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom2064 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23535 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom2064 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23536 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom2064 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23537 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom2064 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23538 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2064 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0811
    PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom2064 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23539 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom2065 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2392
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23540 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom2065 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2392
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23541 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom2065 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2392
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23542 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom2065 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2392
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23543 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom2065 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2392
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23545 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom2066 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23546 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom2066 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23547 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom2066 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23548 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom2066 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23549 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom2066 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23550 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2066 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom0813
    PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom2066 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23551 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom2067 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23552 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom2067 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23553 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom2067 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23554 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom2067 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23555 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom2067 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23556 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2067 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0814
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom2067 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23557 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom2068 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23558 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom2068 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23559 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom2068 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23560 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom2068 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23561 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom2068 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23562 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2068 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0907 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom0815
    PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom2068 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23563 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom2069 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23564 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom2069 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23565 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom2069 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23566 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom2069 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4696
  ] at hbad
  tauto

end ErdosSzekeres

end
