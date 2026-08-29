module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 090. -/

theorem predecessorHalfFin13_clause24835 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2281 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom2281 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24836 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2281 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom2281 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24837 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2281 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0982 PredecessorHalfFin13Atom2281 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24838 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2281 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0986 PredecessorHalfFin13Atom2281 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24839 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2281 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom1000 PredecessorHalfFin13Atom2281 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24840 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2281 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0982 chi ∧
      PredecessorHalfFin13Atom0986 chi ∧
      PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0982
    PredecessorHalfFin13Atom0986 PredecessorHalfFin13Atom1000 PredecessorHalfFin13Atom2281 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24842 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2282 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom2282 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24843 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2282 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0985 PredecessorHalfFin13Atom2282 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24844 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2282 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0986 PredecessorHalfFin13Atom2282 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24845 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2282 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom1001 PredecessorHalfFin13Atom2282 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24847 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2283 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2283 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24848 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2283 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom2283 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24849 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2283 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom2283 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24850 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2283 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom2283 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24851 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2283 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0997 PredecessorHalfFin13Atom2283 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24852 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2283 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0988 chi ∧
      PredecessorHalfFin13Atom0990 chi ∧
      PredecessorHalfFin13Atom0993 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom0990
    PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom0997 PredecessorHalfFin13Atom2283 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24853 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2284 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6016
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24854 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2284 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6016
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24855 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2284 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6016
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24856 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2284 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6016
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24857 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2284 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6016
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24858 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2284 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom0991
    PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6016
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24859 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2285 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom2285 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7040
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24860 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2285 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2285 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7040
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24861 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2285 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0992 PredecessorHalfFin13Atom2285 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7040
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24862 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2285 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0995 PredecessorHalfFin13Atom2285 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7040
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24863 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2285 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0999 PredecessorHalfFin13Atom2285 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7040
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24866 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2286 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2286 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7552
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24868 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2286 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0996 PredecessorHalfFin13Atom2286 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7552
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24869 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2286 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom1000 PredecessorHalfFin13Atom2286 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7552
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24872 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2287 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2287 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7808
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24873 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2287 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0995 PredecessorHalfFin13Atom2287 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7808
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24874 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2287 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0996 PredecessorHalfFin13Atom2287 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7808
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24875 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2287 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom1001 PredecessorHalfFin13Atom2287 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7808
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24877 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2288 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0997 PredecessorHalfFin13Atom2288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24878 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2288 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24879 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2288 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0999 PredecessorHalfFin13Atom2288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24880 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2288 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom1000 PredecessorHalfFin13Atom2288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24881 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2288 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom1001 PredecessorHalfFin13Atom2288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24882 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2288 chi ∧
      PredecessorHalfFin13Atom0997 chi ∧
      PredecessorHalfFin13Atom0998 chi ∧
      PredecessorHalfFin13Atom0999 chi ∧
      PredecessorHalfFin13Atom1000 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0997 PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom0999
    PredecessorHalfFin13Atom1000 PredecessorHalfFin13Atom1001 PredecessorHalfFin13Atom2288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause25213 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 5, 6} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 5, 6}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0344
    PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0359
    PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0395
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0673
    PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0792 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25215 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 5, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 5, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0346
    PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0361
    PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0397
    PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0675
    PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0794 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25216 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 5, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 5, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0347
    PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0362
    PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0398
    PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0676
    PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0795 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25220 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 6, 7} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 6, 7}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0345
    PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0366
    PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0402
    PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0674
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0799 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25221 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 6, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 6, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0346
    PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0367
    PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0403
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0675
    PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0800 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25222 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 6, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 6, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0347
    PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0368
    PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0404
    PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0676
    PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0801 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25223 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 6, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 6, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0369
    PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0405
    PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0802 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25225 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0804 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 6, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 6, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom0371
    PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom0407
    PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0804 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25226 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0805 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0346
    PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0372
    PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0408
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0675
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0805 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25227 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0806 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0347
    PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0373
    PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0409
    PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0676
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0806 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25228 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0807 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0374
    PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0410
    PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0807 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25230 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0809 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom0376
    PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom0412
    PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0809 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25231 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0810 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0347
    PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0676
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0810 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25232 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0811 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0811 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25234 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0813 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0813 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25235 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0814 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0814 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25237 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0816 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0816 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25239 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0818 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 4, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 4, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0449 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom0818 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25241 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0820 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 6, 7} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 6, 7}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0345
    PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0366
    PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0402
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0681
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0820 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25242 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0821 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 6, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 6, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0346
    PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0367
    PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0403
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0682
    PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0821 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25243 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0822 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 6, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 6, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0347
    PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0368
    PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0404
    PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0683
    PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0822 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25244 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0823 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 6, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 6, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0369
    PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0405
    PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0684
    PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0823 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25246 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0825 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 6, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 6, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0371
    PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0407
    PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0825 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25247 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0826 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0346
    PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0372
    PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0408
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0682
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0826 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25248 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0827 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0347
    PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0373
    PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0409
    PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0683
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0827 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25249 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0828 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0374
    PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0410
    PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0684
    PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0828 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25251 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0830 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0376
    PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0412
    PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0830 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25252 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0831 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0347
    PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0683
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0831 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25253 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0684
    PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0832 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25255 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0834 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25256 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0684
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0835 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25258 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0837 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25260 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 5, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom0839 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25262 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0346
    PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0372
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0408
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0688
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0841 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25263 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0347
    PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0373
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0409
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0689
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0842 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25264 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 6, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0374
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0410
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0690
    PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0843 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25266 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 6, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0376
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0412
    PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0845 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25267 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0347
    PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0689
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0846 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25268 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 6, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0690
    PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0847 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25270 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 6, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0849 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25271 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 6, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0690
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0850 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25273 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 6, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0852 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25275 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0854 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 6, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0854 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25277 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0856 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0347
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0694
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0856 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25278 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0857 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0695
    PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0857 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25280 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0859 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0859 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25281 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0860 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0695
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0860 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25283 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0862 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25285 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0864 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25287 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0348
    PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0699
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0866 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25289 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0868 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25291 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0870 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25294 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 3, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0350
    PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0873 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25297 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 6, 7} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 6, 7}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0353
    PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0366
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0430
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0709
    PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0876 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25298 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 6, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 6, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0354
    PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0367
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0431
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0710
    PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0877 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25299 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 6, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 6, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0355
    PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0368
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0432
    PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0711
    PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0878 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25300 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 6, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 6, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0356
    PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0369
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0433
    PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0712
    PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0879 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25302 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 6, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 6, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0371
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0435
    PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0881 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25303 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0354
    PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0372
    PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0436
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0710
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0882 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25304 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0355
    PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0373
    PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0437
    PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0711
    PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0883 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25305 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0356
    PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0374
    PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0438
    PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0712
    PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0884 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25307 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0376
    PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0440
    PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0886 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25308 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0355
    PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0711
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0887 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25309 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0356
    PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0712
    PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0888 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25311 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0890 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25312 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0356
    PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0712
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0891 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25314 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0893 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25316 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 5, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 5, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom0895 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25318 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0354
    PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0372
    PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0436
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0716
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0897 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25319 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0355
    PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0373
    PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0437
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0717
    PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0898 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25320 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 6, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 6, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0356
    PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0374
    PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0438
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0718
    PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0899 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25323 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0355
    PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0717
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0902 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25324 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 6, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 6, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0356
    PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0718
    PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0903 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25326 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 6, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 6, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0905 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25327 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 6, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 6, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0356
    PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0718
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0906 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25329 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 6, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 6, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0908 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25331 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 6, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 6, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0910 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25333 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0355
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0722
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0912 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25334 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0356
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0723
    PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0913 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25336 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0915 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25337 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0356
    PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0723
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0916 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25339 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0918 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25341 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0920 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25343 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0356
    PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0727
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0922 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25345 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0924 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25347 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0926 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25350 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 4, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 4, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0929 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25353 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0361
    PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0372
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0457
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0737
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0932 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
