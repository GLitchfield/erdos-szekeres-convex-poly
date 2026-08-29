module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 065. -/

theorem predecessorHalfFin13_clause18893 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom1290 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0569
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18894 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1290 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0398
    PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom1290 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0569
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18895 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom1291 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1081
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18896 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom1291 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1081
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18897 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom1291 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1081
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18898 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom1291 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1081
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18899 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom1291 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1081
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18900 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1291 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0399
    PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom1291 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1081
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18907 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom1293 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4153
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18908 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom1293 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4153
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18909 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom1293 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4153
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18910 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom1293 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4153
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18911 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom1293 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4153
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18912 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1293 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom0401
    PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom1293 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4153
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18913 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom1294 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0217
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18914 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom1294 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0217
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18915 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom1294 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0217
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18916 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom1294 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0217
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18917 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom1294 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0217
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18918 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1294 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0402
    PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom1294 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0217
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18919 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom1295 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0345
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18920 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom1295 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0345
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18921 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom1295 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0345
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18922 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom1295 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0345
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18923 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom1295 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0345
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18924 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1295 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0403
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom1295 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0345
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18925 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom1296 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0601
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18926 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom1296 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0601
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18927 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom1296 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0601
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18928 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom1296 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0601
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18929 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom1296 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0601
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18930 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1296 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0404
    PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom1296 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0601
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18931 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom1297 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1113
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18932 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom1297 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1113
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18933 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom1297 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1113
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18934 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom1297 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1113
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18935 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom1297 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1113
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18936 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1297 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0405
    PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom1297 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1113
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18943 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom1299 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18944 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom1299 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18945 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom1299 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18946 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom1299 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18947 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom1299 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18948 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1299 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0804 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom0407
    PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom1299 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18949 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom1300 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18950 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom1300 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18951 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom1300 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18952 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom1300 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18953 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom1300 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18954 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1300 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0805 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0408
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom1300 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18955 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom1301 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0665
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18956 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom1301 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0665
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18957 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom1301 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0665
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18958 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom1301 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0665
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18959 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom1301 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0665
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18961 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom1302 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1177
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18962 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom1302 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1177
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18963 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom1302 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1177
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18964 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom1302 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1177
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18965 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom1302 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1177
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18966 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1302 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0807 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0410
    PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom1302 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1177
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18973 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom1304 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4249
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18974 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom1304 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4249
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18975 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom1304 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4249
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18976 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom1304 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4249
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18977 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom1304 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4249
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18978 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1304 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0809 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom0412
    PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom1304 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4249
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18979 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom1305 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0793
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18980 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom1305 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0793
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18981 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom1305 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0793
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18982 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom1305 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0793
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18983 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom1305 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0793
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18984 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1305 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0810 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom1305 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0793
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18985 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom1306 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18986 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom1306 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18987 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom1306 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18988 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom1306 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18989 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom1306 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18990 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1306 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0811 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom1306 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18997 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom1308 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18998 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom1308 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18999 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom1308 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19000 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom1308 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19001 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom1308 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19002 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1308 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0813 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom1308 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19003 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom1309 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1561
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19004 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom1309 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1561
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19005 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom1309 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1561
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19006 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom1309 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1561
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19007 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom1309 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1561
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19008 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1309 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0814 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom1309 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1561
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19015 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom1311 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4633
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19016 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom1311 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4633
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19017 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom1311 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4633
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19018 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom1311 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4633
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19019 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom1311 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4633
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19027 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom1313 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5145
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19028 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom1313 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5145
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19029 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0421 PredecessorHalfFin13Atom1313 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5145
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19030 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0449 PredecessorHalfFin13Atom1313 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5145
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19031 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom1313 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5145
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19032 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1313 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0818 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0449 PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom1313 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5145
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19039 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom1315 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19040 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom1315 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19041 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom1315 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19042 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom1315 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19043 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom1315 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19044 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1315 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0820 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0402
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom1315 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19045 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom1316 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19046 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom1316 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19047 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom1316 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19048 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom1316 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19049 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom1316 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19050 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1316 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0821 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0403
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom1316 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19051 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom1317 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19052 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom1317 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19053 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom1317 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19054 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom1317 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19055 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom1317 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19056 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1317 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0822 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0404
    PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom1317 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19057 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom1318 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1129
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19058 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom1318 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1129
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19059 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom1318 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1129
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19060 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom1318 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1129
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19061 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom1318 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1129
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19062 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1318 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0823 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0405
    PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom1318 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1129
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19069 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom1320 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19070 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom1320 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4201
  ] at hbad
  tauto

end ErdosSzekeres

end
