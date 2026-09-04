module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 202. -/

theorem fin15Anchored_clause25856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom4218 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09768
  ] at hbad
  tauto

theorem fin15Anchored_clause25857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom4218 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09768
  ] at hbad
  tauto

theorem fin15Anchored_clause25858 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom1395 Fin15AnchoredAtom1399
    Fin15AnchoredAtom1473 Fin15AnchoredAtom1677 Fin15AnchoredAtom4218 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09768
  ] at hbad
  tauto

theorem fin15Anchored_clause25859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom4219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17960
  ] at hbad
  tauto

theorem fin15Anchored_clause25860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1396 Fin15AnchoredAtom4219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17960
  ] at hbad
  tauto

theorem fin15Anchored_clause25861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1400 Fin15AnchoredAtom4219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17960
  ] at hbad
  tauto

theorem fin15Anchored_clause25862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1474 Fin15AnchoredAtom4219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17960
  ] at hbad
  tauto

theorem fin15Anchored_clause25863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1678 Fin15AnchoredAtom4219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17960
  ] at hbad
  tauto

theorem fin15Anchored_clause25864 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom1396 Fin15AnchoredAtom1400
    Fin15AnchoredAtom1474 Fin15AnchoredAtom1678 Fin15AnchoredAtom4219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17960
  ] at hbad
  tauto

theorem fin15Anchored_clause25865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4220 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom4220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06696
  ] at hbad
  tauto

theorem fin15Anchored_clause25866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4220 chi ∧
      ¬Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1679 Fin15AnchoredAtom4220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06696
  ] at hbad
  tauto

theorem fin15Anchored_clause25867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4221 chi ∧
      ¬Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1680 Fin15AnchoredAtom4221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10792
  ] at hbad
  tauto

theorem fin15Anchored_clause25868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4222 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1396 Fin15AnchoredAtom4222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18984
  ] at hbad
  tauto

theorem fin15Anchored_clause25869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4222 chi ∧
      ¬Fin15AnchoredAtom1681 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1681 Fin15AnchoredAtom4222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18984
  ] at hbad
  tauto

theorem fin15Anchored_clause25870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom4223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12840
  ] at hbad
  tauto

theorem fin15Anchored_clause25871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1395 Fin15AnchoredAtom4223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12840
  ] at hbad
  tauto

theorem fin15Anchored_clause25872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1404 Fin15AnchoredAtom4223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12840
  ] at hbad
  tauto

theorem fin15Anchored_clause25873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom4223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12840
  ] at hbad
  tauto

theorem fin15Anchored_clause25874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom4223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12840
  ] at hbad
  tauto

theorem fin15Anchored_clause25875 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom1395 Fin15AnchoredAtom1404
    Fin15AnchoredAtom1478 Fin15AnchoredAtom1682 Fin15AnchoredAtom4223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12840
  ] at hbad
  tauto

theorem fin15Anchored_clause25876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom4224 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21032
  ] at hbad
  tauto

theorem fin15Anchored_clause25877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1396 Fin15AnchoredAtom4224 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21032
  ] at hbad
  tauto

theorem fin15Anchored_clause25878 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1405 Fin15AnchoredAtom4224 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21032
  ] at hbad
  tauto

theorem fin15Anchored_clause25879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1479 Fin15AnchoredAtom4224 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21032
  ] at hbad
  tauto

theorem fin15Anchored_clause25880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1683 Fin15AnchoredAtom4224 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21032
  ] at hbad
  tauto

theorem fin15Anchored_clause25881 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom1396 Fin15AnchoredAtom1405
    Fin15AnchoredAtom1479 Fin15AnchoredAtom1683 Fin15AnchoredAtom4224 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21032
  ] at hbad
  tauto

theorem fin15Anchored_clause25882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1395 Fin15AnchoredAtom4225 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25128
  ] at hbad
  tauto

theorem fin15Anchored_clause25883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1396 Fin15AnchoredAtom4225 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25128
  ] at hbad
  tauto

theorem fin15Anchored_clause25884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1406 Fin15AnchoredAtom4225 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25128
  ] at hbad
  tauto

theorem fin15Anchored_clause25885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1480 Fin15AnchoredAtom4225 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25128
  ] at hbad
  tauto

theorem fin15Anchored_clause25886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1684 Fin15AnchoredAtom4225 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25128
  ] at hbad
  tauto

theorem fin15Anchored_clause25887 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1395 Fin15AnchoredAtom1396 Fin15AnchoredAtom1406
    Fin15AnchoredAtom1480 Fin15AnchoredAtom1684 Fin15AnchoredAtom4225 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25128
  ] at hbad
  tauto

theorem fin15Anchored_clause25888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4226 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom4226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07208
  ] at hbad
  tauto

theorem fin15Anchored_clause25889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4226 chi ∧
      ¬Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1481 Fin15AnchoredAtom4226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07208
  ] at hbad
  tauto

theorem fin15Anchored_clause25890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4226 chi ∧
      ¬Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1685 Fin15AnchoredAtom4226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07208
  ] at hbad
  tauto

theorem fin15Anchored_clause25891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4227 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom4227 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11304
  ] at hbad
  tauto

theorem fin15Anchored_clause25892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4227 chi ∧
      ¬Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1686 Fin15AnchoredAtom4227 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11304
  ] at hbad
  tauto

theorem fin15Anchored_clause25893 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4227 chi ∧
      Fin15AnchoredAtom1397 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1402 chi ∧
      Fin15AnchoredAtom1482 chi ∧
      Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1397 Fin15AnchoredAtom1399 Fin15AnchoredAtom1402
    Fin15AnchoredAtom1482 Fin15AnchoredAtom1686 Fin15AnchoredAtom4227 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11304
  ] at hbad
  tauto

theorem fin15Anchored_clause25894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom4229 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13352
  ] at hbad
  tauto

theorem fin15Anchored_clause25895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom4229 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13352
  ] at hbad
  tauto

theorem fin15Anchored_clause25896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1404 Fin15AnchoredAtom4229 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13352
  ] at hbad
  tauto

theorem fin15Anchored_clause25897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom4229 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13352
  ] at hbad
  tauto

theorem fin15Anchored_clause25898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom4229 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13352
  ] at hbad
  tauto

theorem fin15Anchored_clause25899 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom1399 Fin15AnchoredAtom1404
    Fin15AnchoredAtom1484 Fin15AnchoredAtom1688 Fin15AnchoredAtom4229 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13352
  ] at hbad
  tauto

theorem fin15Anchored_clause25900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom4230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21544
  ] at hbad
  tauto

theorem fin15Anchored_clause25901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1400 Fin15AnchoredAtom4230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21544
  ] at hbad
  tauto

theorem fin15Anchored_clause25902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1405 Fin15AnchoredAtom4230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21544
  ] at hbad
  tauto

theorem fin15Anchored_clause25903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1485 Fin15AnchoredAtom4230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21544
  ] at hbad
  tauto

theorem fin15Anchored_clause25904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1689 Fin15AnchoredAtom4230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21544
  ] at hbad
  tauto

theorem fin15Anchored_clause25905 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom1400 Fin15AnchoredAtom1405
    Fin15AnchoredAtom1485 Fin15AnchoredAtom1689 Fin15AnchoredAtom4230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21544
  ] at hbad
  tauto

theorem fin15Anchored_clause25906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom4231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25640
  ] at hbad
  tauto

theorem fin15Anchored_clause25907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1400 Fin15AnchoredAtom4231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25640
  ] at hbad
  tauto

theorem fin15Anchored_clause25908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1406 Fin15AnchoredAtom4231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25640
  ] at hbad
  tauto

theorem fin15Anchored_clause25909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1486 Fin15AnchoredAtom4231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25640
  ] at hbad
  tauto

theorem fin15Anchored_clause25910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1690 Fin15AnchoredAtom4231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25640
  ] at hbad
  tauto

theorem fin15Anchored_clause25911 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom1400 Fin15AnchoredAtom1406
    Fin15AnchoredAtom1486 Fin15AnchoredAtom1690 Fin15AnchoredAtom4231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25640
  ] at hbad
  tauto

theorem fin15Anchored_clause25912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4232 chi ∧
      ¬Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1487 Fin15AnchoredAtom4232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14376
  ] at hbad
  tauto

theorem fin15Anchored_clause25913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4232 chi ∧
      ¬Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1691 Fin15AnchoredAtom4232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14376
  ] at hbad
  tauto

theorem fin15Anchored_clause25914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4233 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1405 Fin15AnchoredAtom4233 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22568
  ] at hbad
  tauto

theorem fin15Anchored_clause25915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4234 chi ∧
      ¬Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1693 Fin15AnchoredAtom4234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26664
  ] at hbad
  tauto

theorem fin15Anchored_clause25916 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4234 chi ∧
      Fin15AnchoredAtom1402 chi ∧
      Fin15AnchoredAtom1403 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1489 chi ∧
      Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1402 Fin15AnchoredAtom1403 Fin15AnchoredAtom1406
    Fin15AnchoredAtom1489 Fin15AnchoredAtom1693 Fin15AnchoredAtom4234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26664
  ] at hbad
  tauto

theorem fin15Anchored_clause25917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1404 Fin15AnchoredAtom4235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28712
  ] at hbad
  tauto

theorem fin15Anchored_clause25918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1405 Fin15AnchoredAtom4235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28712
  ] at hbad
  tauto

theorem fin15Anchored_clause25919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1406 Fin15AnchoredAtom4235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28712
  ] at hbad
  tauto

theorem fin15Anchored_clause25920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1490 Fin15AnchoredAtom4235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28712
  ] at hbad
  tauto

theorem fin15Anchored_clause25921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1694 Fin15AnchoredAtom4235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28712
  ] at hbad
  tauto

theorem fin15Anchored_clause25922 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1404 Fin15AnchoredAtom1405 Fin15AnchoredAtom1406
    Fin15AnchoredAtom1490 Fin15AnchoredAtom1694 Fin15AnchoredAtom4235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28712
  ] at hbad
  tauto

theorem fin15Anchored_clause25923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom4236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00968
  ] at hbad
  tauto

theorem fin15Anchored_clause25924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom4236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00968
  ] at hbad
  tauto

theorem fin15Anchored_clause25925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom4236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00968
  ] at hbad
  tauto

theorem fin15Anchored_clause25926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom4236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00968
  ] at hbad
  tauto

theorem fin15Anchored_clause25927 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4236 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom1408 Fin15AnchoredAtom1414
    Fin15AnchoredAtom1435 Fin15AnchoredAtom1695 Fin15AnchoredAtom4236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00968
  ] at hbad
  tauto

theorem fin15Anchored_clause25928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom4237 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01480
  ] at hbad
  tauto

theorem fin15Anchored_clause25929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom4237 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01480
  ] at hbad
  tauto

theorem fin15Anchored_clause25930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom4237 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01480
  ] at hbad
  tauto

theorem fin15Anchored_clause25931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom4237 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01480
  ] at hbad
  tauto

theorem fin15Anchored_clause25932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom4237 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01480
  ] at hbad
  tauto

theorem fin15Anchored_clause25933 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4237 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom1409 Fin15AnchoredAtom1415
    Fin15AnchoredAtom1436 Fin15AnchoredAtom1696 Fin15AnchoredAtom4237 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01480
  ] at hbad
  tauto

theorem fin15Anchored_clause25934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom4239 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04552
  ] at hbad
  tauto

theorem fin15Anchored_clause25935 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom4239 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04552
  ] at hbad
  tauto

theorem fin15Anchored_clause25936 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1417 Fin15AnchoredAtom4239 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04552
  ] at hbad
  tauto

theorem fin15Anchored_clause25937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1698 Fin15AnchoredAtom4239 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04552
  ] at hbad
  tauto

theorem fin15Anchored_clause25938 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4239 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom1411 Fin15AnchoredAtom1417
    Fin15AnchoredAtom1438 Fin15AnchoredAtom1698 Fin15AnchoredAtom4239 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04552
  ] at hbad
  tauto

theorem fin15Anchored_clause25939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom4240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08648
  ] at hbad
  tauto

theorem fin15Anchored_clause25940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1412 Fin15AnchoredAtom4240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08648
  ] at hbad
  tauto

theorem fin15Anchored_clause25941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1418 Fin15AnchoredAtom4240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08648
  ] at hbad
  tauto

theorem fin15Anchored_clause25942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1699 Fin15AnchoredAtom4240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08648
  ] at hbad
  tauto

theorem fin15Anchored_clause25943 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4240 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom1412 Fin15AnchoredAtom1418
    Fin15AnchoredAtom1439 Fin15AnchoredAtom1699 Fin15AnchoredAtom4240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08648
  ] at hbad
  tauto

theorem fin15Anchored_clause25944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom4241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16840
  ] at hbad
  tauto

theorem fin15Anchored_clause25945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1413 Fin15AnchoredAtom4241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16840
  ] at hbad
  tauto

theorem fin15Anchored_clause25946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1419 Fin15AnchoredAtom4241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16840
  ] at hbad
  tauto

theorem fin15Anchored_clause25947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1440 Fin15AnchoredAtom4241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16840
  ] at hbad
  tauto

theorem fin15Anchored_clause25948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1700 Fin15AnchoredAtom4241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16840
  ] at hbad
  tauto

theorem fin15Anchored_clause25949 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4241 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom1413 Fin15AnchoredAtom1419
    Fin15AnchoredAtom1440 Fin15AnchoredAtom1700 Fin15AnchoredAtom4241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16840
  ] at hbad
  tauto

theorem fin15Anchored_clause25950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom4242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01736
  ] at hbad
  tauto

theorem fin15Anchored_clause25951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom4242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01736
  ] at hbad
  tauto

theorem fin15Anchored_clause25952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom4242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01736
  ] at hbad
  tauto

theorem fin15Anchored_clause25953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom4242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01736
  ] at hbad
  tauto

theorem fin15Anchored_clause25954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom4242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01736
  ] at hbad
  tauto

theorem fin15Anchored_clause25955 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom1409 Fin15AnchoredAtom1420
    Fin15AnchoredAtom1441 Fin15AnchoredAtom1701 Fin15AnchoredAtom4242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01736
  ] at hbad
  tauto

theorem fin15Anchored_clause25956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4243 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom4243 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02760
  ] at hbad
  tauto

theorem fin15Anchored_clause25957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom4244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04808
  ] at hbad
  tauto

theorem fin15Anchored_clause25958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom4244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04808
  ] at hbad
  tauto

theorem fin15Anchored_clause25959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom4244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04808
  ] at hbad
  tauto

theorem fin15Anchored_clause25960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom4244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04808
  ] at hbad
  tauto

theorem fin15Anchored_clause25961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom4244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04808
  ] at hbad
  tauto

theorem fin15Anchored_clause25962 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom1411 Fin15AnchoredAtom1422
    Fin15AnchoredAtom1443 Fin15AnchoredAtom1703 Fin15AnchoredAtom4244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04808
  ] at hbad
  tauto

theorem fin15Anchored_clause25963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom4245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08904
  ] at hbad
  tauto

theorem fin15Anchored_clause25964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1412 Fin15AnchoredAtom4245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08904
  ] at hbad
  tauto

theorem fin15Anchored_clause25965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom4245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08904
  ] at hbad
  tauto

theorem fin15Anchored_clause25966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom4245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08904
  ] at hbad
  tauto

theorem fin15Anchored_clause25967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom4245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08904
  ] at hbad
  tauto

theorem fin15Anchored_clause25968 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom1412 Fin15AnchoredAtom1423
    Fin15AnchoredAtom1444 Fin15AnchoredAtom1704 Fin15AnchoredAtom4245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08904
  ] at hbad
  tauto

theorem fin15Anchored_clause25969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom4246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17096
  ] at hbad
  tauto

theorem fin15Anchored_clause25970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1413 Fin15AnchoredAtom4246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17096
  ] at hbad
  tauto

theorem fin15Anchored_clause25971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1424 Fin15AnchoredAtom4246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17096
  ] at hbad
  tauto

theorem fin15Anchored_clause25972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1445 Fin15AnchoredAtom4246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17096
  ] at hbad
  tauto

theorem fin15Anchored_clause25973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1705 Fin15AnchoredAtom4246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17096
  ] at hbad
  tauto

theorem fin15Anchored_clause25974 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom1413 Fin15AnchoredAtom1424
    Fin15AnchoredAtom1445 Fin15AnchoredAtom1705 Fin15AnchoredAtom4246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17096
  ] at hbad
  tauto

theorem fin15Anchored_clause25975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4247 chi ∧
      ¬Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1706 Fin15AnchoredAtom4247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03272
  ] at hbad
  tauto

theorem fin15Anchored_clause25976 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4247 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1410 chi ∧
      Fin15AnchoredAtom1425 chi ∧
      Fin15AnchoredAtom1446 chi ∧
      Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom1410 Fin15AnchoredAtom1425
    Fin15AnchoredAtom1446 Fin15AnchoredAtom1706 Fin15AnchoredAtom4247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03272
  ] at hbad
  tauto

theorem fin15Anchored_clause25977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom4248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05320
  ] at hbad
  tauto

theorem fin15Anchored_clause25978 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom4248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05320
  ] at hbad
  tauto

theorem fin15Anchored_clause25979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom4248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05320
  ] at hbad
  tauto

theorem fin15Anchored_clause25980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom4248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05320
  ] at hbad
  tauto

theorem fin15Anchored_clause25981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom4248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05320
  ] at hbad
  tauto

theorem fin15Anchored_clause25982 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom1411 Fin15AnchoredAtom1426
    Fin15AnchoredAtom1447 Fin15AnchoredAtom1707 Fin15AnchoredAtom4248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05320
  ] at hbad
  tauto

theorem fin15Anchored_clause25983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom4249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09416
  ] at hbad
  tauto

end ErdosSzekeres

end
