module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 192. -/

theorem fin15Anchored_clause24576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom3887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05668
  ] at hbad
  tauto

theorem fin15Anchored_clause24577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom3887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05668
  ] at hbad
  tauto

theorem fin15Anchored_clause24578 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1233 Fin15AnchoredAtom3887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05668
  ] at hbad
  tauto

theorem fin15Anchored_clause24579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom3887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05668
  ] at hbad
  tauto

theorem fin15Anchored_clause24580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom3887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05668
  ] at hbad
  tauto

theorem fin15Anchored_clause24581 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom1229 Fin15AnchoredAtom1233
    Fin15AnchoredAtom1307 Fin15AnchoredAtom1676 Fin15AnchoredAtom3887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05668
  ] at hbad
  tauto

theorem fin15Anchored_clause24582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom3888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09764
  ] at hbad
  tauto

theorem fin15Anchored_clause24583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1230 Fin15AnchoredAtom3888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09764
  ] at hbad
  tauto

theorem fin15Anchored_clause24584 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom3888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09764
  ] at hbad
  tauto

theorem fin15Anchored_clause24585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1308 Fin15AnchoredAtom3888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09764
  ] at hbad
  tauto

theorem fin15Anchored_clause24586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom3888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09764
  ] at hbad
  tauto

theorem fin15Anchored_clause24587 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom1230 Fin15AnchoredAtom1234
    Fin15AnchoredAtom1308 Fin15AnchoredAtom1677 Fin15AnchoredAtom3888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09764
  ] at hbad
  tauto

theorem fin15Anchored_clause24588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom3889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17956
  ] at hbad
  tauto

theorem fin15Anchored_clause24589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1231 Fin15AnchoredAtom3889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17956
  ] at hbad
  tauto

theorem fin15Anchored_clause24590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1235 Fin15AnchoredAtom3889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17956
  ] at hbad
  tauto

theorem fin15Anchored_clause24591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1309 Fin15AnchoredAtom3889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17956
  ] at hbad
  tauto

theorem fin15Anchored_clause24592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1678 Fin15AnchoredAtom3889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17956
  ] at hbad
  tauto

theorem fin15Anchored_clause24593 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom1231 Fin15AnchoredAtom1235
    Fin15AnchoredAtom1309 Fin15AnchoredAtom1678 Fin15AnchoredAtom3889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17956
  ] at hbad
  tauto

theorem fin15Anchored_clause24594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom3890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06692
  ] at hbad
  tauto

theorem fin15Anchored_clause24595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1310 Fin15AnchoredAtom3890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06692
  ] at hbad
  tauto

theorem fin15Anchored_clause24596 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1679 Fin15AnchoredAtom3890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06692
  ] at hbad
  tauto

theorem fin15Anchored_clause24597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1230 Fin15AnchoredAtom3891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10788
  ] at hbad
  tauto

theorem fin15Anchored_clause24598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1680 Fin15AnchoredAtom3891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10788
  ] at hbad
  tauto

theorem fin15Anchored_clause24599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3892 chi ∧
      ¬Fin15AnchoredAtom1312 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1312 Fin15AnchoredAtom3892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18980
  ] at hbad
  tauto

theorem fin15Anchored_clause24600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3892 chi ∧
      ¬Fin15AnchoredAtom1681 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1681 Fin15AnchoredAtom3892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18980
  ] at hbad
  tauto

theorem fin15Anchored_clause24601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom3893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12836
  ] at hbad
  tauto

theorem fin15Anchored_clause24602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1230 Fin15AnchoredAtom3893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12836
  ] at hbad
  tauto

theorem fin15Anchored_clause24603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1239 Fin15AnchoredAtom3893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12836
  ] at hbad
  tauto

theorem fin15Anchored_clause24604 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1313 Fin15AnchoredAtom3893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12836
  ] at hbad
  tauto

theorem fin15Anchored_clause24605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom3893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12836
  ] at hbad
  tauto

theorem fin15Anchored_clause24606 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom1230 Fin15AnchoredAtom1239
    Fin15AnchoredAtom1313 Fin15AnchoredAtom1682 Fin15AnchoredAtom3893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12836
  ] at hbad
  tauto

theorem fin15Anchored_clause24607 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom3894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21028
  ] at hbad
  tauto

theorem fin15Anchored_clause24608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1231 Fin15AnchoredAtom3894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21028
  ] at hbad
  tauto

theorem fin15Anchored_clause24609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1240 Fin15AnchoredAtom3894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21028
  ] at hbad
  tauto

theorem fin15Anchored_clause24610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1314 Fin15AnchoredAtom3894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21028
  ] at hbad
  tauto

theorem fin15Anchored_clause24611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1683 Fin15AnchoredAtom3894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21028
  ] at hbad
  tauto

theorem fin15Anchored_clause24612 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom1231 Fin15AnchoredAtom1240
    Fin15AnchoredAtom1314 Fin15AnchoredAtom1683 Fin15AnchoredAtom3894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21028
  ] at hbad
  tauto

theorem fin15Anchored_clause24613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1230 Fin15AnchoredAtom3895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25124
  ] at hbad
  tauto

theorem fin15Anchored_clause24614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1231 Fin15AnchoredAtom3895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25124
  ] at hbad
  tauto

theorem fin15Anchored_clause24615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1241 Fin15AnchoredAtom3895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25124
  ] at hbad
  tauto

theorem fin15Anchored_clause24616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1315 Fin15AnchoredAtom3895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25124
  ] at hbad
  tauto

theorem fin15Anchored_clause24617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1684 Fin15AnchoredAtom3895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25124
  ] at hbad
  tauto

theorem fin15Anchored_clause24618 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1230 Fin15AnchoredAtom1231 Fin15AnchoredAtom1241
    Fin15AnchoredAtom1315 Fin15AnchoredAtom1684 Fin15AnchoredAtom3895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25124
  ] at hbad
  tauto

theorem fin15Anchored_clause24619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3896 chi ∧
      ¬Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1316 Fin15AnchoredAtom3896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07204
  ] at hbad
  tauto

theorem fin15Anchored_clause24620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3896 chi ∧
      ¬Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1685 Fin15AnchoredAtom3896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07204
  ] at hbad
  tauto

theorem fin15Anchored_clause24621 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3896 chi ∧
      Fin15AnchoredAtom1232 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1236 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1232 Fin15AnchoredAtom1233 Fin15AnchoredAtom1236
    Fin15AnchoredAtom1316 Fin15AnchoredAtom1685 Fin15AnchoredAtom3896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07204
  ] at hbad
  tauto

theorem fin15Anchored_clause24622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3897 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom3897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11300
  ] at hbad
  tauto

theorem fin15Anchored_clause24623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3897 chi ∧
      ¬Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1686 Fin15AnchoredAtom3897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11300
  ] at hbad
  tauto

theorem fin15Anchored_clause24624 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3897 chi ∧
      Fin15AnchoredAtom1232 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1237 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1232 Fin15AnchoredAtom1234 Fin15AnchoredAtom1237
    Fin15AnchoredAtom1317 Fin15AnchoredAtom1686 Fin15AnchoredAtom3897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11300
  ] at hbad
  tauto

theorem fin15Anchored_clause24625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3898 chi ∧
      ¬Fin15AnchoredAtom1687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1687 Fin15AnchoredAtom3898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19492
  ] at hbad
  tauto

theorem fin15Anchored_clause24626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1233 Fin15AnchoredAtom3899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13348
  ] at hbad
  tauto

theorem fin15Anchored_clause24627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom3899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13348
  ] at hbad
  tauto

theorem fin15Anchored_clause24628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1239 Fin15AnchoredAtom3899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13348
  ] at hbad
  tauto

theorem fin15Anchored_clause24629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom3899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13348
  ] at hbad
  tauto

theorem fin15Anchored_clause24630 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom3899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13348
  ] at hbad
  tauto

theorem fin15Anchored_clause24631 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1233 Fin15AnchoredAtom1234 Fin15AnchoredAtom1239
    Fin15AnchoredAtom1319 Fin15AnchoredAtom1688 Fin15AnchoredAtom3899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13348
  ] at hbad
  tauto

theorem fin15Anchored_clause24632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1233 Fin15AnchoredAtom3900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21540
  ] at hbad
  tauto

theorem fin15Anchored_clause24633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1235 Fin15AnchoredAtom3900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21540
  ] at hbad
  tauto

theorem fin15Anchored_clause24634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1240 Fin15AnchoredAtom3900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21540
  ] at hbad
  tauto

theorem fin15Anchored_clause24635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1320 Fin15AnchoredAtom3900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21540
  ] at hbad
  tauto

theorem fin15Anchored_clause24636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1689 Fin15AnchoredAtom3900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21540
  ] at hbad
  tauto

theorem fin15Anchored_clause24637 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1233 Fin15AnchoredAtom1235 Fin15AnchoredAtom1240
    Fin15AnchoredAtom1320 Fin15AnchoredAtom1689 Fin15AnchoredAtom3900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21540
  ] at hbad
  tauto

theorem fin15Anchored_clause24638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom3901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25636
  ] at hbad
  tauto

theorem fin15Anchored_clause24639 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1235 Fin15AnchoredAtom3901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25636
  ] at hbad
  tauto

theorem fin15Anchored_clause24640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1241 Fin15AnchoredAtom3901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25636
  ] at hbad
  tauto

theorem fin15Anchored_clause24641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1321 Fin15AnchoredAtom3901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25636
  ] at hbad
  tauto

theorem fin15Anchored_clause24642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1690 Fin15AnchoredAtom3901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25636
  ] at hbad
  tauto

theorem fin15Anchored_clause24643 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom1235 Fin15AnchoredAtom1241
    Fin15AnchoredAtom1321 Fin15AnchoredAtom1690 Fin15AnchoredAtom3901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25636
  ] at hbad
  tauto

theorem fin15Anchored_clause24644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3902 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1239 Fin15AnchoredAtom3902 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14372
  ] at hbad
  tauto

theorem fin15Anchored_clause24645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3902 chi ∧
      ¬Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1322 Fin15AnchoredAtom3902 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14372
  ] at hbad
  tauto

theorem fin15Anchored_clause24646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3903 chi ∧
      ¬Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1692 Fin15AnchoredAtom3903 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22564
  ] at hbad
  tauto

theorem fin15Anchored_clause24647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3904 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1241 Fin15AnchoredAtom3904 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26660
  ] at hbad
  tauto

theorem fin15Anchored_clause24648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1239 Fin15AnchoredAtom3905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28708
  ] at hbad
  tauto

theorem fin15Anchored_clause24649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1240 Fin15AnchoredAtom3905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28708
  ] at hbad
  tauto

theorem fin15Anchored_clause24650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1241 Fin15AnchoredAtom3905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28708
  ] at hbad
  tauto

theorem fin15Anchored_clause24651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1325 Fin15AnchoredAtom3905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28708
  ] at hbad
  tauto

theorem fin15Anchored_clause24652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1694 Fin15AnchoredAtom3905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28708
  ] at hbad
  tauto

theorem fin15Anchored_clause24653 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1239 Fin15AnchoredAtom1240 Fin15AnchoredAtom1241
    Fin15AnchoredAtom1325 Fin15AnchoredAtom1694 Fin15AnchoredAtom3905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28708
  ] at hbad
  tauto

theorem fin15Anchored_clause24654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3906 chi ∧
      ¬Fin15AnchoredAtom1270 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1270 Fin15AnchoredAtom3906 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00964
  ] at hbad
  tauto

theorem fin15Anchored_clause24655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3906 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom3906 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00964
  ] at hbad
  tauto

theorem fin15Anchored_clause24656 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3906 chi ∧
      Fin15AnchoredAtom1242 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1249 chi ∧
      Fin15AnchoredAtom1270 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1242 Fin15AnchoredAtom1243 Fin15AnchoredAtom1249
    Fin15AnchoredAtom1270 Fin15AnchoredAtom1695 Fin15AnchoredAtom3906 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00964
  ] at hbad
  tauto

theorem fin15Anchored_clause24657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3907 chi ∧
      ¬Fin15AnchoredAtom1271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1271 Fin15AnchoredAtom3907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01476
  ] at hbad
  tauto

theorem fin15Anchored_clause24658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3907 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom3907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01476
  ] at hbad
  tauto

theorem fin15Anchored_clause24659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3911 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1248 Fin15AnchoredAtom3911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16836
  ] at hbad
  tauto

theorem fin15Anchored_clause24660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom3912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01732
  ] at hbad
  tauto

theorem fin15Anchored_clause24661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom3912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01732
  ] at hbad
  tauto

theorem fin15Anchored_clause24662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom3912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01732
  ] at hbad
  tauto

theorem fin15Anchored_clause24663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom3912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01732
  ] at hbad
  tauto

theorem fin15Anchored_clause24664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom3912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01732
  ] at hbad
  tauto

theorem fin15Anchored_clause24665 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom1244 Fin15AnchoredAtom1255
    Fin15AnchoredAtom1276 Fin15AnchoredAtom1701 Fin15AnchoredAtom3912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01732
  ] at hbad
  tauto

theorem fin15Anchored_clause24666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom3913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02756
  ] at hbad
  tauto

theorem fin15Anchored_clause24667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1256 Fin15AnchoredAtom3913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02756
  ] at hbad
  tauto

theorem fin15Anchored_clause24668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1277 Fin15AnchoredAtom3913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02756
  ] at hbad
  tauto

theorem fin15Anchored_clause24669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1702 Fin15AnchoredAtom3913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02756
  ] at hbad
  tauto

theorem fin15Anchored_clause24670 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3913 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1277 chi ∧
      Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom1245 Fin15AnchoredAtom1256
    Fin15AnchoredAtom1277 Fin15AnchoredAtom1702 Fin15AnchoredAtom3913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02756
  ] at hbad
  tauto

theorem fin15Anchored_clause24671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom3914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04804
  ] at hbad
  tauto

theorem fin15Anchored_clause24672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom3914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04804
  ] at hbad
  tauto

theorem fin15Anchored_clause24673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom3914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04804
  ] at hbad
  tauto

theorem fin15Anchored_clause24674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom3914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04804
  ] at hbad
  tauto

theorem fin15Anchored_clause24675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom3914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04804
  ] at hbad
  tauto

theorem fin15Anchored_clause24676 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom1246 Fin15AnchoredAtom1257
    Fin15AnchoredAtom1278 Fin15AnchoredAtom1703 Fin15AnchoredAtom3914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04804
  ] at hbad
  tauto

theorem fin15Anchored_clause24677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom3915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08900
  ] at hbad
  tauto

theorem fin15Anchored_clause24678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1247 Fin15AnchoredAtom3915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08900
  ] at hbad
  tauto

theorem fin15Anchored_clause24679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1258 Fin15AnchoredAtom3915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08900
  ] at hbad
  tauto

theorem fin15Anchored_clause24680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1279 Fin15AnchoredAtom3915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08900
  ] at hbad
  tauto

theorem fin15Anchored_clause24681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom3915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08900
  ] at hbad
  tauto

theorem fin15Anchored_clause24682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom1247 Fin15AnchoredAtom1258
    Fin15AnchoredAtom1279 Fin15AnchoredAtom1704 Fin15AnchoredAtom3915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08900
  ] at hbad
  tauto

theorem fin15Anchored_clause24683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom3916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17092
  ] at hbad
  tauto

theorem fin15Anchored_clause24684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1248 Fin15AnchoredAtom3916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17092
  ] at hbad
  tauto

theorem fin15Anchored_clause24685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1259 Fin15AnchoredAtom3916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17092
  ] at hbad
  tauto

theorem fin15Anchored_clause24686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1280 Fin15AnchoredAtom3916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17092
  ] at hbad
  tauto

theorem fin15Anchored_clause24687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1705 Fin15AnchoredAtom3916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17092
  ] at hbad
  tauto

theorem fin15Anchored_clause24688 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom1248 Fin15AnchoredAtom1259
    Fin15AnchoredAtom1280 Fin15AnchoredAtom1705 Fin15AnchoredAtom3916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17092
  ] at hbad
  tauto

theorem fin15Anchored_clause24689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom3917 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03268
  ] at hbad
  tauto

theorem fin15Anchored_clause24690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1260 Fin15AnchoredAtom3917 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03268
  ] at hbad
  tauto

theorem fin15Anchored_clause24691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1281 Fin15AnchoredAtom3917 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03268
  ] at hbad
  tauto

theorem fin15Anchored_clause24692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1706 Fin15AnchoredAtom3917 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03268
  ] at hbad
  tauto

theorem fin15Anchored_clause24693 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3917 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom1245 Fin15AnchoredAtom1260
    Fin15AnchoredAtom1281 Fin15AnchoredAtom1706 Fin15AnchoredAtom3917 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03268
  ] at hbad
  tauto

theorem fin15Anchored_clause24694 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom3918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05316
  ] at hbad
  tauto

theorem fin15Anchored_clause24695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom3918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05316
  ] at hbad
  tauto

theorem fin15Anchored_clause24696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom3918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05316
  ] at hbad
  tauto

theorem fin15Anchored_clause24697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom3918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05316
  ] at hbad
  tauto

theorem fin15Anchored_clause24698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom3918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05316
  ] at hbad
  tauto

theorem fin15Anchored_clause24699 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom1246 Fin15AnchoredAtom1261
    Fin15AnchoredAtom1282 Fin15AnchoredAtom1707 Fin15AnchoredAtom3918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05316
  ] at hbad
  tauto

theorem fin15Anchored_clause24700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom3919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09412
  ] at hbad
  tauto

theorem fin15Anchored_clause24701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1247 Fin15AnchoredAtom3919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09412
  ] at hbad
  tauto

theorem fin15Anchored_clause24702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1262 Fin15AnchoredAtom3919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09412
  ] at hbad
  tauto

theorem fin15Anchored_clause24703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1283 Fin15AnchoredAtom3919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09412
  ] at hbad
  tauto

end ErdosSzekeres

end
