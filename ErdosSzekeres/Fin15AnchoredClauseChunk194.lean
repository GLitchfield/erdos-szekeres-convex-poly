module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 194. -/

theorem fin15Anchored_clause24832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3958 chi ∧
      ¬Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1747 Fin15AnchoredAtom3958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14404
  ] at hbad
  tauto

theorem fin15Anchored_clause24833 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3958 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1265 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1322 chi ∧
      Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1264 Fin15AnchoredAtom1265 Fin15AnchoredAtom1267
    Fin15AnchoredAtom1322 Fin15AnchoredAtom1747 Fin15AnchoredAtom3958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14404
  ] at hbad
  tauto

theorem fin15Anchored_clause24834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3959 chi ∧
      ¬Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1323 Fin15AnchoredAtom3959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22596
  ] at hbad
  tauto

theorem fin15Anchored_clause24835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom3961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28740
  ] at hbad
  tauto

theorem fin15Anchored_clause24836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1268 Fin15AnchoredAtom3961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28740
  ] at hbad
  tauto

theorem fin15Anchored_clause24837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1269 Fin15AnchoredAtom3961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28740
  ] at hbad
  tauto

theorem fin15Anchored_clause24838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1325 Fin15AnchoredAtom3961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28740
  ] at hbad
  tauto

theorem fin15Anchored_clause24839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1750 Fin15AnchoredAtom3961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28740
  ] at hbad
  tauto

theorem fin15Anchored_clause24840 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom1268 Fin15AnchoredAtom1269
    Fin15AnchoredAtom1325 Fin15AnchoredAtom1750 Fin15AnchoredAtom3961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28740
  ] at hbad
  tauto

theorem fin15Anchored_clause24841 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3962 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom3962 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01924
  ] at hbad
  tauto

theorem fin15Anchored_clause24842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3964 chi ∧
      ¬Fin15AnchoredAtom1270 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1270 Fin15AnchoredAtom3964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04996
  ] at hbad
  tauto

theorem fin15Anchored_clause24843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3966 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1280 Fin15AnchoredAtom3966 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17284
  ] at hbad
  tauto

theorem fin15Anchored_clause24844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3969 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1758 Fin15AnchoredAtom3969 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09604
  ] at hbad
  tauto

theorem fin15Anchored_clause24845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3975 chi ∧
      ¬Fin15AnchoredAtom1273 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1273 Fin15AnchoredAtom3975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20868
  ] at hbad
  tauto

theorem fin15Anchored_clause24846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3975 chi ∧
      ¬Fin15AnchoredAtom1304 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1304 Fin15AnchoredAtom3975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20868
  ] at hbad
  tauto

theorem fin15Anchored_clause24847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom3977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03716
  ] at hbad
  tauto

theorem fin15Anchored_clause24848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1306 Fin15AnchoredAtom3977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03716
  ] at hbad
  tauto

theorem fin15Anchored_clause24849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom3977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03716
  ] at hbad
  tauto

theorem fin15Anchored_clause24850 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3977 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1277 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1306 chi ∧
      Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom1277 Fin15AnchoredAtom1281
    Fin15AnchoredAtom1306 Fin15AnchoredAtom1766 Fin15AnchoredAtom3977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03716
  ] at hbad
  tauto

theorem fin15Anchored_clause24851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom3978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05764
  ] at hbad
  tauto

theorem fin15Anchored_clause24852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom3978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05764
  ] at hbad
  tauto

theorem fin15Anchored_clause24853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom3978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05764
  ] at hbad
  tauto

theorem fin15Anchored_clause24854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom3978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05764
  ] at hbad
  tauto

theorem fin15Anchored_clause24855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom3978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05764
  ] at hbad
  tauto

theorem fin15Anchored_clause24856 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom1278 Fin15AnchoredAtom1282
    Fin15AnchoredAtom1307 Fin15AnchoredAtom1767 Fin15AnchoredAtom3978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05764
  ] at hbad
  tauto

theorem fin15Anchored_clause24857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom3979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09860
  ] at hbad
  tauto

theorem fin15Anchored_clause24858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1279 Fin15AnchoredAtom3979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09860
  ] at hbad
  tauto

theorem fin15Anchored_clause24859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1283 Fin15AnchoredAtom3979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09860
  ] at hbad
  tauto

theorem fin15Anchored_clause24860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1308 Fin15AnchoredAtom3979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09860
  ] at hbad
  tauto

theorem fin15Anchored_clause24861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1768 Fin15AnchoredAtom3979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09860
  ] at hbad
  tauto

theorem fin15Anchored_clause24862 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom1279 Fin15AnchoredAtom1283
    Fin15AnchoredAtom1308 Fin15AnchoredAtom1768 Fin15AnchoredAtom3979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09860
  ] at hbad
  tauto

theorem fin15Anchored_clause24863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom3980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18052
  ] at hbad
  tauto

theorem fin15Anchored_clause24864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1280 Fin15AnchoredAtom3980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18052
  ] at hbad
  tauto

theorem fin15Anchored_clause24865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1284 Fin15AnchoredAtom3980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18052
  ] at hbad
  tauto

theorem fin15Anchored_clause24866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1309 Fin15AnchoredAtom3980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18052
  ] at hbad
  tauto

theorem fin15Anchored_clause24867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1769 Fin15AnchoredAtom3980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18052
  ] at hbad
  tauto

theorem fin15Anchored_clause24868 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom1280 Fin15AnchoredAtom1284
    Fin15AnchoredAtom1309 Fin15AnchoredAtom1769 Fin15AnchoredAtom3980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18052
  ] at hbad
  tauto

theorem fin15Anchored_clause24869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3981 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom3981 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06788
  ] at hbad
  tauto

theorem fin15Anchored_clause24870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3981 chi ∧
      ¬Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1310 Fin15AnchoredAtom3981 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06788
  ] at hbad
  tauto

theorem fin15Anchored_clause24871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3981 chi ∧
      ¬Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1770 Fin15AnchoredAtom3981 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06788
  ] at hbad
  tauto

theorem fin15Anchored_clause24872 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3981 chi ∧
      Fin15AnchoredAtom1277 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1285 chi ∧
      Fin15AnchoredAtom1310 chi ∧
      Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1277 Fin15AnchoredAtom1278 Fin15AnchoredAtom1285
    Fin15AnchoredAtom1310 Fin15AnchoredAtom1770 Fin15AnchoredAtom3981 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06788
  ] at hbad
  tauto

theorem fin15Anchored_clause24873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3982 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1279 Fin15AnchoredAtom3982 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10884
  ] at hbad
  tauto

theorem fin15Anchored_clause24874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3982 chi ∧
      ¬Fin15AnchoredAtom1311 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1311 Fin15AnchoredAtom3982 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10884
  ] at hbad
  tauto

theorem fin15Anchored_clause24875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3983 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1280 Fin15AnchoredAtom3983 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19076
  ] at hbad
  tauto

theorem fin15Anchored_clause24876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom3984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12932
  ] at hbad
  tauto

theorem fin15Anchored_clause24877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1279 Fin15AnchoredAtom3984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12932
  ] at hbad
  tauto

theorem fin15Anchored_clause24878 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1288 Fin15AnchoredAtom3984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12932
  ] at hbad
  tauto

theorem fin15Anchored_clause24879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1313 Fin15AnchoredAtom3984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12932
  ] at hbad
  tauto

theorem fin15Anchored_clause24880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom3984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12932
  ] at hbad
  tauto

theorem fin15Anchored_clause24881 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom1279 Fin15AnchoredAtom1288
    Fin15AnchoredAtom1313 Fin15AnchoredAtom1773 Fin15AnchoredAtom3984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12932
  ] at hbad
  tauto

theorem fin15Anchored_clause24882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom3985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21124
  ] at hbad
  tauto

theorem fin15Anchored_clause24883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1280 Fin15AnchoredAtom3985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21124
  ] at hbad
  tauto

theorem fin15Anchored_clause24884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1289 Fin15AnchoredAtom3985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21124
  ] at hbad
  tauto

theorem fin15Anchored_clause24885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1314 Fin15AnchoredAtom3985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21124
  ] at hbad
  tauto

theorem fin15Anchored_clause24886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1774 Fin15AnchoredAtom3985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21124
  ] at hbad
  tauto

theorem fin15Anchored_clause24887 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom1280 Fin15AnchoredAtom1289
    Fin15AnchoredAtom1314 Fin15AnchoredAtom1774 Fin15AnchoredAtom3985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21124
  ] at hbad
  tauto

theorem fin15Anchored_clause24888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1279 Fin15AnchoredAtom3986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25220
  ] at hbad
  tauto

theorem fin15Anchored_clause24889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1280 Fin15AnchoredAtom3986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25220
  ] at hbad
  tauto

theorem fin15Anchored_clause24890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1290 Fin15AnchoredAtom3986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25220
  ] at hbad
  tauto

theorem fin15Anchored_clause24891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1315 Fin15AnchoredAtom3986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25220
  ] at hbad
  tauto

theorem fin15Anchored_clause24892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1775 Fin15AnchoredAtom3986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25220
  ] at hbad
  tauto

theorem fin15Anchored_clause24893 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1279 Fin15AnchoredAtom1280 Fin15AnchoredAtom1290
    Fin15AnchoredAtom1315 Fin15AnchoredAtom1775 Fin15AnchoredAtom3986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25220
  ] at hbad
  tauto

theorem fin15Anchored_clause24894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3987 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom3987 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07300
  ] at hbad
  tauto

theorem fin15Anchored_clause24895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3987 chi ∧
      ¬Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1316 Fin15AnchoredAtom3987 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07300
  ] at hbad
  tauto

theorem fin15Anchored_clause24896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3987 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1776 Fin15AnchoredAtom3987 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07300
  ] at hbad
  tauto

theorem fin15Anchored_clause24897 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3987 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1285 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1281 Fin15AnchoredAtom1282 Fin15AnchoredAtom1285
    Fin15AnchoredAtom1316 Fin15AnchoredAtom1776 Fin15AnchoredAtom3987 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07300
  ] at hbad
  tauto

theorem fin15Anchored_clause24898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3988 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1281 Fin15AnchoredAtom3988 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11396
  ] at hbad
  tauto

theorem fin15Anchored_clause24899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3988 chi ∧
      ¬Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1777 Fin15AnchoredAtom3988 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11396
  ] at hbad
  tauto

theorem fin15Anchored_clause24900 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3988 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1286 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1281 Fin15AnchoredAtom1283 Fin15AnchoredAtom1286
    Fin15AnchoredAtom1317 Fin15AnchoredAtom1777 Fin15AnchoredAtom3988 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11396
  ] at hbad
  tauto

theorem fin15Anchored_clause24901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1281 Fin15AnchoredAtom3989 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19588
  ] at hbad
  tauto

theorem fin15Anchored_clause24902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1284 Fin15AnchoredAtom3989 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19588
  ] at hbad
  tauto

theorem fin15Anchored_clause24903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom1287 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1287 Fin15AnchoredAtom3989 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19588
  ] at hbad
  tauto

theorem fin15Anchored_clause24904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom1318 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1318 Fin15AnchoredAtom3989 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19588
  ] at hbad
  tauto

theorem fin15Anchored_clause24905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1778 Fin15AnchoredAtom3989 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19588
  ] at hbad
  tauto

theorem fin15Anchored_clause24906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom3990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13444
  ] at hbad
  tauto

theorem fin15Anchored_clause24907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1283 Fin15AnchoredAtom3990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13444
  ] at hbad
  tauto

theorem fin15Anchored_clause24908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1288 Fin15AnchoredAtom3990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13444
  ] at hbad
  tauto

theorem fin15Anchored_clause24909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom3990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13444
  ] at hbad
  tauto

theorem fin15Anchored_clause24910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom3990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13444
  ] at hbad
  tauto

theorem fin15Anchored_clause24911 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom1283 Fin15AnchoredAtom1288
    Fin15AnchoredAtom1319 Fin15AnchoredAtom1779 Fin15AnchoredAtom3990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13444
  ] at hbad
  tauto

theorem fin15Anchored_clause24912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom3991 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21636
  ] at hbad
  tauto

theorem fin15Anchored_clause24913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1284 Fin15AnchoredAtom3991 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21636
  ] at hbad
  tauto

theorem fin15Anchored_clause24914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1289 Fin15AnchoredAtom3991 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21636
  ] at hbad
  tauto

theorem fin15Anchored_clause24915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1320 Fin15AnchoredAtom3991 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21636
  ] at hbad
  tauto

theorem fin15Anchored_clause24916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1780 Fin15AnchoredAtom3991 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21636
  ] at hbad
  tauto

theorem fin15Anchored_clause24917 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom1284 Fin15AnchoredAtom1289
    Fin15AnchoredAtom1320 Fin15AnchoredAtom1780 Fin15AnchoredAtom3991 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21636
  ] at hbad
  tauto

theorem fin15Anchored_clause24918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1283 Fin15AnchoredAtom3992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25732
  ] at hbad
  tauto

theorem fin15Anchored_clause24919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1284 Fin15AnchoredAtom3992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25732
  ] at hbad
  tauto

theorem fin15Anchored_clause24920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1290 Fin15AnchoredAtom3992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25732
  ] at hbad
  tauto

theorem fin15Anchored_clause24921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1321 Fin15AnchoredAtom3992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25732
  ] at hbad
  tauto

theorem fin15Anchored_clause24922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1781 Fin15AnchoredAtom3992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25732
  ] at hbad
  tauto

theorem fin15Anchored_clause24923 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1283 Fin15AnchoredAtom1284 Fin15AnchoredAtom1290
    Fin15AnchoredAtom1321 Fin15AnchoredAtom1781 Fin15AnchoredAtom3992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25732
  ] at hbad
  tauto

theorem fin15Anchored_clause24924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3993 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1288 Fin15AnchoredAtom3993 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14468
  ] at hbad
  tauto

theorem fin15Anchored_clause24925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3993 chi ∧
      ¬Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1322 Fin15AnchoredAtom3993 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14468
  ] at hbad
  tauto

theorem fin15Anchored_clause24926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3994 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1289 Fin15AnchoredAtom3994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22660
  ] at hbad
  tauto

theorem fin15Anchored_clause24927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3994 chi ∧
      ¬Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1323 Fin15AnchoredAtom3994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22660
  ] at hbad
  tauto

theorem fin15Anchored_clause24928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3995 chi ∧
      ¬Fin15AnchoredAtom1286 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1286 Fin15AnchoredAtom3995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26756
  ] at hbad
  tauto

theorem fin15Anchored_clause24929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3995 chi ∧
      ¬Fin15AnchoredAtom1287 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1287 Fin15AnchoredAtom3995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26756
  ] at hbad
  tauto

theorem fin15Anchored_clause24930 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3995 chi ∧
      Fin15AnchoredAtom1286 chi ∧
      Fin15AnchoredAtom1287 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1324 chi ∧
      Fin15AnchoredAtom1784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1286 Fin15AnchoredAtom1287 Fin15AnchoredAtom1290
    Fin15AnchoredAtom1324 Fin15AnchoredAtom1784 Fin15AnchoredAtom3995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26756
  ] at hbad
  tauto

theorem fin15Anchored_clause24931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1288 Fin15AnchoredAtom3996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28804
  ] at hbad
  tauto

theorem fin15Anchored_clause24932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1289 Fin15AnchoredAtom3996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28804
  ] at hbad
  tauto

theorem fin15Anchored_clause24933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1290 Fin15AnchoredAtom3996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28804
  ] at hbad
  tauto

theorem fin15Anchored_clause24934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1325 Fin15AnchoredAtom3996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28804
  ] at hbad
  tauto

theorem fin15Anchored_clause24935 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1785 Fin15AnchoredAtom3996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28804
  ] at hbad
  tauto

theorem fin15Anchored_clause24936 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1288 Fin15AnchoredAtom1289 Fin15AnchoredAtom1290
    Fin15AnchoredAtom1325 Fin15AnchoredAtom1785 Fin15AnchoredAtom3996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28804
  ] at hbad
  tauto

theorem fin15Anchored_clause24937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3998 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom3998 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05892
  ] at hbad
  tauto

theorem fin15Anchored_clause24938 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3998 chi ∧
      Fin15AnchoredAtom1291 chi ∧
      Fin15AnchoredAtom1293 chi ∧
      Fin15AnchoredAtom1297 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1291 Fin15AnchoredAtom1293 Fin15AnchoredAtom1297
    Fin15AnchoredAtom1307 Fin15AnchoredAtom1787 Fin15AnchoredAtom3998 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05892
  ] at hbad
  tauto

theorem fin15Anchored_clause24939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4005 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1314 Fin15AnchoredAtom4005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21252
  ] at hbad
  tauto

theorem fin15Anchored_clause24940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4010 chi ∧
      ¬Fin15AnchoredAtom1297 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1297 Fin15AnchoredAtom4010 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13572
  ] at hbad
  tauto

theorem fin15Anchored_clause24941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4010 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom4010 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13572
  ] at hbad
  tauto

theorem fin15Anchored_clause24942 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4010 chi ∧
      Fin15AnchoredAtom1297 chi ∧
      Fin15AnchoredAtom1298 chi ∧
      Fin15AnchoredAtom1303 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1297 Fin15AnchoredAtom1298 Fin15AnchoredAtom1303
    Fin15AnchoredAtom1319 Fin15AnchoredAtom1799 Fin15AnchoredAtom4010 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13572
  ] at hbad
  tauto

theorem fin15Anchored_clause24943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4011 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1320 Fin15AnchoredAtom4011 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21764
  ] at hbad
  tauto

theorem fin15Anchored_clause24944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4012 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1321 Fin15AnchoredAtom4012 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25860
  ] at hbad
  tauto

theorem fin15Anchored_clause24945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4016 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1325 Fin15AnchoredAtom4016 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28932
  ] at hbad
  tauto

theorem fin15Anchored_clause24946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4017 chi ∧
      ¬Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1306 Fin15AnchoredAtom4017 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07684
  ] at hbad
  tauto

theorem fin15Anchored_clause24947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4017 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom4017 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07684
  ] at hbad
  tauto

theorem fin15Anchored_clause24948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4017 chi ∧
      ¬Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1806 Fin15AnchoredAtom4017 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07684
  ] at hbad
  tauto

theorem fin15Anchored_clause24949 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4017 chi ∧
      Fin15AnchoredAtom1306 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1310 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1306 Fin15AnchoredAtom1307 Fin15AnchoredAtom1310
    Fin15AnchoredAtom1316 Fin15AnchoredAtom1806 Fin15AnchoredAtom4017 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07684
  ] at hbad
  tauto

theorem fin15Anchored_clause24950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4018 chi ∧
      ¬Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1306 Fin15AnchoredAtom4018 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11780
  ] at hbad
  tauto

theorem fin15Anchored_clause24951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4018 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1308 Fin15AnchoredAtom4018 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11780
  ] at hbad
  tauto

theorem fin15Anchored_clause24952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4019 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1309 Fin15AnchoredAtom4019 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19972
  ] at hbad
  tauto

theorem fin15Anchored_clause24953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom4020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13828
  ] at hbad
  tauto

theorem fin15Anchored_clause24954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1308 Fin15AnchoredAtom4020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13828
  ] at hbad
  tauto

theorem fin15Anchored_clause24955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1313 Fin15AnchoredAtom4020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13828
  ] at hbad
  tauto

theorem fin15Anchored_clause24956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom4020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13828
  ] at hbad
  tauto

theorem fin15Anchored_clause24957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom4020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13828
  ] at hbad
  tauto

theorem fin15Anchored_clause24958 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom1308 Fin15AnchoredAtom1313
    Fin15AnchoredAtom1319 Fin15AnchoredAtom1809 Fin15AnchoredAtom4020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13828
  ] at hbad
  tauto

theorem fin15Anchored_clause24959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom4021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22020
  ] at hbad
  tauto

end ErdosSzekeres

end
