module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 163. -/

theorem fin15Anchored_clause20864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom2949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05158
  ] at hbad
  tauto

theorem fin15Anchored_clause20865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom2949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05158
  ] at hbad
  tauto

theorem fin15Anchored_clause20866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0877 Fin15AnchoredAtom2949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05158
  ] at hbad
  tauto

theorem fin15Anchored_clause20867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom2949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05158
  ] at hbad
  tauto

theorem fin15Anchored_clause20868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1233 Fin15AnchoredAtom2949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05158
  ] at hbad
  tauto

theorem fin15Anchored_clause20869 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom0847 Fin15AnchoredAtom0877
    Fin15AnchoredAtom1013 Fin15AnchoredAtom1233 Fin15AnchoredAtom2949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05158
  ] at hbad
  tauto

theorem fin15Anchored_clause20870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom2950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09254
  ] at hbad
  tauto

theorem fin15Anchored_clause20871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0848 Fin15AnchoredAtom2950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09254
  ] at hbad
  tauto

theorem fin15Anchored_clause20872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0878 Fin15AnchoredAtom2950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09254
  ] at hbad
  tauto

theorem fin15Anchored_clause20873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1014 Fin15AnchoredAtom2950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09254
  ] at hbad
  tauto

theorem fin15Anchored_clause20874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom2950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09254
  ] at hbad
  tauto

theorem fin15Anchored_clause20875 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom0848 Fin15AnchoredAtom0878
    Fin15AnchoredAtom1014 Fin15AnchoredAtom1234 Fin15AnchoredAtom2950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09254
  ] at hbad
  tauto

theorem fin15Anchored_clause20876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom2951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17446
  ] at hbad
  tauto

theorem fin15Anchored_clause20877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0849 Fin15AnchoredAtom2951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17446
  ] at hbad
  tauto

theorem fin15Anchored_clause20878 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0879 Fin15AnchoredAtom2951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17446
  ] at hbad
  tauto

theorem fin15Anchored_clause20879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1015 Fin15AnchoredAtom2951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17446
  ] at hbad
  tauto

theorem fin15Anchored_clause20880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1235 Fin15AnchoredAtom2951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17446
  ] at hbad
  tauto

theorem fin15Anchored_clause20881 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom0849 Fin15AnchoredAtom0879
    Fin15AnchoredAtom1015 Fin15AnchoredAtom1235 Fin15AnchoredAtom2951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17446
  ] at hbad
  tauto

theorem fin15Anchored_clause20882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom2955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12326
  ] at hbad
  tauto

theorem fin15Anchored_clause20883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0848 Fin15AnchoredAtom2955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12326
  ] at hbad
  tauto

theorem fin15Anchored_clause20884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0883 Fin15AnchoredAtom2955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12326
  ] at hbad
  tauto

theorem fin15Anchored_clause20885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom2955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12326
  ] at hbad
  tauto

theorem fin15Anchored_clause20886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1239 Fin15AnchoredAtom2955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12326
  ] at hbad
  tauto

theorem fin15Anchored_clause20887 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom0848 Fin15AnchoredAtom0883
    Fin15AnchoredAtom1019 Fin15AnchoredAtom1239 Fin15AnchoredAtom2955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12326
  ] at hbad
  tauto

theorem fin15Anchored_clause20888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom2956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20518
  ] at hbad
  tauto

theorem fin15Anchored_clause20889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0849 Fin15AnchoredAtom2956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20518
  ] at hbad
  tauto

theorem fin15Anchored_clause20890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0884 Fin15AnchoredAtom2956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20518
  ] at hbad
  tauto

theorem fin15Anchored_clause20891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1020 Fin15AnchoredAtom2956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20518
  ] at hbad
  tauto

theorem fin15Anchored_clause20892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1240 Fin15AnchoredAtom2956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20518
  ] at hbad
  tauto

theorem fin15Anchored_clause20893 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom0849 Fin15AnchoredAtom0884
    Fin15AnchoredAtom1020 Fin15AnchoredAtom1240 Fin15AnchoredAtom2956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20518
  ] at hbad
  tauto

theorem fin15Anchored_clause20894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0848 Fin15AnchoredAtom2957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24614
  ] at hbad
  tauto

theorem fin15Anchored_clause20895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0849 Fin15AnchoredAtom2957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24614
  ] at hbad
  tauto

theorem fin15Anchored_clause20896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0885 Fin15AnchoredAtom2957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24614
  ] at hbad
  tauto

theorem fin15Anchored_clause20897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1021 Fin15AnchoredAtom2957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24614
  ] at hbad
  tauto

theorem fin15Anchored_clause20898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1241 Fin15AnchoredAtom2957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24614
  ] at hbad
  tauto

theorem fin15Anchored_clause20899 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0848 Fin15AnchoredAtom0849 Fin15AnchoredAtom0885
    Fin15AnchoredAtom1021 Fin15AnchoredAtom1241 Fin15AnchoredAtom2957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24614
  ] at hbad
  tauto

theorem fin15Anchored_clause20900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2958 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom2958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00454
  ] at hbad
  tauto

theorem fin15Anchored_clause20901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2958 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom2958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00454
  ] at hbad
  tauto

theorem fin15Anchored_clause20902 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2958 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0851 chi ∧
      Fin15AnchoredAtom0858 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom0851 Fin15AnchoredAtom0858
    Fin15AnchoredAtom1022 Fin15AnchoredAtom1242 Fin15AnchoredAtom2958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00454
  ] at hbad
  tauto

theorem fin15Anchored_clause20903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom2959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00710
  ] at hbad
  tauto

theorem fin15Anchored_clause20904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom2959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00710
  ] at hbad
  tauto

theorem fin15Anchored_clause20905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom2959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00710
  ] at hbad
  tauto

theorem fin15Anchored_clause20906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom2959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00710
  ] at hbad
  tauto

theorem fin15Anchored_clause20907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom2959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00710
  ] at hbad
  tauto

theorem fin15Anchored_clause20908 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom0852 Fin15AnchoredAtom0859
    Fin15AnchoredAtom1023 Fin15AnchoredAtom1243 Fin15AnchoredAtom2959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00710
  ] at hbad
  tauto

theorem fin15Anchored_clause20909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom2960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01222
  ] at hbad
  tauto

theorem fin15Anchored_clause20910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom2960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01222
  ] at hbad
  tauto

theorem fin15Anchored_clause20911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom2960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01222
  ] at hbad
  tauto

theorem fin15Anchored_clause20912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom2960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01222
  ] at hbad
  tauto

theorem fin15Anchored_clause20913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom2960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01222
  ] at hbad
  tauto

theorem fin15Anchored_clause20914 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom0853 Fin15AnchoredAtom0860
    Fin15AnchoredAtom1024 Fin15AnchoredAtom1244 Fin15AnchoredAtom2960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01222
  ] at hbad
  tauto

theorem fin15Anchored_clause20915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2961 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom2961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02246
  ] at hbad
  tauto

theorem fin15Anchored_clause20916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2961 chi ∧
      ¬Fin15AnchoredAtom1025 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1025 Fin15AnchoredAtom2961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02246
  ] at hbad
  tauto

theorem fin15Anchored_clause20917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom2962 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04294
  ] at hbad
  tauto

theorem fin15Anchored_clause20918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom2962 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04294
  ] at hbad
  tauto

theorem fin15Anchored_clause20919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom2962 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04294
  ] at hbad
  tauto

theorem fin15Anchored_clause20920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom2962 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04294
  ] at hbad
  tauto

theorem fin15Anchored_clause20921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom2962 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04294
  ] at hbad
  tauto

theorem fin15Anchored_clause20922 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom0855 Fin15AnchoredAtom0862
    Fin15AnchoredAtom1026 Fin15AnchoredAtom1246 Fin15AnchoredAtom2962 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04294
  ] at hbad
  tauto

theorem fin15Anchored_clause20923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom2963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08390
  ] at hbad
  tauto

theorem fin15Anchored_clause20924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0856 Fin15AnchoredAtom2963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08390
  ] at hbad
  tauto

theorem fin15Anchored_clause20925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0863 Fin15AnchoredAtom2963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08390
  ] at hbad
  tauto

theorem fin15Anchored_clause20926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1027 Fin15AnchoredAtom2963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08390
  ] at hbad
  tauto

theorem fin15Anchored_clause20927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1247 Fin15AnchoredAtom2963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08390
  ] at hbad
  tauto

theorem fin15Anchored_clause20928 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom0856 Fin15AnchoredAtom0863
    Fin15AnchoredAtom1027 Fin15AnchoredAtom1247 Fin15AnchoredAtom2963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08390
  ] at hbad
  tauto

theorem fin15Anchored_clause20929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom2964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16582
  ] at hbad
  tauto

theorem fin15Anchored_clause20930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0857 Fin15AnchoredAtom2964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16582
  ] at hbad
  tauto

theorem fin15Anchored_clause20931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0864 Fin15AnchoredAtom2964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16582
  ] at hbad
  tauto

theorem fin15Anchored_clause20932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1028 Fin15AnchoredAtom2964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16582
  ] at hbad
  tauto

theorem fin15Anchored_clause20933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1248 Fin15AnchoredAtom2964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16582
  ] at hbad
  tauto

theorem fin15Anchored_clause20934 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom0857 Fin15AnchoredAtom0864
    Fin15AnchoredAtom1028 Fin15AnchoredAtom1248 Fin15AnchoredAtom2964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16582
  ] at hbad
  tauto

theorem fin15Anchored_clause20935 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2965 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom2965 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00838
  ] at hbad
  tauto

theorem fin15Anchored_clause20936 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2965 chi ∧
      Fin15AnchoredAtom0851 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0865 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0851 Fin15AnchoredAtom0852 Fin15AnchoredAtom0865
    Fin15AnchoredAtom1029 Fin15AnchoredAtom1249 Fin15AnchoredAtom2965 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00838
  ] at hbad
  tauto

theorem fin15Anchored_clause20937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2966 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom2966 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01350
  ] at hbad
  tauto

theorem fin15Anchored_clause20938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2966 chi ∧
      ¬Fin15AnchoredAtom0866 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0866 Fin15AnchoredAtom2966 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01350
  ] at hbad
  tauto

theorem fin15Anchored_clause20939 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2966 chi ∧
      Fin15AnchoredAtom0851 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0866 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0851 Fin15AnchoredAtom0853 Fin15AnchoredAtom0866
    Fin15AnchoredAtom1030 Fin15AnchoredAtom1250 Fin15AnchoredAtom2966 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01350
  ] at hbad
  tauto

theorem fin15Anchored_clause20940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2970 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0857 Fin15AnchoredAtom2970 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16710
  ] at hbad
  tauto

theorem fin15Anchored_clause20941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom2971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01606
  ] at hbad
  tauto

theorem fin15Anchored_clause20942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom2971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01606
  ] at hbad
  tauto

theorem fin15Anchored_clause20943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom2971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01606
  ] at hbad
  tauto

theorem fin15Anchored_clause20944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom2971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01606
  ] at hbad
  tauto

theorem fin15Anchored_clause20945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom2971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01606
  ] at hbad
  tauto

theorem fin15Anchored_clause20946 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom0853 Fin15AnchoredAtom0871
    Fin15AnchoredAtom1035 Fin15AnchoredAtom1255 Fin15AnchoredAtom2971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01606
  ] at hbad
  tauto

theorem fin15Anchored_clause20947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2972 chi ∧
      ¬Fin15AnchoredAtom1036 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1036 Fin15AnchoredAtom2972 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02630
  ] at hbad
  tauto

theorem fin15Anchored_clause20948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2972 chi ∧
      ¬Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1256 Fin15AnchoredAtom2972 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02630
  ] at hbad
  tauto

theorem fin15Anchored_clause20949 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2972 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0854 chi ∧
      Fin15AnchoredAtom0872 chi ∧
      Fin15AnchoredAtom1036 chi ∧
      Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom0854 Fin15AnchoredAtom0872
    Fin15AnchoredAtom1036 Fin15AnchoredAtom1256 Fin15AnchoredAtom2972 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02630
  ] at hbad
  tauto

theorem fin15Anchored_clause20950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom2973 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04678
  ] at hbad
  tauto

theorem fin15Anchored_clause20951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom2973 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04678
  ] at hbad
  tauto

theorem fin15Anchored_clause20952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom2973 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04678
  ] at hbad
  tauto

theorem fin15Anchored_clause20953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom2973 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04678
  ] at hbad
  tauto

theorem fin15Anchored_clause20954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom2973 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04678
  ] at hbad
  tauto

theorem fin15Anchored_clause20955 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom0855 Fin15AnchoredAtom0873
    Fin15AnchoredAtom1037 Fin15AnchoredAtom1257 Fin15AnchoredAtom2973 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04678
  ] at hbad
  tauto

theorem fin15Anchored_clause20956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom2974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08774
  ] at hbad
  tauto

theorem fin15Anchored_clause20957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0856 Fin15AnchoredAtom2974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08774
  ] at hbad
  tauto

theorem fin15Anchored_clause20958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0874 Fin15AnchoredAtom2974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08774
  ] at hbad
  tauto

theorem fin15Anchored_clause20959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom2974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08774
  ] at hbad
  tauto

theorem fin15Anchored_clause20960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1258 Fin15AnchoredAtom2974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08774
  ] at hbad
  tauto

theorem fin15Anchored_clause20961 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom0856 Fin15AnchoredAtom0874
    Fin15AnchoredAtom1038 Fin15AnchoredAtom1258 Fin15AnchoredAtom2974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08774
  ] at hbad
  tauto

theorem fin15Anchored_clause20962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom2975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16966
  ] at hbad
  tauto

theorem fin15Anchored_clause20963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0857 Fin15AnchoredAtom2975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16966
  ] at hbad
  tauto

theorem fin15Anchored_clause20964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0875 Fin15AnchoredAtom2975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16966
  ] at hbad
  tauto

theorem fin15Anchored_clause20965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1039 Fin15AnchoredAtom2975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16966
  ] at hbad
  tauto

theorem fin15Anchored_clause20966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1259 Fin15AnchoredAtom2975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16966
  ] at hbad
  tauto

theorem fin15Anchored_clause20967 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom0857 Fin15AnchoredAtom0875
    Fin15AnchoredAtom1039 Fin15AnchoredAtom1259 Fin15AnchoredAtom2975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16966
  ] at hbad
  tauto

theorem fin15Anchored_clause20968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom2976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03142
  ] at hbad
  tauto

theorem fin15Anchored_clause20969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom0854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0854 Fin15AnchoredAtom2976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03142
  ] at hbad
  tauto

theorem fin15Anchored_clause20970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom0876 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0876 Fin15AnchoredAtom2976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03142
  ] at hbad
  tauto

theorem fin15Anchored_clause20971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1040 Fin15AnchoredAtom2976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03142
  ] at hbad
  tauto

theorem fin15Anchored_clause20972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1260 Fin15AnchoredAtom2976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03142
  ] at hbad
  tauto

theorem fin15Anchored_clause20973 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2976 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0854 chi ∧
      Fin15AnchoredAtom0876 chi ∧
      Fin15AnchoredAtom1040 chi ∧
      Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom0854 Fin15AnchoredAtom0876
    Fin15AnchoredAtom1040 Fin15AnchoredAtom1260 Fin15AnchoredAtom2976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03142
  ] at hbad
  tauto

theorem fin15Anchored_clause20974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom2977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05190
  ] at hbad
  tauto

theorem fin15Anchored_clause20975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom2977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05190
  ] at hbad
  tauto

theorem fin15Anchored_clause20976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0877 Fin15AnchoredAtom2977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05190
  ] at hbad
  tauto

theorem fin15Anchored_clause20977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom2977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05190
  ] at hbad
  tauto

theorem fin15Anchored_clause20978 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom2977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05190
  ] at hbad
  tauto

theorem fin15Anchored_clause20979 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom0855 Fin15AnchoredAtom0877
    Fin15AnchoredAtom1041 Fin15AnchoredAtom1261 Fin15AnchoredAtom2977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05190
  ] at hbad
  tauto

theorem fin15Anchored_clause20980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom2978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09286
  ] at hbad
  tauto

theorem fin15Anchored_clause20981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0856 Fin15AnchoredAtom2978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09286
  ] at hbad
  tauto

theorem fin15Anchored_clause20982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0878 Fin15AnchoredAtom2978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09286
  ] at hbad
  tauto

theorem fin15Anchored_clause20983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom2978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09286
  ] at hbad
  tauto

theorem fin15Anchored_clause20984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1262 Fin15AnchoredAtom2978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09286
  ] at hbad
  tauto

theorem fin15Anchored_clause20985 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom0856 Fin15AnchoredAtom0878
    Fin15AnchoredAtom1042 Fin15AnchoredAtom1262 Fin15AnchoredAtom2978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09286
  ] at hbad
  tauto

theorem fin15Anchored_clause20986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom2979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17478
  ] at hbad
  tauto

theorem fin15Anchored_clause20987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0857 Fin15AnchoredAtom2979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17478
  ] at hbad
  tauto

theorem fin15Anchored_clause20988 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0879 Fin15AnchoredAtom2979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17478
  ] at hbad
  tauto

theorem fin15Anchored_clause20989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1043 Fin15AnchoredAtom2979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17478
  ] at hbad
  tauto

theorem fin15Anchored_clause20990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1263 Fin15AnchoredAtom2979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17478
  ] at hbad
  tauto

theorem fin15Anchored_clause20991 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom0857 Fin15AnchoredAtom0879
    Fin15AnchoredAtom1043 Fin15AnchoredAtom1263 Fin15AnchoredAtom2979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17478
  ] at hbad
  tauto

end ErdosSzekeres

end
