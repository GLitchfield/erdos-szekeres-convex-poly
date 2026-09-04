module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 164. -/

theorem fin15Anchored_clause20992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2980 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom2980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06214
  ] at hbad
  tauto

theorem fin15Anchored_clause20993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2980 chi ∧
      ¬Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1264 Fin15AnchoredAtom2980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06214
  ] at hbad
  tauto

theorem fin15Anchored_clause20994 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2980 chi ∧
      Fin15AnchoredAtom0854 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0880 chi ∧
      Fin15AnchoredAtom1044 chi ∧
      Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0854 Fin15AnchoredAtom0855 Fin15AnchoredAtom0880
    Fin15AnchoredAtom1044 Fin15AnchoredAtom1264 Fin15AnchoredAtom2980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06214
  ] at hbad
  tauto

theorem fin15Anchored_clause20995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom2983 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12358
  ] at hbad
  tauto

theorem fin15Anchored_clause20996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0856 Fin15AnchoredAtom2983 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12358
  ] at hbad
  tauto

theorem fin15Anchored_clause20997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0883 Fin15AnchoredAtom2983 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12358
  ] at hbad
  tauto

theorem fin15Anchored_clause20998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom2983 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12358
  ] at hbad
  tauto

theorem fin15Anchored_clause20999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom2983 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12358
  ] at hbad
  tauto

theorem fin15Anchored_clause21000 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom0856 Fin15AnchoredAtom0883
    Fin15AnchoredAtom1047 Fin15AnchoredAtom1267 Fin15AnchoredAtom2983 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12358
  ] at hbad
  tauto

theorem fin15Anchored_clause21001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom2984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20550
  ] at hbad
  tauto

theorem fin15Anchored_clause21002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0857 Fin15AnchoredAtom2984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20550
  ] at hbad
  tauto

theorem fin15Anchored_clause21003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0884 Fin15AnchoredAtom2984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20550
  ] at hbad
  tauto

theorem fin15Anchored_clause21004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1048 Fin15AnchoredAtom2984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20550
  ] at hbad
  tauto

theorem fin15Anchored_clause21005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1268 Fin15AnchoredAtom2984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20550
  ] at hbad
  tauto

theorem fin15Anchored_clause21006 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom0857 Fin15AnchoredAtom0884
    Fin15AnchoredAtom1048 Fin15AnchoredAtom1268 Fin15AnchoredAtom2984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20550
  ] at hbad
  tauto

theorem fin15Anchored_clause21007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0856 Fin15AnchoredAtom2985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24646
  ] at hbad
  tauto

theorem fin15Anchored_clause21008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0857 Fin15AnchoredAtom2985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24646
  ] at hbad
  tauto

theorem fin15Anchored_clause21009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0885 Fin15AnchoredAtom2985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24646
  ] at hbad
  tauto

theorem fin15Anchored_clause21010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1049 Fin15AnchoredAtom2985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24646
  ] at hbad
  tauto

theorem fin15Anchored_clause21011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1269 Fin15AnchoredAtom2985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24646
  ] at hbad
  tauto

theorem fin15Anchored_clause21012 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0856 Fin15AnchoredAtom0857 Fin15AnchoredAtom0885
    Fin15AnchoredAtom1049 Fin15AnchoredAtom1269 Fin15AnchoredAtom2985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24646
  ] at hbad
  tauto

theorem fin15Anchored_clause21013 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2986 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom2986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00902
  ] at hbad
  tauto

theorem fin15Anchored_clause21014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2987 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1051 Fin15AnchoredAtom2987 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01414
  ] at hbad
  tauto

theorem fin15Anchored_clause21015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2991 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0864 Fin15AnchoredAtom2991 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16774
  ] at hbad
  tauto

theorem fin15Anchored_clause21016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom2992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01670
  ] at hbad
  tauto

theorem fin15Anchored_clause21017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom2992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01670
  ] at hbad
  tauto

theorem fin15Anchored_clause21018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom2992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01670
  ] at hbad
  tauto

theorem fin15Anchored_clause21019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom2992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01670
  ] at hbad
  tauto

theorem fin15Anchored_clause21020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom2992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01670
  ] at hbad
  tauto

theorem fin15Anchored_clause21021 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom0860 Fin15AnchoredAtom0871
    Fin15AnchoredAtom1056 Fin15AnchoredAtom1276 Fin15AnchoredAtom2992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01670
  ] at hbad
  tauto

theorem fin15Anchored_clause21022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2993 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom2993 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02694
  ] at hbad
  tauto

theorem fin15Anchored_clause21023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2993 chi ∧
      ¬Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1277 Fin15AnchoredAtom2993 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02694
  ] at hbad
  tauto

theorem fin15Anchored_clause21024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom2994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04742
  ] at hbad
  tauto

theorem fin15Anchored_clause21025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom2994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04742
  ] at hbad
  tauto

theorem fin15Anchored_clause21026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom2994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04742
  ] at hbad
  tauto

theorem fin15Anchored_clause21027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom2994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04742
  ] at hbad
  tauto

theorem fin15Anchored_clause21028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom2994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04742
  ] at hbad
  tauto

theorem fin15Anchored_clause21029 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom0862 Fin15AnchoredAtom0873
    Fin15AnchoredAtom1058 Fin15AnchoredAtom1278 Fin15AnchoredAtom2994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04742
  ] at hbad
  tauto

theorem fin15Anchored_clause21030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom2995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08838
  ] at hbad
  tauto

theorem fin15Anchored_clause21031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0863 Fin15AnchoredAtom2995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08838
  ] at hbad
  tauto

theorem fin15Anchored_clause21032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0874 Fin15AnchoredAtom2995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08838
  ] at hbad
  tauto

theorem fin15Anchored_clause21033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom2995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08838
  ] at hbad
  tauto

theorem fin15Anchored_clause21034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1279 Fin15AnchoredAtom2995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08838
  ] at hbad
  tauto

theorem fin15Anchored_clause21035 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom0863 Fin15AnchoredAtom0874
    Fin15AnchoredAtom1059 Fin15AnchoredAtom1279 Fin15AnchoredAtom2995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08838
  ] at hbad
  tauto

theorem fin15Anchored_clause21036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom2996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17030
  ] at hbad
  tauto

theorem fin15Anchored_clause21037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0864 Fin15AnchoredAtom2996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17030
  ] at hbad
  tauto

theorem fin15Anchored_clause21038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0875 Fin15AnchoredAtom2996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17030
  ] at hbad
  tauto

theorem fin15Anchored_clause21039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1060 Fin15AnchoredAtom2996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17030
  ] at hbad
  tauto

theorem fin15Anchored_clause21040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1280 Fin15AnchoredAtom2996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17030
  ] at hbad
  tauto

theorem fin15Anchored_clause21041 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom0864 Fin15AnchoredAtom0875
    Fin15AnchoredAtom1060 Fin15AnchoredAtom1280 Fin15AnchoredAtom2996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17030
  ] at hbad
  tauto

theorem fin15Anchored_clause21042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2997 chi ∧
      ¬Fin15AnchoredAtom0861 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0861 Fin15AnchoredAtom2997 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03206
  ] at hbad
  tauto

theorem fin15Anchored_clause21043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2997 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1281 Fin15AnchoredAtom2997 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03206
  ] at hbad
  tauto

theorem fin15Anchored_clause21044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom2998 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05254
  ] at hbad
  tauto

theorem fin15Anchored_clause21045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom2998 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05254
  ] at hbad
  tauto

theorem fin15Anchored_clause21046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0877 Fin15AnchoredAtom2998 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05254
  ] at hbad
  tauto

theorem fin15Anchored_clause21047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom2998 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05254
  ] at hbad
  tauto

theorem fin15Anchored_clause21048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom2998 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05254
  ] at hbad
  tauto

theorem fin15Anchored_clause21049 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom0862 Fin15AnchoredAtom0877
    Fin15AnchoredAtom1062 Fin15AnchoredAtom1282 Fin15AnchoredAtom2998 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05254
  ] at hbad
  tauto

theorem fin15Anchored_clause21050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom2999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09350
  ] at hbad
  tauto

theorem fin15Anchored_clause21051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0863 Fin15AnchoredAtom2999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09350
  ] at hbad
  tauto

theorem fin15Anchored_clause21052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0878 Fin15AnchoredAtom2999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09350
  ] at hbad
  tauto

theorem fin15Anchored_clause21053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom2999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09350
  ] at hbad
  tauto

theorem fin15Anchored_clause21054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1283 Fin15AnchoredAtom2999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09350
  ] at hbad
  tauto

theorem fin15Anchored_clause21055 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom0863 Fin15AnchoredAtom0878
    Fin15AnchoredAtom1063 Fin15AnchoredAtom1283 Fin15AnchoredAtom2999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09350
  ] at hbad
  tauto

theorem fin15Anchored_clause21056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom3000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17542
  ] at hbad
  tauto

theorem fin15Anchored_clause21057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0864 Fin15AnchoredAtom3000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17542
  ] at hbad
  tauto

theorem fin15Anchored_clause21058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0879 Fin15AnchoredAtom3000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17542
  ] at hbad
  tauto

theorem fin15Anchored_clause21059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1064 Fin15AnchoredAtom3000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17542
  ] at hbad
  tauto

theorem fin15Anchored_clause21060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1284 Fin15AnchoredAtom3000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17542
  ] at hbad
  tauto

theorem fin15Anchored_clause21061 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom0864 Fin15AnchoredAtom0879
    Fin15AnchoredAtom1064 Fin15AnchoredAtom1284 Fin15AnchoredAtom3000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17542
  ] at hbad
  tauto

theorem fin15Anchored_clause21062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3001 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom3001 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06278
  ] at hbad
  tauto

theorem fin15Anchored_clause21063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom3004 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12422
  ] at hbad
  tauto

theorem fin15Anchored_clause21064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0863 Fin15AnchoredAtom3004 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12422
  ] at hbad
  tauto

theorem fin15Anchored_clause21065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0883 Fin15AnchoredAtom3004 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12422
  ] at hbad
  tauto

theorem fin15Anchored_clause21066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom3004 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12422
  ] at hbad
  tauto

theorem fin15Anchored_clause21067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1288 Fin15AnchoredAtom3004 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12422
  ] at hbad
  tauto

theorem fin15Anchored_clause21068 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom0863 Fin15AnchoredAtom0883
    Fin15AnchoredAtom1068 Fin15AnchoredAtom1288 Fin15AnchoredAtom3004 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12422
  ] at hbad
  tauto

theorem fin15Anchored_clause21069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom3005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20614
  ] at hbad
  tauto

theorem fin15Anchored_clause21070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0864 Fin15AnchoredAtom3005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20614
  ] at hbad
  tauto

theorem fin15Anchored_clause21071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0884 Fin15AnchoredAtom3005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20614
  ] at hbad
  tauto

theorem fin15Anchored_clause21072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1069 Fin15AnchoredAtom3005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20614
  ] at hbad
  tauto

theorem fin15Anchored_clause21073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1289 Fin15AnchoredAtom3005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20614
  ] at hbad
  tauto

theorem fin15Anchored_clause21074 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom0864 Fin15AnchoredAtom0884
    Fin15AnchoredAtom1069 Fin15AnchoredAtom1289 Fin15AnchoredAtom3005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20614
  ] at hbad
  tauto

theorem fin15Anchored_clause21075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0863 Fin15AnchoredAtom3006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24710
  ] at hbad
  tauto

theorem fin15Anchored_clause21076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0864 Fin15AnchoredAtom3006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24710
  ] at hbad
  tauto

theorem fin15Anchored_clause21077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0885 Fin15AnchoredAtom3006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24710
  ] at hbad
  tauto

theorem fin15Anchored_clause21078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1070 Fin15AnchoredAtom3006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24710
  ] at hbad
  tauto

theorem fin15Anchored_clause21079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1290 Fin15AnchoredAtom3006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24710
  ] at hbad
  tauto

theorem fin15Anchored_clause21080 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0863 Fin15AnchoredAtom0864 Fin15AnchoredAtom0885
    Fin15AnchoredAtom1070 Fin15AnchoredAtom1290 Fin15AnchoredAtom3006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24710
  ] at hbad
  tauto

theorem fin15Anchored_clause21081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3007 chi ∧
      ¬Fin15AnchoredAtom1291 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1291 Fin15AnchoredAtom3007 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01798
  ] at hbad
  tauto

theorem fin15Anchored_clause21082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3013 chi ∧
      ¬Fin15AnchoredAtom1297 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1297 Fin15AnchoredAtom3013 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05382
  ] at hbad
  tauto

theorem fin15Anchored_clause21083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3014 chi ∧
      ¬Fin15AnchoredAtom1298 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1298 Fin15AnchoredAtom3014 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09478
  ] at hbad
  tauto

theorem fin15Anchored_clause21084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3019 chi ∧
      ¬Fin15AnchoredAtom1303 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1303 Fin15AnchoredAtom3019 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12550
  ] at hbad
  tauto

theorem fin15Anchored_clause21085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom3022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03590
  ] at hbad
  tauto

theorem fin15Anchored_clause21086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom0872 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0872 Fin15AnchoredAtom3022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03590
  ] at hbad
  tauto

theorem fin15Anchored_clause21087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom0876 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0876 Fin15AnchoredAtom3022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03590
  ] at hbad
  tauto

theorem fin15Anchored_clause21088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom1086 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1086 Fin15AnchoredAtom3022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03590
  ] at hbad
  tauto

theorem fin15Anchored_clause21089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1306 Fin15AnchoredAtom3022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03590
  ] at hbad
  tauto

theorem fin15Anchored_clause21090 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3022 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0872 chi ∧
      Fin15AnchoredAtom0876 chi ∧
      Fin15AnchoredAtom1086 chi ∧
      Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom0872 Fin15AnchoredAtom0876
    Fin15AnchoredAtom1086 Fin15AnchoredAtom1306 Fin15AnchoredAtom3022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03590
  ] at hbad
  tauto

theorem fin15Anchored_clause21091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom3023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05638
  ] at hbad
  tauto

theorem fin15Anchored_clause21092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom3023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05638
  ] at hbad
  tauto

theorem fin15Anchored_clause21093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0877 Fin15AnchoredAtom3023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05638
  ] at hbad
  tauto

theorem fin15Anchored_clause21094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom3023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05638
  ] at hbad
  tauto

theorem fin15Anchored_clause21095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom3023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05638
  ] at hbad
  tauto

theorem fin15Anchored_clause21096 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom0873 Fin15AnchoredAtom0877
    Fin15AnchoredAtom1087 Fin15AnchoredAtom1307 Fin15AnchoredAtom3023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05638
  ] at hbad
  tauto

theorem fin15Anchored_clause21097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom3024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09734
  ] at hbad
  tauto

theorem fin15Anchored_clause21098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0874 Fin15AnchoredAtom3024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09734
  ] at hbad
  tauto

theorem fin15Anchored_clause21099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0878 Fin15AnchoredAtom3024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09734
  ] at hbad
  tauto

theorem fin15Anchored_clause21100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom3024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09734
  ] at hbad
  tauto

theorem fin15Anchored_clause21101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1308 Fin15AnchoredAtom3024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09734
  ] at hbad
  tauto

theorem fin15Anchored_clause21102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom0874 Fin15AnchoredAtom0878
    Fin15AnchoredAtom1088 Fin15AnchoredAtom1308 Fin15AnchoredAtom3024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09734
  ] at hbad
  tauto

theorem fin15Anchored_clause21103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom3025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17926
  ] at hbad
  tauto

theorem fin15Anchored_clause21104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0875 Fin15AnchoredAtom3025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17926
  ] at hbad
  tauto

theorem fin15Anchored_clause21105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0879 Fin15AnchoredAtom3025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17926
  ] at hbad
  tauto

theorem fin15Anchored_clause21106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1089 Fin15AnchoredAtom3025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17926
  ] at hbad
  tauto

theorem fin15Anchored_clause21107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1309 Fin15AnchoredAtom3025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17926
  ] at hbad
  tauto

theorem fin15Anchored_clause21108 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom0875 Fin15AnchoredAtom0879
    Fin15AnchoredAtom1089 Fin15AnchoredAtom1309 Fin15AnchoredAtom3025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17926
  ] at hbad
  tauto

theorem fin15Anchored_clause21109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3026 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom3026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06662
  ] at hbad
  tauto

theorem fin15Anchored_clause21110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3026 chi ∧
      ¬Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1090 Fin15AnchoredAtom3026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06662
  ] at hbad
  tauto

theorem fin15Anchored_clause21111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3026 chi ∧
      ¬Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1310 Fin15AnchoredAtom3026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06662
  ] at hbad
  tauto

theorem fin15Anchored_clause21112 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3026 chi ∧
      Fin15AnchoredAtom0872 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0880 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0872 Fin15AnchoredAtom0873 Fin15AnchoredAtom0880
    Fin15AnchoredAtom1090 Fin15AnchoredAtom1310 Fin15AnchoredAtom3026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06662
  ] at hbad
  tauto

theorem fin15Anchored_clause21113 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom3029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12806
  ] at hbad
  tauto

theorem fin15Anchored_clause21114 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0874 Fin15AnchoredAtom3029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12806
  ] at hbad
  tauto

theorem fin15Anchored_clause21115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0883 Fin15AnchoredAtom3029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12806
  ] at hbad
  tauto

theorem fin15Anchored_clause21116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom3029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12806
  ] at hbad
  tauto

theorem fin15Anchored_clause21117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1313 Fin15AnchoredAtom3029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12806
  ] at hbad
  tauto

theorem fin15Anchored_clause21118 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom0874 Fin15AnchoredAtom0883
    Fin15AnchoredAtom1093 Fin15AnchoredAtom1313 Fin15AnchoredAtom3029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12806
  ] at hbad
  tauto

theorem fin15Anchored_clause21119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom3030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20998
  ] at hbad
  tauto

end ErdosSzekeres

end
