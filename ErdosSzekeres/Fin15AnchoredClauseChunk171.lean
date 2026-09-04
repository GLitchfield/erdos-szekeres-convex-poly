module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 171. -/

theorem fin15Anchored_clause21888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0939 Fin15AnchoredAtom3195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21002
  ] at hbad
  tauto

theorem fin15Anchored_clause21889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1094 Fin15AnchoredAtom3195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21002
  ] at hbad
  tauto

theorem fin15Anchored_clause21890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1479 Fin15AnchoredAtom3195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21002
  ] at hbad
  tauto

theorem fin15Anchored_clause21891 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom0930 Fin15AnchoredAtom0939
    Fin15AnchoredAtom1094 Fin15AnchoredAtom1479 Fin15AnchoredAtom3195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21002
  ] at hbad
  tauto

theorem fin15Anchored_clause21892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom3196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25098
  ] at hbad
  tauto

theorem fin15Anchored_clause21893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0930 Fin15AnchoredAtom3196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25098
  ] at hbad
  tauto

theorem fin15Anchored_clause21894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0940 Fin15AnchoredAtom3196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25098
  ] at hbad
  tauto

theorem fin15Anchored_clause21895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1095 Fin15AnchoredAtom3196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25098
  ] at hbad
  tauto

theorem fin15Anchored_clause21896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1480 Fin15AnchoredAtom3196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25098
  ] at hbad
  tauto

theorem fin15Anchored_clause21897 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom0930 Fin15AnchoredAtom0940
    Fin15AnchoredAtom1095 Fin15AnchoredAtom1480 Fin15AnchoredAtom3196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25098
  ] at hbad
  tauto

theorem fin15Anchored_clause21898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3197 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom3197 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07178
  ] at hbad
  tauto

theorem fin15Anchored_clause21899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3197 chi ∧
      ¬Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1096 Fin15AnchoredAtom3197 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07178
  ] at hbad
  tauto

theorem fin15Anchored_clause21900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3198 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom3198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11274
  ] at hbad
  tauto

theorem fin15Anchored_clause21901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3198 chi ∧
      ¬Fin15AnchoredAtom0936 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0936 Fin15AnchoredAtom3198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11274
  ] at hbad
  tauto

theorem fin15Anchored_clause21902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3199 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0934 Fin15AnchoredAtom3199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19466
  ] at hbad
  tauto

theorem fin15Anchored_clause21903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom3200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13322
  ] at hbad
  tauto

theorem fin15Anchored_clause21904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom3200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13322
  ] at hbad
  tauto

theorem fin15Anchored_clause21905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom3200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13322
  ] at hbad
  tauto

theorem fin15Anchored_clause21906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom3200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13322
  ] at hbad
  tauto

theorem fin15Anchored_clause21907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom3200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13322
  ] at hbad
  tauto

theorem fin15Anchored_clause21908 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom0933 Fin15AnchoredAtom0938
    Fin15AnchoredAtom1099 Fin15AnchoredAtom1484 Fin15AnchoredAtom3200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13322
  ] at hbad
  tauto

theorem fin15Anchored_clause21909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom3201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21514
  ] at hbad
  tauto

theorem fin15Anchored_clause21910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0934 Fin15AnchoredAtom3201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21514
  ] at hbad
  tauto

theorem fin15Anchored_clause21911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0939 Fin15AnchoredAtom3201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21514
  ] at hbad
  tauto

theorem fin15Anchored_clause21912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1100 Fin15AnchoredAtom3201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21514
  ] at hbad
  tauto

theorem fin15Anchored_clause21913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1485 Fin15AnchoredAtom3201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21514
  ] at hbad
  tauto

theorem fin15Anchored_clause21914 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom0934 Fin15AnchoredAtom0939
    Fin15AnchoredAtom1100 Fin15AnchoredAtom1485 Fin15AnchoredAtom3201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21514
  ] at hbad
  tauto

theorem fin15Anchored_clause21915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom3202 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25610
  ] at hbad
  tauto

theorem fin15Anchored_clause21916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0934 Fin15AnchoredAtom3202 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25610
  ] at hbad
  tauto

theorem fin15Anchored_clause21917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0940 Fin15AnchoredAtom3202 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25610
  ] at hbad
  tauto

theorem fin15Anchored_clause21918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1101 Fin15AnchoredAtom3202 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25610
  ] at hbad
  tauto

theorem fin15Anchored_clause21919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1486 Fin15AnchoredAtom3202 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25610
  ] at hbad
  tauto

theorem fin15Anchored_clause21920 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom0934 Fin15AnchoredAtom0940
    Fin15AnchoredAtom1101 Fin15AnchoredAtom1486 Fin15AnchoredAtom3202 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25610
  ] at hbad
  tauto

theorem fin15Anchored_clause21921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3203 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom3203 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14346
  ] at hbad
  tauto

theorem fin15Anchored_clause21922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3204 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0939 Fin15AnchoredAtom3204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22538
  ] at hbad
  tauto

theorem fin15Anchored_clause21923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom3206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28682
  ] at hbad
  tauto

theorem fin15Anchored_clause21924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0939 Fin15AnchoredAtom3206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28682
  ] at hbad
  tauto

theorem fin15Anchored_clause21925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0940 Fin15AnchoredAtom3206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28682
  ] at hbad
  tauto

theorem fin15Anchored_clause21926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1105 Fin15AnchoredAtom3206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28682
  ] at hbad
  tauto

theorem fin15Anchored_clause21927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1490 Fin15AnchoredAtom3206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28682
  ] at hbad
  tauto

theorem fin15Anchored_clause21928 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom0939 Fin15AnchoredAtom0940
    Fin15AnchoredAtom1105 Fin15AnchoredAtom1490 Fin15AnchoredAtom3206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28682
  ] at hbad
  tauto

theorem fin15Anchored_clause21929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom3207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00242
  ] at hbad
  tauto

theorem fin15Anchored_clause21930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom3207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00242
  ] at hbad
  tauto

theorem fin15Anchored_clause21931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom3207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00242
  ] at hbad
  tauto

theorem fin15Anchored_clause21932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom3207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00242
  ] at hbad
  tauto

theorem fin15Anchored_clause21933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom3207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00242
  ] at hbad
  tauto

theorem fin15Anchored_clause21934 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom0942 Fin15AnchoredAtom0950
    Fin15AnchoredAtom0986 Fin15AnchoredAtom1491 Fin15AnchoredAtom3207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00242
  ] at hbad
  tauto

theorem fin15Anchored_clause21935 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom3208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00370
  ] at hbad
  tauto

theorem fin15Anchored_clause21936 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom3208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00370
  ] at hbad
  tauto

theorem fin15Anchored_clause21937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom3208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00370
  ] at hbad
  tauto

theorem fin15Anchored_clause21938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom3208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00370
  ] at hbad
  tauto

theorem fin15Anchored_clause21939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom3208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00370
  ] at hbad
  tauto

theorem fin15Anchored_clause21940 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3208 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom0943 Fin15AnchoredAtom0951
    Fin15AnchoredAtom0987 Fin15AnchoredAtom1492 Fin15AnchoredAtom3208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00370
  ] at hbad
  tauto

theorem fin15Anchored_clause21941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom3209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00626
  ] at hbad
  tauto

theorem fin15Anchored_clause21942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom3209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00626
  ] at hbad
  tauto

theorem fin15Anchored_clause21943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom3209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00626
  ] at hbad
  tauto

theorem fin15Anchored_clause21944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom3209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00626
  ] at hbad
  tauto

theorem fin15Anchored_clause21945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom3209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00626
  ] at hbad
  tauto

theorem fin15Anchored_clause21946 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom0944 Fin15AnchoredAtom0952
    Fin15AnchoredAtom0988 Fin15AnchoredAtom1493 Fin15AnchoredAtom3209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00626
  ] at hbad
  tauto

theorem fin15Anchored_clause21947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom3210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01138
  ] at hbad
  tauto

theorem fin15Anchored_clause21948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom3210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01138
  ] at hbad
  tauto

theorem fin15Anchored_clause21949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom3210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01138
  ] at hbad
  tauto

theorem fin15Anchored_clause21950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom3210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01138
  ] at hbad
  tauto

theorem fin15Anchored_clause21951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom3210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01138
  ] at hbad
  tauto

theorem fin15Anchored_clause21952 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom0945 Fin15AnchoredAtom0953
    Fin15AnchoredAtom0989 Fin15AnchoredAtom1494 Fin15AnchoredAtom3210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01138
  ] at hbad
  tauto

theorem fin15Anchored_clause21953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3211 chi ∧
      ¬Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1495 Fin15AnchoredAtom3211 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02162
  ] at hbad
  tauto

theorem fin15Anchored_clause21954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom3212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04210
  ] at hbad
  tauto

theorem fin15Anchored_clause21955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom3212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04210
  ] at hbad
  tauto

theorem fin15Anchored_clause21956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom3212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04210
  ] at hbad
  tauto

theorem fin15Anchored_clause21957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom3212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04210
  ] at hbad
  tauto

theorem fin15Anchored_clause21958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom3212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04210
  ] at hbad
  tauto

theorem fin15Anchored_clause21959 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom0947 Fin15AnchoredAtom0955
    Fin15AnchoredAtom0991 Fin15AnchoredAtom1496 Fin15AnchoredAtom3212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04210
  ] at hbad
  tauto

theorem fin15Anchored_clause21960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom3213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08306
  ] at hbad
  tauto

theorem fin15Anchored_clause21961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom3213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08306
  ] at hbad
  tauto

theorem fin15Anchored_clause21962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom3213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08306
  ] at hbad
  tauto

theorem fin15Anchored_clause21963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0992 Fin15AnchoredAtom3213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08306
  ] at hbad
  tauto

theorem fin15Anchored_clause21964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom3213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08306
  ] at hbad
  tauto

theorem fin15Anchored_clause21965 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom0948 Fin15AnchoredAtom0956
    Fin15AnchoredAtom0992 Fin15AnchoredAtom1497 Fin15AnchoredAtom3213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08306
  ] at hbad
  tauto

theorem fin15Anchored_clause21966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom3214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16498
  ] at hbad
  tauto

theorem fin15Anchored_clause21967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0949 Fin15AnchoredAtom3214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16498
  ] at hbad
  tauto

theorem fin15Anchored_clause21968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0957 Fin15AnchoredAtom3214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16498
  ] at hbad
  tauto

theorem fin15Anchored_clause21969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0993 Fin15AnchoredAtom3214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16498
  ] at hbad
  tauto

theorem fin15Anchored_clause21970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1498 Fin15AnchoredAtom3214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16498
  ] at hbad
  tauto

theorem fin15Anchored_clause21971 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom0949 Fin15AnchoredAtom0957
    Fin15AnchoredAtom0993 Fin15AnchoredAtom1498 Fin15AnchoredAtom3214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16498
  ] at hbad
  tauto

theorem fin15Anchored_clause21972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom3215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00434
  ] at hbad
  tauto

theorem fin15Anchored_clause21973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom3215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00434
  ] at hbad
  tauto

theorem fin15Anchored_clause21974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom3215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00434
  ] at hbad
  tauto

theorem fin15Anchored_clause21975 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3215 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom0943 Fin15AnchoredAtom0958
    Fin15AnchoredAtom0994 Fin15AnchoredAtom1499 Fin15AnchoredAtom3215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00434
  ] at hbad
  tauto

theorem fin15Anchored_clause21976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom3216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00690
  ] at hbad
  tauto

theorem fin15Anchored_clause21977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom3216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00690
  ] at hbad
  tauto

theorem fin15Anchored_clause21978 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom3216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00690
  ] at hbad
  tauto

theorem fin15Anchored_clause21979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom3216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00690
  ] at hbad
  tauto

theorem fin15Anchored_clause21980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom3216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00690
  ] at hbad
  tauto

theorem fin15Anchored_clause21981 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom0944 Fin15AnchoredAtom0959
    Fin15AnchoredAtom0995 Fin15AnchoredAtom1500 Fin15AnchoredAtom3216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00690
  ] at hbad
  tauto

theorem fin15Anchored_clause21982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom3217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01202
  ] at hbad
  tauto

theorem fin15Anchored_clause21983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom3217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01202
  ] at hbad
  tauto

theorem fin15Anchored_clause21984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom3217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01202
  ] at hbad
  tauto

theorem fin15Anchored_clause21985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom3217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01202
  ] at hbad
  tauto

theorem fin15Anchored_clause21986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom3217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01202
  ] at hbad
  tauto

theorem fin15Anchored_clause21987 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom0945 Fin15AnchoredAtom0960
    Fin15AnchoredAtom0996 Fin15AnchoredAtom1501 Fin15AnchoredAtom3217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01202
  ] at hbad
  tauto

theorem fin15Anchored_clause21988 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3218 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom3218 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02226
  ] at hbad
  tauto

theorem fin15Anchored_clause21989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3218 chi ∧
      ¬Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1502 Fin15AnchoredAtom3218 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02226
  ] at hbad
  tauto

theorem fin15Anchored_clause21990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom3219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04274
  ] at hbad
  tauto

theorem fin15Anchored_clause21991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom3219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04274
  ] at hbad
  tauto

theorem fin15Anchored_clause21992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom3219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04274
  ] at hbad
  tauto

theorem fin15Anchored_clause21993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom3219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04274
  ] at hbad
  tauto

theorem fin15Anchored_clause21994 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom3219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04274
  ] at hbad
  tauto

theorem fin15Anchored_clause21995 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom0947 Fin15AnchoredAtom0962
    Fin15AnchoredAtom0998 Fin15AnchoredAtom1503 Fin15AnchoredAtom3219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04274
  ] at hbad
  tauto

theorem fin15Anchored_clause21996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom3220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08370
  ] at hbad
  tauto

theorem fin15Anchored_clause21997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom3220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08370
  ] at hbad
  tauto

theorem fin15Anchored_clause21998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom3220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08370
  ] at hbad
  tauto

theorem fin15Anchored_clause21999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom3220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08370
  ] at hbad
  tauto

theorem fin15Anchored_clause22000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom3220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08370
  ] at hbad
  tauto

theorem fin15Anchored_clause22001 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom0948 Fin15AnchoredAtom0963
    Fin15AnchoredAtom0999 Fin15AnchoredAtom1504 Fin15AnchoredAtom3220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08370
  ] at hbad
  tauto

theorem fin15Anchored_clause22002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom3221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16562
  ] at hbad
  tauto

theorem fin15Anchored_clause22003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0949 Fin15AnchoredAtom3221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16562
  ] at hbad
  tauto

theorem fin15Anchored_clause22004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0964 Fin15AnchoredAtom3221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16562
  ] at hbad
  tauto

theorem fin15Anchored_clause22005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1000 Fin15AnchoredAtom3221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16562
  ] at hbad
  tauto

theorem fin15Anchored_clause22006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1505 Fin15AnchoredAtom3221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16562
  ] at hbad
  tauto

theorem fin15Anchored_clause22007 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom0949 Fin15AnchoredAtom0964
    Fin15AnchoredAtom1000 Fin15AnchoredAtom1505 Fin15AnchoredAtom3221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16562
  ] at hbad
  tauto

theorem fin15Anchored_clause22008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom3222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00818
  ] at hbad
  tauto

theorem fin15Anchored_clause22009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom3222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00818
  ] at hbad
  tauto

theorem fin15Anchored_clause22010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom3222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00818
  ] at hbad
  tauto

theorem fin15Anchored_clause22011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom3222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00818
  ] at hbad
  tauto

theorem fin15Anchored_clause22012 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3222 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom0944 Fin15AnchoredAtom0965
    Fin15AnchoredAtom1001 Fin15AnchoredAtom1506 Fin15AnchoredAtom3222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00818
  ] at hbad
  tauto

theorem fin15Anchored_clause22013 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom3223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01330
  ] at hbad
  tauto

theorem fin15Anchored_clause22014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom3223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01330
  ] at hbad
  tauto

theorem fin15Anchored_clause22015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom3223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01330
  ] at hbad
  tauto

end ErdosSzekeres

end
