module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 140. -/

theorem fin15Anchored_clause17920 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom0604 Fin15AnchoredAtom0621
    Fin15AnchoredAtom0666 Fin15AnchoredAtom1337 Fin15AnchoredAtom2338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00601
  ] at hbad
  tauto

theorem fin15Anchored_clause17921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom2339 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01113
  ] at hbad
  tauto

theorem fin15Anchored_clause17922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom2339 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01113
  ] at hbad
  tauto

theorem fin15Anchored_clause17923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom2339 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01113
  ] at hbad
  tauto

theorem fin15Anchored_clause17924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom2339 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01113
  ] at hbad
  tauto

theorem fin15Anchored_clause17925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom2339 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01113
  ] at hbad
  tauto

theorem fin15Anchored_clause17926 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom0605 Fin15AnchoredAtom0622
    Fin15AnchoredAtom0667 Fin15AnchoredAtom1338 Fin15AnchoredAtom2339 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01113
  ] at hbad
  tauto

theorem fin15Anchored_clause17927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2340 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom2340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02137
  ] at hbad
  tauto

theorem fin15Anchored_clause17928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2340 chi ∧
      ¬Fin15AnchoredAtom0668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0668 Fin15AnchoredAtom2340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02137
  ] at hbad
  tauto

theorem fin15Anchored_clause17929 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2340 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom1339 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom0606 Fin15AnchoredAtom0623
    Fin15AnchoredAtom0668 Fin15AnchoredAtom1339 Fin15AnchoredAtom2340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02137
  ] at hbad
  tauto

theorem fin15Anchored_clause17930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom2341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04185
  ] at hbad
  tauto

theorem fin15Anchored_clause17931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom2341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04185
  ] at hbad
  tauto

theorem fin15Anchored_clause17932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom2341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04185
  ] at hbad
  tauto

theorem fin15Anchored_clause17933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom2341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04185
  ] at hbad
  tauto

theorem fin15Anchored_clause17934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom2341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04185
  ] at hbad
  tauto

theorem fin15Anchored_clause17935 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom0607 Fin15AnchoredAtom0624
    Fin15AnchoredAtom0669 Fin15AnchoredAtom1340 Fin15AnchoredAtom2341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04185
  ] at hbad
  tauto

theorem fin15Anchored_clause17936 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom2342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08281
  ] at hbad
  tauto

theorem fin15Anchored_clause17937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom2342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08281
  ] at hbad
  tauto

theorem fin15Anchored_clause17938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom2342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08281
  ] at hbad
  tauto

theorem fin15Anchored_clause17939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0670 Fin15AnchoredAtom2342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08281
  ] at hbad
  tauto

theorem fin15Anchored_clause17940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1341 Fin15AnchoredAtom2342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08281
  ] at hbad
  tauto

theorem fin15Anchored_clause17941 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom0608 Fin15AnchoredAtom0625
    Fin15AnchoredAtom0670 Fin15AnchoredAtom1341 Fin15AnchoredAtom2342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08281
  ] at hbad
  tauto

theorem fin15Anchored_clause17942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom2343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16473
  ] at hbad
  tauto

theorem fin15Anchored_clause17943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0609 Fin15AnchoredAtom2343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16473
  ] at hbad
  tauto

theorem fin15Anchored_clause17944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0626 Fin15AnchoredAtom2343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16473
  ] at hbad
  tauto

theorem fin15Anchored_clause17945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0671 Fin15AnchoredAtom2343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16473
  ] at hbad
  tauto

theorem fin15Anchored_clause17946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1342 Fin15AnchoredAtom2343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16473
  ] at hbad
  tauto

theorem fin15Anchored_clause17947 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom0609 Fin15AnchoredAtom0626
    Fin15AnchoredAtom0671 Fin15AnchoredAtom1342 Fin15AnchoredAtom2343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16473
  ] at hbad
  tauto

theorem fin15Anchored_clause17948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom2344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00409
  ] at hbad
  tauto

theorem fin15Anchored_clause17949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom0603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom2344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00409
  ] at hbad
  tauto

theorem fin15Anchored_clause17950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom2344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00409
  ] at hbad
  tauto

theorem fin15Anchored_clause17951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom2344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00409
  ] at hbad
  tauto

theorem fin15Anchored_clause17952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2344 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom2344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00409
  ] at hbad
  tauto

theorem fin15Anchored_clause17953 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom0603 Fin15AnchoredAtom0627
    Fin15AnchoredAtom0672 Fin15AnchoredAtom1343 Fin15AnchoredAtom2344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00409
  ] at hbad
  tauto

theorem fin15Anchored_clause17954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom2345 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00665
  ] at hbad
  tauto

theorem fin15Anchored_clause17955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom2345 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00665
  ] at hbad
  tauto

theorem fin15Anchored_clause17956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom2345 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00665
  ] at hbad
  tauto

theorem fin15Anchored_clause17957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom2345 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00665
  ] at hbad
  tauto

theorem fin15Anchored_clause17958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom2345 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00665
  ] at hbad
  tauto

theorem fin15Anchored_clause17959 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom0604 Fin15AnchoredAtom0628
    Fin15AnchoredAtom0673 Fin15AnchoredAtom1344 Fin15AnchoredAtom2345 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00665
  ] at hbad
  tauto

theorem fin15Anchored_clause17960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom2346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01177
  ] at hbad
  tauto

theorem fin15Anchored_clause17961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom2346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01177
  ] at hbad
  tauto

theorem fin15Anchored_clause17962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom2346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01177
  ] at hbad
  tauto

theorem fin15Anchored_clause17963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom2346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01177
  ] at hbad
  tauto

theorem fin15Anchored_clause17964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom2346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01177
  ] at hbad
  tauto

theorem fin15Anchored_clause17965 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom0605 Fin15AnchoredAtom0629
    Fin15AnchoredAtom0674 Fin15AnchoredAtom1345 Fin15AnchoredAtom2346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01177
  ] at hbad
  tauto

theorem fin15Anchored_clause17966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom2347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02201
  ] at hbad
  tauto

theorem fin15Anchored_clause17967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom0606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0606 Fin15AnchoredAtom2347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02201
  ] at hbad
  tauto

theorem fin15Anchored_clause17968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom0630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0630 Fin15AnchoredAtom2347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02201
  ] at hbad
  tauto

theorem fin15Anchored_clause17969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom0675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0675 Fin15AnchoredAtom2347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02201
  ] at hbad
  tauto

theorem fin15Anchored_clause17970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2347 chi ∧
      ¬Fin15AnchoredAtom1346 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1346 Fin15AnchoredAtom2347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02201
  ] at hbad
  tauto

theorem fin15Anchored_clause17971 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2347 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom1346 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom0606 Fin15AnchoredAtom0630
    Fin15AnchoredAtom0675 Fin15AnchoredAtom1346 Fin15AnchoredAtom2347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02201
  ] at hbad
  tauto

theorem fin15Anchored_clause17972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom2348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04249
  ] at hbad
  tauto

theorem fin15Anchored_clause17973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom2348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04249
  ] at hbad
  tauto

theorem fin15Anchored_clause17974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom2348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04249
  ] at hbad
  tauto

theorem fin15Anchored_clause17975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom2348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04249
  ] at hbad
  tauto

theorem fin15Anchored_clause17976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom2348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04249
  ] at hbad
  tauto

theorem fin15Anchored_clause17977 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom0607 Fin15AnchoredAtom0631
    Fin15AnchoredAtom0676 Fin15AnchoredAtom1347 Fin15AnchoredAtom2348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04249
  ] at hbad
  tauto

theorem fin15Anchored_clause17978 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom2349 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08345
  ] at hbad
  tauto

theorem fin15Anchored_clause17979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom2349 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08345
  ] at hbad
  tauto

theorem fin15Anchored_clause17980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom2349 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08345
  ] at hbad
  tauto

theorem fin15Anchored_clause17981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0677 Fin15AnchoredAtom2349 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08345
  ] at hbad
  tauto

theorem fin15Anchored_clause17982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1348 Fin15AnchoredAtom2349 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08345
  ] at hbad
  tauto

theorem fin15Anchored_clause17983 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom0608 Fin15AnchoredAtom0632
    Fin15AnchoredAtom0677 Fin15AnchoredAtom1348 Fin15AnchoredAtom2349 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08345
  ] at hbad
  tauto

theorem fin15Anchored_clause17984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom2350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16537
  ] at hbad
  tauto

theorem fin15Anchored_clause17985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0609 Fin15AnchoredAtom2350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16537
  ] at hbad
  tauto

theorem fin15Anchored_clause17986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0633 Fin15AnchoredAtom2350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16537
  ] at hbad
  tauto

theorem fin15Anchored_clause17987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0678 Fin15AnchoredAtom2350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16537
  ] at hbad
  tauto

theorem fin15Anchored_clause17988 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1349 Fin15AnchoredAtom2350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16537
  ] at hbad
  tauto

theorem fin15Anchored_clause17989 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom0609 Fin15AnchoredAtom0633
    Fin15AnchoredAtom0678 Fin15AnchoredAtom1349 Fin15AnchoredAtom2350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16537
  ] at hbad
  tauto

theorem fin15Anchored_clause17990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom0603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom2351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00793
  ] at hbad
  tauto

theorem fin15Anchored_clause17991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom2351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00793
  ] at hbad
  tauto

theorem fin15Anchored_clause17992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom0634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom2351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00793
  ] at hbad
  tauto

theorem fin15Anchored_clause17993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom0679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom2351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00793
  ] at hbad
  tauto

theorem fin15Anchored_clause17994 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2351 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom2351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00793
  ] at hbad
  tauto

theorem fin15Anchored_clause17995 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom0604 Fin15AnchoredAtom0634
    Fin15AnchoredAtom0679 Fin15AnchoredAtom1350 Fin15AnchoredAtom2351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00793
  ] at hbad
  tauto

theorem fin15Anchored_clause17996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom0603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom2352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01305
  ] at hbad
  tauto

theorem fin15Anchored_clause17997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom2352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01305
  ] at hbad
  tauto

theorem fin15Anchored_clause17998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom2352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01305
  ] at hbad
  tauto

theorem fin15Anchored_clause17999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom0680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom2352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01305
  ] at hbad
  tauto

theorem fin15Anchored_clause18000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2352 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom2352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01305
  ] at hbad
  tauto

theorem fin15Anchored_clause18001 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom0605 Fin15AnchoredAtom0635
    Fin15AnchoredAtom0680 Fin15AnchoredAtom1351 Fin15AnchoredAtom2352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01305
  ] at hbad
  tauto

theorem fin15Anchored_clause18002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom0603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom2354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04377
  ] at hbad
  tauto

theorem fin15Anchored_clause18003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom2354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04377
  ] at hbad
  tauto

theorem fin15Anchored_clause18004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom2354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04377
  ] at hbad
  tauto

theorem fin15Anchored_clause18005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom0682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0682 Fin15AnchoredAtom2354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04377
  ] at hbad
  tauto

theorem fin15Anchored_clause18006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2354 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1353 Fin15AnchoredAtom2354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04377
  ] at hbad
  tauto

theorem fin15Anchored_clause18007 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom0607 Fin15AnchoredAtom0637
    Fin15AnchoredAtom0682 Fin15AnchoredAtom1353 Fin15AnchoredAtom2354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04377
  ] at hbad
  tauto

theorem fin15Anchored_clause18008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom0603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom2355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08473
  ] at hbad
  tauto

theorem fin15Anchored_clause18009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom2355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08473
  ] at hbad
  tauto

theorem fin15Anchored_clause18010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom0638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0638 Fin15AnchoredAtom2355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08473
  ] at hbad
  tauto

theorem fin15Anchored_clause18011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom0683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0683 Fin15AnchoredAtom2355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08473
  ] at hbad
  tauto

theorem fin15Anchored_clause18012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2355 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1354 Fin15AnchoredAtom2355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08473
  ] at hbad
  tauto

theorem fin15Anchored_clause18013 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom0608 Fin15AnchoredAtom0638
    Fin15AnchoredAtom0683 Fin15AnchoredAtom1354 Fin15AnchoredAtom2355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08473
  ] at hbad
  tauto

theorem fin15Anchored_clause18014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom0603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom2356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16665
  ] at hbad
  tauto

theorem fin15Anchored_clause18015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0609 Fin15AnchoredAtom2356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16665
  ] at hbad
  tauto

theorem fin15Anchored_clause18016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom0639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0639 Fin15AnchoredAtom2356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16665
  ] at hbad
  tauto

theorem fin15Anchored_clause18017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0684 Fin15AnchoredAtom2356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16665
  ] at hbad
  tauto

theorem fin15Anchored_clause18018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2356 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1355 Fin15AnchoredAtom2356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16665
  ] at hbad
  tauto

theorem fin15Anchored_clause18019 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom0609 Fin15AnchoredAtom0639
    Fin15AnchoredAtom0684 Fin15AnchoredAtom1355 Fin15AnchoredAtom2356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16665
  ] at hbad
  tauto

theorem fin15Anchored_clause18020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom2357 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01561
  ] at hbad
  tauto

theorem fin15Anchored_clause18021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom2357 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01561
  ] at hbad
  tauto

theorem fin15Anchored_clause18022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom2357 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01561
  ] at hbad
  tauto

theorem fin15Anchored_clause18023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom2357 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01561
  ] at hbad
  tauto

theorem fin15Anchored_clause18024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom2357 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01561
  ] at hbad
  tauto

theorem fin15Anchored_clause18025 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom0605 Fin15AnchoredAtom0640
    Fin15AnchoredAtom0685 Fin15AnchoredAtom1356 Fin15AnchoredAtom2357 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01561
  ] at hbad
  tauto

theorem fin15Anchored_clause18026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2358 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom2358 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02585
  ] at hbad
  tauto

theorem fin15Anchored_clause18027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2358 chi ∧
      ¬Fin15AnchoredAtom0686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0686 Fin15AnchoredAtom2358 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02585
  ] at hbad
  tauto

theorem fin15Anchored_clause18028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2358 chi ∧
      ¬Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1357 Fin15AnchoredAtom2358 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02585
  ] at hbad
  tauto

theorem fin15Anchored_clause18029 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2358 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom0606 Fin15AnchoredAtom0641
    Fin15AnchoredAtom0686 Fin15AnchoredAtom1357 Fin15AnchoredAtom2358 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02585
  ] at hbad
  tauto

theorem fin15Anchored_clause18030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom2359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04633
  ] at hbad
  tauto

theorem fin15Anchored_clause18031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom2359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04633
  ] at hbad
  tauto

theorem fin15Anchored_clause18032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom2359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04633
  ] at hbad
  tauto

theorem fin15Anchored_clause18033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom2359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04633
  ] at hbad
  tauto

theorem fin15Anchored_clause18034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom2359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04633
  ] at hbad
  tauto

theorem fin15Anchored_clause18035 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom0607 Fin15AnchoredAtom0642
    Fin15AnchoredAtom0687 Fin15AnchoredAtom1358 Fin15AnchoredAtom2359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04633
  ] at hbad
  tauto

theorem fin15Anchored_clause18036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom2360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08729
  ] at hbad
  tauto

theorem fin15Anchored_clause18037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom2360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08729
  ] at hbad
  tauto

theorem fin15Anchored_clause18038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0643 Fin15AnchoredAtom2360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08729
  ] at hbad
  tauto

theorem fin15Anchored_clause18039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0688 Fin15AnchoredAtom2360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08729
  ] at hbad
  tauto

theorem fin15Anchored_clause18040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1359 Fin15AnchoredAtom2360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08729
  ] at hbad
  tauto

theorem fin15Anchored_clause18041 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom0608 Fin15AnchoredAtom0643
    Fin15AnchoredAtom0688 Fin15AnchoredAtom1359 Fin15AnchoredAtom2360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08729
  ] at hbad
  tauto

theorem fin15Anchored_clause18042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom2361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16921
  ] at hbad
  tauto

theorem fin15Anchored_clause18043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0609 Fin15AnchoredAtom2361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16921
  ] at hbad
  tauto

theorem fin15Anchored_clause18044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0644 Fin15AnchoredAtom2361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16921
  ] at hbad
  tauto

theorem fin15Anchored_clause18045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0689 Fin15AnchoredAtom2361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16921
  ] at hbad
  tauto

theorem fin15Anchored_clause18046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1360 Fin15AnchoredAtom2361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16921
  ] at hbad
  tauto

theorem fin15Anchored_clause18047 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom0609 Fin15AnchoredAtom0644
    Fin15AnchoredAtom0689 Fin15AnchoredAtom1360 Fin15AnchoredAtom2361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16921
  ] at hbad
  tauto

end ErdosSzekeres

end
