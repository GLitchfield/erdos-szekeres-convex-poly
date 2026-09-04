module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 125. -/

theorem fin15Anchored_clause16000 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom0478 Fin15AnchoredAtom0527
    Fin15AnchoredAtom0648 Fin15AnchoredAtom0934 Fin15AnchoredAtom1935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17419
  ] at hbad
  tauto

theorem fin15Anchored_clause16001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom1936 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06155
  ] at hbad
  tauto

theorem fin15Anchored_clause16002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom0528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0528 Fin15AnchoredAtom1936 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06155
  ] at hbad
  tauto

theorem fin15Anchored_clause16003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1936 chi ∧
      ¬Fin15AnchoredAtom0935 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0935 Fin15AnchoredAtom1936 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06155
  ] at hbad
  tauto

theorem fin15Anchored_clause16004 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1936 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0935 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0475 Fin15AnchoredAtom0476 Fin15AnchoredAtom0528
    Fin15AnchoredAtom0649 Fin15AnchoredAtom0935 Fin15AnchoredAtom1936 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06155
  ] at hbad
  tauto

theorem fin15Anchored_clause16005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1937 chi ∧
      ¬Fin15AnchoredAtom0475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0475 Fin15AnchoredAtom1937 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10251
  ] at hbad
  tauto

theorem fin15Anchored_clause16006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1937 chi ∧
      ¬Fin15AnchoredAtom0529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0529 Fin15AnchoredAtom1937 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10251
  ] at hbad
  tauto

theorem fin15Anchored_clause16007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1937 chi ∧
      ¬Fin15AnchoredAtom0650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0650 Fin15AnchoredAtom1937 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10251
  ] at hbad
  tauto

theorem fin15Anchored_clause16008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1937 chi ∧
      ¬Fin15AnchoredAtom0936 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0936 Fin15AnchoredAtom1937 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10251
  ] at hbad
  tauto

theorem fin15Anchored_clause16009 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1937 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0936 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0475 Fin15AnchoredAtom0477 Fin15AnchoredAtom0529
    Fin15AnchoredAtom0650 Fin15AnchoredAtom0936 Fin15AnchoredAtom1937 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10251
  ] at hbad
  tauto

theorem fin15Anchored_clause16010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom0475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0475 Fin15AnchoredAtom1938 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18443
  ] at hbad
  tauto

theorem fin15Anchored_clause16011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0478 Fin15AnchoredAtom1938 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18443
  ] at hbad
  tauto

theorem fin15Anchored_clause16012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom0530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0530 Fin15AnchoredAtom1938 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18443
  ] at hbad
  tauto

theorem fin15Anchored_clause16013 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom0651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0651 Fin15AnchoredAtom1938 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18443
  ] at hbad
  tauto

theorem fin15Anchored_clause16014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1938 chi ∧
      ¬Fin15AnchoredAtom0937 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0937 Fin15AnchoredAtom1938 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18443
  ] at hbad
  tauto

theorem fin15Anchored_clause16015 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1938 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0530 chi ∧
      Fin15AnchoredAtom0651 chi ∧
      Fin15AnchoredAtom0937 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0475 Fin15AnchoredAtom0478 Fin15AnchoredAtom0530
    Fin15AnchoredAtom0651 Fin15AnchoredAtom0937 Fin15AnchoredAtom1938 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18443
  ] at hbad
  tauto

theorem fin15Anchored_clause16016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom1939 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12299
  ] at hbad
  tauto

theorem fin15Anchored_clause16017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0477 Fin15AnchoredAtom1939 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12299
  ] at hbad
  tauto

theorem fin15Anchored_clause16018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0531 Fin15AnchoredAtom1939 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12299
  ] at hbad
  tauto

theorem fin15Anchored_clause16019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom1939 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12299
  ] at hbad
  tauto

theorem fin15Anchored_clause16020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom1939 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12299
  ] at hbad
  tauto

theorem fin15Anchored_clause16021 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom0477 Fin15AnchoredAtom0531
    Fin15AnchoredAtom0652 Fin15AnchoredAtom0938 Fin15AnchoredAtom1939 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12299
  ] at hbad
  tauto

theorem fin15Anchored_clause16022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom1940 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20491
  ] at hbad
  tauto

theorem fin15Anchored_clause16023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0478 Fin15AnchoredAtom1940 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20491
  ] at hbad
  tauto

theorem fin15Anchored_clause16024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0532 Fin15AnchoredAtom1940 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20491
  ] at hbad
  tauto

theorem fin15Anchored_clause16025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0653 Fin15AnchoredAtom1940 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20491
  ] at hbad
  tauto

theorem fin15Anchored_clause16026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0939 Fin15AnchoredAtom1940 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20491
  ] at hbad
  tauto

theorem fin15Anchored_clause16027 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom0478 Fin15AnchoredAtom0532
    Fin15AnchoredAtom0653 Fin15AnchoredAtom0939 Fin15AnchoredAtom1940 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20491
  ] at hbad
  tauto

theorem fin15Anchored_clause16028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0477 Fin15AnchoredAtom1941 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24587
  ] at hbad
  tauto

theorem fin15Anchored_clause16029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0478 Fin15AnchoredAtom1941 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24587
  ] at hbad
  tauto

theorem fin15Anchored_clause16030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0533 Fin15AnchoredAtom1941 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24587
  ] at hbad
  tauto

theorem fin15Anchored_clause16031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0654 Fin15AnchoredAtom1941 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24587
  ] at hbad
  tauto

theorem fin15Anchored_clause16032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0940 Fin15AnchoredAtom1941 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24587
  ] at hbad
  tauto

theorem fin15Anchored_clause16033 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0477 Fin15AnchoredAtom0478 Fin15AnchoredAtom0533
    Fin15AnchoredAtom0654 Fin15AnchoredAtom0940 Fin15AnchoredAtom1941 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24587
  ] at hbad
  tauto

theorem fin15Anchored_clause16034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom1942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00115
  ] at hbad
  tauto

theorem fin15Anchored_clause16035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom1942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00115
  ] at hbad
  tauto

theorem fin15Anchored_clause16036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom1942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00115
  ] at hbad
  tauto

theorem fin15Anchored_clause16037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom1942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00115
  ] at hbad
  tauto

theorem fin15Anchored_clause16038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom1942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00115
  ] at hbad
  tauto

theorem fin15Anchored_clause16039 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom0480 Fin15AnchoredAtom0489
    Fin15AnchoredAtom0655 Fin15AnchoredAtom0941 Fin15AnchoredAtom1942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00115
  ] at hbad
  tauto

theorem fin15Anchored_clause16040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom1943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00179
  ] at hbad
  tauto

theorem fin15Anchored_clause16041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom1943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00179
  ] at hbad
  tauto

theorem fin15Anchored_clause16042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom1943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00179
  ] at hbad
  tauto

theorem fin15Anchored_clause16043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom1943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00179
  ] at hbad
  tauto

theorem fin15Anchored_clause16044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom1943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00179
  ] at hbad
  tauto

theorem fin15Anchored_clause16045 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom0481 Fin15AnchoredAtom0490
    Fin15AnchoredAtom0656 Fin15AnchoredAtom0942 Fin15AnchoredAtom1943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00179
  ] at hbad
  tauto

theorem fin15Anchored_clause16046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom1944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00307
  ] at hbad
  tauto

theorem fin15Anchored_clause16047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom1944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00307
  ] at hbad
  tauto

theorem fin15Anchored_clause16048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom0657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom1944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00307
  ] at hbad
  tauto

theorem fin15Anchored_clause16049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1944 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom1944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00307
  ] at hbad
  tauto

theorem fin15Anchored_clause16050 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1944 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom0482 Fin15AnchoredAtom0491
    Fin15AnchoredAtom0657 Fin15AnchoredAtom0943 Fin15AnchoredAtom1944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00307
  ] at hbad
  tauto

theorem fin15Anchored_clause16051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom1945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00563
  ] at hbad
  tauto

theorem fin15Anchored_clause16052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom1945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00563
  ] at hbad
  tauto

theorem fin15Anchored_clause16053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom1945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00563
  ] at hbad
  tauto

theorem fin15Anchored_clause16054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom1945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00563
  ] at hbad
  tauto

theorem fin15Anchored_clause16055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom1945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00563
  ] at hbad
  tauto

theorem fin15Anchored_clause16056 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom0483 Fin15AnchoredAtom0492
    Fin15AnchoredAtom0658 Fin15AnchoredAtom0944 Fin15AnchoredAtom1945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00563
  ] at hbad
  tauto

theorem fin15Anchored_clause16057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom1946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01075
  ] at hbad
  tauto

theorem fin15Anchored_clause16058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom1946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01075
  ] at hbad
  tauto

theorem fin15Anchored_clause16059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom1946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01075
  ] at hbad
  tauto

theorem fin15Anchored_clause16060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom1946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01075
  ] at hbad
  tauto

theorem fin15Anchored_clause16061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom1946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01075
  ] at hbad
  tauto

theorem fin15Anchored_clause16062 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom0484 Fin15AnchoredAtom0493
    Fin15AnchoredAtom0659 Fin15AnchoredAtom0945 Fin15AnchoredAtom1946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01075
  ] at hbad
  tauto

theorem fin15Anchored_clause16063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1947 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom1947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02099
  ] at hbad
  tauto

theorem fin15Anchored_clause16064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1947 chi ∧
      ¬Fin15AnchoredAtom0660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0660 Fin15AnchoredAtom1947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02099
  ] at hbad
  tauto

theorem fin15Anchored_clause16065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom1948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04147
  ] at hbad
  tauto

theorem fin15Anchored_clause16066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom1948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04147
  ] at hbad
  tauto

theorem fin15Anchored_clause16067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom1948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04147
  ] at hbad
  tauto

theorem fin15Anchored_clause16068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom1948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04147
  ] at hbad
  tauto

theorem fin15Anchored_clause16069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom1948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04147
  ] at hbad
  tauto

theorem fin15Anchored_clause16070 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom0486 Fin15AnchoredAtom0495
    Fin15AnchoredAtom0661 Fin15AnchoredAtom0947 Fin15AnchoredAtom1948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04147
  ] at hbad
  tauto

theorem fin15Anchored_clause16071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom1949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08243
  ] at hbad
  tauto

theorem fin15Anchored_clause16072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom1949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08243
  ] at hbad
  tauto

theorem fin15Anchored_clause16073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0496 Fin15AnchoredAtom1949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08243
  ] at hbad
  tauto

theorem fin15Anchored_clause16074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0662 Fin15AnchoredAtom1949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08243
  ] at hbad
  tauto

theorem fin15Anchored_clause16075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom1949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08243
  ] at hbad
  tauto

theorem fin15Anchored_clause16076 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom0487 Fin15AnchoredAtom0496
    Fin15AnchoredAtom0662 Fin15AnchoredAtom0948 Fin15AnchoredAtom1949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08243
  ] at hbad
  tauto

theorem fin15Anchored_clause16077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom1950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16435
  ] at hbad
  tauto

theorem fin15Anchored_clause16078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0488 Fin15AnchoredAtom1950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16435
  ] at hbad
  tauto

theorem fin15Anchored_clause16079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0497 Fin15AnchoredAtom1950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16435
  ] at hbad
  tauto

theorem fin15Anchored_clause16080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0663 Fin15AnchoredAtom1950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16435
  ] at hbad
  tauto

theorem fin15Anchored_clause16081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0949 Fin15AnchoredAtom1950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16435
  ] at hbad
  tauto

theorem fin15Anchored_clause16082 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom0488 Fin15AnchoredAtom0497
    Fin15AnchoredAtom0663 Fin15AnchoredAtom0949 Fin15AnchoredAtom1950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16435
  ] at hbad
  tauto

theorem fin15Anchored_clause16083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom1951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00211
  ] at hbad
  tauto

theorem fin15Anchored_clause16084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom1951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00211
  ] at hbad
  tauto

theorem fin15Anchored_clause16085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom1951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00211
  ] at hbad
  tauto

theorem fin15Anchored_clause16086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom1951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00211
  ] at hbad
  tauto

theorem fin15Anchored_clause16087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom1951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00211
  ] at hbad
  tauto

theorem fin15Anchored_clause16088 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom0481 Fin15AnchoredAtom0498
    Fin15AnchoredAtom0664 Fin15AnchoredAtom0950 Fin15AnchoredAtom1951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00211
  ] at hbad
  tauto

theorem fin15Anchored_clause16089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom1952 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00339
  ] at hbad
  tauto

theorem fin15Anchored_clause16090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom1952 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00339
  ] at hbad
  tauto

theorem fin15Anchored_clause16091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom1952 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00339
  ] at hbad
  tauto

theorem fin15Anchored_clause16092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1952 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom1952 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00339
  ] at hbad
  tauto

theorem fin15Anchored_clause16093 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1952 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom0482 Fin15AnchoredAtom0499
    Fin15AnchoredAtom0665 Fin15AnchoredAtom0951 Fin15AnchoredAtom1952 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00339
  ] at hbad
  tauto

theorem fin15Anchored_clause16094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom1953 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00595
  ] at hbad
  tauto

theorem fin15Anchored_clause16095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom1953 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00595
  ] at hbad
  tauto

theorem fin15Anchored_clause16096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom1953 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00595
  ] at hbad
  tauto

theorem fin15Anchored_clause16097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom1953 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00595
  ] at hbad
  tauto

theorem fin15Anchored_clause16098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom1953 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00595
  ] at hbad
  tauto

theorem fin15Anchored_clause16099 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom0483 Fin15AnchoredAtom0500
    Fin15AnchoredAtom0666 Fin15AnchoredAtom0952 Fin15AnchoredAtom1953 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00595
  ] at hbad
  tauto

theorem fin15Anchored_clause16100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom1954 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01107
  ] at hbad
  tauto

theorem fin15Anchored_clause16101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom1954 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01107
  ] at hbad
  tauto

theorem fin15Anchored_clause16102 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom1954 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01107
  ] at hbad
  tauto

theorem fin15Anchored_clause16103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom1954 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01107
  ] at hbad
  tauto

theorem fin15Anchored_clause16104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom1954 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01107
  ] at hbad
  tauto

theorem fin15Anchored_clause16105 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom0484 Fin15AnchoredAtom0501
    Fin15AnchoredAtom0667 Fin15AnchoredAtom0953 Fin15AnchoredAtom1954 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01107
  ] at hbad
  tauto

theorem fin15Anchored_clause16106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1955 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom1955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02131
  ] at hbad
  tauto

theorem fin15Anchored_clause16107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1955 chi ∧
      ¬Fin15AnchoredAtom0668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0668 Fin15AnchoredAtom1955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02131
  ] at hbad
  tauto

theorem fin15Anchored_clause16108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom1956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04179
  ] at hbad
  tauto

theorem fin15Anchored_clause16109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom1956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04179
  ] at hbad
  tauto

theorem fin15Anchored_clause16110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom1956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04179
  ] at hbad
  tauto

theorem fin15Anchored_clause16111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom1956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04179
  ] at hbad
  tauto

theorem fin15Anchored_clause16112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom1956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04179
  ] at hbad
  tauto

theorem fin15Anchored_clause16113 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom0486 Fin15AnchoredAtom0503
    Fin15AnchoredAtom0669 Fin15AnchoredAtom0955 Fin15AnchoredAtom1956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04179
  ] at hbad
  tauto

theorem fin15Anchored_clause16114 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom1957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08275
  ] at hbad
  tauto

theorem fin15Anchored_clause16115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom1957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08275
  ] at hbad
  tauto

theorem fin15Anchored_clause16116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom1957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08275
  ] at hbad
  tauto

theorem fin15Anchored_clause16117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0670 Fin15AnchoredAtom1957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08275
  ] at hbad
  tauto

theorem fin15Anchored_clause16118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom1957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08275
  ] at hbad
  tauto

theorem fin15Anchored_clause16119 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom0487 Fin15AnchoredAtom0504
    Fin15AnchoredAtom0670 Fin15AnchoredAtom0956 Fin15AnchoredAtom1957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08275
  ] at hbad
  tauto

theorem fin15Anchored_clause16120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom1958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16467
  ] at hbad
  tauto

theorem fin15Anchored_clause16121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0488 Fin15AnchoredAtom1958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16467
  ] at hbad
  tauto

theorem fin15Anchored_clause16122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0505 Fin15AnchoredAtom1958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16467
  ] at hbad
  tauto

theorem fin15Anchored_clause16123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0671 Fin15AnchoredAtom1958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16467
  ] at hbad
  tauto

theorem fin15Anchored_clause16124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0957 Fin15AnchoredAtom1958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16467
  ] at hbad
  tauto

theorem fin15Anchored_clause16125 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom0488 Fin15AnchoredAtom0505
    Fin15AnchoredAtom0671 Fin15AnchoredAtom0957 Fin15AnchoredAtom1958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16467
  ] at hbad
  tauto

theorem fin15Anchored_clause16126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom1959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00403
  ] at hbad
  tauto

theorem fin15Anchored_clause16127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom1959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00403
  ] at hbad
  tauto

end ErdosSzekeres

end
