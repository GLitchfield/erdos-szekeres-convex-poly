module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 141. -/

theorem fin15Anchored_clause18048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2362 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom2362 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03097
  ] at hbad
  tauto

theorem fin15Anchored_clause18049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2362 chi ∧
      ¬Fin15AnchoredAtom0690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0690 Fin15AnchoredAtom2362 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03097
  ] at hbad
  tauto

theorem fin15Anchored_clause18050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom2363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05145
  ] at hbad
  tauto

theorem fin15Anchored_clause18051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom2363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05145
  ] at hbad
  tauto

theorem fin15Anchored_clause18052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom2363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05145
  ] at hbad
  tauto

theorem fin15Anchored_clause18053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom2363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05145
  ] at hbad
  tauto

theorem fin15Anchored_clause18054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom2363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05145
  ] at hbad
  tauto

theorem fin15Anchored_clause18055 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom0607 Fin15AnchoredAtom0646
    Fin15AnchoredAtom0691 Fin15AnchoredAtom1362 Fin15AnchoredAtom2363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05145
  ] at hbad
  tauto

theorem fin15Anchored_clause18056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom2364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09241
  ] at hbad
  tauto

theorem fin15Anchored_clause18057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom2364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09241
  ] at hbad
  tauto

theorem fin15Anchored_clause18058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom2364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09241
  ] at hbad
  tauto

theorem fin15Anchored_clause18059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom2364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09241
  ] at hbad
  tauto

theorem fin15Anchored_clause18060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom2364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09241
  ] at hbad
  tauto

theorem fin15Anchored_clause18061 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom0608 Fin15AnchoredAtom0647
    Fin15AnchoredAtom0692 Fin15AnchoredAtom1363 Fin15AnchoredAtom2364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09241
  ] at hbad
  tauto

theorem fin15Anchored_clause18062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom2365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17433
  ] at hbad
  tauto

theorem fin15Anchored_clause18063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0609 Fin15AnchoredAtom2365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17433
  ] at hbad
  tauto

theorem fin15Anchored_clause18064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0648 Fin15AnchoredAtom2365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17433
  ] at hbad
  tauto

theorem fin15Anchored_clause18065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0693 Fin15AnchoredAtom2365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17433
  ] at hbad
  tauto

theorem fin15Anchored_clause18066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1364 Fin15AnchoredAtom2365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17433
  ] at hbad
  tauto

theorem fin15Anchored_clause18067 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom0609 Fin15AnchoredAtom0648
    Fin15AnchoredAtom0693 Fin15AnchoredAtom1364 Fin15AnchoredAtom2365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17433
  ] at hbad
  tauto

theorem fin15Anchored_clause18068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom0606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0606 Fin15AnchoredAtom2366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06169
  ] at hbad
  tauto

theorem fin15Anchored_clause18069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom2366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06169
  ] at hbad
  tauto

theorem fin15Anchored_clause18070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom0694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0694 Fin15AnchoredAtom2366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06169
  ] at hbad
  tauto

theorem fin15Anchored_clause18071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2366 chi ∧
      ¬Fin15AnchoredAtom1365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1365 Fin15AnchoredAtom2366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06169
  ] at hbad
  tauto

theorem fin15Anchored_clause18072 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2366 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom1365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0606 Fin15AnchoredAtom0607 Fin15AnchoredAtom0649
    Fin15AnchoredAtom0694 Fin15AnchoredAtom1365 Fin15AnchoredAtom2366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06169
  ] at hbad
  tauto

theorem fin15Anchored_clause18073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2367 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom2367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10265
  ] at hbad
  tauto

theorem fin15Anchored_clause18074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2368 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0609 Fin15AnchoredAtom2368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18457
  ] at hbad
  tauto

theorem fin15Anchored_clause18075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom2369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12313
  ] at hbad
  tauto

theorem fin15Anchored_clause18076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom2369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12313
  ] at hbad
  tauto

theorem fin15Anchored_clause18077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom2369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12313
  ] at hbad
  tauto

theorem fin15Anchored_clause18078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom2369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12313
  ] at hbad
  tauto

theorem fin15Anchored_clause18079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1368 Fin15AnchoredAtom2369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12313
  ] at hbad
  tauto

theorem fin15Anchored_clause18080 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom0608 Fin15AnchoredAtom0652
    Fin15AnchoredAtom0697 Fin15AnchoredAtom1368 Fin15AnchoredAtom2369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12313
  ] at hbad
  tauto

theorem fin15Anchored_clause18081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom2370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20505
  ] at hbad
  tauto

theorem fin15Anchored_clause18082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0609 Fin15AnchoredAtom2370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20505
  ] at hbad
  tauto

theorem fin15Anchored_clause18083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0653 Fin15AnchoredAtom2370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20505
  ] at hbad
  tauto

theorem fin15Anchored_clause18084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0698 Fin15AnchoredAtom2370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20505
  ] at hbad
  tauto

theorem fin15Anchored_clause18085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1369 Fin15AnchoredAtom2370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20505
  ] at hbad
  tauto

theorem fin15Anchored_clause18086 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom0609 Fin15AnchoredAtom0653
    Fin15AnchoredAtom0698 Fin15AnchoredAtom1369 Fin15AnchoredAtom2370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20505
  ] at hbad
  tauto

theorem fin15Anchored_clause18087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom2371 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24601
  ] at hbad
  tauto

theorem fin15Anchored_clause18088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0609 Fin15AnchoredAtom2371 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24601
  ] at hbad
  tauto

theorem fin15Anchored_clause18089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0654 Fin15AnchoredAtom2371 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24601
  ] at hbad
  tauto

theorem fin15Anchored_clause18090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0699 Fin15AnchoredAtom2371 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24601
  ] at hbad
  tauto

theorem fin15Anchored_clause18091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1370 Fin15AnchoredAtom2371 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24601
  ] at hbad
  tauto

theorem fin15Anchored_clause18092 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom0609 Fin15AnchoredAtom0654
    Fin15AnchoredAtom0699 Fin15AnchoredAtom1370 Fin15AnchoredAtom2371 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24601
  ] at hbad
  tauto

theorem fin15Anchored_clause18093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom2372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00233
  ] at hbad
  tauto

theorem fin15Anchored_clause18094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom2372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00233
  ] at hbad
  tauto

theorem fin15Anchored_clause18095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom2372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00233
  ] at hbad
  tauto

theorem fin15Anchored_clause18096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom2372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00233
  ] at hbad
  tauto

theorem fin15Anchored_clause18097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom2372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00233
  ] at hbad
  tauto

theorem fin15Anchored_clause18098 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom0611 Fin15AnchoredAtom0619
    Fin15AnchoredAtom0700 Fin15AnchoredAtom1371 Fin15AnchoredAtom2372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00233
  ] at hbad
  tauto

theorem fin15Anchored_clause18099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom2373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00361
  ] at hbad
  tauto

theorem fin15Anchored_clause18100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom2373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00361
  ] at hbad
  tauto

theorem fin15Anchored_clause18101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom2373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00361
  ] at hbad
  tauto

theorem fin15Anchored_clause18102 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom2373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00361
  ] at hbad
  tauto

theorem fin15Anchored_clause18103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2373 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom2373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00361
  ] at hbad
  tauto

theorem fin15Anchored_clause18104 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2373 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom0612 Fin15AnchoredAtom0620
    Fin15AnchoredAtom0701 Fin15AnchoredAtom1372 Fin15AnchoredAtom2373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00361
  ] at hbad
  tauto

theorem fin15Anchored_clause18105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom2374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00617
  ] at hbad
  tauto

theorem fin15Anchored_clause18106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom2374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00617
  ] at hbad
  tauto

theorem fin15Anchored_clause18107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom2374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00617
  ] at hbad
  tauto

theorem fin15Anchored_clause18108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom2374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00617
  ] at hbad
  tauto

theorem fin15Anchored_clause18109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom2374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00617
  ] at hbad
  tauto

theorem fin15Anchored_clause18110 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom0613 Fin15AnchoredAtom0621
    Fin15AnchoredAtom0702 Fin15AnchoredAtom1373 Fin15AnchoredAtom2374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00617
  ] at hbad
  tauto

theorem fin15Anchored_clause18111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom2375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01129
  ] at hbad
  tauto

theorem fin15Anchored_clause18112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom2375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01129
  ] at hbad
  tauto

theorem fin15Anchored_clause18113 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom2375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01129
  ] at hbad
  tauto

theorem fin15Anchored_clause18114 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom2375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01129
  ] at hbad
  tauto

theorem fin15Anchored_clause18115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom2375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01129
  ] at hbad
  tauto

theorem fin15Anchored_clause18116 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom0614 Fin15AnchoredAtom0622
    Fin15AnchoredAtom0703 Fin15AnchoredAtom1374 Fin15AnchoredAtom2375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01129
  ] at hbad
  tauto

theorem fin15Anchored_clause18117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2376 chi ∧
      ¬Fin15AnchoredAtom0704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0704 Fin15AnchoredAtom2376 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02153
  ] at hbad
  tauto

theorem fin15Anchored_clause18118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2376 chi ∧
      ¬Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1375 Fin15AnchoredAtom2376 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02153
  ] at hbad
  tauto

theorem fin15Anchored_clause18119 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2376 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom0615 Fin15AnchoredAtom0623
    Fin15AnchoredAtom0704 Fin15AnchoredAtom1375 Fin15AnchoredAtom2376 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02153
  ] at hbad
  tauto

theorem fin15Anchored_clause18120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom2377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04201
  ] at hbad
  tauto

theorem fin15Anchored_clause18121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom2377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04201
  ] at hbad
  tauto

theorem fin15Anchored_clause18122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom2377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04201
  ] at hbad
  tauto

theorem fin15Anchored_clause18123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom2377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04201
  ] at hbad
  tauto

theorem fin15Anchored_clause18124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom2377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04201
  ] at hbad
  tauto

theorem fin15Anchored_clause18125 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom0616 Fin15AnchoredAtom0624
    Fin15AnchoredAtom0705 Fin15AnchoredAtom1376 Fin15AnchoredAtom2377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04201
  ] at hbad
  tauto

theorem fin15Anchored_clause18126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom2378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08297
  ] at hbad
  tauto

theorem fin15Anchored_clause18127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom2378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08297
  ] at hbad
  tauto

theorem fin15Anchored_clause18128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom2378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08297
  ] at hbad
  tauto

theorem fin15Anchored_clause18129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0706 Fin15AnchoredAtom2378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08297
  ] at hbad
  tauto

theorem fin15Anchored_clause18130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1377 Fin15AnchoredAtom2378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08297
  ] at hbad
  tauto

theorem fin15Anchored_clause18131 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom0617 Fin15AnchoredAtom0625
    Fin15AnchoredAtom0706 Fin15AnchoredAtom1377 Fin15AnchoredAtom2378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08297
  ] at hbad
  tauto

theorem fin15Anchored_clause18132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom2379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16489
  ] at hbad
  tauto

theorem fin15Anchored_clause18133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0618 Fin15AnchoredAtom2379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16489
  ] at hbad
  tauto

theorem fin15Anchored_clause18134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0626 Fin15AnchoredAtom2379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16489
  ] at hbad
  tauto

theorem fin15Anchored_clause18135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0707 Fin15AnchoredAtom2379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16489
  ] at hbad
  tauto

theorem fin15Anchored_clause18136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1378 Fin15AnchoredAtom2379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16489
  ] at hbad
  tauto

theorem fin15Anchored_clause18137 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom0618 Fin15AnchoredAtom0626
    Fin15AnchoredAtom0707 Fin15AnchoredAtom1378 Fin15AnchoredAtom2379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16489
  ] at hbad
  tauto

theorem fin15Anchored_clause18138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom2380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00425
  ] at hbad
  tauto

theorem fin15Anchored_clause18139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom2380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00425
  ] at hbad
  tauto

theorem fin15Anchored_clause18140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom2380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00425
  ] at hbad
  tauto

theorem fin15Anchored_clause18141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom2380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00425
  ] at hbad
  tauto

theorem fin15Anchored_clause18142 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2380 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom2380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00425
  ] at hbad
  tauto

theorem fin15Anchored_clause18143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom0612 Fin15AnchoredAtom0627
    Fin15AnchoredAtom0708 Fin15AnchoredAtom1379 Fin15AnchoredAtom2380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00425
  ] at hbad
  tauto

theorem fin15Anchored_clause18144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom2381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00681
  ] at hbad
  tauto

theorem fin15Anchored_clause18145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom2381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00681
  ] at hbad
  tauto

theorem fin15Anchored_clause18146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom2381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00681
  ] at hbad
  tauto

theorem fin15Anchored_clause18147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom2381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00681
  ] at hbad
  tauto

theorem fin15Anchored_clause18148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom2381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00681
  ] at hbad
  tauto

theorem fin15Anchored_clause18149 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom0613 Fin15AnchoredAtom0628
    Fin15AnchoredAtom0709 Fin15AnchoredAtom1380 Fin15AnchoredAtom2381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00681
  ] at hbad
  tauto

theorem fin15Anchored_clause18150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom2382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01193
  ] at hbad
  tauto

theorem fin15Anchored_clause18151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom2382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01193
  ] at hbad
  tauto

theorem fin15Anchored_clause18152 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom2382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01193
  ] at hbad
  tauto

theorem fin15Anchored_clause18153 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom2382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01193
  ] at hbad
  tauto

theorem fin15Anchored_clause18154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom2382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01193
  ] at hbad
  tauto

theorem fin15Anchored_clause18155 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom0614 Fin15AnchoredAtom0629
    Fin15AnchoredAtom0710 Fin15AnchoredAtom1381 Fin15AnchoredAtom2382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01193
  ] at hbad
  tauto

theorem fin15Anchored_clause18156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom2383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02217
  ] at hbad
  tauto

theorem fin15Anchored_clause18157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom0615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0615 Fin15AnchoredAtom2383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02217
  ] at hbad
  tauto

theorem fin15Anchored_clause18158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom0630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0630 Fin15AnchoredAtom2383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02217
  ] at hbad
  tauto

theorem fin15Anchored_clause18159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom0711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0711 Fin15AnchoredAtom2383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02217
  ] at hbad
  tauto

theorem fin15Anchored_clause18160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2383 chi ∧
      ¬Fin15AnchoredAtom1382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1382 Fin15AnchoredAtom2383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02217
  ] at hbad
  tauto

theorem fin15Anchored_clause18161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom2384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04265
  ] at hbad
  tauto

theorem fin15Anchored_clause18162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom2384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04265
  ] at hbad
  tauto

theorem fin15Anchored_clause18163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom2384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04265
  ] at hbad
  tauto

theorem fin15Anchored_clause18164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom2384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04265
  ] at hbad
  tauto

theorem fin15Anchored_clause18165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom2384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04265
  ] at hbad
  tauto

theorem fin15Anchored_clause18166 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom0616 Fin15AnchoredAtom0631
    Fin15AnchoredAtom0712 Fin15AnchoredAtom1383 Fin15AnchoredAtom2384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04265
  ] at hbad
  tauto

theorem fin15Anchored_clause18167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom2385 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08361
  ] at hbad
  tauto

theorem fin15Anchored_clause18168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom2385 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08361
  ] at hbad
  tauto

theorem fin15Anchored_clause18169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom2385 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08361
  ] at hbad
  tauto

theorem fin15Anchored_clause18170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom2385 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08361
  ] at hbad
  tauto

theorem fin15Anchored_clause18171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom2385 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08361
  ] at hbad
  tauto

theorem fin15Anchored_clause18172 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom0617 Fin15AnchoredAtom0632
    Fin15AnchoredAtom0713 Fin15AnchoredAtom1384 Fin15AnchoredAtom2385 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08361
  ] at hbad
  tauto

theorem fin15Anchored_clause18173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom2386 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16553
  ] at hbad
  tauto

theorem fin15Anchored_clause18174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0618 Fin15AnchoredAtom2386 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16553
  ] at hbad
  tauto

theorem fin15Anchored_clause18175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0633 Fin15AnchoredAtom2386 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16553
  ] at hbad
  tauto

end ErdosSzekeres

end
