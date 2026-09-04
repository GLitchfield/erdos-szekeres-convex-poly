module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 128. -/

theorem fin15Anchored_clause16384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom2010 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04643
  ] at hbad
  tauto

theorem fin15Anchored_clause16385 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom0495 Fin15AnchoredAtom0521
    Fin15AnchoredAtom0723 Fin15AnchoredAtom1009 Fin15AnchoredAtom2010 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04643
  ] at hbad
  tauto

theorem fin15Anchored_clause16386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom2011 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08739
  ] at hbad
  tauto

theorem fin15Anchored_clause16387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0496 Fin15AnchoredAtom2011 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08739
  ] at hbad
  tauto

theorem fin15Anchored_clause16388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0522 Fin15AnchoredAtom2011 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08739
  ] at hbad
  tauto

theorem fin15Anchored_clause16389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0724 Fin15AnchoredAtom2011 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08739
  ] at hbad
  tauto

theorem fin15Anchored_clause16390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom2011 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08739
  ] at hbad
  tauto

theorem fin15Anchored_clause16391 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom0496 Fin15AnchoredAtom0522
    Fin15AnchoredAtom0724 Fin15AnchoredAtom1010 Fin15AnchoredAtom2011 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08739
  ] at hbad
  tauto

theorem fin15Anchored_clause16392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom2012 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16931
  ] at hbad
  tauto

theorem fin15Anchored_clause16393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0497 Fin15AnchoredAtom2012 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16931
  ] at hbad
  tauto

theorem fin15Anchored_clause16394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0523 Fin15AnchoredAtom2012 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16931
  ] at hbad
  tauto

theorem fin15Anchored_clause16395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0725 Fin15AnchoredAtom2012 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16931
  ] at hbad
  tauto

theorem fin15Anchored_clause16396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1011 Fin15AnchoredAtom2012 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16931
  ] at hbad
  tauto

theorem fin15Anchored_clause16397 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom0497 Fin15AnchoredAtom0523
    Fin15AnchoredAtom0725 Fin15AnchoredAtom1011 Fin15AnchoredAtom2012 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16931
  ] at hbad
  tauto

theorem fin15Anchored_clause16398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom2013 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03107
  ] at hbad
  tauto

theorem fin15Anchored_clause16399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom0494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0494 Fin15AnchoredAtom2013 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03107
  ] at hbad
  tauto

theorem fin15Anchored_clause16400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom0726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0726 Fin15AnchoredAtom2013 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03107
  ] at hbad
  tauto

theorem fin15Anchored_clause16401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2013 chi ∧
      ¬Fin15AnchoredAtom1012 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1012 Fin15AnchoredAtom2013 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03107
  ] at hbad
  tauto

theorem fin15Anchored_clause16402 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2013 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0494 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom1012 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom0494 Fin15AnchoredAtom0524
    Fin15AnchoredAtom0726 Fin15AnchoredAtom1012 Fin15AnchoredAtom2013 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03107
  ] at hbad
  tauto

theorem fin15Anchored_clause16403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom2014 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05155
  ] at hbad
  tauto

theorem fin15Anchored_clause16404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom2014 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05155
  ] at hbad
  tauto

theorem fin15Anchored_clause16405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom2014 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05155
  ] at hbad
  tauto

theorem fin15Anchored_clause16406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom2014 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05155
  ] at hbad
  tauto

theorem fin15Anchored_clause16407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom2014 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05155
  ] at hbad
  tauto

theorem fin15Anchored_clause16408 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom0495 Fin15AnchoredAtom0525
    Fin15AnchoredAtom0727 Fin15AnchoredAtom1013 Fin15AnchoredAtom2014 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05155
  ] at hbad
  tauto

theorem fin15Anchored_clause16409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom2015 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09251
  ] at hbad
  tauto

theorem fin15Anchored_clause16410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0496 Fin15AnchoredAtom2015 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09251
  ] at hbad
  tauto

theorem fin15Anchored_clause16411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom2015 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09251
  ] at hbad
  tauto

theorem fin15Anchored_clause16412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom2015 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09251
  ] at hbad
  tauto

theorem fin15Anchored_clause16413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1014 Fin15AnchoredAtom2015 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09251
  ] at hbad
  tauto

theorem fin15Anchored_clause16414 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom0496 Fin15AnchoredAtom0526
    Fin15AnchoredAtom0728 Fin15AnchoredAtom1014 Fin15AnchoredAtom2015 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09251
  ] at hbad
  tauto

theorem fin15Anchored_clause16415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom2016 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17443
  ] at hbad
  tauto

theorem fin15Anchored_clause16416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0497 Fin15AnchoredAtom2016 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17443
  ] at hbad
  tauto

theorem fin15Anchored_clause16417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0527 Fin15AnchoredAtom2016 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17443
  ] at hbad
  tauto

theorem fin15Anchored_clause16418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0729 Fin15AnchoredAtom2016 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17443
  ] at hbad
  tauto

theorem fin15Anchored_clause16419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1015 Fin15AnchoredAtom2016 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17443
  ] at hbad
  tauto

theorem fin15Anchored_clause16420 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom0497 Fin15AnchoredAtom0527
    Fin15AnchoredAtom0729 Fin15AnchoredAtom1015 Fin15AnchoredAtom2016 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17443
  ] at hbad
  tauto

theorem fin15Anchored_clause16421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2017 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom2017 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06179
  ] at hbad
  tauto

theorem fin15Anchored_clause16422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2017 chi ∧
      ¬Fin15AnchoredAtom0528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0528 Fin15AnchoredAtom2017 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06179
  ] at hbad
  tauto

theorem fin15Anchored_clause16423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2018 chi ∧
      ¬Fin15AnchoredAtom1017 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1017 Fin15AnchoredAtom2018 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10275
  ] at hbad
  tauto

theorem fin15Anchored_clause16424 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2018 chi ∧
      Fin15AnchoredAtom0494 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom1017 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0494 Fin15AnchoredAtom0496 Fin15AnchoredAtom0529
    Fin15AnchoredAtom0731 Fin15AnchoredAtom1017 Fin15AnchoredAtom2018 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10275
  ] at hbad
  tauto

theorem fin15Anchored_clause16425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2019 chi ∧
      ¬Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0497 Fin15AnchoredAtom2019 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18467
  ] at hbad
  tauto

theorem fin15Anchored_clause16426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom2020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12323
  ] at hbad
  tauto

theorem fin15Anchored_clause16427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0496 Fin15AnchoredAtom2020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12323
  ] at hbad
  tauto

theorem fin15Anchored_clause16428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0531 Fin15AnchoredAtom2020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12323
  ] at hbad
  tauto

theorem fin15Anchored_clause16429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom2020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12323
  ] at hbad
  tauto

theorem fin15Anchored_clause16430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom2020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12323
  ] at hbad
  tauto

theorem fin15Anchored_clause16431 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom0496 Fin15AnchoredAtom0531
    Fin15AnchoredAtom0733 Fin15AnchoredAtom1019 Fin15AnchoredAtom2020 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12323
  ] at hbad
  tauto

theorem fin15Anchored_clause16432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom2021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20515
  ] at hbad
  tauto

theorem fin15Anchored_clause16433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0497 Fin15AnchoredAtom2021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20515
  ] at hbad
  tauto

theorem fin15Anchored_clause16434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0532 Fin15AnchoredAtom2021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20515
  ] at hbad
  tauto

theorem fin15Anchored_clause16435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0734 Fin15AnchoredAtom2021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20515
  ] at hbad
  tauto

theorem fin15Anchored_clause16436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1020 Fin15AnchoredAtom2021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20515
  ] at hbad
  tauto

theorem fin15Anchored_clause16437 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom0497 Fin15AnchoredAtom0532
    Fin15AnchoredAtom0734 Fin15AnchoredAtom1020 Fin15AnchoredAtom2021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20515
  ] at hbad
  tauto

theorem fin15Anchored_clause16438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0496 Fin15AnchoredAtom2022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24611
  ] at hbad
  tauto

theorem fin15Anchored_clause16439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0497 Fin15AnchoredAtom2022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24611
  ] at hbad
  tauto

theorem fin15Anchored_clause16440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0533 Fin15AnchoredAtom2022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24611
  ] at hbad
  tauto

theorem fin15Anchored_clause16441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0735 Fin15AnchoredAtom2022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24611
  ] at hbad
  tauto

theorem fin15Anchored_clause16442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1021 Fin15AnchoredAtom2022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24611
  ] at hbad
  tauto

theorem fin15Anchored_clause16443 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0496 Fin15AnchoredAtom0497 Fin15AnchoredAtom0533
    Fin15AnchoredAtom0735 Fin15AnchoredAtom1021 Fin15AnchoredAtom2022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24611
  ] at hbad
  tauto

theorem fin15Anchored_clause16444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom2023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00451
  ] at hbad
  tauto

theorem fin15Anchored_clause16445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom0736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom2023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00451
  ] at hbad
  tauto

theorem fin15Anchored_clause16446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2023 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom2023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00451
  ] at hbad
  tauto

theorem fin15Anchored_clause16447 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2023 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom0499 Fin15AnchoredAtom0506
    Fin15AnchoredAtom0736 Fin15AnchoredAtom1022 Fin15AnchoredAtom2023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00451
  ] at hbad
  tauto

theorem fin15Anchored_clause16448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom2024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00707
  ] at hbad
  tauto

theorem fin15Anchored_clause16449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom2024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00707
  ] at hbad
  tauto

theorem fin15Anchored_clause16450 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom2024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00707
  ] at hbad
  tauto

theorem fin15Anchored_clause16451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom2024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00707
  ] at hbad
  tauto

theorem fin15Anchored_clause16452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom2024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00707
  ] at hbad
  tauto

theorem fin15Anchored_clause16453 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom0500 Fin15AnchoredAtom0507
    Fin15AnchoredAtom0737 Fin15AnchoredAtom1023 Fin15AnchoredAtom2024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00707
  ] at hbad
  tauto

theorem fin15Anchored_clause16454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom2025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01219
  ] at hbad
  tauto

theorem fin15Anchored_clause16455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom2025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01219
  ] at hbad
  tauto

theorem fin15Anchored_clause16456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom2025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01219
  ] at hbad
  tauto

theorem fin15Anchored_clause16457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom2025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01219
  ] at hbad
  tauto

theorem fin15Anchored_clause16458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom2025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01219
  ] at hbad
  tauto

theorem fin15Anchored_clause16459 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom0501 Fin15AnchoredAtom0508
    Fin15AnchoredAtom0738 Fin15AnchoredAtom1024 Fin15AnchoredAtom2025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01219
  ] at hbad
  tauto

theorem fin15Anchored_clause16460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2026 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom2026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02243
  ] at hbad
  tauto

theorem fin15Anchored_clause16461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2026 chi ∧
      ¬Fin15AnchoredAtom0739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom2026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02243
  ] at hbad
  tauto

theorem fin15Anchored_clause16462 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom2027 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04291
  ] at hbad
  tauto

theorem fin15Anchored_clause16463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom2027 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04291
  ] at hbad
  tauto

theorem fin15Anchored_clause16464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom2027 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04291
  ] at hbad
  tauto

theorem fin15Anchored_clause16465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom2027 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04291
  ] at hbad
  tauto

theorem fin15Anchored_clause16466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom2027 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04291
  ] at hbad
  tauto

theorem fin15Anchored_clause16467 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom0503 Fin15AnchoredAtom0510
    Fin15AnchoredAtom0740 Fin15AnchoredAtom1026 Fin15AnchoredAtom2027 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04291
  ] at hbad
  tauto

theorem fin15Anchored_clause16468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom2028 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08387
  ] at hbad
  tauto

theorem fin15Anchored_clause16469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom2028 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08387
  ] at hbad
  tauto

theorem fin15Anchored_clause16470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom2028 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08387
  ] at hbad
  tauto

theorem fin15Anchored_clause16471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom2028 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08387
  ] at hbad
  tauto

theorem fin15Anchored_clause16472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1027 Fin15AnchoredAtom2028 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08387
  ] at hbad
  tauto

theorem fin15Anchored_clause16473 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom0504 Fin15AnchoredAtom0511
    Fin15AnchoredAtom0741 Fin15AnchoredAtom1027 Fin15AnchoredAtom2028 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08387
  ] at hbad
  tauto

theorem fin15Anchored_clause16474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom2029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16579
  ] at hbad
  tauto

theorem fin15Anchored_clause16475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0505 Fin15AnchoredAtom2029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16579
  ] at hbad
  tauto

theorem fin15Anchored_clause16476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0512 Fin15AnchoredAtom2029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16579
  ] at hbad
  tauto

theorem fin15Anchored_clause16477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0742 Fin15AnchoredAtom2029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16579
  ] at hbad
  tauto

theorem fin15Anchored_clause16478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1028 Fin15AnchoredAtom2029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16579
  ] at hbad
  tauto

theorem fin15Anchored_clause16479 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom0505 Fin15AnchoredAtom0512
    Fin15AnchoredAtom0742 Fin15AnchoredAtom1028 Fin15AnchoredAtom2029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16579
  ] at hbad
  tauto

theorem fin15Anchored_clause16480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom0499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom2030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00835
  ] at hbad
  tauto

theorem fin15Anchored_clause16481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom2030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00835
  ] at hbad
  tauto

theorem fin15Anchored_clause16482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom0513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom2030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00835
  ] at hbad
  tauto

theorem fin15Anchored_clause16483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom0743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom2030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00835
  ] at hbad
  tauto

theorem fin15Anchored_clause16484 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2030 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1029 Fin15AnchoredAtom2030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00835
  ] at hbad
  tauto

theorem fin15Anchored_clause16485 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom0500 Fin15AnchoredAtom0513
    Fin15AnchoredAtom0743 Fin15AnchoredAtom1029 Fin15AnchoredAtom2030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00835
  ] at hbad
  tauto

theorem fin15Anchored_clause16486 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom0499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom2031 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01347
  ] at hbad
  tauto

theorem fin15Anchored_clause16487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom2031 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01347
  ] at hbad
  tauto

theorem fin15Anchored_clause16488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2031 chi ∧
      ¬Fin15AnchoredAtom0744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom2031 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01347
  ] at hbad
  tauto

theorem fin15Anchored_clause16489 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom0501 Fin15AnchoredAtom0514
    Fin15AnchoredAtom0744 Fin15AnchoredAtom1030 Fin15AnchoredAtom2031 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01347
  ] at hbad
  tauto

theorem fin15Anchored_clause16490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom0499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom2033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04419
  ] at hbad
  tauto

theorem fin15Anchored_clause16491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom2033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04419
  ] at hbad
  tauto

theorem fin15Anchored_clause16492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom0516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0516 Fin15AnchoredAtom2033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04419
  ] at hbad
  tauto

theorem fin15Anchored_clause16493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom0746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0746 Fin15AnchoredAtom2033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04419
  ] at hbad
  tauto

theorem fin15Anchored_clause16494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2033 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1032 Fin15AnchoredAtom2033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04419
  ] at hbad
  tauto

theorem fin15Anchored_clause16495 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2033 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom0503 Fin15AnchoredAtom0516
    Fin15AnchoredAtom0746 Fin15AnchoredAtom1032 Fin15AnchoredAtom2033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04419
  ] at hbad
  tauto

theorem fin15Anchored_clause16496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom0499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom2034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08515
  ] at hbad
  tauto

theorem fin15Anchored_clause16497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom2034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08515
  ] at hbad
  tauto

theorem fin15Anchored_clause16498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom0517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0517 Fin15AnchoredAtom2034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08515
  ] at hbad
  tauto

theorem fin15Anchored_clause16499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom0747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0747 Fin15AnchoredAtom2034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08515
  ] at hbad
  tauto

theorem fin15Anchored_clause16500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2034 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1033 Fin15AnchoredAtom2034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08515
  ] at hbad
  tauto

theorem fin15Anchored_clause16501 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2034 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom0504 Fin15AnchoredAtom0517
    Fin15AnchoredAtom0747 Fin15AnchoredAtom1033 Fin15AnchoredAtom2034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08515
  ] at hbad
  tauto

theorem fin15Anchored_clause16502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom0499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom2035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16707
  ] at hbad
  tauto

theorem fin15Anchored_clause16503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0505 Fin15AnchoredAtom2035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16707
  ] at hbad
  tauto

theorem fin15Anchored_clause16504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom0518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0518 Fin15AnchoredAtom2035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16707
  ] at hbad
  tauto

theorem fin15Anchored_clause16505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom0748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0748 Fin15AnchoredAtom2035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16707
  ] at hbad
  tauto

theorem fin15Anchored_clause16506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2035 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1034 Fin15AnchoredAtom2035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16707
  ] at hbad
  tauto

theorem fin15Anchored_clause16507 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2035 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom0505 Fin15AnchoredAtom0518
    Fin15AnchoredAtom0748 Fin15AnchoredAtom1034 Fin15AnchoredAtom2035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16707
  ] at hbad
  tauto

theorem fin15Anchored_clause16508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom2036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01603
  ] at hbad
  tauto

theorem fin15Anchored_clause16509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom2036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01603
  ] at hbad
  tauto

theorem fin15Anchored_clause16510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom2036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01603
  ] at hbad
  tauto

theorem fin15Anchored_clause16511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom2036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01603
  ] at hbad
  tauto

end ErdosSzekeres

end
