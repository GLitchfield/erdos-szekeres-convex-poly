module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 138. -/

theorem fin15Anchored_clause17664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom2277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01669
  ] at hbad
  tauto

theorem fin15Anchored_clause17665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom2277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01669
  ] at hbad
  tauto

theorem fin15Anchored_clause17666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom2277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01669
  ] at hbad
  tauto

theorem fin15Anchored_clause17667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom2277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01669
  ] at hbad
  tauto

theorem fin15Anchored_clause17668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom2277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01669
  ] at hbad
  tauto

theorem fin15Anchored_clause17669 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom0574 Fin15AnchoredAtom0585
    Fin15AnchoredAtom0770 Fin15AnchoredAtom1276 Fin15AnchoredAtom2277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01669
  ] at hbad
  tauto

theorem fin15Anchored_clause17670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom2278 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02693
  ] at hbad
  tauto

theorem fin15Anchored_clause17671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom0575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0575 Fin15AnchoredAtom2278 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02693
  ] at hbad
  tauto

theorem fin15Anchored_clause17672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom0586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0586 Fin15AnchoredAtom2278 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02693
  ] at hbad
  tauto

theorem fin15Anchored_clause17673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom0771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0771 Fin15AnchoredAtom2278 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02693
  ] at hbad
  tauto

theorem fin15Anchored_clause17674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1277 Fin15AnchoredAtom2278 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02693
  ] at hbad
  tauto

theorem fin15Anchored_clause17675 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2278 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom0575 Fin15AnchoredAtom0586
    Fin15AnchoredAtom0771 Fin15AnchoredAtom1277 Fin15AnchoredAtom2278 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02693
  ] at hbad
  tauto

theorem fin15Anchored_clause17676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom2279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04741
  ] at hbad
  tauto

theorem fin15Anchored_clause17677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom2279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04741
  ] at hbad
  tauto

theorem fin15Anchored_clause17678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom2279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04741
  ] at hbad
  tauto

theorem fin15Anchored_clause17679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom2279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04741
  ] at hbad
  tauto

theorem fin15Anchored_clause17680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom2279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04741
  ] at hbad
  tauto

theorem fin15Anchored_clause17681 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom0576 Fin15AnchoredAtom0587
    Fin15AnchoredAtom0772 Fin15AnchoredAtom1278 Fin15AnchoredAtom2279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04741
  ] at hbad
  tauto

theorem fin15Anchored_clause17682 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom2280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08837
  ] at hbad
  tauto

theorem fin15Anchored_clause17683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom2280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08837
  ] at hbad
  tauto

theorem fin15Anchored_clause17684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0588 Fin15AnchoredAtom2280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08837
  ] at hbad
  tauto

theorem fin15Anchored_clause17685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0773 Fin15AnchoredAtom2280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08837
  ] at hbad
  tauto

theorem fin15Anchored_clause17686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1279 Fin15AnchoredAtom2280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08837
  ] at hbad
  tauto

theorem fin15Anchored_clause17687 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom0577 Fin15AnchoredAtom0588
    Fin15AnchoredAtom0773 Fin15AnchoredAtom1279 Fin15AnchoredAtom2280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08837
  ] at hbad
  tauto

theorem fin15Anchored_clause17688 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom2281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17029
  ] at hbad
  tauto

theorem fin15Anchored_clause17689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0578 Fin15AnchoredAtom2281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17029
  ] at hbad
  tauto

theorem fin15Anchored_clause17690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0589 Fin15AnchoredAtom2281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17029
  ] at hbad
  tauto

theorem fin15Anchored_clause17691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0774 Fin15AnchoredAtom2281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17029
  ] at hbad
  tauto

theorem fin15Anchored_clause17692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1280 Fin15AnchoredAtom2281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17029
  ] at hbad
  tauto

theorem fin15Anchored_clause17693 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom0578 Fin15AnchoredAtom0589
    Fin15AnchoredAtom0774 Fin15AnchoredAtom1280 Fin15AnchoredAtom2281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17029
  ] at hbad
  tauto

theorem fin15Anchored_clause17694 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2282 chi ∧
      ¬Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom2282 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03205
  ] at hbad
  tauto

theorem fin15Anchored_clause17695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2282 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1281 Fin15AnchoredAtom2282 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03205
  ] at hbad
  tauto

theorem fin15Anchored_clause17696 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2282 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom0575 Fin15AnchoredAtom0590
    Fin15AnchoredAtom0775 Fin15AnchoredAtom1281 Fin15AnchoredAtom2282 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03205
  ] at hbad
  tauto

theorem fin15Anchored_clause17697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom2283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05253
  ] at hbad
  tauto

theorem fin15Anchored_clause17698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom2283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05253
  ] at hbad
  tauto

theorem fin15Anchored_clause17699 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom2283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05253
  ] at hbad
  tauto

theorem fin15Anchored_clause17700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom2283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05253
  ] at hbad
  tauto

theorem fin15Anchored_clause17701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom2283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05253
  ] at hbad
  tauto

theorem fin15Anchored_clause17702 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom0576 Fin15AnchoredAtom0591
    Fin15AnchoredAtom0776 Fin15AnchoredAtom1282 Fin15AnchoredAtom2283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05253
  ] at hbad
  tauto

theorem fin15Anchored_clause17703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom2284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09349
  ] at hbad
  tauto

theorem fin15Anchored_clause17704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom2284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09349
  ] at hbad
  tauto

theorem fin15Anchored_clause17705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0592 Fin15AnchoredAtom2284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09349
  ] at hbad
  tauto

theorem fin15Anchored_clause17706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom2284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09349
  ] at hbad
  tauto

theorem fin15Anchored_clause17707 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1283 Fin15AnchoredAtom2284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09349
  ] at hbad
  tauto

theorem fin15Anchored_clause17708 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom0577 Fin15AnchoredAtom0592
    Fin15AnchoredAtom0777 Fin15AnchoredAtom1283 Fin15AnchoredAtom2284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09349
  ] at hbad
  tauto

theorem fin15Anchored_clause17709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom2285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17541
  ] at hbad
  tauto

theorem fin15Anchored_clause17710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0578 Fin15AnchoredAtom2285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17541
  ] at hbad
  tauto

theorem fin15Anchored_clause17711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0593 Fin15AnchoredAtom2285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17541
  ] at hbad
  tauto

theorem fin15Anchored_clause17712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0778 Fin15AnchoredAtom2285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17541
  ] at hbad
  tauto

theorem fin15Anchored_clause17713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1284 Fin15AnchoredAtom2285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17541
  ] at hbad
  tauto

theorem fin15Anchored_clause17714 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom0578 Fin15AnchoredAtom0593
    Fin15AnchoredAtom0778 Fin15AnchoredAtom1284 Fin15AnchoredAtom2285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17541
  ] at hbad
  tauto

theorem fin15Anchored_clause17715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2286 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom2286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06277
  ] at hbad
  tauto

theorem fin15Anchored_clause17716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2286 chi ∧
      ¬Fin15AnchoredAtom0594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0594 Fin15AnchoredAtom2286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06277
  ] at hbad
  tauto

theorem fin15Anchored_clause17717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2286 chi ∧
      ¬Fin15AnchoredAtom0779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0779 Fin15AnchoredAtom2286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06277
  ] at hbad
  tauto

theorem fin15Anchored_clause17718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2286 chi ∧
      ¬Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1285 Fin15AnchoredAtom2286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06277
  ] at hbad
  tauto

theorem fin15Anchored_clause17719 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2286 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0575 Fin15AnchoredAtom0576 Fin15AnchoredAtom0594
    Fin15AnchoredAtom0779 Fin15AnchoredAtom1285 Fin15AnchoredAtom2286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06277
  ] at hbad
  tauto

theorem fin15Anchored_clause17720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2287 chi ∧
      ¬Fin15AnchoredAtom0575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0575 Fin15AnchoredAtom2287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10373
  ] at hbad
  tauto

theorem fin15Anchored_clause17721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2287 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom2287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10373
  ] at hbad
  tauto

theorem fin15Anchored_clause17722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2287 chi ∧
      ¬Fin15AnchoredAtom0780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0780 Fin15AnchoredAtom2287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10373
  ] at hbad
  tauto

theorem fin15Anchored_clause17723 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2287 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom1286 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0575 Fin15AnchoredAtom0577 Fin15AnchoredAtom0595
    Fin15AnchoredAtom0780 Fin15AnchoredAtom1286 Fin15AnchoredAtom2287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10373
  ] at hbad
  tauto

theorem fin15Anchored_clause17724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2288 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0578 Fin15AnchoredAtom2288 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18565
  ] at hbad
  tauto

theorem fin15Anchored_clause17725 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2288 chi ∧
      ¬Fin15AnchoredAtom0781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0781 Fin15AnchoredAtom2288 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18565
  ] at hbad
  tauto

theorem fin15Anchored_clause17726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2288 chi ∧
      ¬Fin15AnchoredAtom1287 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1287 Fin15AnchoredAtom2288 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18565
  ] at hbad
  tauto

theorem fin15Anchored_clause17727 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2288 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom1287 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0575 Fin15AnchoredAtom0578 Fin15AnchoredAtom0596
    Fin15AnchoredAtom0781 Fin15AnchoredAtom1287 Fin15AnchoredAtom2288 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18565
  ] at hbad
  tauto

theorem fin15Anchored_clause17728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom2289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12421
  ] at hbad
  tauto

theorem fin15Anchored_clause17729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom2289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12421
  ] at hbad
  tauto

theorem fin15Anchored_clause17730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0597 Fin15AnchoredAtom2289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12421
  ] at hbad
  tauto

theorem fin15Anchored_clause17731 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom2289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12421
  ] at hbad
  tauto

theorem fin15Anchored_clause17732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1288 Fin15AnchoredAtom2289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12421
  ] at hbad
  tauto

theorem fin15Anchored_clause17733 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom0577 Fin15AnchoredAtom0597
    Fin15AnchoredAtom0782 Fin15AnchoredAtom1288 Fin15AnchoredAtom2289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12421
  ] at hbad
  tauto

theorem fin15Anchored_clause17734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom2290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20613
  ] at hbad
  tauto

theorem fin15Anchored_clause17735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0578 Fin15AnchoredAtom2290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20613
  ] at hbad
  tauto

theorem fin15Anchored_clause17736 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0598 Fin15AnchoredAtom2290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20613
  ] at hbad
  tauto

theorem fin15Anchored_clause17737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0783 Fin15AnchoredAtom2290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20613
  ] at hbad
  tauto

theorem fin15Anchored_clause17738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1289 Fin15AnchoredAtom2290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20613
  ] at hbad
  tauto

theorem fin15Anchored_clause17739 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom0578 Fin15AnchoredAtom0598
    Fin15AnchoredAtom0783 Fin15AnchoredAtom1289 Fin15AnchoredAtom2290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20613
  ] at hbad
  tauto

theorem fin15Anchored_clause17740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom2291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24709
  ] at hbad
  tauto

theorem fin15Anchored_clause17741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0578 Fin15AnchoredAtom2291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24709
  ] at hbad
  tauto

theorem fin15Anchored_clause17742 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0599 Fin15AnchoredAtom2291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24709
  ] at hbad
  tauto

theorem fin15Anchored_clause17743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0784 Fin15AnchoredAtom2291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24709
  ] at hbad
  tauto

theorem fin15Anchored_clause17744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1290 Fin15AnchoredAtom2291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24709
  ] at hbad
  tauto

theorem fin15Anchored_clause17745 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom0578 Fin15AnchoredAtom0599
    Fin15AnchoredAtom0784 Fin15AnchoredAtom1290 Fin15AnchoredAtom2291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24709
  ] at hbad
  tauto

theorem fin15Anchored_clause17746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2292 chi ∧
      ¬Fin15AnchoredAtom0580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0580 Fin15AnchoredAtom2292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01797
  ] at hbad
  tauto

theorem fin15Anchored_clause17747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2292 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom2292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01797
  ] at hbad
  tauto

theorem fin15Anchored_clause17748 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2292 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1291 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0579 Fin15AnchoredAtom0580 Fin15AnchoredAtom0585
    Fin15AnchoredAtom0785 Fin15AnchoredAtom1291 Fin15AnchoredAtom2292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01797
  ] at hbad
  tauto

theorem fin15Anchored_clause17749 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2294 chi ∧
      ¬Fin15AnchoredAtom0579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0579 Fin15AnchoredAtom2294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04869
  ] at hbad
  tauto

theorem fin15Anchored_clause17750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2294 chi ∧
      ¬Fin15AnchoredAtom0582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0582 Fin15AnchoredAtom2294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04869
  ] at hbad
  tauto

theorem fin15Anchored_clause17751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2296 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0589 Fin15AnchoredAtom2296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17157
  ] at hbad
  tauto

theorem fin15Anchored_clause17752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2298 chi ∧
      ¬Fin15AnchoredAtom0580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0580 Fin15AnchoredAtom2298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05381
  ] at hbad
  tauto

theorem fin15Anchored_clause17753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2299 chi ∧
      ¬Fin15AnchoredAtom0580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0580 Fin15AnchoredAtom2299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09477
  ] at hbad
  tauto

theorem fin15Anchored_clause17754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2299 chi ∧
      ¬Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0792 Fin15AnchoredAtom2299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09477
  ] at hbad
  tauto

theorem fin15Anchored_clause17755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2304 chi ∧
      ¬Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0797 Fin15AnchoredAtom2304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12549
  ] at hbad
  tauto

theorem fin15Anchored_clause17756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2305 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0598 Fin15AnchoredAtom2305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20741
  ] at hbad
  tauto

theorem fin15Anchored_clause17757 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2305 chi ∧
      Fin15AnchoredAtom0582 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1304 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0582 Fin15AnchoredAtom0584 Fin15AnchoredAtom0598
    Fin15AnchoredAtom0798 Fin15AnchoredAtom1304 Fin15AnchoredAtom2305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20741
  ] at hbad
  tauto

theorem fin15Anchored_clause17758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2307 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom2307 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03589
  ] at hbad
  tauto

theorem fin15Anchored_clause17759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2307 chi ∧
      ¬Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom2307 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03589
  ] at hbad
  tauto

theorem fin15Anchored_clause17760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom2308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05637
  ] at hbad
  tauto

theorem fin15Anchored_clause17761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom2308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05637
  ] at hbad
  tauto

theorem fin15Anchored_clause17762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom2308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05637
  ] at hbad
  tauto

theorem fin15Anchored_clause17763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom2308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05637
  ] at hbad
  tauto

theorem fin15Anchored_clause17764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom2308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05637
  ] at hbad
  tauto

theorem fin15Anchored_clause17765 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom0587 Fin15AnchoredAtom0591
    Fin15AnchoredAtom0801 Fin15AnchoredAtom1307 Fin15AnchoredAtom2308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05637
  ] at hbad
  tauto

theorem fin15Anchored_clause17766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom2309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09733
  ] at hbad
  tauto

theorem fin15Anchored_clause17767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0588 Fin15AnchoredAtom2309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09733
  ] at hbad
  tauto

theorem fin15Anchored_clause17768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0592 Fin15AnchoredAtom2309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09733
  ] at hbad
  tauto

theorem fin15Anchored_clause17769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom2309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09733
  ] at hbad
  tauto

theorem fin15Anchored_clause17770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1308 Fin15AnchoredAtom2309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09733
  ] at hbad
  tauto

theorem fin15Anchored_clause17771 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom0588 Fin15AnchoredAtom0592
    Fin15AnchoredAtom0802 Fin15AnchoredAtom1308 Fin15AnchoredAtom2309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09733
  ] at hbad
  tauto

theorem fin15Anchored_clause17772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom2310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17925
  ] at hbad
  tauto

theorem fin15Anchored_clause17773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0589 Fin15AnchoredAtom2310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17925
  ] at hbad
  tauto

theorem fin15Anchored_clause17774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0593 Fin15AnchoredAtom2310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17925
  ] at hbad
  tauto

theorem fin15Anchored_clause17775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0803 Fin15AnchoredAtom2310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17925
  ] at hbad
  tauto

theorem fin15Anchored_clause17776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1309 Fin15AnchoredAtom2310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17925
  ] at hbad
  tauto

theorem fin15Anchored_clause17777 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom0589 Fin15AnchoredAtom0593
    Fin15AnchoredAtom0803 Fin15AnchoredAtom1309 Fin15AnchoredAtom2310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17925
  ] at hbad
  tauto

theorem fin15Anchored_clause17778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom0586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0586 Fin15AnchoredAtom2311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06661
  ] at hbad
  tauto

theorem fin15Anchored_clause17779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom2311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06661
  ] at hbad
  tauto

theorem fin15Anchored_clause17780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom0594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0594 Fin15AnchoredAtom2311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06661
  ] at hbad
  tauto

theorem fin15Anchored_clause17781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom0804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0804 Fin15AnchoredAtom2311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06661
  ] at hbad
  tauto

theorem fin15Anchored_clause17782 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2311 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0586 Fin15AnchoredAtom0587 Fin15AnchoredAtom0594
    Fin15AnchoredAtom0804 Fin15AnchoredAtom1310 Fin15AnchoredAtom2311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06661
  ] at hbad
  tauto

theorem fin15Anchored_clause17783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2312 chi ∧
      ¬Fin15AnchoredAtom0586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0586 Fin15AnchoredAtom2312 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10757
  ] at hbad
  tauto

theorem fin15Anchored_clause17784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2312 chi ∧
      ¬Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0588 Fin15AnchoredAtom2312 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10757
  ] at hbad
  tauto

theorem fin15Anchored_clause17785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2312 chi ∧
      ¬Fin15AnchoredAtom0805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0805 Fin15AnchoredAtom2312 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10757
  ] at hbad
  tauto

theorem fin15Anchored_clause17786 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2312 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1311 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0586 Fin15AnchoredAtom0588 Fin15AnchoredAtom0595
    Fin15AnchoredAtom0805 Fin15AnchoredAtom1311 Fin15AnchoredAtom2312 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10757
  ] at hbad
  tauto

theorem fin15Anchored_clause17787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2313 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0589 Fin15AnchoredAtom2313 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18949
  ] at hbad
  tauto

theorem fin15Anchored_clause17788 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2313 chi ∧
      ¬Fin15AnchoredAtom0596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0596 Fin15AnchoredAtom2313 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18949
  ] at hbad
  tauto

theorem fin15Anchored_clause17789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2313 chi ∧
      ¬Fin15AnchoredAtom0806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0806 Fin15AnchoredAtom2313 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18949
  ] at hbad
  tauto

theorem fin15Anchored_clause17790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2313 chi ∧
      ¬Fin15AnchoredAtom1312 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1312 Fin15AnchoredAtom2313 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18949
  ] at hbad
  tauto

theorem fin15Anchored_clause17791 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2313 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom1312 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0586 Fin15AnchoredAtom0589 Fin15AnchoredAtom0596
    Fin15AnchoredAtom0806 Fin15AnchoredAtom1312 Fin15AnchoredAtom2313 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18949
  ] at hbad
  tauto

end ErdosSzekeres

end
