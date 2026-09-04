module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 131. -/

theorem fin15Anchored_clause16768 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2091 chi ∧
      Fin15AnchoredAtom0520 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0520 Fin15AnchoredAtom0521 Fin15AnchoredAtom0528
    Fin15AnchoredAtom0804 Fin15AnchoredAtom1090 Fin15AnchoredAtom2091 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06659
  ] at hbad
  tauto

theorem fin15Anchored_clause16769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom0520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0520 Fin15AnchoredAtom2092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10755
  ] at hbad
  tauto

theorem fin15Anchored_clause16770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom0529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0529 Fin15AnchoredAtom2092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10755
  ] at hbad
  tauto

theorem fin15Anchored_clause16771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom0805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0805 Fin15AnchoredAtom2092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10755
  ] at hbad
  tauto

theorem fin15Anchored_clause16772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom1091 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1091 Fin15AnchoredAtom2092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10755
  ] at hbad
  tauto

theorem fin15Anchored_clause16773 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2092 chi ∧
      Fin15AnchoredAtom0520 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1091 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0520 Fin15AnchoredAtom0522 Fin15AnchoredAtom0529
    Fin15AnchoredAtom0805 Fin15AnchoredAtom1091 Fin15AnchoredAtom2092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10755
  ] at hbad
  tauto

theorem fin15Anchored_clause16774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2093 chi ∧
      ¬Fin15AnchoredAtom0520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0520 Fin15AnchoredAtom2093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18947
  ] at hbad
  tauto

theorem fin15Anchored_clause16775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2093 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0523 Fin15AnchoredAtom2093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18947
  ] at hbad
  tauto

theorem fin15Anchored_clause16776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2093 chi ∧
      ¬Fin15AnchoredAtom0806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0806 Fin15AnchoredAtom2093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18947
  ] at hbad
  tauto

theorem fin15Anchored_clause16777 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom2094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12803
  ] at hbad
  tauto

theorem fin15Anchored_clause16778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0522 Fin15AnchoredAtom2094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12803
  ] at hbad
  tauto

theorem fin15Anchored_clause16779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0531 Fin15AnchoredAtom2094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12803
  ] at hbad
  tauto

theorem fin15Anchored_clause16780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom2094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12803
  ] at hbad
  tauto

theorem fin15Anchored_clause16781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom2094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12803
  ] at hbad
  tauto

theorem fin15Anchored_clause16782 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom0522 Fin15AnchoredAtom0531
    Fin15AnchoredAtom0807 Fin15AnchoredAtom1093 Fin15AnchoredAtom2094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12803
  ] at hbad
  tauto

theorem fin15Anchored_clause16783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom2095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20995
  ] at hbad
  tauto

theorem fin15Anchored_clause16784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0523 Fin15AnchoredAtom2095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20995
  ] at hbad
  tauto

theorem fin15Anchored_clause16785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0532 Fin15AnchoredAtom2095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20995
  ] at hbad
  tauto

theorem fin15Anchored_clause16786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0808 Fin15AnchoredAtom2095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20995
  ] at hbad
  tauto

theorem fin15Anchored_clause16787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1094 Fin15AnchoredAtom2095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20995
  ] at hbad
  tauto

theorem fin15Anchored_clause16788 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom0523 Fin15AnchoredAtom0532
    Fin15AnchoredAtom0808 Fin15AnchoredAtom1094 Fin15AnchoredAtom2095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20995
  ] at hbad
  tauto

theorem fin15Anchored_clause16789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0522 Fin15AnchoredAtom2096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25091
  ] at hbad
  tauto

theorem fin15Anchored_clause16790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0523 Fin15AnchoredAtom2096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25091
  ] at hbad
  tauto

theorem fin15Anchored_clause16791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0533 Fin15AnchoredAtom2096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25091
  ] at hbad
  tauto

theorem fin15Anchored_clause16792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0809 Fin15AnchoredAtom2096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25091
  ] at hbad
  tauto

theorem fin15Anchored_clause16793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1095 Fin15AnchoredAtom2096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25091
  ] at hbad
  tauto

theorem fin15Anchored_clause16794 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0522 Fin15AnchoredAtom0523 Fin15AnchoredAtom0533
    Fin15AnchoredAtom0809 Fin15AnchoredAtom1095 Fin15AnchoredAtom2096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25091
  ] at hbad
  tauto

theorem fin15Anchored_clause16795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom0524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0524 Fin15AnchoredAtom2097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07171
  ] at hbad
  tauto

theorem fin15Anchored_clause16796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom2097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07171
  ] at hbad
  tauto

theorem fin15Anchored_clause16797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom0528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0528 Fin15AnchoredAtom2097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07171
  ] at hbad
  tauto

theorem fin15Anchored_clause16798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom0810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0810 Fin15AnchoredAtom2097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07171
  ] at hbad
  tauto

theorem fin15Anchored_clause16799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1096 Fin15AnchoredAtom2097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07171
  ] at hbad
  tauto

theorem fin15Anchored_clause16800 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2097 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0524 Fin15AnchoredAtom0525 Fin15AnchoredAtom0528
    Fin15AnchoredAtom0810 Fin15AnchoredAtom1096 Fin15AnchoredAtom2097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07171
  ] at hbad
  tauto

theorem fin15Anchored_clause16801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom0524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0524 Fin15AnchoredAtom2098 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11267
  ] at hbad
  tauto

theorem fin15Anchored_clause16802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom2098 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11267
  ] at hbad
  tauto

theorem fin15Anchored_clause16803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom0529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0529 Fin15AnchoredAtom2098 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11267
  ] at hbad
  tauto

theorem fin15Anchored_clause16804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0811 Fin15AnchoredAtom2098 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11267
  ] at hbad
  tauto

theorem fin15Anchored_clause16805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom1097 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1097 Fin15AnchoredAtom2098 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11267
  ] at hbad
  tauto

theorem fin15Anchored_clause16806 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2098 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1097 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0524 Fin15AnchoredAtom0526 Fin15AnchoredAtom0529
    Fin15AnchoredAtom0811 Fin15AnchoredAtom1097 Fin15AnchoredAtom2098 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11267
  ] at hbad
  tauto

theorem fin15Anchored_clause16807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2099 chi ∧
      ¬Fin15AnchoredAtom0524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0524 Fin15AnchoredAtom2099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19459
  ] at hbad
  tauto

theorem fin15Anchored_clause16808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2099 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0527 Fin15AnchoredAtom2099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19459
  ] at hbad
  tauto

theorem fin15Anchored_clause16809 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2099 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0530 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom1098 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0524 Fin15AnchoredAtom0527 Fin15AnchoredAtom0530
    Fin15AnchoredAtom0812 Fin15AnchoredAtom1098 Fin15AnchoredAtom2099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19459
  ] at hbad
  tauto

theorem fin15Anchored_clause16810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom2100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13315
  ] at hbad
  tauto

theorem fin15Anchored_clause16811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom2100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13315
  ] at hbad
  tauto

theorem fin15Anchored_clause16812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0531 Fin15AnchoredAtom2100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13315
  ] at hbad
  tauto

theorem fin15Anchored_clause16813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom2100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13315
  ] at hbad
  tauto

theorem fin15Anchored_clause16814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom2100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13315
  ] at hbad
  tauto

theorem fin15Anchored_clause16815 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom0526 Fin15AnchoredAtom0531
    Fin15AnchoredAtom0813 Fin15AnchoredAtom1099 Fin15AnchoredAtom2100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13315
  ] at hbad
  tauto

theorem fin15Anchored_clause16816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom2101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21507
  ] at hbad
  tauto

theorem fin15Anchored_clause16817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0527 Fin15AnchoredAtom2101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21507
  ] at hbad
  tauto

theorem fin15Anchored_clause16818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0532 Fin15AnchoredAtom2101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21507
  ] at hbad
  tauto

theorem fin15Anchored_clause16819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0814 Fin15AnchoredAtom2101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21507
  ] at hbad
  tauto

theorem fin15Anchored_clause16820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1100 Fin15AnchoredAtom2101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21507
  ] at hbad
  tauto

theorem fin15Anchored_clause16821 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom0527 Fin15AnchoredAtom0532
    Fin15AnchoredAtom0814 Fin15AnchoredAtom1100 Fin15AnchoredAtom2101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21507
  ] at hbad
  tauto

theorem fin15Anchored_clause16822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom2102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25603
  ] at hbad
  tauto

theorem fin15Anchored_clause16823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0527 Fin15AnchoredAtom2102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25603
  ] at hbad
  tauto

theorem fin15Anchored_clause16824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0533 Fin15AnchoredAtom2102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25603
  ] at hbad
  tauto

theorem fin15Anchored_clause16825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0815 Fin15AnchoredAtom2102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25603
  ] at hbad
  tauto

theorem fin15Anchored_clause16826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1101 Fin15AnchoredAtom2102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25603
  ] at hbad
  tauto

theorem fin15Anchored_clause16827 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom0527 Fin15AnchoredAtom0533
    Fin15AnchoredAtom0815 Fin15AnchoredAtom1101 Fin15AnchoredAtom2102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25603
  ] at hbad
  tauto

theorem fin15Anchored_clause16828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom0528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0528 Fin15AnchoredAtom2103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14339
  ] at hbad
  tauto

theorem fin15Anchored_clause16829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom0529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0529 Fin15AnchoredAtom2103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14339
  ] at hbad
  tauto

theorem fin15Anchored_clause16830 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0531 Fin15AnchoredAtom2103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14339
  ] at hbad
  tauto

theorem fin15Anchored_clause16831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom0816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0816 Fin15AnchoredAtom2103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14339
  ] at hbad
  tauto

theorem fin15Anchored_clause16832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom1102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1102 Fin15AnchoredAtom2103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14339
  ] at hbad
  tauto

theorem fin15Anchored_clause16833 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2103 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0528 Fin15AnchoredAtom0529 Fin15AnchoredAtom0531
    Fin15AnchoredAtom0816 Fin15AnchoredAtom1102 Fin15AnchoredAtom2103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14339
  ] at hbad
  tauto

theorem fin15Anchored_clause16834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2104 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0532 Fin15AnchoredAtom2104 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22531
  ] at hbad
  tauto

theorem fin15Anchored_clause16835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2104 chi ∧
      ¬Fin15AnchoredAtom0817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0817 Fin15AnchoredAtom2104 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22531
  ] at hbad
  tauto

theorem fin15Anchored_clause16836 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2104 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0530 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1103 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0528 Fin15AnchoredAtom0530 Fin15AnchoredAtom0532
    Fin15AnchoredAtom0817 Fin15AnchoredAtom1103 Fin15AnchoredAtom2104 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22531
  ] at hbad
  tauto

theorem fin15Anchored_clause16837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2105 chi ∧
      ¬Fin15AnchoredAtom0529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0529 Fin15AnchoredAtom2105 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26627
  ] at hbad
  tauto

theorem fin15Anchored_clause16838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0531 Fin15AnchoredAtom2106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28675
  ] at hbad
  tauto

theorem fin15Anchored_clause16839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0532 Fin15AnchoredAtom2106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28675
  ] at hbad
  tauto

theorem fin15Anchored_clause16840 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0533 Fin15AnchoredAtom2106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28675
  ] at hbad
  tauto

theorem fin15Anchored_clause16841 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0819 Fin15AnchoredAtom2106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28675
  ] at hbad
  tauto

theorem fin15Anchored_clause16842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1105 Fin15AnchoredAtom2106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28675
  ] at hbad
  tauto

theorem fin15Anchored_clause16843 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0531 Fin15AnchoredAtom0532 Fin15AnchoredAtom0533
    Fin15AnchoredAtom0819 Fin15AnchoredAtom1105 Fin15AnchoredAtom2106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28675
  ] at hbad
  tauto

theorem fin15Anchored_clause16844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom2107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00061
  ] at hbad
  tauto

theorem fin15Anchored_clause16845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom2107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00061
  ] at hbad
  tauto

theorem fin15Anchored_clause16846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom2107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00061
  ] at hbad
  tauto

theorem fin15Anchored_clause16847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom2107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00061
  ] at hbad
  tauto

theorem fin15Anchored_clause16848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom2107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00061
  ] at hbad
  tauto

theorem fin15Anchored_clause16849 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom0535 Fin15AnchoredAtom0545
    Fin15AnchoredAtom0600 Fin15AnchoredAtom1106 Fin15AnchoredAtom2107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00061
  ] at hbad
  tauto

theorem fin15Anchored_clause16850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom2108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00093
  ] at hbad
  tauto

theorem fin15Anchored_clause16851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom2108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00093
  ] at hbad
  tauto

theorem fin15Anchored_clause16852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom2108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00093
  ] at hbad
  tauto

theorem fin15Anchored_clause16853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom2108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00093
  ] at hbad
  tauto

theorem fin15Anchored_clause16854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom2108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00093
  ] at hbad
  tauto

theorem fin15Anchored_clause16855 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom0536 Fin15AnchoredAtom0546
    Fin15AnchoredAtom0601 Fin15AnchoredAtom1107 Fin15AnchoredAtom2108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00093
  ] at hbad
  tauto

theorem fin15Anchored_clause16856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom2109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00157
  ] at hbad
  tauto

theorem fin15Anchored_clause16857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom2109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00157
  ] at hbad
  tauto

theorem fin15Anchored_clause16858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom2109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00157
  ] at hbad
  tauto

theorem fin15Anchored_clause16859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom2109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00157
  ] at hbad
  tauto

theorem fin15Anchored_clause16860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom2109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00157
  ] at hbad
  tauto

theorem fin15Anchored_clause16861 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom0537 Fin15AnchoredAtom0547
    Fin15AnchoredAtom0602 Fin15AnchoredAtom1108 Fin15AnchoredAtom2109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00157
  ] at hbad
  tauto

theorem fin15Anchored_clause16862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2110 chi ∧
      ¬Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom2110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00285
  ] at hbad
  tauto

theorem fin15Anchored_clause16863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2110 chi ∧
      ¬Fin15AnchoredAtom0538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom2110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00285
  ] at hbad
  tauto

theorem fin15Anchored_clause16864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2110 chi ∧
      ¬Fin15AnchoredAtom0548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0548 Fin15AnchoredAtom2110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00285
  ] at hbad
  tauto

theorem fin15Anchored_clause16865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2110 chi ∧
      ¬Fin15AnchoredAtom1109 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1109 Fin15AnchoredAtom2110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00285
  ] at hbad
  tauto

theorem fin15Anchored_clause16866 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2110 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom1109 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom0538 Fin15AnchoredAtom0548
    Fin15AnchoredAtom0603 Fin15AnchoredAtom1109 Fin15AnchoredAtom2110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00285
  ] at hbad
  tauto

theorem fin15Anchored_clause16867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom2111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00541
  ] at hbad
  tauto

theorem fin15Anchored_clause16868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom2111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00541
  ] at hbad
  tauto

theorem fin15Anchored_clause16869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom2111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00541
  ] at hbad
  tauto

theorem fin15Anchored_clause16870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom2111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00541
  ] at hbad
  tauto

theorem fin15Anchored_clause16871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom2111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00541
  ] at hbad
  tauto

theorem fin15Anchored_clause16872 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom0539 Fin15AnchoredAtom0549
    Fin15AnchoredAtom0604 Fin15AnchoredAtom1110 Fin15AnchoredAtom2111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00541
  ] at hbad
  tauto

theorem fin15Anchored_clause16873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom2112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01053
  ] at hbad
  tauto

theorem fin15Anchored_clause16874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom2112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01053
  ] at hbad
  tauto

theorem fin15Anchored_clause16875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom2112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01053
  ] at hbad
  tauto

theorem fin15Anchored_clause16876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom2112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01053
  ] at hbad
  tauto

theorem fin15Anchored_clause16877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom2112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01053
  ] at hbad
  tauto

theorem fin15Anchored_clause16878 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom0540 Fin15AnchoredAtom0550
    Fin15AnchoredAtom0605 Fin15AnchoredAtom1111 Fin15AnchoredAtom2112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01053
  ] at hbad
  tauto

theorem fin15Anchored_clause16879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom0541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0541 Fin15AnchoredAtom2113 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02077
  ] at hbad
  tauto

theorem fin15Anchored_clause16880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom0551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0551 Fin15AnchoredAtom2113 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02077
  ] at hbad
  tauto

theorem fin15Anchored_clause16881 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom0606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0606 Fin15AnchoredAtom2113 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02077
  ] at hbad
  tauto

theorem fin15Anchored_clause16882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom1112 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1112 Fin15AnchoredAtom2113 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02077
  ] at hbad
  tauto

theorem fin15Anchored_clause16883 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2113 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0551 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom1112 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom0541 Fin15AnchoredAtom0551
    Fin15AnchoredAtom0606 Fin15AnchoredAtom1112 Fin15AnchoredAtom2113 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02077
  ] at hbad
  tauto

theorem fin15Anchored_clause16884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom2114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04125
  ] at hbad
  tauto

theorem fin15Anchored_clause16885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom2114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04125
  ] at hbad
  tauto

theorem fin15Anchored_clause16886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom2114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04125
  ] at hbad
  tauto

theorem fin15Anchored_clause16887 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom2114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04125
  ] at hbad
  tauto

theorem fin15Anchored_clause16888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom2114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04125
  ] at hbad
  tauto

theorem fin15Anchored_clause16889 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom0542 Fin15AnchoredAtom0552
    Fin15AnchoredAtom0607 Fin15AnchoredAtom1113 Fin15AnchoredAtom2114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04125
  ] at hbad
  tauto

theorem fin15Anchored_clause16890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom2115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08221
  ] at hbad
  tauto

theorem fin15Anchored_clause16891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom2115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08221
  ] at hbad
  tauto

theorem fin15Anchored_clause16892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0553 Fin15AnchoredAtom2115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08221
  ] at hbad
  tauto

theorem fin15Anchored_clause16893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom2115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08221
  ] at hbad
  tauto

theorem fin15Anchored_clause16894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1114 Fin15AnchoredAtom2115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08221
  ] at hbad
  tauto

theorem fin15Anchored_clause16895 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom0543 Fin15AnchoredAtom0553
    Fin15AnchoredAtom0608 Fin15AnchoredAtom1114 Fin15AnchoredAtom2115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08221
  ] at hbad
  tauto

end ErdosSzekeres

end
