module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 157. -/

theorem fin15Anchored_clause20096 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom0773 Fin15AnchoredAtom0777
    Fin15AnchoredAtom0802 Fin15AnchoredAtom1768 Fin15AnchoredAtom2769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09857
  ] at hbad
  tauto

theorem fin15Anchored_clause20097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom2770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18049
  ] at hbad
  tauto

theorem fin15Anchored_clause20098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0774 Fin15AnchoredAtom2770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18049
  ] at hbad
  tauto

theorem fin15Anchored_clause20099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0778 Fin15AnchoredAtom2770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18049
  ] at hbad
  tauto

theorem fin15Anchored_clause20100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0803 Fin15AnchoredAtom2770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18049
  ] at hbad
  tauto

theorem fin15Anchored_clause20101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1769 Fin15AnchoredAtom2770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18049
  ] at hbad
  tauto

theorem fin15Anchored_clause20102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom0774 Fin15AnchoredAtom0778
    Fin15AnchoredAtom0803 Fin15AnchoredAtom1769 Fin15AnchoredAtom2770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18049
  ] at hbad
  tauto

theorem fin15Anchored_clause20103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom0771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0771 Fin15AnchoredAtom2771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06785
  ] at hbad
  tauto

theorem fin15Anchored_clause20104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom2771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06785
  ] at hbad
  tauto

theorem fin15Anchored_clause20105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom0779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0779 Fin15AnchoredAtom2771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06785
  ] at hbad
  tauto

theorem fin15Anchored_clause20106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom0804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0804 Fin15AnchoredAtom2771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06785
  ] at hbad
  tauto

theorem fin15Anchored_clause20107 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2771 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0771 Fin15AnchoredAtom0772 Fin15AnchoredAtom0779
    Fin15AnchoredAtom0804 Fin15AnchoredAtom1770 Fin15AnchoredAtom2771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06785
  ] at hbad
  tauto

theorem fin15Anchored_clause20108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2772 chi ∧
      ¬Fin15AnchoredAtom0771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0771 Fin15AnchoredAtom2772 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10881
  ] at hbad
  tauto

theorem fin15Anchored_clause20109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2772 chi ∧
      ¬Fin15AnchoredAtom0780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0780 Fin15AnchoredAtom2772 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10881
  ] at hbad
  tauto

theorem fin15Anchored_clause20110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2772 chi ∧
      ¬Fin15AnchoredAtom0805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0805 Fin15AnchoredAtom2772 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10881
  ] at hbad
  tauto

theorem fin15Anchored_clause20111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2772 chi ∧
      ¬Fin15AnchoredAtom1771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1771 Fin15AnchoredAtom2772 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10881
  ] at hbad
  tauto

theorem fin15Anchored_clause20112 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2772 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0771 Fin15AnchoredAtom0773 Fin15AnchoredAtom0780
    Fin15AnchoredAtom0805 Fin15AnchoredAtom1771 Fin15AnchoredAtom2772 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10881
  ] at hbad
  tauto

theorem fin15Anchored_clause20113 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2773 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0774 Fin15AnchoredAtom2773 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19073
  ] at hbad
  tauto

theorem fin15Anchored_clause20114 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2773 chi ∧
      ¬Fin15AnchoredAtom0806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0806 Fin15AnchoredAtom2773 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19073
  ] at hbad
  tauto

theorem fin15Anchored_clause20115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom2774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12929
  ] at hbad
  tauto

theorem fin15Anchored_clause20116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0773 Fin15AnchoredAtom2774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12929
  ] at hbad
  tauto

theorem fin15Anchored_clause20117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom2774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12929
  ] at hbad
  tauto

theorem fin15Anchored_clause20118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom2774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12929
  ] at hbad
  tauto

theorem fin15Anchored_clause20119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom2774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12929
  ] at hbad
  tauto

theorem fin15Anchored_clause20120 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom0773 Fin15AnchoredAtom0782
    Fin15AnchoredAtom0807 Fin15AnchoredAtom1773 Fin15AnchoredAtom2774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12929
  ] at hbad
  tauto

theorem fin15Anchored_clause20121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom2775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21121
  ] at hbad
  tauto

theorem fin15Anchored_clause20122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0774 Fin15AnchoredAtom2775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21121
  ] at hbad
  tauto

theorem fin15Anchored_clause20123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0783 Fin15AnchoredAtom2775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21121
  ] at hbad
  tauto

theorem fin15Anchored_clause20124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0808 Fin15AnchoredAtom2775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21121
  ] at hbad
  tauto

theorem fin15Anchored_clause20125 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1774 Fin15AnchoredAtom2775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21121
  ] at hbad
  tauto

theorem fin15Anchored_clause20126 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom0774 Fin15AnchoredAtom0783
    Fin15AnchoredAtom0808 Fin15AnchoredAtom1774 Fin15AnchoredAtom2775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21121
  ] at hbad
  tauto

theorem fin15Anchored_clause20127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0773 Fin15AnchoredAtom2776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25217
  ] at hbad
  tauto

theorem fin15Anchored_clause20128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0774 Fin15AnchoredAtom2776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25217
  ] at hbad
  tauto

theorem fin15Anchored_clause20129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0784 Fin15AnchoredAtom2776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25217
  ] at hbad
  tauto

theorem fin15Anchored_clause20130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0809 Fin15AnchoredAtom2776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25217
  ] at hbad
  tauto

theorem fin15Anchored_clause20131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1775 Fin15AnchoredAtom2776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25217
  ] at hbad
  tauto

theorem fin15Anchored_clause20132 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0773 Fin15AnchoredAtom0774 Fin15AnchoredAtom0784
    Fin15AnchoredAtom0809 Fin15AnchoredAtom1775 Fin15AnchoredAtom2776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25217
  ] at hbad
  tauto

theorem fin15Anchored_clause20133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom2777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07297
  ] at hbad
  tauto

theorem fin15Anchored_clause20134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom2777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07297
  ] at hbad
  tauto

theorem fin15Anchored_clause20135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom0810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0810 Fin15AnchoredAtom2777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07297
  ] at hbad
  tauto

theorem fin15Anchored_clause20136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1776 Fin15AnchoredAtom2777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07297
  ] at hbad
  tauto

theorem fin15Anchored_clause20137 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2777 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom0776 Fin15AnchoredAtom0779
    Fin15AnchoredAtom0810 Fin15AnchoredAtom1776 Fin15AnchoredAtom2777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07297
  ] at hbad
  tauto

theorem fin15Anchored_clause20138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom2778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11393
  ] at hbad
  tauto

theorem fin15Anchored_clause20139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom2778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11393
  ] at hbad
  tauto

theorem fin15Anchored_clause20140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom0780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0780 Fin15AnchoredAtom2778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11393
  ] at hbad
  tauto

theorem fin15Anchored_clause20141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0811 Fin15AnchoredAtom2778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11393
  ] at hbad
  tauto

theorem fin15Anchored_clause20142 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1777 Fin15AnchoredAtom2778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11393
  ] at hbad
  tauto

theorem fin15Anchored_clause20143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2778 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom0777 Fin15AnchoredAtom0780
    Fin15AnchoredAtom0811 Fin15AnchoredAtom1777 Fin15AnchoredAtom2778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11393
  ] at hbad
  tauto

theorem fin15Anchored_clause20144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom2779 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19585
  ] at hbad
  tauto

theorem fin15Anchored_clause20145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0778 Fin15AnchoredAtom2779 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19585
  ] at hbad
  tauto

theorem fin15Anchored_clause20146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom0812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0812 Fin15AnchoredAtom2779 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19585
  ] at hbad
  tauto

theorem fin15Anchored_clause20147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1778 Fin15AnchoredAtom2779 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19585
  ] at hbad
  tauto

theorem fin15Anchored_clause20148 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2779 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom0778 Fin15AnchoredAtom0781
    Fin15AnchoredAtom0812 Fin15AnchoredAtom1778 Fin15AnchoredAtom2779 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19585
  ] at hbad
  tauto

theorem fin15Anchored_clause20149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom2780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13441
  ] at hbad
  tauto

theorem fin15Anchored_clause20150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom2780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13441
  ] at hbad
  tauto

theorem fin15Anchored_clause20151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom2780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13441
  ] at hbad
  tauto

theorem fin15Anchored_clause20152 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom2780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13441
  ] at hbad
  tauto

theorem fin15Anchored_clause20153 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom2780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13441
  ] at hbad
  tauto

theorem fin15Anchored_clause20154 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom0777 Fin15AnchoredAtom0782
    Fin15AnchoredAtom0813 Fin15AnchoredAtom1779 Fin15AnchoredAtom2780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13441
  ] at hbad
  tauto

theorem fin15Anchored_clause20155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom2781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21633
  ] at hbad
  tauto

theorem fin15Anchored_clause20156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0778 Fin15AnchoredAtom2781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21633
  ] at hbad
  tauto

theorem fin15Anchored_clause20157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0783 Fin15AnchoredAtom2781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21633
  ] at hbad
  tauto

theorem fin15Anchored_clause20158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0814 Fin15AnchoredAtom2781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21633
  ] at hbad
  tauto

theorem fin15Anchored_clause20159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1780 Fin15AnchoredAtom2781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21633
  ] at hbad
  tauto

theorem fin15Anchored_clause20160 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom0778 Fin15AnchoredAtom0783
    Fin15AnchoredAtom0814 Fin15AnchoredAtom1780 Fin15AnchoredAtom2781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21633
  ] at hbad
  tauto

theorem fin15Anchored_clause20161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom2782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25729
  ] at hbad
  tauto

theorem fin15Anchored_clause20162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0778 Fin15AnchoredAtom2782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25729
  ] at hbad
  tauto

theorem fin15Anchored_clause20163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0784 Fin15AnchoredAtom2782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25729
  ] at hbad
  tauto

theorem fin15Anchored_clause20164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0815 Fin15AnchoredAtom2782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25729
  ] at hbad
  tauto

theorem fin15Anchored_clause20165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1781 Fin15AnchoredAtom2782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25729
  ] at hbad
  tauto

theorem fin15Anchored_clause20166 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom0778 Fin15AnchoredAtom0784
    Fin15AnchoredAtom0815 Fin15AnchoredAtom1781 Fin15AnchoredAtom2782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25729
  ] at hbad
  tauto

theorem fin15Anchored_clause20167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2783 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom2783 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14465
  ] at hbad
  tauto

theorem fin15Anchored_clause20168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2783 chi ∧
      ¬Fin15AnchoredAtom0816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0816 Fin15AnchoredAtom2783 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14465
  ] at hbad
  tauto

theorem fin15Anchored_clause20169 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2783 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0779 Fin15AnchoredAtom0780 Fin15AnchoredAtom0782
    Fin15AnchoredAtom0816 Fin15AnchoredAtom1782 Fin15AnchoredAtom2783 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14465
  ] at hbad
  tauto

theorem fin15Anchored_clause20170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom0781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0781 Fin15AnchoredAtom2784 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22657
  ] at hbad
  tauto

theorem fin15Anchored_clause20171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0783 Fin15AnchoredAtom2784 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22657
  ] at hbad
  tauto

theorem fin15Anchored_clause20172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom0817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0817 Fin15AnchoredAtom2784 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22657
  ] at hbad
  tauto

theorem fin15Anchored_clause20173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1783 Fin15AnchoredAtom2784 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22657
  ] at hbad
  tauto

theorem fin15Anchored_clause20174 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2784 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0779 Fin15AnchoredAtom0781 Fin15AnchoredAtom0783
    Fin15AnchoredAtom0817 Fin15AnchoredAtom1783 Fin15AnchoredAtom2784 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22657
  ] at hbad
  tauto

theorem fin15Anchored_clause20175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2785 chi ∧
      ¬Fin15AnchoredAtom0780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0780 Fin15AnchoredAtom2785 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26753
  ] at hbad
  tauto

theorem fin15Anchored_clause20176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2785 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0784 Fin15AnchoredAtom2785 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26753
  ] at hbad
  tauto

theorem fin15Anchored_clause20177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom2786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28801
  ] at hbad
  tauto

theorem fin15Anchored_clause20178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0783 Fin15AnchoredAtom2786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28801
  ] at hbad
  tauto

theorem fin15Anchored_clause20179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0784 Fin15AnchoredAtom2786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28801
  ] at hbad
  tauto

theorem fin15Anchored_clause20180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0819 Fin15AnchoredAtom2786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28801
  ] at hbad
  tauto

theorem fin15Anchored_clause20181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1785 Fin15AnchoredAtom2786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28801
  ] at hbad
  tauto

theorem fin15Anchored_clause20182 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom0783 Fin15AnchoredAtom0784
    Fin15AnchoredAtom0819 Fin15AnchoredAtom1785 Fin15AnchoredAtom2786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28801
  ] at hbad
  tauto

theorem fin15Anchored_clause20183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom0785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom2788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05889
  ] at hbad
  tauto

theorem fin15Anchored_clause20184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom0787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0787 Fin15AnchoredAtom2788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05889
  ] at hbad
  tauto

theorem fin15Anchored_clause20185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom0791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0791 Fin15AnchoredAtom2788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05889
  ] at hbad
  tauto

theorem fin15Anchored_clause20186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom2788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05889
  ] at hbad
  tauto

theorem fin15Anchored_clause20187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom2788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05889
  ] at hbad
  tauto

theorem fin15Anchored_clause20188 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom0787 Fin15AnchoredAtom0791
    Fin15AnchoredAtom0801 Fin15AnchoredAtom1787 Fin15AnchoredAtom2788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05889
  ] at hbad
  tauto

theorem fin15Anchored_clause20189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom0785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom2789 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09985
  ] at hbad
  tauto

theorem fin15Anchored_clause20190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom0788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0788 Fin15AnchoredAtom2789 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09985
  ] at hbad
  tauto

theorem fin15Anchored_clause20191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0792 Fin15AnchoredAtom2789 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09985
  ] at hbad
  tauto

theorem fin15Anchored_clause20192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom2789 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09985
  ] at hbad
  tauto

theorem fin15Anchored_clause20193 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom0788 Fin15AnchoredAtom0792
    Fin15AnchoredAtom0802 Fin15AnchoredAtom1788 Fin15AnchoredAtom2789 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09985
  ] at hbad
  tauto

theorem fin15Anchored_clause20194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom0785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom2790 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18177
  ] at hbad
  tauto

theorem fin15Anchored_clause20195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom0789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0789 Fin15AnchoredAtom2790 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18177
  ] at hbad
  tauto

theorem fin15Anchored_clause20196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom0793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0793 Fin15AnchoredAtom2790 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18177
  ] at hbad
  tauto

theorem fin15Anchored_clause20197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0803 Fin15AnchoredAtom2790 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18177
  ] at hbad
  tauto

theorem fin15Anchored_clause20198 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2790 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom0789 Fin15AnchoredAtom0793
    Fin15AnchoredAtom0803 Fin15AnchoredAtom1789 Fin15AnchoredAtom2790 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18177
  ] at hbad
  tauto

theorem fin15Anchored_clause20199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom0787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0787 Fin15AnchoredAtom2794 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13057
  ] at hbad
  tauto

theorem fin15Anchored_clause20200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom0788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0788 Fin15AnchoredAtom2794 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13057
  ] at hbad
  tauto

theorem fin15Anchored_clause20201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0797 Fin15AnchoredAtom2794 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13057
  ] at hbad
  tauto

theorem fin15Anchored_clause20202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom2794 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13057
  ] at hbad
  tauto

theorem fin15Anchored_clause20203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1793 Fin15AnchoredAtom2794 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13057
  ] at hbad
  tauto

theorem fin15Anchored_clause20204 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0787 Fin15AnchoredAtom0788 Fin15AnchoredAtom0797
    Fin15AnchoredAtom0807 Fin15AnchoredAtom1793 Fin15AnchoredAtom2794 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13057
  ] at hbad
  tauto

theorem fin15Anchored_clause20205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom0787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0787 Fin15AnchoredAtom2795 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21249
  ] at hbad
  tauto

theorem fin15Anchored_clause20206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom0789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0789 Fin15AnchoredAtom2795 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21249
  ] at hbad
  tauto

theorem fin15Anchored_clause20207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom0798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0798 Fin15AnchoredAtom2795 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21249
  ] at hbad
  tauto

theorem fin15Anchored_clause20208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0808 Fin15AnchoredAtom2795 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21249
  ] at hbad
  tauto

theorem fin15Anchored_clause20209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1794 Fin15AnchoredAtom2795 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21249
  ] at hbad
  tauto

theorem fin15Anchored_clause20210 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0787 Fin15AnchoredAtom0789 Fin15AnchoredAtom0798
    Fin15AnchoredAtom0808 Fin15AnchoredAtom1794 Fin15AnchoredAtom2795 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21249
  ] at hbad
  tauto

theorem fin15Anchored_clause20211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom0788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0788 Fin15AnchoredAtom2796 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25345
  ] at hbad
  tauto

theorem fin15Anchored_clause20212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom0789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0789 Fin15AnchoredAtom2796 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25345
  ] at hbad
  tauto

theorem fin15Anchored_clause20213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom0799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0799 Fin15AnchoredAtom2796 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25345
  ] at hbad
  tauto

theorem fin15Anchored_clause20214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0809 Fin15AnchoredAtom2796 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25345
  ] at hbad
  tauto

theorem fin15Anchored_clause20215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1795 Fin15AnchoredAtom2796 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25345
  ] at hbad
  tauto

theorem fin15Anchored_clause20216 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0788 Fin15AnchoredAtom0789 Fin15AnchoredAtom0799
    Fin15AnchoredAtom0809 Fin15AnchoredAtom1795 Fin15AnchoredAtom2796 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25345
  ] at hbad
  tauto

theorem fin15Anchored_clause20217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom0791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0791 Fin15AnchoredAtom2800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13569
  ] at hbad
  tauto

theorem fin15Anchored_clause20218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0792 Fin15AnchoredAtom2800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13569
  ] at hbad
  tauto

theorem fin15Anchored_clause20219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0797 Fin15AnchoredAtom2800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13569
  ] at hbad
  tauto

theorem fin15Anchored_clause20220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom2800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13569
  ] at hbad
  tauto

theorem fin15Anchored_clause20221 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0791 Fin15AnchoredAtom0792 Fin15AnchoredAtom0797
    Fin15AnchoredAtom0813 Fin15AnchoredAtom1799 Fin15AnchoredAtom2800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13569
  ] at hbad
  tauto

theorem fin15Anchored_clause20222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom0791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0791 Fin15AnchoredAtom2801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21761
  ] at hbad
  tauto

theorem fin15Anchored_clause20223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom0793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0793 Fin15AnchoredAtom2801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21761
  ] at hbad
  tauto

end ErdosSzekeres

end
