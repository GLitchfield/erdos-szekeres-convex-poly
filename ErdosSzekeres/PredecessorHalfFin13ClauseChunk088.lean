module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 088. -/

theorem predecessorHalfFin13_clause24547 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom2233 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0992
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24548 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom2233 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0992
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24549 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom2233 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0992
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24550 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom2233 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0992
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24551 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom2233 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0992
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24552 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2233 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0937
    PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom2233 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0992
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24553 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom2234 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24554 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom2234 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24555 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom2234 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24556 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom2234 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24557 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom2234 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24558 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2234 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0938
    PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom2234 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24559 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom2235 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24560 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0935 PredecessorHalfFin13Atom2235 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24561 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom2235 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24562 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom2235 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24563 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom2235 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24564 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2235 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0935 PredecessorHalfFin13Atom0939
    PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom2235 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24565 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom2236 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4576
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24566 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom2236 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4576
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24567 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom2236 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4576
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24568 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom2236 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4576
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24569 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom2236 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4576
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24570 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2236 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom0940
    PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom2236 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4576
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24571 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom2237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24572 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom2237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24573 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom2237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24574 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom2237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24575 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom2237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24576 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2237 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0941
    PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom2237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24577 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom2238 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2784
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24578 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0935 PredecessorHalfFin13Atom2238 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2784
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24579 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom2238 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2784
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24580 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom2238 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2784
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24581 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom2238 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2784
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24583 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom2239 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24584 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom2239 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24585 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom2239 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24586 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom2239 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24587 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom2239 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24588 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2239 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom0943
    PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom2239 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24589 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom2240 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24590 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0935 PredecessorHalfFin13Atom2240 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24591 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom2240 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24592 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom2240 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24593 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom2240 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24594 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2240 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0935 PredecessorHalfFin13Atom0944
    PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom2240 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24595 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom2241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5344
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24596 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom2241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5344
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24597 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom2241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5344
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24598 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom2241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5344
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24599 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom2241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5344
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24600 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2241 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom0945
    PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom2241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5344
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24601 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0935 PredecessorHalfFin13Atom2242 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24602 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom2242 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24604 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom0956 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0956 PredecessorHalfFin13Atom2242 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24607 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom2243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24608 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom2243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24609 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom2243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24610 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom2243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24611 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom2243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24612 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2243 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0941
    PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom2243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24613 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom2244 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24614 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom2244 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24615 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom2244 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24616 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom2244 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24617 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom2244 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24618 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2244 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom0942
    PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom2244 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24619 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom2245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24620 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom2245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24621 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom2245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24622 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom2245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24623 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom2245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24624 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2245 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom0943
    PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom2245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24625 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom2246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24626 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom2246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24627 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom2246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24628 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom2246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24629 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom2246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24630 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2246 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom0944
    PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom2246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24631 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom2247 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24632 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom2247 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24633 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom2247 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24634 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom2247 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24635 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom2247 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24636 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2247 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom0945
    PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom2247 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24638 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom2248 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6496
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24640 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0962 PredecessorHalfFin13Atom2248 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6496
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24641 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0982 PredecessorHalfFin13Atom2248 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6496
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24643 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom2249 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24644 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom2249 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24645 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom2249 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24646 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom2249 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24647 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom2249 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24648 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2249 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom0944
    PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom2249 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24649 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom2250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24650 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom2250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24651 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom2250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24652 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom2250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24653 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom2250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24654 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2250 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom0945
    PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom2250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24655 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom2251 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6752
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24656 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom2251 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6752
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24658 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0965 PredecessorHalfFin13Atom2251 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6752
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24659 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0985 PredecessorHalfFin13Atom2251 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6752
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24661 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom2252 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24662 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom2252 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24664 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom2252 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24665 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0986 PredecessorHalfFin13Atom2252 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24667 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom2253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24668 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom2253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24669 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom2253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24670 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom2253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24671 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24672 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2253 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0951
    PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24673 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom2254 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24674 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom2254 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24675 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom2254 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24676 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom2254 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24677 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom2254 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24679 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom2255 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5024
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24680 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom2255 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5024
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24681 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom2255 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5024
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24682 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom2255 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5024
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24683 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2255 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5024
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24684 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2255 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom0953
    PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2255 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5024
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24685 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom2256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24686 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom2256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3488
  ] at hbad
  tauto

end ErdosSzekeres

end
