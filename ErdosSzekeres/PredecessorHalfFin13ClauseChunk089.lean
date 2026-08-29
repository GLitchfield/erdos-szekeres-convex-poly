module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 089. -/

theorem predecessorHalfFin13_clause24687 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom2256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24688 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom2256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24689 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom2256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24690 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2256 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom0954
    PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom2256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24691 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom2257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5536
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24692 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom2257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5536
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24693 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom2257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5536
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24694 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom2257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5536
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24695 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5536
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24696 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2257 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom0955
    PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5536
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24698 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2258 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom2258 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6560
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24699 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2258 chi ∧
      ¬PredecessorHalfFin13Atom0956 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0956 PredecessorHalfFin13Atom2258 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6560
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24700 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2258 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0962 PredecessorHalfFin13Atom2258 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6560
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24701 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2258 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0992 PredecessorHalfFin13Atom2258 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6560
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24703 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom2259 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24704 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom2259 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24705 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom2259 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24706 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom2259 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24707 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom2259 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24708 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2259 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom0954
    PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom2259 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24709 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom2260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5792
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24710 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom2260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5792
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24711 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom2260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5792
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24712 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom2260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5792
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24713 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5792
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24714 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2260 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom0955
    PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5792
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24716 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2261 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom2261 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24718 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2261 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0965 PredecessorHalfFin13Atom2261 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24719 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2261 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0995 PredecessorHalfFin13Atom2261 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24722 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2262 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom2262 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24724 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2262 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom2262 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24725 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2262 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0996 PredecessorHalfFin13Atom2262 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24726 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2262 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0956 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0956
    PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom0996 PredecessorHalfFin13Atom2262 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24727 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom2263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24728 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom2263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24729 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom2263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24730 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom2263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24731 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0997 PredecessorHalfFin13Atom2263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24732 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2263 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom0960
    PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0997 PredecessorHalfFin13Atom2263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24733 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom2264 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24734 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom2264 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24735 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom2264 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24736 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom2264 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24737 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2264 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24738 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2264 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0961
    PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2264 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24739 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2265 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom2265 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24740 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2265 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom2265 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24742 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2265 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0965 PredecessorHalfFin13Atom2265 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24745 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom2266 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24746 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom2266 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24748 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom2266 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24749 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom1000 PredecessorHalfFin13Atom2266 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24750 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2266 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0962 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0962
    PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom1000 PredecessorHalfFin13Atom2266 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24752 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2267 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom2267 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24754 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2267 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom2267 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24757 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom2268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1984
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24758 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom2268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1984
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24759 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom2268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1984
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24760 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom2268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1984
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24761 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1984
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24762 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2268 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0971
    PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1984
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24763 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom2269 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24764 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom2269 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24765 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom2269 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24766 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom2269 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24767 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom2269 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24768 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2269 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom0972
    PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom2269 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24769 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom2270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5056
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24770 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom2270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5056
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24771 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom2270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5056
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24772 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom2270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5056
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24773 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5056
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24774 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2270 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom0973
    PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5056
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24775 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom2271 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24776 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom2271 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24777 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom2271 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24778 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom2271 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24779 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom2271 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24781 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom2272 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5568
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24782 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom2272 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5568
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24783 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom2272 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5568
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24784 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom2272 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5568
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24785 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2272 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5568
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24786 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2272 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom0975
    PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2272 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5568
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24787 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2273 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom2273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24788 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2273 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom2273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24789 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2273 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0976 PredecessorHalfFin13Atom2273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24790 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2273 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0982 PredecessorHalfFin13Atom2273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24791 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2273 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0992 PredecessorHalfFin13Atom2273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24792 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2273 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0976 chi ∧
      PredecessorHalfFin13Atom0982 chi ∧
      PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom0976
    PredecessorHalfFin13Atom0982 PredecessorHalfFin13Atom0992 PredecessorHalfFin13Atom2273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6592
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24793 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom2274 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24794 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom2274 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24795 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom2274 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24796 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom2274 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24797 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom2274 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24798 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2274 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom0974
    PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom2274 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24799 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom2275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24800 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom2275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24801 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom2275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24802 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom2275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24803 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24804 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2275 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom0975
    PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5824
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24805 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2276 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom2276 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6848
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24807 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2276 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0976 PredecessorHalfFin13Atom2276 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6848
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24808 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2276 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0985 PredecessorHalfFin13Atom2276 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6848
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24809 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2276 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0995 PredecessorHalfFin13Atom2276 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6848
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24810 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2276 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0976 chi ∧
      PredecessorHalfFin13Atom0985 chi ∧
      PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom0976
    PredecessorHalfFin13Atom0985 PredecessorHalfFin13Atom0995 PredecessorHalfFin13Atom2276 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6848
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24811 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2277 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom2277 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7360
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24812 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2277 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom2277 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7360
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24813 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2277 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0976 PredecessorHalfFin13Atom2277 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7360
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24814 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2277 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0986 PredecessorHalfFin13Atom2277 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7360
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24815 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2277 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0996 PredecessorHalfFin13Atom2277 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7360
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24817 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom2278 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24818 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom2278 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24819 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom2278 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24820 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom2278 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24821 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0997 PredecessorHalfFin13Atom2278 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24822 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2278 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom0980
    PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom0997 PredecessorHalfFin13Atom2278 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24823 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom2279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24824 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom2279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24825 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom2279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24826 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom2279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24827 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24828 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2279 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom0981
    PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24829 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2280 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom2280 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24831 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2280 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0982 PredecessorHalfFin13Atom2280 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24832 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2280 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0985 PredecessorHalfFin13Atom2280 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24833 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2280 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0999 PredecessorHalfFin13Atom2280 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6976
  ] at hbad
  tauto

end ErdosSzekeres

end
