module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 087. -/

theorem predecessorHalfFin13_clause24399 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom2208 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24400 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom2208 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24401 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom2208 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24402 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2208 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0906
    PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom2208 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24403 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom2209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24404 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom2209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24405 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom2209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24406 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom2209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24407 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom2209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24408 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2209 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom0907
    PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom2209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24409 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom2210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24410 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom2210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24411 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom2210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24412 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom2210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24413 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom2210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24414 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2210 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0908
    PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom2210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24415 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom2211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24416 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom2211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24417 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom2211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24418 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom2211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24419 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom2211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24420 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2211 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom0909
    PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom2211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24421 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom2212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24422 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom2212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24423 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom2212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24424 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom2212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24425 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom2212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24426 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2212 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0910
    PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom2212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24427 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom2213 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24428 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom2213 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24431 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0982 PredecessorHalfFin13Atom2213 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24433 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom2214 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24434 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom2214 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24435 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom2214 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24436 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom2214 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24437 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom2214 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24438 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2214 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom0909
    PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom2214 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24439 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom2215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24440 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom2215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24441 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom2215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24442 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom2215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24443 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom2215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24444 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2215 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0910
    PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom2215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24446 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom2216 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24448 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom2216 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24449 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0985 PredecessorHalfFin13Atom2216 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24451 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom2217 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24452 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom2217 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24454 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom2217 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24455 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0986 PredecessorHalfFin13Atom2217 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24457 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom2218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24458 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom2218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24459 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom2218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24460 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom2218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24461 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24462 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2218 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0916
    PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24463 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom2219 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24464 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom2219 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24465 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom2219 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24466 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom2219 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24467 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom2219 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24468 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2219 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0917
    PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom2219 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2960
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24469 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom2220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24470 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom2220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24471 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom2220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24472 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom2220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24473 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24474 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2220 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0918
    PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5008
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24475 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom2221 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24476 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom2221 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24477 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom2221 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24478 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom2221 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24479 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom2221 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24481 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom2222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24482 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom2222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24483 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom2222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24484 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom2222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24485 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24486 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2222 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0920
    PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24487 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom2223 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6544
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24488 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom2223 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6544
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24490 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0927 PredecessorHalfFin13Atom2223 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6544
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24491 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0992 PredecessorHalfFin13Atom2223 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6544
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24493 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom2224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24494 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom2224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24495 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom2224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24496 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom2224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24497 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom2224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24498 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2224 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0919
    PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom2224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24499 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom2225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24500 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom2225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24501 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom2225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24502 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom2225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24503 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24504 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2225 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0920
    PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24505 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom2226 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6800
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24506 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom2226 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6800
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24507 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom2226 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6800
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24508 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom2226 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6800
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24509 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0995 PredecessorHalfFin13Atom2226 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6800
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24510 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2226 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0921
    PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom0995 PredecessorHalfFin13Atom2226 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6800
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24512 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom2227 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24513 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom2227 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24514 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom2227 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24515 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0996 PredecessorHalfFin13Atom2227 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24517 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom2228 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24518 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom2228 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24519 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom2228 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24520 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom2228 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24521 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0997 PredecessorHalfFin13Atom2228 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24523 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom2229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24524 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom2229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24525 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom2229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24526 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom2229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24527 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24528 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2229 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0926
    PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24529 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom2230 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6928
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24530 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom2230 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6928
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24532 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom2230 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6928
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24533 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0999 PredecessorHalfFin13Atom2230 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6928
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24535 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom2231 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24536 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom2231 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24538 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom2231 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24539 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom1000 PredecessorHalfFin13Atom2231 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24541 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom2232 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24542 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom2232 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24543 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom2232 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24544 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom2232 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7696
  ] at hbad
  tauto

end ErdosSzekeres

end
