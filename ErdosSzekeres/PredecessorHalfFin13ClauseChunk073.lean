module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 073. -/

theorem predecessorHalfFin13_clause22441 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom1882 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1356
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22442 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom1882 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1356
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22443 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom1882 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1356
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22444 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom1882 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1356
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22445 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom1882 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1356
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22446 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1882 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0699
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom1882 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1356
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22447 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom1883 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22448 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0691 PredecessorHalfFin13Atom1883 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22449 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0700 PredecessorHalfFin13Atom1883 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22450 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0764 PredecessorHalfFin13Atom1883 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22451 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom1883 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22453 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom1884 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22454 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom1884 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22455 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom1884 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22456 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom1884 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22457 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom1884 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22458 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1884 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom1884 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22459 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom1885 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22460 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom1885 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22461 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom1885 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22462 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom1885 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22463 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom1885 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22464 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1885 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom1885 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22465 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom1886 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22466 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0691 PredecessorHalfFin13Atom1886 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22467 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0703 PredecessorHalfFin13Atom1886 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22468 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom1886 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22469 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom1886 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22470 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1886 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0691 PredecessorHalfFin13Atom0703
    PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom1886 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22471 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom1887 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22472 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom1887 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22473 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom1887 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22474 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom1887 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22475 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom1887 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22476 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1887 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom1887 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22477 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom1888 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3148
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22478 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0691 PredecessorHalfFin13Atom1888 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3148
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22479 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0705 PredecessorHalfFin13Atom1888 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3148
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22480 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0769 PredecessorHalfFin13Atom1888 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3148
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22481 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom1888 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3148
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22483 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom1889 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22484 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom1889 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22485 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom1889 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22486 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom1889 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22487 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom1889 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22488 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1889 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0854 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom1889 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22490 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom1890 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22491 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom0707 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0707 PredecessorHalfFin13Atom1890 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22492 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom0771 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0771 PredecessorHalfFin13Atom1890 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22493 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom0855 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0855 PredecessorHalfFin13Atom1890 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22495 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom1891 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0908
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22496 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom1891 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0908
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22497 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom1891 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0908
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22498 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom1891 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0908
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22499 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom1891 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0908
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22500 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1891 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0856 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0698
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom1891 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0908
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22501 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom1892 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1420
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22502 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom1892 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1420
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22503 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom1892 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1420
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22504 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom1892 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1420
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22505 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom1892 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1420
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22506 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1892 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0857 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0699
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom1892 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1420
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22507 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom1893 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22508 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom1893 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22510 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom1893 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22511 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom1893 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22513 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom1894 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4492
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22514 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom1894 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4492
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22515 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom1894 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4492
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22516 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom1894 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4492
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22517 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom1894 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4492
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22518 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1894 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0859 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom1894 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4492
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22519 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom1895 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1676
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22520 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom1895 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1676
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22521 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom1895 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1676
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22522 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom1895 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1676
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22523 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom1895 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1676
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22524 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1895 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0860 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom1895 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1676
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22525 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom1896 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22527 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0703 PredecessorHalfFin13Atom1896 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22528 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom1896 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22529 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom1896 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22531 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom1897 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4748
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22532 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom1897 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4748
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22533 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom1897 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4748
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22534 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom1897 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4748
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22535 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom1897 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4748
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22536 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1897 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom1897 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4748
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22537 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom1898 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3212
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22538 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom1898 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3212
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22540 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0779 PredecessorHalfFin13Atom1898 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3212
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22541 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom1898 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3212
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22543 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom1899 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22544 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom1899 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22545 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom1899 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22546 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom1899 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22547 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom1899 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22548 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1899 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom1899 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22550 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom1900 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6284
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22551 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom0707 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0707 PredecessorHalfFin13Atom1900 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6284
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22552 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0781 PredecessorHalfFin13Atom1900 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6284
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22553 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0865 PredecessorHalfFin13Atom1900 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6284
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22555 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom1901 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22556 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom1901 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22557 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom1901 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22558 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom1901 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22559 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom1901 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22560 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1901 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom1901 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1804
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22561 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom1902 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2828
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22562 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0700 PredecessorHalfFin13Atom1902 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2828
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22563 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0703 PredecessorHalfFin13Atom1902 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2828
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22564 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom1902 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2828
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22565 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom1902 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2828
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22567 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom1903 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4876
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22568 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom1903 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4876
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22569 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom1903 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4876
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22570 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom1903 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4876
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22571 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom1903 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4876
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22572 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1903 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom1903 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4876
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22573 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom1904 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3340
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22574 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0700 PredecessorHalfFin13Atom1904 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3340
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22575 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0705 PredecessorHalfFin13Atom1904 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3340
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22576 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom1904 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3340
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22577 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom1904 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3340
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22579 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom1905 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5388
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22580 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom1905 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5388
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22581 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom1905 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5388
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22582 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom1905 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5388
  ] at hbad
  tauto

end ErdosSzekeres

end
