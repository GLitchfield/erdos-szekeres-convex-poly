module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 124. -/

theorem fin15Anchored_clause15872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom1912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08267
  ] at hbad
  tauto

theorem fin15Anchored_clause15873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0911 Fin15AnchoredAtom1912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08267
  ] at hbad
  tauto

theorem fin15Anchored_clause15874 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom0477 Fin15AnchoredAtom0504
    Fin15AnchoredAtom0625 Fin15AnchoredAtom0911 Fin15AnchoredAtom1912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08267
  ] at hbad
  tauto

theorem fin15Anchored_clause15875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom1913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16459
  ] at hbad
  tauto

theorem fin15Anchored_clause15876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0478 Fin15AnchoredAtom1913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16459
  ] at hbad
  tauto

theorem fin15Anchored_clause15877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0505 Fin15AnchoredAtom1913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16459
  ] at hbad
  tauto

theorem fin15Anchored_clause15878 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0626 Fin15AnchoredAtom1913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16459
  ] at hbad
  tauto

theorem fin15Anchored_clause15879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0912 Fin15AnchoredAtom1913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16459
  ] at hbad
  tauto

theorem fin15Anchored_clause15880 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom0478 Fin15AnchoredAtom0505
    Fin15AnchoredAtom0626 Fin15AnchoredAtom0912 Fin15AnchoredAtom1913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16459
  ] at hbad
  tauto

theorem fin15Anchored_clause15881 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom1914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00395
  ] at hbad
  tauto

theorem fin15Anchored_clause15882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom1914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00395
  ] at hbad
  tauto

theorem fin15Anchored_clause15883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom0506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom1914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00395
  ] at hbad
  tauto

theorem fin15Anchored_clause15884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom1914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00395
  ] at hbad
  tauto

theorem fin15Anchored_clause15885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1914 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom1914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00395
  ] at hbad
  tauto

theorem fin15Anchored_clause15886 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom0472 Fin15AnchoredAtom0506
    Fin15AnchoredAtom0627 Fin15AnchoredAtom0913 Fin15AnchoredAtom1914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00395
  ] at hbad
  tauto

theorem fin15Anchored_clause15887 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom1915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00651
  ] at hbad
  tauto

theorem fin15Anchored_clause15888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom1915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00651
  ] at hbad
  tauto

theorem fin15Anchored_clause15889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom1915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00651
  ] at hbad
  tauto

theorem fin15Anchored_clause15890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom1915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00651
  ] at hbad
  tauto

theorem fin15Anchored_clause15891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom1915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00651
  ] at hbad
  tauto

theorem fin15Anchored_clause15892 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom0473 Fin15AnchoredAtom0507
    Fin15AnchoredAtom0628 Fin15AnchoredAtom0914 Fin15AnchoredAtom1915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00651
  ] at hbad
  tauto

theorem fin15Anchored_clause15893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom1916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01163
  ] at hbad
  tauto

theorem fin15Anchored_clause15894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom1916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01163
  ] at hbad
  tauto

theorem fin15Anchored_clause15895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom1916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01163
  ] at hbad
  tauto

theorem fin15Anchored_clause15896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom1916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01163
  ] at hbad
  tauto

theorem fin15Anchored_clause15897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom1916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01163
  ] at hbad
  tauto

theorem fin15Anchored_clause15898 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom0474 Fin15AnchoredAtom0508
    Fin15AnchoredAtom0629 Fin15AnchoredAtom0915 Fin15AnchoredAtom1916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01163
  ] at hbad
  tauto

theorem fin15Anchored_clause15899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1917 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom1917 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02187
  ] at hbad
  tauto

theorem fin15Anchored_clause15900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom1918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04235
  ] at hbad
  tauto

theorem fin15Anchored_clause15901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom1918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04235
  ] at hbad
  tauto

theorem fin15Anchored_clause15902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom1918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04235
  ] at hbad
  tauto

theorem fin15Anchored_clause15903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom1918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04235
  ] at hbad
  tauto

theorem fin15Anchored_clause15904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom1918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04235
  ] at hbad
  tauto

theorem fin15Anchored_clause15905 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom0476 Fin15AnchoredAtom0510
    Fin15AnchoredAtom0631 Fin15AnchoredAtom0917 Fin15AnchoredAtom1918 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04235
  ] at hbad
  tauto

theorem fin15Anchored_clause15906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom1919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08331
  ] at hbad
  tauto

theorem fin15Anchored_clause15907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0477 Fin15AnchoredAtom1919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08331
  ] at hbad
  tauto

theorem fin15Anchored_clause15908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom1919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08331
  ] at hbad
  tauto

theorem fin15Anchored_clause15909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom1919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08331
  ] at hbad
  tauto

theorem fin15Anchored_clause15910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom1919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08331
  ] at hbad
  tauto

theorem fin15Anchored_clause15911 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom0477 Fin15AnchoredAtom0511
    Fin15AnchoredAtom0632 Fin15AnchoredAtom0918 Fin15AnchoredAtom1919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08331
  ] at hbad
  tauto

theorem fin15Anchored_clause15912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom1920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16523
  ] at hbad
  tauto

theorem fin15Anchored_clause15913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0478 Fin15AnchoredAtom1920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16523
  ] at hbad
  tauto

theorem fin15Anchored_clause15914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0512 Fin15AnchoredAtom1920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16523
  ] at hbad
  tauto

theorem fin15Anchored_clause15915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0633 Fin15AnchoredAtom1920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16523
  ] at hbad
  tauto

theorem fin15Anchored_clause15916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0919 Fin15AnchoredAtom1920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16523
  ] at hbad
  tauto

theorem fin15Anchored_clause15917 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom0478 Fin15AnchoredAtom0512
    Fin15AnchoredAtom0633 Fin15AnchoredAtom0919 Fin15AnchoredAtom1920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16523
  ] at hbad
  tauto

theorem fin15Anchored_clause15918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom1921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00779
  ] at hbad
  tauto

theorem fin15Anchored_clause15919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom1921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00779
  ] at hbad
  tauto

theorem fin15Anchored_clause15920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom0513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom1921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00779
  ] at hbad
  tauto

theorem fin15Anchored_clause15921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom0634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom1921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00779
  ] at hbad
  tauto

theorem fin15Anchored_clause15922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1921 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom1921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00779
  ] at hbad
  tauto

theorem fin15Anchored_clause15923 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom0473 Fin15AnchoredAtom0513
    Fin15AnchoredAtom0634 Fin15AnchoredAtom0920 Fin15AnchoredAtom1921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00779
  ] at hbad
  tauto

theorem fin15Anchored_clause15924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom1922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01291
  ] at hbad
  tauto

theorem fin15Anchored_clause15925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom1922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01291
  ] at hbad
  tauto

theorem fin15Anchored_clause15926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom0514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0514 Fin15AnchoredAtom1922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01291
  ] at hbad
  tauto

theorem fin15Anchored_clause15927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom1922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01291
  ] at hbad
  tauto

theorem fin15Anchored_clause15928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1922 chi ∧
      ¬Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0921 Fin15AnchoredAtom1922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01291
  ] at hbad
  tauto

theorem fin15Anchored_clause15929 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom0474 Fin15AnchoredAtom0514
    Fin15AnchoredAtom0635 Fin15AnchoredAtom0921 Fin15AnchoredAtom1922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01291
  ] at hbad
  tauto

theorem fin15Anchored_clause15930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom1924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04363
  ] at hbad
  tauto

theorem fin15Anchored_clause15931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom1924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04363
  ] at hbad
  tauto

theorem fin15Anchored_clause15932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom0516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0516 Fin15AnchoredAtom1924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04363
  ] at hbad
  tauto

theorem fin15Anchored_clause15933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom1924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04363
  ] at hbad
  tauto

theorem fin15Anchored_clause15934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1924 chi ∧
      ¬Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0923 Fin15AnchoredAtom1924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04363
  ] at hbad
  tauto

theorem fin15Anchored_clause15935 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom0476 Fin15AnchoredAtom0516
    Fin15AnchoredAtom0637 Fin15AnchoredAtom0923 Fin15AnchoredAtom1924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04363
  ] at hbad
  tauto

theorem fin15Anchored_clause15936 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom1925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08459
  ] at hbad
  tauto

theorem fin15Anchored_clause15937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0477 Fin15AnchoredAtom1925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08459
  ] at hbad
  tauto

theorem fin15Anchored_clause15938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom0517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0517 Fin15AnchoredAtom1925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08459
  ] at hbad
  tauto

theorem fin15Anchored_clause15939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom0638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0638 Fin15AnchoredAtom1925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08459
  ] at hbad
  tauto

theorem fin15Anchored_clause15940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1925 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0924 Fin15AnchoredAtom1925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08459
  ] at hbad
  tauto

theorem fin15Anchored_clause15941 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom0477 Fin15AnchoredAtom0517
    Fin15AnchoredAtom0638 Fin15AnchoredAtom0924 Fin15AnchoredAtom1925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08459
  ] at hbad
  tauto

theorem fin15Anchored_clause15942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom1926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16651
  ] at hbad
  tauto

theorem fin15Anchored_clause15943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0478 Fin15AnchoredAtom1926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16651
  ] at hbad
  tauto

theorem fin15Anchored_clause15944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom0518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0518 Fin15AnchoredAtom1926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16651
  ] at hbad
  tauto

theorem fin15Anchored_clause15945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom0639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0639 Fin15AnchoredAtom1926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16651
  ] at hbad
  tauto

theorem fin15Anchored_clause15946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1926 chi ∧
      ¬Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0925 Fin15AnchoredAtom1926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16651
  ] at hbad
  tauto

theorem fin15Anchored_clause15947 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom0478 Fin15AnchoredAtom0518
    Fin15AnchoredAtom0639 Fin15AnchoredAtom0925 Fin15AnchoredAtom1926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16651
  ] at hbad
  tauto

theorem fin15Anchored_clause15948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom1927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01547
  ] at hbad
  tauto

theorem fin15Anchored_clause15949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom1927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01547
  ] at hbad
  tauto

theorem fin15Anchored_clause15950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom1927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01547
  ] at hbad
  tauto

theorem fin15Anchored_clause15951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom1927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01547
  ] at hbad
  tauto

theorem fin15Anchored_clause15952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom1927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01547
  ] at hbad
  tauto

theorem fin15Anchored_clause15953 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom0474 Fin15AnchoredAtom0519
    Fin15AnchoredAtom0640 Fin15AnchoredAtom0926 Fin15AnchoredAtom1927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01547
  ] at hbad
  tauto

theorem fin15Anchored_clause15954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom1928 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02571
  ] at hbad
  tauto

theorem fin15Anchored_clause15955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom0475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0475 Fin15AnchoredAtom1928 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02571
  ] at hbad
  tauto

theorem fin15Anchored_clause15956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom0520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0520 Fin15AnchoredAtom1928 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02571
  ] at hbad
  tauto

theorem fin15Anchored_clause15957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1928 chi ∧
      ¬Fin15AnchoredAtom0641 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0641 Fin15AnchoredAtom1928 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02571
  ] at hbad
  tauto

theorem fin15Anchored_clause15958 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1928 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0520 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0927 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom0475 Fin15AnchoredAtom0520
    Fin15AnchoredAtom0641 Fin15AnchoredAtom0927 Fin15AnchoredAtom1928 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02571
  ] at hbad
  tauto

theorem fin15Anchored_clause15959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom1929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04619
  ] at hbad
  tauto

theorem fin15Anchored_clause15960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom1929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04619
  ] at hbad
  tauto

theorem fin15Anchored_clause15961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom1929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04619
  ] at hbad
  tauto

theorem fin15Anchored_clause15962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom1929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04619
  ] at hbad
  tauto

theorem fin15Anchored_clause15963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom1929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04619
  ] at hbad
  tauto

theorem fin15Anchored_clause15964 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom0476 Fin15AnchoredAtom0521
    Fin15AnchoredAtom0642 Fin15AnchoredAtom0928 Fin15AnchoredAtom1929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04619
  ] at hbad
  tauto

theorem fin15Anchored_clause15965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom1930 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08715
  ] at hbad
  tauto

theorem fin15Anchored_clause15966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0477 Fin15AnchoredAtom1930 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08715
  ] at hbad
  tauto

theorem fin15Anchored_clause15967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0522 Fin15AnchoredAtom1930 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08715
  ] at hbad
  tauto

theorem fin15Anchored_clause15968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0643 Fin15AnchoredAtom1930 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08715
  ] at hbad
  tauto

theorem fin15Anchored_clause15969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom1930 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08715
  ] at hbad
  tauto

theorem fin15Anchored_clause15970 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom0477 Fin15AnchoredAtom0522
    Fin15AnchoredAtom0643 Fin15AnchoredAtom0929 Fin15AnchoredAtom1930 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08715
  ] at hbad
  tauto

theorem fin15Anchored_clause15971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom1931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16907
  ] at hbad
  tauto

theorem fin15Anchored_clause15972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0478 Fin15AnchoredAtom1931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16907
  ] at hbad
  tauto

theorem fin15Anchored_clause15973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0523 Fin15AnchoredAtom1931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16907
  ] at hbad
  tauto

theorem fin15Anchored_clause15974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0644 Fin15AnchoredAtom1931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16907
  ] at hbad
  tauto

theorem fin15Anchored_clause15975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0930 Fin15AnchoredAtom1931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16907
  ] at hbad
  tauto

theorem fin15Anchored_clause15976 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom0478 Fin15AnchoredAtom0523
    Fin15AnchoredAtom0644 Fin15AnchoredAtom0930 Fin15AnchoredAtom1931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16907
  ] at hbad
  tauto

theorem fin15Anchored_clause15977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom1932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03083
  ] at hbad
  tauto

theorem fin15Anchored_clause15978 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom0475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0475 Fin15AnchoredAtom1932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03083
  ] at hbad
  tauto

theorem fin15Anchored_clause15979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom0524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0524 Fin15AnchoredAtom1932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03083
  ] at hbad
  tauto

theorem fin15Anchored_clause15980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom0645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0645 Fin15AnchoredAtom1932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03083
  ] at hbad
  tauto

theorem fin15Anchored_clause15981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1932 chi ∧
      ¬Fin15AnchoredAtom0931 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0931 Fin15AnchoredAtom1932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03083
  ] at hbad
  tauto

theorem fin15Anchored_clause15982 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1932 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0931 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom0475 Fin15AnchoredAtom0524
    Fin15AnchoredAtom0645 Fin15AnchoredAtom0931 Fin15AnchoredAtom1932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03083
  ] at hbad
  tauto

theorem fin15Anchored_clause15983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom1933 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05131
  ] at hbad
  tauto

theorem fin15Anchored_clause15984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom1933 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05131
  ] at hbad
  tauto

theorem fin15Anchored_clause15985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom1933 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05131
  ] at hbad
  tauto

theorem fin15Anchored_clause15986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom1933 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05131
  ] at hbad
  tauto

theorem fin15Anchored_clause15987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom1933 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05131
  ] at hbad
  tauto

theorem fin15Anchored_clause15988 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom0476 Fin15AnchoredAtom0525
    Fin15AnchoredAtom0646 Fin15AnchoredAtom0932 Fin15AnchoredAtom1933 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05131
  ] at hbad
  tauto

theorem fin15Anchored_clause15989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom1934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09227
  ] at hbad
  tauto

theorem fin15Anchored_clause15990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0477 Fin15AnchoredAtom1934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09227
  ] at hbad
  tauto

theorem fin15Anchored_clause15991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom1934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09227
  ] at hbad
  tauto

theorem fin15Anchored_clause15992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom1934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09227
  ] at hbad
  tauto

theorem fin15Anchored_clause15993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom1934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09227
  ] at hbad
  tauto

theorem fin15Anchored_clause15994 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom0477 Fin15AnchoredAtom0526
    Fin15AnchoredAtom0647 Fin15AnchoredAtom0933 Fin15AnchoredAtom1934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09227
  ] at hbad
  tauto

theorem fin15Anchored_clause15995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom1935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17419
  ] at hbad
  tauto

theorem fin15Anchored_clause15996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0478 Fin15AnchoredAtom1935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17419
  ] at hbad
  tauto

theorem fin15Anchored_clause15997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0527 Fin15AnchoredAtom1935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17419
  ] at hbad
  tauto

theorem fin15Anchored_clause15998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0648 Fin15AnchoredAtom1935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17419
  ] at hbad
  tauto

theorem fin15Anchored_clause15999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0934 Fin15AnchoredAtom1935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17419
  ] at hbad
  tauto

end ErdosSzekeres

end
