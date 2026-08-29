module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 093. -/

theorem predecessorHalfFin13_clause26290 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0959 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26291 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0713
    PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom0754
    PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0889
    PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0960 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26292 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0961 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26295 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0893
    PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0964 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26298 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0717
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0726
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0762
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0898
    PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0967 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26299 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0718
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0727
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0763
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0899
    PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0968 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26301 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0765
    PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0901
    PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0970 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26302 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0718
    PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0766
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0899
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0971 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26303 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0760 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 7, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 7, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0719
    PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom0731
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom0767
    PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0900
    PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0972 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26304 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0768
    PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0901
    PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0973 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26306 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0901
    PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0975 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26308 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0718
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0766
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0903
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0977 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26309 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0764 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0719
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom0731
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0764 PredecessorHalfFin13Atom0767
    PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0904
    PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0978 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26310 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0768
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0905
    PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0979 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26311 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0764 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0719
    PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0764 PredecessorHalfFin13Atom0769
    PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0904
    PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0980 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26312 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0905
    PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0981 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26314 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0719
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom0769
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0907
    PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0983 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26315 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0908
    PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0984 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26316 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0735 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0771 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0911 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 6, 9, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 9, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0735
    PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0771
    PredecessorHalfFin13Atom0790 PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom0908
    PredecessorHalfFin13Atom0911 PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom0985 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26318 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0723
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0776
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0913
    PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26319 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 7, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 7, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0724
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom0731
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom0777
    PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0914
    PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0988 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26320 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0778
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0915
    PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26321 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 7, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 7, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0724
    PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom0779
    PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0914
    PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0990 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26322 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0780
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0915
    PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26325 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0780
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0918
    PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26326 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0735 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0781 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 7, 9, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 7, 9, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0735
    PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0781
    PredecessorHalfFin13Atom0790 PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0918
    PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom0995 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26328 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0728
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0785
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0923
    PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26329 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0786
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0924
    PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26330 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0735 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0787 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0927 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 8, 9, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 8, 9, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0735
    PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0787
    PredecessorHalfFin13Atom0790 PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0924
    PredecessorHalfFin13Atom0927 PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom0999 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26332 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0735 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0791 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0931 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 9, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 9, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0733 PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom0735
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0790
    PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0929
    PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom1001 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26333 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0738
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0747
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0762
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0933
    PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0967 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26334 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0739
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0748
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0763
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0934
    PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0968 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26336 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0741
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0750
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0765
    PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom0970 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26337 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0739
    PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0766
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0934
    PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0971 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26339 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0741
    PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0768
    PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom0973 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26340 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0740 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0760 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 7, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 7, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0740
    PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom0754
    PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom0769
    PredecessorHalfFin13Atom0779 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0935
    PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom0974 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26341 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0741
    PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0975 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26343 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0739
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0766
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0938
    PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0977 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26345 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0741
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0768
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0940
    PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0979 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26347 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0741
    PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0940
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0981 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26350 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0741
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0943
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0984 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26351 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0740 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0756 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0771 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0946 chi ∧
      PredecessorHalfFin13Atom0965 chi ∧
      PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 6, 9, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 6, 9, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom0741
    PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0756
    PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0771
    PredecessorHalfFin13Atom0790 PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom0943
    PredecessorHalfFin13Atom0946 PredecessorHalfFin13Atom0965 PredecessorHalfFin13Atom0985 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26353 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0744
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0776
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0948
    PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26355 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0746
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0778
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0950
    PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26357 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0746
    PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0780
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0950
    PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26359 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 7, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 7, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0745
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom0754
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom0779
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0952
    PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0993 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26360 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0746
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0780
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0953
    PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26363 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0749
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom0754
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0785
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0958
    PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26364 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0750
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0786
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0959
    PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26366 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0756 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0787 chi ∧
      PredecessorHalfFin13Atom0791 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0962 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 8, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 8, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom0750
    PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom0756
    PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0787
    PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0961
    PredecessorHalfFin13Atom0962 PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom1000 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26367 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0756 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0791 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0965 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 5, 9, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 5, 9, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom0756
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0790
    PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0964
    PredecessorHalfFin13Atom0965 PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom1001 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26368 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 6, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 6, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0759
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0766
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0776
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0968
    PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26370 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 6, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 6, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0761
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0768
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0778
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26372 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 6, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 6, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0761
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0780
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26375 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 6, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 6, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0761
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0780
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0973
    PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26378 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0764 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 6, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 6, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0764
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom0769
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0785
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0978
    PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26379 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 6, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 6, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0765
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0786
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0979
    PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26383 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0988 chi ∧
      PredecessorHalfFin13Atom0990 chi ∧
      PredecessorHalfFin13Atom0993 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 7, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 7, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0774
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom0779
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0785
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom0988
    PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26384 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 7, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 7, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0775
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0780
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0786
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom0989
    PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26386 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0781 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0787 chi ∧
      PredecessorHalfFin13Atom0791 chi ∧
      PredecessorHalfFin13Atom0990 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0992 chi ∧
      PredecessorHalfFin13Atom0996 chi ∧
      PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 7, 8, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 7, 8, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom0775
    PredecessorHalfFin13Atom0779 PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0781
    PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0787
    PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom0991
    PredecessorHalfFin13Atom0992 PredecessorHalfFin13Atom0996 PredecessorHalfFin13Atom1000 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26389 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0794
    PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0805
    PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0826
    PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0877
    PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0932 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26390 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0795
    PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0806
    PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0827
    PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0878
    PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0933 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26391 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0807
    PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0828
    PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0879
    PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0934 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26393 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom0936 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26394 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0795
    PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0810
    PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0831
    PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0878
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0937 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26395 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0811
    PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0832
    PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0879
    PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0938 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26397 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom0813
    PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom0834
    PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0940 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26398 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0814
    PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0835
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0879
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0941 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26399 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom0815
    PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom0836
    PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0880
    PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom0942 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26400 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0943 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26401 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom0817
    PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0880
    PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom0944 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26402 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 6, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0945 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26404 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0795
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0810
    PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0831
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0883
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0947 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26405 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0811
    PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0832
    PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0884
    PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0948 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26406 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 7, 8, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 7, 8, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0812
    PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0833
    PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0885
    PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0949 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26407 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0813
    PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0834
    PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0950 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26408 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0814
    PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0835
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0884
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0951 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26409 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0952 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 7, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 7, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0815
    PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0836
    PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0885
    PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0952 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26410 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0953 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26411 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0954 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 7, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 7, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0817
    PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0885
    PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom0954 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26412 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0955 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26413 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0840 chi ∧
      PredecessorHalfFin13Atom0865 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0956 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 7, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 7, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0797 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0819
    PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0840
    PredecessorHalfFin13Atom0865 PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0896 PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom0956 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26414 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0814
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0835
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0888
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0957 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26415 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0815
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom0836
    PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0889
    PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0958 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26416 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0959 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26417 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0817
    PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0889
    PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0960 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26418 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0961 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26419 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0840 chi ∧
      PredecessorHalfFin13Atom0871 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0927 chi ∧
      PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 8, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 8, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0797 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0819
    PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0840
    PredecessorHalfFin13Atom0871 PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0896 PredecessorHalfFin13Atom0927 PredecessorHalfFin13Atom0962 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26420 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom0817
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0892
    PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0963 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26421 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 5, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0893
    PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0964 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26424 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0801
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0810
    PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0846
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0898
    PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0967 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26425 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0802
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0811
    PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0847
    PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0899
    PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0968 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26426 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 7, 8, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 7, 8, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0803
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0812
    PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom0848
    PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0900
    PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0969 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26427 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0813
    PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0849
    PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0901
    PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0970 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26428 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0802
    PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0814
    PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0850
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0899
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0971 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26429 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 7, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 7, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0803
    PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0815
    PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom0851
    PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0900
    PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0972 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26430 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0852
    PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0901
    PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0973 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26431 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 7, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 7, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0803
    PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0817
    PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom0853
    PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0900
    PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom0974 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26432 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0901
    PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0975 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26434 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0802
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0814
    PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0850
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0903
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0977 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26435 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0803
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0815
    PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom0851
    PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0904
    PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0978 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26436 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0852
    PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0905
    PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0979 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26437 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0803
    PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0817
    PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom0853
    PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0904
    PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0980 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26438 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0905
    PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0981 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26440 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0803
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom0817
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom0853
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0907
    PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0983 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26441 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0908
    PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0984 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26442 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0855 chi ∧
      PredecessorHalfFin13Atom0874 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0911 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 9, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 9, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0819
    PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0855
    PredecessorHalfFin13Atom0874 PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom0908
    PredecessorHalfFin13Atom0911 PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom0985 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26443 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0855 chi ∧
      PredecessorHalfFin13Atom0875 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0911 chi ∧
      PredecessorHalfFin13Atom0931 chi ∧
      PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 6, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 6, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0819
    PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0855
    PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom0910
    PredecessorHalfFin13Atom0911 PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom0986 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26444 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0807
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0814
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0860
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0913
    PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26445 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 7, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 7, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0808
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0815
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0861
    PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0914
    PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0988 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26446 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0862
    PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0915
    PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26448 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0864
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0915
    PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26449 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0865 chi ∧
      PredecessorHalfFin13Atom0871 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0927 chi ∧
      PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 7, 8, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 7, 8, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0819
    PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0865
    PredecessorHalfFin13Atom0871 PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0915
    PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom0927 PredecessorHalfFin13Atom0992 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26450 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 7, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 7, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0808
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom0817
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0863
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0917
    PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0993 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26451 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0864
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0918
    PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26452 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0865 chi ∧
      PredecessorHalfFin13Atom0874 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 7, 9, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 7, 9, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0819
    PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0865
    PredecessorHalfFin13Atom0874 PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0918
    PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom0995 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26453 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0865 chi ∧
      PredecessorHalfFin13Atom0875 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0931 chi ∧
      PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 7, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 7, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0819
    PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0865
    PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom0920
    PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom0996 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26455 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0813
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0870
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0924
    PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26458 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0874 chi ∧
      PredecessorHalfFin13Atom0875 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0931 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 4, 9, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 9, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0819
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0874
    PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0929
    PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom1001 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26459 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0822
    PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0831
    PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0846
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0933
    PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0967 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26460 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0823
    PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0832
    PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0847
    PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0934
    PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0968 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26461 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 7, 8, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 7, 8, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0824
    PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0833
    PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom0848
    PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0935
    PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom0969 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26462 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0834
    PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0849
    PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom0970 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26463 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0823
    PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0835
    PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0850
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0934
    PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0971 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26464 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 7, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 7, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0824
    PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0836
    PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom0851
    PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0935
    PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom0972 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26465 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0852
    PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom0973 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26466 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 7, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 7, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0824
    PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom0853
    PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0935
    PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom0974 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26467 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0975 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
