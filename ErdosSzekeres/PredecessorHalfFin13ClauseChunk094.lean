module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 094. -/

theorem predecessorHalfFin13_clause26469 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0823
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0835
    PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0850
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0938
    PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0977 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26471 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0852
    PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0940
    PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0979 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26472 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0824
    PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom0853
    PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0939
    PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0980 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26473 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0940
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0981 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26475 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0824
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom0853
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0942
    PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0983 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26476 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 6, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 6, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0943
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0984 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26479 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0828
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0835
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0860
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0948
    PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26480 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 7, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 7, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0829
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom0836
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0861
    PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0949
    PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom0988 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26481 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0862
    PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0950
    PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26482 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 7, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 7, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0829
    PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0863
    PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0949
    PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0990 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26483 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0864
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0950
    PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26485 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 7, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 7, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0829
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0863
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0952
    PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0993 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26486 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0864
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0953
    PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26488 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0840 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0865 chi ∧
      PredecessorHalfFin13Atom0875 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0956 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 7, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 7, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0840
    PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0865
    PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom0955
    PredecessorHalfFin13Atom0956 PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom0996 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26489 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0833
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0869
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0958
    PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26490 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0834
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0870
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0959
    PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26493 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0840 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0874 chi ∧
      PredecessorHalfFin13Atom0875 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0965 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 5, 9, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 5, 9, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0840
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0874
    PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0964
    PredecessorHalfFin13Atom0965 PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom1001 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26494 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 6, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{3, 6, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0843
    PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0850
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0860
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0968
    PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26496 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 6, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 6, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0845
    PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0852
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0862
    PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26498 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 6, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 6, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0845
    PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0864
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26501 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 6, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 6, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0845
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0864
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0973
    PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26503 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0855 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0865 chi ∧
      PredecessorHalfFin13Atom0875 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0976 chi ∧
      PredecessorHalfFin13Atom0986 chi ∧
      PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 6, 7, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 6, 7, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom0845
    PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0855
    PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0865
    PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom0975
    PredecessorHalfFin13Atom0976 PredecessorHalfFin13Atom0986 PredecessorHalfFin13Atom0996 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26504 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 6, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{3, 6, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0848
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom0853
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0869
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0978
    PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26505 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 6, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 6, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0849
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0870
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0979
    PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26510 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {3, 7, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{3, 7, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0859
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0864
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0870
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom0989
    PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26515 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0878
    PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0887
    PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0902
    PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0933
    PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0967 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26516 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0879
    PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0888
    PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0903
    PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0934
    PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0968 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26517 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 7, 8, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 7, 8, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0880
    PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom0889
    PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom0904
    PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0935
    PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom0969 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26518 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom0905
    PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom0970 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26519 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0879
    PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0891
    PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0906
    PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0934
    PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0971 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26520 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 7, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 7, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0880
    PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom0892
    PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom0907
    PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0935
    PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom0972 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26521 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom0893
    PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom0908
    PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom0973 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26523 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom0895
    PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom0910
    PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0975 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26525 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0879
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0891
    PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0906
    PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0938
    PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0977 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26526 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0880
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0892
    PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom0907
    PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0939
    PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom0978 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26527 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0893
    PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0908
    PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0940
    PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0979 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26528 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0880
    PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0894
    PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom0909
    PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0939
    PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0980 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26529 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0895
    PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0910
    PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0940
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0981 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26530 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0911 chi ∧
      PredecessorHalfFin13Atom0927 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0946 chi ∧
      PredecessorHalfFin13Atom0962 chi ∧
      PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 8, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 8, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0896
    PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0911
    PredecessorHalfFin13Atom0927 PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom0940
    PredecessorHalfFin13Atom0946 PredecessorHalfFin13Atom0962 PredecessorHalfFin13Atom0982 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26531 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0880
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom0894
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom0909
    PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0942
    PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0983 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26532 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0895
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0910
    PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0943
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0984 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26534 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0911 chi ∧
      PredecessorHalfFin13Atom0931 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0946 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 6, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 6, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0896
    PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0911
    PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom0945
    PredecessorHalfFin13Atom0946 PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom0986 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26535 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0884
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0891
    PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0916
    PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0948
    PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26536 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 7, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 7, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0885
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0892
    PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0917
    PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0949
    PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom0988 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26537 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0893
    PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0918
    PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0950
    PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26538 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 7, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 7, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0885
    PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0894
    PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0919
    PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0949
    PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0990 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26539 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0895
    PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0920
    PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0950
    PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26540 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0927 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0956 chi ∧
      PredecessorHalfFin13Atom0962 chi ∧
      PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 7, 8, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 7, 8, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0896
    PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0921
    PredecessorHalfFin13Atom0927 PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom0950
    PredecessorHalfFin13Atom0956 PredecessorHalfFin13Atom0962 PredecessorHalfFin13Atom0992 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26541 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 7, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 7, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0885
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom0894
    PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0919
    PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0952
    PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0993 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26542 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0895
    PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0920
    PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0953
    PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26543 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0956 chi ∧
      PredecessorHalfFin13Atom0965 chi ∧
      PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 7, 9, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 7, 9, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0896
    PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0921
    PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom0953
    PredecessorHalfFin13Atom0956 PredecessorHalfFin13Atom0965 PredecessorHalfFin13Atom0995 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26544 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0931 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0956 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 7, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 7, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0896
    PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0921
    PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom0955
    PredecessorHalfFin13Atom0956 PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom0996 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26545 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0889
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom0894
    PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0925
    PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0958
    PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26546 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0895
    PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0926
    PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0959
    PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26548 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0927 chi ∧
      PredecessorHalfFin13Atom0931 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0962 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 5, 8, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 5, 8, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0896
    PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0927
    PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0961
    PredecessorHalfFin13Atom0962 PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom1000 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26550 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 6, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{4, 6, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0899
    PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0906
    PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0916
    PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0968
    PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26551 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 6, 7, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 6, 7, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0900
    PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom0907
    PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0917
    PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0969
    PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom0988 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26552 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 6, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 6, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0901
    PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0908
    PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0918
    PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26553 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 6, 7, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 6, 7, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0900
    PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom0909
    PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0919
    PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0969
    PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom0990 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26554 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 6, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 6, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0901
    PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0910
    PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0920
    PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26557 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 6, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 6, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0901
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0910
    PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0920
    PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0973
    PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26560 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 6, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{4, 6, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0904
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom0909
    PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0925
    PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0978
    PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26561 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 6, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 6, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0905
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0910
    PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0926
    PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0979
    PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26566 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {4, 7, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{4, 7, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0915
    PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0920
    PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0926
    PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom0989
    PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26571 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {5, 6, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{5, 6, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0934
    PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0941
    PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0951
    PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0968
    PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26573 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {5, 6, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{5, 6, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom0943
    PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom0953
    PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26574 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {5, 6, 7, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{5, 6, 7, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0935
    PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom0944
    PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom0954
    PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0969
    PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom0990 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26575 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {5, 6, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{5, 6, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom0945
    PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom0955
    PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26577 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {5, 6, 7, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{5, 6, 7, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0935
    PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom0944
    PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom0954
    PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0972
    PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom0993 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26578 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {5, 6, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{5, 6, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom0945
    PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom0955
    PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0973
    PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26581 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {5, 6, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{5, 6, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0939
    PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom0944
    PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom0960
    PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0978
    PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26582 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {5, 6, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{5, 6, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0940
    PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom0945
    PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0961
    PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0979
    PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26586 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0988 chi ∧
      PredecessorHalfFin13Atom0990 chi ∧
      PredecessorHalfFin13Atom0993 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {5, 7, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{5, 7, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0949
    PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom0954
    PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom0960
    PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom0988
    PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26587 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {5, 7, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{5, 7, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0950
    PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom0955
    PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0961
    PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom0989
    PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26592 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0988 chi ∧
      PredecessorHalfFin13Atom0990 chi ∧
      PredecessorHalfFin13Atom0993 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {6, 7, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{6, 7, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0969
    PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom0974
    PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom0980
    PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom0988
    PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26593 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {6, 7, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{6, 7, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom0975
    PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom0981
    PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom0989
    PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26594 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0976 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0982 chi ∧
      PredecessorHalfFin13Atom0985 chi ∧
      PredecessorHalfFin13Atom0988 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0992 chi ∧
      PredecessorHalfFin13Atom0995 chi ∧
      PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {6, 7, 8, 9, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{6, 7, 8, 9, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom0976
    PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom0982
    PredecessorHalfFin13Atom0985 PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom0989
    PredecessorHalfFin13Atom0992 PredecessorHalfFin13Atom0995 PredecessorHalfFin13Atom0999 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26595 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0976 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0982 chi ∧
      PredecessorHalfFin13Atom0986 chi ∧
      PredecessorHalfFin13Atom0990 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0992 chi ∧
      PredecessorHalfFin13Atom0996 chi ∧
      PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {6, 7, 8, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{6, 7, 8, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0976
    PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0982
    PredecessorHalfFin13Atom0986 PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom0991
    PredecessorHalfFin13Atom0992 PredecessorHalfFin13Atom0996 PredecessorHalfFin13Atom1000 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26596 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0976 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0985 chi ∧
      PredecessorHalfFin13Atom0986 chi ∧
      PredecessorHalfFin13Atom0993 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0995 chi ∧
      PredecessorHalfFin13Atom0996 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {6, 7, 9, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{6, 7, 9, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom0973
    PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0976
    PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0985
    PredecessorHalfFin13Atom0986 PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom0994
    PredecessorHalfFin13Atom0995 PredecessorHalfFin13Atom0996 PredecessorHalfFin13Atom1001 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause27061 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 7}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0253
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1169
    PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1182
    PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1210
    PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1288
    PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1371
    PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1834
    PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom2037 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27062 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 8}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0381
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1170
    PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1183
    PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1211
    PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1289
    PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1372
    PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1835
    PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom2038 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27063 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0637
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1171
    PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1184
    PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1212
    PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1290
    PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1373
    PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1836
    PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom2039 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27064 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1149
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1172
    PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1179 PredecessorHalfFin13Atom1185
    PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1207 PredecessorHalfFin13Atom1213
    PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1291
    PredecessorHalfFin13Atom1297 PredecessorHalfFin13Atom1318 PredecessorHalfFin13Atom1374
    PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1837
    PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom2040 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27066 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 6, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4221
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1181 PredecessorHalfFin13Atom1187
    PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1209 PredecessorHalfFin13Atom1215
    PredecessorHalfFin13Atom1236 PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1299 PredecessorHalfFin13Atom1320 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1833 PredecessorHalfFin13Atom1839
    PredecessorHalfFin13Atom1860 PredecessorHalfFin13Atom1916 PredecessorHalfFin13Atom2042 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27067 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 8}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0445
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1170
    PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1188
    PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1216
    PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1289
    PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1377
    PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1840
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom2043 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27068 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0701
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1171
    PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1189
    PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1217
    PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1290
    PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1378
    PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1841
    PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom2044 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27069 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1213
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1172
    PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1179 PredecessorHalfFin13Atom1190
    PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1207 PredecessorHalfFin13Atom1218
    PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1291
    PredecessorHalfFin13Atom1302 PredecessorHalfFin13Atom1323 PredecessorHalfFin13Atom1379
    PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1842
    PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom2045 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27071 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4285
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1181 PredecessorHalfFin13Atom1192
    PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1209 PredecessorHalfFin13Atom1220
    PredecessorHalfFin13Atom1241 PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1304 PredecessorHalfFin13Atom1325 PredecessorHalfFin13Atom1381
    PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1833 PredecessorHalfFin13Atom1844
    PredecessorHalfFin13Atom1865 PredecessorHalfFin13Atom1921 PredecessorHalfFin13Atom2047 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27072 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0829
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1171
    PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1193
    PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1221
    PredecessorHalfFin13Atom1242 PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1290
    PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1382
    PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1845
    PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom2048 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27073 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1341
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1172
    PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1179 PredecessorHalfFin13Atom1194
    PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1207 PredecessorHalfFin13Atom1222
    PredecessorHalfFin13Atom1243 PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1291
    PredecessorHalfFin13Atom1306 PredecessorHalfFin13Atom1327 PredecessorHalfFin13Atom1383
    PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1846
    PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom2049 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27075 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4413
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1181 PredecessorHalfFin13Atom1196
    PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1209 PredecessorHalfFin13Atom1224
    PredecessorHalfFin13Atom1245 PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1308 PredecessorHalfFin13Atom1329 PredecessorHalfFin13Atom1385
    PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1833 PredecessorHalfFin13Atom1848
    PredecessorHalfFin13Atom1869 PredecessorHalfFin13Atom1925 PredecessorHalfFin13Atom2051 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27076 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1597
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1171 PredecessorHalfFin13Atom1172
    PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1179 PredecessorHalfFin13Atom1197
    PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1207 PredecessorHalfFin13Atom1225
    PredecessorHalfFin13Atom1246 PredecessorHalfFin13Atom1290 PredecessorHalfFin13Atom1291
    PredecessorHalfFin13Atom1309 PredecessorHalfFin13Atom1330 PredecessorHalfFin13Atom1386
    PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1849
    PredecessorHalfFin13Atom1870 PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom2052 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27078 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4669
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1171 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1181 PredecessorHalfFin13Atom1199
    PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1209 PredecessorHalfFin13Atom1227
    PredecessorHalfFin13Atom1248 PredecessorHalfFin13Atom1290 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1311 PredecessorHalfFin13Atom1332 PredecessorHalfFin13Atom1388
    PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1833 PredecessorHalfFin13Atom1851
    PredecessorHalfFin13Atom1872 PredecessorHalfFin13Atom1928 PredecessorHalfFin13Atom2054 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27080 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 5, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5181
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1167 PredecessorHalfFin13Atom1172 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1179 PredecessorHalfFin13Atom1181 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1207 PredecessorHalfFin13Atom1209 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1250 PredecessorHalfFin13Atom1291 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1313 PredecessorHalfFin13Atom1334 PredecessorHalfFin13Atom1390
    PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1833 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1874 PredecessorHalfFin13Atom1930 PredecessorHalfFin13Atom2056 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27082 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 8}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0477
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1170
    PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1188
    PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1216
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1295
    PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1392
    PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1840
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom2058 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27083 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0733
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1171
    PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1189
    PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1217
    PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1296
    PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1393
    PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1841
    PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom2059 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27084 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1245
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1172
    PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1185 PredecessorHalfFin13Atom1190
    PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1213 PredecessorHalfFin13Atom1218
    PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1297
    PredecessorHalfFin13Atom1302 PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1394
    PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1842
    PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom2060 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27086 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4317
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1187 PredecessorHalfFin13Atom1192
    PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1215 PredecessorHalfFin13Atom1220
    PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1299
    PredecessorHalfFin13Atom1304 PredecessorHalfFin13Atom1340 PredecessorHalfFin13Atom1396
    PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1839 PredecessorHalfFin13Atom1844
    PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1936 PredecessorHalfFin13Atom2062 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27087 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0861
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1171
    PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1193
    PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1221
    PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1296
    PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1397
    PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1845
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom2063 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27088 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1373
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1172
    PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1185 PredecessorHalfFin13Atom1194
    PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1213 PredecessorHalfFin13Atom1222
    PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1297
    PredecessorHalfFin13Atom1306 PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1398
    PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1846
    PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom2064 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27090 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4445
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1187 PredecessorHalfFin13Atom1196
    PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1215 PredecessorHalfFin13Atom1224
    PredecessorHalfFin13Atom1260 PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1299
    PredecessorHalfFin13Atom1308 PredecessorHalfFin13Atom1344 PredecessorHalfFin13Atom1400
    PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1839 PredecessorHalfFin13Atom1848
    PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom2066 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27091 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1629
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1171 PredecessorHalfFin13Atom1172
    PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1185 PredecessorHalfFin13Atom1197
    PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1213 PredecessorHalfFin13Atom1225
    PredecessorHalfFin13Atom1261 PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1297
    PredecessorHalfFin13Atom1309 PredecessorHalfFin13Atom1345 PredecessorHalfFin13Atom1401
    PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1849
    PredecessorHalfFin13Atom1885 PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom2067 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27093 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4701
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1171 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1187 PredecessorHalfFin13Atom1199
    PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1215 PredecessorHalfFin13Atom1227
    PredecessorHalfFin13Atom1263 PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1299
    PredecessorHalfFin13Atom1311 PredecessorHalfFin13Atom1347 PredecessorHalfFin13Atom1403
    PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1839 PredecessorHalfFin13Atom1851
    PredecessorHalfFin13Atom1887 PredecessorHalfFin13Atom1943 PredecessorHalfFin13Atom2069 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27095 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 6, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5213
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1168 PredecessorHalfFin13Atom1172 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1185 PredecessorHalfFin13Atom1187 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1213 PredecessorHalfFin13Atom1215 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1265 PredecessorHalfFin13Atom1297 PredecessorHalfFin13Atom1299
    PredecessorHalfFin13Atom1313 PredecessorHalfFin13Atom1349 PredecessorHalfFin13Atom1405
    PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1839 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1889 PredecessorHalfFin13Atom1945 PredecessorHalfFin13Atom2071 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27097 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0925
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1171
    PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1193
    PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1221
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1301
    PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1407
    PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1845
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom2073 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27098 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1437
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1172
    PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1190 PredecessorHalfFin13Atom1194
    PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1218 PredecessorHalfFin13Atom1222
    PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1302
    PredecessorHalfFin13Atom1306 PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1408
    PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1846
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom2074 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27100 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4509
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1192 PredecessorHalfFin13Atom1196
    PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1220 PredecessorHalfFin13Atom1224
    PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1304
    PredecessorHalfFin13Atom1308 PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1410
    PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1844 PredecessorHalfFin13Atom1848
    PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom2076 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27101 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1693
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1171 PredecessorHalfFin13Atom1172
    PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1190 PredecessorHalfFin13Atom1197
    PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1218 PredecessorHalfFin13Atom1225
    PredecessorHalfFin13Atom1271 PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1302
    PredecessorHalfFin13Atom1309 PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1411
    PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1849
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom2077 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27103 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4765
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1171 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1192 PredecessorHalfFin13Atom1199
    PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1220 PredecessorHalfFin13Atom1227
    PredecessorHalfFin13Atom1273 PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1304
    PredecessorHalfFin13Atom1311 PredecessorHalfFin13Atom1357 PredecessorHalfFin13Atom1413
    PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1844 PredecessorHalfFin13Atom1851
    PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom2079 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27105 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5277
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1169 PredecessorHalfFin13Atom1172 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1190 PredecessorHalfFin13Atom1192 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1218 PredecessorHalfFin13Atom1220 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1275 PredecessorHalfFin13Atom1302 PredecessorHalfFin13Atom1304
    PredecessorHalfFin13Atom1313 PredecessorHalfFin13Atom1359 PredecessorHalfFin13Atom1415
    PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1844 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1899 PredecessorHalfFin13Atom1955 PredecessorHalfFin13Atom2081 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27107 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1821
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1171 PredecessorHalfFin13Atom1172
    PredecessorHalfFin13Atom1193 PredecessorHalfFin13Atom1194 PredecessorHalfFin13Atom1197
    PredecessorHalfFin13Atom1221 PredecessorHalfFin13Atom1222 PredecessorHalfFin13Atom1225
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1306
    PredecessorHalfFin13Atom1309 PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1417
    PredecessorHalfFin13Atom1845 PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1849
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom2083 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27109 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4893
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1171 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1193 PredecessorHalfFin13Atom1196 PredecessorHalfFin13Atom1199
    PredecessorHalfFin13Atom1221 PredecessorHalfFin13Atom1224 PredecessorHalfFin13Atom1227
    PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1308
    PredecessorHalfFin13Atom1311 PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1419
    PredecessorHalfFin13Atom1845 PredecessorHalfFin13Atom1848 PredecessorHalfFin13Atom1851
    PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom2085 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27111 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5405
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1170 PredecessorHalfFin13Atom1172 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1194 PredecessorHalfFin13Atom1196 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1222 PredecessorHalfFin13Atom1224 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1281 PredecessorHalfFin13Atom1306 PredecessorHalfFin13Atom1308
    PredecessorHalfFin13Atom1313 PredecessorHalfFin13Atom1365 PredecessorHalfFin13Atom1421
    PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1848 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom2087 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27114 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 4, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5661
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1171 PredecessorHalfFin13Atom1172 PredecessorHalfFin13Atom1174
    PredecessorHalfFin13Atom1197 PredecessorHalfFin13Atom1199 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1225 PredecessorHalfFin13Atom1227 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1309 PredecessorHalfFin13Atom1311
    PredecessorHalfFin13Atom1313 PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1424
    PredecessorHalfFin13Atom1849 PredecessorHalfFin13Atom1851 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom2090 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27117 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 8}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0493
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1177
    PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1188
    PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1237
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1316
    PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1427
    PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1861
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom2093 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27118 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0749
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1178
    PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1189
    PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1238
    PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1317
    PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1428
    PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1862
    PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom2094 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27119 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1261
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1179
    PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1185 PredecessorHalfFin13Atom1190
    PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1239
    PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1318
    PredecessorHalfFin13Atom1323 PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1429
    PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1863
    PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom2095 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27121 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4333
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1181
    PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1187 PredecessorHalfFin13Atom1192
    PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1236 PredecessorHalfFin13Atom1241
    PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1320
    PredecessorHalfFin13Atom1325 PredecessorHalfFin13Atom1340 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1860 PredecessorHalfFin13Atom1865
    PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1971 PredecessorHalfFin13Atom2097 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27122 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0877
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1178
    PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1193
    PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1242
    PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1317
    PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1432
    PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1866
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom2098 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27123 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1389
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1179
    PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1185 PredecessorHalfFin13Atom1194
    PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1243
    PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1318
    PredecessorHalfFin13Atom1327 PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1433
    PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1867
    PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom2099 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27125 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4461
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1181
    PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1187 PredecessorHalfFin13Atom1196
    PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1236 PredecessorHalfFin13Atom1245
    PredecessorHalfFin13Atom1260 PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1320
    PredecessorHalfFin13Atom1329 PredecessorHalfFin13Atom1344 PredecessorHalfFin13Atom1435
    PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1860 PredecessorHalfFin13Atom1869
    PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1975 PredecessorHalfFin13Atom2101 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27126 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1645
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1179
    PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1185 PredecessorHalfFin13Atom1197
    PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1246
    PredecessorHalfFin13Atom1261 PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1318
    PredecessorHalfFin13Atom1330 PredecessorHalfFin13Atom1345 PredecessorHalfFin13Atom1436
    PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1870
    PredecessorHalfFin13Atom1885 PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom2102 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27128 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4717
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1181
    PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1187 PredecessorHalfFin13Atom1199
    PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1236 PredecessorHalfFin13Atom1248
    PredecessorHalfFin13Atom1263 PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1320
    PredecessorHalfFin13Atom1332 PredecessorHalfFin13Atom1347 PredecessorHalfFin13Atom1438
    PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1860 PredecessorHalfFin13Atom1872
    PredecessorHalfFin13Atom1887 PredecessorHalfFin13Atom1978 PredecessorHalfFin13Atom2104 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27130 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 6, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5229
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1175 PredecessorHalfFin13Atom1179 PredecessorHalfFin13Atom1181
    PredecessorHalfFin13Atom1185 PredecessorHalfFin13Atom1187 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1236 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1265 PredecessorHalfFin13Atom1318 PredecessorHalfFin13Atom1320
    PredecessorHalfFin13Atom1334 PredecessorHalfFin13Atom1349 PredecessorHalfFin13Atom1440
    PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1860 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1889 PredecessorHalfFin13Atom1980 PredecessorHalfFin13Atom2106 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27132 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0941
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1178
    PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1193
    PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1242
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1322
    PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1442
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1866
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom2108 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27133 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1453
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1179
    PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1190 PredecessorHalfFin13Atom1194
    PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1243
    PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1323
    PredecessorHalfFin13Atom1327 PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1443
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1867
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom2109 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27135 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4525
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1181
    PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1192 PredecessorHalfFin13Atom1196
    PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1241 PredecessorHalfFin13Atom1245
    PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1325
    PredecessorHalfFin13Atom1329 PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1445
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1865 PredecessorHalfFin13Atom1869
    PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1985 PredecessorHalfFin13Atom2111 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27136 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1709
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1179
    PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1190 PredecessorHalfFin13Atom1197
    PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1246
    PredecessorHalfFin13Atom1271 PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1323
    PredecessorHalfFin13Atom1330 PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1446
    PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1870
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom2112 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

end ErdosSzekeres

end
