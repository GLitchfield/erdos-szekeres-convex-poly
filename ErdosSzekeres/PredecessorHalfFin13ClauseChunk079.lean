module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 079. -/

theorem predecessorHalfFin13_clause23282 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom2022 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1924
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23283 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom2022 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1924
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23284 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom2022 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1924
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23285 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2022 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1924
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23286 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2022 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0776
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2022 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1924
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23287 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom2023 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2948
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23288 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom2023 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2948
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23289 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom2023 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2948
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23290 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom2023 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2948
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23291 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom2023 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2948
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23293 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom2024 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4996
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23294 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom2024 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4996
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23295 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom2024 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4996
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23296 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom2024 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4996
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23297 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2024 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4996
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23298 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2024 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0778
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2024 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4996
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23299 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom2025 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3460
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23300 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom2025 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3460
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23301 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0779 PredecessorHalfFin13Atom2025 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3460
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23302 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom2025 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3460
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23303 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom2025 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3460
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23305 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom2026 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5508
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23306 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom2026 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5508
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23307 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom2026 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5508
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23308 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom2026 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5508
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23309 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2026 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5508
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23310 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2026 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0780
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2026 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5508
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23312 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom2027 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6532
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23314 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom0787 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0787 PredecessorHalfFin13Atom2027 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6532
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23315 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0992 PredecessorHalfFin13Atom2027 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6532
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23317 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom2028 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3716
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23320 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom2028 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3716
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23321 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom2028 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3716
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23323 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom2029 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5764
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23324 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom2029 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5764
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23325 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom2029 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5764
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23326 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom2029 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5764
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23327 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2029 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5764
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23328 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2029 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0780
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2029 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5764
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23330 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom2030 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6788
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23332 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0790 PredecessorHalfFin13Atom2030 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6788
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23333 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0995 PredecessorHalfFin13Atom2030 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6788
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23336 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom2031 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7300
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23337 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0781 PredecessorHalfFin13Atom2031 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7300
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23338 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom2031 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7300
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23339 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0996 PredecessorHalfFin13Atom2031 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7300
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23341 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom2032 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3844
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23342 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom2032 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3844
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23343 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom2032 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3844
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23344 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom2032 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3844
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23345 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0997 PredecessorHalfFin13Atom2032 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3844
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23347 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom2033 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5892
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23348 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom2033 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5892
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23349 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom2033 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5892
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23350 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom2033 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5892
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23351 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2033 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5892
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23352 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2033 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0786
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2033 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5892
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23356 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2034 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0790 PredecessorHalfFin13Atom2034 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6916
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23357 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2034 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0999 PredecessorHalfFin13Atom2034 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6916
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23359 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom2035 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23360 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom2035 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23362 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom2035 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23363 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom1000 PredecessorHalfFin13Atom2035 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23366 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom2036 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23367 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0790 PredecessorHalfFin13Atom2036 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23368 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom2036 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23369 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom1001 PredecessorHalfFin13Atom2036 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23371 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom2037 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23372 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom2037 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23373 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom2037 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23374 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom2037 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23375 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom2037 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23376 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2037 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0799
    PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom2037 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23377 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom2038 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23378 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom2038 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23379 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom2038 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23380 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom2038 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23381 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom2038 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23382 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2038 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0800
    PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom2038 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23383 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom2039 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0632
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23384 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom2039 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0632
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23385 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom2039 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0632
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23386 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom2039 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0632
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23387 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom2039 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0632
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23388 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2039 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0801
    PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom2039 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0632
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23389 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom2040 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1144
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23390 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom2040 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1144
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23391 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom2040 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1144
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23392 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom2040 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1144
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23393 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom2040 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1144
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23394 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2040 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0802
    PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom2040 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1144
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23395 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom2041 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2168
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23397 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom2041 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2168
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23398 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom2041 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2168
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23399 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom2041 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2168
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23400 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2041 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0880 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0797 PredecessorHalfFin13Atom0803
    PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom2041 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2168
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23401 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom2042 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4216
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23402 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom2042 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4216
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23403 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom2042 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4216
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23404 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom2042 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4216
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23405 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom2042 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4216
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23406 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2042 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom2042 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4216
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23407 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom2043 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23408 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom2043 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23409 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom2043 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23410 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom2043 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23411 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom2043 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23412 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2043 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0805
    PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom2043 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23413 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom2044 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23414 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom2044 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23415 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom2044 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23416 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom2044 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23417 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom2044 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23418 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2044 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0806
    PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom2044 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23419 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom2045 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23420 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom2045 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23421 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom2045 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23422 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom2045 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23423 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom2045 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23424 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2045 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0807
    PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom2045 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23425 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom2046 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23426 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0797 PredecessorHalfFin13Atom2046 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23427 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom2046 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23428 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom2046 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23429 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom2046 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23431 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom2047 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23432 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom2047 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23433 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom2047 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4280
  ] at hbad
  tauto

end ErdosSzekeres

end
