import ErdosSzekeres.Duality

namespace ErdosSzekeres

/-- At a deep split, a lower cup gains two upper sweep endpoints, and an upper cap gains two lower sweep endpoints. Crossing triples are determined by their middle child, so simultaneous endpoint insertion requires no one-change assumption.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs -/
theorem deepSplit_two_endpoint_extensions {n : ℕ} {χ : TripleColoring n} {A B : Finset (Fin n)} (hdeep : HasDeepBelowSplit χ A B) : (∀ C : Finset (Fin n), C ⊆ A → IsCupSet χ C → ∀ x y : Fin n, x ∈ B → y ∈ B → x < y → (∀ z ∈ C, x < z) → (∀ z ∈ C, z < y) → IsCupSet χ (insert x (insert y C))) ∧ (∀ C : Finset (Fin n), C ⊆ B → IsCapSet χ C → ∀ x y : Fin n, x ∈ A → y ∈ A → x < y → (∀ z ∈ C, x < z) → (∀ z ∈ C, z < y) → IsCapSet χ (insert x (insert y C))) := by
  classical
  have hCupEnds (ψ : TripleColoring n) (L R C : Finset (Fin n))
      (hd : HasDeepBelowSplit ψ L R) (hCL : C ⊆ L) (hC : IsCupSet ψ C)
      (x y : Fin n) (hxR : x ∈ R) (hyR : y ∈ R) (hxy : x < y)
      (hxl : ∀ z ∈ C, x < z) (hry : ∀ z ∈ C, z < y) :
      IsCupSet ψ (insert x (insert y C)) := by
    have hdis := Finset.disjoint_left.mp hd.disjoint
    have hsub : insert x (insert y C) ⊆ L ∪ R := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_union_right _ hxR
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_union_right _ hyR
      exact Finset.mem_union_left _ (hCL hz)
    have hlo : ∀ z ∈ insert x (insert y C), x ≤ z := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact le_rfl
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hxy.le
      exact (hxl z hz).le
    have hhi : ∀ z ∈ insert x (insert y C), z ≤ y := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hxy.le
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact le_rfl
      exact (hry z hz).le
    have hLC : ∀ z ∈ insert x (insert y C), z ∈ L → z ∈ C := by
      intro z hz hzL
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (hdis hzL hxR).elim
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (hdis hzL hyR).elim
      exact hz
    intro t hi hj ht
    have hjC : t.j ∈ C := by
      rcases Finset.mem_insert.mp hj with hjx | hj
      · have := hlo t.i hi
        have := t.hij
        omega
      rcases Finset.mem_insert.mp hj with hjy | hj
      · have := hhi t.k ht
        have := t.hjk
        omega
      exact hj
    by_cases hall : t.i ∈ L ∧ t.j ∈ L ∧ t.k ∈ L
    · exact hC t (hLC _ hi hall.1) hjC (hLC _ ht hall.2.2)
    have hnR : ¬(t.i ∈ R ∧ t.j ∈ R ∧ t.k ∈ R) := by
      intro h
      exact hdis (hCL hjC) h.2.1
    simpa only [hCL hjC, if_true] using hd.crossing t (hsub hi) (hsub hj) (hsub ht) hall hnR
  have hCapEnds (ψ : TripleColoring n) (L R C : Finset (Fin n))
      (hd : HasDeepBelowSplit ψ L R) (hCR : C ⊆ R) (hC : IsCapSet ψ C)
      (x y : Fin n) (hxL : x ∈ L) (hyL : y ∈ L) (hxy : x < y)
      (hxl : ∀ z ∈ C, x < z) (hry : ∀ z ∈ C, z < y) :
      IsCapSet ψ (insert x (insert y C)) :=
    isCupSet_dual_iff.mp (hCupEnds ψ.dual R L C hd.dual hCR
      (isCupSet_dual_iff.mpr hC) x y hxL hyL hxy hxl hry)
  constructor
  · intro C hCA hCcup x y hxB hyB hxy hleft hright
    exact hCupEnds χ A B C hdeep hCA hCcup x y hxB hyB hxy hleft hright
  · intro C hCB hCcap x y hxA hyA hxy hleft hright
    exact hCapEnds χ A B C hdeep hCB hCcap x y hxA hyA hxy hleft hright

end ErdosSzekeres
