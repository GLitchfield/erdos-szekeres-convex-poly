import ESBlueprint.B.ThreeCupBlocksCardLeOfDecomposableNoCapFourNoStrongOfPairBound
import ESBlueprint.B.CardLeChooseAddOfOrderedCupPrefixNoCapFiveNoCup
import ESBlueprint.B.CardLeChooseAddOfOrderedCupPrefixNoCapFiveNoCupNoStrong
import ESBlueprint.B.ThreeCupBlocksCardLeOfOneChangeAdjacentNoCapFourNoStrongOfPairBounds

namespace ErdosSzekeres

open HasDeepBelowSplit

/-- A decomposable ordered cup prefix and four-cap-free suffix avoiding five-caps and strong k-polygons has at most 1+choose(k-1,2)+k-4 points under explicit uniform two-cup and Baek inputs. Concrete upper caps and lower occupancy reduce the root to accepted Z-prime, R1, extremal deficit and predecessor R2 bounds.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.card_le_choose_add_of_ordered_cup_prefix_no_capFive_no_cup, ErdosSzekeres.threeCupBlocks_card_le_of_decomposable_no_capFour_no_strong_of_pair_bound, ErdosSzekeres.threeCupBlocks_card_le_of_oneChange_adjacent_no_capFour_no_strong_of_pair_bounds
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs -/
theorem card_le_choose_add_of_decomposable_ordered_cup_prefix_no_capFive_no_strong_of_inputs {k : ℕ} (hk : 6 ≤ k) (hTwo : ∀ {n : ℕ} {χ : TripleColoring n} {P Q : Finset (Fin n)}, (∀ x ∈ P, ∀ y ∈ Q, x < y) → IsCupSet χ P → IsCupSet χ Q → OneChangeOn χ (P ∪ Q) → ¬ContainsCapSet χ (P ∪ Q) 4 → ¬ContainsStrongPolygonSet χ (P ∪ Q) k → P.card + Q.card ≤ 2 * k - 4) (hBaek : ∀ {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}, OneChangeOn χ s → ¬ContainsCapSet χ s 4 → ¬ContainsStrongPolygonSet χ s k → s.card ≤ 1 + Nat.choose (k - 1) 2) {n : ℕ} {χ : TripleColoring n} {P Q : Finset (Fin n)} (hPQ : ∀ x ∈ P, ∀ y ∈ Q, x < y) (hPcup : IsCupSet χ P) (hdec : IsDecomposableOn χ (P ∪ Q)) (hQnoCap : ¬ContainsCapSet χ Q 4) (hnoCap : ¬ContainsCapSet χ (P ∪ Q) 5) (hnoStrong : ¬ContainsStrongPolygonSet χ (P ∪ Q) k) : P.card + Q.card ≤ 1 + Nat.choose (k - 1) 2 + (k - 4) := by
  classical
  let T := 1 + Nat.choose (k - 1) 2 + (k - 4)
  have hpascal (j : ℕ) : Nat.choose (j + 1) 2 = Nat.choose j 2 + j := by
    simpa only [Nat.reduceAdd, Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' j 1
  have h1 := hpascal (k - 2)
  have h2 := hpascal (k - 3)
  have h3 := hpascal (k - 4)
  have he1 : k - 2 + 1 = k - 1 := by omega
  have he2 : k - 3 + 1 = k - 2 := by omega
  have he3 : k - 4 + 1 = k - 3 := by omega
  rw [he1] at h1
  rw [he2] at h2
  rw [he3] at h3
  have hT3 : T = Nat.choose (k - 3) 2 + (3 * k - 8) := by dsimp [T]; omega
  have hT4 : T = Nat.choose (k - 4) 2 + (4 * k - 12) := by dsimp [T]; omega
  have hPQdis : Disjoint P Q := Finset.disjoint_left.mpr (fun z hzP hzQ ↦ (lt_irrefl z) (hPQ z hzP z hzQ))
  have hwhole : (P ∪ Q).card = P.card + Q.card := Finset.card_union_of_disjoint hPQdis
  by_cases hsmall : (P ∪ Q).card ≤ 1
  · dsimp [T] at *
    omega
  obtain ⟨A, B, hAne, hBne, hAdec, hBdec, hdeep, hroot⟩ := hdec.exists_split (by omega)
  have hAs : A ⊆ P ∪ Q := by rw [hroot]; exact Finset.subset_union_left
  have hBs : B ⊆ P ∪ Q := by rw [hroot]; exact Finset.subset_union_right
  have hPsub : P ⊆ A ∪ B := by rw [← hroot]; exact Finset.subset_union_left
  have hQsub : Q ⊆ A ∪ B := by rw [← hroot]; exact Finset.subset_union_right
  have hone : OneChangeOn χ (A ∪ B) := by rw [← hroot]; exact hdec.turnSequenceAllowed
  have hn5 : ¬ContainsCapSet χ (A ∪ B) 5 := by simpa only [← hroot] using hnoCap
  have hnStrong : ¬ContainsStrongPolygonSet χ (A ∪ B) k := by simpa only [← hroot] using hnoStrong
  have hnCup : ¬ContainsCupSet χ (A ∪ B) k :=
    fun h ↦ hnStrong (FinsetPolygon.ContainsCupSet.toContainsStrongPolygonSet h)
  have hrootcard : (P ∪ Q).card = A.card + B.card := by
    rw [hroot, Finset.card_union_of_disjoint hdeep.disjoint]
  have hdis := Finset.disjoint_left.mp hdeep.disjoint
  have hcupCard (C : Finset (Fin n)) (hCs : C ⊆ A ∪ B) (hC : IsCupSet χ C) : C.card < k := by
    by_contra h
    obtain ⟨D, hDC, hDcard⟩ := Finset.exists_subset_card_eq (show k ≤ C.card by omega)
    exact hnCup ⟨D, hDC.trans hCs, hDcard, FinsetPolygon.IsCupSet.mono hC hDC⟩
  have hsmallCap (C : Finset (Fin n)) (hC : C.card ≤ 2) : IsCapSet χ C := by
    intro t hi hj ht
    exfalso
    have hsub : ({t.i, t.j, t.k} : Finset (Fin n)) ⊆ C := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hi, hj, ht⟩
    have hcard : ({t.i, t.j, t.k} : Finset (Fin n)).card = 3 := by
      simp [ne_of_lt t.hij, ne_of_lt t.hjk, ne_of_lt (t.hij.trans t.hjk)]
    have := Finset.card_le_card hsub
    omega
  have hCouple (b : ℕ) (hb : b ≤ k) (hcap : ContainsCapSet χ B b) :
      ¬ContainsCupSet χ A (k - b) := by
    obtain ⟨D, hDB, hDcard, hDcap⟩ := hcap
    rintro ⟨C, hCA, hCcard, hCcup⟩
    exact hnStrong (hdeep.containsStrongPolygonSet_of_cup_cap hCA hDB hCcup hDcap (by omega))
  have hBaekBound (C : Finset (Fin n)) (hCs : C ⊆ A ∪ B)
      (hn4 : ¬ContainsCapSet χ C 4) : C.card ≤ 1 + Nat.choose (k - 1) 2 :=
    hBaek (hone.mono hCs) hn4
      (fun h ↦ hnStrong (FinsetPolygon.ContainsStrongPolygonSet.mono h hCs))
  let AP := A ∩ P
  let AQ := A ∩ Q
  have hAP_A : AP ⊆ A := Finset.inter_subset_left
  have hAQ_A : AQ ⊆ A := Finset.inter_subset_left
  have hAP_P : AP ⊆ P := Finset.inter_subset_right
  have hAQ_Q : AQ ⊆ Q := Finset.inter_subset_right
  have hAPcup := FinsetPolygon.IsCupSet.mono hPcup hAP_P
  have hAPQ : ∀ x ∈ AP, ∀ y ∈ AQ, x < y := fun x hx y hy ↦ hPQ x (hAP_P hx) y (hAQ_Q hy)
  have hAeq : A = AP ∪ AQ := by
    ext x
    simp only [AP, AQ, Finset.mem_union, Finset.mem_inter]
    have hx := hAs (a := x)
    simp only [Finset.mem_union] at hx
    tauto
  have hAcard : A.card = AP.card + AQ.card := by
    rw [hAeq, Finset.card_union_of_disjoint (Finset.disjoint_left.mpr
      (fun z hz1 hz2 ↦ (lt_irrefl z) (hAPQ z hz1 z hz2)))]
  have hAno5 : ¬ContainsCapSet χ (AP ∪ AQ) 5 := by
    intro h
    exact hn5 (FinsetPolygon.ContainsCapSet.mono h (by rw [← hAeq]; exact Finset.subset_union_left))
  have hAQno4 : ¬ContainsCapSet χ AQ 4 :=
    fun h ↦ hQnoCap (FinsetPolygon.ContainsCapSet.mono h hAQ_Q)
  have hZ (u : ℕ) (hu : 2 ≤ u) (hno : ¬ContainsCupSet χ A u) :
      A.card ≤ Nat.choose u 2 + (u - 2) := by
    rw [hAcard]
    apply card_le_choose_add_of_ordered_cup_prefix_no_capFive_no_cup hu hAPQ hAPcup
      (hone.mono (by rw [← hAeq]; exact Finset.subset_union_left)) hAQno4 hAno5
    simpa only [← hAeq] using hno
  have hAinP (h : ¬AQ.Nonempty) : A ⊆ P := by
    intro z hz
    rcases Finset.mem_union.mp (hAs hz) with hzP | hzQ
    · exact hzP
    · exact (h ⟨z, Finset.mem_inter.mpr ⟨hz, hzQ⟩⟩).elim
  have hAinQ (h : ¬AP.Nonempty) : A ⊆ Q := by
    intro z hz
    rcases Finset.mem_union.mp (hAs hz) with hzP | hzQ
    · exact (h ⟨z, Finset.mem_inter.mpr ⟨hz, hzP⟩⟩).elim
    · exact hzQ
  have hAcupSmall (u : ℕ) (hno : ¬ContainsCupSet χ A u) (hAP : A ⊆ P) : A.card < u := by
    by_contra h
    obtain ⟨D, hDA, hDcard⟩ := Finset.exists_subset_card_eq (show u ≤ A.card by omega)
    exact hno ⟨D, hDA, hDcard, FinsetPolygon.IsCupSet.mono hPcup (hDA.trans hAP)⟩
  have hATriangle (u : ℕ) (hno : ¬ContainsCupSet χ A u) (hAQ : A ⊆ Q) :
      A.card ≤ Nat.choose u 2 :=
    card_le_choose_of_oneChange_no_capFour_no_cup (hone.mono Finset.subset_union_left)
      (fun h ↦ hQnoCap (FinsetPolygon.ContainsCapSet.mono h hAQ)) hno
  have hsideNo4 (a : Fin n) (ha : a ∈ A) (E : Finset (Fin n)) (hEB : E ⊆ B)
      (hside : (∀ z ∈ E, z < a) ∨ (∀ z ∈ E, a < z)) :
      ¬ContainsCapSet χ E 4 := by
    rintro ⟨C, hCE, hCcard, hCcap⟩
    have hend : IsSweepEndpoint C a := by
      rcases hside with hl | hr
      · exact Or.inr (fun z hz ↦ (hl z (hCE hz)).le)
      · exact Or.inl (fun z hz ↦ (hr z (hCE hz)).le)
    exact hn5 (hdeep.containsCapSet_succ_of_lower_endpoint
      (hCE.trans hEB) hCcard hCcap ha hend)
  have hsideCupQ (a : Fin n) (haA : a ∈ A) (haQ : a ∈ Q)
      (E : Finset (Fin n)) (hEB : E ⊆ B) (hEQ : E ⊆ Q)
      (hside : (∀ z ∈ E, z < a) ∨ (∀ z ∈ E, a < z)) : IsCupSet χ E := by
    apply isCupSet_iff_not_containsCapSet_three.mpr
    rintro ⟨C, hCE, hCcard, hCcap⟩
    have haNot : a ∉ C := fun hz ↦ hdis haA (hEB (hCE hz))
    refine hQnoCap ⟨insert a C, Finset.insert_subset_iff.mpr ⟨haQ, hCE.trans hEQ⟩, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem haNot, hCcard]
    · rcases hside with hl | hr
      · exact hdeep.insert_lower_isCapSet_of_isRightSweepEndpoint
          (hCE.trans hEB) hCcap haA (fun z hz ↦ (hl z (hCE hz)).le)
      · exact hdeep.insert_lower_isCapSet_of_isLeftSweepEndpoint
          (hCE.trans hEB) hCcap haA (fun z hz ↦ (hr z (hCE hz)).le)
  have hbetweenCup (a b : Fin n) (haA : a ∈ A) (hbA : b ∈ A) (hab : a < b)
      (E : Finset (Fin n)) (hEB : E ⊆ B)
      (hal : ∀ z ∈ E, a < z) (hbr : ∀ z ∈ E, z < b) : IsCupSet χ E := by
    apply isCupSet_iff_not_containsCapSet_three.mpr
    rintro ⟨C, hCE, hCcard, hCcap⟩
    have haNot : a ∉ insert b C := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨ne_of_lt hab, fun hz ↦ (lt_irrefl a) (hal a (hCE hz))⟩
    have hbNot : b ∉ C := fun hz ↦ (lt_irrefl b) (hbr b (hCE hz))
    refine hn5 ⟨insert a (insert b C), ?_, ?_,
      (deepSplit_two_endpoint_extensions hdeep).2 C (hCE.trans hEB) hCcap
        a b haA hbA hab (fun z hz ↦ hal z (hCE hz)) (fun z hz ↦ hbr z (hCE hz))⟩
    · exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ haA,
        Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hbA,
          (hCE.trans hEB).trans Finset.subset_union_right⟩⟩
    · rw [Finset.card_insert_of_notMem haNot, Finset.card_insert_of_notMem hbNot, hCcard]
  have hBeforeP (a : Fin n) (haP : a ∈ P) : B.filter (fun z ↦ z < a) ⊆ P := by
    intro z hz
    have hzB := (Finset.mem_filter.mp hz).1
    have hza := (Finset.mem_filter.mp hz).2
    rcases Finset.mem_union.mp (hBs hzB) with hzP | hzQ
    · exact hzP
    · have := hPQ a haP z hzQ
      omega
  have hAfterQ (b : Fin n) (hbQ : b ∈ Q) : B.filter (fun z ↦ b < z) ⊆ Q := by
    intro z hz
    have hzB := (Finset.mem_filter.mp hz).1
    have hbz := (Finset.mem_filter.mp hz).2
    rcases Finset.mem_union.mp (hBs hzB) with hzP | hzQ
    · have := hPQ z hzP b hbQ
      omega
    · exact hzQ
  have hBeforeOne (a : Fin n) (haA : a ∈ A) (haP : a ∈ P) :
      (B.filter (fun z ↦ z < a)).card ≤ 1 := by
    let E := B.filter (fun z ↦ z < a)
    have hep (z : Fin n) (hz : z ∈ E) : IsLeftSweepEndpoint P z := by
      have hzB := (Finset.mem_filter.mp hz).1
      have hzP := hBeforeP a haP hz
      rcases hdeep.upper_mem_cup_isSweepEndpoint hPsub hPcup
          ⟨a, Finset.mem_inter.mpr ⟨haP, haA⟩⟩ hzP hzB with hl | hr
      · exact hl
      · have := hr a haP
        have := (Finset.mem_filter.mp hz).2
        omega
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact le_antisymm (hep x hx y (hBeforeP a haP hy)) (hep y hy x (hBeforeP a haP hx))
  have hBpartition (a : Fin n) (ha : a ∈ A) :
      B = B.filter (fun z ↦ z < a) ∪ B.filter (fun z ↦ a < z) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hz
      have hza : z ≠ a := by rintro rfl; exact hdis ha hz
      rcases lt_or_gt_of_ne hza with hl | hr
      · exact Or.inl ⟨hz, hl⟩
      · exact Or.inr ⟨hz, hr⟩
    · tauto
  have hBsum (a : Fin n) (ha : a ∈ A) :
      B.card = (B.filter (fun z ↦ z < a)).card + (B.filter (fun z ↦ a < z)).card := by
    conv_lhs => rw [hBpartition a ha]
    exact Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (by
      intro z hz1 hz2
      have := (Finset.mem_filter.mp hz1).2
      have := (Finset.mem_filter.mp hz2).2
      omega))
  have hBprefix (hAP : A ⊆ P) : B.card ≤ 2 + Nat.choose (k - 1) 2 := by
    obtain ⟨a, ha⟩ := hAne
    have h1 := hBeforeOne a ha (hAP ha)
    have h4 := hsideNo4 a ha (B.filter (fun z ↦ a < z)) (Finset.filter_subset _ _)
      (Or.inr (fun z hz ↦ (Finset.mem_filter.mp hz).2))
    have hb := hBaekBound _ ((Finset.filter_subset _ _).trans Finset.subset_union_right) h4
    have hs := hBsum a ha
    omega
  have hdisj (X Y : Finset (Fin n)) (ho : ∀ x ∈ X, ∀ y ∈ Y, x < y) :
      Disjoint X Y := Finset.disjoint_left.mpr (fun z hzX hzY ↦ (lt_irrefl z) (ho z hzX z hzY))
  have hcount (X Y Z : Finset (Fin n))
      (hXY : ∀ x ∈ X, ∀ y ∈ Y, x < y)
      (hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y < z)
      (hXZ : ∀ x ∈ X, ∀ z ∈ Z, x < z) :
      (X ∪ Y ∪ Z).card = X.card + Y.card + Z.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨hdisj X Z hXZ, hdisj Y Z hYZ⟩), Finset.card_union_of_disjoint (hdisj X Y hXY)]
  have hBmixed (hAPne : AP.Nonempty) (hAQne : AQ.Nonempty) : B.card ≤ 2 * k - 3 := by
    obtain ⟨a, ha⟩ := hAPne
    obtain ⟨b, hb⟩ := hAQne
    have haA := hAP_A ha
    have hbA := hAQ_A hb
    have hab := hPQ a (hAP_P ha) b (hAQ_Q hb)
    let V := B.filter (fun z ↦ z < a)
    let W := B.filter (fun z ↦ a < z ∧ z < b)
    let X := B.filter (fun z ↦ b < z)
    have hpart : B = V ∪ W ∪ X := by
      ext z
      simp only [V, W, X, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hz
        have hza : z ≠ a := by rintro rfl; exact hdis haA hz
        have hzb : z ≠ b := by rintro rfl; exact hdis hbA hz
        by_cases hza' : z < a
        · exact Or.inl (Or.inl ⟨hz, hza'⟩)
        by_cases hzb' : z < b
        · exact Or.inl (Or.inr ⟨hz, by omega, hzb'⟩)
        · exact Or.inr ⟨hz, by omega⟩
      · tauto
    have hVW : ∀ x ∈ V, ∀ y ∈ W, x < y :=
      fun x hx y hy ↦ (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.1
    have hWX : ∀ y ∈ W, ∀ z ∈ X, y < z :=
      fun y hy z hz ↦ (Finset.mem_filter.mp hy).2.2.trans (Finset.mem_filter.mp hz).2
    have hVX : ∀ x ∈ V, ∀ z ∈ X, x < z :=
      fun x hx z hz ↦ (Finset.mem_filter.mp hx).2.trans (hab.trans (Finset.mem_filter.mp hz).2)
    have hsum : B.card = V.card + W.card + X.card := by
      rw [hpart]
      exact hcount V W X hVW hWX hVX
    have hWcup : IsCupSet χ W := hbetweenCup a b haA hbA hab W (Finset.filter_subset _ _)
      (fun z hz ↦ (Finset.mem_filter.mp hz).2.1) (fun z hz ↦ (Finset.mem_filter.mp hz).2.2)
    have hXcup : IsCupSet χ X := hsideCupQ b hbA (hAQ_Q hb) X (Finset.filter_subset _ _)
      (hAfterQ b (hAQ_Q hb)) (Or.inr (fun z hz ↦ (Finset.mem_filter.mp hz).2))
    have hWXB : W ∪ X ⊆ B := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hWXsub : W ∪ X ⊆ A ∪ B := hWXB.trans Finset.subset_union_right
    have hWXno4 : ¬ContainsCapSet χ (W ∪ X) 4 := hsideNo4 a haA _ hWXB
      (Or.inr (by
        intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · exact (Finset.mem_filter.mp hz).2.1
        · exact hab.trans (Finset.mem_filter.mp hz).2))
    have hpair := hTwo hWX hWcup hXcup (hone.mono hWXsub) hWXno4
      (fun h ↦ hnStrong (FinsetPolygon.ContainsStrongPolygonSet.mono h hWXsub))
    have hVone : V.card ≤ 1 := hBeforeOne a haA (hAP_P ha)
    omega
  have hBthree (hAQ : A ⊆ Q) :
      B.card ≤ 3 * k - 6 ∧ (¬ContainsCapSet χ B 4 → B.card ≤ 3 * k - 8) := by
    obtain ⟨a, haA⟩ := hAne
    have haQ := hAQ haA
    let V := B ∩ P
    let W := B.filter (fun z ↦ z ∈ Q ∧ z < a)
    let X := B.filter (fun z ↦ z ∈ Q ∧ a < z)
    have hVB : V ⊆ B := Finset.inter_subset_left
    have hVP : V ⊆ P := Finset.inter_subset_right
    have hWB : W ⊆ B := Finset.filter_subset _ _
    have hXB : X ⊆ B := Finset.filter_subset _ _
    have hWQ : W ⊆ Q := fun z hz ↦ (Finset.mem_filter.mp hz).2.1
    have hXQ : X ⊆ Q := fun z hz ↦ (Finset.mem_filter.mp hz).2.1
    have hVcup : IsCupSet χ V := FinsetPolygon.IsCupSet.mono hPcup hVP
    have hWcup : IsCupSet χ W := hsideCupQ a haA haQ W hWB hWQ
      (Or.inl (fun z hz ↦ (Finset.mem_filter.mp hz).2.2))
    have hXcup : IsCupSet χ X := hsideCupQ a haA haQ X hXB hXQ
      (Or.inr (fun z hz ↦ (Finset.mem_filter.mp hz).2.2))
    have hpart : B = V ∪ W ∪ X := by
      ext z
      simp only [V, W, X, Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
      constructor
      · intro hz
        rcases Finset.mem_union.mp (hBs hz) with hzP | hzQ
        · exact Or.inl (Or.inl ⟨hz, hzP⟩)
        have hza : z ≠ a := by rintro rfl; exact hdis haA hz
        by_cases hza' : z < a
        · exact Or.inl (Or.inr ⟨hz, hzQ, hza'⟩)
        · exact Or.inr ⟨hz, hzQ, by omega⟩
      · tauto
    have hVW : ∀ x ∈ V, ∀ y ∈ W, x < y := fun x hx y hy ↦ hPQ x (hVP hx) y (hWQ hy)
    have hWX : ∀ y ∈ W, ∀ z ∈ X, y < z := fun y hy z hz ↦
      (Finset.mem_filter.mp hy).2.2.trans (Finset.mem_filter.mp hz).2.2
    have hVX : ∀ x ∈ V, ∀ z ∈ X, x < z := fun x hx z hz ↦ hPQ x (hVP hx) z (hXQ hz)
    have hsum : B.card = V.card + W.card + X.card := by
      rw [hpart]
      exact hcount V W X hVW hWX hVX
    have hVWB : V ∪ W ⊆ B := Finset.union_subset hVB hWB
    have hWXB : W ∪ X ⊆ B := Finset.union_subset hWB hXB
    have hVWs : V ∪ W ⊆ A ∪ B := hVWB.trans Finset.subset_union_right
    have hWXs : W ∪ X ⊆ A ∪ B := hWXB.trans Finset.subset_union_right
    have hVWno4 : ¬ContainsCapSet χ (V ∪ W) 4 := hsideNo4 a haA _ hVWB
      (Or.inl (by
        intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · exact hPQ z (hVP hz) a haQ
        · exact (Finset.mem_filter.mp hz).2.2))
    have hWXno4 : ¬ContainsCapSet χ (W ∪ X) 4 :=
      fun h ↦ hQnoCap (FinsetPolygon.ContainsCapSet.mono h (Finset.union_subset hWQ hXQ))
    have hVWcount := hTwo hVW hVcup hWcup (hone.mono hVWs) hVWno4
      (fun h ↦ hnStrong (FinsetPolygon.ContainsStrongPolygonSet.mono h hVWs))
    have hWXcount := hTwo hWX hWcup hXcup (hone.mono hWXs) hWXno4
      (fun h ↦ hnStrong (FinsetPolygon.ContainsStrongPolygonSet.mono h hWXs))
    have hsub3 : V ∪ W ∪ X ⊆ A ∪ B := by rw [← hpart]; exact Finset.subset_union_right
    have hnoS3 : ¬ContainsStrongPolygonSet χ (V ∪ W ∪ X) k :=
      fun h ↦ hnStrong (FinsetPolygon.ContainsStrongPolygonSet.mono h hsub3)
    have hdef := threeCupBlocks_card_le_of_oneChange_adjacent_no_capFour_no_strong_of_pair_bounds
      hk hVW hWX hVX hVcup hWcup hXcup (hone.mono hsub3) hVWno4 hWXno4
      hVWcount hWXcount hnoS3
    constructor
    · omega
    · intro hn4B
      have hdec3 : IsDecomposableOn χ (V ∪ W ∪ X) := by rw [← hpart]; exact hBdec
      have hn4 : ¬ContainsCapSet χ (V ∪ W ∪ X) 4 := by simpa only [← hpart] using hn4B
      have hR1 := threeCupBlocks_card_le_of_decomposable_no_capFour_no_strong_of_pair_bound
        hk hTwo hVW hWX hVX hVcup hWcup hXcup hdec3 hn4 hnoS3
      omega
  change P.card + Q.card ≤ T
  rw [← hwhole, hrootcard]
  by_cases hBone : B.card ≤ 1
  · obtain ⟨b, hb⟩ := hBne
    have hcap1 : ContainsCapSet χ B 1 :=
      ⟨{b}, Finset.singleton_subset_iff.mpr hb, by simp, hsmallCap _ (by simp)⟩
    have hno1 := hCouple 1 (by omega) hcap1
    have he : k - 1 + 1 = k := by omega
    have hAS : ¬ContainsStrongPolygonSet χ (AP ∪ AQ) (k - 1 + 1) := by
      rw [he]
      exact fun h ↦ hnStrong (FinsetPolygon.ContainsStrongPolygonSet.mono h
        (by rw [← hAeq]; exact Finset.subset_union_left))
    have hpred := card_le_choose_add_of_ordered_cup_prefix_no_capFive_no_cup_no_strong
      (show 4 ≤ k - 1 by omega) hAPQ hAPcup
      (hone.mono (by rw [← hAeq]; exact Finset.subset_union_left)) hAQno4 hAno5
      (by simpa only [← hAeq] using hno1) hAS
    rw [← hAcard] at hpred
    dsimp [T]
    omega
  by_cases hBcup : IsCupSet χ B
  · obtain ⟨D, hDB, hDcard⟩ := Finset.exists_subset_card_eq (show 2 ≤ B.card by omega)
    have hno2 := hCouple 2 (by omega) ⟨D, hDB, hDcard, hsmallCap D (by omega)⟩
    have ha := hZ (k - 2) (by omega) hno2
    have hb := hcupCard B Finset.subset_union_right hBcup
    dsimp [T]
    omega
  have hcap3 : ContainsCapSet χ B 3 := by
    by_contra h
    exact hBcup (isCupSet_iff_not_containsCapSet_three.mpr h)
  have hno3 := hCouple 3 (by omega) hcap3
  by_cases hcap4 : ContainsCapSet χ B 4
  · have hno4 := hCouple 4 (by omega) hcap4
    by_cases hAPne : AP.Nonempty
    · by_cases hAQne : AQ.Nonempty
      · have ha := hZ (k - 4) (by omega) hno4
        have hb := hBmixed hAPne hAQne
        omega
      · have hAP := hAinP hAQne
        have ha := hAcupSmall (k - 4) hno4 hAP
        have hb := hBprefix hAP
        dsimp [T]
        omega
    · have hAQ := hAinQ hAPne
      have ha := hATriangle (k - 4) hno4 hAQ
      have hb := (hBthree hAQ).1
      omega
  · by_cases hAPne : AP.Nonempty
    · by_cases hAQne : AQ.Nonempty
      · have ha := hZ (k - 3) (by omega) hno3
        have hb := hBmixed hAPne hAQne
        omega
      · have hAP := hAinP hAQne
        have ha := hAcupSmall (k - 3) hno3 hAP
        have hb := hBaekBound B Finset.subset_union_right hcap4
        dsimp [T]
        omega
    · have hAQ := hAinQ hAPne
      have ha := hATriangle (k - 3) hno3 hAQ
      have hb := (hBthree hAQ).2 hcap4
      omega

end ErdosSzekeres
