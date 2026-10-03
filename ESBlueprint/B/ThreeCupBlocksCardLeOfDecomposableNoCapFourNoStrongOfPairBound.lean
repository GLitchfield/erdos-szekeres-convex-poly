import ESBlueprint.B.ThreeCupBlocksCardLeOfOneChangeNoCapFourNoCup
import ESBlueprint.B.DeepSplitTwoEndpointExtensions
import ESBlueprint.B.IsCupSetIffNotContainsCapSetThree

namespace ErdosSzekeres

open HasDeepBelowSplit

/-- Three ordered cups at a decomposable root avoiding four-caps and strong k-polygons have at most 3k-8 points under the uniform diagonal two-cup bound. Lower occupied blocks constrain upper sweep endpoints, while concrete upper cap witnesses force smaller lower cups.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.deepSplit_two_endpoint_extensions, ErdosSzekeres.threeCupBlocks_card_le_of_oneChange_no_capFour_no_cup
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs -/
theorem threeCupBlocks_card_le_of_decomposable_no_capFour_no_strong_of_pair_bound {k : ℕ} (hk : 6 ≤ k) (hTwo : ∀ {n : ℕ} {χ : TripleColoring n} {P Q : Finset (Fin n)}, (∀ x ∈ P, ∀ y ∈ Q, x < y) → IsCupSet χ P → IsCupSet χ Q → OneChangeOn χ (P ∪ Q) → ¬ContainsCapSet χ (P ∪ Q) 4 → ¬ContainsStrongPolygonSet χ (P ∪ Q) k → P.card + Q.card ≤ 2 * k - 4) {n : ℕ} {χ : TripleColoring n} {P Q R : Finset (Fin n)} (hPQ : ∀ x ∈ P, ∀ y ∈ Q, x < y) (hQR : ∀ y ∈ Q, ∀ z ∈ R, y < z) (hPR : ∀ x ∈ P, ∀ z ∈ R, x < z) (hPcup : IsCupSet χ P) (hQcup : IsCupSet χ Q) (hRcup : IsCupSet χ R) (hdec : IsDecomposableOn χ (P ∪ Q ∪ R)) (hnoCap : ¬ContainsCapSet χ (P ∪ Q ∪ R) 4) (hnoStrong : ¬ContainsStrongPolygonSet χ (P ∪ Q ∪ R) k) : P.card + Q.card + R.card ≤ 3 * k - 8 := by
  classical
  have hdisj (X Y : Finset (Fin n)) (ho : ∀ x ∈ X, ∀ y ∈ Y, x < y) :
      Disjoint X Y := Finset.disjoint_left.mpr (fun z hzX hzY ↦ (lt_irrefl z) (ho z hzX z hzY))
  have hcount (X Y Z : Finset (Fin n))
      (hXY : ∀ x ∈ X, ∀ y ∈ Y, x < y)
      (hYZ : ∀ y ∈ Y, ∀ z ∈ Z, y < z)
      (hXZ : ∀ x ∈ X, ∀ z ∈ Z, x < z) :
      (X ∪ Y ∪ Z).card = X.card + Y.card + Z.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨hdisj X Z hXZ, hdisj Y Z hYZ⟩), Finset.card_union_of_disjoint (hdisj X Y hXY)]
  have hwhole := hcount P Q R hPQ hQR hPR
  by_cases hsmall : (P ∪ Q ∪ R).card ≤ 1
  · omega
  obtain ⟨A, B, hAne, hBne, hAdec, hBdec, hdeep, hroot⟩ :=
    hdec.exists_split (by omega)
  have hPsub : P ⊆ A ∪ B := by rw [← hroot]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hQsub : Q ⊆ A ∪ B := by rw [← hroot]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hRsub : R ⊆ A ∪ B := by rw [← hroot]; exact Finset.subset_union_right
  have hAs : A ⊆ P ∪ Q ∪ R := by rw [hroot]; exact Finset.subset_union_left
  have hBs : B ⊆ P ∪ Q ∪ R := by rw [hroot]; exact Finset.subset_union_right
  have hone : OneChangeOn χ (A ∪ B) := by rw [← hroot]; exact hdec.turnSequenceAllowed
  have hn4 : ¬ContainsCapSet χ (A ∪ B) 4 := by simpa only [← hroot] using hnoCap
  have hnStrong : ¬ContainsStrongPolygonSet χ (A ∪ B) k := by simpa only [← hroot] using hnoStrong
  have hrootcard : (P ∪ Q ∪ R).card = A.card + B.card := by
    rw [hroot, Finset.card_union_of_disjoint hdeep.disjoint]
  have hcupCard (C : Finset (Fin n)) (hCs : C ⊆ A ∪ B) (hC : IsCupSet χ C) :
      C.card < k := by
    by_contra h
    obtain ⟨D, hDC, hDcard⟩ := Finset.exists_subset_card_eq (show k ≤ C.card by omega)
    exact hnStrong (FinsetPolygon.ContainsCupSet.toContainsStrongPolygonSet
      ⟨D, hDC.trans hCs, hDcard, FinsetPolygon.IsCupSet.mono hC hDC⟩)
  have hCouple (b : ℕ) (hb : b ≤ k) (hcap : ContainsCapSet χ B b) :
      ¬ContainsCupSet χ A (k - b) := by
    obtain ⟨D, hDB, hDcard, hDcap⟩ := hcap
    rintro ⟨C, hCA, hCcard, hCcup⟩
    exact hnStrong (hdeep.containsStrongPolygonSet_of_cup_cap hCA hDB hCcup hDcap (by omega))
  let AP := A ∩ P
  let AQ := A ∩ Q
  let AR := A ∩ R
  have hAP_A : AP ⊆ A := Finset.inter_subset_left
  have hAQ_A : AQ ⊆ A := Finset.inter_subset_left
  have hAR_A : AR ⊆ A := Finset.inter_subset_left
  have hAP_P : AP ⊆ P := Finset.inter_subset_right
  have hAQ_Q : AQ ⊆ Q := Finset.inter_subset_right
  have hAR_R : AR ⊆ R := Finset.inter_subset_right
  have hAPcup := FinsetPolygon.IsCupSet.mono hPcup hAP_P
  have hAQcup := FinsetPolygon.IsCupSet.mono hQcup hAQ_Q
  have hARcup := FinsetPolygon.IsCupSet.mono hRcup hAR_R
  have hAPQ : ∀ x ∈ AP, ∀ y ∈ AQ, x < y := fun x hx y hy ↦ hPQ x (hAP_P hx) y (hAQ_Q hy)
  have hAQR : ∀ y ∈ AQ, ∀ z ∈ AR, y < z := fun y hy z hz ↦ hQR y (hAQ_Q hy) z (hAR_R hz)
  have hAPR : ∀ x ∈ AP, ∀ z ∈ AR, x < z := fun x hx z hz ↦ hPR x (hAP_P hx) z (hAR_R hz)
  have hAeq : A = AP ∪ AQ ∪ AR := by
    ext x
    simp only [AP, AQ, AR, Finset.mem_union, Finset.mem_inter]
    have hx := hAs (a := x)
    simp only [Finset.mem_union] at hx
    tauto
  have hAcard : A.card = AP.card + AQ.card + AR.card := by
    rw [hAeq]; exact hcount AP AQ AR hAPQ hAQR hAPR
  have hLower (u : ℕ) (hu : 2 ≤ u) (hno : ¬ContainsCupSet χ A u) :
      AP.card < u ∧ AQ.card < u ∧ AR.card < u ∧
      AP.card + AQ.card ≤ 2 * u - 3 ∧ AQ.card + AR.card ≤ 2 * u - 3 := by
    have hc (C : Finset (Fin n)) (hCA : C ⊆ A) (hC : IsCupSet χ C) : C.card < u := by
      by_contra h
      obtain ⟨D, hDC, hDcard⟩ := Finset.exists_subset_card_eq (show u ≤ C.card by omega)
      exact hno ⟨D, hDC.trans hCA, hDcard, FinsetPolygon.IsCupSet.mono hC hDC⟩
    have ht (X Y : Finset (Fin n)) (hXA : X ⊆ A) (hYA : Y ⊆ A)
        (ho : ∀ x ∈ X, ∀ y ∈ Y, x < y) (hX : IsCupSet χ X) (hY : IsCupSet χ Y) :
        X.card + Y.card ≤ 2 * u - 3 :=
      (twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup hu
        (hone.mono ((Finset.union_subset hXA hYA).trans Finset.subset_union_left))
        ho hX hY
        (fun h ↦ hn4 (FinsetPolygon.ContainsCapSet.mono h
          ((Finset.union_subset hXA hYA).trans Finset.subset_union_left)))
        (fun h ↦ hno (FinsetPolygon.ContainsCupSet.mono h (Finset.union_subset hXA hYA)))).1
    exact ⟨hc AP hAP_A hAPcup, hc AQ hAQ_A hAQcup, hc AR hAR_A hARcup,
      ht AP AQ hAP_A hAQ_A hAPQ hAPcup hAQcup,
      ht AQ AR hAQ_A hAR_A hAQR hAQcup hARcup⟩
  have hLowerThree (u : ℕ) (hu : 4 ≤ u) (hno : ¬ContainsCupSet χ A u) :
      A.card ≤ 3 * u - 6 := by
    rw [hAcard]
    apply threeCupBlocks_card_le_of_oneChange_no_capFour_no_cup hu
      (hone.mono (by rw [← hAeq]; exact Finset.subset_union_left))
      hAPQ hAQR hAPR hAPcup hAQcup hARcup
    · intro h
      apply hn4
      exact FinsetPolygon.ContainsCapSet.mono h (by rw [← hAeq]; exact Finset.subset_union_left)
    · simpa only [← hAeq] using hno
  have hdis := Finset.disjoint_left.mp hdeep.disjoint
  have hsideCup (a : Fin n) (ha : a ∈ A) (E : Finset (Fin n)) (hEB : E ⊆ B)
      (hside : (∀ z ∈ E, z < a) ∨ (∀ z ∈ E, a < z)) : IsCupSet χ E := by
    apply isCupSet_iff_not_containsCapSet_three.mpr
    rintro ⟨C, hCE, hCcard, hCcap⟩
    have hend : IsSweepEndpoint C a := by
      rcases hside with hl | hr
      · exact Or.inr (fun z hz ↦ (hl z (hCE hz)).le)
      · exact Or.inl (fun z hz ↦ (hr z (hCE hz)).le)
    exact hn4 (hdeep.containsCapSet_succ_of_lower_endpoint
      (hCE.trans hEB) hCcard hCcap ha hend)
  have houtside (K E : Finset (Fin n)) (hKs : K ⊆ A ∪ B) (hKcup : IsCupSet χ K)
      (a : Fin n) (haA : a ∈ A) (haK : a ∈ K) (hEB : E ⊆ B) (hEK : E ⊆ K)
      (hside : (∀ z ∈ E, z < a) ∨ (∀ z ∈ E, a < z)) : E.card ≤ 1 := by
    have hep (z : Fin n) (hz : z ∈ E) : IsSweepEndpoint K z :=
      hdeep.upper_mem_cup_isSweepEndpoint hKs hKcup
        ⟨a, Finset.mem_inter.mpr ⟨haK, haA⟩⟩ (hEK hz) (hEB hz)
    apply Finset.card_le_one.mpr
    intro x hx y hy
    rcases hside with hl | hr
    · have hleft (z : Fin n) (hz : z ∈ E) : IsLeftSweepEndpoint K z := by
        rcases hep z hz with h | h
        · exact h
        · have := h a haK
          have := hl z hz
          omega
      exact le_antisymm (hleft x hx y (hEK hy)) (hleft y hy x (hEK hx))
    · have hright (z : Fin n) (hz : z ∈ E) : IsRightSweepEndpoint K z := by
        rcases hep z hz with h | h
        · have := h a haK
          have := hr z hz
          omega
        · exact h
      exact le_antisymm (hright y hy x (hEK hx)) (hright x hx y (hEK hy))
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
  have hBeforeCup (a : Fin n) (ha : a ∈ A) :
      IsCupSet χ (B.filter (fun z ↦ z < a)) :=
    hsideCup a ha _ (Finset.filter_subset _ _) (Or.inl (fun z hz ↦ (Finset.mem_filter.mp hz).2))
  have hAfterCup (a : Fin n) (ha : a ∈ A) :
      IsCupSet χ (B.filter (fun z ↦ a < z)) :=
    hsideCup a ha _ (Finset.filter_subset _ _) (Or.inr (fun z hz ↦ (Finset.mem_filter.mp hz).2))
  have hBtwo : B.card ≤ 2 * k - 4 := by
    obtain ⟨a, ha⟩ := hAne
    have hsub : B.filter (fun z ↦ z < a) ∪ B.filter (fun z ↦ a < z) ⊆ A ∪ B :=
      (by rw [← hBpartition a ha]; exact Finset.subset_union_right)
    rw [hBsum a ha]
    apply hTwo (fun x hx y hy ↦ (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2)
      (hBeforeCup a ha) (hAfterCup a ha) (hone.mono hsub)
    · exact fun h ↦ hn4 (FinsetPolygon.ContainsCapSet.mono h hsub)
    · exact fun h ↦ hnStrong (FinsetPolygon.ContainsStrongPolygonSet.mono h hsub)
  have hBeforeP (a : Fin n) (haP : a ∈ P) :
      B.filter (fun z ↦ z < a) ⊆ P := by
    intro z hz
    have hzB := (Finset.mem_filter.mp hz).1
    have hza := (Finset.mem_filter.mp hz).2
    rcases Finset.mem_union.mp (hBs hzB) with hzPQ | hzR
    · rcases Finset.mem_union.mp hzPQ with hzP | hzQ
      · exact hzP
      · have := hPQ a haP z hzQ
        omega
    · have := hPR a haP z hzR
      omega
  have hAfterR (a : Fin n) (haR : a ∈ R) :
      B.filter (fun z ↦ a < z) ⊆ R := by
    intro z hz
    have hzB := (Finset.mem_filter.mp hz).1
    have haz := (Finset.mem_filter.mp hz).2
    rcases Finset.mem_union.mp (hBs hzB) with hzPQ | hzR
    · rcases Finset.mem_union.mp hzPQ with hzP | hzQ
      · have := hPR z hzP a haR
        omega
      · have := hQR z hzQ a haR
        omega
    · exact hzR
  have hBeforeOne (a : Fin n) (haA : a ∈ A) (haP : a ∈ P) :
      (B.filter (fun z ↦ z < a)).card ≤ 1 :=
    houtside P _ hPsub hPcup a haA haP (Finset.filter_subset _ _) (hBeforeP a haP)
      (Or.inl (fun z hz ↦ (Finset.mem_filter.mp hz).2))
  have hAfterOne (a : Fin n) (haA : a ∈ A) (haR : a ∈ R) :
      (B.filter (fun z ↦ a < z)).card ≤ 1 :=
    houtside R _ hRsub hRcup a haA haR (Finset.filter_subset _ _) (hAfterR a haR)
      (Or.inr (fun z hz ↦ (Finset.mem_filter.mp hz).2))
  have hBouter : AP.Nonempty ∨ AR.Nonempty → B.card ≤ k := by
    rintro (hne | hne)
    · obtain ⟨a, ha⟩ := hne
      have haA := hAP_A ha
      have hc := hcupCard _ ((Finset.filter_subset _ _).trans Finset.subset_union_right) (hAfterCup a haA)
      have h1 := hBeforeOne a haA (hAP_P ha)
      have hs := hBsum a haA
      omega
    · obtain ⟨a, ha⟩ := hne
      have haA := hAR_A ha
      have hc := hcupCard _ ((Finset.filter_subset _ _).trans Finset.subset_union_right) (hBeforeCup a haA)
      have h1 := hAfterOne a haA (hAR_R ha)
      have hs := hBsum a haA
      omega
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
  have hBboth (hAPne : AP.Nonempty) (hARne : AR.Nonempty) : B.card ≤ 3 := by
    obtain ⟨a, ha⟩ := hAPne
    obtain ⟨b, hb⟩ := hARne
    have haA := hAP_A ha
    have hbA := hAR_A hb
    have hab := hPR a (hAP_P ha) b (hAR_R hb)
    let E := B.filter (fun z ↦ a < z ∧ z < b)
    have hEone : E.card ≤ 1 := by
      by_contra h
      obtain ⟨C, hCE, hCcard⟩ := Finset.exists_subset_card_eq (show 2 ≤ E.card by omega)
      have hCB : C ⊆ B := hCE.trans (Finset.filter_subset _ _)
      have hac : ∀ z ∈ C, a < z := fun z hz ↦ (Finset.mem_filter.mp (hCE hz)).2.1
      have hcb : ∀ z ∈ C, z < b := fun z hz ↦ (Finset.mem_filter.mp (hCE hz)).2.2
      have haNot : a ∉ insert b C := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨ne_of_lt hab, fun hz ↦ (lt_irrefl a) (hac a hz)⟩
      have hbNot : b ∉ C := fun hz ↦ (lt_irrefl b) (hcb b hz)
      refine hn4 ⟨insert a (insert b C), ?_, ?_,
        (deepSplit_two_endpoint_extensions hdeep).2 C hCB (hsmallCap C (by omega))
          a b haA hbA hab hac hcb⟩
      · exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ haA,
          Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hbA,
            hCB.trans Finset.subset_union_right⟩⟩
      · rw [Finset.card_insert_of_notMem haNot, Finset.card_insert_of_notMem hbNot, hCcard]
    have hpart : B = B.filter (fun z ↦ z < a) ∪ E ∪ B.filter (fun z ↦ b < z) := by
      ext z
      simp only [E, Finset.mem_union, Finset.mem_filter]
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
    have hsum : B.card = (B.filter (fun z ↦ z < a)).card + E.card +
        (B.filter (fun z ↦ b < z)).card := by
      conv_lhs => rw [hpart]
      apply hcount
      · intro x hx y hy
        exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.1
      · intro y hy z hz
        exact (Finset.mem_filter.mp hy).2.2.trans (Finset.mem_filter.mp hz).2
      · intro x hx z hz
        exact (Finset.mem_filter.mp hx).2.trans (hab.trans (Finset.mem_filter.mp hz).2)
    have h1 := hBeforeOne a haA (hAP_P ha)
    have h3 := hAfterOne b hbA (hAR_R hb)
    omega
  have hAzeroP (h : ¬AP.Nonempty) : AP.card = 0 := by
    exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
  have hAzeroR (h : ¬AR.Nonempty) : AR.card = 0 := by
    exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
  have hLowerMissing (u : ℕ) (hu : 2 ≤ u) (hno : ¬ContainsCupSet χ A u)
      (hmissing : ¬(AP.Nonempty ∧ AR.Nonempty)) : A.card ≤ 2 * u - 3 := by
    have hl := hLower u hu hno
    by_cases hAPne : AP.Nonempty
    · have hz := hAzeroR (fun hARne ↦ hmissing ⟨hAPne, hARne⟩)
      omega
    · have hz := hAzeroP hAPne
      omega
  rw [← hwhole, hrootcard]
  by_cases hBone : B.card ≤ 1
  · obtain ⟨b, hb⟩ := hBne
    have hcap : ContainsCapSet χ B 1 :=
      ⟨{b}, Finset.singleton_subset_iff.mpr hb, by simp, hsmallCap _ (by simp)⟩
    have hl := hLowerThree (k - 1) (by omega) (hCouple 1 (by omega) hcap)
    omega
  by_cases hBcup : IsCupSet χ B
  · obtain ⟨D, hDB, hDcard⟩ := Finset.exists_subset_card_eq (show 2 ≤ B.card by omega)
    have hno2 := hCouple 2 (by omega) ⟨D, hDB, hDcard, hsmallCap D (by omega)⟩
    have hb := hcupCard B Finset.subset_union_right hBcup
    by_cases houter : AP.Nonempty ∧ AR.Nonempty
    · have hl := hLowerThree (k - 2) (by omega) hno2
      have hbb := hBboth houter.1 houter.2
      omega
    · have hl := hLowerMissing (k - 2) (by omega) hno2 houter
      omega
  · have hcap3 : ContainsCapSet χ B 3 := by
      by_contra h
      exact hBcup (isCupSet_iff_not_containsCapSet_three.mpr h)
    have hno3 := hCouple 3 (by omega) hcap3
    have hl := hLower (k - 3) (by omega) hno3
    by_cases houter : AP.Nonempty ∧ AR.Nonempty
    · have hb := hBboth houter.1 houter.2
      omega
    by_cases honeouter : AP.Nonempty ∨ AR.Nonempty
    · have ha := hLowerMissing (k - 3) (by omega) hno3 houter
      have hb := hBouter honeouter
      omega
    · have hp := hAzeroP (fun h ↦ honeouter (Or.inl h))
      have hr := hAzeroR (fun h ↦ honeouter (Or.inr h))
      omega

end ErdosSzekeres
