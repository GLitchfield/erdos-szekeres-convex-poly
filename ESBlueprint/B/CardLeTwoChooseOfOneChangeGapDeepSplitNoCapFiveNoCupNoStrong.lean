import ESBlueprint.B.CardLeMulOfOneChangeGapNoCapFiveStraddledCups
import ESBlueprint.B.CardLeChooseAddOfOrderedCupPrefixNoCapFiveNoCupNoStrong
import ESBlueprint.B.ThreeCupBlocksCardLeOfOneChangeNoCapFourNoCup
import ESBlueprint.B.ReverseColorSetInvariants
import ErdosSzekeres.Duality

namespace ErdosSzekeres

/-- The complete audited five-predecessor two-side bound at a genuine nonempty deep root. Coupling a lower cup with an upper cap and gaining outer endpoints reduce all root configurations to the classic square, triangular, two/three-cup, marker, and sharp R2 bounds; reflection handles mirrored orientations.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem card_le_two_choose_of_oneChange_gap_deepSplit_no_capFive_no_cup_no_strong {n k : ℕ} {χ : TripleColoring n} {A B : Finset (Fin n)} {q : Fin n} (hk : 6 ≤ k) (hAne : A.Nonempty) (hBne : B.Nonempty) (hdeep : HasDeepBelowSplit χ A B) (hq : q ∉ A ∪ B) (hone : OneChangeOn χ (A ∪ B)) (hleft : ¬ContainsCapSet χ ((A ∪ B).filter (fun x ↦ x < q)) 4) (hright : ¬ContainsCapSet χ ((A ∪ B).filter (fun x ↦ q < x)) 4) (hnoCap : ¬ContainsCapSet χ (A ∪ B) 5) (hnoCup : ¬ContainsCupSet χ (A ∪ B) (k - 1)) (hnoStrong : ¬ContainsStrongPolygonSet χ (A ∪ B) k) : (A ∪ B).card ≤ Nat.choose (k - 1) 2 + Nat.choose (k - 3) 2 := by
  classical
  let H := Nat.choose (k - 1) 2 + Nat.choose (k - 3) 2
  have hpascal : Nat.choose (k - 1) 2 = Nat.choose (k - 3) 2 + (k - 3) + (k - 2) := by
    have h1 := Nat.choose_succ_succ' (k - 3) 1
    have h2 := Nat.choose_succ_succ' (k - 2) 1
    have he1 : k - 3 + 1 = k - 2 := by omega
    have he2 : k - 2 + 1 = k - 1 := by omega
    simp only [he1, he2, Nat.choose_one_right, Nat.reduceAdd] at h1 h2
    omega
  have hprod : (k - 3) * (k - 4) = Nat.choose (k - 3) 2 * 2 := by
    have h := Nat.add_one_mul_choose_eq (k - 4) 1
    have he : k - 4 + 1 = k - 3 := by omega
    simpa only [he, Nat.choose_one_right] using h
  have hH : H = (k - 3) ^ 2 + (k - 2) := by
    have hs : (k - 3) ^ 2 = (k - 3) * (k - 4) + (k - 3) := by
      have he : k - 3 = k - 4 + 1 := by omega
      rw [he]
      ring
    dsimp [H]
    omega
  have hsmall (ψ : TripleColoring n) (C : Finset (Fin n)) (hC : C.card ≤ 2) :
      IsCapSet ψ C := by
    intro t hi hj ht
    exfalso
    have hsub : ({t.i, t.j, t.k} : Finset (Fin n)) ⊆ C := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hi, hj, ht⟩
    have hcard : ({t.i, t.j, t.k} : Finset (Fin n)).card = 3 := by
      simp [ne_of_lt t.hij, ne_of_lt t.hjk, ne_of_lt (t.hij.trans t.hjk)]
    have := Finset.card_le_card hsub
    omega
  have hcupCard (ψ : TripleColoring n) (V C : Finset (Fin n)) (u : ℕ)
      (hno : ¬ContainsCupSet ψ V u) (hCsub : C ⊆ V) (hCcup : IsCupSet ψ C) :
      C.card < u := by
    by_contra h
    obtain ⟨D, hDC, hDcard⟩ := Finset.exists_subset_card_eq (show u ≤ C.card by omega)
    exact hno ⟨D, hDC.trans hCsub, hDcard, FinsetPolygon.IsCupSet.mono hCcup hDC⟩
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
  have hBetweenCup (ψ : TripleColoring n) (L R V : Finset (Fin n))
      (hd : HasDeepBelowSplit ψ L R) (hVR : V ⊆ R)
      (hno5 : ¬ContainsCapSet ψ (L ∪ R) 5)
      (x y : Fin n) (hxL : x ∈ L) (hyL : y ∈ L) (hxy : x < y)
      (hxl : ∀ z ∈ V, x < z) (hry : ∀ z ∈ V, z < y) : IsCupSet ψ V := by
    apply isCupSet_iff_not_containsCapSet_three.mpr
    rintro ⟨C, hCV, hCcard, hCcap⟩
    have hCL : x ∉ C := fun hx ↦ (ne_of_lt (hxl x (hCV hx))) rfl
    have hCR : y ∉ C := fun hy ↦ (ne_of_lt (hry y (hCV hy))) rfl
    refine hno5 ⟨insert x (insert y C), ?_, ?_,
      hCapEnds ψ L R C hd (hCV.trans hVR) hCcap x y hxL hyL hxy
        (fun z hz ↦ hxl z (hCV hz)) (fun z hz ↦ hry z (hCV hz))⟩
    · exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hxL,
        Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hyL,
          (hCV.trans hVR).trans Finset.subset_union_right⟩⟩
    · rw [Finset.card_insert_of_notMem (by simp [ne_of_lt hxy, hCL]),
        Finset.card_insert_of_notMem hCR, hCcard]
  have hOutsideNo4 (ψ : TripleColoring n) (L R V : Finset (Fin n))
      (hd : HasDeepBelowSplit ψ L R) (hVR : V ⊆ R)
      (hno5 : ¬ContainsCapSet ψ (L ∪ R) 5)
      (x : Fin n) (hxL : x ∈ L)
      (hside : (∀ z ∈ V, x ≤ z) ∨ ∀ z ∈ V, z ≤ x) : ¬ContainsCapSet ψ V 4 := by
    rintro ⟨C, hCV, hCcard, hCcap⟩
    exact hno5 (hd.containsCapSet_succ_of_lower_endpoint (hCV.trans hVR)
      hCcard hCcap hxL (hside.imp
        (fun h z hz ↦ h z (hCV hz)) (fun h z hz ↦ h z (hCV hz))))
  have hGapOutsideCup (ψ : TripleColoring n) (L R V : Finset (Fin n))
      (hd : HasDeepBelowSplit ψ L R) (hVR : V ⊆ R) (q0 x : Fin n)
      (hxL : x ∈ L)
      (hleft0 : ¬ContainsCapSet ψ ((L ∪ R).filter (fun z ↦ z < q0)) 4)
      (hright0 : ¬ContainsCapSet ψ ((L ∪ R).filter (fun z ↦ q0 < z)) 4)
      (hside : (x < q0 ∧ ∀ z ∈ V, z < x) ∨ (q0 < x ∧ ∀ z ∈ V, x < z)) :
      IsCupSet ψ V := by
    apply isCupSet_iff_not_containsCapSet_three.mpr
    rintro ⟨C, hCV, hCcard, hCcap⟩
    rcases hside with ⟨hxq, hzx⟩ | ⟨hqx, hxz⟩
    · have hxC : x ∉ C := fun hx ↦ (ne_of_lt (hzx x (hCV hx))) rfl
      refine hleft0 ⟨insert x C, ?_, ?_,
        hd.insert_lower_isCapSet_of_isRightSweepEndpoint (hCV.trans hVR) hCcap hxL
          (fun z hz ↦ (hzx z (hCV hz)).le)⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hxL, hxq⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (hVR (hCV hz)),
          (hzx z (hCV hz)).trans hxq⟩
      · rw [Finset.card_insert_of_notMem hxC, hCcard]
    · have hxC : x ∉ C := fun hx ↦ (ne_of_lt (hxz x (hCV hx))) rfl
      refine hright0 ⟨insert x C, ?_, ?_,
        hd.insert_lower_isCapSet_of_isLeftSweepEndpoint (hCV.trans hVR) hCcap hxL
          (fun z hz ↦ (hxz z (hCV hz)).le)⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hxL, hqx⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (hVR (hCV hz)),
          hqx.trans (hxz z (hCV hz))⟩
      · rw [Finset.card_insert_of_notMem hxC, hCcard]
  have hcore (ψ : TripleColoring n) (L R : Finset (Fin n)) (q0 x0 x1 : Fin n)
      (hLne : L.Nonempty) (hRne : R.Nonempty) (hd : HasDeepBelowSplit ψ L R)
      (hq0 : q0 ∉ L ∪ R) (ho : OneChangeOn ψ (L ∪ R))
      (hl : ¬ContainsCapSet ψ ((L ∪ R).filter (fun x ↦ x < q0)) 4)
      (hr : ¬ContainsCapSet ψ ((L ∪ R).filter (fun x ↦ q0 < x)) 4)
      (hn5 : ¬ContainsCapSet ψ (L ∪ R) 5)
      (hnc : ¬ContainsCupSet ψ (L ∪ R) (k - 1))
      (hns : ¬ContainsStrongPolygonSet ψ (L ∪ R) k)
      (hx0 : x0 ∈ L ∪ R) (hx1 : x1 ∈ L ∪ R)
      (hmin : ∀ z ∈ L ∪ R, x0 ≤ z) (hmax : ∀ z ∈ L ∪ R, z ≤ x1)
      (hx0q : x0 < q0) (hqx1 : q0 < x1)
      (horient : x0 ∈ L ∨ (x1 ∈ R ∧ ∃ a ∈ L, a < q0)) :
      (L ∪ R).card ≤ H := by
    have hLsub : L ⊆ L ∪ R := Finset.subset_union_left
    have hRsub : R ⊆ L ∪ R := Finset.subset_union_right
    have hdis := Finset.disjoint_left.mp hd.disjoint
    have hneq {x y : Fin n} (hx : x ∈ L) (hy : y ∈ R) : x ≠ y := by
      rintro rfl
      exact hdis hx hy
    have hqn {x : Fin n} (hx : x ∈ L ∪ R) : x ≠ q0 := by
      rintro rfl
      exact hq0 hx
    have hSquare (V : Finset (Fin n)) (v : ℕ) (hv : 2 ≤ v)
        (hVU : V ⊆ L ∪ R) (hno : ¬ContainsCupSet ψ V v) : V.card ≤ (v - 1)^2 :=
      card_le_square_of_oneChange_gap_no_capFive_no_cup hv (fun h ↦ hq0 (hVU h))
        (ho.mono hVU)
        (fun h ↦ hl (FinsetPolygon.ContainsCapSet.mono h (Finset.filter_subset_filter _ hVU)))
        (fun h ↦ hr (FinsetPolygon.ContainsCapSet.mono h (Finset.filter_subset_filter _ hVU)))
        (fun h ↦ hn5 (FinsetPolygon.ContainsCapSet.mono h hVU)) hno
    have hTri (V : Finset (Fin n)) (v : ℕ) (hVU : V ⊆ L ∪ R)
        (hno4 : ¬ContainsCapSet ψ V 4) (hno : ¬ContainsCupSet ψ V v) :
        V.card ≤ Nat.choose v 2 :=
      card_le_choose_of_oneChange_no_capFour_no_cup (ho.mono hVU) hno4 hno
    have hCouple (b : ℕ) (hb : b ≤ k) (hcap : ContainsCapSet ψ R b) :
        ¬ContainsCupSet ψ L (k - b) := by
      obtain ⟨D, hDR, hDcard, hDcap⟩ := hcap
      rintro ⟨C, hCL, hCcard, hCcup⟩
      exact hns (hd.containsStrongPolygonSet_of_cup_cap hCL hDR hCcup hDcap (by omega))
    have hLno1 : ¬ContainsCupSet ψ L (k - 1) :=
      fun h ↦ hnc (FinsetPolygon.ContainsCupSet.mono h hLsub)
    have hRno1 : ¬ContainsCupSet ψ R (k - 1) :=
      fun h ↦ hnc (FinsetPolygon.ContainsCupSet.mono h hRsub)
    have hcard : (L ∪ R).card = L.card + R.card := Finset.card_union_of_disjoint hd.disjoint
    rw [hcard]
    by_cases hx0L : x0 ∈ L
    · by_cases hx1L : x1 ∈ L
      · -- Both outer points are lower: the upper block is a cup.
        have hRcup : IsCupSet ψ R := hBetweenCup ψ L R R hd (Finset.Subset.refl _) hn5
          x0 x1 hx0L hx1L (hx0q.trans hqx1)
          (fun z hz ↦ lt_of_le_of_ne (hmin z (hRsub hz)) (hneq hx0L hz))
          (fun z hz ↦ lt_of_le_of_ne (hmax z (hRsub hz)) (hneq hx1L hz).symm)
        have hRsize := hcupCard ψ (L ∪ R) R (k - 1) hnc hRsub hRcup
        by_cases hRtwo : 2 ≤ R.card
        · obtain ⟨D, hDR, hDcard⟩ := Finset.exists_subset_card_eq hRtwo
          have hLno2 := hCouple 2 (by omega) ⟨D, hDR, hDcard, hsmall ψ D (by omega)⟩
          have hLsq := hSquare L (k - 2) (by omega) hLsub hLno2
          have he : k - 2 - 1 = k - 3 := by omega
          rw [he] at hLsq
          omega
        · obtain ⟨b, hbR⟩ := hRne
          have hRone : R.card = 1 := by have := Finset.card_pos.mpr ⟨b, hbR⟩; omega
          have hstraddle : ∀ C : Finset (Fin n), C ⊆ L → C.card = k - 2 → IsCupSet ψ C →
              (∃ x ∈ C, x < b) ∧ ∃ y ∈ C, b < y := by
            intro C hCL hCcard hCcup
            exact hd.cup_straddles_upper_of_not_containsCupSet_succ hCL hCcard hCcup hbR
              (by simpa only [show k - 2 + 1 = k - 1 by omega] using hnc)
          have hmark := card_le_mul_of_oneChange_gap_no_capFive_straddled_cups
            (show 3 ≤ k - 2 by omega) (fun h ↦ hq0 (hLsub h)) (ho.mono hLsub)
            (fun h ↦ hl (FinsetPolygon.ContainsCapSet.mono h (Finset.filter_subset_filter _ hLsub)))
            (fun h ↦ hr (FinsetPolygon.ContainsCapSet.mono h (Finset.filter_subset_filter _ hLsub)))
            (fun h ↦ hn5 (FinsetPolygon.ContainsCapSet.mono h hLsub))
            (by simpa only [show k - 2 + 1 = k - 1 by omega] using hLno1) hstraddle
          have he : k - 2 = (k - 3) + 1 := by omega
          have hm : (k - 2) * (k - 2 - 1) = (k - 3)^2 + (k - 3) := by
            rw [show k - 2 - 1 = k - 3 by omega, he]
            ring
          rw [hm] at hmark
          omega
      · -- Lower minimum, upper maximum.
        have hx1R : x1 ∈ R := (Finset.mem_union.mp hx1).resolve_left hx1L
        have hRno4 := hOutsideNo4 ψ L R R hd (Finset.Subset.refl _) hn5 x0 hx0L
          (Or.inl (fun z hz ↦ hmin z (hRsub hz)))
        have hLno2 : ¬ContainsCupSet ψ L (k - 2) := by
          rintro ⟨C, hCL, hCcard, hCcup⟩
          have he := hd.containsCupSet_succ_of_upper_endpoint hCL hCcard hCcup hx1R
            (Or.inr (fun z hz ↦ hmax z (hLsub (hCL hz))))
          exact hnc (by simpa only [show k - 2 + 1 = k - 1 by omega] using he)
        by_cases hRno3 : ¬ContainsCapSet ψ R 3
        · have hRcup := isCupSet_iff_not_containsCapSet_three.mpr hRno3
          have hRb := hcupCard ψ (L ∪ R) R (k - 1) hnc hRsub hRcup
          have hLb := hSquare L (k - 2) (by omega) hLsub hLno2
          rw [show k - 2 - 1 = k - 3 by omega] at hLb
          omega
        · have hRcap3 : ContainsCapSet ψ R 3 := by push Not at hRno3; exact hRno3
          have hLno3 := hCouple 3 (by omega) hRcap3
          by_cases hLleft : ∀ z ∈ L, z < q0
          · have hLno4 : ¬ContainsCapSet ψ L 4 := by
              intro h
              exact hl (FinsetPolygon.ContainsCapSet.mono h
                (fun z hz ↦ Finset.mem_filter.mpr ⟨hLsub hz, hLleft z hz⟩))
            have hLb := hTri L (k - 3) hLsub hLno4 hLno3
            have hRb := hTri R (k - 1) hRsub hRno4 hRno1
            dsimp [H]
            omega
          · push Not at hLleft
            obtain ⟨z, hzL, hqz⟩ := hLleft
            let a := L.max' hLne
            have haL : a ∈ L := Finset.max'_mem _ _
            have hamax : ∀ z ∈ L, z ≤ a := fun z hz ↦ Finset.le_max' _ _ hz
            have hqa : q0 < a := by have := hamax z hzL; have := hqn (hLsub hzL); omega
            let P := R.filter (fun z ↦ z < a)
            let Q := R.filter (fun z ↦ a < z)
            have hPR : P ⊆ R := Finset.filter_subset _ _
            have hQR : Q ⊆ R := Finset.filter_subset _ _
            have hPQ : P ∪ Q = R := by
              ext z
              simp only [P, Q, Finset.mem_union, Finset.mem_filter]
              constructor
              · exact fun h ↦ h.elim And.left And.left
              · intro hz
                have := hneq haL hz
                by_cases hza : z < a
                · exact Or.inl ⟨hz, hza⟩
                · exact Or.inr ⟨hz, by omega⟩
            have hsep : ∀ z ∈ P, ∀ w ∈ Q, z < w := by
              intro z hz w hw
              exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2
            have hPcup := hBetweenCup ψ L R P hd hPR hn5 x0 a hx0L haL
              (hx0q.trans hqa)
              (fun z hz ↦ lt_of_le_of_ne (hmin z (hRsub (hPR hz))) (hneq hx0L (hPR hz)))
              (fun z hz ↦ (Finset.mem_filter.mp hz).2)
            have hQcup := hGapOutsideCup ψ L R Q hd hQR q0 a haL hl hr
              (Or.inr ⟨hqa, fun z hz ↦ (Finset.mem_filter.mp hz).2⟩)
            have hoPQ : OneChangeOn ψ (P ∪ Q) := by
              rw [hPQ]
              exact ho.mono hRsub
            have htwo := (twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup
              (show 2 ≤ k - 1 by omega) hoPQ
              hsep hPcup hQcup (by simpa only [hPQ] using hRno4)
              (by simpa only [hPQ] using hRno1)).1
            have hPQdis : Disjoint P Q := Finset.disjoint_left.mpr (fun z hz hw ↦
              (lt_irrefl z) (hsep z hz z hw))
            have hRb : R.card ≤ 2 * (k - 1) - 3 := by
              rw [← hPQ, Finset.card_union_of_disjoint hPQdis]
              exact htwo
            have hLb := hSquare L (k - 3) (by omega) hLsub hLno3
            rw [show k - 3 - 1 = k - 4 by omega] at hLb
            rw [hH]
            have he : k - 3 = k - 4 + 1 := by omega
            have he2 : k - 2 = k - 4 + 2 := by omega
            have hb : R.card ≤ 2 * (k - 4) + 3 := by omega
            rw [he, he2]
            nlinarith
    · -- Both outer points are upper, with a lower point left of the gap.
      have hx0R : x0 ∈ R := (Finset.mem_union.mp hx0).resolve_left hx0L
      obtain ⟨hx1R, a0, ha0L, ha0q⟩ := horient.resolve_left hx0L
      let a := L.min' hLne
      let b := L.max' hLne
      have haL : a ∈ L := Finset.min'_mem _ _
      have hbL : b ∈ L := Finset.max'_mem _ _
      have hamin : ∀ z ∈ L, a ≤ z := fun z hz ↦ Finset.min'_le _ _ hz
      have hbmax : ∀ z ∈ L, z ≤ b := fun z hz ↦ Finset.le_max' _ _ hz
      have haq : a < q0 := (hamin a0 ha0L).trans_lt ha0q
      have hLno3 : ¬ContainsCupSet ψ L (k - 3) := by
        rintro ⟨C, hCL, hCcard, hCcup⟩
        have hx0C : x0 ∉ C := fun h ↦ hdis (hCL h) hx0R
        have hx1C : x1 ∉ C := fun h ↦ hdis (hCL h) hx1R
        refine hnc ⟨insert x0 (insert x1 C), ?_, ?_,
          hCupEnds ψ L R C hd hCL hCcup x0 x1 hx0R hx1R (hx0q.trans hqx1)
            (fun z hz ↦ lt_of_le_of_ne (hmin z (hLsub (hCL hz))) (hneq (hCL hz) hx0R).symm)
            (fun z hz ↦ lt_of_le_of_ne (hmax z (hLsub (hCL hz))) (hneq (hCL hz) hx1R))⟩
        · exact Finset.insert_subset_iff.mpr ⟨hx0, Finset.insert_subset_iff.mpr ⟨hx1,
            hCL.trans hLsub⟩⟩
        · rw [Finset.card_insert_of_notMem (by simp [ne_of_lt (hx0q.trans hqx1), hx0C]),
            Finset.card_insert_of_notMem hx1C, hCcard]
          omega
      by_cases hRno3 : ¬ContainsCapSet ψ R 3
      · have hRcup := isCupSet_iff_not_containsCapSet_three.mpr hRno3
        have hRb := hcupCard ψ (L ∪ R) R (k - 1) hnc hRsub hRcup
        have hLb := hSquare L (k - 3) (by omega) hLsub hLno3
        rw [show k - 3 - 1 = k - 4 by omega] at hLb
        rw [hH]
        have he : k - 3 = k - 4 + 1 := by omega
        have he2 : k - 2 = k - 4 + 2 := by omega
        have hb : R.card ≤ k - 4 + 2 := by omega
        rw [he, he2]
        nlinarith
      · by_cases hLno4 : ¬ContainsCapSet ψ L 4
        · by_cases hRno4 : ¬ContainsCapSet ψ R 4
          · have hLb := hTri L (k - 3) hLsub hLno4 hLno3
            have hRb := hTri R (k - 1) hRsub hRno4 hRno1
            dsimp [H]
            omega
          · have hRcap4 : ContainsCapSet ψ R 4 := by push Not at hRno4; exact hRno4
            have hLnoCup4 := hCouple 4 (by omega) hRcap4
            have hLb := hTri L (k - 4) hLsub hLno4 hLnoCup4
            let P := R.filter (fun z ↦ z < a)
            let Q := R.filter (fun z ↦ a < z)
            have hPR : P ⊆ R := Finset.filter_subset _ _
            have hQR : Q ⊆ R := Finset.filter_subset _ _
            have hPQ : P ∪ Q = R := by
              ext z
              simp only [P, Q, Finset.mem_union, Finset.mem_filter]
              constructor
              · exact fun h ↦ h.elim And.left And.left
              · intro hz
                have := hneq haL hz
                by_cases hza : z < a
                · exact Or.inl ⟨hz, hza⟩
                · exact Or.inr ⟨hz, by omega⟩
            have hsep : ∀ z ∈ P, ∀ w ∈ Q, z < w := by
              intro z hz w hw
              exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2
            have hPcup := hGapOutsideCup ψ L R P hd hPR q0 a haL hl hr
              (Or.inl ⟨haq, fun z hz ↦ (Finset.mem_filter.mp hz).2⟩)
            have hQno4 := hOutsideNo4 ψ L R Q hd hQR hn5 a haL
              (Or.inl (fun z hz ↦ (Finset.mem_filter.mp hz).2.le))
            have hoPQ : OneChangeOn ψ (P ∪ Q) := by rw [hPQ]; exact ho.mono hRsub
            have hR2 := card_le_choose_add_of_ordered_cup_prefix_no_capFive_no_cup_no_strong
              (show 4 ≤ k - 1 by omega) hsep hPcup hoPQ hQno4
              (by rw [hPQ]; exact fun h ↦ hn5 (FinsetPolygon.ContainsCapSet.mono h hRsub))
              (by rw [hPQ]; exact hRno1)
              (by rw [hPQ, show k - 1 + 1 = k by omega]
                  exact fun h ↦ hns (FinsetPolygon.ContainsStrongPolygonSet.mono h hRsub))
            have hPQdis : Disjoint P Q := Finset.disjoint_left.mpr (fun z hz hw ↦
              (lt_irrefl z) (hsep z hz z hw))
            have hRb : R.card ≤ Nat.choose (k - 1) 2 + (k - 1 - 3) := by
              rw [← hPQ, Finset.card_union_of_disjoint hPQdis]
              exact hR2
            have hp := Nat.choose_succ_succ' (k - 4) 1
            simp only [show k - 4 + 1 = k - 3 by omega, Nat.choose_one_right, Nat.reduceAdd] at hp
            dsimp [H]
            omega
        · have hLcap4 : ContainsCapSet ψ L 4 := by push Not at hLno4; exact hLno4
          have hqb : q0 < b := by
            by_contra h
            have hbq : b ≤ q0 := le_of_not_gt h
            apply hl
            exact FinsetPolygon.ContainsCapSet.mono hLcap4 (fun z hz ↦
              Finset.mem_filter.mpr ⟨hLsub hz, by have := hbmax z hz; have := hqn (hLsub hz); omega⟩)
          let P := R.filter (fun z ↦ z < a)
          let Q := R.filter (fun z ↦ a < z ∧ z < b)
          let T := R.filter (fun z ↦ b < z)
          have hPR : P ⊆ R := Finset.filter_subset _ _
          have hQR : Q ⊆ R := Finset.filter_subset _ _
          have hTR : T ⊆ R := Finset.filter_subset _ _
          have hPQ : ∀ z ∈ P, ∀ w ∈ Q, z < w := by
            intro z hz w hw
            exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.1
          have hQT : ∀ z ∈ Q, ∀ w ∈ T, z < w := by
            intro z hz w hw
            exact (Finset.mem_filter.mp hz).2.2.trans (Finset.mem_filter.mp hw).2
          have hPT : ∀ z ∈ P, ∀ w ∈ T, z < w := by
            intro z hz w hw
            exact ((Finset.mem_filter.mp hz).2.trans (haq.trans hqb)).trans (Finset.mem_filter.mp hw).2
          have hPQT : P ∪ Q ∪ T = R := by
            ext z
            simp only [P, Q, T, Finset.mem_union, Finset.mem_filter]
            constructor
            · intro h
              rcases h with (h | h) | h <;> exact h.1
            · intro hz
              have := hneq haL hz
              have := hneq hbL hz
              by_cases hza : z < a
              · exact Or.inl (Or.inl ⟨hz, hza⟩)
              by_cases hzb : z < b
              · exact Or.inl (Or.inr ⟨hz, by omega, hzb⟩)
              · exact Or.inr ⟨hz, by omega⟩
          have hdisPQ : Disjoint P Q := Finset.disjoint_left.mpr (fun z hz hw ↦
            (lt_irrefl z) (hPQ z hz z hw))
          have hdisPQT : Disjoint (P ∪ Q) T := by
            apply Finset.disjoint_left.mpr
            intro z hz hw
            rcases Finset.mem_union.mp hz with hz | hz
            · exact (lt_irrefl z) (hPT z hz z hw)
            · exact (lt_irrefl z) (hQT z hz z hw)
          have hRcard : R.card = P.card + Q.card + T.card := by
            rw [← hPQT, Finset.card_union_of_disjoint hdisPQT,
              Finset.card_union_of_disjoint hdisPQ]
          have hPcup := hGapOutsideCup ψ L R P hd hPR q0 a haL hl hr
            (Or.inl ⟨haq, fun z hz ↦ (Finset.mem_filter.mp hz).2⟩)
          have hQcup := hBetweenCup ψ L R Q hd hQR hn5 a b haL hbL (haq.trans hqb)
            (fun z hz ↦ (Finset.mem_filter.mp hz).2.1)
            (fun z hz ↦ (Finset.mem_filter.mp hz).2.2)
          have hTcup := hGapOutsideCup ψ L R T hd hTR q0 b hbL hl hr
            (Or.inr ⟨hqb, fun z hz ↦ (Finset.mem_filter.mp hz).2⟩)
          by_cases hRno4 : ¬ContainsCapSet ψ R 4
          · have hoPQT : OneChangeOn ψ (P ∪ Q ∪ T) := by rw [hPQT]; exact ho.mono hRsub
            have hthree := threeCupBlocks_card_le_of_oneChange_no_capFour_no_cup
              (show 4 ≤ k - 1 by omega) hoPQT hPQ hQT hPT hPcup hQcup hTcup
              (by rw [hPQT]; exact hRno4) (by rw [hPQT]; exact hRno1)
            have hLb := hSquare L (k - 3) (by omega) hLsub hLno3
            rw [show k - 3 - 1 = k - 4 by omega] at hLb
            have hRb : R.card ≤ 3 * (k - 1) - 6 := by rw [hRcard]; exact hthree
            rw [hH]
            have he : k - 3 = k - 4 + 1 := by omega
            have he2 : k - 2 = k - 4 + 2 := by omega
            have hb : R.card ≤ 3 * (k - 4) + 3 := by omega
            rw [he, he2]
            nlinarith
          · have hRcap4 : ContainsCapSet ψ R 4 := by push Not at hRno4; exact hRno4
            have hLnoCup4 := hCouple 4 (by omega) hRcap4
            have hPQsub : P ∪ Q ⊆ R := Finset.union_subset hPR hQR
            have hPQno4 := hOutsideNo4 ψ L R (P ∪ Q) hd hPQsub hn5 b hbL
              (Or.inr (by
                intro z hz
                rcases Finset.mem_union.mp hz with hz | hz
                · exact ((Finset.mem_filter.mp hz).2.trans (haq.trans hqb)).le
                · exact (Finset.mem_filter.mp hz).2.2.le))
            have hoPQ : OneChangeOn ψ (P ∪ Q) := ho.mono (hPQsub.trans hRsub)
            have htwo := (twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup
              (show 2 ≤ k - 1 by omega) hoPQ hPQ hPcup hQcup hPQno4
              (fun h ↦ hnc (FinsetPolygon.ContainsCupSet.mono h (hPQsub.trans hRsub)))).1
            have hTb := hcupCard ψ (L ∪ R) T (k - 1) hnc (hTR.trans hRsub) hTcup
            have hLb := hSquare L (k - 4) (by omega) hLsub hLnoCup4
            rw [show k - 4 - 1 = k - 5 by omega] at hLb
            have hRb : R.card ≤ 3 * (k - 5) + 8 := by rw [hRcard]; omega
            rw [hH]
            have he : k - 3 = k - 5 + 2 := by omega
            have he2 : k - 2 = k - 5 + 3 := by omega
            have hdif : 1 ≤ k - 5 := by omega
            rw [he, he2]
            nlinarith
  have hUe : (A ∪ B).Nonempty := hAne.mono Finset.subset_union_left
  let x0 := (A ∪ B).min' hUe
  let x1 := (A ∪ B).max' hUe
  have hx0 : x0 ∈ A ∪ B := Finset.min'_mem _ _
  have hx1 : x1 ∈ A ∪ B := Finset.max'_mem _ _
  have hmin : ∀ z ∈ A ∪ B, x0 ≤ z := fun z hz ↦ Finset.min'_le _ _ hz
  have hmax : ∀ z ∈ A ∪ B, z ≤ x1 := fun z hz ↦ Finset.le_max' _ _ hz
  have hqn {z : Fin n} (hz : z ∈ A ∪ B) : z ≠ q := by rintro rfl; exact hq hz
  by_cases hx0q : x0 < q
  · by_cases hqx1 : q < x1
    · by_cases horient : x0 ∈ A ∨ (x1 ∈ B ∧ ∃ a ∈ A, a < q)
      · exact hcore χ A B q x0 x1 hAne hBne hdeep hq hone hleft hright
          hnoCap hnoCup hnoStrong hx0 hx1 hmin hmax hx0q hqx1 horient
      · let L := A.image Fin.rev
        let R := B.image Fin.rev
        have hmem (V : Finset (Fin n)) (z : Fin n) : z ∈ V.image Fin.rev ↔ z.rev ∈ V := by
          constructor
          · intro hz
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
            simpa only [Fin.rev_rev] using hw
          · intro hz
            exact Finset.mem_image.mpr ⟨z.rev, hz, by simp⟩
        have hUR : L ∪ R = (A ∪ B).image Fin.rev := (Finset.image_union A B).symm
        rcases reverseColor_set_invariants χ with
          ⟨hrevO, _, _, _, hrevCup, hrevCap, hrevStrong, hrevDeep, _⟩
        have hdRev : HasDeepBelowSplit (reverseColor χ) L R := (hrevDeep A B).mp hdeep
        have hqRev : q.rev ∉ L ∪ R := by
          rw [hUR, hmem]
          simpa only [Fin.rev_rev] using hq
        have hoRev : OneChangeOn (reverseColor χ) (L ∪ R) := by
          rw [hUR]
          exact (hrevO (A ∪ B)).mp hone
        have hleftSet : (L ∪ R).filter (fun z ↦ z < q.rev) =
            ((A ∪ B).filter (fun z ↦ q < z)).image Fin.rev := by
          ext z
          rw [hUR]
          simp only [Finset.mem_filter, hmem, Fin.lt_rev_iff]
        have hrightSet : (L ∪ R).filter (fun z ↦ q.rev < z) =
            ((A ∪ B).filter (fun z ↦ z < q)).image Fin.rev := by
          ext z
          rw [hUR]
          simp only [Finset.mem_filter, hmem, Fin.rev_lt_iff]
        have hlRev : ¬ContainsCapSet (reverseColor χ) ((L ∪ R).filter (fun z ↦ z < q.rev)) 4 := by
          rw [hleftSet]
          exact fun h ↦ hright ((hrevCap _ _).mpr h)
        have hrRev : ¬ContainsCapSet (reverseColor χ) ((L ∪ R).filter (fun z ↦ q.rev < z)) 4 := by
          rw [hrightSet]
          exact fun h ↦ hleft ((hrevCap _ _).mpr h)
        have hn5Rev : ¬ContainsCapSet (reverseColor χ) (L ∪ R) 5 := by
          rw [hUR]
          exact fun h ↦ hnoCap ((hrevCap _ _).mpr h)
        have hncRev : ¬ContainsCupSet (reverseColor χ) (L ∪ R) (k - 1) := by
          rw [hUR]
          exact fun h ↦ hnoCup ((hrevCup _ _).mpr h)
        have hnsRev : ¬ContainsStrongPolygonSet (reverseColor χ) (L ∪ R) k := by
          rw [hUR]
          exact fun h ↦ hnoStrong ((hrevStrong _ _).mpr h)
        have hx1Rev : x1.rev ∈ L ∪ R := by rw [hUR, hmem]; simpa only [Fin.rev_rev] using hx1
        have hx0Rev : x0.rev ∈ L ∪ R := by rw [hUR, hmem]; simpa only [Fin.rev_rev] using hx0
        have hminRev : ∀ z ∈ L ∪ R, x1.rev ≤ z := by
          intro z hz
          rw [hUR, hmem] at hz
          exact Fin.rev_le_iff.mpr (hmax z.rev hz)
        have hmaxRev : ∀ z ∈ L ∪ R, z ≤ x0.rev := by
          intro z hz
          rw [hUR, hmem] at hz
          exact Fin.le_rev_iff.mpr (hmin z.rev hz)
        have hOrientRev : x1.rev ∈ L ∨ (x0.rev ∈ R ∧ ∃ a ∈ L, a < q.rev) := by
          by_cases hx1A : x1 ∈ A
          · exact Or.inl (Finset.mem_image.mpr ⟨x1, hx1A, rfl⟩)
          have hx1B : x1 ∈ B := (Finset.mem_union.mp hx1).resolve_left hx1A
          have hx0A : x0 ∉ A := fun h ↦ horient (Or.inl h)
          have hx0B : x0 ∈ B := (Finset.mem_union.mp hx0).resolve_left hx0A
          have hnoLeft : ¬∃ a ∈ A, a < q := fun h ↦ horient (Or.inr ⟨hx1B, h⟩)
          obtain ⟨a, haA⟩ := hAne
          have hqa : q < a := by
            by_contra h
            apply hnoLeft
            exact ⟨a, haA, by have := hqn (Finset.mem_union_left _ haA); omega⟩
          exact Or.inr ⟨Finset.mem_image.mpr ⟨x0, hx0B, rfl⟩,
            a.rev, Finset.mem_image.mpr ⟨a, haA, rfl⟩, by simpa using hqa⟩
        have hbound := hcore (reverseColor χ) L R q.rev x1.rev x0.rev
          (hAne.image _) (hBne.image _) hdRev hqRev hoRev hlRev hrRev hn5Rev hncRev hnsRev
          hx1Rev hx0Rev hminRev hmaxRev (by simpa using hqx1) (by simpa using hx0q) hOrientRev
        rw [hUR, Finset.card_image_of_injective _ Fin.rev_injective] at hbound
        exact hbound
    · have hU4 : ¬ContainsCapSet χ (A ∪ B) 4 := by
        intro h
        exact hleft (FinsetPolygon.ContainsCapSet.mono h (by
          intro z hz
          exact Finset.mem_filter.mpr ⟨hz, by have := hmax z hz; have := hqn hz; omega⟩))
      have htri := card_le_choose_of_oneChange_no_capFour_no_cup hone hU4 hnoCup
      omega
  · have hU4 : ¬ContainsCapSet χ (A ∪ B) 4 := by
      intro h
      exact hright (FinsetPolygon.ContainsCapSet.mono h (by
        intro z hz
        exact Finset.mem_filter.mpr ⟨hz, by have := hmin z hz; have := hqn hz; omega⟩))
    have htri := card_le_choose_of_oneChange_no_capFour_no_cup hone hU4 hnoCup
    omega

end ErdosSzekeres
