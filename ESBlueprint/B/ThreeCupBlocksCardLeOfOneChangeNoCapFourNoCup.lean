import ESBlueprint.B.TwoCupBlocksCardAndExtensionsOfOneChangeNoCapFourNoCup

namespace ErdosSzekeres

/-- Three ordered cup blocks in a one-change set avoiding four-caps and u-cups have at most 3u-6 points for u at least four. Full blocks force boundary extensions, and the two-cup bound or a glued u-cup gives the extra saving.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem threeCupBlocks_card_le_of_oneChange_no_capFour_no_cup {n u : ℕ} {χ : TripleColoring n} {P Q R : Finset (Fin n)} (hu : 4 ≤ u) (hone : OneChangeOn χ (P ∪ Q ∪ R)) (hPQ : ∀ x ∈ P, ∀ y ∈ Q, x < y) (hQR : ∀ y ∈ Q, ∀ z ∈ R, y < z) (hPR : ∀ x ∈ P, ∀ z ∈ R, x < z) (hPcup : IsCupSet χ P) (hQcup : IsCupSet χ Q) (hRcup : IsCupSet χ R) (hnoCap : ¬ContainsCapSet χ (P ∪ Q ∪ R) 4) (hnoCup : ¬ContainsCupSet χ (P ∪ Q ∪ R) u) : P.card + Q.card + R.card ≤ 3 * u - 6 := by
  classical
  have hPsub : P ⊆ P ∪ Q ∪ R := Finset.subset_union_left.trans Finset.subset_union_left
  have hQsub : Q ⊆ P ∪ Q ∪ R := Finset.subset_union_right.trans Finset.subset_union_left
  have hRsub : R ⊆ P ∪ Q ∪ R := Finset.subset_union_right
  have hbound : ∀ (A : Finset (Fin n)), A ⊆ P ∪ Q ∪ R → IsCupSet χ A → A.card < u := by
    intro A hAs hAcup
    by_contra h
    obtain ⟨D, hDA, hDcard⟩ := Finset.exists_subset_card_eq (show u ≤ A.card by omega)
    exact hnoCup ⟨D, hDA.trans hAs, hDcard, FinsetPolygon.IsCupSet.mono hAcup hDA⟩
  let two (A B : Finset (Fin n)) (hAB : A ∪ B ⊆ P ∪ Q ∪ R)
      (ho : ∀ x ∈ A, ∀ y ∈ B, x < y) (hA : IsCupSet χ A) (hB : IsCupSet χ B) :=
    twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup
      (show 2 ≤ u by omega) (hone.mono hAB) ho hA hB
      (fun h ↦ hnoCap (FinsetPolygon.ContainsCapSet.mono h hAB))
      (fun h ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono h hAB))
  have hPQsub := Finset.union_subset hPsub hQsub
  have hQRsub := Finset.union_subset hQsub hRsub
  have hPRsub := Finset.union_subset hPsub hRsub
  have hPQcount := (two P Q hPQsub hPQ hPcup hQcup).1
  have hQRcount := (two Q R hQRsub hQR hQcup hRcup).1
  have hPRcount := (two P R hPRsub hPR hPcup hRcup).1
  have hPbound := hbound P hPsub hPcup
  have hQbound := hbound Q hQsub hQcup
  have hRbound := hbound R hRsub hRcup
  rcases P.eq_empty_or_nonempty with hPempty | hPne
  · have hPzero : P.card = 0 := by simp [hPempty]
    omega
  rcases Q.eq_empty_or_nonempty with hQempty | hQne
  · have hQzero : Q.card = 0 := by simp [hQempty]
    omega
  rcases R.eq_empty_or_nonempty with hRempty | hRne
  · have hRzero : R.card = 0 := by simp [hRempty]
    omega
  let p := P.max' hPne
  let q₁ := Q.min' hQne
  let q₂ := Q.max' hQne
  let r := R.min' hRne
  have hp : p ∈ P := Finset.max'_mem _ _
  have hq₁ : q₁ ∈ Q := Finset.min'_mem _ _
  have hq₂ : q₂ ∈ Q := Finset.max'_mem _ _
  have hr : r ∈ R := Finset.min'_mem _ _
  have hPmax : ∀ x ∈ P, x ≤ p := fun x hx ↦ Finset.le_max' _ x hx
  have hQmin : ∀ y ∈ Q, q₁ ≤ y := fun y hy ↦ Finset.min'_le _ y hy
  have hQmax : ∀ y ∈ Q, y ≤ q₂ := fun y hy ↦ Finset.le_max' _ y hy
  have hRmin : ∀ z ∈ R, r ≤ z := fun z hz ↦ Finset.min'_le _ z hz
  have hpNotQ : p ∉ Q := fun hpQ ↦ (lt_irrefl p) (hPQ p hp p hpQ)
  have hrNotQ : r ∉ Q := fun hrQ ↦ (lt_irrefl r) (hQR r hrQ r hr)
  have hq₁NotP : q₁ ∉ P := fun hqP ↦ (lt_irrefl q₁) (hPQ q₁ hqP q₁ hq₁)
  have hq₂NotR : q₂ ∉ R := fun hqR ↦ (lt_irrefl q₂) (hQR q₂ hq₂ q₂ hqR)
  have hPQext := (two P Q hPQsub hPQ hPcup hQcup).2 p q₁ hp hq₁ hPmax hQmin
  have hQRext := (two Q R hQRsub hQR hQcup hRcup).2 q₂ r hq₂ hr hQmax hRmin
  have hleftSub : insert p Q ⊆ P ∪ Q ∪ R :=
    Finset.insert_subset_iff.mpr ⟨hPsub hp, hQsub⟩
  have hrightSub : insert r Q ⊆ P ∪ Q ∪ R :=
    Finset.insert_subset_iff.mpr ⟨hRsub hr, hQsub⟩
  have hbothSub : insert r (insert p Q) ⊆ P ∪ Q ∪ R :=
    Finset.insert_subset_iff.mpr ⟨hRsub hr, hleftSub⟩
  have hrNotLeft : r ∉ insert p Q := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_gt (hPR p hp r hr), hrNotQ⟩
  have hglue (hQcard : 2 ≤ Q.card) (hleftCup : IsCupSet χ (insert p Q))
      (hrightCup : IsCupSet χ (insert r Q)) : IsCupSet χ (insert r (insert p Q)) := by
    have hrest : (Q.erase q₂).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hq₂]
      omega
    let a := (Q.erase q₂).max' hrest
    have haErase : a ∈ Q.erase q₂ := Finset.max'_mem _ _
    have haQ : a ∈ Q := (Finset.mem_erase.mp haErase).2
    have haq : a < q₂ := by
      have := hQmax a haQ
      have := (Finset.mem_erase.mp haErase).1
      omega
    have hmax : ∀ y ∈ insert p Q, y ≤ q₂ := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hPQ p hp q₂ hq₂).le
      · exact hQmax y hy
    have hprev : ∀ y ∈ insert p Q, y < q₂ → y ≤ a := by
      intro y hy hyq
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hPQ p hp a haQ).le
      · exact Finset.le_max' _ y (Finset.mem_erase.mpr ⟨ne_of_lt hyq, hy⟩)
    exact monochromaticSet_insert_max_of_oneChange (Finset.mem_insert_of_mem haQ)
      (Finset.mem_insert_of_mem hq₂) haq (hQR q₂ hq₂ r hr) hmax hprev hleftCup
      (hone.mono hbothSub) (hrightCup _ (Finset.mem_insert_of_mem haQ)
        (Finset.mem_insert_of_mem hq₂) (Finset.mem_insert_self _ _))
  have hglueImpossible (hQcard : Q.card = u - 2)
      (hleftCup : IsCupSet χ (insert p Q)) (hrightCup : IsCupSet χ (insert r Q)) : False := by
    have h := hbound _ hbothSub (hglue (by omega) hleftCup hrightCup)
    rw [Finset.card_insert_of_notMem hrNotLeft, Finset.card_insert_of_notMem hpNotQ,
      hQcard] at h
    omega
  by_cases hQfull : Q.card = u - 1
  · have hcupA := hPQext.2.2 hQfull
    have hcupB := hQRext.2.1 hQfull
    have hq₁q₂ : q₁ < q₂ := Finset.min'_lt_max'_of_card Q (by omega)
    have hsubA : insert q₁ P ⊆ P ∪ Q ∪ R :=
      Finset.insert_subset_iff.mpr ⟨hQsub hq₁, hPsub⟩
    have hsubB : insert q₂ R ⊆ P ∪ Q ∪ R :=
      Finset.insert_subset_iff.mpr ⟨hQsub hq₂, hRsub⟩
    have horder : ∀ x ∈ insert q₁ P, ∀ y ∈ insert q₂ R, x < y := by
      intro x hx y hy
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hq₁q₂
        · exact hQR q₁ hq₁ y hy
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hPQ x hx q₂ hq₂
        · exact hPR x hx y hy
    have h := (two (insert q₁ P) (insert q₂ R) (Finset.union_subset hsubA hsubB)
      horder hcupA hcupB).1
    rw [Finset.card_insert_of_notMem hq₁NotP, Finset.card_insert_of_notMem hq₂NotR] at h
    omega
  by_cases hPfull : P.card = u - 1
  · have hQupper : Q.card ≤ u - 2 := by omega
    have hRupper : R.card ≤ u - 2 := by omega
    by_cases hQlow : Q.card ≤ u - 3
    · omega
    by_cases hRlow : R.card ≤ u - 3
    · omega
    have hQcard : Q.card = u - 2 := by omega
    have hRcard : R.card = u - 2 := by omega
    have hleftCup := hPQext.2.1 hPfull
    rcases hQRext.1 with hrightCup | hnewCup
    · exact (hglueImpossible hQcard hleftCup hrightCup).elim
    · have hsub : insert q₂ R ⊆ P ∪ Q ∪ R :=
        Finset.insert_subset_iff.mpr ⟨hQsub hq₂, hRsub⟩
      have horder : ∀ x ∈ P, ∀ y ∈ insert q₂ R, x < y := by
        intro x hx y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hPQ x hx q₂ hq₂
        · exact hPR x hx y hy
      have h := (two P (insert q₂ R) (Finset.union_subset hPsub hsub)
        horder hPcup hnewCup).1
      rw [Finset.card_insert_of_notMem hq₂NotR] at h
      omega
  by_cases hRfull : R.card = u - 1
  · have hPupper : P.card ≤ u - 2 := by omega
    have hQupper : Q.card ≤ u - 2 := by omega
    by_cases hPlow : P.card ≤ u - 3
    · omega
    by_cases hQlow : Q.card ≤ u - 3
    · omega
    have hPcard : P.card = u - 2 := by omega
    have hQcard : Q.card = u - 2 := by omega
    have hrightCup := hQRext.2.2 hRfull
    rcases hPQext.1 with hnewCup | hleftCup
    · have hsub : insert q₁ P ⊆ P ∪ Q ∪ R :=
        Finset.insert_subset_iff.mpr ⟨hQsub hq₁, hPsub⟩
      have horder : ∀ x ∈ insert q₁ P, ∀ y ∈ R, x < y := by
        intro x hx y hy
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hQR q₁ hq₁ y hy
        · exact hPR x hx y hy
      have h := (two (insert q₁ P) R (Finset.union_subset hsub hRsub)
        horder hnewCup hRcup).1
      rw [Finset.card_insert_of_notMem hq₁NotP] at h
      omega
    · exact (hglueImpossible hQcard hleftCup hrightCup).elim
  omega

end ErdosSzekeres
