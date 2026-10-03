import ESBlueprint.B.ThreeCupBlocksCardLeOfOneChangeNoCapFourNoCup
import ESBlueprint.B.IsStrongPolygonSetUnionOfCupCapCommonExtremes

namespace ErdosSzekeres

/-- Three ordered cups with four-cap-free adjacent pairs, pair counts at most 2k-4 and no strong k-polygon have total at most 3k-6. The sole violating size pattern k-1,k-3,k-1 forces boundary cup extensions whose remaining cap triples share endpoints with large cups.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup, ErdosSzekeres.isStrongPolygonSet_union_of_cup_cap_common_extremes
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs -/
theorem threeCupBlocks_card_le_of_oneChange_adjacent_no_capFour_no_strong_of_pair_bounds {n k : ℕ} {χ : TripleColoring n} {P Q R : Finset (Fin n)} (hk : 6 ≤ k) (hPQ : ∀ x ∈ P, ∀ y ∈ Q, x < y) (hQR : ∀ y ∈ Q, ∀ z ∈ R, y < z) (hPR : ∀ x ∈ P, ∀ z ∈ R, x < z) (hPcup : IsCupSet χ P) (hQcup : IsCupSet χ Q) (hRcup : IsCupSet χ R) (hone : OneChangeOn χ (P ∪ Q ∪ R)) (hPQnoCap : ¬ContainsCapSet χ (P ∪ Q) 4) (hQRnoCap : ¬ContainsCapSet χ (Q ∪ R) 4) (hPQcount : P.card + Q.card ≤ 2 * k - 4) (hQRcount : Q.card + R.card ≤ 2 * k - 4) (hnoStrong : ¬ContainsStrongPolygonSet χ (P ∪ Q ∪ R) k) : P.card + Q.card + R.card ≤ 3 * k - 6 := by
  classical
  let S := P ∪ Q ∪ R
  have hPsub : P ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hQsub : Q ⊆ S := Finset.subset_union_right.trans Finset.subset_union_left
  have hRsub : R ⊆ S := Finset.subset_union_right
  have hnoCup : ¬ContainsCupSet χ S k :=
    fun h ↦ hnoStrong (FinsetPolygon.ContainsCupSet.toContainsStrongPolygonSet h)
  have hbound (C : Finset (Fin n)) (hCs : C ⊆ S) (hCcup : IsCupSet χ C) : C.card < k := by
    by_contra h
    obtain ⟨D, hDC, hDcard⟩ := Finset.exists_subset_card_eq (show k ≤ C.card by omega)
    exact hnoCup ⟨D, hDC.trans hCs, hDcard, FinsetPolygon.IsCupSet.mono hCcup hDC⟩
  have hPb := hbound P hPsub hPcup
  have hQb := hbound Q hQsub hQcup
  have hRb := hbound R hRsub hRcup
  by_contra htotal
  have hPcard : P.card = k - 1 := by omega
  have hQcard : Q.card = k - 3 := by omega
  have hRcard : R.card = k - 1 := by omega
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
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
  have hPQsub : P ∪ Q ⊆ S := Finset.union_subset hPsub hQsub
  have hQRsub : Q ∪ R ⊆ S := Finset.union_subset hQsub hRsub
  have hPQext := (twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup
    (show 2 ≤ k by omega) (hone.mono hPQsub) hPQ hPcup hQcup hPQnoCap
    (fun h ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono h hPQsub))).2 p q₁ hp hq₁ hPmax hQmin
  have hQRext := (twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup
    (show 2 ≤ k by omega) (hone.mono hQRsub) hQR hQcup hRcup hQRnoCap
    (fun h ↦ hnoCup (FinsetPolygon.ContainsCupSet.mono h hQRsub))).2 q₂ r hq₂ hr hQmax hRmin
  have hleftCup : IsCupSet χ (insert p Q) := hPQext.2.1 hPcard
  have hrightCup : IsCupSet χ (insert r Q) := hQRext.2.2 hRcard
  have hleftSub : insert p Q ⊆ S := Finset.insert_subset_iff.mpr ⟨hPsub hp, hQsub⟩
  have hrightSub : insert r Q ⊆ S := Finset.insert_subset_iff.mpr ⟨hRsub hr, hQsub⟩
  have hbothSub : insert r (insert p Q) ⊆ S := Finset.insert_subset_iff.mpr ⟨hRsub hr, hleftSub⟩
  have hrNotLeft : r ∉ insert p Q := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_gt (hPR p hp r hr), hrNotQ⟩
  have hM : IsCupSet χ (insert r (insert p Q)) := by
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
  have hMcard : (insert r (insert p Q)).card = k - 1 := by
    rw [Finset.card_insert_of_notMem hrNotLeft, Finset.card_insert_of_notMem hpNotQ, hQcard]
    omega
  have hbridge {C D : Finset (Fin n)} {l t : Fin n}
      (hCs : C ⊆ S) (hDs : D ⊆ S) (hlt : l < t)
      (hlC : l ∈ C) (htC : t ∈ C) (hlD : l ∈ D) (htD : t ∈ D)
      (hspan : ∀ x ∈ C ∪ D, l ≤ x ∧ x ≤ t)
      (hCcup : IsCupSet χ C) (hDcap : IsCapSet χ D)
      (hCcard : C.card = k - 1) (hDcard : D.card = 3) : False := by
    have hsub := Finset.union_subset hCs hDs
    obtain ⟨hstrong, hinter⟩ := isStrongPolygonSet_union_of_cup_cap_common_extremes
      hlt hlC htC hlD htD hspan hCcup hDcap (hone.mono hsub)
    apply hnoStrong
    refine ⟨C ∪ D, hsub, ?_, hstrong⟩
    have hc := Finset.card_union_add_card_inter C D
    have hi : (C ∩ D).card = 2 := by rw [hinter]; simp [ne_of_lt hlt]
    omega
  let Z := P.erase p
  have hZP : Z ⊆ P := Finset.erase_subset _ _
  have hZs : Z ⊆ S := hZP.trans hPsub
  have hZcard : Z.card = k - 2 := by
    dsimp [Z]
    rw [Finset.card_erase_of_mem hp, hPcard]
    omega
  have hZne : Z.Nonempty := Finset.card_pos.mp (by omega)
  let a := Z.max' hZne
  have haZ : a ∈ Z := Finset.max'_mem _ _
  have haP : a ∈ P := hZP haZ
  have hap : a < p := by
    have := hPmax a haP
    have := (Finset.mem_erase.mp haZ).1
    omega
  have hZmax : ∀ z ∈ Z, z ≤ a := fun z hz ↦ Finset.le_max' _ z hz
  let Z₀ := Z.erase a
  have hZ₀card : Z₀.card = k - 3 := by
    dsimp [Z₀]
    rw [Finset.card_erase_of_mem haZ, hZcard]
    omega
  have hZ₀ne : Z₀.Nonempty := Finset.card_pos.mp (by omega)
  let a₂ := Z₀.max' hZ₀ne
  have ha₂Z₀ : a₂ ∈ Z₀ := Finset.max'_mem _ _
  have ha₂Z : a₂ ∈ Z := (Finset.mem_erase.mp ha₂Z₀).2
  have ha₂a : a₂ < a := by
    have := hZmax a₂ ha₂Z
    have := (Finset.mem_erase.mp ha₂Z₀).1
    omega
  have haPrev : ∀ z ∈ P, z < p → z ≤ a := by
    intro z hz hzp
    exact hZmax z (Finset.mem_erase.mpr ⟨ne_of_lt hzp, hz⟩)
  have ha₂Prev : ∀ z ∈ Z, z < a → z ≤ a₂ := by
    intro z hz hza
    exact Finset.le_max' _ z (Finset.mem_erase.mpr ⟨ne_of_lt hza, hz⟩)
  have hQrest : (Q.erase q₁).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hq₁]
    omega
  let y₂ := (Q.erase q₁).min' hQrest
  have hy₂rest : y₂ ∈ Q.erase q₁ := Finset.min'_mem _ _
  have hy₂Q : y₂ ∈ Q := (Finset.mem_erase.mp hy₂rest).2
  have hq₁y₂ : q₁ < y₂ := by
    have := hQmin y₂ hy₂Q
    have := (Finset.mem_erase.mp hy₂rest).1
    omega
  have hy₂Next : ∀ y ∈ insert r Q, q₁ < y → y₂ ≤ y := by
    intro y hy hq₁y
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact (hQR y₂ hy₂Q r hr).le
    · exact Finset.min'_le _ y (Finset.mem_erase.mpr ⟨ne_of_gt hq₁y, hy⟩)
  have hQrightMin : ∀ y ∈ insert r Q, q₁ ≤ y := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact (hQR q₁ hq₁ r hr).le
    · exact hQmin y hy
  have har := hPR a haP r hr
  have hpr := hPR p hp r hr
  have haq₁ := hPQ a haP q₁ hq₁
  have hq₁r := hQR q₁ hq₁ r hr
  have haNotRight : a ∉ insert r Q := by
    intro hx
    have := hQrightMin a hx
    omega
  have hAprCap : χ ⟨a, p, r, hap, hpr⟩ = Turn.right := by
    cases hturn : χ ⟨a, p, r, hap, hpr⟩ with
    | right => rfl
    | left =>
      have hsub : insert r P ⊆ S := Finset.insert_subset_iff.mpr ⟨hRsub hr, hPsub⟩
      have hcup := monochromaticSet_insert_max_of_oneChange haP hp hap hpr
        hPmax haPrev hPcup (hone.mono hsub) hturn
      have hrNotP : r ∉ P := fun hx ↦ (lt_irrefl r) (hPR r hx r hr)
      have hc := hbound _ hsub hcup
      rw [Finset.card_insert_of_notMem hrNotP, hPcard] at hc
      omega
  have hAyCap : χ ⟨a, q₁, y₂, haq₁, hq₁y₂⟩ = Turn.right := by
    cases hturn : χ ⟨a, q₁, y₂, haq₁, hq₁y₂⟩ with
    | right => rfl
    | left =>
      exfalso
      let C := insert a (insert r Q)
      let D : Finset (Fin n) := {a, p, r}
      have hCs : C ⊆ S := Finset.insert_subset_iff.mpr ⟨hPsub haP, hrightSub⟩
      have hDs : D ⊆ S := by
        simp only [D, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hPsub haP, hPsub hp, hRsub hr⟩
      have hCcup : IsCupSet χ C := monochromaticSet_insert_min_of_oneChange
        (Finset.mem_insert_of_mem hq₁) (Finset.mem_insert_of_mem hy₂Q) hq₁y₂ haq₁
        hQrightMin hy₂Next hrightCup (hone.mono hCs) hturn
      have hDcap : IsCapSet χ D := isCapSet_three ⟨a, p, r, hap, hpr⟩ hAprCap
      have hCcard : C.card = k - 1 := by
        dsimp [C]
        rw [Finset.card_insert_of_notMem haNotRight, Finset.card_insert_of_notMem hrNotQ, hQcard]
        omega
      have hDcard : D.card = 3 := by simp [D, ne_of_lt hap, ne_of_lt hpr, ne_of_lt har]
      apply hbridge hCs hDs har (by simp [C]) (by simp [C]) (by simp [D]) (by simp [D])
        _ hCcup hDcap hCcard hDcard
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨le_rfl, har.le⟩
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨har.le, le_rfl⟩
        exact ⟨(hPQ a haP x hx).le, (hQR x hx r hr).le⟩
      · simp only [D, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨le_rfl, har.le⟩
        · exact ⟨hap.le, hpr.le⟩
        · exact ⟨har.le, le_rfl⟩
  have hA₂AyCup : χ ⟨a₂, a, q₁, ha₂a, haq₁⟩ = Turn.left := by
    cases hturn : χ ⟨a₂, a, q₁, ha₂a, haq₁⟩ with
    | left => rfl
    | right =>
      exfalso
      have hfour : IsCapSet χ {a₂, a, q₁, y₂} := by
        have ht := (hone ha₂a haq₁ hq₁y₂ (hZs ha₂Z) (hPsub haP)
          (hQsub hq₁) (hQsub hy₂Q)).all_eq_of_outer_eq (hturn.trans hAyCap.symm)
        rintro ⟨i, j, l, hij, hjl⟩ hi hj hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hl
        rcases hi with rfl | rfl | rfl | rfl <;>
          rcases hj with rfl | rfl | rfl | rfl <;>
            rcases hl with rfl | rfl | rfl | rfl <;> try omega
        all_goals first | exact hturn | exact ht.1.symm.trans hturn |
          exact ht.2.2.trans hAyCap
      apply hPQnoCap
      refine ⟨{a₂, a, q₁, y₂}, ?_, ?_, hfour⟩
      · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_union_left _ (hZP ha₂Z), Finset.mem_union_left _ haP,
          Finset.mem_union_right _ hq₁, Finset.mem_union_right _ hy₂Q⟩
      · simp [ne_of_lt ha₂a, ne_of_lt haq₁, ne_of_lt hq₁y₂,
          ne_of_lt (ha₂a.trans haq₁), ne_of_lt (haq₁.trans hq₁y₂),
          ne_of_lt (ha₂a.trans (haq₁.trans hq₁y₂))]
  have hZqSub : insert q₁ Z ⊆ S := Finset.insert_subset_iff.mpr ⟨hQsub hq₁, hZs⟩
  have hZqCup : IsCupSet χ (insert q₁ Z) := monochromaticSet_insert_max_of_oneChange
    ha₂Z haZ ha₂a haq₁ hZmax ha₂Prev (FinsetPolygon.IsCupSet.mono hPcup hZP)
    (hone.mono hZqSub) hA₂AyCup
  let p₁ := P.min' hPne
  have hp₁P : p₁ ∈ P := Finset.min'_mem _ _
  have hp₁p : p₁ < p := Finset.min'_lt_max'_of_card P (by omega)
  have hp₁Z : p₁ ∈ Z := Finset.mem_erase.mpr ⟨ne_of_lt hp₁p, hp₁P⟩
  have hPmin : ∀ x ∈ P, p₁ ≤ x := fun x hx ↦ Finset.min'_le _ x hx
  have hpq₁ := hPQ p hp q₁ hq₁
  have hp₁q₁ := hPQ p₁ hp₁P q₁ hq₁
  cases hturn : χ ⟨p₁, p, q₁, hp₁p, hpq₁⟩ with
  | left =>
    have hmin : ∀ x ∈ insert r (insert p Q), p ≤ x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hpr.le
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (hPQ p hp x hx).le
    have hnext : ∀ x ∈ insert r (insert p Q), p < x → q₁ ≤ x := by
      intro x hx hpx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hq₁r.le
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · exact hQmin x hx
    have hsub : insert p₁ (insert r (insert p Q)) ⊆ S :=
      Finset.insert_subset_iff.mpr ⟨hPsub hp₁P, hbothSub⟩
    have hcup := monochromaticSet_insert_min_of_oneChange
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq₁)) hpq₁ hp₁p
      hmin hnext hM (hone.mono hsub) hturn
    have hp₁Not : p₁ ∉ insert r (insert p Q) := by
      intro hx
      have := hmin p₁ hx
      omega
    have hc := hbound _ hsub hcup
    rw [Finset.card_insert_of_notMem hp₁Not, hMcard] at hc
    omega
  | right =>
    let C := insert q₁ Z
    let D : Finset (Fin n) := {p₁, p, q₁}
    have hDs : D ⊆ S := by
      simp only [D, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hPsub hp₁P, hPsub hp, hQsub hq₁⟩
    have hDcap : IsCapSet χ D := isCapSet_three ⟨p₁, p, q₁, hp₁p, hpq₁⟩ hturn
    have hq₁NotZ : q₁ ∉ Z := fun hx ↦ (lt_irrefl q₁) (hPQ q₁ (hZP hx) q₁ hq₁)
    have hCcard : C.card = k - 1 := by
      dsimp [C]
      rw [Finset.card_insert_of_notMem hq₁NotZ, hZcard]
      omega
    have hDcard : D.card = 3 := by
      simp [D, ne_of_lt hp₁p, ne_of_lt hpq₁, ne_of_lt hp₁q₁]
    apply hbridge hZqSub hDs hp₁q₁ (by simp [hp₁Z]) (by simp)
      (by simp [D]) (by simp [D]) _ hZqCup hDcap hCcard hDcard
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hp₁q₁.le, le_rfl⟩
      · exact ⟨hPmin x (hZP hx), (hPQ x (hZP hx) q₁ hq₁).le⟩
    · simp only [D, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨le_rfl, hp₁q₁.le⟩
      · exact ⟨hp₁p.le, hpq₁.le⟩
      · exact ⟨hp₁q₁.le, le_rfl⟩

end ErdosSzekeres
