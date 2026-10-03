import ESBlueprint.B.MonochromaticSetInsertMinOfOneChange

namespace ErdosSzekeres

/-- In a one-change set avoiding four-caps, longest-cup-start ranks are attained and maximal; every equal-rank layer is a cup and has at most its rank many points. This certifies the layer structure behind the triangular bound and the audited R2 defect.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem exists_cupStartLayers_of_oneChange_no_capFour {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4) : ∃ β : Fin n → ℕ, (∀ x ∈ s, ∃ C : Finset (Fin n), C ⊆ s ∧ x ∈ C ∧ IsCupSet χ C ∧ (∀ y ∈ C, x ≤ y) ∧ C.card = β x) ∧ (∀ x ∈ s, ∀ C : Finset (Fin n), C ⊆ s → x ∈ C → IsCupSet χ C → (∀ y ∈ C, x ≤ y) → C.card ≤ β x) ∧ (∀ j : ℕ, IsCupSet χ (s.filter (fun x ↦ β x = j)) ∧ (s.filter (fun x ↦ β x = j)).card ≤ j) := by
  classical
  let cups (x : Fin n) := s.powerset.filter (fun C ↦
    x ∈ C ∧ IsCupSet χ C ∧ ∀ y ∈ C, x ≤ y)
  let β (x : Fin n) := (cups x).sup Finset.card
  have memcups {x : Fin n} {C : Finset (Fin n)} :
      C ∈ cups x ↔ C ⊆ s ∧ x ∈ C ∧ IsCupSet χ C ∧ ∀ y ∈ C, x ≤ y := by
    simp only [cups, Finset.mem_filter, Finset.mem_powerset]
  have hatt : ∀ x ∈ s, ∃ C : Finset (Fin n), C ⊆ s ∧ x ∈ C ∧ IsCupSet χ C ∧
      (∀ y ∈ C, x ≤ y) ∧ C.card = β x := by
    intro x hx
    have hsingle : IsCupSet χ {x} := by
      intro t hi hj _
      exfalso
      simp only [Finset.mem_singleton] at hi hj
      have := t.hij
      omega
    have hnonempty : (cups x).Nonempty := by
      refine ⟨{x}, memcups.mpr ⟨Finset.singleton_subset_iff.mpr hx, by simp,
        hsingle, ?_⟩⟩
      intro y hy
      have hyx := Finset.mem_singleton.mp hy
      subst y
      exact le_rfl
    obtain ⟨C, hC, heq⟩ := Finset.exists_mem_eq_sup (cups x) hnonempty Finset.card
    obtain ⟨hsub, hxC, hcup, hmin⟩ := memcups.mp hC
    exact ⟨C, hsub, hxC, hcup, hmin, heq.symm⟩
  have hmax : ∀ x ∈ s, ∀ C : Finset (Fin n), C ⊆ s → x ∈ C → IsCupSet χ C →
      (∀ y ∈ C, x ≤ y) → C.card ≤ β x := by
    intro x _ C hsub hxC hcup hmin
    exact Finset.le_sup (s := cups x) (f := Finset.card)
      (memcups.mpr ⟨hsub, hxC, hcup, hmin⟩)
  refine ⟨β, hatt, hmax, ?_⟩
  intro j
  let row := s.filter (fun x ↦ β x = j)
  have hrowSub : row ⊆ s := Finset.filter_subset _ _
  have hrowCup : IsCupSet χ row := by
    intro t hi hj hk
    have hiS : t.i ∈ s := hrowSub hi
    have hjS : t.j ∈ s := hrowSub hj
    have hkS : t.k ∈ s := hrowSub hk
    have hiβ : β t.i = j := (Finset.mem_filter.mp hi).2
    have hjβ : β t.j = j := (Finset.mem_filter.mp hj).2
    have hkβ : β t.k = j := (Finset.mem_filter.mp hk).2
    cases hcol : χ t with
    | left => rfl
    | right =>
      exfalso
      have hpairCup : IsCupSet χ {t.i, t.j} := by
        intro u hui huj huk
        exfalso
        simp only [Finset.mem_insert, Finset.mem_singleton] at hui huj huk
        have := u.hij
        have := u.hjk
        omega
      have hpairSub : ({t.i, t.j} : Finset (Fin n)) ⊆ s :=
        Finset.insert_subset_iff.mpr ⟨hiS, Finset.singleton_subset_iff.mpr hjS⟩
      have hpairMin : ∀ y ∈ ({t.i, t.j} : Finset (Fin n)), t.i ≤ y := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact le_rfl
        · have hyj := Finset.mem_singleton.mp hy
          simpa only [hyj] using t.hij.le
      have hpairCard : ({t.i, t.j} : Finset (Fin n)).card = 2 := by
        simp [ne_of_lt t.hij]
      have hjTwo : 2 ≤ j := by
        have h := hmax t.i hiS {t.i, t.j} hpairSub (by simp) hpairCup hpairMin
        simpa only [hpairCard, hiβ] using h
      obtain ⟨C, hCsub, hzC, hCcup, hCmin, hCcard⟩ := hatt t.k hkS
      have hrest : (C.erase t.k).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hzC]
        omega
      let w := (C.erase t.k).min' hrest
      have hw : w ∈ C.erase t.k := Finset.min'_mem _ _
      have hwC : w ∈ C := (Finset.mem_erase.mp hw).2
      have hzw : t.k < w := by
        have := hCmin w hwC
        have := (Finset.mem_erase.mp hw).1
        omega
      have hCnext : ∀ y ∈ C, t.k < y → w ≤ y := by
        intro y hy hzy
        exact Finset.min'_le _ y (Finset.mem_erase.mpr ⟨ne_of_gt hzy, hy⟩)
      have hnewSub : insert t.j C ⊆ s := Finset.insert_subset_iff.mpr ⟨hjS, hCsub⟩
      have hlast : χ ⟨t.j, t.k, w, t.hjk, hzw⟩ = Turn.right := by
        cases hcol₂ : χ ⟨t.j, t.k, w, t.hjk, hzw⟩ with
        | right => rfl
        | left =>
          exfalso
          have hnewCup : IsCupSet χ (insert t.j C) :=
            monochromaticSet_insert_min_of_oneChange hzC hwC hzw t.hjk hCmin hCnext
              hCcup (hone.mono hnewSub) hcol₂
          have hnewMin : ∀ y ∈ insert t.j C, t.j ≤ y := by
            intro y hy
            rcases Finset.mem_insert.mp hy with rfl | hy
            · exact le_rfl
            · exact t.hjk.le.trans (hCmin y hy)
          have hbound := hmax t.j hjS (insert t.j C) hnewSub (by simp) hnewCup hnewMin
          have hjNot : t.j ∉ C := by
            intro hjC
            have := hCmin t.j hjC
            have := t.hjk
            omega
          rw [Finset.card_insert_of_notMem hjNot] at hbound
          omega
      apply hnoCap
      let f : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono ![t.i, t.j, t.k, w] (by
        apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        fin_cases i
        · simpa using t.hij
        · simpa using t.hjk
        · simpa using hzw)
      have hsub : Finset.univ.image f ⊆ s := by
        intro z hz
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
        obtain ⟨i, rfl⟩ := hz
        fin_cases i
        · simpa [f] using hiS
        · simpa [f] using hjS
        · simpa [f] using hkS
        · simpa [f] using hCsub hwC
      refine ⟨Finset.univ.image f, hsub, ?_, ?_⟩
      · simpa using Finset.card_image_of_injective Finset.univ f.injective
      · exact FinsetPolygon.IsCap.image (isMonochromaticChain_finFour_of_outer_eq f
          (hone.mono hsub) (by simpa [f] using hcol) (by simpa [f] using hlast))
  refine ⟨hrowCup, ?_⟩
  change row.card ≤ j
  rcases row.eq_empty_or_nonempty with hempty | hnonempty
  · simp [hempty]
  · let x := row.min' hnonempty
    have hx : x ∈ row := Finset.min'_mem _ _
    have hmin : ∀ y ∈ row, x ≤ y := by
      intro y hy
      exact Finset.min'_le _ y hy
    have h := hmax x (hrowSub hx) row hrowSub hx hrowCup hmin
    simpa only [(Finset.mem_filter.mp hx).2] using h

end ErdosSzekeres
