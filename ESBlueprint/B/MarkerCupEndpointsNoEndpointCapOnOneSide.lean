import ESBlueprint.B.MarkerStraddleTurnCore

namespace ErdosSzekeres

/-- Generalized strong marker endpoint exclusion: with a-cap-free left side, b-cap-free right side, no m+1 cup and every m-cup straddling a marker, either no (a-1)-cap ends at a first m-cup endpoint or no (b-1)-cap begins at a last endpoint. Derives all abstract marker-core premises from actual cup witnesses and saturation, without global six-cap exclusion.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_six_pred_pred_of_seven_le -/
theorem markerCupEndpoints_no_endpoint_cap_on_one_side {n a b m : ℕ} {χ : TripleColoring n} {s E F : Finset (Fin n)} {q h : Fin n}
(ha : 3 ≤ a) (hb : 3 ≤ b) (hm : 3 ≤ m) (hq : q ∉ s)
(hone : OneChangeOn χ s)
(hleft : ¬ContainsCapSet χ (s.filter (fun x ↦ x < q)) a)
(hright : ¬ContainsCapSet χ (s.filter (fun x ↦ q < x)) b)
(hnoCup : ¬ContainsCupSet χ s (m + 1))
(hstraddle : ∀ C : Finset (Fin n), C ⊆ s → C.card = m → IsCupSet χ C →
  (∃ x ∈ C, x < h) ∧ ∃ y ∈ C, h < y)
(hE : ∀ e ∈ E, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = m ∧ IsCupSet χ C ∧
  e ∈ C ∧ ∀ x ∈ C, e ≤ x)
(hF : ∀ f ∈ F, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = m ∧ IsCupSet χ C ∧
  f ∈ C ∧ ∀ x ∈ C, x ≤ f) :
¬(∃ K : Finset (Fin n), ∃ e : Fin n, K ⊆ s ∧ K.card = a - 1 ∧ IsCapSet χ K ∧
  e ∈ K ∧ e ∈ E ∧ ∀ x ∈ K, x ≤ e) ∨
¬(∃ K : Finset (Fin n), ∃ f : Fin n, K ⊆ s ∧ K.card = b - 1 ∧ IsCapSet χ K ∧
  f ∈ K ∧ f ∈ F ∧ ∀ x ∈ K, f ≤ x) := by
  classical
  by_contra hboth
  push Not at hboth
  obtain ⟨K, e, hKs, hKcard, hKcap, heK, heE, hKmax⟩ := hboth.1
  obtain ⟨K', f, hK's, hK'card, hK'cap, hfK', hfF, hK'min⟩ := hboth.2
  have heS := hKs heK
  have hfS := hK's hfK'
  have hKrest : (K.erase e).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem heK, hKcard]
    omega
  let p := (K.erase e).max' hKrest
  have hpErase : p ∈ K.erase e := Finset.max'_mem _ _
  have hpK : p ∈ K := (Finset.mem_erase.mp hpErase).2
  have hpe : p < e := by
    have := hKmax p hpK
    have := (Finset.mem_erase.mp hpErase).1
    omega
  have hKprev : ∀ x ∈ K, x < e → x ≤ p := by
    intro x hx hxe
    exact Finset.le_max' _ x (Finset.mem_erase.mpr ⟨ne_of_lt hxe, hx⟩)
  have hK'rest : (K'.erase f).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hfK', hK'card]
    omega
  let r := (K'.erase f).min' hK'rest
  have hrErase : r ∈ K'.erase f := Finset.min'_mem _ _
  have hrK' : r ∈ K' := (Finset.mem_erase.mp hrErase).2
  have hfr : f < r := by
    have := hK'min r hrK'
    have := (Finset.mem_erase.mp hrErase).1
    omega
  have hK'next : ∀ x ∈ K', f < x → r ≤ x := by
    intro x hx hfx
    exact Finset.min'_le _ x (Finset.mem_erase.mpr ⟨ne_of_gt hfx, hx⟩)
  obtain ⟨D, hDs, hDcard, hDcup, heD, hemin⟩ := hE e heE
  obtain ⟨C, hCs, hCcard, hCcup, hfC, hfmax⟩ := hF f hfF
  have hfirstTwo (A : Finset (Fin n)) (hcard : 2 ≤ A.card) :
      ∃ x y, x ∈ A ∧ y ∈ A ∧ x < y ∧ (∀ t ∈ A, x ≤ t) ∧
        (∀ t ∈ A, x < t → y ≤ t) := by
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    let x := A.min' hne
    have hx : x ∈ A := Finset.min'_mem _ _
    have hrest : (A.erase x).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hx]
      omega
    let y := (A.erase x).min' hrest
    have hy : y ∈ A.erase x := Finset.min'_mem _ _
    refine ⟨x, y, hx, (Finset.mem_erase.mp hy).2, ?_, ?_, ?_⟩
    · have := Finset.min'_le A y (Finset.mem_erase.mp hy).2
      have := (Finset.mem_erase.mp hy).1
      omega
    · exact fun t ht ↦ Finset.min'_le A t ht
    · intro t ht hxt
      exact Finset.min'_le _ t (Finset.mem_erase.mpr ⟨ne_of_gt hxt, ht⟩)
  have hlastTwo (A : Finset (Fin n)) (hcard : 2 ≤ A.card) :
      ∃ x y, x ∈ A ∧ y ∈ A ∧ x < y ∧ (∀ t ∈ A, t ≤ y) ∧
        (∀ t ∈ A, t < y → t ≤ x) := by
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    let y := A.max' hne
    have hy : y ∈ A := Finset.max'_mem _ _
    have hrest : (A.erase y).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hy]
      omega
    let x := (A.erase y).max' hrest
    have hx : x ∈ A.erase y := Finset.max'_mem _ _
    refine ⟨x, y, (Finset.mem_erase.mp hx).2, hy, ?_, ?_, ?_⟩
    · have := Finset.le_max' A x (Finset.mem_erase.mp hx).2
      have := (Finset.mem_erase.mp hx).1
      omega
    · exact fun t ht ↦ Finset.le_max' A t ht
    · intro t ht hty
      exact Finset.le_max' _ t (Finset.mem_erase.mpr ⟨ne_of_lt hty, ht⟩)
  let Dt := D.erase e
  let Ct := C.erase f
  have hDtcard : Dt.card = m - 1 := by
    dsimp [Dt]
    rw [Finset.card_erase_of_mem heD, hDcard]
  have hCtcard : Ct.card = m - 1 := by
    dsimp [Ct]
    rw [Finset.card_erase_of_mem hfC, hCcard]
  obtain ⟨d₂, d₃, hd₂Dt, hd₃Dt, hd23, hd₂min, hd₃next⟩ := hfirstTwo Dt (by omega)
  obtain ⟨c₁, c₂, hc₁Ct, hc₂Ct, hc12, hc₂max, hc₁prev⟩ := hlastTwo Ct (by omega)
  have hd₂D := (Finset.mem_erase.mp hd₂Dt).2
  have hd₃D := (Finset.mem_erase.mp hd₃Dt).2
  have hc₁C := (Finset.mem_erase.mp hc₁Ct).2
  have hc₂C := (Finset.mem_erase.mp hc₂Ct).2
  have hd₂S := hDs hd₂D
  have hd₃S := hDs hd₃D
  have hc₁S := hCs hc₁C
  have hc₂S := hCs hc₂C
  have hed2 : e < d₂ := by
    have := hemin d₂ hd₂D
    have := (Finset.mem_erase.mp hd₂Dt).1
    omega
  have hc2f : c₂ < f := by
    have := hfmax c₂ hc₂C
    have := (Finset.mem_erase.mp hc₂Ct).1
    omega
  have hd₂next : ∀ x ∈ D, e < x → d₂ ≤ x := by
    intro x hx hex
    exact hd₂min x (Finset.mem_erase.mpr ⟨ne_of_gt hex, hx⟩)
  have hc₂prev : ∀ x ∈ C, x < f → x ≤ c₂ := by
    intro x hx hxf
    exact hc₂max x (Finset.mem_erase.mpr ⟨ne_of_lt hxf, hx⟩)
  have heh : e < h := by
    obtain ⟨x, hx, hxh⟩ := (hstraddle D hDs hDcard hDcup).1
    exact (hemin x hx).trans_lt hxh
  have hhf : h < f := by
    obtain ⟨x, hx, hhx⟩ := (hstraddle C hCs hCcard hCcup).2
    exact hhx.trans_le (hfmax x hx)
  have hS1left : ∀ x ∈ s, ∀ hxe : x < e,
      χ ⟨x, e, d₂, hxe, hed2⟩ = Turn.right := by
    intro x hx hxe
    cases hturn : χ ⟨x, e, d₂, hxe, hed2⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert x D ⊆ s := Finset.insert_subset_iff.mpr ⟨hx, hDs⟩
      have hcup := monochromaticSet_insert_min_of_oneChange heD hd₂D hed2 hxe
        hemin hd₂next hDcup (hone.mono hsub) hturn
      have hxNotD : x ∉ D := by
        intro hxD
        have := hemin x hxD
        omega
      exact hnoCup ⟨insert x D, hsub,
        by rw [Finset.card_insert_of_notMem hxNotD, hDcard], hcup⟩
  have hS1right : ∀ y ∈ s, ∀ hfy : f < y,
      χ ⟨c₂, f, y, hc2f, hfy⟩ = Turn.right := by
    intro y hy hfy
    cases hturn : χ ⟨c₂, f, y, hc2f, hfy⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert y C ⊆ s := Finset.insert_subset_iff.mpr ⟨hy, hCs⟩
      have hcup := monochromaticSet_insert_max_of_oneChange hc₂C hfC hc2f hfy
        hfmax hc₂prev hCcup (hone.mono hsub) hturn
      have hyNotC : y ∉ C := by
        intro hyC
        have := hfmax y hyC
        omega
      exact hnoCup ⟨insert y C, hsub,
        by rw [Finset.card_insert_of_notMem hyNotC, hCcard], hcup⟩
  have hleftCap (T : Finset (Fin n)) (hTs : T ⊆ s) (hTcard : T.card = a)
      (hTcap : IsCapSet χ T) (hy : ∀ x ∈ T, x < q) : False := by
    exact hleft ⟨T, fun x hx ↦ Finset.mem_filter.mpr ⟨hTs hx, hy x hx⟩, hTcard, hTcap⟩
  have hrightCap (T : Finset (Fin n)) (hTs : T ⊆ s) (hTcard : T.card = b)
      (hTcap : IsCapSet χ T) (hy : ∀ x ∈ T, q < x) : False := by
    exact hright ⟨T, fun x hx ↦ Finset.mem_filter.mpr ⟨hTs hx, hy x hx⟩,
      hTcard, hTcap⟩
  have hqd2 : q < d₂ := by
    have hdNot : d₂ ∉ K := by
      intro hx
      have := hKmax d₂ hx
      omega
    have hsub : insert d₂ K ⊆ s := Finset.insert_subset_iff.mpr ⟨hd₂S, hKs⟩
    have hcap := monochromaticSet_insert_max_of_oneChange hpK heK hpe hed2
      hKmax hKprev hKcap (hone.mono hsub) (hS1left p (hKs hpK) hpe)
    have hcard : (insert d₂ K).card = a := by
      rw [Finset.card_insert_of_notMem hdNot, hKcard]
      omega
    by_contra h
    have hdq : d₂ ≠ q := by rintro rfl; exact hq hd₂S
    have hdlt : d₂ < q := by omega
    exact hleftCap _ hsub hcard hcap (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hdlt
      · exact (hKmax x hx).trans_lt (hed2.trans hdlt))
  have hc2q : c₂ < q := by
    have hcNot : c₂ ∉ K' := by
      intro hx
      have := hK'min c₂ hx
      omega
    have hsub : insert c₂ K' ⊆ s := Finset.insert_subset_iff.mpr ⟨hc₂S, hK's⟩
    have hcap := monochromaticSet_insert_min_of_oneChange hfK' hrK' hfr hc2f
      hK'min hK'next hK'cap (hone.mono hsub) (hS1right r (hK's hrK') hfr)
    have hcard : (insert c₂ K').card = b := by
      rw [Finset.card_insert_of_notMem hcNot, hK'card]
      omega
    by_contra h
    have hcq : c₂ ≠ q := by rintro rfl; exact hq hc₂S
    have hqclt : q < c₂ := by omega
    exact hrightCap _ hsub hcard hcap (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hqclt
      · exact (hqclt.trans hc2f).trans_le (hK'min x hx))
  have hc2d2 : c₂ < d₂ := hc2q.trans hqd2
  have hCtSub : Ct ⊆ s := (Finset.erase_subset _ _).trans hCs
  have hDtSub : Dt ⊆ s := (Finset.erase_subset _ _).trans hDs
  have hCtCup : IsCupSet χ Ct := FinsetPolygon.IsCupSet.mono hCcup (Finset.erase_subset _ _)
  have hDtCup : IsCupSet χ Dt := FinsetPolygon.IsCupSet.mono hDcup (Finset.erase_subset _ _)
  have hS4left : ∀ hc2e : c₂ < e, χ ⟨c₁, c₂, e, hc12, hc2e⟩ = Turn.right := by
    intro hc2e
    cases hturn : χ ⟨c₁, c₂, e, hc12, hc2e⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert e Ct ⊆ s := Finset.insert_subset_iff.mpr ⟨heS, hCtSub⟩
      have hcup := monochromaticSet_insert_max_of_oneChange hc₁Ct hc₂Ct hc12 hc2e
        hc₂max hc₁prev hCtCup (hone.mono hsub) hturn
      have heNot : e ∉ Ct := by
        intro hx
        have := hc₂max e hx
        omega
      have hcard : (insert e Ct).card = m := by
        rw [Finset.card_insert_of_notMem heNot, hCtcard]
        omega
      obtain ⟨x, hx, hhx⟩ := (hstraddle _ hsub hcard hcup).2
      have hxh : x < h := by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact heh
        · exact (hc₂max x hx).trans_lt (hc2e.trans heh)
      omega
  have hS4right : ∀ hfd2 : f < d₂, χ ⟨f, d₂, d₃, hfd2, hd23⟩ = Turn.right := by
    intro hfd2
    cases hturn : χ ⟨f, d₂, d₃, hfd2, hd23⟩ with
    | right => rfl
    | left =>
      exfalso
      have hsub : insert f Dt ⊆ s := Finset.insert_subset_iff.mpr ⟨hfS, hDtSub⟩
      have hcup := monochromaticSet_insert_min_of_oneChange hd₂Dt hd₃Dt hd23 hfd2
        hd₂min hd₃next hDtCup (hone.mono hsub) hturn
      have hfNot : f ∉ Dt := by
        intro hx
        have := hd₂min f hx
        omega
      have hcard : (insert f Dt).card = m := by
        rw [Finset.card_insert_of_notMem hfNot, hDtcard]
        omega
      obtain ⟨x, hx, hxh⟩ := (hstraddle _ hsub hcard hcup).1
      have hhx : h < x := by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hhf
        · exact (hhf.trans hfd2).trans_le (hd₂min x hx)
      omega
  have hS4both : ¬(χ ⟨c₁, c₂, d₂, hc12, hc2d2⟩ = Turn.left ∧
      χ ⟨c₂, d₂, d₃, hc2d2, hd23⟩ = Turn.left) := by
    rintro ⟨hfirst, hlast⟩
    have hd₂Sub : insert d₂ Ct ⊆ s := Finset.insert_subset_iff.mpr ⟨hd₂S, hCtSub⟩
    have hd₂Cup := monochromaticSet_insert_max_of_oneChange hc₁Ct hc₂Ct hc12 hc2d2
      hc₂max hc₁prev hCtCup (hone.mono hd₂Sub) hfirst
    have hsub : insert d₃ (insert d₂ Ct) ⊆ s :=
      Finset.insert_subset_iff.mpr ⟨hd₃S, hd₂Sub⟩
    have hmax : ∀ x ∈ insert d₂ Ct, x ≤ d₂ := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (hc₂max x hx).trans hc2d2.le
    have hprev : ∀ x ∈ insert d₂ Ct, x < d₂ → x ≤ c₂ := by
      intro x hx hxd
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · exact hc₂max x hx
    have hcup := monochromaticSet_insert_max_of_oneChange (Finset.mem_insert_of_mem hc₂Ct)
      (by simp : d₂ ∈ insert d₂ Ct) hc2d2 hd23 hmax hprev hd₂Cup (hone.mono hsub) hlast
    have hd₂Not : d₂ ∉ Ct := by
      intro hx
      have := hc₂max d₂ hx
      omega
    have hd₃Not : d₃ ∉ insert d₂ Ct := by
      intro hx
      have := hmax d₃ hx
      omega
    have hcard : (insert d₃ (insert d₂ Ct)).card = m + 1 := by
      rw [Finset.card_insert_of_notMem hd₃Not, Finset.card_insert_of_notMem hd₂Not, hCtcard]
      omega
    exact hnoCup ⟨_, hsub, hcard, hcup⟩
  have hblockLeft : ∀ hec2 : e < c₂, χ ⟨p, e, c₂, hpe, hec2⟩ ≠ Turn.right := by
    intro hec2 hturn
    have hsub : insert c₂ K ⊆ s := Finset.insert_subset_iff.mpr ⟨hc₂S, hKs⟩
    have hcap := monochromaticSet_insert_max_of_oneChange hpK heK hpe hec2
      hKmax hKprev hKcap (hone.mono hsub) hturn
    have hcNot : c₂ ∉ K := by
      intro hx
      have := hKmax c₂ hx
      omega
    have hcard : (insert c₂ K).card = a := by
      rw [Finset.card_insert_of_notMem hcNot, hKcard]
      omega
    exact hleftCap _ hsub hcard hcap (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hc2q
      · exact (hKmax x hx).trans_lt (hec2.trans hc2q))
  have hblockRight : ∀ hd2f : d₂ < f, χ ⟨d₂, f, r, hd2f, hfr⟩ ≠ Turn.right := by
    intro hd2f hturn
    have hsub : insert d₂ K' ⊆ s := Finset.insert_subset_iff.mpr ⟨hd₂S, hK's⟩
    have hcap := monochromaticSet_insert_min_of_oneChange hfK' hrK' hfr hd2f
      hK'min hK'next hK'cap (hone.mono hsub) hturn
    have hdNot : d₂ ∉ K' := by
      intro hx
      have := hK'min d₂ hx
      omega
    have hcard : (insert d₂ K').card = b := by
      rw [Finset.card_insert_of_notMem hdNot, hK'card]
      omega
    exact hrightCap _ hsub hcard hcap (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hqd2
      · exact (hqd2.trans hd2f).trans_le (hK'min x hx))
  exact marker_straddle_turn_core hone (hKs hpK) heS hfS (hK's hrK') hc₁S hc₂S hd₂S hd₃S
    hpe (heh.trans hhf) hfr hc12 hc2f hed2 hd23 hc2d2
    (hDcup _ heD hd₂D hd₃D) (hCcup _ hc₁C hc₂C hfC)
    hS1left hS1right hS4left hS4right hS4both hblockLeft hblockRight


end ErdosSzekeres
